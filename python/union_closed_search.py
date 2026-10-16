"""Exact union-closed family enumeration for 1 <= n <= 5, stdlib only.

A set is its coordinate bitmask; a family is a bitmask of set bitmasks.
The empty family and {empty set} are excluded; unused coordinates are allowed.

Completeness and safe pruning:
Decide sets in decreasing integer order. At decision s all selected sets t
satisfy t > s. Therefore s | t >= t > s, so every union required by adding s
has already been decided. Reject inclusion exactly when such a union is
absent (hence forbidden), never merely because an arbitrary partial family
is nonclosed. Every closed target follows one unique include/exclude path,
and that path cannot be rejected. Every leaf is closed by induction. Empty
set membership is an independent final binary choice.

Symmetry reduction occurs only AFTER exhaustive labeled generation. Mark
the full orbit under S_n and record its smallest integer member. Thus no
unproved canonical-augmentation rule can remove a family. Orbit sizes give
exact labeled multiplicities; all reported frequency comparisons are integer
comparisons, with rational minima. This is finite verification, not a proof
of Frankl's conjecture for arbitrary n.
"""

import argparse
import json
from fractions import Fraction
from itertools import permutations
from pathlib import Path
from time import perf_counter


def _validate_n(n):
    if not isinstance(n, int) or isinstance(n, bool) or not 1 <= n <= 5:
        raise ValueError('Exact search supports integer 1 <= n <= 5')


def _nonempty_set_families(n):
    """Generate closed families not containing empty set, including no sets."""
    selected = []

    def visit(s, family):
        if s == 0:
            yield family
            return
        yield from visit(s - 1, family)
        if all(family & (1 << (s | t)) for t in selected):
            selected.append(s)
            yield from visit(s - 1, family | (1 << s))
            selected.pop()

    yield from visit((1 << n) - 1, 0)


def enumerate_family_masks(n):
    """Yield every admitted labeled family once, with either empty choice."""
    _validate_n(n)
    for family in _nonempty_set_families(n):
        if family:
            yield family
            yield family | 1


class PermutationAction:
    """All coordinate permutations, applied by precomputed byte lookups."""

    def __init__(self, n):
        _validate_n(n)
        self.n = n
        self.byte_count = ((1 << n) + 7) // 8
        self.tables = []
        for permutation in permutations(range(n)):
            moved_bits = []
            for s in range(1 << n):
                moved = sum(1 << permutation[i] for i in range(n)
                            if s & (1 << i))
                moved_bits.append(1 << moved)
            tables = []
            for offset in range(0, 1 << n, 8):
                table = [0] * 256
                for value in range(1, 256):
                    bit = value & -value
                    index = offset + bit.bit_length() - 1
                    table[value] = table[value ^ bit]
                    if index < len(moved_bits):
                        table[value] |= moved_bits[index]
                tables.append(table)
            self.tables.append(tables)

    def orbit(self, family):
        if family < 0 or family >= 1 << (1 << self.n):
            raise ValueError('Family mask exceeds its ground set')
        chunks = [(family >> (8 * i)) & 255 for i in range(self.byte_count)]
        if self.byte_count == 4:
            a, b, c, d = chunks
            return {t[0][a] | t[1][b] | t[2][c] | t[3][d]
                    for t in self.tables}
        return {sum(table[value] for table, value in zip(tables, chunks))
                for tables in self.tables}

    def canonical(self, family):
        return min(self.orbit(family))


def _members(family):
    result = []
    while family:
        bit = family & -family
        result.append(bit.bit_length() - 1)
        family ^= bit
    return result


def audit(n, include_representatives=False):
    """Enumerate all labeled families and summarize every S_n orbit."""
    _validate_n(n)
    started = perf_counter()
    action = PermutationAction(n)
    seen = set()
    representatives = []
    strata = {}
    total = classes = equality = violation_count = generated = 0
    counterexamples = []
    best = Fraction(1)
    witness = None
    for family in _nonempty_set_families(n):
        if not family:
            continue
        generated += 1
        if family in seen:
            continue
        orbit = action.orbit(family)
        seen.update(orbit)
        representative = min(orbit)
        members = _members(representative)
        support = 0
        for s in members:
            support |= s
        support_size = support.bit_count()
        frequencies = [sum(bool(s & (1 << i)) for s in members)
                       for i in range(n)]
        maximum = max(frequencies)
        weight = len(orbit)
        for contains_empty in (False, True):
            canonical = representative | int(contains_empty)
            size = len(members) + int(contains_empty)
            ratio = Fraction(maximum, size)
            key = support_size, contains_empty
            if key not in strata:
                strata[key] = dict(support_size=support_size,
                                   full_support=support_size == n,
                                   contains_empty=contains_empty,
                                   labeled_count=0, isomorphism_classes=0,
                                   equality_families=0, frankl_violations=0,
                                   minimum_max_frequency=ratio)
            row = strata[key]
            row['labeled_count'] += weight
            row['isomorphism_classes'] += 1
            row['minimum_max_frequency'] = min(row['minimum_max_frequency'], ratio)
            total += weight
            classes += 1
            if witness is None or ratio < best:
                best, witness = ratio, _members(canonical)
            if 2 * maximum == size:
                equality += weight
                row['equality_families'] += weight
            if 2 * maximum < size:
                violation_count += weight
                row['frankl_violations'] += weight
                counterexamples.extend(_members(m | int(contains_empty))
                                       for m in sorted(orbit))
            if include_representatives:
                representatives.append(dict(family_mask=canonical,
                                            family=_members(canonical),
                                            orbit_size=weight,
                                            support_size=support_size,
                                            contains_empty=contains_empty,
                                            maximum_frequency=str(ratio)))
    if total != 2 * generated or len(seen) != generated:
        raise AssertionError('Orbit multiplicities disagree with labeled enumeration')
    rows = []
    for key in sorted(strata):
        row = strata[key]
        row['minimum_max_frequency'] = str(row['minimum_max_frequency'])
        rows.append(row)
    result = dict(n=n, valid_families=total, isomorphism_classes=classes,
                  equality_families=equality, frankl_violations=violation_count,
                  minimum_max_frequency=str(best), witness_masks=witness,
                  counterexamples=counterexamples, strata=rows,
                  labeled_generation_count=2 * generated,
                  elapsed_seconds=perf_counter() - started,
                  conventions='Labeled ground set [n]; unused coordinates allowed; '
                              'empty set optional; empty family and {empty} excluded.',
                  scope='Exhaustive finite verification only; no general proof.')
    full_empty = strata[(n, True)]
    result['conventional_counts'] = {
        'empty_required_dummy_allowed_including_singleton_empty': {
            'labeled_count': total // 2 + 1,
            'isomorphism_classes': classes // 2 + 1},
        'empty_required_full_support': {
            'labeled_count': full_empty['labeled_count'],
            'isomorphism_classes': full_empty['isomorphism_classes']}}
    if include_representatives:
        result['representatives'] = sorted(representatives,
                                           key=lambda r: r['family_mask'])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, choices=range(1, 6), default=5)
    parser.add_argument('--representatives', action='store_true',
                        help='Include actual canonical families and orbit sizes')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = [audit(n, args.representatives) for n in range(1, args.max_n + 1)]
    rendered = json.dumps({'closed_families': results}, indent=2, allow_nan=False)
    if args.output:
        args.output.write_text(rendered + '\n', encoding='utf-8')
    print(rendered)


if __name__ == '__main__':
    main()
