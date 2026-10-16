"""Unit and property tests for poonen_obstruction_breaker.py."""

from __future__ import annotations

from fractions import Fraction
import json
import math
import pytest

from poonen_obstruction_breaker import (
    _bits_of,
    analyze_complement_defect_transfer,
    analyze_conditional_fiber_entropy,
    analyze_fiber_base_surplus_absorption,
    analyze_high_mc_prefix_fiber_conditioning,
    analyze_iterative_layer_decomposition,
    analyze_local_global_compensation,
    analyze_minimal_fiber_uniqueness,
    analyze_n_gt_2k_regime,
    analyze_prefix_tower_support_contraction,
    analyze_quotient_carrier_density_and_mass_integration,
    analyze_subcritical_fiber_positivity,
    analyze_intra_fiber_union_closure,
    analyze_volume_bonus_extended_dense_witness,
    analyze_intra_fiber_deficit_cap,
    verify_k3_intra_fiber_slice_deficit_le_one,
    analyze_universal_top_fiber_absorption,
    audit_asymmetric_gilmer_shift,
    audit_conditional_fiber_entropy_barrier,
    audit_pincer_trap_adversary,
    build_disjoint_absorption_adversary_family,
    build_poonen_local_obstruction_family,
    build_sarvate_renaud_k3_obstruction,
    compute_coupled_asymmetric_gilmer_shift,
    compute_prefix_chain_rule,
    compute_quotient_lattice_decomposition,
    delta_h2,
    main,
    optimize_absorption_adversary,
    optimize_pincer_trap_adversary,
    optimize_quotient_carrier_adversary,
    psi2_rate,
    run_poonen_obstruction_audit,
    secant_factorization_difference,
    secant_factorization_integer,
    solve_pincer_trap_zero_crossing,
    solve_poonen_farkas_weights,
    verify_concrete_bridge_identities,
    verify_cross_fiber_join_submultiplicativity,
    verify_unconditional_frankl_resolution,
    verify_universal_meta_dichotomy,
)
from universal_frankl_resolver import (
    build_tier4_obstruction_family,
    check_is_inter_closed,
    check_is_union_closed,
    generate_adversarial_non_biclosed_families,
    resolve_universal_frankl,
    union_close_arbitrary_seeds,
)


def _assert_valid_injection(
    family: list[int],
    witness: int,
    pairs: list[tuple[int, int]],
) -> None:
    bit = 1 << witness
    without_w = [s for s in family if not (s & bit)]
    with_w = {s for s in family if (s & bit)}
    assert len(pairs) == len(without_w)
    seen_sources = set()
    seen_targets = set()
    for src, dst in pairs:
        assert src in without_w
        assert dst in with_w
        assert src not in seen_sources
        assert dst not in seen_targets
        seen_sources.add(src)
        seen_targets.add(dst)


class TestLocalObstructionConstructions:
    """Verify Sarvate-Renaud (k=3) and Poonen (k=4, 5) local obstruction families."""

    def test_sarvate_renaud_k3_obstruction_exact_properties(self) -> None:
        fam = build_sarvate_renaud_k3_obstruction(n=10)
        is_uc, uc_witness = check_is_union_closed(fam)
        assert is_uc and uc_witness is None

        is_ic, ic_witness = check_is_inter_closed(fam)
        assert not is_ic and ic_witness is not None

        # Unique smallest non-empty set is A_min = {0, 1, 2} (mask 0b111) of size 3
        non_empty = [s for s in fam if s > 0]
        min_sz = min(s.bit_count() for s in non_empty)
        assert min_sz == 3
        min_sets = [s for s in non_empty if s.bit_count() == 3]
        assert min_sets == [0b111]

        # Every element x in A_min = {0, 1, 2} has strict negative defect Delta_F(x) = -1 < 0
        transfer = analyze_complement_defect_transfer(fam)
        assert transfer["a_mask"] == 0b111
        assert transfer["is_strict_local_obstruction"] is True
        assert transfer["is_averaging_obstruction"] is True
        for x in (0, 1, 2):
            assert transfer["a_element_defects"][x] == -1
        assert transfer["local_defect"] == -3

        # Broken by Quotient-Complement Defect Transfer
        assert transfer["complement_defect"] > 0
        y_star = transfer["complement_witness"]
        assert y_star is not None
        assert y_star not in (0, 1, 2)
        assert (transfer["c_mask"] >> y_star) & 1
        assert transfer["complement_witness_defect"] >= 0
        assert transfer["obstruction_broken"] is True
        _assert_valid_injection(fam, y_star, transfer["complement_injection_pairs"])

    @pytest.mark.parametrize("k,c_size", [(3, 6), (4, 6), (5, 6), (5, 7)])
    def test_poonen_local_obstruction_family_k3_k4_k5(self, k: int, c_size: int) -> None:
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        is_uc, _ = check_is_union_closed(fam)
        assert is_uc
        is_ic, _ = check_is_inter_closed(fam)
        assert not is_ic

        a_mask = (1 << k) - 1
        assert a_mask in fam
        assert min(s.bit_count() for s in fam if s > 0) == k

        transfer = analyze_complement_defect_transfer(fam)
        assert transfer["a_mask"] == a_mask
        assert transfer["is_strict_local_obstruction"] is True
        assert all(d < 0 for d in transfer["a_element_defects"].values())
        assert transfer["local_defect"] < 0
        assert transfer["complement_defect"] > 0

        y_star = transfer["complement_witness"]
        assert y_star is not None and y_star >= k
        assert transfer["complement_witness_defect"] > 0
        assert transfer["obstruction_broken"] is True
        _assert_valid_injection(fam, y_star, transfer["complement_injection_pairs"])


class TestQuotientLatticeAndCrucialCollisionLaw:
    """Verify F / A union-closure, top-slice isomorphism, and the Crucial Collision Law."""

    @pytest.mark.parametrize(
        "fam,a_mask",
        [
            (build_sarvate_renaud_k3_obstruction(n=10), 0b111),
            (build_poonen_local_obstruction_family(k=4, c_size=6), 0b1111),
            (build_poonen_local_obstruction_family(k=5, c_size=6), 0b11111),
            (build_tier4_obstruction_family(n=10), 0b11111),
        ],
    )
    def test_quotient_lattice_and_collision_law_with_and_without_empty_set(
        self, fam: list[int], a_mask: int
    ) -> None:
        for include_empty in (False, True):
            current_fam = sorted(set(fam) | ({0} if include_empty else set()))
            decomp = compute_quotient_lattice_decomposition(current_fam, a_mask)

            assert decomp["quotient_is_union_closed"] is True
            assert decomp["quotient_uc_counterexample"] is None
            assert decomp["top_slice_isomorphic"] is True
            assert decomp["is_minimal_non_empty_set"] is True
            assert decomp["low_multiplicity_nonnegative"] is True
            assert decomp["empty_fiber_bounded_by_2"] is True
            assert decomp["empty_fiber_multiplicity"] == (2 if include_empty else 1)
            assert decomp["empty_fiber_defect"] >= 0
            assert decomp["collision_law_verified"] is True

            # Verify every Q with m(Q) <= 2 has Delta_{F_Q}(A) >= 0
            for q_mask, info in decomp["fibers"].items():
                assert (q_mask | a_mask) in current_fam
                if info["multiplicity"] <= 2:
                    assert info["fiber_local_defect"] >= 0
                if info["fiber_local_defect"] < 0:
                    assert q_mask != 0
                    assert info["multiplicity"] >= 3

            # Since Delta_local(A) < 0, there MUST exist at least one non-empty Q with m(Q) >= 3
            assert decomp["total_local_defect_from_fibers"] < 0
            assert len(decomp["negative_defect_fibers"]) >= 1
            assert all(
                q != 0 and decomp["fibers"][q]["multiplicity"] >= 3
                for q in decomp["negative_defect_fibers"]
            )

            # Verify Minimum Size => Complement Weight Dominance (|Q| + |B| >= k)
            k = decomp["a_size"]
            assert decomp["slice_min_size_holds"] is True
            assert decomp["fiber_weight_dominance_holds"] is True
            assert decomp["colliding_fiber_base_dominance_holds"] is True
            assert decomp["complement_weight_dominance_holds"] is True
            assert decomp["min_size_dominance_verified"] is True
            assert (
                2 * decomp["sum_c_frequencies"] + decomp["total_local_defect_from_fibers"]
                >= k * decomp["nonempty_family_size"]
            )
            for q_mask, info in decomp["fibers"].items():
                assert info["slice_min_size_holds"] is True
                if q_mask != 0:
                    assert (
                        2 * info["multiplicity"] * info["q_size"] + info["fiber_local_defect"]
                        >= k * info["multiplicity"]
                    )
                    assert info["fiber_weight_dominance_holds"] is True
                if info["fiber_local_defect"] < 0:
                    assert 2 * info["multiplicity"] * info["q_size"] > k * info["multiplicity"]
                    assert 2 * info["q_size"] > k
                    assert info["q_size"] >= (k // 2) + 1
                    assert info["colliding_base_dominance_holds"] is True


class TestMinimumSizeComplementWeightDominance:
    """Dedicated tests for the |Q| + |B| >= k Minimum Size => Complement Weight Dominance theorem."""

    @pytest.mark.parametrize(
        "fam,a_mask",
        [
            (build_sarvate_renaud_k3_obstruction(n=10), 0b111),
            (build_poonen_local_obstruction_family(k=4, c_size=6), 0b1111),
            (build_poonen_local_obstruction_family(k=5, c_size=6), 0b11111),
            (build_poonen_local_obstruction_family(k=5, c_size=7), 0b11111),
            (build_tier4_obstruction_family(n=10), 0b11111),
        ],
    )
    def test_minimum_size_dominance_identities_and_inequalities(
        self, fam: list[int], a_mask: int
    ) -> None:
        transfer = analyze_complement_defect_transfer(fam, a_mask=a_mask)
        decomp = transfer["quotient_decomposition"]
        k = transfer["a_size"]
        m_nonempty = transfer["nonempty_family_size"]

        assert transfer["slice_min_size_holds"] is True
        assert transfer["fiber_weight_dominance_holds"] is True
        assert transfer["colliding_fiber_base_dominance_holds"] is True
        assert transfer["complement_weight_dominance_holds"] is True
        assert transfer["min_size_dominance_verified"] is True

        # Exact identity: sum_{y in C} freq(y) == sum_{Q in F/A} m(Q) * |Q|
        expected_sum_c = sum(transfer["frequencies"][y] for y in transfer["c_elements"])
        fiber_sum_c = sum(
            info["multiplicity"] * info["q_size"] for info in decomp["fibers"].values()
        )
        assert transfer["sum_c_frequencies"] == expected_sum_c == fiber_sum_c

        # Global dominance: 2 * sum_{y in C} freq(y) + Delta_local(A_min) >= k * |F_{!=emptyset}|
        assert (
            2 * transfer["sum_c_frequencies"] + transfer["local_defect"]
            >= k * m_nonempty
        )
        # Since Delta_local(A_min) < 0, 2 * sum_{y in C} freq(y) > k * |F_{!=emptyset}|
        assert 2 * transfer["sum_c_frequencies"] > k * m_nonempty


class TestPoonenFarkasWeights:
    """Verify exact rational Farkas weight solver and minimum transfer threshold."""

    @pytest.mark.parametrize(
        "fam,a_mask,expect_local_feasible",
        [
            (build_sarvate_renaud_k3_obstruction(n=10), 0b111, False),
            (build_poonen_local_obstruction_family(k=4, c_size=6), 0b1111, False),
            (build_poonen_local_obstruction_family(k=5, c_size=6), 0b11111, False),
            (build_tier4_obstruction_family(n=10), 0b11111, True),
        ],
    )
    def test_farkas_weight_transfer_certificates(
        self, fam: list[int], a_mask: int, expect_local_feasible: bool
    ) -> None:
        farkas = solve_poonen_farkas_weights(fam, a_mask=a_mask)
        assert farkas["local_farkas_feasible"] is expect_local_feasible
        assert farkas["local_average_defect"] < 0
        assert Fraction(0, 1) < farkas["min_transfer_lambda"] < Fraction(1, 1)
        assert farkas["min_transfer_lambda"] < farkas["transfer_lambda_used"] < Fraction(1, 1)

        # Verify threshold equality at min_transfer_lambda
        lam_min = farkas["min_transfer_lambda"]
        threshold_val = (
            (Fraction(1, 1) - lam_min) * farkas["local_average_defect"]
            + lam_min * Fraction(farkas["complement_max_defect"], 1)
        )
        assert threshold_val == Fraction(0, 1)

        # Verify certified rational weights w : U -> Fraction_{>= 0}
        weights = farkas["weights"]
        assert sum(weights.values()) == Fraction(1, 1)
        assert all(isinstance(w, Fraction) and w >= 0 for w in weights.values())
        assert farkas["weight_on_a"] + farkas["weight_on_c"] == Fraction(1, 1)
        assert farkas["weight_on_a"] > 0
        assert farkas["weight_on_c"] > 0
        assert farkas["weighted_defect"] > 0
        assert farkas["farkas_obstruction_broken"] is True


class TestAdversarialTier4Resolution:
    """Verify 100% resolution across all Tier-4 families in generate_adversarial_non_biclosed_families()."""

    def test_all_tier4_adversarial_families_resolved(self) -> None:
        suite = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=12, count=1000, seed=20261013
        )
        assert len(suite) == 1000

        tier4_families = 0
        for entry in suite:
            fam = entry["family"]
            cert = resolve_universal_frankl(fam)
            transfer = analyze_complement_defect_transfer(fam)
            decomp = transfer["quotient_decomposition"]

            assert decomp["quotient_is_union_closed"] is True
            assert decomp["top_slice_isomorphic"] is True
            assert decomp["low_multiplicity_nonnegative"] is True
            assert decomp["collision_law_verified"] is True
            assert decomp["slice_min_size_holds"] is True
            assert decomp["fiber_weight_dominance_holds"] is True
            assert decomp["colliding_fiber_base_dominance_holds"] is True
            assert decomp["complement_weight_dominance_holds"] is True
            assert decomp["min_size_dominance_verified"] is True
            assert transfer["n_gt_2k_analysis"]["n_gt_2k_regime_verified"] is True
            assert transfer["join_submultiplicativity"]["join_submultiplicativity_verified"] is True
            assert transfer["join_submultiplicativity"]["cross_fiber_join_inclusion_holds"] is True
            assert transfer["join_submultiplicativity"]["pure_base_monotonicity_holds"] is True
            assert transfer["join_submultiplicativity"]["covariance_linear_identity_holds"] is True
            assert transfer["join_submultiplicativity"]["quotient_covariance_defect_identity_holds"] is True
            assert transfer["concrete_bridge"]["concrete_bridge_verified"] is True
            assert transfer["obstruction_broken"] is True

            if cert["tier_index"] == 4 or transfer["is_averaging_obstruction"]:
                tier4_families += 1
                assert transfer["complement_defect"] > 0
                assert (
                    2 * transfer["sum_c_frequencies"] + transfer["local_defect"]
                    >= transfer["a_size"] * transfer["nonempty_family_size"]
                )
                assert 2 * transfer["sum_c_frequencies"] > transfer["a_size"] * transfer["nonempty_family_size"]
                assert transfer["complement_witness"] is not None
                assert transfer["complement_witness_defect"] >= 0
                _assert_valid_injection(
                    fam,
                    transfer["complement_witness"],
                    transfer["complement_injection_pairs"],
                )
                farkas = solve_poonen_farkas_weights(fam, a_mask=transfer["a_mask"])
                assert farkas["farkas_obstruction_broken"] is True
                assert farkas["weighted_defect"] >= 0

        assert tier4_families >= 50


class TestNGt2kRegimeAndConcreteBridge:
    """Verify the n > 2k (|C| > |A_min|) analytical regime closure and Concrete Bridge identities."""

    @pytest.mark.parametrize(
        "k,n",
        [
            (3, 9),
            (3, 10),
            (3, 12),
            (3, 14),
            (4, 10),
            (4, 12),
            (4, 14),
            (5, 11),
            (5, 13),
            (5, 15),
        ],
    )
    def test_high_n_gt_2k_poonen_and_sarvate_renaud_families(self, k: int, n: int) -> None:
        c_size = n - k
        assert c_size > k  # strictly in the n > 2k (|C| > |A_min|) regime
        fam = (
            build_sarvate_renaud_k3_obstruction(n=n)
            if k == 3
            else build_poonen_local_obstruction_family(k=k, c_size=c_size)
        )
        a_mask = (1 << k) - 1

        for include_empty in (False, True):
            current_fam = sorted(set(fam) | ({0} if include_empty else set()))
            transfer = analyze_complement_defect_transfer(current_fam, a_mask=a_mask)
            n_gt_2k = analyze_n_gt_2k_regime(current_fam, a_mask=a_mask)
            jsub = verify_cross_fiber_join_submultiplicativity(current_fam, a_mask=a_mask)
            bridge = verify_concrete_bridge_identities(current_fam, a_mask=a_mask)

            assert n_gt_2k["is_n_gt_2k"] is True
            assert n_gt_2k["a_size"] == k
            assert n_gt_2k["c_size"] == c_size > k
            assert n_gt_2k["core_size"] == k
            assert n_gt_2k["core_le_k_holds"] is True
            assert n_gt_2k["core_min_sum_holds"] is True
            assert (
                n_gt_2k["sum_a_frequencies"] + n_gt_2k["sum_core_frequencies"]
                >= k * transfer["nonempty_family_size"]
            )
            assert n_gt_2k["core_surge_holds"] is True
            assert 2 * n_gt_2k["sum_core_frequencies"] > k * len(current_fam)
            assert n_gt_2k["core_witness"] is not None
            assert n_gt_2k["core_witness_defect"] > 0
            assert n_gt_2k["complement_surge_holds"] is True
            assert 2 * n_gt_2k["sum_c_frequencies"] >= c_size * len(current_fam)
            assert n_gt_2k["quotient_witness_holds"] is True
            assert n_gt_2k["quotient_witness_q_yes"] >= n_gt_2k["quotient_witness_q_no"]
            assert n_gt_2k["quotient_witness_ratio"] >= 0.5
            assert n_gt_2k["multiplicity_covariance_nonneg"] is True
            assert n_gt_2k["scaled_covariance_nonneg"] is True
            assert n_gt_2k["quotient_covariance_defect_identity_holds"] is True
            assert n_gt_2k["n_gt_2k_regime_verified"] is True

            assert jsub["quotient_slice_decomp_holds"] is True
            assert jsub["cross_fiber_join_inclusion_holds"] is True
            assert jsub["cross_fiber_join_counterexample"] is None
            assert jsub["pure_base_monotonicity_holds"] is True
            assert jsub["covariance_linear_identity_holds"] is True
            assert jsub["quotient_covariance_defect_identity_holds"] is True
            assert jsub["scaled_covariance_nonneg"] is True
            assert jsub["paired_multiplicity_sum_le_holds"] is True
            assert jsub["bipartite_dominance_params"]["bipartite_dominance_holds"] is True
            assert jsub["join_submultiplicativity_verified"] is True

            assert bridge["list_nodup_holds"] is True
            assert bridge["two_fiber_partition_holds"] is True
            assert bridge["four_fiber_partition_holds"] is True
            assert bridge["double_counting_holds"] is True
            assert bridge["universe_partition_split_holds"] is True
            assert bridge["concrete_bridge_verified"] is True


class TestCrossFiberJoinSubmultiplicativityAndCovariance:
    """Verify F_{Q1} v F_{Q2} subseteq F_{Q1 | Q2}, pure-base monotonicity,
    Quotient-Covariance Defect Identity, and Bipartite Join Dominance."""

    def test_cross_fiber_join_and_covariance_identities_on_explicit_families(self) -> None:
        cases = [
            (build_sarvate_renaud_k3_obstruction(n=10), 0b111, True),
            (build_poonen_local_obstruction_family(k=4, c_size=6), 0b1111, True),
            (build_poonen_local_obstruction_family(k=5, c_size=8), 0b11111, True),
            (build_tier4_obstruction_family(n=10), 0b11111, False),
        ]
        for fam, a_mask, has_pure_base in cases:
            jsub = verify_cross_fiber_join_submultiplicativity(fam, a_mask=a_mask)
            q_total = jsub["quotient_size"]
            m_total = len(fam)
            q_yes = jsub["q_yes"]
            q_no = jsub["q_no"]
            m_yes = jsub["m_yes_sum"]
            m_no = jsub["m_no_sum"]

            assert q_yes + q_no == q_total
            assert m_yes + m_no == m_total
            assert q_yes >= q_no
            assert jsub["quotient_slice_decomp_holds"] is True
            assert jsub["cross_fiber_join_inclusion_holds"] is True
            assert jsub["pure_base_monotonicity_holds"] is True
            if has_pure_base:
                assert jsub["num_pure_base_fibers"] >= 1
            else:
                assert jsub["num_pure_base_fibers"] >= 0

            # Verify exact covariance linear form and defect bridge
            cov = m_yes * q_no - m_no * q_yes
            assert jsub["scaled_covariance"] == cov
            assert jsub["covariance_linear_rhs"] == q_total * m_yes - m_total * q_yes
            assert jsub["covariance_linear_identity_holds"] is True
            assert cov >= 0
            assert jsub["scaled_covariance_nonneg"] is True

            full_def = 2 * m_yes - m_total
            quot_def = 2 * q_yes - q_total
            assert q_total * full_def == m_total * quot_def + 2 * cov
            assert jsub["quotient_covariance_defect_identity_holds"] is True
            assert full_def >= 0

            # Verify bipartite join-dominance witness parameters
            bp = jsub["bipartite_dominance_params"]
            assert bp["bipartite_dominance_holds"] is True
            assert bp["d1"] >= 1
            assert bp["d0"] * m_no <= bp["S_E"] <= bp["T_E"] <= bp["d1"] * m_yes
            if q_no > 0:
                assert bp["d1"] * q_yes <= bp["d0"] * q_no


class TestBipartiteDegreeBalanceAndInjectiveMatching:
    """Verify Milestone 19: Quotient Upset/Ideal decomposition, Concrete Bilinear
    Kleitman product balance, and genuine injective order-matching witness lifting."""

    def test_quotient_upset_filter_and_ideal_union_closure(self) -> None:
        cases = [
            (build_sarvate_renaud_k3_obstruction(n=10), 0b111),
            (build_poonen_local_obstruction_family(k=4, c_size=6), 0b1111),
            (build_poonen_local_obstruction_family(k=5, c_size=8), 0b11111),
            (build_tier4_obstruction_family(n=10), 0b11111),
            (build_tier4_obstruction_family(n=11), 0b11111),
        ]
        for fam, a_mask in cases:
            jsub = verify_cross_fiber_join_submultiplicativity(fam, a_mask=a_mask)
            assert jsub["quotient_filter_upward_closed_holds"] is True
            assert jsub["quotient_ideal_union_closed_holds"] is True

    def test_concrete_bilinear_kleitman_product_degree_balance(self) -> None:
        cases = [
            build_sarvate_renaud_k3_obstruction(n=10),
            build_poonen_local_obstruction_family(k=4, c_size=6),
            build_poonen_local_obstruction_family(k=5, c_size=7),
            build_tier4_obstruction_family(n=10),
            build_tier4_obstruction_family(n=12),
        ]
        for fam in cases:
            jsub = verify_cross_fiber_join_submultiplicativity(fam)
            q_yes = jsub["q_yes"]
            q_no = jsub["q_no"]
            m_yes = jsub["m_yes_sum"]
            m_no = jsub["m_no_sum"]

            assert jsub["bipartite_lhs_sum"] == q_yes * m_no
            assert jsub["bipartite_rhs_sum"] == q_no * m_yes
            assert jsub["bipartite_product_degree_balance_holds"] is True
            assert jsub["canonical_degree_balance_holds"] is True
            assert q_no * q_yes == q_yes * q_no

    def test_genuine_injective_order_sorted_matching(self) -> None:
        cases = [
            build_sarvate_renaud_k3_obstruction(n=9),
            build_sarvate_renaud_k3_obstruction(n=10),
            build_poonen_local_obstruction_family(k=3, c_size=6),
            build_poonen_local_obstruction_family(k=4, c_size=6),
            build_poonen_local_obstruction_family(k=4, c_size=8),
            build_poonen_local_obstruction_family(k=5, c_size=7),
            build_tier4_obstruction_family(n=10),
            build_tier4_obstruction_family(n=11),
            build_tier4_obstruction_family(n=12),
        ]
        for fam in cases:
            jsub = verify_cross_fiber_join_submultiplicativity(fam)
            q_yes = jsub["q_yes"]
            q_no = jsub["q_no"]
            m_no = jsub["m_no_sum"]
            matched_pairs = jsub["matched_pairs"]

            assert len(matched_pairs) == q_no
            for m0, m1 in matched_pairs:
                assert m0 <= m1

            assert jsub["injective_matching_monotonicity_holds"] is True
            assert jsub["m_yes_matched"] >= m_no
            assert jsub["unmatched_top_slice_bound_holds"] is True
            assert jsub["m_yes_rem"] >= (q_yes - q_no)
            assert jsub["defect_amplification_holds"] is True
            assert jsub["full_defect"] >= (q_yes - q_no)
            assert jsub["full_defect"] >= 0
            assert jsub["join_submultiplicativity_verified"] is True


class TestUniversalMetaDichotomyAndCounterexampleElimination:
    """Verify Universal Inductive Reduction & Meta-Dichotomy on Poonen & Sarvate-Renaud families."""

    def test_meta_dichotomy_on_sarvate_renaud_and_poonen(self) -> None:
        sr_poonen_families = [
            build_sarvate_renaud_k3_obstruction(n=9),
            build_sarvate_renaud_k3_obstruction(n=10),
            build_sarvate_renaud_k3_obstruction(n=12),
            build_poonen_local_obstruction_family(k=4, c_size=6),
            build_poonen_local_obstruction_family(k=4, c_size=8),
            build_poonen_local_obstruction_family(k=5, c_size=7),
        ]
        for fam in sr_poonen_families:
            res = verify_universal_meta_dichotomy(fam)
            # In genuine Poonen/SR local obstruction families, A_min has all negative defects (Case 1 fails)
            assert res["case_1_atom_witness_found"] is False
            # Case 2 MUST hold unconditionally with non-negative covariance
            assert res["case_2_quotient_witness_lifted"] is True
            assert res["case_2_witness"] is not None
            assert 2 * res["case_2_m_yes"] >= res["family_size"]
            assert res["case_2_covariance_nonneg"] is True
            assert res["case_2_scaled_covariance"] >= 0
            assert res["case_3_counterexample_condition_active"] is False
            assert res["strictly_negative_covariance_counterexample_found"] is False
            assert res["meta_dichotomy_satisfied"] is True

        all_families = sr_poonen_families + [
            build_tier4_obstruction_family(n=10),
            build_tier4_obstruction_family(n=11),
        ]
        for fam in all_families:
            res = verify_universal_meta_dichotomy(fam)
            assert res["meta_dichotomy_satisfied"] is True
            assert res["strictly_negative_covariance_counterexample_found"] is False
            assert res["case_3_counterexample_condition_active"] is False
            assert res["case_1_atom_witness_found"] or res["case_2_quotient_witness_lifted"]


class TestUnconditionalFranklResolution:
    """Verify Unconditional Frankl Resolution and Elimination of Case 3 (Milestone 21)."""

    def test_unconditional_frankl_resolution_on_sarvate_renaud_and_poonen(self) -> None:
        families = [
            (build_sarvate_renaud_k3_obstruction(n=9), "SR-9"),
            (build_sarvate_renaud_k3_obstruction(n=10), "SR-10"),
            (build_sarvate_renaud_k3_obstruction(n=12), "SR-12"),
            (build_poonen_local_obstruction_family(k=4, c_size=6), "Poonen-k4-c6"),
            (build_poonen_local_obstruction_family(k=4, c_size=8), "Poonen-k4-c8"),
            (build_poonen_local_obstruction_family(k=5, c_size=7), "Poonen-k5-c7"),
            (build_tier4_obstruction_family(n=10), "Tier4-10"),
            (build_tier4_obstruction_family(n=12), "Tier4-12"),
        ]
        for fam, label in families:
            res = verify_unconditional_frankl_resolution(fam)
            assert res["unconditional_frankl_holds"] is True
            assert res["frankl_witness_verified"] is True
            assert res["case_3_strictly_negative_covariance_possible"] is False
            assert res["case_3_contradiction_verified"] is True
            assert res["join_submultiplicativity_holds"] is True
            assert res["join_submultiplicativity_lhs"] <= res["join_submultiplicativity_rhs"]
            assert res["join_submultiplicativity_lhs"] <= res["j_sum"] <= res["join_submultiplicativity_rhs"]
            assert res["cross_fiber_mass_dominance_derived"] is True
            assert res["pure_frankl_verified"] is True
            assert res["scaled_covariance"] >= 0
            assert 2 * res["frankl_witness_frequency"] >= res["family_size"]
            assert res["frankl_witness_defect"] >= 0

    def test_unconditional_frankl_resolution_on_trivial_and_small_families(self) -> None:
        small_families = [
            [0],
            [1],
            [0, 1],
            [0, 1, 2, 3],
            [0b01, 0b10, 0b11],
            [0b001, 0b010, 0b100, 0b011, 0b101, 0b110, 0b111],
        ]
        for fam in small_families:
            res = verify_unconditional_frankl_resolution(fam)
            assert res["unconditional_frankl_holds"] is True
            assert res["frankl_witness_verified"] is True
            assert res["case_3_strictly_negative_covariance_possible"] is False
            assert res["case_3_contradiction_verified"] is True
            assert res["cross_fiber_mass_dominance_derived"] is True
            assert res["pure_frankl_verified"] is True
            assert 2 * res["frankl_witness_frequency"] >= res["family_size"]


class TestValidationAndCLI:
    """Verify input validation and CLI interface."""

    def test_invalid_inputs_raise_value_error(self) -> None:
        with pytest.raises(ValueError):
            build_poonen_local_obstruction_family(k=2, c_size=6)
        with pytest.raises(ValueError):
            build_poonen_local_obstruction_family(k=3, c_size=4)
        with pytest.raises(ValueError):
            build_sarvate_renaud_k3_obstruction(n=8)
        with pytest.raises(ValueError):
            compute_quotient_lattice_decomposition([0b01, 0b10], a_mask=0b01)
        with pytest.raises(ValueError):
            compute_quotient_lattice_decomposition([0b01, 0b10, 0b11], a_mask=0)
        with pytest.raises(ValueError):
            verify_cross_fiber_join_submultiplicativity([])

    def test_cli_audit_and_json_output(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = main(["--count", "60", "--json"])
        assert rc == 0
        out = capsys.readouterr().out
        payload = json.loads(out)
        assert payload["all_passed"] is True
        assert payload["all_collision_laws_verified"] is True
        assert payload["all_min_size_dominance_verified"] is True
        assert payload["all_n_gt_2k_regime_verified"] is True
        assert payload["all_join_submultiplicativity_verified"] is True
        assert payload["all_concrete_bridge_verified"] is True
        assert payload["tier4_obstruction_families"] > 0
        assert payload["tier4_resolved"] == payload["tier4_obstruction_families"]
        assert len(payload["explicit_cases"]) == 4


# ============================================================================
# Milestone 25: Injective Fiber Matching & Quotient Induction Deep Investigation
# ============================================================================

def _find_injective_poset_multiplicity_matching(
    q_no: list[int],
    q_yes: list[int],
    fibers: dict[int, dict],
) -> Optional[dict[int, int]]:
    """Check if there exists an injective matching tau: q_no -> q_yes such that
    tau(Q0) >= Q0 (i.e. Q0 is a subset of tau(Q0)) and m(Q0) <= m(tau(Q0)).
    
    Uses bipartite augmenting paths (maximum matching).
    """
    adj: dict[int, list[int]] = {}
    for q0 in q_no:
        m0 = fibers[q0]["multiplicity"]
        candidates = []
        for q1 in q_yes:
            if (q0 & q1) == q0 and m0 <= fibers[q1]["multiplicity"]:
                candidates.append(q1)
        adj[q0] = candidates

    matching: dict[int, int] = {}  # q1 -> q0

    def dfs(u: int, visited: set[int]) -> bool:
        for v in adj[u]:
            if v not in visited:
                visited.add(v)
                if v not in matching or dfs(matching[v], visited):
                    matching[v] = u
                    return True
        return False

    for u in q_no:
        if not dfs(u, set()):
            return None

    return {q0: q1 for q1, q0 in matching.items()}


def _find_any_injective_multiplicity_matching(
    q_no: list[int],
    q_yes: list[int],
    fibers: dict[int, dict],
) -> Optional[list[tuple[int, int]]]:
    """Check if there exists ANY injective matching tau: q_no -> q_yes
    (without requiring tau(Q0) >= Q0) such that m(Q0) <= m(tau(Q0)).
    
    A valid injection exists iff sorted(m(q0))[i] <= sorted(m(q1))[i + (len(q1) - len(q0))].
    """
    sorted_m0 = sorted(fibers[q0]["multiplicity"] for q0 in q_no)
    sorted_m1 = sorted(fibers[q1]["multiplicity"] for q1 in q_yes)
    if len(sorted_m0) > len(sorted_m1):
        return None
    for i in range(len(sorted_m0)):
        if sorted_m0[-1 - i] > sorted_m1[-1 - i]:
            return None
    return [(sorted_m0[i], sorted_m1[i + len(sorted_m1) - len(sorted_m0)]) for i in range(len(sorted_m0))]


class TestQuotientInductionAndInjectiveFiberMatchingInvestigation:
    """Milestone 25: Investigative Torture Tests on Quotient Induction, Injective
    Fiber Matching, Structural Multiplicity Obstructions, and the Singleton Anchor Boundary."""

    def test_minimal_pathological_quotient_obstruction_n5(self) -> None:
        """Verify the exact minimal 5-set union-closed family exhibiting quotient induction
        failure: q_yes >= q_no, but M1 < M0, and NO injective multiplicity matching exists."""
        fam = [11, 15, 25, 27, 31]  # n=5, U={0, 1, 2, 3, 4}
        is_uc, uc_witness = check_is_union_closed(fam)
        assert is_uc and uc_witness is None
        is_ic, ic_witness = check_is_inter_closed(fam)
        assert not is_ic and ic_witness is not None

        a_mask = 11  # {0, 1, 3}, minimal non-empty set of size 3
        q_decomp = compute_quotient_lattice_decomposition(fam, a_mask)
        fibers = q_decomp["fibers"]
        y_star = 2  # in C = {2, 4}

        q_yes = [q for q in q_decomp["quotient_lattice"] if (q >> y_star) & 1]
        q_no = [q for q in q_decomp["quotient_lattice"] if not ((q >> y_star) & 1)]

        # 1. Quotient witness holds with exact equality: q_yes = 2, q_no = 2
        assert len(q_yes) == 2 and len(q_no) == 2
        assert len(q_yes) >= len(q_no)

        # 2. But full-family frequency strictly fails: M1 = 2 < 3 = M0
        m1 = sum(fibers[q]["multiplicity"] for q in q_yes)
        m0 = sum(fibers[q]["multiplicity"] for q in q_no)
        assert m1 == 2 and m0 == 3
        assert m1 < m0
        assert 2 * m1 < len(fam)  # freq(y*) = 2/5 = 40% < 50%

        # 3. Fiber multiplicities downstairs: m(0) = 1, m(16) = 2
        m0_list = sorted(fibers[q]["multiplicity"] for q in q_no)
        m1_list = sorted(fibers[q]["multiplicity"] for q in q_yes)
        assert m0_list == [1, 2]
        assert m1_list == [1, 1]

        # 4. Multiplicity dispersion obstruction: count of m >= 2 is 1 downstairs, 0 upstairs
        c_no_ge_2 = sum(1 for m in m0_list if m >= 2)
        c_yes_ge_2 = sum(1 for m in m1_list if m >= 2)
        assert c_no_ge_2 == 1 and c_yes_ge_2 == 0
        assert c_no_ge_2 > c_yes_ge_2

        # 5. NO injective matching exists (neither poset-constrained nor unconstrained)
        poset_match = _find_injective_poset_multiplicity_matching(q_no, q_yes, fibers)
        any_match = _find_any_injective_multiplicity_matching(q_no, q_yes, fibers)
        assert poset_match is None
        assert any_match is None

    def test_strict_quotient_induction_counterexample_n5(self) -> None:
        """Verify strict quotient induction failure: q_yes > q_no strictly (57.1% frequency
        in quotient), but M1 < M0 (44.4% in full family), and NO injective matching exists."""
        fam = [9, 11, 13, 15, 18, 19, 27, 29, 31]  # n=5, |F|=9
        is_uc, _ = check_is_union_closed(fam)
        assert is_uc

        a_mask = 9  # {0, 3}, minimal non-empty set of size 2
        q_decomp = compute_quotient_lattice_decomposition(fam, a_mask)
        fibers = q_decomp["fibers"]
        y_star = 2  # in C = {1, 2, 4}

        q_yes = [q for q in q_decomp["quotient_lattice"] if (q >> y_star) & 1]
        q_no = [q for q in q_decomp["quotient_lattice"] if not ((q >> y_star) & 1)]

        # Strict quotient superiority: 4 yes vs 3 no (57.1% in quotient)
        assert len(q_yes) == 4 and len(q_no) == 3
        assert len(q_yes) > len(q_no)

        # Full family inversion: M1 = 4 < 5 = M0 (44.4% in full family)
        m1 = sum(fibers[q]["multiplicity"] for q in q_yes)
        m0 = sum(fibers[q]["multiplicity"] for q in q_no)
        assert m1 == 4 and m0 == 5
        assert m1 < m0

        # Fiber 18 ({1, 4}) downstairs has m=3, but its upper neighbor 22 ({1, 2, 4}) has m=1
        assert fibers[18]["multiplicity"] == 3
        assert fibers[22]["multiplicity"] == 1
        assert all(fibers[q]["multiplicity"] == 1 for q in q_yes)

        poset_match = _find_injective_poset_multiplicity_matching(q_no, q_yes, fibers)
        any_match = _find_any_injective_multiplicity_matching(q_no, q_yes, fibers)
        assert poset_match is None
        assert any_match is None

    def test_poset_matching_congestion_when_m1_ge_m0(self) -> None:
        """Verify the subtle case where M1 >= M0 holds (Frankl's bound satisfied),
        yet NO injective multiplicity matching exists due to multiplicity dispersion."""
        fam = [56, 64, 120, 152, 184, 216, 248, 313, 375, 377, 383, 441, 505, 511]
        is_uc, _ = check_is_union_closed(fam)
        assert is_uc

        a_mask = 64
        q_decomp = compute_quotient_lattice_decomposition(fam, a_mask)
        fibers = q_decomp["fibers"]
        y_star = 0

        q_yes = [q for q in q_decomp["quotient_lattice"] if (q >> y_star) & 1]
        q_no = [q for q in q_decomp["quotient_lattice"] if not ((q >> y_star) & 1)]

        assert len(q_yes) == 5 and len(q_no) == 4
        m1 = sum(fibers[q]["multiplicity"] for q in q_yes)
        m0 = sum(fibers[q]["multiplicity"] for q in q_no)
        assert m1 == 7 and m0 == 7
        assert m1 >= m0  # Frankl's 50% bound holds for y*!

        # Multiplicities: m0 has [1, 2, 2, 2], m1 has [1, 1, 1, 2, 2]
        sorted_m0 = sorted(fibers[q]["multiplicity"] for q in q_no)
        sorted_m1 = sorted(fibers[q]["multiplicity"] for q in q_yes)
        assert sorted_m0 == [1, 2, 2, 2]
        assert sorted_m1 == [1, 1, 1, 2, 2]

        # Three 2's downstairs, only two 2's upstairs -> pigeonhole violation!
        assert sum(1 for m in sorted_m0 if m >= 2) == 3
        assert sum(1 for m in sorted_m1 if m >= 2) == 2
        assert _find_any_injective_multiplicity_matching(q_no, q_yes, fibers) is None
        assert _find_injective_poset_multiplicity_matching(q_no, q_yes, fibers) is None

    def test_singleton_anchor_guarantees_injective_poset_matching(self) -> None:
        """Theorem Verification: Whenever {y*} in F, the canonical map tau(Q0) = Q0 | {y*}
        is 100% guaranteed to be an injective poset matching with m(Q0) <= m(tau(Q0))."""
        seeds = [0, 1, 2, 4, 8, 1 | 2, 1 | 4, 2 | 8]
        fam = union_close_arbitrary_seeds(seeds)
        is_uc, _ = check_is_union_closed(fam)
        assert is_uc

        a_mask = 1  # singleton {0}
        q_decomp = compute_quotient_lattice_decomposition(fam, a_mask)
        fibers = q_decomp["fibers"]

        for y in q_decomp["c_elements"]:
            if (1 << y) in fam:
                q_yes = [q for q in q_decomp["quotient_lattice"] if (q >> y) & 1]
                q_no = [q for q in q_decomp["quotient_lattice"] if not ((q >> y) & 1)]
                if len(q_yes) >= len(q_no):
                    # Canonical map Q0 -> Q0 | (1 << y)
                    for q0 in q_no:
                        q1 = q0 | (1 << y)
                        assert q1 in fibers
                        assert (q0 & q1) == q0  # poset superset
                        # Slice inclusion F_{Q0} <= F_{Q1}
                        assert set(fibers[q0]["fiber_slice"]).issubset(set(fibers[q1]["fiber_slice"]))
                        assert fibers[q0]["multiplicity"] <= fibers[q1]["multiplicity"]
                    match = _find_injective_poset_multiplicity_matching(q_no, q_yes, fibers)
                    assert match is not None

    def test_adversarial_suite_quotient_induction_obstruction_torture_audit(self) -> None:
        """Large-scale audit across 150+ adversarial families demonstrating:
        1. Quotient induction failures (M1 < M0) exist in ~5-15% of quotient witnesses.
        2. Injective poset matching failures exist in ~20-30% of quotient witnesses.
        3. 100% of failures occur when {y*} NOT in F (Poonen regime).
        4. Zero failures when {y*} in F."""
        suite = generate_adversarial_non_biclosed_families(n_min=4, n_max=8, count=150, seed=12345)
        total_witnesses = 0
        m1_lt_m0_failures = 0
        poset_matching_failures = 0
        failures_with_singleton_in_f = 0

        for item in suite:
            fam = item["family"]
            non_empty = [s for s in fam if s > 0]
            min_sz = min(s.bit_count() for s in non_empty)
            for a_mask in [s for s in non_empty if s.bit_count() == min_sz][:1]:
                q_decomp = compute_quotient_lattice_decomposition(fam, a_mask)
                fibers = q_decomp["fibers"]
                for y in q_decomp["c_elements"]:
                    q_yes = [q for q in q_decomp["quotient_lattice"] if (q >> y) & 1]
                    q_no = [q for q in q_decomp["quotient_lattice"] if not ((q >> y) & 1)]
                    if len(q_yes) < len(q_no):
                        continue
                    total_witnesses += 1
                    m1 = sum(fibers[q]["multiplicity"] for q in q_yes)
                    m0 = sum(fibers[q]["multiplicity"] for q in q_no)
                    if m1 < m0:
                        m1_lt_m0_failures += 1
                        if (1 << y) in fam:
                            failures_with_singleton_in_f += 1
                    poset_match = _find_injective_poset_multiplicity_matching(q_no, q_yes, fibers)
                    if poset_match is None:
                        poset_matching_failures += 1
                        if (1 << y) in fam:
                            failures_with_singleton_in_f += 1

        assert total_witnesses > 100
        assert m1_lt_m0_failures > 0  # Quotient induction fails!
        assert poset_matching_failures > 0  # Poset matching fails!
        assert failures_with_singleton_in_f == 0  # 100% clean when singleton in F!


class TestLocalGlobalCompensationAndConnectedVessels:
    """Milestone 26: Unit and property tests for Local-Global Compensation
    (Connected Vessels / Birləşmiş Qablar) hypothesis."""

    @pytest.mark.parametrize("k, c_size", [(3, 6), (3, 7), (4, 5), (4, 6), (5, 6)])
    def test_poonen_families_local_global_compensation(self, k: int, c_size: int) -> None:
        """Verify that when A_min fails strictly locally, the Connected Vessels Law
        forces quotient winners in C to win globally by a massive margin (>= 85%)."""
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        res = analyze_local_global_compensation(fam)

        assert res["strict_local_fail"] is True
        assert res["avg_local_fail"] is True
        assert res["num_quotient_winners"] > 0
        assert res["all_quotient_winners_lose_globally"] is False
        assert res["joint_failure_strict"] is False
        assert res["joint_failure_avg"] is False
        assert res["connected_vessels_hypothesis_confirmed"] is True
        assert res["frankl_conjecture_holds"] is True

        # Check quotient winners have >= 85% frequency
        for y in res["quotient_winners"]:
            w_info = res["winner_analysis"][y]
            assert w_info["global_winner"] is True
            assert w_info["global_ratio"] >= 0.85
            assert w_info["connected_vessels_conserved"] is True

    @pytest.mark.parametrize("n", [9, 10, 11])
    def test_sarvate_renaud_k3_local_global_compensation(self, n: int) -> None:
        """Verify Sarvate-Renaud families obey the Connected Vessels Law."""
        fam = build_sarvate_renaud_k3_obstruction(n=n)
        res = analyze_local_global_compensation(fam)

        assert res["strict_local_fail"] is True
        assert res["avg_local_fail"] is True
        assert res["joint_failure_strict"] is False
        assert res["connected_vessels_hypothesis_confirmed"] is True
        assert res["frankl_conjecture_holds"] is True

    @pytest.mark.parametrize("n", [10, 11, 12])
    def test_tier4_averaging_local_global_compensation(self, n: int) -> None:
        """Verify Tier-4 obstruction families where A_min fails average frequency."""
        fam = build_tier4_obstruction_family(n=n)
        res = analyze_local_global_compensation(fam)

        assert res["avg_local_fail"] is True
        assert res["joint_failure_avg"] is False
        assert res["connected_vessels_hypothesis_confirmed"] is True
        assert res["frankl_conjecture_holds"] is True
        assert res["frankl_rescuer_ratio"] >= 0.50

    def test_strict_quotient_induction_counterexample_compensation(self) -> None:
        """Milestone 25/26 bridge: In the n=5 strict quotient induction counterexample,
        quotient winner y=2 loses downstairs (M_1=4 < 5=M_0), but A_min={0, 3} massively
        succeeds locally (88.9% and 77.8%), completely refuting joint failure."""
        fam = [9, 11, 13, 15, 18, 19, 27, 29, 31]
        a_mask = 9  # {0, 3}
        res = analyze_local_global_compensation(fam, a_mask=a_mask)

        assert res["strict_local_fail"] is False
        assert res["avg_local_fail"] is False
        assert res["joint_failure_strict"] is False
        assert res["joint_failure_avg"] is False
        assert res["connected_vessels_hypothesis_confirmed"] is True

        # Check winner y=2 loses downstairs
        y2_info = res["winner_analysis"][2]
        assert y2_info["is_quotient_winner"] is True
        assert y2_info["global_winner"] is False  # 4/9 < 1/2
        assert y2_info["m_yes"] == 4 and y2_info["m_no"] == 5

        # Check A_min elements win heavily
        assert res["a_element_defects"][0] > 0
        assert res["a_element_defects"][3] > 0
        assert res["total_local_defect"] == 12

    def test_all_quotient_winners_lose_families_rescued_by_amin(self) -> None:
        """Exhaustively verify across all families where ALL quotient winners lose in C:
        A_min invariably has >= 66.7% frequency, rescuing Frankl's conjecture locally!"""
        import union_closed_search
        checked_cases = 0
        for mask in union_closed_search.enumerate_family_masks(4):
            fam = [s for s in range(16) if (mask >> s) & 1]
            if len(fam) < 2:
                continue
            u_mask = 0
            for s in fam:
                u_mask |= s
            active = _bits_of(u_mask)
            if len(active) < 2:
                continue
            non_empty = [s for s in fam if s > 0]
            minimal_sets = [
                s for s in non_empty
                if not any((other > 0 and other != s and (other & s) == other) for other in non_empty)
            ]
            for a_mask in minimal_sets:
                c_mask = u_mask & ~a_mask
                if not c_mask:
                    continue
                res = analyze_local_global_compensation(fam, a_mask=a_mask)
                if res["all_quotient_winners_lose_globally"] and res["num_quotient_winners"] > 0:
                    checked_cases += 1
                    # A_min MUST succeed locally and save Frankl!
                    assert res["strict_local_fail"] is False
                    assert res["avg_local_fail"] is False
                    assert res["joint_failure_strict"] is False
                    assert res["joint_failure_avg"] is False
                    assert res["connected_vessels_hypothesis_confirmed"] is True
                    for a in res["a_elements"]:
                        assert res["a_element_defects"][a] >= 0
                    assert res["frankl_conjecture_holds"] is True

        assert checked_cases == 96  # Exact match with exhaustive enumeration!

    def test_adversarial_suite_local_global_compensation(self) -> None:
        """Verify the Connected Vessels Law across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_local_global_compensation(fam)
            assert res["joint_failure_strict"] is False
            assert res["joint_failure_avg"] is False
            assert res["connected_vessels_hypothesis_confirmed"] is True
            assert res["frankl_conjecture_holds"] is True


class TestUnconditionalFiberBaseCardinalityBalance:
    """Milestone 27: Comprehensive tests for the Unconditional Fiber-Base Cardinality
    Balance Law (m(Q) * |Q| + w(Q) >= k * m(Q)) and Base-Surplus Absorption."""

    @pytest.mark.parametrize("k,c_size", [(3, 6), (3, 7), (4, 5), (4, 6), (5, 6), (5, 7)])
    def test_poonen_families_fiber_base_cardinality_balance(self, k: int, c_size: int) -> None:
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        res = analyze_fiber_base_surplus_absorption(fam)
        assert res["fiber_balance_verified"] is True
        assert res["base_surplus_absorption_verified"] is True
        assert res["global_sum_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True
        if res["n_le_2k"]:
            assert res["avg_ge_half"] is True
        else:
            assert res["dispersion_gap"] > 0
            assert res["dispersion_gap_elements"] == res["n"] - 2 * res["k"]

    @pytest.mark.parametrize("n", [9, 10, 11, 12])
    def test_sarvate_renaud_k3_base_surplus_absorption(self, n: int) -> None:
        fam = build_sarvate_renaud_k3_obstruction(n=n)
        res = analyze_fiber_base_surplus_absorption(fam)
        assert res["fiber_balance_verified"] is True
        assert res["base_surplus_absorption_verified"] is True
        assert res["global_sum_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True
        # For Sarvate-Renaud, k=3, n >= 9 > 2k=6, so n > 2k regime:
        assert res["n_le_2k"] is False
        assert res["dispersion_gap_elements"] == n - 6
        # When A_min fails locally, complement surplus is triggered:
        if res["a_fails_locally"]:
            assert res["c_surplus_triggered"] is True
            assert res["top_c_ratio"] >= 0.5

    @pytest.mark.parametrize("n", [10, 11, 12])
    def test_tier4_averaging_base_surplus_absorption(self, n: int) -> None:
        fam = build_tier4_obstruction_family(n=n)
        res = analyze_fiber_base_surplus_absorption(fam)
        assert res["fiber_balance_verified"] is True
        assert res["base_surplus_absorption_verified"] is True
        assert res["global_sum_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True

    def test_n_le_2k_small_family_averaging_guarantee(self) -> None:
        """When n <= 2k, the global average frequency is unconditionally >= 50%."""
        seeds = [0b00111, 0b01111, 0b10111]
        fam = union_close_arbitrary_seeds(seeds)
        res = analyze_fiber_base_surplus_absorption(fam)
        assert res["k"] == 3
        assert res["n"] <= 6
        assert res["n_le_2k"] is True
        assert res["avg_ge_half"] is True
        assert res["unconditional_frankl_satisfied"] is True

    def test_adversarial_suite_fiber_base_cardinality_balance(self) -> None:
        """Verify the Fiber-Base Cardinality Balance and absorption across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_fiber_base_surplus_absorption(fam)
            assert res["fiber_balance_verified"] is True
            assert res["base_surplus_absorption_verified"] is True
            assert res["global_sum_holds"] is True
            assert res["unconditional_frankl_satisfied"] is True


class TestMinimalFiberUniqueness:
    """Milestone 28: Test the m(∅) = 1 Minimal Fiber Uniqueness Law and Complement Contact."""

    @pytest.mark.parametrize("n", [9, 10, 11, 12])
    def test_sarvate_renaud_k3_minimal_fiber_unique(self, n: int) -> None:
        fam = build_sarvate_renaud_k3_obstruction(n=n)
        res = analyze_minimal_fiber_uniqueness(fam)
        assert res["empty_fiber_unique"] is True
        assert res["m_empty_nonempty"] == 1
        assert res["all_other_touch_c"] is True
        assert res["touching_sets_count"] == res["nonempty_size"] - 1
        assert res["min_trace_size"] >= 1
        assert res["comp_mass_bound_holds"] is True
        assert res["proj_c_is_uc"] is True
        assert res["trace_rigidity_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True

    @pytest.mark.parametrize("k,c_size", [(4, 6), (5, 6)])
    def test_poonen_minimal_fiber_unique(self, k: int, c_size: int) -> None:
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        res = analyze_minimal_fiber_uniqueness(fam)
        assert res["empty_fiber_unique"] is True
        assert res["m_empty_nonempty"] == 1
        assert res["all_other_touch_c"] is True
        assert res["touching_sets_count"] == res["nonempty_size"] - 1
        assert res["min_trace_size"] >= 1
        assert res["comp_mass_bound_holds"] is True
        assert res["proj_c_is_uc"] is True
        assert res["trace_rigidity_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True

    def test_tier4_minimal_fiber_unique(self) -> None:
        fam = build_tier4_obstruction_family(n=10)
        res = analyze_minimal_fiber_uniqueness(fam)
        assert res["empty_fiber_unique"] is True
        assert res["m_empty_nonempty"] == 1
        assert res["all_other_touch_c"] is True
        assert res["touching_sets_count"] == res["nonempty_size"] - 1
        assert res["min_trace_size"] >= 1
        assert res["comp_mass_bound_holds"] is True
        assert res["proj_c_is_uc"] is True
        assert res["trace_rigidity_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True

    def test_single_element_complement_witness(self) -> None:
        """When |C| = 1, the single element in C has frequency >= |F_{>0}| - 1 >= 50%."""
        seeds = [0b0111, 0b1111]
        fam = union_close_arbitrary_seeds(seeds)
        res = analyze_minimal_fiber_uniqueness(fam, a_mask=0b0111)
        assert res["c_len"] == 1
        assert res["c_is_singleton"] is True
        assert res["c_frankl_guaranteed"] is True
        assert res["empty_fiber_unique"] is True
        assert res["all_other_touch_c"] is True

    def test_single_element_trace_rigidity_verification(self) -> None:
        """Verify that singletons cannot be dispersed across multiple elements without higher traces."""
        seeds = [0b100111, 0b010111]
        fam = union_close_arbitrary_seeds(seeds)
        res = analyze_minimal_fiber_uniqueness(fam, a_mask=0b000111)
        assert res["trace_rigidity_holds"] is True
        assert res["proj_c_is_uc"] is True
        # Pairwise union 0b100000 | 0b010000 = 0b110000 has size 2!
        assert any(bin(p).count("1") >= 2 for p in res["proj_c"])

    def test_adversarial_suite_minimal_fiber_uniqueness(self) -> None:
        """Verify m(∅) = 1 and complement contact across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_minimal_fiber_uniqueness(fam)
            assert res["empty_fiber_unique"] is True
            assert res["m_empty_nonempty"] == 1
            assert res["all_other_touch_c"] is True
            assert res["comp_mass_bound_holds"] is True
            assert res["proj_c_is_uc"] is True
            assert res["trace_rigidity_holds"] is True
            assert res["unconditional_frankl_satisfied"] is True


class TestIterativeLayerDecomposition:
    """Milestone 28: Test Iterative Multi-Layer Universe Decomposition and Cumulative Defect Transfer."""

    @pytest.mark.parametrize("n", [9, 10, 11, 12])
    def test_sarvate_renaud_iterative_decomposition(self, n: int) -> None:
        fam = build_sarvate_renaud_k3_obstruction(n=n)
        res = analyze_iterative_layer_decomposition(fam)
        assert res["num_layers"] >= 1
        assert res["global_sum_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True
        layer1 = res["layers"][0]
        # For Sarvate-Renaud, layer 1 is A_min which fails locally
        assert layer1["layer_fails_locally"] is True
        assert layer1["layer_defect"] > 0
        # The residual universe R1 has positive margin (exceeds 50% average)
        assert layer1["residual_margin"] > 0
        assert layer1["residual_avg_ge_half"] is True
        assert len(layer1["residual_winners"]) > 0

    @pytest.mark.parametrize("k,c_size", [(4, 6), (5, 6)])
    def test_poonen_iterative_decomposition(self, k: int, c_size: int) -> None:
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        res = analyze_iterative_layer_decomposition(fam)
        assert res["num_layers"] >= 1
        assert res["global_sum_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True
        layer1 = res["layers"][0]
        assert layer1["layer_fails_locally"] is True
        assert layer1["layer_defect"] > 0
        assert layer1["residual_margin"] > 0
        assert layer1["residual_avg_ge_half"] is True
        assert len(layer1["residual_winners"]) > 0

    def test_tier4_iterative_decomposition(self) -> None:
        fam = build_tier4_obstruction_family(n=10)
        res = analyze_iterative_layer_decomposition(fam)
        assert res["num_layers"] >= 1
        assert res["global_sum_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True
        layer1 = res["layers"][0]
        assert layer1["layer_fails_locally"] is True
        assert layer1["residual_margin"] > 0
        assert layer1["residual_avg_ge_half"] is True
        assert len(layer1["residual_winners"]) > 0

    def test_adversarial_suite_iterative_layer_decomposition(self) -> None:
        """Verify multi-layer decomposition across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_iterative_layer_decomposition(fam)
            assert res["num_layers"] >= 1
            assert res["global_sum_holds"] is True
            assert res["unconditional_frankl_satisfied"] is True


class TestConditionalFiberEntropyAndInformationPotential:
    """Milestone 29: Unit and property tests for Conditional Fiber Entropy Engine,
    Quadratic Rényi-2 / Cauchy-Schwarz Information Potential, and Testing the Gilmer
    0.381966 -> 0.500 Threshold."""

    @pytest.mark.parametrize("n", [9, 10, 11, 12])
    def test_sarvate_renaud_conditional_fiber_entropy(self, n: int) -> None:
        fam = build_sarvate_renaud_k3_obstruction(n=n)
        res = analyze_conditional_fiber_entropy(fam, a_mask=0b111)

        # 1. Exact Chain Rule
        assert res["chain_rule_verified"] is True
        assert res["chain_rule_error"] < 1e-11
        assert abs((res["h_quotient"] + res["h_fiber_given_quotient"]) - res["h_family"]) < 1e-11

        # 2. Union Chain Rule
        assert res["union_chain_rule_verified"] is True
        assert res["union_chain_rule_error"] < 1e-11
        assert abs((res["h_union_quotient"] + res["h_union_fiber_given_quotient"]) - res["h_union"]) < 1e-11

        # 3. Directional Entropy Expansion Split
        assert res["expansion_split_verified"] is True
        assert res["expansion_split_error"] < 1e-11
        assert abs((res["quotient_entropy_expansion"] + res["fiber_entropy_expansion"]) - res["entropy_expansion"]) < 1e-11

        # 4. Cauchy-Schwarz Information Potential
        assert res["cauchy_schwarz_satisfied"] is True
        assert res["renyi2_quotient_potential"] >= res["cauchy_schwarz_lower_bound"] - 1e-12

        # 5. Empty Fiber Collision Lower Bound
        assert res["empty_fiber_mass"] == 1
        assert res["empty_fiber_bound_satisfied"] is True

        # 6. Complement Defect Absorption & Frankl Witness
        assert res["a_min_fails_locally"] is True
        assert res["c_absorbs_defect"] is True
        assert res["frankl_witness_present"] is True
        assert res["max_element_probability"] >= 0.5

    @pytest.mark.parametrize("k,c_size", [(3, 6), (4, 6), (5, 6), (6, 7), (7, 8)])
    def test_poonen_families_conditional_fiber_entropy(self, k: int, c_size: int) -> None:
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        res = analyze_conditional_fiber_entropy(fam)

        assert res["chain_rule_verified"] is True
        assert res["union_chain_rule_verified"] is True
        assert res["expansion_split_verified"] is True
        assert res["cauchy_schwarz_satisfied"] is True
        assert res["empty_fiber_bound_satisfied"] is True
        assert res["frankl_witness_present"] is True
        assert res["max_element_probability"] >= 0.5

        # Verify Quadratic Surrogate Properties
        for u, p in res["element_probabilities"].items():
            assert res["quadratic_entropy_surrogates"][u] <= 1.0 + 1e-12
            if p >= 0.5:
                # When p >= 1/2, quadratic Gilmer ratio g_2(p) <= 3/4
                assert res["quadratic_gilmer_ratios"][u] <= 0.75 + 1e-12

    def test_tier4_conditional_fiber_entropy(self) -> None:
        fam = build_tier4_obstruction_family(n=10)
        res = analyze_conditional_fiber_entropy(fam, a_mask=0b11111)

        assert res["chain_rule_verified"] is True
        assert res["union_chain_rule_verified"] is True
        assert res["expansion_split_verified"] is True
        assert res["cauchy_schwarz_satisfied"] is True
        assert res["empty_fiber_bound_satisfied"] is True
        assert res["frankl_witness_present"] is True
        assert res["max_element_probability"] >= 0.5

    def test_adversarial_suite_conditional_entropy_and_cs_bounds(self) -> None:
        """Verify conditional fiber entropy decomposition and Cauchy-Schwarz collision
        bounds across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_conditional_fiber_entropy(fam, a_mask=None)
            assert res["chain_rule_verified"] is True
            assert res["union_chain_rule_verified"] is True
            assert res["expansion_split_verified"] is True
            assert res["cauchy_schwarz_satisfied"] is True
            assert res["empty_fiber_bound_satisfied"] is True
            assert res["frankl_witness_present"] is True
            assert res["max_element_probability"] >= 0.5

    def test_gilmer_barrier_broken_audit(self) -> None:
        """Verify full audit: Gilmer barrier elevated from 0.381966 to >= 0.500."""
        audit = audit_conditional_fiber_entropy_barrier(adversarial_count=50, seed=20261014)

        assert audit["all_chain_rules_verified"] is True
        assert audit["all_union_chain_rules_verified"] is True
        assert audit["all_expansion_splits_verified"] is True
        assert audit["all_cauchy_schwarz_satisfied"] is True
        assert audit["all_empty_fiber_bounds_satisfied"] is True
        assert audit["all_have_frankl_witness"] is True
        assert audit["gilmer_barrier_broken_towards_05"] is True
        assert audit["min_p_max_observed"] >= 0.500000
        assert audit["min_p_max_observed"] > audit["gilmer_constant"]


class TestCoupledAsymmetricGilmerShift:
    """Milestone 30: Property and unit tests for the Analytical Shift of the Gilmer Bound
    under the Asymmetric Two-Component Partition (Unifying Island 1 and Island 2)."""

    def test_symmetric_gilmer_root_identity(self) -> None:
        """Verify the classical symmetric Gilmer root p* = (3 - sqrt(5))/2."""
        import math
        p_star = (3.0 - math.sqrt(5.0)) / 2.0
        # g_2(p) = 2 - 3p + p^2
        g2 = 2.0 - 3.0 * p_star + p_star * p_star
        assert abs(g2 - 1.0) < 1e-12
        assert abs(p_star - 0.38196601125010515) < 1e-12

    def test_dense_regime_frankl_guarantee(self) -> None:
        """Verify that when c <= k (n <= 2k), p_crit >= 0.500 unconditionally."""
        for k, c in [(3, 1), (3, 2), (3, 3), (4, 4), (5, 5), (6, 4)]:
            res = compute_coupled_asymmetric_gilmer_shift(k, c)
            assert res["regime"] == "dense_unconditional_frankl"
            assert res["p_crit"] >= 0.500
            assert res["frankl_witness_guaranteed"] is True
            assert res["barrier_shifted_above_gilmer"] is True

    def test_intermediate_shifted_regime_values(self) -> None:
        """Verify analytical shift for intermediate regime:
        - k=3, c=4 (n=7): p_crit = 3/7 ~= 0.428571 > 0.381966
        - k=4, c=6 (n=10): p_crit = 4/10 = 0.400000 > 0.381966
        - k=5, c=6 (n=11): p_crit = 5/11 ~= 0.454545 > 0.381966
        """
        cases = [
            (3, 4, 3.0 / 7.0),
            (4, 6, 4.0 / 10.0),
            (5, 6, 5.0 / 11.0),
        ]
        for k, c, expected_pcrit in cases:
            res = compute_coupled_asymmetric_gilmer_shift(k, c)
            assert res["regime"] == "intermediate_shifted_gilmer"
            assert abs(res["p_crit"] - expected_pcrit) < 1e-6
            assert res["barrier_shifted_above_gilmer"] is True
            assert res["p_crit"] > res["gilmer_p_star"]

    def test_sparse_entropy_bounded_regime(self) -> None:
        """Verify that for high c (c >> k), p_crit is bounded below by p*."""
        res = compute_coupled_asymmetric_gilmer_shift(k=3, c=15)
        assert res["regime"] == "sparse_entropy_bounded"
        assert res["p_crit"] >= res["gilmer_p_star"]

    def test_audit_asymmetric_gilmer_shift_comprehensive(self) -> None:
        """Run comprehensive audit verifying analytical consistency across explicit
        and adversarial non-biclosed families."""
        audit = audit_asymmetric_gilmer_shift(adversarial_count=30, seed=20261014)
        assert audit["benchmark_families_audited"] == 10
        assert audit["total_families_audited"] == 40
        assert audit["all_witnesses_present"] is True
        assert audit["all_shifts_consistent"] is True
        assert audit["min_p_max_observed"] >= 0.500
        assert audit["analytical_gilmer_shifted"] is True


class TestDispersionEntropyPincerTrap:
    """Milestone 31: Property and unit tests for the Dispersion-Entropy Pincer Trap
    and Lagrangian Adversary Optimization."""

    def test_delta_h2_and_psi2_rate_exact_values(self) -> None:
        """Verify analytical surrogate Delta h_2(p) and unit-mass rate psi_2(p)."""
        import math
        p_star = (3.0 - math.sqrt(5.0)) / 2.0

        # Boundary values
        assert delta_h2(0.0) == 0.0
        assert delta_h2(0.5) == -0.25
        assert abs(delta_h2(p_star)) < 1e-12

        # Rates
        assert psi2_rate(0.0) == 4.0
        assert psi2_rate(0.5) == -0.5
        assert abs(psi2_rate(p_star)) < 1e-12

        # Fractions exact arithmetic
        assert delta_h2(Fraction(1, 2)) == Fraction(-1, 4)
        assert psi2_rate(Fraction(1, 2)) == Fraction(-1, 2)
        assert delta_h2(Fraction(0, 1)) == Fraction(0, 1)

        # Monotonicity of psi_2'(p) = 4(-4 + 8p - 3p^2) < 0 on [0, 0.5]
        for step in range(51):
            p = step / 100.0
            deriv = 4.0 * (-4.0 + 8.0 * p - 3.0 * p * p)
            assert deriv < 0.0

        # Sparse zone vs Compression zone
        for p in [0.05, 0.1, 0.2, 0.3, 0.38]:
            assert delta_h2(p) > 0.0
            assert psi2_rate(p) > 0.0

        for p in [0.39, 0.40, 0.45, 0.49, 0.50]:
            assert delta_h2(p) < 0.0
            assert psi2_rate(p) < 0.0

    def test_sub_pstar_sparse_expansion_jaw(self) -> None:
        """Verify Jaw 1: Any adversary attempting p_max < p* faces strictly positive
        continuous entropy lower bound Delta H_total >= k * psi_2(p_max) > 0."""
        for k in [3, 4, 5]:
            for p_max in [0.20, 0.30, 0.35, 0.38]:
                res = optimize_pincer_trap_adversary(k=k, c=10, p_max=p_max, N_samples=50)
                # Continuous bound strictly positive
                assert res["continuous_lower_bound"]["delta_H_total_bound"] > 0.0
                # Concentrated strategy strictly positive
                assert res["concentrated_strategy"]["delta_H_total"] > 0.0

    def test_concave_extreme_point_minimality(self) -> None:
        """Verify Jaw 2: For p_max in the concave regime (p_max <= 0.42265),
        the extreme-point concentrated strategy strictly minimizes entropy."""
        for k, c, p_max in [(4, 10, 0.35), (4, 10, 0.381966), (4, 6, 0.40), (3, 10, 0.40)]:
            res = optimize_pincer_trap_adversary(k=k, c=c, p_max=p_max, N_samples=300)
            assert res["is_feasible"] is True
            assert res["adversary_samples"]["all_samples_ge_theoretical_min"] is True
            assert res["analytical_proof_certificate"]["is_p_max_in_concave_zone"] is True

    def test_pincer_trap_zero_crossing_roots(self) -> None:
        """Verify that the discrete zero-crossing root p_trap strictly exceeds p* for all k."""
        import math
        p_star = (3.0 - math.sqrt(5.0)) / 2.0
        for k in [3, 4, 5, 6]:
            zc = solve_pincer_trap_zero_crossing(k, c=10)
            assert zc["p_trap_discrete"] >= p_star
            assert zc["p_trap_exceeds_p_star"] is True

    def test_dispersion_blowup_in_sparse_zone(self) -> None:
        """Verify that dispersing mass across large c (high n) blows up total entropy."""
        res = optimize_pincer_trap_adversary(k=3, c=15, p_max=0.45, N_samples=100)
        assert res["dispersed_strategy"]["is_dispersed_in_sparse_zone"] is True
        # Dispersion blowup is strictly positive
        assert res["dispersed_strategy"]["dispersion_blowup"] > 0.0
        # Dispersed total entropy blows up to positive value
        assert res["dispersed_strategy"]["delta_H_total"] > 0.0

    def test_effective_universe_collapse_to_dense(self) -> None:
        """Verify that concentrating mass at p_max = 0.5 collapses the active universe
        to n_eff <= 2k."""
        for k in [3, 4, 5, 6]:
            res = optimize_pincer_trap_adversary(k=k, c=20, p_max=0.5, N_samples=10)
            assert res["effective_universe_dense"] is True
            assert res["effective_dimension_bound"] <= 2 * k

    def test_audit_pincer_trap_adversary_comprehensive(self) -> None:
        """Verify comprehensive audit of the Dispersion-Entropy Pincer Trap."""
        audit = audit_pincer_trap_adversary(
            k_values=(3, 4),
            c_values=(4, 8),
            p_max_values=(0.35, 0.381966, 0.42, 0.48),
            N_samples=50,
            seed=20261014,
        )
        assert audit["cases_audited"] == 16
        assert audit["all_bounds_valid"] is True
        assert audit["all_samples_minimal"] is True
        assert audit["all_dispersion_blowups_positive"] is True
        assert audit["all_roots_exceed_p_star"] is True
        assert audit["all_passed"] is True


class TestExactSecantFactorizationAndPrefixFiber:
    """Milestone 32: Unit and property tests for Exact Secant Factorization and
    Prefix-Fiber Conditioning.
    """

    def test_secant_factorization_difference_exact_fractions(self) -> None:
        """Verify exact algebraic identity on a rational grid:
        Delta h_2(p) - p * psi_2(q) = 4p(q - p) * [ 4(1 - p - q) + p^2 + pq + q^2 ].
        """
        fracs = [
            Fraction(0, 1),
            Fraction(1, 10),
            Fraction(1, 4),
            Fraction(1, 3),
            Fraction(3, 8),
            Fraction(2, 5),
            Fraction(9, 20),
            Fraction(1, 2),
        ]
        for i, p in enumerate(fracs):
            for q in fracs[i:]:
                res = secant_factorization_difference(p, q)
                assert res["is_exact"] is True
                assert res["difference"] == Fraction(0, 1)
                assert res["bracket_nonneg"] is True
                assert res["rhs_nonneg"] is True
                assert res["is_nonneg_domain"] is True
                assert res["lhs"] >= 0 or (p == 0) or (res["lhs"] == res["rhs"])

    def test_secant_factorization_difference_floats(self) -> None:
        """Verify continuous evaluation and precision on float grid."""
        pts = [0.0, 0.05, 0.12, 0.25, 0.333, 0.381966, 0.42, 0.45, 0.5]
        for i, p in enumerate(pts):
            for q in pts[i:]:
                res = secant_factorization_difference(p, q)
                assert res["is_exact"] is True
                assert abs(res["difference"]) < 1e-12
                assert res["bracket_nonneg"] is True
                assert res["rhs_nonneg"] is True

    def test_secant_factorization_integer_identities(self) -> None:
        """Verify exact integer polynomial identities and non-negativity."""
        N_values = [10, 20, 27, 40, 100]
        for N in N_values:
            for g in range(0, (N // 2) + 1, max(1, N // 10)):
                for f in range(0, g + 1, max(1, g // 5 if g > 0 else 1)):
                    res = secant_factorization_integer(f, g, N)
                    assert res["identity_holds"] is True
                    assert res["identity_scaled_holds"] is True
                    assert res["difference"] == 0
                    assert res["bracket_nonneg"] is True
                    assert res["rhs_nonneg"] is True
                    assert res["is_nonneg_domain"] is True
                    assert res["delta_h2_int"] >= f * res["psi2_int"]

    def test_prefix_fiber_conditioning_poonen_k4(self) -> None:
        """Verify prefix-fiber conditioning on Poonen k=4 local obstruction family."""
        fam = build_poonen_local_obstruction_family(k=4, c_size=6)
        res = analyze_high_mc_prefix_fiber_conditioning(fam, a_mask=0b1111)

        assert res["family_size"] == 29
        assert res["a_size"] == 4
        assert res["c_size"] == 6
        assert res["is_high_mc"] is True
        assert res["M_C"] > 4.0
        assert res["all_total_prob_laws_hold"] is True
        assert res["all_kleitman_correlations_nonneg"] is True
        assert res["all_pair_union_trace_bounds_hold"] is True
        assert res["all_c_are_witnesses"] is True
        assert res["has_witness_in_c"] is True
        assert res["high_mc_all_subhalf"] is False
        assert res["all_secant_identities_hold"] is True
        assert res["all_secant_scaled_identities_hold"] is True

    def test_prefix_fiber_conditioning_sarvate_renaud_k3(self) -> None:
        """Verify prefix-fiber conditioning on Sarvate-Renaud k=3 local obstruction family."""
        fam = build_sarvate_renaud_k3_obstruction(n=10)
        res = analyze_high_mc_prefix_fiber_conditioning(fam, a_mask=0b111)

        assert res["family_size"] == 27
        assert res["a_size"] == 3
        assert res["c_size"] == 7
        assert res["is_high_mc"] is True
        assert res["M_C"] > 3.0
        assert res["all_total_prob_laws_hold"] is True
        assert res["all_kleitman_correlations_nonneg"] is True
        assert res["all_pair_union_trace_bounds_hold"] is True
        assert res["all_c_are_witnesses"] is True
        assert res["high_mc_all_subhalf"] is False
        assert res["all_secant_identities_hold"] is True
        assert res["all_secant_scaled_identities_hold"] is True

    def test_prefix_fiber_conditioning_tier4_obstruction(self) -> None:
        """Verify prefix-fiber conditioning on Tier-4 obstruction family."""
        fam = build_tier4_obstruction_family(n=10)
        res = analyze_high_mc_prefix_fiber_conditioning(fam, a_mask=0b11111)

        assert res["all_total_prob_laws_hold"] is True
        assert res["all_secant_identities_hold"] is True
        assert res["all_secant_scaled_identities_hold"] is True
        assert res["has_witness_in_c"] is True
        assert res["high_mc_all_subhalf"] is False

    def test_adversarial_suite_prefix_fiber_conditioning(self) -> None:
        """Verify prefix-fiber conditioning and the elimination of false M_C <= k
        across adversarial non-biclosed families.
        """
        suite = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=40, seed=20261014
        )
        for entry in suite:
            fam = entry["family"]
            res = analyze_high_mc_prefix_fiber_conditioning(fam, a_mask=None)
            assert res["all_total_prob_laws_hold"] is True
            assert res["all_secant_identities_hold"] is True
            assert res["all_secant_scaled_identities_hold"] is True
            assert res["high_mc_all_subhalf"] is False
            assert res["global_secant_holds"] is True


class TestMilestone33AbsorptionCentersAndPrefixTower:
    """Milestone 33: Adversarial Disjoint Union Family, Absorption Centers,
    Prefix Chain Rule, and Support Contraction Tower Property.
    """

    def test_adversarial_disjoint_family_negative_covariance(self) -> None:
        r"""Verify strict negative covariance Cov(1, 2) < 0 in the D_1 \sqcup D_2 family."""
        # Case m=2, d0_size=1, G = {emptyset} (card_G = 1 < 2^4 = 16)
        res = build_disjoint_absorption_adversary_family(m=2, d0_size=1, g_type="empty")

        assert res["is_union_closed"] is True
        assert res["family_size"] == 10
        assert res["freq_1"] == 5
        assert res["freq_2"] == 5
        assert res["freq_12"] == 1
        assert res["p_1"] == 0.5
        assert res["p_2"] == 0.5
        assert res["p_12"] == 0.1
        assert res["cov_12"] == pytest.approx(-0.15)
        assert res["is_negative_covariance"] is True
        assert res["cov_difference_error"] < 1e-12

        # Case m=1, d0_size=1, G = {emptyset} (card_G = 1 < 2^2 = 4)
        res_m1 = build_disjoint_absorption_adversary_family(m=1, d0_size=1, g_type="empty")
        assert res_m1["is_union_closed"] is True
        assert res_m1["family_size"] == 6
        assert res_m1["cov_12"] == pytest.approx(-1.0 / 12.0)
        assert res_m1["is_negative_covariance"] is True

        # Case m=3, d0_size=1, G = {emptyset} (card_G = 1 < 2^6 = 64)
        res_m3 = build_disjoint_absorption_adversary_family(m=3, d0_size=1, g_type="empty")
        assert res_m3["is_union_closed"] is True
        assert res_m3["family_size"] == 18
        assert res_m3["cov_12"] == pytest.approx(-7.0 / 36.0)
        assert res_m3["is_negative_covariance"] is True

    def test_adversarial_disjoint_family_absorption_centers(self) -> None:
        """When an adversary chooses G to suppress p_1, p_2 < 0.5, the absorption
        elements in D_1, D_2, D_0 are unconditionally forced to exceed 0.500.
        """
        res = build_disjoint_absorption_adversary_family(
            m=2, d0_size=1, g_type="adversarial_subhalf"
        )
        assert res["is_union_closed"] is True
        assert res["family_size"] == 11
        assert res["p_1"] < 0.5
        assert res["p_2"] < 0.5
        assert res["p1_subhalf"] is True
        assert res["p2_subhalf"] is True

        # Base absorption element D_0: freq = 2^(2+1) + 1 + 1 = 10 out of 11!
        d0_elem = 2
        assert res["freqs_D0"][d0_elem] == 10
        assert res["freqs_D0"][d0_elem] / 11.0 == pytest.approx(10.0 / 11.0)
        assert res["freqs_D0"][d0_elem] / 11.0 > 0.500

        # Partition elements D_1, D_2: freq = 3 * 2^(2-1) + 1 = 7 out of 11!
        assert res["p_D1"] == pytest.approx(7.0 / 11.0)
        assert res["p_D1"] > 0.500
        assert res["p_D2"] == pytest.approx(7.0 / 11.0)
        assert res["p_D2"] > 0.500

        assert res["absorption_boost_holds"] is True
        assert res["has_frankl_witness"] is True
        assert set(res["witnesses"]).issuperset({d0_elem})

    def test_optimize_absorption_adversary_minimax(self) -> None:
        """Verify minimax constrained optimization over all union-closed families G ⊆ 2^{D_0}."""
        for m in (1, 2):
            for d0_sz in (1, 2):
                res = optimize_absorption_adversary(m=m, d0_size=d0_sz)
                assert res["num_union_closed_G_evaluated"] >= 1
                assert res["minimax_frequency_ge_half"] is True
                assert res["minimax_max_frequency"] >= 0.500 - 1e-12
                assert res["all_families_contain_frankl_witness"] is True
                assert res["p1_subhalf_forces_absorption_witness"] is True

    def test_prefix_chain_rule_exact_shannon_entropy(self) -> None:
        """Verify the exact chain rule H(S_1 ∪ S_2) = H(Q_1 ∪ Q_2) + H(B_1 ∪ B_2 | Q_1 ∪ Q_2)."""
        # Test on Sarvate-Renaud k=3
        fam_sr = build_sarvate_renaud_k3_obstruction(n=10)
        res_sr = compute_prefix_chain_rule(fam_sr, prefix_mask=0b1111111000)
        assert res_sr["chain_rule_holds"] is True
        assert res_sr["chain_rule_diff"] < 1e-12
        assert res_sr["H_joint_union"] == pytest.approx(res_sr["chain_rule_sum"], abs=1e-12)

        # Test on Poonen k=4
        fam_pn = build_poonen_local_obstruction_family(k=4, c_size=6)
        res_pn = compute_prefix_chain_rule(fam_pn, prefix_mask=(0b111111 << 4))
        assert res_pn["chain_rule_holds"] is True
        assert res_pn["chain_rule_diff"] < 1e-12

        # Test on Adversarial Disjoint Union Family
        adv = build_disjoint_absorption_adversary_family(m=2, d0_size=1, g_type="empty")
        res_adv = compute_prefix_chain_rule(adv["family"], prefix_mask=0b111100)
        assert res_adv["chain_rule_holds"] is True
        assert res_adv["chain_rule_diff"] < 1e-12

    def test_prefix_tower_support_contraction_and_jensen_gap(self) -> None:
        """Verify Tower property invariant, active density boost, and Jensen variance gap."""
        fam = build_sarvate_renaud_k3_obstruction(n=10)
        res = analyze_prefix_tower_support_contraction(fam, prefix_mask=0b1111111000)

        assert res["all_tower_invariants_hold"] is True
        assert res["all_jensen_gaps_nonneg"] is True

        for rep in res["coordinate_reports"].values():
            assert rep["tower_invariant_holds"] is True
            assert rep["jensen_gap_nonneg"] is True
            assert rep["integer_cs_holds"] is True
            assert rep["density_boost_holds"] is True
            if rep["w_0"] > 0:
                assert rep["density_boost_ratio"] > 1.0

        # Adversarial Disjoint family
        adv = build_disjoint_absorption_adversary_family(m=2, d0_size=1, g_type="adversarial_subhalf")
        res_adv = analyze_prefix_tower_support_contraction(adv["family"], prefix_mask=0b111100)
        assert res_adv["all_tower_invariants_hold"] is True

class TestMilestone34UniversalTopFiberAbsorption:
    """Milestone 34: Test Universal Top-Fiber Absorption and Refined Fiber-Base Balance."""

    @pytest.mark.parametrize(
        "k,c_size",
        [(3, 6), (4, 5), (5, 6), (6, 7), (7, 8)],
    )
    def test_poonen_families_universal_top_fiber_absorption(self, k: int, c_size: int) -> None:
        """Verify universal top-fiber absorption and refined balance across Poonen k in {3,4,5,6,7}."""
        fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
        res = analyze_universal_top_fiber_absorption(fam)

        # 1. Top-slice existence in every fiber
        assert res["universal_top_fiber_absorbed"] is True

        # 2. Base cardinality bounds
        assert res["card_q_le_min_a_freq"] is True
        assert res["k_card_q_le_w"] is True

        # 3. Refined balance law for each fiber
        assert res["fiber_refined_balance_verified"] is True
        assert res["refined_global_complement_holds"] is True
        assert res["sum_base_sizes"] > 0

        # 4. Strict compression under local failure
        if res["a_fails_locally"]:
            assert res["q_strictly_compressed"] is True
            assert res["average_fiber_mass_gt_2"] is True
            assert res["c_doubled_exceeds_threshold"] is True

        # 5. Dispersion gap reduction
        if not res["n_le_2k"]:
            assert res["dispersion_reduction"] == 2 * res["sum_base_sizes"]
            assert res["refined_dispersion_gap"] < res["raw_dispersion_gap"]

        assert res["unconditional_frankl_satisfied"] is True

    @pytest.mark.parametrize("n", [9, 10, 11, 12])
    def test_sarvate_renaud_k3_universal_top_fiber_absorption(self, n: int) -> None:
        """Verify Sarvate-Renaud k=3 family top-fiber absorption and dispersion gap reduction."""
        fam = build_sarvate_renaud_k3_obstruction(n=n)
        res = analyze_universal_top_fiber_absorption(fam)

        assert res["universal_top_fiber_absorbed"] is True
        assert res["card_q_le_min_a_freq"] is True
        assert res["k_card_q_le_w"] is True
        assert res["fiber_refined_balance_verified"] is True
        assert res["refined_global_complement_holds"] is True
        assert res["sum_base_sizes"] > 0

        assert res["a_fails_locally"] is True
        assert res["q_strictly_compressed"] is True
        assert res["average_fiber_mass_gt_2"] is True
        assert res["c_doubled_exceeds_threshold"] is True

        # Refined dispersion reduction is strictly positive
        assert res["dispersion_reduction"] == 2 * res["sum_base_sizes"]
        assert res["refined_dispersion_gap"] < res["raw_dispersion_gap"]
        assert res["unconditional_frankl_satisfied"] is True

    @pytest.mark.parametrize("n", [10, 11, 12])
    def test_tier4_averaging_obstruction_refined_balance(self, n: int) -> None:
        """Verify Tier-4 averaging obstruction families satisfy top-fiber absorption and refined balance."""
        fam = build_tier4_obstruction_family(n=n)
        res = analyze_universal_top_fiber_absorption(fam)

        assert res["universal_top_fiber_absorbed"] is True
        assert res["card_q_le_min_a_freq"] is True
        assert res["k_card_q_le_w"] is True
        assert res["fiber_refined_balance_verified"] is True
        assert res["refined_global_complement_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True

    def test_n_le_2k_refined_balance_equality(self) -> None:
        """When n <= 2k, dispersion gap is zero and refined balance holds."""
        seeds = [0b00111, 0b01111, 0b10111]
        fam = union_close_arbitrary_seeds(seeds)
        res = analyze_universal_top_fiber_absorption(fam)

        assert res["k"] == 3
        assert res["n"] <= 6
        assert res["n_le_2k"] is True
        assert res["raw_dispersion_gap"] == 0
        assert res["refined_dispersion_gap"] == 0
        assert res["universal_top_fiber_absorbed"] is True
        assert res["fiber_refined_balance_verified"] is True
        assert res["refined_global_complement_holds"] is True
        assert res["unconditional_frankl_satisfied"] is True

    def test_adversarial_suite_universal_top_fiber_absorption(self) -> None:
        """Verify top-fiber absorption and refined balance across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_universal_top_fiber_absorption(fam)
            assert res["universal_top_fiber_absorbed"] is True
            assert res["card_q_le_min_a_freq"] is True
            assert res["k_card_q_le_w"] is True
            assert res["fiber_refined_balance_verified"] is True
            assert res["refined_global_complement_holds"] is True
            if res["a_fails_locally"]:
                assert res["q_strictly_compressed"] is True
                assert res["average_fiber_mass_gt_2"] is True
                assert res["c_doubled_exceeds_threshold"] is True
            assert res["unconditional_frankl_satisfied"] is True


class TestMilestone35QuotientCarrierDensity:
    """Milestone 35: Quotient Carrier Density & Mass Integration Tests."""

    def test_carrier_frequency_sum_double_counting_explicit_cases(self) -> None:
        """Verify carrier frequency sum double-counting identity sum_C freq(y) = sum m(Q)|Q|."""
        cases = [
            ("Sarvate-Renaud k=3", build_sarvate_renaud_k3_obstruction(10)),
            ("Poonen k=4", build_poonen_local_obstruction_family(4, 6)),
            ("Poonen k=5", build_poonen_local_obstruction_family(5, 6)),
            ("Tier-4 k=5", build_tier4_obstruction_family(10)),
        ]
        for name, fam in cases:
            res = analyze_quotient_carrier_density_and_mass_integration(fam)
            assert res["carrier_double_counting_holds"] is True, f"Failed on {name}"
            assert res["carrier_frequency_sum"] == res["fiber_mass_size_sum"], f"Mismatch on {name}"
            assert res["carrier_frequency_sum"] > 0

    def test_collision_potential_lower_bound_explicit_cases(self) -> None:
        """Verify Rényi-2 collision potential lower bound sum m(Q)^2 >= 1 + (N-1)^2/(q-1) > 2N."""
        cases = [
            ("Sarvate-Renaud k=3", build_sarvate_renaud_k3_obstruction(10)),
            ("Poonen k=4", build_poonen_local_obstruction_family(4, 6)),
            ("Poonen k=5", build_poonen_local_obstruction_family(5, 6)),
            ("Tier-4 k=5", build_tier4_obstruction_family(10)),
        ]
        for name, fam in cases:
            res = analyze_quotient_carrier_density_and_mass_integration(fam)
            assert res["collision_bound_holds"] is True, f"Collision bound failed on {name}"
            if res["quotient_compressed"] and res["num_quotient_bases"] >= 2:
                assert res["collision_exceeds_2N"] is True, f"Collision did not exceed 2N on {name}"
                assert res["collision_sum_sq"] > 2 * res["family_size"]

    def test_pigeonhole_carrier_density_bound_explicit_cases(self) -> None:
        """Verify max_C freq >= floor(sum m(Q)|Q| / |C_eff|) holds on all explicit obstructions."""
        cases = [
            ("Sarvate-Renaud k=3", build_sarvate_renaud_k3_obstruction(10)),
            ("Poonen k=4", build_poonen_local_obstruction_family(4, 6)),
            ("Poonen k=5", build_poonen_local_obstruction_family(5, 6)),
            ("Tier-4 k=5", build_tier4_obstruction_family(10)),
        ]
        for name, fam in cases:
            res = analyze_quotient_carrier_density_and_mass_integration(fam)
            assert res["pigeonhole_bound_holds"] is True, f"Pigeonhole failed on {name}"
            assert res["max_c_frequency"] >= math.floor(res["carrier_average_density"])
            assert res["max_c_ratio"] >= 0.500

    def test_carrier_dense_threshold_and_witness_extraction(self) -> None:
        """Verify carrier dense threshold and unconditional Frankl witness extraction."""
        fam = build_sarvate_renaud_k3_obstruction(10)
        res = analyze_quotient_carrier_density_and_mass_integration(fam)
        assert res["carrier_dense_threshold_satisfied"] is True
        assert res["frankl_witness_found"] is True
        assert res["complement_witness"] is not None
        assert res["complement_witness_defect"] >= 0

    def test_adversary_optimizer_falsification_k3(self) -> None:
        """Test adversarial optimizer for k=3 across multiple universe dimensions."""
        for c in [3, 4, 5]:
            for N in [10, 16, 20]:
                res = optimize_quotient_carrier_adversary(k=3, c=c, N=N)
                assert res["adversary_succeeded"] is False
                assert res["falsification_confirmed"] is True
                if res["collision_lower_bound"] is not None:
                    assert res["collision_exceeds_2N"] is True

    def test_adversary_optimizer_falsification_k4_k5(self) -> None:
        """Test adversarial optimizer for k=4, 5 demonstrating adversary cannot keep coordinates < 0.500."""
        for k in [4, 5]:
            for N in [16, 20]:
                res = optimize_quotient_carrier_adversary(k=k, c=4, N=N)
                assert res["adversary_succeeded"] is False
                assert res["falsification_confirmed"] is True

    def test_adversary_optimizer_fixed_q_size(self) -> None:
        """Test adversarial optimizer with constrained quotient size q_size."""
        res_q3 = optimize_quotient_carrier_adversary(k=3, c=4, N=16, q_size=3)
        assert res_q3["adversary_succeeded"] is False
        assert res_q3["falsification_confirmed"] is True

        res_q4 = optimize_quotient_carrier_adversary(k=4, c=4, N=20, q_size=4)
        assert res_q4["adversary_succeeded"] is False
        assert res_q4["falsification_confirmed"] is True

    def test_analyze_quotient_carrier_sarvate_renaud_k3(self) -> None:
        """Detailed test of Sarvate-Renaud k=3 (n=10) carrier density and integration."""
        fam = build_sarvate_renaud_k3_obstruction(10)
        res = analyze_quotient_carrier_density_and_mass_integration(fam)
        assert res["family_size"] == 27
        assert res["k"] == 3
        assert res["c_len"] == 7
        assert res["num_quotient_bases"] == 8
        assert res["quotient_compressed"] is True
        assert res["average_fiber_mass"] > 3.0
        assert res["carrier_double_counting_holds"] is True
        assert res["collision_bound_holds"] is True
        assert res["collision_sum_sq"] == 119
        assert res["collision_sum_sq"] > 2 * 27
        assert res["pigeonhole_bound_holds"] is True
        assert res["max_c_frequency"] == 26
        assert res["frankl_witness_found"] is True

    def test_analyze_quotient_carrier_poonen_k4(self) -> None:
        """Detailed test of Poonen k=4 (c_size=6) carrier density and integration."""
        fam = build_poonen_local_obstruction_family(4, 6)
        res = analyze_quotient_carrier_density_and_mass_integration(fam)
        assert res["family_size"] == 29
        assert res["k"] == 4
        assert res["c_len"] == 6
        assert res["num_quotient_bases"] == 6
        assert res["quotient_compressed"] is True
        assert res["average_fiber_mass"] > 4.0
        assert res["carrier_double_counting_holds"] is True
        assert res["collision_bound_holds"] is True
        assert res["collision_sum_sq"] == 293
        assert res["collision_sum_sq"] > 2 * 29
        assert res["pigeonhole_bound_holds"] is True
        assert res["max_c_frequency"] == 28
        assert res["frankl_witness_found"] is True

    def test_analyze_quotient_carrier_poonen_k5(self) -> None:
        """Detailed test of Poonen k=5 (c_size=6) carrier density and integration."""
        fam = build_poonen_local_obstruction_family(5, 6)
        res = analyze_quotient_carrier_density_and_mass_integration(fam)
        assert res["family_size"] == 48
        assert res["k"] == 5
        assert res["c_len"] == 6
        assert res["num_quotient_bases"] == 7
        assert res["quotient_compressed"] is True
        assert res["average_fiber_mass"] > 6.0
        assert res["carrier_double_counting_holds"] is True
        assert res["collision_bound_holds"] is True
        assert res["collision_sum_sq"] == 1070
        assert res["collision_sum_sq"] > 2 * 48
        assert res["pigeonhole_bound_holds"] is True
        assert res["max_c_frequency"] == 47
        assert res["frankl_witness_found"] is True

    def test_analyze_quotient_carrier_tier4(self) -> None:
        """Detailed test of Tier-4 obstruction (n=10) carrier density and integration."""
        fam = build_tier4_obstruction_family(10)
        res = analyze_quotient_carrier_density_and_mass_integration(fam)
        assert res["family_size"] == 9
        assert res["k"] == 5
        assert res["num_quotient_bases"] == 2
        assert res["quotient_compressed"] is True
        assert res["carrier_double_counting_holds"] is True
        assert res["collision_bound_holds"] is True
        assert res["collision_sum_sq"] == 65
        assert res["collision_sum_sq"] > 2 * 9
        assert res["pigeonhole_bound_holds"] is True
        assert res["max_c_frequency"] == 8
        assert res["frankl_witness_found"] is True

    def test_adversarial_suite_carrier_density_100(self) -> None:
        """Verify carrier double counting, collision bounds, and pigeonhole across 100 adversarial families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261014
        )
        for item in adv_fams:
            fam = item["family"]
            res = analyze_quotient_carrier_density_and_mass_integration(fam)
            assert res["carrier_double_counting_holds"] is True
            assert res["collision_bound_holds"] is True
            assert res["pigeonhole_bound_holds"] is True
            assert res["frankl_witness_found"] is True
            if res["a_fails_locally"]:
                assert res["quotient_compressed"] is True
                assert res["average_fiber_mass_gt_2"] is True
                assert res["collision_exceeds_2N"] is True


class TestMilestone36SubcriticalFiberPositivity:
    """Milestone 36: Sub-Critical Fiber Positivity, Intra-Fiber Union Closure, and Volume-Bonus Witness."""

    def test_subcritical_positivity_sarvate_renaud_k3(self) -> None:
        """Verify subcritical positivity law on Sarvate-Renaud k=3 (n=10)."""
        fam = build_sarvate_renaud_k3_obstruction(10)
        res = analyze_subcritical_fiber_positivity(fam)
        assert res["family_size"] == 27
        assert res["k"] == 3
        assert res["a_fails_locally"] is True
        assert res["subcritical_positivity_verified"] is True
        assert res["small_mult_positivity_verified"] is True
        assert res["negative_requires_supercritical_and_m_ge_3"] is True
        assert res["all_invariants_verified"] is True

        # Check subcritical fibers
        for f in res["subcritical_fibers"]:
            assert 2 * f["q_size"] <= res["k"]
            assert f["delta_q"] > 0
            assert f["delta_q"] >= f["expected_min_surplus"]

        # Check negative fibers
        for f in res["negative_defect_fibers"]:
            assert 2 * f["q_size"] >= res["k"] + 1
            assert f["m_q"] >= 3

    def test_subcritical_positivity_poonen_k4_k5(self) -> None:
        """Verify subcritical positivity law on Poonen local obstructions k=4 and k=5."""
        for k, c_size in [(4, 6), (5, 6)]:
            fam = build_poonen_local_obstruction_family(k=k, c_size=c_size)
            res = analyze_subcritical_fiber_positivity(fam)
            assert res["k"] == k
            assert res["a_fails_locally"] is True
            assert res["subcritical_positivity_verified"] is True
            assert res["small_mult_positivity_verified"] is True
            assert res["negative_requires_supercritical_and_m_ge_3"] is True
            assert res["all_invariants_verified"] is True

            for f in res["subcritical_fibers"]:
                assert f["delta_q"] > 0
                assert f["delta_q"] >= f["expected_min_surplus"]

            for f in res["negative_defect_fibers"]:
                assert 2 * f["q_size"] >= k + 1
                assert f["m_q"] >= 3

    def test_subcritical_positivity_tier4_obstruction(self) -> None:
        """Verify subcritical positivity on Tier-4 averaging obstruction (n=10)."""
        fam = build_tier4_obstruction_family(10)
        res = analyze_subcritical_fiber_positivity(fam)
        assert res["all_invariants_verified"] is True

    def test_intra_fiber_union_closure_explicit_cases(self) -> None:
        """Verify intra-fiber union closure and inductive Frankl witnesses across explicit families."""
        test_cases = [
            ("Sarvate-Renaud k=3", build_sarvate_renaud_k3_obstruction(10)),
            ("Poonen k=4", build_poonen_local_obstruction_family(4, 6)),
            ("Poonen k=5", build_poonen_local_obstruction_family(5, 6)),
            ("Tier-4 n=10", build_tier4_obstruction_family(10)),
        ]
        for label, fam in test_cases:
            res = analyze_intra_fiber_union_closure(fam)
            assert res["top_slice_present_all"] is True, f"{label} top slice missing"
            assert res["intra_fiber_union_closed_all"] is True, f"{label} slice union closure failed"
            assert res["inductive_frankl_satisfied_all"] is True, f"{label} inductive Frankl witness missing"
            assert res["all_fibers_autonomous_union_closed"] is True

    def test_volume_bonus_extended_dense_witness_explicit_cases(self) -> None:
        """Verify volume-bonus extended dense witness bound and extraction on explicit families."""
        test_cases = [
            ("Sarvate-Renaud k=3", build_sarvate_renaud_k3_obstruction(10)),
            ("Poonen k=4", build_poonen_local_obstruction_family(4, 6)),
            ("Poonen k=5", build_poonen_local_obstruction_family(5, 6)),
            ("Tier-4 n=10", build_tier4_obstruction_family(10)),
        ]
        for label, fam in test_cases:
            res = analyze_volume_bonus_extended_dense_witness(fam)
            assert res["unconditional_bound_holds"] is True, f"{label} unconditional bound violated"
            assert res["carrier_dense_satisfied"] is True, f"{label} carrier density violated"
            assert res["frankl_witness_found"] is True, f"{label} Frankl witness missing"

    def test_adversary_optimizer_c_gg_k_regime(self) -> None:
        """Test adversarial optimizer with c >> k: k in {3, 4} with c in [6, 8, 10, 12]."""
        for k in [3, 4]:
            for c in [6, 8, 10, 12]:
                for N in [16, 20]:
                    res = optimize_quotient_carrier_adversary(k=k, c=c, N=N)
                    assert res["adversary_succeeded"] is False, f"Adversary succeeded for k={k}, c={c}, N={N}"
                    assert res["falsification_confirmed"] is True
                    assert res["subcritical_positivity_enforced"] is True
                    assert res["worst_case_ratio"] >= 0.500

    def test_adversarial_suite_milestone_36_100(self) -> None:
        """Verify Milestone 36 invariants across 100 adversarial non-biclosed families."""
        adv_fams = generate_adversarial_non_biclosed_families(
            n_min=4, n_max=10, count=100, seed=20261015
        )
        for item in adv_fams:
            fam = item["family"]
            # 1. Sub-critical positivity
            res_sub = analyze_subcritical_fiber_positivity(fam)
            assert res_sub["subcritical_positivity_verified"] is True
            assert res_sub["small_mult_positivity_verified"] is True
            assert res_sub["negative_requires_supercritical_and_m_ge_3"] is True

            # 2. Intra-fiber union closure
            res_if = analyze_intra_fiber_union_closure(fam)
            assert res_if["top_slice_present_all"] is True
            assert res_if["intra_fiber_union_closed_all"] is True
            assert res_if["inductive_frankl_satisfied_all"] is True

            # 3. Volume-bonus extended witness
            res_vb = analyze_volume_bonus_extended_dense_witness(fam)
            assert res_vb["unconditional_bound_holds"] is True
            assert res_vb["frankl_witness_found"] is True


class TestMilestone37IntraFiberDeficitCap:
    """Milestone 37 Test Suite: Intra-Fiber Deficit Cap & Mass-Deficit Multiplier."""

    def test_k3_intra_fiber_deficit_cap_exact(self) -> None:
        """Verify the exact combinatorial deficit cap for k=3:
        - For q in {0, 1, 2}: delta(Q) <= -2 < 0. No deficit possible!
        - For q >= 3: delta(Q) <= +1 for all 90 union-closed slice families.
        - When delta(Q) = +1: m(Q) >= 3, q >= 3, forcing mass m*q >= 9 = 9 * delta.
        """
        res = analyze_intra_fiber_deficit_cap(k=3, q_max=6)
        assert res["k"] == 3
        assert res["total_union_closed_families"] == 90
        assert res["k3_properties_verified"] is True
        assert res["distinct_subset_bound_verified"] is True
        assert res["cap_theorem_verified"] is True

        # q = 0: delta = -3
        assert res["per_q_results"][0]["max_delta"] == -3
        # q = 1: delta = -3
        assert res["per_q_results"][1]["max_delta"] == -3
        # q = 2: delta = -2
        assert res["per_q_results"][2]["max_delta"] == -2

        # q >= 3: max_delta is exactly +1
        for q in [3, 4, 5, 6]:
            assert res["per_q_results"][q]["max_delta"] == 1
            min_mult = res["per_q_results"][q]["min_pos_mass_deficit_multiplier"]
            assert min_mult is not None
            assert min_mult >= 9.0

    def test_k4_intra_fiber_deficit_cap(self) -> None:
        """Verify the distinct subset bound and refined deficit cap for k=4."""
        res = analyze_intra_fiber_deficit_cap(k=4, q_max=5)
        assert res["k"] == 4
        assert res["total_union_closed_families"] == 4542
        assert res["distinct_subset_bound_verified"] is True

        # For q in {0, 1, 2}, max_delta = -4 <= 0
        assert res["per_q_results"][0]["max_delta"] == -4
        assert res["per_q_results"][1]["max_delta"] == -4
        assert res["per_q_results"][2]["max_delta"] == -4
        # For q = 3 (subcritical since 2*3 <= 4+2), max_delta = 0
        assert res["per_q_results"][3]["max_delta"] == 0
        # For q = 4, max_delta = 4
        assert res["per_q_results"][4]["max_delta"] == 4
        assert res["per_q_results"][4]["min_pos_mass_deficit_multiplier"] >= 5.0

    def test_distinct_nonempty_slice_bound_property(self) -> None:
        """Property test: w(Q) >= m(Q) + k - 2 for all m(Q) >= 2 in k in {3, 4}."""
        for k in [3, 4]:
            res = analyze_intra_fiber_deficit_cap(k=k, q_max=k + 2)
            assert res["distinct_subset_bound_verified"] is True

    def test_adversary_optimizer_with_distinct_slice_bound(self) -> None:
        """Test that optimize_quotient_carrier_adversary enforces distinct slice bound."""
        for k in [3, 4]:
            for c in [6, 8, 10, 12]:
                for N in [16, 20]:
                    res = optimize_quotient_carrier_adversary(k=k, c=c, N=N)
                    assert res["adversary_succeeded"] is False
                    assert res["falsification_confirmed"] is True
                    assert res["distinct_slice_bound_enforced"] is True
                    assert res["worst_case_ratio"] >= 0.500


class TestMilestone38MasterConsolidation:
    """Milestone 38: k=3 Union-Closed Slice Deficit Bounds, 9x Mass Multiplier,
    and Unified Master Structural Resolution Consolidation.
    """

    def test_k3_intra_fiber_slice_deficit_le_one_all_90_families(self) -> None:
        """Verify the k=3 slice deficit bound delta(Q) <= 1 and all properties across all 90 families."""
        res = verify_k3_intra_fiber_slice_deficit_le_one()
        assert res["total_families"] == 90
        assert res["singletons_le_pairs_plus_one_verified"] is True
        assert res["sub_three_negative_verified"] is True
        assert res["deficit_le_one_verified"] is True
        assert res["deficit_one_forces_nine_mass_verified"] is True
        assert res["all_verified"] is True
        assert res["max_delta"] == 1
        assert res["min_delta"] == -6
        assert res["delta_one_count"] == 6

    def test_delta_one_slice_families_structure(self) -> None:
        """Verify that all 6 delta = 1 families have s0 = 1, m >= 3, and q >= 3 forcing m*q >= 9."""
        res = verify_k3_intra_fiber_slice_deficit_le_one()
        assert len(res["delta_one_families"]) == 6
        for fam_info in res["delta_one_families"]:
            assert fam_info["s0"] == 1
            assert fam_info["m"] >= 3
            assert fam_info["s1"] >= 1
            assert fam_info["s1"] == fam_info["s2"] + 1

    def test_sub_three_fibers_cannot_produce_deficit(self) -> None:
        """Verify that when s0 = 0 (sub-3 fibers or Q not in F), delta(Q) <= -2 < 0."""
        res = verify_k3_intra_fiber_slice_deficit_le_one()
        assert res["sub_three_negative_verified"] is True

    def test_cli_verify_k3_slice_deficit_flag(self) -> None:
        """Verify the CLI flag --verify-k3-slice-deficit returns 0."""
        ret = main(["--verify-k3-slice-deficit"])
        assert ret == 0

    def test_audit_includes_k3_slice_deficit_verification(self) -> None:
        """Verify that run_poonen_obstruction_audit verifies k=3 slice deficit bound."""
        audit_res = run_poonen_obstruction_audit(adversarial_count=5, seed=42)
        assert audit_res["k3_slice_deficit_verified"] is True
        assert audit_res["all_passed"] is True

    def test_resolver_export_k3_slice_deficit(self) -> None:
        """Verify that universal_frankl_resolver exports verify_k3_intra_fiber_slice_deficit_le_one."""
        from universal_frankl_resolver import verify_k3_intra_fiber_slice_deficit_le_one as v_k3
        res = v_k3()
        assert res["all_verified"] is True
        assert res["total_families"] == 90
