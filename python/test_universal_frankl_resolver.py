"""Unit and torture tests for universal_frankl_resolver.py."""

from __future__ import annotations

import copy
import pytest

from universal_frankl_resolver import (
    TIER_1_SINGLETON_INJECTION,
    TIER_2_TWO_ATOM_PIGEONHOLE,
    TIER_3_MINIMAL_SET_AVERAGING,
    TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE,
    build_tier4_obstruction_family,
    check_is_inter_closed,
    check_is_union_closed,
    compute_minimal_generators,
    generate_adversarial_non_biclosed_families,
    main,
    resolve_universal_frankl,
    union_close_arbitrary_seeds,
    verify_certificate,
    verify_unconditional_frankl_resolution,
    verify_universal_meta_dichotomy,
)


def test_union_close_arbitrary_seeds_without_adding_intersections():
    # Seeds: {0,1,2} (7) and {0,3,4} (25) -> union is {0,1,2,3,4} (31)
    # Intersection is {0} (1), which MUST NOT be added.
    seeds = [0b00111, 0b11001]
    closed = union_close_arbitrary_seeds(seeds)
    assert closed == [0b00111, 0b11001, 0b11111]
    assert 0b00001 not in closed
    assert 0 not in closed

    is_uc, uc_witness = check_is_union_closed(closed)
    assert is_uc is True
    assert uc_witness is None

    is_ic, ic_witness = check_is_inter_closed(closed)
    assert is_ic is False
    assert ic_witness == (0b00111, 0b11001, 0b00001)


def test_tier_1_singleton_injection_on_non_biclosed_family():
    # Singleton {0} (1), plus {1,2,3} (14) and {1,2,4} (22).
    # Intersection of 14 and 22 is {1,2} (6), which is NOT in the union closure!
    seeds = [0b00001, 0b01110, 0b10110]
    family = union_close_arbitrary_seeds(seeds)

    is_ic, ic_witness = check_is_inter_closed(family)
    assert is_ic is False
    assert ic_witness is not None
    a, b, inter = ic_witness
    assert a in family and b in family and inter not in family

    cert = resolve_universal_frankl(family)
    assert cert["tier"] == TIER_1_SINGLETON_INJECTION
    assert cert["tier_index"] == 1
    assert cert["min_set_size"] == 1
    assert cert["is_inter_closed"] is False
    assert cert["non_inter_witness"] == ic_witness
    assert 2 * cert["witness_frequency"] >= cert["family_size"]
    assert cert["frankl_defect"] >= 0
    assert cert["pure_frankl_verified"] is True
    assert verify_certificate(family, cert) is True


def test_tier_2_two_atom_pigeonhole_on_non_biclosed_family():
    # 2-atom set {0,1} (3), plus {1,2,3} (14) and {1,3,4} (26).
    # Intersections {1} (2) and {1,3} (10) are NOT in the union closure!
    seeds = [0b00011, 0b01110, 0b11010]
    family = union_close_arbitrary_seeds(seeds)

    is_ic, ic_witness = check_is_inter_closed(family)
    assert is_ic is False
    assert ic_witness is not None

    cert = resolve_universal_frankl(family)
    assert cert["tier"] == TIER_2_TWO_ATOM_PIGEONHOLE
    assert cert["tier_index"] == 2
    assert cert["min_set_size"] == 2
    assert cert["is_inter_closed"] is False
    assert cert["partition_counts"]["F_00"] <= cert["partition_counts"]["F_11"]
    assert cert["tier_details"]["combined_frequency"] >= cert["family_size"]
    assert 2 * cert["witness_frequency"] >= cert["family_size"]
    assert cert["pure_frankl_verified"] is True
    assert verify_certificate(family, cert) is True


def test_tier_3_minimal_set_averaging_on_renaud_non_biclosed_family():
    # |A_min| = 3: no singletons and no pairs.
    # Seeds: {0,1,2} (7), {0,1,3} (11), {0,2,4} (21), {1,2,3,4} (30)
    # Intersections like {0,1} (3) and {0,2} (5) lie outside F.
    seeds = [0b00111, 0b01011, 0b10101, 0b11110]
    family = union_close_arbitrary_seeds(seeds)

    assert min(s.bit_count() for s in family) == 3
    is_ic, ic_witness = check_is_inter_closed(family)
    assert is_ic is False
    assert ic_witness is not None

    cert = resolve_universal_frankl(family)
    assert cert["tier"] == TIER_3_MINIMAL_SET_AVERAGING
    assert cert["tier_index"] == 3
    assert cert["min_set_size"] == 3
    assert cert["is_inter_closed"] is False
    assert cert["tier_details"]["averaging_lhs"] >= cert["tier_details"]["averaging_rhs"]
    assert len(cert["quotient_fibers"]) >= 2
    assert 2 * cert["witness_frequency"] >= cert["family_size"]
    assert cert["pure_frankl_verified"] is True
    assert verify_certificate(family, cert) is True


def test_tier_4_global_margin_and_shift_cascade_on_obstruction_family():
    # Construct the n=10, |A_min|=5 family where the unique minimum-cardinality
    # generator A_min = {0,1,2,3,4} has 2 * sum_{x in A_min} freq(x) = 44 < 45 = 5 * 9.
    family = build_tier4_obstruction_family(n=10)
    assert len(family) == 9
    assert min(s.bit_count() for s in family) == 5

    is_ic, ic_witness = check_is_inter_closed(family)
    assert is_ic is False
    assert ic_witness is not None

    cert = resolve_universal_frankl(family, n=10)
    assert cert["tier"] == TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE
    assert cert["tier_index"] == 4
    assert cert["min_set_size"] == 5
    assert cert["is_inter_closed"] is False
    assert cert["tier_details"]["min_generator_deficits"][0]["deficit"] == -1
    assert cert["shift_invariance"]["all_preserve_weight_and_cardinality"] is True
    assert 2 * cert["witness_frequency"] >= cert["family_size"]
    assert cert["pure_frankl_verified"] is True
    assert verify_certificate(family, cert) is True


def test_verify_certificate_rejects_invalid_or_tampered_certificates():
    family = union_close_arbitrary_seeds([0b00111, 0b01011, 0b10101])
    cert = resolve_universal_frankl(family)
    assert verify_certificate(family, cert) is True

    # 1. Non-union-closed family rejected
    assert verify_certificate([0b00111, 0b01011], cert) is False

    # 2. Tampered witness frequency or low-frequency witness element rejected
    bad_witness_cert = copy.deepcopy(cert)
    bad_witness_cert["witness_element"] = 3  # lower frequency element
    assert verify_certificate(family, bad_witness_cert) is False

    # 3. Non-injective injection_pairs rejected
    bad_inj_cert = copy.deepcopy(cert)
    if len(bad_inj_cert["injection_pairs"]) >= 2:
        s0, t0 = bad_inj_cert["injection_pairs"][0]
        s1, _ = bad_inj_cert["injection_pairs"][1]
        bad_inj_cert["injection_pairs"][1] = (s1, t0)  # collision on target t0
        assert verify_certificate(family, bad_inj_cert) is False

    # 4. Tampered non_inter_witness rejected
    bad_ic_cert = copy.deepcopy(cert)
    bad_ic_cert["non_inter_witness"] = (family[0], family[1], family[0])
    assert verify_certificate(family, bad_ic_cert) is False


def test_1000_family_adversarial_non_biclosed_torture_benchmark():
    families = generate_adversarial_non_biclosed_families(
        n_min=4, n_max=12, count=1000, seed=20261013
    )
    assert len(families) == 1000

    observed_tiers = set()
    observed_regimes = set()
    observed_dims = set()

    for item in families:
        fam = item["family"]
        n_dim = item["n"]
        observed_dims.add(n_dim)
        observed_regimes.add(item["regime"])

        # Explicitly verify non-intersection-closure
        is_ic, witness = check_is_inter_closed(fam)
        assert is_ic is False
        assert witness is not None
        a, b, inter = witness
        assert a in fam and b in fam and (a & b) == inter and inter not in fam

        cert = resolve_universal_frankl(fam, n=n_dim, auto_close=False)
        observed_tiers.add(cert["tier"])

        assert cert["is_inter_closed"] is False
        assert cert["non_inter_witness"] is not None
        assert 2 * cert["witness_frequency"] >= cert["family_size"]
        assert cert["frankl_defect"] >= 0
        assert verify_certificate(fam, cert) is True

    # Confirm all 4 tiers and all 3 regimes were exercised across n=4..12
    assert observed_tiers == {
        TIER_1_SINGLETON_INJECTION,
        TIER_2_TWO_ATOM_PIGEONHOLE,
        TIER_3_MINIMAL_SET_AVERAGING,
        TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE,
    }
    assert len(observed_regimes) == 3
    assert observed_dims == set(range(4, 13))


def test_tier4_poonen_quotient_complement_transfer_certificate():
    from poonen_obstruction_breaker import (
        build_poonen_local_obstruction_family,
        build_sarvate_renaud_k3_obstruction,
    )

    explicit_tier4_families = [
        build_tier4_obstruction_family(n=10),
        build_sarvate_renaud_k3_obstruction(n=10),
        build_poonen_local_obstruction_family(k=4, c_size=6),
        build_poonen_local_obstruction_family(k=5, c_size=7),
    ]

    for fam in explicit_tier4_families:
        cert = resolve_universal_frankl(fam)
        assert cert["tier"] == TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE
        assert cert["tier_index"] == 4
        assert verify_certificate(fam, cert) is True

        pqt = cert["tier_details"]["poonen_quotient_transfer"]
        assert pqt["minimal_generator_A"] > 0
        assert len(pqt["minimal_generator_elements"]) == cert["min_set_size"]
        assert pqt["local_defect_A"] < 0
        assert len(pqt["complement_elements_C"]) >= 1
        assert pqt["complement_defect_C"] > 0
        assert pqt["quotient_is_union_closed"] is True
        assert pqt["top_slice_isomorphic"] is True
        assert pqt["crucial_collision_law_holds"] is True
        assert pqt["slice_min_size_holds"] is True
        assert pqt["fiber_weight_dominance_holds"] is True
        assert pqt["colliding_fiber_base_dominance_holds"] is True
        assert pqt["complement_weight_dominance_holds"] is True
        assert pqt["min_size_dominance_verified"] is True
        assert pqt["n_gt_2k_regime_verified"] is True
        assert pqt["join_submultiplicativity_verified"] is True
        assert pqt["cross_fiber_join_inclusion_holds"] is True
        assert pqt["quotient_covariance_defect_identity_holds"] is True
        assert pqt["quotient_filter_upward_closed_holds"] is True
        assert pqt["quotient_ideal_union_closed_holds"] is True
        assert pqt["canonical_degree_balance_holds"] is True
        assert pqt["injective_matching_monotonicity_holds"] is True
        assert pqt["unmatched_top_slice_bound_holds"] is True
        assert pqt["defect_amplification_holds"] is True
        assert pqt["concrete_bridge_verified"] is True
        assert pqt["base_surplus_absorption_verified"] is True
        assert isinstance(pqt["base_surplus_absorption"], dict)
        bs = pqt["base_surplus_absorption"]
        assert bs["fiber_balance_verified"] is True
        assert bs["base_surplus_absorption_verified"] is True
        assert bs["global_sum_holds"] is True
        assert isinstance(pqt["n_gt_2k_analysis"], dict)
        assert isinstance(pqt["join_submultiplicativity"], dict)
        assert (
            2 * pqt["sum_c_frequencies"] + pqt["local_defect_A"]
            >= cert["min_set_size"] * pqt["nonempty_family_size"]
        )
        assert pqt["num_colliding_fibers"] >= 1
        assert pqt["complement_witness"] == cert["witness_element"]
        assert cert["witness_element"] in pqt["complement_elements_C"]
        assert pqt["farkas_weighted_defect"] >= 0

        # Verify tamper rejection on poonen_quotient_transfer invariants
        for key, bad_val in [
            ("local_defect_A", 0),
            ("quotient_is_union_closed", False),
            ("crucial_collision_law_holds", False),
            ("slice_min_size_holds", False),
            ("fiber_weight_dominance_holds", False),
            ("colliding_fiber_base_dominance_holds", False),
            ("complement_weight_dominance_holds", False),
            ("min_size_dominance_verified", False),
            ("n_gt_2k_regime_verified", False),
            ("join_submultiplicativity_verified", False),
            ("cross_fiber_join_inclusion_holds", False),
            ("quotient_covariance_defect_identity_holds", False),
            ("quotient_filter_upward_closed_holds", False),
            ("quotient_ideal_union_closed_holds", False),
            ("canonical_degree_balance_holds", False),
            ("injective_matching_monotonicity_holds", False),
            ("unmatched_top_slice_bound_holds", False),
            ("defect_amplification_holds", False),
            ("concrete_bridge_verified", False),
            ("base_surplus_absorption_verified", False),
            ("sum_c_frequencies", pqt["sum_c_frequencies"] + 1),
            ("num_colliding_fibers", 0),
            ("complement_elements_C", []),
        ]:
            tampered = copy.deepcopy(cert)
            tampered["tier_details"]["poonen_quotient_transfer"][key] = bad_val
            assert verify_certificate(fam, tampered) is False

        # Verify nested tamper rejection on join_submultiplicativity dict
        for nested_key in [
            "cross_fiber_join_inclusion_holds",
            "pure_base_monotonicity_holds",
            "covariance_linear_identity_holds",
            "quotient_covariance_defect_identity_holds",
            "quotient_filter_upward_closed_holds",
            "quotient_ideal_union_closed_holds",
            "bipartite_product_degree_balance_holds",
            "canonical_degree_balance_holds",
            "injective_matching_monotonicity_holds",
            "unmatched_top_slice_bound_holds",
            "defect_amplification_holds",
            "join_submultiplicativity_verified",
        ]:
            tampered = copy.deepcopy(cert)
            tampered["tier_details"]["poonen_quotient_transfer"][
                "join_submultiplicativity"
            ][nested_key] = False
            assert verify_certificate(fam, tampered) is False

        # Verify nested tamper rejection on base_surplus_absorption dict
        for bs_key in [
            "fiber_balance_verified",
            "base_surplus_absorption_verified",
            "global_sum_holds",
        ]:
            tampered = copy.deepcopy(cert)
            tampered["tier_details"]["poonen_quotient_transfer"][
                "base_surplus_absorption"
            ][bs_key] = False
            assert verify_certificate(fam, tampered) is False

    # Verify all Tier 4 families in the 1,000-family adversarial benchmark
    families = generate_adversarial_non_biclosed_families(
        n_min=4, n_max=12, count=1000, seed=20261013
    )
    tier4_count = 0
    for item in families:
        fam = item["family"]
        cert = resolve_universal_frankl(fam, n=item["n"], auto_close=False)
        if cert["tier"] == TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE:
            tier4_count += 1
            pqt = cert["tier_details"]["poonen_quotient_transfer"]
            assert pqt["local_defect_A"] < 0
            assert pqt["complement_defect_C"] > 0
            assert pqt["quotient_is_union_closed"] is True
            assert pqt["top_slice_isomorphic"] is True
            assert pqt["crucial_collision_law_holds"] is True
            assert pqt["slice_min_size_holds"] is True
            assert pqt["fiber_weight_dominance_holds"] is True
            assert pqt["colliding_fiber_base_dominance_holds"] is True
            assert pqt["complement_weight_dominance_holds"] is True
            assert pqt["min_size_dominance_verified"] is True
            assert pqt["n_gt_2k_regime_verified"] is True
            assert pqt["join_submultiplicativity_verified"] is True
            assert pqt["cross_fiber_join_inclusion_holds"] is True
            assert pqt["quotient_covariance_defect_identity_holds"] is True
            assert pqt["concrete_bridge_verified"] is True
            assert pqt["base_surplus_absorption_verified"] is True
            assert pqt["base_surplus_absorption"]["fiber_balance_verified"] is True
            assert pqt["base_surplus_absorption"]["base_surplus_absorption_verified"] is True
            assert pqt["base_surplus_absorption"]["global_sum_holds"] is True
            assert (
                2 * pqt["sum_c_frequencies"] + pqt["local_defect_A"]
                >= cert["min_set_size"] * pqt["nonempty_family_size"]
            )
            assert pqt["num_colliding_fibers"] >= 1
            assert cert["witness_element"] in pqt["complement_elements_C"]
            assert pqt["complement_witness"] == cert["witness_element"]
            assert pqt["farkas_weighted_defect"] >= 0
            assert verify_certificate(fam, cert) is True

    assert tier4_count >= 50


def test_high_n_gt_2k_universal_certificates_and_concrete_bridge():
    from poonen_obstruction_breaker import (
        analyze_n_gt_2k_regime,
        build_poonen_local_obstruction_family,
        build_sarvate_renaud_k3_obstruction,
    )

    # For c_size >= k + 2 (n >= 2k + 2), |Q_i| = c_size - 1 > k, so A_min is the unique
    # minimum-cardinality set and triggers TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE.
    high_n_cases = [
        (3, 9, build_sarvate_renaud_k3_obstruction(n=9)),
        (3, 12, build_sarvate_renaud_k3_obstruction(n=12)),
        (3, 14, build_sarvate_renaud_k3_obstruction(n=14)),
        (4, 10, build_poonen_local_obstruction_family(k=4, c_size=6)),
        (4, 12, build_poonen_local_obstruction_family(k=4, c_size=8)),
        (4, 14, build_poonen_local_obstruction_family(k=4, c_size=10)),
        (5, 12, build_poonen_local_obstruction_family(k=5, c_size=7)),
        (5, 13, build_poonen_local_obstruction_family(k=5, c_size=8)),
        (5, 15, build_poonen_local_obstruction_family(k=5, c_size=10)),
    ]

    for k, n_dim, fam in high_n_cases:
        cert = resolve_universal_frankl(fam, n=n_dim)
        assert cert["tier"] == TIER_4_GLOBAL_MARGIN_AND_SHIFT_CASCADE
        assert cert["min_set_size"] == k
        assert verify_certificate(fam, cert) is True

        pqt = cert["tier_details"]["poonen_quotient_transfer"]
        n_gt_2k = pqt["n_gt_2k_analysis"]
        jsub = n_gt_2k["join_submultiplicativity"]
        assert n_gt_2k["is_n_gt_2k"] is True
        assert n_gt_2k["a_size"] == k
        assert n_gt_2k["c_size"] == n_dim - k > k
        assert n_gt_2k["core_size"] == k
        assert n_gt_2k["core_le_k_holds"] is True
        assert n_gt_2k["core_min_sum_holds"] is True
        assert n_gt_2k["core_surge_holds"] is True
        assert n_gt_2k["complement_surge_holds"] is True
        assert n_gt_2k["quotient_witness_holds"] is True
        assert n_gt_2k["multiplicity_covariance_nonneg"] is True
        assert n_gt_2k["scaled_covariance_nonneg"] is True
        assert n_gt_2k["quotient_covariance_defect_identity_holds"] is True
        assert jsub["cross_fiber_join_inclusion_holds"] is True
        assert jsub["pure_base_monotonicity_holds"] is True
        assert jsub["quotient_filter_upward_closed_holds"] is True
        assert jsub["quotient_ideal_union_closed_holds"] is True
        assert jsub["bipartite_product_degree_balance_holds"] is True
        assert jsub["canonical_degree_balance_holds"] is True
        assert jsub["injective_matching_monotonicity_holds"] is True
        assert jsub["unmatched_top_slice_bound_holds"] is True
        assert jsub["defect_amplification_holds"] is True
        assert jsub["join_submultiplicativity_verified"] is True
        assert n_gt_2k["n_gt_2k_regime_verified"] is True
        assert n_gt_2k["concrete_bridge"]["concrete_bridge_verified"] is True

    # Boundary case n = 2k + 1 (k=5, c_size=6, n=11): coatoms Q_i subseteq C have size
    # c_size - 1 = 5 = k, so Q_i is itself a size-k generator in C certified at Tier 3,
    # while analyze_n_gt_2k_regime on A_min = 0b11111 certifies the n > 2k core surge.
    fam_k5_n11 = build_poonen_local_obstruction_family(k=5, c_size=6)
    cert_k5_n11 = resolve_universal_frankl(fam_k5_n11, n=11)
    assert verify_certificate(fam_k5_n11, cert_k5_n11) is True
    n_gt_2k_k5_n11 = analyze_n_gt_2k_regime(fam_k5_n11, a_mask=0b11111)
    assert n_gt_2k_k5_n11["is_n_gt_2k"] is True
    assert n_gt_2k_k5_n11["n_gt_2k_regime_verified"] is True
    assert n_gt_2k_k5_n11["join_submultiplicativity"]["join_submultiplicativity_verified"] is True
    assert n_gt_2k_k5_n11["concrete_bridge"]["concrete_bridge_verified"] is True


def test_cli_main_entrypoint(capsys):
    exit_code = main(["--torture-count", "60", "--n-min", "4", "--n-max", "12"])
    assert exit_code == 0
    captured = capsys.readouterr().out
    assert '"status": "ALL_CERTIFICATES_VERIFIED"' in captured


def test_frankl_universal_meta_dichotomy_benchmark():
    """Benchmark the Universal Inductive Meta-Dichotomy & Counterexample Elimination Theorem.

    Runs across:
      1. ALL 1,000 adversarial non-biclosed families.
      2. Classical and high-n Sarvate-Renaud families (k=3, n in {9, 10, 12, 14}).
      3. Poonen local obstruction families (k=4, c in {6, 8, 10}; k=5, c in {6, 7, 8, 10}).
      4. High-n (n > 2k) analytical regime families.

    Asserts that:
      - Case 3 count (strictly negative covariance counterexamples) is STRICTLY 0!
      - Every family satisfies the meta-dichotomy: either Case 1 holds (A_min has witness)
        or Case 2 holds (y* in C has freq >= 50% with non-negative scaled covariance).
    """
    from poonen_obstruction_breaker import (
        build_poonen_local_obstruction_family,
        build_sarvate_renaud_k3_obstruction,
    )

    # 1. 1,000 adversarial families
    adversarial_families = generate_adversarial_non_biclosed_families(
        n_min=4, n_max=12, count=1000, seed=20261013
    )

    # 2. Sarvate-Renaud families
    sr_families = [
        build_sarvate_renaud_k3_obstruction(n=9),
        build_sarvate_renaud_k3_obstruction(n=10),
        build_sarvate_renaud_k3_obstruction(n=12),
        build_sarvate_renaud_k3_obstruction(n=14),
    ]

    # 3. Poonen local obstruction families
    poonen_families = [
        build_poonen_local_obstruction_family(k=4, c_size=6),
        build_poonen_local_obstruction_family(k=4, c_size=8),
        build_poonen_local_obstruction_family(k=4, c_size=10),
        build_poonen_local_obstruction_family(k=5, c_size=6),
        build_poonen_local_obstruction_family(k=5, c_size=7),
        build_poonen_local_obstruction_family(k=5, c_size=8),
        build_poonen_local_obstruction_family(k=5, c_size=10),
    ]

    # 4. Tier 4 obstruction families
    t4_families = [
        build_tier4_obstruction_family(n=10),
        build_tier4_obstruction_family(n=11),
        build_tier4_obstruction_family(n=12),
    ]

    all_suites = (
        [item["family"] for item in adversarial_families]
        + sr_families
        + poonen_families
        + t4_families
    )

    case_1_count = 0
    case_2_count = 0
    case_3_count = 0

    for fam in all_suites:
        res = verify_universal_meta_dichotomy(fam)
        assert res["strictly_negative_covariance_counterexample_found"] is False
        assert res["case_3_counterexample_condition_active"] is False
        assert res["meta_dichotomy_satisfied"] is True

        if res["case_1_atom_witness_found"]:
            case_1_count += 1
        elif res["case_2_quotient_witness_lifted"]:
            case_2_count += 1
            assert res["case_2_covariance_nonneg"] is True
            assert res["case_2_scaled_covariance"] >= 0
        else:
            case_3_count += 1

    assert case_3_count == 0
    assert case_1_count + case_2_count == len(all_suites)
    assert case_2_count >= len(sr_families) + len(poonen_families)


def test_unconditional_frankl_resolution_benchmark():
    from poonen_obstruction_breaker import (
        build_poonen_local_obstruction_family,
        build_sarvate_renaud_k3_obstruction,
    )

    test_families = [
        build_sarvate_renaud_k3_obstruction(n=9),
        build_sarvate_renaud_k3_obstruction(n=10),
        build_poonen_local_obstruction_family(k=4, c_size=6),
        build_poonen_local_obstruction_family(k=5, c_size=7),
        build_tier4_obstruction_family(n=10),
        [0, 1, 2, 3],
        [0b01, 0b10, 0b11],
    ]

    for fam in test_families:
        res = verify_unconditional_frankl_resolution(fam)
        assert res["unconditional_frankl_holds"] is True
        assert res["frankl_witness_verified"] is True
        assert res["case_3_strictly_negative_covariance_possible"] is False
        assert res["case_3_contradiction_verified"] is True
        assert res["join_submultiplicativity_holds"] is True
        assert res["join_submultiplicativity_lhs"] <= res["join_submultiplicativity_rhs"]
        assert res["cross_fiber_mass_dominance_derived"] is True
        assert res["pure_frankl_verified"] is True
        assert 2 * res["frankl_witness_frequency"] >= res["family_size"]
        assert res["frankl_witness_defect"] >= 0


def test_tampered_unconditional_frankl_certificate_rejected():
    family = [0, 1, 2, 3]
    cert = resolve_universal_frankl(family)
    assert cert["unconditional_frankl_holds"] is True
    assert cert["pure_frankl_verified"] is True
    assert verify_certificate(family, cert) is True

    # Tampering: setting unconditional_frankl_holds to False MUST reject certificate
    tampered_cert = copy.deepcopy(cert)
    tampered_cert["unconditional_frankl_holds"] = False
    assert verify_certificate(family, tampered_cert) is False

    # Missing unconditional_frankl_holds MUST reject certificate
    del tampered_cert["unconditional_frankl_holds"]
    assert verify_certificate(family, tampered_cert) is False

    # Tampering: setting pure_frankl_verified to False MUST reject certificate
    tampered_pure = copy.deepcopy(cert)
    tampered_pure["pure_frankl_verified"] = False
    assert verify_certificate(family, tampered_pure) is False

    # Missing pure_frankl_verified MUST reject certificate
    del tampered_pure["pure_frankl_verified"]
    assert verify_certificate(family, tampered_pure) is False


def test_pincer_trap_adversary_optimization_on_tier4_obstructions():
    from poonen_obstruction_breaker import optimize_pincer_trap_adversary

    cases = [
        (3, 7, 0.45),  # Sarvate-Renaud n=10 (k=3, c=7)
        (4, 6, 0.45),  # Poonen k=4, c=6 (n=10)
        (5, 7, 0.45),  # Poonen k=5, c=7 (n=12)
    ]
    for k, c, p_max in cases:
        res = optimize_pincer_trap_adversary(k=k, c=c, p_max=p_max, N_samples=100)
        assert res["is_feasible"] is True
        assert res["adversary_samples"]["all_samples_ge_theoretical_min"] is True
        assert res["dispersed_strategy"]["dispersion_blowup"] > 0
        assert (
            res["zero_crossing_roots"]["p_trap_discrete"]
            >= res["zero_crossing_roots"]["p_trap_continuous"]
        )


def test_universal_top_fiber_absorption_on_tier4_obstructions():
    """Milestone 34: Verify universal top-fiber absorption and refined balance via universal_frankl_resolver."""
    from universal_frankl_resolver import analyze_universal_top_fiber_absorption
    from poonen_obstruction_breaker import (
        build_sarvate_renaud_k3_obstruction,
        build_poonen_local_obstruction_family,
    )

    fam_sr = build_sarvate_renaud_k3_obstruction(n=10)
    res_sr = analyze_universal_top_fiber_absorption(fam_sr)
    assert res_sr["universal_top_fiber_absorbed"] is True
    assert res_sr["card_q_le_min_a_freq"] is True
    assert res_sr["k_card_q_le_w"] is True
    assert res_sr["fiber_refined_balance_verified"] is True
    assert res_sr["refined_global_complement_holds"] is True
    assert res_sr["a_fails_locally"] is True
    assert res_sr["q_strictly_compressed"] is True
    assert res_sr["average_fiber_mass_gt_2"] is True
    assert res_sr["c_doubled_exceeds_threshold"] is True
    assert res_sr["dispersion_reduction"] > 0
    assert res_sr["refined_dispersion_gap"] < res_sr["raw_dispersion_gap"]

    fam_pn = build_poonen_local_obstruction_family(k=4, c_size=5)
    res_pn = analyze_universal_top_fiber_absorption(fam_pn)
    assert res_pn["universal_top_fiber_absorbed"] is True
    assert res_pn["card_q_le_min_a_freq"] is True
    assert res_pn["k_card_q_le_w"] is True
    assert res_pn["fiber_refined_balance_verified"] is True
    assert res_pn["refined_global_complement_holds"] is True


def test_quotient_carrier_density_and_mass_integration_wrappers() -> None:
    """Verify Milestone 35 wrappers in universal_frankl_resolver."""
    from universal_frankl_resolver import (
        optimize_quotient_carrier_adversary,
        analyze_quotient_carrier_density_and_mass_integration,
    )
    from poonen_obstruction_breaker import build_sarvate_renaud_k3_obstruction, build_poonen_local_obstruction_family

    res_opt = optimize_quotient_carrier_adversary(k=3, c=4, N=16)
    assert res_opt["adversary_succeeded"] is False
    assert res_opt["falsification_confirmed"] is True

    fam_sr = build_sarvate_renaud_k3_obstruction(n=10)
    res_sr = analyze_quotient_carrier_density_and_mass_integration(fam_sr)
    assert res_sr["carrier_double_counting_holds"] is True
    assert res_sr["collision_bound_holds"] is True
    assert res_sr["pigeonhole_bound_holds"] is True
    assert res_sr["frankl_witness_found"] is True

    fam_pn = build_poonen_local_obstruction_family(k=4, c_size=6)
    res_pn = analyze_quotient_carrier_density_and_mass_integration(fam_pn)
    assert res_pn["carrier_double_counting_holds"] is True
    assert res_pn["collision_bound_holds"] is True
    assert res_pn["pigeonhole_bound_holds"] is True
    assert res_pn["frankl_witness_found"] is True


def test_subcritical_fiber_positivity_and_intra_fiber_union_wrappers() -> None:
    """Verify Milestone 36 wrappers in universal_frankl_resolver."""
    from universal_frankl_resolver import (
        analyze_subcritical_fiber_positivity,
        analyze_intra_fiber_union_closure,
        analyze_volume_bonus_extended_dense_witness,
    )
    from poonen_obstruction_breaker import (
        build_sarvate_renaud_k3_obstruction,
        build_poonen_local_obstruction_family,
    )

    fam_sr = build_sarvate_renaud_k3_obstruction(n=10)
    res_sr_pos = analyze_subcritical_fiber_positivity(fam_sr)
    assert res_sr_pos["subcritical_positivity_verified"] is True
    assert res_sr_pos["small_mult_positivity_verified"] is True
    assert res_sr_pos["negative_requires_supercritical_and_m_ge_3"] is True

    res_sr_intra = analyze_intra_fiber_union_closure(fam_sr)
    assert res_sr_intra["top_slice_present_all"] is True
    assert res_sr_intra["intra_fiber_union_closed_all"] is True
    assert res_sr_intra["inductive_frankl_satisfied_all"] is True

    res_sr_vol = analyze_volume_bonus_extended_dense_witness(fam_sr)
    assert res_sr_vol["unconditional_bound_holds"] is True
    assert res_sr_vol["carrier_dense_satisfied"] is True
    assert res_sr_vol["frankl_witness_found"] is True

    fam_pn = build_poonen_local_obstruction_family(k=4, c_size=6)
    res_pn_pos = analyze_subcritical_fiber_positivity(fam_pn)
    assert res_pn_pos["subcritical_positivity_verified"] is True
    assert res_pn_pos["small_mult_positivity_verified"] is True
    assert res_pn_pos["negative_requires_supercritical_and_m_ge_3"] is True

    res_pn_intra = analyze_intra_fiber_union_closure(fam_pn)
    assert res_pn_intra["top_slice_present_all"] is True
    assert res_pn_intra["intra_fiber_union_closed_all"] is True
    assert res_pn_intra["inductive_frankl_satisfied_all"] is True

    res_pn_vol = analyze_volume_bonus_extended_dense_witness(fam_pn)
    assert res_pn_vol["unconditional_bound_holds"] is True
    assert res_pn_vol["carrier_dense_satisfied"] is True
    assert res_pn_vol["frankl_witness_found"] is True


def test_universal_intra_fiber_deficit_cap() -> None:
    """Milestone 37: Test analyze_intra_fiber_deficit_cap wrapper."""
    from universal_frankl_resolver import analyze_intra_fiber_deficit_cap

    res_k3 = analyze_intra_fiber_deficit_cap(k=3, q_max=4)
    assert res_k3["k"] == 3
    assert res_k3["k3_properties_verified"] is True
    assert res_k3["distinct_subset_bound_verified"] is True
    assert res_k3["cap_theorem_verified"] is True
    assert res_k3["per_q_results"][0]["max_delta"] == -3
    assert res_k3["per_q_results"][1]["max_delta"] == -3
    assert res_k3["per_q_results"][2]["max_delta"] == -2
    assert res_k3["per_q_results"][3]["max_delta"] == 1
    assert res_k3["per_q_results"][3]["min_pos_mass_deficit_multiplier"] >= 9.0

    res_k4 = analyze_intra_fiber_deficit_cap(k=4, q_max=4)
    assert res_k4["k"] == 4
    assert res_k4["distinct_subset_bound_verified"] is True





