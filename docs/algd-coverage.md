# alg-d coverage report

**Environment:** Lean v4.35.0 · mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`

This report counts the rows of the [alg-d ledgers](ledger/algd/) against the [source index](algd-source-index.md). The tables between the `GENERATED` markers are written by `python3 checks/ledger.py --write`. The **Ledger checks** CI job fails when they do not match the ledgers, so do not edit them by hand. The definitions follow the [Category strategy](Project_Episteme_Category_Strategy.md#6-ledger-and-verification-rules):

- **Mapped** means an item has a ledger row.
- **Verified** means all of the following: the row's status is `existing`, `bridged`, or `new-proved`; it names a Lean declaration; `lake build` succeeds; the axiom audit passes; and the statement has been reviewed against the source.

`unreviewed` rows are mapped but not verified. The mathlib candidates in those rows were checked to exist (`#check` on every cited name under the pin), but they have not been matched against the source statement.

## Summary

<!-- BEGIN GENERATED: summary -->
| Scope | PDFs cataloged | Numbers 1..max with a row | Ledger rows | Verified | Exercises cataloged |
| --- | --- | --- | --- | --- | --- |
| Chapter 0 | 8 / 8 | 120 / 120 | 189 | 0 | 2 |
| Chapter 1 | 5 / 5 | 121 / 121 | 175 | 154 | 0 |
| Chapter 2 | 4 / 10 | 96 / 202 | 141 | 124 | 0 |
| **Chapters 0–2** | **17 / 23** | **337 / 443** | **505** | **278** | **2** |

Verified main-text items: **278** (197 numbered items and 81 definitions or prose claims). Exercises cataloged: **2**.
<!-- END GENERATED: summary -->

The two Chapter 0 exercises are ALGD-C0-CDIAG-E01 and -E02. They will be proved in a later phase.

## By document

Numbered counts the numbers 1..max, split into statements and labelled displays (equations). D, R, and E count the unnumbered definitions, prose claims, and exercises. The status columns count rows.

<!-- BEGIN GENERATED: by-document -->
| Ledger | Rows | Numbered (items + equations) | D | R | E | unreviewed | existing | bridged | new-proved | blocked | non-propositional | Verified |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| [C0-CDIAG](ledger/algd/C0-CDIAG.md) | 9 | 3 (1 + 2) | 3 | 1 | 2 | 9 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-CONSTR](ledger/algd/C0-CONSTR.md) | 19 | 12 (12 + 0) | 7 | 0 | 0 | 19 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-DUAL](ledger/algd/C0-DUAL.md) | 29 | 20 (20 + 0) | 7 | 2 | 0 | 29 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-EQUIV](ledger/algd/C0-EQUIV.md) | 30 | 20 (20 + 0) | 7 | 3 | 0 | 30 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-FUNDGPD](ledger/algd/C0-FUNDGPD.md) | 22 | 11 (11 + 0) | 7 | 4 | 0 | 22 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-INTRO](ledger/algd/C0-INTRO.md) | 44 | 32 (32 + 0) | 8 | 4 | 0 | 44 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-SHEAF](ledger/algd/C0-SHEAF.md) | 13 | 8 (7 + 1) | 4 | 1 | 0 | 13 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-UNIV](ledger/algd/C0-UNIV.md) | 23 | 14 (14 + 0) | 7 | 2 | 0 | 23 | 0 | 0 | 0 | 0 | 0 | 0 |
| **Chapter 0** | **189** | **120 (117 + 3)** | **50** | **17** | **2** | **189** | **0** | **0** | **0** | **0** | **0** | **0** |
| [C1-ADJOINT](ledger/algd/C1-ADJOINT.md) | 72 | 56 (55 + 1) | 9 | 7 | 0 | 0 | 26 | 19 | 23 | 3 | 1 | 68 |
| [C1-COMMA](ledger/algd/C1-COMMA.md) | 10 | 8 (8 + 0) | 2 | 0 | 0 | 0 | 3 | 2 | 4 | 0 | 1 | 9 |
| [C1-LIMIT](ledger/algd/C1-LIMIT.md) | 51 | 33 (30 + 3) | 14 | 4 | 0 | 0 | 13 | 18 | 12 | 0 | 8 | 43 |
| [C1-NAT](ledger/algd/C1-NAT.md) | 23 | 13 (13 + 0) | 8 | 2 | 0 | 0 | 12 | 6 | 4 | 0 | 1 | 22 |
| [C1-YONEDA](ledger/algd/C1-YONEDA.md) | 19 | 11 (9 + 2) | 5 | 3 | 0 | 5 | 7 | 4 | 1 | 0 | 2 | 12 |
| **Chapter 1** | **175** | **121 (115 + 6)** | **38** | **16** | **0** | **5** | **61** | **49** | **44** | **3** | **13** | **154** |
| [C2-AFT](ledger/algd/C2-AFT.md) | 36 | 24 (23 + 1) | 11 | 1 | 0 | 6 | 4 | 15 | 10 | 0 | 1 | 29 |
| [C2-COYONEDA](ledger/algd/C2-COYONEDA.md) | 6 | 2 (2 + 0) | 0 | 4 | 0 | 0 | 1 | 2 | 3 | 0 | 0 | 6 |
| [C2-FILTERED](ledger/algd/C2-FILTERED.md) | 27 | 15 (15 + 0) | 9 | 3 | 0 | 0 | 6 | 9 | 9 | 0 | 3 | 24 |
| [C2-KAN](ledger/algd/C2-KAN.md) | 72 | 55 (47 + 8) | 12 | 5 | 0 | 0 | 23 | 11 | 31 | 0 | 7 | 65 |
| **Chapter 2** | **141** | **96 (87 + 9)** | **32** | **13** | **0** | **6** | **34** | **37** | **53** | **0** | **11** | **124** |
<!-- END GENERATED: by-document -->

## Verified declarations

<!-- BEGIN GENERATED: verified -->
| Ledger ID | Lean declaration | Status |
| --- | --- | --- |
| ALGD-C1-ADJOINT-D01 | `ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction` | bridged |
| ALGD-C1-ADJOINT-01 | `ProjectEpisteme.AlgD.Adjoint.square_iff` | existing |
| ALGD-C1-ADJOINT-02 | `ProjectEpisteme.AlgD.Adjoint.factor_iff` | bridged |
| ALGD-C1-ADJOINT-D03 | `ProjectEpisteme.AlgD.Adjoint.unit_app_eq` | existing |
| ALGD-C1-ADJOINT-03 | `ProjectEpisteme.AlgD.Adjoint.unit_universal` | bridged |
| ALGD-C1-ADJOINT-04 | `ProjectEpisteme.AlgD.Adjoint.universalArrow_exists_iff` | new-proved |
| ALGD-C1-ADJOINT-05 | `ProjectEpisteme.AlgD.Adjoint.homEquiv_eq_unit` | existing |
| ALGD-C1-ADJOINT-06 | `ProjectEpisteme.AlgD.Adjoint.universalArrows_leftAdjoint` | bridged |
| ALGD-C1-ADJOINT-R01 | `ProjectEpisteme.AlgD.Adjoint.isRightAdjoint_iff_corepresentable` | bridged |
| ALGD-C1-ADJOINT-D04 | `ProjectEpisteme.AlgD.Adjoint.unit_naturality` | existing |
| ALGD-C1-ADJOINT-07 | `ProjectEpisteme.AlgD.Adjoint.leftAdjoint_unique` | existing |
| ALGD-C1-ADJOINT-08 | `ProjectEpisteme.AlgD.Adjoint.leftAdjoint_preserves_colimit` | existing |
| ALGD-C1-ADJOINT-09 | `ProjectEpisteme.AlgD.Adjoint.op_adjunction` | existing |
| ALGD-C1-ADJOINT-10 | `ProjectEpisteme.AlgD.Adjoint.counit_dual` | bridged |
| ALGD-C1-ADJOINT-11 | `ProjectEpisteme.AlgD.Adjoint.colim_adjunction` | existing |
| ALGD-C1-ADJOINT-12 | `ProjectEpisteme.AlgD.Adjoint.free_abelian_group` | bridged |
| ALGD-C1-ADJOINT-13 | `ProjectEpisteme.AlgD.Adjoint.top_discrete_indiscrete` | existing |
| ALGD-C1-ADJOINT-D05 | `ProjectEpisteme.AlgD.Adjoint.split_iff` | existing |
| ALGD-C1-ADJOINT-14 | `ProjectEpisteme.AlgD.Adjoint.split_epi_mono` | existing |
| ALGD-C1-ADJOINT-15 | `ProjectEpisteme.AlgD.Adjoint.isIso_of_mono_of_split_epi` | existing |
| ALGD-C1-ADJOINT-R02 | `ProjectEpisteme.AlgD.Adjoint.isIso_of_epi_of_split_mono` | existing |
| ALGD-C1-ADJOINT-16 | `ProjectEpisteme.AlgD.Adjoint.map_split_epi` | existing |
| ALGD-C1-ADJOINT-17 | `ProjectEpisteme.AlgD.Adjoint.yoneda_split` | bridged |
| ALGD-C1-ADJOINT-18 | `ProjectEpisteme.AlgD.Adjoint.faithful_full_criteria` | existing |
| ALGD-C1-ADJOINT-19 | `ProjectEpisteme.AlgD.Adjoint.triple_fullyFaithful` | bridged |
| ALGD-C1-ADJOINT-20 | `ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction.right_triangle` | new-proved |
| ALGD-C1-ADJOINT-R03 | `ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction.left_triangle` | new-proved |
| ALGD-C1-ADJOINT-21 | `ProjectEpisteme.AlgD.Adjoint.adjunction_of_triangle` | bridged |
| ALGD-C1-ADJOINT-D06 | `CategoryTheory.Adjunction` | existing |
| ALGD-C1-ADJOINT-22 | `ProjectEpisteme.AlgD.Adjoint.counit_isIso_of_iso` | existing |
| ALGD-C1-ADJOINT-23 | `ProjectEpisteme.AlgD.Adjoint.adjunction_of_equivalence` | bridged |
| ALGD-C1-ADJOINT-24 | `ProjectEpisteme.AlgD.Adjoint.equivalence_preserves` | existing |
| ALGD-C1-ADJOINT-25 | `ProjectEpisteme.AlgD.Adjoint.hasColimits_of_equivalence` | existing |
| ALGD-C1-ADJOINT-R04 | `ProjectEpisteme.AlgD.Adjoint.unit_counit_iso_consequences` | bridged |
| ALGD-C1-ADJOINT-R05 | `ProjectEpisteme.AlgD.Adjoint.isEquivalence_of_fullyFaithful` | bridged |
| ALGD-C1-ADJOINT-R06 | `ProjectEpisteme.AlgD.Adjoint.free_vectorSpace` | new-proved |
| ALGD-C1-ADJOINT-26 | `ProjectEpisteme.AlgD.Adjoint.comp_adjunction` | existing |
| ALGD-C1-ADJOINT-27 | `ProjectEpisteme.AlgD.Adjoint.postcomp_adjunction` | existing |
| ALGD-C1-ADJOINT-28 | `ProjectEpisteme.AlgD.Adjoint.precomp_adjunction` | existing |
| ALGD-C1-ADJOINT-29 | `ProjectEpisteme.AlgD.Adjoint.presheaf_adjunction` | bridged |
| ALGD-C1-ADJOINT-D07 | `ProjectEpisteme.AlgD.Adjoint.unitFixed_le_essImage` | new-proved |
| ALGD-C1-ADJOINT-30 | `ProjectEpisteme.AlgD.Adjoint.fixedPoint_equivalence` | new-proved |
| ALGD-C1-ADJOINT-31 | `ProjectEpisteme.AlgD.Adjoint.idempotent_tfae` | new-proved |
| ALGD-C1-ADJOINT-32 | `ProjectEpisteme.AlgD.Adjoint.idempotent_iff_factorization` | new-proved |
| ALGD-C1-ADJOINT-33 | `ProjectEpisteme.AlgD.Adjoint.unitFixed_reflective` | new-proved |
| ALGD-C1-ADJOINT-34 | `ProjectEpisteme.AlgD.Adjoint.factorization_equivalence` | new-proved |
| ALGD-C1-ADJOINT-D08 | `ProjectEpisteme.AlgD.Adjoint.IsExponential` | new-proved |
| ALGD-C1-ADJOINT-35 | `ProjectEpisteme.AlgD.Adjoint.types_exponential` | new-proved |
| ALGD-C1-ADJOINT-36 | `ProjectEpisteme.AlgD.Adjoint.exponential_adjunction` | bridged |
| ALGD-C1-ADJOINT-D09 | `ProjectEpisteme.AlgD.Adjoint.IsCartesianClosed` | bridged |
| ALGD-C1-ADJOINT-R07 | `ProjectEpisteme.AlgD.Adjoint.exponential_of_rightAdjoint` | bridged |
| ALGD-C1-ADJOINT-37 | `ProjectEpisteme.AlgD.Adjoint.exponential_preserves` | bridged |
| ALGD-C1-ADJOINT-38 | `ProjectEpisteme.AlgD.Adjoint.exponential_exponential` | new-proved |
| ALGD-C1-ADJOINT-39 | `ProjectEpisteme.AlgD.Adjoint.exponential_coprod` | new-proved |
| ALGD-C1-ADJOINT-40 | `ProjectEpisteme.AlgD.Adjoint.exponential_initial_unit` | new-proved |
| ALGD-C1-ADJOINT-41 | `ProjectEpisteme.AlgD.Adjoint.parametrized_adjunction` | new-proved |
| ALGD-C1-ADJOINT-42 | `ProjectEpisteme.AlgD.Adjoint.parametrized_square_iff` | new-proved |
| ALGD-C1-ADJOINT-43 | `ProjectEpisteme.AlgD.Adjoint.exponential_bifunctor` | new-proved |
| ALGD-C1-ADJOINT-44 | `ProjectEpisteme.AlgD.Adjoint.ab_not_cartesianClosed` | new-proved |
| ALGD-C1-ADJOINT-45 | `ProjectEpisteme.AlgD.Adjoint.free_group` | existing |
| ALGD-C1-ADJOINT-46 | `ProjectEpisteme.AlgD.Adjoint.abelianization` | existing |
| ALGD-C1-ADJOINT-47 | `ProjectEpisteme.AlgD.Adjoint.module_forget` | bridged |
| ALGD-C1-ADJOINT-48 | `ProjectEpisteme.AlgD.Adjoint.top_adjoint_triple` | existing |
| ALGD-C1-ADJOINT-49 | `ProjectEpisteme.AlgD.Adjoint.monoid_ring` | new-proved |
| ALGD-C1-ADJOINT-50 | `ProjectEpisteme.AlgD.Adjoint.Ex50.polynomial_adjunction` | new-proved |
| ALGD-C1-ADJOINT-51 | `ProjectEpisteme.AlgD.Adjoint.Ex51.fractionField_adjunction` | new-proved |
| ALGD-C1-ADJOINT-54 | `ProjectEpisteme.AlgD.Adjoint.stoneCech_adjunction` | existing |
| ALGD-C1-ADJOINT-56 | `ProjectEpisteme.AlgD.Adjoint.Ex56.idem_adjunctions` | new-proved |
| ALGD-C1-COMMA-D01 | `ProjectEpisteme.AlgD.CommaCategory.comma_category` | existing |
| ALGD-C1-COMMA-01 | `ProjectEpisteme.AlgD.CommaCategory.comma_id_fromPUnit` | existing |
| ALGD-C1-COMMA-02 | `ProjectEpisteme.AlgD.CommaCategory.comma_to_punit` | bridged |
| ALGD-C1-COMMA-03 | `ProjectEpisteme.AlgD.CommaCategory.comma_id_id` | new-proved |
| ALGD-C1-COMMA-05 | `ProjectEpisteme.AlgD.CommaCategory.elements_op_iso` | new-proved |
| ALGD-C1-COMMA-06 | `ProjectEpisteme.AlgD.CommaCategory.comma_op` | bridged |
| ALGD-C1-COMMA-D02 | `ProjectEpisteme.AlgD.CommaCategory.projections` | existing |
| ALGD-C1-COMMA-07 | `ProjectEpisteme.AlgD.CommaCategory.universal_property` | new-proved |
| ALGD-C1-COMMA-08 | `ProjectEpisteme.AlgD.CommaCategory.natTrans_equiv_sections` | new-proved |
| ALGD-C1-LIMIT-D01 | `ProjectEpisteme.AlgD.Limit.CoproductTriple` | new-proved |
| ALGD-C1-LIMIT-01 | `ProjectEpisteme.AlgD.Limit.coproduct_iff_isInitial` | bridged |
| ALGD-C1-LIMIT-D02 | `ProjectEpisteme.AlgD.Limit.PushoutTriple` | new-proved |
| ALGD-C1-LIMIT-03 | `ProjectEpisteme.AlgD.Limit.pushout_iff_isInitial` | bridged |
| ALGD-C1-LIMIT-D03 | `ProjectEpisteme.AlgD.Limit.CoequalizerPair` | new-proved |
| ALGD-C1-LIMIT-04 | `ProjectEpisteme.AlgD.Limit.coequalizer_iff_isInitial` | bridged |
| ALGD-C1-LIMIT-05 | `ProjectEpisteme.AlgD.Limit.spanComma_iso_pushoutTriple` | new-proved |
| ALGD-C1-LIMIT-07 | `ProjectEpisteme.AlgD.Limit.parallelPairComma_iso_coequalizerPair` | new-proved |
| ALGD-C1-LIMIT-08 | `ProjectEpisteme.AlgD.Limit.pairComma_iso_coproductTriple` | new-proved |
| ALGD-C1-LIMIT-D07 | `ProjectEpisteme.AlgD.Limit.universalArrow_iff` | bridged |
| ALGD-C1-LIMIT-D08 | `ProjectEpisteme.AlgD.Limit.limit_iff_terminal_colimit_iff_initial` | bridged |
| ALGD-C1-LIMIT-09 | `ProjectEpisteme.AlgD.Limit.fan_isLimit_iff` | bridged |
| ALGD-C1-LIMIT-10 | `ProjectEpisteme.AlgD.Limit.decreasing_sequence_limit` | bridged |
| ALGD-C1-LIMIT-11 | `ProjectEpisteme.AlgD.Limit.padic_limit` | new-proved |
| ALGD-C1-LIMIT-D10 | `ProjectEpisteme.AlgD.Limit.completeness_definitions` | existing |
| ALGD-C1-LIMIT-12 | `ProjectEpisteme.AlgD.Limit.types_limit` | bridged |
| ALGD-C1-LIMIT-13 | `ProjectEpisteme.AlgD.Limit.types_colimit` | bridged |
| ALGD-C1-LIMIT-15 | `ProjectEpisteme.AlgD.Limit.cocomplete_of_coproducts_coequalizers` | existing |
| ALGD-C1-LIMIT-16 | `ProjectEpisteme.AlgD.Limit.complete_of_products_equalizers` | existing |
| ALGD-C1-LIMIT-17 | `ProjectEpisteme.AlgD.Limit.finitelyComplete_finitelyCocomplete` | existing |
| ALGD-C1-LIMIT-18 | `ProjectEpisteme.AlgD.Limit.colimit_functor_unique` | new-proved |
| ALGD-C1-LIMIT-19 | `ProjectEpisteme.AlgD.Limit.iterated_colimit_iff` | new-proved |
| ALGD-C1-LIMIT-R01 | `ProjectEpisteme.AlgD.Limit.colimits_commute` | bridged |
| ALGD-C1-LIMIT-20 | `ProjectEpisteme.AlgD.Limit.functorCategory_colimit_pointwise` | existing |
| ALGD-C1-LIMIT-21 | `ProjectEpisteme.AlgD.Limit.functorCategory_cocomplete_complete` | existing |
| ALGD-C1-LIMIT-22 | `ProjectEpisteme.AlgD.Limit.presheaf_complete_cocomplete` | existing |
| ALGD-C1-LIMIT-23 | `ProjectEpisteme.AlgD.Limit.Ex23.counterexample` | new-proved |
| ALGD-C1-LIMIT-D12 | `ProjectEpisteme.AlgD.Limit.representable_iff` | bridged |
| ALGD-C1-LIMIT-24 | `ProjectEpisteme.AlgD.Limit.representing_object_unique` | bridged |
| ALGD-C1-LIMIT-25 | `ProjectEpisteme.AlgD.Limit.isIso_iff_unique_factorization` | bridged |
| ALGD-C1-LIMIT-R02 | `ProjectEpisteme.AlgD.Limit.condition_iff_isInitial` | bridged |
| ALGD-C1-LIMIT-26 | `ProjectEpisteme.AlgD.Limit.representable_iff_hasInitial` | bridged |
| ALGD-C1-LIMIT-27 | `ProjectEpisteme.AlgD.Limit.universalArrow_exists_iff` | new-proved |
| ALGD-C1-LIMIT-28 | `ProjectEpisteme.AlgD.Limit.universalArrow_from_exists_iff` | new-proved |
| ALGD-C1-LIMIT-29 | `ProjectEpisteme.AlgD.Limit.binaryFan_isLimit_iff_bijective` | bridged |
| ALGD-C1-LIMIT-D13 | `ProjectEpisteme.AlgD.Limit.commutes_with_colimit_iff` | bridged |
| ALGD-C1-LIMIT-D14 | `ProjectEpisteme.AlgD.Limit.cocontinuous_continuous_iff` | existing |
| ALGD-C1-LIMIT-30 | `ProjectEpisteme.AlgD.Limit.coyoneda_preserves_limit` | existing |
| ALGD-C1-LIMIT-31 | `ProjectEpisteme.AlgD.Limit.yoneda_preserves_limits` | existing |
| ALGD-C1-LIMIT-32 | `ProjectEpisteme.AlgD.Limit.evaluation_preserves_colimits` | existing |
| ALGD-C1-LIMIT-R03 | `ProjectEpisteme.AlgD.Limit.evaluation_preserves_limits` | existing |
| ALGD-C1-LIMIT-33 | `ProjectEpisteme.AlgD.Limit.epi_mono_iff_app` | bridged |
| ALGD-C1-LIMIT-R04 | `ProjectEpisteme.AlgD.Limit.post_comparison` | existing |
| ALGD-C1-NAT-D01 | `ProjectEpisteme.AlgD.Nat.vcomp_app` | existing |
| ALGD-C1-NAT-D02 | `ProjectEpisteme.AlgD.Nat.whiskerRight_app` | existing |
| ALGD-C1-NAT-D03 | `ProjectEpisteme.AlgD.Nat.whiskerLeft_app` | existing |
| ALGD-C1-NAT-02 | `ProjectEpisteme.AlgD.Nat.horizontal_composites_eq` | bridged |
| ALGD-C1-NAT-03 | `ProjectEpisteme.AlgD.Nat.interchange` | bridged |
| ALGD-C1-NAT-04 | `ProjectEpisteme.AlgD.Nat.horizontal_eq_vertical_of_id` | bridged |
| ALGD-C1-NAT-D04 | `ProjectEpisteme.AlgD.Nat.functorCategory_hom_id_comp` | existing |
| ALGD-C1-NAT-R01 | `ProjectEpisteme.AlgD.Nat.functorCategory_locallySmall` | existing |
| ALGD-C1-NAT-05 | `ProjectEpisteme.AlgD.Nat.functorCategory_zero_one` | new-proved |
| ALGD-C1-NAT-06 | `ProjectEpisteme.AlgD.Nat.functorCategory_singleObj` | bridged |
| ALGD-C1-NAT-07 | `ProjectEpisteme.AlgD.Nat.functorCategory_discrete_two` | new-proved |
| ALGD-C1-NAT-08 | `ProjectEpisteme.AlgD.Nat.presheaf_hom` | existing |
| ALGD-C1-NAT-09 | `ProjectEpisteme.AlgD.Nat.isIso_iff_isIso_app` | existing |
| ALGD-C1-NAT-D05 | `ProjectEpisteme.AlgD.Nat.postcomposition_obj_map` | existing |
| ALGD-C1-NAT-D06 | `ProjectEpisteme.AlgD.Nat.precomposition_obj_map` | existing |
| ALGD-C1-NAT-10 | `ProjectEpisteme.AlgD.Nat.diagonal` | bridged |
| ALGD-C1-NAT-11 | `ProjectEpisteme.AlgD.Nat.ev_functors` | bridged |
| ALGD-C1-NAT-12 | `ProjectEpisteme.AlgD.Nat.arrowCategory` | new-proved |
| ALGD-C1-NAT-13 | `ProjectEpisteme.AlgD.Nat.powerset_iso_functorCategory` | new-proved |
| ALGD-C1-NAT-D07 | `ProjectEpisteme.AlgD.Nat.partial_functors` | existing |
| ALGD-C1-NAT-D08 | `ProjectEpisteme.AlgD.Nat.curry_map_app` | existing |
| ALGD-C1-NAT-R02 | `ProjectEpisteme.AlgD.Nat.curry_bijective` | existing |
| ALGD-C1-YONEDA-D02 | `CategoryTheory.yoneda` | existing |
| ALGD-C1-YONEDA-D04 | `CategoryTheory.yoneda` | existing |
| ALGD-C1-YONEDA-01 | `ProjectEpisteme.AlgD.Yoneda.yoneda_bijective` | existing |
| ALGD-C1-YONEDA-02 | `ProjectEpisteme.AlgD.Yoneda.yoneda_map_bijective` | existing |
| ALGD-C1-YONEDA-03 | `ProjectEpisteme.AlgD.Yoneda.isIso_iff_isIso_yonedaEquiv` | bridged |
| ALGD-C1-YONEDA-04 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_yoneda_iso` | existing |
| ALGD-C1-YONEDA-05 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_natural_equiv_hom_to` | bridged |
| ALGD-C1-YONEDA-06 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_natural_equiv_hom_from` | bridged |
| ALGD-C1-YONEDA-07 | `ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_symm_natural_iff_natural` | new-proved |
| ALGD-C1-YONEDA-09 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_yoneda_comp_iso` | bridged |
| ALGD-C1-YONEDA-10 | `ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_natural_in_object` | existing |
| ALGD-C1-YONEDA-11 | `ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_natural_in_presheaf` | existing |
| ALGD-C2-AFT-01 | `ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae` | new-proved |
| ALGD-C2-AFT-02 | `ProjectEpisteme.AlgD.Kan.colimit_of_terminal` | existing |
| ALGD-C2-AFT-03 | `ProjectEpisteme.AlgD.Kan.pointwise_tfae` | new-proved |
| ALGD-C2-AFT-D01 | `ProjectEpisteme.AlgD.AFT.IsFinalColim` | new-proved |
| ALGD-C2-AFT-04 | `ProjectEpisteme.AlgD.AFT.isLeftKanExtension_comp_iff` | new-proved |
| ALGD-C2-AFT-06 | `ProjectEpisteme.AlgD.AFT.isFinalColim_of_isRightAdjoint` | bridged |
| ALGD-C2-AFT-07 | `ProjectEpisteme.AlgD.AFT.isFinalColim_of_isEquivalence` | bridged |
| ALGD-C2-AFT-D02 | `CategoryTheory.Zigzag` | existing |
| ALGD-C2-AFT-D03 | `ProjectEpisteme.AlgD.AFT.isConnected_iff_zigzag` | bridged |
| ALGD-C2-AFT-08 | `ProjectEpisteme.AlgD.AFT.isFinalColim_tfae` | bridged |
| ALGD-C2-AFT-09 | `ProjectEpisteme.AlgD.AFT.nonempty_isTerminal_iff_isFinalColim` | new-proved |
| ALGD-C2-AFT-10 | `ProjectEpisteme.AlgD.AFT.isLeftAdjoint_of_leftSolutionSetCondition` | new-proved |
| ALGD-C2-AFT-D04 | `ProjectEpisteme.AlgD.AFT.EpiUnder` | new-proved |
| ALGD-C2-AFT-12 | `ProjectEpisteme.AlgD.AFT.epiUnder_hom_subsingleton` | new-proved |
| ALGD-C2-AFT-D05 | `ProjectEpisteme.AlgD.AFT.Quotients` | new-proved |
| ALGD-C2-AFT-D06 | `ProjectEpisteme.AlgD.AFT.isWellCopowered_iff` | bridged |
| ALGD-C2-AFT-13 | `ProjectEpisteme.AlgD.AFT.isWellCopowered_of_smallCategory` | bridged |
| ALGD-C2-AFT-14 | `ProjectEpisteme.AlgD.AFT.isWellCopowered_type` | new-proved |
| ALGD-C2-AFT-D07 | `ProjectEpisteme.AlgD.AFT.isGeneratingSet_iff` | bridged |
| ALGD-C2-AFT-D08 | `ProjectEpisteme.AlgD.AFT.isGeneratingSet_singleton_iff` | bridged |
| ALGD-C2-AFT-16 | `CategoryTheory.Types.isSeparator_punit` | existing |
| ALGD-C2-AFT-18 | `ProjectEpisteme.AlgD.AFT.preservesColimits_iff_isLeftAdjoint` | bridged |
| ALGD-C2-AFT-D09 | `ProjectEpisteme.AlgD.AFT.isWellPowered_iff` | bridged |
| ALGD-C2-AFT-D10 | `ProjectEpisteme.AlgD.AFT.isCogeneratingSet_iff` | bridged |
| ALGD-C2-AFT-D11 | `ProjectEpisteme.AlgD.AFT.isGeneratingSet_singleton_op_iff` | bridged |
| ALGD-C2-AFT-19 | `CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition` | existing |
| ALGD-C2-AFT-20 | `ProjectEpisteme.AlgD.AFT.preservesLimits_iff_isRightAdjoint` | bridged |
| ALGD-C2-AFT-22 | `ProjectEpisteme.AlgD.AFT.isCorepresentable_of_solutionSetCondition` | bridged |
| ALGD-C2-AFT-23 | `ProjectEpisteme.AlgD.AFT.preservesLimits_tfae` | bridged |
| ALGD-C2-COYONEDA-R01 | `ProjectEpisteme.AlgD.Coyoneda.rightKanExtension_id` | existing |
| ALGD-C2-COYONEDA-R02 | `ProjectEpisteme.AlgD.Coyoneda.yoneda_via_rightKanExtension` | bridged |
| ALGD-C2-COYONEDA-R03 | `ProjectEpisteme.AlgD.Coyoneda.endWedge_isLimit` | new-proved |
| ALGD-C2-COYONEDA-01 | `ProjectEpisteme.AlgD.Coyoneda.coyonedaCowedge_isColimit` | new-proved |
| ALGD-C2-COYONEDA-R04 | `ProjectEpisteme.AlgD.Coyoneda.coendCowedge_isColimit` | new-proved |
| ALGD-C2-COYONEDA-02 | `ProjectEpisteme.AlgD.Coyoneda.presheaf_cartesianClosed` | bridged |
| ALGD-C2-FILTERED-D01 | `ProjectEpisteme.AlgD.Filtered.isFiltered_iff_cocone` | bridged |
| ALGD-C2-FILTERED-D02 | `ProjectEpisteme.AlgD.Filtered.isCofiltered_iff_op` | existing |
| ALGD-C2-FILTERED-01 | `ProjectEpisteme.AlgD.Filtered.isFiltered_iff` | bridged |
| ALGD-C2-FILTERED-02 | `ProjectEpisteme.AlgD.Filtered.isFiltered_of_hasFiniteColimits` | existing |
| ALGD-C2-FILTERED-03 | `ProjectEpisteme.AlgD.Filtered.isFiltered_of_hasTerminal` | existing |
| ALGD-C2-FILTERED-04 | `ProjectEpisteme.AlgD.Filtered.preorder_isFiltered_iff` | bridged |
| ALGD-C2-FILTERED-05 | `ProjectEpisteme.AlgD.Filtered.colim_preservesFiniteLimits` | existing |
| ALGD-C2-FILTERED-06 | `ProjectEpisteme.AlgD.Filtered.structuredArrow_isCofiltered` | existing |
| ALGD-C2-FILTERED-D04 | `ProjectEpisteme.AlgD.Filtered.IsFlat` | new-proved |
| ALGD-C2-FILTERED-07 | `ProjectEpisteme.AlgD.Filtered.isFlat_tfae` | new-proved |
| ALGD-C2-FILTERED-08 | `ProjectEpisteme.AlgD.Filtered.colim_preservesFiniteLimits_iff` | bridged |
| ALGD-C2-FILTERED-09 | `ProjectEpisteme.AlgD.Filtered.isFlat_preservesFiniteLimits` | new-proved |
| ALGD-C2-FILTERED-10 | `ProjectEpisteme.AlgD.Filtered.coyoneda_isFlat` | new-proved |
| ALGD-C2-FILTERED-11 | `ProjectEpisteme.AlgD.Filtered.preservesFiniteLimits_iff_lan` | existing |
| ALGD-C2-FILTERED-12 | `ProjectEpisteme.AlgD.Filtered.TopExample.isEmpty_colimLim_iso_limColim` | new-proved |
| ALGD-C2-FILTERED-D05 | `ProjectEpisteme.AlgD.Filtered.isSiftedSet_iff` | bridged |
| ALGD-C2-FILTERED-D07 | `ProjectEpisteme.AlgD.Filtered.IsSiftedFlat` | new-proved |
| ALGD-C2-FILTERED-R01 | `ProjectEpisteme.AlgD.Filtered.isSiftedSet_of_isFiltered` | bridged |
| ALGD-C2-FILTERED-D09 | `ProjectEpisteme.AlgD.Filtered.Span` | bridged |
| ALGD-C2-FILTERED-13 | `ProjectEpisteme.AlgD.Filtered.span_isConnected_of_isSiftedFlat` | new-proved |
| ALGD-C2-FILTERED-14 | `ProjectEpisteme.AlgD.Filtered.isSifted_tfae` | bridged |
| ALGD-C2-FILTERED-R02 | `ProjectEpisteme.AlgD.Filtered.isSiftedSet_of_hasFiniteCoproducts` | bridged |
| ALGD-C2-FILTERED-R03 | `ProjectEpisteme.AlgD.Filtered.isCosifted_iff` | new-proved |
| ALGD-C2-FILTERED-15 | `ProjectEpisteme.AlgD.Filtered.isSiftedFlat_tfae` | new-proved |
| ALGD-C2-KAN-D01 | `ProjectEpisteme.AlgD.Kan.isLeftKanExtension_iff` | bridged |
| ALGD-C2-KAN-D03 | `ProjectEpisteme.AlgD.Kan.isRightKanExtension_iff` | bridged |
| ALGD-C2-KAN-D04 | `ProjectEpisteme.AlgD.Kan.IsLeftKanLift` | new-proved |
| ALGD-C2-KAN-01 | `ProjectEpisteme.AlgD.Kan.representable_iff_hasLeftKanExtension` | bridged |
| ALGD-C2-KAN-02 | `ProjectEpisteme.AlgD.Kan.lan_ran_adjunction` | existing |
| ALGD-C2-KAN-03 | `ProjectEpisteme.AlgD.Kan.colimit_iff_isLeftKanExtension` | bridged |
| ALGD-C2-KAN-04 | `ProjectEpisteme.AlgD.Kan.pointwise_leftKanExtension` | existing |
| ALGD-C2-KAN-05 | `ProjectEpisteme.AlgD.Kan.hasLeftKanExtension_of_cocomplete` | existing |
| ALGD-C2-KAN-06 | `ProjectEpisteme.AlgD.Kan.presheaf_hasLeftKanExtension` | existing |
| ALGD-C2-KAN-R01 | `ProjectEpisteme.AlgD.Kan.presheaf_lan_adjunction` | existing |
| ALGD-C2-KAN-07 | `ProjectEpisteme.AlgD.Kan.pointwise_rightKanExtension` | existing |
| ALGD-C2-KAN-R02 | `ProjectEpisteme.AlgD.Kan.hasRightKanExtension_of_complete` | existing |
| ALGD-C2-KAN-08 | `ProjectEpisteme.AlgD.Kan.preimage_adjoints` | bridged |
| ALGD-C2-KAN-09 | `ProjectEpisteme.AlgD.Kan.pullback_pushforward` | existing |
| ALGD-C2-KAN-10 | `ProjectEpisteme.AlgD.Kan.pullback_obj_iso_colimit` | bridged |
| ALGD-C2-KAN-11 | `ProjectEpisteme.AlgD.Kan.leftKanExtension_not_pointwise` | new-proved |
| ALGD-C2-KAN-D05 | `ProjectEpisteme.AlgD.Kan.coconeAt_eq` | existing |
| ALGD-C2-KAN-13 | `ProjectEpisteme.AlgD.Kan.pointwiseLeftKanExtension_isPointwise` | existing |
| ALGD-C2-KAN-14 | `ProjectEpisteme.AlgD.Kan.isPointwise_isLeftKanExtension` | existing |
| ALGD-C2-KAN-D06 | `ProjectEpisteme.AlgD.Kan.commutesWith_iff_preserves` | bridged |
| ALGD-C2-KAN-15 | `ProjectEpisteme.AlgD.Kan.commutesWith_of_preservesColimit` | existing |
| ALGD-C2-KAN-D07 | `ProjectEpisteme.AlgD.Kan.IsAbsoluteLeftKanExtension` | new-proved |
| ALGD-C2-KAN-16 | `ProjectEpisteme.AlgD.Kan.isAbsoluteLeftKanExtension_iff` | new-proved |
| ALGD-C2-KAN-17 | `ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae` | new-proved |
| ALGD-C2-KAN-18 | `ProjectEpisteme.AlgD.Kan.hasTerminal_iff_hasColimit_id` | bridged |
| ALGD-C2-KAN-19 | `ProjectEpisteme.AlgD.Kan.colimit_of_terminal` | existing |
| ALGD-C2-KAN-D08 | `ProjectEpisteme.AlgD.Kan.IsAbsoluteRightKanExtension` | new-proved |
| ALGD-C2-KAN-20 | `ProjectEpisteme.AlgD.Kan.isRightAdjoint_tfae` | new-proved |
| ALGD-C2-KAN-21 | `ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae_kanLift` | new-proved |
| ALGD-C2-KAN-22 | `ProjectEpisteme.AlgD.Kan.isRightAdjoint_tfae_kanLift` | new-proved |
| ALGD-C2-KAN-23 | `ProjectEpisteme.AlgD.Kan.leftAdjoint_commutesWith` | existing |
| ALGD-C2-KAN-24 | `ProjectEpisteme.AlgD.Kan.coconeHomEquiv_natural` | new-proved |
| ALGD-C2-KAN-25 | `ProjectEpisteme.AlgD.Kan.pointwise_tfae` | new-proved |
| ALGD-C2-KAN-26 | `ProjectEpisteme.AlgD.Kan.isPointwise_iff_bijective` | new-proved |
| ALGD-C2-KAN-R03 | `ProjectEpisteme.AlgD.Kan.pointwiseRight_tfae` | new-proved |
| ALGD-C2-KAN-27 | `ProjectEpisteme.AlgD.Kan.isPointwise_of_isAbsolute` | new-proved |
| ALGD-C2-KAN-28 | `ProjectEpisteme.AlgD.Kan.restrictYoneda_isPointwise` | new-proved |
| ALGD-C2-KAN-R04 | `ProjectEpisteme.AlgD.Kan.restrictYonedaUnit_yonedaEquiv` | new-proved |
| ALGD-C2-KAN-29 | `ProjectEpisteme.AlgD.Kan.yoneda_lan_yoneda` | existing |
| ALGD-C2-KAN-R05 | `ProjectEpisteme.AlgD.Kan.yoneda_isLeftKanExtension_id` | existing |
| ALGD-C2-KAN-30 | `ProjectEpisteme.AlgD.Kan.presheaf_colimit_of_representables` | existing |
| ALGD-C2-KAN-31 | `ProjectEpisteme.AlgD.Kan.costructuredArrow_mk_isTerminal` | bridged |
| ALGD-C2-KAN-32 | `ProjectEpisteme.AlgD.Kan.isRepresentable_iff_hasTerminal` | bridged |
| ALGD-C2-KAN-33 | `ProjectEpisteme.AlgD.Kan.lan_comp_restrictYoneda` | new-proved |
| ALGD-C2-KAN-34 | `ProjectEpisteme.AlgD.Kan.lan_yoneda` | existing |
| ALGD-C2-KAN-35 | `ProjectEpisteme.AlgD.Kan.lan_yoneda_coyoneda` | new-proved |
| ALGD-C2-KAN-36 | `ProjectEpisteme.AlgD.Kan.unit_isIso_of_fullyFaithful` | existing |
| ALGD-C2-KAN-38 | `ProjectEpisteme.AlgD.Kan.fullyFaithful_of_isIso_unit` | new-proved |
| ALGD-C2-KAN-39 | `ProjectEpisteme.AlgD.Kan.restrictYonedaUnit_app_app` | new-proved |
| ALGD-C2-KAN-40 | `ProjectEpisteme.AlgD.Kan.fullyFaithful_iff_isIso_unit` | new-proved |
| ALGD-C2-KAN-41 | `ProjectEpisteme.AlgD.Kan.lan_fullyFaithful_tfae` | bridged |
| ALGD-C2-KAN-D09 | `ProjectEpisteme.AlgD.Kan.IsStronglyGenerating` | new-proved |
| ALGD-C2-KAN-D10 | `ProjectEpisteme.AlgD.Kan.isDense_iff` | existing |
| ALGD-C2-KAN-42 | `ProjectEpisteme.AlgD.Kan.yoneda_isDense` | existing |
| ALGD-C2-KAN-43 | `ProjectEpisteme.AlgD.Kan.isDense_tfae` | new-proved |
| ALGD-C2-KAN-44 | `ProjectEpisteme.AlgD.Kan.isStronglyGenerating_of_isDense` | new-proved |
| ALGD-C2-KAN-45 | `ProjectEpisteme.AlgD.Kan.universal_adjunction` | new-proved |
| ALGD-C2-KAN-46 | `ProjectEpisteme.AlgD.Kan.adjunction_eq_universal` | new-proved |
| ALGD-C2-KAN-47 | `ProjectEpisteme.AlgD.Kan.types_adjunction` | new-proved |
| ALGD-C2-KAN-48 | `ProjectEpisteme.AlgD.Kan.types_op_adjunction` | new-proved |
| ALGD-C2-KAN-49 | `ProjectEpisteme.AlgD.Kan.limit_iso_hom_const` | existing |
| ALGD-C2-KAN-50 | `ProjectEpisteme.AlgD.Kan.presheaf_functors_as_kanExtensions` | new-proved |
| ALGD-C2-KAN-D12 | `ProjectEpisteme.AlgD.Kan.IsSmallProjective` | new-proved |
| ALGD-C2-KAN-51 | `ProjectEpisteme.AlgD.Kan.presheafCategory_iff` | new-proved |
| ALGD-C2-KAN-54 | `ProjectEpisteme.AlgD.Kan.over_presheaf_equivalence` | existing |
<!-- END GENERATED: verified -->

Every project declaration depends only on `[propext, Classical.choice, Quot.sound]`. Two mechanisms check this: `checks/AxiomAudit.lean` covers the whole library, and the `#guard_msgs` blocks in each source module cover the individual source items. `checks/LedgerDeclarations.lean` checks that each declaration named above exists.

## Known gaps flagged during cataloging

These rows are expected to become `new-proved` or `blocked` rather than `existing`. Details are in each ledger's Notes.

- **Isomorphisms of categories.** mathlib has the notion (`IsoCat` and `Functor.IsIso` in Mathlib/CategoryTheory/IsoCat.lean), contrary to the first catalog pass. NAT and COMMA show the pattern: prove that the comparison functor is full, faithful and bijective on objects, using the library module `ProjectEpisteme/Category/Basic/FunctorCategory.lean`. LIMIT-05, -07 and -08 follow the same pattern. The same is still needed for CONSTR-01 and -04–06, and INTRO-19 and -28.
- **Not in mathlib**
  - General subcategories. Used by CONSTR-D06 and -08, -10, -11.
  - Skeletons as full subcategories and their uniqueness (EQUIV-D07, -19, -20).
  - Kan lifts and absolute Kan extensions for functors (KAN-D04, -D07, -D08). They are verified as new work; mathlib has them only for bicategories.
  - The characterization of presheaf categories by small projective, strongly generating subcategories (KAN-51), and the hom-set form of pointwise Kan extensions (KAN-24, -25). Both are verified as new work.
  - Kan extensions along a composite (AFT-04), the left-adjoint form of the general adjoint functor theorem (AFT-10) and well-copowered categories through quotient objects (AFT-D06). They are verified as new work or bridges.
- **Topology and algebra prerequisites**
  - π₁ as a functor on pointed spaces (INTRO-10, CONSTR-07).
  - Seifert–van Kampen for groupoids (FUNDGPD-10, -11).
  - The p-adic integers as a limit in Set (UNIV-14; LIMIT-11 is verified).
  - Gelfand–Naimark as an equivalence (EQUIV-03).
  - Algebraic examples in ADJOINT: 例 52, 53 and 55 are `blocked`, since mathlib has no Henselization, free lattices or Ban_1.
- **Source issues**
  - Typos in adjoint.pdf, limit.pdf and nat.pdf (例 4).
  - A missing boundedness hypothesis in UNIV-13 and LIMIT-10.
  - A missing nonemptiness hypothesis in SHEAF 例 6.
  - A missing injectivity hypothesis in ADJOINT 例 51.
  - A missing commutativity hypothesis in ADJOINT 例 50.
  - A possibly missing hypothesis in AFT 補題 5 (H should commute with F†E), to be checked when the row is verified.
