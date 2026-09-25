/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNormal
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# Corestriction at index two, and the conjugation `res ∘ cor - id`

Let `U` be an open subgroup of index two in a topological group `G` and let `M` be a topological
`G`-module. On explicit `H¹(U, M)`, the composite `res_U ∘ cor_U` of degree-one corestriction and
restriction is `1 + s` for any element `s` of the nontrivial coset: computed on the transversal
`{1, s}`, the corestriction sum has two terms, the first restricts to the identity and the second to
conjugation by `s`. The difference `res ∘ cor - id` is therefore the conjugation action of the
nontrivial coset on explicit `H¹(U, M)`, defined without choosing an element of that coset.

This is the conjugation `evensConj` of the index-two Evens norm, hence the name `evensConj1`; it
is stated for an arbitrary topological coefficient module and uses only the corestriction and
conjugation APIs. It supplies the conjugate class in the graph-cocycle restriction computation of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Restriction`. The theorem
`evensConj1_eq_explicitConj1` identifies it with conjugation by **every** element outside `U`,
providing the comparison needed for computations using a chosen coset representative.

The computation is carried out on cochains for an arbitrary coefficient module, with no topology:
`cochainsCor1_indexTwoTransversal_apply_coe` is the two-term formula for the corestriction cochain
on the elements of `U`. The simp rule `sum_indexTwoTransversal_smul_lWord` evaluates the sum
produced by `cochainsCor1_apply`; it only needs an additive commutative monoid of coefficients,
and the named corestriction formula is also available for rewriting.

## Main definitions

* `TauCeti.ContCohomology.evensConj1`: the map `res ∘ cor - id` on explicit `H¹(U, M)` for an open
  subgroup `U` of index two.

## Main results

* `TauCeti.ContCohomology.cochainsCor1_indexTwoTransversal_apply_coe`: on `γ ∈ U`, the
  corestriction cochain over the transversal `{1, s}` is `f γ + s • f (s⁻¹ γ s)`.
* `TauCeti.ContCohomology.evensConj1_eq_explicitConj1`: `evensConj1` is conjugation by every element
  outside `U`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section Cochain

variable {G : Type u} [Group G] {M : Type v} {U : Subgroup G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The corestriction sum on the transversal `{1, s}`, evaluated on an element of `U`, has the
two terms `f γ` and `s • f (s⁻¹ γ s)`. -/
@[simp]
theorem sum_indexTwoTransversal_smul_lWord [AddCommMonoid M] [DistribMulAction G M]
    (hU : U.index = 2) {s : G} (hs : s ∉ U) (f : U → M) (γ : G) (hγ : γ ∈ U) :
    letI : U.FiniteIndex := ⟨by omega⟩
    ∑ u, U.indexTwoTransversal s u •
      f ⟨lWord U (U.indexTwoTransversal s) u γ,
        lWord_mem U _ (Subgroup.indexTwoTransversal_mk hU hs) _ _⟩ =
      f ⟨γ, hγ⟩ + s • f ⟨s⁻¹ * γ * s, (Subgroup.normal_of_index_eq_two hU).conj_mem' γ hγ s⟩ := by
  have : U.FiniteIndex := ⟨by omega⟩
  have h1 : (⟨lWord U (U.indexTwoTransversal s) (QuotientGroup.mk 1) γ,
      lWord_mem U _ (Subgroup.indexTwoTransversal_mk hU hs) _ _⟩ : U) = ⟨γ, hγ⟩ :=
    Subtype.ext (lWord_indexTwoTransversal_mk_one_of_mem s hγ)
  have h2 : (⟨lWord U (U.indexTwoTransversal s) (QuotientGroup.mk s) γ,
      lWord_mem U _ (Subgroup.indexTwoTransversal_mk hU hs) _ _⟩ : U) =
      ⟨s⁻¹ * γ * s, (Subgroup.normal_of_index_eq_two hU).conj_mem' γ hγ s⟩ :=
    Subtype.ext (lWord_indexTwoTransversal_mk_of_mem hU hs hγ)
  rw [sum_quotient_eq_add_of_index_two hU hs, h1, h2,
    Subgroup.indexTwoTransversal_mk_one, one_smul,
    Subgroup.indexTwoTransversal_of_ne s (mk_ne_mk_one_of_notMem hs)]

/-- **The corestriction cochain over the transversal `{1, s}`, on the subgroup.** For `U` of index
two, `s ∉ U` and `γ ∈ U`, the two terms of the corestriction sum of `f : U → M` are `f γ` at the
trivial coset and `s • f (s⁻¹ γ s)` at the coset of `s`. -/
theorem cochainsCor1_indexTwoTransversal_apply_coe [AddCommGroup M] [DistribMulAction G M]
    (hU : U.index = 2) {s : G} (hs : s ∉ U) (f : U → M) (γ : U) :
    letI : U.FiniteIndex := ⟨by omega⟩
    cochainsCor1 G M U (U.indexTwoTransversal s) (Subgroup.indexTwoTransversal_mk hU hs) f γ =
      f γ + s • f ⟨s⁻¹ * γ * s, (Subgroup.normal_of_index_eq_two hU).conj_mem' γ γ.2 s⟩ := by
  have : U.FiniteIndex := ⟨by omega⟩
  simp [hU, hs]

end Cochain

section Cohomology

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (U : Subgroup G)

/-- **The conjugation on `H¹(U, M)` of an open subgroup of index two, defined choice-free** as
`res ∘ cor - id`, with `cor` the degree-one corestriction `TauCeti.ContCohomology.explicitCor1`.

At index two `res ∘ cor` is `1 + s` for every element `s` outside `U`, so this difference is
conjugation by `s` for every `s ∉ U` (`evensConj1_eq_explicitConj1`) and depends on `U` alone. It
is the conjugate `α ↦ s · α` appearing in the identities of the index-two Evens norm. -/
noncomputable def evensConj1 (hU : U.index = 2) (hUo : IsOpen (U : Set G)) : H1 U M →+ H1 U M :=
  haveI : U.FiniteIndex := ⟨by omega⟩
  (explicitRes1 G M U).comp (explicitCor1 G M U hUo) - AddMonoidHom.id (H1 U M)

/-- The defining formula of `evensConj1`: restriction of the corestriction, minus the identity. -/
@[simp]
theorem evensConj1_apply (hU : U.index = 2) (hUo : IsOpen (U : Set G)) (x : H1 U M) :
    letI : U.FiniteIndex := ⟨by omega⟩
    evensConj1 G M U hU hUo x = explicitRes1 G M U (explicitCor1 G M U hUo x) - x :=
  (rfl)

/-- **The choice-free conjugation is conjugation by every element outside `U`.** For `s ∉ U`,
`evensConj1` is the conjugation map `TauCeti.ContCohomology.explicitConj1 U s` of the normal
subgroup `U`. -/
theorem evensConj1_eq_explicitConj1 (hU : U.index = 2) (hUo : IsOpen (U : Set G)) {s : G}
    (hs : s ∉ U) :
    letI := Subgroup.normal_of_index_eq_two hU
    evensConj1 G M U hU hUo = explicitConj1 (M := M) U s := by
  have := Subgroup.normal_of_index_eq_two hU
  have : U.FiniteIndex := ⟨by omega⟩
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    -- Compute the corestriction on the transversal `{1, s}`, where it has two terms.
    rw [evensConj1_apply, explicitCor1_eq_transversal G M U (U.indexTwoTransversal s)
      (Subgroup.indexTwoTransversal_mk hU hs) hUo]
    simp only [explicitCor1Transversal_mk, explicitRes1_mk, explicitConj1_apply_eq_smul, smul_mk]
    rw [sub_eq_iff_eq_add, ← QuotientAddGroup.mk_add]
    apply congrArg (fun z : Z1 U M => (z : H1 U M))
    apply Subtype.ext
    funext γ
    simp only [cocyclesMap1_coe, cochainsMap1_apply, ContinuousMonoidHom.coe_subgroupSubtype,
      Subgroup.subtype_apply, AddMonoidHom.id_apply, coe_cocyclesCor1,
      cochainsCor1_indexTwoTransversal_apply_coe hU hs, AddSubgroup.coe_add, Pi.add_apply,
      DistribSMul.toAddMonoidHom_apply, MonoidHom.coe_coe,
      Subgroup.inverseConjugationHom_apply]
    exact add_comm _ _

end Cohomology

end TauCeti.ContCohomology
