/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Minimal sub-realizations and central complements

Every finite-dimensional matrix realization contains a minimal sub-realization with a
complement annihilated by all simple roots. Thus enlarging a minimal realization adds only
central directions. We construct restrictions to subspaces containing the coroots on which
root evaluation remains surjective, and characterize minimality by containment of the full
Cartan center in the coroot span.

The source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1,
Proposition 1.1, and Proposition 1.6. No finite-type or nonsingularity assumption is used.
-/

public section

open Module

namespace TauCeti.CartanRealization

variable {I K H : Type*} [Fintype I] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I K} (R : CartanRealization A H)

variable [FiniteDimensional K H]

/-- A realization is minimal exactly when its entire center lies in its coroot span. -/
theorem isMinimal_iff_cartanCenter_le_corootSpan :
    R.IsMinimal ↔ R.cartanCenter ≤ R.corootSpan := by
  rw [R.isMinimal_iff]
  have hc := R.finrank_cartanCenter_add_card
  have hi := R.finrank_cartanCenter_inf_corootSpan_add_rank
  constructor
  · intro h
    have heq : R.cartanCenter ⊓ R.corootSpan = R.cartanCenter :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact inf_eq_left.mp heq
  · intro h
    rw [inf_eq_left.mpr h] at hi
    omega

/-- Restrict a realization to a subspace containing its coroots and supplementing its center.
The supplement condition ensures that the restricted simple roots remain independent. -/
noncomputable def restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hm : M ⊔ R.cartanCenter = ⊤) : CartanRealization A M where
  coroot i := ⟨R.coroot i, hc (R.coroot_mem_corootSpan i)⟩
  root i := (R.root i).domRestrict M
  coroot_linearIndependent := R.coroot_linearIndependent.of_comp M.subtype
  root_linearIndependent := by
    classical
    have hsurj : Function.Surjective (R.rootEvaluation.domRestrict M) :=
      (LinearMap.surjective_domRestrict_iff R.rootEvaluation_surjective).mpr
        (codisjoint_iff.mpr (by rwa [← R.cartanCenter_def]))
    have h := (Pi.basisFun K I).dualBasis.linearIndependent.map'
      (R.rootEvaluation.domRestrict M).dualMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective hsurj))
    convert h using 1
    ext i x
    simp
  root_coroot i j := R.root_coroot i j

@[simp]
theorem restrict_coroot_coe (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hm : M ⊔ R.cartanCenter = ⊤) (i : I) :
    ((R.restrict M hc hm).coroot i : H) = R.coroot i := (rfl)

@[simp]
theorem restrict_root_apply (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hm : M ⊔ R.cartanCenter = ⊤) (i : I) (x : M) :
    (R.restrict M hc hm).root i x = R.root i x := (rfl)

/-- The center of a restricted realization is the intersection with the original center,
viewed inside the restricting subspace. -/
@[simp]
theorem cartanCenter_restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hm : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hm).cartanCenter = R.cartanCenter.comap M.subtype := by
  ext x
  simp

/-- The coroot span of a restricted realization is the original coroot span, viewed inside
the restricting subspace. -/
@[simp]
theorem corootSpan_restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hm : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hm).corootSpan = R.corootSpan.comap M.subtype := by
  apply (Submodule.map_injective_of_injective M.subtype_injective)
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hc]
  simp only [corootSpan_def, Submodule.map_span, ← Set.range_comp]
  congr 1

/-- A restriction is minimal exactly when the center it retains is in the coroot span. -/
theorem isMinimal_restrict_iff (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hm : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hm).IsMinimal ↔ M ⊓ R.cartanCenter ≤ R.corootSpan := by
  rw [isMinimal_iff_cartanCenter_le_corootSpan, cartanCenter_restrict, corootSpan_restrict]
  constructor
  · intro h x hx
    exact h (x := ⟨x, hx.1⟩) hx.2
  · intro h x hx
    exact h ⟨x.2, hx⟩

/-- Every finite-dimensional realization is a minimal sub-realization plus central directions.
The minimal subspace contains every simple coroot, and its complementary subspace is killed
by every simple root. No uniqueness of either summand is asserted. -/
theorem exists_minimal_restrict_isCompl :
    ∃ (M Z : Submodule K H) (hc : R.corootSpan ≤ M)
      (hm : M ⊔ R.cartanCenter = ⊤),
      (R.restrict M hc hm).IsMinimal ∧ IsCompl M Z ∧ Z ≤ R.cartanCenter := by
  obtain ⟨Z, hd, hz⟩ := IsModularLattice.exists_disjoint_and_sup_eq
    (inf_le_left : R.cartanCenter ⊓ R.corootSpan ≤ R.cartanCenter)
  have hZ : Z ≤ R.cartanCenter := hz ▸ le_sup_right
  have hUZ : Disjoint R.corootSpan Z := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    calc
      R.corootSpan ⊓ Z ≤ (R.cartanCenter ⊓ R.corootSpan) ⊓ Z :=
        le_inf (le_inf (inf_le_right.trans hZ) inf_le_left) inf_le_right
      _ = ⊥ := hd.eq_bot
  obtain ⟨M, hc, hM⟩ := hUZ.exists_isCompl
  have hm : M ⊔ R.cartanCenter = ⊤ :=
    top_unique (hM.sup_eq_top ▸ sup_le_sup_left hZ M)
  refine ⟨M, Z, hc, hm, (R.isMinimal_restrict_iff M hc hm).mpr ?_, hM, hZ⟩
  rw [← hz, sup_comm, ← inf_sup_assoc_of_le _ (inf_le_right.trans hc),
    hM.inf_eq_bot, bot_sup_eq]
  exact inf_le_right

end TauCeti.CartanRealization
