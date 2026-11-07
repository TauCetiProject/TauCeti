/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic

/-!
# Central splittings of Cartan realizations

Every finite-dimensional realization contains a minimal sub-realization, with a complementary
subspace annihilated by all simple roots. Thus an arbitrary realization differs from a minimal
one only by central directions. We also characterize minimality by containment of the Cartan
center in the coroot span, and compute the dimension of the extra central directions.

Restriction to a subspace is a realization when it contains the coroots and, together with the
Cartan center, spans the ambient space. This criterion ensures that the restricted roots remain
independent even for singular matrices.

The mathematical source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition,
§1.1, Proposition 1.1 and Proposition 1.6.
-/

public section

open Module

namespace TauCeti.CartanRealization

variable {I K H : Type*} [Fintype I] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I K} (R : CartanRealization A H)

variable [FiniteDimensional K H]

omit [FiniteDimensional K H] in
/-- The central part of the coroot span has dimension equal to the nullity of the matrix. -/
theorem finrank_cartanCenter_inf_corootSpan_add_rank :
    finrank K ↥(R.cartanCenter ⊓ R.corootSpan) + A.rank = Fintype.card I := by
  rw [R.cartanCenter_inf_corootSpan,
    ← (Submodule.equivMapOfInjective R.corootMap R.corootMap_injective
      (LinearMap.ker A.transpose.mulVecLin)).finrank_eq]
  have h := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  -- Matrix rank is the dimension of the range of its coordinate linear map.
  have hr : finrank K (LinearMap.range A.transpose.mulVecLin) = A.transpose.rank := (rfl)
  rw [hr, Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- A realization is minimal exactly when its full center lies in the coroot span. -/
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

/-- A sub-realization is minimal exactly when its central vectors already lie in the
original coroot span. -/
theorem isMinimal_restrict_iff (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hs).IsMinimal ↔ R.cartanCenter ⊓ M ≤ R.corootSpan := by
  rw [isMinimal_iff_cartanCenter_le_corootSpan,
    ← Submodule.map_le_map_iff_of_injective M.injective_subtype,
    map_corootSpan_restrict, cartanCenter_restrict, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_comm]

/-- Every finite-dimensional realization is a minimal sub-realization plus a central
summand. The roots of the sub-realization are restrictions, and its coroots are the original
coroots, rather than merely abstractly isomorphic families. -/
theorem exists_isMinimal_restrict_isCompl :
    ∃ (M Z : Submodule K H) (hc : R.corootSpan ≤ M)
      (hs : M ⊔ R.cartanCenter = ⊤),
      (R.restrict M hc hs).IsMinimal ∧ IsCompl M Z ∧ Z ≤ R.cartanCenter := by
  obtain ⟨Z, hd, hZ⟩ := IsModularLattice.exists_disjoint_and_sup_eq
    (inf_le_left : R.cartanCenter ⊓ R.corootSpan ≤ R.cartanCenter)
  have hz : Z ≤ R.cartanCenter := hZ ▸ le_sup_right
  have hd' : Disjoint R.corootSpan Z := by
    rw [disjoint_iff] at hd ⊢
    calc
      R.corootSpan ⊓ Z = (R.cartanCenter ⊓ R.corootSpan) ⊓ Z := by
        rw [inf_comm R.cartanCenter, inf_assoc, inf_eq_right.mpr hz]
      _ = ⊥ := hd
  obtain ⟨M, hc, hM⟩ := hd'.exists_isCompl
  have hs : M ⊔ R.cartanCenter = ⊤ :=
    top_unique (hM.sup_eq_top ▸ sup_le_sup_left hz M)
  refine ⟨M, Z, hc, hs, (R.isMinimal_restrict_iff M hc hs).mpr ?_, hM, hz⟩
  rw [← hZ, sup_inf_assoc_of_le _ (inf_le_right.trans hc), hM.symm.inf_eq_bot,
    sup_bot_eq]
  exact inf_le_right

/-- In any splitting with a minimal sub-realization as first summand, the dimension of the
complement is exactly the excess dimension of the original realization. -/
theorem finrank_complement_of_isMinimal_restrict {M Z : Submodule K H} (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hm : (R.restrict M hc hs).IsMinimal)
    (h : IsCompl M Z) :
    finrank K Z + (2 * Fintype.card I - A.rank) = finrank K H := by
  have hdim := (isMinimal_iff _).mp hm
  have := Submodule.finrank_add_eq_of_isCompl h
  omega

end TauCeti.CartanRealization
