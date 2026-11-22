/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint

/-!
# Calculus of rectangular parametrices modulo compact operators

A compact parametrix of `T : E →L[𝕜] F` is a continuous linear map in the reverse direction whose
two inverse errors are compact. Parametrices compose in reverse order, pass to binary Cartesian
products and Hilbert adjoints, and survive compact perturbations of either map. Any two parametrices
differ by a compact operator; in fact, when nonempty, the parametrices of a fixed map form
exactly one coset of the compact operators.

These algebraic laws hold for topological modules over a ring, without completeness or Hilbert
structure (except for adjoints). Import `TauCeti.Analysis.Fredholm.CompactPerturbation` to use
them alongside the Fredholm and index API: for real or complex Banach spaces, Atkinson's theorem
`TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one` identifies existence of such a
parametrix with Fredholmness. The existing
`ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one` supplies the inverse-index
sign, using the native Fredholm composition law.

## References

* F. V. Atkinson, *The normal solubility of linear equations in normed spaces*, Mat. Sbornik
  N.S. 28 (70) (1951), 3–14.
* J. B. Conway, *A Course in Functional Analysis*, Chapter XI.
-/

public section

open scoped InnerProduct

namespace ContinuousLinearMap

section Topological

variable {𝕜 E F G E' F' : Type*} [Ring 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [Module 𝕜 G]
variable [AddCommGroup E'] [TopologicalSpace E'] [IsTopologicalAddGroup E'] [Module 𝕜 E']
variable [AddCommGroup F'] [TopologicalSpace F'] [IsTopologicalAddGroup F'] [Module 𝕜 F']

/-- `S` is a two-sided inverse of `T` modulo compact operators. The errors act on the source
and target separately, so the definition applies to maps between different spaces. -/
structure IsCompactParametrix (S : F →L[𝕜] E) (T : E →L[𝕜] F) : Prop where
  /-- The error of the left inverse is compact on the source. -/
  left : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E)
  /-- The error of the right inverse is compact on the target. -/
  right : IsCompactOperator (T.comp S - 1 : F →L[𝕜] F)

/-- The two corner error identities characterizing a compact parametrix. -/
theorem isCompactParametrix_iff (S : F →L[𝕜] E) (T : E →L[𝕜] F) :
    S.IsCompactParametrix T ↔
      IsCompactOperator (S.comp T - 1 : E →L[𝕜] E) ∧
        IsCompactOperator (T.comp S - 1 : F →L[𝕜] F) :=
  ⟨fun h ↦ ⟨h.left, h.right⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The identity is its own compact parametrix. -/
@[simp]
theorem isCompactParametrix_id :
    (ContinuousLinearMap.id 𝕜 E).IsCompactParametrix (ContinuousLinearMap.id 𝕜 E) := by
  have h : IsCompactOperator (0 : E → E) := isCompactOperator_zero
  constructor <;> simpa only [one_def, id_comp, sub_self, FunLike.coe_zero] using h

/-- The unit endomorphism is its own compact parametrix. -/
@[simp]
theorem isCompactParametrix_one : (1 : E →L[𝕜] E).IsCompactParametrix 1 := by
  simpa only [one_def] using (isCompactParametrix_id (𝕜 := 𝕜) (E := E))

/-- The inverse of a continuous linear equivalence is a compact parametrix. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.isCompactParametrix (e : E ≃L[𝕜] F) :
    e.symm.toContinuousLinearMap.IsCompactParametrix e.toContinuousLinearMap := by
  constructor
  · simpa only [ContinuousLinearEquiv.coe_symm_comp_coe, one_def, sub_self, FunLike.coe_zero]
      using (isCompactOperator_zero : IsCompactOperator (0 : E → E))
  · simpa only [ContinuousLinearEquiv.coe_comp_coe_symm, one_def, sub_self, FunLike.coe_zero]
      using (isCompactOperator_zero : IsCompactOperator (0 : F → F))

/-- Any reverse map is a compact parametrix when both spaces are locally compact. -/
theorem isCompactParametrix_of_locallyCompactSpace [LocallyCompactSpace E] [LocallyCompactSpace F]
    (S : F →L[𝕜] E) (T : E →L[𝕜] F) : S.IsCompactParametrix T :=
  ⟨isCompactOperator_of_locallyCompactSpace_dom _, isCompactOperator_of_locallyCompactSpace_dom _⟩

/-- The compact-parametrix relation is symmetric. -/
@[symm]
theorem IsCompactParametrix.symm {S : F →L[𝕜] E} {T : E →L[𝕜] F}
    (h : S.IsCompactParametrix T) : T.IsCompactParametrix S := ⟨h.right, h.left⟩

/-- Either map can be regarded as the parametrix of the other. -/
theorem isCompactParametrix_comm (S : F →L[𝕜] E) (T : E →L[𝕜] F) :
    S.IsCompactParametrix T ↔ T.IsCompactParametrix S :=
  ⟨IsCompactParametrix.symm, IsCompactParametrix.symm⟩

/-- Parametrices of a composite are obtained by composing parametrices in reverse order. -/
theorem IsCompactParametrix.comp {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    {U : F →L[𝕜] G} {R : G →L[𝕜] F}
    (hS : S.IsCompactParametrix T) (hR : R.IsCompactParametrix U) :
    (S.comp R).IsCompactParametrix (U.comp T) := by
  constructor
  · have heq : (S.comp R).comp (U.comp T) - 1 =
        S.comp ((R.comp U - 1).comp T) + (S.comp T - 1) := by
      simp only [comp_sub, sub_comp, comp_assoc, one_def, id_comp]
      abel
    rw [heq]
    exact ((hR.left.comp_clm T).clm_comp S).add hS.left
  · have heq : (U.comp T).comp (S.comp R) - 1 =
        U.comp ((T.comp S - 1).comp R) + (U.comp R - 1) := by
      simp only [comp_sub, sub_comp, comp_assoc, one_def, id_comp]
      abel
    rw [heq]
    exact ((hS.right.comp_clm R).clm_comp U).add hR.right

/-- Adding a compact operator to the original map retains the same parametrix. -/
theorem IsCompactParametrix.add_right_of_isCompactOperator {T K : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : S.IsCompactParametrix T) (hK : IsCompactOperator K) :
    S.IsCompactParametrix (T + K) := by
  constructor
  · have heq : S.comp (T + K) - 1 = (S.comp T - 1) + S.comp K := by
      rw [comp_add]
      abel
    rw [heq]
    exact h.1.add (hK.clm_comp S)
  · have heq : (T + K).comp S - 1 = (T.comp S - 1) + K.comp S := by
      rw [add_comp]
      abel
    rw [heq]
    exact h.2.add (hK.comp_clm S)

/-- Adding a compact operator to a parametrix gives another parametrix of the same map. -/
theorem IsCompactParametrix.add_left_of_isCompactOperator {T : E →L[𝕜] F} {S L : F →L[𝕜] E}
    (h : S.IsCompactParametrix T) (hL : IsCompactOperator L) :
    (S + L).IsCompactParametrix T :=
  (h.symm.add_right_of_isCompactOperator hL).symm

/-- Independent compact perturbations of an operator and its parametrix preserve the relation. -/
theorem IsCompactParametrix.add_of_isCompactOperator {T K : E →L[𝕜] F} {S L : F →L[𝕜] E}
    (h : S.IsCompactParametrix T) (hL : IsCompactOperator L) (hK : IsCompactOperator K) :
    (S + L).IsCompactParametrix (T + K) :=
  (h.add_left_of_isCompactOperator hL).add_right_of_isCompactOperator hK

/-- Subtracting a compact operator from a parametrix preserves the parametrix property. -/
theorem IsCompactParametrix.sub_left_of_isCompactOperator {T : E →L[𝕜] F} {S L : F →L[𝕜] E}
    (h : S.IsCompactParametrix T) (hL : IsCompactOperator L) :
    (S - L).IsCompactParametrix T := by
  simpa only [sub_eq_add_neg] using h.add_left_of_isCompactOperator hL.neg

/-- Subtracting a compact operator from the original map retains the same parametrix. -/
theorem IsCompactParametrix.sub_right_of_isCompactOperator {T K : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : S.IsCompactParametrix T) (hK : IsCompactOperator K) :
    S.IsCompactParametrix (T - K) := by
  simpa only [sub_eq_add_neg] using h.add_right_of_isCompactOperator hK.neg

/-- A compact perturbation of the first argument does not change the parametrix relation. -/
theorem isCompactParametrix_add_left_iff {T : E →L[𝕜] F} {S L : F →L[𝕜] E}
    (hL : IsCompactOperator L) : (S + L).IsCompactParametrix T ↔ S.IsCompactParametrix T :=
  ⟨fun h ↦ by simpa only [add_sub_cancel_right] using h.sub_left_of_isCompactOperator hL,
    fun h ↦ h.add_left_of_isCompactOperator hL⟩

/-- A compact perturbation of the second argument does not change the parametrix relation. -/
theorem isCompactParametrix_add_right_iff {T K : E →L[𝕜] F} {S : F →L[𝕜] E}
    (hK : IsCompactOperator K) : S.IsCompactParametrix (T + K) ↔ S.IsCompactParametrix T :=
  ⟨fun h ↦ by simpa only [add_sub_cancel_right] using h.sub_right_of_isCompactOperator hK,
    fun h ↦ h.add_right_of_isCompactOperator hK⟩

/-- Subtracting a compact operator from the first argument does not change the relation. -/
theorem isCompactParametrix_sub_left_iff {T : E →L[𝕜] F} {S L : F →L[𝕜] E}
    (hL : IsCompactOperator L) : (S - L).IsCompactParametrix T ↔ S.IsCompactParametrix T := by
  simpa only [sub_eq_add_neg] using isCompactParametrix_add_left_iff hL.neg

/-- Subtracting a compact operator from the second argument does not change the relation. -/
theorem isCompactParametrix_sub_right_iff {T K : E →L[𝕜] F} {S : F →L[𝕜] E}
    (hK : IsCompactOperator K) : S.IsCompactParametrix (T - K) ↔ S.IsCompactParametrix T := by
  simpa only [sub_eq_add_neg] using isCompactParametrix_add_right_iff hK.neg

/-- A left inverse modulo compact operators and a right inverse modulo compact operators
of the same map differ by a compact operator. No other corner error is needed. -/
theorem isCompactOperator_sub_of_isCompactOperator_comp_sub_one
    {T : E →L[𝕜] F} {S R : F →L[𝕜] E}
    (hST : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E))
    (hTR : IsCompactOperator (T.comp R - 1 : F →L[𝕜] F)) : IsCompactOperator (S - R) := by
  have heq : S - R = (S.comp T - 1).comp R - S.comp (T.comp R - 1) := by
    simp only [sub_comp, comp_sub, comp_assoc, one_def, id_comp, comp_id]
    abel
  rw [heq]
  exact (hST.comp_clm R).sub (hTR.clm_comp S)

/-- Once one parametrix is fixed, all the others are exactly its compact perturbations. -/
theorem IsCompactParametrix.isCompactParametrix_iff_isCompactOperator_sub
    {T : E →L[𝕜] F} {S : F →L[𝕜] E} (h : S.IsCompactParametrix T) (R : F →L[𝕜] E) :
    R.IsCompactParametrix T ↔ IsCompactOperator (R - S) := by
  constructor
  · intro hR
    exact isCompactOperator_sub_of_isCompactOperator_comp_sub_one hR.left h.right
  · intro hRS
    simpa only [add_sub_cancel] using h.add_left_of_isCompactOperator hRS

/-- A fixed parametrix works for exactly the compact perturbations of the original map. -/
theorem IsCompactParametrix.isCompactParametrix_right_iff_isCompactOperator_sub
    {T : E →L[𝕜] F} {S : F →L[𝕜] E} (h : S.IsCompactParametrix T) (T' : E →L[𝕜] F) :
    S.IsCompactParametrix T' ↔ IsCompactOperator (T' - T) :=
  (isCompactParametrix_comm S T').trans (h.symm.isCompactParametrix_iff_isCompactOperator_sub T')

/-- A binary block product is a compact parametrix exactly when each factor is. -/
@[simp]
theorem isCompactParametrix_prodMap_iff {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    {U : E' →L[𝕜] F'} {R : F' →L[𝕜] E'} :
    (S.prodMap R).IsCompactParametrix (T.prodMap U) ↔
      S.IsCompactParametrix T ∧ R.IsCompactParametrix U := by
  have hl : (S.prodMap R).comp (T.prodMap U) - 1 = (S.comp T - 1).prodMap (R.comp U - 1) := by
    ext x <;> simp
  have hr : (T.prodMap U).comp (S.prodMap R) - 1 = (T.comp S - 1).prodMap (U.comp R - 1) := by
    ext x <;> simp
  simp only [isCompactParametrix_iff, hl, hr, coe_prodMap', isCompactOperator_prodMap_iff]
  exact and_and_and_comm

/-- The binary Cartesian product of two parametrices is a parametrix of the product map. -/
theorem IsCompactParametrix.prodMap {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    {U : E' →L[𝕜] F'} {R : F' →L[𝕜] E'}
    (hS : S.IsCompactParametrix T) (hR : R.IsCompactParametrix U) :
    (S.prodMap R).IsCompactParametrix (T.prodMap U) :=
  isCompactParametrix_prodMap_iff.mpr ⟨hS, hR⟩

end Topological

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Hilbert adjoints preserve compact parametrices, with the source and target corners swapped. -/
theorem IsCompactParametrix.adjoint {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : S.IsCompactParametrix T) : (S†).IsCompactParametrix (T†) := by
  constructor
  · simpa only [map_sub, adjoint_comp, adjoint_one] using h.2.adjoint
  · simpa only [map_sub, adjoint_comp, adjoint_one] using h.1.adjoint

/-- A pair of Hilbert adjoints is a compact-parametrix pair exactly when the original pair is. -/
@[simp]
theorem isCompactParametrix_adjoint_iff (S : F →L[𝕜] E) (T : E →L[𝕜] F) :
    (S†).IsCompactParametrix (T†) ↔ S.IsCompactParametrix T := by
  constructor
  · intro h
    simpa only [adjoint_adjoint] using h.adjoint
  · exact IsCompactParametrix.adjoint

end Hilbert

end ContinuousLinearMap
