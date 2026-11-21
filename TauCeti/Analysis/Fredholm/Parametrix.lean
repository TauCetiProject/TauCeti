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

A compact parametrix of `T : E →L[𝕜] F` is a bounded map in the reverse direction whose two
inverse errors are compact. Parametrices compose in reverse order, pass to finite block sums
and Hilbert adjoints, and survive compact perturbations of either map. Any two parametrices
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
structure IsCompactParametrix (T : E →L[𝕜] F) (S : F →L[𝕜] E) : Prop where
  /-- The error of the left inverse is compact on the source. -/
  left : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E)
  /-- The error of the right inverse is compact on the target. -/
  right : IsCompactOperator (T.comp S - 1 : F →L[𝕜] F)

/-- The two corner error identities characterizing a compact parametrix. -/
theorem isCompactParametrix_iff (T : E →L[𝕜] F) (S : F →L[𝕜] E) :
    T.IsCompactParametrix S ↔
      IsCompactOperator (S.comp T - 1 : E →L[𝕜] E) ∧
        IsCompactOperator (T.comp S - 1 : F →L[𝕜] F) :=
  ⟨fun h ↦ ⟨h.left, h.right⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The compact-parametrix relation is symmetric. -/
theorem IsCompactParametrix.symm {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : T.IsCompactParametrix S) : S.IsCompactParametrix T := ⟨h.right, h.left⟩

/-- Either map can be regarded as the parametrix of the other. -/
theorem isCompactParametrix_comm (T : E →L[𝕜] F) (S : F →L[𝕜] E) :
    T.IsCompactParametrix S ↔ S.IsCompactParametrix T :=
  ⟨IsCompactParametrix.symm, IsCompactParametrix.symm⟩

/-- Parametrices of a composite are obtained by composing parametrices in reverse order. -/
theorem IsCompactParametrix.comp {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    {U : F →L[𝕜] G} {R : G →L[𝕜] F}
    (hT : T.IsCompactParametrix S) (hU : U.IsCompactParametrix R) :
    (U.comp T).IsCompactParametrix (S.comp R) := by
  constructor
  · have heq : (S.comp R).comp (U.comp T) - 1 =
        S.comp ((R.comp U - 1).comp T) + (S.comp T - 1) := by
      simp only [comp_sub, sub_comp, comp_assoc, one_def, id_comp]
      abel
    rw [heq]
    exact ((hU.1.comp_clm T).clm_comp S).add hT.1
  · have heq : (U.comp T).comp (S.comp R) - 1 =
        U.comp ((T.comp S - 1).comp R) + (U.comp R - 1) := by
      simp only [comp_sub, sub_comp, comp_assoc, one_def, id_comp]
      abel
    rw [heq]
    exact ((hT.2.comp_clm R).clm_comp U).add hU.2

/-- A compact perturbation of the original map retains the same parametrix. -/
theorem IsCompactParametrix.add {T K : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : T.IsCompactParametrix S) (hK : IsCompactOperator K) :
    (T + K).IsCompactParametrix S := by
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

/-- A left inverse modulo compact operators and a right inverse modulo compact operators
of the same map differ by a compact operator. No other corner error is needed. -/
theorem isCompactOperator_sub_of_comp_sub_one (T : E →L[𝕜] F) (S R : F →L[𝕜] E)
    (hST : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E))
    (hTR : IsCompactOperator (T.comp R - 1 : F →L[𝕜] F)) : IsCompactOperator (S - R) := by
  have heq : S - R = (S.comp T - 1).comp R - S.comp (T.comp R - 1) := by
    simp only [sub_comp, comp_sub, comp_assoc, one_def, id_comp, comp_id]
    abel
  rw [heq]
  exact (hST.comp_clm R).sub (hTR.clm_comp S)

/-- Once one parametrix is fixed, all the others are exactly its compact perturbations. -/
theorem IsCompactParametrix.iff_isCompactOperator_sub {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : T.IsCompactParametrix S) (R : F →L[𝕜] E) :
    T.IsCompactParametrix R ↔ IsCompactOperator (R - S) := by
  constructor
  · intro hR
    exact T.isCompactOperator_sub_of_comp_sub_one R S hR.1 h.2
  · intro hRS
    simpa only [add_sub_cancel] using (h.symm.add hRS).symm

/-- Independent compact perturbations of an operator and its parametrix preserve the relation. -/
theorem IsCompactParametrix.add_add {T K : E →L[𝕜] F} {S L : F →L[𝕜] E}
    (h : T.IsCompactParametrix S) (hK : IsCompactOperator K) (hL : IsCompactOperator L) :
    (T + K).IsCompactParametrix (S + L) :=
  ((h.add hK).symm.add hL).symm

/-- Binary block sums carry the block sum of the respective parametrices. Iteration gives
parametrices for arbitrary finite block-diagonal sums, including finite-dimensional blocks. -/
theorem IsCompactParametrix.prodMap {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    {U : E' →L[𝕜] F'} {R : F' →L[𝕜] E'}
    (hT : T.IsCompactParametrix S) (hU : U.IsCompactParametrix R) :
    (T.prodMap U).IsCompactParametrix (S.prodMap R) := by
  constructor
  · convert hT.left.prodMap hU.left using 1
    ext x <;> simp
  · convert hT.right.prodMap hU.right using 1
    ext x <;> simp

end Topological

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Hilbert adjoints preserve compact parametrices, with the source and target corners swapped. -/
theorem IsCompactParametrix.adjoint {T : E →L[𝕜] F} {S : F →L[𝕜] E}
    (h : T.IsCompactParametrix S) : (T†).IsCompactParametrix (S†) := by
  constructor
  · simpa only [map_sub, adjoint_comp, adjoint_one] using h.2.adjoint
  · simpa only [map_sub, adjoint_comp, adjoint_one] using h.1.adjoint

/-- A pair of Hilbert adjoints is a compact-parametrix pair exactly when the original pair is. -/
@[simp]
theorem isCompactParametrix_adjoint_iff (T : E →L[𝕜] F) (S : F →L[𝕜] E) :
    (T†).IsCompactParametrix (S†) ↔ T.IsCompactParametrix S := by
  constructor
  · intro h
    simpa only [adjoint_adjoint] using h.adjoint
  · exact IsCompactParametrix.adjoint

end Hilbert

end ContinuousLinearMap
