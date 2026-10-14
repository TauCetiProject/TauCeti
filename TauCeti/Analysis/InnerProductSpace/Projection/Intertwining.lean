/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

/-!
# Davis's intertwining unitary

A complete family of orthogonal projections on an inner product space `E` is a finite family
`(Pⱼ)` of symmetric idempotents with `∑ⱼ Pⱼ = 1`. Such a family is automatically orthogonal,
`Pᵢ Pⱼ = 0` for `i ≠ j`, so distinct ranges are orthogonal and the family is a family of
`CompleteOrthogonalIdempotents` in `Module.End 𝕜 E`.

Let `(Pⱼ)` and `(P'ⱼ)` be two such families on a finite-dimensional real or complex inner product
space, indexed by the same type, and suppose that `P'ⱼ` is injective on `range Pⱼ` for every `j`
(Davis's non-degeneracy condition). Then there is exactly one unitary `U` that is simultaneously a
polar factor of every overlap `P'ⱼ Pⱼ`, that is `U |P'ⱼ Pⱼ| = P'ⱼ Pⱼ` for every `j`. On `range Pⱼ`
it is the polar factor of the block `P'ⱼ Pⱼ`, and it intertwines the two families:
`U Pⱼ = P'ⱼ U` for every `j`. This is the unitary used by Davis to compare the spectral
subspaces of two self-adjoint operators.

The unitary is the polar factor of the assembled overlap `T = ∑ⱼ P'ⱼ Pⱼ`, which satisfies
`T Pⱼ = P'ⱼ Pⱼ = P'ⱼ T`; the non-degeneracy condition makes `T` injective. In the case of two
complementary pairs of projections this is Kato's unitary `U = T (T† T)^(-1/2)` for
`T = Q P + (1 - Q) (1 - P)`.

## Main results

* `CompleteOrthogonalIdempotents.of_isSymmetricProjection`: symmetric idempotents summing to the
  identity are complete orthogonal idempotents.
* `TauCeti.existsUnique_linearIsometryEquiv_comp_operatorAbs_eq`: under Davis's non-degeneracy
  condition, there is a unique unitary `U` with `U |P'ⱼ Pⱼ| = P'ⱼ Pⱼ` for every `j`.
* `TauCeti.comp_eq_comp_of_forall_comp_operatorAbs_eq`: this unitary satisfies `U Pⱼ = P'ⱼ U`;
  so does every linear map that is a polar factor of each overlap.
* `TauCeti.exists_linearIsometryEquiv_comp_eq_comp`: a unitary intertwining the two families
  exists.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl. **6** (1963),
  159–173.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer, 1966, Chapter I, §4.6.
-/

public section

open LinearMap
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- Symmetric idempotents summing to the identity are orthogonal: a complete family of orthogonal
projections is a family of complete orthogonal idempotents. -/
theorem CompleteOrthogonalIdempotents.of_isSymmetricProjection {P : ι → E →ₗ[𝕜] E}
    (hP : ∀ j, (P j).IsSymmetricProjection) (hsum : ∑ j, P j = 1) :
    CompleteOrthogonalIdempotents P := by
  classical
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.2 ⟨fun i j hij ↦ ?_, hsum⟩
  ext x
  set y := P j x
  have hidem (k : ι) (z : E) : P k (P k z) = P k z := by
    rw [← Module.End.mul_apply, (hP k).isIdempotentElem.eq]
  have hnorm (k : ι) : RCLike.re ⟪P k y, y⟫_𝕜 = ‖P k y‖ ^ 2 := by
    rw [← hidem k y, (hP k).isSymmetric, hidem, inner_self_eq_norm_sq]
  have htotal : ∑ k, ‖P k y‖ ^ 2 = ‖y‖ ^ 2 := by
    have hy : ∑ k, P k y = y := by rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
    simp_rw [← hnorm, ← map_sum, ← sum_inner, hy, inner_self_eq_norm_sq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hidem, add_eq_left] at htotal
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ sq_nonneg ‖P k y‖).1 htotal i
    (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩)
  rw [Module.End.mul_apply, LinearMap.zero_apply]
  simpa using hi

namespace TauCeti

variable {P P' : ι → E →ₗ[𝕜] E}

section Overlap

variable (hP : CompleteOrthogonalIdempotents P) (hP' : CompleteOrthogonalIdempotents P')
include hP

/-- The assembled overlap `T = ∑ⱼ P'ⱼ Pⱼ` restricts to the block overlap on `range Pⱼ`. -/
private theorem overlap_comp (j : ι) : (∑ k, P' k ∘ₗ P k) ∘ₗ P j = P' j ∘ₗ P j := by
  classical
  simp only [← Module.End.mul_eq_comp, Finset.sum_mul, mul_assoc, hP.mul_eq, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include hP'

/-- The assembled overlap intertwines the two families: `T Pⱼ = P'ⱼ T`. -/
private theorem overlap_comp_eq_comp (j : ι) :
    (∑ k, P' k ∘ₗ P k) ∘ₗ P j = P' j ∘ₗ ∑ k, P' k ∘ₗ P k := by
  classical
  rw [overlap_comp hP]
  simp only [← Module.End.mul_eq_comp, Finset.mul_sum, ← mul_assoc, hP'.mul_eq, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

variable [FiniteDimensional 𝕜 E] (hPs : ∀ j, (P j).IsSymmetric) (hP's : ∀ j, (P' j).IsSymmetric)
include hPs hP's

/-- Each `Pⱼ` commutes with the source Gram operator of the assembled overlap. -/
private theorem commute_adjoint_overlap_comp_overlap (j : ι) :
    Commute (P j) ((∑ k, P' k ∘ₗ P k).adjoint ∘ₗ ∑ k, P' k ∘ₗ P k) := by
  set T := ∑ k, P' k ∘ₗ P k
  have h := overlap_comp_eq_comp hP hP' j
  have hadj : P j ∘ₗ T.adjoint = T.adjoint ∘ₗ P' j := by
    simpa only [adjoint_comp, (hPs j).adjoint_eq, (hP's j).adjoint_eq] using
      congrArg LinearMap.adjoint h
  rw [commute_iff_eq, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← comp_assoc, hadj,
    comp_assoc, ← h, comp_assoc]

/-- The modulus of the block overlap `P'ⱼ Pⱼ` is the restriction `|T| Pⱼ` of the modulus of the
assembled overlap. -/
private theorem operatorAbs_comp (j : ι) :
    (P' j ∘ₗ P j).operatorAbs = (∑ k, P' k ∘ₗ P k).operatorAbs ∘ₗ P j := by
  rw [← overlap_comp hP j]
  exact operatorAbs_comp_of_commute ⟨hP.idem j, hPs j⟩
    (commute_adjoint_overlap_comp_overlap hP hP' hPs hP's j)

/-- A map is a simultaneous polar factor of every block overlap exactly when it is a polar factor
of the assembled overlap. -/
private theorem forall_comp_operatorAbs_eq_iff (V : E →ₗ[𝕜] E) :
    (∀ j, V ∘ₗ (P' j ∘ₗ P j).operatorAbs = P' j ∘ₗ P j) ↔
      V ∘ₗ (∑ k, P' k ∘ₗ P k).operatorAbs = ∑ k, P' k ∘ₗ P k := by
  simp only [operatorAbs_comp hP hP' hPs hP's, ← comp_assoc]
  constructor
  · intro h
    rw [← mul_one (V ∘ₗ _), ← hP.complete, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ h j
  · intro h j
    rw [h, overlap_comp hP]

end Overlap

variable [FiniteDimensional 𝕜 E]

/-- Under Davis's non-degeneracy condition the modulus of the assembled overlap is surjective. -/
private theorem surjective_operatorAbs_overlap (hP : CompleteOrthogonalIdempotents P)
    (hP' : CompleteOrthogonalIdempotents P') (hnd : ∀ j, Disjoint (range (P j)) (ker (P' j))) :
    Function.Surjective (∑ k, P' k ∘ₗ P k).operatorAbs := by
  refine injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 ?_)
  rw [ker_operatorAbs, LinearMap.ker_eq_bot']
  intro x hx
  have hblock (j : ι) : P j x = 0 := by
    refine (disjoint_ker.1 (hnd j)) _ (mem_range_self _ x) ?_
    rw [← comp_apply, ← overlap_comp hP, overlap_comp_eq_comp hP hP', comp_apply, hx, map_zero]
  rw [← Module.End.one_apply (R := 𝕜) x, ← hP.complete, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun j _ ↦ hblock j

variable (hP : ∀ j, (P j).IsSymmetricProjection) (hPsum : ∑ j, P j = 1)
  (hP' : ∀ j, (P' j).IsSymmetricProjection) (hP'sum : ∑ j, P' j = 1)
  (hnd : ∀ j, Disjoint (range (P j)) (ker (P' j)))
include hP hPsum hP' hP'sum hnd

/-- **Davis's intertwining unitary.** Let `(Pⱼ)` and `(P'ⱼ)` be complete families of orthogonal
projections such that `P'ⱼ` is injective on `range Pⱼ` for every `j`. Then the polar factors of
the overlaps `P'ⱼ Pⱼ` assemble to a unique unitary `U`: it is the only unitary with
`U |P'ⱼ Pⱼ| = P'ⱼ Pⱼ` for every `j`. -/
theorem existsUnique_linearIsometryEquiv_comp_operatorAbs_eq :
    ∃! U : E ≃ₗᵢ[𝕜] E, ∀ j, (U : E →ₗ[𝕜] E) ∘ₗ (P' j ∘ₗ P j).operatorAbs = P' j ∘ₗ P j := by
  have hc := CompleteOrthogonalIdempotents.of_isSymmetricProjection hP hPsum
  have hc' := CompleteOrthogonalIdempotents.of_isSymmetricProjection hP' hP'sum
  have hPs (j : ι) := (hP j).isSymmetric
  have hP's (j : ι) := (hP' j).isSymmetric
  simp only [forall_comp_operatorAbs_eq_iff hc hc' hPs hP's]
  set T := ∑ k, P' k ∘ₗ P k
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_inner_eq (v := T.operatorAbs) (w := T)
    fun x y ↦ by
      rw [← T.isSymmetric_operatorAbs, ← comp_apply, operatorAbs_sq, comp_apply,
        adjoint_inner_left]
  refine ⟨U, LinearMap.ext hU, fun V hV ↦ ?_⟩
  refine LinearIsometryEquiv.toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective <|
    (cancel_right (surjective_operatorAbs_overlap hc hc' hnd)).1 ?_
  exact hV.trans (LinearMap.ext hU).symm

/-- **Davis's intertwining equation.** A map that is a polar factor of every overlap `P'ⱼ Pⱼ`,
such as the unitary of `existsUnique_linearIsometryEquiv_comp_operatorAbs_eq`, intertwines the
two families of projections: `V Pⱼ = P'ⱼ V`. -/
theorem comp_eq_comp_of_forall_comp_operatorAbs_eq {V : E →ₗ[𝕜] E}
    (hV : ∀ j, V ∘ₗ (P' j ∘ₗ P j).operatorAbs = P' j ∘ₗ P j) (j : ι) :
    V ∘ₗ P j = P' j ∘ₗ V := by
  have hc := CompleteOrthogonalIdempotents.of_isSymmetricProjection hP hPsum
  have hc' := CompleteOrthogonalIdempotents.of_isSymmetricProjection hP' hP'sum
  have hPs (k : ι) := (hP k).isSymmetric
  have hP's (k : ι) := (hP' k).isSymmetric
  rw [forall_comp_operatorAbs_eq_iff hc hc' hPs hP's] at hV
  set T := ∑ k, P' k ∘ₗ P k
  have hcomm : P j ∘ₗ T.operatorAbs = T.operatorAbs ∘ₗ P j :=
    (commute_operatorAbs_of_commute (commute_adjoint_overlap_comp_overlap hc hc' hPs hP's j)).eq
  refine (cancel_right (surjective_operatorAbs_overlap hc hc' hnd)).1 ?_
  rw [comp_assoc, hcomm, ← comp_assoc, hV, overlap_comp_eq_comp hc hc', comp_assoc, hV]

/-- Under Davis's non-degeneracy condition, some unitary intertwines the two complete families of
orthogonal projections: `U Pⱼ = P'ⱼ U` for every `j`. -/
theorem exists_linearIsometryEquiv_comp_eq_comp :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ j, (U : E →ₗ[𝕜] E) ∘ₗ P j = P' j ∘ₗ (U : E →ₗ[𝕜] E) := by
  obtain ⟨U, hU, -⟩ := existsUnique_linearIsometryEquiv_comp_operatorAbs_eq hP hPsum hP' hP'sum hnd
  exact ⟨U, comp_eq_comp_of_forall_comp_operatorAbs_eq hP hPsum hP' hP'sum hnd hU⟩

end TauCeti
