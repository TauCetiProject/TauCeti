/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Algebra.Star.Projection.Idempotent
public import TauCeti.Analysis.Calculus.ContDiff.Adjoint
public import TauCeti.Analysis.Normed.Operator.Splitting.RangeComplement

/-!
# The orthogonal left inverse of an operator into a Hilbert space

Let `L : E →L[𝕜] F` be an operator from a normed space into a Hilbert space with a continuous
left inverse, for instance an injective operator with closed range out of a Banach space
(`ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range`). Among its continuous left
inverses exactly one vanishes on the orthogonal complement of its range: the *orthogonal left
inverse* `ContinuousLinearMap.orthogonalLeftInverse L`. Then `L ∘ R` is the orthogonal projection
onto the range of `L` and `1 - L ∘ R` the orthogonal projection onto its complement, the cokernel.

It is computed from any continuous left inverse `K`. The operator `e = L ∘ K` is an idempotent
with the range of `L`, and its range projection
`Π = e e† (1 - (e - e†)²)⁻¹` (`TauCeti.idempotentRangeProjection`) is the orthogonal projection
onto that range. The denominator `1 + x x†`, `x = e - e†`, is invertible for every operator `e` of
a Hilbert space (`ContinuousLinearMap.isUnit_idempotentProjectionDenom`), since
`⟪(1 + x x†) v, v⟫ = ‖v‖² + ‖x† v‖²`. Then `R = K Π`
(`ContinuousLinearMap.orthogonalLeftInverse_eq_comp_idempotentRangeProjection`).

The formula shows that `R` depends smoothly on `L`. Near an operator `L₀` with a left inverse
`K₀`, the left inverses `(K₀ L)⁻¹ K₀` of `L` along `ker K₀`
(`ContinuousLinearMap.leftInverseAlong`) are smooth in `L`, and so is the range projection.
Hence, over `ℝ`, the orthogonal left inverse is a `C^n` function of the operator on the open set
of operators with a continuous left inverse
(`ContinuousLinearMap.contDiffAt_orthogonalLeftInverse`).
No inner product on `E` is needed; typically `E` is a Sobolev space and `F` a space of `L²`
classes, and `R` inverts an injective elliptic operator on its range.

## Main definitions

* `ContinuousLinearMap.orthogonalLeftInverse L`: the left inverse of `L` vanishing on the
  orthogonal complement of its range, and `0` if `L` has no continuous left inverse.

## Main results

* `ContinuousLinearMap.isUnit_idempotentProjectionDenom`: the denominator of the range projection
  formula is invertible for every operator of a Hilbert space.
* `ContinuousLinearMap.orthogonalLeftInverse_comp_self`,
  `ContinuousLinearMap.orthogonalLeftInverse_apply_eq_zero`: `R` is a left inverse of `L` and
  vanishes on the orthogonal complement of the range.
* `ContinuousLinearMap.eq_orthogonalLeftInverse`: these two properties characterize it.
* `ContinuousLinearMap.isStarProjection_comp_orthogonalLeftInverse`,
  `ContinuousLinearMap.range_comp_orthogonalLeftInverse`,
  `ContinuousLinearMap.inner_apply_sub_apply_orthogonalLeftInverse`: `L ∘ R` is the orthogonal
  projection onto the range of `L`.
* `ContinuousLinearMap.contDiffAt_orthogonalLeftInverse`: over `ℝ`, `R` is a `C^n` function of
  `L`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Springer, 1976,
  Chapter I, §4.6.
* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Cambridge University Press,
  1998, Proposition 4.6.2.
-/

public section

open Function TauCeti
open scoped InnerProductSpace

namespace ContinuousLinearMap

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- **The denominator of the range projection formula is invertible** for every operator `e` of a
Hilbert space: it is `1 + x x†` with `x = e - e†`, and `⟪(1 + x x†) v, v⟫ = ‖v‖² + ‖x† v‖²`. -/
theorem isUnit_idempotentProjectionDenom (e : F →L[𝕜] F) :
    IsUnit (idempotentProjectionDenom e) := by
  rw [idempotentProjectionDenom_eq, star_eq_adjoint (e - star e)]
  generalize e - star e = x
  refine isUnit_of_forall_le_norm_inner_map _ one_pos fun v ↦ ?_
  have h : ⟪(1 + x * adjoint x) v, v⟫_𝕜 = ((‖v‖ ^ 2 + ‖adjoint x v‖ ^ 2 : ℝ) : 𝕜) := by
    rw [_root_.add_apply, one_apply_eq_self, mul_def, comp_apply, inner_add_left,
      ← adjoint_inner_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h, RCLike.norm_ofReal, NNReal.coe_one, mul_one]
  exact (le_add_of_nonneg_right (by positivity)).trans (le_abs_self _)

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {L : E →L[𝕜] F} {K R : F →L[𝕜] E}

/-- The properties of `K Π`, for a left inverse `K` of `L` and the range projection `Π` of the
idempotent `L K`: it is a left inverse of `L`, it vanishes on the orthogonal complement of the
range, `L K Π = Π`, `Π` is a star projection, and `f - Π f` is orthogonal to the range. -/
private theorem comp_idempotentRangeProjection_spec (hK : K ∘L L = .id 𝕜 E) :
    (K ∘L idempotentRangeProjection (L ∘L K)) ∘L L = .id 𝕜 E ∧
      (∀ f, (∀ x, ⟪L x, f⟫_𝕜 = 0) → (K ∘L idempotentRangeProjection (L ∘L K)) f = 0) ∧
      L ∘L (K ∘L idempotentRangeProjection (L ∘L K)) = idempotentRangeProjection (L ∘L K) ∧
      IsStarProjection (idempotentRangeProjection (L ∘L K)) ∧
      ∀ x f, ⟪L x, f - idempotentRangeProjection (L ∘L K) f⟫_𝕜 = 0 := by
  set P := idempotentRangeProjection (L ∘L K)
  have he : IsIdempotentElem (L ∘L K) := by
    rw [IsIdempotentElem, mul_def, comp_assoc, ← comp_assoc K, hK, id_comp]
  have hu := isUnit_idempotentProjectionDenom (L ∘L K)
  have hP := he.isStarProjection_idempotentRangeProjection_of_isUnit hu
  have hPe : P ∘L (L ∘L K) = L ∘L K := he.idempotentRangeProjection_mul_of_isUnit hu
  have heP : (L ∘L K) ∘L P = P := he.mul_idempotentRangeProjection
  have hPP (g : F) : P (P g) = P g := by
    rw [← comp_apply, ← mul_def, hP.isIdempotentElem.eq]
  -- `Π` fixes the range of `L`.
  have hPL : P ∘L L = L := by
    simpa only [comp_assoc, hK, comp_id] using congrArg (· ∘L L) hPe
  have hadj : adjoint P = P := by rw [← star_eq_adjoint, hP.isSelfAdjoint.star_eq]
  have horth (x : E) (f : F) : ⟪L x, f - P f⟫_𝕜 = 0 := by
    rw [← hPL, comp_apply, ← adjoint_inner_right, hadj, map_sub, hPP, sub_self, inner_zero_right]
  refine ⟨by rw [comp_assoc, hPL, hK], fun f hf ↦ ?_, by rw [← comp_assoc, heP], hP, horth⟩
  -- `‖Π f‖² = ⟪f, Π f⟫ = ⟪f, L (K Π f)⟫ = 0`.
  have h0 : P f = 0 := by
    rw [← inner_self_eq_zero (𝕜 := 𝕜), ← adjoint_inner_right, hadj, hPP, ← heP, comp_apply,
      comp_apply, ← inner_conj_symm, hf, map_zero]
  rw [comp_apply, h0, map_zero]

/-- For a continuous left inverse `K` of `L`, every continuous left inverse `R` of `L` vanishing on
the orthogonal complement of the range of `L` is `K Π`, where `Π` is the range projection of the
idempotent `L K`. -/
private theorem eq_comp_idempotentRangeProjection (hK : K ∘L L = .id 𝕜 E) (hR : R ∘L L = .id 𝕜 E)
    (hR0 : ∀ f, (∀ x, ⟪L x, f⟫_𝕜 = 0) → R f = 0) :
    R = K ∘L idempotentRangeProjection (L ∘L K) := by
  obtain ⟨-, -, hLR, -, horth⟩ := comp_idempotentRangeProjection_spec hK
  ext f
  -- Split `f = Π f + (f - Π f)` with `Π f = L (K Π f)` and `f - Π f` orthogonal to the range.
  have hsplit : f = L ((K ∘L idempotentRangeProjection (L ∘L K)) f) +
      (f - idempotentRangeProjection (L ∘L K) f) := by
    rw [← comp_apply L, hLR, add_sub_cancel]
  conv_lhs => rw [hsplit]
  rw [map_add, ← comp_apply R L, hR, id_apply, hR0 _ (horth · f), add_zero]

open Classical in
/-- **The orthogonal left inverse** of an operator `L` into a Hilbert space: the continuous left
inverse of `L` vanishing on the orthogonal complement of its range, when `L` has a continuous
left inverse (`ContinuousLinearMap.orthogonalLeftInverse_comp_self`,
`ContinuousLinearMap.orthogonalLeftInverse_apply_eq_zero`), and `0` otherwise. -/
noncomputable def orthogonalLeftInverse (L : E →L[𝕜] F) : F →L[𝕜] E :=
  if h : L.HasLeftInverse then
    h.leftInverse ∘L idempotentRangeProjection (L ∘L h.leftInverse)
  else 0

/-- **The orthogonal left inverse from any left inverse.** If `K` is a continuous left inverse of
`L`, then the orthogonal left inverse of `L` is `K Π`, where `Π` is the range projection of the
idempotent `L K`. -/
theorem orthogonalLeftInverse_eq_comp_idempotentRangeProjection (hK : K ∘L L = .id 𝕜 E) :
    L.orthogonalLeftInverse = K ∘L idempotentRangeProjection (L ∘L K) := by
  have h : L.HasLeftInverse := ⟨K, fun x ↦ by rw [← comp_apply K L, hK, id_apply]⟩
  obtain ⟨hR, hR0, -⟩ := comp_idempotentRangeProjection_spec (ext h.leftInverse_leftInverse)
  simp only [orthogonalLeftInverse, h, ↓reduceDIte]
  exact eq_comp_idempotentRangeProjection hK hR hR0

variable (h : L.HasLeftInverse)
include h

/-- The orthogonal left inverse is a left inverse. -/
theorem orthogonalLeftInverse_comp_self : L.orthogonalLeftInverse ∘L L = .id 𝕜 E := by
  rw [orthogonalLeftInverse_eq_comp_idempotentRangeProjection (ext h.leftInverse_leftInverse)]
  exact (comp_idempotentRangeProjection_spec (ext h.leftInverse_leftInverse)).1

/-- The orthogonal left inverse is a left inverse. -/
@[simp]
theorem orthogonalLeftInverse_apply_self (x : E) : L.orthogonalLeftInverse (L x) = x := by
  rw [← comp_apply _ L, orthogonalLeftInverse_comp_self h, id_apply]

/-- The orthogonal left inverse vanishes on the orthogonal complement of the range. -/
theorem orthogonalLeftInverse_apply_eq_zero {f : F} (hf : ∀ x, ⟪L x, f⟫_𝕜 = 0) :
    L.orthogonalLeftInverse f = 0 := by
  rw [orthogonalLeftInverse_eq_comp_idempotentRangeProjection (ext h.leftInverse_leftInverse)]
  exact (comp_idempotentRangeProjection_spec (ext h.leftInverse_leftInverse)).2.1 f hf

/-- **Characterization of the orthogonal left inverse.** A continuous left inverse of `L` vanishing
on the orthogonal complement of its range is the orthogonal left inverse. -/
theorem eq_orthogonalLeftInverse (hR : R ∘L L = .id 𝕜 E)
    (hR0 : ∀ f, (∀ x, ⟪L x, f⟫_𝕜 = 0) → R f = 0) : R = L.orthogonalLeftInverse := by
  rw [orthogonalLeftInverse_eq_comp_idempotentRangeProjection (ext h.leftInverse_leftInverse)]
  exact eq_comp_idempotentRangeProjection (ext h.leftInverse_leftInverse) hR hR0

/-- `L ∘ R` is a star projection: the orthogonal projection onto the range of `L`
(`ContinuousLinearMap.range_comp_orthogonalLeftInverse`). -/
theorem isStarProjection_comp_orthogonalLeftInverse :
    IsStarProjection (L ∘L L.orthogonalLeftInverse) := by
  obtain ⟨-, -, hLR, hP, -⟩ := comp_idempotentRangeProjection_spec (ext h.leftInverse_leftInverse)
  rw [orthogonalLeftInverse_eq_comp_idempotentRangeProjection (ext h.leftInverse_leftInverse), hLR]
  exact hP

/-- The star projection `L ∘ R` has the range of `L`. -/
theorem range_comp_orthogonalLeftInverse : (L ∘L L.orthogonalLeftInverse).range = L.range := by
  refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨L x, by simp [h]⟩

/-- The component `f - L (R f)` of `f` is orthogonal to the range of `L`: `L R` is the orthogonal
projection onto the range and `1 - L R` the orthogonal projection onto the cokernel. -/
theorem inner_apply_sub_apply_orthogonalLeftInverse (x : E) (f : F) :
    ⟪L x, f - L (L.orthogonalLeftInverse f)⟫_𝕜 = 0 := by
  have hK : h.leftInverse ∘L L = .id 𝕜 E := ext h.leftInverse_leftInverse
  obtain ⟨-, -, hLR, -, horth⟩ := comp_idempotentRangeProjection_spec hK
  rw [orthogonalLeftInverse_eq_comp_idempotentRangeProjection hK, ← comp_apply L, hLR]
  exact horth x f

omit h

/-- **Operators with closed range into a Hilbert space have continuous left inverses.** An
injective operator with closed range from a Banach space into a Hilbert space has a continuous
left inverse: its range is complemented by its orthogonal complement. -/
theorem HasLeftInverse.of_injective_of_isClosed_range [CompleteSpace E] (hinj : Injective L)
    (hcl : IsClosed (Set.range L)) : L.HasLeftInverse := by
  have : CompleteSpace L.range := hcl.completeSpace_coe
  exact .of_injective_of_isClosed_range_of_closedComplement_range hinj hcl
    (.of_isCompl_isClosed L.range.isCompl_orthogonal hcl
      (Submodule.isClosed_orthogonal _))

end RCLike

section Real

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}

/-- The range projection formula is a smooth function of the operator of a real Hilbert space,
even away from idempotents. -/
theorem contDiff_idempotentRangeProjection :
    ContDiff ℝ n (idempotentRangeProjection : (F →L[ℝ] F) → F →L[ℝ] F) := by
  have hs : ContDiff ℝ n (star : (F →L[ℝ] F) → F →L[ℝ] F) := by
    have h : (star : (F →L[ℝ] F) → F →L[ℝ] F) = fun e ↦ adjoint (id e) :=
      funext star_eq_adjoint
    rw [h]
    exact contDiff_id.adjoint
  have hd : ContDiff ℝ n fun e : F →L[ℝ] F ↦ idempotentProjectionDenom e := by
    simp_rw [idempotentProjectionDenom_def]
    exact contDiff_const.sub ((contDiff_id.sub hs).pow 2)
  have hi : ContDiff ℝ n fun e : F →L[ℝ] F ↦ Ring.inverse (idempotentProjectionDenom e) := by
    refine contDiff_iff_contDiffAt.2 fun e ↦ ?_
    obtain ⟨u, hu⟩ := isUnit_idempotentProjectionDenom e
    exact (hu ▸ contDiffAt_ringInverse ℝ u).comp e hd.contDiffAt
  -- Eta-expand so that the formula of the range projection rewrites under `ContDiff`.
  change ContDiff ℝ n fun e : F →L[ℝ] F ↦ idempotentRangeProjection e
  simp_rw [idempotentRangeProjection_def]
  exact (contDiff_id.mul hs).mul hi

/-- **The orthogonal left inverse is a smooth function of the operator.** Over `ℝ`, at every
operator `L` from a Banach space into a Hilbert space with a continuous left inverse, the
orthogonal left inverse is `C^n` in the operator. -/
theorem contDiffAt_orthogonalLeftInverse {L : E →L[ℝ] F} (h : L.HasLeftInverse) :
    ContDiffAt ℝ n (orthogonalLeftInverse : (E →L[ℝ] F) → F →L[ℝ] E) L := by
  set K := h.leftInverse
  have hKL : (K ∘L L).IsInvertible := by
    have hK : K ∘L L = .id ℝ E := ext h.leftInverse_leftInverse
    rw [hK]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  -- Near `L`, the left inverses `(K L')⁻¹ K` of `L'` are smooth, and give the formula.
  have hΛ : ContDiffAt ℝ n (fun L' : E →L[ℝ] F ↦ leftInverseAlong L' K) L :=
    contDiffAt_id.leftInverseAlong contDiffAt_const hKL
  refine (hΛ.clm_comp (contDiff_idempotentRangeProjection.contDiffAt.comp L
    (contDiffAt_id.clm_comp hΛ))).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_setOf_isInvertible_comp (P := K) continuous_id).mem_nhds hKL]
    with L' hL'
  exact orthogonalLeftInverse_eq_comp_idempotentRangeProjection (leftInverseAlong_comp_self hL')

/-- The orthogonal left inverses of a family of operators with continuous left inverses have the
regularity of the family. -/
theorem _root_.ContDiffAt.orthogonalLeftInverse {L : X → E →L[ℝ] F} {x : X}
    (hL : ContDiffAt ℝ n L x) (h : (L x).HasLeftInverse) :
    ContDiffAt ℝ n (fun y ↦ (L y).orthogonalLeftInverse) x :=
  (contDiffAt_orthogonalLeftInverse h).comp x hL

/-- The orthogonal left inverses of a `C^n` family of operators with continuous left inverses form
a `C^n` family. -/
theorem _root_.ContDiff.orthogonalLeftInverse {L : X → E →L[ℝ] F} (hL : ContDiff ℝ n L)
    (h : ∀ x, (L x).HasLeftInverse) : ContDiff ℝ n fun y ↦ (L y).orthogonalLeftInverse :=
  contDiff_iff_contDiffAt.2 fun x ↦ hL.contDiffAt.orthogonalLeftInverse (h x)

end Real

end ContinuousLinearMap
