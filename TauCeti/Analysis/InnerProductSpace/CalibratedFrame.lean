/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import Mathlib.LinearAlgebra.Determinant
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Calibrated frames for real alternating forms

An ordered frame `v : ι → E` in a real inner product space is **calibrated** by a continuous
alternating form `φ : E [⋀^ι]→L[ℝ] ℝ` (`TauCeti.IsCalibratedFrame φ v`) when `v` is orthonormal
and `φ v = 1`. When `φ` has comass at most one (`‖φ‖ ≤ 1`), calibrated frames are precisely the
positively oriented orthonormal frames of the contact set (equality planes) of `φ`.

This file develops the linear-algebraic invariance and characterization API of calibrated frames:

* Existence of a calibrated frame forces `1 ≤ ‖φ‖`, so `‖φ‖ = 1` whenever `‖φ‖ ≤ 1`.
* A zero form calibrates no frame; reversing a vector or swapping two distinct vectors toggles
  between `φ` and `-φ`; even permutations preserve calibration.
* Pullback along any linear isometry `f : E →ₗᵢ[ℝ] F` preserves calibrated frames.
* Right multiplication of a frame by a special orthogonal matrix `g ∈ SO(ι)` preserves calibrated
  frames, via the general matrix-action formula `φ (fun i ↦ ∑ j, A i j • v j) = A.det • φ v`.
* On a finite-dimensional real inner product space, a unit `k`-vector `η : ⋀[ℝ]^k E` induces the
  form `alternatingFormEquiv E k η` whose calibrated frames are precisely the orthonormal frames
  with `v₁ ∧ ⋯ ∧ vₖ = η`. In particular, a unit decomposable form `e₁* ∧ ⋯ ∧ eₖ*` calibrates
  precisely the positively oriented orthonormal frames of the span of `e`, and `-φ` calibrates the
  opposite orientation.

## Main definitions

* `TauCeti.IsCalibratedFrame`: predicate `Orthonormal ℝ v ∧ φ v = 1`.

## Main results

* `AlternatingMap.map_sum_smul` and `ContinuousAlternatingMap.map_sum_smul`: action of a square
  matrix on a frame multiplies an alternating map by its determinant.
* `TauCeti.IsCalibratedFrame.one_le_norm`, `TauCeti.IsCalibratedFrame.norm_eq_one`: comass lower
  bound and equality from a calibrated frame.
* `TauCeti.isCalibratedFrame_comp_linearIsometry_iff`: invariance under linear isometries.
* `TauCeti.isCalibratedFrame_sum_smul_iff`: right `SO(ι)` invariance.
* `TauCeti.isCalibratedFrame_alternatingFormEquiv_iff` and
  `TauCeti.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff`: calibrated frames of a unit
  `k`-vector form and of a unit decomposable form.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.3.
* D. Joyce, *Lectures on Calabi–Yau and special Lagrangian geometry*, arXiv:math/0108088 (2001),
  Definition 2.1.
-/

public section

open scoped RealInnerProductSpace Matrix

/-! ### Action of a square matrix on alternating maps -/

namespace AlternatingMap

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]

/-- Applying an alternating map to linear combinations of a frame `v` with coefficients given by
the rows of a square matrix `A` multiplies `f v` by `A.det`. -/
theorem map_sum_smul (f : M [⋀^ι]→ₗ[R] N) (A : Matrix ι ι R) (v : ι → M) :
    f (fun i ↦ ∑ j, A i j • v j) = A.det • f v := by
  let L : (ι → R) →ₗ[R] M := Fintype.linearCombination R v
  have hL : L ∘ Pi.basisFun R ι = v := by
    ext j
    simp [L]
  have h := DFunLike.congr_fun ((f.compLinearMap L).eq_basis_det_smulRight (Pi.basisFun R ι))
    (fun i ↦ A i)
  rw [AlternatingMap.compLinearMap_apply, AlternatingMap.compLinearMap_apply,
    AlternatingMap.smulRight_apply, Pi.basisFun_det_apply] at h
  simpa [L, hL, Function.comp_def, Fintype.linearCombination_apply,
    show Matrix.of (fun i ↦ A i) = A from rfl] using h

end AlternatingMap

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] [DecidableEq ι]

/-- Applying a continuous alternating map to linear combinations of a frame `v` with coefficients
given by the rows of a square matrix `A` multiplies `φ v` by `A.det`. -/
theorem map_sum_smul (φ : E [⋀^ι]→L[𝕜] F) (A : Matrix ι ι 𝕜) (v : ι → E) :
    φ (fun i ↦ ∑ j, A i j • v j) = A.det • φ v :=
  φ.toAlternatingMap.map_sum_smul A v

end ContinuousAlternatingMap

/-! ### Calibrated frames -/

namespace TauCeti

section Basic

variable {E F ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An ordered frame `v : ι → E` is **calibrated** by a real continuous alternating form `φ` when
`v` is orthonormal and `φ v = 1`. -/
def IsCalibratedFrame (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) : Prop :=
  Orthonormal ℝ v ∧ φ v = 1

/-- Unfolding lemma for `TauCeti.IsCalibratedFrame`. -/
theorem isCalibratedFrame_iff {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E} :
    IsCalibratedFrame φ v ↔ Orthonormal ℝ v ∧ φ v = 1 := Iff.rfl

/-- A calibrated frame is orthonormal. -/
theorem IsCalibratedFrame.orthonormal {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : IsCalibratedFrame φ v) : Orthonormal ℝ v := h.1

/-- A form evaluates to `1` on every frame it calibrates. -/
theorem IsCalibratedFrame.apply {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : IsCalibratedFrame φ v) : φ v = 1 := h.2

/-- A form admitting a calibrated frame has comass at least one. -/
theorem IsCalibratedFrame.one_le_norm [Fintype ι] {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : IsCalibratedFrame φ v) : 1 ≤ ‖φ‖ := by
  simpa [h.apply, h.orthonormal.norm_eq_one] using φ.le_opNorm v

/-- A form of comass at most one that calibrates a frame has comass exactly one. -/
theorem IsCalibratedFrame.norm_eq_one [Fintype ι] {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : IsCalibratedFrame φ v) (hφ : ‖φ‖ ≤ 1) : ‖φ‖ = 1 :=
  le_antisymm hφ h.one_le_norm

/-- The zero form calibrates no frame. -/
@[simp]
theorem not_isCalibratedFrame_zero (v : ι → E) :
    ¬ IsCalibratedFrame (0 : E [⋀^ι]→L[ℝ] ℝ) v := by
  intro h
  have h1 := h.apply
  simp at h1

/-- A frame cannot be calibrated by both `φ` and `-φ`. -/
theorem IsCalibratedFrame.not_neg {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : IsCalibratedFrame φ v) : ¬ IsCalibratedFrame (-φ) v := by
  intro hneg
  have h1 : -(1 : ℝ) = 1 := by simpa [h.apply] using hneg.apply
  norm_num at h1

/-- In degree zero (any empty index type), a frame is calibrated by `φ` iff `φ` takes the value `1`
on it, since every empty family is vacuously orthonormal. -/
theorem isCalibratedFrame_of_isEmpty_iff [IsEmpty ι] (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) :
    IsCalibratedFrame φ v ↔ φ v = 1 :=
  ⟨fun h ↦ h.apply, fun h ↦ ⟨⟨isEmptyElim, isEmptyElim⟩, h⟩⟩

/-- In degree zero, the constant form `c` calibrates a frame iff `c = 1`. -/
@[simp]
theorem isCalibratedFrame_constOfIsEmpty_iff [IsEmpty ι] (c : ℝ) (v : ι → E) :
    IsCalibratedFrame (ContinuousAlternatingMap.constOfIsEmpty ℝ E ι c) v ↔ c = 1 := by
  rw [isCalibratedFrame_of_isEmpty_iff, ContinuousAlternatingMap.constOfIsEmpty_apply]

/-! ### Invariance under permutations, orientation reversal, isometries, and `SO(ι)` -/

/-- Reversing a single vector of a frame toggles calibration between `φ` and `-φ`. -/
theorem isCalibratedFrame_neg_update_iff [DecidableEq ι] (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) (i : ι) :
    IsCalibratedFrame (-φ) (Function.update v i (-v i)) ↔ IsCalibratedFrame φ v := by
  have hdir (w : ι → E) (hw : Orthonormal ℝ w) : Orthonormal ℝ (Function.update w i (-w i)) := by
    refine ⟨fun j ↦ ?_, fun j k hjk ↦ ?_⟩
    · by_cases hj : j = i
      · subst hj; simp [hw.1 j]
      · simp [hj, hw.1 j]
    · by_cases hj : j = i
      · subst hj; simp [hjk.symm, hw.2 hjk]
      · by_cases hk : k = i
        · subst hk; simp [hj, hw.2 hjk]
        · simp [hj, hk, hw.2 hjk]
  have horth : Orthonormal ℝ (Function.update v i (-v i)) ↔ Orthonormal ℝ v :=
    ⟨fun hv ↦ by simpa [Function.update_idem, Function.update_eq_self] using hdir _ hv, hdir v⟩
  have hval : (-φ) (Function.update v i (-v i)) = φ v := by
    rw [ContinuousAlternatingMap.neg_apply, ← ContinuousAlternatingMap.coe_toAlternatingMap,
      φ.toAlternatingMap.map_update_neg, Function.update_eq_self, neg_neg,
      ContinuousAlternatingMap.coe_toAlternatingMap]
  simp only [isCalibratedFrame_iff, horth, hval]

/-- An even permutation of a frame preserves calibration. -/
theorem isCalibratedFrame_comp_perm_iff [Fintype ι] [DecidableEq ι]
    (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) {σ : Equiv.Perm ι} (hσ : Equiv.Perm.sign σ = 1) :
    IsCalibratedFrame φ (v ∘ σ) ↔ IsCalibratedFrame φ v := by
  have horth : Orthonormal ℝ (v ∘ σ) ↔ Orthonormal ℝ v := by
    refine ⟨fun h ↦ ?_, fun h ↦ h.comp σ σ.injective⟩
    simpa [Function.comp_assoc] using h.comp σ.symm σ.symm.injective
  have hval : φ (v ∘ σ) = φ v := by
    rw [← ContinuousAlternatingMap.coe_toAlternatingMap, φ.toAlternatingMap.map_perm v σ,
      hσ, one_smul, ContinuousAlternatingMap.coe_toAlternatingMap]
  simp only [isCalibratedFrame_iff, horth, hval]

/-- Swapping two distinct vectors of a frame toggles calibration between `φ` and `-φ`. -/
theorem isCalibratedFrame_neg_comp_swap_iff [DecidableEq ι]
    (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) {i j : ι} (hij : i ≠ j) :
    IsCalibratedFrame (-φ) (v ∘ Equiv.swap i j) ↔ IsCalibratedFrame φ v := by
  have horth : Orthonormal ℝ (v ∘ Equiv.swap i j) ↔ Orthonormal ℝ v := by
    refine ⟨fun h ↦ ?_, fun h ↦ h.comp _ (Equiv.swap i j).injective⟩
    simpa [Function.comp_def] using h.comp (Equiv.swap i j) (Equiv.swap i j).injective
  have hval : (-φ) (v ∘ Equiv.swap i j) = φ v := by
    rw [ContinuousAlternatingMap.neg_apply, ← ContinuousAlternatingMap.coe_toAlternatingMap,
      φ.toAlternatingMap.map_swap v hij, neg_neg, ContinuousAlternatingMap.coe_toAlternatingMap]
  simp only [isCalibratedFrame_iff, horth, hval]

/-- Pullback along a linear isometry preserves calibrated frames: `v` is calibrated by `f* φ`
exactly when `f ∘ v` is calibrated by `φ`. -/
theorem isCalibratedFrame_comp_linearIsometry_iff (f : E →ₗᵢ[ℝ] F)
    (φ : F [⋀^ι]→L[ℝ] ℝ) (v : ι → E) :
    IsCalibratedFrame (φ.compContinuousLinearMap f.toContinuousLinearMap) v ↔
      IsCalibratedFrame φ (f ∘ v) := by
  have horth : Orthonormal ℝ (f ∘ v) ↔ Orthonormal ℝ v := by
    simp only [Orthonormal, Function.comp_apply, f.norm_map, f.inner_map_map]
  simp only [isCalibratedFrame_iff, horth,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    LinearIsometry.coe_toContinuousLinearMap]

end Basic

section OrthogonalGroup

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Right multiplication of a calibrated frame by a special orthogonal matrix produces a calibrated
frame. -/
theorem IsCalibratedFrame.sum_smul [Fintype ι] [DecidableEq ι] {φ : E [⋀^ι]→L[ℝ] ℝ}
    {v : ι → E} (h : IsCalibratedFrame φ v) (g : Matrix.specialOrthogonalGroup ι ℝ) :
    IsCalibratedFrame φ (fun i ↦ ∑ j, g.1 i j • v j) := by
  obtain ⟨hgO, hgdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp g.2
  refine ⟨(h.orthonormal.orthonormal_sum_smul_iff g.1).2 ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hgO
  · rw [φ.map_sum_smul g.1 v, hgdet, one_smul, h.apply]

/-- Right `SO(ι)` invariance of calibrated frames: multiplying a frame on the right by a matrix in
`SO(ι)` preserves `TauCeti.IsCalibratedFrame`. -/
theorem isCalibratedFrame_sum_smul_iff [Fintype ι] [DecidableEq ι] (φ : E [⋀^ι]→L[ℝ] ℝ)
    (v : ι → E) (g : Matrix.specialOrthogonalGroup ι ℝ) :
    IsCalibratedFrame φ (fun i ↦ ∑ j, g.1 i j • v j) ↔ IsCalibratedFrame φ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.sum_smul g⟩
  have hinv := h.sum_smul g⁻¹
  have hmul : (g⁻¹ : Matrix.specialOrthogonalGroup ι ℝ).1 * g.1 = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  have heq : (fun i ↦ ∑ j, (g⁻¹ : Matrix.specialOrthogonalGroup ι ℝ).1 i j •
      ∑ k, g.1 j k • v k) = v := by
    ext i
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, hmul, Matrix.one_apply]
    simp
  rwa [heq] at hinv

end OrthogonalGroup

/-! ### Exterior-power characterizations in finite dimensions -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}

/-- Two orthonormal frames with the same exterior product are simultaneously calibrated by any
alternating form. -/
theorem isCalibratedFrame_iff_of_ιMulti_eq (φ : E [⋀^Fin k]→L[ℝ] ℝ) {v w : Fin k → E}
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (h : exteriorPower.ιMulti ℝ k v = exteriorPower.ιMulti ℝ k w) :
    IsCalibratedFrame φ v ↔ IsCalibratedFrame φ w := by
  have hval : φ v = φ w := by
    rw [← inner_alternatingFormEquiv_symm_ιMulti φ v, h, inner_alternatingFormEquiv_symm_ιMulti]
  simp only [isCalibratedFrame_iff, hv, hw, hval]

/-- The calibrated frames of the form associated to a unit `k`-vector `η` are precisely the
orthonormal frames whose exterior product equals `η`. -/
theorem isCalibratedFrame_alternatingFormEquiv_iff {η : ⋀[ℝ]^k E} (hη : ‖η‖ = 1) (v : Fin k → E) :
    IsCalibratedFrame (alternatingFormEquiv E k η) v ↔
      Orthonormal ℝ v ∧ exteriorPower.ιMulti ℝ k v = η := by
  constructor
  · rintro ⟨hv, hval⟩
    refine ⟨hv, ?_⟩
    rw [alternatingFormEquiv_apply] at hval
    have hsq : ‖exteriorPower.ιMulti ℝ k v - η‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hv.norm_ιMulti, hη, real_inner_comm, hval]
      norm_num
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  · rintro ⟨hv, hveq⟩
    refine ⟨hv, ?_⟩
    rw [alternatingFormEquiv_apply, hveq, real_inner_self_eq_norm_sq, hη, one_pow]

/-- The calibrated frames of the negated form `-alternatingFormEquiv E k η` of a unit `k`-vector
`η` are precisely the orthonormal frames whose exterior product equals `-η`. -/
theorem isCalibratedFrame_neg_alternatingFormEquiv_iff {η : ⋀[ℝ]^k E} (hη : ‖η‖ = 1)
    (v : Fin k → E) :
    IsCalibratedFrame (-alternatingFormEquiv E k η) v ↔
      Orthonormal ℝ v ∧ exteriorPower.ιMulti ℝ k v = -η := by
  rw [← map_neg]
  exact isCalibratedFrame_alternatingFormEquiv_iff (by rwa [norm_neg]) v

/-- **Calibrated frames of a unit decomposable form**: for an orthonormal frame `e`, the form
`e₁* ∧ ⋯ ∧ eₖ*` calibrates precisely the orthonormal frames with the same exterior product as `e`
(the positively oriented orthonormal frames of the supporting `k`-plane). -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff {e : Fin k → E} (he : Orthonormal ℝ e)
    (v : Fin k → E) :
    IsCalibratedFrame (alternatingFormEquiv E k (exteriorPower.ιMulti ℝ k e)) v ↔
      Orthonormal ℝ v ∧ exteriorPower.ιMulti ℝ k v = exteriorPower.ιMulti ℝ k e :=
  isCalibratedFrame_alternatingFormEquiv_iff he.norm_ιMulti v

/-- The negated unit decomposable form `-(e₁* ∧ ⋯ ∧ eₖ*)` calibrates precisely the oppositely
oriented orthonormal frames of the supporting `k`-plane. -/
theorem isCalibratedFrame_neg_alternatingFormEquiv_ιMulti_iff {e : Fin k → E}
    (he : Orthonormal ℝ e) (v : Fin k → E) :
    IsCalibratedFrame (-alternatingFormEquiv E k (exteriorPower.ιMulti ℝ k e)) v ↔
      Orthonormal ℝ v ∧ exteriorPower.ιMulti ℝ k v = -exteriorPower.ιMulti ℝ k e :=
  isCalibratedFrame_neg_alternatingFormEquiv_iff he.norm_ιMulti v

end FiniteDimensional

end TauCeti
