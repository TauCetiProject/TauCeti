/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Unilateral shifts on `ℓᵖ`

For `1 ≤ p ≤ ∞` and a normed space `E`, the **unilateral right shift** on `ℓ^p(ℕ, E)` inserts `0`
in coordinate `0` and advances each entry by one index, `(x₀, x₁, …) ↦ (0, x₀, x₁, …)`. The
**unilateral left shift** drops coordinate `0`, `(x₀, x₁, x₂, …) ↦ (x₁, x₂, …)`.

The right shift is a linear isometry (`lp.rightShiftₗᵢ`, bundled as `lp.rightShift`), while the
left shift (`lp.leftShift`) is a contraction satisfying `leftShift ∘ rightShift = id` and
`id - rightShift ∘ leftShift = single 0 ∘ eval 0`. Consequently:

* `rightShift` is a closed isometric embedding with trivial kernel and range `{f | f 0 = 0}`, so
  its cokernel is linearly isomorphic to `E` (`lp.cokerRightShiftEquiv`, and
  `lp.cokerRightShiftPowEquiv` identifying the cokernel of `rightShift ^ m` with `Fin m → E`);
* `leftShift` is a quotient map with complemented kernel `{single 0 x | x ∈ E}`, linearly
  isomorphic to `E` (`lp.kerLeftShiftEquiv`, and `lp.kerLeftShiftPowEquiv` identifying the kernel
  of `leftShift ^ m` with `Fin m → E`);
* on `ℓ²(ℕ, E)` for a Hilbert space `E`, `rightShift` and `leftShift` are Hilbert-space adjoints
  (`lp.adjoint_rightShift`, `lp.adjoint_leftShift`, `lp.star_rightShift`, `lp.star_leftShift`).

Fredholmness and index formulas for the unilateral shifts and their powers live in
`TauCeti.Analysis.Fredholm.Shift`.

## Main declarations

* `lp.rightShiftₗᵢ`, `lp.rightShift`: the unilateral right shift on `ℓ^p(ℕ, E)` as a linear
  isometry and as a continuous linear map.
* `lp.leftShift`: the unilateral left shift on `ℓ^p(ℕ, E)`.
* `lp.kerLeftShiftEquiv`, `lp.cokerRightShiftEquiv`, `lp.kerLeftShiftPowEquiv`,
  `lp.cokerRightShiftPowEquiv`: linear equivalences identifying `ker (leftShift ^ m)` and
  `coker (rightShift ^ m)` with `E` (for `m = 1`) and `Fin m → E`.
* `lp.isClosedEmbedding_rightShift`, `lp.isQuotientMap_leftShift`: topological embedding and
  quotient properties of the shifts and their powers.
* `lp.adjoint_rightShift`, `lp.adjoint_leftShift`: adjointness of the unilateral shifts on
  `ℓ²(ℕ, E)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, Chapter II, §2,
  Examples 2.10–2.11.
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter III, §7, Example 7.5.
-/

public section

open Topology
open scoped ENNReal InnerProductSpace lp

namespace lp

section BoundedSMul

variable (𝕜 E : Type*) {p : ℝ≥0∞} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E]

private def rightShiftSeq (f : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => f n

private theorem rightShiftSeq_eq_indicator (f : ℕ → E) :
    rightShiftSeq E f = {j : ℕ | 1 ≤ j}.indicator (f ∘ fun j ↦ j - 1) := by
  ext (_ | n)
  · simp [rightShiftSeq]
  · simp [rightShiftSeq]

private theorem memℓp_rightShiftSeq {f : ℕ → E} (hf : Memℓp f p) :
    Memℓp (rightShiftSeq E f) p := by
  rw [rightShiftSeq_eq_indicator]
  exact hf.indicator_comp fun _ ha _ hb hab ↦ tsub_inj_left ha hb hab

variable (p) [Fact (1 ≤ p)]

/-- The **unilateral right shift** on `ℓ^p(ℕ, E)`, sending `(x₀, x₁, …)` to `(0, x₀, x₁, …)`,
bundled as a linear isometry. -/
noncomputable def rightShiftₗᵢ : ℓ^p(ℕ, E) →ₗᵢ[𝕜] ℓ^p(ℕ, E) where
  toFun f := ⟨rightShiftSeq E f, memℓp_rightShiftSeq E (lp.memℓp f)⟩
  map_add' _ _ := by
    ext (_ | _)
    · exact (add_zero 0).symm
    · rfl
  map_smul' _ _ := by
    ext (_ | _)
    · exact (smul_zero _).symm
    · rfl
  norm_map' f := by
    let g : ℓ^p(ℕ, E) := ⟨rightShiftSeq E f, memℓp_rightShiftSeq E (lp.memℓp f)⟩
    apply le_antisymm
    · exact lp.norm_le_of_forall_eq_indicator_comp
        (g := fun j ↦ j - 1) (s := {j : ℕ | 1 ≤ j})
        (fun _ ha _ hb hab ↦ tsub_inj_left ha hb hab)
        fun j ↦ congrFun (rightShiftSeq_eq_indicator E f) j
    · exact lp.norm_le_of_forall_eq_nat_add (f' := f) (f := g) 1 fun _ ↦ rfl

/-- The **unilateral right shift** on `ℓ^p(ℕ, E)`, sending `(x₀, x₁, …)` to `(0, x₀, x₁, …)`, as a
continuous linear map. -/
noncomputable def rightShift : ℓ^p(ℕ, E) →L[𝕜] ℓ^p(ℕ, E) :=
  (rightShiftₗᵢ 𝕜 E p).toContinuousLinearMap

/-- The **unilateral left shift** on `ℓ^p(ℕ, E)`, sending `(x₀, x₁, x₂, …)` to `(x₁, x₂, …)`, as a
continuous linear map. -/
noncomputable def leftShift : ℓ^p(ℕ, E) →L[𝕜] ℓ^p(ℕ, E) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ⟨fun n ↦ f (n + 1), (TauCeti.memℓp_nat_add_iff 1).2 (lp.memℓp f)⟩
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
    1 fun f ↦ by
      rw [one_mul]
      exact lp.norm_le_of_forall_eq_nat_add 1 fun _ ↦ rfl

@[simp]
theorem toContinuousLinearMap_rightShiftₗᵢ :
    (rightShiftₗᵢ 𝕜 E p).toContinuousLinearMap = rightShift 𝕜 E p := (rfl)

@[simp]
theorem toLinearMap_rightShiftₗᵢ :
    (rightShiftₗᵢ 𝕜 E p).toLinearMap = (rightShift 𝕜 E p).toLinearMap := by
  rw [← toContinuousLinearMap_rightShiftₗᵢ, LinearIsometry.toLinearMap_toContinuousLinearMap]

@[simp]
theorem coe_rightShiftₗᵢ :
    ⇑(rightShiftₗᵢ 𝕜 E p) = rightShift 𝕜 E p := by
  rw [← toContinuousLinearMap_rightShiftₗᵢ, LinearIsometry.coe_toContinuousLinearMap]

theorem rightShiftₗᵢ_apply (f : ℓ^p(ℕ, E)) :
    rightShiftₗᵢ 𝕜 E p f = rightShift 𝕜 E p f :=
  congrFun (coe_rightShiftₗᵢ 𝕜 E p) f

@[simp]
theorem rightShift_apply_zero (f : ℓ^p(ℕ, E)) : rightShift 𝕜 E p f 0 = 0 := by
  simp [rightShift, rightShiftₗᵢ, rightShiftSeq]

@[simp]
theorem rightShift_apply_succ (f : ℓ^p(ℕ, E)) (n : ℕ) :
    rightShift 𝕜 E p f (n + 1) = f n := by
  simp [rightShift, rightShiftₗᵢ, rightShiftSeq]

@[simp]
theorem leftShift_apply (f : ℓ^p(ℕ, E)) (n : ℕ) :
    leftShift 𝕜 E p f n = f (n + 1) := by
  simp [leftShift]

@[simp]
theorem norm_rightShift_apply (f : ℓ^p(ℕ, E)) : ‖rightShift 𝕜 E p f‖ = ‖f‖ := by
  rw [← rightShiftₗᵢ_apply, (rightShiftₗᵢ 𝕜 E p).norm_map]

/-- The unilateral right shift on `ℓ^p(ℕ, E)` is an isometry. -/
theorem isometry_rightShift : Isometry (rightShift 𝕜 E p) := by
  rw [← coe_rightShiftₗᵢ]
  exact (rightShiftₗᵢ 𝕜 E p).isometry

/-- The unilateral left shift on `ℓ^p(ℕ, E)` is a contraction. -/
theorem norm_leftShift_apply_le (f : ℓ^p(ℕ, E)) : ‖leftShift 𝕜 E p f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_eq_nat_add 1 fun j ↦ leftShift_apply 𝕜 E p f j

@[simp]
theorem rightShift_single (n : ℕ) (x : E) :
    rightShift 𝕜 E p (lp.single p n x) = lp.single p (n + 1) x := by
  ext (_ | m)
  · simp [lp.single_apply]
  · simp [lp.single_apply, Pi.single_apply]

@[simp]
theorem leftShift_single_zero (x : E) :
    leftShift 𝕜 E p (lp.single p 0 x) = 0 := by
  ext n
  simp [lp.single_apply]

@[simp]
theorem leftShift_single_succ (n : ℕ) (x : E) :
    leftShift 𝕜 E p (lp.single p (n + 1) x) = lp.single p n x := by
  ext m
  simp [lp.single_apply, Pi.single_apply]

@[simp]
theorem leftShift_rightShift (f : ℓ^p(ℕ, E)) :
    leftShift 𝕜 E p (rightShift 𝕜 E p f) = f := by
  ext n
  simp

/-- The unilateral left shift is a left inverse to the unilateral right shift. -/
@[simp]
theorem leftShift_comp_rightShift :
    (leftShift 𝕜 E p).comp (rightShift 𝕜 E p) = ContinuousLinearMap.id 𝕜 ℓ^p(ℕ, E) := by
  ext f n
  simp

/-- Endomorphism-ring form of `lp.leftShift_comp_rightShift`. -/
@[simp]
theorem leftShift_mul_rightShift :
    leftShift 𝕜 E p * rightShift 𝕜 E p = 1 := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, leftShift_comp_rightShift]

/-- For every `m : ℕ`, `leftShift ^ m` is a left inverse to `rightShift ^ m` in the endomorphism
ring. -/
@[simp]
theorem leftShift_pow_mul_rightShift_pow (m : ℕ) :
    leftShift 𝕜 E p ^ m * rightShift 𝕜 E p ^ m = 1 :=
  pow_mul_pow_eq_one m (leftShift_mul_rightShift 𝕜 E p)

/-- Operator-composition form of `lp.leftShift_pow_mul_rightShift_pow`. -/
@[simp]
theorem leftShift_pow_comp_rightShift_pow (m : ℕ) :
    (leftShift 𝕜 E p ^ m).comp (rightShift 𝕜 E p ^ m) = ContinuousLinearMap.id 𝕜 ℓ^p(ℕ, E) := by
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.one_def,
    leftShift_pow_mul_rightShift_pow]

/-- Pointwise left-inverse identity `leftShift (rightShift f) = f`. -/
theorem leftInverse_leftShift_rightShift :
    Function.LeftInverse (leftShift 𝕜 E p) (rightShift 𝕜 E p) :=
  leftShift_rightShift 𝕜 E p

/-- Pointwise left-inverse identity `(leftShift ^ m) ((rightShift ^ m) f) = f`. -/
theorem leftInverse_leftShift_pow_rightShift_pow (m : ℕ) :
    Function.LeftInverse ⇑(leftShift 𝕜 E p ^ m) ⇑(rightShift 𝕜 E p ^ m) := fun f ↦ by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congr($(leftShift_pow_comp_rightShift_pow 𝕜 E p m) f)

/-- Applying `leftShift` followed by `rightShift` zeroes out the `0`-th coordinate. -/
theorem rightShift_leftShift (f : ℓ^p(ℕ, E)) :
    rightShift 𝕜 E p (leftShift 𝕜 E p f) = f - lp.single p 0 (f 0) := by
  ext (_ | n)
  · simp [lp.single_apply]
  · simp [lp.single_apply]

/-- The `m`-th power of `leftShift` advances coordinates by `m`. -/
@[simp]
theorem leftShift_pow_apply (m : ℕ) (f : ℓ^p(ℕ, E)) (n : ℕ) :
    (leftShift 𝕜 E p ^ m) f n = f (n + m) := by
  induction m generalizing n with
  | zero => rw [pow_zero, one_apply_eq_self, Nat.add_zero]
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp, leftShift_apply, ih, Nat.add_right_comm, Nat.add_assoc]

/-- The `m`-th power of `rightShift` vanishes in coordinates `< m`. -/
theorem rightShift_pow_apply_of_lt {m k : ℕ} (hk : k < m) (f : ℓ^p(ℕ, E)) :
    (rightShift 𝕜 E p ^ m) f k = 0 := by
  induction m generalizing k with
  | zero => exact (Nat.not_lt_zero k hk).elim
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp]
    cases k with
    | zero => exact rightShift_apply_zero 𝕜 E p _
    | succ k =>
      rw [rightShift_apply_succ]
      exact ih (Nat.lt_of_succ_lt_succ hk)

/-- The `m`-th power of `rightShift` shifts coordinate `n` to `n + m`. -/
@[simp]
theorem rightShift_pow_apply_add (m n : ℕ) (f : ℓ^p(ℕ, E)) :
    (rightShift 𝕜 E p ^ m) f (n + m) = f n := by
  induction m with
  | zero => rw [pow_zero, one_apply_eq_self, Nat.add_zero]
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp, ← Nat.add_assoc, rightShift_apply_succ, ih]

/-- Applying `leftShift ^ m` followed by `rightShift ^ m` zeroes out the first `m` coordinates. -/
theorem rightShift_pow_leftShift_pow (m : ℕ) (f : ℓ^p(ℕ, E)) :
    (rightShift 𝕜 E p ^ m) ((leftShift 𝕜 E p ^ m) f) =
      f - ∑ i : Fin m, lp.single p (i : ℕ) (f i) := by
  ext k
  rw [lp.coeFn_sub, Pi.sub_apply]
  by_cases hk : k < m
  · rw [rightShift_pow_apply_of_lt 𝕜 E p hk,
      lp.sum_single_apply_of_injOn_of_mem (E := fun _ : ℕ ↦ E) (j := ⟨k, hk⟩)
        Fin.val_injective.injOn (Finset.mem_univ _),
      sub_self]
  · have hkm : m ≤ k := Nat.le_of_not_lt hk
    rw [lp.sum_single_apply_eq_zero_of_forall_ne (E := fun _ : ℕ ↦ E)
        (fun (i : Fin m) _ ↦ (i.isLt.trans_le hkm).ne'),
      sub_zero, ← Nat.sub_add_cancel hkm, rightShift_pow_apply_add, leftShift_pow_apply]

/-- The defect `id - rightShift ∘ leftShift` is the coordinate projection onto coordinate `0`. -/
theorem id_sub_rightShift_comp_leftShift :
    ContinuousLinearMap.id 𝕜 ℓ^p(ℕ, E) - (rightShift 𝕜 E p).comp (leftShift 𝕜 E p) =
      (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p 0).comp
        (evalCLM 𝕜 (fun _ : ℕ ↦ E) p 0) := by
  ext f n
  simp [rightShift_leftShift, sub_sub_cancel]

/-- Endomorphism-ring form of `lp.id_sub_rightShift_comp_leftShift`. -/
theorem one_sub_rightShift_mul_leftShift :
    1 - rightShift 𝕜 E p * leftShift 𝕜 E p =
      (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p 0).comp
        (evalCLM 𝕜 (fun _ : ℕ ↦ E) p 0) := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.mul_def, id_sub_rightShift_comp_leftShift]

@[simp]
theorem evalCLM_zero_comp_rightShift :
    (evalCLM 𝕜 (fun _ : ℕ ↦ E) p 0).comp (rightShift 𝕜 E p) = 0 := by
  ext f
  simp

@[simp]
theorem evalCLM_succ_comp_rightShift (n : ℕ) :
    (evalCLM 𝕜 (fun _ : ℕ ↦ E) p (n + 1)).comp (rightShift 𝕜 E p) =
      evalCLM 𝕜 (fun _ : ℕ ↦ E) p n := by
  ext f
  simp

@[simp]
theorem evalCLM_comp_leftShift (n : ℕ) :
    (evalCLM 𝕜 (fun _ : ℕ ↦ E) p n).comp (leftShift 𝕜 E p) =
      evalCLM 𝕜 (fun _ : ℕ ↦ E) p (n + 1) := by
  ext f
  simp

@[simp]
theorem rightShift_comp_singleContinuousLinearMap (n : ℕ) :
    (rightShift 𝕜 E p).comp (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p n) =
      singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p (n + 1) := by
  ext x m
  simp

@[simp]
theorem leftShift_comp_singleContinuousLinearMap_zero :
    (leftShift 𝕜 E p).comp (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p 0) = 0 := by
  ext x n
  simp

@[simp]
theorem leftShift_comp_singleContinuousLinearMap_succ (n : ℕ) :
    (leftShift 𝕜 E p).comp (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p (n + 1)) =
      singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p n := by
  ext x m
  simp

/-- The unilateral right shift on `ℓ^p(ℕ, E)` is injective. -/
theorem rightShift_injective : Function.Injective (rightShift 𝕜 E p) :=
  (leftInverse_leftShift_rightShift 𝕜 E p).injective

/-- Every natural-number power of `rightShift` on `ℓ^p(ℕ, E)` is injective. -/
theorem rightShift_pow_injective (m : ℕ) : Function.Injective ⇑(rightShift 𝕜 E p ^ m) :=
  (leftInverse_leftShift_pow_rightShift_pow 𝕜 E p m).injective

/-- The unilateral left shift on `ℓ^p(ℕ, E)` is surjective. -/
theorem leftShift_surjective : Function.Surjective (leftShift 𝕜 E p) :=
  (leftInverse_leftShift_rightShift 𝕜 E p).surjective

/-- Every natural-number power of `leftShift` on `ℓ^p(ℕ, E)` is surjective. -/
theorem leftShift_pow_surjective (m : ℕ) : Function.Surjective ⇑(leftShift 𝕜 E p ^ m) :=
  (leftInverse_leftShift_pow_rightShift_pow 𝕜 E p m).surjective

@[simp]
theorem ker_rightShift :
    LinearMap.ker (rightShift 𝕜 E p).toLinearMap = ⊥ :=
  LinearMap.ker_eq_bot.2 (rightShift_injective 𝕜 E p)

@[simp]
theorem range_leftShift :
    LinearMap.range (leftShift 𝕜 E p).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.2 (leftShift_surjective 𝕜 E p)

/-- The range of the unilateral right shift consists of those sequences vanishing at `0`. -/
theorem range_rightShift :
    LinearMap.range (rightShift 𝕜 E p).toLinearMap =
      LinearMap.ker (evalCLM 𝕜 (fun _ : ℕ ↦ E) p 0).toLinearMap := by
  ext g
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, LinearMap.mem_ker, evalCLM_apply]
  refine ⟨?_, fun hg ↦ ⟨leftShift 𝕜 E p g, ?_⟩⟩
  · rintro ⟨f, rfl⟩
    exact rightShift_apply_zero 𝕜 E p f
  · simp [rightShift_leftShift, hg]

private theorem eq_single_zero_of_leftShift_eq_zero {f : ℓ^p(ℕ, E)}
    (hf : leftShift 𝕜 E p f = 0) : f = lp.single p 0 (f 0) := by
  have h := rightShift_leftShift 𝕜 E p f
  rw [hf, map_zero, eq_comm, sub_eq_zero] at h
  exact h

/-- The kernel of the unilateral left shift is the image of the `0`-th coordinate inclusion. -/
theorem ker_leftShift :
    LinearMap.ker (leftShift 𝕜 E p).toLinearMap =
      LinearMap.range (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ E) p 0).toLinearMap := by
  ext f
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, LinearMap.mem_range,
    singleContinuousLinearMap_apply]
  refine ⟨fun hf ↦ ⟨f 0, (eq_single_zero_of_leftShift_eq_zero 𝕜 E p hf).symm⟩, ?_⟩
  rintro ⟨x, rfl⟩
  exact leftShift_single_zero 𝕜 E p x

/-- The kernel of `leftShift` is linearly isomorphic to the fiber `E` via evaluation at `0`. -/
noncomputable def kerLeftShiftEquiv :
    LinearMap.ker (leftShift 𝕜 E p).toLinearMap ≃ₗ[𝕜] E :=
  (LinearEquiv.ofEq _ _ (ker_leftShift 𝕜 E p)).trans
    (LinearEquiv.ofLeftInverse
      (g := evalCLM 𝕜 (fun _ : ℕ ↦ E) p 0)
      (by
        rw [ContinuousLinearMap.coe_coe]
        exact leftInverse_evalCLM_singleContinuousLinearMap 0)).symm

@[simp]
theorem kerLeftShiftEquiv_apply (f : LinearMap.ker (leftShift 𝕜 E p).toLinearMap) :
    kerLeftShiftEquiv 𝕜 E p f = (f : ℓ^p(ℕ, E)) 0 := by
  simp [kerLeftShiftEquiv]

@[simp]
theorem coe_kerLeftShiftEquiv_symm_apply (x : E) :
    ((kerLeftShiftEquiv 𝕜 E p).symm x : ℓ^p(ℕ, E)) = lp.single p 0 x := by
  simp [kerLeftShiftEquiv]

/-- The cokernel of `rightShift` is linearly isomorphic to `E` via evaluation at `0`. -/
noncomputable def cokerRightShiftEquiv :
    (ℓ^p(ℕ, E) ⧸ LinearMap.range (rightShift 𝕜 E p).toLinearMap) ≃ₗ[𝕜] E :=
  (Submodule.quotEquivOfEq _ _ (range_rightShift 𝕜 E p)).trans <|
    (evalCLM 𝕜 (fun _ : ℕ ↦ E) p 0).toLinearMap.quotKerEquivOfSurjective
      (by
        rw [ContinuousLinearMap.coe_coe]
        exact evalCLM_surjective 0)

@[simp]
theorem cokerRightShiftEquiv_mk (f : ℓ^p(ℕ, E)) :
    cokerRightShiftEquiv 𝕜 E p (Submodule.Quotient.mk f) = f 0 := by
  simp [cokerRightShiftEquiv]

@[simp]
theorem cokerRightShiftEquiv_symm_apply (x : E) :
    (cokerRightShiftEquiv 𝕜 E p).symm x = Submodule.Quotient.mk (lp.single p 0 x) := by
  apply (cokerRightShiftEquiv 𝕜 E p).injective
  simp

/-- The range of `rightShift ^ m` consists of those sequences vanishing in the first `m`
coordinates. -/
theorem range_rightShift_pow (m : ℕ) :
    LinearMap.range (rightShift 𝕜 E p ^ m).toLinearMap =
      LinearMap.ker (LinearMap.pi fun i : Fin m ↦ (evalCLM 𝕜 (fun _ : ℕ ↦ E) p i).toLinearMap) := by
  ext g
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, LinearMap.mem_ker, funext_iff,
    LinearMap.pi_apply, evalCLM_apply, Pi.zero_apply]
  refine ⟨?_, fun hg ↦ ⟨(leftShift 𝕜 E p ^ m) g, ?_⟩⟩
  · rintro ⟨f, rfl⟩ i
    exact rightShift_pow_apply_of_lt 𝕜 E p i.isLt f
  · rw [rightShift_pow_leftShift_pow,
      Finset.sum_eq_zero fun i _ ↦ by rw [hg i, lp.single_zero], sub_zero]

/-- The kernel of `leftShift ^ m` is linearly isomorphic to `Fin m → E` via evaluation at the first
`m` coordinates. -/
noncomputable def kerLeftShiftPowEquiv (m : ℕ) :
    LinearMap.ker (leftShift 𝕜 E p ^ m).toLinearMap ≃ₗ[𝕜] (Fin m → E) where
  toFun f i := (f : ℓ^p(ℕ, E)) i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun v := ⟨∑ i : Fin m, lp.single p (i : ℕ) (v i), by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    ext n
    rw [leftShift_pow_apply, lp.coeFn_zero, Pi.zero_apply]
    exact lp.sum_single_apply_eq_zero_of_forall_ne
      fun i _ ↦ (i.isLt.trans_le (Nat.le_add_left m n)).ne'⟩
  left_inv f := by
    ext k
    have hf : (leftShift 𝕜 E p ^ m) f = 0 := by
      simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] using f.property
    have h := rightShift_pow_leftShift_pow 𝕜 E p m f
    rw [hf, map_zero, eq_comm, sub_eq_zero] at h
    exact congr($h.symm k)
  right_inv v := by
    ext j
    exact lp.sum_single_apply_of_injOn_of_mem Fin.val_injective.injOn (Finset.mem_univ j)

@[simp]
theorem kerLeftShiftPowEquiv_apply (m : ℕ)
    (f : LinearMap.ker (leftShift 𝕜 E p ^ m).toLinearMap) (i : Fin m) :
    kerLeftShiftPowEquiv 𝕜 E p m f i = (f : ℓ^p(ℕ, E)) i := by
  simp [kerLeftShiftPowEquiv]

@[simp]
theorem coe_kerLeftShiftPowEquiv_symm_apply (m : ℕ) (v : Fin m → E) :
    ((kerLeftShiftPowEquiv 𝕜 E p m).symm v : ℓ^p(ℕ, E)) =
      ∑ i : Fin m, lp.single p (i : ℕ) (v i) := by
  simp [kerLeftShiftPowEquiv]

/-- The cokernel of `rightShift ^ m` is linearly isomorphic to `Fin m → E` via evaluation at the
first `m` coordinates. -/
noncomputable def cokerRightShiftPowEquiv (m : ℕ) :
    (ℓ^p(ℕ, E) ⧸ LinearMap.range (rightShift 𝕜 E p ^ m).toLinearMap) ≃ₗ[𝕜] (Fin m → E) :=
  (Submodule.quotEquivOfEq _ _ (range_rightShift_pow 𝕜 E p m)).trans <|
    (LinearMap.pi fun i : Fin m ↦
      (evalCLM 𝕜 (fun _ : ℕ ↦ E) p i).toLinearMap).quotKerEquivOfSurjective
      (Function.HasRightInverse.surjective ⟨fun v ↦ ∑ i : Fin m, lp.single p (i : ℕ) (v i),
        fun v ↦ by
          ext j
          rw [LinearMap.pi_apply, ContinuousLinearMap.coe_coe, evalCLM_apply]
          exact lp.sum_single_apply_of_injOn_of_mem Fin.val_injective.injOn (Finset.mem_univ j)⟩)

@[simp]
theorem cokerRightShiftPowEquiv_mk (m : ℕ) (f : ℓ^p(ℕ, E)) (i : Fin m) :
    cokerRightShiftPowEquiv 𝕜 E p m (Submodule.Quotient.mk f) i = f i := by
  simp [cokerRightShiftPowEquiv]

@[simp]
theorem cokerRightShiftPowEquiv_symm_apply (m : ℕ) (v : Fin m → E) :
    (cokerRightShiftPowEquiv 𝕜 E p m).symm v =
      Submodule.Quotient.mk (∑ i : Fin m, lp.single p (i : ℕ) (v i)) := by
  apply (cokerRightShiftPowEquiv 𝕜 E p m).injective
  ext j
  rw [LinearEquiv.apply_symm_apply, cokerRightShiftPowEquiv_mk]
  symm
  exact lp.sum_single_apply_of_injOn_of_mem Fin.val_injective.injOn (Finset.mem_univ j)

/-- The unilateral right shift on `ℓ^p(ℕ, E)` is a closed topological embedding. -/
theorem isClosedEmbedding_rightShift : IsClosedEmbedding (rightShift 𝕜 E p) :=
  (leftInverse_leftShift_rightShift 𝕜 E p).isClosedEmbedding
    (leftShift 𝕜 E p).continuous (rightShift 𝕜 E p).continuous

/-- Every natural-number power of the unilateral right shift on `ℓ^p(ℕ, E)` is a closed topological
embedding. -/
theorem isClosedEmbedding_rightShift_pow (m : ℕ) : IsClosedEmbedding ⇑(rightShift 𝕜 E p ^ m) :=
  (leftInverse_leftShift_pow_rightShift_pow 𝕜 E p m).isClosedEmbedding
    (leftShift 𝕜 E p ^ m).continuous (rightShift 𝕜 E p ^ m).continuous

/-- The unilateral left shift on `ℓ^p(ℕ, E)` is a quotient map. -/
theorem isQuotientMap_leftShift : IsQuotientMap (leftShift 𝕜 E p) :=
  IsQuotientMap.of_inverse (rightShift 𝕜 E p).continuous (leftShift 𝕜 E p).continuous
    (leftInverse_leftShift_rightShift 𝕜 E p)

/-- Every natural-number power of the unilateral left shift on `ℓ^p(ℕ, E)` is a quotient map. -/
theorem isQuotientMap_leftShift_pow (m : ℕ) : IsQuotientMap ⇑(leftShift 𝕜 E p ^ m) :=
  IsQuotientMap.of_inverse (rightShift 𝕜 E p ^ m).continuous (leftShift 𝕜 E p ^ m).continuous
    (leftInverse_leftShift_pow_rightShift_pow 𝕜 E p m)

end BoundedSMul

section OpNorm

variable (𝕜 E : Type*) (p : ℝ≥0∞) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [Fact (1 ≤ p)]

/-- The operator norm of `leftShift` on `ℓ^p(ℕ, E)` is at most `1`. -/
theorem norm_leftShift_le : ‖leftShift 𝕜 E p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa only [one_mul] using norm_leftShift_apply_le 𝕜 E p f

/-- For nontrivial `E`, the unilateral right shift on `ℓ^p(ℕ, E)` has operator norm `1`. -/
@[simp]
theorem norm_rightShift [Nontrivial E] : ‖rightShift 𝕜 E p‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have : Nontrivial ℓ^p(ℕ, E) := ⟨⟨lp.single p 0 x, 0, fun h ↦ hx (by simpa using congr($h 0))⟩⟩
  rw [← toContinuousLinearMap_rightShiftₗᵢ]
  exact (rightShiftₗᵢ 𝕜 E p).norm_toContinuousLinearMap

/-- For nontrivial `E`, the unilateral left shift on `ℓ^p(ℕ, E)` has operator norm `1`. -/
@[simp]
theorem norm_leftShift [Nontrivial E] : ‖leftShift 𝕜 E p‖ = 1 := by
  have hp : 0 < p := zero_lt_one.trans_le Fact.out
  apply le_antisymm (norm_leftShift_le 𝕜 E p)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hle := (leftShift 𝕜 E p).le_opNorm (lp.single p 1 x)
  rw [leftShift_single_succ, lp.norm_single hp, lp.norm_single hp] at hle
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.2 hx)).1 (by simpa only [one_mul] using hle)

end OpNorm

section Adjoint

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- On `ℓ²(ℕ, E)`, `rightShift` and `leftShift` are formal adjoints with respect to the inner
product. -/
theorem inner_rightShift_left (f g : ℓ²(ℕ, E)) :
    ⟪rightShift 𝕜 E 2 f, g⟫_𝕜 = ⟪f, leftShift 𝕜 E 2 g⟫_𝕜 := by
  have h₁ := (hasSum_nat_add_iff' 1).2 (lp.hasSum_inner (𝕜 := 𝕜) (rightShift 𝕜 E 2 f) g)
  simp only [Finset.sum_range_one, rightShift_apply_zero, inner_zero_left, sub_zero,
    rightShift_apply_succ] at h₁
  exact h₁.unique
    (by simpa only [leftShift_apply] using lp.hasSum_inner (𝕜 := 𝕜) f (leftShift 𝕜 E 2 g))

/-- On `ℓ²(ℕ, E)`, `leftShift` and `rightShift` are formal adjoints with respect to the inner
product. -/
theorem inner_leftShift_left (f g : ℓ²(ℕ, E)) :
    ⟪leftShift 𝕜 E 2 f, g⟫_𝕜 = ⟪f, rightShift 𝕜 E 2 g⟫_𝕜 := by
  rw [← inner_conj_symm, ← inner_rightShift_left, inner_conj_symm]

/-- On `ℓ²(ℕ, E)` for a Hilbert space `E`, the Hilbert-space adjoint of `rightShift` is
`leftShift`. -/
@[simp]
theorem adjoint_rightShift [CompleteSpace E] :
    ContinuousLinearMap.adjoint (rightShift 𝕜 E 2) = leftShift 𝕜 E 2 := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  exact inner_leftShift_left 𝕜 E f g

/-- On `ℓ²(ℕ, E)` for a Hilbert space `E`, the Hilbert-space adjoint of `leftShift` is
`rightShift`. -/
@[simp]
theorem adjoint_leftShift [CompleteSpace E] :
    ContinuousLinearMap.adjoint (leftShift 𝕜 E 2) = rightShift 𝕜 E 2 := by
  rw [← adjoint_rightShift, ContinuousLinearMap.adjoint_adjoint]

/-- C*-algebra star form of `lp.adjoint_rightShift`. -/
@[simp]
theorem star_rightShift [CompleteSpace E] :
    star (rightShift 𝕜 E 2) = leftShift 𝕜 E 2 := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rightShift]

/-- C*-algebra star form of `lp.adjoint_leftShift`. -/
@[simp]
theorem star_leftShift [CompleteSpace E] :
    star (leftShift 𝕜 E 2) = rightShift 𝕜 E 2 := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_leftShift]

end Adjoint

end lp
