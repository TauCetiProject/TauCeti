/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The Hermitian form of a Riemann form; scaling and pullback

Let `V` be an integral module (for a complex torus `V_ℝ / Λ`, the period lattice `Λ`), `J` an
almost complex structure on its realification `V_ℝ = ℝ ⊗[ℤ] V`, and `E` an integral bilinear form
on `V` with real extension `E_ℝ`. The **Hermitian form** of `E` is

`H (v, w) = E_ℝ (J v) w + i E_ℝ v w`,

complex linear in the first variable for the complex structure `J.complexModule` in which `i`
acts by `J`. Its imaginary part is `E_ℝ`. When `E` is a Riemann form
(`TauCeti.AlmostComplexStructure.IsRiemannForm`), `H` is conjugate symmetric and positive
definite, `H (v, v) = E_ℝ (J v) v > 0` for `v ≠ 0`. This is the translation between Riemann forms
and positive definite Hermitian forms whose imaginary part is integral on the lattice
(Birkenhake–Lange, *Complex Abelian Varieties*, Lemma 2.1.7 and §4.1; Stanford VIGRE notes,
*Complex theory of abelian varieties*, Definitions 1.13–1.14).

The file also records the operations on Riemann forms of the roadmap: a positive integer multiple
of a Riemann form is a Riemann form, and a Riemann form pulls back to a Riemann form along an
injective integral map whose real extension is complex linear. Negating both the form and the
complex structure also gives a Riemann form; this is the sign change behind the homological Hodge
structure of a complex torus.

The convention `H (v, w) = E_ℝ (J v) w + i E_ℝ v w`, linear in the first variable, follows
Birkenhake–Lange. On `ℤ + iℤ ⊂ ℂ` with `H (v, w) = v * conj w` it gives `E (i, 1) = 1`.

## Main declarations

* `TauCeti.AlmostComplexStructure.RiemannForm.hermitian`: the form `H` of `(J, E)`.
* `TauCeti.AlmostComplexStructure.RiemannForm.re_hermitian`,
  `TauCeti.AlmostComplexStructure.RiemannForm.im_hermitian`: `Re H = E_ℝ (J ·) ·` and
  `Im H = E_ℝ`.
* `TauCeti.AlmostComplexStructure.RiemannForm.hermitian_smul_left`: `H` is complex linear in the
  first variable for `J.complexModule`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.conj_hermitian`: for a Riemann form, `H` is
  conjugate symmetric.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.hermitian_self_pos`: for a Riemann form,
  `0 < H (v, v)` for `v ≠ 0`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.neg`: `-E` is a Riemann form for `-J`, while
  `TauCeti.AlmostComplexStructure.IsRiemannForm.not_isRiemannForm_neg`: on a nonzero lattice `-E`
  is not a Riemann form for `J`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.scale`: a positive integer multiple of a Riemann
  form is a Riemann form.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.pullback`: the pullback of a Riemann form along an
  injective map with complex linear real extension is a Riemann form.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct ComplexOrder ComplexConjugate

universe u u'

variable {V : Type u} [AddCommGroup V]

/-- Base change of integral bilinear forms to `ℝ` commutes with integer multiples. -/
private theorem baseChange_zsmul_apply (n : ℤ) (E : LinearMap.BilinForm ℤ V)
    (x y : Hodge.Realification V) : (n • E).baseChange ℝ x y = n * E.baseChange ℝ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y => simp [mul_assoc]
    | add y z hy hz => simp only [map_add, hy, hz, mul_add]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]

/-- Base change of integral bilinear forms to `ℝ` commutes with negation. -/
private theorem baseChange_neg_apply (E : LinearMap.BilinForm ℤ V) (x y : Hodge.Realification V) :
    (-E).baseChange ℝ x y = -E.baseChange ℝ x y := by
  simpa using baseChange_zsmul_apply (-1) E x y

/-- The real extension of an alternating integral form is skew-symmetric. -/
private theorem baseChange_apply_swap {E : LinearMap.BilinForm ℤ V} (hE : E.IsAlt)
    (x y : Hodge.Realification V) : E.baseChange ℝ y x = -E.baseChange ℝ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul, ← hE.neg_eq x y, neg_smul, mul_comm a b]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, neg_add]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]

/-- The real extension of an alternating integral form vanishes on the diagonal. -/
private theorem baseChange_apply_self {E : LinearMap.BilinForm ℤ V} (hE : E.IsAlt)
    (x : Hodge.Realification V) : E.baseChange ℝ x x = 0 := by
  have := baseChange_apply_swap hE x x
  linarith

namespace RiemannForm

variable (J : AlmostComplexStructure (Hodge.Realification V)) (E : LinearMap.BilinForm ℤ V)

/-- The **Hermitian form** `H (v, w) = E_ℝ (J v) w + i E_ℝ v w` of an integral bilinear form `E`
on `V` and an almost complex structure `J` on the realification of `V`, as a real bilinear map. It
is complex linear in the first variable for `J.complexModule` (`hermitian_smul_left`); when `E` is
a Riemann form it is conjugate symmetric (`IsRiemannForm.conj_hermitian`) and positive definite
(`IsRiemannForm.hermitian_self_pos`). -/
noncomputable def hermitian :
    Hodge.Realification V →ₗ[ℝ] Hodge.Realification V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun v w ↦ (E.baseChange ℝ (J v) w : ℂ) + Complex.I * E.baseChange ℝ v w)
    (fun v v' w ↦ by simp only [map_add, LinearMap.add_apply]; push_cast; ring)
    (fun c v w ↦ by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast; ring)
    (fun v w w' ↦ by simp only [map_add]; push_cast; ring)
    (fun c v w ↦ by
      simp only [map_smul, smul_eq_mul, Complex.real_smul]
      push_cast; ring)

/-- The defining formula `H (v, w) = E_ℝ (J v) w + i E_ℝ v w`. -/
@[simp]
theorem hermitian_apply (v w : Hodge.Realification V) :
    hermitian J E v w = (E.baseChange ℝ (J v) w : ℂ) + Complex.I * E.baseChange ℝ v w := by
  simp [hermitian]

/-- The real part of the Hermitian form is `E_ℝ (J v) w`. -/
theorem re_hermitian (v w : Hodge.Realification V) :
    (hermitian J E v w).re = E.baseChange ℝ (J v) w := by
  simp

/-- **The imaginary part of the Hermitian form is the Riemann form**: `Im H = E_ℝ`. -/
theorem im_hermitian (v w : Hodge.Realification V) :
    (hermitian J E v w).im = E.baseChange ℝ v w := by
  simp

/-- The Hermitian form turns `J` in the first variable into multiplication by `i`. -/
theorem hermitian_apply_left (v w : Hodge.Realification V) :
    hermitian J E (J v) w = Complex.I * hermitian J E v w := by
  simp only [hermitian_apply, apply_apply, map_neg, LinearMap.neg_apply]
  push_cast
  linear_combination (-(E.baseChange ℝ v w : ℂ)) * Complex.I_sq

/-- The Hermitian form is complex linear in the first variable for the complex structure
`J.complexModule`, in which `i` acts by `J`. -/
theorem hermitian_smul_left (z : ℂ) (v w : Hodge.Realification V) :
    letI := J.complexModule
    hermitian J E (z • v) w = z * hermitian J E v w := by
  let := J.complexModule
  rw [J.complexModule_smul_def, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, hermitian_apply_left, Complex.real_smul,
    Complex.real_smul, ← mul_assoc, ← add_mul]
  conv_rhs => rw [← Complex.re_add_im z]

/-- On the diagonal, the Hermitian form of an alternating form is real, equal to `E_ℝ (J v) v`. -/
theorem hermitian_self {E : LinearMap.BilinForm ℤ V} (hE : E.IsAlt) (v : Hodge.Realification V) :
    hermitian J E v v = (E.baseChange ℝ (J v) v : ℂ) := by
  simp [baseChange_apply_self hE]

end RiemannForm

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}

/-- The real extension of a Riemann form satisfies `E_ℝ (J v) w = E_ℝ (J w) v`: the real part of
the Hermitian form is symmetric. -/
theorem baseChange_apply_left_comm (h : J.IsRiemannForm E) (v w : Hodge.Realification V) :
    E.baseChange ℝ (J v) w = E.baseChange ℝ (J w) v := by
  have hinv := h.invariant v (J w)
  have hswap := baseChange_apply_swap h.isAlt v (J w)
  rw [apply_apply, map_neg] at hinv
  linarith

/-- **The Hermitian form of a Riemann form is conjugate symmetric**: `conj (H (w, v)) = H (v, w)`.
-/
theorem conj_hermitian (h : J.IsRiemannForm E) (v w : Hodge.Realification V) :
    conj (RiemannForm.hermitian J E w v) = RiemannForm.hermitian J E v w := by
  apply Complex.ext
  · simp [h.baseChange_apply_left_comm v w]
  · simp [baseChange_apply_swap h.isAlt v w]

/-- **The Hermitian form of a Riemann form is positive definite**:
`H (v, v) = E_ℝ (J v) v > 0` for every nonzero real vector `v`. -/
theorem hermitian_self_pos (h : J.IsRiemannForm E) {v : Hodge.Realification V} (hv : v ≠ 0) :
    0 < RiemannForm.hermitian J E v v := by
  rw [RiemannForm.hermitian_self J h.isAlt]
  exact Complex.zero_lt_real.mpr (h.positive v hv)

/-- Negating both the form and the complex structure preserves the Riemann form condition: if `E`
is a Riemann form for `J`, then `-E` is a Riemann form for `-J`, since
`(-E)_ℝ ((-J) v) v = E_ℝ (J v) v`. -/
theorem neg (h : J.IsRiemannForm E) : (-J).IsRiemannForm (-E) := by
  refine ⟨h.isAlt.neg, fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · simp [baseChange_neg_apply, h.invariant]
  · simpa [baseChange_neg_apply] using h.positive x hx

/-- On a nonzero lattice, the negative of a Riemann form for `J` is not a Riemann form for `J`:
it fails positivity. -/
theorem not_isRiemannForm_neg [Nontrivial (Hodge.Realification V)] (h : J.IsRiemannForm E) :
    ¬ J.IsRiemannForm (-E) := by
  intro h'
  obtain ⟨x, hx⟩ := exists_ne (0 : Hodge.Realification V)
  have := h'.positive x hx
  rw [baseChange_neg_apply] at this
  linarith [h.positive x hx]

/-- **A positive integer multiple of a Riemann form is a Riemann form.** Scaling does not preserve
principality: on a nonzero lattice, `n • E` with `n ≥ 2` is not a perfect pairing. -/
theorem scale (h : J.IsRiemannForm E) {n : ℕ} (hn : 0 < n) : J.IsRiemannForm (n • E) := by
  have hn' (x y : Hodge.Realification V) :
      (n • E).baseChange ℝ x y = n * E.baseChange ℝ x y := by
    simpa using baseChange_zsmul_apply n E x y
  refine ⟨h.isAlt.smul n, fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · simp [hn', h.invariant]
  · simpa [hn'] using mul_pos (Nat.cast_pos.mpr hn) (h.positive x hx)

variable {W : Type u'} [AddCommGroup W] {J' : AlmostComplexStructure (Hodge.Realification W)}

/-- The real extension of the pullback of an integral form is the pullback of its real extension
along the real extension of the map. -/
private theorem baseChange_compl₁₂ (f : W →ₗ[ℤ] V) (x y : Hodge.Realification W) :
    LinearMap.BilinForm.baseChange ℝ (E.compl₁₂ f f) x y =
      E.baseChange ℝ (f.baseChange ℝ x) (f.baseChange ℝ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **The pullback of a Riemann form along an injective integral map whose real extension is
complex linear is a Riemann form.** For complex tori this is pulling back a polarization along an
injective complex-linear map carrying lattice into lattice. -/
theorem pullback (h : J.IsRiemannForm E) {f : W →ₗ[ℤ] V} (hf : Function.Injective f)
    (hJ : ∀ x, f.baseChange ℝ (J' x) = J (f.baseChange ℝ x)) :
    J'.IsRiemannForm (E.compl₁₂ f f) := by
  have : Module.Flat ℤ ℝ := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have hfℝ : Function.Injective (f.baseChange ℝ) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  refine ⟨fun x ↦ h.isAlt (f x), fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [baseChange_compl₁₂, hJ, h.invariant]
  · rw [baseChange_compl₁₂, hJ]
    exact h.positive _ ((injective_iff_map_eq_zero' _).mp hfℝ x |>.not.mpr hx)

end IsRiemannForm

end TauCeti.AlmostComplexStructure
