/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Compact
import TauCeti.Topology.MetricSpace.Lipschitz.Basic

/-!
# Complexified curvature, isotropic curvature, and the PIC2 cone

Let `V` be a real inner product space and `r : FourTensor V` an algebraic curvature tensor in the
convention `r(u, v, z, w) = g(R(u, v)w, z)` (positive on the unit sphere). Extending `r`
complex-multilinearly to `TauCeti.Complexification V`, pair interchange and the first Bianchi
identity yield for every `f : Fin 4 → V` and `l, m : ℝ` the real-valued identity
`r_ℂ(f₀ + i m f₁, f₂ + i l f₃, f₀ - i m f₁, f₂ - i l f₃) = pic2Expression r f l m`, namely
`r₀₂₀₂ + l² r₀₃₀₃ + m² r₁₂₁₂ + l² m² r₁₃₁₃ - 2 l m r₀₁₂₃` (and `isotropicExpression r f` at
`l = m = 1`).

Nonnegativity on orthonormal four-frames defines `IsPICFourFrame`, while nonnegativity for all
`l, m ∈ [-1, 1]` defines `IsPIC2FourFrame`. When `4 ≤ Module.finrank ℝ V`, `IsPIC2FourFrame r`
coincides with nonnegative isotropic curvature of `r` zero-extended to `V ⊕ ℝ²`; when
`Module.finrank ℝ V < 4`, no orthonormal four-frame exists in `V` and both `IsPICFourFrame` and
`IsPIC2FourFrame` hold vacuously for every four-tensor. Both predicates cut out closed convex
`O(V)`-invariant cones in `FourTensor V`. In finite dimensions, the interior of the `PIC2` cone
inside `algebraicCurvatureSubmodule V` is characterized by strict positivity of `pic2Expression` on
all orthonormal four-frames and `l, m ∈ [-1, 1]` (hence equals `Set.univ` when `finrank ℝ V < 4`,
and is characterized by `0 < pic2Min r` when `4 ≤ finrank ℝ V`).

## Main definitions

* `TauCeti.FourTensor.complexify`: complex-multilinear extension to `TauCeti.Complexification V`.
* `TauCeti.FourTensor.pic2Expression`, `TauCeti.FourTensor.isotropicExpression`,
  `TauCeti.FourTensor.pic2Min`: isotropic-curvature expressions and compact-domain infimum.
* `TauCeti.FourTensor.IsPICFourFrame`, `TauCeti.FourTensor.IsPIC2FourFrame`: real four-frame `PIC`
  and `PIC2` cones.

## Main statements

* `TauCeti.FourTensor.complexify_apply`, `TauCeti.FourTensor.complexify_apply_four`,
  `TauCeti.FourTensor.complexify_zero`, `TauCeti.FourTensor.complexify_add`,
  `TauCeti.FourTensor.complexify_smul`: evaluation and `ℝ`-linearity of `complexify`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.complexify_apply_conj`: complexified isotropic identity.
* `TauCeti.FourTensor.isClosed_setOf_le_pic2Expression`,
  `TauCeti.FourTensor.convex_setOf_le_pic2Expression`,
  `TauCeti.FourTensor.isClosed_setOf_isPIC2FourFrame`,
  `TauCeti.FourTensor.convex_setOf_isPIC2FourFrame`, `TauCeti.FourTensor.lipschitzWith_pic2Min`.
* `TauCeti.FourTensor.mem_interior_isPIC2FourFrame_iff_forall_pos`,
  `TauCeti.FourTensor.mem_interior_isPIC2FourFrame_iff_exists_pos_le`,
  `TauCeti.FourTensor.mem_interior_isPIC2FourFrame_iff_pic2Min_pos`.

## References

* M. Micallef and J. D. Moore, *Minimal two-spheres and the topology of manifolds with positive
  curvature on totally isotropic two-planes*, Ann. of Math. (2) 127 (1988), 199–227.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307.
-/

public section

open Set
open scoped InnerProductSpace NNReal

noncomputable section

namespace TauCeti.FourTensor

/-! ### Complexification and the isotropic curvature expressions -/

section NormedSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private def partBit (z : Complexification V) (b : Bool) : V :=
  if b then z.im else z.re

private def weightBit (b : Bool) : ℂ :=
  if b then Complex.I else 1

private theorem sum_weightBit_partBit_smul (L : V →ₗ[ℝ] ℝ) (c : ℂ) (x : Complexification V)
    (b : Bool) :
    weightBit b * (L (partBit (c • x) b) : ℂ) +
      weightBit (!b) * (L (partBit (c • x) (!b)) : ℂ) =
    c * (weightBit b * (L (partBit x b) : ℂ) +
      weightBit (!b) * (L (partBit x (!b)) : ℂ)) := by
  cases b <;>
    simp only [Bool.not_false, Bool.not_true, weightBit, partBit, ↓reduceIte, Bool.false_eq_true,
      Complexification.smul_re, Complexification.smul_im, map_add, map_sub, map_smul, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;>
  · conv_rhs => rw [← Complex.re_add_im c]
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- Auxiliary `ℂ`-homogeneity in slot `i` for the 16-term real/imaginary expansion of `r`:
multiplying `x` by `c : ℂ` mixes its real and imaginary parts, so individual bit-tuples `b` are not
`ℂ`-homogeneous in isolation. Pairing each `b : Fin 4 → Bool` with the involutive bit-flip
`τ b = Function.update b i (!b i)` groups the two terms `1 * L((c • x).re) + I * L((c • x).im)` (for
the real linear functional `L` obtained by freezing the three entries `j ≠ i`), where
`sum_weightBit_partBit_smul` gives `ℂ`-homogeneity of each pair; doubling the sum via `τ` recovers
the full 16-term sum. -/
private theorem complexifyMultilinear_map_update_smul (r : FourTensor V)
    (m : Fin 4 → Complexification V) (i : Fin 4) (c : ℂ) (x : Complexification V) :
    (∑ b : Fin 4 → Bool, (∏ j : Fin 4, weightBit (b j)) *
      (r (fun j ↦ partBit (Function.update m i (c • x) j) (b j)) : ℂ)) =
    c * ∑ b : Fin 4 → Bool, (∏ j : Fin 4, weightBit (b j)) *
      (r (fun j ↦ partBit (Function.update m i x j) (b j)) : ℂ) := by
  let τ : Equiv.Perm (Fin 4 → Bool) :=
    { toFun := fun b ↦ Function.update b i (!b i)
      invFun := fun b ↦ Function.update b i (!b i)
      left_inv := fun b ↦ by ext j; by_cases hj : j = i <;> simp [hj]
      right_inv := fun b ↦ by ext j; by_cases hj : j = i <;> simp [hj] }
  let term (z : Complexification V) (b : Fin 4 → Bool) : ℂ :=
    (∏ j : Fin 4, weightBit (b j)) *
      (r (fun j ↦ partBit (Function.update m i z j) (b j)) : ℂ)
  suffices ∑ b, term (c • x) b = c * ∑ b, term x b from this
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  have hdoub (z : Complexification V) :
      2 * ∑ b, term z b = ∑ b, (term z b + term z (τ b)) := by
    rw [two_mul, Finset.sum_add_distrib, ← Equiv.sum_comp τ (term z)]
  rw [hdoub (c • x), mul_left_comm, hdoub x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hτne : ∀ j ≠ i, τ b j = b j := fun j hj ↦ by simp [τ, hj]
  let L : V →ₗ[ℝ] ℝ := r.toMultilinearMap.toLinearMap (fun j ↦ partBit (m j) (b j)) i
  have hterm (b' : Fin 4 → Bool) (hb' : ∀ j ≠ i, b' j = b j) (z : Complexification V) :
      term z b' = (∏ j ∈ Finset.univ.erase i, weightBit (b j)) * weightBit (b' i) *
        (L (partBit z (b' i)) : ℂ) := by
    have hupd : (fun j ↦ partBit (Function.update m i z j) (b' j)) =
        Function.update (fun j ↦ partBit (m j) (b j)) i (partBit z (b' i)) := by
      ext j; by_cases hj : j = i <;> simp [hj, hb']
    have hprod : (∏ j : Fin 4, weightBit (b' j)) =
        (∏ j ∈ Finset.univ.erase i, weightBit (b j)) * weightBit (b' i) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm]
      exact congr_arg₂ (· * ·) (Finset.prod_congr rfl fun j hj ↦
        congrArg weightBit (hb' j (Finset.ne_of_mem_erase hj))) rfl
    dsimp only [term, L]
    rw [hupd, hprod, ← ContinuousMultilinearMap.coe_coe, ← MultilinearMap.toLinearMap_apply]
  rw [hterm b (fun _ _ ↦ rfl), hterm (τ b) hτne, hterm b (fun _ _ ↦ rfl), hterm (τ b) hτne,
    show τ b i = !b i by simp [τ]]
  linear_combination (∏ j ∈ Finset.univ.erase i, weightBit (b j)) *
    sum_weightBit_partBit_smul L c x (b i)

/-- Auxiliary complex-multilinear extension of a real four-tensor to `Complexification V`, written
as the 16-term expansion over real and imaginary parts. -/
private def complexifyMultilinear (r : FourTensor V) :
    MultilinearMap (RingHom.id ℂ) (fun _ : Fin 4 ↦ Complexification V) ℂ :=
  MultilinearMap.mk'
    (fun m ↦ ∑ b : Fin 4 → Bool,
      (∏ j : Fin 4, weightBit (b j)) * (r (fun j ↦ partBit (m j) (b j)) : ℂ))
    (fun m i x y ↦ by
      have hupd (b : Fin 4 → Bool) (z : Complexification V) :
          (fun j ↦ partBit (Function.update m i z j) (b j)) =
            Function.update (fun j ↦ partBit (m j) (b j)) i (partBit z (b i)) := by
        ext j; by_cases hj : j = i <;> simp [hj]
      have hadd (b : Bool) : partBit (x + y) b = partBit x b + partBit y b := by
        cases b <;> simp [partBit]
      simp_rw [hupd, hadd, r.map_update_add, Complex.ofReal_add, mul_add, Finset.sum_add_distrib])
    (fun m i c x ↦ by
      simpa only [RingHom.id_apply, smul_eq_mul] using
        complexifyMultilinear_map_update_smul r m i c x)

/-- The complex-multilinear extension of a continuous real four-tensor `r : FourTensor V` to the
complexification `Complexification V`, characterized on real vectors by
`r.complexify ![ofReal u, ofReal v, ofReal z, ofReal w] = r ![u, v, z, w]`. -/
def complexify (r : FourTensor V) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 4 ↦ Complexification V) ℂ :=
  (complexifyMultilinear r).mkContinuous (16 * ‖r‖) fun m ↦ by
    simp only [complexifyMultilinear, MultilinearMap.mk'_apply]
    apply (norm_sum_le _ _).trans
    refine (Finset.sum_le_sum (g := fun _ ↦ ‖r‖ * ∏ j, ‖m j‖) fun b _ ↦ ?_).trans (le_of_eq ?_)
    · have hw : ‖∏ j : Fin 4, weightBit (b j)‖ = 1 := by
        rw [norm_prod]; exact Finset.prod_eq_one fun j _ ↦ by cases b j <;> simp [weightBit]
      rw [norm_mul, hw, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine (r.le_opNorm _).trans ?_
      gcongr with j; cases b j
      · exact Complexification.norm_re_le (m j)
      · exact Complexification.norm_im_le (m j)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
        Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- Expansion of `r.complexify m` into the `16`-term sum over the real and imaginary parts of
`m 0, m 1, m 2, m 3`. -/
theorem complexify_apply (r : FourTensor V) (m : Fin 4 → Complexification V) :
    r.complexify m =
      ∑ b : Fin 4 → Bool,
        (∏ j : Fin 4, if b j then (Complex.I : ℂ) else 1) *
          (r (fun j ↦ if b j then (m j).im else (m j).re) : ℂ) := by
  simp only [complexify, MultilinearMap.coe_mkContinuous, complexifyMultilinear,
    MultilinearMap.mk'_apply, weightBit, partBit]

/-- Four-variable expansion of `r.complexify ![z₀, z₁, z₂, z₃]` over `b₀, b₁, b₂, b₃ : Bool`
selecting the imaginary (`true`, weighted by `I`) or real (`false`, weighted by `1`) part of each
slot. -/
theorem complexify_apply_four (r : FourTensor V) (z₀ z₁ z₂ z₃ : Complexification V) :
    r.complexify ![z₀, z₁, z₂, z₃] =
      ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
        (if b₀ then (Complex.I : ℂ) else 1) * (if b₁ then (Complex.I : ℂ) else 1) *
          (if b₂ then (Complex.I : ℂ) else 1) * (if b₃ then (Complex.I : ℂ) else 1) *
          (toLinearMap₄ r (if b₀ then z₀.im else z₀.re) (if b₁ then z₁.im else z₁.re)
            (if b₂ then z₂.im else z₂.re) (if b₃ then z₃.im else z₃.re) : ℂ) := by
  rw [complexify_apply]
  let e : (Bool × Bool × Bool × Bool) ≃ (Fin 4 → Bool) :=
    { toFun := fun ⟨b₀, b₁, b₂, b₃⟩ ↦ ![b₀, b₁, b₂, b₃]
      invFun := fun b ↦ (b 0, b 1, b 2, b 3)
      left_inv := fun ⟨_, _, _, _⟩ ↦ rfl
      right_inv := fun b ↦ by ext j; fin_cases j <;> rfl }
  rw [← e.sum_comp]; simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₀ _ ↦ Finset.sum_congr rfl fun b₁ _ ↦
    Finset.sum_congr rfl fun b₂ _ ↦ Finset.sum_congr rfl fun b₃ _ ↦ ?_
  have harg :
      (fun j : Fin 4 ↦
        if e (b₀, b₁, b₂, b₃) j then (![z₀, z₁, z₂, z₃] j).im else (![z₀, z₁, z₂, z₃] j).re) =
        ![if b₀ then z₀.im else z₀.re, if b₁ then z₁.im else z₁.re,
          if b₂ then z₂.im else z₂.re, if b₃ then z₃.im else z₃.re] := by
    ext j; fin_cases j <;> rfl
  rw [harg, ← toLinearMap₄_apply, Fin.prod_univ_four]
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-- Complexifying the zero four-tensor gives `0`. -/
@[simp]
theorem complexify_zero : (0 : FourTensor V).complexify = 0 := by
  ext m
  simp [complexify_apply]

/-- Complexification of four-tensors is additive. -/
@[simp]
theorem complexify_add (r q : FourTensor V) :
    (r + q).complexify = r.complexify + q.complexify := by
  ext m
  simp [complexify_apply, mul_add, Finset.sum_add_distrib]

/-- Complexification of four-tensors is `ℝ`-homogeneous. -/
@[simp]
theorem complexify_smul (c : ℝ) (r : FourTensor V) :
    (c • r).complexify = (c : ℂ) • r.complexify := by
  ext m
  simp [complexify_apply, Finset.mul_sum, mul_left_comm]

/-- On real vectors embedded into `Complexification V`, `r.complexify` agrees with `r`. -/
@[simp]
theorem complexify_ofReal (r : FourTensor V) (u v z w : V) :
    r.complexify
      ![Complexification.ofReal u, Complexification.ofReal v,
        Complexification.ofReal z, Complexification.ofReal w] = (r ![u, v, z, w] : ℂ) := by
  rw [complexify_apply_four]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true,
    Complexification.ofReal_re, Complexification.ofReal_im, map_zero, LinearMap.zero_apply,
    Complex.ofReal_zero]; simp

/-- The two-parameter real isotropic-curvature expression of `r` on a four-tuple `f` with
parameters `l` and `m`:
`r₀₂₀₂ + l² r₀₃₀₃ + m² r₁₂₁₂ + l² m² r₁₃₁₃ - 2 l m r₀₁₂₃`. -/
def pic2Expression (r : FourTensor V) (f : Fin 4 → V) (l m : ℝ) : ℝ :=
  r ![f 0, f 2, f 0, f 2] + l ^ 2 * r ![f 0, f 3, f 0, f 3] +
    m ^ 2 * r ![f 1, f 2, f 1, f 2] + l ^ 2 * m ^ 2 * r ![f 1, f 3, f 1, f 3] -
    2 * l * m * r ![f 0, f 1, f 2, f 3]

/-- Defining formula for `pic2Expression`. -/
theorem pic2Expression_def (r : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression r f l m = r ![f 0, f 2, f 0, f 2] + l ^ 2 * r ![f 0, f 3, f 0, f 3] +
      m ^ 2 * r ![f 1, f 2, f 1, f 2] + l ^ 2 * m ^ 2 * r ![f 1, f 3, f 1, f 3] -
      2 * l * m * r ![f 0, f 1, f 2, f 3] := (rfl)

/-- The unit-parameter isotropic-curvature expression `r₀₂₀₂ + r₀₃₀₃ + r₁₂₁₂ + r₁₃₁₃ - 2 r₀₁₂₃`
on a four-tuple `f`: the specialization of `pic2Expression` to `l = 1` and `m = 1`. -/
def isotropicExpression (r : FourTensor V) (f : Fin 4 → V) : ℝ :=
  pic2Expression r f 1 1

/-- `isotropicExpression` is `pic2Expression` at `l = 1` and `m = 1`. -/
theorem isotropicExpression_def (r : FourTensor V) (f : Fin 4 → V) :
    isotropicExpression r f = pic2Expression r f 1 1 := (rfl)

/-- Explicit expansion of `isotropicExpression`. -/
theorem isotropicExpression_apply (r : FourTensor V) (f : Fin 4 → V) :
    isotropicExpression r f =
      r ![f 0, f 2, f 0, f 2] + r ![f 0, f 3, f 0, f 3] +
        r ![f 1, f 2, f 1, f 2] + r ![f 1, f 3, f 1, f 3] -
        2 * r ![f 0, f 1, f 2, f 3] := by
  simp only [isotropicExpression_def, pic2Expression_def]; ring

/-- The zero four-tensor has zero `pic2Expression`. -/
@[simp]
theorem pic2Expression_zero (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (0 : FourTensor V) f l m = 0 := by simp [pic2Expression_def]

/-- `pic2Expression` is additive in the four-tensor. -/
theorem pic2Expression_add (r q : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (r + q) f l m = pic2Expression r f l m + pic2Expression q f l m := by
  simp only [pic2Expression_def, add_apply]; ring

/-- `pic2Expression` preserves subtraction in the four-tensor. -/
theorem pic2Expression_sub (r q : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (r - q) f l m = pic2Expression r f l m - pic2Expression q f l m := by
  simp only [pic2Expression_def, sub_apply]; ring

/-- `pic2Expression` is homogeneous in the four-tensor. -/
theorem pic2Expression_smul (c : ℝ) (r : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (c • r) f l m = c * pic2Expression r f l m := by
  simp only [pic2Expression_def, smul_apply, smul_eq_mul]; ring

/-- At `l = 0` and `m = 0`, `pic2Expression r f 0 0` reduces to the sectional term
`r ![f 0, f 2, f 0, f 2]`. -/
@[simp]
theorem pic2Expression_zero_zero (r : FourTensor V) (f : Fin 4 → V) :
    pic2Expression r f 0 0 = r ![f 0, f 2, f 0, f 2] := by simp [pic2Expression_def]

/-- Pulling `r` back along a continuous linear map `L` evaluates `pic2Expression` on `L ∘ f`. -/
theorem pic2Expression_compContinuousLinearMap (r : FourTensor V) (L : W →L[ℝ] V)
    (f : Fin 4 → W) (l m : ℝ) :
    pic2Expression (r.compContinuousLinearMap fun _ ↦ L) f l m =
      pic2Expression r (L ∘ f) l m := by
  simp only [pic2Expression_def, compContinuousLinearMap_apply_vec, Function.comp_apply]

/-- **Complexified isotropic-curvature identity.** For an algebraic curvature tensor `r`, any
four-tuple `f : Fin 4 → V`, and scalars `l, m : ℝ`, evaluating the complexified curvature tensor on
`z = f 0 + i (m • f 1)`, `w = f 2 + i (l • f 3)`, and their conjugates `conj z, conj w` yields the
real quantity `pic2Expression r f l m`. -/
theorem IsAlgebraicCurvature.complexify_apply_conj {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (f : Fin 4 → V) (l m : ℝ) :
    r.complexify
      ![⟨f 0, m • f 1⟩, ⟨f 2, l • f 3⟩,
        Complexification.conj V ⟨f 0, m • f 1⟩,
        Complexification.conj V ⟨f 2, l • f 3⟩] =
      (pic2Expression r f l m : ℂ) := by
  rw [complexify_apply_four]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true,
    Complexification.conj_re, Complexification.conj_im,
    map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [toLinearMap₄_apply, Complex.ofReal_mul, Complex.ofReal_neg, pic2Expression_def,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hbianchiℂ :
      (r ![f 0, f 3, f 1, f 2] : ℂ) - (r ![f 0, f 2, f 1, f 3] : ℂ) =
        -(r ![f 0, f 1, f 2, f 3] : ℂ) := by
    exact_mod_cast (show r ![f 0, f 3, f 1, f 2] - r ![f 0, f 2, f 1, f 3] =
      -r ![f 0, f 1, f 2, f 3] by
      linarith [hr.cyclic_eq_zero (f 0) (f 1) (f 2) (f 3),
        hr.antisymm_first (f 2) (f 0) (f 1) (f 3), hr.swap_pairs (f 1) (f 2) (f 0) (f 3)])
  have hswap1 : (r ![f 1, f 3, f 0, f 2] : ℂ) = r ![f 0, f 2, f 1, f 3] := by
    exact_mod_cast hr.swap_pairs (f 1) (f 3) (f 0) (f 2)
  have hswap2 : (r ![f 1, f 2, f 0, f 3] : ℂ) = r ![f 0, f 3, f 1, f 2] := by
    exact_mod_cast hr.swap_pairs (f 1) (f 2) (f 0) (f 3)
  have hswap3 : (r ![f 0, f 3, f 0, f 2] : ℂ) = r ![f 0, f 2, f 0, f 3] := by
    exact_mod_cast hr.swap_pairs (f 0) (f 3) (f 0) (f 2)
  have hswap4 : (r ![f 1, f 2, f 0, f 2] : ℂ) = r ![f 0, f 2, f 1, f 2] := by
    exact_mod_cast hr.swap_pairs (f 1) (f 2) (f 0) (f 2)
  have hswap5 : (r ![f 1, f 3, f 0, f 3] : ℂ) = r ![f 0, f 3, f 1, f 3] := by
    exact_mod_cast hr.swap_pairs (f 1) (f 3) (f 0) (f 3)
  have hswap6 : (r ![f 1, f 3, f 1, f 2] : ℂ) = r ![f 1, f 2, f 1, f 3] := by
    exact_mod_cast hr.swap_pairs (f 1) (f 3) (f 1) (f 2)
  linear_combination
    Complex.I * (l : ℂ) * hswap3 +
    Complex.I * (m : ℂ) * hswap4 -
    Complex.I ^ 3 * (l : ℂ) ^ 2 * (m : ℂ) * hswap5 -
    Complex.I ^ 3 * (l : ℂ) * (m : ℂ) ^ 2 * hswap6 +
    Complex.I ^ 2 * (l : ℂ) * (m : ℂ) * hswap1 -
    Complex.I ^ 2 * (l : ℂ) * (m : ℂ) * hswap2 -
    2 * Complex.I ^ 2 * (l : ℂ) * (m : ℂ) * hbianchiℂ +
    (-((l : ℂ) ^ 2 * r ![f 0, f 3, f 0, f 3]) - (m : ℂ) ^ 2 * r ![f 1, f 2, f 1, f 2] +
      2 * (l : ℂ) * (m : ℂ) * r ![f 0, f 1, f 2, f 3]) * Complex.I_sq +
    (l : ℂ) ^ 2 * (m : ℂ) ^ 2 * r ![f 1, f 3, f 1, f 3] * Complex.I_pow_four

/-- Unit-parameter complexified isotropic-curvature identity: for `z = f 0 + i f 1` and
`w = f 2 + i f 3`, `r_ℂ(z, w, conj z, conj w) = isotropicExpression r f`. -/
theorem IsAlgebraicCurvature.complexify_apply_conj_one {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (f : Fin 4 → V) :
    r.complexify
      ![⟨f 0, f 1⟩, ⟨f 2, f 3⟩,
        Complexification.conj V ⟨f 0, f 1⟩,
        Complexification.conj V ⟨f 2, f 3⟩] =
      (isotropicExpression r f : ℂ) := by
  simpa only [one_smul, isotropicExpression_def] using hr.complexify_apply_conj f 1 1

end NormedSpace

/-! ### The real four-frame PIC and PIC2 cones -/

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Nonnegative isotropic curvature in real four-frame form: `isotropicExpression r f ≥ 0` on every
orthonormal four-frame `f` in `V` (vacuously satisfied when `Module.finrank ℝ V < 4`). -/
def IsPICFourFrame (r : FourTensor V) : Prop :=
  ∀ f : Fin 4 → V, Orthonormal ℝ f → 0 ≤ isotropicExpression r f

/-- Unfolding characterization of `IsPICFourFrame`. -/
theorem isPICFourFrame_def (r : FourTensor V) :
    IsPICFourFrame r ↔ ∀ f : Fin 4 → V, Orthonormal ℝ f → 0 ≤ isotropicExpression r f :=
  Iff.rfl

/-- The real four-frame form of `PIC2`: `pic2Expression r f l m ≥ 0` for every orthonormal
four-frame `f` in `V` and all parameters `l, m ∈ [-1, 1]`. When `4 ≤ Module.finrank ℝ V`, this
agrees with nonnegative isotropic curvature of the zero extension of `r` to `V ⊕ ℝ²`; when
`Module.finrank ℝ V < 4`, no orthonormal four-frame exists in `V` and `IsPIC2FourFrame r` holds
vacuously for every four-tensor `r`. -/
def IsPIC2FourFrame (r : FourTensor V) : Prop :=
  ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
    ∀ m ∈ Icc (-1 : ℝ) 1, 0 ≤ pic2Expression r f l m

/-- Unfolding characterization of `IsPIC2FourFrame`. -/
theorem isPIC2FourFrame_def (r : FourTensor V) :
    IsPIC2FourFrame r ↔ ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, 0 ≤ pic2Expression r f l m :=
  Iff.rfl

/-- `PIC2` implies `PIC` in the real four-frame formulation (`l = 1`, `m = 1`). -/
theorem IsPIC2FourFrame.isPICFourFrame {r : FourTensor V} (hr : IsPIC2FourFrame r) :
    IsPICFourFrame r :=
  fun f hf ↦ hr f hf 1 (by norm_num) 1 (by norm_num)

/-- The zero four-tensor satisfies `IsPICFourFrame`. -/
@[simp]
theorem isPICFourFrame_zero : IsPICFourFrame (0 : FourTensor V) :=
  fun _ _ ↦ by simp [isotropicExpression_def]

/-- The zero four-tensor satisfies `IsPIC2FourFrame`. -/
@[simp]
theorem isPIC2FourFrame_zero : IsPIC2FourFrame (0 : FourTensor V) :=
  fun _ _ _ _ _ _ ↦ by simp

/-- `IsPICFourFrame` is closed under addition. -/
theorem IsPICFourFrame.add {r q : FourTensor V} (hr : IsPICFourFrame r) (hq : IsPICFourFrame q) :
    IsPICFourFrame (r + q) := fun f hf ↦ by
  rw [isotropicExpression_def, pic2Expression_add]; exact add_nonneg (hr f hf) (hq f hf)

/-- `IsPIC2FourFrame` is closed under addition. -/
theorem IsPIC2FourFrame.add {r q : FourTensor V} (hr : IsPIC2FourFrame r)
    (hq : IsPIC2FourFrame q) : IsPIC2FourFrame (r + q) := fun f hf l hl m hm ↦ by
  rw [pic2Expression_add]; exact add_nonneg (hr f hf l hl m hm) (hq f hf l hl m hm)

/-- `IsPICFourFrame` is closed under nonnegative scalar multiplication. -/
theorem IsPICFourFrame.smul {r : FourTensor V} (hr : IsPICFourFrame r) {c : ℝ} (hc : 0 ≤ c) :
    IsPICFourFrame (c • r) := fun f hf ↦ by
  rw [isotropicExpression_def, pic2Expression_smul]; exact mul_nonneg hc (hr f hf)

/-- `IsPIC2FourFrame` is closed under nonnegative scalar multiplication. -/
theorem IsPIC2FourFrame.smul {r : FourTensor V} (hr : IsPIC2FourFrame r) {c : ℝ} (hc : 0 ≤ c) :
    IsPIC2FourFrame (c • r) := fun f hf l hl m hm ↦ by
  rw [pic2Expression_smul]; exact mul_nonneg hc (hr f hf l hl m hm)

/-- For any real threshold `ε`, the superlevel set of four-tensors satisfying
`ε ≤ pic2Expression r f l m` on all orthonormal four-frames `f` and `l, m ∈ [-1, 1]` is convex in
`FourTensor V`. -/
theorem convex_setOf_le_pic2Expression (ε : ℝ) :
    Convex ℝ {r : FourTensor V | ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m} :=
  fun _ h₁ _ h₂ a b ha hb hab f hf l hl m hm ↦ by
    rw [pic2Expression_add, pic2Expression_smul, pic2Expression_smul]
    linarith [mul_le_mul_of_nonneg_left (h₁ f hf l hl m hm) ha,
      mul_le_mul_of_nonneg_left (h₂ f hf l hl m hm) hb,
      show a * ε + b * ε = ε by rw [← add_mul, hab, one_mul]]

/-- The `PIC` four-frame cone is convex in `FourTensor V`. -/
theorem convex_setOf_isPICFourFrame : Convex ℝ {r : FourTensor V | IsPICFourFrame r} :=
  fun _ hr _ hq _ _ ha hb _ ↦ (hr.smul ha).add (hq.smul hb)

/-- The `PIC2` four-frame cone is convex in `FourTensor V`. -/
theorem convex_setOf_isPIC2FourFrame : Convex ℝ {r : FourTensor V | IsPIC2FourFrame r} :=
  convex_setOf_le_pic2Expression 0

/-- Joint continuity of `(r, f, l, m) ↦ pic2Expression r f l m`. -/
theorem continuous_pic2Expression :
    Continuous fun p : FourTensor V × (Fin 4 → V) × ℝ × ℝ ↦
      pic2Expression p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have heval (i₀ i₁ i₂ i₃ : Fin 4) :
      Continuous fun p : FourTensor V × (Fin 4 → V) × ℝ × ℝ ↦
        p.1 ![p.2.1 i₀, p.2.1 i₁, p.2.1 i₂, p.2.1 i₃] := by
    have hcongr : (fun p : FourTensor V × (Fin 4 → V) × ℝ × ℝ ↦
        ![p.2.1 i₀, p.2.1 i₁, p.2.1 i₂, p.2.1 i₃]) =
        fun p k ↦ p.2.1 (![i₀, i₁, i₂, i₃] k) := by ext p k; fin_cases k <;> rfl
    have hvec : Continuous fun p : FourTensor V × (Fin 4 → V) × ℝ × ℝ ↦
        ![p.2.1 i₀, p.2.1 i₁, p.2.1 i₂, p.2.1 i₃] := by
      rw [hcongr]
      exact continuous_pi fun k ↦
        (continuous_apply (![i₀, i₁, i₂, i₃] k)).comp (continuous_fst.comp continuous_snd)
    exact continuous_eval.comp (continuous_fst.prodMk hvec)
  simp only [pic2Expression_def]
  fun_prop

/-- For any real threshold `ε`, the superlevel set of four-tensors satisfying
`ε ≤ pic2Expression r f l m` on all orthonormal four-frames `f` and `l, m ∈ [-1, 1]` is closed in
`FourTensor V`. -/
theorem isClosed_setOf_le_pic2Expression (ε : ℝ) :
    IsClosed {r : FourTensor V | ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m} := by
  have heq : {r : FourTensor V | ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m} =
      ⋂ (f : {f : Fin 4 → V // Orthonormal ℝ f}) (l : Icc (-1 : ℝ) 1) (m : Icc (-1 : ℝ) 1),
        {r : FourTensor V | ε ≤ pic2Expression r f.1 l.1 m.1} := by
    ext r; simp only [mem_ofPred_eq, mem_iInter, Subtype.forall]
  rw [heq]
  exact isClosed_iInter fun f ↦ isClosed_iInter fun l ↦ isClosed_iInter fun m ↦
    isClosed_le continuous_const
      (continuous_pic2Expression.comp (Continuous.prodMk_left (f.1, l.1, m.1)))

/-- The `PIC2` four-frame cone is closed in `FourTensor V`. -/
theorem isClosed_setOf_isPIC2FourFrame : IsClosed {r : FourTensor V | IsPIC2FourFrame r} :=
  isClosed_setOf_le_pic2Expression 0

/-- The `PIC` four-frame cone is closed in `FourTensor V`. -/
theorem isClosed_setOf_isPICFourFrame : IsClosed {r : FourTensor V | IsPICFourFrame r} := by
  have heq : {r : FourTensor V | IsPICFourFrame r} =
      ⋂ (f : {f : Fin 4 → V // Orthonormal ℝ f}),
        {r : FourTensor V | 0 ≤ pic2Expression r f.1 1 1} := by
    ext r; simp only [mem_ofPred_eq, IsPICFourFrame, isotropicExpression_def, mem_iInter,
      Subtype.forall]
  rw [heq]
  exact isClosed_iInter fun f ↦ isClosed_le continuous_const
    (continuous_pic2Expression.comp (Continuous.prodMk_left (f.1, 1, 1)))

/-- Pulling a `PIC2` four-tensor back along a linear isometry preserves `IsPIC2FourFrame`. -/
theorem IsPIC2FourFrame.compContinuousLinearMap_linearIsometry {r : FourTensor V}
    (hr : IsPIC2FourFrame r) (L : W →ₗᵢ[ℝ] V) :
    IsPIC2FourFrame (r.compContinuousLinearMap fun _ ↦ L.toContinuousLinearMap) :=
  fun f hf l hl m hm ↦ by
    rw [pic2Expression_compContinuousLinearMap]
    exact hr (L ∘ f) (L.orthonormal_comp_iff.2 hf) l hl m hm

/-- Linear isometric equivalences preserve and reflect `IsPIC2FourFrame`. -/
@[simp]
theorem isPIC2FourFrame_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    {r : FourTensor V} :
    IsPIC2FourFrame (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) ↔
      IsPIC2FourFrame r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compContinuousLinearMap_linearIsometry e.toLinearIsometry⟩
  convert h.compContinuousLinearMap_linearIsometry e.symm.toLinearIsometry using 1
  ext m; simp

/-- Linear isometric equivalences preserve and reflect `IsPICFourFrame`. -/
@[simp]
theorem isPICFourFrame_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    {r : FourTensor V} :
    IsPICFourFrame (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) ↔
      IsPICFourFrame r := by
  refine ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · simpa [isotropicExpression_def, pic2Expression_compContinuousLinearMap, Function.comp_def]
      using h (e.symm ∘ f) (e.symm.toLinearIsometry.orthonormal_comp_iff.2 hf)
  · simpa [isotropicExpression_def, pic2Expression_compContinuousLinearMap] using
      h (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf)

/-- `algebraicCurvatureLinearIsometryEquiv e` preserves and reflects membership in the topological
interior of `{q : algebraicCurvatureSubmodule _ | IsPIC2FourFrame q.1}`. -/
@[simp]
theorem algebraicCurvatureLinearIsometryEquiv_mem_interior_isPIC2FourFrame_iff (e : W ≃ₗᵢ[ℝ] V)
    {r : algebraicCurvatureSubmodule V} :
    algebraicCurvatureLinearIsometryEquiv e r ∈
        interior {q : algebraicCurvatureSubmodule W | IsPIC2FourFrame q.1} ↔
      r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  let φ := (algebraicCurvatureLinearIsometryEquiv e).toHomeomorph
  have hpre : φ ⁻¹' {q : algebraicCurvatureSubmodule W | IsPIC2FourFrame q.1} =
      {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
    ext q; simp [φ]
  rw [← hpre, ← φ.preimage_interior]; rfl

/-- Operator-norm bound on `pic2Expression` over orthonormal four-frames and `l, m ∈ [-1, 1]`:
`|pic2Expression r f l m| ≤ 6 ‖r‖`. -/
theorem abs_pic2Expression_le_six_mul_norm (r : FourTensor V) {f : Fin 4 → V}
    (hf : Orthonormal ℝ f) {l m : ℝ} (hl : l ∈ Icc (-1 : ℝ) 1) (hm : m ∈ Icc (-1 : ℝ) 1) :
    |pic2Expression r f l m| ≤ 6 * ‖r‖ := by
  have hentry (i₀ i₁ i₂ i₃ : Fin 4) : |r ![f i₀, f i₁, f i₂, f i₃]| ≤ ‖r‖ :=
    abs_apply_le_norm_of_norm_eq_one r (hf.1 i₀) (hf.1 i₁) (hf.1 i₂) (hf.1 i₃)
  have hscale (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ ‖r‖) : |a * b| ≤ ‖r‖ := by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
  have hl_sq : |l ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg l)]; nlinarith [hl.1, hl.2]
  have hm_sq : |m ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg m)]; nlinarith [hm.1, hm.2]
  have hb3 := abs_le.1 (hscale (l ^ 2 * m ^ 2) _
    (by rw [abs_mul]; nlinarith [abs_nonneg (l ^ 2), abs_nonneg (m ^ 2)]) (hentry 1 3 1 3))
  have hb4 := abs_le.1 (hscale (l * m) _
    (by rw [abs_mul]; nlinarith [abs_le.2 hl, abs_le.2 hm, abs_nonneg l, abs_nonneg m])
    (hentry 0 1 2 3))
  rw [pic2Expression_def, abs_le]
  exact ⟨by linarith [(abs_le.1 (hentry 0 2 0 2)).1,
      (abs_le.1 (hscale (l ^ 2) _ hl_sq (hentry 0 3 0 3))).1,
      (abs_le.1 (hscale (m ^ 2) _ hm_sq (hentry 1 2 1 2))).1],
    by linarith [(abs_le.1 (hentry 0 2 0 2)).2,
      (abs_le.1 (hscale (l ^ 2) _ hl_sq (hentry 0 3 0 3))).2,
      (abs_le.1 (hscale (m ^ 2) _ hm_sq (hentry 1 2 1 2))).2]⟩

/-- The infimum of `pic2Expression r f l m` over all orthonormal four-frames `f` and parameters
`l, m ∈ [-1, 1]` (equal to `0` when no orthonormal four-frame exists). -/
def pic2Min (r : FourTensor V) : ℝ :=
  sInf ((fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2) ''
    ({f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))

/-- Defining formula for `pic2Min`. -/
theorem pic2Min_def (r : FourTensor V) :
    pic2Min r =
      sInf ((fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2) ''
        ({f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) :=
  (rfl)

private theorem bddBelow_pic2Image (r : FourTensor V) :
    BddBelow ((fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2) ''
      ({f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) :=
  ⟨-(6 * ‖r‖), by rintro _ ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, rfl⟩; exact
    neg_le_of_abs_le (abs_pic2Expression_le_six_mul_norm r hf hl hm)⟩

/-- `pic2Min r` bounds `pic2Expression r f l m` from below on every orthonormal four-frame `f` and
`l, m ∈ [-1, 1]`. -/
theorem pic2Min_le_pic2Expression (r : FourTensor V) {f : Fin 4 → V} (hf : Orthonormal ℝ f)
    {l m : ℝ} (hl : l ∈ Icc (-1 : ℝ) 1) (hm : m ∈ Icc (-1 : ℝ) 1) :
    pic2Min r ≤ pic2Expression r f l m :=
  csInf_le (bddBelow_pic2Image r) ⟨(f, l, m), ⟨hf, hl, hm⟩, rfl⟩

/-- If `c ≤ pic2Expression r f l m` on a nonempty orthonormal-four-frame domain, then
`c ≤ pic2Min r`. -/
theorem le_pic2Min_of_forall_le {r : FourTensor V} {c : ℝ}
    (hne : {f : Fin 4 → V | Orthonormal ℝ f}.Nonempty)
    (hc : ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, c ≤ pic2Expression r f l m) :
    c ≤ pic2Min r := by
  obtain ⟨f₀, hf₀⟩ := hne
  refine le_csInf ⟨pic2Expression r f₀ 0 0, ⟨(f₀, 0, 0), ⟨hf₀, by norm_num, by norm_num⟩, rfl⟩⟩ ?_
  rintro _ ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, rfl⟩; exact hc f hf l hl m hm

/-- `pic2Min` is `6`-Lipschitz on `FourTensor V`. -/
theorem lipschitzWith_pic2Min : LipschitzWith 6 (pic2Min (V := V)) :=
  TauCeti.lipschitzWith_sInf_image bddBelow_pic2Image fun ⟨f, l, m⟩ ⟨hf, hl, hm⟩ ↦
    LipschitzWith.of_dist_le_mul fun r q ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat, ← pic2Expression_sub] using
        abs_pic2Expression_le_six_mul_norm (r - q) hf hl hm

/-- `pic2Min` is continuous on `FourTensor V`. -/
theorem continuous_pic2Min : Continuous (pic2Min (V := V)) :=
  lipschitzWith_pic2Min.continuous

/-- `pic2Min` is invariant under pullback by linear isometric equivalences. -/
@[simp]
theorem pic2Min_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    pic2Min (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) = pic2Min r := by
  rw [pic2Min_def, pic2Min_def]; congr 1; ext y; constructor
  · rintro ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, rfl⟩
    exact ⟨(e ∘ f, l, m), ⟨e.toLinearIsometry.orthonormal_comp_iff.2 hf, hl, hm⟩,
      (pic2Expression_compContinuousLinearMap r (e : W →L[ℝ] V) f l m).symm⟩
  · rintro ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, rfl⟩
    refine ⟨(e.symm ∘ f, l, m), ⟨e.symm.toLinearIsometry.orthonormal_comp_iff.2 hf, hl, hm⟩, ?_⟩
    dsimp only; rw [pic2Expression_compContinuousLinearMap]; congr 2; funext i; simp

/-- If a uniform positive margin `ε > 0` bounds `pic2Expression r.1 f l m` below on all orthonormal
four-frames and `l, m ∈ [-1, 1]`, then `r` lies in the topological interior of
`{q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}` (which coincides with the `PIC2` cone
when `4 ≤ Module.finrank ℝ V` and equals `Set.univ` when `Module.finrank ℝ V < 4`). -/
theorem mem_interior_isPIC2FourFrame_of_exists_pos_le {r : algebraicCurvatureSubmodule V}
    {ε : ℝ} (hε : 0 < ε)
    (hle : ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r.1 f l m) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε / 6, by positivity, fun {q} hq f hf l hl m hm ↦ ?_⟩
  have hdist : ‖q.1 - r.1‖ < ε / 6 := by rwa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hq
  have hdiff : |pic2Expression q.1 f l m - pic2Expression r.1 f l m| ≤ 6 * ‖q.1 - r.1‖ := by
    rw [← pic2Expression_sub]; exact abs_pic2Expression_le_six_mul_norm (q.1 - r.1) hf hl hm
  linarith [hle f hf l hl m hm, (abs_le.1 hdiff).1]

end InnerProductSpace

/-! ### Finite-dimensional consequences: constant curvature and interior of PIC2 -/

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- On an orthonormal four-frame `f`, `constantCurvature V` has `pic2Expression` equal to
`(1 + l²) (1 + m²)`. -/
@[simp]
theorem pic2Expression_constantCurvature {f : Fin 4 → V} (hf : Orthonormal ℝ f) (l m : ℝ) :
    pic2Expression (constantCurvature V) f l m = (1 + l ^ 2) * (1 + m ^ 2) := by
  have hdiag (i j : Fin 4) (hij : i ≠ j) : constantCurvature V ![f i, f j, f i, f j] = 1 := by
    rw [constantCurvature_apply_self, hf.1 i, hf.1 j, hf.2 hij]; ring
  have hmix : constantCurvature V ![f 0, f 1, f 2, f 3] = 0 := by
    rw [constantCurvature_apply, hf.2 (by decide : (0 : Fin 4) ≠ 2),
      hf.2 (by decide : (0 : Fin 4) ≠ 3)]; ring
  rw [pic2Expression_def, hdiag 0 2 (by decide), hdiag 0 3 (by decide),
    hdiag 1 2 (by decide), hdiag 1 3 (by decide), hmix]; ring

/-- On an orthonormal four-frame `f`, `constantCurvature V` has `isotropicExpression` `4`. -/
@[simp]
theorem isotropicExpression_constantCurvature {f : Fin 4 → V} (hf : Orthonormal ℝ f) :
    isotropicExpression (constantCurvature V) f = 4 := by
  rw [isotropicExpression_def, pic2Expression_constantCurvature hf]; norm_num

/-- Every nonnegative multiple of `constantCurvature V` lies in `IsPIC2FourFrame`. -/
theorem isPIC2FourFrame_smul_constantCurvature {κ : ℝ} (hκ : 0 ≤ κ) :
    IsPIC2FourFrame (κ • constantCurvature V) := fun _ hf _ _ _ _ ↦ by
  rw [pic2Expression_smul, pic2Expression_constantCurvature hf]; positivity

/-- In dimension at least four, `κ • constantCurvature V` lies in `IsPIC2FourFrame` if and only if
`0 ≤ κ`. -/
theorem isPIC2FourFrame_smul_constantCurvature_iff (hn : 4 ≤ Module.finrank ℝ V) {κ : ℝ} :
    IsPIC2FourFrame (κ • constantCurvature V) ↔ 0 ≤ κ := by
  refine ⟨fun h ↦ ?_, isPIC2FourFrame_smul_constantCurvature⟩
  obtain ⟨f, hf⟩ :=
    (TauCeti.nonempty_setOfPred_orthonormal_iff (ι := Fin 4) (E := V)).2 (by simpa using hn)
  have h0 := h f hf 0 (by norm_num) 0 (by norm_num)
  rw [pic2Expression_smul, pic2Expression_constantCurvature hf] at h0; linarith

/-- In dimension at least four, `pic2Min r` is attained at an orthonormal four-frame and parameters
`l, m ∈ [-1, 1]`. -/
theorem exists_orthonormal_eq_pic2Min (hn : 4 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ∃ (f : Fin 4 → V) (l m : ℝ), Orthonormal ℝ f ∧ l ∈ Icc (-1 : ℝ) 1 ∧ m ∈ Icc (-1 : ℝ) 1 ∧
      pic2Expression r f l m = pic2Min r := by
  set K := {f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hK : IsCompact K :=
    TauCeti.isCompact_setOfPred_orthonormal.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨f₀, hf₀⟩ :=
    (TauCeti.nonempty_setOfPred_orthonormal_iff (ι := Fin 4) (E := V)).2 (by simpa using hn)
  have hcont : Continuous fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2 :=
    continuous_pic2Expression.comp (Continuous.prodMk_right r)
  obtain ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, hmin⟩ :=
    hK.exists_isMinOn ⟨(f₀, 0, 0), hf₀, by norm_num, by norm_num⟩ hcont.continuousOn
  exact ⟨f, l, m, hf, hl, hm, le_antisymm
    (le_pic2Min_of_forall_le ⟨f₀, hf₀⟩ fun f' hf' l' hl' m' hm' ↦
      isMinOn_iff.1 hmin (f', l', m') ⟨hf', hl', hm'⟩) (pic2Min_le_pic2Expression r hf hl hm)⟩

private theorem exists_pos_le_pic2Expression_of_forall_pos {r : FourTensor V}
    (hpos : ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, 0 < pic2Expression r f l m) :
    ∃ ε > 0, ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m := by
  by_cases hn : 4 ≤ Module.finrank ℝ V
  · obtain ⟨f₀, l₀, m₀, hf₀, hl₀, hm₀, hmin⟩ := exists_orthonormal_eq_pic2Min hn r
    exact ⟨pic2Min r, hmin ▸ hpos f₀ hf₀ l₀ hl₀ m₀ hm₀,
      fun _ hf _ hl _ hm ↦ pic2Min_le_pic2Expression r hf hl hm⟩
  · refine ⟨1, zero_lt_one, fun f hf ↦ ?_⟩
    have hcard := hf.linearIndependent.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard; omega

/-- On a finite-dimensional real inner product space, `r ∈ algebraicCurvatureSubmodule V` lies in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}` if and only if
`0 < pic2Expression r.1 f l m` for every orthonormal four-frame `f` and all `l, m ∈ [-1, 1]`
(in particular, when `Module.finrank ℝ V < 4`, both sides hold vacuously for every `r`). -/
theorem mem_interior_isPIC2FourFrame_iff_forall_pos {r : algebraicCurvatureSubmodule V} :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} ↔
      ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
        ∀ m ∈ Icc (-1 : ℝ) 1, 0 < pic2Expression r.1 f l m := by
  refine ⟨fun hint f hf l hl m hm ↦ ?_, fun hpos ↦ ?_⟩
  · rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨δ, hδ, hball⟩ := hint
    let I₀ : algebraicCurvatureSubmodule V :=
      ⟨constantCurvature V,
        mem_algebraicCurvatureSubmodule.2 isAlgebraicCurvature_constantCurvature⟩
    set t : ℝ := δ / (2 * (‖I₀.1‖ + 1))
    have ht_pos : 0 < t := by positivity
    have hdist : dist (r - t • I₀) r < δ := by
      rw [Subtype.dist_eq, dist_eq_norm, Submodule.coe_sub, Submodule.coe_smul_of_tower,
        sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht_pos.le]
      calc δ / (2 * (‖I₀.1‖ + 1)) * ‖I₀.1‖ = δ * (‖I₀.1‖ / (2 * (‖I₀.1‖ + 1))) := by ring
        _ < δ * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2
          (by linarith [norm_nonneg I₀.1])) hδ
        _ = δ := mul_one δ
    have hval := hball hdist f hf l hl m hm
    simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, I₀, pic2Expression_sub,
      pic2Expression_smul, pic2Expression_constantCurvature hf] at hval
    nlinarith [show 1 ≤ (1 + l ^ 2) * (1 + m ^ 2) by nlinarith [sq_nonneg l, sq_nonneg m]]
  · obtain ⟨ε, hε, hle⟩ := exists_pos_le_pic2Expression_of_forall_pos hpos
    exact mem_interior_isPIC2FourFrame_of_exists_pos_le hε hle

/-- On a finite-dimensional real inner product space, `r ∈ algebraicCurvatureSubmodule V` lies in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}` if and only if there is a
uniform margin `ε > 0` bounding `pic2Expression` below on all orthonormal four-frames and
`l, m ∈ [-1, 1]` (vacuously satisfied with any `ε > 0` when `Module.finrank ℝ V < 4`). -/
theorem mem_interior_isPIC2FourFrame_iff_exists_pos_le {r : algebraicCurvatureSubmodule V} :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} ↔
      ∃ ε > 0, ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
        ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r.1 f l m :=
  ⟨fun hint ↦ exists_pos_le_pic2Expression_of_forall_pos
    (mem_interior_isPIC2FourFrame_iff_forall_pos.1 hint),
    fun ⟨_, hε, hle⟩ ↦ mem_interior_isPIC2FourFrame_of_exists_pos_le hε hle⟩

/-- Every positive multiple of `constantCurvature V` lies in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}`. -/
theorem smul_constantCurvature_mem_interior_isPIC2FourFrame {κ : ℝ} (hκ : 0 < κ) :
    (⟨κ • constantCurvature V,
      Submodule.smul_mem _ κ (mem_algebraicCurvatureSubmodule.2
        isAlgebraicCurvature_constantCurvature)⟩ : algebraicCurvatureSubmodule V) ∈
      interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  rw [mem_interior_isPIC2FourFrame_iff_forall_pos]; intro f hf l _ m _
  rw [pic2Expression_smul, pic2Expression_constantCurvature hf]; positivity

/-- In dimension at least four, `r ∈ algebraicCurvatureSubmodule V` lies in the interior of the
`PIC2` cone if and only if `0 < pic2Min r.1`. -/
theorem mem_interior_isPIC2FourFrame_iff_pic2Min_pos (hn : 4 ≤ Module.finrank ℝ V)
    {r : algebraicCurvatureSubmodule V} :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} ↔ 0 < pic2Min r.1 := by
  rw [mem_interior_isPIC2FourFrame_iff_exists_pos_le]
  refine ⟨fun ⟨ε, hε, hle⟩ ↦ ?_, fun hpos ↦ ⟨pic2Min r.1, hpos, fun _ hf _ hl _ hm ↦
    pic2Min_le_pic2Expression r.1 hf hl hm⟩⟩
  obtain ⟨f₀, hf₀⟩ :=
    (TauCeti.nonempty_setOfPred_orthonormal_iff (ι := Fin 4) (E := V)).2 (by simpa using hn)
  exact hε.trans_le (le_pic2Min_of_forall_le ⟨f₀, hf₀⟩ hle)

end FiniteDimensional

end TauCeti.FourTensor
