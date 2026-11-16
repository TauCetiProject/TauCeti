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

For `r : FourTensor V`, its complex-multilinear extension `r.complexify` to
`TauCeti.Complexification V` satisfies `r_ℂ(f₀ + i m f₁, f₂ + i l f₃, conj _, conj _) =
pic2Expression r f l m` for algebraic curvature tensors (and `isotropicExpression r f` at
`l = m = 1`). Nonnegativity on orthonormal four-frames (and `l, m ∈ [-1, 1]`) defines the closed
convex `O(V)`-invariant cones `IsPICFourFrame` and `IsPIC2FourFrame` (matching geometric `PIC2`
in finite dimension `≥ 4`, and vacuous when no orthonormal four-frame exists). In finite
dimensions, `interior {q | IsPIC2FourFrame q.1}` is characterized by strict positivity of
`pic2Expression` and by `0 < pic2Min r` when `4 ≤ finrank ℝ V`.

## Main definitions & statements

* `complexify`, `pic2Expression`, `isotropicExpression`, `pic2Min`, `IsPICFourFrame`,
  `IsPIC2FourFrame`, `complexify_apply_four`, `IsAlgebraicCurvature.complexify_apply_conj`,
  `lipschitzWith_pic2Min`, `mem_interior_isPIC2FourFrame_iff_forall_pos`,
  `mem_interior_isPIC2FourFrame_iff_exists_pos_le`, `mem_interior_isPIC2FourFrame_iff_pic2Min_pos`.

## References

* M. Micallef and J. D. Moore, Ann. of Math. (2) 127 (1988), 199–227.
* S. Brendle and R. Schoen, J. Amer. Math. Soc. 22 (2009), 287–307.
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

private def liftStep {A B : Type*} [AddCommMonoid A] [Module ℝ A]
    [AddCommMonoid B] [Module ℝ B] [Module ℂ B] [IsScalarTower ℝ ℂ B]
    (g : A →ₗ[ℝ] B) : (V →ₗ[ℝ] A) →ₗ[ℝ] (Complexification V →ₗ[ℂ] B) where
  toFun f :=
    { toFun := fun z ↦ g (f z.re) + Complex.I • g (f z.im)
      map_add' := fun z w ↦ by
        simp only [Complexification.add_re, Complexification.add_im, map_add, smul_add]
        exact add_add_add_comm _ _ _ _
      map_smul' := fun c z ↦ by
        have hre : (c.re : ℂ) + Complex.I * c.im = c := by rw [mul_comm]; exact Complex.re_add_im c
        have him : ((-c.im : ℝ) : ℂ) + Complex.I * c.re = c * Complex.I := by
          apply Complex.ext <;> simp
        have hs (a : ℝ) (x : B) : a • x = (a : ℂ) • x := by
          rw [← Complex.coe_algebraMap, algebraMap_smul]
        simp only [Complexification.smul_re, Complexification.smul_im, sub_eq_add_neg, ← neg_smul,
          map_add, map_smul, smul_add, RingHom.id_apply, hs, smul_smul]
        rw [add_add_add_comm, ← add_smul, ← add_smul, hre, him] }
  map_add' _ _ := by
    ext z; simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, map_add, smul_add]
    exact add_add_add_comm _ _ _ _
  map_smul' c _ := by
    ext z; simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
      map_smul, smul_add]; rw [← algebraMap_smul ℂ c, smul_comm]

private theorem liftStep_apply {A B : Type*} [AddCommMonoid A] [Module ℝ A]
    [AddCommMonoid B] [Module ℝ B] [Module ℂ B] [IsScalarTower ℝ ℂ B]
    (g : A →ₗ[ℝ] B) (f : V →ₗ[ℝ] A) (z : Complexification V) :
    liftStep g f z = g (f z.re) + Complex.I • g (f z.im) := rfl

private def complexifyLinear₄ : FourTensor V →ₗ[ℝ] Complexification V →ₗ[ℂ]
    Complexification V →ₗ[ℂ] Complexification V →ₗ[ℂ] Complexification V →ₗ[ℂ] ℂ :=
  (liftStep (liftStep (liftStep (liftStep (Algebra.linearMap ℝ ℂ))))).comp toLinearMap₄

private theorem complexifyLinear₄_eq (r : FourTensor V) (z₀ z₁ z₂ z₃ : Complexification V) :
    complexifyLinear₄ r z₀ z₁ z₂ z₃ =
      ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
        (if b₀ then (Complex.I : ℂ) else 1) * (if b₁ then (Complex.I : ℂ) else 1) *
          (if b₂ then (Complex.I : ℂ) else 1) * (if b₃ then (Complex.I : ℂ) else 1) *
          (toLinearMap₄ r (if b₀ then z₀.im else z₀.re) (if b₁ then z₁.im else z₁.re)
            (if b₂ then z₂.im else z₂.re) (if b₃ then z₃.im else z₃.re) : ℂ) := by
  simp only [complexifyLinear₄, LinearMap.comp_apply, liftStep_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Algebra.linearMap_apply, Complex.coe_algebraMap, smul_eq_mul,
    Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, one_mul]; ring

/-- Complex-multilinear extension of `r : FourTensor V` to `Complexification V`. -/
def complexify (r : FourTensor V) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 4 ↦ Complexification V) ℂ :=
  (MultilinearMap.mk' (fun m ↦ complexifyLinear₄ r (m 0) (m 1) (m 2) (m 3))
    (fun m i x y ↦ by fin_cases i <;> simp)
    (fun m i c x ↦ by fin_cases i <;> simp)).mkContinuous (16 * ‖r‖) fun m ↦ by
    simp only [MultilinearMap.mk'_apply]; rw [complexifyLinear₄_eq]
    have hI (b : Bool) : ‖if b then (Complex.I : ℂ) else 1‖ = 1 := by cases b <;> simp
    have hri (b : Bool) (z : Complexification V) : ‖if b then z.im else z.re‖ ≤ ‖z‖ := by
      cases b; exacts [Complexification.norm_re_le z, Complexification.norm_im_le z]
    have hterm (b₀ b₁ b₂ b₃ : Bool) :
        ‖(if b₀ then (Complex.I : ℂ) else 1) * (if b₁ then (Complex.I : ℂ) else 1) *
          (if b₂ then (Complex.I : ℂ) else 1) * (if b₃ then (Complex.I : ℂ) else 1) *
          (toLinearMap₄ r (if b₀ then (m 0).im else (m 0).re) (if b₁ then (m 1).im else (m 1).re)
            (if b₂ then (m 2).im else (m 2).re) (if b₃ then (m 3).im else (m 3).re) : ℂ)‖ ≤
          ‖r‖ * ∏ i, ‖m i‖ := by
      simp only [norm_mul, hI, one_mul, Complex.norm_real, toLinearMap₄_apply]
      refine (r.le_opNorm _).trans ?_
      simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      gcongr <;> exact hri _ _
    refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun b₀ _ ↦ (norm_sum_le _ _).trans <|
      (Finset.sum_le_sum fun b₁ _ ↦ (norm_sum_le _ _).trans <|
        (Finset.sum_le_sum fun b₂ _ ↦ (norm_sum_le _ _).trans <|
          Finset.sum_le_sum fun b₃ _ ↦ hterm b₀ b₁ b₂ b₃))).trans_eq ?_
    simp; ring

/-- Four-variable real/imaginary expansion of `r.complexify ![z₀, z₁, z₂, z₃]`. -/
theorem complexify_apply_four (r : FourTensor V) (z₀ z₁ z₂ z₃ : Complexification V) :
    r.complexify ![z₀, z₁, z₂, z₃] =
      ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
        (if b₀ then (Complex.I : ℂ) else 1) * (if b₁ then (Complex.I : ℂ) else 1) *
          (if b₂ then (Complex.I : ℂ) else 1) * (if b₃ then (Complex.I : ℂ) else 1) *
          (toLinearMap₄ r (if b₀ then z₀.im else z₀.re) (if b₁ then z₁.im else z₁.re)
            (if b₂ then z₂.im else z₂.re) (if b₃ then z₃.im else z₃.re) : ℂ) :=
  complexifyLinear₄_eq r z₀ z₁ z₂ z₃

/-- Expansion of `r.complexify m` into the `16`-term sum over real and imaginary parts. -/
theorem complexify_apply (r : FourTensor V) (m : Fin 4 → Complexification V) :
    r.complexify m =
      ∑ b : Fin 4 → Bool,
        (∏ j : Fin 4, if b j then (Complex.I : ℂ) else 1) *
          (r (fun j ↦ if b j then (m j).im else (m j).re) : ℂ) := by
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext j; fin_cases j <;> rfl
  rw [hm, complexify_apply_four]
  let e : (Bool × Bool × Bool × Bool) ≃ (Fin 4 → Bool) :=
    ⟨fun ⟨a, b, c, d⟩ ↦ ![a, b, c, d], fun b ↦ (b 0, b 1, b 2, b 3), fun ⟨_, _, _, _⟩ ↦ rfl,
      fun b ↦ by ext j; fin_cases j <;> rfl⟩
  rw [← e.sum_comp]; simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  have harg : (fun j : Fin 4 ↦ if ![a, b, c, d] j then (![m 0, m 1, m 2, m 3] j).im
      else (![m 0, m 1, m 2, m 3] j).re) =
      ![if a then (m 0).im else (m 0).re, if b then (m 1).im else (m 1).re,
        if c then (m 2).im else (m 2).re, if d then (m 3).im else (m 3).re] := by
    ext j; fin_cases j <;> rfl
  rw [toLinearMap₄_apply]; dsimp [e]; rw [harg, Fin.prod_univ_four]
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Complexifying the zero four-tensor gives `0`. -/
@[simp]
theorem complexify_zero : (0 : FourTensor V).complexify = 0 := by ext m; simp [complexify]

/-- Complexification of four-tensors is additive. -/
@[simp]
theorem complexify_add (r q : FourTensor V) :
    (r + q).complexify = r.complexify + q.complexify := by ext m; simp [complexify]

/-- Complexification of four-tensors is `ℝ`-homogeneous. -/
@[simp]
theorem complexify_smul (c : ℝ) (r : FourTensor V) :
    (c • r).complexify = (c : ℂ) • r.complexify := by ext m; simp [complexify, ← Complex.coe_smul]

/-- On real vectors embedded into `Complexification V`, `r.complexify` agrees with `r`. -/
@[simp]
theorem complexify_ofReal (r : FourTensor V) (u v z w : V) :
    r.complexify ![Complexification.ofReal u, Complexification.ofReal v,
      Complexification.ofReal z, Complexification.ofReal w] = (r ![u, v, z, w] : ℂ) := by
  rw [complexify_apply_four]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, Complexification.ofReal_re,
    Complexification.ofReal_im, map_zero, LinearMap.zero_apply, Complex.ofReal_zero]; simp

/-- Two-parameter isotropic-curvature expression
`r₀₂₀₂ + l² r₀₃₀₃ + m² r₁₂₁₂ + l² m² r₁₃₁₃ - 2 l m r₀₁₂₃`. -/
def pic2Expression (r : FourTensor V) (f : Fin 4 → V) (l m : ℝ) : ℝ :=
  r ![f 0, f 2, f 0, f 2] + l ^ 2 * r ![f 0, f 3, f 0, f 3] + m ^ 2 * r ![f 1, f 2, f 1, f 2] +
    l ^ 2 * m ^ 2 * r ![f 1, f 3, f 1, f 3] - 2 * l * m * r ![f 0, f 1, f 2, f 3]

/-- Defining formula for `pic2Expression`. -/
theorem pic2Expression_def (r : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression r f l m = r ![f 0, f 2, f 0, f 2] + l ^ 2 * r ![f 0, f 3, f 0, f 3] +
      m ^ 2 * r ![f 1, f 2, f 1, f 2] + l ^ 2 * m ^ 2 * r ![f 1, f 3, f 1, f 3] -
      2 * l * m * r ![f 0, f 1, f 2, f 3] := (rfl)

/-- The unit-parameter isotropic-curvature expression `pic2Expression r f 1 1`. -/
def isotropicExpression (r : FourTensor V) (f : Fin 4 → V) : ℝ := pic2Expression r f 1 1

/-- `isotropicExpression` is `pic2Expression` at `l = 1` and `m = 1`. -/
theorem isotropicExpression_def (r : FourTensor V) (f : Fin 4 → V) :
    isotropicExpression r f = pic2Expression r f 1 1 := (rfl)

/-- Explicit expansion of `isotropicExpression`. -/
theorem isotropicExpression_apply (r : FourTensor V) (f : Fin 4 → V) :
    isotropicExpression r f = r ![f 0, f 2, f 0, f 2] + r ![f 0, f 3, f 0, f 3] +
      r ![f 1, f 2, f 1, f 2] + r ![f 1, f 3, f 1, f 3] - 2 * r ![f 0, f 1, f 2, f 3] := by
  simp only [isotropicExpression_def, pic2Expression_def]; ring

/-- The zero four-tensor has zero `pic2Expression`. -/
@[simp]
theorem pic2Expression_zero (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (0 : FourTensor V) f l m = 0 := by simp [pic2Expression_def]

/-- `pic2Expression` is additive in the four-tensor. -/
@[simp]
theorem pic2Expression_add (r q : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (r + q) f l m = pic2Expression r f l m + pic2Expression q f l m := by
  simp only [pic2Expression_def, add_apply]; ring

/-- `pic2Expression` preserves subtraction in the four-tensor. -/
@[simp]
theorem pic2Expression_sub (r q : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (r - q) f l m = pic2Expression r f l m - pic2Expression q f l m := by
  simp only [pic2Expression_def, sub_apply]; ring

/-- `pic2Expression` is homogeneous in the four-tensor. -/
@[simp]
theorem pic2Expression_smul (c : ℝ) (r : FourTensor V) (f : Fin 4 → V) (l m : ℝ) :
    pic2Expression (c • r) f l m = c * pic2Expression r f l m := by
  simp only [pic2Expression_def, smul_apply, smul_eq_mul]; ring

/-- At `l = 0` and `m = 0`, `pic2Expression r f 0 0` reduces to `r ![f 0, f 2, f 0, f 2]`. -/
@[simp]
theorem pic2Expression_zero_zero (r : FourTensor V) (f : Fin 4 → V) :
    pic2Expression r f 0 0 = r ![f 0, f 2, f 0, f 2] := by simp [pic2Expression_def]

/-- Pulling `r` back along a continuous linear map `L` evaluates `pic2Expression` on `L ∘ f`. -/
@[simp]
theorem pic2Expression_compContinuousLinearMap (r : FourTensor V) (L : W →L[ℝ] V)
    (f : Fin 4 → W) (l m : ℝ) :
    pic2Expression (r.compContinuousLinearMap fun _ ↦ L) f l m = pic2Expression r (L ∘ f) l m := by
  simp only [pic2Expression_def, compContinuousLinearMap_apply_vec, Function.comp_apply]

/-- **Complexified isotropic-curvature identity.** For an algebraic curvature tensor `r`,
`r_ℂ(f₀ + i m f₁, f₂ + i l f₃, conj _, conj _) = pic2Expression r f l m`. -/
theorem IsAlgebraicCurvature.complexify_apply_conj {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (f : Fin 4 → V) (l m : ℝ) :
    r.complexify ![⟨f 0, m • f 1⟩, ⟨f 2, l • f 3⟩, Complexification.conj V ⟨f 0, m • f 1⟩,
      Complexification.conj V ⟨f 2, l • f 3⟩] = (pic2Expression r f l m : ℂ) := by
  rw [complexify_apply_four]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, Complexification.conj_re,
    Complexification.conj_im, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
    smul_eq_mul]
  simp only [toLinearMap₄_apply, Complex.ofReal_mul, Complex.ofReal_neg, pic2Expression_def,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hbianchi : (r ![f 0, f 3, f 1, f 2] : ℂ) - r ![f 0, f 2, f 1, f 3] =
      -r ![f 0, f 1, f 2, f 3] := by
    have h : r ![f 0, f 3, f 1, f 2] - r ![f 0, f 2, f 1, f 3] = -r ![f 0, f 1, f 2, f 3] := by
      linarith [hr.cyclic_eq_zero (f 0) (f 1) (f 2) (f 3),
        hr.antisymm_first (f 2) (f 0) (f 1) (f 3), hr.swap_pairs (f 1) (f 2) (f 0) (f 3)]
    exact_mod_cast h
  have hsw (a b c d : V) : (r ![a, b, c, d] : ℂ) = r ![c, d, a, b] := by
    exact_mod_cast hr.swap_pairs a b c d
  linear_combination Complex.I * (l : ℂ) * hsw (f 0) (f 3) (f 0) (f 2) +
    Complex.I * (m : ℂ) * hsw (f 1) (f 2) (f 0) (f 2) -
    Complex.I ^ 3 * (l : ℂ) ^ 2 * (m : ℂ) * hsw (f 1) (f 3) (f 0) (f 3) -
    Complex.I ^ 3 * (l : ℂ) * (m : ℂ) ^ 2 * hsw (f 1) (f 3) (f 1) (f 2) +
    Complex.I ^ 2 * (l : ℂ) * (m : ℂ) * (hsw (f 1) (f 3) (f 0) (f 2) -
      hsw (f 1) (f 2) (f 0) (f 3) - 2 * hbianchi) +
    (-((l : ℂ) ^ 2 * r ![f 0, f 3, f 0, f 3]) - (m : ℂ) ^ 2 * r ![f 1, f 2, f 1, f 2] +
      2 * (l : ℂ) * (m : ℂ) * r ![f 0, f 1, f 2, f 3]) * Complex.I_sq +
    (l : ℂ) ^ 2 * (m : ℂ) ^ 2 * r ![f 1, f 3, f 1, f 3] * Complex.I_pow_four

/-- Unit-parameter complexified isotropic-curvature identity:
`r_ℂ(f₀ + i f₁, f₂ + i f₃, conj _, conj _) = isotropicExpression r f`. -/
theorem IsAlgebraicCurvature.complexify_apply_conj_one {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (f : Fin 4 → V) :
    r.complexify ![⟨f 0, f 1⟩, ⟨f 2, f 3⟩, Complexification.conj V ⟨f 0, f 1⟩,
      Complexification.conj V ⟨f 2, f 3⟩] = (isotropicExpression r f : ℂ) := by
  simpa only [one_smul, isotropicExpression_def] using hr.complexify_apply_conj f 1 1

end NormedSpace

/-! ### The real four-frame PIC and PIC2 cones -/

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Nonnegative isotropic curvature in real four-frame form (vacuous when no orthonormal
four-frame exists). -/
def IsPICFourFrame (r : FourTensor V) : Prop :=
  ∀ f : Fin 4 → V, Orthonormal ℝ f → 0 ≤ isotropicExpression r f

/-- Unfolding characterization of `IsPICFourFrame`. -/
theorem isPICFourFrame_def (r : FourTensor V) :
    IsPICFourFrame r ↔ ∀ f : Fin 4 → V, Orthonormal ℝ f → 0 ≤ isotropicExpression r f := Iff.rfl

/-- Real four-frame `PIC2`: `pic2Expression r f l m ≥ 0` on orthonormal four-frames `f` and
`l, m ∈ [-1, 1]` (vacuous when no orthonormal four-frame exists). -/
def IsPIC2FourFrame (r : FourTensor V) : Prop :=
  ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
    ∀ m ∈ Icc (-1 : ℝ) 1, 0 ≤ pic2Expression r f l m

/-- Unfolding characterization of `IsPIC2FourFrame`. -/
theorem isPIC2FourFrame_def (r : FourTensor V) :
    IsPIC2FourFrame r ↔ ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, 0 ≤ pic2Expression r f l m := Iff.rfl

/-- `PIC2` implies `PIC` in the real four-frame formulation (`l = m = 1`). -/
theorem IsPIC2FourFrame.isPICFourFrame {r : FourTensor V} (hr : IsPIC2FourFrame r) :
    IsPICFourFrame r := fun f hf ↦ hr f hf 1 (by norm_num) 1 (by norm_num)

/-- The zero four-tensor satisfies `IsPICFourFrame`. -/
@[simp]
theorem isPICFourFrame_zero : IsPICFourFrame (0 : FourTensor V) :=
  fun _ _ ↦ by simp [isotropicExpression_def]

/-- The zero four-tensor satisfies `IsPIC2FourFrame`. -/
@[simp]
theorem isPIC2FourFrame_zero : IsPIC2FourFrame (0 : FourTensor V) := fun _ _ _ _ _ _ ↦ by simp

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

/-- The `ε`-superlevel set of `pic2Expression` is convex in `FourTensor V`. -/
theorem convex_setOf_le_pic2Expression (ε : ℝ) :
    Convex ℝ {r : FourTensor V | ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m} :=
  fun _ h₁ _ h₂ a b ha hb hab f hf l hl m hm ↦ by
    rw [pic2Expression_add, pic2Expression_smul, pic2Expression_smul]
    have hε : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left (h₁ f hf l hl m hm) ha,
      mul_le_mul_of_nonneg_left (h₂ f hf l hl m hm) hb]

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
  have heval (i₀ i₁ i₂ i₃ : Fin 4) : Continuous fun p : FourTensor V × (Fin 4 → V) × ℝ × ℝ ↦
      p.1 ![p.2.1 i₀, p.2.1 i₁, p.2.1 i₂, p.2.1 i₃] := by
    have hvec : Continuous fun p : FourTensor V × (Fin 4 → V) × ℝ × ℝ ↦
        ![p.2.1 i₀, p.2.1 i₁, p.2.1 i₂, p.2.1 i₃] :=
      continuous_pi fun k ↦ by fin_cases k <;> dsimp <;> fun_prop
    exact continuous_eval.comp (continuous_fst.prodMk hvec)
  simp only [pic2Expression_def]; fun_prop

/-- The `ε`-superlevel set of `pic2Expression` is closed in `FourTensor V`. -/
theorem isClosed_setOf_le_pic2Expression (ε : ℝ) :
    IsClosed {r : FourTensor V | ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m} := by
  convert isClosed_iInter fun f : {f : Fin 4 → V // Orthonormal ℝ f} ↦
    isClosed_iInter fun l : Icc (-1 : ℝ) 1 ↦ isClosed_iInter fun m : Icc (-1 : ℝ) 1 ↦
      isClosed_le (continuous_const (y := ε))
        (continuous_pic2Expression.comp (Continuous.prodMk_left (f.1, l.1, m.1))) using 1
  ext r; simp only [mem_ofPred_eq, mem_iInter, Subtype.forall, Function.comp_apply]

/-- The `PIC2` four-frame cone is closed in `FourTensor V`. -/
theorem isClosed_setOf_isPIC2FourFrame : IsClosed {r : FourTensor V | IsPIC2FourFrame r} :=
  isClosed_setOf_le_pic2Expression 0

/-- The `PIC` four-frame cone is closed in `FourTensor V`. -/
theorem isClosed_setOf_isPICFourFrame : IsClosed {r : FourTensor V | IsPICFourFrame r} := by
  convert isClosed_iInter fun f : {f : Fin 4 → V // Orthonormal ℝ f} ↦
    isClosed_le (continuous_const (y := (0 : ℝ)))
      (continuous_pic2Expression.comp (Continuous.prodMk_left (f.1, 1, 1))) using 1
  ext r; simp only [mem_ofPred_eq, IsPICFourFrame, isotropicExpression_def, mem_iInter,
    Subtype.forall, Function.comp_apply]

/-- Pulling back along a linear isometry preserves `IsPIC2FourFrame`. -/
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
    IsPIC2FourFrame (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) ↔ IsPIC2FourFrame r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compContinuousLinearMap_linearIsometry e.toLinearIsometry⟩
  convert h.compContinuousLinearMap_linearIsometry e.symm.toLinearIsometry using 1; ext m; simp

/-- Linear isometric equivalences preserve and reflect `IsPICFourFrame`. -/
@[simp]
theorem isPICFourFrame_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    {r : FourTensor V} :
    IsPICFourFrame (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) ↔ IsPICFourFrame r := by
  refine ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · simpa [isotropicExpression_def, pic2Expression_compContinuousLinearMap, Function.comp_def]
      using h (e.symm ∘ f) (e.symm.toLinearIsometry.orthonormal_comp_iff.2 hf)
  · rw [isotropicExpression_def, pic2Expression_compContinuousLinearMap]
    exact h (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf)

/-- `algebraicCurvatureLinearIsometryEquiv e` preserves and reflects `interior PIC2`. -/
@[simp]
theorem algebraicCurvatureLinearIsometryEquiv_mem_interior_isPIC2FourFrame_iff (e : W ≃ₗᵢ[ℝ] V)
    {r : algebraicCurvatureSubmodule V} :
    algebraicCurvatureLinearIsometryEquiv e r ∈
        interior {q : algebraicCurvatureSubmodule W | IsPIC2FourFrame q.1} ↔
      r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  let φ := (algebraicCurvatureLinearIsometryEquiv e).toHomeomorph
  have hpre : φ ⁻¹' {q : algebraicCurvatureSubmodule W | IsPIC2FourFrame q.1} =
      {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by ext q; simp [φ]
  rw [← hpre, ← φ.preimage_interior]; rfl

/-- Bound `|pic2Expression r f l m| ≤ 6 * ‖r‖` on orthonormal four-frames and `l, m ∈ [-1, 1]`. -/
theorem abs_pic2Expression_le_six_mul_norm (r : FourTensor V) {f : Fin 4 → V}
    (hf : Orthonormal ℝ f) {l m : ℝ} (hl : l ∈ Icc (-1 : ℝ) 1) (hm : m ∈ Icc (-1 : ℝ) 1) :
    |pic2Expression r f l m| ≤ 6 * ‖r‖ := by
  have he (i₀ i₁ i₂ i₃ : Fin 4) : |r ![f i₀, f i₁, f i₂, f i₃]| ≤ ‖r‖ :=
    abs_apply_le_norm_of_norm_eq_one r (hf.1 i₀) (hf.1 i₁) (hf.1 i₂) (hf.1 i₃)
  have hl1 : |l| ≤ 1 := abs_le.2 hl; have hm1 : |m| ≤ 1 := abs_le.2 hm
  have hsc {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ ‖r‖) : -‖r‖ ≤ a * b ∧ a * b ≤ ‖r‖ :=
    abs_le.1 <| by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
  have hmul {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg y]
  have hsq {x : ℝ} (hx : |x| ≤ 1) : |x ^ 2| ≤ 1 := by rw [sq]; exact hmul hx hx
  have h1 := abs_le.1 (he 0 2 0 2); have h2 := hsc (hsq hl1) (he 0 3 0 3)
  have h3 := hsc (hsq hm1) (he 1 2 1 2)
  have h4 := hsc (hmul (hsq hl1) (hsq hm1)) (he 1 3 1 3)
  have h5 := hsc (hmul hl1 hm1) (he 0 1 2 3)
  rw [pic2Expression_def, abs_le]; exact ⟨by linarith, by linarith⟩

/-- Infimum of `pic2Expression r f l m` over orthonormal four-frames `f` and `l, m ∈ [-1, 1]`. -/
def pic2Min (r : FourTensor V) : ℝ :=
  sInf ((fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2) ''
    ({f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))

/-- Defining formula for `pic2Min`. -/
theorem pic2Min_def (r : FourTensor V) :
    pic2Min r = sInf ((fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2) ''
      ({f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) := (rfl)

private theorem bddBelow_pic2Image (r : FourTensor V) :
    BddBelow ((fun p : (Fin 4 → V) × ℝ × ℝ ↦ pic2Expression r p.1 p.2.1 p.2.2) ''
      ({f : Fin 4 → V | Orthonormal ℝ f} ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) :=
  ⟨-(6 * ‖r‖), fun _ ⟨⟨_, _, _⟩, ⟨hf, hl, hm⟩, h⟩ ↦ h ▸ neg_le_of_abs_le
    (abs_pic2Expression_le_six_mul_norm r hf hl hm)⟩

/-- `pic2Min r` bounds `pic2Expression r f l m` below on orthonormal four-frames and `[-1, 1]`. -/
theorem pic2Min_le_pic2Expression (r : FourTensor V) {f : Fin 4 → V} (hf : Orthonormal ℝ f)
    {l m : ℝ} (hl : l ∈ Icc (-1 : ℝ) 1) (hm : m ∈ Icc (-1 : ℝ) 1) :
    pic2Min r ≤ pic2Expression r f l m :=
  csInf_le (bddBelow_pic2Image r) ⟨(f, l, m), ⟨hf, hl, hm⟩, rfl⟩

/-- A uniform lower bound on `pic2Expression` bounds `pic2Min r` below when four-frames exist. -/
theorem le_pic2Min_of_forall_le {r : FourTensor V} {c : ℝ}
    (hne : {f : Fin 4 → V | Orthonormal ℝ f}.Nonempty)
    (hc : ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, c ≤ pic2Expression r f l m) : c ≤ pic2Min r :=
  let ⟨f₀, hf₀⟩ := hne
  le_csInf ⟨_, ⟨(f₀, 0, 0), ⟨hf₀, by norm_num, by norm_num⟩, rfl⟩⟩
    fun _ ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, h⟩ ↦ h ▸ hc f hf l hl m hm

/-- `pic2Min` is `6`-Lipschitz on `FourTensor V`. -/
theorem lipschitzWith_pic2Min : LipschitzWith 6 (pic2Min (V := V)) :=
  TauCeti.lipschitzWith_sInf_image bddBelow_pic2Image fun ⟨_, _, _⟩ ⟨hf, hl, hm⟩ ↦
    LipschitzWith.of_dist_le_mul fun r q ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat, ← pic2Expression_sub] using
        abs_pic2Expression_le_six_mul_norm (r - q) hf hl hm

/-- `pic2Min` is continuous on `FourTensor V`. -/
theorem continuous_pic2Min : Continuous (pic2Min (V := V)) := lipschitzWith_pic2Min.continuous

/-- `pic2Min` is invariant under pullback by linear isometric equivalences. -/
@[simp]
theorem pic2Min_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    pic2Min (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) = pic2Min r := by
  rw [pic2Min_def, pic2Min_def]; congr 1; ext y; constructor
  · rintro ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, rfl⟩
    exact ⟨(e ∘ f, l, m), ⟨e.toLinearIsometry.orthonormal_comp_iff.2 hf, hl, hm⟩,
      (pic2Expression_compContinuousLinearMap r (e : W →L[ℝ] V) f l m).symm⟩
  · rintro ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, rfl⟩
    exact ⟨(e.symm ∘ f, l, m), ⟨e.symm.toLinearIsometry.orthonormal_comp_iff.2 hf, hl, hm⟩, by
      dsimp only; rw [pic2Expression_compContinuousLinearMap]; congr 2; funext i; simp⟩

/-- A uniform margin `ε > 0` below `pic2Expression r.1` places `r` in `interior PIC2`. -/
theorem mem_interior_isPIC2FourFrame_of_exists_pos_le {r : algebraicCurvatureSubmodule V}
    {ε : ℝ} (hε : 0 < ε)
    (hle : ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r.1 f l m) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε / 6, by positivity, fun {q} hq f hf l hl m hm ↦ ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hq
  have hdiff := abs_pic2Expression_le_six_mul_norm (q.1 - r.1) hf hl hm
  rw [pic2Expression_sub, abs_le] at hdiff; linarith [hle f hf l hl m hm]

end InnerProductSpace

/-! ### Finite-dimensional consequences: constant curvature and interior of PIC2 -/

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- On an orthonormal four-frame `f`, `pic2Expression (constantCurvature V) f l m = (1+l²)(1+m²)`.
-/
@[simp]
theorem pic2Expression_constantCurvature {f : Fin 4 → V} (hf : Orthonormal ℝ f) (l m : ℝ) :
    pic2Expression (constantCurvature V) f l m = (1 + l ^ 2) * (1 + m ^ 2) := by
  have hd (i j : Fin 4) (hij : i ≠ j) : constantCurvature V ![f i, f j, f i, f j] = 1 := by
    rw [constantCurvature_apply_self, hf.1 i, hf.1 j, hf.2 hij]; ring
  rw [pic2Expression_def, hd 0 2 (by decide), hd 0 3 (by decide), hd 1 2 (by decide),
    hd 1 3 (by decide), constantCurvature_apply, hf.2 (by decide : (0 : Fin 4) ≠ 2),
    hf.2 (by decide : (0 : Fin 4) ≠ 3)]; ring

/-- On an orthonormal four-frame `f`, `constantCurvature V` has `isotropicExpression` `4`. -/
@[simp]
theorem isotropicExpression_constantCurvature {f : Fin 4 → V} (hf : Orthonormal ℝ f) :
    isotropicExpression (constantCurvature V) f = 4 := by
  rw [isotropicExpression_def, pic2Expression_constantCurvature hf]; norm_num

/-- Every nonnegative multiple of `constantCurvature V` lies in `IsPIC2FourFrame`. -/
theorem isPIC2FourFrame_smul_constantCurvature {κ : ℝ} (hκ : 0 ≤ κ) :
    IsPIC2FourFrame (κ • constantCurvature V) := fun _ hf _ _ _ _ ↦ by
  rw [pic2Expression_smul, pic2Expression_constantCurvature hf]; positivity

/-- In dimension `≥ 4`, `κ • constantCurvature V` lies in `IsPIC2FourFrame` iff `0 ≤ κ`. -/
theorem isPIC2FourFrame_smul_constantCurvature_iff (hn : 4 ≤ Module.finrank ℝ V) {κ : ℝ} :
    IsPIC2FourFrame (κ • constantCurvature V) ↔ 0 ≤ κ := by
  refine ⟨fun h ↦ ?_, isPIC2FourFrame_smul_constantCurvature⟩
  obtain ⟨f, hf⟩ :=
    (TauCeti.nonempty_setOfPred_orthonormal_iff (ι := Fin 4) (E := V)).2 (by simpa using hn)
  have h0 := h f hf 0 (by norm_num) 0 (by norm_num)
  rw [pic2Expression_smul, pic2Expression_constantCurvature hf] at h0; linarith

/-- In dimension `≥ 4`, `pic2Min r` is attained on an orthonormal four-frame and `l, m ∈ [-1, 1]`.
-/
theorem exists_orthonormal_eq_pic2Min (hn : 4 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ∃ (f : Fin 4 → V) (l m : ℝ), Orthonormal ℝ f ∧ l ∈ Icc (-1 : ℝ) 1 ∧ m ∈ Icc (-1 : ℝ) 1 ∧
      pic2Expression r f l m = pic2Min r := by
  obtain ⟨f₀, hf₀⟩ :=
    (TauCeti.nonempty_setOfPred_orthonormal_iff (ι := Fin 4) (E := V)).2 (by simpa using hn)
  obtain ⟨⟨f, l, m⟩, ⟨hf, hl, hm⟩, hmin⟩ := (TauCeti.isCompact_setOfPred_orthonormal.prod
      ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
        (isCompact_Icc (a := (-1 : ℝ)) (b := 1)))).exists_isMinOn
    ⟨(f₀, 0, 0), hf₀, by norm_num, by norm_num⟩
    (continuous_pic2Expression.comp (Continuous.prodMk_right r)).continuousOn
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
    have := hf.linearIndependent.fintype_card_le_finrank; rw [Fintype.card_fin] at this; omega

/-- In finite dimensions, `r ∈ interior PIC2` iff `0 < pic2Expression r.1 f l m` on all orthonormal
four-frames and `l, m ∈ [-1, 1]`. -/
theorem mem_interior_isPIC2FourFrame_iff_forall_pos {r : algebraicCurvatureSubmodule V} :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} ↔
      ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
        ∀ m ∈ Icc (-1 : ℝ) 1, 0 < pic2Expression r.1 f l m := by
  refine ⟨fun hint f hf l hl m hm ↦ ?_, fun hpos ↦ ?_⟩
  · obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    let I₀ : algebraicCurvatureSubmodule V := ⟨constantCurvature V,
      mem_algebraicCurvatureSubmodule.2 isAlgebraicCurvature_constantCurvature⟩
    set t : ℝ := δ / (2 * (‖I₀.1‖ + 1)); have ht : 0 < t := by positivity
    have hdist : dist (r - t • I₀) r < δ := by
      rw [Subtype.dist_eq, dist_eq_norm, Submodule.coe_sub, Submodule.coe_smul_of_tower,
        sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.le]
      exact (div_mul_eq_mul_div _ _ _).trans_lt <| (div_lt_iff₀ (by positivity)).2 <| by
        nlinarith [norm_nonneg I₀.1]
    have hval := hball hdist f hf l hl m hm
    simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, I₀, pic2Expression_sub,
      pic2Expression_smul, pic2Expression_constantCurvature hf] at hval
    have hprod : 1 ≤ (1 + l ^ 2) * (1 + m ^ 2) := by nlinarith [sq_nonneg l, sq_nonneg m]
    nlinarith
  · obtain ⟨ε, hε, hle⟩ := exists_pos_le_pic2Expression_of_forall_pos hpos
    exact mem_interior_isPIC2FourFrame_of_exists_pos_le hε hle

/-- In finite dimensions, `r ∈ interior PIC2` iff a uniform margin `ε > 0` bounds
`pic2Expression r.1` below. -/
theorem mem_interior_isPIC2FourFrame_iff_exists_pos_le {r : algebraicCurvatureSubmodule V} :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} ↔
      ∃ ε > 0, ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
        ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r.1 f l m :=
  ⟨fun hint ↦ exists_pos_le_pic2Expression_of_forall_pos
    (mem_interior_isPIC2FourFrame_iff_forall_pos.1 hint),
    fun ⟨_, hε, hle⟩ ↦ mem_interior_isPIC2FourFrame_of_exists_pos_le hε hle⟩

/-- Every positive multiple of `constantCurvature V` lies in `interior PIC2`. -/
theorem smul_constantCurvature_mem_interior_isPIC2FourFrame {κ : ℝ} (hκ : 0 < κ) :
    (⟨κ • constantCurvature V, Submodule.smul_mem _ κ (mem_algebraicCurvatureSubmodule.2
      isAlgebraicCurvature_constantCurvature)⟩ : algebraicCurvatureSubmodule V) ∈
      interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} :=
  mem_interior_isPIC2FourFrame_iff_forall_pos.2 fun _ hf _ _ _ _ ↦ by
    rw [pic2Expression_smul, pic2Expression_constantCurvature hf]; positivity

/-- In dimension `≥ 4`, `r ∈ interior {q | IsPIC2FourFrame q.1}` iff `0 < pic2Min r.1`. -/
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
