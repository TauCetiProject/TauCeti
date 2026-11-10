/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# Nondegenerate critical points of separated sums

A *separated sum* `φ ∘ Prod.fst + ψ ∘ Prod.snd` on a product `E × F` has block-diagonal second
derivative, so its Hessian quadratic form at `(a, b)` is the orthogonal product of the Hessians of
`φ` at `a` and of `ψ` at `b`. Consequently `(a, b)` is a nondegenerate critical point of the sum
exactly when `a` and `b` are nondegenerate critical points of the summands, and the Morse index
is additive. This is the calculus behind the product of two Morse functions on a product manifold,
whose critical points are the pairs of critical points, graded by the sum of the indices.

For real functions `f` and `g` on inner product spaces, `TauCeti.separatedSum f g` is the separated
sum on the `L²` product `WithLp 2 (E × F)`, whose inner product makes the gradient of the sum the
pair of gradients. The results above transfer to it through
`WithLp.prodContinuousLinearEquiv`.

## Main declarations

* `TauCeti.hessianQuadraticForm_comp_fst_add_comp_snd`: the Hessian of a separated sum is the
  product of the Hessians of the summands.
* `TauCeti.isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff` and
  `TauCeti.IsNondegenerateCriticalPoint.comp_fst_add_comp_snd`: nondegenerate critical points of
  a separated sum are the pairs of nondegenerate critical points of the summands.
* `TauCeti.morseIndex_comp_fst_add_comp_snd`: the Morse index of a separated sum is the sum of
  the Morse indices of the summands.
* `TauCeti.separatedSum`: the separated sum on the `L²` product.
* `TauCeti.gradient_separatedSum` and `TauCeti.lipschitzWith_gradient_separatedSum`: its gradient is
  the pair of gradients, and is Lipschitz when both gradients are.
* `IsIntegralCurve.separatedSum`: pairs of negative gradient trajectories of the summands are
  negative gradient trajectories of the separated sum.
* `TauCeti.isNondegenerateCriticalPoint_separatedSum_iff` and `TauCeti.morseIndex_separatedSum`:
  its nondegenerate critical points are the pairs of nondegenerate critical points, with additive
  Morse index.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1 (sums of Morse functions on products).
-/

public section

open ContinuousLinearMap

namespace TauCeti

section CompFstAddCompSnd

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → ℝ} {ψ : F → ℝ} {a : E} {b : F}

/-- The Hessian quadratic form of a separated sum at `(a, b)` is the orthogonal product of the
Hessians of the summands at `a` and `b`. -/
@[simp]
theorem hessianQuadraticForm_comp_fst_add_comp_snd (hφ : ContDiffAt ℝ 2 φ a)
    (hψ : ContDiffAt ℝ 2 ψ b) :
    hessianQuadraticForm (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) =
      (hessianQuadraticForm φ a).prod (hessianQuadraticForm ψ b) := by
  ext ⟨v, w⟩
  rw [hessianQuadraticForm_apply, fderiv_fderiv_comp_fst_add_comp_snd hφ hψ,
    QuadraticMap.prod_apply, hessianQuadraticForm_apply, hessianQuadraticForm_apply]
  simp [coprodEquivL_apply_apply]

/-- **Nondegenerate critical points of a separated sum.** The separated sum
`φ ∘ Prod.fst + ψ ∘ Prod.snd` has a nondegenerate critical point at `(a, b)` exactly when `φ` has
one at `a` and `ψ` has one at `b`. -/
@[simp]
theorem isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff :
    IsNondegenerateCriticalPoint (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) ↔
      IsNondegenerateCriticalPoint φ a ∧ IsNondegenerateCriticalPoint ψ b := by
  by_cases hc : ContDiffAt ℝ 2 φ a ∧ ContDiffAt ℝ 2 ψ b
  · obtain ⟨hφ, hψ⟩ := hc
    have hcrit := fderiv_comp_fst_add_comp_snd_eq_zero_iff (hφ.differentiableAt two_ne_zero)
      (hψ.differentiableAt two_ne_zero)
    have hsnd := fderiv_fderiv_comp_fst_add_comp_snd hφ hψ
    constructor
    · intro h
      have hinv := h.isInvertible
      rw [hsnd, isInvertible_equiv_comp, isInvertible_prodMap_iff] at hinv
      exact ⟨⟨hφ, (hcrit.1 h.fderiv_eq_zero).1, hinv.1⟩,
        ⟨hψ, (hcrit.1 h.fderiv_eq_zero).2, hinv.2⟩⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨(hφ.comp _ contDiffAt_fst).add (hψ.comp _ contDiffAt_snd),
        hcrit.2 ⟨h₁.fderiv_eq_zero, h₂.fderiv_eq_zero⟩, ?_⟩
      rw [hsnd, isInvertible_equiv_comp, isInvertible_prodMap_iff]
      exact ⟨h₁.isInvertible, h₂.isInvertible⟩
  · refine iff_of_false (fun h ↦ hc ?_) fun h ↦ hc ⟨h.1.contDiffAt, h.2.contDiffAt⟩
    have hφ : ContDiffAt ℝ 2 (fun x ↦ φ x + ψ b) a :=
      h.contDiffAt.comp (f := fun x : E ↦ (x, b)) a (by fun_prop)
    have hψ : ContDiffAt ℝ 2 (fun y ↦ φ a + ψ y) b :=
      h.contDiffAt.comp (f := fun y : F ↦ (a, y)) b (by fun_prop)
    exact ⟨by simpa using hφ.sub (contDiffAt_const (c := ψ b)),
      by simpa using hψ.sub (contDiffAt_const (c := φ a))⟩

/-- A pair of nondegenerate critical points of `φ` and `ψ` is a nondegenerate critical point of
the separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd`. -/
theorem IsNondegenerateCriticalPoint.comp_fst_add_comp_snd (hφ : IsNondegenerateCriticalPoint φ a)
    (hψ : IsNondegenerateCriticalPoint ψ b) :
    IsNondegenerateCriticalPoint (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) :=
  isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff.2 ⟨hφ, hψ⟩

/-- **The Morse index of a separated sum is additive**: for `φ` twice continuously differentiable
at `a` and `ψ` twice continuously differentiable at `b`, the index of `φ ∘ Prod.fst + ψ ∘ Prod.snd`
at `(a, b)` is the sum of the indices of `φ` at `a` and of `ψ` at `b`. -/
@[simp]
theorem morseIndex_comp_fst_add_comp_snd [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hφ : ContDiffAt ℝ 2 φ a) (hψ : ContDiffAt ℝ 2 ψ b) :
    morseIndex (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) = morseIndex φ a + morseIndex ψ b := by
  simp only [morseIndex_def, hessianQuadraticForm_comp_fst_add_comp_snd hφ hψ,
    QuadraticForm.sigNeg_prod]

end CompFstAddCompSnd

section SeparatedSum

open Set
open scoped Gradient NNReal

section Defs

variable {E F : Type*} {f : E → ℝ} {g : F → ℝ}

/-- The **separated sum** `(x, y) ↦ f x + g y` of two real functions, on the `L²` product of their
domains. -/
def separatedSum (f : E → ℝ) (g : F → ℝ) (z : WithLp 2 (E × F)) : ℝ :=
  f z.fst + g z.snd

@[simp]
theorem separatedSum_apply (z : WithLp 2 (E × F)) : separatedSum f g z = f z.fst + g z.snd :=
  (rfl)

end Defs

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E → ℝ} {g : F → ℝ}

/-- The separated sum is the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on the plain product, read
through the identification of the `L²` product with it. -/
theorem separatedSum_eq_comp :
    separatedSum f g =
      (f ∘ Prod.fst + g ∘ Prod.snd) ∘ WithLp.prodContinuousLinearEquiv 2 ℝ E F :=
  (rfl)

/-- A separated sum of `Cⁿ` functions is `Cⁿ`. -/
theorem _root_.ContDiff.separatedSum {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (separatedSum f g) := by
  rw [separatedSum_eq_comp]
  exact ((hf.comp contDiff_fst).add (hg.comp contDiff_snd)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).contDiff

section Gradient

variable [CompleteSpace E] [CompleteSpace F]

/-- **The gradient of a separated sum is the pair of gradients.** -/
theorem hasGradientAt_separatedSum {z : WithLp 2 (E × F)} (hf : DifferentiableAt ℝ f z.fst)
    (hg : DifferentiableAt ℝ g z.snd) :
    HasGradientAt (separatedSum f g) (WithLp.toLp 2 (∇ f z.fst, ∇ g z.snd)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hF := hf.hasGradientAt.hasFDerivAt.comp z (WithLp.fstL 2 ℝ E F).hasFDerivAt
  have hG := hg.hasGradientAt.hasFDerivAt.comp z (WithLp.sndL 2 ℝ E F).hasFDerivAt
  refine (hF.add hG).congr_fderiv ?_
  ext w
  simp [WithLp.prod_inner_apply]

/-- **The gradient of a separated sum is the pair of gradients.** -/
theorem gradient_separatedSum {z : WithLp 2 (E × F)} (hf : DifferentiableAt ℝ f z.fst)
    (hg : DifferentiableAt ℝ g z.snd) :
    ∇ (separatedSum f g) z = WithLp.toLp 2 (∇ f z.fst, ∇ g z.snd) :=
  (hasGradientAt_separatedSum hf hg).gradient

/-- The gradient of a separated sum is Lipschitz, with the larger of the two constants, when both
gradients are. -/
theorem lipschitzWith_gradient_separatedSum {K K' : ℝ≥0} (hfd : Differentiable ℝ f)
    (hgd : Differentiable ℝ g) (hf : LipschitzWith K (∇ f)) (hg : LipschitzWith K' (∇ g)) :
    LipschitzWith (max K K') (∇ (separatedSum f g)) := by
  refine LipschitzWith.of_dist_le_mul fun z w ↦ ?_
  rw [gradient_separatedSum (hfd _) (hgd _), gradient_separatedSum (hfd _) (hgd _),
    WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  have h₁ : dist (∇ f z.fst) (∇ f w.fst) ≤ max K K' * dist z.fst w.fst :=
    (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_right (by simp) dist_nonneg)
  have h₂ : dist (∇ g z.snd) (∇ g w.snd) ≤ max K K' * dist z.snd w.snd :=
    (hg.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_right (by simp) dist_nonneg)
  rw [show ((max K K' : ℝ≥0) : ℝ) * √(dist z.fst w.fst ^ 2 + dist z.snd w.snd ^ 2) =
      √(((max K K' : ℝ≥0) : ℝ) ^ 2 * (dist z.fst w.fst ^ 2 + dist z.snd w.snd ^ 2)) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [pow_le_pow_left₀ dist_nonneg h₁ 2, pow_le_pow_left₀ dist_nonneg h₂ 2]

/-- **Negative gradient trajectories of a separated sum.** If `γ₁` and `γ₂` are negative gradient
trajectories of `f` and `g`, then the pair `s ↦ (γ₁ s, γ₂ s)` is a negative gradient trajectory of
`separatedSum f g`. -/
theorem _root_.IsIntegralCurve.separatedSum {γ₁ : ℝ → E} {γ₂ : ℝ → F}
    (h₁ : IsIntegralCurve γ₁ fun _ x ↦ -∇ f x) (h₂ : IsIntegralCurve γ₂ fun _ y ↦ -∇ g y)
    (hf : ∀ s, DifferentiableAt ℝ f (γ₁ s)) (hg : ∀ s, DifferentiableAt ℝ g (γ₂ s)) :
    IsIntegralCurve (fun s ↦ WithLp.toLp 2 (γ₁ s, γ₂ s)) fun _ z ↦ -∇ (separatedSum f g) z := by
  intro s
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.hasFDerivAt.comp_hasDerivAt s
    ((h₁ s).prodMk (h₂ s))
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply] at h
  refine h.congr_deriv ?_
  dsimp only
  rw [gradient_separatedSum (z := WithLp.toLp 2 (γ₁ s, γ₂ s)) (hf s) (hg s), WithLp.toLp_fst,
    WithLp.toLp_snd, ← Prod.neg_mk, WithLp.toLp_neg]

end Gradient

section Critical

/-- **Nondegenerate critical points of a separated sum** are the pairs of nondegenerate critical
points of the summands. -/
theorem isNondegenerateCriticalPoint_separatedSum_iff {z : WithLp 2 (E × F)}
    (hf : ContDiffAt ℝ 2 f z.fst) (hg : ContDiffAt ℝ 2 g z.snd) :
    IsNondegenerateCriticalPoint (separatedSum f g) z ↔
      IsNondegenerateCriticalPoint f z.fst ∧ IsNondegenerateCriticalPoint g z.snd := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  have hsum : ContDiffAt ℝ 2 (f ∘ Prod.fst + g ∘ Prod.snd) (e z) :=
    (ContDiffAt.comp (e z) hf contDiffAt_fst).add (ContDiffAt.comp (e z) hg contDiffAt_snd)
  rw [separatedSum_eq_comp, isNondegenerateCriticalPoint_comp_iff hsum e.contDiff.contDiffAt
    (by rw [e.fderiv]; exact ⟨e, rfl⟩)]
  exact isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff

/-- A pair of nondegenerate critical points is a nondegenerate critical point of the separated
sum. -/
theorem IsNondegenerateCriticalPoint.separatedSum {x : E} {y : F}
    (hx : IsNondegenerateCriticalPoint f x) (hy : IsNondegenerateCriticalPoint g y) :
    IsNondegenerateCriticalPoint (separatedSum f g) (WithLp.toLp 2 (x, y)) :=
  (isNondegenerateCriticalPoint_separatedSum_iff (z := WithLp.toLp 2 (x, y)) hx.contDiffAt
    hy.contDiffAt).2 ⟨hx, hy⟩

/-- **Critical points of a separated sum** are the pairs of critical points of the summands. -/
theorem fderiv_separatedSum_eq_zero_iff {z : WithLp 2 (E × F)} (hf : DifferentiableAt ℝ f z.fst)
    (hg : DifferentiableAt ℝ g z.snd) :
    fderiv ℝ (separatedSum f g) z = 0 ↔ fderiv ℝ f z.fst = 0 ∧ fderiv ℝ g z.snd = 0 := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  rw [separatedSum_eq_comp, fderiv_comp_eq_zero_iff_of_isInvertible
    ((DifferentiableAt.comp (e z) hf differentiableAt_fst).add
      (DifferentiableAt.comp (e z) hg differentiableAt_snd))
    (by rw [e.fderiv]; exact ⟨e, rfl⟩)]
  exact fderiv_comp_fst_add_comp_snd_eq_zero_iff hf hg

/-- A separated sum of functions with nondegenerate critical points has nondegenerate critical
points. -/
theorem HasNondegenerateCriticalPointsOn.separatedSum
    (hf : HasNondegenerateCriticalPointsOn f univ)
    (hg : HasNondegenerateCriticalPointsOn g univ) :
    HasNondegenerateCriticalPointsOn (separatedSum f g) univ := by
  refine hasNondegenerateCriticalPointsOn_iff.2 fun z _ hz ↦ ?_
  have hdf : DifferentiableAt ℝ f z.fst := by
    by_contra h
    exact h ((hasNondegenerateCriticalPointsOn_iff.1 hf (mem_univ _)
      (fderiv_zero_of_not_differentiableAt h)).contDiffAt.differentiableAt two_ne_zero)
  have hdg : DifferentiableAt ℝ g z.snd := by
    by_contra h
    exact h ((hasNondegenerateCriticalPointsOn_iff.1 hg (mem_univ _)
      (fderiv_zero_of_not_differentiableAt h)).contDiffAt.differentiableAt two_ne_zero)
  obtain ⟨h₁, h₂⟩ := (fderiv_separatedSum_eq_zero_iff hdf hdg).1 hz
  have hf' := hasNondegenerateCriticalPointsOn_iff.1 hf (mem_univ _) h₁
  have hg' := hasNondegenerateCriticalPointsOn_iff.1 hg (mem_univ _) h₂
  exact (isNondegenerateCriticalPoint_separatedSum_iff hf'.contDiffAt hg'.contDiffAt).2
    ⟨hf', hg'⟩

/-- **The Morse index of a separated sum is additive.** -/
theorem morseIndex_separatedSum [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {z : WithLp 2 (E × F)} (hf : ContDiffAt ℝ 2 f z.fst) (hg : ContDiffAt ℝ 2 g z.snd) :
    morseIndex (separatedSum f g) z = morseIndex f z.fst + morseIndex g z.snd := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  have hsum : ContDiffAt ℝ 2 (f ∘ Prod.fst + g ∘ Prod.snd) (e z) :=
    (ContDiffAt.comp (e z) hf contDiffAt_fst).add (ContDiffAt.comp (e z) hg contDiffAt_snd)
  -- The change of coordinates is linear, so the Hessian pulls back without a criticality
  -- hypothesis.
  have hH := (e : WithLp 2 (E × F) →L[ℝ] E × F).hessianQuadraticForm_comp hsum
  simp only [ContinuousLinearEquiv.coe_coe] at hH
  rw [separatedSum_eq_comp, morseIndex_def, hH, ← morseIndex_comp_fst_add_comp_snd hf hg,
    morseIndex_def]
  exact (QuadraticMap.Equivalent.sigNeg_eq
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv _ e.toLinearEquiv⟩).symm

end Critical

end SeparatedSum

end TauCeti

end
