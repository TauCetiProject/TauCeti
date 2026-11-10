/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The rough Laplacian of a connection

Let `∇` be a connection on a vector bundle `V` over a Riemannian manifold `M`, and `∇ᵀ` a
connection on the tangent bundle. The **rough Laplacian** (or connection Laplacian, Bochner
Laplacian) of a smooth section `σ` is the negative metric trace of its second covariant
derivative,

`∇*∇ σ = -tr_g ∇²σ = -∑ᵢ ∇²σ(eᵢ, eᵢ)`,

for any orthonormal basis `eᵢ` of the tangent space. Its principal symbol is `-|ξ|²_g` times
the identity in the geometric convention, equivalently `|ξ|²_g` in the Fourier convention: this
file computes the double commutator with multiplication by functions,

`[[∇*∇, f], g] σ = ∇*∇(f g σ) - f ∇*∇(g σ) - g ∇*∇(f σ) + f g ∇*∇ σ = -2 ⟪grad f, grad g⟫ σ`,

so `(1/2!) [[∇*∇, f], f] = -|df|²_g`. When `∇ᵀ` is the Levi-Civita connection, it also proves
the Leibniz rule `∇*∇(f σ) = f ∇*∇ σ - 2 ∇_{grad f} σ - (Δ f) σ`, where `Δ = div ∘ grad` is
`TauCeti.Manifold.laplaceBeltrami`. For the canonical flat connection on the trivial line bundle
this gives `∇*∇ f = -Δ f`.

The trace is the contraction of the bilinear map `∇²σ` against the canonical covariant tensor
`InnerProductSpace.canonicalCovariantTensor`, so the definition involves no choice of basis.

## Main definitions and results

* `CovariantDerivative.roughLaplacian`: the rough Laplacian `∇*∇ σ` at a point.
* `CovariantDerivative.roughLaplacian_eq_sum`: its value in an orthonormal basis.
* `CovariantDerivative.roughLaplacian_smul_smul_sub`: the double commutator of `∇*∇` with
  multiplication by two functions is `-2 ⟪grad f, grad g⟫ σ`.
* `CovariantDerivative.roughLaplacian_smul`: the Leibniz rule for the rough Laplacian of the
  Levi-Civita second covariant derivative.
* `CovariantDerivative.roughLaplacian_trivial`: on the trivial line bundle, `∇*∇ f = -Δ f`.

## References

* P. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, §2 (the rough
  Laplacian and operators of Laplace type).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 4
  (the second covariant derivative and traces).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {σ : Π y : M, V y} {f g : M → ℝ}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **rough Laplacian** `∇*∇ σ = -tr_g ∇²σ` of a section `σ` at `x`: the negative metric
trace of the second covariant derivative of `σ` for the connections `∇` on `V` and `∇ᵀ` on the
tangent bundle. In an orthonormal basis it is `-∑ᵢ ∇²σ(eᵢ, eᵢ)` (`roughLaplacian_eq_sum`). It is
zero when `σ` is not smooth. -/
def roughLaplacian (σ : Π y : M, V y) (x : M) : V x :=
  -TensorProduct.lift.equiv (.id ℝ) (TangentSpace I x) (TangentSpace I x) (V x)
    (cov.secondCovariantDerivative covT σ x)
    (InnerProductSpace.canonicalCovariantTensor (TangentSpace I x))

/-- The rough Laplacian in an orthonormal basis: `∇*∇ σ = -∑ᵢ ∇²σ(eᵢ, eᵢ)`. -/
theorem roughLaplacian_eq_sum (σ : Π y : M, V y) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.roughLaplacian covT σ x = -∑ i, cov.secondCovariantDerivative covT σ x (b i) (b i) := by
  rw [roughLaplacian, InnerProductSpace.canonicalCovariantTensor_eq_sum _ b, map_sum]
  simp only [TensorProduct.lift.equiv_apply]

/-- The rough Laplacian of a section which is not smooth is zero. -/
@[simp]
theorem roughLaplacian_of_not_contMDiff (hσ : ¬CMDiff ∞ (T% σ)) (x : M) :
    cov.roughLaplacian covT σ x = 0 := by
  simp [roughLaplacian, hσ]

/-- The rough Laplacian of the zero section is zero. -/
@[simp]
theorem roughLaplacian_zero (x : M) :
    cov.roughLaplacian covT (0 : Π y : M, V y) x = 0 := by
  simp [roughLaplacian]

/-- The rough Laplacian is additive on smooth sections. -/
theorem roughLaplacian_add {τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (x : M) :
    cov.roughLaplacian covT (σ + τ) x =
      cov.roughLaplacian covT σ x + cov.roughLaplacian covT τ x := by
  simp only [roughLaplacian, secondCovariantDerivative_add cov covT hσ hτ x, map_add,
    LinearMap.add_apply, neg_add]

/-- The rough Laplacian commutes with multiplication of a smooth section by a constant. -/
theorem roughLaplacian_const_smul (c : ℝ) (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.roughLaplacian covT (c • σ) x = c • cov.roughLaplacian covT σ x := by
  simp only [roughLaplacian, secondCovariantDerivative_const_smul cov covT c hσ x, map_smul,
    LinearMap.smul_apply, smul_neg]

/-- The rough Laplacian commutes with negation of a smooth section. -/
theorem roughLaplacian_neg (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.roughLaplacian covT (-σ) x = -cov.roughLaplacian covT σ x := by
  simpa using roughLaplacian_const_smul cov covT (-1) hσ x

/-- The rough Laplacian commutes with differences of smooth sections. -/
theorem roughLaplacian_sub {τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (x : M) :
    cov.roughLaplacian covT (σ - τ) x =
      cov.roughLaplacian covT σ x - cov.roughLaplacian covT τ x := by
  have hτ' : CMDiff ∞ (T% (-τ)) := by
    simpa using (hτ.const_smul_section (a := (-1 : ℝ)) :)
  rw [sub_eq_add_neg, roughLaplacian_add cov covT hσ hτ' x, roughLaplacian_neg cov covT hτ x,
    sub_eq_add_neg]

/-- **The principal symbol of the rough Laplacian.** For smooth functions `f`, `g` and a smooth
section `σ`, the double commutator of `∇*∇` with multiplication by `f` and `g` is
`∇*∇(f g σ) - f ∇*∇(g σ) - g ∇*∇(f σ) + f g ∇*∇ σ = -2 ⟪grad f, grad g⟫ σ`.
This computes the geometric principal symbol of `∇*∇` as `-|ξ|²_g` times the identity. -/
theorem roughLaplacian_smul_smul_sub (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.roughLaplacian covT (f • g • σ) x - f x • cov.roughLaplacian covT (g • σ) x -
        g x • cov.roughLaplacian covT (f • σ) x + (f x * g x) • cov.roughLaplacian covT σ x =
      -(2 * ⟪TauCeti.Manifold.mgradient I f x, TauCeti.Manifold.mgradient I g x⟫) • σ x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- `∑ᵢ df(eᵢ) dg(eᵢ) = ⟪grad f, grad g⟫` by Parseval.
  have hsum : ∑ i, d% f x (b i) * d% g x (b i) =
      ⟪TauCeti.Manifold.mgradient I f x, TauCeti.Manifold.mgradient I g x⟫ := by
    rw [← b.sum_inner_mul_inner]
    simp only [TauCeti.Manifold.inner_mgradient, TauCeti.Manifold.inner_mgradient_right]
  simp only [roughLaplacian_eq_sum cov covT _ x b, smul_neg, Finset.smul_sum]
  calc _ = -∑ i, (cov.secondCovariantDerivative covT (f • g • σ) x (b i) (b i) -
          f x • cov.secondCovariantDerivative covT (g • σ) x (b i) (b i) -
            g x • cov.secondCovariantDerivative covT (f • σ) x (b i) (b i) +
              (f x * g x) • cov.secondCovariantDerivative covT σ x (b i) (b i)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        abel
    _ = -∑ i, (2 * (d% f x (b i) * d% g x (b i))) • σ x := by
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [secondCovariantDerivative_smul_smul_sub cov covT hf hg hσ x]
        congr 1
        ring
    _ = _ := by
        rw [← Finset.sum_smul, ← Finset.mul_sum, hsum, neg_smul]

/-- The diagonal case of `roughLaplacian_smul_smul_sub`:
`∇*∇(f² σ) - 2 f ∇*∇(f σ) + f² ∇*∇ σ = -2 |grad f|² σ`, so that
`(1/2!) [[∇*∇, f], f] = -|df|²_g`. -/
theorem roughLaplacian_smul_smul_sub_self (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hσ : CMDiff ∞ (T% σ))
    (x : M) :
    cov.roughLaplacian covT (f • f • σ) x - (2 * f x) • cov.roughLaplacian covT (f • σ) x +
        (f x ^ 2) • cov.roughLaplacian covT σ x =
      -(2 * ‖TauCeti.Manifold.mgradient I f x‖ ^ 2) • σ x := by
  rw [← real_inner_self_eq_norm_sq, ← roughLaplacian_smul_smul_sub cov covT hf hf hσ x]
  module

section LeviCivita

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Leibniz rule for the rough Laplacian.** With the Levi-Civita connection on the tangent
bundle, `∇*∇(f σ) = f ∇*∇ σ - 2 ∇_{grad f} σ - (Δ f) σ` for a smooth function `f` and a smooth
section `σ`, where `Δ = div ∘ grad` is the Laplace–Beltrami operator. -/
theorem roughLaplacian_smul (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.roughLaplacian (leviCivitaConnection I M) (f • σ) x =
      f x • cov.roughLaplacian (leviCivitaConnection I M) σ x -
        (2 : ℝ) • cov σ x (TauCeti.Manifold.mgradient I f x) -
          TauCeti.Manifold.laplaceBeltrami I f x • σ x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- Each diagonal term of `∇²(f σ)` is computed with a smooth extension `Y` of `b i`, and its
  -- scalar coefficient is the Hessian of `f`.
  have hterm (i) : cov.secondCovariantDerivative (leviCivitaConnection I M) (f • σ) x (b i) (b i) =
      f x • cov.secondCovariantDerivative (leviCivitaConnection I M) σ x (b i) (b i) +
        (2 * d% f x (b i)) • cov σ x (b i) +
          TauCeti.Manifold.hessian I f x (b i) (b i) • σ x := by
    obtain ⟨Y, hY, hYx⟩ := exists_contMDiff_section_eq I E ∞ (b i)
    obtain ⟨X, -, hX⟩ := exists_contMDiff_section_eq I E ∞ (b i)
    have hS := secondCovariantDerivative_smul_apply cov (leviCivitaConnection I M) hf hσ x hY
      (b i)
    have hH := TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub (I := I) x
      (hf.contMDiffAt.of_le (by simp)) X Y (hY.mdifferentiable (by simp) x)
    rw [hX, hYx] at hH
    rw [hYx] at hS
    rw [hS, hH]
    module
  -- `∑ᵢ df(eᵢ) ∇_{eᵢ} σ = ∇_{grad f} σ`, since `grad f = ∑ᵢ df(eᵢ) eᵢ`.
  have hgrad : ∑ i, d% f x (b i) • cov σ x (b i) =
      cov σ x (TauCeti.Manifold.mgradient I f x) := by
    conv_rhs => rw [← b.sum_repr' (TauCeti.Manifold.mgradient I f x)]
    simp only [map_sum, map_smul, TauCeti.Manifold.inner_mgradient_right]
  rw [roughLaplacian_eq_sum cov _ _ x b, roughLaplacian_eq_sum cov _ _ x b,
    TauCeti.Manifold.laplaceBeltrami_eq_sum_hessian I f x b, ← hgrad]
  simp only [hterm, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, mul_smul,
    smul_neg]
  module

/-- **The rough Laplacian of a function.** For the canonical flat connection on the trivial line
bundle and the Levi-Civita connection on the tangent bundle, the rough Laplacian of a smooth
function is minus its Laplace–Beltrami operator: `∇*∇ f = -Δ f`. -/
theorem roughLaplacian_trivial (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    (trivial (I := I) (M := M) ℝ).roughLaplacian (leviCivitaConnection I M) f x =
      -TauCeti.Manifold.laplaceBeltrami I f x := by
  -- Write `f` as `f • 1`; the constant section `1` is parallel, so only `-(Δ f) • 1` survives.
  set one : Π y : M, Trivial M ℝ y := fun _ ↦ (1 : ℝ)
  have hone : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun y ↦ (⟨y, one y⟩ : TotalSpace ℝ (Trivial M ℝ))) :=
    fun y ↦ by
      simp only [contMDiffAt_section, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply]
      exact contMDiffAt_const
  have hpar (y : M) : trivial (I := I) ℝ one y = 0 := by
    simp only [one, trivial_apply, mvfderiv_const]
  have hsecond : (trivial (I := I) (M := M) ℝ).secondCovariantDerivative
      (leviCivitaConnection I M) one x = 0 := by
    refine ((eq_secondCovariantDerivative_iff _ _ hone x 0).2 fun Y _ u ↦ ?_).symm
    simp only [one, trivial_apply, mvfderiv_const, zero_apply, LinearMap.zero_apply, sub_zero]
    -- What remains is the derivative of the zero section, whose values lie in the fibres
    -- `Trivial M ℝ y`; these are `ℝ` only up to unfolding `Bundle.Trivial`, so `mvfderiv_const`
    -- applies by definitional unfolding rather than by rewriting.
    exact ((DFunLike.congr_fun (mvfderiv_const (I := I) (x := x) (0 : ℝ)) u).trans
      (zero_apply u)).symm
  have hf1 : f • one = f := by
    funext y
    simp [one]
  have h := roughLaplacian_smul (trivial (I := I) (M := M) ℝ) hf hone x
  rw [hf1] at h
  rw [h, roughLaplacian, hsecond, hpar]
  simp [one]

end LeviCivita

end CovariantDerivative
