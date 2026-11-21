/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorField.Derivation
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# The Bochner connection of a scalar second-order operator

Let `M` be a Riemannian manifold, `c ≠ 0` a real number and `D` an operator on the smooth
functions `C^∞(M)` which differs from `-c Δ` by an operator of order at most one, in Grothendieck's
sense (`TauCeti.differentialOperators`); here `Δ = div ∘ grad` is the Laplace–Beltrami operator, so
`-Δ = ∇*∇` is the rough Laplacian of the flat connection `d` on the trivial line bundle
(`CovariantDerivative.roughLaplacian_trivial`). For `c > 0` such an operator is of Laplace type
with constant `c` (`TauCeti.IsLaplaceType`), since `-Δ` is and perturbations of order at most one
keep the Laplace type. The **Bochner connection** of `D` is the unique connection `∇` on the
trivial line bundle that absorbs the first-order part of `D` into its rough Laplacian:

`D f = c ∇*∇ f + V f`

for a function `V`, the zeroth-order remainder (Gilkey, Lemma 2.1, applied to `c⁻¹ D`).

On the trivial line, a connection is `∇ = d + ω` for the one-form `ω = ∇ 1`
(`CovariantDerivative.apply_eq_mvfderiv_add_smul_one`), and with the Levi-Civita connection on
the tangent bundle its rough Laplacian is

`∇*∇ f = -Δ f - 2 ω(grad f) + f ∇*∇ 1`

(`CovariantDerivative.roughLaplacian_eq_neg_laplaceBeltrami_sub_add`). Writing `ω = ⟪Y, ·⟫` for a
vector field `Y`, that is `∇ = d + ⟪Y, ·⟫` (`CovariantDerivative.trivialAddInner`), one has
`∇*∇ 1 = -(div Y + ‖Y‖²)`, so

`∇*∇ f = -Δ f - 2 df(Y) - (div Y + ‖Y‖²) f`

(`CovariantDerivative.roughLaplacian_trivialAddInner`). If `D + c Δ` is differentiation along a
vector field `X` plus multiplication by `U = (D + c Δ) 1`, the Bochner connection is therefore
`d + ⟪Y, ·⟫` with `Y = -(2 c)⁻¹ X`, and the remainder is `V = U + c (div Y + ‖Y‖²)`.

The connection `d + ⟪Y, ·⟫` is compatible with the standard fibre metric only for `Y = 0`
(`CovariantDerivative.isMetricCompatible_trivialAddInner_iff`), so the Bochner connection of `D`
is metric exactly when `D + c Δ` has no first-order part. For instance, on a line with coordinate
`x`, the operator `-∂ₓ² - cos x ∂ₓ` has the Bochner connection `d + ½ cos x dx`, which is not
metric.

## Main results

* `CovariantDerivative.eq_of_mul_roughLaplacian_add_mul_eq`: **uniqueness of the Bochner
  connection**: two smooth connections on the trivial line and two remainders giving the same
  operator agree on differentiable sections, and the remainders are equal.
* `LinearMap.existsUnique_eq_mul_roughLaplacian_trivialAddInner_add_mul`: **existence of the
  Bochner connection**, with a unique smooth field `Y` and a unique smooth remainder `V`.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2, Lemma 2.1.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (the connection and potential of a generalized Laplacian).
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Uniqueness of the Bochner connection -/

/-- **Uniqueness of the Bochner connection.** If two smooth connections `∇`, `∇'` on the trivial
line bundle and two functions `V`, `V'` give the same operator, `c ∇*∇ f + V f = c ∇'*∇' f + V' f`
for every smooth `f`, with `c ≠ 0`, then the connections agree on every section differentiable at
a point, and `V = V'`. -/
theorem eq_of_mul_roughLaplacian_add_mul_eq
    (cov cov' : CovariantDerivative I ℝ (Bundle.Trivial M ℝ))
    [ContMDiffCovariantDerivative cov ∞] [ContMDiffCovariantDerivative cov' ∞]
    {c : ℝ} (hc : c ≠ 0) {V V' : M → ℝ}
    (h : ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
      c * cov.roughLaplacian (leviCivitaConnection I M) f x + V x * f x =
        c * cov'.roughLaplacian (leviCivitaConnection I M) f x + V' x * f x) :
    (∀ (σ : M → ℝ) (x : M), MDifferentiableAt I 𝓘(ℝ) σ x → cov σ x = cov' σ x) ∧ V = V' := by
  have h1 (x : M) := h 1 x
  simp only [ContMDiffMap.coe_one, Pi.one_apply, mul_one] at h1
  -- The connection forms agree: test against a function with a prescribed gradient at `x`.
  have hform (x : M) : cov (1 : M → ℝ) x = cov' (1 : M → ℝ) x := by
    ext w
    obtain ⟨f, -, hfx⟩ := TauCeti.exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (innerSL ℝ w)
    have hgrad : TauCeti.Manifold.mgradient I f x = w := by
      refine (TauCeti.Manifold.eq_mgradient_iff.2 fun v ↦ ?_).symm
      rw [hfx, innerSL_apply_apply]
    have hf := h f x
    rw [roughLaplacian_eq_neg_laplaceBeltrami_sub_add cov f.contMDiff,
      roughLaplacian_eq_neg_laplaceBeltrami_sub_add cov' f.contMDiff, hgrad] at hf
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hc)
    linear_combination (-1 : ℝ) * hf + f x * h1 x
  have hagree (σ : M → ℝ) (x : M) (hσ : MDifferentiableAt I 𝓘(ℝ) σ x) :
      cov σ x = cov' σ x := by
    rw [cov.apply_eq_mvfderiv_add_smul_one hσ, cov'.apply_eq_mvfderiv_add_smul_one hσ, hform]
  refine ⟨hagree, ?_⟩
  -- The rough Laplacians agree, hence so do the remainders.
  have hrough := cov.roughLaplacian_congr (leviCivitaConnection I M) cov' (σ := (1 : M → ℝ))
    fun τ hτ ↦ funext fun x ↦ hagree τ x
      ((((Trivial.contMDiff_mk_iff (b := id) (f := τ)).1 hτ).2 x).mdifferentiableAt (by simp))
  funext x
  have hx := h1 x
  rw [hrough] at hx
  linarith

end CovariantDerivative

namespace LinearMap

open CovariantDerivative TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Existence of the Bochner connection -/

/-- **Existence and uniqueness of the Bochner connection.** Let `D` be an operator on the smooth
functions of a boundaryless Riemannian manifold which differs from `-c Δ`, with `c ≠ 0`, by an
operator of order at most one. Then there are a unique smooth vector field `Y` and a unique smooth
function `V` with

`D f = c ∇*∇ f + V f` for the connection `∇ = d + ⟪Y, ·⟫` on the trivial line bundle

(`CovariantDerivative.trivialAddInner`). If `D + c Δ` is differentiation along `X` plus
multiplication by a function, then `Y = -(2 c)⁻¹ X` and `V = (D + c Δ) 1 + c (div Y + ‖Y‖²)`.
By `CovariantDerivative.eq_of_mul_roughLaplacian_add_mul_eq`, every smooth connection with this
property agrees with `d + ⟪Y, ·⟫` on differentiable sections. -/
theorem existsUnique_eq_mul_roughLaplacian_trivialAddInner_add_mul [BoundarylessManifold I M]
    (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) {c : ℝ} (hc : c ≠ 0)
    (hD : D + c • smoothLaplaceBeltrami I M ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 1) :
    ∃! p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯,
      ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M), D f x =
        c * (trivialAddInner (p.1 : Π x : M, TangentSpace I x)).roughLaplacian
          (leviCivitaConnection I M) f x + p.2 x * f x := by
  set Q := D + c • smoothLaplaceBeltrami I M
  set δ := Q.derivationOfMemDifferentialOperatorsOne hD
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (-(2 * c)⁻¹) • derivationEquivSmoothVectorField δ
  have hYsmooth : ContMDiff I I.tangent (∞ + 1)
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) := by
    simpa using Y.contMDiff
  have hV : ContMDiff I 𝓘(ℝ) ∞
      (fun x ↦ Q 1 x + c * (Manifold.divergence I Y x + ⟪Y x, Y x⟫)) := by
    have hdiv := Manifold.contMDiff_divergence (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp)
      hYsmooth
    have hnorm : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ ⟪Y x, Y x⟫) :=
      ContMDiff.inner_bundle (IB := I) (n := ∞) (F := E) (E := fun y : M ↦ TangentSpace I y)
        Y.contMDiff Y.contMDiff
    exact (Q 1).contMDiff.add (contMDiff_const.mul (hdiv.add hnorm))
  set V : C^∞⟮I, M; ℝ⟯ := ⟨_, hV⟩
  -- Existence: expand `D = Q - c Δ` and the rough Laplacian of `d + ⟪Y, ·⟫`.
  have hexist (f : C^∞⟮I, M; ℝ⟯) (x : M) : D f x =
      c * (trivialAddInner (Y : Π x : M, TangentSpace I x)).roughLaplacian
        (leviCivitaConnection I M) f x + V x * f x := by
    have hQ : D f x = Q f x - c * Manifold.laplaceBeltrami I f x := by
      simp [Q]
    have hδ : δ f x = Q f x - f x * Q 1 x := by
      simp [δ, derivationOfMemDifferentialOperatorsOne_apply]
    have hX : mvfderiv I f x (Y x) = -(2 * c)⁻¹ * δ f x := by
      have hYx : Y x = (-(2 * c)⁻¹) • δ.vectorField x := by simp [Y]
      rw [hYx, map_smul, Derivation.mvfderiv_vectorField, smul_eq_mul]
    simp only [V, ContMDiffMap.coeFn_mk]
    rw [hQ, roughLaplacian_trivialAddInner Y f.contMDiff, hX, hδ]
    field_simp
    ring
  refine ⟨(Y, V), hexist, fun p hp ↦ ?_⟩
  -- Uniqueness: compare with the connection constructed above.
  obtain ⟨hcov, hVeq⟩ := eq_of_mul_roughLaplacian_add_mul_eq
    (trivialAddInner (p.1 : Π x : M, TangentSpace I x))
    (trivialAddInner (Y : Π x : M, TangentSpace I x)) hc (V := p.2) (V' := V)
    fun f x ↦ (hp f x).symm.trans (hexist f x)
  refine Prod.ext (ContMDiffSection.ext fun x ↦ ?_) (ContMDiffMap.ext fun x ↦ congrFun hVeq x)
  have h1 := hcov 1 x mdifferentiableAt_const
  rw [trivialAddInner_one, trivialAddInner_one] at h1
  exact ext_inner_right ℝ fun v ↦ by simpa using congrArg (fun L ↦ L v) h1

end LinearMap
