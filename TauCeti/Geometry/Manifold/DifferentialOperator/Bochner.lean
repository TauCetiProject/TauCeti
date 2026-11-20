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
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
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

## Main definitions

* `CovariantDerivative.trivialAddInner Y`: the connection `d + ⟪Y, ·⟫` on the trivial line
  bundle; it is smooth for a smooth vector field `Y`.

## Main results

* `CovariantDerivative.apply_eq_mvfderiv_add_smul_one`: every connection on the trivial line is
  `d + ∇ 1` on differentiable sections.
* `CovariantDerivative.roughLaplacian_eq_neg_laplaceBeltrami_sub_add`: the rough Laplacian of a
  smooth connection on the trivial line.
* `CovariantDerivative.roughLaplacian_trivialAddInner`: the rough Laplacian of `d + ⟪Y, ·⟫`.
* `CovariantDerivative.isMetricCompatible_trivialAddInner_iff`: `d + ⟪Y, ·⟫` is metric exactly
  when `Y = 0`.
* `CovariantDerivative.eq_of_smul_roughLaplacian_add_mul_eq`: **uniqueness of the Bochner
  connection**: two smooth connections on the trivial line and two remainders giving the same
  operator agree on differentiable sections, and the remainders are equal.
* `LinearMap.existsUnique_eq_smul_roughLaplacian_trivialAddInner_add_mul`: **existence of the
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

/-! ### Connections on the trivial line bundle -/

section TrivialLine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Connections on the trivial line.** Every connection on the trivial line bundle is
`d + ω` with the connection form `ω = ∇ 1`: on a section `σ` differentiable at `x`,
`∇ σ x = dσ_x + σ x ∇ 1 x`. -/
theorem apply_eq_mvfderiv_add_smul_one (cov : CovariantDerivative I ℝ (Bundle.Trivial M ℝ))
    {σ : M → ℝ} {x : M} (hσ : MDifferentiableAt I 𝓘(ℝ) σ x) :
    cov σ x = mvfderiv I σ x + σ x • cov (1 : M → ℝ) x := by
  have hone := Trivial.mdifferentiableAt_mk_iff (I := I) (b := id) (f := (1 : M → ℝ))
    (x := x) |>.2 ⟨mdifferentiableAt_id, mdifferentiableAt_const⟩
  have h := cov.isCovariantDerivativeOnUniv.leibniz hone hσ
  have hσ1 : (σ • (1 : M → ℝ) : Π y : M, Bundle.Trivial M ℝ y) = σ := by
    funext y
    simp
  rw [hσ1] at h
  rw [h, add_comm]
  congr 1
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, Pi.one_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact mul_one _

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The connection `d + ⟪Y, ·⟫` on the trivial line bundle, whose connection form is the one-form
metric-dual to the vector field `Y`: `∇ σ = dσ + σ ⟪Y, ·⟫`
(`CovariantDerivative.trivialAddInner_apply`). Every connection on the trivial line agrees with
one of these on differentiable sections (`CovariantDerivative.apply_eq_mvfderiv_add_smul_one`). -/
def trivialAddInner (Y : Π x : M, TangentSpace I x) :
    CovariantDerivative I ℝ (Bundle.Trivial M ℝ) :=
  (trivial ℝ).addOneForm fun x ↦ ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ (Y x))

@[simp]
theorem trivialAddInner_apply (Y : Π x : M, TangentSpace I x) (σ : M → ℝ) (x : M) :
    trivialAddInner Y σ x = mvfderiv I σ x + σ x • innerSL ℝ (Y x) := by
  rw [trivialAddInner, addOneForm_apply, trivial_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- For `Y = 0`, `d + ⟪Y, ·⟫` is the flat connection `d`. -/
@[simp]
theorem trivialAddInner_zero : trivialAddInner (0 : Π x : M, TangentSpace I x) = trivial ℝ := by
  ext σ x : 3
  rw [trivialAddInner_apply, trivial_apply, Pi.zero_apply, map_zero, smul_zero, add_zero]

/-- The connection form of `d + ⟪Y, ·⟫` is `⟪Y, ·⟫`. -/
theorem trivialAddInner_one (Y : Π x : M, TangentSpace I x) (x : M) :
    trivialAddInner Y (1 : M → ℝ) x = innerSL ℝ (Y x) := by
  rw [trivialAddInner_apply, Pi.one_def, mvfderiv_const, zero_add]
  simp

variable [IsManifold I ∞ M]

/-- The connection `d + ⟪Y, ·⟫` is compatible with the standard fibre metric of the trivial line
bundle exactly when `Y = 0`: on a line, the only skew-adjoint connection form is zero. -/
theorem isMetricCompatible_trivialAddInner_iff (Y : Π x : M, TangentSpace I x) :
    (trivialAddInner Y).IsMetricCompatible ↔ Y = 0 := by
  rw [isMetricCompatible_iff]
  constructor
  · intro h
    funext x
    refine ext_inner_left ℝ fun v ↦ ?_
    have hone := Trivial.mdifferentiableAt_mk_iff (I := I) (b := id) (f := (1 : M → ℝ))
      (x := x) |>.2 ⟨mdifferentiableAt_id, mdifferentiableAt_const⟩
    have hv := h (X := FiberBundle.extend E v) (FiberBundle.mdifferentiableAt_extend I E v)
      hone hone
    simp only [trivialAddInner_one, innerSL_apply_apply, FiberBundle.extend_apply_self,
      Pi.one_apply, Real.inner_apply, mul_one, one_mul] at hv
    rw [mvfderiv_const, zero_apply] at hv
    rw [Pi.zero_apply, inner_zero_right, real_inner_comm]
    linarith
  · rintro rfl x X σ τ - hσ hτ
    have hσ' := ((Trivial.mdifferentiableAt_mk_iff (b := id) (f := σ)).1 hσ).2
    have hτ' := ((Trivial.mdifferentiableAt_mk_iff (b := id) (f := τ)).1 hτ).2
    simp only [trivialAddInner_apply, Pi.zero_apply, map_zero, smul_zero, add_zero,
      Real.inner_apply]
    rw [mvfderiv_fun_mul hσ' hτ']
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The connection `d + ⟪Y, ·⟫` is smooth for a smooth vector field `Y`. -/
instance (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffCovariantDerivative (trivialAddInner (Y : Π x : M, TangentSpace I x)) ∞ where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    have hf : ContMDiff I 𝓘(ℝ) (∞ + 1) σ := (Trivial.contMDiff_mk_iff.1 hσ).2
    have hY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (innerSL ℝ (Y x))) :=
      fun x ↦ ContMDiffWithinAt.innerSL_bundle (I := I) (F := E)
        (V := fun x : M ↦ TangentSpace I x) (Y.contMDiff x)
    have h := hf.contMDiff_totalSpaceMk_mvfderiv.add_section
      ((hf.of_le (by simp)).smul_section hY)
    convert h using 3 with x
    rw [trivialAddInner_apply, Pi.add_apply, Pi.smul_apply']

variable [T2Space M]

/-- **The rough Laplacian on the trivial line.** For a smooth connection `∇` on the trivial line
bundle with connection form `ω = ∇ 1`, and the Levi-Civita connection on the tangent bundle,
`∇*∇ f = -Δ f - 2 ω(grad f) + f ∇*∇ 1` for every smooth function `f`. -/
theorem roughLaplacian_eq_neg_laplaceBeltrami_sub_add
    (cov : CovariantDerivative I ℝ (Bundle.Trivial M ℝ)) [ContMDiffCovariantDerivative cov ∞]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    cov.roughLaplacian (leviCivitaConnection I M) f x =
      -TauCeti.Manifold.laplaceBeltrami I f x -
        2 * cov (1 : M → ℝ) x (TauCeti.Manifold.mgradient I f x) +
        f x * cov.roughLaplacian (leviCivitaConnection I M) (1 : M → ℝ) x := by
  have hone := Trivial.contMDiff_mk_iff (I := I) (J := I) (n := ∞) (b := id)
    (f := (1 : M → ℝ)) |>.2 ⟨contMDiff_id, contMDiff_const⟩
  have h := cov.roughLaplacian_smul hf hone x
  have hf1 : (f • (1 : M → ℝ) : Π y : M, Bundle.Trivial M ℝ y) = f := by
    funext y
    simp
  rw [hf1] at h
  rw [h]
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  ring

/-- The rough Laplacian of the constant function `1` for `d + ⟪Y, ·⟫` is `-(div Y + ‖Y‖²)`. -/
theorem roughLaplacian_trivialAddInner_one (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) :
    (trivialAddInner (Y : Π x : M, TangentSpace I x)).roughLaplacian
        (leviCivitaConnection I M) (1 : M → ℝ) x =
      -(TauCeti.Manifold.divergence I Y x + ⟪Y x, Y x⟫) := by
  set cov := trivialAddInner (Y : Π x : M, TangentSpace I x)
  set covT := leviCivitaConnection I M
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hone := Trivial.contMDiff_mk_iff (I := I) (J := I) (n := ∞) (b := id)
    (f := (1 : M → ℝ)) |>.2 ⟨contMDiff_id, contMDiff_const⟩
  have hYd : MDiffAt (T% (Y : Π x : M, TangentSpace I x)) x :=
    (Y.contMDiff x).mdifferentiableAt (by simp)
  -- Each diagonal term is `∇²1(eᵢ, eᵢ) = ⟪∇_{eᵢ} Y, eᵢ⟫ + ⟪Y, eᵢ⟫²`.
  have hterm (i) : cov.secondCovariantDerivative covT (1 : M → ℝ) x (b i) (b i) =
      ⟪covT Y x (b i), b i⟫ + ⟪Y x, b i⟫ ^ 2 := by
    obtain ⟨W, hW, hWx⟩ := exists_contMDiff_section_eq I E ∞ (b i)
    have hWd : MDiffAt (T% W) x := hW.mdifferentiable (by simp) x
    have hS := cov.secondCovariantDerivative_apply covT hone x hW (b i)
    -- The function `y ↦ ∇_{W y} 1 = ⟪Y y, W y⟫` and its derivative.
    have hfun : (fun y ↦ cov (1 : M → ℝ) y (W y)) = fun y ↦ ⟪Y y, W y⟫ := by
      funext y
      simp only [cov, trivialAddInner_one, innerSL_apply_apply]
    have hφd : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ⟪Y y, W y⟫) x :=
      MDifferentiableAt.inner_bundle (F := E) (E := fun y : M ↦ TangentSpace I y) hYd hWd
    have hLC := (isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      (FiberBundle.extend E (b i)) hYd hWd
    simp only [FiberBundle.extend_apply_self] at hLC
    rw [hfun, cov.apply_eq_mvfderiv_add_smul_one hφd, trivialAddInner_one] at hS
    rw [hWx] at hS hLC
    rw [hS]
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [mvfderiv_apply_eq_mfderiv_apply] at *
    rw [hLC]
    ring
  rw [roughLaplacian_eq_sum cov covT _ x b, TauCeti.Manifold.divergence_eq_sum_inner I _ x b,
    real_inner_self_eq_norm_sq, ← b.sum_sq_inner_right (Y x)]
  simp only [hterm, Finset.sum_add_distrib, real_inner_comm (b _) (Y x), covT]

/-- **The rough Laplacian of `d + ⟪Y, ·⟫`.** With the Levi-Civita connection on the tangent bundle,
`∇*∇ f = -Δ f - 2 df(Y) - (div Y + ‖Y‖²) f` for every smooth function `f`. -/
theorem roughLaplacian_trivialAddInner (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    (trivialAddInner (Y : Π x : M, TangentSpace I x)).roughLaplacian
        (leviCivitaConnection I M) f x =
      -TauCeti.Manifold.laplaceBeltrami I f x - 2 * mvfderiv I f x (Y x) -
        (TauCeti.Manifold.divergence I Y x + ⟪Y x, Y x⟫) * f x := by
  rw [roughLaplacian_eq_neg_laplaceBeltrami_sub_add _ hf, roughLaplacian_trivialAddInner_one,
    trivialAddInner_one, innerSL_apply_apply, TauCeti.Manifold.inner_mgradient_right]
  ring

/-! ### Uniqueness of the Bochner connection -/

/-- **Uniqueness of the Bochner connection.** If two smooth connections `∇`, `∇'` on the trivial
line bundle and two functions `V`, `V'` give the same operator, `c ∇*∇ f + V f = c ∇'*∇' f + V' f`
for every smooth `f`, with `c ≠ 0`, then the connections agree on every section differentiable at
a point, and `V = V'`. -/
theorem eq_of_smul_roughLaplacian_add_mul_eq
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

end TrivialLine

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
By `CovariantDerivative.eq_of_smul_roughLaplacian_add_mul_eq`, every smooth connection with this
property agrees with `d + ⟪Y, ·⟫` on differentiable sections. -/
theorem existsUnique_eq_smul_roughLaplacian_trivialAddInner_add_mul [BoundarylessManifold I M]
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
  obtain ⟨hcov, hVeq⟩ := eq_of_smul_roughLaplacian_add_mul_eq
    (trivialAddInner (p.1 : Π x : M, TangentSpace I x))
    (trivialAddInner (Y : Π x : M, TangentSpace I x)) hc (V := p.2) (V' := V)
    fun f x ↦ (hp f x).symm.trans (hexist f x)
  refine Prod.ext (ContMDiffSection.ext fun x ↦ ?_) (ContMDiffMap.ext fun x ↦ congrFun hVeq x)
  have h1 := hcov 1 x mdifferentiableAt_const
  rw [trivialAddInner_one, trivialAddInner_one] at h1
  exact ext_inner_right ℝ fun v ↦ by simpa using congrArg (fun L ↦ L v) h1

end LinearMap
