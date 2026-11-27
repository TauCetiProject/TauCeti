/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Function.L2Space.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# The Sobolev space `H¹` of a closed Riemannian manifold

Let `M` be a compact manifold with a continuous Riemannian metric and its Riemannian volume `dV`.
The Sobolev space `H¹(M)` (`TauCeti.Manifold.SobolevH1`) is the completion of the smooth functions
on `M` for the inner product

`⟪u, v⟫_{H¹} = ∫ u v dV + ∫ ⟪∇u, ∇v⟫ dV`.

It is a real Hilbert space in which the smooth functions are dense
(`TauCeti.Manifold.SobolevH1.denseRange_ofSmooth`), and it is the natural domain of the weak
formulation of second order elliptic equations on `M` such as the Poisson equation.

The inclusion of the smooth functions into `L²(M)` does not increase norms, so it extends to a
continuous linear map `TauCeti.Manifold.SobolevH1.toLp : H¹(M) →L[ℝ] L²(M)`, the value of an
element of `H¹(M)`. When `M` has no boundary and the metric is `C¹`, Green's identity for smooth
functions extends by continuity to all of `H¹(M)`: for `w ∈ H¹(M)` and a smooth function `φ`,

`⟪w, φ⟫_{H¹} = ∫ w (φ - Δφ) dV`

(`TauCeti.Manifold.SobolevH1.inner_ofSmooth_right`), where `Δ = div grad` is the
Laplace–Beltrami operator. Consequently an element of `H¹(M)` with value zero is orthogonal to
the dense set of smooth functions, so `toLp` is injective
(`TauCeti.Manifold.SobolevH1.toLp_injective`), and `H¹(M)` is a subspace of `L²(M)`. Its
values are dense in `L²(M)` (`TauCeti.Manifold.SobolevH1.denseRange_toLp`).

The **Dirichlet form** `TauCeti.Manifold.SobolevH1.dirichletForm` is the continuous bilinear form
`⟪w, v⟫_{H¹} - ⟪w, v⟫_{L²}` on `H¹(M)`. It extends `∫ ⟪∇u, ∇v⟫ dV` from smooth functions, and
against a smooth function `φ` it is `∫ w Δ⁺φ dV`, where `Δ⁺ = -Δ` is the nonnegative Laplacian.

## Main results

* `TauCeti.Manifold.SobolevH1`: the Sobolev space `H¹(M)`, with
  `TauCeti.Manifold.SobolevH1.ofSmooth` the inclusion of the smooth functions (injective by
  `TauCeti.Manifold.SobolevH1.ofSmooth_injective`, so a smooth function vanishes in `H¹(M)` only
  if it is zero by `TauCeti.Manifold.SobolevH1.ofSmooth_eq_zero_iff`),
  `TauCeti.Manifold.SobolevH1.inner_ofSmooth` the inner product of two smooth functions, and
  `TauCeti.Manifold.SobolevH1.subsingleton_of_isEmpty` showing `H¹(M)` is a subsingleton on an empty
  manifold, and `TauCeti.Manifold.SobolevH1.nontrivial_of_nonempty` showing it is nontrivial on a
  nonempty one.
* `TauCeti.Manifold.SobolevH1.liftSmooth`: continuous linear extension of a bounded `ℝ`-linear map
  from smooth functions to `H¹(M)`, characterized by `liftSmooth_ofSmooth` and `liftSmooth_unique`.
* `TauCeti.Manifold.SobolevH1.toLp`: the value map `H¹(M) → L²(M)`, injective by
  `TauCeti.Manifold.SobolevH1.toLp_injective`, with dense range by
  `TauCeti.Manifold.SobolevH1.denseRange_toLp`.
* `TauCeti.Manifold.SobolevH1.inner_ofSmooth_right`: Green's identity on `H¹(M)`.
* `TauCeti.Manifold.SobolevH1.dirichletForm`: the Dirichlet form.

## Implementation notes

The pre-completion inner product space `TauCeti.Manifold.PreSobolevH1`, a type synonym of the
smooth functions carrying the `H¹` inner product before taking the completion, follows the
pattern of Mathlib's `PositiveLinearMap.PreGNS` and `PositiveLinearMap.GNS` in
`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §2.2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), §2.1.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (I M) in
/-- The smooth functions on `M`, as the space on which the `H¹` inner product is defined before
completion. -/
def PreSobolevH1 : Type _ := C^∞⟮I, M; ℝ⟯

instance : AddCommGroup (PreSobolevH1 I M) := inferInstanceAs (AddCommGroup C^∞⟮I, M; ℝ⟯)

instance : Module ℝ (PreSobolevH1 I M) := inferInstanceAs (Module ℝ C^∞⟮I, M; ℝ⟯)

namespace PreSobolevH1

/-- A smooth function, as an element of `PreSobolevH1`. -/
def toPreSobolevH1 : C^∞⟮I, M; ℝ⟯ ≃ₗ[ℝ] PreSobolevH1 I M := LinearEquiv.refl ℝ _

/-- An element of `PreSobolevH1`, as a smooth function. -/
def ofPreSobolevH1 : PreSobolevH1 I M ≃ₗ[ℝ] C^∞⟮I, M; ℝ⟯ := toPreSobolevH1.symm

@[simp]
theorem toPreSobolevH1_ofPreSobolevH1 (u : PreSobolevH1 I M) :
    toPreSobolevH1 (ofPreSobolevH1 u) = u :=
  (rfl)

@[simp]
theorem ofPreSobolevH1_toPreSobolevH1 (u : C^∞⟮I, M; ℝ⟯) :
    ofPreSobolevH1 (toPreSobolevH1 u) = u :=
  (rfl)

variable [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold I 1 M] [MeasurableSpace M]
  [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The integral `∫ u v dV` of the product of two smooth functions is additive in `u`. -/
private theorem integral_mul_add_left (u v w : C^∞⟮I, M; ℝ⟯) :
    ∫ x, (u + v) x * w x ∂riemannianVolume I M =
      ∫ x, u x * w x ∂riemannianVolume I M + ∫ x, v x * w x ∂riemannianVolume I M := by
  simp only [ContMDiffMap.coe_add, Pi.add_apply, add_mul]
  exact integral_add (((map_continuous u).mul (map_continuous w)).integrable_of_compactSpace)
    (((map_continuous v).mul (map_continuous w)).integrable_of_compactSpace)

/-- The integral `∫ ⟪∇u, ∇v⟫ dV` of two smooth functions is additive in `u`. -/
private theorem integral_inner_mgradient_add_left (u v w : C^∞⟮I, M; ℝ⟯) :
    ∫ x, ⟪mgradient I (u + v) x, mgradient I w x⟫_ℝ ∂riemannianVolume I M =
      ∫ x, ⟪mgradient I u x, mgradient I w x⟫_ℝ ∂riemannianVolume I M +
        ∫ x, ⟪mgradient I v x, mgradient I w x⟫_ℝ ∂riemannianVolume I M := by
  have hu := u.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  have hv := v.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  have hw := w.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  rw [ContMDiffMap.coe_add, mgradient_add (hu.mdifferentiable one_ne_zero)
    (hv.mdifferentiable one_ne_zero)]
  simp only [Pi.add_apply, inner_add_left]
  exact integral_add (continuous_inner_mgradient hu hw).integrable_of_compactSpace
    (continuous_inner_mgradient hv hw).integrable_of_compactSpace

/-- The `H¹` pre-inner product `∫ u v dV + ∫ ⟪∇u, ∇v⟫ dV` on smooth functions. -/
abbrev preInner : PreInnerProductSpace.Core ℝ (PreSobolevH1 I M) where
  inner u v := ∫ x, ofPreSobolevH1 u x * ofPreSobolevH1 v x ∂riemannianVolume I M +
    ∫ x, ⟪mgradient I (ofPreSobolevH1 u) x, mgradient I (ofPreSobolevH1 v) x⟫_ℝ
      ∂riemannianVolume I M
  conj_inner_symm u v := by
    simp only [conj_trivial, mul_comm (ofPreSobolevH1 u _), real_inner_comm]
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real]
    exact add_nonneg (integral_nonneg fun x ↦ mul_self_nonneg _)
      (integral_nonneg fun x ↦ real_inner_self_nonneg)
  add_left u v w := by
    simp only [map_add, integral_mul_add_left, integral_inner_mgradient_add_left]
    ring
  smul_left u v r := by
    simp only [map_smul, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, mgradient_smul,
      inner_smul_left, conj_trivial, mul_assoc, integral_const_mul]
    ring

instance : SeminormedAddCommGroup (PreSobolevH1 I M) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preInner)

instance : InnerProductSpace ℝ (PreSobolevH1 I M) :=
  InnerProductSpace.ofCore preInner

/-- The `H¹` inner product of two smooth functions. -/
theorem inner_toPreSobolevH1 (u v : C^∞⟮I, M; ℝ⟯) :
    ⟪toPreSobolevH1 u, toPreSobolevH1 v⟫_ℝ =
      ∫ x, u x * v x ∂riemannianVolume I M +
        ∫ x, ⟪mgradient I u x, mgradient I v x⟫_ℝ ∂riemannianVolume I M :=
  (rfl)

end PreSobolevH1

open PreSobolevH1

variable [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold I 1 M] [MeasurableSpace M]
  [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The **Sobolev space** `H¹(M)` of a compact Riemannian manifold: the completion of the smooth
functions on `M` for the inner product `⟪u, v⟫_{H¹} = ∫ u v dV + ∫ ⟪∇u, ∇v⟫ dV`. -/
abbrev SobolevH1 := UniformSpace.Completion (PreSobolevH1 I M)

namespace SobolevH1

/-- The inclusion of the smooth functions into `H¹(M)`. -/
def ofSmooth : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] SobolevH1 I M :=
  UniformSpace.Completion.toComplL.toLinearMap ∘ₗ toPreSobolevH1.toLinearMap

/-- A smooth function in `H¹(M)` is the image of its copy in the pre-completion space. -/
theorem ofSmooth_apply (u : C^∞⟮I, M; ℝ⟯) :
    ofSmooth u = ((toPreSobolevH1 u : PreSobolevH1 I M) : SobolevH1 I M) :=
  (rfl)

/-- **The `H¹` inner product of smooth functions.** -/
@[simp]
theorem inner_ofSmooth (u v : C^∞⟮I, M; ℝ⟯) :
    ⟪ofSmooth u, ofSmooth v⟫_ℝ =
      ∫ x, u x * v x ∂riemannianVolume I M +
        ∫ x, ⟪mgradient I u x, mgradient I v x⟫_ℝ ∂riemannianVolume I M := by
  rw [ofSmooth_apply, ofSmooth_apply, UniformSpace.Completion.inner_coe, inner_toPreSobolevH1]

/-- The squared `H¹` norm of a smooth function is `∫ u² dV + ∫ ‖∇u‖² dV`. -/
theorem norm_ofSmooth_sq (u : C^∞⟮I, M; ℝ⟯) :
    ‖ofSmooth u‖ ^ 2 =
      ∫ x, u x ^ 2 ∂riemannianVolume I M + ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M := by
  rw [← real_inner_self_eq_norm_sq, inner_ofSmooth]
  simp only [real_inner_self_eq_norm_sq, sq]

/-- The smooth functions are dense in `H¹(M)`. -/
theorem denseRange_ofSmooth : DenseRange (ofSmooth (I := I) (M := M)) :=
  UniformSpace.Completion.denseRange_coe.comp toPreSobolevH1.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- **Induction principle for `H¹(M)`.** A closed property of elements of `H¹(M)` that holds for
all smooth functions holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : SobolevH1 I M → Prop} (w : SobolevH1 I M) (hp : IsClosed {w | p w})
    (h : ∀ u : C^∞⟮I, M; ℝ⟯, p (ofSmooth u)) : p w :=
  denseRange_ofSmooth.induction_on w hp h

/-- On an empty manifold, `H¹(M)` is a subsingleton. -/
instance subsingleton_of_isEmpty [IsEmpty M] : Subsingleton (SobolevH1 I M) :=
  ⟨fun w₁ w₂ ↦ by
    have hz (w : SobolevH1 I M) : w = 0 :=
      induction_on w (isClosed_eq continuous_id continuous_const) fun v ↦ by
        have hv : v = 0 := ContMDiffMap.ext isEmptyElim
        rw [hv, map_zero]
    exact (hz w₁).trans (hz w₂).symm⟩

/-! ### Extending bounded linear maps from smooth functions -/

section LiftSmooth

variable {F : Type*} [SeminormedAddCommGroup F] [Module ℝ F] [UniformContinuousConstSMul ℝ F]
  [T0Space F] [CompleteSpace F]

/-- **Extension of a bounded linear map from smooth functions to `H¹(M)`.** Any `ℝ`-linear map
`L : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] F` into a complete separated seminormed space that is bounded in the `H¹`
norm extends uniquely (`TauCeti.Manifold.SobolevH1.liftSmooth_unique`) to a continuous linear map
`H¹(M) →L[ℝ] F` agreeing with `L` on smooth functions
(`TauCeti.Manifold.SobolevH1.liftSmooth_ofSmooth`). -/
def liftSmooth (L : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] F)
    (hL : ∃ C : ℝ, ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖) :
    SobolevH1 I M →L[ℝ] F :=
  (LinearMap.mkContinuousOfExistsBound (L.comp ofPreSobolevH1.toLinearMap) <|
    hL.imp fun C hC w ↦ by
      obtain ⟨u, rfl⟩ := toPreSobolevH1.surjective w
      have h := hC u
      rw [ofSmooth_apply u, UniformSpace.Completion.norm_coe] at h
      simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        ofPreSobolevH1_toPreSobolevH1] using h).fromCompletion

/-- On a smooth function `u`, `liftSmooth L hL` agrees with `L u`. -/
@[simp]
theorem liftSmooth_ofSmooth (L : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] F)
    (hL : ∃ C : ℝ, ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖) (u : C^∞⟮I, M; ℝ⟯) :
    liftSmooth L hL (ofSmooth u) = L u := by
  rw [liftSmooth, ofSmooth_apply u, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearMap.mkContinuousOfExistsBound_apply]
  simp

/-- Uniqueness of `liftSmooth`: any continuous linear map `H¹(M) →L[ℝ] F` agreeing with `L` on
smooth functions equals `liftSmooth L hL`. -/
theorem liftSmooth_unique (L : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] F)
    (hL : ∃ C : ℝ, ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖)
    {T : SobolevH1 I M →L[ℝ] F} (hT : ∀ u : C^∞⟮I, M; ℝ⟯, T (ofSmooth u) = L u) :
    T = liftSmooth L hL := by
  ext1 w
  refine induction_on w (isClosed_eq T.continuous (liftSmooth L hL).continuous) fun u ↦ ?_
  rw [hT u, liftSmooth_ofSmooth]

/-- A norm bound on smooth functions extends to all of `H¹(M)` for `liftSmooth`. -/
theorem norm_liftSmooth_apply_le (L : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] F)
    (hL : ∃ C : ℝ, ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖)
    {C : ℝ} (hC : ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖) (w : SobolevH1 I M) :
    ‖liftSmooth L hL w‖ ≤ C * ‖w‖ := by
  induction w using induction_on with
  | hp => exact isClosed_le (liftSmooth L hL).continuous.norm (continuous_const.mul continuous_norm)
  | h u => simpa only [liftSmooth_ofSmooth] using hC u

end LiftSmooth

/-- Operator-norm bound for `liftSmooth`. -/
theorem norm_liftSmooth_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F] [T0Space F]
    [CompleteSpace F] (L : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] F)
    (hL : ∃ C : ℝ, ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ u : C^∞⟮I, M; ℝ⟯, ‖L u‖ ≤ C * ‖ofSmooth u‖) :
    ‖liftSmooth L hL‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0 (norm_liftSmooth_apply_le L hL hC)

/-! ### The value in `L²` -/

/-- The inclusion of the smooth functions into `L²(M)`, on the pre-completion space. -/
private def preToLp : PreSobolevH1 I M →L[ℝ] Lp ℝ 2 (riemannianVolume I M) :=
  LinearMap.mkContinuous
    ((ContinuousMap.toLp 2 (riemannianVolume I M) ℝ).toLinearMap ∘ₗ
      { toFun u := (ofPreSobolevH1 u : C(M, ℝ))
        map_add' _ _ := rfl
        map_smul' _ _ := rfl })
    1 fun u ↦ by
      obtain ⟨u, rfl⟩ := toPreSobolevH1.surjective u
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, inner_toPreSobolevH1]
      simp only [LinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe, ContinuousMap.inner_toLp, conj_trivial]
      exact le_add_of_nonneg_right (integral_nonneg fun x ↦ real_inner_self_nonneg)

private theorem preToLp_toPreSobolevH1 (u : C^∞⟮I, M; ℝ⟯) :
    preToLp (toPreSobolevH1 u) = ContinuousMap.toLp 2 (riemannianVolume I M) ℝ (u : C(M, ℝ)) :=
  (rfl)

/-- The **value** of an element of `H¹(M)` in `L²(M)`: the continuous extension of the inclusion
of the smooth functions into `L²(M)`. -/
def toLp : SobolevH1 I M →L[ℝ] Lp ℝ 2 (riemannianVolume I M) :=
  preToLp.fromCompletion

/-- The value of a smooth function in `L²(M)` is its class. -/
@[simp]
theorem toLp_ofSmooth (u : C^∞⟮I, M; ℝ⟯) :
    toLp (ofSmooth u) = ContinuousMap.toLp 2 (riemannianVolume I M) ℝ (u : C(M, ℝ)) := by
  rw [toLp, ofSmooth_apply, ContinuousLinearMap.fromCompletion_apply_coe,
    preToLp_toPreSobolevH1]

/-- The value of a smooth function in `L²(M)` is almost everywhere equal to the function. -/
theorem toLp_ofSmooth_ae_eq (u : C^∞⟮I, M; ℝ⟯) :
    toLp (ofSmooth u) =ᵐ[riemannianVolume I M] u := by
  rw [toLp_ofSmooth]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ _

/-- **Smooth functions embed into `H¹(M)`.** Two smooth functions with the same image in `H¹(M)`
have the same class in `L²(M)`, hence agree, since the Riemannian volume charges every nonempty open
set. -/
theorem ofSmooth_injective : Function.Injective (ofSmooth (I := I) (M := M)) := fun u v huv ↦ by
  have h : (u : C(M, ℝ)) = v := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ)
    (riemannianVolume I M) (by simpa only [toLp_ofSmooth] using congrArg toLp huv)
  exact ContMDiffMap.ext fun x ↦ DFunLike.congr_fun h x

/-- A smooth function is zero in `H¹(M)` if and only if it is zero. -/
@[simp]
theorem ofSmooth_eq_zero_iff {u : C^∞⟮I, M; ℝ⟯} : ofSmooth u = 0 ↔ u = 0 :=
  map_eq_zero_iff _ ofSmooth_injective

/-- On a nonempty manifold, the constant function `1` is nonzero in `H¹(M)`. -/
theorem ofSmooth_one_ne_zero [Nonempty M] : ofSmooth (1 : C^∞⟮I, M; ℝ⟯) ≠ 0 :=
  ofSmooth_eq_zero_iff.not.2 fun h ↦ one_ne_zero (congrArg (· (Classical.arbitrary M)) h)

/-- On a nonempty manifold, `H¹(M)` is nontrivial: the constant function `1` is nonzero. -/
instance nontrivial_of_nonempty [Nonempty M] : Nontrivial (SobolevH1 I M) :=
  nontrivial_of_ne _ _ ofSmooth_one_ne_zero

/-- The `L²` inner product of the values of two smooth functions is `∫ u v dV`. -/
theorem inner_toLp_ofSmooth (u v : C^∞⟮I, M; ℝ⟯) :
    ⟪toLp (ofSmooth u), toLp (ofSmooth v)⟫_ℝ = ∫ x, u x * v x ∂riemannianVolume I M := by
  rw [toLp_ofSmooth, toLp_ofSmooth, ContinuousMap.inner_toLp]
  simp only [conj_trivial, ContinuousMap.coe_ofClass, mul_comm (v _)]

/-- The value map does not increase norms: `‖w‖_{L²} ≤ ‖w‖_{H¹}`. -/
theorem norm_toLp_le (w : SobolevH1 I M) : ‖toLp w‖ ≤ ‖w‖ := by
  induction w using induction_on with
  | hp => exact isClosed_le (toLp (I := I) (M := M)).continuous.norm continuous_norm
  | h u =>
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      inner_toLp_ofSmooth, norm_ofSmooth_sq]
    simp only [← sq]
    exact le_add_of_nonneg_right (integral_nonneg fun x ↦ by positivity)

/-- The `L²` norm of the length of the gradient of a smooth function is at most its `H¹` norm. -/
theorem norm_toLp_norm_mgradient_le (u : C^∞⟮I, M; ℝ⟯) :
    ‖ContinuousMap.toLp 2 (riemannianVolume I M) ℝ
        ⟨fun x ↦ ‖mgradient I u x‖,
          continuous_norm_mgradient (u.contMDiff.of_le (by simp))⟩‖ ≤ ‖ofSmooth u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ContinuousMap.inner_toLp, norm_ofSmooth_sq]
  simp only [ContinuousMap.coe_mk, conj_trivial, ← sq]
  exact le_add_of_nonneg_left (integral_nonneg fun x ↦ sq_nonneg _)

/-- The `L²` inner product of the value of `w ∈ H¹(M)` with a smooth function `φ` is
`∫ w φ dV`. -/
theorem inner_toLp_ofSmooth_right (w : SobolevH1 I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ⟪toLp w, toLp (ofSmooth φ)⟫_ℝ = ∫ x, toLp w x * φ x ∂riemannianVolume I M := by
  rw [toLp_ofSmooth, L2.inner_toLp_continuousMap]
  simp only [ContinuousMap.coe_ofClass, conj_trivial, mul_comm (φ _)]

/-- The integral of the value of `w ∈ H¹(M)` is its `L²` inner product with the constant
function `1`. -/
theorem integral_toLp_eq_inner_toLp_ofSmooth_one (w : SobolevH1 I M) :
    ∫ x, toLp w x ∂riemannianVolume I M = ⟪toLp w, toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯))⟫_ℝ := by
  rw [inner_toLp_ofSmooth_right]
  simp

/-- The integral of the square of the value of `w ∈ H¹(M)` is its squared `L²` norm. -/
theorem integral_toLp_sq_eq_norm_sq (w : SobolevH1 I M) :
    ∫ x, toLp w x ^ 2 ∂riemannianVolume I M = ‖toLp w‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using Lp.integral_norm_sq_eq_norm_sq (toLp w)

/-- The squared `L²` norm of the constant function `1` is the total volume. -/
theorem norm_toLp_ofSmooth_one_sq :
    ‖toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯))‖ ^ 2 = riemannianTotalVolume I M := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_ofSmooth]
  simp [riemannianTotalVolume_def]

/-! ### The Dirichlet form -/

/-- The **Dirichlet form** `D(w, v) = ⟪w, v⟫_{H¹} - ⟪w, v⟫_{L²}` on `H¹(M)`, the continuous
extension of `∫ ⟪∇u, ∇v⟫ dV` from smooth functions
(`TauCeti.Manifold.SobolevH1.dirichletForm_ofSmooth`). -/
def dirichletForm : SobolevH1 I M →L[ℝ] SobolevH1 I M →L[ℝ] ℝ :=
  innerSL ℝ - (innerSL ℝ).bilinearComp toLp toLp

/-- Unfolding lemma for `TauCeti.Manifold.SobolevH1.dirichletForm`. -/
theorem dirichletForm_apply (w v : SobolevH1 I M) :
    dirichletForm w v = ⟪w, v⟫_ℝ - ⟪toLp w, toLp v⟫_ℝ :=
  (rfl)

/-- The Dirichlet form of two smooth functions is `∫ ⟪∇u, ∇v⟫ dV`. -/
@[simp]
theorem dirichletForm_ofSmooth (u v : C^∞⟮I, M; ℝ⟯) :
    dirichletForm (ofSmooth u) (ofSmooth v) =
      ∫ x, ⟪mgradient I u x, mgradient I v x⟫_ℝ ∂riemannianVolume I M := by
  rw [dirichletForm_apply, inner_ofSmooth, inner_toLp_ofSmooth, add_sub_cancel_left]

/-- The Dirichlet form is symmetric. -/
theorem dirichletForm_comm (w v : SobolevH1 I M) : dirichletForm w v = dirichletForm v w := by
  rw [dirichletForm_apply, dirichletForm_apply, real_inner_comm, real_inner_comm (toLp w)]

/-- The Dirichlet form is nonnegative on the diagonal. -/
theorem dirichletForm_self_nonneg (w : SobolevH1 I M) : 0 ≤ dirichletForm w w := by
  induction w using induction_on with
  | hp => exact isClosed_le continuous_const (by fun_prop)
  | h u =>
    exact (dirichletForm_ofSmooth u u).ge.trans' (integral_nonneg fun x ↦ real_inner_self_nonneg)

/-- The squared `H¹` norm is the Dirichlet energy plus the squared `L²` norm. -/
theorem norm_sq_eq_dirichletForm_add (w : SobolevH1 I M) :
    ‖w‖ ^ 2 = dirichletForm w w + ‖toLp w‖ ^ 2 := by
  rw [dirichletForm_apply, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    sub_add_cancel]

/-- The Dirichlet form vanishes against the constant function `1`. -/
@[simp]
theorem dirichletForm_ofSmooth_one (w : SobolevH1 I M) :
    dirichletForm w (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) = 0 := by
  refine induction_on w (isClosed_eq (by fun_prop) continuous_const) fun u ↦ ?_
  rw [dirichletForm_ofSmooth, ContMDiffMap.coe_one, Pi.one_def, mgradient_const]
  simp

/-! ### Green's identity -/

section Green

variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The function `φ - Δφ` for a smooth function `φ`, as a continuous function. -/
private def subLaplaceBeltrami (φ : C^∞⟮I, M; ℝ⟯) : C(M, ℝ) :=
  ⟨fun x ↦ φ x - laplaceBeltrami I φ x,
    (map_continuous φ).sub (continuous_laplaceBeltrami (φ.contMDiff.of_le (by simp)))⟩

/-- Green's identity on `H¹(M)`, with the right-hand side as an `L²` inner product. -/
private theorem inner_ofSmooth_right_eq_inner (w : SobolevH1 I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ⟪w, ofSmooth φ⟫_ℝ =
      ⟪toLp w, ContinuousMap.toLp 2 (riemannianVolume I M) ℝ (subLaplaceBeltrami φ)⟫_ℝ := by
  refine induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
  have hu := u.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  have hφ := φ.contMDiff.of_le (n := ∞) (m := 2) (by simp)
  have hΔ := continuous_laplaceBeltrami hφ
  rw [inner_ofSmooth, toLp_ofSmooth, ContinuousMap.inner_toLp]
  simp only [subLaplaceBeltrami, ContinuousMap.coe_mk, conj_trivial, sub_mul]
  rw [integral_sub (f := fun x ↦ φ x * u x) (g := fun x ↦ laplaceBeltrami I φ x * u x)
      ((map_continuous φ).mul (map_continuous u)).integrable_of_compactSpace
      (hΔ.mul (map_continuous u)).integrable_of_compactSpace]
  simp_rw [mul_comm (laplaceBeltrami I φ _) (u _), mul_comm (φ _) (u _)]
  rw [integral_mul_laplaceBeltrami hu (HasCompactSupport.of_compactSpace _) hφ, sub_neg_eq_add]

/-- **Green's identity on `H¹(M)`.** On a closed manifold with a `C¹` metric, for `w ∈ H¹(M)` and a
smooth function `φ`, `⟪w, φ⟫_{H¹} = ∫ w (φ - Δφ) dV`, where `Δ = div grad`. -/
theorem inner_ofSmooth_right (w : SobolevH1 I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ⟪w, ofSmooth φ⟫_ℝ =
      ∫ x, toLp w x * (φ x - laplaceBeltrami I φ x) ∂riemannianVolume I M := by
  rw [inner_ofSmooth_right_eq_inner, L2.inner_toLp_continuousMap]
  simp only [subLaplaceBeltrami, ContinuousMap.coe_mk, conj_trivial, mul_comm (_ - _)]

/-- **The value map is injective.** An element of `H¹(M)` whose value in `L²(M)` vanishes is
zero, so `H¹(M)` is a subspace of `L²(M)`. -/
theorem toLp_injective : Function.Injective (toLp (I := I) (M := M)) := by
  refine (injective_iff_map_eq_zero toLp).2 fun w hw ↦ ?_
  -- By Green's identity `w` is orthogonal to the dense set of smooth functions.
  refine denseRange_ofSmooth.eq_zero_of_inner_left ℝ fun φ ↦ ?_
  rw [inner_ofSmooth_right_eq_inner, hw, inner_zero_left]

/-- The value of `w ∈ H¹(M)` in `L²(M)` vanishes exactly when `w` does. -/
@[simp]
theorem toLp_eq_zero_iff {w : SobolevH1 I M} : toLp w = 0 ↔ w = 0 :=
  toLp_injective.eq_iff' (map_zero _)

/-- The value of `w ∈ H¹(M)` has positive `L²` norm exactly when `w ≠ 0`. -/
theorem norm_toLp_pos_iff {w : SobolevH1 I M} : 0 < ‖toLp w‖ ↔ w ≠ 0 := by
  rw [norm_pos_iff, Ne, toLp_eq_zero_iff]

/-- An element of `H¹(M)` agrees almost everywhere in `L²(M)` with a smooth function `u`
if and only if it equals `ofSmooth u`. -/
@[simp]
theorem toLp_ae_eq_iff_eq_ofSmooth {w : SobolevH1 I M} {u : C^∞⟮I, M; ℝ⟯} :
    toLp w =ᵐ[riemannianVolume I M] u ↔ w = ofSmooth u :=
  ⟨fun hwu ↦ toLp_injective (Lp.ext (hwu.trans (toLp_ofSmooth_ae_eq u).symm)),
    fun h ↦ h ▸ toLp_ofSmooth_ae_eq u⟩

/-- **The Dirichlet form against a smooth function.** On a closed manifold with a `C¹` metric,
`D(w, φ) = ∫ w Δ⁺φ dV` for `w ∈ H¹(M)` and a smooth function `φ`, where `Δ⁺ = -div grad` is the
nonnegative Laplacian. -/
theorem dirichletForm_ofSmooth_right (w : SobolevH1 I M) (φ : C^∞⟮I, M; ℝ⟯) :
    dirichletForm w (ofSmooth φ) =
      ∫ x, toLp w x * -laplaceBeltrami I φ x ∂riemannianVolume I M := by
  rw [dirichletForm_apply, inner_ofSmooth_right_eq_inner, toLp_ofSmooth, ← inner_sub_right,
    ← map_sub, L2.inner_toLp_continuousMap]
  simp [subLaplaceBeltrami, mul_comm]

end Green

/-! ### Density of the values in `L²(M)` -/

/-- **The values of `H¹(M)` are dense in `L²(M)`.** A function in `L²(M)` orthogonal to the values
of all smooth functions has zero integral against every smooth function, so it vanishes almost
everywhere. -/
theorem denseRange_toLp [IsManifold I ∞ M] [T2Space M] :
    DenseRange (toLp (I := I) (M := M)) := by
  set J : SobolevH1 I M →ₗ[ℝ] Lp ℝ 2 (riemannianVolume I M) := (toLp (I := I) (M := M)).toLinearMap
  have hK : (LinearMap.range J)ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun f hf ↦ Lp.eq_zero_iff_ae_eq_zero.2 ?_
    have h (φ : C^∞⟮I, M; ℝ⟯) : ∫ x, φ x • f x ∂riemannianVolume I M = 0 := by
      have h := Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self J (ofSmooth φ)) hf
      rw [ContinuousLinearMap.coe_coe, toLp_ofSmooth, L2.inner_toLp_continuousMap] at h
      simpa only [ContinuousMap.coe_ofClass, conj_trivial, smul_eq_mul] using h
    exact ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      ((Lp.memLp f).locallyIntegrable one_le_two) fun g hg _ ↦ h ⟨g, hg⟩
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hK)
  rwa [LinearMap.coe_range, ContinuousLinearMap.coe_coe] at hd

end SobolevH1

end TauCeti.Manifold
