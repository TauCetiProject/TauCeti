/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.DifferentialOperator
public import TauCeti.MeasureTheory.Function.LpSection.Dense
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# The Sobolev space `H¹` of sections of a vector bundle with a connection

Let `V` be a smooth real vector bundle of finite rank with a smooth fibre metric over a compact
manifold `M` with a smooth Riemannian metric and its Riemannian volume `dV`, and let `∇` be a smooth
connection on `V`. The Sobolev space `H¹(V)` (`CovariantDerivative.SobolevH1 ∇`) is the completion
of the smooth sections of `V` for the inner product

`⟪σ, τ⟫_{H¹} = ∫ ⟪σ, τ⟫ dV + ∫ ⟪∇σ, ∇τ⟫ dV`,

where `⟪∇σ, ∇τ⟫` is the pointwise Hilbert–Schmidt inner product of the covariant derivatives
(`CovariantDerivative.innerCovariantDerivative`). It is a real Hilbert space in which the smooth
sections are dense (`CovariantDerivative.SobolevH1.denseRange_ofSmooth`) and embed injectively
(`CovariantDerivative.SobolevH1.ofSmooth_injective`). It is the analogue for sections of a bundle
of the space `TauCeti.Manifold.SobolevH1` of functions.

The inclusion of the smooth sections into the space `L²(V)` of square-integrable sections
(`TauCeti.LpSection`) does not increase norms, so it extends to a continuous linear map
`CovariantDerivative.SobolevH1.toLp : H¹(V) →L[ℝ] L²(V)`, the value of an element of `H¹(V)`.
Its range is dense, since the smooth sections are dense in `L²(V)`
(`CovariantDerivative.SobolevH1.denseRange_toLp`).

The **energy form** `CovariantDerivative.SobolevH1.energyForm` is the continuous bilinear form
`⟪w, v⟫_{H¹} - ⟪w, v⟫_{L²}` on `H¹(V)`. It extends `∫ ⟪∇σ, ∇τ⟫ dV` from smooth sections, and it is
symmetric and nonnegative, so that `H¹(V)` with its value map and its energy form is the setting
in which the rough Laplacian `∇*∇` is realized as a self-adjoint operator on `L²(V)`.

When `M` has no boundary and `∇` is compatible with the metric, the energy identity
`∫ ⟪∇*∇ φ, σ⟫ dV = ∫ ⟪∇φ, ∇σ⟫ dV` for smooth sections
(`CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian`) extends by continuity to
**Green's identity** on `H¹(V)`: for `w ∈ H¹(V)` and a smooth section `φ`,

`⟪w, φ⟫_{H¹} = ⟪w, φ + ∇*∇ φ⟫_{L²}`

(`CovariantDerivative.SobolevH1.inner_ofSmooth_right`), where `∇*∇` is the rough Laplacian built
with the Levi-Civita connection (`CovariantDerivative.smoothRoughLaplacian`). Consequently an
element of `H¹(V)` with value zero is orthogonal to the dense set of smooth sections, so `toLp` is
injective (`CovariantDerivative.SobolevH1.toLp_injective`), and `H¹(V)` is a subspace of `L²(V)`.

## Main definitions

* `CovariantDerivative.SobolevH1 ∇`: the Sobolev space `H¹(V)`, with
  `CovariantDerivative.SobolevH1.ofSmooth ∇` the inclusion of the smooth sections.
* `CovariantDerivative.SobolevH1.toLp`: the value map `H¹(V) → L²(V)`.
* `CovariantDerivative.SobolevH1.energyForm`: the energy form `∫ ⟪∇w, ∇v⟫ dV`.

## Main results

* `CovariantDerivative.SobolevH1.inner_ofSmooth`: the `H¹` inner product of smooth sections.
* `CovariantDerivative.SobolevH1.ofSmooth_injective`: smooth sections embed into `H¹(V)`.
* `CovariantDerivative.SobolevH1.inner_toLp_ofSmooth`: the `L²` inner product of their values.
* `CovariantDerivative.SobolevH1.energyForm_ofSmooth`: the energy form of smooth sections is
  `∫ ⟪∇σ, ∇τ⟫ dV`; it is symmetric (`CovariantDerivative.SobolevH1.energyForm_comm`) and
  nonnegative (`CovariantDerivative.SobolevH1.energyForm_self_nonneg`).
* `CovariantDerivative.SobolevH1.denseRange_toLp`: the values of `H¹(V)` are dense in `L²(V)`.
* `CovariantDerivative.SobolevH1.inner_ofSmooth_right`: Green's identity.
* `CovariantDerivative.SobolevH1.energyForm_ofSmooth_right`: the energy form against a smooth
  section `φ` is the `L²` pairing with `∇*∇ φ`.
* `CovariantDerivative.SobolevH1.toLp_injective`: the value map is injective.

## Implementation notes

The pre-completion inner product space `CovariantDerivative.PreSobolevH1 ∇`, a type synonym of the
smooth sections carrying the `H¹` inner product of `∇` before taking the completion, follows the
pattern of `TauCeti.Manifold.PreSobolevH1` and of Mathlib's `PositiveLinearMap.PreGNS`.

## References

* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter III, §2 (Sobolev spaces of sections defined through a connection).
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), §2.1.
-/

public section

open Bundle MeasureTheory TauCeti
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The smooth sections of `V`, as the space on which the `H¹` inner product of the connection
`∇` is defined before completion. -/
def PreSobolevH1 (_cov : CovariantDerivative I F V) : Type _ := Cₛ^∞⟮I; F, V⟯

variable (cov : CovariantDerivative I F V)

instance : AddCommGroup cov.PreSobolevH1 := inferInstanceAs (AddCommGroup Cₛ^∞⟮I; F, V⟯)

instance : Module ℝ cov.PreSobolevH1 := inferInstanceAs (Module ℝ Cₛ^∞⟮I; F, V⟯)

namespace PreSobolevH1

/-- A smooth section, as an element of `PreSobolevH1`. -/
def toPreSobolevH1 : Cₛ^∞⟮I; F, V⟯ ≃ₗ[ℝ] cov.PreSobolevH1 := LinearEquiv.refl ℝ _

/-- An element of `PreSobolevH1`, as a smooth section. -/
def ofPreSobolevH1 : cov.PreSobolevH1 ≃ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ := (toPreSobolevH1 cov).symm

@[simp]
theorem toPreSobolevH1_ofPreSobolevH1 (u : cov.PreSobolevH1) :
    toPreSobolevH1 cov (ofPreSobolevH1 cov u) = u :=
  (rfl)

@[simp]
theorem ofPreSobolevH1_toPreSobolevH1 (u : Cₛ^∞⟮I; F, V⟯) :
    ofPreSobolevH1 cov (toPreSobolevH1 cov u) = u :=
  (rfl)

end PreSobolevH1

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ F V] [IsContinuousRiemannianBundle F V]

/-- A smooth metric on the tangent bundle is continuous. -/
local instance instIsContinuousRiemannianBundleTangentSpaceSobolevH1 :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

namespace PreSobolevH1

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ContMDiffCovariantDerivative cov ∞]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ F V] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ContMDiffCovariantDerivative cov ∞] in
/-- The fibre inner product of two smooth sections is continuous. -/
private theorem continuous_inner (u v : Cₛ^∞⟮I; F, V⟯) : Continuous fun x ↦ ⟪u x, v x⟫_ℝ :=
  u.contMDiff.continuous.inner_bundle v.contMDiff.continuous

omit [IsContinuousRiemannianBundle F V] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The pointwise inner product `⟪∇u, ∇v⟫` of two smooth sections is continuous. -/
private theorem continuous_innerCovariantDerivative (u v : Cₛ^∞⟮I; F, V⟯) :
    Continuous (cov.innerCovariantDerivative u v) :=
  (cov.contMDiff_innerCovariantDerivative u.contMDiff v.contMDiff).continuous

omit [IsContMDiffRiemannianBundle I ∞ F V] in
/-- The integral `∫ ⟪u, w⟫ dV` of two smooth sections is additive in `u`. -/
private theorem integral_inner_add_left (u v w : Cₛ^∞⟮I; F, V⟯) :
    ∫ x, ⟪(u + v : Cₛ^∞⟮I; F, V⟯) x, w x⟫_ℝ ∂riemannianVolume I M =
      ∫ x, ⟪u x, w x⟫_ℝ ∂riemannianVolume I M + ∫ x, ⟪v x, w x⟫_ℝ ∂riemannianVolume I M := by
  simp only [ContMDiffSection.coe_add, Pi.add_apply, inner_add_left]
  exact integral_add (continuous_inner u w).integrable_of_compactSpace
    (continuous_inner v w).integrable_of_compactSpace

omit [IsContinuousRiemannianBundle F V] in
/-- The integral `∫ ⟪∇u, ∇w⟫ dV` of two smooth sections is additive in `u`. -/
private theorem integral_innerCovariantDerivative_add_left (u v w : Cₛ^∞⟮I; F, V⟯) :
    ∫ x, cov.innerCovariantDerivative ⇑(u + v : Cₛ^∞⟮I; F, V⟯) w x ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative u w x ∂riemannianVolume I M +
        ∫ x, cov.innerCovariantDerivative v w x ∂riemannianVolume I M := by
  rw [← integral_add (continuous_innerCovariantDerivative cov u w).integrable_of_compactSpace
    (continuous_innerCovariantDerivative cov v w).integrable_of_compactSpace]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [ContMDiffSection.coe_add]
  exact cov.innerCovariantDerivative_add_left ((u.contMDiff x).mdifferentiableAt (by simp))
    ((v.contMDiff x).mdifferentiableAt (by simp))

/-- The `H¹` pre-inner product `∫ ⟪u, v⟫ dV + ∫ ⟪∇u, ∇v⟫ dV` on smooth sections. -/
abbrev preInner : PreInnerProductSpace.Core ℝ cov.PreSobolevH1 where
  inner u v := ∫ x, ⟪ofPreSobolevH1 cov u x, ofPreSobolevH1 cov v x⟫_ℝ ∂riemannianVolume I M +
    ∫ x, cov.innerCovariantDerivative (ofPreSobolevH1 cov u) (ofPreSobolevH1 cov v) x
      ∂riemannianVolume I M
  conj_inner_symm u v := by
    simp only [conj_trivial, real_inner_comm (ofPreSobolevH1 cov u _),
      cov.innerCovariantDerivative_comm (ofPreSobolevH1 cov u)]
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real]
    exact add_nonneg (integral_nonneg fun x ↦ real_inner_self_nonneg)
      (integral_nonneg fun x ↦ cov.innerCovariantDerivative_self_nonneg _ x)
  add_left u v w := by
    simp only [map_add, integral_inner_add_left, integral_innerCovariantDerivative_add_left]
    ring
  smul_left u v r := by
    have h (x : M) : cov.innerCovariantDerivative (r • ⇑(ofPreSobolevH1 cov u))
        (ofPreSobolevH1 cov v) x =
        r * cov.innerCovariantDerivative (ofPreSobolevH1 cov u) (ofPreSobolevH1 cov v) x :=
      cov.innerCovariantDerivative_const_smul_left r
        (((ofPreSobolevH1 cov u).contMDiff x).mdifferentiableAt (by simp))
    simp only [map_smul, ContMDiffSection.coe_smul, Pi.smul_apply, real_inner_smul_left, h,
      conj_trivial, integral_const_mul]
    ring

instance : SeminormedAddCommGroup cov.PreSobolevH1 :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preInner cov)

instance : InnerProductSpace ℝ cov.PreSobolevH1 :=
  InnerProductSpace.ofCore (preInner cov)

/-- The `H¹` inner product of two smooth sections. -/
theorem inner_toPreSobolevH1 (u v : Cₛ^∞⟮I; F, V⟯) :
    ⟪toPreSobolevH1 cov u, toPreSobolevH1 cov v⟫_ℝ =
      ∫ x, ⟪u x, v x⟫_ℝ ∂riemannianVolume I M +
        ∫ x, cov.innerCovariantDerivative u v x ∂riemannianVolume I M :=
  (rfl)

end PreSobolevH1

open PreSobolevH1

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ContMDiffCovariantDerivative cov ∞]

/-- The **Sobolev space** `H¹(V)` of a smooth connection `∇` on a vector bundle with a fibre
metric over a compact Riemannian manifold: the completion of the smooth sections of `V` for the
inner product `⟪σ, τ⟫_{H¹} = ∫ ⟪σ, τ⟫ dV + ∫ ⟪∇σ, ∇τ⟫ dV`. -/
abbrev SobolevH1 := UniformSpace.Completion cov.PreSobolevH1

namespace SobolevH1

/-- The inclusion of the smooth sections into `H¹(V)`. -/
def ofSmooth : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] cov.SobolevH1 :=
  UniformSpace.Completion.toComplL.toLinearMap ∘ₗ (toPreSobolevH1 cov).toLinearMap

/-- A smooth section in `H¹(V)` is the image of its copy in the pre-completion space. -/
theorem ofSmooth_apply (u : Cₛ^∞⟮I; F, V⟯) :
    ofSmooth cov u = ((toPreSobolevH1 cov u : cov.PreSobolevH1) : cov.SobolevH1) :=
  (rfl)

/-- **The `H¹` inner product of smooth sections.** -/
@[simp]
theorem inner_ofSmooth (u v : Cₛ^∞⟮I; F, V⟯) :
    ⟪ofSmooth cov u, ofSmooth cov v⟫_ℝ =
      ∫ x, ⟪u x, v x⟫_ℝ ∂riemannianVolume I M +
        ∫ x, cov.innerCovariantDerivative u v x ∂riemannianVolume I M := by
  rw [ofSmooth_apply, ofSmooth_apply, UniformSpace.Completion.inner_coe, inner_toPreSobolevH1]

/-- The squared `H¹` norm of a smooth section is `∫ |u|² dV + ∫ |∇u|² dV`. -/
theorem norm_ofSmooth_sq (u : Cₛ^∞⟮I; F, V⟯) :
    ‖ofSmooth cov u‖ ^ 2 =
      ∫ x, ‖u x‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, cov.innerCovariantDerivative u u x ∂riemannianVolume I M := by
  rw [← real_inner_self_eq_norm_sq, inner_ofSmooth]
  simp only [real_inner_self_eq_norm_sq]

/-- The smooth sections are dense in `H¹(V)`. -/
theorem denseRange_ofSmooth : DenseRange (ofSmooth cov) :=
  UniformSpace.Completion.denseRange_coe.comp (toPreSobolevH1 cov).surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

variable {cov}

/-- **Induction principle for `H¹(V)`.** A closed property of elements of `H¹(V)` that holds for
all smooth sections holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : cov.SobolevH1 → Prop} (w : cov.SobolevH1) (hp : IsClosed {w | p w})
    (h : ∀ u : Cₛ^∞⟮I; F, V⟯, p (ofSmooth cov u)) : p w :=
  (denseRange_ofSmooth cov).induction_on w hp h

/-! ### The value in `L²` -/

variable [SecondCountableTopology M] [FiniteDimensional ℝ F]

/-- The class in `L²(V)` of a smooth section. -/
private def smoothToLp : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] LpSection ℝ F V 2 (riemannianVolume I M) where
  toFun u := LpSection.ofCompactlySupported ℝ I 2 (riemannianVolume I M)
    ⟨u, by simp⟩
  map_add' u v := map_add (LpSection.ofCompactlySupported ℝ I 2 (riemannianVolume I M))
    ⟨u, by simp⟩ ⟨v, by simp⟩
  map_smul' c u := by
    simpa using LpSection.ofCompactlySupported_smul (𝕜 := ℝ) (p := 2) (μ := riemannianVolume I M) c
      ⟨u, by simp⟩

omit [IsContMDiffRiemannianBundle I ∞ F V] [FiniteDimensional ℝ F] in
private theorem smoothToLp_apply (u : Cₛ^∞⟮I; F, V⟯) :
    smoothToLp u = LpSection.ofCompactlySupported ℝ I 2 (riemannianVolume I M)
      ⟨u, by simp⟩ :=
  (rfl)

omit [IsContMDiffRiemannianBundle I ∞ F V] [FiniteDimensional ℝ F] in
/-- The `L²` inner product of the classes of two smooth sections is `∫ ⟪u, v⟫ dV`. -/
private theorem inner_smoothToLp (u v : Cₛ^∞⟮I; F, V⟯) :
    ⟪smoothToLp u, smoothToLp v⟫_ℝ = ∫ x, ⟪u x, v x⟫_ℝ ∂riemannianVolume I M := by
  rw [smoothToLp_apply, smoothToLp_apply, LpSection.ofCompactlySupported_apply,
    LpSection.ofCompactlySupported_apply, LpSection.inner_mk]

variable (cov) in
/-- The inclusion of the smooth sections into `L²(V)`, on the pre-completion space. -/
private def preToLp : cov.PreSobolevH1 →L[ℝ] LpSection ℝ F V 2 (riemannianVolume I M) :=
  LinearMap.mkContinuous (smoothToLp ∘ₗ (ofPreSobolevH1 cov).toLinearMap) 1 fun u ↦ by
    obtain ⟨u, rfl⟩ := (toPreSobolevH1 cov).surjective u
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_toPreSobolevH1]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      ofPreSobolevH1_toPreSobolevH1, inner_smoothToLp]
    exact le_add_of_nonneg_right
      (integral_nonneg fun x ↦ cov.innerCovariantDerivative_self_nonneg _ x)

variable (cov) in
/-- The **value** of an element of `H¹(V)` in `L²(V)`: the continuous extension of the inclusion
of the smooth sections into `L²(V)`. -/
def toLp : cov.SobolevH1 →L[ℝ] LpSection ℝ F V 2 (riemannianVolume I M) :=
  (preToLp cov).fromCompletion

/-- The value of a smooth section in `L²(V)` is its class. -/
theorem toLp_ofSmooth (u : Cₛ^∞⟮I; F, V⟯) :
    toLp cov (ofSmooth cov u) = LpSection.ofCompactlySupported ℝ I 2 (riemannianVolume I M)
      ⟨u, by simp⟩ := by
  rw [toLp, ofSmooth_apply, ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The value of a smooth section in `L²(V)` is almost everywhere equal to the section. -/
theorem toLp_ofSmooth_ae_eq (u : Cₛ^∞⟮I; F, V⟯) :
    ∀ᵐ x ∂riemannianVolume I M, toLp cov (ofSmooth cov u) x = u x := by
  rw [toLp_ofSmooth]
  exact LpSection.coeFn_ofCompactlySupported _

/-- The `L²` inner product of the values of two smooth sections is `∫ ⟪u, v⟫ dV`. -/
@[simp]
theorem inner_toLp_ofSmooth (u v : Cₛ^∞⟮I; F, V⟯) :
    ⟪toLp cov (ofSmooth cov u), toLp cov (ofSmooth cov v)⟫_ℝ =
      ∫ x, ⟪u x, v x⟫_ℝ ∂riemannianVolume I M := by
  rw [toLp_ofSmooth, toLp_ofSmooth, ← smoothToLp_apply, ← smoothToLp_apply, inner_smoothToLp]

/-- **Smooth sections embed into `H¹(V)`.** Two smooth sections with the same image in `H¹(V)`
have the same class in `L²(V)`, hence agree, since the Riemannian volume charges every nonempty
open set. -/
theorem ofSmooth_injective : Function.Injective (ofSmooth cov) := fun u v huv ↦ by
  have h := congrArg (toLp cov) huv
  rw [toLp_ofSmooth, toLp_ofSmooth] at h
  exact congrArg Subtype.val (LpSection.ofCompactlySupported_injective h)

/-- A smooth section is zero in `H¹(V)` if and only if it is zero. -/
@[simp]
theorem ofSmooth_eq_zero_iff {u : Cₛ^∞⟮I; F, V⟯} : ofSmooth cov u = 0 ↔ u = 0 :=
  map_eq_zero_iff _ ofSmooth_injective

/-- The value map does not increase norms: `‖w‖_{L²} ≤ ‖w‖_{H¹}`. -/
theorem norm_toLp_le (w : cov.SobolevH1) : ‖toLp cov w‖ ≤ ‖w‖ := by
  induction w using induction_on with
  | hp => exact isClosed_le (toLp cov).continuous.norm continuous_norm
  | h u =>
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_toLp_ofSmooth, inner_ofSmooth]
    exact le_add_of_nonneg_right
      (integral_nonneg fun x ↦ cov.innerCovariantDerivative_self_nonneg _ x)

/-- **The values of `H¹(V)` are dense in `L²(V)`**, since the smooth sections are. -/
theorem denseRange_toLp [T2Space M] [ContMDiffVectorBundle ∞ F V I] : DenseRange (toLp cov) := by
  refine (LpSection.denseRange_ofCompactlySupported (𝕜 := ℝ) (I := I) (F := F) (E := V)
    (p := 2) (μ := riemannianVolume I M) ENNReal.ofNat_ne_top).mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨ofSmooth cov u, toLp_ofSmooth (u : Cₛ^∞⟮I; F, V⟯)⟩

/-! ### The energy form -/

/-- The **energy form** `Q(w, v) = ⟪w, v⟫_{H¹} - ⟪w, v⟫_{L²}` on `H¹(V)`, the continuous
extension of `∫ ⟪∇σ, ∇τ⟫ dV` from smooth sections
(`CovariantDerivative.SobolevH1.energyForm_ofSmooth`). -/
def energyForm : cov.SobolevH1 →L[ℝ] cov.SobolevH1 →L[ℝ] ℝ :=
  innerSL ℝ - (innerSL ℝ).bilinearComp (toLp cov) (toLp cov)

/-- Unfolding lemma for `CovariantDerivative.SobolevH1.energyForm`. -/
theorem energyForm_apply (w v : cov.SobolevH1) :
    energyForm w v = ⟪w, v⟫_ℝ - ⟪toLp cov w, toLp cov v⟫_ℝ :=
  (rfl)

/-- The energy form of two smooth sections is `∫ ⟪∇σ, ∇τ⟫ dV`. -/
@[simp]
theorem energyForm_ofSmooth (u v : Cₛ^∞⟮I; F, V⟯) :
    energyForm (ofSmooth cov u) (ofSmooth cov v) =
      ∫ x, cov.innerCovariantDerivative u v x ∂riemannianVolume I M := by
  rw [energyForm_apply, inner_ofSmooth, inner_toLp_ofSmooth, add_sub_cancel_left]

/-- The energy form is symmetric. -/
theorem energyForm_comm (w v : cov.SobolevH1) : energyForm w v = energyForm v w := by
  rw [energyForm_apply, energyForm_apply, real_inner_comm, real_inner_comm (toLp cov w)]

/-- The energy form is nonnegative on the diagonal. -/
theorem energyForm_self_nonneg (w : cov.SobolevH1) : 0 ≤ energyForm w w := by
  induction w using induction_on with
  | hp => exact isClosed_le continuous_const (by fun_prop)
  | h u =>
    exact (energyForm_ofSmooth u u).ge.trans'
      (integral_nonneg fun x ↦ cov.innerCovariantDerivative_self_nonneg _ x)

/-- The squared `H¹` norm is the energy plus the squared `L²` norm. -/
theorem norm_sq_eq_energyForm_add (w : cov.SobolevH1) :
    ‖w‖ ^ 2 = energyForm w w + ‖toLp cov w‖ ^ 2 := by
  rw [energyForm_apply, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    sub_add_cancel]

/-! ### Green's identity -/

section Green

variable [I.Boundaryless] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- **Green's identity on `H¹(V)`.** For a metric connection `∇` on a bundle over a closed
manifold, `w ∈ H¹(V)` and a smooth section `φ`, `⟪w, φ⟫_{H¹} = ⟪w, φ + ∇*∇ φ⟫_{L²}`, where `∇*∇`
is the rough Laplacian built with the Levi-Civita connection. -/
theorem inner_ofSmooth_right (hcov : cov.IsMetricCompatible) (w : cov.SobolevH1)
    (φ : Cₛ^∞⟮I; F, V⟯) :
    ⟪w, ofSmooth cov φ⟫_ℝ = ⟪toLp cov w,
      toLp cov (ofSmooth cov (φ + cov.smoothRoughLaplacian (leviCivitaConnection I M) φ))⟫_ℝ := by
  refine induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
  rw [inner_ofSmooth, map_add, map_add, inner_add_right, inner_toLp_ofSmooth,
    inner_toLp_ofSmooth, add_right_inj]
  -- The energy identity `∫ ⟪∇*∇ φ, u⟫ dV = ∫ ⟪∇φ, ∇u⟫ dV`, read with both pairings swapped.
  have h := hcov.integral_inner_roughLaplacian φ.contMDiff u.contMDiff
    isClosed_closure.isCompact
  simp only [smoothRoughLaplacian_apply]
  rw [integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _), h]
  exact integral_congr_ae (.of_forall fun x ↦ cov.innerCovariantDerivative_comm _ _ x)

/-- **The energy form against a smooth section.** For a metric connection `∇` on a bundle over a
closed manifold, `Q(w, φ) = ⟪w, ∇*∇ φ⟫_{L²}` for `w ∈ H¹(V)` and a smooth section `φ`. -/
theorem energyForm_ofSmooth_right (hcov : cov.IsMetricCompatible) (w : cov.SobolevH1)
    (φ : Cₛ^∞⟮I; F, V⟯) :
    energyForm w (ofSmooth cov φ) = ⟪toLp cov w,
      toLp cov (ofSmooth cov (cov.smoothRoughLaplacian (leviCivitaConnection I M) φ))⟫_ℝ := by
  rw [energyForm_apply, inner_ofSmooth_right hcov, map_add, map_add, inner_add_right,
    add_sub_cancel_left]

/-- **The value map is injective.** For a metric connection on a bundle over a closed manifold,
an element of `H¹(V)` whose value in `L²(V)` vanishes is zero, so `H¹(V)` is a subspace of
`L²(V)`. -/
theorem toLp_injective (hcov : cov.IsMetricCompatible) : Function.Injective (toLp cov) := by
  refine (injective_iff_map_eq_zero (toLp cov)).2 fun w hw ↦ ?_
  -- By Green's identity `w` is orthogonal to the dense set of smooth sections.
  refine (denseRange_ofSmooth cov).eq_zero_of_inner_left ℝ fun φ ↦ ?_
  rw [inner_ofSmooth_right hcov, hw, inner_zero_left]

/-- The value of `w ∈ H¹(V)` in `L²(V)` vanishes exactly when `w` does. -/
theorem toLp_eq_zero_iff (hcov : cov.IsMetricCompatible) {w : cov.SobolevH1} :
    toLp cov w = 0 ↔ w = 0 :=
  (toLp_injective hcov).eq_iff' (map_zero _)

end Green

end SobolevH1

end CovariantDerivative
