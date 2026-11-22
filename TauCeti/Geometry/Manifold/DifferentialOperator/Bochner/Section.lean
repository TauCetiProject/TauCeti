/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Connection
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.DifferentialOperator
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Affine
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Bochner connection of an operator on the sections of a vector bundle

Let `V` be a smooth real vector bundle of finite rank over a Riemannian manifold `M`, let `c ≠ 0`
and let `P : Γ(V) → Γ(V)` be an operator on the smooth sections. A smooth connection `∇` on `V` is
a **Bochner connection** of `P` with constant `c` when

`P = c ∇*∇ + E`

for an operator `E` of order zero, in Grothendieck's sense (`TauCeti.differentialOperators`), that
is a bundle endomorphism; here `∇*∇` is the rough Laplacian of `∇`
(`CovariantDerivative.smoothRoughLaplacian`), built with the Levi-Civita connection on the tangent
bundle. Such a `P` is of Laplace type with constant `c` when `c > 0`. This file proves that every
operator of Laplace type has a Bochner connection (Gilkey, Lemma 2.1), that the Bochner connection
is unique, and that it is compatible with the fibre metric, with a fibrewise self-adjoint remainder
`E`, when `P` is formally self-adjoint for the Riemannian volume.

## Uniqueness

The commutator of the rough Laplacian with multiplication by a smooth function `f` is
`[∇*∇, f] σ = -2 ∇_{grad f} σ - (Δ f) σ`
(`CovariantDerivative.smulCommutator_smoothRoughLaplacian_apply`). An operator of order zero
commutes with multiplication, so if `∇*∇ - ∇'*∇'` has order zero then `∇_{grad f} = ∇'_{grad f}`
on smooth sections for every `f`. Every tangent vector is a gradient, so the difference
`∇ - ∇'` (`CovariantDerivative.difference`) vanishes. Conversely connections with the same values on
smooth sections have the same rough Laplacian.

## Existence

Let `∇` be any smooth connection. If `P` is of Laplace type, then `Q = P - c ∇*∇` has order at most
one, since `P` and `c ∇*∇` have the same principal symbol `ξ ↦ -(c ‖ξ‖²) Id`. The commutator of `Q`
with multiplication by `f` is then the operator of order zero `σ(Q)(df)`, where `σ(Q)` is the
principal symbol. By the commutator formula above, replacing `∇` by `∇ + A` changes `[c ∇*∇, f]` by
`-2 c A(·, grad f)`, so the endomorphism-valued one-form

`A(u, w) = -(2 c)⁻¹ σ(Q)(⟪w, ·⟫) u`

makes every commutator of `P - c (∇ + A)*(∇ + A)` with multiplication vanish. It is smooth since,
near each point, the gradients of finitely many functions form a frame of the tangent bundle, on
which `A` is given by commutators of `Q`.

## Metric compatibility

Suppose that `P` is its own formal adjoint for the Riemannian volume (`LinearMap.IsFormalAdjoint`).
Correcting `∇` by half its metric defect gives a metric connection `∇⁰ = ∇ + C`
(`CovariantDerivative.metricCorrected`), and the metric defect of `∇` is the symmetric part
`⟪C(u, w), v⟫ + ⟪u, C(v, w)⟫` of the correction `C` (`CovariantDerivative.metricCorrection`). For a
smooth function `f` with gradient `X`, the commutator `T = [P, f] = c (-2 ∇_X - Δ f)` is formally
skew-adjoint, and the operator of order zero

`B = ∇⁰_X + (2 c)⁻¹ T + ½ Δ f`,   `B σ = C(σ, X)`,

has formal adjoint `(-∇⁰_X - div X) - (2 c)⁻¹ T + ½ Δ f = -B`, using
`(∇⁰_X)* = -∇⁰_X - div X` for the metric connection `∇⁰`
(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField`) and `div X = Δ f`.
Formal adjoints of operators of order zero are pointwise adjoints, so `C(·, X)` is skew-adjoint at
every point, and the metric defect of `∇` vanishes. The remainder `E` is then the difference of
the formally self-adjoint operators `P` and `c ∇*∇`, hence fibrewise self-adjoint.

The canonical density matters: on the circle, `-∂ₓ² - cos x ∂ₓ` is formally self-adjoint for the
density `e^(sin x) dx`, but its Bochner connection `d + ½ cos x dx` is not metric.

## Main results

* `CovariantDerivative.smoothRoughLaplacian_sub_mem_differentialOperators_zero_iff`: two smooth
  connections have rough Laplacians differing by an operator of order zero exactly when their
  difference vanishes.
* `CovariantDerivative.difference_eq_zero_of_sub_smul_smoothRoughLaplacian_mem`: **uniqueness of
  the Bochner connection**.
* `CovariantDerivative.exists_sub_smul_smoothRoughLaplacian_mem_differentialOperators_zero`:
  **existence of the Bochner connection** when `P - c ∇*∇` has order at most one.
* `TauCeti.IsSectionLaplaceType.sub_smul_smoothRoughLaplacian_mem_differentialOperators_one`: an
  operator of Laplace type differs from `c ∇*∇` by an operator of order at most one.
* `TauCeti.IsSectionLaplaceType.exists_sub_smul_smoothRoughLaplacian_mem_differentialOperators_zero`
  : every operator of Laplace type has a Bochner connection.
* `LinearMap.IsFormalAdjoint.isMetricCompatible_of_sub_smul_smoothRoughLaplacian_mem`: the Bochner
  connection of a formally self-adjoint operator is metric.
* `LinearMap.IsFormalAdjoint.inner_sub_smul_smoothRoughLaplacian_apply`: its zeroth-order remainder
  is fibrewise self-adjoint.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2, Lemma 2.1 and the paragraph following it.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992,
  Proposition 2.5 (the connection and potential of a generalized Laplacian).
-/

public section

noncomputable section

open Bundle FiberBundle MeasureTheory TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace CovariantDerivative

section Bochner

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {cov cov' : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [ContMDiffCovariantDerivative cov' ∞]

/-! ### Uniqueness of the Bochner connection -/

/-- **Rough Laplacians determine connections.** The rough Laplacians of two smooth connections
`∇`, `∇'`, built with the Levi-Civita connection on the tangent bundle, differ by an operator of
order zero exactly when the connections are equal, that is their difference `∇ - ∇'` vanishes. -/
theorem smoothRoughLaplacian_sub_mem_differentialOperators_zero_iff :
    cov.smoothRoughLaplacian (leviCivitaConnection I M) -
        cov'.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0 ↔
    cov.difference cov' = 0 := by
  constructor
  · intro h
    -- The commutators with multiplication by `f` agree, so `∇_{grad f} σ = ∇'_{grad f} σ`.
    have hsmooth (σ : Cₛ^∞⟮I; F, V⟯) (x : M) (w : TangentSpace I x) : cov σ x w = cov' σ x w := by
      obtain ⟨f, hf⟩ := exists_contMDiffMap_mgradient_eq x w
      have hc := congrArg (fun Q ↦ Q σ x)
        (smulCommutator_eq_zero_of_mem_differentialOperators_zero h f)
      simp only [map_sub, LinearMap.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
        smulCommutator_smoothRoughLaplacian_apply, hf, LinearMap.zero_apply,
        ContMDiffSection.coe_zero, Pi.zero_apply] at hc
      have h2 : (2 : ℝ) • (cov σ x w - cov' σ x w) = 0 := by
        rw [← neg_eq_zero, ← hc]
        module
      exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)
    funext x
    ext v w
    obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq (I := I) (F := F) ∞ v
    rw [cov.difference_apply cov' ((hσ x).mdifferentiableAt (by simp))]
    simpa [sub_eq_zero] using hsmooth ⟨σ, hσ⟩ x w
  · intro h
    suffices heq : cov.smoothRoughLaplacian (leviCivitaConnection I M) =
        cov'.smoothRoughLaplacian (leviCivitaConnection I M) by
      rw [heq, sub_self]
      exact zero_mem _
    refine LinearMap.ext fun σ ↦ ContMDiffSection.ext fun x ↦ ?_
    simp only [smoothRoughLaplacian_apply]
    rw [roughLaplacian_congr cov _ cov' fun τ hτ ↦ funext fun y ↦ ?_]
    have hd := cov.difference_apply cov' ((hτ y).mdifferentiableAt (by simp))
    rw [h, Pi.zero_apply, zero_apply] at hd
    exact sub_eq_zero.1 hd.symm

/-- **Uniqueness of the Bochner connection.** If `P - c ∇*∇` and `P - c ∇'*∇'` are both operators
of order zero for smooth connections `∇`, `∇'` and a constant `c ≠ 0`, then `∇ = ∇'`: their
difference vanishes. The zeroth-order remainders are then equal as well. -/
theorem difference_eq_zero_of_sub_smul_smoothRoughLaplacian_mem
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯} {c : ℝ} (hc : c ≠ 0)
    (h : P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (h' : P - c • cov'.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0) :
    cov.difference cov' = 0 := by
  refine smoothRoughLaplacian_sub_mem_differentialOperators_zero_iff.1 ?_
  have e : cov.smoothRoughLaplacian (leviCivitaConnection I M) -
      cov'.smoothRoughLaplacian (leviCivitaConnection I M) =
        c⁻¹ • ((P - c • cov'.smoothRoughLaplacian (leviCivitaConnection I M)) -
          (P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M))) := by
    rw [sub_sub_sub_cancel_left, ← smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h' h)

/-! ### Existence of the Bochner connection -/

section Existence

variable [BoundarylessManifold I M]
  {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}

/-- The principal symbol at `x` of a first-order operator `Q`, as a linear map in the covector. -/
private def bochnerSymbol
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] V x →ₗ[ℝ] V x where
  toFun := sectionPrincipalSymbol I BoundarylessManifold.isInteriorPoint ⟨Q, hQ⟩
  map_add' := sectionPrincipalSymbol_add_covector _ ⟨Q, hQ⟩
  map_smul' a ξ := by simpa using sectionPrincipalSymbol_smul_covector _ ⟨Q, hQ⟩ a ξ

/-- The endomorphism-valued one-form `A(u, w) = -(2 c)⁻¹ σ(Q)(⟪w, ·⟫) u` built from the principal
symbol of a first-order operator `Q`. For `Q = P - c ∇*∇`, adding it to `∇` absorbs `Q` into the
rough Laplacian. -/
private def bochnerForm
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1) (c : ℝ)
    (x : M) : V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  -- The fibres of `V` are finite-dimensional and Hausdorff, so linear maps out of them are
  -- continuous.
  haveI := FiberBundle.t2Space F V x
  haveI := VectorBundle.finiteDimensional ℝ F V x
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (TangentSpace I x →ₗ[ℝ] V x) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun u w ↦ -(2 * c)⁻¹ • bochnerSymbol hQ x (innerSL ℝ w) u)
        (fun u u' w ↦ by simp [smul_add]) (fun a u w ↦ by simp [smul_comm a])
        (fun u w w' ↦ by simp [smul_add]) (fun a u w ↦ by simp [smul_comm a]))

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- On a gradient, the one-form is a commutator: `A(s, grad f) = -(2 c)⁻¹ [Q, f] s`. -/
private theorem bochnerForm_apply_mgradient
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1) (c : ℝ)
    (f : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    bochnerForm hQ c x (s x) (mgradient I f x) = -(2 * c)⁻¹ • (Q (f • s) x - f x • Q s x) := by
  have hξ : innerSL ℝ (mgradient I f x) = mvfderiv I f x :=
    ContinuousLinearMap.ext fun v ↦ by rw [innerSL_apply_apply, inner_mgradient]
  have h := sectionPrincipalSymbol_mvfderiv_of_order_one (x := x)
    BoundarylessManifold.isInteriorPoint ⟨Q, hQ⟩ f s
  simp only [bochnerForm, bochnerSymbol, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.mk₂_apply,
    LinearMap.coe_mk, AddHom.coe_mk, hξ]
  rw [h]

/-- The one-form is smooth: near each point, the gradients of finitely many functions form a frame
of the tangent bundle, and on that frame it is given by commutators of `Q`. -/
private theorem contMDiff_bochnerForm
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1) (c : ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun y ↦ V y →L[ℝ] TangentSpace I y →L[ℝ] V y) x (bochnerForm hQ c x)) := by
  -- `∞ + 1 = ∞` holds by `rfl`, but instance search does not see it.
  have : IsManifold I (∞ + 1) M := ‹IsManifold I ∞ M›
  refine (Manifold.contMDiff_hom_iff _).2 fun s hs ↦
    (Manifold.contMDiff_hom_iff fun x ↦ bochnerForm hQ c x (s x)).2 fun W hW x₀ ↦ ?_
  -- Functions whose gradients at `x₀` form a basis of the tangent space.
  let b := Module.finBasis ℝ (TangentSpace I x₀)
  choose f hf using fun k ↦ exists_contMDiffMap_mgradient_eq x₀ (b k)
  have hb : (fun k ↦ mgradient I (f k) x₀) = ⇑b := funext hf
  obtain ⟨U, -, hU, hx₀, hfr⟩ := IsLocalFrameOn.exists_of_linearIndependent isOpen_univ
    (fun k ↦ (contMDiff_mgradient_infty (f k).contMDiff).contMDiffOn) (Set.mem_univ x₀)
    (hb ▸ b.linearIndependent) (hb ▸ b.span_eq.ge)
  -- Near `x₀`, `A(s, W) = ∑ₖ Wₖ A(s, grad fₖ)` with smooth coefficients `Wₖ`.
  let s' : Cₛ^∞⟮I; F, V⟯ := ⟨s, hs⟩
  let τ (k : Fin (Module.finrank ℝ (TangentSpace I x₀))) : Cₛ^∞⟮I; F, V⟯ :=
    (-(2 * c)⁻¹) • (Q (f k • s') - f k • Q s')
  have hsum : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞
      (fun x ↦ TotalSpace.mk' F x (∑ k, hfr.coeff k x (W x) • τ k x)) x₀ :=
    ContMDiffAt.sum_section fun k _ ↦
      ((hfr.contMDiffOn_coeff hU le_rfl hW.contMDiffOn k).contMDiffAt (hU.mem_nhds hx₀))
        |>.smul_section ((τ k).contMDiff x₀)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀] with x hx
  refine congrArg (TotalSpace.mk' F x) ?_
  conv_lhs => rw [hfr.coeff_sum_eq W hx]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg _ ?_
  rw [show s x = s' x from rfl, bochnerForm_apply_mgradient hQ c (f k) s' x]
  simp [τ, ContMDiffSection.smul_apply]

/-- **Existence of the Bochner connection.** Let `∇` be a smooth connection on `V` and `c ≠ 0`. If
`P - c ∇*∇` is an operator of order at most one, then there is a smooth connection `∇'` for which
`P - c ∇'*∇'` has order zero. It is `∇ + A` for the endomorphism-valued one-form
`A(u, w) = -(2 c)⁻¹ σ(P - c ∇*∇)(⟪w, ·⟫) u` built from the principal symbol of `P - c ∇*∇`, which
absorbs its first-order part. -/
theorem exists_sub_smul_smoothRoughLaplacian_mem_differentialOperators_zero
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯} {c : ℝ} (hc : c ≠ 0)
    (h1 : P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1) :
    ∃ (cov' : _root_.CovariantDerivative I F V) (_ : ContMDiffCovariantDerivative cov' ∞),
      P - c • cov'.smoothRoughLaplacian (leviCivitaConnection I M) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0 := by
  set Q := P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M)
  -- The commutators of `P - c (∇ + A)*(∇ + A)` with multiplication vanish.
  refine ⟨cov.addOneForm (bochnerForm h1 c),
    (inferInstance : ContMDiffCovariantDerivative cov ∞).addOneForm (contMDiff_bochnerForm h1 c),
    mem_differentialOperators_zero_iff_smulCommutator.2 fun f ↦
      LinearMap.ext fun σ ↦ ContMDiffSection.ext fun x ↦ ?_⟩
  have hP : P = Q + c • cov.smoothRoughLaplacian (leviCivitaConnection I M) :=
    (sub_add_cancel _ _).symm
  have hQc : smulCommutator ℝ f Q σ x = Q (f • σ) x - f x • Q σ x := by
    simp [smulCommutator_apply_apply, ContMDiffSection.smul_apply]
  rw [hP, map_sub, map_add, map_smul, map_smul]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, LinearMap.zero_apply, ContMDiffSection.coe_zero, Pi.zero_apply,
    smulCommutator_smoothRoughLaplacian_apply, addOneForm_apply, add_apply,
    bochnerForm_apply_mgradient h1 c f σ x, hQc]
  match_scalars <;> field_simp <;> ring

end Existence

end Bochner

end CovariantDerivative

/-! ### Operators of Laplace type -/

namespace TauCeti.IsSectionLaplaceType

open CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [BoundarylessManifold I M]
  {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2} {c : ℝ}

/-- An operator `P` of Laplace type with constant `c` differs from `c ∇*∇` by an operator of order
at most one, for every smooth connection `∇`: both have principal symbol `ξ ↦ -(c ‖ξ‖²) Id`. -/
theorem sub_smul_smoothRoughLaplacian_mem_differentialOperators_one
    (hP : IsSectionLaplaceType P c) (cov : _root_.CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) -
        c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  set L : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ (1 + 1) :=
    ⟨_, cov.smoothRoughLaplacian_mem_differentialOperators_two (leviCivitaConnection I M)⟩
  refine (forall_sectionPrincipalSymbol_eq_zero_iff (P - c • L)).1 fun x ξ ↦ ?_
  rw [sectionPrincipalSymbol_sub, sectionPrincipalSymbol_smul, hP.sectionPrincipalSymbol_eq,
    sectionPrincipalSymbol_smoothRoughLaplacian, smul_smul]
  simp

/-- **Every operator of Laplace type has a Bochner connection** (Gilkey, Lemma 2.1). If `P` is of
Laplace type with constant `c` on a bundle with a smooth connection, then there is a smooth
connection `∇'` for which `P - c ∇'*∇'` is an operator of order zero. It is unique by
`CovariantDerivative.difference_eq_zero_of_sub_smul_smoothRoughLaplacian_mem`. -/
theorem exists_sub_smul_smoothRoughLaplacian_mem_differentialOperators_zero
    (hP : IsSectionLaplaceType P c) (cov : _root_.CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] :
    ∃ (cov' : _root_.CovariantDerivative I F V) (_ : ContMDiffCovariantDerivative cov' ∞),
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) -
          c • cov'.smoothRoughLaplacian (leviCivitaConnection I M) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0 :=
  CovariantDerivative.exists_sub_smul_smoothRoughLaplacian_mem_differentialOperators_zero
    hP.pos.ne' (hP.sub_smul_smoothRoughLaplacian_mem_differentialOperators_one cov)

end TauCeti.IsSectionLaplaceType

/-! ### Formally self-adjoint operators -/

namespace LinearMap.IsFormalAdjoint

open CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯} {c : ℝ}

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle I ∞ F V] [I.Boundaryless]
  [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- An operator differing from `c ∇*∇` by an operator of order zero has order at most two. -/
private theorem mem_differentialOperators_two_of_sub_smul_smoothRoughLaplacian_mem
    (h0 : P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0) :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2 := by
  simpa using add_mem (differentialOperators_mono (by norm_num : 0 ≤ 2) h0)
    (Submodule.smul_mem _ c
      (cov.smoothRoughLaplacian_mem_differentialOperators_two (leviCivitaConnection I M)))

omit [FiniteDimensional ℝ F] [I.Boundaryless] in
/-- Covariant derivatives along gradients behave as for a metric connection: if `P` is its own
formal adjoint for the Riemannian volume and `P - c ∇*∇` has order zero with `c ≠ 0`, then the
formal adjoint of `∇_X` for `X = grad f` is `-∇_X - div X`. Indeed `[P, f] = c (-2 ∇_X - Δ f)` is
formally skew-adjoint, and `div X = Δ f`. -/
private theorem isFormalAdjoint_alongVectorField_of_sub_smul_smoothRoughLaplacian_mem
    (hP : P.IsFormalAdjoint P (riemannianVolume I M)) (hc : c ≠ 0)
    (h0 : P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (f : C^∞⟮I, M; ℝ⟯) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : ⇑X = mgradient I f) :
    (cov.alongVectorField X).IsFormalAdjoint (-cov.alongVectorField X -
      Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ (smoothDivergence I M X)) (riemannianVolume I M) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  set Γ := differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯
  have hsupp {m : ℕ} {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯} (hQ : Q ∈ Γ m) :
      ∀ s, (Q s).tsupport ⊆ s.tsupport :=
    tsupport_differentialOperators_section_apply_subset hQ
  have hP2 : P ∈ Γ 2 := mem_differentialOperators_two_of_sub_smul_smoothRoughLaplacian_mem h0
  let Δf := smoothLaplaceBeltrami I M f
  let T := TauCeti.smulCommutator ℝ f P
  let lsmul : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] Module.End ℝ Cₛ^∞⟮I; F, V⟯ := Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯
  -- The commutator `[P, f] = c [∇*∇, f]` is `c (-2 ∇_X - Δ f)`.
  have hT (σ : Cₛ^∞⟮I; F, V⟯) (y : M) :
      T σ y = c • (-(2 : ℝ) • cov σ y (X y) - Δf y • σ y) := by
    have hR := congrArg (fun Q ↦ Q σ y)
      (smulCommutator_eq_zero_of_mem_differentialOperators_zero h0 f)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smulCommutator_smoothRoughLaplacian_apply, LinearMap.zero_apply, ContMDiffSection.coe_zero,
      Pi.zero_apply] at hR
    simpa [T, hX, Δf, sub_eq_zero] using hR
  have hT1 : T ∈ Γ 1 := smulCommutator_mem_differentialOperators hP2 f
  have hl1 : lsmul Δf ∈ Γ 1 :=
    differentialOperators_le_succ 0 <|
      mem_differentialOperators_zero_iff.2 fun b σ ↦ smul_comm Δf b σ
  -- `∇_X = -(2 c)⁻¹ (T + c Δ f)`, and `T` is formally skew-adjoint.
  have h := ((hP.smulCommutator (hsupp hP2) (hsupp hP2) f).add
    ((isFormalAdjoint_lsmul Δf).smul c) (hsupp hT1) (hsupp (Submodule.smul_mem _ _ hl1))
    (hsupp (neg_mem hT1)) (hsupp (Submodule.smul_mem _ _ hl1))).smul (-(2 * c)⁻¹)
  have hdiv (y : M) : smoothDivergence I M X y = Δf y := by
    simp [Δf, hX, laplaceBeltrami_def]
  have e₁ : -cov.alongVectorField X - lsmul (smoothDivergence I M X) =
      -(2 * c)⁻¹ • (-T + c • lsmul Δf) := by
    refine LinearMap.ext fun τ ↦ ContMDiffSection.ext fun y ↦ ?_
    simp only [lsmul, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Algebra.lsmul_coe, ContMDiffSection.coe_sub, ContMDiffSection.coe_neg,
      ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.sub_apply, Pi.neg_apply,
      Pi.add_apply, Pi.smul_apply, ContMDiffSection.smul_apply, alongVectorField_apply, hT, hdiv]
    match_scalars <;> field_simp
    ring
  have e₂ : cov.alongVectorField X = -(2 * c)⁻¹ • (T + c • lsmul Δf) := by
    refine LinearMap.ext fun τ ↦ ContMDiffSection.ext fun y ↦ ?_
    simp only [lsmul, LinearMap.add_apply, LinearMap.smul_apply, Algebra.lsmul_coe,
      ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.add_apply, Pi.smul_apply,
      ContMDiffSection.smul_apply, alongVectorField_apply, hT]
    match_scalars <;> field_simp
    ring
  rw [e₁, e₂]
  exact h

/-- **The Bochner connection of a formally self-adjoint operator is metric.** If `P` is its own
formal adjoint for the Riemannian volume and `P - c ∇*∇` is an operator of order zero for a smooth
connection `∇` and a constant `c ≠ 0`, then `∇` is compatible with the fibre metric. -/
theorem isMetricCompatible_of_sub_smul_smoothRoughLaplacian_mem
    (hP : P.IsFormalAdjoint P (riemannianVolume I M)) (hc : c ≠ 0)
    (h0 : P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0) :
    cov.IsMetricCompatible := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  -- `∞ + 1 = ∞` holds by `rfl`, but instance search does not see it.
  have : ContMDiffVectorBundle (∞ + 1) F V I := ‹ContMDiffVectorBundle ∞ F V I›
  have : IsContMDiffRiemannianBundle I (∞ + 1) F V := ‹IsContMDiffRiemannianBundle I ∞ F V›
  have : ContMDiffCovariantDerivative cov.metricCorrected ∞ :=
    ContMDiffCovariantDerivative.metricCorrected (cov := cov) (n := ∞)
  set C := cov.metricCorrection
  set Γ := differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯
  -- The metric defect of `∇` is the symmetric part of the correction `C`.
  rw [isMetricCompatible_iff_derivMetricTensor_eq_zero]
  ext x u v w
  simp only [derivMetricTensor_eq_inner_metricCorrection_add, zero_apply]
  -- Along a gradient `X` with `X x = w`, the difference `B = ∇⁰_X - ∇_X` of the covariant
  -- derivatives of `∇⁰ = ∇ + C` and `∇` is the operator of order zero `B σ = C(σ, X)`.
  obtain ⟨f, hf⟩ := exists_contMDiffMap_mgradient_eq x w
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨mgradient I f, by simpa using contMDiff_mgradient_infty f.contMDiff⟩
  let N := cov.metricCorrected.alongVectorField X
  let L := Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ (smoothDivergence I M X)
  have hB (σ : Cₛ^∞⟮I; F, V⟯) (y : M) :
      (N - cov.alongVectorField X) σ y = C y (σ y) (X y) := by
    simp [N, C, metricCorrected_apply]
  have hB0 : N - cov.alongVectorField X ∈ Γ 0 :=
    mem_differentialOperators_zero_iff.2 fun a σ ↦ ContMDiffSection.ext fun y ↦ by
      simp only [ContMDiffSection.smul_apply, hB, map_smul, smul_apply]
  -- Both `∇⁰_X` and `∇_X` have formal adjoints `-∇⁰_X - div X` and `-∇_X - div X`, so `B` is
  -- formally skew-adjoint.
  have hN1 : N ∈ Γ 1 := cov.metricCorrected.alongVectorField_mem_differentialOperators_one X
  have hK1 : cov.alongVectorField X ∈ Γ 1 := cov.alongVectorField_mem_differentialOperators_one X
  have hL1 : L ∈ Γ 1 := differentialOperators_le_succ 0 <|
    mem_differentialOperators_zero_iff.2 fun b σ ↦ smul_comm (smoothDivergence I M X) b σ
  have hN : N.IsFormalAdjoint (-N - L) (riemannianVolume I M) :=
    cov.isMetricCompatible_metricCorrected.isFormalAdjoint_alongVectorField X fun τ y ↦ by
      simp [N, L]
  have hBadj := hN.sub (isFormalAdjoint_alongVectorField_of_sub_smul_smoothRoughLaplacian_mem
      hP hc h0 f X rfl) (tsupport_differentialOperators_section_apply_subset hN1)
    (tsupport_differentialOperators_section_apply_subset hK1)
    (tsupport_differentialOperators_section_apply_subset (sub_mem (neg_mem hN1) hL1))
    (tsupport_differentialOperators_section_apply_subset (sub_mem (neg_mem hK1) hL1))
  rw [show -N - L - (-cov.alongVectorField X - L) = -(N - cov.alongVectorField X) by abel]
    at hBadj
  -- Formal adjoints of operators of order zero are pointwise adjoints.
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq (I := I) (F := F) ∞ u
  obtain ⟨τ, hτ, rfl⟩ := exists_contMDiff_section_eq (I := I) (F := F) ∞ v
  have hpt := hBadj.inner_apply_eq_of_mem_differentialOperators_zero hB0 ⟨σ, hσ⟩ ⟨τ, hτ⟩ x
  simp only [LinearMap.neg_apply, ContMDiffSection.coe_neg, Pi.neg_apply, inner_neg_right, hB,
    ContMDiffSection.coeFn_mk, show X x = w from hf] at hpt
  linarith

/-- **The zeroth-order remainder of a formally self-adjoint operator is self-adjoint.** If `P` is
its own formal adjoint for the Riemannian volume and `E = P - c ∇*∇` is an operator of order zero
for a smooth connection `∇`, then `E` is fibrewise self-adjoint:
`⟪E σ (x), τ (x)⟫ = ⟪σ (x), E τ (x)⟫` for all smooth sections `σ`, `τ` and every point `x`. -/
theorem inner_sub_smul_smoothRoughLaplacian_apply
    (hP : P.IsFormalAdjoint P (riemannianVolume I M))
    (h0 : P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (σ τ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    ⟪(P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M)) σ x, τ x⟫ =
      ⟪σ x, (P - c • cov.smoothRoughLaplacian (leviCivitaConnection I M)) τ x⟫ := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  rcases eq_or_ne c 0 with rfl | hc
  · -- For `c = 0` the operator `P` itself has order zero.
    simp only [zero_smul, sub_zero] at h0 ⊢
    exact hP.inner_apply_eq_of_mem_differentialOperators_zero h0 σ τ x
  -- Otherwise `∇` is metric, so `c ∇*∇` is formally self-adjoint, and so is `P - c ∇*∇`.
  have hcL : (c • cov.smoothRoughLaplacian (leviCivitaConnection I M)) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2 :=
    Submodule.smul_mem _ c
      (cov.smoothRoughLaplacian_mem_differentialOperators_two (leviCivitaConnection I M))
  have hP2 := mem_differentialOperators_two_of_sub_smul_smoothRoughLaplacian_mem h0
  have hL := ((hP.isMetricCompatible_of_sub_smul_smoothRoughLaplacian_mem hc
    h0).isFormalAdjoint_smoothRoughLaplacian).smul c
  have hE := hP.sub hL (tsupport_differentialOperators_section_apply_subset hP2)
    (tsupport_differentialOperators_section_apply_subset hcL)
    (tsupport_differentialOperators_section_apply_subset hP2)
    (tsupport_differentialOperators_section_apply_subset hcL)
  exact hE.inner_apply_eq_of_mem_differentialOperators_zero h0 σ τ x

end LinearMap.IsFormalAdjoint
