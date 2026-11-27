/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Immersion
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Laplacian of an isometric immersion into a Euclidean space

Let `f : M → F` be a `C²` map from a Riemannian manifold `M` of dimension `m` into a
finite-dimensional real inner product space `F` with its flat metric, whose differential preserves
inner products, `⟪v, w⟫ = ⟪df v, df w⟫`. For a vector `e ∈ F`, the coordinate function
`⟪f, e⟫ : M → ℝ` has Hessian `⟪B(v, w), e⟫`, with `B` the second fundamental form of `f`
(`TauCeti.hessian_inner_eq_inner_immersionSecondFundamentalFormAt`). Taking traces,

`Δ ⟪f, e⟫ = m ⟪H, e⟫`

for the mean curvature vector `H = (tr B) / m`
(`TauCeti.laplaceBeltrami_inner_eq_finrank_mul_inner_immersionMeanCurvatureVector`), with Tau
Ceti's sign convention `Δ = div grad`. With the positive (geometers') Laplacian
`Δ⁺ = -div grad` this is `Δ⁺ f = -m H`, read componentwise. Hence
`f` is minimal at a point exactly when every coordinate function `⟪f, e⟫` has vanishing Laplacian
there (`TauCeti.immersionMeanCurvatureVector_eq_zero_iff_laplaceBeltrami_inner_eq_zero`), and
`f` is minimal everywhere exactly when all its coordinate functions are harmonic
(`TauCeti.forall_immersionMeanCurvatureVector_eq_zero_iff_forall_laplaceBeltrami_inner_eq_zero`).

The Hessian identity rests on the flat-ambient form of the Gauss formula: the ambient derivative
`D_v (df W)` of the `F`-valued map `df W` splits into its tangential part `df (∇_v W)`, by
`CovariantDerivative.IsLeviCivitaConnection.inner_apply_eq_inner_mvfderiv`, and its normal
part `B(v, w)`, by `TauCeti.immersionSecondFundamentalForm_model_space`
(`TauCeti.immersionSecondFundamentalFormAt_model_space_eq_sub`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the Gauss formula, the second fundamental form and the mean curvature vector).
-/

public section

noncomputable section

open Bundle Manifold Module
open scoped InnerProductSpace Manifold ContDiff Topology

namespace TauCeti

open TauCeti.Manifold CovariantDerivative

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {f : M → F}

/-- **The second fundamental form of an isometric immersion into a Euclidean space** is the
ambient derivative of `df W` minus its tangential part:
`B(v, w) = D_v (df W) - df (∇_v W)` for vector fields `V`, `W` through `v`, `w`, with `∇` the
Levi-Civita connection of `M`. -/
theorem immersionSecondFundamentalFormAt_model_space_eq_sub {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hg : ∀ y (v w : TangentSpace I y), ⟪v, w⟫_ℝ = ⟪mvfderiv I f y v, mvfderiv I f y w⟫_ℝ)
    {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, F) F) f x (V x) (W x) =
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
        mvfderiv I f x (leviCivitaConnection I M W x (V x)) := by
  have hdW : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ (mfderiv I 𝓘(ℝ, F) f y (W y) : F)) x := by
    simpa only [mvfderiv_apply_eq_mfderiv_apply] using
      mdifferentiableAt_mvfderiv_apply hf le_rfl hW
  rw [immersionSecondFundamentalFormAt_apply hf hV hW,
    immersionSecondFundamentalForm_model_space (hf.mdifferentiableAt two_ne_zero) hdW]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun z hz ↦ ?_
  · -- `D_v (df W) - df (∇_v W)` is orthogonal to the image of `df`, by the Gauss formula.
    refine mem_orthogonalNormalSpace_iff.2 fun u ↦ ?_
    have hG := (isLeviCivitaConnection_leviCivitaConnection I).inner_apply_eq_inner_mvfderiv
      hf hg hV hW u
    -- `mvfderiv` is `mfderiv` followed by the identification of `TangentSpace 𝓘(ℝ, F) _` with
    -- `F`, which is the identity, so this restates the goal in `mvfderiv` form.
    change ⟪mvfderiv I f x u, mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
      mvfderiv I f x (leviCivitaConnection I M W x (V x))⟫_ℝ = 0
    rw [inner_sub_right, real_inner_comm, ← hG, ← hg, real_inner_comm, sub_self]
  · -- `df (∇_v W)` is tangent, so orthogonal to the normal space. As above, `change` restates
    -- the goal in `mvfderiv` form.
    change ⟪mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
      (mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
        mvfderiv I f x (leviCivitaConnection I M W x (V x))), (z : F)⟫_ℝ = 0
    rw [sub_sub_cancel]
    exact mem_orthogonalNormalSpace_iff.1 hz _

/-- **The Hessian of a coordinate function of an isometric immersion into a Euclidean space** is
the second fundamental form in that direction: `Hess ⟪f, e⟫ (v, w) = ⟪B(v, w), e⟫`. -/
theorem hessian_inner_eq_inner_immersionSecondFundamentalFormAt {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hg : ∀ y (v w : TangentSpace I y), ⟪v, w⟫_ℝ = ⟪mvfderiv I f y v, mvfderiv I f y w⟫_ℝ)
    (e : F) (v w : TangentSpace I x) :
    hessian I (fun y ↦ ⟪f y, e⟫_ℝ) x v w =
      ⟪immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, F) F) f x v w, e⟫_ℝ := by
  have hφ : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ⟪f y, e⟫_ℝ) x := by
    have := ContMDiffAt.comp x
      ((contDiff_id.inner ℝ (contDiff_const (c := e))).contMDiff.contMDiffAt) hf
    simpa [Function.comp_def] using this
  set V : Π y : M, TangentSpace I y := FiberBundle.extend E v
  set W : Π y : M, TangentSpace I y := FiberBundle.extend E w
  have hV : MDiffAt (T% V) x := FiberBundle.mdifferentiableAt_extend I E v
  have hW : MDiffAt (T% W) x := FiberBundle.mdifferentiableAt_extend I E w
  have hVx : V x = v := FiberBundle.extend_apply_self _ v
  have hWx : W x = w := FiberBundle.extend_apply_self _ w
  have hH := hessian_apply_eq_mvfderiv_sub x hφ V W hW
  -- `f` is `C²` near `x`, so `d⟪f, e⟫ = ⟪df, e⟫` near `x`.
  have hfun : (fun y ↦ mvfderiv I (fun y ↦ ⟪f y, e⟫_ℝ) y (W y)) =ᶠ[𝓝 x]
      fun y ↦ ⟪mvfderiv I f y (W y), e⟫_ℝ :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf).mono fun y hy ↦
      mvfderiv_inner_const_apply (hy.mdifferentiableAt two_ne_zero) e (W y)
  rw [hfun.mvfderiv_eq, mvfderiv_inner_const_apply (mdifferentiableAt_mvfderiv_apply hf le_rfl hW),
    mvfderiv_inner_const_apply (hf.mdifferentiableAt two_ne_zero), ← inner_sub_left, hVx,
    hWx] at hH
  have hB := immersionSecondFundamentalFormAt_model_space_eq_sub hf hg hV hW
  rw [hVx, hWx] at hB
  rw [hH]
  exact congrArg (fun z ↦ ⟪z, e⟫_ℝ) hB.symm

/-- **`Δ⁺ f = -m H` for an isometric immersion into a Euclidean space**, componentwise: for every
`e`, the Laplacian `Δ = div grad` of the coordinate function `⟪f, e⟫` is `m ⟪H, e⟫`, with
`m = dim M` and `H` the mean curvature vector. -/
theorem laplaceBeltrami_inner_eq_finrank_mul_inner_immersionMeanCurvatureVector {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hg : ∀ y (v w : TangentSpace I y), ⟪v, w⟫_ℝ = ⟪mvfderiv I f y v, mvfderiv I f y w⟫_ℝ)
    (e : F) :
    laplaceBeltrami I (fun y ↦ ⟪f y, e⟫_ℝ) x =
      finrank ℝ E * ⟪immersionMeanCurvatureVector (I := I)
        (leviCivitaConnection 𝓘(ℝ, F) F) f x, e⟫_ℝ := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  set B := immersionSecondFundamentalFormAt (I := I) (leviCivitaConnection 𝓘(ℝ, F) F) f x
  have hsum : laplaceBeltrami I (fun y ↦ ⟪f y, e⟫_ℝ) x = ⟪∑ i, B (b i) (b i), e⟫_ℝ :=
    calc laplaceBeltrami I (fun y ↦ ⟪f y, e⟫_ℝ) x
        = ∑ i, hessian I (fun y ↦ ⟪f y, e⟫_ℝ) x (b i) (b i) :=
          laplaceBeltrami_eq_sum_hessian I _ x b
      _ = ∑ i, ⟪B (b i) (b i), e⟫_ℝ := Finset.sum_congr rfl fun i _ ↦
          hessian_inner_eq_inner_immersionSecondFundamentalFormAt hf hg e _ _
      _ = ⟪∑ i, B (b i) (b i), e⟫_ℝ := (sum_inner _ _ _).symm
  have hH : ⟪immersionMeanCurvatureVector (I := I) (leviCivitaConnection 𝓘(ℝ, F) F) f x, e⟫_ℝ =
      (finrank ℝ E : ℝ)⁻¹ * ⟪∑ i, B (b i) (b i), e⟫_ℝ :=
    (congrArg (fun z ↦ ⟪z, e⟫_ℝ) (immersionMeanCurvatureVector_eq_sum b)).trans
      (real_inner_smul_left _ _ _)
  rw [hsum, hH]
  rcases eq_or_ne (finrank ℝ E) 0 with h0 | h0
  · -- In dimension zero every tangent vector vanishes (`TangentSpace I x` is `E`), and both
    -- sides are `0`.
    have : Subsingleton (TangentSpace I x) := (Module.finrank_zero_iff.1 h0 : Subsingleton E)
    have hB : ∑ i, B (b i) (b i) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by simp [Subsingleton.elim (b i) 0]
    -- The zero of `TangentSpace 𝓘(ℝ, F) (f x)` is the zero of `F`.
    rw [hB, h0, Nat.cast_zero, zero_mul]
    exact inner_zero_left _
  · exact (mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 h0) _).symm

/-- **Minimality in coordinates.** An isometric immersion into a Euclidean space has vanishing
mean curvature vector at `x` iff every coordinate function `⟪f, e⟫` has vanishing Laplacian
at `x`. -/
theorem immersionMeanCurvatureVector_eq_zero_iff_laplaceBeltrami_inner_eq_zero {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hg : ∀ y (v w : TangentSpace I y), ⟪v, w⟫_ℝ = ⟪mvfderiv I f y v, mvfderiv I f y w⟫_ℝ) :
    immersionMeanCurvatureVector (I := I) (leviCivitaConnection 𝓘(ℝ, F) F) f x = 0 ↔
      ∀ e : F, laplaceBeltrami I (fun y ↦ ⟪f y, e⟫_ℝ) x = 0 := by
  rcases eq_or_ne (finrank ℝ E) 0 with h0 | hm
  · -- In dimension zero both sides hold.
    refine iff_of_true ?_ fun e ↦ ?_
    · rw [immersionMeanCurvatureVector_eq_sum (stdOrthonormalBasis ℝ (TangentSpace I x)), h0,
        Nat.cast_zero, inv_zero, zero_smul]
    · rw [laplaceBeltrami_inner_eq_finrank_mul_inner_immersionMeanCurvatureVector hf hg, h0,
        Nat.cast_zero, zero_mul]
  simp_rw [laplaceBeltrami_inner_eq_finrank_mul_inner_immersionMeanCurvatureVector hf hg,
    mul_eq_zero, Nat.cast_eq_zero, hm, false_or]
  refine ⟨fun h e ↦ ?_, fun h ↦ ext_inner_right ℝ fun e ↦ by rw [h e, inner_zero_left]⟩
  -- The zero of `TangentSpace 𝓘(ℝ, F) (f x)` is the zero of `F`.
  rw [h]
  exact inner_zero_left _

/-- **Minimal immersions are those with harmonic coordinate functions.** An isometric immersion
into a Euclidean space is minimal everywhere iff all its coordinate functions `⟪f, e⟫` are
harmonic. -/
theorem forall_immersionMeanCurvatureVector_eq_zero_iff_forall_laplaceBeltrami_inner_eq_zero
    (hf : ContMDiff I 𝓘(ℝ, F) 2 f)
    (hg : ∀ y (v w : TangentSpace I y), ⟪v, w⟫_ℝ = ⟪mvfderiv I f y v, mvfderiv I f y w⟫_ℝ) :
    (∀ x, immersionMeanCurvatureVector (I := I) (leviCivitaConnection 𝓘(ℝ, F) F) f x = 0) ↔
      ∀ e : F, laplaceBeltrami I (fun y ↦ ⟪f y, e⟫_ℝ) = 0 := by
  simp_rw [immersionMeanCurvatureVector_eq_zero_iff_laplaceBeltrami_inner_eq_zero (hf _) hg,
    funext_iff, Pi.zero_apply]
  exact forall_comm

end TauCeti
