/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Tangent

/-!
# Covariant differentiation along maps under local Riemannian isometries

For a local Riemannian isometry `f : M → N` and a map `γ : P → M` from any manifold `P`,
covariant differentiation of tangent fields along `γ` commutes with the tangent map of `f`:

`df (∇ᴹ_v V) = ∇ᴺ_v (df V)`,

where `df V : p ↦ df_{γ p} (V p)` is the transported field along `f ∘ γ`, `v ∈ T_pP`, and both
sides use Levi-Civita connections. This is the along-map form of the naturality of the Levi-Civita
connection, and specialises at `P = ℝ` to the unrestricted along-curve form
`TauCeti.IsLocalRiemannianIsometry.mfderiv_alongCurve`. It applies to fields along `γ` that are
not restrictions of vector fields on `M`, such as the differential `df Y` of an immersion or a
normal field along it, and so transports the submanifold geometry of an immersion `γ` into `M` to
that of `f ∘ γ`.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.mfderiv_alongMap_of_isLeviCivitaConnection`:
  **naturality of covariant differentiation along maps** under local Riemannian isometries, for
  any Levi-Civita connections on `M` and `N`.
* `TauCeti.IsLocalRiemannianIsometry.mfderiv_alongMap`: the same statement for Mathlib's
  `CovariantDerivative.leviCivitaConnection`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Prop. 5.13.
-/

public section

open Bundle CovariantDerivative Filter Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {HP : Type*} [TopologicalSpace HP] {K : ModelWithCorners ℝ G HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

/-! ### Naturality of covariant differentiation along maps -/

namespace IsLocalRiemannianIsometry

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

/-- **Naturality of covariant differentiation along maps under local Riemannian isometries.**
Let `f : M → N` be a local Riemannian isometry and `∇ᴹ`, `∇ᴺ` Levi-Civita connections. For a map
`γ : P → M` differentiable at `t` and a tangent field `V` along `γ` whose coordinate reading is
differentiable at `t`, the differential of `f` carries the covariant derivative of `V` along `γ`
to the covariant derivative of the transported field `df V` along `f ∘ γ`:
`df (∇ᴹ_v V) = ∇ᴺ_v (df V)` for every `v ∈ T_tP`. -/
theorem mfderiv_alongMap_of_isLeviCivitaConnection (hf : IsLocalRiemannianIsometry I J f)
    {covM : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {covN : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    {γ : P → M} {V : ∀ p, TangentSpace I (γ p)} {t : P} (hγ : MDifferentiableAt K I γ t)
    (hV : MDifferentiableAt K 𝓘(ℝ, E) (sectionCoord ℝ (F := E) γ V (γ t)) t)
    (v : TangentSpace K t) :
    mfderiv I J f (γ t) (covM.alongMap K γ V t v) =
      covN.alongMap K (f ∘ γ) (fun p ↦ mfderiv I J f (γ p) (V p)) t v := by
  have hfγ : MDifferentiableAt K J (f ∘ γ) t := (hf.mdifferentiableAt (γ t)).comp t hγ
  have hfV : MDifferentiableAt K 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) (f ∘ γ) (fun p ↦ mfderiv I J f (γ p) (V p)) (f (γ t))) t :=
    hf.contMDiff.contMDiffAt.mdifferentiableAt_sectionCoord_mfderiv (by simp) hγ hV
  -- Pair both sides with a differentiable vector field `Y` on `N`: the pairings `⟪V, f^* Y⟫` and
  -- `⟪df V, Y⟫` along `γ` agree, the metric product rule along maps differentiates them, and the
  -- remaining terms agree by the naturality of the Levi-Civita connection on `f^* Y`.
  refine injective_inner_mdifferentiableAt_section J F (TangentSpace J) (f (γ t)) ?_
  ext Y hY
  dsimp only
  let X : Π x : M, TangentSpace I x := mpullback I J f Y
  have hX : MDiffAt (T% X) (γ t) := hf.mdifferentiableAt_mpullback hY
  have hXc : MDifferentiableAt K 𝓘(ℝ, E)
      (sectionCoord ℝ (F := E) γ (fun p ↦ X (γ p)) (γ t)) t :=
    mdifferentiableAt_sectionCoord γ (fun p ↦ X (γ p)) (hX.comp t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hYc : MDifferentiableAt K 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) (f ∘ γ) (fun p ↦ Y ((f ∘ γ) p)) (f (γ t))) t :=
    mdifferentiableAt_sectionCoord (f ∘ γ) (fun p ↦ Y ((f ∘ γ) p)) (hY.comp t hfγ)
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t)))
  have hsource := hM.isMetricCompatible.mvfderiv_inner_alongMap hγ hV hXc v
  have htarget := hN.isMetricCompatible.mvfderiv_inner_alongMap hfγ hfV hYc v
  have hXY (p : P) : mfderiv I J f (γ p) (X (γ p)) = Y ((f ∘ γ) p) :=
    hf.mfderiv_apply_mpullback Y (γ p)
  have hinner : (fun p ↦ inner ℝ (V p) (X (γ p))) =
      fun p ↦ inner ℝ (mfderiv I J f (γ p) (V p)) (Y ((f ∘ γ) p)) := by
    funext p
    rw [← hf.inner_mfderiv (γ p), hXY]
  rw [hinner] at hsource
  rw [alongMap_pullback covM γ hγ hX] at hsource
  rw [alongMap_pullback covN (f ∘ γ) hfγ hY] at htarget
  have hsecond : inner ℝ (V t) (covM X (γ t) (mfderiv K I γ t v)) =
      inner ℝ (mfderiv I J f (γ t) (V t))
        (covN Y (f (γ t)) (mfderiv K J (f ∘ γ) t v)) := by
    rw [← hf.inner_mfderiv (γ t), hf.mfderiv_apply_mpullback_of_isLeviCivitaConnection hM hN hY,
      mfderiv_comp t (hf.mdifferentiableAt (γ t)) hγ, ContinuousLinearMap.comp_apply]
  have hleft : inner ℝ (mfderiv I J f (γ t) (covM.alongMap K γ V t v)) (Y (f (γ t))) =
      inner ℝ (covM.alongMap K γ V t v) (X (γ t)) := by
    rw [← hf.inner_mfderiv (γ t), hXY, Function.comp_apply]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply] at hsource htarget hsecond hXY ⊢
  rw [hleft]
  linarith

/-- **Naturality of covariant differentiation along maps under local Riemannian isometries**, for
Mathlib's `CovariantDerivative.leviCivitaConnection`: `df (∇ᴹ_v V) = ∇ᴺ_v (df V)`. -/
theorem mfderiv_alongMap (hf : IsLocalRiemannianIsometry I J f)
    {γ : P → M} {V : ∀ p, TangentSpace I (γ p)} {t : P} (hγ : MDifferentiableAt K I γ t)
    (hV : MDifferentiableAt K 𝓘(ℝ, E) (sectionCoord ℝ (F := E) γ V (γ t)) t)
    (v : TangentSpace K t) :
    mfderiv I J f (γ t) ((leviCivitaConnection I M).alongMap K γ V t v) =
      (leviCivitaConnection J N).alongMap K (f ∘ γ) (fun p ↦ mfderiv I J f (γ p) (V p)) t v :=
  hf.mfderiv_alongMap_of_isLeviCivitaConnection (isLeviCivitaConnection_leviCivitaConnection I)
    (isLeviCivitaConnection_leviCivitaConnection J) hγ hV v

end IsLocalRiemannianIsometry

end TauCeti

end
