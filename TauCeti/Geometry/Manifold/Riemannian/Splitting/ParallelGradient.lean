/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Killing.Flow
public import TauCeti.Geometry.Manifold.Flow.FlowOut
public import TauCeti.Geometry.Manifold.Flow.LevelProduct
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Complete
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Complete
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.RegularValue
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Flow

/-!
# Splitting by a parallel unit gradient

A complete connected Riemannian manifold with a smooth unit gradient and
vanishing Hessian is the Riemannian product of the real line and its complete
connected zero level. This is the parallel-gradient splitting criterion in
Morgan–Tian, Lemma 2.14.

Source references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

section FlowMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] {f : M → ℝ}

section Product

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [ChartedSpace K {x : M // f x = 0}]
  [IsManifold J 1 {x : M // f x = 0}]

/-- A complete Killing unit gradient gives a Riemannian product isometry whenever its actual
zero level carries the induced smooth metric. Ambient completeness and connectedness are not
required for this construction. -/
theorem exists_riemannianIsometry_prod_zeroLevel_of_isCompleteVectorField
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hι : Manifold.IsSmoothEmbedding J I ∞ (Subtype.val : {x : M // f x = 0} → M))
    (hc : IsCompleteVectorField (mgradient I f))
    (hkill : IsKillingField I (mgradient I f))
    (hunit : ∀ x, inner ℝ (mgradient I f x) (mgradient I f x) = 1)
    (gL : ContMDiffRiemannianMetric J ∞ F
      (TangentSpace J : {x : M // f x = 0} → Type _))
    (hL : ∀ z (v w : TangentSpace J z), gL.inner z v w =
      inner ℝ (mfderiv J I (Subtype.val : {x : M // f x = 0} → M) z v)
        (mfderiv J I (Subtype.val : {x : M // f x = 0} → M) z w)) :
    let gR := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
      (IB := 𝓘(ℝ)) (n := ∞) (F := ℝ) (V := (TangentSpace 𝓘(ℝ) : ℝ → Type _))
    let gP := gR.prodTangentSpace gL
    letI : RiemannianBundle (TangentSpace (𝓘(ℝ).prod J) :
      ℝ × {x : M // f x = 0} → Type _) := ⟨gP.toRiemannianMetric⟩
    ∃ e : RiemannianIsometry (𝓘(ℝ).prod J) I (ℝ × {x : M // f x = 0}) M,
      (∀ z, f (e z) = z.1) ∧
      (∀ z : {x : M // f x = 0}, e (0, z) = z) ∧
      ∀ x, (e.symm x).1 = f x := by
  let φ := globalFlow (mgradient I f) (hkill.contMDiff.of_le (by simp)) hc
  have hφ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2) :=
    contMDiff_globalFlow_uncurry hc le_top hkill.contMDiff
  have hscalar : ∀ t x, f (φ t x) = f x + t :=
    apply_globalFlow_mgradient_eq_add _ hc hunit
  let e := φ.zeroLevelProductDiffeomorph hφ hf hι hscalar
  let gR := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := 𝓘(ℝ)) (n := ∞) (F := ℝ) (V := (TangentSpace 𝓘(ℝ) : ℝ → Type _))
  let gP := gR.prodTangentSpace gL
  let : RiemannianBundle (TangentSpace (𝓘(ℝ).prod J) :
    ℝ × {x : M // f x = 0} → Type _) := ⟨gP.toRiemannianMetric⟩
  let Φ : RiemannianIsometry (𝓘(ℝ).prod J) I (ℝ × {x : M // f x = 0}) M :=
    { toDiffeomorph := e
      inner_mfderiv' := by
        intro z v w
        rw [ContMDiffRiemannianMetric.inner_riemannianBundle gP z v w,
          ContMDiffRiemannianMetric.prodTangentSpace_inner,
          ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner_real]
        obtain ⟨⟨a, v⟩, rfl⟩ := (tangentSpaceProdEquiv z).symm.surjective v
        obtain ⟨⟨b, w⟩, rfl⟩ := (tangentSpaceProdEquiv z).symm.surjective w
        simp only [ContinuousLinearEquiv.apply_symm_apply, hL]
        rw [Flow.coe_zeroLevelProductDiffeomorph]
        exact inner_mfderiv_globalFlow_mgradient_comp hc hkill hunit z
          (hι.contMDiff.mdifferentiableAt (by simp))
          (Filter.Eventually.of_forall fun z ↦ z.property) a b v w }
  refine ⟨Φ, ?_, ?_, ?_⟩
  · exact Flow.apply_zeroLevelProductDiffeomorph φ hφ hf hι hscalar
  · exact Flow.zeroLevelProductDiffeomorph_apply_zero φ hφ hf hι hscalar
  · intro x
    rw [RiemannianIsometry.coe_symm]
    exact Flow.zeroLevelProductDiffeomorph_symm_apply_fst φ hφ hf hι hscalar x

end Product

end FlowMetric

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [EMetricSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
  {f : M → ℝ}

/-- **Parallel gradient splitting.** A complete connected Riemannian manifold with a smooth
unit gradient and vanishing Hessian is the metric product of its actual complete connected
zero level and the real line. -/
theorem exists_riemannianIsometry_prod_zeroLevel
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hunit : ∀ x, inner ℝ (mgradient I f x) (mgradient I f x) = 1)
    (hzero : ∀ x (v w : TangentSpace I x), hessian I f x v w = 0) :
    let hreg := isRegularValue_of_unit_mgradient hunit 0
    let hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = Module.finrank ℝ E - 1 := by simp
    letI := regularLevelChartedSpace
      (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hreg hn
    letI := isManifold_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt) hreg hn
    let L := {x : M // f x = 0}
    let J := 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
    ∃ gL : ContMDiffRiemannianMetric J ∞ (Fin (Module.finrank ℝ E - 1) → ℝ)
        (TangentSpace J : L → Type _),
      (∀ z (v w : TangentSpace J z), gL.inner z v w =
        inner ℝ (mfderiv J I (Subtype.val : L → M) z v)
          (mfderiv J I (Subtype.val : L → M) z w)) ∧
      ConnectedSpace L ∧
      (letI : RiemannianBundle (TangentSpace J : L → Type _) := ⟨gL.toRiemannianMetric⟩
       letI := Bundle.instIsContMDiffRiemannianBundle gL
       letI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
         (IB := J) (n := ∞) (F := Fin (Module.finrank ℝ E - 1) → ℝ)
         (V := (TangentSpace J : L → Type _))
       let eL := EMetricSpace.ofRiemannianMetric J L
       @CompleteSpace L eL.toUniformSpace) ∧
      (let gR := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
          (IB := 𝓘(ℝ)) (n := ∞) (F := ℝ) (V := (TangentSpace 𝓘(ℝ) : ℝ → Type _))
       let gP := gR.prodTangentSpace gL
       letI : RiemannianBundle (TangentSpace (𝓘(ℝ).prod J) : ℝ × L → Type _) :=
         ⟨gP.toRiemannianMetric⟩
       ∃ e : RiemannianIsometry (𝓘(ℝ).prod J) I (ℝ × L) M,
         (∀ z, f (e z) = z.1) ∧ (∀ z : L, e (0, z) = z) ∧ ∀ x, (e.symm x).1 = f x) := by
  let : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  let hreg := isRegularValue_of_unit_mgradient hunit 0
  let hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = Module.finrank ℝ E - 1 := by simp
  let := regularLevelChartedSpace
    (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hreg hn
  let := isManifold_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt) hreg hn
  let L := {x : M // f x = 0}
  let J := 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
  have hι := isSmoothEmbedding_coe_regularLevel (by simp)
    (fun _ _ ↦ hf.contMDiffAt) hreg hn
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := (TangentSpace I : M → Type _))
  let gL := g.pullback (Subtype.val : L → M) (by simpa using hι.contMDiff)
    (hι.isImmersion.mfderiv_injective (by simp))
  let gR := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := 𝓘(ℝ)) (n := ∞) (F := ℝ) (V := (TangentSpace 𝓘(ℝ) : ℝ → Type _))
  let : RiemannianBundle (TangentSpace (𝓘(ℝ).prod J) : ℝ × L → Type _) :=
    ⟨(gR.prodTangentSpace gL).toRiemannianMetric⟩
  have hgrad := contMDiff_mgradient (n := ∞) (by simpa using hf)
  have hc := isCompleteVectorField_mgradient_of_hessian_eq_zero
    (fun x ↦ isGeodesicallyCompleteAt_of_completeSpace x) (hgrad.mdifferentiable (by simp)) hzero
  have hL (z : L) (v w : TangentSpace J z) : gL.inner z v w =
      inner ℝ (mfderiv J I (Subtype.val : L → M) z v)
        (mfderiv J I (Subtype.val : L → M) z w) := by
    exact ContMDiffRiemannianMetric.pullback_ofIsContMDiffRiemannianBundle_inner
      (Subtype.val : L → M) _ _ z v w
  obtain ⟨e, he, hzeroSlice, hfst⟩ :=
    exists_riemannianIsometry_prod_zeroLevel_of_isCompleteVectorField hf hι hc
      (((isMetricCompatible_leviCivitaConnection (M := M) I).isKillingField_iff_inner_self
        (torsion_leviCivitaConnection_eq_zero I)).2
          ⟨hgrad, fun x v ↦ by simpa only [hessian_def] using hzero x v v⟩)
      hunit gL hL
  have hconn : ConnectedSpace L := by
    have hsurj : Surjective (fun x : M ↦ (e.symm x).2) := fun z ↦
      ⟨e (0, z), by simp only [e.symm_apply_apply]⟩
    exact hsurj.connectedSpace (continuous_snd.comp e.symm.continuous)
  refine ⟨gL, hL, hconn, ?_, e, he, hzeroSlice, hfst⟩
  exact IsRiemannianManifold.completeSpace_pullback_of_isClosedEmbedding
    (I := J) (J := I) (n := ∞) (by simpa using hι.contMDiff)
    (hι.isImmersion.mfderiv_injective (by simp))
    ⟨Topology.IsEmbedding.subtypeVal, by
      rw [Subtype.range_coe_subtype]
      exact isClosed_singleton.preimage hf.continuous⟩

end TauCeti.Manifold
