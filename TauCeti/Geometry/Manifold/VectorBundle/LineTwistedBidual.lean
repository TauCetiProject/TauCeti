/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
public import TauCeti.Topology.VectorBundle.LineTwistedBidual

/-!
# Smooth bidual evaluation twisted by a line bundle

Line-twisted evaluation `TauCeti.bundleLineTwistedBidual`, from a vector bundle `V` to
`Hom(Hom(V, D), D)` for a line bundle `D`, is a smooth section of the hom bundle, because its
expression in every pair of frames is the constant map `NormedSpace.inclusionInDoubleDual`. For a
finite-dimensional model fibre the induced map of total spaces and its inverse are smooth. No
regularity of the transition functions of `V` or `D` is used, and no metric, orientation or
generator of `D` is chosen.

Applied pointwise, the inverse identification therefore transports compactly supported smooth
sections, and it does so continuously for the test topologies in both directions, since it is
constant in frames. Thus the bundle tests of `Hom(Hom(V, D), D)` are, as topological vector
spaces, the bundle tests of `V` (`TauCeti.BundleTest.lineTwistedBidualEquiv`). For `V` the bundle
of alternating forms and `D` the density line, the source is the space of tests on which
distributional sections of `Hom(V, D)` act.

## Main declarations

* `TauCeti.contMDiff_bundleLineTwistedBidual`: line-twisted evaluation is a smooth hom-bundle
  section.
* `TauCeti.contMDiff_totalSpace_bundleLineTwistedBidualEquiv`,
  `TauCeti.contMDiff_totalSpace_bundleLineTwistedBidualEquiv_symm`: the finite-dimensional
  identification and its inverse are smooth maps of total spaces.
* `TauCeti.BundleTest.lineTwistedBidualEquiv`: the bundle tests of `Hom(Hom(V, D), D)` and of `V`
  are isomorphic topological vector spaces, characterized by
  `TauCeti.BundleTest.apply_lineTwistedBidualEquiv_apply`.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace TauCeti

section Smooth

variable {𝕜 M F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  (D : M → Type*) [∀ x, AddCommGroup (D x)] [∀ x, Module 𝕜 (D x)]
  [∀ x, TopologicalSpace (D x)] [TopologicalSpace (TotalSpace 𝕜 D)]
  [FiberBundle 𝕜 D] [VectorBundle 𝕜 𝕜 D]
  [∀ x, IsTopologicalAddGroup (D x)] [∀ x, ContinuousSMul 𝕜 (D x)]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}

/-- Line-twisted evaluation is a smooth hom-bundle section, in every regularity class. -/
theorem contMDiff_bundleLineTwistedBidual :
    letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F))
        (E := fun y ↦ V y →L[𝕜] (V y →L[𝕜] D y) →L[𝕜] D y) x
        (bundleLineTwistedBidual (F := F) V D x)) := by
  let : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  exact contMDiff_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ NormedSpace.inclusionInDoubleDual 𝕜 F)
    (fun a _ hxV hx ↦ bundleLineTwistedBidual_inCoordinates V D a hxV hx.2)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- For a finite-dimensional model fibre, the line-twisted bidual identification is a smooth map
of total spaces. -/
theorem contMDiff_totalSpace_bundleLineTwistedBidualEquiv :
    letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, StrongDual 𝕜 (StrongDual 𝕜 F))) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' (StrongDual 𝕜 (StrongDual 𝕜 F))
        (E := fun y ↦ (V y →L[𝕜] D y) →L[𝕜] D y) p.proj
        (bundleLineTwistedBidualEquiv (F := F) V D p.proj p.snd)) := by
  let : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  have h := contMDiff_bundleLineTwistedBidual (I := I) (n := n) (F := F) V D
  simpa only [← bundleLineTwistedBidualEquiv_toContinuousLinearMap,
    ContinuousLinearEquiv.coe_coe] using (contMDiff_hom_bundle_iff (IB := I) (n := n) (F₁ := F)
    (F₂ := StrongDual 𝕜 (StrongDual 𝕜 F)) (E₂ := fun y ↦ (V y →L[𝕜] D y) →L[𝕜] D y)
    (fun x ↦ bundleLineTwistedBidual (F := F) V D x)).1 h

/-- The inverse line-twisted bidual identification is a smooth map of total spaces. -/
theorem contMDiff_totalSpace_bundleLineTwistedBidualEquiv_symm :
    letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
    ContMDiff (I.prod 𝓘(𝕜, StrongDual 𝕜 (StrongDual 𝕜 F))) (I.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace (StrongDual 𝕜 (StrongDual 𝕜 F))
          (fun y ↦ (V y →L[𝕜] D y) →L[𝕜] D y) ↦
        TotalSpace.mk' F p.proj
          ((bundleLineTwistedBidualEquiv (F := F) V D p.proj).symm p.snd)) := by
  let : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) := inferInstance
  exact contMDiff_bundle_symm _ (contMDiff_totalSpace_bundleLineTwistedBidualEquiv V D)

end Smooth

section BundleTest

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {D : M → Type*} [∀ x, AddCommGroup (D x)] [∀ x, Module ℝ (D x)]
  [∀ x, TopologicalSpace (D x)] [TopologicalSpace (TotalSpace ℝ D)]
  [FiberBundle ℝ D] [VectorBundle ℝ ℝ D]
  [∀ x, IsTopologicalAddGroup (D x)] [∀ x, ContinuousSMul ℝ (D x)]

namespace BundleTest

/-- A point of the base lies in the preferred chart of `Hom(Hom(V, D), D)` at `a` exactly when it
lies in the preferred charts of `V` and `D` at `a`. -/
private theorem mem_lineTwistedBidual_baseSet {a x : M} :
    x ∈ (trivializationAt ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun y ↦ (V y →L[ℝ] D y) →L[ℝ] D y) a).baseSet ↔
      x ∈ (trivializationAt F V a).baseSet ∧ x ∈ (trivializationAt ℝ D a).baseSet := by
  simp

variable [FiniteDimensional ℝ F]

variable (I F V D) in
/-- The linear equivalence underlying `TauCeti.BundleTest.lineTwistedBidualEquiv`. -/
private def lineTwistedBidualLinearEquiv :
    BundleTest I ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun x ↦ (V x →L[ℝ] D x) →L[ℝ] D x) ≃ₗ[ℝ]
      BundleTest I F V :=
  (ofCompactlySupported _ _ _).symm.trans <|
    (ContMDiffSection.mapCompactlySupportedEquiv (𝕜 := ℝ) (I := I) (G := F) (W := V)
      (fun x ↦ (bundleLineTwistedBidualEquiv (F := F) V D x).symm.toLinearEquiv)
      (contMDiff_totalSpace_bundleLineTwistedBidualEquiv_symm V D)
      (contMDiff_totalSpace_bundleLineTwistedBidualEquiv V D)).trans
    (ofCompactlySupported _ _ _)

private theorem lineTwistedBidualLinearEquiv_apply
    (s : BundleTest I ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun x ↦ (V x →L[ℝ] D x) →L[ℝ] D x)) (x : M) :
    lineTwistedBidualLinearEquiv I F V D s x =
      (bundleLineTwistedBidualEquiv (F := F) V D x).symm (s x) := by
  simp [lineTwistedBidualLinearEquiv, ContMDiffSection.mapEquiv_apply]

private theorem lineTwistedBidualLinearEquiv_symm_apply (t : BundleTest I F V) (x : M) :
    (lineTwistedBidualLinearEquiv I F V D).symm t x =
      bundleLineTwistedBidualEquiv (F := F) V D x (t x) := by
  rw [← (bundleLineTwistedBidualEquiv (F := F) V D x).apply_symm_apply
    ((lineTwistedBidualLinearEquiv I F V D).symm t x), ← lineTwistedBidualLinearEquiv_apply,
    LinearEquiv.apply_symm_apply]

variable [LocallyCompactSpace E] [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffVectorBundle ∞ ℝ D I]

variable (I F V D) in
/-- Bundle tests of `Hom(Hom(V, D), D)`, for a line bundle `D`, are the bundle tests of `V`: the
inverse of line-twisted bidual evaluation, applied pointwise, is a topological linear isomorphism
of the test spaces. It is characterized by
`TauCeti.BundleTest.apply_lineTwistedBidualEquiv_apply` and preserves supports. -/
def lineTwistedBidualEquiv :
    BundleTest I ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun x ↦ (V x →L[ℝ] D x) →L[ℝ] D x) ≃L[ℝ]
      BundleTest I F V where
  toLinearEquiv := lineTwistedBidualLinearEquiv I F V D
  continuous_toFun := by
    refine (continuous_map_of_inCoordinates_eq_const
      (fun x ↦ (bundleLineTwistedBidualEquiv (F := F) V D x).symm.toContinuousLinearMap)
      (contMDiff_totalSpace_bundleLineTwistedBidualEquiv_symm V D)
      (c := fun _ ↦ (NormedSpace.inclusionInDoubleDual ℝ F).inverse)
      fun a x hx _ ↦ bundleLineTwistedBidualEquiv_symm_inCoordinates V D a
        (mem_lineTwistedBidual_baseSet.1 hx).1 (mem_lineTwistedBidual_baseSet.1 hx).2).congr
      fun s ↦ ext fun x ↦ ?_
    simp [lineTwistedBidualLinearEquiv_apply, ContMDiffSection.mapLinearMap_apply]
  continuous_invFun := by
    refine (continuous_map_of_inCoordinates_eq_const
      (fun x ↦ (bundleLineTwistedBidualEquiv (F := F) V D x).toContinuousLinearMap)
      (contMDiff_totalSpace_bundleLineTwistedBidualEquiv V D)
      (c := fun _ ↦ NormedSpace.inclusionInDoubleDual ℝ F)
      fun a x hx hx' ↦ ?_).congr fun t ↦ ext fun x ↦ ?_
    · rw [bundleLineTwistedBidualEquiv_toContinuousLinearMap]
      exact bundleLineTwistedBidual_inCoordinates V D a hx (mem_lineTwistedBidual_baseSet.1 hx').2
    · simp [lineTwistedBidualLinearEquiv_symm_apply, ContMDiffSection.mapLinearMap_apply,
        - bundleLineTwistedBidualEquiv_toContinuousLinearMap]

/-- The test of `V` attached to a test of `Hom(Hom(V, D), D)` is computed pointwise by the inverse
of line-twisted bidual evaluation. -/
theorem lineTwistedBidualEquiv_apply
    (s : BundleTest I ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun x ↦ (V x →L[ℝ] D x) →L[ℝ] D x)) (x : M) :
    lineTwistedBidualEquiv I F V D s x =
      (bundleLineTwistedBidualEquiv (F := F) V D x).symm (s x) :=
  lineTwistedBidualLinearEquiv_apply s x

/-- The inverse identification is line-twisted bidual evaluation, pointwise. -/
theorem lineTwistedBidualEquiv_symm_apply (t : BundleTest I F V) (x : M) :
    (lineTwistedBidualEquiv I F V D).symm t x =
      bundleLineTwistedBidualEquiv (F := F) V D x (t x) :=
  lineTwistedBidualLinearEquiv_symm_apply t x

/-- The characteristic property of the identification: a `D x`-valued map `φ` on `V x` takes on
the identified test of `V` the value that the original test assigns to `φ`. -/
@[simp]
theorem apply_lineTwistedBidualEquiv_apply
    (s : BundleTest I ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun x ↦ (V x →L[ℝ] D x) →L[ℝ] D x)) (x : M)
    (φ : V x →L[ℝ] D x) :
    φ (lineTwistedBidualEquiv I F V D s x) = s x φ := by
  rw [lineTwistedBidualEquiv_apply, apply_bundleLineTwistedBidualEquiv_symm]

/-- The inverse identification pairs a `D x`-valued map `φ` on `V x` with the value of the test. -/
@[simp]
theorem lineTwistedBidualEquiv_symm_apply_apply (t : BundleTest I F V) (x : M)
    (φ : V x →L[ℝ] D x) :
    (lineTwistedBidualEquiv I F V D).symm t x φ = φ (t x) := by
  rw [lineTwistedBidualEquiv_symm_apply, bundleLineTwistedBidualEquiv_apply]

/-- The identification preserves the exact set where a test vanishes, hence its support. -/
@[simp]
theorem lineTwistedBidualEquiv_apply_eq_zero_iff
    {s : BundleTest I ((F →L[ℝ] ℝ) →L[ℝ] ℝ) (fun x ↦ (V x →L[ℝ] D x) →L[ℝ] D x)} {x : M} :
    lineTwistedBidualEquiv I F V D s x = 0 ↔ s x = 0 := by
  rw [lineTwistedBidualEquiv_apply, map_eq_zero_iff _ (ContinuousLinearEquiv.injective _)]

end BundleTest

end BundleTest

end TauCeti
