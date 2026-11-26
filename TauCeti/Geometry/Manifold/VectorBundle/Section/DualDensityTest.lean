/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.DoubleDual.Line
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.CompactSupport

/-!
# Dual-density tests of a dual-density bundle

Let `V` be a finite-rank smooth real vector bundle over a manifold `M` and `D = |Λ|` its density
line. The tests of the dual-density bundle `V* ⊗ D = Hom(V, D)` are the bundle tests of
`Hom(Hom(V, D), D)` (`TauCeti.DualDensityTest`). Fibrewise evaluation
`V ≅ Hom(Hom(V, D), D)` (`TauCeti.bundleLineDoubleDualEquiv`) has the constant model map
`NormedSpace.inclusionInDoubleDual` as its expression in the induced frames, so native transport
of bundle tests (`TauCeti.BundleTest.mapCLE`) identifies these tests with the bundle tests of `V`:
`TauCeti.DualDensityTest.doubleDualEquiv`. A test `s` goes to the section `u` with
`φ (u x) = s x φ` for every `φ : V x →L[ℝ] D x`. The identification is an isomorphism of
topological vector spaces, it preserves the exact support, and it uses no measure, metric or
choice of frame.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.DualDensityTest

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- The tests of the dual-density bundle of `V` are the bundle tests of `V`, as topological
vector spaces. A test `s` corresponds to the section `u` with `φ (u x) = s x φ` for every
density-valued functional `φ` on `V x` (`TauCeti.DualDensityTest.apply_doubleDualEquiv_apply`):
the inverse of fibrewise evaluation `TauCeti.bundleLineDoubleDualEquiv` is applied pointwise. -/
def doubleDualEquiv :
    DualDensityTest I M (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] DensityBundle I M x) ≃L[ℝ]
      BundleTest I F V := by
  let e := fun a : M ↦ trivializationAt F V a
  let d := fun a : M ↦ trivializationAt ℝ (DensityBundle I M) a
  let U : M → TopologicalSpace.Opens M := fun a ↦
    ⟨(e a).baseSet ∩ (d a).baseSet, (e a).open_baseSet.inter (d a).open_baseSet⟩
  refine BundleTest.mapCLE (I := I) (fun a ↦ trivializationAt _ _ a) e U
    (fun _ _ hx ↦ ⟨hx, hx.2⟩) (fun _ _ hx ↦ hx.1)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt _ _ x, mem_baseSet_trivializationAt _ _ x⟩)
    (fun x ↦ (bundleLineDoubleDualEquiv (F := F) V (DensityBundle I M) x).toLinearEquiv.symm)
    (contMDiff_bundle_symm _
      (contMDiff_bundleLineDoubleDualEquiv (I := I) (n := ∞) V (DensityBundle I M)))
    (contMDiff_bundleLineDoubleDualEquiv (I := I) (n := ∞) V (DensityBundle I M))
    (fun _ ↦ ContMDiffMap.const (inclusionInDoubleDualEquiv ℝ F).symm.toContinuousLinearMap)
    (fun _ ↦ ContMDiffMap.const (NormedSpace.inclusionInDoubleDual ℝ F)) ?_ ?_
  -- `simp only [Trivialization.frameCoordinates_apply, ContMDiffSection.mapEquiv_apply]` leaves
  -- these goals unchanged: the test fibres and the fibres of `bundleLineDoubleDualEquiv` carry
  -- different but definitionally equal instances, so each step is closed by unification.
  -- In the frames induced at `a`, the inverse of evaluation is the inverse model evaluation.
  · intro a s x
    have h := (e a).bundleLineDoubleDualEquiv_symm_inFrame (d a) x.property (s x)
    rw [← inclusionInDoubleDualEquiv_apply] at h
    refine (Trivialization.frameCoordinates_apply _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Trivialization.frameCoordinates_apply _ _ _ _).symm)
    refine (congrArg (fun v ↦ (e a ⟨(x : M), v⟩).2)
      (ContMDiffSection.mapEquiv_apply _ _ _ s x)).trans ?_
    exact (ContinuousLinearEquiv.eq_symm_apply _).2 h
  -- In the same frames, evaluation is the model evaluation.
  · intro a s x
    refine (Trivialization.frameCoordinates_apply _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Trivialization.frameCoordinates_apply _ _ _ _).symm)
    refine (congrArg (fun v ↦ (trivializationAt _ _ a ⟨(x : M), v⟩).2) ?_).trans
      ((e a).bundleLineDoubleDualEquiv_inFrame (d a) x.property (s x))
    exact (DFunLike.congr_fun (DFunLike.congr_fun (ContMDiffSection.mapEquiv_symm _ _ _) s)
      (x : M)).trans (ContMDiffSection.mapEquiv_apply _ _ _ s x)
/-- A test of the dual-density bundle goes to the inverse fibrewise evaluation of its values. -/
theorem doubleDualEquiv_apply
    (s : DualDensityTest I M (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] DensityBundle I M x)) (x : M) :
    doubleDualEquiv s x = (bundleLineDoubleDualEquiv (F := F) V (DensityBundle I M) x).symm (s x) :=
  BundleTest.mapCLE_apply ..

/-- A bundle test of `V` goes to the fibrewise evaluation of its values. -/
theorem doubleDualEquiv_symm_apply (u : BundleTest I F V) (x : M) :
    doubleDualEquiv.symm u x = bundleLineDoubleDualEquiv (F := F) V (DensityBundle I M) x (u x) :=
  BundleTest.mapCLE_symm_apply ..

/-- The section of a dual-density test `s` is characterized by its pairings: a density-valued
functional `φ` on `V x` takes on it the value `s x φ`. -/
@[simp]
theorem apply_doubleDualEquiv_apply
    (s : DualDensityTest I M (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] DensityBundle I M x)) (x : M)
    (φ : V x →L[ℝ] DensityBundle I M x) :
    φ (doubleDualEquiv s x) = s x φ := by
  rw [doubleDualEquiv_apply]
  exact apply_bundleLineDoubleDualEquiv_symm (F := F) V (DensityBundle I M) x (s x) φ

/-- The dual-density test of a bundle test `u` pairs a density-valued functional `φ` on `V x`
with `u x`. -/
@[simp]
theorem doubleDualEquiv_symm_apply_apply (u : BundleTest I F V) (x : M)
    (φ : V x →L[ℝ] DensityBundle I M x) :
    doubleDualEquiv.symm u x φ = φ (u x) := by
  rw [doubleDualEquiv_symm_apply]
  exact bundleLineDoubleDualEquiv_apply (F := F) V (DensityBundle I M) x (u x) φ

/-- A dual-density test and its section of `V` vanish at the same points, so they have the same
support. -/
@[simp]
theorem doubleDualEquiv_apply_eq_zero_iff
    {s : DualDensityTest I M (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] DensityBundle I M x)} {x : M} :
    doubleDualEquiv s x = 0 ↔ s x = 0 := by
  rw [doubleDualEquiv_apply, ContinuousLinearEquiv.map_eq_zero_iff]

end TauCeti.DualDensityTest
