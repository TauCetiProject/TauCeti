/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Smooth Gram pairings of alternating forms

The Gram inner product on real alternating forms varies smoothly with the metric of a
finite-rank Riemannian bundle. Its normalization is the sum over increasing tuples of an
orthonormal frame, rather than over all ordered tuples. In particular, this gives the smooth
fibre pairing needed to integrate inner products of differential forms without choosing an
orientation or replacing their continuous-alternating-map fibres.

The regularity theorem works locally and at every differentiability order. The proof uses
the smooth orthonormal frames constructed by Gram–Schmidt and the pointwise formula
`TauCeti.alternatingFormInner_eq_sum`. Restricting `TauCeti.alternatingFormInner` to any `C^n`
subbundle of alternating forms given by `C^n` local frames then yields an induced `C^n` Riemannian
bundle metric (`TauCeti.alternatingFormSubbundleRiemannianMetric`).

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsContMDiffRiemannianBundle I n F V]
  {k : ℕ}

/-- The Gram pairing of two `C^n` sections of the real alternating-form bundle is `C^n`
within a set. No orientation of the original bundle is required. -/
theorem ContMDiffWithinAt.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ} {s : Set M} {x : M}
    (hα : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) s x)
    (hβ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y)) s x) :
    ContMDiffWithinAt I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) s x := by
  classical
  let : FiniteDimensional ℝ F :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).finiteDimensional
  let e := trivializationAt F V x
  let b := Module.finBasis ℝ F
  let v : Fin (Module.finrank ℝ F) → ∀ y, V y := fun i y ↦
    if hy : y ∈ e.baseSet then e.orthonormalBasis b ⟨y, hy⟩ i else 0
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  have hv (i) : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F y (v i y)) x :=
    (e.contMDiffOn_orthonormalBasis b i).contMDiffAt (e.open_baseSet.mem_nhds hx)
  have hval (γ : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ)
      (hγ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (γ y)) s x)
      (t : powersetCard (Fin (Module.finrank ℝ F)) k) :
      ContMDiffWithinAt I 𝓘(ℝ) n
        (fun y ↦ γ y (fun i ↦ v (powersetCard.ofFinEmbEquiv.symm t i) y)) s x :=
    (contMDiffWithinAt_totalSpace_iff.1 (hγ.continuousAlternatingMap_bundle_apply
      (fun i ↦ (hv _).contMDiffWithinAt))).2
  have hs := contMDiffWithinAt_finsetSum (t := Finset.univ) fun t _ ↦
    (hval α hα t).mul (hval β hβ t)
  have heq (y : M) (hy : y ∈ e.baseSet) :
      (∑ t : powersetCard (Fin (Module.finrank ℝ F)) k,
        α y (fun i ↦ v (powersetCard.ofFinEmbEquiv.symm t i) y) *
          β y (fun i ↦ v (powersetCard.ofFinEmbEquiv.symm t i) y)) =
        TauCeti.alternatingFormInner (V y) k (α y) (β y) := by
    simpa only [v, dite_eq_left hy, Function.comp_def] using
      (TauCeti.alternatingFormInner_eq_sum (e.orthonormalBasis b ⟨y, hy⟩) (α y) (β y)).symm
  exact hs.congr_of_eventuallyEq
    (Filter.mem_of_superset (nhdsWithin_le_nhds (e.open_baseSet.mem_nhds hx))
      fun y hy ↦ (heq y hy).symm) ((heq x hx).symm)

/-- The Gram pairing of two alternating-form sections smooth at a point is smooth there. -/
theorem ContMDiffAt.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) x)
    (hβ : ContMDiffAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y)) x) :
    ContMDiffAt I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) x :=
  ContMDiffWithinAt.alternatingFormInner_bundle hα hβ

/-- The Gram pairing preserves regularity of alternating-form sections on arbitrary sets. -/
theorem ContMDiffOn.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ} {s : Set M}
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) s)
    (hβ : ContMDiffOn I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y)) s) :
    ContMDiffOn I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) s :=
  fun x hx ↦ (hα x hx).alternatingFormInner_bundle (hβ x hx)

/-- The Gram pairing of smooth real alternating-form sections is smooth. -/
theorem ContMDiff.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ}
    (hα : ContMDiff I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)))
    (hβ : ContMDiff I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y))) :
    ContMDiff I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) :=
  fun x ↦ (hα x).alternatingFormInner_bundle (hβ x)

namespace TauCeti

/-- Restricting the Gram inner product `TauCeti.alternatingFormInner` on exterior `k`-forms of a
finite-rank `C^n` Riemannian bundle `V` to any `C^n` subbundle `W` given by `C^n` local frames
yields an induced `C^n` Riemannian bundle metric on `W`. -/
def alternatingFormSubbundleRiemannianMetric
    {ι : Type*} [Fintype ι] {W : ∀ x, Submodule ℝ (V x [⋀^Fin k]→L[ℝ] ℝ)}
    (hW : HasLocalContMDiffSubbundleFrames I n (F [⋀^Fin k]→L[ℝ] ℝ) ι W) :
    letI := subbundleTopology (F [⋀^Fin k]→L[ℝ] ℝ) (F' := ι → ℝ) W
    letI := hW.fiberBundle
    letI := hW.vectorBundle
    ContMDiffRiemannianMetric I n (ι → ℝ) (fun x ↦ W x) :=
  letI := subbundleTopology (F [⋀^Fin k]→L[ℝ] ℝ) (F' := ι → ℝ) W
  letI := hW.fiberBundle
  letI := hW.vectorBundle
  letI := hW.contMDiffVectorBundle
  let g (x : M) :=
    IsBilinearMap.toContinuousBilinearMap (𝕜 := ℝ) (E := W x) (F := W x) (G := ℝ)
      (f := fun v w : W x ↦ alternatingFormInner (V x) k v.1 w.1)
      { add_left := fun _ _ _ ↦ by simp
        smul_left := fun _ _ _ ↦ by simp
        add_right := fun _ _ _ ↦ by simp
        smul_right := fun _ _ _ ↦ by simp }
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection
    (⟨g, by
      have hg (x : M) (v w : W x) : g x v w = alternatingFormInner (V x) k v.1 w.1 := rfl
      intro x
      let eW := trivializationAt (ι → ℝ) (fun y ↦ W y) x
      have hx : x ∈ eW.baseSet := FiberBundle.mem_baseSet_trivializationAt (ι → ℝ) (fun y ↦ W y) x
      have hsec (c : ι → ℝ) : ContMDiffAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
          (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) (E := fun z ↦ V z [⋀^Fin k]→L[ℝ] ℝ) y
            (eW.symm y c : V y [⋀^Fin k]→L[ℝ] ℝ)) x := by
        have hs : ContMDiffAt I (I.prod 𝓘(ℝ, ι → ℝ)) n
            (fun y ↦ TotalSpace.mk' (ι → ℝ) (E := fun z ↦ W z) y (eW.symm y c)) x := by
          rw [contMDiffAt_section_iff]
          refine (contMDiffAt_const (c := c)).congr_of_eventuallyEq ?_
          filter_upwards [eW.open_baseSet.mem_nhds hx] with y hy
          exact congr(Prod.snd $(eW.apply_mk_symm hy c))
        exact (hW.contMDiff_totalSpace_inclusion _).comp x hs
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, contMDiffAt_clm_apply.2 fun u ↦
        contMDiffAt_clm_apply.2 fun w ↦ ?_⟩
      refine (ContMDiffAt.alternatingFormInner_bundle (hsec u) (hsec w)).congr_of_eventuallyEq ?_
      filter_upwards [eW.open_baseSet.mem_nhds hx] with y hy
      rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hy hy (by simp)]
      simp [hg, eW]⟩ :
      Manifold.BilinearSection I (ι → ℝ) (fun x ↦ W x) ℝ n)
    ((Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(Manifold.mem_symmetricBilinearSections _).2
        fun _ v w ↦ alternatingFormInner_comm v.1 w.1,
        fun _ v hv ↦ (alternatingFormInner_self_nonneg v.1).lt_of_ne'
          (mt (fun h0 ↦ Subtype.ext (alternatingFormInner_self_eq_zero.mp h0)) hv)⟩)

/-- `TauCeti.alternatingFormSubbundleRiemannianMetric` evaluates on `v, w ∈ W x` as the ambient
Gram inner product `TauCeti.alternatingFormInner`. -/
@[simp]
theorem alternatingFormSubbundleRiemannianMetric_inner
    {ι : Type*} [Fintype ι] {W : ∀ x, Submodule ℝ (V x [⋀^Fin k]→L[ℝ] ℝ)}
    (hW : HasLocalContMDiffSubbundleFrames I n (F [⋀^Fin k]→L[ℝ] ℝ) ι W)
    (x : M) (v w : W x) :
    letI := subbundleTopology (F [⋀^Fin k]→L[ℝ] ℝ) (F' := ι → ℝ) W
    letI := hW.fiberBundle
    letI := hW.vectorBundle
    (alternatingFormSubbundleRiemannianMetric hW).inner x v w =
      alternatingFormInner (V x) k
        (v : V x [⋀^Fin k]→L[ℝ] ℝ) (w : V x [⋀^Fin k]→L[ℝ] ℝ) := by
  let := subbundleTopology (F [⋀^Fin k]→L[ℝ] ℝ) (F' := ι → ℝ) W
  let := hW.fiberBundle
  let := hW.vectorBundle
  rw [alternatingFormSubbundleRiemannianMetric,
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner]
  rfl

end TauCeti
