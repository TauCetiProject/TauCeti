/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Cochains
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Cech
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Trivialization
public import TauCeti.Topology.Sheaves.Cech.Cocycle
public import TauCeti.Topology.Sheaves.Cohomology.Restriction
public import TauCeti.Topology.Sheaves.Leray.Colimit
import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Finiteness
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Finite dimensionality of `H¹(X, 𝒪(L))` on a compact Riemann surface

Let `L` be a holomorphic line bundle, with any normed rank-one model `F`, on a compact Hausdorff
Riemann surface `X`. The first Čech cohomology `H¹(X, 𝒪(L))` of its sheaf of holomorphic sections
is a finite-dimensional complex vector space (Forster, Theorem 14.9 and §29). For the trivial line
bundle this is the finite dimensionality of `H¹(X, 𝒪)` for the holomorphic structure sheaf.

The proof combines two inputs, with Čech cochains read in holomorphic frames of `L`.

* On a coordinate disc contained in the base set of a holomorphic trivialization, the sheaf
  `𝒪(L)` is isomorphic to `𝒪` (`Bundle.Trivialization.holomorphicSectionSheafIso`), so such discs
  are acyclic for `𝒪(L)` (`TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray`). They form a
  neighbourhood basis, so on a compact surface the degree-one Leray theorem computes
  `H¹(X, 𝒪(L))` on every finite cover by opens with vanishing `H¹`.
* The Bergman-space argument of `TauCeti.RiemannSurface.ChartBergman`, with the overlap scalars
  `g i j` the actual transition functions between the frames: for three nested families
  `W'' ≤ W' ≤ W` of frame discs with relatively compact closures, finitely many square-integrable
  cocycles on `W'` span every holomorphic Čech `1`-cocycle on `W''` up to holomorphic coboundaries
  (`ChartBergman.exists_finset_forall_cocycle_eq_add_smul_sub`). Read through the native sections
  of `𝒪(L)` and the classical description of degree one Čech cohomology of a cover
  (`TauCeti.Topology.CechOne`), this says that the Čech `H¹` of the cover `W''` is finitely
  generated.

A finite cover by coordinate balls `(e i).preimageBall (c i) (r i)` whose concentric balls of
radius `8 r i` are still coordinate balls inside the base set of a trivialization
(`TauCeti.exists_finite_preimageBall_cover`) gives such nested families, with radii
`r i < 2 r i < 4 r i < 8 r i`.

## Main results

* `Bundle.Trivialization.subsingleton_H'_one_holomorphicSectionSheaf_chart_eball`: a coordinate
  disc inside the base set of a holomorphic trivialization of a line bundle has vanishing `H¹`
  for its sheaf of holomorphic sections.
* `TauCeti.RiemannSurface.exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf`: on a
  compact Riemann surface, every open cover has a finite refinement by such acyclic opens.
* `TauCeti.RiemannSurface.isIso_toCechCohomology_one_holomorphicSectionSheaf`: every finite cover
  by opens with vanishing `H¹` for `𝒪(L)` computes the degree one Čech cohomology of `𝒪(L)`.
* `TauCeti.RiemannSurface.ChartBergman.toBundleSections₁_mem_cocycles₁`: square-integrable
  cocycles for the frame transition scalars, realized in the frames, are native Čech cocycles.
* `TauCeti.RiemannSurface.ChartBergman.finite_homology_one_cechComplex_holomorphicSectionSheaf`:
  the Čech `H¹` of `𝒪(L)` on the innermost cover of nested relatively compact frame discs is
  finitely generated.
* `TauCeti.RiemannSurface.finiteDimensional_holomorphicSectionCechCohomology_one`:
  `H¹(X, 𝒪(L))` is finite-dimensional on every compact Hausdorff Riemann surface.
* `TauCeti.RiemannSurface.finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules`:
  `H¹(X, 𝒪)` is finite-dimensional on every compact Hausdorff Riemann surface.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§12–14 (Theorem 14.9) and §29.
-/

public noncomputable section

open Bundle CategoryTheory Metric Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]

namespace Bundle.Trivialization

open TauCeti

/-- **Frame discs are acyclic.** On a Riemann surface, a coordinate disc `e.source ∩ e ⁻¹' D`,
for a disc `D ⊆ e.target`, contained in the base set of a holomorphic trivialization `τ` of a line
bundle has vanishing `H¹` for the sheaf of holomorphic sections of the bundle. -/
theorem subsingleton_H'_one_holomorphicSectionSheaf_chart_eball
    (τ : Trivialization F (π F V)) [τ.IsLinear ℂ] (q : F ≃L[ℂ] ℂ)
    (hτa : τ.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {c : ℂ}
    {R : ENNReal} (hR : eball c R ⊆ e.target) (hτ : e.source ∩ e ⁻¹' eball c R ⊆ τ.baseSet) :
    Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1
      ⟨e.source ∩ e ⁻¹' eball c R, e.isOpen_inter_preimage isOpen_eball⟩) := by
  let U : Opens X := ⟨e.source ∩ e ⁻¹' eball c R, e.isOpen_inter_preimage isOpen_eball⟩
  let L := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (holomorphicSectionSheaf 𝓘(ℂ) F V)
  let G := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (holomorphicStructureSheafModules 𝓘(ℂ) X)
  have : Subsingleton (Sheaf.H' G 1 U) :=
    subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball he hR
  exact (U.cohomologyIsoOfRestrictIso (X := TopCat.of X) (F := L) (G := G)
    ((sheafCompose (Opens.grothendieckTopology U)
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).mapIso
        (τ.holomorphicSectionSheafIso q hτa (U := U) hτ)) 1).addCommGroupIsoToAddEquiv.subsingleton

end Bundle.Trivialization

namespace TauCeti.RiemannSurface

/-- **Acyclic neighbourhoods for a line bundle.** Every neighbourhood of a point of a Riemann
surface contains an open neighbourhood with vanishing `H¹` for the sheaf of holomorphic sections
of a holomorphic line bundle, namely a coordinate disc on which the bundle is trivial. -/
theorem exists_mem_subset_subsingleton_H'_one_holomorphicSectionSheaf
    (hF : Module.finrank ℂ F = 1) (x : X) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ W : Opens (TopCat.of X), x ∈ W ∧ (W : Set X) ⊆ N ∧
      Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1 W) := by
  have : Module.Finite ℂ F := Module.finite_of_finrank_eq_succ hF
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (hF.trans (Module.finrank_self ℂ).symm)
  let τ := trivializationAt F V x
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hN' : N ∩ τ.baseSet ∈ 𝓝 x :=
    Filter.inter_mem hN (τ.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x))
  have hT : e.target ∩ e.symm ⁻¹' (N ∩ τ.baseSet) ∈ 𝓝 (e x) :=
    Filter.inter_mem (e.open_target.mem_nhds (e.map_source hx))
      ((e.eventually_nhds' (· ∈ N ∩ τ.baseSet) hx).2 hN')
  obtain ⟨R, hR, hRT⟩ := EMetric.mem_nhds_iff.1 hT
  have hRe : eball (e x) R ⊆ e.target := hRT.trans inter_subset_left
  have hW : e.source ∩ e ⁻¹' eball (e x) R ⊆ N ∩ τ.baseSet := by
    rintro y ⟨hy, hyR⟩
    simpa only [mem_preimage, e.left_inv hy] using (hRT hyR).2
  exact ⟨⟨e.source ∩ e ⁻¹' eball (e x) R, e.isOpen_inter_preimage isOpen_eball⟩,
    ⟨hx, mem_eball_self hR⟩, fun y hy ↦ (hW hy).1,
    τ.subsingleton_H'_one_holomorphicSectionSheaf_chart_eball q
      (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ) ω τ)
      (IsManifold.chart_mem_maximalAtlas x) hRe fun y hy ↦ (hW hy).2⟩

/-- **Finite acyclic covers for a line bundle.** On a compact Riemann surface, every open cover is
refined by a finite open cover whose members have vanishing `H¹` for the sheaf of holomorphic
sections of a holomorphic line bundle. -/
theorem exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf [CompactSpace X]
    (hF : Module.finrank ℂ F = 1) {κ : Type*} (W : κ → Opens (TopCat.of X)) (hW : IsOpenCover W) :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens (TopCat.of X)), ⨆ i, U i = ⊤ ∧
      (∀ i, ∃ k, U i ≤ W k) ∧ ∀ i,
        Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1 (U i)) := by
  choose k hk using hW.exists_mem
  choose U hxU hUW hU using fun x ↦
    exists_mem_subset_subsingleton_H'_one_holomorphicSectionSheaf (V := V) hF x
      ((W (k x)).isOpen.mem_nhds (hk x))
  have hUc : IsOpenCover U := .mk <| eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hUc.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ U i.val, hs.iSup_eq_top, fun i ↦ ⟨k i.val, hUW i.val⟩,
    fun i ↦ hU i.val⟩

/-- **Finite acyclic covers compute `H¹(X, 𝒪(L))`.** On a compact Riemann surface, a finite open
cover whose members have vanishing `H¹` for the sheaf of holomorphic sections of a holomorphic line
bundle computes its degree one Čech cohomology. -/
theorem isIso_toCechCohomology_one_holomorphicSectionSheaf [CompactSpace X]
    (hF : Module.finrank ℂ F = 1)
    {ι : Type} [Finite ι] (U : ι → Opens (TopCat.of X)) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1 (U i))) :
    IsIso ((Topology.toCechCohomology (ModuleCat.{0} ℂ) 1 U (IsOpenCover.mk hU)).app
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj) :=
  Sheaf.isIso_toCechCohomology_one_of_subsingleton_H' _
    (fun W hW ↦ exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf hF W hW) U hU hFU

namespace ChartBergman

variable {ι : Type} (τ : ι → Trivialization F (π F V)) [∀ i, (τ i).IsLinear ℂ]
  (q : ι → F ≃L[ℂ] ℂ)
  (hτa : ∀ i, (τ i).toOpenPartialHomeomorph ∈
    (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
  {e : ι → OpenPartialHomeomorph X ℂ} (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
  {W W' W'' : ι → Opens X}

/-- Realized in the actual frames of a line bundle, a square-integrable cocycle for the frame
transition scalars is a native Čech cocycle of the sheaf of holomorphic sections. -/
theorem toBundleSections₁_mem_cocycles₁ (hW : ∀ i, (W i : Set X) ⊆ (e i).source)
    (hτ : ∀ i, (W i : Set X) ⊆ (τ i).baseSet)
    {ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))}
    (hξ : ξ ∈ cocycles₁ (fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i)) hW) :
    toBundleSections₁ τ q hτa he hW hτ ξ ∈
      Topology.CechOne.cocycles₁ (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W :=
  (Topology.CechOne.mem_cocycles₁_iff _ _).2
    ((mem_cocycles₁_iff_toBundleSections₁ τ q hτa he hW hτ).1 hξ)

omit [IsManifold 𝓘(ℂ) 1 X] in
include hτa in
/-- The frame coordinates of a native Čech one-cocycle of `𝒪(L)` on a family `W` inside the base
sets of the frames, extended by zero off the overlaps, are holomorphic functions on the overlaps
satisfying the twisted cocycle identity `ζ i j + g i j • ζ j k = ζ i k`, where `g i j` converts
coordinates in the frame of `j` into the frame of `i`. -/
private theorem exists_mdifferentiableOn_eq_of_mem_cocycles₁
    (hτ : ∀ i, (W i : Set X) ⊆ (τ i).baseSet)
    (z : Topology.CechOne.cocycles₁ (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W) :
    ∃ ζ : ι → ι → X → ℂ, (∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ζ i j) (W i ⊓ W j)) ∧
      (∀ i j k, ∀ x ∈ W i ⊓ W j ⊓ W k,
        ζ i j x + (τ j).scalarCoordChange (τ i) (q j) (q i) x • ζ j k x = ζ i k x) ∧
      ∀ i j (x : ↥(W i ⊓ W j)),
        ζ i j x = q i ((τ i).continuousLinearMapAt ℂ x (z.val i j x)) := by
  classical
  let ζ : ι → ι → X → ℂ := fun i j x ↦
    if hx : x ∈ W i ⊓ W j then q i ((τ i).continuousLinearMapAt ℂ x (z.val i j ⟨x, hx⟩)) else 0
  have hζ_eq (i j : ι) (x : ↥(W i ⊓ W j)) :
      ζ i j x = q i ((τ i).continuousLinearMapAt ℂ x (z.val i j x)) := by
    simp only [ζ]
    split_ifs with h
    · rfl
    · exact absurd x.property h
  refine ⟨ζ, fun i j x hx ↦ ?_, fun i j k x hx ↦ ?_, hζ_eq⟩
  · -- `ζ i j` is the frame coordinate of the native section `z i j`, a holomorphic function.
    have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥(W i ⊓ W j) ↦ ζ i j y) ⟨x, hx⟩ :=
      (holomorphicStructureSheafModules.contMDiff ((τ i).holomorphicSectionLinearEquiv (q i)
        (hτa i) (fun y (hy : y ∈ W i ⊓ W j) ↦ hτ i hy.1) (z.val i j)) ⟨x, hx⟩).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ (hζ_eq i j y).trans
          ((τ i).holomorphicSectionLinearEquiv_apply (q i) (hτa i) _ (z.val i j) y).symm)
    exact ((contMDiffAt_subtype_iff.1 hc).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  · have := congrArg (fun s ↦ q i ((τ i).continuousLinearMapAt ℂ x
        (holomorphicSectionSheaf.toFun 𝓘(ℂ) F V s ⟨x, hx⟩ : V x)))
      ((Topology.CechOne.mem_cocycles₁_iff (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W).1
        z.property i j k)
    simp only [holomorphicSectionSheaf.add_apply,
      holomorphicSectionSheaf.sub_apply, holomorphicSectionSheaf.map_apply,
      holomorphicSectionSheaf.zero_apply, map_add, map_sub, map_zero] at this
    -- Read `z j k` in the frame of `i` through the transition scalar from the frame of `j`.
    have hjk := (τ j).scalarCoordChange_mul_coordinate (τ i) (q j) (q i) (hτ j hx.1.2)
      (hτ i hx.1.1) (z.val j k ⟨x, hx.1.2, hx.2⟩)
    rw [hζ_eq i j ⟨x, hx.1⟩, hζ_eq j k ⟨x, hx.1.2, hx.2⟩, hζ_eq i k ⟨x, hx.1.1, hx.2⟩,
      smul_eq_mul]
    linear_combination this + hjk

include hτa in
/-- Two native Čech one-cocycles of `𝒪(L)` on a family `W` inside the base sets of the frames
have the same class when, at every point of every overlap, their frame coordinates differ by the
twisted coboundary `g i j • η j - η i` of holomorphic functions `η i` on the members. -/
private theorem toHomology_eq_of_forall_coordinate_eq (hτ : ∀ i, (W i : Set X) ⊆ (τ i).baseSet)
    (z z' : Topology.CechOne.cocycles₁ (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W)
    (η : ι → X → ℂ) (hη : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (η i) (W i))
    (h : ∀ i j (x : ↥(W i ⊓ W j)),
      q i ((τ i).continuousLinearMapAt ℂ x (z.val i j x)) =
        q i ((τ i).continuousLinearMapAt ℂ x (z'.val i j x)) +
          (τ j).scalarCoordChange (τ i) (q j) (q i) x * η j x - η i x) :
    Topology.CechOne.toHomology (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W z =
      Topology.CechOne.toHomology (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W z' := by
  have hηs (i : ι) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : W i ↦ η i x) := fun x ↦
    contMDiffAt_subtype_iff.2 (((hη i).contMDiffOn (W i).isOpen).contMDiffAt
      ((W i).isOpen.mem_nhds x.property))
  -- The sections of `𝒪(L)` with frame coordinates `η i`.
  let b (i : ι) := ((τ i).holomorphicSectionLinearEquiv (q i) (hτa i) (hτ i)).symm
    (holomorphicStructureSheafModules.ofContMDiff _ (hηs i))
  refine (Topology.CechOne.toHomology_eq_iff (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W z z').2
    ⟨b, ?_⟩
  funext i j
  ext x
  simp only [Topology.CechOne.d₀₁_apply, holomorphicSectionSheaf.sub_apply,
    holomorphicSectionSheaf.map_apply, Pi.sub_apply]
  -- Compare frame coordinates in the frame of `i`, an injective linear map on the fibre.
  let L := ((τ i).continuousLinearEquivAt ℂ x (hτ i x.property.1)).trans (q i)
  apply L.injective
  simp only [map_sub, L, ContinuousLinearEquiv.trans_apply,
    Trivialization.coe_continuousLinearEquivAt_eq]
  have hb (k : ι) (y : X) (hy : y ∈ W k) :
      q k ((τ k).continuousLinearMapAt ℂ y (b k ⟨y, hy⟩)) = η k y := by
    rw [Trivialization.holomorphicSectionLinearEquiv_symm_apply,
      (τ k).continuousLinearMapAt_symmL (hτ k hy), (q k).apply_symm_apply,
      holomorphicStructureSheafModules.ofContMDiff_apply]
  rw [← (τ j).scalarCoordChange_mul_coordinate (τ i) (q j) (q i) (hτ j x.property.2)
    (hτ i x.property.1)]
  simp only [Opens.inclusion]
  rw [hb j x x.property.2, hb i x x.property.1, h i j x]
  ring

include q hτa he in
/-- **The Čech `H¹` of `𝒪(L)` on nested frame discs is finitely generated** (Forster 14.9). Let
`τ i` be holomorphic trivializations of a line bundle with scalar model coordinates `q i`, and let
`closure (W'' i) ⊆ W' i`, `closure (W' i) ⊆ W i`, and `closure (W i)` compact inside the coordinate
disc `(e i).source ∩ e i ⁻¹' eball (c i) (R i)`, which lies in the base set of `τ i`, with the
`W'' i` covering `X`. Then the degree one Čech cohomology of the sheaf of holomorphic sections on
the cover `W''` is a finitely generated complex vector space. -/
theorem finite_homology_one_cechComplex_holomorphicSectionSheaf [T2Space X] [Finite ι]
    {c : ι → ℂ} {R : ι → ENNReal} (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hRτ : ∀ i, (e i).source ∩ e i ⁻¹' eball (c i) (R i) ⊆ (τ i).baseSet)
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hW'W : ∀ i, closure (W' i : Set X) ⊆ W i)
    (hIW : ∀ i, closure (W'' i : Set X) ⊆ W' i) (hcov : IsOpenCover W'') :
    Module.Finite ℂ (((cechComplexFunctor (C := Opens (TopCat.of X)) W'').obj
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj).homology 1) := by
  classical
  let g : ι → ι → X → ℂ := fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i)
  have hW (i : ι) : (W i : Set X) ⊆ (e i).source :=
    subset_closure.trans ((hWU i).trans inter_subset_left)
  have hτW (i : ι) : (W i : Set X) ⊆ (τ i).baseSet :=
    subset_closure.trans ((hWU i).trans (hRτ i))
  have h' (i : ι) : W' i ≤ W i := subset_closure.trans (hW'W i)
  have h'' (i : ι) : W'' i ≤ W' i := subset_closure.trans (hIW i)
  have hW' := subset_source_of_le hW h'
  have hW'' := subset_source_of_le hW' h''
  have hτW' (i : ι) : (W' i : Set X) ⊆ (τ i).baseSet := fun _ hx ↦ hτW i (h' i hx)
  have hτW'' (i : ι) : (W'' i : Set X) ⊆ (τ i).baseSet := fun _ hx ↦ hτW' i (h'' i hx)
  -- The transition scalars are holomorphic, trivial on the diagonal and multiplicative.
  obtain ⟨s, hs⟩ := exists_finset_forall_cocycle_eq_add_smul_sub g he hW hR (fun _ ↦ rfl) hKW hWU
    hW'W hIW hcov
    (fun i j ↦ ((Trivialization.contMDiffOn_scalarCoordChange (τ j) (τ i) (q j) (q i) (hτa j)
      (hτa i)).mdifferentiableOn (by simp)).mono fun _ hx ↦ ⟨hRτ j hx.2, hRτ i hx.1⟩)
    (fun i _ hx ↦ (τ i).scalarCoordChange_self (q i) (hτW' i hx))
    (fun i j k _ hx ↦ (τ k).scalarCoordChange_mul_scalarCoordChange (τ j) (τ i) (q k) (q j) (q i)
      (hRτ k hx.2) (hRτ j hx.1.2) (hRτ i hx.1.1))
  -- Restrict square-integrable cocycles on `W'` to native cocycles on `W''`, then take classes.
  let Φ : cocycles₁ g hW' →ₗ[ℂ]
      Topology.CechOne.cocycles₁ (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W'' :=
    LinearMap.codRestrict _ (toBundleSections₁ τ q hτa he hW'' hτW'' ∘ₗ
      (cocycles₁ g hW'').subtype ∘ₗ (restrictCocycles₁ g hW' h'').toLinearMap)
      fun ξ ↦ toBundleSections₁_mem_cocycles₁ τ q hτa he hW'' hτW''
        (restrictCocycles₁ g hW' h'' ξ).property
  have hΦ (ξ : cocycles₁ g hW') (i j : ι) (x : ↥(W'' i ⊓ W'' j)) :
      q i ((τ i).continuousLinearMapAt ℂ x ((Φ ξ).val i j x)) =
        BergmanSpace.representative (ξ.val i j) (e i x) := by
    simp only [Φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      ContinuousLinearMap.coe_coe, coe_restrictCocycles₁, toBundleSections₁_apply]
    refine ((τ i).bergmanSection_coordinate_self (q i) (hτa i) (he i) _ _ _ x).trans ?_
    rw [restrictCochains₁_apply, BergmanSpace.representative_restrict _ _
      ((e i).map_mem_imageOpens (hW'' i x.property.1) x.property)]
  let Fh := Topology.CechOne.toHomology (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W'' ∘ₗ Φ
  refine ⟨⟨s.image Fh, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
  obtain ⟨z, rfl⟩ :=
    Topology.CechOne.toHomology_surjective (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W'' y
  obtain ⟨ζ, hζ, hζc, hζ_eq⟩ := exists_mdifferentiableOn_eq_of_mem_cocycles₁ τ q hτa hτW'' z
  obtain ⟨b, hb, η, hη, hζη⟩ := hs ζ hζ hζc
  -- `z` and the realization of `b` differ by the twisted coboundary of `η`.
  have hzb : Topology.CechOne.toHomology (holomorphicSectionSheaf 𝓘(ℂ) F V).obj W'' z = Fh b :=
    toHomology_eq_of_forall_coordinate_eq τ q hτa hτW'' z (Φ b) η hη fun i j x ↦ by
      rw [← hζ_eq, hζη i j x x.property, hΦ, smul_eq_mul]
  rw [hzb, Finset.coe_image, Submodule.span_image]
  exact Submodule.mem_map_of_mem hb

end ChartBergman

omit [IsManifold 𝓘(ℂ) 1 X] [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)] in
/-- A compact charted space carrying a fibre bundle is covered by finitely many coordinate balls
`(e i).preimageBall (c i) (r i)` whose concentric closed balls of radius `8 r i` lie in the chart
target, and whose coordinate balls of radius `a r i`, `a ≤ 8`, lie in the base set of the
trivialization at a point `k i`. -/
private theorem exists_finite_preimageBall_cover_baseSet [CompactSpace X] :
    ∃ (ι : Type) (_ : Finite ι) (e : ι → OpenPartialHomeomorph X ℂ) (c : ι → ℂ) (r : ι → ℝ)
      (k : ι → X), (∀ i, e i ∈ atlas ℂ X) ∧ (∀ i, 0 < r i) ∧
        (∀ i, closedBall (c i) (8 * r i) ⊆ (e i).target) ∧
        (∀ i, ∀ a ≤ 8, (e i).source ∩ e i ⁻¹' eball (c i) (.ofReal (a * r i)) ⊆
          (trivializationAt F V (k i)).baseSet) ∧
        ⨆ i, (e i).preimageBall (c i) (r i) = ⊤ := by
  let T : X → Opens X := fun x ↦ ⟨(trivializationAt F V x).baseSet,
    (trivializationAt F V x).open_baseSet⟩
  have hT : IsOpenCover T := .mk <| eq_top_iff.2 fun x _ ↦
    Opens.mem_iSup.2 ⟨x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  obtain ⟨ι, _, e, c, r, hatlas, hr, hK, hKT, hcov⟩ :=
    exists_finite_preimageBall_cover (H := ℂ) 8 hT
  choose k hk using hKT
  refine ⟨ι, inferInstance, e, c, r, k, hatlas, hr, hK, fun i a ha x ⟨hx, hxB⟩ ↦ ?_, hcov⟩
  rw [mem_preimage, eball_ofReal] at hxB
  have hxB' : e i x ∈ closedBall (c i) (8 * r i) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ha (hr i).le)
      (ball_subset_closedBall hxB)
  have := hk i ⟨e i x, hxB', rfl⟩
  rw [(e i).left_inv hx] at this
  exact this

/-- **Finiteness of `H¹(X, 𝒪(L))`** (Forster 14.9, §29). On a compact Hausdorff Riemann surface,
the first Čech cohomology of the sheaf of holomorphic sections of a holomorphic line bundle, with
any normed rank-one model, is a finite-dimensional complex vector space. -/
theorem finiteDimensional_holomorphicSectionCechCohomology_one [CompactSpace X] [T2Space X]
    (hF : Module.finrank ℂ F = 1) :
    FiniteDimensional ℂ (holomorphicSectionCechCohomology 𝓘(ℂ) F V 1) := by
  have : Module.Finite ℂ F := Module.finite_of_finrank_eq_succ hF
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (hF.trans (Module.finrank_self ℂ).symm)
  -- Coordinate balls `B i = (e i).preimageBall (c i) (r i)` covering `X`, with `8 r i` in range
  -- and the ball of radius `8 r i` inside the base set of a trivialization `τ i`.
  obtain ⟨ι, _, e, c, r, k, hatlas, hr, hK, hτ, hcov⟩ :=
    exists_finite_preimageBall_cover_baseSet (F := F) (V := V) (X := X)
  let τ (i : ι) := trivializationAt F V (k i)
  have he (i : ι) : e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X :=
    IsManifold.subset_maximalAtlas (hatlas i)
  have hτa (i : ι) := Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ) ω (τ i)
  have hsmall (i : ι) (a : ℝ) (ha : a ≤ 8) : closedBall (c i) (a * r i) ⊆ (e i).target :=
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ha (hr i).le)).trans (hK i)
  have hlt (i : ι) {a b : ℝ} (hab : a < b) : a * r i < b * r i :=
    mul_lt_mul_of_pos_right hab (hr i)
  -- The innermost family `B`, written with `one_mul` so that it matches the cover.
  have hB (i : ι) : (e i).preimageBall (c i) (r i) =
      ⟨(e i).source ∩ e i ⁻¹' eball (c i) (.ofReal (r i)),
        (e i).isOpen_inter_preimage isOpen_eball⟩ := by
    ext x
    rw [SetLike.mem_coe, OpenPartialHomeomorph.mem_preimageBall, Opens.coe_mk, eball_ofReal]
    rfl
  have hfin := ChartBergman.finite_homology_one_cechComplex_holomorphicSectionSheaf τ
    (fun _ ↦ q) hτa he
    (W := fun i ↦ (e i).preimageBall (c i) (4 * r i))
    (W' := fun i ↦ (e i).preimageBall (c i) (2 * r i))
    (W'' := fun i ↦ (e i).preimageBall (c i) (r i)) (R := fun i ↦ .ofReal (8 * r i))
    (fun i ↦ by rw [eball_ofReal]; exact ball_subset_closedBall.trans (hK i))
    (fun i ↦ hτ i 8 le_rfl)
    (fun i ↦ (e i).isCompact_closure_preimageBall (hsmall i 4 (by norm_num)))
    (fun i ↦ by
      rw [eball_ofReal, ← OpenPartialHomeomorph.coe_preimageBall]
      exact (e i).closure_preimageBall_subset (hsmall i 4 (by norm_num)) (hlt i (by norm_num)))
    (fun i ↦ (e i).closure_preimageBall_subset (hsmall i 2 (by norm_num)) (hlt i (by norm_num)))
    (fun i ↦ by
      simpa only [one_mul] using (e i).closure_preimageBall_subset (hsmall i 1 (by norm_num))
        (hlt i (by norm_num : (1 : ℝ) < 2)))
    (.mk hcov)
  refine (Sheaf.finite_cechCohomology_one_iff_finite_homology_cechComplex _
    (fun W hW ↦ exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf hF W hW)
    (fun i ↦ (e i).preimageBall (c i) (r i)) hcov fun i ↦ ?_).2 hfin
  have hT : eball (c i) (.ofReal (r i)) ⊆ (e i).target := by
    rw [eball_ofReal]
    simpa only [one_mul] using ball_subset_closedBall.trans (hsmall i 1 (by norm_num))
  rw [hB]
  exact (τ i).subsingleton_H'_one_holomorphicSectionSheaf_chart_eball q (hτa i) (he i) hT
    (by simpa only [one_mul] using hτ i 1 (by norm_num))

/-- **Finiteness of `H¹(X, 𝒪(L))` for line bundles with model fibre `ℂ`.** -/
instance finiteDimensional_holomorphicSectionCechCohomology_one_complex
    {L : X → Type} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
    [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
    [ContMDiffVectorBundle ω ℂ L 𝓘(ℂ)] [CompactSpace X] [T2Space X] :
    FiniteDimensional ℂ (holomorphicSectionCechCohomology 𝓘(ℂ) ℂ L 1) :=
  finiteDimensional_holomorphicSectionCechCohomology_one (Module.finrank_self ℂ)

/-- **Finiteness of `H¹(X, 𝒪)`** (Forster 14.9). On a compact Hausdorff Riemann surface the first
Čech cohomology of the holomorphic structure sheaf is a finite-dimensional complex vector space:
it is the cohomology of the trivial line bundle. -/
instance finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules [CompactSpace X]
    [T2Space X] :
    FiniteDimensional ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) :=
  (holomorphicSectionCechCohomology.trivialIso 𝓘(ℂ) X 1).toLinearEquiv.finiteDimensional

end TauCeti.RiemannSurface
