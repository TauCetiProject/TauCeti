/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Geometry.Diffeology.Basic
public import TauCeti.Geometry.Diffeology.Induced
public import TauCeti.Geometry.Diffeology.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
public import TauCeti.Geometry.Manifold.IsManifold.Prod

import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The diffeology of a smooth manifold

`manifoldDiffeology E M` equips a finite-dimensional boundaryless real manifold with the
native diffeology whose plots are its smooth Cartesian parametrizations. Its D-topology is
the original manifold topology. Smoothness between these diffeologies is precisely ordinary
manifold smoothness, so this construction does not depend on a choice of smooth atlas.

As for Mathlib's `NormedSpace.toDiffeology`, the construction is not a global instance:
`IsContMDiffCompatible` records agreement with a diffeology already installed on a manifold.
This avoids conflicting diffeologies on normed spaces and products. In particular, the normed
space construction agrees with the manifold construction, open submanifolds
(`TopologicalSpace.Opens`) inherit compatible subspace diffeologies
(`instIsContMDiffCompatibleOpens`, `manifoldDiffeology_opens`), and finite products carry
compatible product diffeologies (`isContMDiffCompatible_chartedSpaceProd`,
`manifoldDiffeology_prod`, `dSmooth_prod_iff_contMDiff`).

The plot conversion lemmas support dot notation: `hp.isPlot` turns
a smooth Cartesian parametrization into a plot, and `hp.contMDiff` turns a plot into a smooth
manifold map. The equivalence is also available as `isPlot_iff_contMDiff`, and on open subsets of
Cartesian spaces as `isPlotOn_iff_contMDiffOn`.
Likewise, `hf.dSmooth` and `hf.contMDiff` convert between manifold and diffeological
smoothness, with the equivalence available as `dSmooth_iff_contMDiff`.

The plot axioms and compatibility interface follow Mathlib's
`DiffeologicalSpace.ofCorePlotsOn` and `Diffeology.IsContDiffCompatible`.
-/

public noncomputable section

open Set Function Diffeology
open scoped Manifold Topology ContDiff

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (M : Type*) [tM : TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The standard diffeology of a finite-dimensional boundaryless real smooth manifold.
Its plots are smooth manifold maps, and its D-topology is the given topology. -/
@[instance_reducible]
def manifoldDiffeology : DiffeologicalSpace M :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p => ContMDiffOn 𝓘(ℝ, _) 𝓘(ℝ, E) ∞ p u
    isPlotOn_congr := fun _ _ _ h => contMDiffOn_congr h
    isPlot := fun p => ContMDiff 𝓘(ℝ, _) 𝓘(ℝ, E) ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ => contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf => hp.comp hf.contMDiffOn h
    locality := fun _ _ h x hx => by
      obtain ⟨v, hv, hxv, hp⟩ := h x hx
      exact (hp.contMDiffAt (hv.mem_nhds hxv)).contMDiffWithinAt
    dTopology := tM
    isOpen_iff_preimages_plots := fun {u} => by
      refine ⟨fun hu _ p hp => IsOpen.preimage hp.continuous hu,
        fun h => isOpen_iff_mem_nhds.mpr ?_⟩
      intro x hx
      obtain ⟨e, hs, he, hp, _⟩ := exists_contMDiff_parametrization (E := E) (n := ⊤) x
      have ho := (e.isOpenEmbedding hs).isOpenMap _ (h e hp)
      have hm : x ∈ e '' (e ⁻¹' u) := ⟨e.symm x, by simpa [e.right_inv he], e.right_inv he⟩
      exact Filter.mem_of_superset (ho.mem_nhds hm) (image_preimage_subset _ _) }

variable {E M}

/-- The plots of the manifold diffeology are exactly the smooth Cartesian parametrizations. -/
theorem isPlot_manifoldDiffeology_iff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    @IsPlot M (manifoldDiffeology E M) n p ↔
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p :=
  -- The construction passes its global plots unchanged to `ofCorePlotsOn`.
  (Iff.rfl)

/-- The D-topology of the manifold diffeology is the original manifold topology. -/
theorem dTopology_manifoldDiffeology : @dTopology M (manifoldDiffeology E M) = tM :=
  -- `ofCorePlotsOn` retains the topology supplied by the construction.
  (rfl)

/-- A diffeology agrees with the smooth manifold structure if its Cartesian plots are
exactly the smooth manifold maps. -/
class IsContMDiffCompatible (E : outParam (Type*)) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [DiffeologicalSpace M] : Prop where
  /-- A Cartesian parametrization is a plot exactly when it is smooth in manifold charts. -/
  isPlot_iff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p

section

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [DiffeologicalSpace M] [IsContMDiffCompatible E M]

/-- A Cartesian parametrization is a plot exactly when it is smooth as a manifold map. -/
theorem isPlot_iff_contMDiff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p :=
  IsContMDiffCompatible.isPlot_iff

/-- A smooth Cartesian parametrization of a compatible manifold is a plot. -/
@[fun_prop]
protected theorem _root_.ContMDiff.isPlot {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p) : IsPlot p :=
  isPlot_iff_contMDiff.mpr hp

/-- A plot of a compatible manifold is smooth as a manifold map. -/
protected theorem _root_.Diffeology.IsPlot.contMDiff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : IsPlot p) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p :=
  isPlot_iff_contMDiff.mp hp

/-- A smooth manifold map on a subset of a Cartesian space into a compatible manifold is a plot on
that subset. -/
protected theorem _root_.ContMDiffOn.isPlotOn {n : ℕ} {u : Set (EuclideanSpace ℝ (Fin n))}
    {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p u) :
    Diffeology.IsPlotOn u p :=
  Diffeology.isPlotOn_iff.mpr fun _ hfu hf ↦
    (hp.comp_contMDiff hf.contMDiff fun x ↦ hfu (mem_univ x)).isPlot

/-- A plot on an open subset of a Cartesian space into a compatible manifold is smooth on that
subset as a manifold map. -/
protected theorem Diffeology.IsPlotOn.contMDiffOn {n : ℕ} {u : Set (EuclideanSpace ℝ (Fin n))}
    {p : EuclideanSpace ℝ (Fin n) → M} (hp : Diffeology.IsPlotOn u p) (hu : IsOpen u) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p u := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu z hz
  let φ := OpenPartialHomeomorph.univBall z ε
  have htarget : φ.target = Metric.ball z ε := OpenPartialHomeomorph.univBall_target z hε
  have hφu : MapsTo φ univ u := fun y _ ↦
    hball (htarget ▸ φ.map_source (by simp [φ, OpenPartialHomeomorph.univBall_source]))
  have hpφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (p ∘ φ) :=
    (hp.isPlot_comp hφu OpenPartialHomeomorph.contDiff_univBall).contMDiff
  have hnhds : Metric.ball z ε ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
  have hφsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      φ.symm z :=
    OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn.contMDiffAt hnhds
  exact ((hpφ.contMDiffAt.comp z hφsymm).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem hnhds
      fun y hy ↦ congrArg p (φ.right_inv (htarget.symm ▸ hy)).symm)).contMDiffWithinAt

/-- On an open subset of a Cartesian space, a map into a compatible manifold is a local plot if
and only if it is smooth on that open subset as a manifold map. -/
theorem isPlotOn_iff_contMDiffOn {n : ℕ} {u : Set (EuclideanSpace ℝ (Fin n))}
    {p : EuclideanSpace ℝ (Fin n) → M} (hu : IsOpen u) :
    Diffeology.IsPlotOn u p ↔ ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p u :=
  ⟨fun hp ↦ hp.contMDiffOn hu, ContMDiffOn.isPlotOn⟩

/-- An open submanifold of a compatible manifold carries a compatible subspace diffeology, without
requiring finite-dimensionality or atlas smoothness. -/
instance instIsContMDiffCompatibleOpens
    (U : TopologicalSpace.Opens M) : IsContMDiffCompatible E U where
  isPlot_iff {_ _} := by
    rw [Diffeology.isPlot_subtype_iff, isPlot_iff_contMDiff, ContMDiff.subtypeVal_comp_iff]

/-- A smooth manifold map between compatible diffeologies is diffeologically smooth.
This implication needs neither finite-dimensionality nor smooth atlas assumptions. -/
@[fun_prop]
protected theorem _root_.ContMDiff.dSmooth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [DiffeologicalSpace N] [IsContMDiffCompatible F N] {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) : DSmooth f :=
  fun _ _ hp => isPlot_iff_contMDiff.mpr (hf.comp (isPlot_iff_contMDiff.mp hp))

/-- A manifold map that is smooth on a subset restricts to a smooth map on that subset with its
subspace diffeology. -/
protected theorem _root_.ContMDiffOn.dSmooth_domRestrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [DiffeologicalSpace N] [IsContMDiffCompatible F N] {f : M → N} {s : Set M}
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f s) : DSmooth (s.domRestrict f) :=
  fun _ p hp => isPlot_iff_contMDiff.mpr (hf.comp_contMDiff
    (isPlot_iff_contMDiff.mp (TauCeti.Diffeology.isPlot_subtype_iff.mp hp)) fun z => (p z).2)

/-- A Cartesian parametrization into a product of compatible charted spaces is a plot of the
product diffeology if and only if it is smooth for the product model `𝓘(ℝ, E).prod 𝓘(ℝ, F)`. -/
theorem isPlot_prod_iff_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [DiffeologicalSpace N] [IsContMDiffCompatible F N]
    {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M × N} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ p := by
  rw [Diffeology.isPlot_prod_iff, isPlot_iff_contMDiff, isPlot_iff_contMDiff, contMDiff_prod_iff]

/-- The product diffeology on `M × N` is compatible with `TauCeti.chartedSpaceProd E F M N`,
without requiring finite-dimensionality or atlas smoothness. -/
theorem isContMDiffCompatible_chartedSpaceProd
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [DiffeologicalSpace N] [IsContMDiffCompatible F N] :
    @IsContMDiffCompatible (E × F) _ _ (M × N) _ (chartedSpaceProd E F M N) inferInstance := by
  let : ChartedSpace (E × F) (M × N) := chartedSpaceProd E F M N
  refine ⟨fun {n p} ↦ ?_⟩
  rw [isPlot_prod_iff_contMDiff, modelWithCornersSelf_prod]

/-- A manifold map from a product `M × N` of compatible charted spaces to a compatible charted
space `P` that is smooth for `𝓘(ℝ, E).prod 𝓘(ℝ, F)` is diffeologically smooth. -/
@[fun_prop]
protected theorem _root_.ContMDiff.dSmooth_prod
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [DiffeologicalSpace N] [IsContMDiffCompatible F N]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    {f : M × N → P} (hf : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) 𝓘(ℝ, G) ∞ f) : DSmooth f :=
  fun _ _ hp ↦ isPlot_iff_contMDiff.mpr (hf.comp (isPlot_prod_iff_contMDiff.mp hp))

end

instance : @IsContMDiffCompatible E _ _ M _ _ (manifoldDiffeology E M) := by
  let := manifoldDiffeology E M
  exact ⟨isPlot_manifoldDiffeology_iff⟩

/-- Characterization of the manifold diffeology by its plots. -/
theorem isContMDiffCompatible_iff_eq_manifoldDiffeology [d : DiffeologicalSpace M] :
    IsContMDiffCompatible (E := E) (M := M) ↔ d = manifoldDiffeology E M := by
  refine ⟨fun h => ?_, fun h => h ▸ inferInstance⟩
  ext n p
  rw [isPlot_manifoldDiffeology_iff]
  exact h.isPlot_iff

/-- The manifold construction agrees with Mathlib's standard normed-space diffeology. -/
@[simp]
theorem manifoldDiffeology_self : manifoldDiffeology E E = NormedSpace.toDiffeology E := by
  let := NormedSpace.toDiffeology E
  ext n p
  rw [isPlot_manifoldDiffeology_iff, isPlot_iff_contDiff]
  exact contMDiff_iff_contDiff

/-- Smoothly equivalent atlases give the same diffeology, even when their model spaces differ. -/
theorem manifoldDiffeology_eq_of_contMDiff_id
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    (h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (id : M → M))
    (h' : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (id : M → M)) :
    manifoldDiffeology E M = manifoldDiffeology F M := by
  ext n p
  rw [isPlot_manifoldDiffeology_iff, isPlot_manifoldDiffeology_iff]
  exact ⟨fun hp => h.comp hp, fun hp => h'.comp hp⟩

/-- On an open submanifold `U` of `M`, the manifold diffeology agrees with the subspace diffeology
induced from `manifoldDiffeology E M`. -/
theorem manifoldDiffeology_opens_eq_induced (U : TopologicalSpace.Opens M) :
    manifoldDiffeology E U =
      @Diffeology.inducedDiffeology M U (manifoldDiffeology E M) Subtype.val := by
  let : DiffeologicalSpace M := manifoldDiffeology E M
  exact ((isContMDiffCompatible_iff_eq_manifoldDiffeology (E := E) (M := U)).mp inferInstance).symm

/-- For two finite-dimensional boundaryless smooth manifolds `M` and `N`, the manifold diffeology on
`M × N` (charted by `TauCeti.chartedSpaceProd E F M N`) equals the product of their manifold
diffeologies. -/
theorem manifoldDiffeology_prod_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] :
    @manifoldDiffeology (E × F) _ _ _ (M × N) _ (chartedSpaceProd E F M N)
        isManifold_chartedSpaceProd =
      @Diffeology.instDiffeologicalSpaceProd M N
        (manifoldDiffeology E M) (manifoldDiffeology F N) := by
  let : DiffeologicalSpace M := manifoldDiffeology E M
  let : DiffeologicalSpace N := manifoldDiffeology F N
  let : ChartedSpace (E × F) (M × N) := chartedSpaceProd E F M N
  have : IsManifold 𝓘(ℝ, E × F) ∞ (M × N) := isManifold_chartedSpaceProd
  have h : IsContMDiffCompatible (E × F) (M × N) := isContMDiffCompatible_chartedSpaceProd
  exact (isContMDiffCompatible_iff_eq_manifoldDiffeology.mp h).symm

variable [DiffeologicalSpace M] [IsContMDiffCompatible (E := E) (M := M)]

/-- The D-topology of a manifold-compatible diffeology equals its original topology. -/
instance : IsDTopologyCompatible M := by
  rw [isContMDiffCompatible_iff_eq_manifoldDiffeology.mp
    (inferInstance : IsContMDiffCompatible (E := E) (M := M))]
  let := manifoldDiffeology E M
  exact ⟨dTopology_manifoldDiffeology⟩

/-- On an open submanifold of a compatible manifold, the manifold diffeology equals the subspace
diffeology. -/
@[simp]
theorem manifoldDiffeology_opens (U : TopologicalSpace.Opens M) :
    manifoldDiffeology E U = Diffeology.instDiffeologicalSpaceSubtype :=
  ((isContMDiffCompatible_iff_eq_manifoldDiffeology (E := E) (M := U)).mp inferInstance).symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [DiffeologicalSpace N] [IsContMDiffCompatible (E := F) (M := N)]

/-- A map between manifold-compatible diffeologies is smooth exactly when it is smooth
as a map of manifolds. -/
theorem dSmooth_iff_contMDiff {f : M → N} :
    DSmooth f ↔ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  constructor
  · intro hf x
    obtain ⟨e, _, hx, he, hei⟩ := exists_contMDiff_parametrization (E := E) (n := ⊤) x
    have hfe := (IsContMDiffCompatible.isPlot_iff (E := F)).mp
      (hf _ e (IsContMDiffCompatible.isPlot_iff.mpr he))
    have hg := hfe.contMDiffAt.comp x
      (hei.contMDiffAt (e.open_target.mem_nhds hx))
    exact hg.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
      (e.open_target.mem_nhds hx) (fun y hy => congrArg f (e.right_inv hy).symm))
  · exact ContMDiff.dSmooth

/-- A diffeologically smooth map from a finite-dimensional smooth manifold to a compatible
charted space is smooth as a manifold map. -/
protected theorem _root_.Diffeology.DSmooth.contMDiff {f : M → N} (hf : DSmooth f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f :=
  dSmooth_iff_contMDiff.mp hf

/-- A map from a finite-dimensional smooth manifold into a product of compatible charted spaces is
diffeologically smooth if and only if it is smooth for the product model `𝓘(ℝ, F).prod 𝓘(ℝ, G)`. -/
theorem dSmooth_iff_contMDiff_prod
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    {f : M → N × P} :
    DSmooth f ↔ ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, F).prod 𝓘(ℝ, G)) ∞ f :=
  ⟨fun hf ↦ (contMDiff_prod_iff f).mpr
      ⟨(Diffeology.dSmooth_fst.comp hf).contMDiff, (Diffeology.dSmooth_snd.comp hf).contMDiff⟩,
    fun hf ↦ ((contMDiff_prod_iff f).mp hf).1.dSmooth.prodMk
      ((contMDiff_prod_iff f).mp hf).2.dSmooth⟩

section ProdDom

variable [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- On a product `M × N` of compatible manifolds, the manifold diffeology (for
`TauCeti.chartedSpaceProd E F M N`) equals the product diffeology. -/
theorem manifoldDiffeology_prod :
    @manifoldDiffeology (E × F) _ _ _ (M × N) _ (chartedSpaceProd E F M N)
        isManifold_chartedSpaceProd = Diffeology.instDiffeologicalSpaceProd := by
  let : ChartedSpace (E × F) (M × N) := chartedSpaceProd E F M N
  have : IsManifold 𝓘(ℝ, E × F) ∞ (M × N) := isManifold_chartedSpaceProd
  have h : IsContMDiffCompatible (E × F) (M × N) := isContMDiffCompatible_chartedSpaceProd
  exact (isContMDiffCompatible_iff_eq_manifoldDiffeology.mp h).symm

/-- A map from a product `M × N` of finite-dimensional smooth manifolds into a compatible charted
space `P` is diffeologically smooth if and only if it is smooth as a manifold map for
`𝓘(ℝ, E).prod 𝓘(ℝ, F)`. -/
theorem dSmooth_prod_iff_contMDiff
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    {f : M × N → P} :
    DSmooth f ↔ ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) 𝓘(ℝ, G) ∞ f := by
  let : ChartedSpace (E × F) (M × N) := chartedSpaceProd E F M N
  have : IsManifold 𝓘(ℝ, E × F) ∞ (M × N) := isManifold_chartedSpaceProd
  have : IsContMDiffCompatible (E × F) (M × N) := isContMDiffCompatible_chartedSpaceProd
  rw [dSmooth_iff_contMDiff (E := E × F) (F := G), modelWithCornersSelf_prod]

/-- A diffeologically smooth map out of a product `M × N` of finite-dimensional smooth manifolds
into a compatible charted space is smooth for `𝓘(ℝ, E).prod 𝓘(ℝ, F)`. -/
protected theorem _root_.Diffeology.DSmooth.contMDiff_prod
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    {f : M × N → P} (hf : DSmooth f) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) 𝓘(ℝ, G) ∞ f :=
  dSmooth_prod_iff_contMDiff.mp hf

end ProdDom

/-- A normed-space-compatible diffeology is also compatible with the normed space's
canonical manifold structure. No finite-dimensionality is needed for this implication. -/
instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DiffeologicalSpace V] [IsContDiffCompatible V] : IsContMDiffCompatible V V where
  isPlot_iff := isPlot_iff_contDiff.trans contMDiff_iff_contDiff.symm

end TauCeti
