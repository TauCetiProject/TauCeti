/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Geometry.Diffeology.Induced
public import TauCeti.Geometry.Diffeology.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The diffeology of a smooth manifold

`manifoldDiffeology I M` equips a finite-dimensional boundaryless real smooth manifold `M`
modelled on `I : ModelWithCorners ℝ E H` with the native diffeology whose plots are its smooth
Cartesian parametrizations. Its D-topology is the original manifold topology. Smoothness between
these diffeologies is precisely ordinary manifold smoothness, so this construction does not depend
on a choice of smooth atlas or model.

As for Mathlib's `NormedSpace.toDiffeology`, the construction is not a global instance:
`IsContMDiffCompatible I M` records agreement with a diffeology already installed on a charted
space `M`. This avoids conflicting diffeologies on normed spaces, open submanifolds, and products:

* On a real normed space `V`, `manifoldDiffeology 𝓘(ℝ, V) V` agrees with `NormedSpace.toDiffeology`
  (`TauCeti.manifoldDiffeology_self`).
* On an open submanifold `U : Opens M`, the subspace diffeology is manifold-compatible whenever
  `M` is (`TauCeti.instIsContMDiffCompatibleOpens`), so `manifoldDiffeology I U` agrees with the
  subspace diffeology (`TauCeti.manifoldDiffeology_opens`).
* On a finite product `M × N`, the product diffeology is compatible with `I.prod J` whenever the
  factors are compatible with `I` and `J` (`TauCeti.instIsContMDiffCompatibleProd`), so
  `manifoldDiffeology (I.prod J) (M × N)` agrees with the product diffeology
  (`TauCeti.manifoldDiffeology_prod`) and has the product topology as its D-topology.

On open subsets of Cartesian spaces, local plots (`TauCeti.Diffeology.IsPlotOn`) are precisely
`ContMDiffOn` maps (`TauCeti.isPlotOn_iff_contMDiffOn`). Globally, `hp.isPlot` and `hp.contMDiff`
convert between smooth Cartesian parametrizations and plots (`TauCeti.isPlot_iff_contMDiff`), and
`hf.dSmooth` and `hf.contMDiff` convert between manifold and diffeological smoothness when the
source is a finite-dimensional boundaryless smooth manifold (`TauCeti.dSmooth_iff_contMDiff`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 4, for smooth manifolds as diffeological spaces.
-/

public noncomputable section

open Set Function Diffeology
open scoped Manifold Topology ContDiff

namespace TauCeti

section Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [tM : TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- The standard diffeology of a finite-dimensional boundaryless real smooth manifold.
Its plots are smooth manifold maps, and its D-topology is the given topology. -/
@[instance_reducible]
def manifoldDiffeology : DiffeologicalSpace M :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p ↦ ContMDiffOn 𝓘(ℝ, _) I ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contMDiffOn_congr h
    isPlot := fun p ↦ ContMDiff 𝓘(ℝ, _) I ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ ↦ contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf.contMDiffOn h
    locality := fun _ _ h x hx ↦ by
      obtain ⟨v, hv, hxv, hp⟩ := h x hx
      exact (hp.contMDiffAt (hv.mem_nhds hxv)).contMDiffWithinAt
    dTopology := tM
    isOpen_iff_preimages_plots := fun {u} ↦ by
      refine ⟨fun hu _ p hp ↦ IsOpen.preimage hp.continuous hu,
        fun h ↦ isOpen_iff_mem_nhds.mpr ?_⟩
      intro x hx
      obtain ⟨U, hxU, ⟨φ⟩⟩ := exists_opens_diffeomorph_euclideanSpace (I := I) (n := ⊤)
        (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
      let p := Subtype.val ∘ φ.symm
      have hp : ContMDiff 𝓘(ℝ, _) I ∞ p := contMDiff_subtype_val.comp φ.symm.contMDiff
      have ho : IsOpen (Subtype.val '' (φ ⁻¹' (p ⁻¹' u))) :=
        U.isOpen.isOpenMap_subtype_val _ ((h p hp).preimage φ.continuous)
      have hm : x ∈ Subtype.val '' (φ ⁻¹' (p ⁻¹' u)) := ⟨⟨x, hxU⟩, by simp [p, hx], rfl⟩
      exact Filter.mem_of_superset (ho.mem_nhds hm)
        (by rintro _ ⟨y, hy, rfl⟩; simpa [p] using hy) }

variable {I M}

/-- The plots of the manifold diffeology are exactly the smooth Cartesian parametrizations. -/
@[simp]
theorem isPlot_manifoldDiffeology_iff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    @IsPlot M (manifoldDiffeology I M) n p ↔
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p :=
  -- The construction passes its global plots unchanged to `ofCorePlotsOn`.
  (Iff.rfl)

/-- The D-topology of the manifold diffeology is the original manifold topology. -/
@[simp]
theorem dTopology_manifoldDiffeology : @dTopology M (manifoldDiffeology I M) = tM :=
  -- `ofCorePlotsOn` retains the topology supplied by the construction.
  (rfl)

end Construction

/-- A diffeology agrees with a smooth manifold structure if its Cartesian plots are
exactly the smooth manifold maps. -/
class IsContMDiffCompatible {E : outParam Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : outParam Type*} [TopologicalSpace H] (I : outParam (ModelWithCorners ℝ E H))
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [DiffeologicalSpace M] : Prop where
  /-- A Cartesian parametrization is a plot exactly when it is smooth in manifold charts. -/
  isPlot_iff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p

section Compatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [DiffeologicalSpace M] [IsContMDiffCompatible I M]

/-- A Cartesian parametrization is a plot exactly when it is smooth as a manifold map. -/
theorem isPlot_iff_contMDiff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p :=
  IsContMDiffCompatible.isPlot_iff

/-- A smooth Cartesian parametrization of a compatible manifold is a plot. -/
@[fun_prop]
protected theorem _root_.ContMDiff.isPlot {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p) : IsPlot p :=
  isPlot_iff_contMDiff.mpr hp

/-- A plot of a compatible manifold is smooth as a manifold map. -/
protected theorem _root_.Diffeology.IsPlot.contMDiff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : IsPlot p) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p :=
  isPlot_iff_contMDiff.mp hp

/-- A manifold map defined on a subset of a Cartesian space that is smooth on that subset is a
local plot on that subset. -/
protected theorem _root_.ContMDiffOn.isPlotOn {n : ℕ} {u : Set (EuclideanSpace ℝ (Fin n))}
    {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p u) : Diffeology.IsPlotOn u p :=
  Diffeology.isPlotOn_iff.mpr fun _ hfu hf ↦
    (hp.comp_contMDiff hf.contMDiff fun z ↦ hfu (mem_univ z)).isPlot

/-- On an open subset of a Cartesian space, local plots of a compatible manifold are precisely
the smooth manifold maps on that subset. -/
theorem isPlotOn_iff_contMDiffOn {n : ℕ} {u : Set (EuclideanSpace ℝ (Fin n))} (hu : IsOpen u)
    {p : EuclideanSpace ℝ (Fin n) → M} :
    Diffeology.IsPlotOn u p ↔ ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p u := by
  refine ⟨fun hp z hz ↦ ?_, ContMDiffOn.isPlotOn⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu z hz
  let φ := OpenPartialHomeomorph.univBall z ε
  have htarget : φ.target = Metric.ball z ε := OpenPartialHomeomorph.univBall_target z hε
  have hφu : MapsTo φ univ u := fun y _ ↦
    hball (htarget ▸ φ.map_source (by simp [φ, OpenPartialHomeomorph.univBall_source]))
  have hzt : z ∈ φ.target := htarget ▸ Metric.mem_ball_self hε
  have hpφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ (p ∘ φ) :=
    (hp.isPlot_comp hφu OpenPartialHomeomorph.contDiff_univBall).contMDiff
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      φ.symm z :=
    (htarget ▸ OpenPartialHomeomorph.contDiffOn_univBall_symm).contMDiffOn.contMDiffAt
      (φ.open_target.mem_nhds hzt)
  exact ((hpφ.contMDiffAt.comp z hsymm).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (φ.open_target.mem_nhds hzt) fun y hy ↦
      congrArg p (φ.right_inv hy).symm)).contMDiffWithinAt

/-- A local plot on an open subset of a Cartesian space is smooth as a manifold map on that
subset. -/
protected theorem Diffeology.IsPlotOn.contMDiffOn {n : ℕ} {u : Set (EuclideanSpace ℝ (Fin n))}
    {p : EuclideanSpace ℝ (Fin n) → M} (hp : Diffeology.IsPlotOn u p) (hu : IsOpen u) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p u :=
  (isPlotOn_iff_contMDiffOn hu).mp hp

/-- A smooth manifold map between compatible diffeologies is diffeologically smooth.
This implication needs neither finite-dimensionality nor smooth atlas assumptions. -/
@[fun_prop]
protected theorem _root_.ContMDiff.dSmooth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    [DiffeologicalSpace N] [IsContMDiffCompatible J N] {f : M → N}
    (hf : ContMDiff I J ∞ f) : DSmooth f :=
  fun _ _ hp ↦ (hf.comp hp.contMDiff).isPlot

/-- A manifold map that is smooth on a subset restricts to a smooth map on that subset with its
subspace diffeology. -/
protected theorem _root_.ContMDiffOn.dSmooth_domRestrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    [DiffeologicalSpace N] [IsContMDiffCompatible J N] {f : M → N} {s : Set M}
    (hf : ContMDiffOn I J ∞ f s) : DSmooth (s.domRestrict f) :=
  fun _ p hp ↦ (hf.comp_contMDiff
    (Diffeology.isPlot_subtype_iff.mp hp).contMDiff fun z ↦ (p z).2).isPlot

/-- A normed-space-compatible diffeology is also compatible with the normed space's
canonical manifold structure. No finite-dimensionality is needed for this implication. -/
instance instIsContMDiffCompatibleSelf {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DiffeologicalSpace V] [IsContDiffCompatible V] : IsContMDiffCompatible 𝓘(ℝ, V) V where
  isPlot_iff := isPlot_iff_contDiff.trans contMDiff_iff_contDiff.symm

/-- The subspace diffeology on an open submanifold is compatible with its open-submanifold
charted space structure. -/
instance instIsContMDiffCompatibleOpens (U : TopologicalSpace.Opens M) :
    IsContMDiffCompatible I U where
  isPlot_iff := Diffeology.isPlot_subtype_iff.trans <|
    (isPlot_iff_contMDiff (I := I)).trans (ContMDiff.subtypeVal_comp_iff U _)

/-- The product diffeology on a product of compatible manifolds is compatible with the product
manifold structure. -/
instance instIsContMDiffCompatibleProd
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    [DiffeologicalSpace N] [IsContMDiffCompatible J N] :
    IsContMDiffCompatible (I.prod J) (M × N) where
  isPlot_iff := Diffeology.isPlot_prod_iff.trans <|
    (and_congr (isPlot_iff_contMDiff (I := I)) (isPlot_iff_contMDiff (I := J))).trans
      (contMDiff_prod_iff _).symm

end Compatible

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- `manifoldDiffeology I M` is compatible with the smooth manifold structure on `M`. -/
instance instIsContMDiffCompatibleManifoldDiffeology (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] :
    @IsContMDiffCompatible E _ _ H _ I M _ _ (manifoldDiffeology I M) := by
  let := manifoldDiffeology I M
  exact ⟨isPlot_manifoldDiffeology_iff⟩

/-- Characterization of the manifold diffeology by its plots. -/
theorem isContMDiffCompatible_iff_eq_manifoldDiffeology [d : DiffeologicalSpace M] :
    IsContMDiffCompatible I M ↔ d = manifoldDiffeology I M := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ instIsContMDiffCompatibleManifoldDiffeology I M⟩
  ext n p
  rw [isPlot_manifoldDiffeology_iff]
  exact h.isPlot_iff

/-- The manifold construction agrees with Mathlib's standard normed-space diffeology. -/
@[simp]
theorem manifoldDiffeology_self (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    manifoldDiffeology 𝓘(ℝ, E) E = NormedSpace.toDiffeology E := by
  let := NormedSpace.toDiffeology E
  exact (isContMDiffCompatible_iff_eq_manifoldDiffeology.mp inferInstance).symm

/-- On an open submanifold, the manifold diffeology agrees with the subspace diffeology. -/
theorem manifoldDiffeology_opens (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
    (U : TopologicalSpace.Opens M) :
    manifoldDiffeology I U =
      @Diffeology.instDiffeologicalSpaceSubtype M (manifoldDiffeology I M) (· ∈ U) := by
  let : DiffeologicalSpace M := manifoldDiffeology I M
  have : IsContMDiffCompatible I M := instIsContMDiffCompatibleManifoldDiffeology I M
  exact (isContMDiffCompatible_iff_eq_manifoldDiffeology.mp
    (instIsContMDiffCompatibleOpens (I := I) U)).symm

/-- On a product of finite-dimensional boundaryless smooth manifolds, the manifold diffeology
agrees with the product diffeology. -/
theorem manifoldDiffeology_prod
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [BoundarylessManifold J N] :
    manifoldDiffeology (I.prod J) (M × N) =
      @Diffeology.instDiffeologicalSpaceProd M N
        (manifoldDiffeology I M) (manifoldDiffeology J N) := by
  let : DiffeologicalSpace M := manifoldDiffeology I M
  let : DiffeologicalSpace N := manifoldDiffeology J N
  have : IsContMDiffCompatible I M := instIsContMDiffCompatibleManifoldDiffeology I M
  have : IsContMDiffCompatible J N := instIsContMDiffCompatibleManifoldDiffeology J N
  exact (isContMDiffCompatible_iff_eq_manifoldDiffeology.mp
    (instIsContMDiffCompatibleProd (I := I) (J := J))).symm

/-- Smoothly equivalent atlases give the same diffeology, even when their models differ. -/
theorem manifoldDiffeology_eq_of_contMDiff_id
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [ChartedSpace G M] [IsManifold J ∞ M] [BoundarylessManifold J M]
    (h : ContMDiff I J ∞ (id : M → M)) (h' : ContMDiff J I ∞ (id : M → M)) :
    manifoldDiffeology I M = manifoldDiffeology J M := by
  ext n p
  rw [isPlot_manifoldDiffeology_iff, isPlot_manifoldDiffeology_iff]
  exact ⟨fun hp ↦ h.comp hp, fun hp ↦ h'.comp hp⟩

variable [DiffeologicalSpace M] [IsContMDiffCompatible I M]

/-- The D-topology of a manifold-compatible diffeology on a finite-dimensional boundaryless smooth
manifold equals its original topology. -/
instance instIsDTopologyCompatibleManifold : IsDTopologyCompatible M := by
  rw [isContMDiffCompatible_iff_eq_manifoldDiffeology.mp
    (inferInstance : IsContMDiffCompatible I M)]
  let := manifoldDiffeology I M
  exact ⟨dTopology_manifoldDiffeology⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [DiffeologicalSpace N] [IsContMDiffCompatible J N]

/-- A map from a finite-dimensional boundaryless smooth manifold to a manifold-compatible
diffeological space is diffeologically smooth exactly when it is smooth as a manifold map. -/
theorem dSmooth_iff_contMDiff {f : M → N} :
    DSmooth f ↔ ContMDiff I J ∞ f := by
  refine ⟨fun hf x ↦ ?_, ContMDiff.dSmooth⟩
  obtain ⟨U, hxU, ⟨φ⟩⟩ := exists_opens_diffeomorph_euclideanSpace (I := I) (n := ⊤)
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  rw [← contMDiffAt_subtype_iff (U := U) (x := ⟨x, hxU⟩)]
  have hfp : ContMDiff 𝓘(ℝ, _) J ∞ (f ∘ Subtype.val ∘ φ.symm) :=
    (hf _ _ (contMDiff_subtype_val.comp φ.symm.contMDiff).isPlot).contMDiff
  exact (hfp.comp φ.contMDiff ⟨x, hxU⟩).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ congrArg f (congrArg Subtype.val (φ.left_inv u)).symm)

/-- A diffeologically smooth map from a finite-dimensional boundaryless smooth manifold to a
compatible charted space is smooth as a manifold map. -/
protected theorem _root_.Diffeology.DSmooth.contMDiff {f : M → N} (hf : DSmooth f) :
    ContMDiff I J ∞ f :=
  dSmooth_iff_contMDiff.mp hf

end Manifold

end TauCeti
