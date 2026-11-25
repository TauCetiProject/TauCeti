/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback.Basic
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The determinant line bundle of a vector bundle

Let `E → B` be a vector bundle over a complete nontrivially normed field `𝕜`, with
finite-dimensional model fibre `F` of dimension `r`, presented by Mathlib's `FiberBundle` and
`VectorBundle` classes. Its **determinant line** `det E = ⋀ʳ E` is the family
`TauCeti.DetBundle 𝕜 F E` whose fibre over `x` is the top exterior power `⋀ʳ (E x)`, with the
topology of a finite-dimensional vector space. It is a vector bundle with model fibre `𝕜`
(`TauCeti.DetBundle.vectorBundle`) whose fibres are lines (`TauCeti.DetBundle.finrank_eq_one`):

* every trivialization `e` of `E` in its atlas induces a trivialization
  `TauCeti.DetBundle.trivialization e` of `det E` over the same base set, which reads
  `v₁ ∧ ⋯ ∧ vᵣ` over `x` as the determinant of `(e v₁, …, e vᵣ)` in the fixed basis
  `Module.finBasis 𝕜 F` of the model fibre (`TauCeti.DetBundle.chartCoord_ιMulti`);
* its coordinate changes are the determinants of the coordinate changes of `E`
  (`TauCeti.DetBundle.coordChangeL_trivialization`).

For `𝕜 = ℂ`, the determinant bundle is a complex line bundle.

The construction is natural:

* a continuous fibrewise linear isomorphism `e` between two vector bundles with model fibre `F`
  induces the isomorphism of determinant lines `TauCeti.DetBundle.congrHomeomorph e`, given on
  each fibre by `LinearEquiv.exteriorPower`, functorially (`TauCeti.DetBundle.congrEquiv_refl`,
  `TauCeti.DetBundle.congrEquiv_trans`, `TauCeti.DetBundle.congrEquiv_symm`);
* arbitrary fibrewise families of continuous linear equivalences between independent model
  presentations induce the fibrewise determinant transport `TauCeti.DetBundle.congrModelEquiv`.
  No continuity of the family in the base is assumed or asserted;
* for a continuous map `f : B' → B`, the pullback of `det E` is the determinant line of the
  pullback of `E`, by the map induced by the identity of the fibres of `E`
  (`TauCeti.DetBundle.pullbackHomeomorph`).

When `E` is itself a line, its determinant line is `E`: the fibre `⋀¹ (E x)` is `E x`
(`TauCeti.DetBundle.lineEquiv`, from `exteriorPower.oneEquiv`), and these identifications form a
homeomorphism of total spaces (`TauCeti.DetBundle.lineHomeomorph`). Continuous sections
`s₁, …, sᵣ` of `E` have a continuous wedge `x ↦ s₁(x) ∧ ⋯ ∧ sᵣ(x)`, a section of `det E`
(`TauCeti.DetBundle.continuous_ιMulti`), which vanishes nowhere when the `sᵢ` form a frame
(`exteriorPower.ιMulti_ne_zero_iff`).

For a bundle with model fibre `Fin n → 𝕜`, the determinant line agrees with the determinant line
`TauCeti.FiniteRankBundleCore.det` of its point-indexed coordinate core
`TauCeti.FiniteRankBundleCore.ofBundle 𝕜 n E`: the total space of the reconstructed core is
homeomorphic to that of `det E`, linearly on each fibre
(`TauCeti.DetBundle.ofBundleDetHomeomorph`).

## Main definitions

* `TauCeti.DetBundle 𝕜 F E`: the determinant lines of the fibres of `E`.
* `TauCeti.DetBundle.chartCoord`: the coordinate on a fibre of `det E` induced by a linear
  trivialization of `E`.
* `TauCeti.DetBundle.trivialization`: the trivialization of `det E` induced by a trivialization
  of `E`.
* `TauCeti.DetBundle.congrHomeomorph`: the isomorphism of determinant lines induced by an
  isomorphism of vector bundles.
* `TauCeti.DetBundle.pullbackHomeomorph`: the pullback of `det E` is `det (f *ᵖ E)`.
* `TauCeti.DetBundle.lineEquiv`, `TauCeti.DetBundle.lineHomeomorph`: the determinant line of a
  line bundle `L` is `L`.
* `TauCeti.DetBundle.ofBundleDetHomeomorph`: comparison with `FiniteRankBundleCore.det`.
* `TauCeti.DetBundle.fiberDetLineEquiv`: identification with the intrinsic top exterior power
  indexed by the actual fibre rank.
* `TauCeti.DetBundle.congrModelEquiv`: fibrewise transport between independent model presentations,
  without a continuity hypothesis in the base.
* `TauCeti.DetBundle.zeroEquiv`: the canonical scalar coordinate of the degree-zero exterior power
  when the model has rank zero.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §3 and §14.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
-/

public section

noncomputable section

open Bundle Set Topology Module

namespace TauCeti

/-- The **determinant line** of a vector bundle `E` whose model fibre `F` has dimension `r`: over
`x`, the top exterior power `⋀ʳ (E x)` of the fibre, with the topology of a finite-dimensional
vector space. It is a vector bundle (`TauCeti.DetBundle.vectorBundle`) whose trivializations are
induced from those of `E` with model `F`. Use `TauCeti.DetBundle.linearEquiv` to pass to the
exterior power of the fibre itself. -/
@[expose]
def DetBundle (𝕜 : Type*) [CommRing 𝕜] {B : Type*} (F : Type*) [AddCommGroup F] [Module 𝕜 F]
    (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] (x : B) : Type _ :=
  ⋀[𝕜]^(finrank 𝕜 F) (E x)

namespace DetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] {x : B}

instance : AddCommGroup (DetBundle 𝕜 F E x) :=
  inferInstanceAs (AddCommGroup (⋀[𝕜]^(finrank 𝕜 F) (E x)))

instance : Module 𝕜 (DetBundle 𝕜 F E x) :=
  inferInstanceAs (Module 𝕜 (⋀[𝕜]^(finrank 𝕜 F) (E x)))

/-- A fibre of the determinant line carries its topology as a finite-dimensional vector space,
the finest topology making addition and scalar multiplication continuous. -/
instance : TopologicalSpace (DetBundle 𝕜 F E x) := moduleTopology 𝕜 _

instance : IsModuleTopology 𝕜 (DetBundle 𝕜 F E x) := ⟨rfl⟩

instance : IsTopologicalAddGroup (DetBundle 𝕜 F E x) :=
  IsModuleTopology.isTopologicalAddGroup 𝕜 _

variable (𝕜 F E x) in
/-- The fibre of `TauCeti.DetBundle 𝕜 F E` over `x` is the top exterior power of `E x`. -/
@[expose]
def linearEquiv : DetBundle 𝕜 F E x ≃ₗ[𝕜] ⋀[𝕜]^(finrank 𝕜 F) (E x) :=
  LinearEquiv.refl 𝕜 _

@[simp]
theorem linearEquiv_apply (v : DetBundle 𝕜 F E x) : linearEquiv 𝕜 F E x v = v := (rfl)

@[simp]
theorem linearEquiv_symm_apply (v : ⋀[𝕜]^(finrank 𝕜 F) (E x)) :
    (linearEquiv 𝕜 F E x).symm v = v := (rfl)

section Chart

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [FiniteDimensional 𝕜 F]

variable (F) in
/-- The fixed identification of the determinant line of the model fibre with `𝕜`, given by the
basis `Module.finBasis 𝕜 F`. -/
abbrev modelCoord : detLine 𝕜 F ≃ₗ[𝕜] 𝕜 :=
  (Module.finBasis 𝕜 F).exteriorPowerTopEquiv

/-- The coordinate on the fibre of `det E` over `x` induced by a linear trivialization `e` of
`E`: the isomorphism `⋀ʳ (E x) ≃ ⋀ʳ F` induced by `e` on the fibre, followed by the fixed
coordinate `TauCeti.DetBundle.modelCoord` of the determinant line of the model fibre. -/
def chartCoord (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) :
    DetBundle 𝕜 F E x ≃ₗ[𝕜] 𝕜 :=
  linearEquiv 𝕜 F E x ≪≫ₗ (e.linearEquivAt 𝕜 x hx).exteriorPower (finrank 𝕜 F) ≪≫ₗ modelCoord F

theorem chartCoord_def (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) :
    chartCoord e hx = linearEquiv 𝕜 F E x ≪≫ₗ
      (e.linearEquivAt 𝕜 x hx).exteriorPower (finrank 𝕜 F) ≪≫ₗ modelCoord F :=
  (rfl)

/-- The coordinate formula on an arbitrary determinant-line vector. -/
@[simp]
theorem chartCoord_apply (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (hx : x ∈ e.baseSet)
    (v : DetBundle 𝕜 F E x) :
    chartCoord e hx v = modelCoord F
      ((e.linearEquivAt 𝕜 x hx).exteriorPower (finrank 𝕜 F) (linearEquiv 𝕜 F E x v)) := by
  rw [chartCoord_def, LinearEquiv.trans_apply, LinearEquiv.trans_apply]

/-- The inverse coordinate formula on a scalar. -/
@[simp]
theorem chartCoord_symm_apply (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (hx : x ∈ e.baseSet) (c : 𝕜) :
    (chartCoord e hx).symm c = (linearEquiv 𝕜 F E x).symm
      (((e.linearEquivAt 𝕜 x hx).exteriorPower (finrank 𝕜 F)).symm ((modelCoord F).symm c)) := by
  rw [chartCoord_def, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply]

/-- A chart coordinate reads `v₁ ∧ ⋯ ∧ vᵣ` as the determinant of `(e v₁, …, e vᵣ)` in the basis
`Module.finBasis 𝕜 F`. -/
theorem chartCoord_ιMulti (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (hx : x ∈ e.baseSet)
    (v : Fin (finrank 𝕜 F) → E x) :
    chartCoord e hx ((linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ v)) =
      (Module.finBasis 𝕜 F).det (fun i ↦ (e ⟨x, v i⟩).2) := by
  simp only [chartCoord_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.exteriorPower_apply_ιMulti, Module.Basis.exteriorPowerTopEquiv_apply_ιMulti]
  congr 1

/-- **The transitions of the determinant line.** Passing from the chart coordinate of `e` to that
of `e'` multiplies by the determinant of the coordinate change of `E` from `e` to `e'`. -/
theorem chartCoord_chartCoord_symm (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) (c : 𝕜) :
    chartCoord e' hx' ((chartCoord e hx).symm c) =
      (e.coordChangeL 𝕜 e' x : F →L[𝕜] F).det * c := by
  have h : ∀ y, (e'.linearEquivAt 𝕜 x hx').exteriorPower (finrank 𝕜 F)
      ((e.linearEquivAt 𝕜 x hx).symm.exteriorPower (finrank 𝕜 F) y) =
      (e.coordChangeL 𝕜 e' x).toLinearEquiv.exteriorPower (finrank 𝕜 F) y := fun y ↦ by
    rw [e.coe_coordChangeL' e' ⟨hx, hx'⟩, LinearEquiv.exteriorPower_trans,
      LinearEquiv.trans_apply]
  simp only [chartCoord_def, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.exteriorPower_symm]
  rw [h, ← LinearEquiv.coe_toLinearMap
      ((e.coordChangeL 𝕜 e' x).toLinearEquiv.exteriorPower (finrank 𝕜 F)),
    LinearEquiv.exteriorPower_toLinearMap, Module.Basis.exteriorPowerTopEquiv_map,
    LinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.det, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- A chart coordinate is an inducing map. -/
theorem isInducing_chartCoord (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (hx : x ∈ e.baseSet) : IsInducing (chartCoord (𝕜 := 𝕜) e hx) :=
  (Homeomorph.mk (chartCoord e hx).toEquiv
    (IsModuleTopology.continuous_of_linearMap (chartCoord e hx).toLinearMap)
    (IsModuleTopology.continuous_of_linearMap (chartCoord e hx).symm.toLinearMap)).isInducing

open scoped Classical in
/-- **The pretrivialization of `det E` induced by a linear trivialization `e` of `E`.** Over the
base set of `e`, it reads the determinant line in the chart coordinate
`TauCeti.DetBundle.chartCoord e`. -/
def pretrivialization (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    Pretrivialization 𝕜 (π 𝕜 (DetBundle 𝕜 F E)) where
  toFun p := ⟨p.proj, if h : p.proj ∈ e.baseSet then chartCoord e h p.snd else 0⟩
  invFun p := ⟨p.1, if h : p.1 ∈ e.baseSet then (chartCoord e h).symm p.2 else 0⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by
    rintro ⟨x, v⟩ (h : x ∈ e.baseSet)
    simp only [dite_eq_left h, LinearEquiv.symm_apply_apply]
  right_inv' := by
    rintro ⟨x, c⟩ ⟨h : x ∈ e.baseSet, -⟩
    simp only [dite_eq_left h, LinearEquiv.apply_symm_apply]
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := (rfl)
  target_eq := (rfl)
  proj_toFun _ _ := (rfl)

@[simp]
theorem pretrivialization_baseSet (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    (pretrivialization (𝕜 := 𝕜) e).baseSet = e.baseSet := (rfl)

open scoped Classical in
private theorem pretrivialization_apply (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    pretrivialization e p =
      (p.proj, if h : p.proj ∈ e.baseSet then chartCoord e h p.snd else 0) := (rfl)

/-- Over its base set, the induced pretrivialization reads the determinant line in the chart
coordinate. -/
theorem pretrivialization_apply_mk (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (h : x ∈ e.baseSet) (v : DetBundle 𝕜 F E x) :
    pretrivialization e ⟨x, v⟩ = (x, chartCoord e h v) := by
  rw [pretrivialization_apply, dite_eq_left h]

/-- Over its base set, the inverse of the induced pretrivialization is the inverse chart
coordinate. -/
theorem pretrivialization_symm_apply (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (h : x ∈ e.baseSet) (c : 𝕜) :
    (pretrivialization e).symm x c = (chartCoord e h).symm c := by
  have key := (pretrivialization (𝕜 := 𝕜) (F := F) (E := E) e).apply_mk_symm h c
  rw [pretrivialization_apply_mk e h, Prod.mk.injEq] at key
  apply (chartCoord e h).injective
  rw [LinearEquiv.apply_symm_apply]
  exact key.2

instance (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    (pretrivialization (𝕜 := 𝕜) e).IsLinear 𝕜 where
  linear x h := by
    simp only [pretrivialization_apply_mk e h]
    exact (chartCoord e h).toLinearMap.isLinear

end Chart

section Bundle

variable [TopologicalSpace B] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F] [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The transition between two induced pretrivializations is multiplication by the determinant of
the coordinate change of `E`, a continuous function on the overlap of their base sets. -/
private theorem exists_continuousOn_coordChange (e e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ∃ g : B → 𝕜 →L[𝕜] 𝕜,
      ContinuousOn g ((pretrivialization (𝕜 := 𝕜) e).baseSet ∩
        (pretrivialization (𝕜 := 𝕜) e').baseSet) ∧
      ∀ x ∈ (pretrivialization (𝕜 := 𝕜) e).baseSet ∩ (pretrivialization (𝕜 := 𝕜) e').baseSet,
        ∀ c : 𝕜, g x c = (pretrivialization e' ⟨x, (pretrivialization e).symm x c⟩).2 := by
  refine ⟨fun x ↦ (e.coordChangeL 𝕜 e' x : F →L[𝕜] F).det • ContinuousLinearMap.id 𝕜 𝕜,
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_coordChange 𝕜 e e')).smul continuousOn_const, fun x hx c ↦ ?_⟩
  obtain ⟨hx, hx'⟩ : x ∈ e.baseSet ∧ x ∈ e'.baseSet := hx
  rw [pretrivialization_symm_apply e hx, pretrivialization_apply_mk e' hx',
    chartCoord_chartCoord_symm]
  rfl

variable (𝕜 F E) in
/-- **The determinant line as a vector prebundle.** Its atlas consists of the pretrivializations
`TauCeti.DetBundle.pretrivialization e` induced by the trivializations `e` in the atlas of `E`;
their transitions are the determinants of those of `E`. -/
def vectorPrebundle : VectorPrebundle 𝕜 𝕜 (DetBundle 𝕜 F E) where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = pretrivialization e}
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  pretrivializationAt x := pretrivialization (trivializationAt F E x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F E x
  pretrivialization_mem_atlas x := ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    exact exists_continuousOn_coordChange e e'
  totalSpaceMk_isInducing x := by
    have h := (isInducing_const_prod (x := x)).mpr (isInducing_chartCoord (𝕜 := 𝕜)
      (trivializationAt F E x) (mem_baseSet_trivializationAt F E x))
    convert h using 1
    ext v : 1
    exact pretrivialization_apply_mk _ _ v

/-- The topology of the determinant line bundle, for which the trivializations induced from those
of `E` are local trivializations. -/
instance topologicalSpaceTotalSpace : TopologicalSpace (TotalSpace 𝕜 (DetBundle 𝕜 F E)) :=
  (vectorPrebundle 𝕜 F E).totalSpaceTopology

/-- The determinant lines of the fibres of `E` form a fibre bundle. -/
instance fiberBundle : FiberBundle 𝕜 (DetBundle 𝕜 F E) :=
  (vectorPrebundle 𝕜 F E).toFiberBundle

/-- **The determinant line bundle.** The determinant lines of the fibres of a vector bundle with
finite-dimensional model fibre form a vector bundle of rank one. -/
instance vectorBundle : VectorBundle 𝕜 𝕜 (DetBundle 𝕜 F E) :=
  (vectorPrebundle 𝕜 F E).toVectorBundle

/-- The trivialization of the determinant line induced by a trivialization `e` in the atlas of
`E`. -/
def trivialization (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    Trivialization 𝕜 (π 𝕜 (DetBundle 𝕜 F E)) :=
  (vectorPrebundle 𝕜 F E).trivializationOfMemPretrivializationAtlas (e := pretrivialization e)
    ⟨e, inferInstance, rfl⟩

instance (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    MemTrivializationAtlas (trivialization (𝕜 := 𝕜) e) :=
  ⟨⟨_, ⟨e, inferInstance, rfl⟩, rfl⟩⟩

@[simp]
theorem trivialization_baseSet (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    (trivialization (𝕜 := 𝕜) e).baseSet = e.baseSet := (rfl)

/-- The trivialization of the determinant line induced by `e` is the induced pretrivialization. -/
@[simp]
theorem trivialization_toPretrivialization (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] :
    (trivialization (𝕜 := 𝕜) e).toPretrivialization = pretrivialization e := (rfl)

/-- The preferred trivialization of the determinant line at `x` is induced by the preferred
trivialization of `E` at `x`. -/
theorem trivializationAt_eq (x : B) :
    trivializationAt 𝕜 (DetBundle 𝕜 F E) x = trivialization (trivializationAt F E x) := (rfl)

/-- Over its base set, the induced trivialization reads the determinant line in the chart
coordinate. -/
theorem trivialization_apply_mk (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (h : x ∈ e.baseSet) (v : DetBundle 𝕜 F E x) :
    trivialization e ⟨x, v⟩ = (x, chartCoord e h v) :=
  pretrivialization_apply_mk e h v

/-- Over its base set, the inverse of the induced trivialization is the inverse chart
coordinate. -/
theorem trivialization_symm_apply (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (h : x ∈ e.baseSet) (c : 𝕜) :
    (trivialization e).symm x c = (chartCoord e h).symm c :=
  pretrivialization_symm_apply e h c

omit [CompleteSpace 𝕜] in
variable (𝕜 F E) in
/-- The fibres of the determinant line are lines. -/
@[simp]
theorem finrank_eq_one (x : B) : finrank 𝕜 (DetBundle 𝕜 F E x) = 1 :=
  (chartCoord (trivializationAt F E x) (mem_baseSet_trivializationAt F E x)).finrank_eq.trans
    (finrank_self 𝕜)

/-- **The coordinate changes of the determinant line are the determinants of the coordinate
changes of `E`.** -/
theorem coordChangeL_trivialization (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] (hx : x ∈ e.baseSet ∩ e'.baseSet) (c : 𝕜) :
    (trivialization e).coordChangeL 𝕜 (trivialization e') x c =
      (e.coordChangeL 𝕜 e' x : F →L[𝕜] F).det * c := by
  rw [Trivialization.coordChangeL_apply (trivialization e) (trivialization e') hx,
    trivialization_symm_apply e hx.1,
    trivialization_apply_mk e' hx.2, chartCoord_chartCoord_symm]

end Bundle

/-! ### Functoriality in bundle isomorphisms -/

section CongrFiber

variable [∀ x, TopologicalSpace (E x)]
  {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module 𝕜 (E' x)]
  [∀ x, TopologicalSpace (E' x)]
  {E'' : B → Type*} [∀ x, AddCommGroup (E'' x)] [∀ x, Module 𝕜 (E'' x)]
  [∀ x, TopologicalSpace (E'' x)]

/-- The isomorphism of determinant lines over `x` induced by a family of linear isomorphisms
`e x : E x ≃ E' x` between bundles with the same model fibre: it sends `v₁ ∧ ⋯ ∧ vᵣ` to
`e v₁ ∧ ⋯ ∧ e vᵣ` (`LinearEquiv.exteriorPower`). -/
def congrEquiv (e : ∀ x, E x ≃L[𝕜] E' x) (x : B) :
    DetBundle 𝕜 F E x ≃L[𝕜] DetBundle 𝕜 F E' x :=
  (linearEquiv 𝕜 F E x ≪≫ₗ (e x).toLinearEquiv.exteriorPower (finrank 𝕜 F) ≪≫ₗ
    (linearEquiv 𝕜 F E' x).symm).toContinuousLinearEquivOfIsModuleTopology

/-- On the exterior power of the fibre, `TauCeti.DetBundle.congrEquiv` is
`LinearEquiv.exteriorPower`. -/
theorem congrEquiv_apply (e : ∀ x, E x ≃L[𝕜] E' x) (x : B) (v : DetBundle 𝕜 F E x) :
    congrEquiv e x v = (linearEquiv 𝕜 F E' x).symm
      ((e x).toLinearEquiv.exteriorPower (finrank 𝕜 F) (linearEquiv 𝕜 F E x v)) := by
  simp only [congrEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.trans_apply]

/-- The identity of a bundle induces the identity of its determinant line. -/
@[simp]
theorem congrEquiv_refl (x : B) :
    congrEquiv (F := F) (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (E x)) x =
      ContinuousLinearEquiv.refl 𝕜 _ := by
  ext v
  simp only [congrEquiv_apply, ContinuousLinearEquiv.refl, LinearEquiv.exteriorPower_refl]
  -- Both fibre identifications are identity equivalences on the exposed exterior-power alias.
  dsimp only [linearEquiv]
  exact LinearEquiv.symm_apply_apply _ v

/-- The isomorphisms of determinant lines induced by bundle isomorphisms compose. -/
theorem congrEquiv_trans (e : ∀ x, E x ≃L[𝕜] E' x) (e' : ∀ x, E' x ≃L[𝕜] E'' x) (x : B) :
    congrEquiv (F := F) (fun x ↦ (e x).trans (e' x)) x =
      (congrEquiv (F := F) e x).trans (congrEquiv e' x) := by
  ext v
  rw [ContinuousLinearEquiv.trans_apply, congrEquiv_apply, congrEquiv_apply, congrEquiv_apply,
    ContinuousLinearEquiv.trans_toLinearEquiv, LinearEquiv.exteriorPower_trans]
  rw [LinearEquiv.trans_apply, linearEquiv_apply, linearEquiv_symm_apply]
  rw [linearEquiv_symm_apply, LinearEquiv.apply_symm_apply]

/-- The inverse of the isomorphism of determinant lines induced by `e` is induced by the inverse
of `e`. -/
theorem congrEquiv_symm (e : ∀ x, E x ≃L[𝕜] E' x) (x : B) :
    (congrEquiv (F := F) e x).symm = congrEquiv (fun x ↦ (e x).symm) x := by
  ext v
  rw [ContinuousLinearEquiv.symm_apply_eq, congrEquiv_apply, congrEquiv_apply,
    ContinuousLinearEquiv.toLinearEquiv_symm,
    ← LinearEquiv.exteriorPower_symm]
  exact (LinearEquiv.apply_symm_apply ((e x).toLinearEquiv.exteriorPower (finrank 𝕜 F)) v).symm

end CongrFiber

section Congr

variable [TopologicalSpace B] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F] [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module 𝕜 (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F E')] [FiberBundle F E']
  [VectorBundle 𝕜 F E']

/-- Read in chart coordinates, the isomorphism of determinant lines induced by `e` is
multiplication by the determinant of the coordinate expression of `e`, which depends
continuously on the base point. -/
private theorem continuousAt_chartCoord_congrEquiv (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.snd)))
    (a : B) :
    ∃ s : B → 𝕜, ContinuousAt s a ∧ ∀ x (hx : x ∈ (trivializationAt F E a).baseSet)
      (hx' : x ∈ (trivializationAt F E' a).baseSet) (c : 𝕜),
      chartCoord (trivializationAt F E' a) hx'
        (congrEquiv e x ((chartCoord (trivializationAt F E a) hx).symm c)) = s x * c := by
  set t := trivializationAt F E a
  set t' := trivializationAt F E' a
  -- The coordinate expression of `e` is a continuous family of endomorphisms of `F`.
  let T : B → F →L[𝕜] F := fun x ↦ (t'.continuousLinearMapAt 𝕜 x).comp
    (((e x : E x →L[𝕜] E' x)).comp (t.symmL 𝕜 x))
  have hT : ContinuousOn T (t.baseSet ∩ t'.baseSet) :=
    continuousOn_continuousLinearMapAt_comp_symmL (g := id)
      (φ := fun x ↦ (e x : E x →L[𝕜] E' x)) he t' t
  refine ⟨fun x ↦ (T x).det, ContinuousLinearMap.continuous_det.continuousAt.comp
    (hT.continuousAt ((t.open_baseSet.inter t'.open_baseSet).mem_nhds
      ⟨mem_baseSet_trivializationAt F E a, mem_baseSet_trivializationAt F E' a⟩)),
    fun x hx hx' c ↦ ?_⟩
  have hdet : LinearMap.det (((t.linearEquivAt 𝕜 x hx).symm ≪≫ₗ (e x).toLinearEquiv ≪≫ₗ
      t'.linearEquivAt 𝕜 x hx' : F ≃ₗ[𝕜] F) : F →ₗ[𝕜] F) = (T x).det := by
    congr 1
    ext v
    simp [T, Trivialization.symmL_apply t hx, Trivialization.coe_linearMapAt_of_mem t' hx']
  -- Collect the exterior-power isomorphisms into the one induced by the coordinate expression.
  have key : chartCoord t' hx' (congrEquiv e x ((chartCoord t hx).symm c)) =
      modelCoord F (((t.linearEquivAt 𝕜 x hx).symm ≪≫ₗ (e x).toLinearEquiv ≪≫ₗ
        t'.linearEquivAt 𝕜 x hx').exteriorPower (finrank 𝕜 F) ((modelCoord F).symm c)) := by
    rw [chartCoord_def, chartCoord_def, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, congrEquiv_apply]
    simp only [LinearEquiv.trans_apply, LinearEquiv.exteriorPower_trans,
      LinearEquiv.exteriorPower_symm]
    rw [linearEquiv_apply, linearEquiv_apply, linearEquiv_symm_apply, linearEquiv_symm_apply]
  rw [key, ← LinearEquiv.coe_toLinearMap
      (((t.linearEquivAt 𝕜 x hx).symm ≪≫ₗ (e x).toLinearEquiv ≪≫ₗ
        t'.linearEquivAt 𝕜 x hx').exteriorPower (finrank 𝕜 F)),
    LinearEquiv.exteriorPower_toLinearMap, Module.Basis.exteriorPowerTopEquiv_map, hdet,
    LinearEquiv.apply_symm_apply]

/-- **Functoriality of the determinant line in bundle isomorphisms.** A continuous fibrewise
linear isomorphism `e` between vector bundles with the same finite-dimensional model fibre `F`
induces a
homeomorphism of the total spaces of their determinant lines, which is
`TauCeti.DetBundle.congrEquiv e` on each fibre. -/
def congrHomeomorph (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.snd))) :
    TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace 𝕜 (DetBundle 𝕜 F E') :=
  bundleHomeomorph (congrEquiv e) <| by
    refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦ ?_
    obtain ⟨s, hs, hs'⟩ := continuousAt_chartCoord_congrEquiv e he p.proj
    refine ⟨trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj,
      trivializationAt 𝕜 (DetBundle 𝕜 F E') p.proj, fun x c ↦ s x * c,
      mem_baseSet_trivializationAt 𝕜 _ p.proj, mem_baseSet_trivializationAt 𝕜 _ p.proj,
      (hs.comp (FiberBundle.continuous_proj 𝕜 _).continuousAt).mul
        ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).continuousOn.continuousAt
          ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).open_source.mem_nhds
            (FiberBundle.mem_trivializationAt_proj_source))).snd, ?_⟩
    rintro ⟨x, v⟩ (hx : x ∈ (trivializationAt F E p.proj).baseSet)
      (hx' : x ∈ (trivializationAt F E' p.proj).baseSet)
    simp only [trivializationAt_eq]
    rw [trivialization_apply_mk _ hx', trivialization_apply_mk _ hx,
      ← hs' x hx hx' (chartCoord _ hx v), LinearEquiv.symm_apply_apply]

@[simp]
theorem congrHomeomorph_apply (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.snd)))
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    congrHomeomorph e he p = ⟨p.proj, congrEquiv e p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem congrHomeomorph_symm_apply (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.snd)))
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F E')) :
    (congrHomeomorph e he).symm p = ⟨p.proj, (congrEquiv e p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Congr

/-! ### Pullback -/

section Pullback

variable {B' : Type*}

/-- The fibre of `f *ᵖ E` over `y` is the fibre of `E` over `f y`. -/
private def pullbackFiberEquiv (f : B' → B) (y : B') : E (f y) ≃ₗ[𝕜] ((f *ᵖ E) y) :=
  LinearEquiv.refl 𝕜 _

/-- The isomorphism of determinant lines induced by the identity of the fibre of `E` over `f y`,
from the fibre of the pullback of `det E` over `y` to the fibre of `det (f *ᵖ E)` over `y`. -/
def pullbackEquiv (f : B' → B) (y : B') :
    (f *ᵖ (DetBundle 𝕜 F E)) y ≃L[𝕜] DetBundle 𝕜 F (f *ᵖ E) y :=
  (ContinuousLinearEquiv.refl 𝕜 (DetBundle 𝕜 F E (f y))).trans
    (linearEquiv 𝕜 F E (f y) ≪≫ₗ
      (pullbackFiberEquiv (𝕜 := 𝕜) (E := E) f y).exteriorPower (finrank 𝕜 F) ≪≫ₗ
        (linearEquiv 𝕜 F (f *ᵖ E) y).symm).toContinuousLinearEquivOfIsModuleTopology

private theorem linearEquiv_pullbackEquiv (f : B' → B) (y : B')
    (v : (f *ᵖ (DetBundle 𝕜 F E)) y) :
    linearEquiv 𝕜 F (f *ᵖ E) y (pullbackEquiv f y v) =
      (pullbackFiberEquiv (𝕜 := 𝕜) (E := E) f y).exteriorPower (finrank 𝕜 F)
        (linearEquiv 𝕜 F E (f y) v) :=
  congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (linearEquiv 𝕜 F E (f y) ≪≫ₗ
      (pullbackFiberEquiv (𝕜 := 𝕜) (E := E) f y).exteriorPower (finrank 𝕜 F) ≪≫ₗ
        (linearEquiv 𝕜 F (f *ᵖ E) y).symm)) v

/-- Canonical determinant pullback preserves the intrinsic exterior-algebra image of a fibre. -/
theorem coe_linearEquiv_pullbackEquiv (f : B' → B) (y : B')
    (v : (f *ᵖ (DetBundle 𝕜 F E)) y) :
    (linearEquiv 𝕜 F (f *ᵖ E) y (pullbackEquiv (𝕜 := 𝕜) (F := F) (E := E) f y v) :
      ExteriorAlgebra 𝕜 ((f *ᵖ E) y)) =
      (linearEquiv 𝕜 F E (f y) v : ExteriorAlgebra 𝕜 (E (f y))) := by
  rw [linearEquiv_pullbackEquiv]
  -- `pullbackFiberEquiv f y` is the identity of `E (f y)`, with target written as the pullback
  -- fibre `(f *ᵖ E) y`. Rewriting its exterior power to the identity therefore needs `erw` to see
  -- through that alias, and the two sides then agree by definition.
  dsimp only [pullbackFiberEquiv]
  erw [LinearEquiv.exteriorPower_refl (R := 𝕜) (M := E (f y)) (finrank 𝕜 F)]
  rfl

/-- Canonical determinant pullback sends an exterior generator of the fibre of `det E` over
`f y` to the same exterior generator of the fibre of `det (f *ᵖ E)` over `y`. -/
theorem pullbackEquiv_ιMulti (f : B' → B) (y : B') (a : Fin (finrank 𝕜 F) → E (f y)) :
    pullbackEquiv (𝕜 := 𝕜) (F := F) (E := E) f y
        ((linearEquiv 𝕜 F E (f y)).symm (exteriorPower.ιMulti 𝕜 _ a)) =
      (linearEquiv 𝕜 F (f *ᵖ E) y).symm (exteriorPower.ιMulti 𝕜 _ a) := by
  apply (linearEquiv 𝕜 F (f *ᵖ E) y).injective
  apply Subtype.ext
  -- Both exterior generators are the same element of the exterior algebra of `E (f y)`.
  exact (coe_linearEquiv_pullbackEquiv f y _).trans rfl

variable [TopologicalSpace B] [FiniteDimensional 𝕜 F]
  [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B'] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- The chart coordinate of a pulled-back trivialization reads the fibre of `det (f *ᵖ E)` as the
chart coordinate of the original trivialization reads the fibre of `det E` at the image point. -/
theorem chartCoord_pullbackEquiv (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (f : K) {y : B'}
    (hy : y ∈ (e.pullback f).baseSet) (v : ((f : B' → B) *ᵖ (DetBundle 𝕜 F E)) y) :
    chartCoord (e.pullback f) hy (pullbackEquiv (f : B' → B) y v) =
      chartCoord (x := f y) e (by simpa only [Trivialization.pullback_baseSet, mem_preimage]
        using hy) v := by
  have h : pullbackFiberEquiv (𝕜 := 𝕜) (E := E) (f : B' → B) y ≪≫ₗ
      (e.pullback f).linearEquivAt 𝕜 y hy =
      e.linearEquivAt 𝕜 (f y) (by simpa only [Trivialization.pullback_baseSet, mem_preimage]
        using hy) := by
    rw [Trivialization.linearEquivAt_pullback]
    -- Pullback fibres are aliases; their algebraic identification is the identity.
    dsimp only [pullbackFiberEquiv]
    exact LinearEquiv.refl_trans _
  calc chartCoord (e.pullback f) hy (pullbackEquiv (f : B' → B) y v)
      = modelCoord F (((e.pullback f).linearEquivAt 𝕜 y hy).exteriorPower (finrank 𝕜 F)
          (linearEquiv 𝕜 F ((f : B' → B) *ᵖ E) y (pullbackEquiv (f : B' → B) y v))) := by
        rw [chartCoord_apply]
    _ = modelCoord F (((e.pullback f).linearEquivAt 𝕜 y hy).exteriorPower (finrank 𝕜 F)
          ((pullbackFiberEquiv (𝕜 := 𝕜) (E := E) (f : B' → B) y).exteriorPower (finrank 𝕜 F)
            (linearEquiv 𝕜 F E (f y) v))) := by rw [linearEquiv_pullbackEquiv]
    _ = modelCoord F ((pullbackFiberEquiv (𝕜 := 𝕜) (E := E) (f : B' → B) y ≪≫ₗ
          (e.pullback f).linearEquivAt 𝕜 y hy).exteriorPower (finrank 𝕜 F)
            (linearEquiv 𝕜 F E (f y) v)) := by
      rw [LinearEquiv.exteriorPower_trans, LinearEquiv.trans_apply]
    _ = _ := by
      -- The source value has the pulled-back fibre alias, so rewriting needs its representation.
      erw [h, chartCoord_apply]

variable [CompleteSpace 𝕜] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (f : K)

/-- **Pullback of the determinant line.** For a continuous map `f : B' → B`, the pullback of the
determinant line of `E` is the determinant line of the pullback `f *ᵖ E`: their total spaces are
homeomorphic by `TauCeti.DetBundle.pullbackEquiv` on each fibre, the map of determinant lines
induced by the identity of the fibres of `E`. -/
def pullbackHomeomorph :
    TotalSpace 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E)) ≃ₜ
      TotalSpace 𝕜 (DetBundle 𝕜 F ((f : B' → B) *ᵖ E)) :=
  bundleHomeomorph (pullbackEquiv (f : B' → B)) <| by
    refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦ ?_
    refine ⟨trivializationAt 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E)) p.proj,
      trivializationAt 𝕜 (DetBundle 𝕜 F ((f : B' → B) *ᵖ E)) p.proj, fun _ c ↦ c,
      mem_baseSet_trivializationAt 𝕜 _ p.proj, mem_baseSet_trivializationAt 𝕜 _ p.proj,
      ((trivializationAt 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E)) p.proj).continuousOn.continuousAt
        ((trivializationAt 𝕜 _ p.proj).open_source.mem_nhds
          (FiberBundle.mem_trivializationAt_proj_source))).snd, ?_⟩
    rintro ⟨y, v⟩ (hy : f y ∈ (trivializationAt F E (f p.proj)).baseSet)
      (hy' : y ∈ (trivializationAt F ((f : B' → B) *ᵖ E) p.proj).baseSet)
    simp only [trivializationAt_eq]
    rw [trivialization_apply_mk _ hy']
    exact (chartCoord_pullbackEquiv _ f hy' v).trans
      (congrArg Prod.snd (trivialization_apply_mk _ hy v)).symm

@[simp]
theorem pullbackHomeomorph_apply (p : TotalSpace 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E))) :
    pullbackHomeomorph f p = ⟨p.proj, pullbackEquiv (f : B' → B) p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem pullbackHomeomorph_symm_apply
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F ((f : B' → B) *ᵖ E))) :
    (pullbackHomeomorph f).symm p = ⟨p.proj, (pullbackEquiv (f : B' → B) p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Pullback

/-! ### The determinant line of a line bundle -/

section Line

/-- Over a line, the top exterior power of a fibre is its first exterior power, which is the fibre
itself (`exteriorPower.oneEquiv`). -/
private def lineLinearEquiv (hF : finrank 𝕜 F = 1) (x : B) : DetBundle 𝕜 F E x ≃ₗ[𝕜] E x :=
  linearEquiv 𝕜 F E x ≪≫ₗ LinearEquiv.ofEq _ _ (by rw [hF]) ≪≫ₗ exteriorPower.oneEquiv 𝕜 (E x)

variable [TopologicalSpace B] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle 𝕜 F E]

/-- **The determinant line of a line is the line itself.** For a vector bundle `L` whose model
fibre is a line, the fibre `⋀¹ L_x` of `det L` over `x` is `L_x`, by `exteriorPower.oneEquiv`. -/
def lineEquiv (hF : finrank 𝕜 F = 1) (x : B) : DetBundle 𝕜 F E x ≃L[𝕜] E x :=
  let e := (trivializationAt F E x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F E x)
  -- Both directions are continuous, being read through the chart `e` of the fibre.
  { lineLinearEquiv hF x with
    continuous_toFun := (e.symm.continuous.comp (IsModuleTopology.continuous_of_linearMap
      ((lineLinearEquiv hF x).trans e.toLinearEquiv).toLinearMap)).congr
        fun _ ↦ e.symm_apply_apply _
    continuous_invFun := ((LinearMap.continuous_of_finiteDimensional
      (e.symm.toLinearEquiv.trans (lineLinearEquiv hF x).symm).toLinearMap).comp
        e.continuous).congr fun v ↦ congrArg (lineLinearEquiv hF x).symm (e.symm_apply_apply v) }

/-- The inverse of `TauCeti.DetBundle.lineEquiv` sends `v` to `v`, read in `⋀¹ L_x`. -/
@[simp]
theorem lineEquiv_symm_apply (hF : finrank 𝕜 F = 1) (v : E x) :
    (lineEquiv hF x).symm v = (linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ fun _ ↦ v) := by
  -- In degree `n = 1`, the wedge of the single vector `v` is `v` in `⋀¹ (E x) = E x`.
  have key {n : ℕ} (hn : n = 1) (h : ⋀[𝕜]^n (E x) = ⋀[𝕜]^1 (E x)) :
      exteriorPower.oneEquiv 𝕜 (E x)
        (LinearEquiv.ofEq _ _ h (exteriorPower.ιMulti 𝕜 n fun _ ↦ v)) = v := by
    subst hn
    simp only [LinearEquiv.ofEq_rfl, LinearEquiv.refl_apply, exteriorPower.oneEquiv_ιMulti]
  -- The inverse of `lineEquiv` is, by definition, that of the linear equivalence it bundles.
  change (lineLinearEquiv hF x).symm v = _
  apply (lineLinearEquiv hF x).injective
  simp only [LinearEquiv.apply_symm_apply, lineLinearEquiv, LinearEquiv.trans_apply, key hF]

/-- `TauCeti.DetBundle.lineEquiv` sends the wedge of a family `v` with a single member to that
member `v i`. -/
theorem lineEquiv_ιMulti (hF : finrank 𝕜 F = 1) (v : Fin (finrank 𝕜 F) → E x)
    (i : Fin (finrank 𝕜 F)) :
    lineEquiv hF x ((linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ v)) = v i := by
  have : Subsingleton (Fin (finrank 𝕜 F)) := (finCongr hF).subsingleton
  have hv : v = fun _ ↦ v i := funext fun _ ↦ congrArg v (Subsingleton.elim _ _)
  conv_lhs => rw [hv, ← lineEquiv_symm_apply hF, ContinuousLinearEquiv.apply_symm_apply]

/-- In a linear trivialization `e` of a line bundle, the isomorphism `det L ≃ L` sends a vector
with chart coordinate `c` in `det L` to the vector with coordinate `c • b` in `L`, where `b` is the
single vector of the basis `Module.finBasis 𝕜 F` of the model fibre. -/
theorem snd_apply_lineEquiv (hF : finrank 𝕜 F = 1) (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) (v : DetBundle 𝕜 F E x) (i : Fin (finrank 𝕜 F)) :
    (e ⟨x, lineEquiv hF x v⟩).2 = chartCoord e hx v • Module.finBasis 𝕜 F i := by
  have : Unique (Fin (finrank 𝕜 F)) := (finCongr hF).unique
  obtain rfl : i = default := Subsingleton.elim _ _
  obtain ⟨w, rfl⟩ := (lineEquiv hF x).symm.surjective v
  rw [ContinuousLinearEquiv.apply_symm_apply, lineEquiv_symm_apply, chartCoord_ιMulti]
  exact ((Module.finBasis 𝕜 F).det_unique_smul fun _ ↦ (e ⟨x, w⟩).2).symm

/-- The isomorphism `det L ≃ L` is continuous on total spaces. -/
theorem continuous_lineEquiv (hF : finrank 𝕜 F = 1) :
    Continuous fun p : TotalSpace 𝕜 (DetBundle 𝕜 F E) ↦
      TotalSpace.mk' F p.proj (lineEquiv hF p.proj p.snd) := by
  have : Unique (Fin (finrank 𝕜 F)) := (finCongr hF).unique
  refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦ ?_
  refine ⟨trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj, trivializationAt F E p.proj,
    fun _ c ↦ c • Module.finBasis 𝕜 F default,
    mem_baseSet_trivializationAt 𝕜 _ p.proj, mem_baseSet_trivializationAt F E p.proj,
    ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).continuousOn.continuousAt
      ((trivializationAt 𝕜 _ p.proj).open_source.mem_nhds
        (FiberBundle.mem_trivializationAt_proj_source))).snd.smul continuousAt_const, ?_⟩
  rintro ⟨y, v⟩ (hy : y ∈ (trivializationAt F E p.proj).baseSet) -
  rw [snd_apply_lineEquiv hF _ hy _ default, trivializationAt_eq,
    trivialization_apply_mk _ hy]

/-- **The determinant line bundle of a line bundle is the line bundle itself**: the total spaces
of `det L` and `L` are homeomorphic by `TauCeti.DetBundle.lineEquiv` on each fibre. -/
def lineHomeomorph (hF : finrank 𝕜 F = 1) : TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace F E :=
  bundleHomeomorph (lineEquiv hF) (continuous_lineEquiv hF)

@[simp]
theorem lineHomeomorph_apply (hF : finrank 𝕜 F = 1) (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    lineHomeomorph hF p = ⟨p.proj, lineEquiv hF p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem lineHomeomorph_symm_apply (hF : finrank 𝕜 F = 1) (p : TotalSpace F E) :
    (lineHomeomorph hF).symm p = ⟨p.proj, (lineEquiv hF p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Line

/-! ### Wedges of sections -/

section Wedge

variable [TopologicalSpace B] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle 𝕜 F E]

/-- **The wedge of continuous sections is a continuous section of the determinant line.** For
continuous sections `s₁, …, sᵣ` of `E`, `r = finrank 𝕜 F`, the section `x ↦ s₁(x) ∧ ⋯ ∧ sᵣ(x)` of
`det E` is continuous. -/
theorem continuous_ιMulti {s : Fin (finrank 𝕜 F) → ∀ x, E x}
    (hs : ∀ i, Continuous fun x ↦ TotalSpace.mk' F x (s i x)) :
    Continuous fun x ↦ TotalSpace.mk' 𝕜 x
      ((linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ fun i ↦ s i x)) := by
  refine continuous_iff_continuousAt.2 fun a ↦ (FiberBundle.continuousAt_section 𝕜 a).2 ?_
  set t := trivializationAt F E a
  -- Near `a`, the chart coordinate of the wedge is the determinant of the coordinates of the `sᵢ`.
  have hev : (fun x ↦ (trivializationAt 𝕜 (DetBundle 𝕜 F E) a
      ⟨x, (linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ fun i ↦ s i x)⟩).2) =ᶠ[𝓝 a]
      fun x ↦ (Module.finBasis 𝕜 F).det fun i ↦ (t ⟨x, s i x⟩).2 := by
    filter_upwards [t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E a)] with x hx
    rw [trivializationAt_eq, trivialization_apply_mk _ hx, chartCoord_ιMulti]
  refine ContinuousAt.congr ?_ hev.symm
  have hcoord : ContinuousAt (fun x ↦ fun i ↦ (t ⟨x, s i x⟩).2) a :=
    continuousAt_pi.2 fun i ↦ ((t.continuousOn.continuousAt (t.open_source.mem_nhds
      ((t.mem_source).2 (mem_baseSet_trivializationAt F E a)))).comp
        (hs i).continuousAt).snd
  simpa only [Function.comp_def, Module.Basis.continuousDet_apply] using
    (Module.finBasis 𝕜 F).continuousDet.coe_continuous.continuousAt.comp hcoord

end Wedge

/-! ### Comparison with the determinant of finite-rank cores -/

section FiniteRank

variable [TopologicalSpace B] [CompleteSpace 𝕜] {n : ℕ} [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
  [VectorBundle 𝕜 (Fin n → 𝕜) E]

omit [CompleteSpace 𝕜] in
/-- The single coordinate of the model fibre of the determinant line of a finite-rank core, which
has rank one. -/
private def detCoord (A : FiniteRankBundleCore 𝕜 B) : (Fin A.det.rank → 𝕜) ≃L[𝕜] 𝕜 :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr A.rank_det)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)

omit [CompleteSpace 𝕜] in
variable (E) in
/-- The fibre of the reconstructed determinant core of `FiniteRankBundleCore.ofBundle 𝕜 n E` over
`x` is identified with the fibre of `det E` through the preferred chart coordinate at `x`. -/
def ofBundleDetFiberEquiv (x : B) :
    (FiniteRankBundleCore.ofBundle 𝕜 n E).det.core.Fiber x ≃L[𝕜] DetBundle 𝕜 (Fin n → 𝕜) E x :=
  (detCoord (FiniteRankBundleCore.ofBundle 𝕜 n E)).trans
    (chartCoord (trivializationAt (Fin n → 𝕜) E x)
      (mem_baseSet_trivializationAt (Fin n → 𝕜) E x)).symm.toContinuousLinearEquivOfIsModuleTopology

omit [CompleteSpace 𝕜] in
private theorem ofBundleDetFiberEquiv_apply (x : B)
    (v : (FiniteRankBundleCore.ofBundle 𝕜 n E).det.core.Fiber x) :
    ofBundleDetFiberEquiv (𝕜 := 𝕜) (n := n) E x v = (chartCoord (trivializationAt (Fin n → 𝕜) E x)
      (mem_baseSet_trivializationAt (Fin n → 𝕜) E x)).symm
        (detCoord (FiniteRankBundleCore.ofBundle 𝕜 n E) v) := by
  -- The core fibre is an opaque alias for its model space; `trans_apply` cannot synthesize its
  -- module instance before this conversion unfolds the continuous-linear composition.
  change (chartCoord (trivializationAt (Fin n → 𝕜) E x)
    (mem_baseSet_trivializationAt (Fin n → 𝕜) E x)).symm.toContinuousLinearEquivOfIsModuleTopology
      (detCoord (FiniteRankBundleCore.ofBundle 𝕜 n E) v) = _
  rw [LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

variable (E) in
/-- **Comparison with the determinant of finite-rank cores.** For a bundle `E` with model fibre
`Fin n → 𝕜`, the reconstruction of the determinant line `FiniteRankBundleCore.det` of its
point-indexed core `FiniteRankBundleCore.ofBundle 𝕜 n E` is homeomorphic to the determinant line
bundle of `E`, by `TauCeti.DetBundle.ofBundleDetFiberEquiv` on each fibre. -/
def ofBundleDetHomeomorph :
    (FiniteRankBundleCore.ofBundle 𝕜 n E).det.core.TotalSpace ≃ₜ
      TotalSpace 𝕜 (DetBundle 𝕜 (Fin n → 𝕜) E) :=
  bundleHomeomorph (ofBundleDetFiberEquiv E) <| by
    set A := FiniteRankBundleCore.ofBundle 𝕜 n E
    refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦ ?_
    refine ⟨A.det.core.localTriv p.proj,
      trivializationAt 𝕜 (DetBundle 𝕜 (Fin n → 𝕜) E) p.proj, fun _ ↦ detCoord A,
      A.det.mem_baseSet_self p.proj, mem_baseSet_trivializationAt 𝕜 _ p.proj,
      (detCoord A).continuous.continuousAt.comp
        ((A.det.core.localTriv p.proj).continuousOn.continuousAt
          ((A.det.core.localTriv p.proj).open_source.mem_nhds
            ((A.det.core.mem_localTriv_source _ _).2 (A.det.mem_baseSet_self p.proj)))).snd, ?_⟩
    rintro ⟨x, v⟩ (_hx : x ∈ A.det.core.baseSet p.proj)
      (hx' : x ∈ (trivializationAt (Fin n → 𝕜) E p.proj).baseSet)
    simp only [trivializationAt_eq]
    have hsmul (c : 𝕜) (w : Fin A.det.rank → 𝕜) :
        detCoord A ((c • ContinuousLinearMap.id 𝕜 _) w) = c * detCoord A w := by
      simp
    -- Reconstructed-core fibres are aliases of the model; expose them for the coordinate formula.
    erw [trivialization_apply_mk _ hx', VectorBundleCore.localTriv_apply, A.det.indexAt_eq,
      FiniteRankBundleCore.coordChange_det_ofBundle, hsmul, ofBundleDetFiberEquiv_apply,
      chartCoord_chartCoord_symm]

@[simp]
theorem ofBundleDetHomeomorph_apply
    (p : (FiniteRankBundleCore.ofBundle 𝕜 n E).det.core.TotalSpace) :
    ofBundleDetHomeomorph (𝕜 := 𝕜) (n := n) E p =
      ⟨p.proj, ofBundleDetFiberEquiv (𝕜 := 𝕜) (n := n) E p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

end FiniteRank

universe u v₁ v₂ w w₁ w₂ v₁' w₁'

section ModelPresentations

variable {K : Type u} {B : Type w}
  [NontriviallyNormedField K] [TopologicalSpace B]
  {F₁ : Type v₁} [NormedAddCommGroup F₁] [NormedSpace K F₁] [FiniteDimensional K F₁]
  {E₁ : B → Type w₁} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]

/-- The determinant fibre identified with the top exterior power indexed by the actual
fibre rank. -/
def fiberDetLineEquiv (x : B) : DetBundle K F₁ E₁ x ≃ₗ[K] detLine K (E₁ x) :=
  (linearEquiv K F₁ E₁ x).trans
    (LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (E₁ x))
      (VectorBundle.finrank_eq K F₁ E₁ x).symm))

omit [FiniteDimensional K F₁] in
/-- The fibre-rank identification preserves the exterior-algebra image. -/
@[simp]
theorem coe_fiberDetLineEquiv (x : B) (a : DetBundle K F₁ E₁ x) :
    (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a : ExteriorAlgebra K (E₁ x)) =
      linearEquiv K F₁ E₁ x a := by
  simp only [fiberDetLineEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]

section ModelCongr

variable {F' : Type v₁'} [NormedAddCommGroup F'] [NormedSpace K F'] [FiniteDimensional K F']
  {E' : B → Type w₁'} [∀ x, AddCommGroup (E' x)] [∀ x, Module K (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [VectorBundle K F' E']

private def modelCongrLinearEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B) :
    DetBundle K F₁ E₁ x ≃ₗ[K] DetBundle K F' E' x := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E' x) := VectorBundle.finiteDimensional K F' E' x
  exact (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x).trans
    ((e x).toLinearEquiv.detLineCongr.trans
      (fiberDetLineEquiv (K := K) (F₁ := F') (E₁ := E') x).symm)

/-- The determinant transport of a fibrewise family of continuous linear equivalences between
independently presented finite-dimensional models. No continuity in the base is assumed. -/
def congrModelEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B) :
    DetBundle K F₁ E₁ x ≃L[K] DetBundle K F' E' x :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (modelCongrLinearEquiv (F₁ := F₁) (F' := F') e x)

/-- The transport between model presentations induces the determinant action on each fibre. -/
theorem fiberDetLineEquiv_congrModelEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B)
    (a : DetBundle K F₁ E₁ x) :
    fiberDetLineEquiv (K := K) (F₁ := F') (E₁ := E') x
      (congrModelEquiv (F₁ := F₁) (F' := F') e x a) =
      (e x).toLinearEquiv.detLineCongr
        (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a) := by
  simp only [congrModelEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
  simp only [modelCongrLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- Independent model presentations do not change the exterior-algebra action of an isomorphism. -/
theorem coe_congrModelEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B) (a : DetBundle K F₁ E₁ x) :
    (linearEquiv K F' E' x (congrModelEquiv (F₁ := F₁) (F' := F') e x a) :
      ExteriorAlgebra K (E' x)) =
      ExteriorAlgebra.map (e x).toLinearMap (linearEquiv K F₁ E₁ x a) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E' x) := VectorBundle.finiteDimensional K F' E' x
  have h := congrArg (fun v : detLine K (E' x) ↦ (v : ExteriorAlgebra K (E' x)))
    (fiberDetLineEquiv_congrModelEquiv (F₁ := F₁) (F' := F') e x a)
  simpa only [coe_fiberDetLineEquiv, LinearEquiv.coe_detLineCongr] using h

end ModelCongr

section SameModel

variable {E₁' : B → Type w₁'} [∀ x, AddCommGroup (E₁' x)] [∀ x, Module K (E₁' x)]
  [∀ x, TopologicalSpace (E₁' x)] [TopologicalSpace (TotalSpace F₁ E₁')]
  [FiberBundle F₁ E₁'] [VectorBundle K F₁ E₁']

/-- For the same model, the presentation-independent transport is the existing native map. -/
@[simp]
theorem congrModelEquiv_eq_congrEquiv (e : ∀ x, E₁ x ≃L[K] E₁' x) (x : B) :
    congrModelEquiv (F₁ := F₁) (F' := F₁) e x = congrEquiv (F := F₁) e x := by
  ext a
  apply (linearEquiv K F₁ E₁' x).injective
  apply Subtype.ext
  rw [coe_congrModelEquiv, congrEquiv_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.coe_exteriorPower_apply]

end SameModel

variable (K F₁ E₁) in
/-- When the model `F₁` has rank zero, each determinant fibre is the degree-zero exterior power
of the fibre, and this is its canonical scalar coordinate (the coefficient of the empty exterior
product). Only the model rank is assumed: without a vector-bundle identification the fibre itself
may have positive dimension. No basis is chosen. -/
def zeroEquiv (h : finrank K F₁ = 0) (x : B) : DetBundle K F₁ E₁ x ≃L[K] K :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    ((linearEquiv K F₁ E₁ x).trans
      ((LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (E₁ x)) h)).trans
        (exteriorPower.zeroEquiv K (E₁ x))))

omit [FiniteDimensional K F₁] [VectorBundle K F₁ E₁]
  [TopologicalSpace B] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] in
/-- When the model `F₁` has rank zero, the image of a determinant vector, a degree-zero exterior
vector, in the fibre exterior algebra is the scalar `zeroEquiv` coordinate times the empty
product `1`. -/
theorem coe_linearEquiv_zeroEquiv (h : finrank K F₁ = 0) (x : B)
    (a : DetBundle K F₁ E₁ x) :
    (linearEquiv K F₁ E₁ x a : ExteriorAlgebra K (E₁ x)) =
      algebraMap K (ExteriorAlgebra K (E₁ x)) (zeroEquiv K F₁ E₁ h x a) := by
  simp only [zeroEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
  have hz := exteriorPower.coe_eq_algebraMap_zeroEquiv
    ((LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (E₁ x)) h)) (linearEquiv K F₁ E₁ x a))
  simpa only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply] using hz

omit [FiniteDimensional K F₁] in
/-- For an actual vector bundle, the model-degree-zero scalar coordinate is the intrinsic
rank-zero determinant coordinate. The weaker definition `zeroEquiv` itself needs no
fibre-rank identification or bundle topology hypotheses. -/
theorem zeroEquiv_eq_detLineEquivOfFinrankEqZero (h : finrank K F₁ = 0) (x : B) :
    zeroEquiv K F₁ E₁ h x =
      ((fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x).trans
        (detLineEquivOfFinrankEqZero
          ((VectorBundle.finrank_eq K F₁ E₁ x).trans h))).toContinuousLinearEquivOfIsModuleTopology
    := by
  let hf := (VectorBundle.finrank_eq K F₁ E₁ x).trans h
  have hm :
      (zeroEquiv K F₁ E₁ h x).toLinearMap.comp (linearEquiv K F₁ E₁ x).symm.toLinearMap =
        ((detLineEquivOfFinrankEqZero hf).toLinearMap.comp
          (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x).toLinearMap).comp
            (linearEquiv K F₁ E₁ x).symm.toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, zeroEquiv,
      LinearEquiv.toLinearEquiv_toContinuousLinearEquivOfIsModuleTopology,
      fiberDetLineEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [exteriorPower.ofEq_ιMulti (R := K) (M := E₁ x) h v,
      exteriorPower.zeroEquiv_ιMulti]
    rw [exteriorPower.ofEq_ιMulti (R := K) (M := E₁ x)
      (VectorBundle.finrank_eq K F₁ E₁ x).symm v, detLineEquivOfFinrankEqZero_ιMulti]
  ext a
  rw [LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology, LinearEquiv.trans_apply]
  simpa only [LinearMap.comp_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun hm (linearEquiv K F₁ E₁ x a)

end ModelPresentations

end DetBundle

end TauCeti
