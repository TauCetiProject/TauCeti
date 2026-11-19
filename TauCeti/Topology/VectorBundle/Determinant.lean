/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback

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

For `𝕜 = ℂ` these are exactly the carriers of `TauCeti.complexEulerClass`, and `det E` is the
complex line bundle whose first Chern class is the first Chern class of `E`.

The construction is natural:

* a continuous fibrewise linear isomorphism `e` between two vector bundles with model fibre `F`
  induces the isomorphism of determinant lines `TauCeti.DetBundle.congrHomeomorph e`, given on
  each fibre by `LinearEquiv.exteriorPower`, functorially (`TauCeti.DetBundle.congrEquiv_refl`,
  `TauCeti.DetBundle.congrEquiv_trans`, `TauCeti.DetBundle.congrEquiv_symm`);
* for a continuous map `f : B' → B`, the pullback of `det E` is the determinant line of the
  pullback of `E`, by the map induced by the identity of the fibres of `E`
  (`TauCeti.DetBundle.pullbackHomeomorph`).

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
* `TauCeti.DetBundle.ofBundleDetHomeomorph`: comparison with `FiniteRankBundleCore.det`.

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

/-- A chart coordinate reads `v₁ ∧ ⋯ ∧ vᵣ` as the determinant of `(e v₁, …, e vᵣ)` in the basis
`Module.finBasis 𝕜 F`. -/
theorem chartCoord_ιMulti (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (hx : x ∈ e.baseSet)
    (v : Fin (finrank 𝕜 F) → E x) :
    chartCoord e hx ((linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ v)) =
      (Module.finBasis 𝕜 F).det (fun i ↦ (e ⟨x, v i⟩).2) := by
  simp only [chartCoord_def, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.exteriorPower_apply_ιMulti, Module.Basis.exteriorPowerTopEquiv_apply_ιMulti]
  rfl

/-- **The transitions of the determinant line.** Passing from the chart coordinate of `e` to that
of `e'` multiplies by the determinant of the coordinate change of `E` from `e` to `e'`. -/
theorem chartCoord_chartCoord_symm (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) (c : 𝕜) :
    chartCoord e' hx' ((chartCoord e hx).symm c) =
      (e.coordChangeL 𝕜 e' x : F →L[𝕜] F).det * c := by
  have h : ∀ y, (e'.linearEquivAt 𝕜 x hx').exteriorPower (finrank 𝕜 F)
      ((e.linearEquivAt 𝕜 x hx).symm.exteriorPower (finrank 𝕜 F) y) =
      (e.coordChangeL 𝕜 e' x).toLinearEquiv.exteriorPower (finrank 𝕜 F) y := fun y ↦ by
    rw [e.coe_coordChangeL' e' ⟨hx, hx'⟩, LinearEquiv.exteriorPower_trans]
    rfl
  simp only [chartCoord_def, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.exteriorPower_symm]
  rw [h, Module.Basis.exteriorPowerTopEquiv_exteriorPower, LinearEquiv.apply_symm_apply]
  rfl

/-- A chart coordinate is a homeomorphism onto `𝕜`. -/
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
  toFun p := ⟨p.proj, if h : p.proj ∈ e.baseSet then chartCoord e h p.2 else 0⟩
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
      (p.proj, if h : p.proj ∈ e.baseSet then chartCoord e h p.2 else 0) := (rfl)

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
  exact (chartCoord e h).injective (by simpa using key.2)

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

/-! ### Continuity of maps into a determinant line -/

section Continuity

variable [TopologicalSpace B]

/-- A map of total spaces over the identity of the base into a fibre bundle is continuous as soon
as, around each point, it is read in some trivialization of the source and the preferred
trivialization of the target by a function continuous at that point. -/
private theorem continuous_of_forall_trivialization {F₁ F₂ : Type*} [TopologicalSpace F₁]
    [TopologicalSpace F₂] {E₁ E₂ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂) (hΦ : ∀ p, (Φ p).proj = p.proj)
    (hproj : Continuous (π F₁ E₁))
    (h : ∀ p : TotalSpace F₁ E₁, ∃ (e : Trivialization F₁ (π F₁ E₁)) (ψ : B → F₁ → F₂),
      p.proj ∈ e.baseSet ∧ ContinuousAt (fun q ↦ ψ q.proj (e q).2) p ∧
      ∀ q : TotalSpace F₁ E₁, q.proj ∈ e.baseSet →
        q.proj ∈ (trivializationAt F₂ E₂ p.proj).baseSet →
        (trivializationAt F₂ E₂ p.proj (Φ q)).2 = ψ q.proj (e q).2) :
    Continuous Φ := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  obtain ⟨e, ψ, hp, hψ, heq⟩ := h p
  rw [FiberBundle.continuousAt_totalSpace, hΦ p]
  refine ⟨(hproj.congr fun q ↦ (hΦ q).symm).continuousAt, hψ.congr_of_eventuallyEq ?_⟩
  filter_upwards [hproj.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hp),
    hproj.continuousAt.preimage_mem_nhds ((trivializationAt F₂ E₂ p.proj).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₂ E₂ p.proj))] with q hq hq'
  exact heq q hq hq'

end Continuity

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
  rw [congrEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
  rfl

/-- The identity of a bundle induces the identity of its determinant line. -/
@[simp]
theorem congrEquiv_refl (x : B) :
    congrEquiv (F := F) (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (E x)) x =
      ContinuousLinearEquiv.refl 𝕜 _ := by
  ext v
  have h : (ContinuousLinearEquiv.refl 𝕜 (E x)).toLinearEquiv = LinearEquiv.refl 𝕜 (E x) := (rfl)
  rw [congrEquiv_apply, h, LinearEquiv.exteriorPower_refl]
  rfl

/-- The isomorphisms of determinant lines induced by bundle isomorphisms compose. -/
theorem congrEquiv_trans (e : ∀ x, E x ≃L[𝕜] E' x) (e' : ∀ x, E' x ≃L[𝕜] E'' x) (x : B) :
    congrEquiv (F := F) (fun x ↦ (e x).trans (e' x)) x =
      (congrEquiv (F := F) e x).trans (congrEquiv e' x) := by
  ext v
  have h : ((e x).trans (e' x)).toLinearEquiv = (e x).toLinearEquiv ≪≫ₗ (e' x).toLinearEquiv :=
    (rfl)
  rw [ContinuousLinearEquiv.trans_apply, congrEquiv_apply, congrEquiv_apply, congrEquiv_apply, h,
    LinearEquiv.exteriorPower_trans]
  rfl

/-- The inverse of the isomorphism of determinant lines induced by `e` is induced by the inverse
of `e`. -/
theorem congrEquiv_symm (e : ∀ x, E x ≃L[𝕜] E' x) (x : B) :
    (congrEquiv (F := F) e x).symm = congrEquiv (fun x ↦ (e x).symm) x := by
  ext v
  have h : (e x).symm.toLinearEquiv = (e x).toLinearEquiv.symm := (rfl)
  rw [ContinuousLinearEquiv.symm_apply_eq, congrEquiv_apply, congrEquiv_apply, h,
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
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.2)))
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
      LinearEquiv.exteriorPower_symm, linearEquiv_symm_apply]
    rfl
  rw [key, Module.Basis.exteriorPowerTopEquiv_exteriorPower, hdet, LinearEquiv.apply_symm_apply]

/-- **Functoriality of the determinant line in bundle isomorphisms.** A continuous fibrewise
linear isomorphism `e` between vector bundles with finite-dimensional model fibres induces a
homeomorphism of the total spaces of their determinant lines, which is
`TauCeti.DetBundle.congrEquiv e` on each fibre. -/
def congrHomeomorph (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.2))) :
    TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace 𝕜 (DetBundle 𝕜 F E') :=
  bundleHomeomorph (congrEquiv e) <| by
    refine continuous_of_forall_trivialization _ (fun _ ↦ rfl)
      (FiberBundle.continuous_proj 𝕜 _) fun p ↦ ?_
    obtain ⟨s, hs, hs'⟩ := continuousAt_chartCoord_congrEquiv e he p.proj
    refine ⟨trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj, fun x c ↦ s x * c,
      mem_baseSet_trivializationAt 𝕜 _ p.proj,
      (hs.comp (FiberBundle.continuous_proj 𝕜 _).continuousAt).mul
        ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).continuousOn.continuousAt
          ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).open_source.mem_nhds
            (FiberBundle.mem_trivializationAt_proj_source))).snd, ?_⟩
    rintro ⟨x, v⟩ (hx : x ∈ (trivializationAt F E p.proj).baseSet)
      (hx' : x ∈ (trivializationAt F E' p.proj).baseSet)
    change (trivialization (trivializationAt F E' p.proj) ⟨x, congrEquiv e x v⟩).2 =
      s x * (trivialization (trivializationAt F E p.proj) ⟨x, v⟩).2
    rw [trivialization_apply_mk _ hx', trivialization_apply_mk _ hx,
      ← hs' x hx hx' (chartCoord _ hx v), LinearEquiv.symm_apply_apply]

@[simp]
theorem congrHomeomorph_apply (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.2)))
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    congrHomeomorph e he p = ⟨p.proj, congrEquiv e p.proj p.2⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem congrHomeomorph_symm_apply (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.2)))
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F E')) :
    (congrHomeomorph e he).symm p = ⟨p.proj, (congrEquiv e p.proj).symm p.2⟩ :=
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
    rfl
  calc chartCoord (e.pullback f) hy (pullbackEquiv (f : B' → B) y v)
      = modelCoord F (((e.pullback f).linearEquivAt 𝕜 y hy).exteriorPower (finrank 𝕜 F)
          (linearEquiv 𝕜 F ((f : B' → B) *ᵖ E) y (pullbackEquiv (f : B' → B) y v))) := (rfl)
    _ = modelCoord F (((e.pullback f).linearEquivAt 𝕜 y hy).exteriorPower (finrank 𝕜 F)
          ((pullbackFiberEquiv (𝕜 := 𝕜) (E := E) (f : B' → B) y).exteriorPower (finrank 𝕜 F)
            (linearEquiv 𝕜 F E (f y) v))) := by rw [linearEquiv_pullbackEquiv]
    _ = modelCoord F ((pullbackFiberEquiv (𝕜 := 𝕜) (E := E) (f : B' → B) y ≪≫ₗ
          (e.pullback f).linearEquivAt 𝕜 y hy).exteriorPower (finrank 𝕜 F)
            (linearEquiv 𝕜 F E (f y) v)) := by
      rw [LinearEquiv.exteriorPower_trans]
      rfl
    _ = _ := by
      rw [h]
      rfl

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
    refine continuous_of_forall_trivialization _ (fun _ ↦ rfl)
      (FiberBundle.continuous_proj 𝕜 _) fun p ↦ ?_
    refine ⟨trivializationAt 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E)) p.proj, fun _ c ↦ c,
      mem_baseSet_trivializationAt 𝕜 _ p.proj,
      ((trivializationAt 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E)) p.proj).continuousOn.continuousAt
        ((trivializationAt 𝕜 _ p.proj).open_source.mem_nhds
          (FiberBundle.mem_trivializationAt_proj_source))).snd, ?_⟩
    rintro ⟨y, v⟩ (hy : f y ∈ (trivializationAt F E (f p.proj)).baseSet)
      (hy' : y ∈ (trivializationAt F ((f : B' → B) *ᵖ E) p.proj).baseSet)
    change (trivialization (trivializationAt F ((f : B' → B) *ᵖ E) p.proj)
      ⟨y, pullbackEquiv (f : B' → B) y v⟩).2 =
      (trivialization (trivializationAt F E (f p.proj)) ⟨f y, v⟩).2
    rw [trivialization_apply_mk _ hy']
    exact (chartCoord_pullbackEquiv _ f hy' v).trans
      (congrArg Prod.snd (trivialization_apply_mk _ hy v)).symm

@[simp]
theorem pullbackHomeomorph_apply (p : TotalSpace 𝕜 ((f : B' → B) *ᵖ (DetBundle 𝕜 F E))) :
    pullbackHomeomorph f p = ⟨p.proj, pullbackEquiv (f : B' → B) p.proj p.2⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem pullbackHomeomorph_symm_apply
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F ((f : B' → B) *ᵖ E))) :
    (pullbackHomeomorph f).symm p = ⟨p.proj, (pullbackEquiv (f : B' → B) p.proj).symm p.2⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Pullback

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
    refine continuous_of_forall_trivialization _ (fun _ ↦ rfl) A.det.core.continuous_proj
      fun p ↦ ?_
    refine ⟨A.det.core.localTriv p.proj, fun _ ↦ detCoord A, A.det.mem_baseSet_self p.proj,
      (detCoord A).continuous.continuousAt.comp
        ((A.det.core.localTriv p.proj).continuousOn.continuousAt
          ((A.det.core.localTriv p.proj).open_source.mem_nhds
            ((A.det.core.mem_localTriv_source _ _).2 (A.det.mem_baseSet_self p.proj)))).snd, ?_⟩
    rintro ⟨x, v⟩ (_hx : x ∈ A.det.core.baseSet p.proj)
      (hx' : x ∈ (trivializationAt (Fin n → 𝕜) E p.proj).baseSet)
    change (trivialization (trivializationAt (Fin n → 𝕜) E p.proj)
      ⟨x, ofBundleDetFiberEquiv (𝕜 := 𝕜) (n := n) E x v⟩).2 =
        detCoord A (A.det.core.localTriv p.proj ⟨x, v⟩).2
    have hsmul (c : 𝕜) (w : Fin A.det.rank → 𝕜) :
        detCoord A ((c • ContinuousLinearMap.id 𝕜 (Fin A.det.rank → 𝕜)) w) = c * detCoord A w := by
      simp
    have hcc : A.core.coordChange x p.proj x =
        ((trivializationAt (Fin n → 𝕜) E x).coordChangeL 𝕜 (trivializationAt (Fin n → 𝕜) E p.proj)
          x : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)) :=
      pointIndexedCore_coordChange 𝕜 (Fin n → 𝕜) E x p.proj x
    rw [trivialization_apply_mk _ hx', VectorBundleCore.localTriv_apply, A.det.indexAt_eq,
      FiniteRankBundleCore.coordChange_det, ofBundleDetFiberEquiv_apply,
      chartCoord_chartCoord_symm]
    refine ((hsmul _ v).trans ?_).symm
    rw [hcc]
    rfl

@[simp]
theorem ofBundleDetHomeomorph_apply
    (p : (FiniteRankBundleCore.ofBundle 𝕜 n E).det.core.TotalSpace) :
    ofBundleDetHomeomorph (𝕜 := 𝕜) (n := n) E p =
      ⟨p.proj, ofBundleDetFiberEquiv (𝕜 := 𝕜) (n := n) E p.proj p.2⟩ :=
  bundleHomeomorph_apply _ _ p

end FiniteRank

end DetBundle

end TauCeti
