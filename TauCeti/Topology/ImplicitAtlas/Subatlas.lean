/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Pi.Finset
public import TauCeti.Topology.ImplicitAtlas.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Relabelling, subatlases and finite subatlases of implicit atlases

An implicit atlas `𝒜` indexed by `A` can be pulled back along an injective map `f : A' ↪ A` of
index types: the relabelled atlas `𝒜.relabel f h` has isotropy group `Γ_(f α)`, obstruction space
`E_(f α)` and Kuranishi map `s_(f α)` at the index `α ∈ A'`, and thickening `X_(f I)` at a finite
`I ⊆ A'`. It is an implicit atlas exactly when the regular footprints `V_(f I)` still cover `X`,
which is the hypothesis `h`; every other axiom transfers from `𝒜`. Its footprints are those of
`𝒜` (`TauCeti.ImplicitAtlas.footprint_relabel`).

The *subatlas* `𝒜.restrict S h` on a set `S ⊆ A` of indices is the relabelling along the inclusion
`S ↪ A`, defined when the footprints `V_I` with `I ⊆ S` cover `X`. A compact `X` is covered by
finitely many footprints, and the union of their index sets is finite
(`TauCeti.ImplicitAtlas.exists_finset_iUnion_footprint_eq_univ`), so every implicit atlas on a
compact space has a finite subatlas. The covering hypothesis cannot be dropped: the atlas
`s(x) = xᵐ` on a point has `V_∅ = ∅` (`TauCeti.ImplicitAtlas.footprint_powAtlas_empty`), so it does
not restrict to the empty set of indices.

The virtual cochain complexes built from an implicit atlas use only a finite subatlas, so the
finite subatlases are the input of that construction.

## Main definitions

* `TauCeti.ImplicitAtlas.relabelAct`: the actions on `X_(f I)` of the relabelled groups
  `∏_(α ∈ I) Γ_(f α)`, through the relabelling isomorphism `MulEquiv.piFinsetMap`.
* `TauCeti.ImplicitAtlas.relabelKuranishi`: the relabelled Kuranishi maps.
* `TauCeti.ImplicitAtlas.relabel`: the relabelling of an implicit atlas along an embedding of
  index types.
* `TauCeti.ImplicitAtlas.restrict`: the subatlas on a set of indices.

## Main results

* `TauCeti.ImplicitAtlas.kuranishiZeroSet_relabelKuranishi`: the zero sets of the relabelled
  Kuranishi maps are those of the original ones.
* `TauCeti.ImplicitAtlas.footprint_relabel`, `TauCeti.ImplicitAtlas.footprint_restrict`: the
  footprints of a relabelled atlas and of a subatlas.
* `TauCeti.ImplicitAtlas.exists_finset_iUnion_footprint_eq_univ`: on a compact space, the
  footprints of the subsets of some finite set of indices cover.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 3.1.1 and
  Remark 3.1.5.
-/

public section

open Set Topology
open Finset hiding range

namespace TauCeti.ImplicitAtlas

variable {A A' : Type*} (f : A' ↪ A)

section Relabel

/-- The actions of the relabelled groups `∏_(α ∈ I) Γ_(f α)` on the thickenings `X_(f I)`: the
action of `Γ_(f I)` composed with the relabelling isomorphism `∏_(α ∈ I) Γ_(f α) ≃* Γ_(f I)`. -/
noncomputable def relabelAct {Γ : A → Type*} [∀ α, MulOneClass (Γ α)] {T : Finset A → Type*}
    [∀ I, TopologicalSpace (T I)] (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (I : Finset A') : ((α : I) → Γ (f α)) →* (T (I.map f) ≃ₜ T (I.map f)) :=
  (act (I.map f)).comp (MulEquiv.piFinsetMap Γ f I).toMonoidHom

@[simp]
theorem relabelAct_apply {Γ : A → Type*} [∀ α, MulOneClass (Γ α)] {T : Finset A → Type*}
    [∀ I, TopologicalSpace (T I)] (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (I : Finset A') (g : (α : I) → Γ (f α)) :
    relabelAct f act I g =
      act (I.map f) (MulEquiv.piFinsetMap Γ f I g) :=
  (rfl)

/-- The relabelled Kuranishi maps `s_(f α) : X_(f J) → E_(f α)`, for `α ∈ J`. -/
def relabelKuranishi {T : Finset A → Type*} {E : A → Type*}
    (s : ∀ (J : Finset A) (α : J), T J → E α) (J : Finset A') (α : J) : T (J.map f) → E (f α) :=
  s (J.map f) ⟨f α, mem_map_of_mem f α.property⟩

@[simp]
theorem relabelKuranishi_apply {T : Finset A → Type*} {E : A → Type*}
    (s : ∀ (J : Finset A) (α : J), T J → E α) (J : Finset A') (α : J) (x : T (J.map f)) :
    relabelKuranishi f s J α x = s (J.map f) ⟨f α, mem_map_of_mem f α.property⟩ x :=
  (rfl)

/-- The zero sets of the relabelled Kuranishi maps are those of the original ones:
`Z_IJ = Z_(f I)(f J)`. -/
@[simp]
theorem kuranishiZeroSet_relabelKuranishi {T : Finset A → Type*} {E : A → Type*}
    [∀ α, Zero (E α)] (s : ∀ (J : Finset A) (α : J), T J → E α) (I J : Finset A') :
    kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun α ↦ E (f α)) (relabelKuranishi f s) I J =
      kuranishiZeroSet s (I.map f) (J.map f) := by
  ext x
  simp only [mem_kuranishiZeroSet, relabelKuranishi]
  refine ⟨fun hx ⟨β, hβ⟩ hβI ↦ ?_, fun hx α hαI ↦ hx _ fun h ↦ hαI ((mem_map' f).1 h)⟩
  obtain ⟨α, hα, rfl⟩ := mem_map.1 hβ
  exact hx ⟨α, hα⟩ fun h ↦ hβI (mem_map_of_mem f h)

variable [DecidableEq A] [DecidableEq A'] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-- The images `U_IJ` of footprint maps with equal targets `J = J'` agree. -/
private theorem range_footprintMap_eq_of_eq {I J J' : Finset A} (h : I ⊆ J) (h' : I ⊆ J')
    (hJ : J = J') : range (𝒜.footprintMap h) = range (𝒜.footprintMap h') := by
  subst hJ
  rfl

/-- The footprint map `ψ_IJ` of the relabelled atlas: the footprint map `ψ_(f I)(f J)` of `𝒜`,
on the zero set `Z_IJ = Z_(f I)(f J)`. -/
private noncomputable def relabelFootprintMap {I J : Finset A'} (h : I ⊆ J) :
    kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun α ↦ E (f α))
      (relabelKuranishi f 𝒜.kuranishi) I J → T (I.map f) :=
  𝒜.footprintMap (map_subset_map.2 h) ∘
    Homeomorph.setCongr (kuranishiZeroSet_relabelKuranishi f 𝒜.kuranishi I J)

omit [DecidableEq A'] in
private theorem range_relabelFootprintMap {I J : Finset A'} (h : I ⊆ J) :
    range (relabelFootprintMap f 𝒜 h) = range (𝒜.footprintMap (map_subset_map.2 h)) :=
  (Homeomorph.setCongr _).surjective.range_comp _

/-- The **relabelling** of an implicit atlas along an embedding `f : A' ↪ A` of index types, when
the regular footprints `V_(f I)` cover `X`. At `α ∈ A'` and finite `I ⊆ J ⊆ A'` its group,
obstruction space and Kuranishi map are `Γ_(f α)`, `E_(f α)` and `s_(f α)`, and its thickening,
regular locus and footprint map are `X_(f I)`, `X_(f I)^reg` and `ψ_(f I)(f J)`. -/
noncomputable def relabel (hf : ⋃ I : Finset A', 𝒜.footprint (I.map f) = univ) :
    ImplicitAtlas (fun α ↦ Γ (f α)) (fun α ↦ E (f α)) (fun α ↦ ρ (f α)) (fun I ↦ T (I.map f))
      (relabelAct f act) X d where
  -- `T (∅.map f)` is `T ∅` by definition, since `Finset.map_empty` holds by `rfl`.
  baseHomeomorph := 𝒜.baseHomeomorph
  kuranishi := relabelKuranishi f 𝒜.kuranishi
  continuous_kuranishi I α := 𝒜.continuous_kuranishi _ _
  kuranishi_act I α g x := by
    rw [relabelKuranishi, relabelAct_apply, 𝒜.kuranishi_act, MulEquiv.piFinsetMap_apply_mk]
  regLocus I := 𝒜.regLocus (I.map f)
  isOpen_regLocus I := 𝒜.isOpen_regLocus _
  act_mem_regLocus I g x hx := 𝒜.act_mem_regLocus _ _ x hx
  footprintMap _ _ := relabelFootprintMap f 𝒜
  continuous_footprintMap _ _ h :=
    (𝒜.continuous_footprintMap _).comp (Homeomorph.setCongr _).continuous
  footprintMap_act I J h g x hx := by
    simp only [relabelFootprintMap, Function.comp_apply, relabelAct_apply]
    exact (𝒜.footprintMap_act (map_subset_map.2 h) _ ⟨x.val, _⟩ _).trans
      (congrArg (fun γ ↦ act (I.map f) γ _) (MulEquiv.restrict₂_piFinsetMap Γ f h g))
  footprintMap_self I x := 𝒜.footprintMap_self _ x
  footprintMap_footprintMap I J K hIJ hJK x hx hx' :=
    𝒜.footprintMap_footprintMap (map_subset_map.2 hIJ) (map_subset_map.2 hJK) ⟨x.val, _⟩ _ _
  kuranishi_footprintMap I J h x α :=
    𝒜.kuranishi_footprintMap (map_subset_map.2 h) ⟨x.val, _⟩ ⟨f α, mem_map_of_mem f α.property⟩
  isOpen_range_footprintMap I J h := by
    rw [range_relabelFootprintMap]
    exact 𝒜.isOpen_range_footprintMap _
  range_footprintMap_inter I J₁ J₂ h₁ h₂ := by
    simp only [range_relabelFootprintMap]
    rw [𝒜.range_footprintMap_inter]
    exact range_footprintMap_eq_of_eq 𝒜 _ _ (map_union J₁ J₂).symm
  footprintMap_mem_range_iff I J K hIJ hJK x := by
    simp only [range_relabelFootprintMap]
    exact 𝒜.footprintMap_mem_range_iff (map_subset_map.2 hIJ) (map_subset_map.2 hJK) ⟨x.val, _⟩
  isQuotientMap_footprintMap I J h := by
    -- `ψ_IJ` corestricted to its image is that of `ψ_(f I)(f J)`, up to the identifications of
    -- the equal zero sets and of the equal images.
    have key : rangeFactorization (relabelFootprintMap f 𝒜 h) =
        Homeomorph.setCongr (range_relabelFootprintMap f 𝒜 h).symm ∘
          rangeFactorization (𝒜.footprintMap (map_subset_map.2 h)) ∘
            Homeomorph.setCongr (kuranishiZeroSet_relabelKuranishi f 𝒜.kuranishi I J) :=
      (rfl)
    rw [key]
    exact (Homeomorph.setCongr _).isQuotientMap.comp
      ((𝒜.isQuotientMap_footprintMap _).comp (Homeomorph.setCongr _).isQuotientMap)
  footprintMap_eq_footprintMap_iff I J h x y := by
    let Φ := MulEquiv.piFinsetMap Γ f J
    refine (𝒜.footprintMap_eq_footprintMap_iff (map_subset_map.2 h) ⟨x.val, _⟩ ⟨y.val, _⟩).trans
      ⟨fun ⟨g, hg, hgx⟩ ↦ ⟨Φ.symm g, ?_, ?_⟩, fun ⟨g, hg, hgx⟩ ↦ ⟨Φ g, ?_, hgx⟩⟩
    · rw [← (MulEquiv.piFinsetMap Γ f I).map_eq_one_iff, ← MulEquiv.restrict₂_piFinsetMap,
        MulEquiv.apply_symm_apply, hg]
    · simpa [Φ] using hgx
    · rw [MulEquiv.restrict₂_piFinsetMap Γ f h g, hg, map_one]
  mem_regLocus_of_footprintMap_mem I J h x hx :=
    𝒜.mem_regLocus_of_footprintMap_mem (map_subset_map.2 h) ⟨x.val, _⟩ hx
  eq_one_of_act_eq I J h x hx g hg hgx := by
    refine (MulEquiv.piFinsetMap Γ f J).map_eq_one_iff.1 <|
      𝒜.eq_one_of_act_eq (map_subset_map.2 h) ⟨x.val, _⟩ hx _ ?_ hgx
    rw [MulEquiv.restrict₂_piFinsetMap Γ f h g, hg, map_one]
  exists_openPartialHomeomorph I J h x hx := by
    obtain ⟨n, hn, e, hxe, he⟩ :=
      𝒜.exists_openPartialHomeomorph (map_subset_map.2 h) ⟨x.val, _⟩ hx
    -- The indices `J \ I` correspond to the indices `f J \ f I` of the original atlas.
    let σ : ↥(J \ I) ≃ ↥(J.map f \ I.map f) :=
      ((J \ I).equivMap f).trans (Equiv.subtypeEquivRight fun _ ↦ by rw [map_sdiff])
    refine ⟨n, by rw [hn, sum_map], e.transHomeomorph ((Homeomorph.refl _).prodCongr
      (Homeomorph.piCongrLeft (Y := fun α : ↥(J.map f \ I.map f) ↦ E α) σ).symm), hxe,
      fun y hy ↦ ?_⟩
    -- Both sides are `s_(f α)(y)` for `α ∈ J \ I`, since `σ α` is `f α` by definition.
    exact funext fun α ↦ congrFun (he y hy) (σ α)
  exists_footprintMap_eq y := by
    obtain ⟨I, hI⟩ := mem_iUnion.1 (hf.ge (mem_univ y))
    obtain ⟨x, hx, hxy⟩ := 𝒜.mem_footprint.1 hI
    exact ⟨I, ⟨x.val, (kuranishiZeroSet_relabelKuranishi f 𝒜.kuranishi ∅ I).symm ▸ x.property⟩, hx,
        hxy⟩

variable (hf : ⋃ I : Finset A', 𝒜.footprint (I.map f) = univ)

/-- The base identification of the relabelled atlas is that of `𝒜`; its source `X_(f ∅)` is
`X_∅` by definition, since `Finset.map_empty` holds by `rfl`. -/
@[simp]
theorem baseHomeomorph_relabel : (𝒜.relabel f hf).baseHomeomorph = 𝒜.baseHomeomorph :=
  (rfl)

/-- The Kuranishi maps of the relabelled atlas are `s_(f α) : X_(f J) → E_(f α)`. -/
@[simp]
theorem kuranishi_relabel : (𝒜.relabel f hf).kuranishi = relabelKuranishi f 𝒜.kuranishi :=
  (rfl)

/-- The regular loci of the relabelled atlas are `X_(f I)^reg`. -/
@[simp]
theorem regLocus_relabel (I : Finset A') : (𝒜.relabel f hf).regLocus I = 𝒜.regLocus (I.map f) :=
  (rfl)

/-- The zero sets of the relabelled atlas are those of `𝒜`: `Z_IJ = Z_(f I)(f J)`. -/
theorem kuranishiZeroSet_relabel (I J : Finset A') :
    kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun α ↦ E (f α))
        (𝒜.relabel f hf).kuranishi I J =
      kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f) := by
  rw [kuranishi_relabel]
  exact kuranishiZeroSet_relabelKuranishi f 𝒜.kuranishi I J

/-- The footprint maps of the relabelled atlas are those of `𝒜`: `ψ_IJ = ψ_(f I)(f J)`. -/
theorem footprintMap_relabel {I J : Finset A'} (h : I ⊆ J)
    (x : kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun α ↦ E (f α))
      (𝒜.relabel f hf).kuranishi I J) :
    (𝒜.relabel f hf).footprintMap h x =
      𝒜.footprintMap (map_subset_map.2 h) ⟨x.val, 𝒜.kuranishiZeroSet_relabel f hf I J ▸ x.property⟩
          :=
  (rfl)

/-- The footprints of the relabelled atlas are those of `𝒜`: `V_I = V_(f I)`. -/
@[simp]
theorem footprint_relabel (I : Finset A') :
    (𝒜.relabel f hf).footprint I = 𝒜.footprint (I.map f) := by
  ext y
  simp only [mem_footprint]
  -- The footprint maps `ψ_∅I` and `ψ_∅(f I)` agree on the equal zero sets `Z_∅I = Z_∅(f I)`.
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, 𝒜.kuranishiZeroSet_relabel f hf ∅ I ▸ x.property⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, (𝒜.kuranishiZeroSet_relabel f hf ∅ I).symm ▸ x.property⟩, hx, rfl⟩

end Relabel

section Restrict

variable [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-- The **subatlas** of an implicit atlas on a set `S` of indices, when the regular footprints
`V_I` with `I ⊆ S` cover `X`: the relabelling along the inclusion `S ↪ A`. -/
noncomputable def restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) :
    ImplicitAtlas (fun α : S ↦ Γ α) (fun α : S ↦ E α) (fun α : S ↦ ρ α)
      (fun I ↦ T (I.map (.subtype (· ∈ S)))) (relabelAct (.subtype (· ∈ S)) act) X d :=
  𝒜.relabel (.subtype (· ∈ S)) <| eq_univ_of_forall fun y ↦ by
    classical
    obtain ⟨I, hIS, hy⟩ := mem_iUnion₂.1 (hS.ge (mem_univ y))
    exact mem_iUnion.2 ⟨I.subtype (· ∈ S), by rwa [subtype_map_of_mem fun α hα ↦ hIS hα]⟩

/-- The footprints of the subatlas on `S` are those of `𝒜`. -/
@[simp]
theorem footprint_restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) (I : Finset S) :
    (𝒜.restrict S hS).footprint I = 𝒜.footprint (I.map (.subtype (· ∈ S))) :=
  footprint_relabel ..

/-- The base identification of the subatlas on `S` is that of `𝒜`. -/
@[simp]
theorem baseHomeomorph_restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) :
    (𝒜.restrict S hS).baseHomeomorph = 𝒜.baseHomeomorph :=
  (rfl)

/-- The Kuranishi maps of the subatlas on `S` are those of `𝒜` at the indices in `S`. -/
@[simp]
theorem kuranishi_restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) :
    (𝒜.restrict S hS).kuranishi = relabelKuranishi (.subtype (· ∈ S)) 𝒜.kuranishi :=
  (rfl)

/-- The regular loci of the subatlas on `S` are those of `𝒜`. -/
@[simp]
theorem regLocus_restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) (I : Finset S) :
    (𝒜.restrict S hS).regLocus I = 𝒜.regLocus (I.map (.subtype (· ∈ S))) :=
  (rfl)

/-- The zero sets of the subatlas on `S` are those of `𝒜`. -/
theorem kuranishiZeroSet_restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) (I J : Finset S) :
    kuranishiZeroSet (T := fun J ↦ T (J.map (.subtype (· ∈ S)))) (E := fun α : S ↦ E α)
        (𝒜.restrict S hS).kuranishi I J =
      kuranishiZeroSet 𝒜.kuranishi (I.map (.subtype (· ∈ S))) (J.map (.subtype (· ∈ S))) :=
  kuranishiZeroSet_relabel ..

/-- The footprint maps of the subatlas on `S` are those of `𝒜`. -/
theorem footprintMap_restrict (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) {I J : Finset S}
    (h : I ⊆ J)
    (x : kuranishiZeroSet (T := fun J ↦ T (J.map (.subtype (· ∈ S)))) (E := fun α : S ↦ E α)
      (𝒜.restrict S hS).kuranishi I J) :
    (𝒜.restrict S hS).footprintMap h x =
      𝒜.footprintMap (map_subset_map.2 h) ⟨x.val, 𝒜.kuranishiZeroSet_restrict S hS I J ▸ x.property⟩
          :=
  (rfl)

/-- **Finite subatlases.** On a compact space, the regular footprints `V_I` with `I` contained
in some finite set `S` of indices cover, so that `𝒜.restrict S` is a finite subatlas. -/
theorem exists_finset_iUnion_footprint_eq_univ [CompactSpace X] :
    ∃ S : Finset A, ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover 𝒜.footprint 𝒜.isOpen_footprint
    𝒜.iUnion_footprint.ge
  refine ⟨t.sup id, eq_univ_of_forall fun y ↦ ?_⟩
  obtain ⟨I, hI, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact mem_iUnion₂.2 ⟨I, coe_subset.2 (le_sup (f := id) hI), hy⟩

end Restrict

end TauCeti.ImplicitAtlas
