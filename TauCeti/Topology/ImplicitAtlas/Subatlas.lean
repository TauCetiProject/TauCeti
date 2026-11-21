/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.Basic
public import TauCeti.Algebra.Group.Equiv.Pi
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Data.Finset.Image

/-!
# Subatlases and injective relabelling of implicit atlases

An implicit atlas `𝒜` on `X` indexed by `A` restricts to any set of indices `S ⊆ A` whose regular
footprints still cover `X` (`TauCeti.ImplicitAtlas.FootprintsCover`): keep the thickenings `X_I`,
Kuranishi maps, regular loci and footprint maps for the finite `I ⊆ S` and forget the others.
Every axiom other than the covering axiom only involves the index sets it mentions, so it is
inherited; the covering axiom is the hypothesis. More generally, the indices can be relabelled
along an injection `f : B ↪ A` whose image is such a set (`TauCeti.ImplicitAtlas.relabel`). The
relabelled atlas has the groups `Γ (f β)`, the obstruction spaces `E (f β)` and the thickenings
`X_(f I)`. Its action of `∏_(β ∈ I) Γ (f β)` on `X_(f I)` is the action of `∏_(α ∈ f I) Γ α`
after relabelling the factors along the bijection `I ≃ f I` (`TauCeti.ImplicitAtlas.relabelAct`).
The restriction to `S ⊆ A` (`TauCeti.ImplicitAtlas.restrict`) is the relabelling along the
inclusion of `S`.

Relabelling changes no footprint: the regular footprint of `I` in the relabelled atlas is the
regular footprint of `f I` in `𝒜` (`TauCeti.ImplicitAtlas.footprint_relabel`).

On a compact space finitely many footprints cover, since they are open
(`TauCeti.ImplicitAtlas.isOpen_footprint`) and cover `X`
(`TauCeti.ImplicitAtlas.iUnion_footprint`). The union of their finitely many index sets is a finite
set of indices whose footprints cover (`TauCeti.ImplicitAtlas.exists_finset_footprintsCover`), so
every implicit atlas on a compact space restricts to an implicit atlas with finitely many indices.
This is the finiteness the virtual cochain complexes of an atlas need, since they are built from
all of its thickenings at once.

Restriction can fail: the atlas `s(x) = xᵐ` on a point does not restrict to the empty set of
indices, since the regular locus of `X_∅` is empty (see `TauCeti.Topology.ImplicitAtlas.Examples`).

## Main definitions

* `TauCeti.ImplicitAtlas.FootprintsCover 𝒜 S`: the regular footprints `V_I` with `I ⊆ S` cover `X`.
* `TauCeti.ImplicitAtlas.relabel 𝒜 hf`: the relabelling of `𝒜` along an injection `f : B ↪ A`
  whose image satisfies `FootprintsCover`.
* `TauCeti.ImplicitAtlas.restrict 𝒜 S hS`: the restriction of `𝒜` to a set of indices `S` with
  `FootprintsCover 𝒜 S`.

## Main results

* `TauCeti.ImplicitAtlas.footprint_relabel`: relabelling preserves regular footprints.
* `TauCeti.ImplicitAtlas.exists_finset_footprintsCover`: on a compact space, the footprints with
  index sets inside some finite set of indices cover.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Section 3.1: implicit atlases
  (Definition 3.1.1) and Remark 3.1.5, on why reindexing along non-injective maps of index sets
  needs index sets with repetitions; only injective relabelling is treated here.
-/

public section

open Set Topology Function

namespace TauCeti.ImplicitAtlas

section RelabelAct

variable {A B : Type*} {Γ : A → Type*} [∀ α, Group (Γ α)] {T : Finset A → Type*}
  [∀ I, TopologicalSpace (T I)]

/-- The action of the relabelled atlas: along an injection `f : B ↪ A`, the group
`∏_(β ∈ I) Γ (f β)` acts on `X_(f I)` through the relabelling `∏_(β ∈ I) Γ (f β) ≃* ∏_(α ∈ f I) Γ α`
of the factors along the bijection `I ≃ f I` (`MulEquiv.piFinsetMap`). -/
noncomputable def relabelAct (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)) (f : B ↪ A)
    (I : Finset B) : ((β : I) → Γ (f β)) →* (T (I.map f) ≃ₜ T (I.map f)) :=
  (act (I.map f)).comp (MulEquiv.piFinsetMap Γ f I).toMonoidHom

/-- The relabelled action of `g` is the action of the relabelled group element. -/
@[simp]
theorem relabelAct_apply (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)) (f : B ↪ A)
    (I : Finset B) (g : (β : I) → Γ (f β)) :
    relabelAct act f I g = act (I.map f) (MulEquiv.piFinsetMap Γ f I g) :=
  (rfl)

end RelabelAct

variable {A B : Type*} [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-! ### Sets of indices whose footprints cover -/

/-- The regular footprints `V_I` of the finite sets of indices `I ⊆ S` cover `X`. This is the
covering axiom of the restriction of `𝒜` to `S`, the only axiom the restriction does not inherit. -/
def FootprintsCover (S : Set A) : Prop :=
  ∀ y : X, ∃ I : Finset A, ↑I ⊆ S ∧ y ∈ 𝒜.footprint I

/-- The defining property of `TauCeti.ImplicitAtlas.FootprintsCover`. -/
theorem footprintsCover_iff {S : Set A} :
    𝒜.FootprintsCover S ↔ ∀ y : X, ∃ I : Finset A, ↑I ⊆ S ∧ y ∈ 𝒜.footprint I :=
  Iff.rfl

/-- The footprints of all finite sets of indices cover. -/
theorem footprintsCover_univ : 𝒜.FootprintsCover univ := fun y ↦
  let ⟨I, hI⟩ := mem_iUnion.1 (𝒜.iUnion_footprint.ge (mem_univ y))
  ⟨I, subset_univ _, hI⟩

/-- Footprints that cover with index sets inside `S` cover with index sets inside any larger set. -/
theorem FootprintsCover.mono {𝒜 : ImplicitAtlas Γ E ρ T act X d} {S S' : Set A}
    (hS : 𝒜.FootprintsCover S) (h : S ⊆ S') : 𝒜.FootprintsCover S' := fun y ↦
  let ⟨I, hI, hy⟩ := hS y
  ⟨I, hI.trans h, hy⟩

/-- **Finite subatlases.** On a compact space, the regular footprints with index sets inside some
finite set of indices `S` cover, so `𝒜` restricts to an implicit atlas indexed by `S`. -/
theorem exists_finset_footprintsCover [CompactSpace X] :
    ∃ S : Finset A, 𝒜.FootprintsCover S := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover 𝒜.footprint 𝒜.isOpen_footprint
    𝒜.iUnion_footprint.ge
  refine ⟨t.sup id, fun y ↦ ?_⟩
  obtain ⟨I, hI, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact ⟨I, Finset.coe_subset.2 (Finset.le_sup (f := id) hI), hy⟩

/-! ### Relabelling along an injection -/

section Relabel

variable (f : B ↪ A)

/-- The Kuranishi maps of the relabelling of `𝒜` along `f`. -/
private def relabelKuranishi (J : Finset B) (β : J) : T (J.map f) → E (f β) :=
  𝒜.kuranishi (J.map f) ⟨f β, Finset.mem_map_of_mem f β.property⟩

/-- The zero sets of the relabelled Kuranishi maps. -/
private abbrev relabelZeroSet (I J : Finset B) : Set (T (J.map f)) :=
  kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun β ↦ E (f β)) (𝒜.relabelKuranishi f) I J

/-- The zero sets of the relabelled Kuranishi maps are the zero sets of `𝒜` at the image index
sets. -/
private theorem kuranishiZeroSet_relabelKuranishi (I J : Finset B) :
    𝒜.relabelZeroSet f I J =
      kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f) := by
  ext x
  simp only [mem_kuranishiZeroSet, relabelKuranishi]
  refine ⟨fun hx ⟨α, hα⟩ hαI ↦ ?_, fun hx β hβ ↦ hx _ (by simpa using hβ)⟩
  obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.1 hα
  exact hx ⟨β, hβ⟩ fun hβI ↦ hαI (Finset.mem_map_of_mem f hβI)

/-- The identification of the zero sets of the relabelled Kuranishi maps with those of `𝒜`. -/
private def zeroSetHomeomorph (I J : Finset B) :
    𝒜.relabelZeroSet f I J ≃ₜ
      kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f) :=
  Homeomorph.setCongr (𝒜.kuranishiZeroSet_relabelKuranishi f I J)

@[simp]
private theorem coe_zeroSetHomeomorph {I J : Finset B} (x : 𝒜.relabelZeroSet f I J) :
    (𝒜.zeroSetHomeomorph f I J x : T (J.map f)) = x :=
  (rfl)

@[simp]
private theorem coe_zeroSetHomeomorph_symm {I J : Finset B}
    (x : kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f)) :
    ((𝒜.zeroSetHomeomorph f I J).symm x : T (J.map f)) = x :=
  (rfl)

/-- The footprint maps of the relabelling of `𝒜` along `f`. -/
private def relabelFootprintMap {I J : Finset B} (h : I ⊆ J) :
    𝒜.relabelZeroSet f I J → T (I.map f) :=
  𝒜.footprintMap (Finset.map_subset_map.2 h) ∘ 𝒜.zeroSetHomeomorph f I J

private theorem range_relabelFootprintMap {I J : Finset B} (h : I ⊆ J) :
    range (𝒜.relabelFootprintMap f h) = range (𝒜.footprintMap (Finset.map_subset_map.2 h)) :=
  (𝒜.zeroSetHomeomorph f I J).surjective.range_comp _

/-- The image of a footprint map only depends on its target index set. -/
private theorem range_footprintMap_congr {I K K' : Finset A} (hK : K = K') (h : I ⊆ K)
    (h' : I ⊆ K') : range (𝒜.footprintMap h) = range (𝒜.footprintMap h') := by
  subst hK
  rfl

private theorem isQuotientMap_relabelFootprintMap {I J : Finset B} (h : I ⊆ J) :
    IsQuotientMap (rangeFactorization (𝒜.relabelFootprintMap f h)) := by
  have hr := 𝒜.range_relabelFootprintMap f h
  have : rangeFactorization (𝒜.relabelFootprintMap f h) =
      (Homeomorph.setCongr hr).symm ∘ rangeFactorization (𝒜.footprintMap _) ∘
        𝒜.zeroSetHomeomorph f I J :=
    funext fun _ ↦ rfl
  rw [this]
  exact (Homeomorph.setCongr hr).symm.isQuotientMap.comp
    ((𝒜.isQuotientMap_footprintMap _).comp (𝒜.zeroSetHomeomorph f I J).isQuotientMap)

variable {f} in
/-- The local product models of the relabelled atlas: the product model of `𝒜` at `f I ⊆ f J`,
with its obstruction coordinates relabelled along `J \ I ≃ f J \ f I`. -/
private theorem exists_openPartialHomeomorph_relabel [DecidableEq B] {I J : Finset B} (h : I ⊆ J)
    (x : 𝒜.relabelZeroSet f I J)
    (hx : 𝒜.relabelFootprintMap f h x ∈ 𝒜.regLocus (I.map f)) : ∃ n : ℕ,
      (n : ℤ) = d + ∑ β ∈ I, (Module.finrank ℝ (E (f β)) : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (T (J.map f))
          (EuclideanSpace ℝ (Fin n) × ((β : ↥(J \ I)) → E (f β))),
        x.val ∈ e.source ∧ ∀ y ∈ e.source,
          (e y).2 = fun β : ↥(J \ I) ↦
            𝒜.relabelKuranishi f J ⟨β.val, (Finset.mem_sdiff.1 β.property).1⟩ y := by
  obtain ⟨n, hn, e, hxe, he⟩ :=
    𝒜.exists_openPartialHomeomorph (Finset.map_subset_map.2 h) (𝒜.zeroSetHomeomorph f I J x) hx
  let φ := (Homeomorph.piCongrLeft (Y := fun α : ↥(J.map f \ I.map f) ↦ E α)
    (Finset.equivMapSdiff f J I)).symm
  refine ⟨n, by rw [hn, Finset.sum_map], e.transHomeomorph ((Homeomorph.refl _).prodCongr φ), hxe,
    fun y hy ↦ funext fun β ↦ ?_⟩
  exact congrFun (congrArg φ (he y hy)) β

variable {f} [DecidableEq B]

/-- **Relabelling an implicit atlas along an injection.** If the regular footprints of the finite
sets of indices inside the image of `f : B ↪ A` cover `X`, then the groups `Γ (f β)`, obstruction
spaces `E (f β)`, thickenings `X_(f I)` with the relabelled actions, and the Kuranishi maps,
regular loci and footprint maps of `𝒜` at the image index sets form an implicit atlas indexed by
`B`, of the same virtual dimension. -/
noncomputable def relabel (hf : 𝒜.FootprintsCover (range f)) :
    ImplicitAtlas (fun β ↦ Γ (f β)) (fun β ↦ E (f β)) (fun β ↦ ρ (f β)) (fun I ↦ T (I.map f))
      (relabelAct act f) X d where
  -- `(∅ : Finset B).map f` is definitionally `∅` (Mathlib's `Finset.map_empty` is `rfl`), so
  -- `T ((∅ : Finset B).map f)` is `T ∅`. The `baseHomeomorph` and `exists_footprintMap_eq` fields
  -- below and `footprint_relabel` rely on this to reuse the data of `𝒜` over `∅` unchanged.
  baseHomeomorph := 𝒜.baseHomeomorph
  kuranishi := 𝒜.relabelKuranishi f
  continuous_kuranishi J β := 𝒜.continuous_kuranishi _ _
  kuranishi_act J β g x := by
    simp only [relabelKuranishi, relabelAct_apply, 𝒜.kuranishi_act]
    rw [MulEquiv.piFinsetMap_apply_mk Γ f g β.val β.property]
  regLocus I := 𝒜.regLocus (I.map f)
  isOpen_regLocus I := 𝒜.isOpen_regLocus _
  act_mem_regLocus I g x hx := 𝒜.act_mem_regLocus _ _ x hx
  footprintMap _ _ h := 𝒜.relabelFootprintMap f h
  continuous_footprintMap _ _ h :=
    (𝒜.continuous_footprintMap _).comp (𝒜.zeroSetHomeomorph f _ _).continuous
  footprintMap_act I J h g x hx := by
    simp only [relabelFootprintMap, comp_apply, relabelAct_apply]
    rw [← MulEquiv.restrict₂_piFinsetMap Γ f h]
    exact 𝒜.footprintMap_act _ _ (𝒜.zeroSetHomeomorph f I J x) _
  footprintMap_self I x := 𝒜.footprintMap_self _ x
  footprintMap_footprintMap I J K hIJ hJK x hx hx' :=
    𝒜.footprintMap_footprintMap _ _ (𝒜.zeroSetHomeomorph f J K x) _ _
  kuranishi_footprintMap I J h x α :=
    𝒜.kuranishi_footprintMap _ (𝒜.zeroSetHomeomorph f I J x) _
  isOpen_range_footprintMap I J h := by
    rw [range_relabelFootprintMap]
    exact 𝒜.isOpen_range_footprintMap _
  range_footprintMap_inter I J₁ J₂ h₁ h₂ := by
    simp only [range_relabelFootprintMap, 𝒜.range_footprintMap_inter]
    exact 𝒜.range_footprintMap_congr (Finset.map_union J₁ J₂).symm _ _
  footprintMap_mem_range_iff I J K hIJ hJK x := by
    simp only [range_relabelFootprintMap]
    exact 𝒜.footprintMap_mem_range_iff _ _ (𝒜.zeroSetHomeomorph f I J x)
  isQuotientMap_footprintMap _ _ h := 𝒜.isQuotientMap_relabelFootprintMap f h
  footprintMap_eq_footprintMap_iff I J h x y := by
    simp only [relabelFootprintMap, comp_apply, relabelAct_apply]
    rw [𝒜.footprintMap_eq_footprintMap_iff]
    constructor
    · rintro ⟨g, hg, hgx⟩
      refine ⟨(MulEquiv.piFinsetMap Γ f J).symm g, ?_, by simpa using hgx⟩
      apply (MulEquiv.piFinsetMap Γ f I).injective
      rw [← MulEquiv.restrict₂_piFinsetMap Γ f h, MulEquiv.apply_symm_apply, map_one]
      exact hg
    · rintro ⟨g, hg, hgx⟩
      exact ⟨_, by rw [MulEquiv.restrict₂_piFinsetMap Γ f h, hg, map_one], hgx⟩
  mem_regLocus_of_footprintMap_mem I J h x hx :=
    𝒜.mem_regLocus_of_footprintMap_mem _ (𝒜.zeroSetHomeomorph f I J x) hx
  eq_one_of_act_eq I J h x hx g hg hgx := by
    apply (MulEquiv.piFinsetMap Γ f J).injective
    rw [map_one]
    refine 𝒜.eq_one_of_act_eq _ (𝒜.zeroSetHomeomorph f I J x) hx _ ?_ hgx
    rw [MulEquiv.restrict₂_piFinsetMap Γ f h, hg, map_one]
  exists_openPartialHomeomorph _ _ h x hx := 𝒜.exists_openPartialHomeomorph_relabel h x hx
  exists_footprintMap_eq y := by
    obtain ⟨I, hI, hy⟩ := hf y
    rw [← image_univ, Finset.subset_set_image_iff] at hI
    obtain ⟨I', -, rfl⟩ := hI
    obtain ⟨x, hx, hxy⟩ := 𝒜.mem_footprint.1 (Finset.map_eq_image f I' ▸ hy)
    exact ⟨I', (𝒜.zeroSetHomeomorph f ∅ I').symm x, hx, hxy⟩

variable (hf : 𝒜.FootprintsCover (range f))

/-- The relabelled atlas has the identification `X_∅ ≃ₜ X` of `𝒜`. -/
@[simp]
theorem baseHomeomorph_relabel : (𝒜.relabel hf).baseHomeomorph = 𝒜.baseHomeomorph :=
  (rfl)

/-- The Kuranishi map of `β` on `X_(f J)` in the relabelled atlas is that of `f β` in `𝒜`. -/
@[simp]
theorem kuranishi_relabel_apply (J : Finset B) (β : J) (x : T (J.map f)) :
    (𝒜.relabel hf).kuranishi J β x =
      𝒜.kuranishi (J.map f) ⟨f β, Finset.mem_map_of_mem f β.property⟩ x :=
  (rfl)

/-- The regular locus of `I` in the relabelled atlas is the regular locus of `f I` in `𝒜`. -/
@[simp]
theorem regLocus_relabel (I : Finset B) : (𝒜.relabel hf).regLocus I = 𝒜.regLocus (I.map f) :=
  (rfl)

/-- The zero sets of the relabelled atlas are the zero sets of `𝒜` at the image index sets. -/
theorem kuranishiZeroSet_relabel (I J : Finset B) :
    kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun β ↦ E (f β))
        (𝒜.relabel hf).kuranishi I J =
      kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f) :=
  𝒜.kuranishiZeroSet_relabelKuranishi f I J

/-- The footprint maps of the relabelled atlas are the footprint maps of `𝒜` at the image index
sets. -/
@[simp]
theorem footprintMap_relabel {I J : Finset B} (h : I ⊆ J)
    (x : kuranishiZeroSet (T := fun J ↦ T (J.map f)) (E := fun β ↦ E (f β))
      (𝒜.relabel hf).kuranishi I J) :
    (𝒜.relabel hf).footprintMap h x =
      𝒜.footprintMap (Finset.map_subset_map.2 h)
        ⟨x.val, 𝒜.kuranishiZeroSet_relabel hf I J ▸ x.property⟩ :=
  (rfl)

/-- **Relabelling preserves footprints**: the regular footprint of `I` in the relabelled atlas is
the regular footprint of `f I` in `𝒜`. -/
@[simp]
theorem footprint_relabel (I : Finset B) :
    (𝒜.relabel hf).footprint I = 𝒜.footprint (I.map f) := by
  ext y
  simp only [mem_footprint, footprintMap_relabel, baseHomeomorph_relabel, regLocus_relabel]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, (𝒜.kuranishiZeroSet_relabel hf ∅ I).symm ▸ x.property⟩, hx, rfl⟩

end Relabel

/-! ### Restriction to a set of indices -/

section Restrict

variable (S : Set A) (hS : 𝒜.FootprintsCover S)

/-- **The restriction of an implicit atlas** to a set of indices `S` whose regular footprints
cover `X`: the relabelling along the inclusion `S ↪ A`. -/
noncomputable def restrict :
    ImplicitAtlas (fun α : S ↦ Γ α) (fun α : S ↦ E α) (fun α ↦ ρ α)
      (fun I ↦ T (I.map (Embedding.subtype (· ∈ S)))) (relabelAct act (Embedding.subtype _))
      X d :=
  𝒜.relabel (f := Embedding.subtype (· ∈ S)) (by rwa [Embedding.coe_subtype, Subtype.range_coe])

/-- The restriction of `𝒜` to `S` is its relabelling along the inclusion `S ↪ A`. -/
theorem restrict_eq_relabel (h : 𝒜.FootprintsCover (range (Embedding.subtype (· ∈ S)))) :
    𝒜.restrict S hS = 𝒜.relabel h :=
  (rfl)

/-- The restriction of `𝒜` has the identification `X_∅ ≃ₜ X` of `𝒜`. -/
@[simp]
theorem baseHomeomorph_restrict : (𝒜.restrict S hS).baseHomeomorph = 𝒜.baseHomeomorph :=
  (rfl)

/-- The Kuranishi map of `α` on `X_J` in the restriction of `𝒜` is that of `α` in `𝒜`. -/
@[simp]
theorem kuranishi_restrict_apply (J : Finset S) (α : J)
    (x : T (J.map (Embedding.subtype (· ∈ S)))) :
    (𝒜.restrict S hS).kuranishi J α x =
      𝒜.kuranishi (J.map (Embedding.subtype (· ∈ S)))
        ⟨α.val.val, Finset.mem_map_of_mem _ α.property⟩ x :=
  (rfl)

/-- The regular locus of `I` in the restriction of `𝒜` is the regular locus of `I` in `𝒜`. -/
@[simp]
theorem regLocus_restrict (I : Finset S) :
    (𝒜.restrict S hS).regLocus I = 𝒜.regLocus (I.map (Embedding.subtype (· ∈ S))) :=
  (rfl)

/-- The zero sets of the restriction of `𝒜` are the zero sets of `𝒜`. -/
theorem kuranishiZeroSet_restrict (I J : Finset S) :
    kuranishiZeroSet (T := fun J ↦ T (J.map (Embedding.subtype (· ∈ S))))
        (E := fun α : S ↦ E α) (𝒜.restrict S hS).kuranishi I J =
      kuranishiZeroSet 𝒜.kuranishi (I.map (Embedding.subtype (· ∈ S)))
        (J.map (Embedding.subtype (· ∈ S))) :=
  𝒜.kuranishiZeroSet_relabelKuranishi _ I J

/-- The footprint maps of the restriction of `𝒜` are the footprint maps of `𝒜`. -/
@[simp]
theorem footprintMap_restrict {I J : Finset S} (h : I ⊆ J)
    (x : kuranishiZeroSet (T := fun J ↦ T (J.map (Embedding.subtype (· ∈ S))))
      (E := fun α : S ↦ E α) (𝒜.restrict S hS).kuranishi I J) :
    (𝒜.restrict S hS).footprintMap h x =
      𝒜.footprintMap (Finset.map_subset_map.2 h)
        ⟨x.val, 𝒜.kuranishiZeroSet_restrict S hS I J ▸ x.property⟩ :=
  (rfl)

/-- The regular footprint of `I` in the restriction of `𝒜` is the regular footprint of `I` in
`𝒜`. -/
@[simp]
theorem footprint_restrict (I : Finset S) :
    (𝒜.restrict S hS).footprint I = 𝒜.footprint (I.map (Embedding.subtype (· ∈ S))) :=
  𝒜.footprint_relabel _ I

end Restrict

end TauCeti.ImplicitAtlas
