/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import TauCeti.AlgebraicGeometry.Cover.Directed
public import TauCeti.CategoryTheory.Adjunction.Representable
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Sites.Over

/-!
# Representability on the big Zariski site is local on the base

Let `S` be a scheme and `F` a presheaf of sets on the category `Over S` of schemes over `S` which
is a sheaf for the Zariski topology, for instance a sheaf on the big fppf site of `S`. This file
shows that representability of `F` is local on `S`: if `𝒰` is an open cover of `S` and, for every
`i`, the restriction `(Over.map (𝒰.f i)).op ⋙ F` of `F` to schemes over `𝒰.X i` is represented
by a scheme `Y i` over `𝒰.X i`, then `F` is represented by a scheme `X` over `S`
(`AlgebraicGeometry.Scheme.OpenCover.exists_hom_mem_nonempty_representableBy`). The structure
morphism `X ⟶ S` inherits every property local on the target shared by the morphisms
`Y i ⟶ 𝒰.X i`, such as being affine, quasi-compact or locally of finite type.

This extends representability results proved over affine bases to arbitrary bases. For instance,
a sheaf on the big fppf site which is represented by a scheme affine over the base after a single
surjective, flat, quasi-compact base change of finite presentation is represented by a scheme
affine over the base, by fppf descent. Over a base which is not quasi-compact, an fppf covering
family need not be refined by such a single morphism, but its restriction to every affine open
is, and the representing schemes over the affine opens glue by the result of this file.

## Implementation notes

The gluing is first carried out over a locally directed open cover whose index category is thin,
such as the cover of `S` by its affine opens. For `i ⟶ j`, the Yoneda lemma gives a morphism
`Y i ⟶ Y j` over `S` pulling the universal element of `F` over `Y j` back to the one over `Y i`;
it identifies `Y i` with the part of `Y j` over `𝒰.X i`. So the `Y i` form a relative gluing
datum (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), which glues to a scheme `X` over `S`.
By the Zariski sheaf property the universal elements glue to an element of `F` over `X`, and
pulling it back is a bijection from morphisms `T ⟶ X` over `S` to elements of `F` over `T`: the
inverse glues morphisms from the parts of `T` over the `𝒰.X i` to the pieces `Y i` of `X`. A
general open cover is refined to the locally directed cover of `S` by the opens contained in the
image of a member of the cover (`AlgebraicGeometry.Scheme.OpenCover.directedRefinement`). Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` proves the absolute form, for
Zariski sheaves on all schemes with a jointly surjective family of representable open
subfunctors; it does not apply directly to presheaves on `Over S`, whose restrictions to the
`𝒰.X i` are given here as representations over the smaller bases.

## References

* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ), the absolute form:
  a Zariski sheaf on schemes covered by representable open subfunctors is representable.
* [The Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH), relative gluing.
-/

public section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.Scheme.OpenCover

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type w}

section Gluing

variable {𝒰 : S.OpenCover} {Y : ∀ i, Over (𝒰.X i)}
  (e : ∀ i, ((Over.map (𝒰.f i)).op ⋙ F).RepresentableBy (Y i))

/-- The universal element of `F` over the scheme `Y i` representing `F` over `𝒰.X i`. -/
private noncomputable def univ (i : 𝒰.I₀) : F.obj (op ((Over.map (𝒰.f i)).obj (Y i))) :=
  (e i).homEquiv (𝟙 (Y i))

private theorem map_map_univ {i : 𝒰.I₀} {T : Over (𝒰.X i)} (b : T ⟶ Y i) :
    F.map ((Over.map (𝒰.f i)).map b).op (univ e i) = (e i).homEquiv b :=
  ((e i).homEquiv_eq b).symm

/-- Over a scheme `T` lying over `𝒰.X i`, every element of `F` is pulled back from the universal
element along a morphism to `Y i`. -/
private theorem exists_map_univ {i : 𝒰.I₀} {T : Over S} (c : T.left ⟶ 𝒰.X i)
    (hc : c ≫ 𝒰.f i = T.hom) (ζ : F.obj (op T)) :
    ∃ a : T ⟶ (Over.map (𝒰.f i)).obj (Y i), F.map a.op (univ e i) = ζ := by
  let ι := Over.mapMkIso c hc
  refine ⟨ι.inv ≫ (Over.map (𝒰.f i)).map ((e i).homEquiv.symm (F.map ι.hom.op ζ)), ?_⟩
  simp only [op_comp, F.map_comp_apply, map_map_univ, Equiv.apply_symm_apply]
  exact (F.mapIso ι.op).hom_inv_id_apply ζ

/-- Morphisms to `Y i` are determined by the pullback of the universal element. -/
private theorem map_univ_injective {i : 𝒰.I₀} {T : Over S}
    {a b : T ⟶ (Over.map (𝒰.f i)).obj (Y i)}
    (h : F.map a.op (univ e i) = F.map b.op (univ e i)) : a = b := by
  have ha : (a.left ≫ (Y i).hom) ≫ 𝒰.f i = T.hom := by simpa using Over.w a
  have hb : b.left ≫ (Y i).hom = a.left ≫ (Y i).hom := by
    rw [← cancel_mono (𝒰.f i), Category.assoc, ha]
    simpa using Over.w b
  let ι := Over.mapMkIso _ ha
  have key (m : T ⟶ (Over.map (𝒰.f i)).obj (Y i))
      (hm : m.left ≫ (Y i).hom = a.left ≫ (Y i).hom) : F.map m.op (univ e i) =
        F.map ι.inv.op ((e i).homEquiv (Over.homMk m.left hm : Over.mk _ ⟶ Y i)) := by
    rw [← map_map_univ, ← F.map_comp_apply, ← op_comp]
    congr 4
    ext
    simp [ι]
  rw [key a rfl, key b hb] at h
  have h' := congrArg (fun x ↦ F.map ι.hom.op x) h
  simp only [← F.map_comp_apply, ← op_comp, ι.hom_inv_id, op_id, F.map_id_apply] at h'
  have h'' := congrArg CommaMorphism.left ((e i).homEquiv.injective h')
  exact Over.OverMorphism.ext h''

/-- The part of a scheme `T` over `S` lying over `𝒰.X i`, with its inclusion into `T`. -/
private noncomputable abbrev pieceHom (T : Over S) (i : 𝒰.I₀) :
    Over.mk (pullback.fst T.hom (𝒰.f i) ≫ T.hom) ⟶ T :=
  Over.homMk (pullback.fst T.hom (𝒰.f i))

/-- For an element `ζ` of `F` over `T`, the morphism to `Y i` from the part of `T` over `𝒰.X i`
corresponding to the restriction of `ζ`. -/
private noncomputable def pieceLift {T : Over S} (ζ : F.obj (op T)) (i : 𝒰.I₀) :
    Over.mk (pullback.fst T.hom (𝒰.f i) ≫ T.hom) ⟶ (Over.map (𝒰.f i)).obj (Y i) :=
  (exists_map_univ e (pullback.snd T.hom (𝒰.f i)) pullback.condition.symm
    (F.map (pieceHom T i).op ζ)).choose

private theorem map_pieceLift_univ {T : Over S} (ζ : F.obj (op T)) (i : 𝒰.I₀) :
    F.map (pieceLift e ζ i).op (univ e i) = F.map (pieceHom T i).op ζ :=
  (exists_map_univ e (pullback.snd T.hom (𝒰.f i)) pullback.condition.symm _).choose_spec

variable [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- Over `i ⟶ j`, the scheme `Y i` maps to `Y j` by the morphism pulling back the universal
element of `Y j` to that of `Y i`. -/
private theorem exists_transition {i j : 𝒰.I₀} (hij : i ⟶ j) :
    ∃ a : (Over.map (𝒰.f i)).obj (Y i) ⟶ (Over.map (𝒰.f j)).obj (Y j),
      F.map a.op (univ e j) = univ e i :=
  exists_map_univ e ((Y i).hom ≫ 𝒰.trans hij) (by simp) (univ e i)

/-- The transition morphism `Y i ⟶ Y j` over `S`, for `i ⟶ j`. -/
private noncomputable def transition {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Over.map (𝒰.f i)).obj (Y i) ⟶ (Over.map (𝒰.f j)).obj (Y j) :=
  (exists_transition e hij).choose

private theorem map_transition_univ {i j : 𝒰.I₀} (hij : i ⟶ j) :
    F.map (transition e hij).op (univ e j) = univ e i :=
  (exists_transition e hij).choose_spec

private theorem transition_id (i : 𝒰.I₀) : transition e (𝟙 i) = 𝟙 _ :=
  map_univ_injective e (by rw [map_transition_univ, op_id, F.map_id_apply])

private theorem transition_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    transition e (hij ≫ hjk) = transition e hij ≫ transition e hjk :=
  map_univ_injective e (by
    simp only [op_comp, F.map_comp_apply, map_transition_univ])

private theorem transition_left_comp_hom {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (transition e hij).left ≫ (Y j).hom = (Y i).hom ≫ 𝒰.trans hij := by
  rw [← cancel_mono (𝒰.f j), Category.assoc, Category.assoc, 𝒰.trans_map]
  simpa using Over.w (transition e hij)

/-- Over `i ⟶ j`, the scheme `Y i` is the part of `Y j` over `𝒰.X i`. -/
private theorem isPullback_transition {i j : 𝒰.I₀} (hij : i ⟶ j) :
    IsPullback (transition e hij).left (Y i).hom (Y j).hom (𝒰.trans hij) := by
  -- A cone `(s.fst, s.snd)` is a morphism `s.fst` to `Y j` from the scheme `s.snd` over `𝒰.X i`;
  -- its lift to `Y i` is the morphism pulling back the universal element of `Y i` to the
  -- pullback of that of `Y j` along `s.fst`.
  have hs (s : PullbackCone (Y j).hom (𝒰.trans hij)) :
      s.fst ≫ ((Over.map (𝒰.f j)).obj (Y j)).hom = (Over.mk (s.snd ≫ 𝒰.f i)).hom := by
    simp [reassoc_of% s.condition]
  let l (s : PullbackCone (Y j).hom (𝒰.trans hij)) :=
    (exists_map_univ e (T := Over.mk (s.snd ≫ 𝒰.f i)) (i := i) s.snd rfl
      (F.map (Over.homMk s.fst (hs s)).op (univ e j))).choose
  have hl (s) : F.map (l s).op (univ e i) = F.map (Over.homMk s.fst (hs s)).op (univ e j) :=
    (exists_map_univ e (T := Over.mk (s.snd ≫ 𝒰.f i)) (i := i) s.snd rfl _).choose_spec
  have hl₁ (s) : l s ≫ transition e hij = Over.homMk s.fst (hs s) :=
    map_univ_injective e (by simp only [op_comp, F.map_comp_apply, map_transition_univ, hl])
  have hl₂ (s : PullbackCone (Y j).hom (𝒰.trans hij)) : (l s).left ≫ (Y i).hom = s.snd := by
    rw [← cancel_mono (𝒰.f i), Category.assoc]
    simpa using Over.w (l s)
  refine ⟨⟨transition_left_comp_hom e hij⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ (l s).left) (fun s ↦ congr($(hl₁ s).left)) hl₂ fun s m hm₁ hm₂ ↦ ?_⟩⟩
  have hm : m ≫ ((Over.map (𝒰.f i)).obj (Y i)).hom = (Over.mk (s.snd ≫ 𝒰.f i)).hom := by
    simp [← hm₂]
  have : Over.homMk m hm = l s := map_univ_injective e (by
    rw [hl, ← map_transition_univ e hij, ← F.map_comp_apply, ← op_comp]
    congr 3
    ext
    exact hm₁)
  exact congr($(this).left)

/-- The schemes `Y i` and the transition morphisms, as a diagram over the index category of the
cover. -/
private noncomputable def gluingFunctor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj i := (Y i).left
  map hij := (transition e hij).left
  map_id i := by rw [transition_id]; rfl
  map_comp hij hjk := by rw [transition_comp]; rfl

/-- The structure morphisms `Y i ⟶ 𝒰.X i`, as a natural transformation. -/
private noncomputable def gluingNatTrans : gluingFunctor e ⟶ 𝒰.functorOfLocallyDirected where
  app i := (Y i).hom
  naturality _ _ hij := transition_left_comp_hom e hij

/-- The relative gluing datum of the schemes `Y i`. -/
private noncomputable def gluingData : 𝒰.RelativeGluingData where
  functor := gluingFunctor e
  natTrans := gluingNatTrans e
  equifibered _ _ hij := isPullback_transition e hij

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The scheme over `S` glued from the `Y i`. -/
private noncomputable def glued : Over S :=
  Over.mk (gluingData e).toBase

/-- The inclusion of `Y i` into the glued scheme, over `S`. -/
private noncomputable def ιGlued (i : 𝒰.I₀) : (Over.map (𝒰.f i)).obj (Y i) ⟶ glued e :=
  Over.homMk (colimit.ι (gluingData e).functor i) ((gluingData e).ι_toBase i)

private theorem transition_ιGlued {i j : 𝒰.I₀} (hij : i ⟶ j) :
    transition e hij ≫ ιGlued e j = ιGlued e i :=
  Over.OverMorphism.ext (colimit.w (gluingData e).functor hij)

private theorem cancel_ιGlued {i : 𝒰.I₀} {T : Over S}
    {a b : T ⟶ (Over.map (𝒰.f i)).obj (Y i)} (h : a ≫ ιGlued e i = b ≫ ιGlued e i) : a = b := by
  have : IsOpenImmersion (ιGlued e i).left := (gluingData e).cover.map_prop i
  exact Over.OverMorphism.ext ((cancel_mono (ιGlued e i).left).mp congr($(h).left))

/-- A morphism to the glued scheme from a scheme lying over `𝒰.X i` factors through `Y i`. -/
private theorem exists_comp_ιGlued {i : 𝒰.I₀} {T : Over S} (c : T.left ⟶ 𝒰.X i)
    (hc : c ≫ 𝒰.f i = T.hom) (g : T ⟶ glued e) :
    ∃ b : T ⟶ (Over.map (𝒰.f i)).obj (Y i), b ≫ ιGlued e i = g := by
  have h := (gluingData e).isPullback_natTrans_ι_toBase i
  have w : c ≫ 𝒰.f i = g.left ≫ (gluingData e).toBase := hc.trans (Over.w g).symm
  refine ⟨Over.homMk (h.lift c g.left w) ?_, Over.OverMorphism.ext (h.lift_snd _ _ _)⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ 𝒰.f i) (h.lift_fst c g.left w)).trans hc)

/-- A morphism to `Y i` from a scheme lying over `𝒰.X l`, for `l ⟶ i`, factors through `Y l`,
and the two morphisms pull back the universal elements to the same element. -/
private theorem exists_map_univ_eq_of_hom {i l : 𝒰.I₀} (hli : l ⟶ i) {W : Over S}
    (c : W.left ⟶ 𝒰.X l) (hc : c ≫ 𝒰.f l = W.hom) (z : W ⟶ (Over.map (𝒰.f i)).obj (Y i)) :
    ∃ w : W ⟶ (Over.map (𝒰.f l)).obj (Y l),
      w ≫ ιGlued e l = z ≫ ιGlued e i ∧ F.map w.op (univ e l) = F.map z.op (univ e i) := by
  obtain ⟨w, hw⟩ := exists_map_univ e c hc (F.map z.op (univ e i))
  have : w ≫ transition e hli = z :=
    map_univ_injective e (by simp only [op_comp, F.map_comp_apply, map_transition_univ, hw])
  exact ⟨w, by rw [← this, Category.assoc, transition_ιGlued], hw⟩

private theorem trans_pieceLift_comp_ιGlued {T : Over S} (ζ : F.obj (op T))
    {i j : 𝒰.I₀} (hij : i ⟶ j) :
    Cover.trans (𝒰.pullback₁ T.hom) hij ≫ (pieceLift e ζ j ≫ ιGlued e j).left =
      (pieceLift e ζ i ≫ ιGlued e i).left := by
  have h : Cover.trans (𝒰.pullback₁ T.hom) hij ≫ pullback.fst T.hom (𝒰.f j) =
      pullback.fst T.hom (𝒰.f i) :=
    Cover.trans_map (𝒰.pullback₁ T.hom) hij
  let t : Over.mk (pullback.fst T.hom (𝒰.f i) ≫ T.hom) ⟶
      Over.mk (pullback.fst T.hom (𝒰.f j) ≫ T.hom) :=
    Over.homMk (Cover.trans (𝒰.pullback₁ T.hom) hij)
      ((Category.assoc _ _ _).symm.trans (h =≫ T.hom))
  have ht : t ≫ pieceHom T j = pieceHom T i := Over.OverMorphism.ext h
  have key : t ≫ pieceLift e ζ j = pieceLift e ζ i ≫ transition e hij :=
    map_univ_injective e (by
      simp only [← ht, op_comp, F.map_comp_apply, map_pieceLift_univ, map_transition_univ])
  have := congr(($key ≫ ιGlued e j).left)
  rw [Category.assoc, Category.assoc, transition_ιGlued] at this
  exact this

/-- The morphism to the glued scheme corresponding to an element of `F`, glued from the
morphisms `pieceLift` over the parts of `T` lying over the `𝒰.X i`. -/
private noncomputable def toGlued {T : Over S} (ζ : F.obj (op T)) : T ⟶ glued e :=
  OpenCover.glueMorphismsOverOfLocallyDirected (𝒰.pullback₁ T.hom)
    (fun i ↦ (pieceLift e ζ i ≫ ιGlued e i).left) (trans_pieceLift_comp_ιGlued e ζ)
    (fun i ↦ Over.w (pieceLift e ζ i ≫ ιGlued e i))

private theorem pieceHom_comp_toGlued {T : Over S} (ζ : F.obj (op T)) (i : 𝒰.I₀) :
    pieceHom T i ≫ toGlued e ζ = pieceLift e ζ i ≫ ιGlued e i :=
  Over.OverMorphism.ext
    (OpenCover.map_glueMorphismsOverOfLocallyDirected_left (𝒰.pullback₁ T.hom) _ _ _ i)

variable (hF : Presieve.IsSheaf (zariskiTopology.over S) F)
include hF

/-- Two morphisms to `Y i` and `Y j` that agree in the glued scheme pull back the universal
elements to the same element. -/
private theorem map_univ_eq_of_comp_ιGlued_eq {Z : Over S} {i j : 𝒰.I₀}
    {z₁ : Z ⟶ (Over.map (𝒰.f i)).obj (Y i)} {z₂ : Z ⟶ (Over.map (𝒰.f j)).obj (Y j)}
    (h : z₁ ≫ ιGlued e i = z₂ ≫ ιGlued e j) :
    F.map z₁.op (univ e i) = F.map z₂.op (univ e j) := by
  -- `Z` lies over `𝒰.X i ×_S 𝒰.X j`, which is covered by the `𝒰.X l` for `l ⟶ i` and
  -- `l ⟶ j`; over each of them both morphisms factor through the same morphism to `Y l`.
  let q : Z.left ⟶ pullback (𝒰.f i) (𝒰.f j) :=
    pullback.lift (z₁.left ≫ (Y i).hom) (z₂.left ≫ (Y j).hom)
      (by simpa using (Over.w z₁).trans (Over.w z₂).symm)
  let r (k : Σ l : 𝒰.I₀, (l ⟶ i) × (l ⟶ j)) : 𝒰.X k.1 ⟶ pullback (𝒰.f i) (𝒰.f j) :=
    pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  let π (k : Σ l : 𝒰.I₀, (l ⟶ i) × (l ⟶ j)) :
      Over.mk (pullback.fst q (r k) ≫ Z.hom) ⟶ Z :=
    Over.homMk (pullback.fst q (r k))
  -- The morphisms `π k` are the members of the base change along `q` of the cover of
  -- `𝒰.X i ×_S 𝒰.X j` by the `𝒰.X l`.
  have hπ : Sieve.ofArrows _ (fun k ↦ (π k).left) ∈ zariskiTopology Z.left :=
    Cover.mem_grothendieckTopology ((𝒰.intersectionOfLocallyDirected i j).pullback₁ q)
  refine (hF.isSheafFor_ofArrows_over π hπ).isSeparatedFor.ext ?_
  rintro _ _ ⟨k⟩
  have hc : pullback.snd q (r k) ≫ 𝒰.f k.1 = pullback.fst q (r k) ≫ Z.hom := by
    have h₂ : q ≫ pullback.fst _ _ ≫ 𝒰.f i = Z.hom := by simpa [q] using Over.w z₁
    rw [← h₂, pullback.condition_assoc]
    simp [r]
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_map_univ_eq_of_hom e k.2.1 _ hc (π k ≫ z₁)
  obtain ⟨w₂, hw₂, hw₂'⟩ := exists_map_univ_eq_of_hom e k.2.2 _ hc (π k ≫ z₂)
  have : w₁ = w₂ := cancel_ιGlued e (by rw [hw₁, hw₂, Category.assoc, Category.assoc, h])
  simp only [op_comp, F.map_comp_apply] at hw₁' hw₂'
  rw [← hw₁', ← hw₂', this]

/-- There is an element of `F` over the glued scheme restricting to the universal element over
each `Y i`. -/
private theorem exists_univGlued :
    ∃ ξ : F.obj (op (glued e)), ∀ i, F.map (ιGlued e i).op ξ = univ e i := by
  -- The members of the open cover of the glued scheme by the `Y i` are the morphisms `ιGlued e i`
  -- of the underlying schemes.
  obtain ⟨ξ, hξ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (hF.isSheafFor_ofArrows_over (ιGlued e) (gluingData e).cover.mem_grothendieckTopology) (univ e)
    fun i j Z z₁ z₂ h ↦ map_univ_eq_of_comp_ιGlued_eq e hF h
  exact ⟨ξ, hξ⟩

/-- The glued scheme represents `F`: a morphism `T ⟶ glued e` corresponds to the pullback of
the glued universal element. -/
private noncomputable def representableByGlued : F.RepresentableBy (glued e) where
  homEquiv {T} :=
    { toFun g := F.map g.op (exists_univGlued e hF).choose
      invFun := toGlued e
      left_inv g := by
        refine Over.OverMorphism.ext
          (Cover.hom_ext (𝒰.pullback₁ T.hom) _ _ fun (i : 𝒰.I₀) ↦ ?_)
        obtain ⟨b, hb⟩ := exists_comp_ιGlued e (pullback.snd T.hom (𝒰.f i))
          pullback.condition.symm (pieceHom T i ≫ g)
        have : pieceLift e (F.map g.op (exists_univGlued e hF).choose) i = b :=
          map_univ_injective e (by
            rw [map_pieceLift_univ, ← (exists_univGlued e hF).choose_spec i]
            simpa only [op_comp, F.map_comp_apply] using
              congr(F.map ($hb).op (exists_univGlued e hF).choose).symm)
        have h :=
          congr($(pieceHom_comp_toGlued e (F.map g.op (exists_univGlued e hF).choose) i).left)
        rw [this, hb] at h
        exact h
      right_inv ζ := by
        refine (hF.isSheafFor_ofArrows_over (pieceHom T)
          (Cover.mem_grothendieckTopology (𝒰.pullback₁ T.hom))).isSeparatedFor.ext ?_
        rintro _ _ ⟨i⟩
        simpa only [op_comp, F.map_comp_apply, (exists_univGlued e hF).choose_spec,
          map_pieceLift_univ] using
          congr(F.map ($(pieceHom_comp_toGlued e ζ i)).op (exists_univGlued e hF).choose) }
  homEquiv_comp f g := by simp

omit hF in
/-- The glued scheme has every property local on the target which all the `Y i` have. -/
private theorem glued_hom_mem (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ i, P (Y i).hom) : P (glued e).hom := by
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒰 fun i ↦ ?_
  have h := ((gluingData e).isPullback_natTrans_ι_toBase i).flip
  -- The structure morphism `natTrans.app i` of the gluing datum is `(Y i).hom` by definition.
  have h' : h.isoPullback.hom ≫ pullback.snd (gluingData e).toBase (𝒰.f i) = (Y i).hom :=
    h.isoPullback_hom_snd
  exact (P.cancel_left_of_respectsIso h.isoPullback.hom _).mp (h' ▸ hP i)

include e in
/-- Representability on the big Zariski site is local on the base, for a locally directed open
cover whose index category is thin. -/
private theorem exists_hom_mem_nonempty_representableBy_of_locallyDirected
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (hP : ∀ i, P (Y i).hom) :
    ∃ X : Over S, P X.hom ∧ Nonempty (F.RepresentableBy X) :=
  ⟨glued e, glued_hom_mem e P hP, ⟨representableByGlued e hF⟩⟩

end Gluing

/-- **Representability on the big Zariski site is local on the base.** Let `F` be a presheaf on
the category of schemes over `S` which is a sheaf for the Zariski topology, and let `𝒰` be an
open cover of `S`. If, for every `i`, the restriction of `F` to schemes over `𝒰.X i` is
represented by a scheme `Y i` over `𝒰.X i`, then `F` is represented by a scheme `X` over `S`.
Moreover `X ⟶ S` has every property `P` local on the target which all the morphisms
`Y i ⟶ 𝒰.X i` have; for instance `X` is affine over `S` if every `Y i` is affine over `𝒰.X i`.
Taking `P = ⊤` gives representability alone. This is the relative form of
[Stacks, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ). -/
theorem exists_hom_mem_nonempty_representableBy (𝒰 : S.OpenCover)
    (hF : Presieve.IsSheaf (zariskiTopology.over S) F) {Y : ∀ i, Over (𝒰.X i)}
    (e : ∀ i, ((Over.map (𝒰.f i)).op ⋙ F).RepresentableBy (Y i))
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (hP : ∀ i, P (Y i).hom) :
    ∃ X : Over S, P X.hom ∧ Nonempty (F.RepresentableBy X) := by
  -- Over an open `V` contained in the image of `𝒰.f i`, the part of `Y i` over `V` represents
  -- the restriction of `F`; these representations form the data over the directed refinement.
  let r := 𝒰.fromDirectedRefinement
  refine exists_hom_mem_nonempty_representableBy_of_locallyDirected (𝒰 := 𝒰.directedRefinement)
    (Y := fun V ↦ (Over.pullback (r.h₀ V)).obj (Y (r.s₀ V)))
    (fun V ↦ ((Over.mapPullbackAdj (r.h₀ V)).representableByComp (e (r.s₀ V))).ofIso
      (Functor.isoWhiskerRight
        (NatIso.op (Over.mapCongr _ _ (r.w₀ V).symm ≪≫ Over.mapComp _ _)) F))
    hF P fun V ↦ ?_
  have : IsOpenImmersion (r.h₀ V ≫ 𝒰.f (r.s₀ V)) := by rw [r.w₀]; infer_instance
  have : IsOpenImmersion (r.h₀ V) := .of_comp (r.h₀ V) (𝒰.f (r.s₀ V))
  exact IsZariskiLocalAtTarget.of_isPullback (iY := r.h₀ V)
    (IsPullback.of_hasPullback (Y (r.s₀ V)).hom (r.h₀ V)) (hP (r.s₀ V))

end AlgebraicGeometry.Scheme.OpenCover
