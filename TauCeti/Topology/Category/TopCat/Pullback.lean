/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.Topology.Category.TopCat.Fiber

/-!
# Pullbacks in `TopCat`

A commutative square of topological spaces whose top horizontal map is an embedding and whose
bottom horizontal map is injective is a pullback when the range of the top map is the preimage of
the range of the bottom one. This range criterion is useful for geometric constructions presented
as embedded open subspaces.

The base change `TopCat.pullbackFst g p` of a morphism `p : E ⟶ B` along `g : B' ⟶ B` has the
same fibres as `p`: its fibre over `b'` is the fibre of `p` over `g b'`
(`TopCat.Hom.fiberPullbackFstIso`, identified with the square's induced fibre map by
`CategoryTheory.CommSq.fiberMap_pullbackSnd`). A map `f` over `B` induces a map of base changes
(`TopCat.pullbackMapOfCompEq`), which is `f` on these fibres
(`TopCat.Hom.fiberPullbackFstIso_hom_naturality`).
The inclusion `e ↦ (k, e)` of a fibre of `p` into the base change along `g` at a point `k` over
it is `TopCat.Hom.pullbackFiberι`. A map of fibrations over a map of bases, with a compatible map
of parameter spaces, induces a map of base changes (`CategoryTheory.CommSq.pullbackMapOfCompEq`),
which is the map of fibres on these fibre inclusions
(`CategoryTheory.CommSq.pullbackFiberι_comp_pullbackMapOfCompEq`); for the identity of the
parameter space and of the base it is `TopCat.pullbackMapOfCompEq`
(`CategoryTheory.CommSq.pullbackMapOfCompEq_id_eq_topCatPullbackMapOfCompEq`).
-/

public section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace TauCeti.TopCat

universe u

/-- A commutative square whose top horizontal map is an embedding and whose bottom horizontal map
is injective is a pullback when the range of the top map is the preimage of the range of the bottom
map. -/
theorem isPullback_of_isEmbedding_of_range_eq_preimage
    {P X Y Z : TopCat.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hfst : IsEmbedding fst) (hg : Function.Injective g) (hcomm : fst ≫ f = snd ≫ g)
    (hrange : range fst = f ⁻¹' range g) : IsPullback fst snd f g := by
  have mem_range_fst (s : PullbackCone f g) (x : s.pt) : s.fst x ∈ range fst := by
    rw [hrange]
    exact ⟨s.snd x, (CategoryTheory.congr_fun s.condition x).symm⟩
  let lift (s : PullbackCone f g) : s.pt ⟶ P := TopCat.ofHom
    { toFun := fun x ↦ Classical.choose (mem_range_fst s x)
      continuous_toFun := hfst.isInducing.continuous_iff.mpr (by
        convert s.fst.hom.continuous using 1
        funext x
        exact Classical.choose_spec (mem_range_fst s x)) }
  have lift_fst (s : PullbackCone f g) : lift s ≫ fst = s.fst := by
    ext x
    exact Classical.choose_spec (mem_range_fst s x)
  have lift_snd (s : PullbackCone f g) : lift s ≫ snd = s.snd := by
    ext x
    apply hg
    have h : lift s ≫ snd ≫ g = s.snd ≫ g := by
      rw [← hcomm, ← Category.assoc, lift_fst, s.condition]
    exact CategoryTheory.congr_fun h x
  refine IsPullback.of_isLimit' ⟨hcomm⟩
    (PullbackCone.IsLimit.mk hcomm lift lift_fst lift_snd ?_)
  intro s m hm _
  ext x
  apply hfst.injective
  exact CategoryTheory.congr_fun (hm.trans (lift_fst s).symm) x

end TauCeti.TopCat

namespace TopCat

universe u

variable {E E' B B' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B} {f : E ⟶ E'}

/-- The map `B' ×_B E ⟶ B' ×_B E'` of the base changes along `g : B' ⟶ B` induced by a map `f`
over `B`, that is with `f ≫ p' = p`. -/
def pullbackMapOfCompEq (g : B' ⟶ B) (hf : f ≫ p' = p) :
    TopCat.of { x : B' × E // g x.1 = p x.2 } ⟶ TopCat.of { x : B' × E' // g x.1 = p' x.2 } :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x.val.1, f x.val.2), x.property.trans (ConcreteCategory.congr_hom hf
      x.val.2).symm⟩,
    (by fun_prop : Continuous fun x : { x : B' × E // g x.1 = p x.2 } ↦ (x.val.1, f x.val.2)
      ).subtype_mk _⟩

@[simp]
lemma coe_pullbackMapOfCompEq_apply (g : B' ⟶ B) (hf : f ≫ p' = p)
    (x : TopCat.of { x : B' × E // g x.1 = p x.2 }) :
    (pullbackMapOfCompEq g hf x : B' × E') = (x.val.1, f x.val.2) :=
  (rfl)

@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackFst (g : B' ⟶ B) (hf : f ≫ p' = p) :
    pullbackMapOfCompEq g hf ≫ pullbackFst g p' = pullbackFst g p :=
  (rfl)

@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackSnd (g : B' ⟶ B) (hf : f ≫ p' = p) :
    pullbackMapOfCompEq g hf ≫ pullbackSnd g p' = pullbackSnd g p ≫ f :=
  (rfl)

@[simp]
lemma pullbackMapOfCompEq_id (g : B' ⟶ B) (hf : 𝟙 E ≫ p = p) :
    pullbackMapOfCompEq (f := 𝟙 E) g hf = 𝟙 _ :=
  (rfl)

/-- The maps of base changes induced by maps over `B` compose. It is stated in this direction so
that `simp` can use it: the middle map `p'` cannot be recovered from the composite. -/
@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackMapOfCompEq {E'' : TopCat.{u}} {p'' : E'' ⟶ B}
    {f' : E' ⟶ E''} (g : B' ⟶ B) (hf : f ≫ p' = p) (hf' : f' ≫ p'' = p') :
    pullbackMapOfCompEq g hf ≫ pullbackMapOfCompEq g hf' =
      pullbackMapOfCompEq (f := f ≫ f') g (by rw [Category.assoc, hf', hf]) :=
  (rfl)

end TopCat

namespace TopCat.Hom

universe u

variable {E B B' : TopCat.{u}}

/-- The fibre of the base change of `p` along `g : B' ⟶ B` over `b'` is the fibre of `p` over
`g b'`. -/
def fiberPullbackFstIso (p : E ⟶ B) (g : B' ⟶ B) (b' : B') :
    (TopCat.pullbackFst g p).fiber b' ≅ p.fiber (g b') :=
  TopCat.isoOfHomeo
    { toFun x := ⟨x.val.val.2, by
        rw [Set.mem_preimage, Set.mem_singleton_iff, ← x.val.property]
        exact congrArg g x.property⟩
      invFun e := ⟨⟨(b', e.val), e.property.symm⟩, rfl⟩
      left_inv x := Subtype.ext (Subtype.ext (Prod.ext x.property.symm rfl))
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

@[reassoc (attr := simp)]
lemma fiberPullbackFstIso_hom_comp_fiberι (p : E ⟶ B) (g : B' ⟶ B) (b' : B') :
    (p.fiberPullbackFstIso g b').hom ≫ p.fiberι (g b') =
      (TopCat.pullbackFst g p).fiberι b' ≫ TopCat.pullbackSnd g p := by
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberι_apply, fiberι_apply]
  rfl

-- Not `@[simp]`: the reducible `TopCat.pullbackFst` in the fibre's type is unfolded when
-- indexing, so `simp` never matches the left-hand sides of these two lemmas; use `rw` instead.
lemma fiberPullbackFstIso_hom_apply_coe (p : E ⟶ B) (g : B' ⟶ B) (b' : B')
    (x : (TopCat.pullbackFst g p).fiber b') :
    ((p.fiberPullbackFstIso g b').hom x : E) = x.val.val.2 := (rfl)

lemma fiberPullbackFstIso_inv_apply_coe (p : E ⟶ B) (g : B' ⟶ B) (b' : B') (x : p.fiber (g b')) :
    ((p.fiberPullbackFstIso g b').inv x : ↑(TopCat.of { q : B' × E // g q.1 = p q.2 })) =
      ⟨(b', x.val), x.property.symm⟩ := (rfl)

/-- The inclusion `e ↦ (k, e)` of the fibre of `p` over `b` into the base change
`{(k, e) | g k = p e}` of `p` along `g : K ⟶ B`, at a point `k` of `K` over `b`. For `b = g k` it
is the inclusion of the fibre of the base change over `k`, read through
`TopCat.Hom.fiberPullbackFstIso`; the equation `g k = b` lets the fibre be named by its point of
`B`, as for the end points of a path. -/
def pullbackFiberι {K : TopCat.{u}} (p : E ⟶ B) (g : K ⟶ B) {k : K} {b : B}
    (h : g k = b) : p.fiber b ⟶ TopCat.of {x : K × E // g x.1 = p x.2} :=
  TopCat.ofHom ⟨fun e ↦ ⟨(k, e.val), h.trans (e.property : p e.val = b).symm⟩, by fun_prop⟩

/-- The inclusion of a fibre into a base change sends `e` to `(k, e)`. -/
@[simp]
lemma coe_pullbackFiberι_apply {K : TopCat.{u}} (p : E ⟶ B) (g : K ⟶ B) {k : K} {b : B}
    (h : g k = b) (e : p.fiber b) : (p.pullbackFiberι g h e : K × E) = (k, e.val) :=
  (rfl)

/-- The inclusion of a fibre into a base change at `k`, followed by the projection to the parameter
space, is constant at `k`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberι_comp_pullbackFst {K : TopCat.{u}} (p : E ⟶ B) (g : K ⟶ B) {k : K} {b : B}
    (h : g k = b) : p.pullbackFiberι g h ≫ TopCat.pullbackFst g p = TopCat.const k :=
  (rfl)

/-- The inclusion of a fibre into a base change, followed by the projection to the total space, is
the inclusion of the fibre. -/
@[reassoc (attr := simp)]
lemma pullbackFiberι_comp_pullbackSnd {K : TopCat.{u}} (p : E ⟶ B) (g : K ⟶ B) {k : K} {b : B}
    (h : g k = b) : p.pullbackFiberι g h ≫ TopCat.pullbackSnd g p = p.fiberι b := by
  ext e
  rw [ConcreteCategory.comp_apply, fiberι_apply, TopCat.pullbackSnd_apply,
    coe_pullbackFiberι_apply]

/-- The inclusion of the fibre of `p` over `g k` into the base change of `p` along `g`, at `k`, is
the inclusion of the fibre of the base change over `k`, read through
`TopCat.Hom.fiberPullbackFstIso`. -/
lemma pullbackFiberι_eq_fiberPullbackFstIso_inv_comp_fiberι {K : TopCat.{u}} (p : E ⟶ B)
    (g : K ⟶ B) (k : K) :
    p.pullbackFiberι g (rfl : g k = g k) =
      (p.fiberPullbackFstIso g k).inv ≫ (TopCat.pullbackFst g p).fiberι k := by
  ext e <;>
  · rw [ConcreteCategory.comp_apply, fiberι_apply, fiberPullbackFstIso_inv_apply_coe]
    rfl

/-- The identifications `TopCat.Hom.fiberPullbackFstIso` of the fibres of base changes are natural
in maps over the base: on fibres, the map of base changes induced by `f` is the map of fibres
induced by `f`. -/
@[reassoc]
lemma fiberPullbackFstIso_hom_naturality {E' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B}
    {f : E ⟶ E'} (g : B' ⟶ B) (sq : CommSq f p p' (𝟙 B))
    (sq' : CommSq (TopCat.pullbackMapOfCompEq g (sq.w.trans (Category.comp_id p)))
      (TopCat.pullbackFst g p) (TopCat.pullbackFst g p') (𝟙 B')) (b' : B') :
    sq'.fiberMap b' ≫ (p'.fiberPullbackFstIso g b').hom =
      (p.fiberPullbackFstIso g b').hom ≫ sq.fiberMap (g b') := by
  -- `rw` cannot see through the base point `(𝟙 B') b'` of the fibre map, so compare the points of
  -- `E'` directly: both sides send `x` to `f x.1.1.2`.
  ext x
  exact (congrArg (fun y : TopCat.of { x : B' × E' // g x.1 = p' x.2 } ↦ y.val.2)
    (sq'.fiberMap_apply_coe b' x)).trans
    (sq.fiberMap_apply_coe (g b') ((p.fiberPullbackFstIso g b').hom x)).symm

end TopCat.Hom

namespace CategoryTheory.CommSq

universe u

variable {E E' B B' K K' : TopCat.{u}} {f : E ⟶ E'} {p : E ⟶ B} {p' : E' ⟶ B'} {g : B ⟶ B'}

/-- The map `(k, e) ↦ (φ k, f e)` from the base change of `p` along `h : K ⟶ B` to the base change
of `p'` along `h' : K' ⟶ B'`, induced by a map of fibrations, that is, a commutative square from
`p` to `p'` over `g`, and a map `φ : K ⟶ K'` of parameter spaces compatible with `g`. For
`φ = 𝟙` and `g = 𝟙` it is `TopCat.pullbackMapOfCompEq`. -/
def pullbackMapOfCompEq (sq : CommSq f p p' g) {h : K ⟶ B} {h' : K' ⟶ B'} (φ : K ⟶ K')
    (hφ : φ ≫ h' = h ≫ g) :
    TopCat.of {x : K × E // h x.1 = p x.2} ⟶ TopCat.of {x : K' × E' // h' x.1 = p' x.2} :=
  TopCat.ofHom ⟨fun x ↦ ⟨(φ x.val.1, f x.val.2), (ConcreteCategory.congr_hom hφ x.val.1).trans
      ((congrArg g x.property).trans (ConcreteCategory.congr_hom sq.w x.val.2).symm)⟩,
    (by fun_prop : Continuous fun x : {x : K × E // h x.1 = p x.2} ↦ (φ x.val.1, f x.val.2)
      ).subtype_mk _⟩

@[simp]
lemma coe_pullbackMapOfCompEq_apply (sq : CommSq f p p' g) {h : K ⟶ B} {h' : K' ⟶ B'}
    (φ : K ⟶ K') (hφ : φ ≫ h' = h ≫ g) (x : TopCat.of {x : K × E // h x.1 = p x.2}) :
    (sq.pullbackMapOfCompEq φ hφ x : K' × E') = (φ x.val.1, f x.val.2) :=
  (rfl)

@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackFst (sq : CommSq f p p' g) {h : K ⟶ B} {h' : K' ⟶ B'}
    (φ : K ⟶ K') (hφ : φ ≫ h' = h ≫ g) :
    sq.pullbackMapOfCompEq φ hφ ≫ TopCat.pullbackFst h' p' = TopCat.pullbackFst h p ≫ φ :=
  (rfl)

@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackSnd (sq : CommSq f p p' g) {h : K ⟶ B} {h' : K' ⟶ B'}
    (φ : K ⟶ K') (hφ : φ ≫ h' = h ≫ g) :
    sq.pullbackMapOfCompEq φ hφ ≫ TopCat.pullbackSnd h' p' = TopCat.pullbackSnd h p ≫ f :=
  (rfl)

/-- For a map `f` over `B` and the identity of the parameter space, the map of base changes is
`TopCat.pullbackMapOfCompEq`. -/
@[simp]
lemma pullbackMapOfCompEq_id_eq_topCatPullbackMapOfCompEq {p' : E' ⟶ B}
    (sq : CommSq f p p' (𝟙 B)) (h : K ⟶ B) (hφ : 𝟙 K ≫ h = h ≫ 𝟙 B) :
    sq.pullbackMapOfCompEq (𝟙 K) hφ =
      TopCat.pullbackMapOfCompEq h (sq.w.trans (Category.comp_id p)) :=
  (rfl)

/-- The maps of base changes induced by maps of fibrations compose along horizontal composites of
squares. It is stated in this direction so that `simp` can use it: the middle square and parameter
space cannot be recovered from the composite. -/
@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackMapOfCompEq {E'' B'' K'' : TopCat.{u}} {f' : E' ⟶ E''}
    {p'' : E'' ⟶ B''} {g' : B' ⟶ B''} (sq : CommSq f p p' g) (sq' : CommSq f' p' p'' g')
    {h : K ⟶ B} {h' : K' ⟶ B'} {h'' : K'' ⟶ B''} (φ : K ⟶ K') (φ' : K' ⟶ K'')
    (hφ : φ ≫ h' = h ≫ g) (hφ' : φ' ≫ h'' = h' ≫ g') :
    sq.pullbackMapOfCompEq φ hφ ≫ sq'.pullbackMapOfCompEq φ' hφ' =
      (sq.horiz_comp sq').pullbackMapOfCompEq (φ ≫ φ')
        (by rw [Category.assoc, hφ', reassoc_of% hφ]) :=
  (rfl)

/-- On fibres, the map of base changes induced by a map of fibrations is the map of fibres: the
inclusion of the fibre over `b` at `k`, followed by the map of base changes, is the map of fibres
followed by the inclusion of the fibre over `g b` at `φ k`. -/
@[reassoc]
lemma pullbackFiberι_comp_pullbackMapOfCompEq (sq : CommSq f p p' g) {h : K ⟶ B}
    {h' : K' ⟶ B'} (φ : K ⟶ K') (hφ : φ ≫ h' = h ≫ g) {k : K} {b : B} (hk : h k = b)
    (hk' : h' (φ k) = g b) :
    p.pullbackFiberι h hk ≫ sq.pullbackMapOfCompEq φ hφ =
      sq.fiberMap b ≫ p'.pullbackFiberι h' hk' := by
  ext x
  · rfl
  · exact (sq.fiberMap_apply_coe b x).symm

/-- The map on fibres over `b'` induced by the canonical pullback square of `p : E ⟶ B` along
`g : B' ⟶ B` is the canonical isomorphism `p.fiberPullbackFstIso g b'`. -/
lemma fiberMap_pullbackSnd {E B B' : TopCat.{u}} {p : E ⟶ B} {g : B' ⟶ B}
    (sq : CommSq (TopCat.pullbackSnd g p) (TopCat.pullbackFst g p) p g) (b' : B') :
    sq.fiberMap b' = (p.fiberPullbackFstIso g b').hom := by
  ext x
  exact (sq.fiberMap_apply_coe b' x).trans
    ((TopCat.pullbackSnd_apply g p x.val).trans (p.fiberPullbackFstIso_hom_apply_coe g b' x).symm)

end CategoryTheory.CommSq
