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
(`TopCat.Hom.fiberPullbackFstIso`). A map `f` over `B` induces a map of base changes
(`TopCat.pullbackMapOfCompEq`), which is `f` on these fibres
(`TopCat.Hom.fiberPullbackFstIso_hom_naturality`).
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
  TopCat.ofHom ⟨fun x ↦ ⟨(x.1.1, f x.1.2), x.2.trans (ConcreteCategory.congr_hom hf x.1.2).symm⟩,
    (by fun_prop : Continuous fun x : { x : B' × E // g x.1 = p x.2 } ↦ (x.1.1, f x.1.2)
      ).subtype_mk _⟩

@[simp]
lemma coe_pullbackMapOfCompEq_apply (g : B' ⟶ B) (hf : f ≫ p' = p)
    (x : TopCat.of { x : B' × E // g x.1 = p x.2 }) :
    (pullbackMapOfCompEq g hf x : B' × E') = (x.1.1, f x.1.2) :=
  (rfl)

@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackFst (g : B' ⟶ B) (hf : f ≫ p' = p) :
    pullbackMapOfCompEq g hf ≫ pullbackFst g p' = pullbackFst g p :=
  (rfl)

@[reassoc (attr := simp)]
lemma pullbackMapOfCompEq_comp_pullbackSnd (g : B' ⟶ B) (hf : f ≫ p' = p) :
    pullbackMapOfCompEq g hf ≫ pullbackSnd g p' = pullbackSnd g p ≫ f :=
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
    { toFun x := ⟨x.1.1.2, by
        rw [Set.mem_preimage, Set.mem_singleton_iff, ← x.1.2]
        exact congrArg g x.2⟩
      invFun e := ⟨⟨(b', e.1), e.2.symm⟩, rfl⟩
      left_inv x := Subtype.ext (Subtype.ext (Prod.ext x.2.symm rfl))
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
    ((p.fiberPullbackFstIso g b').hom x : E) = x.1.1.2 := (rfl)

lemma fiberPullbackFstIso_inv_apply_coe (p : E ⟶ B) (g : B' ⟶ B) (b' : B') (x : p.fiber (g b')) :
    ((p.fiberPullbackFstIso g b').inv x : ↑(TopCat.of { q : B' × E // g q.1 = p q.2 })) =
      ⟨(b', x.1), x.2.symm⟩ := (rfl)

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
  exact (congrArg (fun y : TopCat.of { x : B' × E' // g x.1 = p' x.2 } ↦ y.1.2)
    (sq'.fiberMap_apply_coe b' x)).trans
    (sq.fiberMap_apply_coe (g b') ((p.fiberPullbackFstIso g b').hom x)).symm

end TopCat.Hom
