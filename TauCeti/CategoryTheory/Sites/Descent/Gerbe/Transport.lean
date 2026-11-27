/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.AutTransport
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.LocalCovers

/-!
# Transport of automorphisms between objects of a gerbe with abelian inertia

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a gerbe for a Grothendieck topology `J` all of whose
automorphism groups are commutative. Any two objects `x y` over `V` are isomorphic on their
isomorphism cover, a covering sieve (`GerbeLocalCovers.isomCover_mem`), so transport of
automorphisms along local isomorphisms (`GerbeAutTransport.conjugateCoverAut`) on that cover gives
a homomorphism `Aut x →* Aut y` (`GerbeAutTransport.isomCoverTransport`). It is independent of the
covering sieve and of the local isomorphisms used
(`GerbeAutTransport.isomCoverTransport_eq_conjugateCoverAut`), so it is canonical. This is the
identification of all automorphism groups of a gerbe with abelian inertia in the Stacks Project,
Lemma 8.11.8 (tag 0CJY).

## Main definitions

* `GerbeLocalCovers.isomCoverIsos`: chosen local isomorphisms on the isomorphism cover.
* `GerbeAutTransport.isomCoverTransport`: transport `Aut x →* Aut y` between objects over one
  base.

## Main results

* `GerbeAutTransport.isomCoverTransport_eq_conjugateCoverAut`: any cover and local isomorphisms.
* `GerbeAutTransport.isomCoverTransport_of_iso`: conjugation along a global isomorphism.
* `GerbeAutTransport.isomCoverTransport_self`, `GerbeAutTransport.isomCoverTransport_comp`: the
  identity and composition laws.
* `GerbeAutTransport.isomCoverTransport_naturality`, `GerbeAutTransport.mapAut_isomCoverTransport`
  (base change) and `GerbeAutTransport.isomCoverTransport_mapAut_comp` (across the composite
  pullback isomorphism `(g ≫ f)^* ≅ g^* f^*`).

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

namespace GerbeLocalCovers

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- Chosen isomorphisms `i^* x ≅ i^* y` on the arrows `i` of the isomorphism cover of `x` and
`y`. -/
noncomputable def isomCoverIsos {V : C} (x y : F.obj (.mk (op V))) :
    GerbeAutTransport.LocalIsos (isomCover F x y) x y :=
  fun i ↦ ((mem_isomCover_iff x y i.obj.hom).1 i.property).some

end GerbeLocalCovers

namespace GerbeAutTransport

open GerbeLocalCovers

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (J : GrothendieckTopology C) [F.IsGerbe J]
  (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)

/-- **Transport** of automorphisms from `x` to `y` over the same base: transport along chosen local
isomorphisms on the isomorphism cover of `x` and `y`. -/
noncomputable def isomCoverTransport {V : C} (x y : F.obj (.mk (op V))) : Aut x →* Aut y :=
  conjugateCoverHom hF (isomCover_mem (J := J) x y) (isomCoverIsos x y)

/-- Unfolding of `GerbeAutTransport.isomCoverTransport`. -/
theorem isomCoverTransport_apply {V : C} (x y : F.obj (.mk (op V))) (a : Aut x) :
    isomCoverTransport J hF x y a =
      conjugateCoverAut hF (isomCover_mem (J := J) x y) (isomCoverIsos x y) a :=
  conjugateCoverHom_apply hF _ _ a

/-- Transport is transport along any local isomorphisms on any covering sieve. -/
theorem isomCoverTransport_eq_conjugateCoverAut {V : C} {x y : F.obj (.mk (op V))}
    {R : Sieve V} (hR : R ∈ J V) (e : LocalIsos R x y) (a : Aut x) :
    isomCoverTransport J hF x y a = conjugateCoverAut hF hR e a := by
  rw [isomCoverTransport_apply]
  exact conjugateCoverAut_cover_independent hF _ hR _ e a

/-- Transport along a global isomorphism `d : x ≅ y` is conjugation along `d`. -/
theorem isomCoverTransport_of_iso {V : C} {x y : F.obj (.mk (op V))} (d : x ≅ y) (a : Aut x) :
    isomCoverTransport J hF x y a = Aut.autMulEquivOfIso d a := by
  rw [isomCoverTransport_apply]
  exact conjugateCoverAut_of_iso hF _ _ d a

/-- Transport from `x` to itself is the identity. -/
@[simp]
theorem isomCoverTransport_self {V : C} (x : F.obj (.mk (op V))) (a : Aut x) :
    isomCoverTransport J hF x x a = a := by
  rw [isomCoverTransport_apply]
  exact conjugateCoverAut_self hF _ _ a

/-- **Composition of transports.** Transport from `x` to `y` followed by transport from `y` to `z`
is transport from `x` to `z`. -/
@[simp]
theorem isomCoverTransport_comp {V : C} (x y z : F.obj (.mk (op V))) (a : Aut x) :
    isomCoverTransport J hF y z (isomCoverTransport J hF x y a) =
      isomCoverTransport J hF x z a := by
  have hR := J.intersection_covering (isomCover_mem (J := J) x y) (isomCover_mem (J := J) y z)
  let e : LocalIsos (isomCover F x y ⊓ isomCover F y z) x y :=
    fun i ↦ isomCoverIsos x y ⟨i.obj, i.property.1⟩
  let d : LocalIsos (isomCover F x y ⊓ isomCover F y z) y z :=
    fun i ↦ isomCoverIsos y z ⟨i.obj, i.property.2⟩
  rw [isomCoverTransport_eq_conjugateCoverAut J hF hR e,
    isomCoverTransport_eq_conjugateCoverAut J hF hR d,
    isomCoverTransport_eq_conjugateCoverAut J hF hR fun i ↦ e i ≪≫ d i]
  exact conjugateCoverAut_comp hF hR e d _ a

/-- **Naturality of transport.** For `c : x₁ ≅ x₂`, `d : y₁ ≅ y₂` and automorphisms `a₁`, `a₂`
related by `c`, the transports are related by `d`. -/
theorem isomCoverTransport_naturality {V : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op V))} (c : x₁ ≅ x₂)
    (d : y₁ ≅ y₂) (a₁ : Aut x₁) (a₂ : Aut x₂)
    (ha : a₁.asIso.hom ≫ c.hom = c.hom ≫ a₂.asIso.hom) :
    (isomCoverTransport J hF x₁ y₁ a₁).asIso.hom ≫ d.hom =
      d.hom ≫ (isomCoverTransport J hF x₂ y₂ a₂).asIso.hom := by
  rw [isomCoverTransport_apply, isomCoverTransport_apply]
  exact conjugateCoverAut_naturality hF _ _ _ _ c d a₁ a₂ ha

/-- **Base change of transport.** Pullback along `g : W ⟶ V` carries the transport from `x` to `y`
to the transport from `g^* x` to `g^* y`. -/
theorem mapAut_isomCoverTransport {V W : C} (g : W ⟶ V) (x y : F.obj (.mk (op V))) (a : Aut x) :
    (F.map g.op.toLoc).toFunctor.mapAut y (isomCoverTransport J hF x y a) =
      isomCoverTransport J hF ((F.map g.op.toLoc).toFunctor.obj x)
        ((F.map g.op.toLoc).toFunctor.obj y) ((F.map g.op.toLoc).toFunctor.mapAut x a) := by
  rw [isomCoverTransport_apply, isomCoverTransport_apply]
  exact conjugateCoverAut_baseChange hF g _ _ _ _ a

/-- **Transport across a composite pullback.** Transporting `(g ≫ f)^* a` from `(g ≫ f)^* x` and
`g^* (f^* a)` from `g^* (f^* x)` to the same object `y` gives the same automorphism. -/
theorem isomCoverTransport_mapAut_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (.mk (op U))) (y : F.obj (.mk (op W))) (a : Aut x) :
    isomCoverTransport J hF ((F.map (g ≫ f).op.toLoc).toFunctor.obj x) y
        ((F.map (g ≫ f).op.toLoc).toFunctor.mapAut x a) =
      isomCoverTransport J hF
        ((F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x)) y
        ((F.map g.op.toLoc).toFunctor.mapAut _ ((F.map f.op.toLoc).toFunctor.mapAut x a)) := by
  have hfg : f.op.toLoc ≫ g.op.toLoc = (g ≫ f).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  -- The component at `x` of the composition isomorphism of `F`; its codomain
  -- `(F.map f ≫ F.map g).toFunctor.obj x` is `g^* (f^* x)` by definition of composition in `Cat`.
  let c : (F.map (g ≫ f).op.toLoc).toFunctor.obj x ≅
      (F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x) :=
    (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc hfg)).app x
  -- `c` relates `(g ≫ f)^* a` and `g^* (f^* a)`: this is the naturality of `F.mapComp'` at `a`.
  have ha : ((F.map (g ≫ f).op.toLoc).toFunctor.mapAut x a).asIso.hom ≫ c.hom =
      c.hom ≫ ((F.map g.op.toLoc).toFunctor.mapAut _
        ((F.map f.op.toLoc).toFunctor.mapAut x a)).asIso.hom := by
    simp only [c, Functor.mapAut_apply_asIso, Functor.mapIso_hom, Iso.app_hom,
      Cat.Hom.toNatIso_hom]
    exact F.mapComp'_hom_naturality f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc hfg a.asIso.hom
  refine Aut.ext (Iso.ext ?_)
  simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
    isomCoverTransport_naturality J hF c (Iso.refl y) _ _ ha

end GerbeAutTransport

end CategoryTheory.Pseudofunctor
