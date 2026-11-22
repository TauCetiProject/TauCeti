/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import TauCeti.Topology.Algebra.Category.ProfiniteGrp.CofilteredLimit
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# The profinite completion of a pro-group

A small cofiltered diagram of groups `G : I ⥤ GrpCat` presents a pro-group. Its profinite
completion `TauCeti.proCompletion G` is the limit, in `ProfiniteGrp`, of the profinite
completions of the stages `G_i`. It is a genuine profinite group with its limit topology; it is
not the completion of the abstract inverse limit of the `G_i`, which can be much smaller. For
instance, the tower `ℤ ← ℤ ← ⋯` with all transition maps multiplication by `2` has trivial
abstract limit, while its completion is `∏_{ℓ ≠ 2} ℤ_ℓ`.

The completion has the universal property of the pro-group it completes, against profinite
targets. A continuous homomorphism from `proCompletion G` to a finite group comes from a
homomorphism out of a single stage, uniquely up to restriction to a later stage
(`TauCeti.proCompletion.homFiniteEquiv`):

`Hom_cont(proCompletion G, A) ≃ colim_i Hom(G_i, A)`.

A profinite group `H` is the limit of its finite quotients `H ⧸ N`, so continuous homomorphisms
into `H` are computed by the limit-colimit formula (`TauCeti.proCompletion.homEquiv`)

`Hom_cont(proCompletion G, H) ≃ lim_N colim_i Hom(G_i, H ⧸ N)`,

whose right-hand side is the formula for morphisms of pro-groups from `G` to the pro-group of
finite quotients of `H`.

## Main definitions

* `TauCeti.proCompletion G`: the profinite completion of the pro-group presented by `G`.
* `TauCeti.proCompletion.π G i`: its projection to the profinite completion of `G_i`.
* `TauCeti.proCompletion.homFiniteEquiv G A`: for a finite profinite group `A`, the bijection
  `Hom_cont(proCompletion G, A) ≃ colim_i Hom(G_i, A)`.
* `TauCeti.proCompletion.homEquiv G H`: for a profinite group `H`, the bijection
  `Hom_cont(proCompletion G, H) ≃ lim_N colim_i Hom(G_i, H ⧸ N)`.

## Main results

* `TauCeti.proCompletion.exists_π_comp_eq`: a continuous homomorphism to a finite group factors
  through the profinite completion of a stage.
* `TauCeti.proCompletion.π_comp_eq_π_comp_iff`: two such factorizations induce the same
  homomorphism exactly when they agree on a later stage.
* `TauCeti.proCompletion.homFiniteEquiv_comp`: naturality of `homFiniteEquiv` in the target.
* `TauCeti.proCompletion.homEquiv_π_apply`, `TauCeti.proCompletion.homEquiv_symm_apply_comp_proj`:
  the coordinates of `homEquiv` and of its inverse.

## References

* A. Schmidt and J. Stix, *Anabelian geometry with étale homotopy types*, Ann. of Math. 184
  (2016), discussion before Corollary 2.5.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace TauCeti

open ProfiniteGrp

/-- The quotient of a profinite group by an open normal subgroup is finite. -/
instance (H : ProfiniteGrp.{u}) (N : OpenNormalSubgroup H) : Finite (H.diagram.obj N) :=
  (H.toFiniteQuotientFunctor.obj N).isFinite

variable {I : Type u} [SmallCategory I]

/-- The profinite completion of the pro-group presented by a small diagram of groups `G`: the
limit in `ProfiniteGrp` of the profinite completions of the stages of `G`. -/
def proCompletion (G : I ⥤ GrpCat.{u}) : ProfiniteGrp.{u} :=
  Limits.limit (G ⋙ profiniteCompletion)

namespace proCompletion

variable (G : I ⥤ GrpCat.{u})

/-- The projection from the profinite completion of `G` to the profinite completion of its stage
`G_i`. -/
def π (i : I) : proCompletion G ⟶ profiniteCompletion.obj (G.obj i) :=
  limit.π (G ⋙ profiniteCompletion) i

/-- The projections commute with the completed transition maps. This is not a `simp` lemma:
`ProfiniteGrp.profiniteCompletion_map` rewrites its left-hand side. -/
@[reassoc]
theorem π_comp_map {i j : I} (a : i ⟶ j) :
    π G i ≫ profiniteCompletion.map (G.map a) = π G j :=
  limit.w (G ⋙ profiniteCompletion) a

/-- The cone of projections from the profinite completion of `G`. The body is exposed so that
its vertex and legs are definitionally `proCompletion G` and `π G i` in `cone_pt` and
`cone_π_app`. -/
@[expose]
def cone : Cone (G ⋙ profiniteCompletion) where
  pt := proCompletion G
  π :=
    { app := π G
      naturality := fun _ _ a ↦ (Category.id_comp (π G _)).trans (π_comp_map G a).symm }

@[simp]
theorem cone_pt : (cone G).pt = proCompletion G := (rfl)

@[simp]
theorem cone_π_app (i : I) : (cone G).π.app i = π G i := (rfl)

/-- The profinite completion of `G` is the limit of the profinite completions of its stages. -/
def isLimit : IsLimit (cone G) :=
  -- `cone G` is `limit.cone` with its legs renamed `π G i`.
  limit.isLimit (G ⋙ profiniteCompletion)

variable {G} in
/-- Morphisms into the profinite completion of `G` are determined by their projections. -/
@[ext]
theorem hom_ext {X : ProfiniteGrp.{u}} {f g : X ⟶ proCompletion G}
    (h : ∀ i, f ≫ π G i = g ≫ π G i) : f = g :=
  (isLimit G).hom_ext h

/-- Continuous homomorphisms into a profinite group `H` are the compatible families of
continuous homomorphisms into its finite quotients. -/
private def homLimitIso (H : ProfiniteGrp.{u}) :
    (proCompletion G ⟶ H) ≅ limit (H.diagram ⋙ coyoneda.obj (op (proCompletion G))) :=
  (isLimitOfPreserves (coyoneda.obj (op (proCompletion G))) H.isLimitCone).conePointUniqueUpToIso
    (limit.isLimit _)

@[reassoc]
private theorem homLimitIso_hom_π (H : ProfiniteGrp.{u}) (N : OpenNormalSubgroup H) :
    (homLimitIso G H).hom ≫ limit.π _ N =
      (coyoneda.obj (op (proCompletion G))).map (ProfiniteGrp.proj N) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ N

variable [IsCofiltered I]

section Finite

variable {A : ProfiniteGrp.{u}} [Finite A]

/-- Every continuous homomorphism from the profinite completion of `G` to a finite group factors
through the profinite completion of a stage of `G`. -/
theorem exists_π_comp_eq (f : proCompletion G ⟶ A) :
    ∃ (i : I) (g : profiniteCompletion.obj (G.obj i) ⟶ A), π G i ≫ g = f := by
  obtain ⟨i, g, hg⟩ := exists_comp_eq_of_isLimit.{u, u} (isLimit G) f.hom
  exact ⟨i, ofHom g, ProfiniteGrp.hom_ext hg⟩

/-- Two continuous homomorphisms from the profinite completion of a stage of `G` to a finite group
induce the same homomorphism on the profinite completion of `G` if and only if they agree on the
profinite completion of a later stage. -/
theorem π_comp_eq_π_comp_iff {i : I} (g g' : profiniteCompletion.obj (G.obj i) ⟶ A) :
    π G i ≫ g = π G i ≫ g' ↔ ∃ (k : I) (a : k ⟶ i),
      profiniteCompletion.map (G.map a) ≫ g = profiniteCompletion.map (G.map a) ≫ g' := by
  constructor
  · intro h
    obtain ⟨k, a, hk⟩ := exists_comp_map_eq_of_isLimit.{u, u} (isLimit G) (g := g.hom)
      (g' := g'.hom) (congrArg Hom.hom h)
    exact ⟨k, a, ProfiniteGrp.hom_ext hk⟩
  · rintro ⟨k, a, h⟩
    rw [← π_comp_map G a, Category.assoc, Category.assoc, h]

variable (A)

/-- The stage representatives of continuous homomorphisms from the profinite completion of `G` to
a finite group `A`, as a cocone over the diagram `i ↦ (G_i ⟶ A)`: a homomorphism `φ` out of `G_i`
represents its extension to the profinite completion of `G_i`, composed with `π G i`. -/
private def homFiniteCocone :
    Cocone (G.op ⋙ yoneda.obj ((forget₂ ProfiniteGrp GrpCat).obj A)) where
  pt := proCompletion G ⟶ A
  ι :=
    { app i := TypeCat.ofHom fun φ ↦
        π G i.unop ≫ (ProfiniteCompletion.adjunction.homEquiv _ _).symm φ
      naturality i k a := by
        ext φ
        simp [-profiniteCompletion_map, Adjunction.homEquiv_naturality_left_symm,
          π_comp_map_assoc] }

/-- `homFiniteCocone` is a colimit cocone. -/
private def isColimitHomFiniteCocone : IsColimit (homFiniteCocone G A) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun f ↦ by
      obtain ⟨i, g, rfl⟩ := exists_π_comp_eq G f
      exact ⟨op i, ProfiniteCompletion.adjunction.homEquiv _ _ g,
        (congrArg (π G i ≫ ·)
          ((ProfiniteCompletion.adjunction.homEquiv _ _).symm_apply_apply g)).symm⟩)
    (fun i φ φ' h ↦ by
      obtain ⟨k, a, hk⟩ := (π_comp_eq_π_comp_iff G _ _).mp h
      refine ⟨op k, a.op, (ProfiniteCompletion.adjunction.homEquiv _ _).symm.injective ?_⟩
      simpa [Adjunction.homEquiv_naturality_left_symm] using hk)

/-- For a finite profinite group `A`, continuous homomorphisms from the profinite completion of
`G` to `A` are the filtered colimit of homomorphisms from the stages of `G` to `A`. -/
def homFiniteEquiv :
    (proCompletion G ⟶ A) ≃ colimit (G.op ⋙ yoneda.obj ((forget₂ ProfiniteGrp GrpCat).obj A)) :=
  ((colimit.isColimit _).coconePointUniqueUpToIso (isColimitHomFiniteCocone G A)).toEquiv.symm

/-- The inverse of `homFiniteEquiv` sends the class of a stage homomorphism `φ` to its extension
to the profinite completion of the stage, composed with the projection. -/
@[simp]
theorem homFiniteEquiv_symm_ι {i : I} (φ : G.obj i ⟶ (forget₂ ProfiniteGrp GrpCat).obj A) :
    dsimp% (homFiniteEquiv G A).symm
        (colimit.ι (G.op ⋙ yoneda.obj ((forget₂ ProfiniteGrp GrpCat).obj A)) (op i) φ) =
      π G i ≫ (ProfiniteCompletion.adjunction.homEquiv _ _).symm φ :=
  ConcreteCategory.congr_hom ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimitHomFiniteCocone G A) (op i)) φ

/-- `homFiniteEquiv` sends `π G i ≫ g` to the class of the restriction of `g` to `G_i`. -/
@[simp]
theorem homFiniteEquiv_π_comp {i : I} (g : profiniteCompletion.obj (G.obj i) ⟶ A) :
    homFiniteEquiv G A (π G i ≫ g) =
      colimit.ι (G.op ⋙ yoneda.obj ((forget₂ ProfiniteGrp GrpCat).obj A)) (op i)
        (ProfiniteCompletion.adjunction.homEquiv _ _ g) := by
  rw [← Equiv.eq_symm_apply, homFiniteEquiv_symm_ι]
  simp

variable {A} in
/-- `homFiniteEquiv` is natural in the finite target: postcomposition with `h : A ⟶ B` becomes
postcomposition of stage homomorphisms with `h`. -/
theorem homFiniteEquiv_comp {B : ProfiniteGrp.{u}} [Finite B] (f : proCompletion G ⟶ A)
    (h : A ⟶ B) :
    homFiniteEquiv G B (f ≫ h) =
      colimMap (Functor.whiskerLeft G.op (yoneda.map ((forget₂ ProfiniteGrp GrpCat).map h)))
        (homFiniteEquiv G A f) := by
  obtain ⟨i, g, rfl⟩ := exists_π_comp_eq G f
  rw [Category.assoc, homFiniteEquiv_π_comp, homFiniteEquiv_π_comp,
    ← ConcreteCategory.comp_apply, ι_colimMap]
  simp [Adjunction.homEquiv_naturality_right]

end Finite

/-- `homFiniteEquiv` over the finite quotients `H ⧸ N` of a profinite group `H`, as a natural
isomorphism of functors of `N`. -/
private def homDiagramIso (H : ProfiniteGrp.{u}) :
    H.diagram ⋙ coyoneda.obj (op (proCompletion G)) ≅
      (H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim :=
  NatIso.ofComponents (fun N ↦ (homFiniteEquiv G (H.diagram.obj N)).toIso) (fun b ↦ by
    ext f
    exact homFiniteEquiv_comp G f (H.diagram.map b))

/-- The limit-colimit formula as an isomorphism of types. -/
private def homIso (H : ProfiniteGrp.{u}) :
    (proCompletion G ⟶ H) ≅
      limit ((H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim) :=
  homLimitIso G H ≪≫ lim.mapIso (homDiagramIso G H)

/-- Continuous homomorphisms from the profinite completion of `G` to a profinite group `H` are
computed by the limit-colimit formula `lim_N colim_i Hom(G_i, H ⧸ N)`, over the open normal
subgroups `N` of `H` and the stages `G_i` of `G`. -/
def homEquiv (H : ProfiniteGrp.{u}) :
    (proCompletion G ⟶ H) ≃
      limit ((H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim) :=
  (homIso G H).toEquiv

/-- The coordinate of `homEquiv G H f` at an open normal subgroup `N` of `H` is the class, under
`homFiniteEquiv`, of the composite of `f` with the projection `H → H ⧸ N`. -/
@[simp]
theorem homEquiv_π_apply (H : ProfiniteGrp.{u}) (f : proCompletion G ⟶ H)
    (N : OpenNormalSubgroup H) :
    dsimp% limit.π ((H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim) N (homEquiv G H f) =
      homFiniteEquiv G (H.diagram.obj N) (f ≫ ProfiniteGrp.proj N) := by
  have h : (homIso G H).hom ≫ limit.π ((H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim) N =
      (coyoneda.obj (op (proCompletion G))).map (ProfiniteGrp.proj N) ≫
        (homDiagramIso G H).hom.app N := by
    rw [homIso, Iso.trans_hom, Category.assoc, Functor.mapIso_hom, lim_map, limMap_π,
      homLimitIso_hom_π_assoc]
  exact ConcreteCategory.congr_hom h f

/-- The continuous homomorphism with given limit-colimit coordinates has, as its composite with
the projection `H → H ⧸ N`, the homomorphism represented by its coordinate at `N`. -/
@[simp]
theorem homEquiv_symm_apply_comp_proj (H : ProfiniteGrp.{u})
    (x : limit ((H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim)) (N : OpenNormalSubgroup H) :
    (homEquiv G H).symm x ≫ ProfiniteGrp.proj N =
      (homFiniteEquiv G (H.diagram.obj N)).symm
        (limit.π ((H.diagram ⋙ forget₂ ProfiniteGrp GrpCat ⋙ yoneda ⋙
          (Functor.whiskeringLeft _ _ _).obj G.op) ⋙ colim) N x) := by
  obtain ⟨f, rfl⟩ := (homEquiv G H).surjective x
  rw [Equiv.symm_apply_apply, homEquiv_π_apply, Equiv.symm_apply_apply]

end proCompletion

end TauCeti
