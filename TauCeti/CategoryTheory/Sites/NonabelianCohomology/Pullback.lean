/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map

/-!
# Pullback of torsors along a morphism of sites

Let `u : C ⥤ D` be a continuous and representably flat functor between sites `(C, J)` and
`(D, K)`, so that it defines a morphism of sites from `(D, K)` to `(C, J)`. Let `G` be a sheaf of
groups on `C`, `G'` a sheaf of groups on `D` and `φ : G ⟶ u_* G'` a morphism of sheaves of groups
to the pushforward of `G'`. For a `G`-torsor `P`, this file constructs the `G'`-torsor
`P.pullback φ`, the pullback `u^* P` of `P` with its structure group extended along the morphism
`u^* G ⟶ G'` adjoint to `φ`. It comes with a `φ`-equivariant morphism `P ⟶ u_* (P.pullback φ)`
which is universal among `φ`-equivariant morphisms from `P` to the pushforwards of
`G'`-torsors. When `G'` is the pullback `u^* G` and `φ` is the unit `G ⟶ u_* u^* G` of the
adjunction, this is the pullback of torsors along the morphism of sites; when `u` is the identity
functor, it is the contracted product `Torsor.map` (`NonabelianH1.pullback_eq_map`).

Over an object `V` of `D`, the sections of `P.pullback φ` are, before sheafification, the classes
of triples `(a, p, x)` with `a : V ⟶ u(U)`, `p` a section of `P` over `U` and `x` a section of
`G'` over `V`, standing for `x • a^* p`. Two triples are identified when they agree over a
common refinement `c` of `a` and `b`, up to the action of a section `g` of `G` over `c` and the
corresponding correction `x ↦ x * c^* φ(g)`. Since `u` is representably flat, any two such `a`
and `b` have a common refinement, and `G'` acts simply transitively on these classes.

## Main declarations

* `CategoryTheory.Sheaf.Torsor.pullback φ P`: the pullback of the `G`-torsor `P` along `φ`.
* `CategoryTheory.Sheaf.Torsor.toPullback φ P`: the `φ`-equivariant morphism
  `P ⟶ u_* (P.pullback φ)`, with `Torsor.toPullback_smul`.
* `CategoryTheory.Sheaf.Torsor.pullbackLift`: a `φ`-equivariant morphism `P ⟶ u_* R` to the
  pushforward of a `G'`-torsor `R` induces a morphism of `G'`-torsors `P.pullback φ ⟶ R`;
  `Torsor.pullback_hom_ext` is its uniqueness.
* `CategoryTheory.Sheaf.NonabelianH1.pullback φ`: the induced map `H¹(G) → H¹(G')`, with
  `NonabelianH1.pullback_mk_eq_mk_iff`, `NonabelianH1.pullback_one`,
  `NonabelianH1.pullback_comp` for a composite of morphisms of sites, the compatibilities
  `NonabelianH1.pullback_map` and `NonabelianH1.map_pullback` with `NonabelianH1.map`, and
  `NonabelianH1.pullback_eq_map`: along the identity functor, the pullback is `NonabelianH1.map`,
  so that `NonabelianH1.pullback_id` holds.
* `CategoryTheory.Sheaf.NonabelianH1.pullback_connecting_of_comp_eq`: the pullback of the torsor
  of lifts of a global section, for a morphism of group extensions to the pushforward of an
  extension on `D`, is the torsor of lifts of the corresponding global section.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG), for
  torsors under a sheaf of groups and their classes.
* J. Giraud, *Cohomologie non abélienne*, Chapitre III, for torsors, their contracted products
  and their inverse images under morphisms of sites.
* The sections before sheafification combine the colimit over `V ⟶ u(U)` defining the presheaf
  pullback, as in Mathlib's `CategoryTheory.Functor.sheafPullback` through the left Kan extension
  along `u.op`, with the contracted product with `G'` along `φ`.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}

namespace Torsor

section Construction

variable {u : C ⥤ D} [u.IsContinuous J K] {G : Sheaf J GrpCat.{w}} {G' : Sheaf K GrpCat.{w}}
  (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G') (P : Torsor G)

/-- The sections of the pushforward `u_* G'` act on those of the pushforward `u_* R` of a
`G'`-torsor `R`: over `U`, these are the sections of `G'` and `R` over `u(U)`. -/
instance (R : Torsor G') (U : Cᵒᵖ) :
    MulAction (((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G').obj.obj U)
      (((u.sheafPushforwardContinuous (Type w) J K).obj R.sheaf).obj.obj U) :=
  R.mulAction (u.op.obj U)

/-- The image in `G'(V)` of a section `g` of `G` over `a.right`, for `a : V ⟶ u(a.right)`: the
restriction along `a` of `φ(g) ∈ G'(u(a.right))`. -/
private def transport {V : D} (a : StructuredArrow V u) :
    G.obj.obj (op a.right) →* G'.obj.obj (op V) :=
  (φ.hom.app (op a.right) ≫ G'.obj.map a.hom.op).hom

private lemma transport_apply {V : D} (a : StructuredArrow V u) (g : G.obj.obj (op a.right)) :
    transport φ a g = G'.obj.map a.hom.op (φ.hom.app (op a.right) g) :=
  rfl

private lemma transport_map {V : D} {c a : StructuredArrow V u} (m : c ⟶ a)
    (g : G.obj.obj (op a.right)) :
    transport φ c (G.obj.map m.right.op g) = transport φ a g := by
  have h := NatTrans.naturality_apply φ.hom m.right.op g
  simp only [Functor.sheafPushforwardContinuous_obj_obj_map] at h
  rw [transport_apply, transport_apply, h, ← StructuredArrow.w m]
  simp only [Quiver.Hom.unop_op, op_comp, Functor.map_comp]
  exact (ConcreteCategory.comp_apply _ _ _).symm

/-- The restriction of a section of `P` along a morphism `m : c ⟶ a` of
`StructuredArrow V u`. -/
private def res {V : D} {c a : StructuredArrow V u} (m : c ⟶ a)
    (p : P.sheaf.obj.obj (op a.right)) : P.sheaf.obj.obj (op c.right) :=
  P.sheaf.obj.map m.right.op p

private lemma res_comp {V : D} {e c a : StructuredArrow V u} (k : e ⟶ c) (m : c ⟶ a)
    (p : P.sheaf.obj.obj (op a.right)) : res P (k ≫ m) p = res P k (res P m p) := by
  simp [res]

private lemma res_smul {V : D} {c a : StructuredArrow V u} (m : c ⟶ a)
    (g : G.obj.obj (op a.right)) (p : P.sheaf.obj.obj (op a.right)) :
    res P m (g • p) = G.obj.map m.right.op g • res P m p :=
  P.map_smul _ _ _

private lemma res_id {V : D} {a : StructuredArrow V u} (p : P.sheaf.obj.obj (op a.right)) :
    res P (𝟙 a) p = p := by
  simp [res]

variable (u G') in
/-- A representative `(a, p, x)` of a section of the pullback over `V`, standing for
`x • a^* p`. -/
private structure Rep (V : D) where
  /-- The morphism `a : V ⟶ u(U)`. -/
  arr : StructuredArrow V u
  /-- The section `p` of `P` over `U`. -/
  sec : P.sheaf.obj.obj (op arr.right)
  /-- The section `x` of `G'` over `V`. -/
  elt : G'.obj.obj (op V)

/-- The relation identifying two representatives which agree over a common refinement. -/
private def Rel (V : D) (x y : Rep u G' P V) : Prop :=
  ∃ (c : StructuredArrow V u) (m : c ⟶ x.arr) (n : c ⟶ y.arr) (g : G.obj.obj (op c.right)),
    res P m x.sec = g • res P n y.sec ∧ y.elt = x.elt * transport φ c g

variable [RepresentablyFlat u]

private lemma rel_equivalence (V : D) : _root_.Equivalence (Rel φ P V) where
  refl x := ⟨x.arr, 𝟙 _, 𝟙 _, 1, by simp, by simp⟩
  symm := by
    rintro x y ⟨c, m, n, g, h₁, h₂⟩
    refine ⟨c, n, m, g⁻¹, by rw [h₁, inv_smul_smul], ?_⟩
    rw [h₂, map_inv, mul_inv_cancel_right]
  trans := by
    rintro x y z ⟨c, m, n, g, h₁, h₂⟩ ⟨c', m', n', g', h₁', h₂'⟩
    -- Refine `c` and `c'` to a common `e` on which the two maps to `y.arr` agree.
    obtain ⟨e, l, r, hk⟩ := IsCofiltered.cospan n m'
    refine ⟨e, l ≫ m, r ≫ n', G.obj.map l.right.op g * G.obj.map r.right.op g', ?_, ?_⟩
    · rw [res_comp, h₁, res_smul, mul_smul, ← res_comp, hk, res_comp, h₁', res_smul, ← res_comp]
    · rw [h₂', h₂, map_mul, transport_map, transport_map, mul_assoc]

/-- The setoid of representatives of sections of the pullback over `V`. -/
private def relSetoid (V : D) : Setoid (Rep u G' P V) :=
  ⟨Rel φ P V, rel_equivalence φ P V⟩

/-- The sections of the pullback over `V` before sheafification, in a large universe. -/
private def Sec (V : D) : Type _ :=
  _root_.Quotient (relSetoid φ P V)

/-- The class of a representative `(a, p, x)`. -/
private def cls {V : D} (a : StructuredArrow V u) (p : P.sheaf.obj.obj (op a.right))
    (x : G'.obj.obj (op V)) : Sec φ P V :=
  _root_.Quotient.mk _ ⟨a, p, x⟩

private lemma cls_surjective {V : D} (s : Sec φ P V) : ∃ a p x, cls φ P a p x = s := by
  obtain ⟨x, rfl⟩ := _root_.Quotient.exists_rep s
  exact ⟨x.arr, x.sec, x.elt, rfl⟩

/-- A representative may be restricted along a morphism of `StructuredArrow V u`. -/
private lemma cls_res {V : D} {c a : StructuredArrow V u} (m : c ⟶ a)
    (p : P.sheaf.obj.obj (op a.right)) (x : G'.obj.obj (op V)) :
    cls φ P c (res P m p) x = cls φ P a p x :=
  _root_.Quotient.sound ⟨c, 𝟙 c, m, 1, by simp [res_id], by simp⟩

/-- Acting on the section of `P` in a representative is acting on the section of `G'`. -/
private lemma cls_smul {V : D} (a : StructuredArrow V u) (g : G.obj.obj (op a.right))
    (p : P.sheaf.obj.obj (op a.right)) (x : G'.obj.obj (op V)) :
    cls φ P a (g • p) x = cls φ P a p (x * transport φ a g) :=
  _root_.Quotient.sound ⟨a, 𝟙 a, 𝟙 a, g, by simp [res_id], rfl⟩

/-- Two sections of the pullback over `V` have representatives with the same `a` and `p`. -/
private lemma exists_eq_cls_and_eq_cls {V : D} (s₁ s₂ : Sec φ P V) :
    ∃ (c : StructuredArrow V u) (p : P.sheaf.obj.obj (op c.right)) (x₁ x₂ : G'.obj.obj (op V)),
      s₁ = cls φ P c p x₁ ∧ s₂ = cls φ P c p x₂ := by
  obtain ⟨a, p, x₁, rfl⟩ := cls_surjective φ P s₁
  obtain ⟨b, q, x₂, rfl⟩ := cls_surjective φ P s₂
  let m := IsCofiltered.minToLeft a b
  let n := IsCofiltered.minToRight a b
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G.obj.obj (op (IsCofiltered.min a b).right))
    (res P m p) (res P n q)
  refine ⟨_, res P m p, x₁, x₂ * transport φ _ g, (cls_res φ P m p x₁).symm, ?_⟩
  rw [← cls_smul, hg, cls_res]

/-- Representatives with the same `a` and `p` have the same class only if they agree. -/
private lemma eq_of_cls_eq_cls {V : D} {a : StructuredArrow V u}
    {p : P.sheaf.obj.obj (op a.right)} {x y : G'.obj.obj (op V)}
    (h : cls φ P a p x = cls φ P a p y) : x = y := by
  obtain ⟨c, m, n, g, h₁, h₂⟩ := _root_.Quotient.exact h
  dsimp only at m n h₁ h₂
  -- Equalise `m` and `n`; the section `g` then fixes a section of `P`, so it restricts to `1`.
  let k := IsCofiltered.eqHom m n
  have hk : k ≫ m = k ≫ n := IsCofiltered.eq_condition m n
  have hg : G.obj.map k.right.op g = 1 := by
    refine P.smul_left_injective (res P (k ≫ n) p) ?_
    dsimp only
    rw [one_smul, res_comp, ← res_smul, ← h₁, ← res_comp, ← res_comp, hk]
  rw [h₂, ← transport_map φ k, hg, map_one, mul_one]

variable (V : D)

/-- `G'(V)` acts on the sections of the pullback over `V` through the sections of `G'`. -/
private instance : MulAction (G'.obj.obj (op V)) (Sec φ P V) where
  smul b := _root_.Quotient.map (fun x ↦ ⟨x.arr, x.sec, b * x.elt⟩) (by
    rintro x y ⟨c, m, n, g, h₁, h₂⟩
    exact ⟨c, m, n, g, h₁, by simp [h₂, mul_assoc]⟩)
  one_smul s := by
    induction s using _root_.Quotient.ind
    exact congrArg (_root_.Quotient.mk _) (by simp)
  mul_smul b b' s := by
    induction s using _root_.Quotient.ind
    exact congrArg (_root_.Quotient.mk _) (by simp [mul_assoc])

private lemma smul_cls {a : StructuredArrow V u} (b : G'.obj.obj (op V))
    (p : P.sheaf.obj.obj (op a.right)) (x : G'.obj.obj (op V)) :
    b • cls φ P a p x = cls φ P a p (b * x) :=
  rfl

/-- `G'(V)` acts simply transitively on the sections of the pullback over `V`. -/
private lemma bijective_sec :
    Function.Bijective fun x : G'.obj.obj (op V) × Sec φ P V ↦ (x.1 • x.2, x.2) := by
  refine ⟨fun ⟨b, s⟩ ⟨b', s'⟩ h ↦ ?_, fun ⟨s₁, s₂⟩ ↦ ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, rfl⟩ := h
    obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P s
    rw [smul_cls, smul_cls] at h₁
    rw [mul_right_cancel (eq_of_cls_eq_cls φ P h₁)]
  · obtain ⟨c, p, x₁, x₂, rfl, rfl⟩ := exists_eq_cls_and_eq_cls φ P s₁ s₂
    exact ⟨(x₁ * x₂⁻¹, cls φ P c p x₂), by simp [smul_cls]⟩

/-- The sections of the pullback over `V` form a set of size at most that of `G'(V)`. -/
private instance : Small.{w} (Sec φ P V) := by
  rcases isEmpty_or_nonempty (Sec φ P V) with h | ⟨⟨s₀⟩⟩
  · infer_instance
  · refine small_of_surjective (f := fun b : G'.obj.obj (op V) ↦ b • s₀) fun s ↦ ?_
    obtain ⟨⟨b, s'⟩, hb⟩ := (bijective_sec φ P V).2 (s, s₀)
    simp only [Prod.mk.injEq] at hb
    obtain ⟨hb, rfl⟩ := hb
    exact ⟨b, hb⟩

variable {V}

/-- The restriction of sections of the pullback along `β : V' ⟶ V`. -/
private def secMap {V' : D} (β : V' ⟶ V) : Sec φ P V → Sec φ P V' :=
  _root_.Quotient.map
    (fun x ↦ ⟨(StructuredArrow.map β).obj x.arr, x.sec, G'.obj.map β.op x.elt⟩) (by
      rintro x y ⟨c, m, n, g, h₁, h₂⟩
      refine ⟨(StructuredArrow.map β).obj c, (StructuredArrow.map β).map m,
        (StructuredArrow.map β).map n, g, h₁, ?_⟩
      rw [h₂, map_mul, transport_apply, transport_apply]
      simp only [StructuredArrow.map_obj_hom, StructuredArrow.map_obj_right, op_comp,
        Functor.map_comp]
      exact congrArg _ (ConcreteCategory.comp_apply _ _ _).symm)

private lemma secMap_cls {V' : D} (β : V' ⟶ V) (a : StructuredArrow V u)
    (p : P.sheaf.obj.obj (op a.right)) (x : G'.obj.obj (op V)) :
    secMap φ P β (cls φ P a p x) =
      cls φ P ((StructuredArrow.map β).obj a) p (G'.obj.map β.op x) :=
  rfl

private lemma secMap_smul {V' : D} (β : V' ⟶ V) (b : G'.obj.obj (op V)) (s : Sec φ P V) :
    secMap φ P β (b • s) = G'.obj.map β.op b • secMap φ P β s := by
  obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P s
  rw [smul_cls, secMap_cls, secMap_cls, smul_cls, map_mul]

private lemma secMap_id (s : Sec φ P V) : secMap φ P (𝟙 V) s = s := by
  obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P s
  have h := cls_res φ P (StructuredArrow.homMk (𝟙 a.right) (by simp) :
    (StructuredArrow.map (𝟙 V)).obj a ⟶ a) p x
  simp only [res, StructuredArrow.homMk_right] at h
  simpa [secMap_cls] using h

private lemma secMap_comp {V' V'' : D} (β' : V'' ⟶ V') (β : V' ⟶ V) (s : Sec φ P V) :
    secMap φ P (β' ≫ β) s = secMap φ P β' (secMap φ P β s) := by
  obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P s
  have h := cls_res φ P (StructuredArrow.homMk (𝟙 a.right) (by simp) :
    (StructuredArrow.map (β' ≫ β)).obj a ⟶ (StructuredArrow.map β').obj
      ((StructuredArrow.map β).obj a)) p (G'.obj.map (β' ≫ β).op x)
  simp only [res, StructuredArrow.homMk_right] at h
  simpa [secMap_cls] using h

private lemma equivShrink_cls (a : StructuredArrow V u) (p : P.sheaf.obj.obj (op a.right))
    (x : G'.obj.obj (op V)) :
    equivShrink.{w} _ (cls φ P a p x) = x • equivShrink _ (cls φ P a p 1) := by
  rw [← equivShrink_smul, smul_cls, mul_one]

/-- A representative `(a, p, x)` is `x` times the restriction along `a` of `(𝟙, p, 1)`. -/
private lemma cls_eq_smul_secMap (a : StructuredArrow V u) (p : P.sheaf.obj.obj (op a.right))
    (x : G'.obj.obj (op V)) :
    cls φ P a p x =
      x • secMap φ P a.hom (cls φ P (StructuredArrow.mk (𝟙 (u.obj a.right))) p 1) := by
  have h := cls_res φ P (StructuredArrow.homMk (𝟙 a.right) (by simp) :
    a ⟶ (StructuredArrow.map a.hom).obj (StructuredArrow.mk (𝟙 (u.obj a.right)))) p x
  rw [secMap_cls, map_one, smul_cls, mul_one]
  simpa [res] using h

/-- The presheaf of sections of the pullback before sheafification. It is reducible so that its
sections are seen to be the small model `Shrink` of `Sec φ P V` with its action of `G'(V)`. -/
private abbrev presheaf : Dᵒᵖ ⥤ Type w where
  obj V := Shrink.{w} (Sec φ P V.unop)
  map β := ↾fun s ↦ equivShrink _ (secMap φ P β.unop ((equivShrink _).symm s))
  map_id V := by
    ext s : 3
    exact (congrArg (equivShrink _) (secMap_id φ P _)).trans (Equiv.apply_symm_apply _ _)
  map_comp β β' := by
    ext s : 3
    exact congrArg (equivShrink _) ((secMap_comp φ P _ _ _).trans
      (congrArg _ (Equiv.symm_apply_apply _ _).symm))

private lemma presheaf_map_equivShrink {V' : D} (β : op V ⟶ op V') (s : Sec φ P V) :
    (presheaf φ P).map β (equivShrink _ s) = equivShrink _ (secMap φ P β.unop s) :=
  congrArg (equivShrink _) (congrArg _ (Equiv.symm_apply_apply _ _))

/-- The pullback before sheafification, a `G'`-pretorsor. It is reducible for the same reason as
`presheaf`. -/
private abbrev pre : PreTorsor G' where
  presheaf := presheaf φ P
  mulAction V :=
    inferInstanceAs (MulAction (G'.obj.obj (op V.unop)) (Shrink.{w} (Sec φ P V.unop)))
  map_smul V V' β b s := by
    obtain ⟨V⟩ := V
    obtain ⟨V'⟩ := V'
    obtain ⟨t, rfl⟩ := (equivShrink _).surjective s
    rw [← equivShrink_smul, presheaf_map_equivShrink, presheaf_map_equivShrink, secMap_smul,
      equivShrink_smul, Quiver.Hom.op_unop]
  coversTop V := by
    obtain ⟨a⟩ : Nonempty (StructuredArrow V u) := IsCofiltered.nonempty
    -- The objects over which `P` has a section cover `a.right`; their images under `u` cover
    -- `u(a.right)`, and their pullbacks along `a` cover `V`.
    refine K.superset_covering ?_ (K.pullback_stable a.hom
      ((CoverPreserving.of_isContinuous u J K).cover_preserve (P.coversTop a.right)))
    rintro V' f ⟨U', f', h, ⟨⟨U'', ⟨p⟩⟩, ⟨e⟩⟩, -⟩
    exact ⟨⟨V', ⟨equivShrink _ (cls φ P (StructuredArrow.mk h) (P.sheaf.obj.map e.op p) 1)⟩⟩,
      ⟨𝟙 V'⟩⟩
  bijective V := by
    obtain ⟨V⟩ := V
    have h := ((Equiv.prodCongr (equivShrink.{w} (Sec φ P V)) (equivShrink _)).bijective.comp
      (bijective_sec φ P V)).comp
        (Equiv.prodCongr (Equiv.refl (G'.obj.obj (op V))) (equivShrink _).symm).bijective
    convert h using 1
    funext x
    simp

/-- The map `p ↦ [𝟙, p, 1]` from `P` to the pullback before sheafification. -/
private def toPre : P.sheaf.obj ⟶ u.op ⋙ (pre φ P).presheaf where
  app U := ↾fun p ↦ equivShrink _ (cls φ P (StructuredArrow.mk (𝟙 (u.obj U.unop))) p 1)
  naturality U U' f := by
    ext p : 3
    refine congrArg (equivShrink _) (Eq.trans ?_ (congrArg (secMap φ P (u.map f.unop))
      (Equiv.symm_apply_apply _ _)).symm)
    rw [secMap_cls, map_one]
    exact cls_res φ P (StructuredArrow.homMk f.unop (by simp) : StructuredArrow.mk (𝟙 _) ⟶
      (StructuredArrow.map (u.map f.unop)).obj (StructuredArrow.mk (𝟙 _))) p 1

private lemma toPre_app (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) :
    (toPre φ P).app U p = equivShrink _ (cls φ P (StructuredArrow.mk (𝟙 (u.obj U.unop))) p 1) :=
  rfl

/-- The map `p ↦ [𝟙, p, 1]` is `φ`-equivariant: the classes of `(𝟙, g • p, 1)` and
`(𝟙, p, φ(g))` agree. -/
private lemma toPre_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    (toPre φ P).app U (g • p) =
      equivShrink _ (cls φ P (StructuredArrow.mk (𝟙 (u.obj U.unop))) p (φ.hom.app U g)) := by
  rw [toPre_app, cls_smul, one_mul, transport_apply]
  congr 2
  exact ConcreteCategory.congr_hom (G'.obj.map_id _) _

variable [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)]

/-- The pullback of a `G`-torsor `P` along a morphism `φ : G ⟶ u_* G'` of sheaves of groups, for
a continuous and representably flat functor `u`: the `G'`-torsor obtained by pulling `P` back along
the morphism of sites defined by `u` and extending its structure group along the morphism
`u^* G ⟶ G'` adjoint to `φ`. Use `toPullback`, `toPullback_smul`, `pullbackLift` and
`pullback_hom_ext` rather than unfolding it. -/
def pullback : Torsor G' :=
  (pre φ P).sheafify

/-- The morphism `P ⟶ u_* (P.pullback φ)`, sending a section `p` of `P` over `U` to the class of
`p` over `u(U)`. -/
def toPullback :
    P.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj (P.pullback φ).sheaf :=
  ObjectProperty.homMk (toPre φ P ≫ Functor.whiskerLeft u.op (pre φ P).toSheafify)

private lemma toPullback_hom_app (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) :
    (P.toPullback φ).hom.app U p = (pre φ P).toSheafify.app (u.op.obj U) ((toPre φ P).app U p) :=
  rfl

/-- The morphism `P ⟶ u_* (P.pullback φ)` is `φ`-equivariant. -/
@[simp]
lemma toPullback_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    (P.toPullback φ).hom.app U (g • p) = φ.hom.app U g • (P.toPullback φ).hom.app U p := by
  rw [toPullback_hom_app, toPullback_hom_app]
  -- The action of `u_* G'` on `u_* (P.pullback φ)` over `U` is that of `G'` over `u(U)`.
  have h := (toPre_smul φ P g p).trans
    (equivShrink_cls φ P (StructuredArrow.mk (𝟙 (u.obj U.unop))) p (φ.hom.app U g))
  exact (congrArg ((pre φ P).toSheafify.app (u.op.obj U)) h).trans ((pre φ P).toSheafify_smul _ _)

variable {φ P} {R : Torsor G'}
  (h : P.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj R.sheaf)

omit [RepresentablyFlat u] [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- Restricting the image of `p` along `a` is restricting the image of `p|_c` along `c`, for
`m : c ⟶ a`. -/
private lemma map_hom_app_res {V : D} {c a : StructuredArrow V u} (m : c ⟶ a)
    (p : P.sheaf.obj.obj (op a.right)) :
    R.sheaf.obj.map a.hom.op (h.hom.app (op a.right) p) =
      R.sheaf.obj.map c.hom.op (h.hom.app (op c.right) (res P m p)) := by
  rw [res, NatTrans.naturality_apply h.hom, Functor.sheafPushforwardContinuous_obj_obj_map,
    ← StructuredArrow.w m]
  simp only [Quiver.Hom.unop_op, op_comp, Functor.map_comp]
  exact types_comp_apply _ _ _

variable (hh : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
  h.hom.app U (g • p) = φ.hom.app U g • h.hom.app U p)

omit [RepresentablyFlat u] [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
include hh in
private lemma map_hom_app_smul {V : D} (c : StructuredArrow V u) (g : G.obj.obj (op c.right))
    (q : P.sheaf.obj.obj (op c.right)) :
    R.sheaf.obj.map c.hom.op (h.hom.app (op c.right) (g • q)) =
      transport φ c g • R.sheaf.obj.map c.hom.op (h.hom.app (op c.right) q) := by
  rw [hh]
  exact R.map_smul _ _ _

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- The section `x • a^* h(p)` of `R` over `V` depends only on the class of `(a, p, x)`. -/
private def secLift (V : D) : Sec φ P V → R.sheaf.obj.obj (op V) :=
  _root_.Quotient.lift
    (fun x ↦ x.elt • R.sheaf.obj.map x.arr.hom.op (h.hom.app (op x.arr.right) x.sec)) (by
      rintro x y ⟨c, m, n, g, h₁, h₂⟩
      dsimp only
      rw [map_hom_app_res h m, h₁, map_hom_app_smul h hh, ← map_hom_app_res h n, h₂,
        mul_smul])

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
private lemma secLift_cls {V : D} (a : StructuredArrow V u) (p : P.sheaf.obj.obj (op a.right))
    (x : G'.obj.obj (op V)) :
    secLift h hh V (cls φ P a p x) =
      x • R.sheaf.obj.map a.hom.op (h.hom.app (op a.right) p) :=
  rfl

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- The `G'`-equivariant morphism from the pullback before sheafification to `R` induced by `h`. -/
private def liftPre : (pre φ P).presheaf ⟶ R.sheaf.obj where
  app V := ↾fun s ↦ secLift h hh V.unop ((equivShrink _).symm s)
  naturality V V' β := by
    obtain ⟨V⟩ := V
    obtain ⟨V'⟩ := V'
    refine ConcreteCategory.ext_apply fun s ↦ ?_
    obtain ⟨t, rfl⟩ := (equivShrink _).surjective s
    obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P t
    simp only [types_comp_apply, TypeCat.ofHom_apply, Equiv.symm_apply_apply]
    rw [secMap_cls, secLift_cls, secLift_cls, R.map_smul]
    congr 1
    simp only [StructuredArrow.map_obj_hom, StructuredArrow.map_obj_right, op_comp,
      Functor.map_comp, Quiver.Hom.op_unop]
    exact types_comp_apply _ _ _

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
private lemma liftPre_app_equivShrink {V : D} (t : Sec φ P V) :
    (liftPre h hh).app (op V) (equivShrink _ t) = secLift h hh V t :=
  congrArg (secLift h hh V) (Equiv.symm_apply_apply _ _)

/-- A `φ`-equivariant morphism `h : P ⟶ u_* R` to the pushforward of a `G'`-torsor `R` induces a
morphism of `G'`-torsors `P.pullback φ ⟶ R`, sending the class of `(a, p, x)` to `x • a^* h(p)`. -/
def pullbackLift : P.pullback φ ⟶ R :=
  (pre φ P).sheafifyLift (liftPre h hh) fun V b s ↦ by
    obtain ⟨V⟩ := V
    obtain ⟨t, rfl⟩ := (equivShrink _).surjective s
    obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P t
    rw [← equivShrink_smul, liftPre_app_equivShrink, liftPre_app_equivShrink, smul_cls,
      secLift_cls, secLift_cls, mul_smul]

/-- The morphism induced by a `φ`-equivariant `h : P ⟶ u_* R` restricts to `h` along
`P ⟶ u_* (P.pullback φ)`. -/
@[reassoc (attr := simp)]
lemma toPullback_pullbackLift :
    P.toPullback φ ≫ (u.sheafPushforwardContinuous (Type w) J K).map (P.pullbackLift h hh).hom =
      h := by
  ext U p
  refine ((pre φ P).sheafifyLift_hom_app_toSheafify _ _ ((toPre φ P).app U p)).trans ?_
  exact (liftPre_app_equivShrink h hh _).trans ((secLift_cls h hh _ _ _).trans
    ((one_smul _ _).trans (ConcreteCategory.congr_hom (R.sheaf.obj.map_id _) _)))

/-- A morphism of `G'`-torsors out of `P.pullback φ` sends the class of `(a, p, x)` to
`x • a^* f(p)`, where `f(p)` is the image of `p` under `P ⟶ u_* (P.pullback φ) ⟶ u_* R`. -/
private lemma hom_app_toSheafify_cls (f : P.pullback φ ⟶ R) {V : D} (a : StructuredArrow V u)
    (p : P.sheaf.obj.obj (op a.right)) (x : G'.obj.obj (op V)) :
    f.hom.hom.app (op V) ((pre φ P).toSheafify.app (op V) (equivShrink _ (cls φ P a p x))) =
      x • R.sheaf.obj.map a.hom.op (f.hom.hom.app (op (u.obj a.right))
        ((P.toPullback φ).hom.app (op a.right) p)) := by
  have e : equivShrink _ (cls φ P a p x) = x • (presheaf φ P).map a.hom.op
      (equivShrink _ (cls φ P (StructuredArrow.mk (𝟙 (u.obj a.right))) p 1)) := by
    rw [cls_eq_smul_secMap, equivShrink_smul, presheaf_map_equivShrink, Quiver.Hom.unop_op]
  rw [e, (pre φ P).toSheafify_smul]
  exact (f.map_smul _ _ _).trans (congrArg (x • ·)
    ((congrArg (f.hom.hom.app _) (NatTrans.naturality_apply (pre φ P).toSheafify a.hom.op _)).trans
      (NatTrans.naturality_apply f.hom.hom a.hom.op _)))

/-- Morphisms of `G'`-torsors out of `P.pullback φ` are determined by their composite with the
morphism `P ⟶ u_* (P.pullback φ)`. -/
lemma pullback_hom_ext {f f' : P.pullback φ ⟶ R}
    (H : P.toPullback φ ≫ (u.sheafPushforwardContinuous (Type w) J K).map f.hom =
      P.toPullback φ ≫ (u.sheafPushforwardContinuous (Type w) J K).map f'.hom) : f = f' := by
  refine (pre φ P).sheafify_hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  ext s : 3
  obtain ⟨V⟩ := V
  obtain ⟨t, rfl⟩ := (equivShrink _).surjective s
  obtain ⟨a, p, x, rfl⟩ := cls_surjective φ P t
  have H' := congrArg (fun k ↦ k.hom.app (op a.right) p) H
  exact (hom_app_toSheafify_cls f a p x).trans
    ((congrArg (fun y ↦ x • R.sheaf.obj.map a.hom.op y) H').trans
      (hom_app_toSheafify_cls f' a p x).symm)

end Construction

end Torsor

namespace IsGroupExtension

section Pushforward

variable {u : C ⥤ D} [u.IsContinuous J K] {A B Q : Sheaf J GrpCat.{w}} {i : A ⟶ B} {π : B ⟶ Q}
  (hE : IsGroupExtension i π) (q : (Q.obj ⋙ forget GrpCat).sections)
  {A' B' Q' : Sheaf K GrpCat.{w}} {i' : A' ⟶ B'} {π' : B' ⟶ Q'} (hE' : IsGroupExtension i' π')
  (β : B ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj B')
  (γ : Q ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj Q')
  (hγ : β ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map π' = π ≫ γ)
  (q' : (Q'.obj ⋙ forget GrpCat).sections)
  (hq : ∀ U, γ.hom.app U (q.val U) = q'.val (u.op.obj U))

include hγ hq in
/-- Applying `β` to a local lift of `q` over `U` gives a local lift of `q'` over `u(U)`. -/
private lemma app_liftsObjEquiv_val (U : Cᵒᵖ) (b : (hE.lifts q).sheaf.obj.obj U) :
    π'.hom.app (u.op.obj U) (β.hom.app U (hE.liftsObjEquiv q U b).val) = q'.val (u.op.obj U) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (·.hom) hγ) U)
    (hE.liftsObjEquiv q U b).val
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, (hE.liftsObjEquiv q U b).property, hq] at this
  exact this

include β γ hγ hq in
/-- The variant of `IsGroupExtension.liftsMap` for an extension on `D` pushed forward along `u`:
a commuting square from the projection of `hE` to the pushforward of the projection of `hE'` sends
local lifts of `q` over `U` to local lifts of `q'` over `u(U)`, by applying `β`. The pushforward of
`hE'` need not be a group extension. -/
def liftsPushforwardMap :
    (hE.lifts q).sheaf ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj (hE'.lifts q').sheaf :=
  ObjectProperty.homMk
    { app U := ↾fun b ↦ (hE'.liftsObjEquiv q' (u.op.obj U)).symm
        ⟨_, hE.app_liftsObjEquiv_val q β γ hγ q' hq U b⟩
      naturality U V f := by
        ext b
        refine (hE'.liftsObjEquiv q' _).injective (Subtype.ext ?_)
        -- Both sides are `β` applied to the restriction of the lift `b`.
        refine (congrArg Subtype.val (Equiv.apply_symm_apply _ _)).trans ?_
        refine (congrArg (β.hom.app V) (hE.liftsObjEquiv_map q f b)).trans
          ((NatTrans.naturality_apply β.hom f _).trans ?_)
        exact ((hE'.liftsObjEquiv_map q' (u.map f.unop).op _).trans
          (congrArg _ (congrArg Subtype.val (Equiv.apply_symm_apply _
            ⟨_, hE.app_liftsObjEquiv_val q β γ hγ q' hq U b⟩)))).symm }

/-- On local lifts, `liftsPushforwardMap` applies `β` to the underlying section. -/
@[simp]
lemma liftsObjEquiv_liftsPushforwardMap_hom_app (U : Cᵒᵖ) (b : (hE.lifts q).sheaf.obj.obj U) :
    (hE'.liftsObjEquiv q' (op (u.obj U.unop))
        ((hE.liftsPushforwardMap q hE' β γ hγ q' hq).hom.app U b)).val =
      β.hom.app U (hE.liftsObjEquiv q U b).val :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- If the square on kernels also commutes, `liftsPushforwardMap` is equivariant for the
corresponding map `α` of kernels. -/
lemma liftsPushforwardMap_smul (α : A ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj A')
    (hα : i ≫ β = α ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map i')
    (U : Cᵒᵖ) (a : A.obj.obj U) (b : (hE.lifts q).sheaf.obj.obj U) :
    (hE.liftsPushforwardMap q hE' β γ hγ q' hq).hom.app U (a • b) =
      α.hom.app U a • (hE.liftsPushforwardMap q hE' β γ hγ q' hq).hom.app U b := by
  refine (hE'.liftsObjEquiv q' (op (u.obj U.unop))).injective (Subtype.ext ?_)
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (·.hom) hα) U) a
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at this
  rw [liftsObjEquiv_liftsPushforwardMap_hom_app, liftsObjEquiv_smul, map_mul, this,
    ← liftsObjEquiv_liftsPushforwardMap_hom_app]
  exact (hE'.liftsObjEquiv_smul q' (α.hom.app U a) _).symm

end Pushforward

end IsGroupExtension

namespace NonabelianH1

variable {u : C ⥤ D} [u.IsContinuous J K] [RepresentablyFlat u]
  [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)]
  {G : Sheaf J GrpCat.{w}} {G' : Sheaf K GrpCat.{w}}

/-- The map `H¹(G) → H¹(G')` induced by a morphism `φ : G ⟶ u_* G'` of sheaves of groups, for a
continuous and representably flat functor `u`: it sends the class of a `G`-torsor `P` to the class
of its pullback `P.pullback φ`. -/
def pullback (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G') :
    NonabelianH1 G → NonabelianH1 G' :=
  lift (fun P ↦ mk (P.pullback φ)) fun P Q f ↦ mk_eq_mk_of_hom <|
    P.pullbackLift (f.hom ≫ Q.toPullback φ) fun U g p ↦ by
      simp [f.map_smul, Torsor.toPullback_smul]

/-- `pullback φ` sends the class of `P` to the class of `P.pullback φ`. -/
@[simp]
lemma pullback_mk (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G')
    (P : Torsor G) : pullback φ (mk P) = mk (P.pullback φ) :=
  lift_mk _ _ P

/-- A `φ`-equivariant morphism from a `G`-torsor `P` to the pushforward of a `G'`-torsor `R`
identifies the image of the class of `P` under `pullback φ` with the class of `R`. -/
lemma pullback_mk_eq_mk {φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G'}
    {P : Torsor G} {R : Torsor G'}
    (h : P.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj R.sheaf)
    (hh : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      h.hom.app U (g • p) = φ.hom.app U g • h.hom.app U p) :
    pullback φ (mk P) = mk R :=
  (pullback_mk φ P).trans (mk_eq_mk_of_hom (P.pullbackLift h hh))

/-- The image of the class of a `G`-torsor `P` under `pullback φ` is the class of a `G'`-torsor
`R` if and only if there is a `φ`-equivariant morphism from `P` to the pushforward of `R`. -/
lemma pullback_mk_eq_mk_iff {φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G'}
    {P : Torsor G} {R : Torsor G'} :
    pullback φ (mk P) = mk R ↔
      ∃ h : P.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj R.sheaf,
        ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
          h.hom.app U (g • p) = φ.hom.app U g • h.hom.app U p := by
  refine ⟨fun H ↦ ?_, fun ⟨h, hh⟩ ↦ pullback_mk_eq_mk h hh⟩
  obtain ⟨e⟩ := mk_eq_mk_iff.1 ((pullback_mk φ P).symm.trans H)
  exact ⟨P.toPullback φ ≫ (u.sheafPushforwardContinuous (Type w) J K).map e.hom.hom,
    fun U g p ↦ (congrArg (e.hom.hom.hom.app _) (P.toPullback_smul φ g p)).trans
      (e.hom.map_smul _ _ _)⟩

/-- `pullback φ` is a map of pointed sets: it sends the class of the trivial torsor to the class
of the trivial torsor. -/
@[simp]
lemma pullback_one (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G') :
    pullback φ 1 = 1 :=
  pullback_mk_eq_mk (R := Torsor.trivial G') ((sheafCompose J (forget GrpCat.{w})).map φ)
    fun U g p ↦ map_mul (φ.hom.app U).hom g p

/-- Pulling back after extending the structure group along `ψ : G₀ ⟶ G` is pulling back along
`ψ ≫ φ`. -/
@[simp]
lemma pullback_map {G₀ : Sheaf J GrpCat.{w}} [HasWeakSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type w)] (ψ : G₀ ⟶ G)
    (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G') (x : NonabelianH1 G₀) :
    pullback φ (map ψ x) = pullback (ψ ≫ φ) x := by
  induction x using ind with | h P => ?_
  rw [map_mk, pullback_mk]
  refine (pullback_mk_eq_mk (P.toMap ψ ≫ (P.map ψ).toPullback φ) fun U g p ↦ ?_).symm
  simp [Torsor.toMap_smul, Torsor.toPullback_smul]

/-- Extending the structure group of a pullback along `ψ : G' ⟶ G''` is pulling back along
`φ ≫ u_* ψ`. -/
@[simp]
lemma map_pullback {G'' : Sheaf K GrpCat.{w}} (ψ : G' ⟶ G'')
    (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G') (x : NonabelianH1 G) :
    map ψ (pullback φ x) =
      pullback (φ ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map ψ) x := by
  induction x using ind with | h P => ?_
  rw [pullback_mk, map_mk]
  refine (pullback_mk_eq_mk (P.toPullback φ ≫
    (u.sheafPushforwardContinuous (Type w) J K).map ((P.pullback φ).toMap ψ)) fun U g p ↦
      (congrArg (((P.pullback φ).toMap ψ).hom.app _) (P.toPullback_smul φ g p)).trans
        ((P.pullback φ).toMap_smul ψ _ _)).symm

/-- Pulling back along `u` and then along `v` is pulling back along the composite `u ⋙ v`, with
the composite morphism `G ⟶ u_* G' ⟶ u_* v_* G'' = (u ⋙ v)_* G''`. -/
@[simp]
lemma pullback_pullback {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {v : D ⥤ E} [v.IsContinuous K L] [RepresentablyFlat v]
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)] {G'' : Sheaf L GrpCat.{w}}
    (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G')
    (φ' : G' ⟶ (v.sheafPushforwardContinuous GrpCat.{w} K L).obj G'') (x : NonabelianH1 G) :
    letI := Functor.isContinuous_comp u v J K L
    pullback φ' (pullback φ x) =
      pullback (φ ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map φ' ≫
        (u.sheafPushforwardContinuousComp v GrpCat.{w} J K L).hom.app G'') x := by
  have := Functor.isContinuous_comp u v J K L
  induction x using ind with | h P => ?_
  rw [pullback_mk, pullback_mk]
  refine (pullback_mk_eq_mk (P.toPullback φ ≫
    (u.sheafPushforwardContinuous (Type w) J K).map ((P.pullback φ).toPullback φ') ≫
      (u.sheafPushforwardContinuousComp v (Type w) J K L).hom.app _) fun U g p ↦
        (congrArg (((P.pullback φ).toPullback φ').hom.app _) (P.toPullback_smul φ g p)).trans
          ((P.pullback φ).toPullback_smul φ' _ _)).symm

/-- The map induced on `H¹` by a composite of morphisms of sites is the composite of the induced
maps. -/
lemma pullback_comp {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {v : D ⥤ E} [v.IsContinuous K L] [RepresentablyFlat v]
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)] {G'' : Sheaf L GrpCat.{w}}
    (φ : G ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj G')
    (φ' : G' ⟶ (v.sheafPushforwardContinuous GrpCat.{w} K L).obj G'') :
    letI := Functor.isContinuous_comp u v J K L
    pullback (φ ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map φ' ≫
      (u.sheafPushforwardContinuousComp v GrpCat.{w} J K L).hom.app G'') =
        pullback φ' ∘ pullback φ :=
  funext fun x ↦ (pullback_pullback φ φ' x).symm

/-- Pulling back along the identity functor is extending the structure group: the pullback is
the contracted product. -/
@[simp]
lemma pullback_eq_map [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    {G' : Sheaf J GrpCat.{w}}
    (φ : G ⟶ ((𝟭 C).sheafPushforwardContinuous GrpCat.{w} J J).obj G') :
    pullback φ = map (φ ≫ (Functor.sheafPushforwardContinuousId GrpCat.{w} J).hom.app G') := by
  funext x
  induction x using ind with | h P => ?_
  rw [map_mk]
  refine pullback_mk_eq_mk (P.toMap _ ≫
    (Functor.sheafPushforwardContinuousId (Type w) J).inv.app _) fun U g p ↦ P.toMap_smul _ g p

/-- Pulling back along the identity functor and the identity of `G` is the identity of
`H¹(G)`. -/
lemma pullback_id [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)] :
    pullback ((Functor.sheafPushforwardContinuousId GrpCat.{w} J).inv.app G) = id := by
  simp

/-- The pullback commutes with the connecting maps of group extensions. Let `1 → A → B → Q → 1` be
an extension of sheaves of groups on `C` and `1 → A' → B' → Q' → 1` one on `D`, with morphisms
`α`, `β`, `γ` to the pushforwards of `A'`, `B'`, `Q'` compatible with the maps of the extensions.
If a global section `q'` of `Q'` restricts over each `u(U)` to the image of a global section `q`
of `Q` under `γ`, then pulling back the torsor of lifts of `q` along `α` gives the torsor of lifts
of `q'`. -/
theorem pullback_connecting_of_comp_eq {A B Q : Sheaf J GrpCat.{w}} {i : A ⟶ B} {π : B ⟶ Q}
    (hE : IsGroupExtension i π) {A' B' Q' : Sheaf K GrpCat.{w}} {i' : A' ⟶ B'} {π' : B' ⟶ Q'}
    (hE' : IsGroupExtension i' π')
    (α : A ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj A')
    (β : B ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj B')
    (γ : Q ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj Q')
    (hα : i ≫ β = α ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map i')
    (hγ : β ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map π' = π ≫ γ)
    (q : (Q.obj ⋙ forget GrpCat).sections) (q' : (Q'.obj ⋙ forget GrpCat).sections)
    (hq : ∀ U, γ.hom.app U (q.val U) = q'.val (u.op.obj U)) :
    pullback α (connecting hE q) = connecting hE' q' := by
  rw [connecting_def, connecting_def]
  exact pullback_mk_eq_mk (hE.liftsPushforwardMap q hE' β γ hγ q' hq)
    (hE.liftsPushforwardMap_smul q hE' β γ hγ q' hq α hα)

end NonabelianH1


end CategoryTheory.Sheaf
