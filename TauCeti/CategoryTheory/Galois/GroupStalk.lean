/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.MinimalAxioms
public import TauCeti.CategoryTheory.Galois.Sheaf

/-!
# Stalks of presheaves of groups on finite continuous `G`-sets

Let `G` be a topological group and `P` a presheaf of groups on the finite continuous `G`-sets
`ContAction FintypeCat G`. The stalk at the point `ContAction.point G` of the underlying presheaf of
sets (`ContAction.GrpStalk P`) is a group: any two elements are germs of sections over a common
finite `G`-set at a common point, and their product is the germ of the product of the sections
(`ContAction.grpGerm_mul`). The action of `G` on the stalk by translating the point
(`ContAction.stalk`) is by group automorphisms, so the stalk is a group with a
`MulDistribMulAction` of `G`. Its stabilizers are open (`ContAction.isSmooth_stalk`), so for a
profinite `G` it is a smooth `G`-group in the sense of
`TauCeti.NonabelianH1.SmoothTorsor`. A morphism of presheaves of groups induces a `G`-equivariant
homomorphism of stalks (`ContAction.grpStalkMap`).

Mathlib's stalk functor `CategoryTheory.GrothendieckTopology.Point.presheafFiber` needs all
colimits in the coefficient category, which Mathlib does not provide for `GrpCat`, so the group
structure is built on the stalk of sets from germs.

## Main definitions

* `ContAction.GrpStalk P`: the stalk of a presheaf of groups, with its `Group` and
  `MulDistribMulAction G` instances.
* `ContAction.grpGerm P S s z`: the germ at `s` of a section `z` over `S`.
* `ContAction.grpStalkMap f`: the homomorphism of stalks induced by a morphism of presheaves of
  groups.

## Main results

* `ContAction.grpGerm_mul`, `ContAction.grpGerm_inv`, `ContAction.grpGerm_one`: germs are
  multiplicative.
* `ContAction.smul_grpGerm`: `G` acts on germs by translating the point.
* `ContAction.grpStalkMap_smul`: the induced homomorphism of stalks is `G`-equivariant.
-/

public section

open CategoryTheory Limits Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ GrpCat.{u})

/-- The germ of a section of a presheaf of groups. -/
noncomputable abbrev grpGerm (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S)
    (z : P.obj (op S)) : ((stalk G).obj (P ⋙ forget GrpCat)).V :=
  germ (P ⋙ forget GrpCat) S s z

theorem grpGerm_map {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T)
    (s : (fiberFunctor G).obj S) (z : P.obj (op T)) :
    grpGerm P S s (P.map f.op z) = grpGerm P T ((fiberFunctor G).map f s) z :=
  germ_map (P ⋙ forget GrpCat) f s z

/-- Two points of finite continuous `G`-sets are images of a common point under `G`-maps. -/
theorem exists_common_refinement (S T : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S)
    (t : (fiberFunctor G).obj T) :
    ∃ (W : ContAction FintypeCat.{u} G) (w : (fiberFunctor G).obj W) (f : W ⟶ S) (g : W ⟶ T),
      (fiberFunctor G).map f w = s ∧ (fiberFunctor G).map g w = t := by
  have := Functor.isCofiltered_elements (fiberFunctor G)
  let a := (fiberFunctor G).elementsMk S s
  let b := (fiberFunctor G).elementsMk T t
  exact ⟨_, (IsCofiltered.min a b).val, (IsCofiltered.minToLeft a b).hom,
    (IsCofiltered.minToRight a b).hom, (IsCofiltered.minToLeft a b).map_val,
    (IsCofiltered.minToRight a b).map_val⟩


/-- If two pairs of sections over `W` have the same germs at `w`, they agree after restriction along
a single `G`-map `V ⟶ W` hitting `w`. -/
theorem exists_map_eq_map₂ {W : ContAction FintypeCat.{u} G} {w : (fiberFunctor G).obj W}
    {a a' b b' : P.obj (op W)} (ha : grpGerm P W w a = grpGerm P W w a')
    (hb : grpGerm P W w b = grpGerm P W w b') :
    ∃ (V : ContAction FintypeCat.{u} G) (v : (fiberFunctor G).obj V) (h : V ⟶ W),
      (fiberFunctor G).map h v = w ∧ P.map h.op a = P.map h.op a' ∧
        P.map h.op b = P.map h.op b' := by
  have := Functor.isCofiltered_elements (fiberFunctor G)
  obtain ⟨T₁, f₁, t₁, hf₁, e₁⟩ :=
    ((point G).toPresheafFiber_eq_iff' (P := P ⋙ forget GrpCat) W w a a').1 ha
  obtain ⟨T₂, f₂, t₂, hf₂, e₂⟩ :=
    ((point G).toPresheafFiber_eq_iff' (P := P ⋙ forget GrpCat) W w b b').1 hb
  obtain ⟨k, i₁, i₂, hi⟩ := IsCofiltered.cospan
    (Functor.Elements.homMk (x := (fiberFunctor G).elementsMk T₁ t₁)
      (y := (fiberFunctor G).elementsMk W w) f₁ hf₁)
    (Functor.Elements.homMk (x := (fiberFunctor G).elementsMk T₂ t₂)
      (y := (fiberFunctor G).elementsMk W w) f₂ hf₂)
  have hi' : i₁.hom ≫ f₁ = i₂.hom ≫ f₂ := congrArg Functor.Elements.Hom.hom hi
  refine ⟨k.obj, k.val, i₁.hom ≫ f₁, ?_, ?_, ?_⟩
  · rw [Functor.map_comp, types_comp_apply, i₁.map_val]
    exact hf₁
  · rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact congrArg (P.map i₁.hom.op) e₁
  · rw [hi', op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact congrArg (P.map i₂.hom.op) e₂

/-- Germs of natural binary operations at different points agree when the germs of the arguments
do. -/
theorem grpGerm_congr₂ (m : ∀ ⦃S : ContAction FintypeCat.{u} G⦄,
      P.obj (op S) → P.obj (op S) → P.obj (op S))
    (hm : ∀ ⦃S T : ContAction FintypeCat.{u} G⦄ (f : S ⟶ T) (a b : P.obj (op T)),
      P.map f.op (m a b) = m (P.map f.op a) (P.map f.op b))
    {S₁ S₂ : ContAction FintypeCat.{u} G} {s₁ : (fiberFunctor G).obj S₁}
    {s₂ : (fiberFunctor G).obj S₂} {a₁ b₁ : P.obj (op S₁)} {a₂ b₂ : P.obj (op S₂)}
    (ha : grpGerm P S₁ s₁ a₁ = grpGerm P S₂ s₂ a₂) (hb : grpGerm P S₁ s₁ b₁ = grpGerm P S₂ s₂ b₂) :
    grpGerm P S₁ s₁ (m a₁ b₁) = grpGerm P S₂ s₂ (m a₂ b₂) := by
  obtain ⟨W, w, f, g, rfl, rfl⟩ := exists_common_refinement S₁ S₂ s₁ s₂
  simp only [← grpGerm_map] at ha hb ⊢
  obtain ⟨V, v, h, rfl, ea, eb⟩ := exists_map_eq_map₂ P ha hb
  rw [← grpGerm_map, ← grpGerm_map, hm, hm, hm, hm, ea, eb]

/-- The stalk at `point G` of the presheaf of sets underlying a presheaf of groups. -/
abbrev GrpStalk : Type u := ((stalk G).obj (P ⋙ forget GrpCat)).V

/-- Every element of the stalk is a germ. -/
theorem exists_grpGerm_eq (p : GrpStalk P) :
    ∃ x : Σ S : ContAction FintypeCat.{u} G, (fiberFunctor G).obj S × P.obj (op S),
      grpGerm P x.fst x.snd.fst x.snd.snd = p := by
  obtain ⟨S, s, a, rfl⟩ := (point G).toPresheafFiber_jointly_surjective (P := P ⋙ forget GrpCat) p
  exact ⟨⟨S, s, a⟩, rfl⟩

/-- Two elements of the stalk are germs at a common point. -/
theorem exists_grpGerm_eq₂ (p q : GrpStalk P) :
    ∃ x : Σ S : ContAction FintypeCat.{u} G,
      (fiberFunctor G).obj S × P.obj (op S) × P.obj (op S),
      grpGerm P x.fst x.snd.fst x.snd.snd.fst = p ∧
        grpGerm P x.fst x.snd.fst x.snd.snd.snd = q := by
  obtain ⟨S, s, a, b, rfl, rfl⟩ :=
    (point G).toPresheafFiber_jointly_surjective₂ (P := P ⋙ forget GrpCat) p q
  exact ⟨⟨S, s, a, b⟩, rfl, rfl⟩

/-- Three elements of the stalk are germs at a common point. -/
theorem exists_grpGerm_eq₃ (p q r : GrpStalk P) :
    ∃ (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) (a b c : P.obj (op S)),
      grpGerm P S s a = p ∧ grpGerm P S s b = q ∧ grpGerm P S s c = r := by
  obtain ⟨⟨S, s, a, b⟩, rfl, rfl⟩ := exists_grpGerm_eq₂ P p q
  obtain ⟨⟨T, t, c⟩, rfl⟩ := exists_grpGerm_eq P r
  obtain ⟨W, w, f, g, rfl, rfl⟩ := exists_common_refinement S T s t
  exact ⟨W, w, P.map f.op a, P.map f.op b, P.map g.op c, grpGerm_map _ _ _ _,
    grpGerm_map _ _ _ _, grpGerm_map _ _ _ _⟩

/-- The product of two germs at a common point is the germ of the product. -/
noncomputable instance instMulGrpStalk : Mul (GrpStalk P) where
  mul p q := grpGerm P (exists_grpGerm_eq₂ P p q).choose.fst
    (exists_grpGerm_eq₂ P p q).choose.snd.fst
    ((exists_grpGerm_eq₂ P p q).choose.snd.snd.fst * (exists_grpGerm_eq₂ P p q).choose.snd.snd.snd)

/-- The inverse of a germ is the germ of the inverse. -/
noncomputable instance instInvGrpStalk : Inv (GrpStalk P) where
  inv p := grpGerm P (exists_grpGerm_eq P p).choose.fst (exists_grpGerm_eq P p).choose.snd.fst
    (exists_grpGerm_eq P p).choose.snd.snd⁻¹

omit [IsTopologicalGroup G] in
/-- A point of some finite continuous `G`-set, at which the unit of the stalk is a germ. -/
noncomputable def someFiberElement : (fiberFunctor G).Elements :=
  have := Functor.isCofiltered_elements (fiberFunctor G)
  Classical.choice IsCofiltered.nonempty

/-- The unit is the germ of the unit section. -/
noncomputable instance instOneGrpStalk : One (GrpStalk P) where
  one := grpGerm P (someFiberElement (G := G)).obj (someFiberElement (G := G)).val 1

/-- Germs are multiplicative. -/
theorem grpGerm_mul (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S)
    (a b : P.obj (op S)) : grpGerm P S s a * grpGerm P S s b = grpGerm P S s (a * b) :=
  grpGerm_congr₂ P (fun _ a b ↦ a * b) (fun _ _ f a b ↦ map_mul (P.map f.op).hom a b)
    (exists_grpGerm_eq₂ P _ _).choose_spec.1 (exists_grpGerm_eq₂ P _ _).choose_spec.2

/-- The germ of an inverse is the inverse of the germ. -/
theorem grpGerm_inv (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S)
    (a : P.obj (op S)) : (grpGerm P S s a)⁻¹ = grpGerm P S s a⁻¹ :=
  grpGerm_congr₂ P (fun _ a _ ↦ a⁻¹) (fun _ _ f a _ ↦ map_inv (P.map f.op).hom a)
    (exists_grpGerm_eq P _).choose_spec (exists_grpGerm_eq P _).choose_spec

/-- The germ of the unit section is the unit, at every point. -/
theorem grpGerm_one (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) :
    grpGerm P S s 1 = 1 := by
  obtain ⟨W, w, f, g, rfl, h⟩ := exists_common_refinement S _ s (someFiberElement (G := G)).val
  change _ = grpGerm P _ _ 1
  rw [← h, ← grpGerm_map, ← grpGerm_map, map_one, map_one]

/-- **The stalk of a presheaf of groups is a group.** -/
noncomputable instance instGroupGrpStalk : Group (GrpStalk P) :=
  Group.ofLeftAxioms
    (fun p q r ↦ by
      obtain ⟨S, s, a, b, c, rfl, rfl, rfl⟩ := exists_grpGerm_eq₃ P p q r
      simp only [grpGerm_mul, mul_assoc])
    (fun p ↦ by
      obtain ⟨⟨S, s, a⟩, rfl⟩ := exists_grpGerm_eq P p
      rw [← grpGerm_one P S s, grpGerm_mul, one_mul])
    (fun p ↦ by
      obtain ⟨⟨S, s, a⟩, rfl⟩ := exists_grpGerm_eq P p
      rw [grpGerm_inv, grpGerm_mul, inv_mul_cancel, grpGerm_one])

/-- `G` acts on germs by translating the point. -/
theorem smul_grpGerm (g : G) (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S)
    (a : P.obj (op S)) : g • grpGerm P S s a = grpGerm P S (g • s) a :=
  smul_germ (P ⋙ forget GrpCat) S s a g

/-- **`G` acts on the stalk of a presheaf of groups by group automorphisms.** -/
noncomputable instance instMulDistribMulActionGrpStalk : MulDistribMulAction G (GrpStalk P) where
  smul_mul g p q := by
    obtain ⟨⟨S, s, a, b⟩, rfl, rfl⟩ := exists_grpGerm_eq₂ P p q
    rw [grpGerm_mul, smul_grpGerm, smul_grpGerm, smul_grpGerm, grpGerm_mul]
  smul_one g := by
    obtain ⟨⟨S, s, -⟩, -⟩ := exists_grpGerm_eq P 1
    calc g • (1 : GrpStalk P) = g • grpGerm P S s 1 := by rw [grpGerm_one]
      _ = grpGerm P S (g • s) 1 := smul_grpGerm P g S s 1
      _ = 1 := grpGerm_one P S (g • s)

variable {P} {Q : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ GrpCat.{u}}

/-- The map of stalks induced by a morphism of presheaves of groups sends germs to germs. -/
theorem stalk_map_hom_grpGerm (f : P ⟶ Q) (S : ContAction FintypeCat.{u} G)
    (s : (fiberFunctor G).obj S) (a : P.obj (op S)) :
    ((stalk G).map (Functor.whiskerRight f (forget GrpCat))).hom (grpGerm P S s a) =
      grpGerm Q S s (f.app _ a) :=
  (point G).toPresheafFiber_naturality_apply (Functor.whiskerRight f (forget GrpCat)) S s a

/-- The homomorphism of stalks induced by a morphism of presheaves of groups. -/
noncomputable def grpStalkMap (f : P ⟶ Q) : GrpStalk P →* GrpStalk Q where
  toFun := ((stalk G).map (Functor.whiskerRight f (forget GrpCat))).hom
  map_one' := by
    obtain ⟨⟨S, s, -⟩, -⟩ := exists_grpGerm_eq P 1
    calc ((stalk G).map (Functor.whiskerRight f (forget GrpCat))).hom (1 : GrpStalk P) =
        ((stalk G).map (Functor.whiskerRight f (forget GrpCat))).hom (grpGerm P S s 1) := by
          rw [grpGerm_one]
      _ = 1 := by rw [stalk_map_hom_grpGerm, map_one, grpGerm_one]
  map_mul' p q := by
    obtain ⟨⟨S, s, a, b⟩, rfl, rfl⟩ := exists_grpGerm_eq₂ P p q
    rw [grpGerm_mul, stalk_map_hom_grpGerm, stalk_map_hom_grpGerm, stalk_map_hom_grpGerm, map_mul,
      grpGerm_mul]

/-- `grpStalkMap f` sends germs to germs. -/
@[simp]
theorem grpStalkMap_grpGerm (f : P ⟶ Q) (S : ContAction FintypeCat.{u} G)
    (s : (fiberFunctor G).obj S) (a : P.obj (op S)) :
    grpStalkMap f (grpGerm P S s a) = grpGerm Q S s (f.app _ a) :=
  stalk_map_hom_grpGerm f S s a

/-- `grpStalkMap f` is `G`-equivariant. -/
theorem grpStalkMap_smul (f : P ⟶ Q) (g : G) (p : GrpStalk P) :
    grpStalkMap f (g • p) = g • grpStalkMap f p := by
  obtain ⟨⟨S, s, a⟩, rfl⟩ := exists_grpGerm_eq P p
  rw [smul_grpGerm, grpStalkMap_grpGerm, grpStalkMap_grpGerm, smul_grpGerm]

end ContAction
