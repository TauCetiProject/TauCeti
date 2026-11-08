/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# The connecting map of an extension of sheaves of groups

Let `1 → A → B → Q → 1` be a short exact sequence of sheaves of groups on a site `(C, J)`:
`A → B` is injective on sections, its image is the kernel of `B → Q`, and `B → Q` is locally
surjective. A global section `q` of `Q` has a sheaf of lifts `U ↦ {b ∈ B(U) | b ↦ q|_U}`, on
which `A` acts by left multiplication. It is an `A`-torsor, and its class is the value of the
connecting map `Q(C) → H¹(A)` at `q`.

This file constructs the connecting map and proves the two exactness statements about it which
do not involve `H¹(B)`:

* exactness at `Q(C)`: the class of `q` is trivial if and only if `q` lifts to a global section
  of `B`;
* its fibres are the orbits of the global sections of `B`, acting on those of `Q` by right
  multiplication through `B → Q`.

## Main declarations

* `CategoryTheory.Sheaf.IsGroupExtension i π`: the sequence `1 → A → B → Q → 1` given by
  `i : A ⟶ B` and `π : B ⟶ Q` is exact.
* `CategoryTheory.Sheaf.IsGroupExtension.lifts`: the `A`-torsor of local lifts of a global
  section of `Q`.
* `CategoryTheory.Sheaf.IsGroupExtension.liftsObjEquiv`: the sections of the torsor of lifts are
  the lifts to `B`.
* `CategoryTheory.Sheaf.NonabelianH1.connecting`: the connecting map `Q(C) → H¹(A)`.
* `CategoryTheory.Sheaf.NonabelianH1.connecting_eq_one_iff`: exactness at `Q(C)`.
* `CategoryTheory.Sheaf.NonabelianH1.connecting_eq_connecting_iff`: the fibres of the connecting
  map are the orbits of `B(C)`.

## References

* J.-P. Serre, *Galois cohomology*, Chapter I, §5.5, Proposition 38, for the analogous
  statements in the nonabelian cohomology of profinite groups.
* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §3.3, for the connecting map of an
  extension of sheaves of groups.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A B Q : Sheaf J GrpCat.{w}}

/-- The sequence `1 → A → B → Q → 1` of sheaves of groups given by `i` and `π` is exact: `i` is
injective on sections, its image is the kernel of `π` on sections, and `π` is locally
surjective. -/
structure IsGroupExtension (i : A ⟶ B) (π : B ⟶ Q) : Prop where
  /-- The map `A → B` is injective on sections. -/
  injective (U : Cᵒᵖ) : Function.Injective (i.hom.app U)
  /-- On sections, the image of `A → B` is the kernel of `B → Q`. -/
  range_eq_ker (U : Cᵒᵖ) : (i.hom.app U).hom.range = (π.hom.app U).hom.ker
  /-- The map `B → Q` is locally surjective. -/
  isLocallySurjective : IsLocallySurjective π

namespace IsGroupExtension

variable {i : A ⟶ B} {π : B ⟶ Q} (hE : IsGroupExtension i π)

include hE in
/-- The composite `A → B → Q` is trivial on sections. -/
@[simp]
lemma app_app_eq_one {U : Cᵒᵖ} (a : A.obj.obj U) : π.hom.app U (i.hom.app U a) = 1 :=
  (hE.range_eq_ker U).le ⟨a, rfl⟩

include hE in
/-- A section of `B` in the kernel of `π` comes from a section of `A`. -/
lemma exists_app_eq {U : Cᵒᵖ} {b : B.obj.obj U} (hb : π.hom.app U b = 1) :
    ∃ a, i.hom.app U a = b :=
  (hE.range_eq_ker U).ge hb

variable (π) in
/-- The subpresheaf of `B`, viewed as a presheaf of sets, of lifts of a global section `q` of `Q`:
its sections over `U` are the sections `b` of `B` over `U` with `π b = q|_U`. -/
private def liftsSubfunctor (q : (Q.obj ⋙ forget GrpCat).sections) :
    Subfunctor (B.obj ⋙ forget GrpCat) where
  obj U := {b | π.hom.app U b = q.1 U}
  map f b hb := Set.mem_preimage.2 <| Set.mem_ofPred.2 <|
    (NatTrans.naturality_apply π.hom f b).trans ((congrArg _ (Set.mem_ofPred.1 hb)).trans (q.2 f))

variable (π) in
/-- The presheaf of lifts of a global section `q` of `Q`: its sections over `U` are the sections
`b` of `B` over `U` with `π b = q|_U`. -/
def liftsPresheaf (q : (Q.obj ⋙ forget GrpCat).sections) : Cᵒᵖ ⥤ Type w :=
  (liftsSubfunctor π q).toFunctor

variable (π) in
/-- The sections over `U` of the presheaf of lifts of `q` are the sections of `B` over `U` lifting
`q`. -/
def liftsPresheafObjEquiv (q : (Q.obj ⋙ forget GrpCat).sections) (U : Cᵒᵖ) :
    (liftsPresheaf π q).obj U ≃ {b : B.obj.obj U // π.hom.app U b = q.1 U} :=
  Equiv.refl _

variable (π) in
@[simp]
lemma liftsPresheafObjEquiv_map (q : (Q.obj ⋙ forget GrpCat).sections) {U V : Cᵒᵖ} (f : U ⟶ V)
    (b : (liftsPresheaf π q).obj U) :
    (liftsPresheafObjEquiv π q V ((liftsPresheaf π q).map f b)).1 =
      B.obj.map f (liftsPresheafObjEquiv π q U b).1 :=
  (rfl)

variable (π) in
/-- The presheaf of lifts is a sheaf: a section of `B` is a lift of `q` as soon as it is one
locally, because `Q` is separated. -/
lemma isSheaf_liftsPresheaf (q : (Q.obj ⋙ forget GrpCat).sections) :
    Presheaf.IsSheaf J (liftsPresheaf π q) := by
  have hB := (isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget GrpCat.{w})).obj B).property
  have hQ := (isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget GrpCat.{w})).obj Q).property
  refine (isSheaf_iff_isSheaf_of_type J _).2 (((liftsSubfunctor π q).isSheaf_iff hB).2 ?_)
  intro U b hb
  refine (hQ.isSeparated _ hb).ext fun V f hf ↦ ?_
  exact (NatTrans.naturality_apply π.hom f.op b).symm.trans (hf.trans (q.2 f.op).symm)

/-- The `A`-torsor of lifts of a global section `q` of `Q`: the sheaf `liftsPresheaf π q`, on
which a section `a` of `A` acts by `b ↦ i a * b`. Use `liftsObjEquiv` to identify its sections
with lifts of `q` to `B`. -/
def lifts (q : (Q.obj ⋙ forget GrpCat).sections) : Torsor A where
  sheaf := ⟨liftsPresheaf π q, isSheaf_liftsPresheaf π q⟩
  mulAction U :=
    { smul a b := (liftsPresheafObjEquiv π q U).symm
        ⟨i.hom.app U a * (liftsPresheafObjEquiv π q U b).1, by
          rw [map_mul, hE.app_app_eq_one, one_mul, (liftsPresheafObjEquiv π q U b).2]⟩
      one_smul b := (liftsPresheafObjEquiv π q U).symm_apply_eq.2 <| Subtype.ext <|
        (congrArg (· * _) (map_one _)).trans (one_mul _)
      mul_smul a a' b := congrArg (liftsPresheafObjEquiv π q U).symm <| Subtype.ext <|
        (congrArg (· * _) (map_mul _ a a')).trans (mul_assoc _ _ _) }
  map_smul U V f a b := Subtype.ext <| (map_mul (ConcreteCategory.hom (B.obj.map f)) _ b.1).trans
    (congrArg (· * B.obj.map f b.1) (NatTrans.naturality_apply i.hom f a).symm)
  coversTop X := by
    have := hE.isLocallySurjective
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J π.hom (q.1 (op X)))
    rintro V g ⟨b, hb⟩
    exact ⟨⟨V, ⟨⟨b, hb.trans (q.2 g.op)⟩⟩⟩, ⟨𝟙 V⟩⟩
  bijective U := by
    refine ⟨fun ⟨a, b⟩ ⟨a', b'⟩ h ↦ ?_, fun ⟨c, b⟩ ↦ ?_⟩
    · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 h
      exact Prod.ext (hE.injective U (mul_right_cancel (congrArg Subtype.val h₁))) rfl
    · let e := liftsPresheafObjEquiv π q U
      obtain ⟨a, ha⟩ := hE.exists_app_eq (b := (e c).1 * (e b).1⁻¹) (by
        rw [map_mul, map_inv, (e c).2, (e b).2, mul_inv_cancel])
      exact ⟨(a, b), Prod.ext (e.injective (Subtype.ext ((congrArg (· * (e b).1) ha).trans
        (inv_mul_cancel_right _ _)))) rfl⟩

variable (q : (Q.obj ⋙ forget GrpCat).sections)

lemma lifts_sheaf_obj : (hE.lifts q).sheaf.obj = liftsPresheaf π q :=
  (rfl)

/-- The sections over `U` of the torsor of lifts of `q` are the sections of `B` over `U` lifting
`q`. -/
def liftsObjEquiv (U : Cᵒᵖ) :
    (hE.lifts q).sheaf.obj.obj U ≃ {b : B.obj.obj U // π.hom.app U b = q.1 U} :=
  liftsPresheafObjEquiv π q U

@[simp]
lemma liftsObjEquiv_smul {U : Cᵒᵖ} (a : A.obj.obj U) (b : (hE.lifts q).sheaf.obj.obj U) :
    (hE.liftsObjEquiv q U (a • b)).1 = i.hom.app U a * (hE.liftsObjEquiv q U b).1 :=
  (rfl)

@[simp]
lemma liftsObjEquiv_map {U V : Cᵒᵖ} (f : U ⟶ V) (b : (hE.lifts q).sheaf.obj.obj U) :
    (hE.liftsObjEquiv q V ((hE.lifts q).sheaf.obj.map f b)).1 =
      B.obj.map f (hE.liftsObjEquiv q U b).1 :=
  (rfl)

/-- Global sections of the torsor of lifts of `q` are the global sections of `B` lifting `q`. -/
def liftsSectionsEquiv : (hE.lifts q).sheaf.obj.sections ≃
    {b : (B.obj ⋙ forget GrpCat).sections // ∀ U, π.hom.app U (b.1 U) = q.1 U} where
  toFun s := ⟨⟨fun U ↦ (s.1 U).1, fun f ↦ congrArg Subtype.val (s.2 f)⟩, fun U ↦ (s.1 U).2⟩
  invFun b := ⟨fun U ↦ ⟨b.1.1 U, b.2 U⟩, fun f ↦ Subtype.ext (b.1.2 f)⟩

@[simp]
lemma liftsSectionsEquiv_apply_val (s : (hE.lifts q).sheaf.obj.sections) (U : Cᵒᵖ) :
    (hE.liftsSectionsEquiv q s).1.1 U = (hE.liftsObjEquiv q U (s.1 U)).1 :=
  (rfl)

@[simp]
lemma liftsObjEquiv_liftsSectionsEquiv_symm_apply
    (b : {b : (B.obj ⋙ forget GrpCat).sections // ∀ U, π.hom.app U (b.1 U) = q.1 U})
    (U : Cᵒᵖ) :
    hE.liftsObjEquiv q U (((hE.liftsSectionsEquiv q).symm b).1 U) = ⟨b.1.1 U, b.2 U⟩ :=
  (rfl)

variable {q} in
/-- Right multiplication by a global section `c` of `B` is a morphism from the torsor of lifts of
`q` to the torsor of lifts of `q'` when `π c = q⁻¹ q'`. -/
private def liftsMulRight (q' : (Q.obj ⋙ forget GrpCat).sections)
    (c : (B.obj ⋙ forget GrpCat).sections) (h : ∀ U, π.hom.app U (c.1 U) = (q.1 U)⁻¹ * q'.1 U) :
    hE.lifts q ⟶ hE.lifts q' where
  hom := ObjectProperty.homMk
    -- `c.1 U` has type `(B.obj ⋙ forget GrpCat).obj U`, for which no `HMul` instance is found,
    -- so the multiplication of the group `B.obj.obj U` is given explicitly.
    { app U := ↾fun b ↦ (hE.liftsObjEquiv q' U).symm
        ⟨@HMul.hMul (B.obj.obj U) (B.obj.obj U) _ _ (hE.liftsObjEquiv q U b).1 (c.1 U), by
          rw [map_mul, (hE.liftsObjEquiv q U b).2, h, mul_inv_cancel_left]⟩
      naturality U V f := by
        ext b
        exact Subtype.ext ((map_mul (ConcreteCategory.hom (B.obj.map f)) b.1 (c.1 U)).trans
          (congrArg (B.obj.map f b.1 * ·) (c.2 f))).symm }
  map_smul U a b := Subtype.ext (mul_assoc _ _ _)

variable {q} in
/-- For a morphism `f` of torsors of lifts, `b⁻¹ * f b` does not depend on the lift `b`. -/
private lemma inv_mul_hom_app_eq {q' : (Q.obj ⋙ forget GrpCat).sections}
    (f : hE.lifts q ⟶ hE.lifts q') {U : Cᵒᵖ} (b b' : (hE.lifts q).sheaf.obj.obj U) :
    (hE.liftsObjEquiv q U b).1⁻¹ * (hE.liftsObjEquiv q' U (f.hom.hom.app U b)).1 =
      (hE.liftsObjEquiv q U b').1⁻¹ * (hE.liftsObjEquiv q' U (f.hom.hom.app U b')).1 := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (A.obj.obj U) b b'
  rw [f.map_smul, liftsObjEquiv_smul, liftsObjEquiv_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]

variable {q} in
/-- Restricting `b⁻¹ * f b` along `g` gives the same expression for the restriction of `b`. -/
private lemma map_inv_mul_hom_app {q' : (Q.obj ⋙ forget GrpCat).sections}
    (f : hE.lifts q ⟶ hE.lifts q') {U V : Cᵒᵖ} (g : U ⟶ V) (b : (hE.lifts q).sheaf.obj.obj U) :
    B.obj.map g ((hE.liftsObjEquiv q U b).1⁻¹ * (hE.liftsObjEquiv q' U (f.hom.hom.app U b)).1) =
      (hE.liftsObjEquiv q V ((hE.lifts q).sheaf.obj.map g b)).1⁻¹ *
        (hE.liftsObjEquiv q' V (f.hom.hom.app V ((hE.lifts q).sheaf.obj.map g b))).1 := by
  rw [map_mul, map_inv, NatTrans.naturality_apply f.hom.hom g b, liftsObjEquiv_map,
    liftsObjEquiv_map]

end IsGroupExtension

namespace NonabelianH1

variable {i : A ⟶ B} {π : B ⟶ Q}

/-- The connecting map `Q(C) → H¹(A)` of a short exact sequence `1 → A → B → Q → 1` of sheaves of
groups: a global section of `Q` is sent to the class of its torsor of lifts to `B`. -/
def connecting (hE : IsGroupExtension i π) (q : (Q.obj ⋙ forget GrpCat).sections) :
    NonabelianH1 A :=
  mk (hE.lifts q)

variable (hE : IsGroupExtension i π)

lemma connecting_def (q : (Q.obj ⋙ forget GrpCat).sections) :
    connecting hE q = mk (hE.lifts q) :=
  (rfl)

/-- Exactness of `B(C) → Q(C) → H¹(A)` at `Q(C)`: the connecting map sends a global section of
`Q` to the base point if and only if it lifts to a global section of `B`. -/
theorem connecting_eq_one_iff (q : (Q.obj ⋙ forget GrpCat).sections) :
    connecting hE q = 1 ↔
      ∃ b : (B.obj ⋙ forget GrpCat).sections, ∀ U, π.hom.app U (b.1 U) = q.1 U := by
  rw [connecting_def, mk_eq_one_iff]
  refine ⟨fun ⟨s, hs⟩ ↦ ⟨_, (hE.liftsSectionsEquiv q ⟨s, hs⟩).2⟩, fun ⟨b, hb⟩ ↦ ?_⟩
  exact ⟨_, ((hE.liftsSectionsEquiv q).symm ⟨b, hb⟩).2⟩

/-- The connecting map sends the unit section to the base point. -/
@[simp]
lemma connecting_one : connecting hE 1 = 1 :=
  (connecting_eq_one_iff hE 1).2 ⟨1, fun _ ↦ map_one _⟩

/-- The fibres of the connecting map `Q(C) → H¹(A)` are the orbits of `B(C)` acting on `Q(C)` by
right multiplication through `π`: two global sections `q`, `q'` of `Q` have isomorphic torsors
of lifts if and only if `q' = q * π c` for a global section `c` of `B`. -/
theorem connecting_eq_connecting_iff (q q' : (Q.obj ⋙ forget GrpCat).sections) :
    connecting hE q = connecting hE q' ↔
      ∃ c : (B.obj ⋙ forget GrpCat).sections, ∀ U, π.hom.app U (c.1 U) = (q.1 U)⁻¹ * q'.1 U := by
  rw [connecting_def, connecting_def, mk_eq_mk_iff]
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨c, hc⟩ ↦ ⟨asIso (hE.liftsMulRight q' c hc)⟩⟩
  -- Glue the local sections `b⁻¹ * e b` of `B`, for `b` a local lift of `q`.
  let x : Presheaf.FamilyOfElementsOnObjects (B.obj ⋙ forget GrpCat)
      fun j : {U : C // Nonempty ((hE.lifts q).sheaf.obj.obj (op U))} ↦ j.1 :=
    fun j ↦ (hE.liftsObjEquiv q _ j.2.some).1⁻¹ *
      (hE.liftsObjEquiv q' _ (e.hom.hom.hom.app _ j.2.some)).1
  have hx : x.IsCompatible := fun Z j k g₁ g₂ ↦
    (hE.map_inv_mul_hom_app e.hom g₁.op _).trans ((hE.inv_mul_hom_app_eq e.hom _ _).trans
      (hE.map_inv_mul_hom_app e.hom g₂.op _).symm)
  obtain ⟨c, hc, -⟩ := hx.existsUnique_section (hE.lifts q).coversTop
    ((sheafCompose J (forget GrpCat.{w})).obj B).property
  refine ⟨c, fun U ↦ congrArg (·.1 U) ((hE.lifts q).coversTop.sections_ext
    (F := (sheafCompose J (forget GrpCat.{w})).obj Q)
    (x := ⟨fun U ↦ π.hom.app U (c.1 U), fun f ↦ ?_⟩) (y := q⁻¹ * q') fun j ↦ ?_)⟩
  · exact (NatTrans.naturality_apply π.hom f (c.1 _)).symm.trans (congrArg _ (c.2 f))
  · refine (congrArg (π.hom.app _) (hc j)).trans ?_
    rw [map_mul, map_inv, (hE.liftsObjEquiv q _ j.2.some).2,
      (hE.liftsObjEquiv q' _ (e.hom.hom.hom.app _ j.2.some)).2]
    -- Multiplication and inversion of global sections are computed objectwise.
    rfl

end NonabelianH1

end CategoryTheory.Sheaf
