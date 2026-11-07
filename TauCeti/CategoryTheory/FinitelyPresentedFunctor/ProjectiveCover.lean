/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Projective covers of functors

Let `C` be a preadditive category and `F : Cᵒᵖ ⥤ AddCommGrpCat` a functor. A *projective cover*
of `F` is an epimorphism `p : (-, P) ⟶ F` from a representable functor which is *right minimal*:
every endomorphism `φ` of `P` with `(-, φ) ≫ p = p` is an isomorphism. A functor with a
projective cover is finitely generated. In the functorial approach to Auslander-Reiten theory,
minimal projective presentations of finitely generated functors are built from such covers.

The notion is phrased through representable functors rather than through projective objects of
the functor category: a representable functor `(-, P)` is projective among the additive functors,
but it need not be projective in the whole category `Cᵒᵖ ⥤ AddCommGrpCat`, so the general
`TauCeti.IsEssentialEpi` is not the right notion there. The lifting property that is always
available, along epimorphisms out of representable functors
(`CategoryTheory.exists_preadditiveYoneda_map_comp_eq`), is all that the arguments below use.

* **The radical criterion.** An epimorphism `p : (-, P) ⟶ F` is right minimal exactly when every
  `ψ : P ⟶ P` with `(-, ψ) ≫ p = 0` lies in the radical of `End P`
  (`TauCeti.isRepresentableProjectiveCover_iff`).
* **Rigidity and uniqueness.** A morphism between the sources of two projective covers of `F`
  commuting with them is an isomorphism, so projective covers are unique up to isomorphism. A
  projective cover `(-, P) ⟶ F` is a retract of every epimorphism `(-, Y) ⟶ F`: there is a split
  epimorphism `Y ⟶ P` compatible with the two.
* **Tops of representable functors.** For an ideal `I` of `C`, the quotient
  `(-, X) ⟶ (-, X) / I(-, X)`, read as the functor `Z ↦ Hom_{C/I}(Z, X)` of the quotient category,
  is a projective cover exactly when `I(X, X)` lies in the radical of `End X`. In particular the
  quotient `(-, X) ⟶ S_X = (-, X) / rad(-, X)` by the radical is a projective cover for every `X`,
  and when `End X` is local the functor `S_X` is simple.
* **Existence.** A quotient of `(-, P₁ ⊞ ⋯ ⊞ Pₙ)` with every `End Pᵢ` local has a projective
  cover; so in a Krull-Schmidt category every finitely generated functor has one. If an
  epimorphism `p : (-, P₁ ⊞ ⋯ ⊞ Pₙ) ⟶ F` with local `End Pᵢ` is not right minimal, the radical
  criterion gives `ψ` outside the radical with `(-, ψ) ≫ p = 0`. One component `Pᵢ ⟶ Pⱼ` of `ψ`
  is then an isomorphism, which lets the summand `Pⱼ` be dropped while keeping an epimorphism
  onto `F`; the number of summands decreases.

## Main definitions

* `TauCeti.IsRepresentableProjectiveCover`: `p : (-, P) ⟶ F` is a projective cover of `F`.

## Main results

* `TauCeti.isRepresentableProjectiveCover_iff`: the radical criterion for right minimality.
* `TauCeti.IsRepresentableProjectiveCover.isIso_of_comp_eq`: rigidity, and
  `TauCeti.IsRepresentableProjectiveCover.exists_iso` the uniqueness of projective covers.
* `TauCeti.IsRepresentableProjectiveCover.exists_comp_eq_and_isSplitEpi`: a projective cover is a
  retract of every epimorphism from a representable functor.
* `TauCeti.MorphismIdeal.isRepresentableProjectiveCover_preadditiveYonedaMap_quotientFunctor_iff`:
  the cover of `(-, X) / I(-, X)`, and
  `TauCeti.isRepresentableProjectiveCover_preadditiveYonedaMap_jacobsonRadicalIdeal` its radical
  case.
* `TauCeti.simple_comp_preadditiveYoneda_obj_quotientFunctor_jacobsonRadicalIdeal`: `S_X` is simple
  when `End X` is local.
* `TauCeti.exists_isRepresentableProjectiveCover_of_epi_biproduct`: a quotient of the
  representable functor of a finite biproduct of objects with local endomorphism rings has a
  projective cover, and `TauCeti.IsKrullSchmidt.exists_isRepresentableProjectiveCover` the
  resulting existence of projective covers of finitely generated functors in a Krull-Schmidt
  category.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Sections 3 and 4.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), I.2 and I.4.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}}

/-- A **projective cover** of a functor `F : Cᵒᵖ ⥤ AddCommGrpCat` by a representable functor: an
epimorphism `p : (-, P) ⟶ F` that is right minimal, in that every endomorphism `φ` of `P` with
`(-, φ) ≫ p = p` is an isomorphism. -/
structure IsRepresentableProjectiveCover {P : C} (p : preadditiveYoneda.obj P ⟶ F) : Prop where
  /-- A projective cover is an epimorphism. -/
  epi : Epi p
  /-- A projective cover is right minimal. -/
  isIso_of_preadditiveYoneda_map_comp_eq (φ : P ⟶ P) : preadditiveYoneda.map φ ≫ p = p → IsIso φ

/-- **The radical criterion.** An epimorphism `p : (-, P) ⟶ F` is a projective cover exactly
when every endomorphism `ψ` of `P` with `(-, ψ) ≫ p = 0` lies in the radical of `End P`. -/
theorem isRepresentableProjectiveCover_iff {P : C} (p : preadditiveYoneda.obj P ⟶ F) :
    IsRepresentableProjectiveCover p ↔
      Epi p ∧ ∀ ψ : P ⟶ P, preadditiveYoneda.map ψ ≫ p = 0 → ψ ∈ jacobsonRadical P P := by
  constructor
  · rintro ⟨hp, hmin⟩
    exact ⟨hp, fun ψ hψ ↦ mem_jacobsonRadical_iff_isIso_id_sub_comp_left.2 fun g ↦
      hmin _ (by simp [hψ])⟩
  · rintro ⟨hp, hrad⟩
    refine ⟨hp, fun φ hφ ↦ ?_⟩
    have h := hrad (𝟙 P - φ) (by simp [hφ])
    simpa using mem_jacobsonRadical_iff_isIso_id_sub_comp_right.1 h (𝟙 P)

namespace IsRepresentableProjectiveCover

variable {P Q : C} {p : preadditiveYoneda.obj P ⟶ F} {q : preadditiveYoneda.obj Q ⟶ F}

/-- A functor with a projective cover is finitely generated. -/
theorem isFinitelyGeneratedFunctor (hp : IsRepresentableProjectiveCover p) :
    IsFinitelyGeneratedFunctor F :=
  isFinitelyGeneratedFunctor_def.2 ⟨P, p, hp.epi⟩

/-- **Rigidity of projective covers.** A morphism `u : P ⟶ Q` between the sources of two
projective covers of `F` that commutes with them is an isomorphism. -/
theorem isIso_of_comp_eq (hp : IsRepresentableProjectiveCover p)
    (hq : IsRepresentableProjectiveCover q) {u : P ⟶ Q} (hu : preadditiveYoneda.map u ≫ q = p) :
    IsIso u := by
  have := hp.epi
  obtain ⟨v, hv⟩ := exists_preadditiveYoneda_map_comp_eq p q
  have huv : IsIso (u ≫ v) :=
    hp.isIso_of_preadditiveYoneda_map_comp_eq _ (by rw [Functor.map_comp, Category.assoc, hv, hu])
  have hvu : IsIso (v ≫ u) :=
    hq.isIso_of_preadditiveYoneda_map_comp_eq _ (by rw [Functor.map_comp, Category.assoc, hu, hv])
  have : Mono u := mono_of_mono u v
  have : IsSplitEpi u := .mk' ⟨inv (v ≫ u) ≫ v, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi u

/-- **Uniqueness of projective covers.** Two projective covers of `F` are isomorphic by an
isomorphism commuting with them. -/
theorem exists_iso (hp : IsRepresentableProjectiveCover p) (hq : IsRepresentableProjectiveCover q) :
    ∃ e : P ≅ Q, preadditiveYoneda.map e.hom ≫ q = p := by
  have := hq.epi
  obtain ⟨u, hu⟩ := exists_preadditiveYoneda_map_comp_eq q p
  have := hp.isIso_of_comp_eq hq hu
  exact ⟨asIso u, hu⟩

/-- **A projective cover is a retract of every epimorphism from a representable functor.** If
`p : (-, P) ⟶ F` is a projective cover and `q : (-, Y) ⟶ F` is an epimorphism, then `q` factors
through `p` by a split epimorphism `Y ⟶ P`. -/
theorem exists_comp_eq_and_isSplitEpi (hp : IsRepresentableProjectiveCover p) {Y : C}
    (q : preadditiveYoneda.obj Y ⟶ F) [Epi q] :
    ∃ u : Y ⟶ P, preadditiveYoneda.map u ≫ p = q ∧ IsSplitEpi u := by
  have := hp.epi
  obtain ⟨u, hu⟩ := exists_preadditiveYoneda_map_comp_eq p q
  obtain ⟨v, hv⟩ := exists_preadditiveYoneda_map_comp_eq q p
  have hvu : IsIso (v ≫ u) :=
    hp.isIso_of_preadditiveYoneda_map_comp_eq _ (by rw [Functor.map_comp, Category.assoc, hu, hv])
  exact ⟨u, hu, .mk' ⟨inv (v ≫ u) ≫ v, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩

/-- Composing a projective cover with an isomorphism of functors gives a projective cover. -/
theorem comp_isIso (hp : IsRepresentableProjectiveCover p) (e : F ⟶ G) [IsIso e] :
    IsRepresentableProjectiveCover (p ≫ e) where
  epi := by have := hp.epi; infer_instance
  isIso_of_preadditiveYoneda_map_comp_eq φ hφ :=
    hp.isIso_of_preadditiveYoneda_map_comp_eq φ (by simpa using hφ =≫ inv e)

end IsRepresentableProjectiveCover

/-- An epimorphism out of the representable functor of a zero object is a projective cover. In
particular `(-, 0) ⟶ 0` is a projective cover of the zero functor. -/
theorem isRepresentableProjectiveCover_of_isZero {P : C} (hP : IsZero P)
    (p : preadditiveYoneda.obj P ⟶ F) [Epi p] : IsRepresentableProjectiveCover p where
  epi := inferInstance
  isIso_of_preadditiveYoneda_map_comp_eq φ _ := by
    rw [hP.eq_of_src φ (𝟙 P)]
    infer_instance

/-! ### Tops of representable functors -/

section Top

/-- For a full additive functor `Φ : C ⥤ D`, the epimorphism `(-, X) ⟶ (Φ -, Φ X)` applying `Φ`
is a projective cover exactly when every endomorphism of `X` killed by `Φ` is radical. -/
theorem isRepresentableProjectiveCover_preadditiveYonedaMap_iff {D : Type*} [Category.{v} D]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] [Φ.Full] (X : C) :
    IsRepresentableProjectiveCover (Φ.preadditiveYonedaMap X) ↔
      ∀ ψ : X ⟶ X, Φ.map ψ = 0 → ψ ∈ jacobsonRadical X X := by
  simp only [isRepresentableProjectiveCover_iff,
    Functor.preadditiveYoneda_map_comp_preadditiveYonedaMap_eq_zero_iff]
  exact and_iff_right inferInstance

/-- **Projective covers of the tops of representable functors.** For an ideal `I` of `C`, the
quotient `(-, X) ⟶ (-, X) / I(-, X)`, the functor `Z ↦ Hom_{C/I}(Z, X)` of the quotient
category, is a projective cover exactly when `I(X, X)` lies in the radical of `End X`. -/
theorem MorphismIdeal.isRepresentableProjectiveCover_preadditiveYonedaMap_quotientFunctor_iff
    (I : MorphismIdeal C) (X : C) :
    IsRepresentableProjectiveCover (I.quotientFunctor.preadditiveYonedaMap X) ↔
      I.hom X X ≤ jacobsonRadical X X := by
  rw [isRepresentableProjectiveCover_preadditiveYonedaMap_iff, IsConcreteLE.le_iff]
  simp only [MorphismIdeal.quotientFunctor_map_eq_zero_iff]

/-- **The radical top of a representable functor.** For every object `X`, the quotient
`(-, X) ⟶ S_X = (-, X) / rad(-, X)` is a projective cover. -/
theorem isRepresentableProjectiveCover_preadditiveYonedaMap_jacobsonRadicalIdeal (X : C) :
    IsRepresentableProjectiveCover
      ((jacobsonRadicalIdeal C).quotientFunctor.preadditiveYonedaMap X) :=
  ((jacobsonRadicalIdeal C).isRepresentableProjectiveCover_preadditiveYonedaMap_quotientFunctor_iff
    X).2 (jacobsonRadicalIdeal_hom X X).le

/-- **The top `S_X = (-, X) / rad(-, X)` is a simple functor** when `End X` is local. -/
theorem simple_comp_preadditiveYoneda_obj_quotientFunctor_jacobsonRadicalIdeal (X : C)
    [IsLocalRing (End X)] :
    Simple ((jacobsonRadicalIdeal C).quotientFunctor.op ⋙
      preadditiveYoneda.obj ((jacobsonRadicalIdeal C).quotientFunctor.obj X)) := by
  set Q := (jacobsonRadicalIdeal C).quotientFunctor
  have hrad {Z : C} (h : Z ⟶ X) : Q.map h = 0 ↔ h ∈ jacobsonRadical Z X := by
    simp [Q]
  refine ⟨fun {H} f _ ↦ ⟨fun _ h0 ↦ ?_, fun hf ↦ ?_⟩⟩
  · -- `S_X` is nonzero: the class of `𝟙 X` survives, as `𝟙 X` is not radical.
    have h1 : 𝟙 (Q.op ⋙ preadditiveYoneda.obj (Q.obj X)) = 0 :=
      (IsIso.inv_hom_id f).symm.trans ((congrArg (inv f ≫ ·) h0).trans comp_zero)
    have h2 : Q.map (𝟙 X) = 0 := congrArg (fun α ↦ α.app (op X) (Q.map (𝟙 X))) h1
    exact mem_jacobsonRadical_iff_not_isIso.1 ((hrad _).1 h2) inferInstance
  · -- A nonzero subfunctor contains the class of a nonradical, hence split, epimorphism
    -- `h : Z ⟶ X`, hence the class of `𝟙 X`, which generates `S_X`.
    obtain ⟨Z, y, hy⟩ : ∃ (Z : Cᵒᵖ) (y : H.obj Z), f.app Z y ≠ 0 := by
      by_contra! h
      exact hf (NatTrans.ext (funext fun Z ↦ AddCommGrpCat.ext (h Z)))
    obtain ⟨h, hh⟩ := Q.map_surjective (f.app Z y)
    have : IsSplitEpi h := by
      by_contra hse
      exact hy (hh ▸ (hrad h).2 (mem_jacobsonRadical_iff_not_isSplitEpi.2 hse))
    have hX : f.app (op X) (H.map (section_ h).op y) = Q.map (𝟙 X) := by
      rw [NatTrans.naturality_apply, ← hh]
      exact (Q.map_comp _ h).symm.trans (by rw [Quiver.Hom.unop_op, IsSplitEpi.id])
    have (W : Cᵒᵖ) : Epi (f.app W) := by
      refine (AddCommGrpCat.epi_iff_surjective _).2 fun x ↦ ?_
      obtain ⟨k, rfl⟩ := Q.map_surjective x
      refine ⟨H.map k.op (H.map (section_ h).op y), ?_⟩
      rw [NatTrans.naturality_apply, hX]
      exact (Q.map_comp _ (𝟙 X)).symm.trans (by rw [Quiver.Hom.unop_op, Category.comp_id])
    have : Epi f := NatTrans.epi_of_epi_app f
    exact isIso_of_mono_of_epi f

end Top

/-! ### Existence in Krull-Schmidt categories -/

section KrullSchmidt

variable [HasFiniteBiproducts C]

/-- An epimorphism onto `F` out of the representable functor of a biproduct of objects with
local endomorphism rings that is not a projective cover can be replaced by one out of a
biproduct with one summand fewer. -/
private theorem exists_epi_of_not_isRepresentableProjectiveCover {J : Type} [Finite J]
    (P : J → C) (hP : ∀ j, IsLocalRing (End (P j))) (p : preadditiveYoneda.obj (⨁ P) ⟶ F) [Epi p]
    (hp : ¬ IsRepresentableProjectiveCover p) :
    ∃ j : J, Epi (preadditiveYoneda.map (biproduct.fromSubtype P (· ≠ j)) ≫ p) := by
  classical
  -- By the radical criterion some `ψ` outside the radical satisfies `(-, ψ) ≫ p = 0`; one of its
  -- components `P i ⟶ P j` is then outside the radical, hence an isomorphism.
  obtain ⟨ψ, hψ, hψrad⟩ : ∃ ψ : ⨁ P ⟶ ⨁ P, preadditiveYoneda.map ψ ≫ p = 0 ∧
      ψ ∉ jacobsonRadical (⨁ P) (⨁ P) := by
    by_contra! h
    exact hp ((isRepresentableProjectiveCover_iff p).2 ⟨inferInstance, h⟩)
  obtain ⟨i, hi⟩ : ∃ i, biproduct.ι P i ≫ ψ ∉ jacobsonRadical (P i) (⨁ P) := by
    by_contra! h
    exact hψrad ((mem_jacobsonRadical_biproduct_left_iff P).2 h)
  obtain ⟨j, hj⟩ : ∃ j, (biproduct.ι P i ≫ ψ) ≫ biproduct.π P j ∉ jacobsonRadical (P i) (P j) := by
    by_contra! h
    exact hi ((mem_jacobsonRadical_biproduct_right_iff P).2 h)
  have := hP i
  have := hP j
  obtain ⟨u, hu, hc⟩ : ∃ u : P i ⟶ ⨁ P, preadditiveYoneda.map u ≫ p = 0 ∧
      IsIso (u ≫ biproduct.π P j) :=
    ⟨biproduct.ι P i ≫ ψ, by rw [Functor.map_comp, Category.assoc, hψ, comp_zero],
      not_not.1 fun h ↦ hj (mem_jacobsonRadical_iff_not_isIso.2 h)⟩
  refine ⟨j, ?_⟩
  -- Since `u ≫ π j` is invertible, the identity of `⨁ P` is the sum of a map through `u` and a
  -- map through the summands other than `P j`.
  set e := biproduct.fromSubtype P (· ≠ j)
  set r := biproduct.toSubtype P (· ≠ j) -
    biproduct.π P j ≫ inv (u ≫ biproduct.π P j) ≫ u ≫ biproduct.toSubtype P (· ≠ j)
  have key : 𝟙 (⨁ P) = biproduct.π P j ≫ inv (u ≫ biproduct.π P j) ≫ u + r ≫ e := by
    refine biproduct.hom_ext _ _ fun k ↦ ?_
    by_cases hk : k = j
    · subst hk
      simp [e, r]
    · simp [e, r, hk]
  have hfac : preadditiveYoneda.map r ≫ preadditiveYoneda.map e ≫ p = p := by
    conv_rhs => rw [← Category.id_comp p, ← preadditiveYoneda.map_id, key]
    simp only [Functor.map_add, Preadditive.add_comp, Functor.map_comp, Category.assoc, hu,
      comp_zero, zero_add]
  exact epi_of_epi_fac hfac

/-- An epimorphism onto `F` out of the representable functor of a finite biproduct of objects
with local endomorphism rings can be shrunk to a projective cover of `F`. -/
private theorem exists_isRepresentableProjectiveCover_of_biproduct (n : ℕ) :
    ∀ {J : Type} [Fintype J] (P : J → C), Fintype.card J = n → (∀ j, IsLocalRing (End (P j))) →
      ∀ (p : preadditiveYoneda.obj (⨁ P) ⟶ F), Epi p →
        ∃ (Q : C) (q : preadditiveYoneda.obj Q ⟶ F), IsRepresentableProjectiveCover q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro J _ P hn hP p hp
    by_cases hmin : IsRepresentableProjectiveCover p
    · exact ⟨_, p, hmin⟩
    classical
    obtain ⟨j, hj⟩ := exists_epi_of_not_isRepresentableProjectiveCover P hP p hmin
    exact ih _ (hn ▸ Fintype.card_subtype_lt (x := j) (by simp))
      (Subtype.restrict (· ≠ j) P) rfl (fun k ↦ hP k.1) _ hj

/-- A quotient of the representable functor `(-, P₁ ⊞ ⋯ ⊞ Pₙ)` of a finite biproduct of objects
with local endomorphism rings has a projective cover. -/
theorem exists_isRepresentableProjectiveCover_of_epi_biproduct {J : Type} [Finite J] (P : J → C)
    (hP : ∀ j, IsLocalRing (End (P j))) (p : preadditiveYoneda.obj (⨁ P) ⟶ F) [Epi p] :
    ∃ (Q : C) (q : preadditiveYoneda.obj Q ⟶ F), IsRepresentableProjectiveCover q := by
  have := Fintype.ofFinite J
  exact exists_isRepresentableProjectiveCover_of_biproduct _ P rfl hP p inferInstance

/-- **Projective covers exist in Krull-Schmidt categories.** In a Krull-Schmidt category every
finitely generated functor `F : Cᵒᵖ ⥤ AddCommGrpCat` has a projective cover. -/
theorem IsKrullSchmidt.exists_isRepresentableProjectiveCover [IsKrullSchmidt C]
    (hF : IsFinitelyGeneratedFunctor F) :
    ∃ (P : C) (p : preadditiveYoneda.obj P ⟶ F), IsRepresentableProjectiveCover p := by
  obtain ⟨Y, p, hp⟩ := isFinitelyGeneratedFunctor_def.1 hF
  obtain ⟨n, P, hP, ⟨e⟩⟩ := IsKrullSchmidt.exists_iso_biproduct Y
  exact exists_isRepresentableProjectiveCover_of_epi_biproduct P hP
    (preadditiveYoneda.map e.inv ≫ p)

end KrullSchmidt

end TauCeti
