/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Bicartesian

/-!
# The Yoneda `Ext¹` of an exact category

For an exact structure `E` on an additive category, an *extension* of `Z` by `X` is a conflation
`X ⟶ Y ⟶ Z` with these prescribed end terms. Two extensions are *Yoneda equivalent* when a
morphism of their middle terms is compatible with the inflations and the deflations; by the short
five lemma such a morphism is an isomorphism. The set `Ext¹_E(Z, X)` of equivalence classes is
the Yoneda `Ext¹` of the exact category, defined intrinsically, without an ambient abelian
category and without enough projectives or injectives.

This file constructs `Ext¹_E(Z, X)` as a pointed set with its two functorialities, which are the
operations every later use of extension classes is built from:

* contravariantly in `Z`, by base change of the deflation along `u : Z' ⟶ Z` (axiom E2op), and
  covariantly in `X`, by cobase change of the inflation along `v : X ⟶ X'` (axiom E2); the two
  actions commute;
* the class of the split conflation `X ⟶ X ⊞ Z ⟶ Z` is the base point, and a class is the base
  point exactly when its deflation is a split epimorphism, or equivalently its inflation is a
  split monomorphism.

For a conflation `X ⟶ Y ⟶ Z` with class `[e]`, the connecting maps `Hom(W, Z) → Ext¹_E(W, X)`,
`u ↦ u^* [e]`, and `Hom(X, W) → Ext¹_E(Z, W)`, `v ↦ v_* [e]`, are exact at their sources and at
their targets: `u^* [e]` is the base point exactly when `u` factors through the deflation, and a
class `ξ ∈ Ext¹_E(W, X)` is of the form `u^* [e]` exactly when its cobase change along the
inflation is the base point; dually for `v_* [e]`. These are the first terms of the two long
exact `Hom`–`Ext` sequences, and they are what converts the vanishing of extension classes into
the factorization properties of almost-split conflations.

## Main definitions

* `TauCeti.ExactStructure.Extension E Z X`: a conflation `X ⟶ Y ⟶ Z` of `E`.
* `TauCeti.ExactStructure.Extension.pullback` and `TauCeti.ExactStructure.Extension.pushout`:
  base change along `u : Z' ⟶ Z` and cobase change along `v : X ⟶ X'`.
* `TauCeti.ExactStructure.Extension.trivial E Z X`: the split extension `X ⟶ X ⊞ Z ⟶ Z`.
* `TauCeti.ExactStructure.Ext1 E Z X`: the Yoneda equivalence classes of extensions of `Z` by `X`,
  with `TauCeti.ExactStructure.Ext1.pullback`, `TauCeti.ExactStructure.Ext1.pushout` and the base
  point `0`.

## Main results

* `TauCeti.ExactStructure.Extension.rel_iff`: Yoneda equivalence is isomorphism of conflations
  fixing the end terms.
* `TauCeti.ExactStructure.Extension.rel_pullback` and
  `TauCeti.ExactStructure.Extension.pushout_rel`: the universal properties of base and cobase
  change, up to Yoneda equivalence.
* `TauCeti.ExactStructure.Ext1.pullback_id`, `TauCeti.ExactStructure.Ext1.pullback_pullback`,
  `TauCeti.ExactStructure.Ext1.pushout_id`, `TauCeti.ExactStructure.Ext1.pushout_pushout` and
  `TauCeti.ExactStructure.Ext1.pushout_pullback`: functoriality in both variables.
* `TauCeti.ExactStructure.Ext1.mk_eq_zero_iff_isSplitEpi` and
  `TauCeti.ExactStructure.Ext1.mk_eq_zero_iff_isSplitMono`: the base point is the class of the
  split conflations.
* `TauCeti.ExactStructure.Ext1.mk_pullback_eq_zero_iff` and
  `TauCeti.ExactStructure.Ext1.pushout_f_eq_zero_iff`: exactness of
  `Hom(W, Y) → Hom(W, Z) → Ext¹_E(W, X) → Ext¹_E(W, Y)` at `Hom(W, Z)` and at `Ext¹_E(W, X)`.
* `TauCeti.ExactStructure.Ext1.mk_pushout_eq_zero_iff` and
  `TauCeti.ExactStructure.Ext1.pullback_g_eq_zero_iff`: the dual statements for
  `Hom(Y, W) → Hom(X, W) → Ext¹_E(Z, W) → Ext¹_E(Y, W)`.
* For the split exact structure every `Ext¹` is a singleton.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>. Proposition 2.12 describes base and cobase change of a
  conflation, and Corollary 3.2 is the short five lemma.
* Saunders Mac Lane, *Homology*, Grundlehren **114**, Springer (1963), Chapter III, for the
  Yoneda description of `Ext¹` by extensions, its functoriality by pullback and pushout, and the
  exact sequences it satisfies, there for modules.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- An **extension** of `Z` by `X` for the exact structure `E`: a conflation `X ⟶ obj ⟶ Z` of `E`
with prescribed end terms. The middle term is part of the data. -/
structure Extension (Z X : C) where
  /-- The middle term of the conflation. -/
  obj : C
  /-- The inflation `X ⟶ obj`. -/
  f : X ⟶ obj
  /-- The deflation `obj ⟶ Z`. -/
  g : obj ⟶ Z
  /-- The composite of the inflation and the deflation vanishes. -/
  zero : f ≫ g = 0
  /-- `X ⟶ obj ⟶ Z` is a conflation of `E`. -/
  conflation : E.Conflation (ShortComplex.mk f g zero)

namespace Extension

attribute [reassoc (attr := simp)] zero

variable {E} {W X X' X'' Z Z' Z'' : C}

/-- The conflation underlying an extension. -/
abbrev shortComplex (e : E.Extension Z X) : ShortComplex C :=
  ShortComplex.mk e.f e.g e.zero

/-- The conflation underlying an extension is a kernel–cokernel pair. -/
theorem isKernelCokernelPair (e : E.Extension Z X) : IsKernelCokernelPair e.shortComplex :=
  E.isKernelCokernelPair _ e.conflation

/-- **A morphism of extensions is an isomorphism.** A morphism of middle terms compatible with
the inflations and the deflations is invertible, by the short five lemma. -/
theorem isIso_of_f_comp_eq_of_comp_g_eq {e e' : E.Extension Z X} (φ : e.obj ⟶ e'.obj)
    (h₁ : e.f ≫ φ = e'.f) (h₂ : φ ≫ e'.g = e.g) : IsIso φ := by
  let ψ : e.shortComplex ⟶ e'.shortComplex :=
    { τ₁ := 𝟙 X, τ₂ := φ, τ₃ := 𝟙 Z, comm₁₂ := by simp [h₁], comm₂₃ := by simp [h₂] }
  have : IsIso ψ.τ₁ := inferInstanceAs (IsIso (𝟙 X))
  have : IsIso ψ.τ₃ := inferInstanceAs (IsIso (𝟙 Z))
  exact E.isIso₂_of_conflation_of_isIso₁₃ ψ e.conflation e'.conflation

/-- **Yoneda equivalence** of extensions: some morphism of the middle terms is compatible with
the inflations and the deflations. Such a morphism is an isomorphism
(`TauCeti.ExactStructure.Extension.isIso_of_f_comp_eq_of_comp_g_eq`). -/
def Rel (e e' : E.Extension Z X) : Prop :=
  ∃ φ : e.obj ⟶ e'.obj, e.f ≫ φ = e'.f ∧ φ ≫ e'.g = e.g

/-- The defining property of Yoneda equivalence. -/
theorem rel_def (e e' : E.Extension Z X) :
    e.Rel e' ↔ ∃ φ : e.obj ⟶ e'.obj, e.f ≫ φ = e'.f ∧ φ ≫ e'.g = e.g :=
  Iff.rfl

/-- Yoneda equivalence is reflexive. -/
theorem Rel.refl (e : E.Extension Z X) : e.Rel e :=
  ⟨𝟙 _, by simp, by simp⟩

/-- Yoneda equivalence is symmetric: the compatible morphism is inverted by the five lemma. -/
theorem Rel.symm {e e' : E.Extension Z X} (h : e.Rel e') : e'.Rel e := by
  obtain ⟨φ, h₁, h₂⟩ := h
  have := isIso_of_f_comp_eq_of_comp_g_eq φ h₁ h₂
  exact ⟨inv φ, by rw [← h₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id],
    by rw [← h₂, IsIso.inv_hom_id_assoc]⟩

/-- Yoneda equivalence is transitive. -/
theorem Rel.trans {e e' e'' : E.Extension Z X} (h : e.Rel e') (h' : e'.Rel e'') : e.Rel e'' := by
  obtain ⟨φ, h₁, h₂⟩ := h
  obtain ⟨φ', h₁', h₂'⟩ := h'
  exact ⟨φ ≫ φ', by rw [reassoc_of% h₁, h₁'], by rw [Category.assoc, h₂', h₂]⟩

/-- **Yoneda equivalence is isomorphism of conflations fixing the end terms.** -/
theorem rel_iff (e e' : E.Extension Z X) :
    e.Rel e' ↔ ∃ φ : e.obj ≅ e'.obj, e.f ≫ φ.hom = e'.f ∧ φ.hom ≫ e'.g = e.g := by
  refine ⟨fun ⟨φ, h₁, h₂⟩ ↦ ?_, fun ⟨φ, h₁, h₂⟩ ↦ ⟨φ.hom, h₁, h₂⟩⟩
  have := isIso_of_f_comp_eq_of_comp_g_eq φ h₁ h₂
  exact ⟨asIso φ, h₁, h₂⟩

/-- Yoneda equivalence, as a setoid on the extensions of `Z` by `X`. -/
instance setoid (E : ExactStructure C) (Z X : C) : Setoid (E.Extension Z X) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- Equivalence for the setoid of extensions is Yoneda equivalence. -/
theorem equiv_iff_rel (e e' : E.Extension Z X) : e ≈ e' ↔ e.Rel e' :=
  Iff.rfl

/-! ### Base change -/

/-- Base change along any morphism into the third term exists, by axiom E2op. -/
instance (e : E.Extension Z X) (u : Z' ⟶ Z) : HasPullback e.g u :=
  E.hasPullbacks_deflations.hasPullback u (E.isDeflation_g e.conflation)

/-- The **base change** `u^* e` of an extension `e` of `Z` by `X` along `u : Z' ⟶ Z`: the
pullback of its deflation along `u`, with the inflation induced by that of `e` and by `0`. Its
characteristic property is the pullback square `TauCeti.ExactStructure.Extension.isPullback`. -/
noncomputable def pullback (e : E.Extension Z X) (u : Z' ⟶ Z) : E.Extension Z' X where
  obj := Limits.pullback e.g u
  f := baseChangeι e.shortComplex (IsPullback.of_hasPullback e.g u)
  g := Limits.pullback.snd e.g u
  zero := baseChangeι_snd _ _
  conflation := by
    have h := E.conflation_baseChange e.conflation (IsPullback.of_hasPullback e.g u)
    rwa [baseChange_def] at h

/-- The projection from the middle term of the base change `u^* e` to the middle term of `e`. -/
noncomputable def pullbackFst (e : E.Extension Z X) (u : Z' ⟶ Z) :
    (e.pullback u).obj ⟶ e.obj :=
  Limits.pullback.fst e.g u

/-- The middle term of the base change `u^* e` is a pullback of the deflation of `e` along `u`. -/
theorem isPullback (e : E.Extension Z X) (u : Z' ⟶ Z) :
    IsPullback (e.pullbackFst u) (e.pullback u).g e.g u :=
  IsPullback.of_hasPullback e.g u

/-- The commutative square of the base change. -/
@[reassoc]
theorem pullbackFst_g (e : E.Extension Z X) (u : Z' ⟶ Z) :
    e.pullbackFst u ≫ e.g = (e.pullback u).g ≫ u :=
  (e.isPullback u).w

/-- The inflation of the base change lifts the inflation of `e`. -/
@[reassoc (attr := simp)]
theorem pullback_f_pullbackFst (e : E.Extension Z X) (u : Z' ⟶ Z) :
    (e.pullback u).f ≫ e.pullbackFst u = e.f :=
  baseChangeι_fst e.shortComplex (e.isPullback u)

/-- **The universal property of base change.** A morphism `h` of middle terms from `e'` to `e`
which is the identity on the first terms and covers `u` on the third terms exhibits `e'` as
Yoneda equivalent to the base change `u^* e`. -/
theorem rel_pullback {e' : E.Extension Z' X} {e : E.Extension Z X} {u : Z' ⟶ Z}
    (h : e'.obj ⟶ e.obj) (h₁ : e'.f ≫ h = e.f) (h₂ : h ≫ e.g = e'.g ≫ u) :
    e'.Rel (e.pullback u) := by
  refine ⟨(e.isPullback u).lift h e'.g h₂, ?_, by simp⟩
  apply (e.isPullback u).hom_ext <;> simp [h₁]

/-- Base change respects Yoneda equivalence. -/
theorem Rel.pullback {e e' : E.Extension Z X} (h : e.Rel e') (u : Z' ⟶ Z) :
    (e.pullback u).Rel (e'.pullback u) := by
  obtain ⟨φ, h₁, h₂⟩ := h
  exact rel_pullback (e.pullbackFst u ≫ φ) (by simp [h₁])
    (by rw [Category.assoc, h₂, pullbackFst_g])

/-! ### Cobase change -/

/-- Cobase change along any morphism out of the first term exists, by axiom E2. -/
instance (e : E.Extension Z X) (v : X ⟶ X') : HasPushout e.f v :=
  E.hasPushouts_inflations.hasPushout v (E.isInflation_f e.conflation)

/-- The **cobase change** `v_* e` of an extension `e` of `Z` by `X` along `v : X ⟶ X'`: the
pushout of its inflation along `v`, with the deflation induced by that of `e` and by `0`. Its
characteristic property is the pushout square `TauCeti.ExactStructure.Extension.isPushout`. -/
noncomputable def pushout (e : E.Extension Z X) (v : X ⟶ X') : E.Extension Z X' where
  obj := Limits.pushout e.f v
  f := Limits.pushout.inr e.f v
  g := cobaseChangeπ e.shortComplex (IsPushout.of_hasPushout e.f v)
  zero := inr_cobaseChangeπ _ _
  conflation := by
    have h := E.conflation_cobaseChange e.conflation (IsPushout.of_hasPushout e.f v)
    rwa [cobaseChange_def] at h

/-- The inclusion of the middle term of `e` into the middle term of the cobase change `v_* e`. -/
noncomputable def pushoutInl (e : E.Extension Z X) (v : X ⟶ X') :
    e.obj ⟶ (e.pushout v).obj :=
  Limits.pushout.inl e.f v

/-- The middle term of the cobase change `v_* e` is a pushout of the inflation of `e` along
`v`. -/
theorem isPushout (e : E.Extension Z X) (v : X ⟶ X') :
    IsPushout e.f v (e.pushoutInl v) (e.pushout v).f :=
  IsPushout.of_hasPushout e.f v

/-- The commutative square of the cobase change. -/
@[reassoc]
theorem f_pushoutInl (e : E.Extension Z X) (v : X ⟶ X') :
    e.f ≫ e.pushoutInl v = v ≫ (e.pushout v).f :=
  (e.isPushout v).w

/-- The deflation of the cobase change extends the deflation of `e`. -/
@[reassoc (attr := simp)]
theorem pushoutInl_pushout_g (e : E.Extension Z X) (v : X ⟶ X') :
    e.pushoutInl v ≫ (e.pushout v).g = e.g :=
  inl_cobaseChangeπ e.shortComplex (e.isPushout v)

/-- **The universal property of cobase change.** A morphism `h` of middle terms from `e` to `e'`
which covers `v` on the first terms and is the identity on the third terms exhibits the cobase
change `v_* e` as Yoneda equivalent to `e'`. -/
theorem pushout_rel {e : E.Extension Z X} {e' : E.Extension Z X'} {v : X ⟶ X'}
    (h : e.obj ⟶ e'.obj) (h₁ : e.f ≫ h = v ≫ e'.f) (h₂ : h ≫ e'.g = e.g) :
    (e.pushout v).Rel e' := by
  refine ⟨(e.isPushout v).desc h e'.f h₁, by simp, ?_⟩
  apply (e.isPushout v).hom_ext <;> simp [h₂]

/-- Cobase change respects Yoneda equivalence. -/
theorem Rel.pushout {e e' : E.Extension Z X} (h : e.Rel e') (v : X ⟶ X') :
    (e.pushout v).Rel (e'.pushout v) := by
  obtain ⟨φ, h₁, h₂⟩ := h
  exact pushout_rel (φ ≫ e'.pushoutInl v) (by rw [reassoc_of% h₁, f_pushoutInl]) (by simp [h₂])

/-! ### The split extension -/

variable (E) in
/-- The **split extension** `X ⟶ X ⊞ Z ⟶ Z`. -/
noncomputable abbrev trivial (Z X : C) : E.Extension Z X where
  obj := X ⊞ Z
  f := biprod.inl
  g := biprod.snd
  zero := biprod.inl_snd
  conflation := E.conflation_biprodShortComplex X Z

/-- An extension is Yoneda equivalent to the split extension exactly when its deflation is a
split epimorphism. -/
theorem rel_trivial_iff_isSplitEpi (e : E.Extension Z X) :
    e.Rel (trivial E Z X) ↔ IsSplitEpi e.g := by
  refine ⟨fun h ↦ ?_, fun _ ↦ (?_ : (trivial E Z X).Rel e).symm⟩
  · obtain ⟨ψ, -, h₂⟩ := h.symm
    exact IsSplitEpi.mk' ⟨biprod.inr ≫ ψ, by simp [h₂]⟩
  · refine ⟨biprod.desc e.f (section_ e.g), by simp, ?_⟩
    apply biprod.hom_ext' <;> simp

/-- An extension is Yoneda equivalent to the split extension exactly when its inflation is a
split monomorphism. -/
theorem rel_trivial_iff_isSplitMono (e : E.Extension Z X) :
    e.Rel (trivial E Z X) ↔ IsSplitMono e.f := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ⟨biprod.lift (retraction e.f) e.g, ?_, by simp⟩⟩
  · obtain ⟨φ, h₁, -⟩ := h
    exact IsSplitMono.mk' ⟨φ ≫ biprod.fst, by simp [reassoc_of% h₁]⟩
  · apply biprod.hom_ext <;> simp

end Extension

/-- `Ext¹_E(Z, X)`, the **Yoneda `Ext¹`** of the exact category: the set of Yoneda equivalence
classes of conflations `X ⟶ Y ⟶ Z` of `E`. -/
def Ext1 (Z X : C) : Type (max u v) :=
  Quotient (Extension.setoid E Z X)

namespace Ext1

variable {E} {W X X' X'' Z Z' Z'' : C}

/-- The Yoneda class of an extension. -/
def mk (e : E.Extension Z X) : E.Ext1 Z X :=
  Quotient.mk _ e

/-- Two extensions have the same class exactly when they are Yoneda equivalent. -/
theorem mk_eq_mk_iff (e e' : E.Extension Z X) : mk e = mk e' ↔ e.Rel e' :=
  Quotient.eq

/-- Every class is the class of an extension. -/
theorem mk_surjective : Function.Surjective (mk : E.Extension Z X → E.Ext1 Z X) :=
  Quotient.mk_surjective

/-- Induction on classes: a property of all classes of extensions holds for every class. -/
@[elab_as_elim]
theorem induction {motive : E.Ext1 Z X → Prop} (h : ∀ e, motive (mk e)) (ξ : E.Ext1 Z X) :
    motive ξ :=
  Quotient.ind h ξ

/-- A function on extensions that is constant on Yoneda equivalence classes descends to
`Ext¹_E(Z, X)`. -/
def lift {α : Sort*} (φ : E.Extension Z X → α) (hφ : ∀ e e', e.Rel e' → φ e = φ e') :
    E.Ext1 Z X → α :=
  Quotient.lift φ hφ

@[simp]
theorem lift_mk {α : Sort*} (φ : E.Extension Z X → α) (hφ : ∀ e e', e.Rel e' → φ e = φ e')
    (e : E.Extension Z X) : lift φ hφ (mk e) = φ e := (rfl)

/-- `TauCeti.ExactStructure.Ext1.lift φ hφ` is the unique function on classes that agrees with `φ`
on the class of every extension. -/
theorem lift_unique {α : Sort*} (φ : E.Extension Z X → α) (hφ : ∀ e e', e.Rel e' → φ e = φ e')
    (ψ : E.Ext1 Z X → α) (hψ : ∀ e, ψ (mk e) = φ e) : ψ = lift φ hφ :=
  funext fun ξ ↦ Quotient.inductionOn ξ hψ

/-- The **contravariant action** of `u : Z' ⟶ Z` on `Ext¹_E(-, X)`, by base change. -/
noncomputable def pullback (ξ : E.Ext1 Z X) (u : Z' ⟶ Z) : E.Ext1 Z' X :=
  Quotient.map (fun e ↦ e.pullback u) (fun _ _ h ↦ Extension.Rel.pullback h u) ξ

/-- The **covariant action** of `v : X ⟶ X'` on `Ext¹_E(Z, -)`, by cobase change. -/
noncomputable def pushout (ξ : E.Ext1 Z X) (v : X ⟶ X') : E.Ext1 Z X' :=
  Quotient.map (fun e ↦ e.pushout v) (fun _ _ h ↦ Extension.Rel.pushout h v) ξ

@[simp]
theorem pullback_mk (e : E.Extension Z X) (u : Z' ⟶ Z) :
    (mk e).pullback u = mk (e.pullback u) := (rfl)

@[simp]
theorem pushout_mk (e : E.Extension Z X) (v : X ⟶ X') :
    (mk e).pushout v = mk (e.pushout v) := (rfl)

/-- Base change along an identity is the identity. -/
@[simp]
theorem pullback_id (ξ : E.Ext1 Z X) : ξ.pullback (𝟙 Z) = ξ := by
  induction ξ using induction with
  | h e =>
    rw [pullback_mk, mk_eq_mk_iff]
    exact (Extension.rel_pullback (𝟙 _) (by simp) (by simp)).symm

/-- Base change is contravariantly functorial. -/
@[simp]
theorem pullback_pullback (ξ : E.Ext1 Z X) (u : Z' ⟶ Z) (u' : Z'' ⟶ Z') :
    (ξ.pullback u).pullback u' = ξ.pullback (u' ≫ u) := by
  induction ξ using induction with
  | h e =>
    simp only [pullback_mk, mk_eq_mk_iff]
    exact Extension.rel_pullback ((e.pullback u).pullbackFst u' ≫ e.pullbackFst u) (by simp)
      (by simp only [Category.assoc, Extension.pullbackFst_g, Extension.pullbackFst_g_assoc])

/-- Cobase change along an identity is the identity. -/
@[simp]
theorem pushout_id (ξ : E.Ext1 Z X) : ξ.pushout (𝟙 X) = ξ := by
  induction ξ using induction with
  | h e =>
    rw [pushout_mk, mk_eq_mk_iff]
    exact Extension.pushout_rel (𝟙 _) (by simp) (by simp)

/-- Cobase change is covariantly functorial. -/
@[simp]
theorem pushout_pushout (ξ : E.Ext1 Z X) (v : X ⟶ X') (v' : X' ⟶ X'') :
    (ξ.pushout v).pushout v' = ξ.pushout (v ≫ v') := by
  induction ξ using induction with
  | h e =>
    simp only [pushout_mk, mk_eq_mk_iff]
    exact (Extension.pushout_rel (e.pushoutInl v ≫ (e.pushout v).pushoutInl v')
      (by simp only [Extension.f_pushoutInl_assoc, Extension.f_pushoutInl, Category.assoc])
      (by simp)).symm

/-- **Base change and cobase change commute**: `u^* (v_* ξ) = v_* (u^* ξ)`. -/
theorem pushout_pullback (ξ : E.Ext1 Z X) (v : X ⟶ X') (u : Z' ⟶ Z) :
    (ξ.pushout v).pullback u = (ξ.pullback u).pushout v := by
  induction ξ using induction with
  | h e =>
    simp only [pullback_mk, pushout_mk, mk_eq_mk_iff]
    refine (Extension.pushout_rel (((e.pushout v).isPullback u).lift
      (e.pullbackFst u ≫ e.pushoutInl v) (e.pullback u).g
        (by simp [Extension.pullbackFst_g])) ?_ (by simp)).symm
    apply ((e.pushout v).isPullback u).hom_ext
    · simp [Extension.f_pushoutInl]
    · simp

/-! ### The base point -/

/-- The base point of `Ext¹_E(Z, X)`: the class of the split extension `X ⟶ X ⊞ Z ⟶ Z`. -/
noncomputable instance : Zero (E.Ext1 Z X) :=
  ⟨mk (Extension.trivial E Z X)⟩

theorem zero_def : (0 : E.Ext1 Z X) = mk (Extension.trivial E Z X) := (rfl)

/-- **A class vanishes exactly when the deflation splits.** -/
theorem mk_eq_zero_iff_isSplitEpi (e : E.Extension Z X) : mk e = 0 ↔ IsSplitEpi e.g := by
  rw [zero_def, mk_eq_mk_iff, Extension.rel_trivial_iff_isSplitEpi]

/-- **A class vanishes exactly when the inflation splits.** -/
theorem mk_eq_zero_iff_isSplitMono (e : E.Extension Z X) : mk e = 0 ↔ IsSplitMono e.f := by
  rw [zero_def, mk_eq_mk_iff, Extension.rel_trivial_iff_isSplitMono]

/-- **Exactness at `Hom(W, Z)`.** For a conflation `e : X ⟶ Y ⟶ Z`, the base change of `[e]`
along `u : W ⟶ Z` vanishes exactly when `u` factors through the deflation. -/
theorem mk_pullback_eq_zero_iff (e : E.Extension Z X) (u : W ⟶ Z) :
    (mk e).pullback u = 0 ↔ ∃ t : W ⟶ e.obj, t ≫ e.g = u := by
  rw [pullback_mk, mk_eq_zero_iff_isSplitEpi]
  refine ⟨fun _ ↦ ⟨section_ (e.pullback u).g ≫ e.pullbackFst u, ?_⟩,
    fun ⟨t, ht⟩ ↦ IsSplitEpi.mk' ⟨(e.isPullback u).lift t (𝟙 W) (by simp [ht]), by simp⟩⟩
  rw [Category.assoc, Extension.pullbackFst_g, IsSplitEpi.id_assoc]

/-- **Exactness at `Hom(X, W)`.** For a conflation `e : X ⟶ Y ⟶ Z`, the cobase change of `[e]`
along `v : X ⟶ W` vanishes exactly when `v` extends along the inflation. -/
theorem mk_pushout_eq_zero_iff (e : E.Extension Z X) (v : X ⟶ W) :
    (mk e).pushout v = 0 ↔ ∃ t : e.obj ⟶ W, e.f ≫ t = v := by
  rw [pushout_mk, mk_eq_zero_iff_isSplitMono]
  refine ⟨fun _ ↦ ⟨e.pushoutInl v ≫ retraction (e.pushout v).f, ?_⟩,
    fun ⟨t, ht⟩ ↦ IsSplitMono.mk' ⟨(e.isPushout v).desc t (𝟙 W) (by simp [ht]), by simp⟩⟩
  rw [Extension.f_pushoutInl_assoc, IsSplitMono.id, Category.comp_id]

/-- Base change of the base point is the base point. -/
@[simp]
theorem zero_pullback (u : Z' ⟶ Z) : (0 : E.Ext1 Z X).pullback u = 0 :=
  (mk_pullback_eq_zero_iff _ u).mpr ⟨u ≫ biprod.inr, by simp⟩

/-- Cobase change of the base point is the base point. -/
@[simp]
theorem zero_pushout (v : X ⟶ X') : (0 : E.Ext1 Z X).pushout v = 0 :=
  (mk_pushout_eq_zero_iff _ v).mpr ⟨biprod.fst ≫ v, by simp⟩

/-- Base change along the zero morphism is the base point. -/
@[simp]
theorem pullback_zero (ξ : E.Ext1 Z X) : ξ.pullback (0 : Z' ⟶ Z) = 0 := by
  induction ξ using induction with
  | h e => exact (mk_pullback_eq_zero_iff e 0).mpr ⟨0, by simp⟩

/-- Cobase change along the zero morphism is the base point. -/
@[simp]
theorem pushout_zero (ξ : E.Ext1 Z X) : ξ.pushout (0 : X ⟶ X') = 0 := by
  induction ξ using induction with
  | h e => exact (mk_pushout_eq_zero_iff e 0).mpr ⟨0, by simp⟩

/-- **Exactness at `Ext¹_E(W, X)`.** For a conflation `e : X ⟶ Y ⟶ Z`, a class
`ξ ∈ Ext¹_E(W, X)` is a base change `u^* [e]` of `[e]` exactly when its cobase change along the
inflation of `e` vanishes. -/
theorem pushout_f_eq_zero_iff (e : E.Extension Z X) (ξ : E.Ext1 W X) :
    ξ.pushout e.f = 0 ↔ ∃ u : W ⟶ Z, (mk e).pullback u = ξ := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu⟩ ↦ hu ▸ ?_⟩
  · induction ξ using induction with
    | h e₀ =>
      obtain ⟨t, ht⟩ := (mk_pushout_eq_zero_iff e₀ e.f).mp h
      have hk : e₀.f ≫ t ≫ e.g = 0 := by rw [reassoc_of% ht, Extension.zero]
      refine ⟨e₀.isKernelCokernelPair.desc (t ≫ e.g) hk, ?_⟩
      exact ((mk_eq_mk_iff _ _).mpr (Extension.rel_pullback t ht
        (e₀.isKernelCokernelPair.g_desc _ hk).symm)).symm
  · exact (mk_pushout_eq_zero_iff _ _).mpr ⟨e.pullbackFst u, by simp⟩

/-- **Exactness at `Ext¹_E(Z, W)`.** For a conflation `e : X ⟶ Y ⟶ Z`, a class
`ξ ∈ Ext¹_E(Z, W)` is a cobase change `v_* [e]` of `[e]` exactly when its base change along the
deflation of `e` vanishes. -/
theorem pullback_g_eq_zero_iff (e : E.Extension Z X) (ξ : E.Ext1 Z W) :
    ξ.pullback e.g = 0 ↔ ∃ v : X ⟶ W, (mk e).pushout v = ξ := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ ↦ hv ▸ ?_⟩
  · induction ξ using induction with
    | h e₀ =>
      obtain ⟨t, ht⟩ := (mk_pullback_eq_zero_iff e₀ e.g).mp h
      have hk : (e.f ≫ t) ≫ e₀.g = 0 := by rw [Category.assoc, ht, Extension.zero]
      refine ⟨e₀.isKernelCokernelPair.lift (e.f ≫ t) hk, ?_⟩
      exact (mk_eq_mk_iff _ _).mpr (Extension.pushout_rel t
        (e₀.isKernelCokernelPair.lift_f _ hk).symm ht)
  · exact (mk_pullback_eq_zero_iff _ _).mpr ⟨e.pushoutInl v, by simp⟩

end Ext1

/-- **`Ext¹` vanishes for the split exact structure**: every conflation is split, so every
`Ext¹` is the singleton of its base point. -/
instance (Z X : C) : Subsingleton ((ExactStructure.split C).Ext1 Z X) where
  allEq ξ ξ' := by
    suffices h : ∀ ξ : (ExactStructure.split C).Ext1 Z X, ξ = 0 by rw [h ξ, h ξ']
    intro ξ
    induction ξ using Ext1.induction with
    | h e =>
      obtain ⟨s⟩ := (split_conflation _).mp e.conflation
      exact (Ext1.mk_eq_zero_iff_isSplitEpi e).mpr s.isSplitEpi_g

end ExactStructure

end TauCeti
