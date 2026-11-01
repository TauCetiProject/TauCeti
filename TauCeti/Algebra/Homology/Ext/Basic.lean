/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Transport and exactness lemmas for `Ext` groups

This file collects general `Ext` API that Mathlib does not state in this form:

* the transport of `Extⁿ(X, Y)` along isomorphisms `X ≅ X'` and `Y ≅ Y'`, additively as
  `TauCeti.extAddEquivOfIso` and `R`-linearly as `TauCeti.extLinearEquivOfIso`;
* in degree zero, composition with `CategoryTheory.Abelian.Ext.mk₀ f` corresponds under
  `CategoryTheory.Abelian.Ext.addEquiv₀` to composition with `f`
  (`TauCeti.ext_addEquiv₀_mk₀_comp` and `TauCeti.ext_addEquiv₀_comp_mk₀`);
* the vanishing of `Extⁿ(X, Y)` when either of the two objects is a zero object;
* short exact cokernel sequences, the cokernel sequence of the chosen embedding into an injective
  object with the morphisms of such sequences extending a given morphism
  (`TauCeti.injectiveCokernelSequenceMap`), and a dimension-shift criterion for vanishing of the
  next `Ext` group;
* Mathlib's long exact `Ext` sequences of a short exact sequence `S`, repackaged as
  `Function.Exact` statements about the composition maps: `TauCeti.exact_postcomp` and
  `TauCeti.exact_precomp` for `CategoryTheory.Abelian.Ext.postcomp` and
  `CategoryTheory.Abelian.Ext.precomp`, and `TauCeti.exact_postcompOfLinear` and
  `TauCeti.exact_precompOfLinear` for their `R`-linear forms; `TauCeti.exact_precomp₁` and
  `TauCeti.exact_precompOfLinear₁` (respectively `TauCeti.exact_precomp₃` and
  `TauCeti.exact_precompOfLinear₃`) are the same repackaging one step further along the
  contravariant sequence, where the outgoing (respectively incoming) map is precomposition with
  the extension class;
* extension of morphisms along a short exact sequence `S` whose cokernel `S.X₃` has
  `Ext¹(S.X₃, Y) = 0` (`CategoryTheory.ShortComplex.ShortExact.exists_f_comp_eq_of_ext_eq_zero`),
  and, when `S.X₂` is projective, the converse
  (`CategoryTheory.ShortComplex.ShortExact.forall_ext_one_eq_zero_iff`) and dimension shifting
  `Ext^{n+2}(S.X₃, Y) = 0 ↔ Ext^{n+1}(S.X₁, Y) = 0`
  (`CategoryTheory.ShortComplex.ShortExact.forall_ext_add_two_eq_zero_iff`);
* the vanishing of morphisms from `X` placed in degree `n` to `Y` placed in degree zero in the
  derived category when `Extⁿ(X, Y) = 0` (`DerivedCategory.singleFunctor_hom_eq_zero_of_ext`).

The exactness statements are `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` and
`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` with the vanishing of the composite
supplied, which is what makes them usable with the `Function.Exact` API.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7, for `Ext` and its long
  exact sequences.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-! ### Transport along isomorphisms -/

variable {X X' Y Y' : C}

/-- Isomorphisms `e : X ≅ X'` and `f : Y ≅ Y'` induce an isomorphism
`Extⁿ(X, Y) ≃ Extⁿ(X', Y')`, by composing with `e.inv` on the left and with `f.hom` on the right.
This is the action of an isomorphism through `CategoryTheory.Abelian.extFunctor`, spelled out so
that `TauCeti.extLinearEquivOfIso` can refine it to an `R`-linear equivalence. -/
noncomputable def extAddEquivOfIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w} X' Y' n where
  toFun x := (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun y := (Ext.mk₀ e.hom).comp (y.comp (Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

/-- `TauCeti.extAddEquivOfIso` composes with `e.inv` and `f.hom`. -/
@[simp]
theorem extAddEquivOfIso_apply (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extAddEquivOfIso e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-- The `R`-linear refinement of `TauCeti.extAddEquivOfIso`: in an `R`-linear abelian category,
isomorphisms `X ≅ X'` and `Y ≅ Y'` identify `Extⁿ(X, Y)` and `Extⁿ(X', Y')` as `R`-modules. -/
noncomputable def extLinearEquivOfIso (R : Type t) [Ring R] [Linear R C] (e : X ≅ X')
    (f : Y ≅ Y') (n : ℕ) : Ext.{w} X Y n ≃ₗ[R] Ext.{w} X' Y' n where
  __ := extAddEquivOfIso e f n
  map_smul' r x := by simp [extAddEquivOfIso_apply]

/-- `TauCeti.extLinearEquivOfIso` composes with `e.inv` and `f.hom`. -/
@[simp]
theorem extLinearEquivOfIso_apply (R : Type t) [Ring R] [Linear R C] (e : X ≅ X')
    (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extLinearEquivOfIso R e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-! ### Composition in degree zero -/

/-- In degree zero, precomposing with `Ext.mk₀ f` is precomposing with `f` in the category. -/
theorem ext_addEquiv₀_mk₀_comp {Z : C} (f : X ⟶ Y) (x : Ext.{w} Y Z 0) :
    Ext.addEquiv₀ ((Ext.mk₀ f).comp x (zero_add 0)) = f ≫ Ext.addEquiv₀ x := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

/-- In degree zero, postcomposing with `Ext.mk₀ f` is postcomposing with `f` in the category. -/
theorem ext_addEquiv₀_comp_mk₀ {Z : C} (x : Ext.{w} X Y 0) (f : Y ⟶ Z) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

/-! ### Vanishing against a zero object -/

/-- There is no `Ext` out of a zero object, in any degree. -/
theorem subsingleton_ext_of_isZero_left (hX : IsZero X) (Y : C) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Ext.mk₀_id_comp x, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]

/-- There is no `Ext` into a zero object, in any degree. -/
theorem subsingleton_ext_of_isZero_right (X : C) (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Ext.comp_mk₀_id x, hY.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.comp_zero]

/-! ### Dimension shifting along an injective embedding -/

section DimensionShift

/-- The middle object in a cokernel sequence is injective when the target of its first map is. -/
instance injective_cokernelSequence_X₂ {X Y : C} (f : X ⟶ Y) [Injective Y] :
    Injective (ShortComplex.cokernelSequence f).X₂ :=
  (inferInstance : Injective Y)

/-- A dimension-shift criterion along a short exact sequence with injective middle term: if
composition with its extension class vanishes, then the next `Ext` group is subsingleton. -/
lemma subsingleton_ext_succ_of_comp_extClass_eq_zero {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] (X : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X S.X₃ n, x₃.comp hS.extClass rfl = 0) :
    Subsingleton (Ext X S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS y
    (Ext.eq_zero_of_injective _) rfl
  exact hzero x₃

variable [EnoughInjectives C]

/-- The cokernel sequence `Y ⟶ Injective.under Y ⟶ cokernel (Injective.ι Y)` of the chosen
embedding of an object into an injective object. It is written with `ShortComplex.mk`, so that
its three objects are reducibly `Y`, `Injective.under Y` and `cokernel (Injective.ι Y)`. -/
noncomputable abbrev injectiveCokernelSequence (Y : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y)) (cokernel.condition _)

omit [HasExt C] in
/-- The cokernel sequence of the chosen embedding into an injective object is short exact. -/
lemma injectiveCokernelSequence_shortExact (Y : C) :
    (injectiveCokernelSequence Y).ShortExact :=
  cokernelSequence_shortExact _

omit [HasExt C] in
/-- A morphism `f : Y ⟶ Y'` extends to a morphism between the cokernel sequences of the chosen
embeddings of `Y` and `Y'` into injective objects. Its middle component is a factorization of
`f` followed by the embedding of `Y'` through the embedding of `Y`, which exists because the
target is injective; its last component is the induced map of cokernels. The extension is a
choice, not unique. -/
noncomputable def injectiveCokernelSequenceMap {Y Y' : C} (f : Y ⟶ Y') :
    injectiveCokernelSequence Y ⟶ injectiveCokernelSequence Y' where
  τ₁ := f
  τ₂ := Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y)
  τ₃ := cokernel.map (Injective.ι Y) (Injective.ι Y') f
    (Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y))
    (Injective.comp_factorThru _ _)
  comm₁₂ := (Injective.comp_factorThru _ _).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

omit [HasExt C] in
@[simp]
lemma injectiveCokernelSequenceMap_τ₁ {Y Y' : C} (f : Y ⟶ Y') :
    (injectiveCokernelSequenceMap f).τ₁ = f :=
  (rfl)

omit [HasExt C] in
@[simp]
lemma injectiveCokernelSequenceMap_τ₂ {Y Y' : C} (f : Y ⟶ Y') :
    (injectiveCokernelSequenceMap f).τ₂ =
      Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y) :=
  (rfl)

omit [HasExt C] in
@[simp]
lemma injectiveCokernelSequenceMap_τ₃ {Y Y' : C} (f : Y ⟶ Y') :
    (injectiveCokernelSequenceMap f).τ₃ =
      cokernel.map (Injective.ι Y) (Injective.ι Y') f
        (Injective.factorThru (f ≫ Injective.ι Y') (Injective.ι Y))
        (Injective.comp_factorThru _ _) :=
  (rfl)

/-- The dimension-shift criterion specialised to the chosen embedding into an injective object. -/
lemma subsingleton_ext_succ_of_injectiveCokernelSequence (X Y : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X (injectiveCokernelSequence Y).X₃ n,
      x₃.comp (injectiveCokernelSequence_shortExact Y).extClass rfl = 0) :
    Subsingleton (Ext X Y (n + 1)) :=
  subsingleton_ext_succ_of_comp_extClass_eq_zero
    (injectiveCokernelSequence_shortExact Y) X n hzero

end DimensionShift

/-! ### The long exact sequences as `Function.Exact` statements -/

variable {S : ShortComplex C}

/-- Exactness of `Extⁿ(X, S.X₁) → Extⁿ(X, S.X₂) → Extⁿ(X, S.X₃)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` packaged as a
`Function.Exact` statement about the postcomposition maps. -/
theorem exact_postcomp (hS : S.ShortExact) (X : C) (n : ℕ) :
    Function.Exact (Ext.postcomp (Ext.mk₀ S.f) X (add_zero n))
      (Ext.postcomp (Ext.mk₀ S.g) X (add_zero n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.covariant_sequence_exact₂ X hS x₂ hx, by
    rintro ⟨x₁, rfl⟩
    simp [S.zero]⟩

/-- Exactness of `Extⁿ(S.X₃, Y) → Extⁿ(S.X₂, Y) → Extⁿ(S.X₁, Y)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` packaged as
a `Function.Exact` statement about the precomposition maps. -/
theorem exact_precomp (hS : S.ShortExact) (Y : C) (n : ℕ) :
    Function.Exact (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n))
      (Ext.precomp (Ext.mk₀ S.f) Y (zero_add n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.contravariant_sequence_exact₂ hS Y x₂ hx, by
    rintro ⟨x₃, rfl⟩
    simp [S.zero]⟩

/-- The linear postcomposition map has `CategoryTheory.Abelian.Ext.postcomp` as its underlying
function. -/
@[simp]
theorem coe_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] {Y Z : C} {n a b : ℕ}
    (beta : Ext.{w} Y Z n) (X : C) (h : a + n = b) :
    ⇑(Ext.postcompOfLinear beta R X h) = Ext.postcomp beta X h :=
  rfl

/-- The linear precomposition map has `CategoryTheory.Abelian.Ext.precomp` as its underlying
function. -/
@[simp]
theorem coe_precompOfLinear (R : Type t) [CommRing R] [Linear R C] {X Y : C} {n a b : ℕ}
    (alpha : Ext.{w} X Y n) (Z : C) (h : n + a = b) :
    ⇑(Ext.precompOfLinear alpha R Z h) = Ext.precomp alpha Z h :=
  rfl

/-- The `R`-linear form of `TauCeti.exact_postcomp`. -/
theorem exact_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (X : C)
    (n : ℕ) :
    Function.Exact (Ext.postcompOfLinear (Ext.mk₀ S.f) R X (add_zero n))
      (Ext.postcompOfLinear (Ext.mk₀ S.g) R X (add_zero n)) := by
  simp only [coe_postcompOfLinear]
  exact exact_postcomp hS X n

/-- The `R`-linear form of `TauCeti.exact_precomp`. -/
theorem exact_precompOfLinear (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n : ℕ) :
    Function.Exact (Ext.precompOfLinear (Ext.mk₀ S.g) R Y (zero_add n))
      (Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add n)) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp hS Y n

/-- Exactness of `Extⁿ⁰(S.X₁, Y) → Extⁿ¹(S.X₃, Y) → Extⁿ¹(S.X₂, Y)` at the middle term, for a
short exact sequence `S` and `n₁ = 1 + n₀`. The first map is precomposition with the extension
class of `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃'` with its
`AddCommGrpCat` wrapper removed. -/
theorem exact_precomp₃ (hS : S.ShortExact) (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precomp hS.extClass Y h)
      (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n₁)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.contravariant_sequence_exact₃' hS Y n₀ n₁ h)

/-- The `R`-linear form of `TauCeti.exact_precomp₃`. -/
theorem exact_precompOfLinear₃ (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precompOfLinear hS.extClass R Y h)
      (Ext.precompOfLinear (Ext.mk₀ S.g) R Y (zero_add n₁)) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp₃ hS Y n₀ n₁ h

/-- Exactness of `Extⁿ⁰(S.X₂, Y) → Extⁿ⁰(S.X₁, Y) → Extⁿ¹(S.X₃, Y)` at the middle term, for a
short exact sequence `S` and `n₁ = 1 + n₀`. The second map is precomposition with the extension
class of `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'` with its
`AddCommGrpCat` wrapper removed. -/
theorem exact_precomp₁ (hS : S.ShortExact) (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precomp (Ext.mk₀ S.f) Y (zero_add n₀))
      (Ext.precomp hS.extClass Y h) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.contravariant_sequence_exact₁' hS Y n₀ n₁ h)

/-- The `R`-linear form of `TauCeti.exact_precomp₁`. -/
theorem exact_precompOfLinear₁ (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add n₀))
      (Ext.precompOfLinear hS.extClass R Y h) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp₁ hS Y n₀ n₁ h

end TauCeti

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}
  (hS : S.ShortExact)
include hS

/-- **Extension along a monomorphism with orthogonal cokernel**: if `S` is short exact and
`Ext¹(S.X₃, Y) = 0`, every morphism `S.X₁ ⟶ Y` extends along `S.f`. -/
lemma exists_f_comp_eq_of_ext_eq_zero {Y : C} (h : ∀ x : Ext.{w} S.X₃ Y 1, x = 0)
    (ψ : S.X₁ ⟶ Y) : ∃ g : S.X₂ ⟶ Y, S.f ≫ g = ψ := by
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ ψ) (n₁ := 1) rfl (h _)
  refine ⟨Ext.addEquiv₀ x, Ext.homEquiv₀.symm.injective ?_⟩
  rw [← Ext.mk₀_addEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
  exact hx

/-- **The connecting map in degree zero**: for `S` short exact, the class `extClass ∘ g` in
`Ext¹(S.X₃, Y)` of a morphism `g : S.X₁ ⟶ Y` vanishes if and only if `g` extends along `S.f`. -/
lemma extClass_comp_mk₀_eq_zero_iff {Y : C} (g : S.X₁ ⟶ Y) :
    hS.extClass.comp (Ext.mk₀ g) (add_zero 1) = 0 ↔ ∃ h : S.X₂ ⟶ Y, S.f ≫ h = g := by
  refine ⟨fun hg ↦ ?_, fun ⟨h, hh⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ g) (n₁ := 1) rfl hg
    refine ⟨Ext.addEquiv₀ x, Ext.homEquiv₀.symm.injective ?_⟩
    rw [← Ext.mk₀_addEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
    exact hx
  · rw [← hh, ← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc _

/-- **Surjectivity of the connecting map against a projective middle term**: if `S` is short
exact with `S.X₂` projective, every class in `Ext¹(S.X₃, Y)` is `extClass ∘ g` for a morphism
`g : S.X₁ ⟶ Y`. -/
lemma exists_extClass_comp_mk₀_eq [Projective S.X₂] {Y : C} (e : Ext.{w} S.X₃ Y 1) :
    ∃ g : S.X₁ ⟶ Y, hS.extClass.comp (Ext.mk₀ g) (add_zero 1) = e := by
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
    (n₀ := 0) rfl
  exact ⟨Ext.addEquiv₀ x, by rw [Ext.mk₀_addEquiv₀_apply]⟩

/-- **Dimension shifting against a projective middle term**: if `S` is short exact with `S.X₂`
projective, composition with the extension class is a bijection
`Ext^{n+1}(S.X₁, Y) ⟶ Ext^{n+2}(S.X₃, Y)`. -/
lemma bijective_precomp_extClass [Projective S.X₂] {Y : C} (n : ℕ) :
    Function.Bijective (Ext.precomp hS.extClass Y (show 1 + (n + 1) = n + 2 by lia)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun e ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₁ hS Y x (n₁ := n + 2) (by lia) hx
    rw [Ext.eq_zero_of_projective y, Ext.comp_zero]
  · obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
      (n₀ := n + 1) (by lia)
    exact ⟨x, rfl⟩

/-- **`Ext¹` against a projective middle term**: if `S` is short exact with `S.X₂` projective, then
`Ext¹(S.X₃, Y) = 0` if and only if every morphism `S.X₁ ⟶ Y` extends along `S.f`. -/
lemma forall_ext_one_eq_zero_iff [Projective S.X₂] {Y : C} :
    (∀ x : Ext.{w} S.X₃ Y 1, x = 0) ↔ ∀ ψ : S.X₁ ⟶ Y, ∃ g : S.X₂ ⟶ Y, S.f ≫ g = ψ := by
  refine ⟨hS.exists_f_comp_eq_of_ext_eq_zero, fun h e ↦ ?_⟩
  -- Every class in `Ext¹(S.X₃, Y)` is the extension class composed with a morphism `S.X₁ ⟶ Y`.
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
    (n₀ := 0) rfl
  obtain ⟨g, hg⟩ := h (Ext.addEquiv₀ x)
  rw [← Ext.mk₀_addEquiv₀_apply x, ← hg, ← Ext.mk₀_comp_mk₀]
  exact hS.extClass_comp_assoc _

/-- **Dimension shifting against a projective middle term**: if `S` is short exact with `S.X₂`
projective, then `Ext^{n+2}(S.X₃, Y) = 0` if and only if `Ext^{n+1}(S.X₁, Y) = 0`. -/
lemma forall_ext_add_two_eq_zero_iff [Projective S.X₂] {Y : C} (n : ℕ) :
    (∀ x : Ext.{w} S.X₃ Y (n + 2), x = 0) ↔ ∀ x : Ext.{w} S.X₁ Y (n + 1), x = 0 := by
  refine ⟨fun h x ↦ ?_, fun h e ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₁ hS Y x (n₁ := n + 2) (by lia) (h _)
    rw [Ext.eq_zero_of_projective y, Ext.comp_zero]
  · obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
      (n₀ := n + 1) (by lia)
    rw [h x, Ext.comp_zero]

end CategoryTheory.ShortComplex.ShortExact

namespace DerivedCategory

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{t} C]

/-- If `Extⁿ(X, Y) = 0`, there are no nonzero morphisms from `X` placed in degree `n` to `Y` placed
in degree zero. -/
lemma singleFunctor_hom_eq_zero_of_ext {X Y : C} {n : ℕ} (h : ∀ e : Ext.{w} X Y n, e = 0)
    (f : (singleFunctor C n).obj X ⟶ (singleFunctor C 0).obj Y) : f = 0 := by
  -- Shifting by `n` turns `f` into a morphism `X ⟶ Y⟦n⟧`, which is the image of an `Ext` class.
  apply (shiftFunctor (DerivedCategory C) (n : ℤ)).map_injective
  obtain ⟨e, he⟩ := Ext.homEquiv.surjective
    (((singleFunctors C).shiftIso (n : ℤ) 0 n (add_zero _)).inv.app X ≫
      (shiftFunctor (DerivedCategory C) (n : ℤ)).map f)
  rw [h e, ← Ext.hom, Ext.zero_hom] at he
  rw [Functor.map_zero, ← cancel_epi (((singleFunctors C).shiftIso (n : ℤ) 0 n
    (add_zero _)).inv.app X), ← he, comp_zero]

end DerivedCategory
