/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import TauCeti.AlgebraicGeometry.Morphisms.NoetherianAlteration
public import TauCeti.NumberTheory.PNumber

import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# `P`-alterations and separable alterations

Let `f : X ⟶ Y` be a noetherian alteration (`AlgebraicGeometry.Scheme.Hom.IsNoetherianAlteration`)
and `x` a component-generic point of `X`. The *generic degree* of `f` at `x` is the residue degree
`[κ(x) : κ(f x)]` (`AlgebraicGeometry.Scheme.Hom.residueDegree`). It is positive, because `f` is
finite over the generic points of `Y`. For a set `P` of prime numbers, `f` is a *`P`-alteration*
when every generic degree is a `P`-number (`TauCeti.IsPNumber`): all its prime factors lie in `P`.
It is a *separable alteration* when every residue field extension `κ(f x) ⟶ κ(x)` at a
component-generic point `x` of `X` is separable. These alterations with controlled degrees are
the ones in Temkin's and Gabber's desingularization theorems: a generic degree prime to `ℓ` is
invertible on `ℓ`-primary coefficients.

The degrees multiply in towers (`AlgebraicGeometry.Scheme.Hom.residueDegree_comp`), so
`P`-alterations compose; separable extensions form towers, so separable alterations compose.
A `{ℓ}ᶜ`-alteration (an *`ℓ′`-alteration*) is one whose generic degrees are prime to `ℓ`, an
`∅`-alteration is one of generic degree one everywhere, and when `P` contains every prime the
`P`-alterations are all the noetherian alterations. An `∅`-alteration is separable, and a
modification of an irreducible scheme is an `∅`-alteration.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsPAlteration P f`: `f` is a noetherian alteration whose generic
  degrees are `P`-numbers.
* `AlgebraicGeometry.Scheme.Hom.IsSeparableAlteration f`: `f` is a noetherian alteration whose
  residue field extensions at the component-generic points of its source are separable.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPAlteration_iff_forall_prime_dvd`: positivity of the generic
  degrees is automatic, so `f` is a `P`-alteration exactly when every prime factor of every
  generic degree lies in `P`.
* `AlgebraicGeometry.Scheme.Hom.IsPAlteration.comp`, `IsSeparableAlteration.comp`: both notions
  are stable under composition.
* `AlgebraicGeometry.Scheme.Hom.IsPAlteration.mono`: enlarging `P` preserves `P`-alterations.
* `AlgebraicGeometry.Scheme.Hom.isPAlteration_iff_of_setOf_prime_subset`: when `P` contains every
  prime, the `P`-alterations are the noetherian alterations.
* `AlgebraicGeometry.Scheme.Hom.isPAlteration_compl_singleton_iff`: the `ℓ′`-alterations are the
  noetherian alterations whose generic degrees are not divisible by `ℓ`.
* `AlgebraicGeometry.Scheme.Hom.isPAlteration_empty_iff`: the `∅`-alterations are the noetherian
  alterations of generic degree one.
* `AlgebraicGeometry.Scheme.Hom.isSeparableAlteration_of_isPAlteration_empty`: an `∅`-alteration is
  separable.
* `AlgebraicGeometry.Scheme.Hom.isPAlteration_empty_of_isModification`: a modification of an
  irreducible scheme is an `∅`-alteration.

## References

* M. Temkin, *Tame distillation and desingularization by p-alterations*, Ann. of Math. 186
  (2017), §1.2.1 and §4.1.2.
* L. Illusie, Y. Laszlo, F. Orgogozo (eds.), *Travaux de Gabber sur l'uniformisation locale et la
  cohomologie étale des schémas quasi-excellents*, Astérisque 363–364 (2014), Exposé X, §2 and
  §3.3.1.
-/

public section

open CategoryTheory Set TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}} {P Q : Set ℕ}

/-! ### `P`-alterations -/

/-- A morphism `f : X ⟶ Y` is a *`P`-alteration*, for a set `P` of prime numbers, if it is a
noetherian alteration whose generic degrees `[κ(x) : κ(f x)]`, at the component-generic points `x`
of `X`, are `P`-numbers: every prime factor of each of them lies in `P` (Temkin, §1.2.1). -/
structure IsPAlteration (P : Set ℕ) (f : X ⟶ Y) : Prop extends f.IsNoetherianAlteration where
  isPNumber_residueDegree : ∀ x ∈ genericPoints X, IsPNumber P (f.residueDegree x)

/-- A `P`-alteration is a noetherian alteration whose generic degrees are `P`-numbers. -/
theorem isPAlteration_iff (f : X ⟶ Y) :
    f.IsPAlteration P ↔
      f.IsNoetherianAlteration ∧ ∀ x ∈ genericPoints X, IsPNumber P (f.residueDegree x) :=
  ⟨fun h ↦ ⟨h.toIsNoetherianAlteration, h.isPNumber_residueDegree⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- A noetherian alteration is a `P`-alteration exactly when every prime factor of each of its
generic degrees lies in `P`: the generic degrees of a noetherian alteration are positive. -/
theorem isPAlteration_iff_forall_prime_dvd (f : X ⟶ Y) :
    f.IsPAlteration P ↔ f.IsNoetherianAlteration ∧
      ∀ x ∈ genericPoints X, ∀ q : ℕ, q.Prime → q ∣ f.residueDegree x → q ∈ P := by
  rw [isPAlteration_iff]
  refine ⟨fun ⟨hf, h⟩ ↦ ⟨hf, fun x hx _ hq hqd ↦ (h x hx).mem_of_prime_of_dvd hq hqd⟩,
    fun ⟨hf, h⟩ ↦ ⟨hf, fun x hx ↦ isPNumber_iff.mpr ⟨hf.residueDegree_pos hx, h x hx⟩⟩⟩

/-- A composite of `P`-alterations is a `P`-alteration: generic degrees multiply in towers. -/
theorem IsPAlteration.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hg : g.IsPAlteration P)
    (hf : f.IsPAlteration P) : (f ≫ g).IsPAlteration P := by
  refine ⟨hg.toIsNoetherianAlteration.comp hf.toIsNoetherianAlteration, fun x hx ↦ ?_⟩
  rw [residueDegree_comp]
  exact (hg.isPNumber_residueDegree _
    (f.isMaximallyDominating_iff.mp hf.isMaximallyDominating x hx)).mul
    (hf.isPNumber_residueDegree x hx)

/-- Enlarging `P` preserves `P`-alterations. -/
theorem IsPAlteration.mono {f : X ⟶ Y} (hPQ : P ⊆ Q) (hf : f.IsPAlteration P) :
    f.IsPAlteration Q :=
  ⟨hf.toIsNoetherianAlteration, fun x hx ↦ (hf.isPNumber_residueDegree x hx).mono hPQ⟩

/-- When `P` contains every prime, the `P`-alterations are exactly the noetherian alterations. In
particular every noetherian alteration is a `P`-alteration for `P` the set of all primes. -/
theorem isPAlteration_iff_of_setOf_prime_subset (f : X ⟶ Y) (hP : {q | q.Prime} ⊆ P) :
    f.IsPAlteration P ↔ f.IsNoetherianAlteration := by
  rw [isPAlteration_iff_forall_prime_dvd]
  exact ⟨And.left, fun hf ↦ ⟨hf, fun _ _ _ hq _ ↦ hP hq⟩⟩

/-- For a prime `p`, the `{p}`-alterations are the noetherian alterations whose generic degrees
are powers of `p`. -/
theorem isPAlteration_singleton_iff (f : X ⟶ Y) {p : ℕ} (hp : p.Prime) :
    f.IsPAlteration {p} ↔
      f.IsNoetherianAlteration ∧ ∀ x ∈ genericPoints X, ∃ r, f.residueDegree x = p ^ r := by
  simp only [isPAlteration_iff, isPNumber_singleton_iff hp]

/-- **`ℓ′`-alterations.** For a prime `ℓ`, the `{ℓ}ᶜ`-alterations are the noetherian alterations
none of whose generic degrees is divisible by `ℓ`. -/
theorem isPAlteration_compl_singleton_iff (f : X ⟶ Y) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    f.IsPAlteration {ℓ}ᶜ ↔
      f.IsNoetherianAlteration ∧ ∀ x ∈ genericPoints X, ¬ℓ ∣ f.residueDegree x := by
  simp only [isPAlteration_iff, isPNumber_compl_singleton_iff hℓ]
  exact ⟨fun ⟨hf, h⟩ ↦ ⟨hf, fun x hx ↦ (h x hx).2⟩,
    fun ⟨hf, h⟩ ↦ ⟨hf, fun x hx ↦ ⟨hf.residueDegree_pos hx, h x hx⟩⟩⟩

/-- The `∅`-alterations are the noetherian alterations of generic degree one at every
component-generic point of the source. -/
theorem isPAlteration_empty_iff (f : X ⟶ Y) :
    f.IsPAlteration ∅ ↔
      f.IsNoetherianAlteration ∧ ∀ x ∈ genericPoints X, f.residueDegree x = 1 := by
  simp only [isPAlteration_iff, isPNumber_empty_iff]

/-- From an irreducible source, a `P`-alteration is a noetherian alteration whose degree at the
generic point is a `P`-number. -/
theorem isPAlteration_iff_of_irreducibleSpace [IrreducibleSpace X] (f : X ⟶ Y) :
    f.IsPAlteration P ↔
      f.IsNoetherianAlteration ∧ IsPNumber P (f.residueDegree (genericPoint X)) := by
  simp only [isPAlteration_iff, genericPoints_eq_singleton, mem_singleton_iff, forall_eq]

/-- An isomorphism is a `P`-alteration for every `P`: its residue degrees are one. -/
theorem isPAlteration_of_isIso (f : X ⟶ Y) [IsIso f] (P : Set ℕ) : f.IsPAlteration P :=
  ⟨isNoetherianAlteration_of_isFinite f (isMaximallyDominating_of_isOpenImmersion f),
    fun x _ ↦ by simp⟩

/-- The identity of a scheme is a `P`-alteration for every `P`. -/
theorem _root_.AlgebraicGeometry.Scheme.isPAlteration_id (X : Scheme.{u}) (P : Set ℕ) :
    IsPAlteration P (𝟙 X) :=
  isPAlteration_of_isIso _ P

/-- A modification of an irreducible scheme is an `∅`-alteration: it is an isomorphism over a
dense open, which contains the image of the generic point of the source, so its generic degree
is one. -/
theorem isPAlteration_empty_of_isModification [IrreducibleSpace X] (f : X ⟶ Y)
    [TauCeti.AlgebraicGeometry.IsModification f] : f.IsPAlteration ∅ := by
  obtain ⟨U, -, hfU, _⟩ :=
    TauCeti.AlgebraicGeometry.IsModification.exists_isIso_morphismRestrict (f := f)
  refine (isPAlteration_iff_of_irreducibleSpace f).mpr
    ⟨isNoetherianAlteration_of_isModification f, ?_⟩
  rw [isPNumber_empty_iff]
  have : Nonempty X := inferInstance
  exact f.residueDegree_eq_one_of_isIso_morphismRestrict
    (((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
      (by rw [univ_inter]; exact hfU.nonempty))

/-! ### Separable alterations -/

/-- A morphism `f : X ⟶ Y` is a *separable alteration* if it is a noetherian alteration whose
residue field extensions `κ(f x) ⟶ κ(x)`, at the component-generic points `x` of `X`, are
separable. -/
structure IsSeparableAlteration (f : X ⟶ Y) : Prop extends f.IsNoetherianAlteration where
  isSeparable_residueField : ∀ x ∈ genericPoints X,
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)

/-- A separable alteration is a noetherian alteration whose residue field extensions at the
component-generic points of its source are separable. -/
theorem isSeparableAlteration_iff (f : X ⟶ Y) :
    f.IsSeparableAlteration ↔ f.IsNoetherianAlteration ∧ ∀ x ∈ genericPoints X,
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) :=
  ⟨fun h ↦ ⟨h.toIsNoetherianAlteration, h.isSeparable_residueField⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- A composite of separable alterations is a separable alteration: separable field extensions
form towers. -/
theorem IsSeparableAlteration.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hg : g.IsSeparableAlteration)
    (hf : f.IsSeparableAlteration) : (f ≫ g).IsSeparableAlteration := by
  refine ⟨hg.toIsNoetherianAlteration.comp hf.toIsNoetherianAlteration, fun x hx ↦ ?_⟩
  let : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  have := isScalarTower_residueField f g x
  have := hg.isSeparable_residueField _
    (f.isMaximallyDominating_iff.mp hf.isMaximallyDominating x hx)
  have := hf.isSeparable_residueField x hx
  exact Algebra.IsSeparable.trans (Z.residueField (g (f x))) (Y.residueField (f x))
    (X.residueField x)

/-- An `∅`-alteration is separable: its residue field extensions at the component-generic points
of the source have degree one, so they are isomorphisms. -/
theorem isSeparableAlteration_of_isPAlteration_empty {f : X ⟶ Y} (hf : f.IsPAlteration ∅) :
    f.IsSeparableAlteration := by
  refine ⟨hf.toIsNoetherianAlteration, fun x hx ↦ ?_⟩
  let := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    (f.residueDegree_eq_one_iff x).mp ((isPAlteration_empty_iff f).mp hf |>.2 x hx)
  exact Algebra.IsSeparable.of_algHom _ _
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).symm.toAlgHom

/-- An isomorphism is a separable alteration. -/
theorem isSeparableAlteration_of_isIso (f : X ⟶ Y) [IsIso f] : f.IsSeparableAlteration :=
  isSeparableAlteration_of_isPAlteration_empty (isPAlteration_of_isIso f ∅)

/-- The identity of a scheme is a separable alteration. -/
theorem _root_.AlgebraicGeometry.Scheme.isSeparableAlteration_id (X : Scheme.{u}) :
    IsSeparableAlteration (𝟙 X) :=
  isSeparableAlteration_of_isIso _

end AlgebraicGeometry.Scheme.Hom
