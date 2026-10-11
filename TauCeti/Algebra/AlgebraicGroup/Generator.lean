/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Bialgebra.Hom.Representable
public import TauCeti.RingTheory.Norm.FullSetOfSections
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Katz–Mazur generators of finite free group schemes

Let `H` be a commutative `R`-bialgebra, finite and free as an `R`-module, so that `G = Spec H` is
a finite locally free monoid scheme over `Spec R`; its points with values in `R` form the
convolution monoid `WithConv (H →ₐ[R] R)`. For a finite group `A`, a homomorphism
`φ : A →* G(R)` is an *`A`-generator* of `G` (Katz–Mazur §1.10) when the `|A|` points `φ a` form a
full set of sections of `G` over `R` (`TauCeti.IsFullSetOfSections`): after every base change, the
norm of a function on `G` is the product of its values at the points `φ a`. This is how Katz and
Mazur say, over an arbitrary base and counting multiplicities, that the points `φ a` exhaust `G`;
they need not be distinct, since in characteristic `p` the identity, taken `p` times, is a full
set of sections of `μ_p`. The Drinfeld level structures on elliptic curves are of this form: a
`[Γ(N)]`-structure on `E` is a `(ℤ/N)²`-generator of `E[N]`.

The second half of the file constructs the scheme of `A`-generators of `G`. The scheme of
homomorphisms `A_R → G` from the constant group `A_R = Spec (coordinateRing R A)` is
`Spec (HomAlgebra R H (coordinateRing R A))`. On it the universal homomorphism provides a universal
family of `|A|` points of `G`, and the locus where these points form a full set of sections is a
closed subscheme of finite presentation, `Spec (HomAlgebra R H (coordinateRing R A) ⧸ I)` with
`I = generatorIdeal R H A`. Its points with values in `T` are the homomorphisms `A_T → G_T` of
monoid schemes over `T` whose points `A →* G(T)` form an `A`-generator of `G_T`.

## Main definitions

* `TauCeti.IsAGenerator φ`: the homomorphism `φ : A →* WithConv (H →ₐ[R] R)` is an `A`-generator.
* `TauCeti.ConstantGroup.pointsOfBialgHom g`: the homomorphism `A →* G(T)` attached to a
  homomorphism `g` of monoid schemes `A_T → G_T` over `T`, given as a `T`-bialgebra homomorphism
  `T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A`.
* `TauCeti.generatorIdeal R H A`: the ideal of `HomAlgebra R H (coordinateRing R A)` cutting out
  the scheme of `A`-generators.

## Main results

* `TauCeti.IsAGenerator.card_eq_finrank`: over a nontrivial ring, the order of `A` is the rank
  of `G`.
* `TauCeti.IsAGenerator.baseChange`, `TauCeti.IsAGenerator.of_baseChange` and
  `TauCeti.isAGenerator_baseChange_iff`: `A`-generators are stable under arbitrary base change and
  descend along injective ring maps, in particular along faithfully flat ones.
* `TauCeti.ConstantGroup.isAGenerator_toPoints`: the tautological homomorphism from `A` to the
  points of the constant group `A_R` is an `A`-generator.
* `TauCeti.isAGenerator_pointsOfBialgHom_homEquiv_iff` and
  `TauCeti.quotientGeneratorIdealHomEquiv`: the universal property of the scheme of
  `A`-generators. `TauCeti.generatorIdeal_fg` and the accompanying instance show that it is of
  finite presentation over `R`.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §§1.8–1.10.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

section Generator

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [Bialgebra R H]
variable {A : Type*} [Monoid A] [Fintype A]

/-- A homomorphism `φ : A →* G(R)` from a finite group (only its monoid structure is used) to the
points of `G = Spec H` is an *`A`-generator* of `G` (Katz–Mazur §1.10) if the points `φ a`, for
`a ∈ A`, form a full set of sections of `G` over `R`. -/
def IsAGenerator (φ : A →* WithConv (H →ₐ[R] R)) : Prop :=
  IsFullSetOfSections fun a ↦ (φ a).ofConv

variable {φ : A →* WithConv (H →ₐ[R] R)}

/-- Unfolding `IsAGenerator`. -/
theorem isAGenerator_iff : IsAGenerator φ ↔ IsFullSetOfSections fun a ↦ (φ a).ofConv :=
  Iff.rfl

variable [Module.Free R H] [Module.Finite R H]

/-- Over a nontrivial ring, if `G` has an `A`-generator then the order of `A` is the rank of `G`. -/
theorem IsAGenerator.card_eq_finrank [Nontrivial R] (h : IsAGenerator φ) :
    Fintype.card A = Module.finrank R H :=
  IsFullSetOfSections.card_eq_finrank h

/-- An `A`-generator remains one after an arbitrary base change `R → T`. -/
theorem IsAGenerator.baseChange (h : IsAGenerator φ) (T : Type w) [CommRing T] [Algebra R T] :
    IsAGenerator ((AlgHom.pointsBaseChange T).comp φ) := by
  simpa [isAGenerator_iff, AlgHom.ofConv_pointsBaseChange] using
    IsFullSetOfSections.baseChange h T

/-- Being an `A`-generator descends along an injective ring map `R → T`, in particular along a
faithfully flat one. -/
theorem IsAGenerator.of_baseChange {T : Type w} [CommRing T] [Algebra R T]
    (hT : Function.Injective (algebraMap R T))
    (h : IsAGenerator ((AlgHom.pointsBaseChange T).comp φ)) : IsAGenerator φ :=
  IsFullSetOfSections.of_baseChange hT <| by
    simpa [isAGenerator_iff, AlgHom.ofConv_pointsBaseChange] using h

/-- Over a base change which is injective, being an `A`-generator can be checked after the base
change. -/
theorem isAGenerator_baseChange_iff {T : Type w} [CommRing T] [Algebra R T]
    (hT : Function.Injective (algebraMap R T)) :
    IsAGenerator ((AlgHom.pointsBaseChange T).comp φ) ↔ IsAGenerator φ :=
  ⟨.of_baseChange hT, fun h ↦ h.baseChange T⟩

end Generator

namespace ConstantGroup

variable (R : Type u) [CommRing R] (A : Type*) [Group A] [Fintype A]

/-- The tautological homomorphism from a finite group `A` to the points of its constant group
`A_R` is an `A`-generator: the evaluations at the elements of `A` form a full set of sections of
`A_R = ⨆_{a ∈ A} Spec R`. -/
theorem isAGenerator_toPoints : IsAGenerator (toPoints R A) := by
  have h (a : A) : (toPoints R A a).ofConv =
      (Pi.evalAlgHom R (fun _ : A ↦ R) a).comp (functionAlgEquiv R A).toAlgHom := by
    ext; simp
  simpa only [isAGenerator_iff, h, isFullSetOfSections_comp_algEquiv_iff] using
    isFullSetOfSections_evalAlgHom

variable {R A} (H : Type v) [CommRing H] [Bialgebra R H] {T : Type w} [CommRing T] [Algebra R T]

/-- The homomorphism `A →* G(T)` attached to a homomorphism `A_T → G_T` of monoid schemes over
`T` from the constant group, where `G = Spec H`. The homomorphism of monoid schemes is given as a
`T`-bialgebra homomorphism `g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A`, and `a ∈ A` goes to
the image under `g` of the point `a` of `A_T`. -/
noncomputable def pointsOfBialgHom (g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) :
    A →* WithConv (T ⊗[R] H →ₐ[T] T) :=
  (AlgHom.mapDomain (H₁ := T ⊗[R] H) (H₂ := T ⊗[R] coordinateRing R A) (A := T) g).comp
    ((AlgHom.pointsBaseChange T).comp (toPoints R A))

variable {H}

/-- The point `pointsOfBialgHom g a` is the composite of `g` with the base change of evaluation
at `a`. -/
@[simp]
theorem ofConv_pointsOfBialgHom (g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) (a : A) :
    (pointsOfBialgHom H g a).ofConv = ((eval R A a).sectionBaseChange T).comp (g : _ →ₐ[T] _) := by
  simp [pointsOfBialgHom, AlgHom.ofConv_pointsBaseChange]

end ConstantGroup

/-! ### The scheme of `A`-generators -/

section Locus

open ConstantGroup TauCeti.Bialgebra

variable (R : Type u) (H : Type v) [CommRing R] [CommRing H] [Bialgebra R H]
  [Module.Free R H] [Module.Finite R H] (A : Type*) [Group A] [Fintype A]

-- `HomAlgebra` asks for the target to be finitely presented as an algebra, which holds for a
-- finite free `H`
attribute [local instance] Module.finitePresentation_of_projective

-- The universal family of points of `Spec H` on the scheme of homomorphisms from `A_R`: the points
-- of the universal homomorphism, restricted along `H → HomAlgebra R H _ ⊗[R] H`.
private noncomputable def generatorFamily (a : A) :
    H →ₐ[R] HomAlgebra R H (coordinateRing R A) :=
  (AlgHom.liftEquiv R _ H _).symm
    (pointsOfBialgHom H (HomAlgebra.homEquiv R H _ _ (AlgHom.id R _)) a).ofConv

variable {R H A}

-- Specializing the universal family along `φ` gives the points of the homomorphism classified by
-- `φ`; this is the naturality `HomAlgebra.homEquiv_comp_one_tmul`.
private theorem liftEquiv_comp_generatorFamily {T : Type w} [CommRing T] [Algebra R T]
    (φ : HomAlgebra R H (coordinateRing R A) →ₐ[R] T) (a : A) :
    AlgHom.liftEquiv R T H T (φ.comp (generatorFamily R H A a)) =
      (pointsOfBialgHom H (HomAlgebra.homEquiv R H _ T φ) a).ofConv := by
  ext h
  have := HomAlgebra.homEquiv_comp_one_tmul (AlgHom.id R _) φ h
  rw [AlgHom.comp_id] at this
  simp [generatorFamily, this]

variable (R H A)

/-- The ideal of the *scheme of `A`-generators* of `G = Spec H`: the closed subscheme
`Spec (HomAlgebra R H (coordinateRing R A) ⧸ generatorIdeal R H A)` of the scheme of homomorphisms
`A_R → G` is the locus over which the points of the universal homomorphism form a full set of
sections (`isAGenerator_pointsOfBialgHom_homEquiv_iff`). It is the full-set ideal
`fullSetIdeal` of that universal family of points. -/
noncomputable def generatorIdeal : Ideal (HomAlgebra R H (coordinateRing R A)) :=
  fullSetIdeal (generatorFamily R H A)

variable {R H A}

/-- **The scheme of `A`-generators.** For `φ : HomAlgebra R H (coordinateRing R A) →ₐ[R] T`,
classifying a homomorphism `A_T → G_T`, the induced homomorphism `A →* G(T)` is an `A`-generator
if and only if `φ` kills `generatorIdeal R H A`, that is, `Spec T → Spec (HomAlgebra R H _)`
factors through the scheme of `A`-generators. -/
theorem isAGenerator_pointsOfBialgHom_homEquiv_iff {T : Type w} [CommRing T] [Algebra R T]
    (φ : HomAlgebra R H (coordinateRing R A) →ₐ[R] T) :
    IsAGenerator (pointsOfBialgHom H (HomAlgebra.homEquiv R H _ T φ)) ↔
      generatorIdeal R H A ≤ RingHom.ker φ := by
  simp only [generatorIdeal, ← isFullSetOfSections_liftEquiv_comp_iff,
    liftEquiv_comp_generatorFamily, isAGenerator_iff]

variable (R H A) in
/-- The ideal of the scheme of `A`-generators is finitely generated. -/
theorem generatorIdeal_fg : (generatorIdeal R H A).FG :=
  fullSetIdeal_fg _

/-- The scheme of `A`-generators is of finite presentation over `R`. -/
instance : Algebra.FinitePresentation R
    (HomAlgebra R H (coordinateRing R A) ⧸ generatorIdeal R H A) :=
  .quotient (generatorIdeal_fg R H A)

variable (R H A) in
/-- **Universal property of the scheme of `A`-generators.** `R`-algebra maps out of
`HomAlgebra R H (coordinateRing R A) ⧸ generatorIdeal R H A` correspond to the homomorphisms
`A_T → G_T` of monoid schemes over `T`, given as `T`-bialgebra homomorphisms
`T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A`, whose points form an `A`-generator. -/
noncomputable def quotientGeneratorIdealHomEquiv (T : Type w) [CommRing T] [Algebra R T] :
    (HomAlgebra R H (coordinateRing R A) ⧸ generatorIdeal R H A →ₐ[R] T) ≃
      {g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A // IsAGenerator (pointsOfBialgHom H g)} :=
  (quotientFullSetIdealHomEquiv _ T).trans <| (HomAlgebra.homEquiv R H _ T).subtypeEquiv
    fun φ ↦ by
      rw [isAGenerator_pointsOfBialgHom_homEquiv_iff, isFullSetOfSections_liftEquiv_comp_iff,
        generatorIdeal]

/-- The homomorphism attached to `g : _ ⧸ generatorIdeal R H A →ₐ[R] T` is the one classified by
`g` composed with the quotient map. -/
@[simp]
theorem coe_quotientGeneratorIdealHomEquiv_apply {T : Type w} [CommRing T] [Algebra R T]
    (g : HomAlgebra R H (coordinateRing R A) ⧸ generatorIdeal R H A →ₐ[R] T) :
    (quotientGeneratorIdealHomEquiv R H A T g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A) =
      HomAlgebra.homEquiv R H _ T (g.comp (Ideal.Quotient.mkₐ R _)) :=
  congrArg (HomAlgebra.homEquiv R H _ T) (coe_quotientFullSetIdealHomEquiv_apply _ g)

/-- The map out of the scheme of `A`-generators attached to an `A`-generating homomorphism `g` is
the map induced on the quotient by the `R`-algebra map classifying `g`. -/
@[simp]
theorem quotientGeneratorIdealHomEquiv_symm_apply_mk {T : Type w} [CommRing T] [Algebra R T]
    (g : {g : T ⊗[R] H →ₐc[T] T ⊗[R] coordinateRing R A // IsAGenerator (pointsOfBialgHom H g)})
    (x : HomAlgebra R H (coordinateRing R A)) :
    (quotientGeneratorIdealHomEquiv R H A T).symm g (Ideal.Quotient.mk _ x) =
      (HomAlgebra.homEquiv R H _ T).symm g.1 x :=
  quotientFullSetIdealHomEquiv_symm_apply_mk _ _ x

end Locus

end TauCeti
