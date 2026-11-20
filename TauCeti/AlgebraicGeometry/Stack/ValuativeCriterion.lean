/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.AlgebraicGeometry.Stack.StackInGroupoids
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.LiftingProblem

/-!
# DVR lifting after extension for morphisms of stacks in groupoids

The existence part of the valuative criterion for a morphism `f : X ⟶ Y` of stacks in groupoids
cannot ask for lifts over a discrete valuation ring `R` itself: a nontrivial `ℤ/2`-torsor over
the fraction field `K` of `ℂ[[t]]` does not extend over `ℂ[[t]]`, although `B(ℤ/2)` is proper over
`ℂ`. It asks instead for lifts after an extension of the generic point. Given a DVR `R` with
fraction field `K` and a lifting problem `P` for `f` along `Spec K ⟶ Spec R` (an object `x` of `X`
over `Spec K`, an object `y` of `Y` over `Spec R`, and an identification of the two images in `Y`
over `Spec K`), we ask for a field extension `K'` of `K` and a valuation ring `R' ⊆ K'` dominating
`R`, such that the pullback of `P` along `Spec R' ⟶ Spec R` has a lift in the sense of
`CategoryTheory.Pseudofunctor.StrongTrans.LiftingProblem.Lift`: an object `a` of `X` over
`Spec R'` with isomorphisms `a|_{Spec K'} ≅ x|_{Spec K'}` and `y|_{Spec R'} ≅ f a` compatible
with the given identification (a nonempty category of dotted arrows, Stacks, Definition 0CLA). This
is the lifting hypothesis of the Noetherian valuative criterion for properness of morphisms of
algebraic stacks (Stacks, Lemma 0CQM, with test diagrams through the identity of `X`).

The ring `R'` need not be a discrete valuation ring and the extension `K'/K` need not be finite.
A morphism has this property as soon as every such lifting problem has a lift over `R` itself
(`StackInGroupoids.Hom.DVRLiftingAfterExtension.of_nonempty_lift`); for instance every morphism
which is an equivalence over every scheme has it
(`StackInGroupoids.Hom.IsFiberwiseEquiv.dvrLiftingAfterExtension`).

## Main declarations

* `TauCeti.AlgebraicGeometry.StackInGroupoids.Hom.DVRLiftingAfterExtension`: every lifting
  problem along `Spec K ⟶ Spec R`, for a DVR `R` with fraction field `K`, has a lift after
  extending `K` and replacing `R` by a dominating valuation ring.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.Hom.DVRLiftingAfterExtension.of_nonempty_lift`:
  lifts without extension suffice.

## References

* [Stacks Project, Definition 0CLA](https://stacks.math.columbia.edu/tag/0CLA)
* [Stacks Project, Lemma 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Section 0CL9](https://stacks.math.columbia.edu/tag/0CL9)
-/

public section

open CategoryTheory Opposite Pseudofunctor

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- A commutative square of commutative rings `b ∘ a = d ∘ c` gives a commutative square of their
spectra, `Spec b ≫ Spec a = Spec d ≫ Spec c`. -/
lemma commSq_SpecMap_ofHom {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T]
    [CommRing U] {a : R →+* S} {b : S →+* T} {c : R →+* U} {d : U →+* T}
    (h : b.comp a = d.comp c) :
    CommSq (Spec.map (CommRingCat.ofHom b)) (Spec.map (CommRingCat.ofHom d))
      (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom c)) :=
  ⟨by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    h]⟩

namespace StackInGroupoids.Hom

variable {X Y : StackInGroupoids.{u}}

/-- A morphism `f : X ⟶ Y` of stacks in groupoids has DVR lifting after extension if for every
discrete valuation ring `R` with fraction field `K` and every lifting problem `P` for `f` along
`Spec K ⟶ Spec R`, there are a field extension `K'` of `K`, a valuation ring `R'` of `K'` and a
local ring map `φ : R →+* R'` compatible with `R → K → K'` (so `R'` dominates `R`), such that the
pullback of `P` along `Spec R' ⟶ Spec R` has a lift. The extension `K'/K` need not be finite
and `R'` need not be a discrete valuation ring (compare the hypothesis of Stacks, Lemma 0CQM). -/
def DVRLiftingAfterExtension (f : X.Hom Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K]
    (P : f.LiftingProblem (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (R' : ValuationSubring K') (φ : R →+* R')
      (hφ : (algebraMap K K').comp (algebraMap R K) = R'.subtype.comp φ),
      IsLocalHom φ ∧ Nonempty (P.pullback (commSq_SpecMap_ofHom hφ)).Lift

lemma dvrLiftingAfterExtension_iff (f : X.Hom Y) :
    f.DVRLiftingAfterExtension ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u) [Field K]
        [Algebra R K] [IsFractionRing R K]
        (P : f.LiftingProblem (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (R' : ValuationSubring K')
          (φ : R →+* R') (hφ : (algebraMap K K').comp (algebraMap R K) = R'.subtype.comp φ),
          IsLocalHom φ ∧ Nonempty (P.pullback (commSq_SpecMap_ofHom hφ)).Lift :=
  Iff.rfl

/-- If every lifting problem for `f` along `Spec K ⟶ Spec R`, for a DVR `R` with fraction field
`K`, has a lift over `R` itself, then `f` has DVR lifting after extension: take `K' = K` and for
`R'` the image of `R` in `K`. -/
lemma DVRLiftingAfterExtension.of_nonempty_lift {f : X.Hom Y}
    (h : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u)
      [Field K] [Algebra R K] [IsFractionRing R K]
      (P : f.LiftingProblem (Spec.map (CommRingCat.ofHom (algebraMap R K)))), Nonempty P.Lift) :
    f.DVRLiftingAfterExtension := by
  intro R _ _ _ K _ _ _ P
  let R' := (ValuationRing.valuation R K).valuationSubring
  have hmem (r : R) : algebraMap R K r ∈ R' := (ValuationRing.mem_integer_iff R K _).2 ⟨r, rfl⟩
  let φ : R →+* R' := (algebraMap R K).codRestrict R' hmem
  have hφ : Function.Bijective φ := by
    refine ⟨fun r s hrs ↦ IsFractionRing.injective R K (congrArg Subtype.val hrs), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := (ValuationRing.mem_integer_iff R K x).1 hx
    exact ⟨r, rfl⟩
  have : IsLocalHom φ := ⟨(isLocalHom_equiv (RingEquiv.ofBijective φ hφ)).map_nonunit⟩
  have := h R K P
  exact ⟨K, inferInstance, inferInstance, R', φ, by ext; simp [φ], inferInstance,
    P.nonempty_lift_pullback _⟩

/-- A morphism of stacks in groupoids which is an equivalence over every scheme has DVR lifting
after extension, without needing to extend. -/
lemma IsFiberwiseEquiv.dvrLiftingAfterExtension {f : X.Hom Y} (hf : f.IsFiberwiseEquiv) :
    f.DVRLiftingAfterExtension :=
  DVRLiftingAfterExtension.of_nonempty_lift fun R _ _ _ K _ _ _ P ↦
    have := (f.isFiberwiseEquiv_iff.1 hf) (Spec (CommRingCat.of R))
    have := (f.isFiberwiseEquiv_iff.1 hf) (Spec (CommRingCat.of K))
    P.nonempty_lift

/-- The identity morphism of a stack in groupoids has DVR lifting after extension. -/
lemma dvrLiftingAfterExtension_id (X : StackInGroupoids.{u}) :
    DVRLiftingAfterExtension (StrongTrans.id X.toSchPseudofunctor) :=
  (isFiberwiseEquiv_id X).dvrLiftingAfterExtension

end StackInGroupoids.Hom

end TauCeti.AlgebraicGeometry
