/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic
-- Unfold the non-exposed `NonabelianH1` and `mk` locally: `equivOfTrivial` applies
-- `Quotient.congr` to the underlying quotient so that its `mk` lemmas hold by `rfl`.
import all TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Continuous nonabelian first cohomology for the trivial action

When `G` acts trivially on `A`, a continuous cocycle `f : G → A` satisfies
`f (g * h) = f g * f h`, so cocycles are continuous homomorphisms, and the cohomology relation
`f' g = a⁻¹ * f g * a` is conjugacy by `A`. Hence `H¹(G, A)` is the set of continuous
homomorphisms `G → A` modulo conjugation by `A`.

## Main definitions

* `TauCeti.NonabelianH1.Cocycle.equivOfTrivial`: for the trivial action, cocycles are continuous
  homomorphisms.
* `TauCeti.NonabelianH1.conjSetoid`: conjugacy of continuous homomorphisms `G → A`.
* `TauCeti.NonabelianH1.equivOfTrivial`: for the trivial action, `H¹(G, A)` is the set of
  continuous homomorphisms modulo conjugacy.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.
-/

public section

namespace TauCeti

namespace NonabelianH1

variable {G A : Type*} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]

variable (G A) in
/-- **Conjugacy of continuous homomorphisms**: `φ'` is conjugate to `φ` when
`φ' g = a⁻¹ * φ g * a` for one `a : A` and all `g`. -/
def conjSetoid : Setoid (G →ₜ* A) where
  r φ φ' := ∃ a : A, ∀ g, φ' g = a⁻¹ * φ g * a
  iseqv := by
    refine ⟨fun φ ↦ ⟨1, fun g ↦ by simp⟩, ?_, ?_⟩
    · rintro φ φ' ⟨a, ha⟩
      exact ⟨a⁻¹, fun g ↦ by simp [ha, mul_assoc]⟩
    · rintro φ φ' φ'' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, fun g ↦ by simp [ha, hb, mul_assoc]⟩

@[simp]
theorem conjSetoid_apply {φ φ' : G →ₜ* A} :
    conjSetoid G A φ φ' ↔ ∃ a : A, ∀ g, φ' g = a⁻¹ * φ g * a :=
  Iff.rfl

variable [MulDistribMulAction G A]

/-- **Cocycles for the trivial action are continuous homomorphisms.** -/
def Cocycle.equivOfTrivial (h : ∀ (g : G) (a : A), g • a = a) : Cocycle G A ≃ (G →ₜ* A) where
  toFun f :=
    { toFun := f
      map_one' := f.apply_one
      map_mul' g g' := by rw [f.apply_mul, h]
      continuous_toFun := f.continuous }
  invFun φ := ⟨φ, φ.continuous, fun g g' ↦ by rw [map_mul, h]⟩

@[simp]
theorem Cocycle.equivOfTrivial_symm_apply (h : ∀ (g : G) (a : A), g • a = a) (φ : G →ₜ* A)
    (g : G) : (Cocycle.equivOfTrivial h).symm φ g = φ g :=
  (rfl)

@[simp]
theorem Cocycle.equivOfTrivial_apply (h : ∀ (g : G) (a : A), g • a = a) (f : Cocycle G A)
    (g : G) : Cocycle.equivOfTrivial h f g = f g :=
  (rfl)

/-- For the trivial action, two cocycles are cohomologous exactly when the corresponding
homomorphisms are conjugate. -/
theorem Cocycle.equiv_iff_of_trivial (h : ∀ (g : G) (a : A), g • a = a) {f f' : Cocycle G A} :
    f ≈ f' ↔ conjSetoid G A (Cocycle.equivOfTrivial h f) (Cocycle.equivOfTrivial h f') := by
  simp only [Cocycle.equiv_iff, conjSetoid_apply, Cocycle.equivOfTrivial_apply, h]

/-- **`H¹` for the trivial action**: when `G` acts trivially on `A`, `H¹(G, A)` is the set of
continuous homomorphisms `G → A` modulo conjugation by `A`. -/
def equivOfTrivial (h : ∀ (g : G) (a : A), g • a = a) :
    NonabelianH1 G A ≃ Quotient (conjSetoid G A) :=
  Quotient.congr (Cocycle.equivOfTrivial h) fun _ _ ↦ Cocycle.equiv_iff_of_trivial h

@[simp]
theorem equivOfTrivial_mk (h : ∀ (g : G) (a : A), g • a = a) (f : Cocycle G A) :
    equivOfTrivial h (mk f) = Quotient.mk _ (Cocycle.equivOfTrivial h f) :=
  (rfl)

@[simp]
theorem equivOfTrivial_symm_mk (h : ∀ (g : G) (a : A), g • a = a) (φ : G →ₜ* A) :
    (equivOfTrivial h).symm (Quotient.mk _ φ) = mk ((Cocycle.equivOfTrivial h).symm φ) :=
  (rfl)

end NonabelianH1

end TauCeti
