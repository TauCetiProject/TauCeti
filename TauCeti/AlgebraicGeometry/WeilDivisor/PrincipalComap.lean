/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal

/-!
# Functoriality of principal divisors in the group of functions

The `OrderSystem` of `TauCeti.AlgebraicGeometry.WeilDivisor.Principal` packages the
order-of-vanishing data on a point type `X` valued in a group `G` (think `G = Additive Kˣ`, the
multiplicative group of a function field) from which principal divisors, the divisor class group
`Cl(X)`, and the abstract `Pic⁰` are built. This file records the **contravariant functoriality
of that construction in `G`**: a group homomorphism `φ : G' →+ G` pulls an order system back to
one valued in `G'`.

Concretely, if a subgroup of rational functions is singled out by a homomorphism `φ : G' →+ G`
(for instance the inclusion of a subgroup of `Additive Kˣ`), then the pulled-back order system
`S.comap φ` uses `ord_x ∘ φ` as its order-of-vanishing data. Its principal divisors are the
`S`-principal divisors of the functions in the image of `φ`, so they form a subgroup of the
`S`-principal divisors. Passing to quotients, the divisor class group of `S.comap φ` therefore
carries a **surjection** onto that of `S`, compatible with the weighted degree and so mapping
`Pic⁰` into `Pic⁰`.

Main definitions and results:

* `OrderSystem.comap`, the order system pulled back along `φ : G' →+ G`, with
  `principalDivisor_comap : (S.comap φ).principalDivisor g = S.principalDivisor (φ g)`;
* `comap_id` and `comap_comp`, the (contravariant) functor laws;
* `principalSubgroup_comap_le` and `principalSubgroup_comap_of_surjective`, comparing the
  principal subgroups (equal when `φ` is surjective);
* `IsWeightedDegreeZero.comap` and `IsUnweightedDegreeZero.comap`, transporting the
  weighted-degree-zero property;
* `OrderSystem.classGroupComap : (S.comap φ).ClassGroup →+ S.ClassGroup`, the induced surjection
  of divisor class groups, `weightedDegreeClass_comp_classGroupComap` (its compatibility with the
  descended weighted degree), and `classGroupComap_mem_picZero` (it carries `Pic⁰` into `Pic⁰`).

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A ("principal divisors",
"`Cl(X)`", "`Pic⁰ X = ker deg` as an abstract group"), rounding out the class-group construction
with its functoriality in the group of functions. No external mathematics is vendored; the proofs
reuse Tau Ceti's `OrderSystem` API and Mathlib's `AddMonoidHom` composition laws together with the
`OrderSystem.ClassGroup.lift` universal property.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G G' G'' : Type*} [AddCommGroup G] [AddCommGroup G'] [AddCommGroup G'']

/-- Two order systems on the same point type and value group agree once their order data agree;
the finiteness fields are propositions, hence equal by proof irrelevance. Kept `private` as the
extensionality helper backing the functor laws. -/
private lemma ext_ord {S T : OrderSystem X G} (h : S.ord = T.ord) : S = T := by
  obtain ⟨o₁, f₁⟩ := S
  obtain ⟨o₂, f₂⟩ := T
  cases h
  rfl

variable (S : OrderSystem X G)

/-- The order system pulled back along a group homomorphism `φ : G' →+ G`: the order of vanishing
at each point is `ord_x ∘ φ`.

For `φ` an inclusion of a subgroup of rational functions, this records the order-of-vanishing data
restricted to that subgroup; its principal divisors are the `S`-principal divisors of functions in
the image of `φ`. -/
@[expose] def comap (φ : G' →+ G) : OrderSystem X G' where
  ord x := (S.ord x).comp φ
  finite_support g := S.finite_support (φ g)

@[simp]
lemma comap_ord (φ : G' →+ G) (x : X) : (S.comap φ).ord x = (S.ord x).comp φ :=
  rfl

/-- The principal divisor of `g : G'` under the pulled-back order system is the `S`-principal
divisor of `φ g`. -/
@[simp]
lemma principalDivisor_comap (φ : G' →+ G) (g : G') :
    (S.comap φ).principalDivisor g = S.principalDivisor (φ g) := by
  ext x
  simp [coeff_principalDivisor]

/-- The principal-divisor homomorphism of the pulled-back order system factors through `φ`. -/
lemma principalHom_comap (φ : G' →+ G) :
    (S.comap φ).principalHom = S.principalHom.comp φ := by
  ext g
  simp [principalHom_apply]

/-- Pulling back along the identity is the original order system. -/
@[simp]
lemma comap_id : S.comap (AddMonoidHom.id G) = S :=
  ext_ord (by funext x; rw [comap_ord]; exact AddMonoidHom.comp_id (S.ord x))

/-- Pulling back is contravariantly functorial: `(S.comap φ).comap ψ = S.comap (φ.comp ψ)`. -/
lemma comap_comp (φ : G' →+ G) (ψ : G'' →+ G') :
    (S.comap φ).comap ψ = S.comap (φ.comp ψ) :=
  ext_ord (by
    funext x
    simp only [comap_ord]
    exact AddMonoidHom.comp_assoc ψ φ (S.ord x))

/-- The principal divisors of the pulled-back order system form a subgroup of the `S`-principal
divisors. -/
lemma principalSubgroup_comap_le (φ : G' →+ G) :
    (S.comap φ).principalSubgroup ≤ S.principalSubgroup := by
  intro D hD
  rw [mem_principalSubgroup] at hD ⊢
  obtain ⟨g, rfl⟩ := hD
  exact ⟨φ g, (principalDivisor_comap S φ g).symm⟩

/-- When `φ` is surjective the two principal subgroups coincide: every function in `G` is hit, so
every `S`-principal divisor is already a `comap`-principal divisor. -/
lemma principalSubgroup_comap_of_surjective (φ : G' →+ G) (hφ : Function.Surjective φ) :
    (S.comap φ).principalSubgroup = S.principalSubgroup := by
  refine le_antisymm (principalSubgroup_comap_le S φ) ?_
  intro D hD
  rw [mem_principalSubgroup] at hD ⊢
  obtain ⟨g, rfl⟩ := hD
  obtain ⟨g', rfl⟩ := hφ g
  exact ⟨g', principalDivisor_comap S φ g'⟩

/-- The induced homomorphism of divisor class groups `(S.comap φ).ClassGroup →+ S.ClassGroup`:
the class of a divisor for the finer principal equivalence maps to its class for the coarser one.
It exists because every `comap`-principal divisor is `S`-principal, and is surjective since the
divisor class map is. -/
noncomputable def classGroupComap (φ : G' →+ G) :
    (S.comap φ).ClassGroup →+ S.ClassGroup :=
  ClassGroup.lift (S.comap φ) S.divisorClass fun g => by
    rw [principalDivisor_comap]
    exact divisorClass_principalDivisor S (φ g)

@[simp]
lemma classGroupComap_divisorClass (φ : G' →+ G) (D : WeilDivisor X) :
    classGroupComap S φ ((S.comap φ).divisorClass D) = S.divisorClass D :=
  ClassGroup.lift_divisorClass (S.comap φ) S.divisorClass _ D

lemma classGroupComap_surjective (φ : G' →+ G) :
    Function.Surjective (classGroupComap S φ) := by
  intro c
  obtain ⟨D, rfl⟩ := S.divisorClass_surjective c
  exact ⟨(S.comap φ).divisorClass D, classGroupComap_divisorClass S φ D⟩

variable {S}

/-- Two divisors linearly equivalent for the pulled-back order system are linearly equivalent for
`S`: the finer equivalence implies the coarser one. -/
lemma LinearlyEquivalent.comap (φ : G' →+ G) {D E : WeilDivisor X}
    (h : (S.comap φ).LinearlyEquivalent D E) : S.LinearlyEquivalent D E := by
  rw [linearlyEquivalent_iff] at h ⊢
  exact principalSubgroup_comap_le S φ h

/-- The weighted-degree-zero property transports along a pullback: if every `S`-principal divisor
has weighted degree zero, so does every `comap`-principal divisor, being an `S`-principal
divisor. -/
lemma IsWeightedDegreeZero.comap {w : X → ℤ} (h : S.IsWeightedDegreeZero w) (φ : G' →+ G) :
    (S.comap φ).IsWeightedDegreeZero w := fun g => by
  rw [principalDivisor_comap]
  exact h (φ g)

/-- The unweighted-degree-zero property transports along a pullback. -/
lemma IsUnweightedDegreeZero.comap (h : S.IsUnweightedDegreeZero) (φ : G' →+ G) :
    (S.comap φ).IsUnweightedDegreeZero :=
  IsWeightedDegreeZero.comap h φ

/-- The induced class-group map is compatible with the descended weighted degree: descending the
weighted degree through `classGroupComap` recovers the descended weighted degree of the
pulled-back order system. -/
lemma weightedDegreeClass_comp_classGroupComap {w : X → ℤ} (h : S.IsWeightedDegreeZero w)
    (φ : G' →+ G) :
    (weightedDegreeClass w h).comp (classGroupComap S φ) =
      weightedDegreeClass w (h.comap φ) := by
  refine AddMonoidHom.ext fun c => ?_
  obtain ⟨D, rfl⟩ := (S.comap φ).divisorClass_surjective c
  simp [classGroupComap_divisorClass, weightedDegreeClass_divisorClass]

/-- The induced class-group map carries `Pic⁰` into `Pic⁰`: a class of weighted degree zero for
the pulled-back order system maps to one of weighted degree zero for `S`. -/
lemma classGroupComap_mem_picZero {w : X → ℤ} (h : S.IsWeightedDegreeZero w) (φ : G' →+ G)
    {c : (S.comap φ).ClassGroup} (hc : c ∈ picZero w (h.comap φ)) :
    classGroupComap S φ c ∈ picZero w h := by
  rw [mem_picZero] at hc ⊢
  have hcomp := DFunLike.congr_fun (weightedDegreeClass_comp_classGroupComap h φ) c
  simp only [AddMonoidHom.comp_apply] at hcomp
  rw [hcomp]
  exact hc

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
