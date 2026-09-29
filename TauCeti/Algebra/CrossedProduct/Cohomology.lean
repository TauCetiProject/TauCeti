/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Cohomologous

/-!
# Cohomology classes of crossed-product cocycles

A `TwoCocycle K L` is the multiplicative form of an inhomogeneous `2`-cocycle of
`Aut_K(L)` with values in `Lˣ`. This file connects that explicit object to Mathlib's second group
cohomology. The map `TwoCocycle.cohomologyClass` reads a crossed-product cocycle as a class in
`H²(Aut_K(L), Lˣ)`, and `TwoCocycle.cohomologyClass_eq_iff` proves that equality of classes is
exactly the explicit coboundary relation already used by crossed products.

Consequently `TwoCocycle.cohomologyClassEquiv` identifies `H²(Aut_K(L), Lˣ)` with explicit
`2`-cocycles modulo `TwoCocycle.Cohomologous`. This is the finite-cohomology input needed to apply
the Hilbert 90 injectivity theorem to the classification of crossed-product Brauer classes.

## Universes

Mathlib's multiplicative interface to `groupCohomology.cocycles₂` (`cocyclesOfIsMulCocycle₂`,
`coboundariesOfIsMulCoboundary₂`, `isMulCoboundary₂_of_mem_coboundaries₂`) is stated for an acting
group and coefficient group in `Type`. This comes from Mathlib's low-degree group cohomology, which
requires the acting group to share the universe of the coefficient ring, here `ℤ : Type`. The
underlying `TwoCocycle` and `CrossedProduct` definitions remain universe-polymorphic; only their
comparison with `groupCohomology` has this restriction.

## Main results

* `TauCeti.TwoCocycle.toCocycles₂`: the additive `2`-cocycle underlying an explicit
  crossed-product cocycle.
* `TauCeti.TwoCocycle.cohomologyClass`: its class in `H²(Aut_K(L), Lˣ)`.
* `TauCeti.TwoCocycle.cohomologyClass_eq_iff`: two explicit cocycles determine the same class
  exactly when they are cohomologous.
* `TauCeti.TwoCocycle.cohomologyClassEquiv`: second cohomology classifies explicit cocycles modulo
  the cohomologous relation.

## References

The construction adapts the factor-set classification of
`TauCeti/GroupTheory/GroupExtension/Cohomology.lean` (`TauCeti.FactorSet.toCocycles₂`,
`TauCeti.FactorSet.cohomologyClass_eq_iff`, `TauCeti.FactorSet.cohomologyClassEquiv`) from
normalized factor sets of an arbitrary group to the unnormalized cocycles of `Aut_K(L)` used by
crossed products; since those cocycles are not normalized, no normalization step is needed for
surjectivity.

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
* J.-P. Serre, *Local Fields*, Chapter X, §5.
-/

public section

open groupCohomology

namespace TauCeti

variable {K L : Type} [CommSemiring K] [CommRing L] [Algebra K L]

namespace TwoCocycle

section Class

variable (z w : TwoCocycle K L)

/-- A crossed-product `2`-cocycle, read as a `2`-cocycle valued in `Additive Lˣ`. -/
def toCocycles₂ : cocycles₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :=
  cocyclesOfIsMulCocycle₂ z.isMulCocycle₂

/-- The additive cocycle underlying `z` evaluates to `Additive.ofMul (z(σ, τ))`. -/
@[simp]
theorem coe_toCocycles₂ :
    ⇑z.toCocycles₂ = fun p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) => Additive.ofMul (z.toFun p.1 p.2) :=
  (rfl)

/-- The class in `H²(Aut_K(L), Lˣ)` represented by a crossed-product `2`-cocycle. -/
noncomputable def cohomologyClass : H2 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :=
  H2π _ z.toCocycles₂

/-- The cohomology class of `z` is the image of its underlying additive cocycle. -/
theorem cohomologyClass_def :
    z.cohomologyClass = H2π (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) z.toCocycles₂ :=
  (rfl)

/-- The pointwise quotient of two multiplicative cocycles is the difference of their additive
counterparts. -/
theorem coe_toCocycles₂_sub :
    ⇑w.toCocycles₂ - ⇑z.toCocycles₂ =
      fun p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) => Additive.ofMul (w.toFun p.1 p.2 / z.toFun p.1 p.2) := by
  ext p
  simp only [coe_toCocycles₂, ofMul_div]
  rfl

/-- Two crossed-product cocycles represent the same class in `H²(Aut_K(L), Lˣ)` exactly when
they are cohomologous. -/
theorem cohomologyClass_eq_iff : z.cohomologyClass = w.cohomologyClass ↔ z.Cohomologous w := by
  rw [cohomologous_def]
  rw [eq_comm, cohomologyClass_def, cohomologyClass_def, H2π_eq_iff, coe_toCocycles₂_sub]
  constructor
  · intro h
    have hb := isMulCoboundary₂_of_mem_coboundaries₂ _ h
    have heq :
        (⇑Additive.toMul ∘
            fun p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) =>
              Additive.ofMul (w.toFun p.1 p.2 / z.toFun p.1 p.2)) =
          fun p => w.toFun p.1 p.2 / z.toFun p.1 p.2 := by
      funext p
      exact toMul_ofMul _
    rwa [heq] at hb
  · intro h
    exact (coboundariesOfIsMulCoboundary₂ h).2

/-- The explicit cohomologous relation is equality of second cohomology classes. -/
@[simp]
theorem cohomologous_iff_cohomologyClass_eq :
    z.Cohomologous w ↔ z.cohomologyClass = w.cohomologyClass :=
  (cohomologyClass_eq_iff z w).symm

end Class

section Classification

/-- Every class in `H²(Aut_K(L), Lˣ)` is represented by an explicit crossed-product
`2`-cocycle. -/
theorem exists_cohomologyClass_eq
    (x : H2 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) :
    ∃ z : TwoCocycle K L, z.cohomologyClass = x := by
  induction x using H2_induction_on with
  | _ y =>
      let z : TwoCocycle K L :=
        { toFun := fun σ τ => Additive.toMul (y (σ, τ))
          isMulCocycle₂ := isMulCocycle₂_of_mem_cocycles₂ _ y.2 }
      refine ⟨z, ?_⟩
      rw [cohomologyClass_def]
      apply congrArg (H2π (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ))
      exact cocycles₂_ext fun _ _ => rfl

variable (K L) in
/-- The setoid of cohomologous crossed-product `2`-cocycles, presented as the kernel of their
cohomology class. -/
noncomputable def cohomologousSetoid : Setoid (TwoCocycle K L) :=
  Setoid.ker cohomologyClass

/-- The relation of `TwoCocycle.cohomologousSetoid` is `TwoCocycle.Cohomologous`. -/
@[simp]
theorem cohomologousSetoid_apply {z w : TwoCocycle K L} :
    cohomologousSetoid K L z w ↔ z.Cohomologous w :=
  Setoid.ker_def.trans (cohomologyClass_eq_iff z w)

variable (K L) in
/-- Second group cohomology classifies crossed-product `2`-cocycles modulo coboundaries. -/
noncomputable def cohomologyClassEquiv :
    Quotient (cohomologousSetoid K L) ≃ H2 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :=
  Setoid.quotientKerEquivOfSurjective _ exists_cohomologyClass_eq

/-- `TwoCocycle.cohomologyClassEquiv` sends the class of a cocycle to its cohomology class. -/
@[simp]
theorem cohomologyClassEquiv_apply_mk (z : TwoCocycle K L) :
    cohomologyClassEquiv K L (Quotient.mk _ z) = z.cohomologyClass :=
  (rfl)

end Classification

end TwoCocycle

end TauCeti
