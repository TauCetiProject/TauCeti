/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.CentralSimple
public import TauCeti.Algebra.CrossedProduct.Cohomologous
public import TauCeti.Algebra.BrauerGroup.Group

/-!
# Brauer classes of crossed-product algebras

This file bundles the crossed-product algebra of a `2`-cocycle of a finite Galois extension as a
central simple algebra and defines its class in the Brauer group.

## Main definitions

* `TauCeti.BrauerGroup.crossedProductCSA`: the crossed product bundled as a central simple algebra.
* `TauCeti.BrauerGroup.crossedProductClass`: its Brauer class.

## Main results

* `TauCeti.BrauerGroup.crossedProductClass_eq_of_cohomologous`: cohomologous cocycles have the
  same Brauer class.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

universe u v

namespace TauCeti.BrauerGroup

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- The crossed product of a cocycle of a finite Galois extension, bundled as a central simple
algebra. -/
noncomputable def crossedProductCSA (c : TwoCocycle K L) : CSA.{u, v} K :=
  CSA.of K (CrossedProduct c)

/-- The bundled algebra underlying `crossedProductCSA` is the crossed product. -/
@[simp] theorem crossedProductCSA_def (c : TwoCocycle K L) :
    crossedProductCSA c = CSA.of K (CrossedProduct c) := (rfl)

/-- The **Brauer class of a cocycle** `c` of a finite Galois extension `L/K`: the class of the
crossed product `(L, Gal(L/K), c)`. -/
noncomputable def crossedProductClass (c : TwoCocycle K L) : BrauerGroup.{u, v} K :=
  mk (crossedProductCSA c)

/-- The defining equation for `crossedProductClass`. Not a `simp` lemma: the class is the normal
form its relations are stated in, and unfolding it to a bare Brauer class would defeat them. -/
theorem crossedProductClass_def (c : TwoCocycle K L) :
    crossedProductClass c = mk (CSA.of K (CrossedProduct c)) := (rfl)

/-- **Cohomologous cocycles give Brauer-equivalent algebras.** If
`w(σ, τ) = z(σ, τ) · σ(b(τ)) · b(στ)⁻¹ · b(σ)` for some `b : Gal(L/K) → Lˣ`, then `z` and `w`
have the same Brauer class; their crossed products are even isomorphic, by
`TauCeti.CrossedProduct.nonempty_algEquiv_of_cohomologous`. -/
theorem crossedProductClass_eq_of_cohomologous {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    crossedProductClass z = crossedProductClass w :=
  let ⟨e⟩ := CrossedProduct.nonempty_algEquiv_of_cohomologous h
  mk_eq_mk_of_algEquiv (A := crossedProductCSA z) (B := crossedProductCSA w) e

end TauCeti.BrauerGroup
