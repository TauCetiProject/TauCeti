/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Integral.Map
public import TauCeti.RingTheory.Perfectoid.PreTilt.Pi

import TauCeti.Algebra.Ring.Pi

/-!
# Products of integral perfectoid rings

Let `(A i)` be an arbitrary family of commutative rings. This file shows that the product
`∏ A i` is integral perfectoid (`TauCeti.Perfectoid.IsIntegralPerfectoid`) exactly when every
factor `A i` is (Česnavičius–Scholze, *Purity for flat cohomology*, Proposition 2.1.11(d)). No
finiteness is assumed on the index type, and no factor need be nonzero: the empty product is the
zero ring, and zero factors may occur.

Each of the three defining conditions is checked coordinatewise.

* **Adic element.** For `π = (π i)`, `π ^ p ∣ p` holds in `∏ A i` exactly when it holds in every
  factor, and `∏ A i` is `π`-adically complete exactly when every `A i` is `π i`-adically
  complete (`TauCeti.isAdicComplete_pi_span_singleton_iff`), as the ideal `(π ^ n)` of a product
  consists of the families of multiples of the `π i ^ n`.
* **Frobenius.** Reduction modulo `p` commutes with products (`ModP.piEquiv`), so Frobenius on
  `(∏ A i) ⧸ p` is surjective exactly when it is on every `A i ⧸ p`.
* **Fontaine kernel.** When every factor is nonzero, `A_inf(∏ A i) ≅ ∏ A_inf(A i)` carries
  `ker θ` onto `∏ ker θ_i` (`PreTilt.map_wittVectorPiEquiv_ker_fontaineTheta`), and a product of
  ideals is principal exactly when every factor is (`Ideal.isPrincipal_pi_iff`,
  `PreTilt.isPrincipal_ker_fontaineTheta_pi_iff`).

Zero factors have no tilt in Mathlib's sense, since `p` is a unit there. They are removed first:
`∏ A i` is isomorphic to the product of its nonzero factors (`RingEquiv.piNontrivial`), and
integral perfectoidness is invariant under ring isomorphisms
(`TauCeti.Perfectoid.IsIntegralPerfectoid.of_ringEquiv`). The tilt of the product is the product
of the tilts (`PreTilt.piEquiv`).

## Main results

* `TauCeti.Perfectoid.isIntegralPerfectoid_pi_iff`: `∏ A i` is integral perfectoid if and only if
  every `A i` is.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.pi`: the corresponding instance.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_pi`: every factor of an integral perfectoid product
  is integral perfectoid.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.prod`: the product `R × S` of two integral perfectoid
  rings is integral perfectoid, as the product of the family `![ULift R, ULift S]`.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1 and Proposition 2.1.11(d).
-/

public section

open Ideal

universe u v

namespace TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]

namespace IsIntegralPerfectoid

/-- A product of integral perfectoid rings is integral perfectoid, when every factor is nonzero.
The general case reduces to this one by discarding the zero factors. -/
private theorem pi_of_nontrivial [∀ i, Nontrivial (A i)] [∀ i, IsIntegralPerfectoid p (A i)] :
    IsIntegralPerfectoid p (∀ i, A i) where
  exists_adic_element := by
    choose π hπ hc using fun i ↦ exists_adic_element (p := p) (A := A i)
    exact ⟨π, pi_dvd_iff.mpr fun i ↦ by simpa using hπ i,
      (isAdicComplete_pi_span_singleton_iff π).mpr hc⟩
  frobenius_surjective x := by
    choose z hz using fun i ↦ frobenius_surjective (p := p) (A := A i) (ModP.piEquiv p x i)
    refine ⟨(ModP.piEquiv p).symm z, (ModP.piEquiv p).injective (funext fun i ↦ ?_)⟩
    dsimp only at hz ⊢
    rw [map_pow, RingEquiv.apply_symm_apply, Pi.pow_apply, hz]
  theta_kernel_principal hp _ := by
    have : Fact ¬IsUnit (p : ∀ i, A i) := ⟨hp⟩
    have (i : ι) : Fact ¬IsUnit (p : A i) := ⟨not_isUnit_natCast⟩
    exact PreTilt.isPrincipal_ker_fontaineTheta_pi_iff.mpr fun _ ↦ isPrincipal_ker_fontaineTheta

/-- When every factor is nonzero, each factor of an integral perfectoid product is integral
perfectoid. -/
private theorem of_pi_of_nontrivial [IsIntegralPerfectoid p (∀ i, A i)] (j : ι)
    [∀ i, Nontrivial (A i)] : IsIntegralPerfectoid p (A j) where
  exists_adic_element := by
    obtain ⟨π, hπ, hc⟩ := exists_adic_element (p := p) (A := ∀ i, A i)
    exact ⟨π j, by simpa using pi_dvd_iff.mp hπ j, .of_pi_span_singleton π j⟩
  frobenius_surjective x := by
    classical
    obtain ⟨z, hz⟩ := frobenius_surjective (p := p) (A := ∀ i, A i)
      ((ModP.piEquiv p).symm (Pi.single j x))
    refine ⟨ModP.piEquiv p z j, ?_⟩
    dsimp only at hz ⊢
    rw [← Pi.pow_apply, ← map_pow, hz, RingEquiv.apply_symm_apply, Pi.single_eq_same]
  theta_kernel_principal _ _ := by
    -- every factor is `p`-adically complete, as the product is, and nonzero, so `p` is a nonunit
    have : IsAdicComplete (span {fun i ↦ (p : A i)}) (∀ i, A i) :=
      isAdicComplete_span_natCast (p := p)
    have (i : ι) : IsAdicComplete (span {(p : A i)}) (A i) :=
      .of_pi_span_singleton (fun i ↦ (p : A i)) i
    have (i : ι) : Fact ¬IsUnit (p : A i) :=
      ⟨IsAdicComplete.not_isUnit_of_mem (mem_span_singleton_self _)⟩
    have : Nonempty ι := ⟨j⟩
    exact PreTilt.isPrincipal_ker_fontaineTheta_pi_iff.mp isPrincipal_ker_fontaineTheta j

end IsIntegralPerfectoid

/-- **Products of integral perfectoid rings** (Česnavičius–Scholze, *Purity for flat cohomology*,
Proposition 2.1.11(d)). The product `∏ A i` of an arbitrary family of commutative rings is
integral perfectoid if and only if every factor `A i` is. The family may be empty, or contain zero
rings. -/
theorem isIntegralPerfectoid_pi_iff :
    IsIntegralPerfectoid p (∀ i, A i) ↔ ∀ i, IsIntegralPerfectoid p (A i) := by
  -- `∏ A i` is isomorphic to the product of its nonzero factors
  let J := {i // Nontrivial (A i)}
  have (j : J) : Nontrivial (A j) := j.property
  let e : (∀ i, A i) ≃+* ∀ j : J, A j := RingEquiv.piNontrivial A
  refine ⟨fun _ i ↦ ?_, fun h ↦ ?_⟩
  · by_cases hi : Nontrivial (A i)
    · have := IsIntegralPerfectoid.of_ringEquiv (p := p) e
      exact IsIntegralPerfectoid.of_pi_of_nontrivial (A := fun j : J ↦ A j) ⟨i, hi⟩
    · have := not_nontrivial_iff_subsingleton.mp hi
      exact .of_subsingleton p (A i)
  · have : IsIntegralPerfectoid p (∀ j : J, A j) := .pi_of_nontrivial
    exact .of_ringEquiv e.symm

namespace IsIntegralPerfectoid

/-- A product of integral perfectoid rings is integral perfectoid. -/
instance pi [∀ i, IsIntegralPerfectoid p (A i)] : IsIntegralPerfectoid p (∀ i, A i) :=
  isIntegralPerfectoid_pi_iff.mpr inferInstance

/-- Every factor of an integral perfectoid product is integral perfectoid. -/
theorem of_pi [IsIntegralPerfectoid p (∀ i, A i)] (i : ι) : IsIntegralPerfectoid p (A i) :=
  isIntegralPerfectoid_pi_iff.mp ‹_› i

/-- **Binary products.** The product `R × S` of two integral perfectoid rings is integral
perfectoid. -/
instance prod {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsIntegralPerfectoid p R]
    [IsIntegralPerfectoid p S] : IsIntegralPerfectoid p (R × S) := by
  -- `R × S` is the product of the family `![ULift R, ULift S]` indexed by `Fin 2`. The ring
  -- structures on the factors are built by `Fin.cases`, so `![..] 0` and `![..] 1` reduce by `rfl`
  -- (`Matrix.cons_val_zero`, `Matrix.cons_val_one`) to `ULift R` and `ULift S` with their usual
  -- ring structures. This definitional unfolding is what lets `RingEquiv.piFinTwo` compose with
  -- `ULift.ringEquiv.prodCongr ULift.ringEquiv` below.
  let _ : ∀ i, CommRing (![ULift.{v} R, ULift.{u} S] i) :=
    Fin.cases (inferInstanceAs (CommRing (ULift R)))
      (Fin.cases (inferInstanceAs (CommRing (ULift S))) finZeroElim)
  have : ∀ i, IsIntegralPerfectoid p (![ULift.{v} R, ULift.{u} S] i) :=
    Fin.cases (.of_ringEquiv ULift.ringEquiv.symm)
      (Fin.cases (.of_ringEquiv ULift.ringEquiv.symm) finZeroElim)
  exact .of_ringEquiv (A := ∀ i, ![ULift.{v} R, ULift.{u} S] i)
    ((RingEquiv.piFinTwo _).trans (ULift.ringEquiv.prodCongr ULift.ringEquiv))

end IsIntegralPerfectoid

end TauCeti.Perfectoid
