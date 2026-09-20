/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Ideal.Away
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Finite ideles and ideals away from a finite set

The finite-idele valuation `adicOrd` records the multiplicity of every finite place in the
fractional ideal attached to a finite idele.  This file makes that dictionary available at the
prime-to carriers used by ray classes: vanishing of the orders on a finite set is exactly
membership in `NumberFieldArithmetic.idealsAway`, and every nonzero integral ideal prime to that
set is realized by a finite idele with the corresponding orders.

The latter realization is the finite-idele form of the integral prime-to monoid.  It lets later
adelic constructions move between local valuations and the single ideal carrier used by the ray
class API, without introducing a second notion of an ideal prime to a modulus.

## Main results

* `TauCeti.GlobalNumberFields.toFractionalIdeal_mem_idealsAway_iff` identifies the
  prime-to condition with vanishing finite-idele orders.
* `TauCeti.GlobalNumberFields.exists_toFractionalIdeal_eq_integralIdealsAwayHom` realizes
  every integral ideal away from a finite set by a finite idele.
* `TauCeti.GlobalNumberFields.exists_adicOrd_eq_count_integralIdealsAway` gives the
  resulting order/count comparison at every finite place.
* `TauCeti.GlobalNumberFields.toIdealsAway` is the resulting homomorphism on the
  finite-idèle subgroup, with `mem_ker_toIdealsAway_iff` identifying its kernel.

The construction uses the standard idelic description of ideals away from a finite set; no
formalization is vendored here.  The ideal carriers and their factorization API are supplied by
`TauCeti.NumberFieldArithmetic`, while the finite-idele factorization is supplied by
`IsDedekindDomain.FiniteAdeleRing.ClassGroup`.
-/

public section

open IsDedekindDomain HeightOneSpectrum
open IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem count_toFractionalIdeal_eq_adicOrd (x : 𝔸ᶠ[(𝓞 K), K]ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (toFractionalIdeal x : FractionalIdeal (𝓞 K)⁰ K) = adicOrd x v :=
  count_coe_toFractionalIdeal x v

/-- A finite idele defines an ideal away from `S` exactly when its orders vanish on `S`. -/
theorem toFractionalIdeal_mem_idealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    toFractionalIdeal x ∈ NumberFieldArithmetic.idealsAway (K := K) S ↔
      ∀ v ∈ S, adicOrd x v = 0 := by
  rw [NumberFieldArithmetic.mem_idealsAway_iff]
  simp only [count_toFractionalIdeal_eq_adicOrd]

/-- The finite ideles whose orders vanish on `S`, viewed as a subgroup. -/
noncomputable def adicOrdAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (𝔸ᶠ[(𝓞 K), K]ˣ) :=
  (NumberFieldArithmetic.idealsAway (K := K) S).comap
    (toFractionalIdeal (R := 𝓞 K) (K := K))

@[simp]
theorem mem_adicOrdAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    x ∈ adicOrdAway S ↔ ∀ v ∈ S, adicOrd x v = 0 := by
  rw [adicOrdAway, Subgroup.mem_comap, toFractionalIdeal_mem_idealsAway_iff]

/-- The ideal away from `S` attached to a finite idele whose orders vanish on `S`. -/
noncomputable def toIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    adicOrdAway S →* NumberFieldArithmetic.idealsAway (K := K) S :=
  MonoidHom.codRestrict
    ((toFractionalIdeal (R := 𝓞 K) (K := K)).comp (adicOrdAway S).subtype) _
    fun x ↦ x.property

@[simp]
theorem toIdealsAway_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) :
    (toIdealsAway S x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toFractionalIdeal (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :=
  by
    -- Unfold the restricted homomorphism to expose its underlying finite idele.
    change toFractionalIdeal ((adicOrdAway S).subtype x) =
      toFractionalIdeal (x : 𝔸ᶠ[(𝓞 K), K]ˣ)
    rfl

/-- The kernel of `toIdealsAway` consists of finite ideles with trivial fractional ideal. -/
theorem mem_ker_toIdealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) :
    x ∈ (toIdealsAway S).ker ↔ (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralUnits (𝓞 K) K := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    rw [← ker_toFractionalIdeal, MonoidHom.mem_ker]
    have h' := congrArg (fun y : NumberFieldArithmetic.idealsAway (K := K) S =>
      (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) h
    simpa [toIdealsAway_apply] using h'
  · intro h
    have hxker : (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈
        (toFractionalIdeal (R := 𝓞 K) (K := K)).ker := by
      rw [ker_toFractionalIdeal]
      exact h
    have h' : toFractionalIdeal (x : 𝔸ᶠ[(𝓞 K), K]ˣ) = 1 :=
      MonoidHom.mem_ker.mp hxker
    apply Subtype.ext
    simpa [toIdealsAway_apply] using h'

/-- Every nonzero integral ideal away from `S` is the fractional ideal of a finite idele. -/
theorem exists_toFractionalIdeal_eq_integralIdealsAwayHom
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : NumberFieldArithmetic.integralIdealsAway (K := K) S) :
    ∃ x : 𝔸ᶠ[(𝓞 K), K]ˣ,
      toFractionalIdeal x = NumberFieldArithmetic.integralIdealsAwayHom S I := by
  exact toFractionalIdeal_surjective (K := K)
    (NumberFieldArithmetic.integralIdealsAwayHom S I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The finite-idele orders of a representative of an integral ideal are its ideal multiplicities.

In particular, these orders are nonnegative everywhere and vanish on the excluded finite set. -/
theorem exists_adicOrd_eq_count_integralIdealsAway
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : NumberFieldArithmetic.integralIdealsAway (K := K) S) :
    ∃ x : 𝔸ᶠ[(𝓞 K), K]ˣ,
      ∀ v : HeightOneSpectrum (𝓞 K),
        adicOrd x v = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨x, hx⟩ := exists_toFractionalIdeal_eq_integralIdealsAwayHom S I
  refine ⟨x, fun v ↦ ?_⟩
  rw [← count_toFractionalIdeal_eq_adicOrd x v, hx]
  exact congrArg (FractionalIdeal.count K v) (NumberFieldArithmetic.coe_integralIdealsAwayHom S I)

end TauCeti.GlobalNumberFields
