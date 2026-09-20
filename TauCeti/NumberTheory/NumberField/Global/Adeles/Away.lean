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
* `TauCeti.GlobalNumberFields.toIdealsAway_surjective` realizes every fractional ideal away from
  a finite set by a finite idele whose orders vanish on that set.
* `TauCeti.GlobalNumberFields.exists_forall_adicOrd_eq_count_integralIdealsAway` gives the
  resulting order/count comparison at every finite place.
* `TauCeti.GlobalNumberFields.toIdealsAway` is the resulting homomorphism on the
  finite-idèle subgroup, with `mem_ker_toIdealsAway_iff` identifying its kernel.

The construction uses the standard idelic description of ideals away from a finite set.  The ideal
carriers and their factorization API are supplied by `TauCeti.NumberFieldArithmetic`, while the
finite-idele factorization is supplied by `IsDedekindDomain.FiniteAdeleRing.ClassGroup`.
-/

public section

open IsDedekindDomain HeightOneSpectrum
open IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- A finite idele defines an ideal away from `S` exactly when its orders vanish on `S`. -/
@[simp]
theorem toFractionalIdeal_mem_idealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : 𝔸ᶠ[(𝓞 K), K]ˣ) :
    toFractionalIdeal x ∈ NumberFieldArithmetic.idealsAway (K := K) S ↔
      ∀ v ∈ S, adicOrd x v = 0 := by
  rw [NumberFieldArithmetic.mem_idealsAway_iff]
  simp only [count_coe_toFractionalIdeal]

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
@[simp]
theorem mem_ker_toIdealsAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : adicOrdAway S) :
    x ∈ (toIdealsAway S).ker ↔ (x : 𝔸ᶠ[(𝓞 K), K]ˣ) ∈ integralUnits (𝓞 K) K := by
  have hker : (toIdealsAway S).ker =
      ((toFractionalIdeal (R := 𝓞 K) (K := K)).comp (adicOrdAway S).subtype).ker := by
    exact MonoidHom.ker_codRestrict _ _ _
  rw [hker, ← MonoidHom.comap_ker, ker_toFractionalIdeal, Subgroup.mem_comap]
  simp only [Subgroup.subtype_apply]

/-- The homomorphism from finite ideles with orders vanishing on `S` to ideals away from `S` is
surjective. -/
theorem toIdealsAway_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (toIdealsAway S) := by
  intro I
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  have hx_mem : x ∈ adicOrdAway S := by
    rw [adicOrdAway, Subgroup.mem_comap, hx]
    exact I.property
  refine ⟨⟨x, hx_mem⟩, ?_⟩
  exact Subtype.ext hx

/-- The finite-idele orders of a representative of an integral ideal are its ideal multiplicities.

In particular, these orders are nonnegative everywhere and vanish on the excluded finite set. -/
theorem exists_forall_adicOrd_eq_count_integralIdealsAway
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : NumberFieldArithmetic.integralIdealsAway (K := K) S) :
    ∃ x : 𝔸ᶠ[(𝓞 K), K]ˣ,
      ∀ v : HeightOneSpectrum (𝓞 K),
        adicOrd x v = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨x, hx⟩ := toIdealsAway_surjective S
    (NumberFieldArithmetic.integralIdealsAwayHom S I)
  refine ⟨x, fun v ↦ ?_⟩
  rw [← count_coe_toFractionalIdeal (x : 𝔸ᶠ[(𝓞 K), K]ˣ) v,
    ← toIdealsAway_apply S x, hx]
  exact congrArg (FractionalIdeal.count K v) (NumberFieldArithmetic.coe_integralIdealsAwayHom S I)

end TauCeti.GlobalNumberFields
