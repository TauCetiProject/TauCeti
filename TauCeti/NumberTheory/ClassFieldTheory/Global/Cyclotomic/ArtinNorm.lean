/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# The cyclotomic character of local Artin symbols along the norm

Let `L/K` be an extension of number fields, `p` a prime and `x ∈ Lˣ`. At every place `w` of `L`
the local Artin symbol `Art_w(x)` of the image of `x` in the completion `L_w` acts on the roots of
unity of `p`-power order through the `p`-adic cyclotomic character
`χ_p = TauCeti.abelianizedLocalCyclotomicCharacter p L_w`. This file proves that these values
are carried to `K` by the norm, place by place and then globally:

```text
∏_{w ∣ v} χ_p(Art_w(x)) = χ_p(Art_v(N_{L/K} x))      for every place v of K,
∏_w χ_p(Art_w(x))       = ∏_v χ_p(Art_v(N_{L/K} x)),
```

the second over the finite and over the infinite places separately. Since the action of a Galois
automorphism on the `m`-th roots of unity is read off from its `p`-adic cyclotomic characters
for the primes `p ∣ m`, this transfers the product formula `∏_v Art_v(a) = 1` for the local
Artin symbols on the cyclotomic extensions `K(μ_m)/K` from `N_{L/K} x` to `x`. Taking `K = ℚ`,
this reduces the product formula for the cyclotomic extensions of every number field to the one
over `ℚ`, where the local symbols are explicit; that product formula is the input from which the
sum of the local invariants of a global Brauer class is shown to vanish.

At a finite place `v` the identity is the local norm functoriality
`TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_norm` at each
`w ∣ v`, combined with the factorization `N_{L/K}(x) = ∏_{w ∣ v} N_{L_w/K_v}(x)` in `K_v`
(`TauCeti.algebraMap_norm_eq_prod_norm`); at an infinite place it is the archimedean norm
functoriality `TauCeti.ClassFieldTheory.infiniteArtinAt_norm` with the archimedean
factorization `TauCeti.GlobalNumberFields.algebraMap_norm_eq_prod_norm_infiniteCompletion`.
The global finite identity regroups the places of `L` by the place below. This needs the
finiteness of the support of `w ↦ χ_p(Art_w(x))`: at a place not above `p` where `x` is a unit,
the unramified formula `χ_p(Art_w(x)) = q_w ^ {v_w(x)}`
(`TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap`) gives `1`.

## Main results

* `TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_normUnits_eq_finprod`
  and `abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits_eq_finprod`: the value at a
  place `v` of `K` on the norm is the product of the values at the places `w ∣ v`.
* `TauCeti.ClassFieldTheory.hasFiniteMulSupport_abelianizedLocalCyclotomicCharacter_artinMap`:
  for `x ∈ Kˣ`, `χ_p(Art_v(x)) = 1` at all but finitely many finite places `v`.
* `TauCeti.ClassFieldTheory.finprod_abelianizedLocalCyclotomicCharacter_artinMap_normUnits`
  and `prod_abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits`: the products over
  all finite, respectively all infinite, places agree.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 8.4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open Function IsDedekindDomain NumberField
open _root_.ValuativeRel
open scoped AdicCompletionExtension NumberField.LiesOver

variable (p : ℕ) [Fact p.Prime]
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Place by place -/

/-- **Norm functoriality at a finite place.** For `x ∈ Lˣ` and a finite place `v` of `K`, the
`p`-adic cyclotomic character of the local Artin symbol of `N_{L/K} x` at `v` is the product of
those of the local Artin symbols of `x` at the places of `L` above `v`. -/
theorem abelianizedLocalCyclotomicCharacter_artinMap_normUnits_eq_finprod
    (v : HeightOneSpectrum (𝓞 K)) (x : Lˣ) :
    abelianizedLocalCyclotomicCharacter p (v.adicCompletion K)
        (artinMap (v.adicCompletion K)
          (Units.map (algebraMap K (v.adicCompletion K)) (Algebra.normUnits K x))) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        abelianizedLocalCyclotomicCharacter p (w.1.adicCompletion L)
          (artinMap (w.1.adicCompletion L)
            (Units.map (algebraMap L (w.1.adicCompletion L)) x)) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  -- Each factor is the character of the Artin symbol of the local norm `N_{L_w/K_v} x`.
  have h (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
      abelianizedLocalCyclotomicCharacter p (w.1.adicCompletion L)
          (artinMap (w.1.adicCompletion L) (Units.map (algebraMap L (w.1.adicCompletion L)) x)) =
        abelianizedLocalCyclotomicCharacter p (v.adicCompletion K)
          (artinMap (v.adicCompletion K) (Algebra.normUnits (v.adicCompletion K)
            (Units.map (algebraMap L (w.1.adicCompletion L) : L →* w.1.adicCompletion L) x))) := by
    have := w.2
    exact abelianizedLocalCyclotomicCharacter_artinMap_norm (v.adicCompletion K) p _
  rw [finprod_eq_prod_of_fintype]
  simp only [h, ← map_prod]
  congr 2
  refine Units.ext ?_
  simp only [Units.coe_prod, Algebra.coe_normUnits, Units.coe_map, MonoidHom.coe_ofClass]
  exact algebraMap_norm_eq_prod_norm L v (x : L)

/-- **Norm functoriality at an infinite place.** For `x ∈ Lˣ` and an infinite place `v` of `K`,
the `p`-adic cyclotomic character of the archimedean Artin symbol of `N_{L/K} x` at `v` is the
product of those of the archimedean Artin symbols of `x` at the places of `L` above `v`. -/
theorem abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits_eq_finprod
    (v : InfinitePlace K) (x : Lˣ) :
    abelianizedLocalCyclotomicCharacter p v.Completion
        (infiniteArtinAt v (Units.map (algebraMap K v.Completion) (Algebra.normUnits K x))) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        abelianizedLocalCyclotomicCharacter p w.1.Completion
          (infiniteArtinAt w.1 (Units.map (algebraMap L w.1.Completion) x)) := by
  classical
  -- Each factor is the character of the Artin symbol of the local norm `N_{L_w/K_v} x`.
  have h (w : {w : InfinitePlace L // w.LiesOver v}) :
      abelianizedLocalCyclotomicCharacter p w.1.Completion
          (infiniteArtinAt w.1 (Units.map (algebraMap L w.1.Completion) x)) =
        abelianizedLocalCyclotomicCharacter p v.Completion
          (infiniteArtinAt v (Units.map (Algebra.norm v.Completion)
            (Units.map (algebraMap L w.1.Completion : L →* w.1.Completion) x))) := by
    have := w.2
    have : CharZero v.Completion :=
      charZero_of_injective_algebraMap (algebraMap K v.Completion).injective
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective
      (infiniteArtinAt w.1 (Units.map (algebraMap L w.1.Completion) x))
    let iota : w.1.Completion →ₐ[v.Completion] SeparableClosure v.Completion := IsSepClosed.lift
    rw [← hτ, ← infiniteArtinAt_norm w.1 v iota _ τ hτ, abelianizedLocalCyclotomicCharacter_mk,
      abelianizedLocalCyclotomicCharacter_mk, localCyclotomicCharacter_absoluteGaloisGroupExtend]
  rw [finprod_eq_prod_of_fintype]
  simp only [h, ← map_prod]
  congr 2
  refine Units.ext ?_
  simp only [Units.coe_prod, Algebra.coe_normUnits, Units.coe_map, MonoidHom.coe_ofClass]
  exact GlobalNumberFields.algebraMap_norm_eq_prod_norm_infiniteCompletion L v (x : L)

/-! ### Over all places -/

/-- For `x ∈ Kˣ`, the `p`-adic cyclotomic character of the local Artin symbol of `x` is `1` at
all but finitely many finite places of `K`: at a place not above `p` where `x` is a unit, it is
`q ^ v(x) = 1` for the residue cardinality `q`. -/
theorem hasFiniteMulSupport_abelianizedLocalCyclotomicCharacter_artinMap (x : Kˣ) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      abelianizedLocalCyclotomicCharacter p (v.adicCompletion K)
        (artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) x)) := by
  have hp := (Fact.out : p.Prime)
  refine ((HeightOneSpectrum.finite_setOfPred_valuation_ne_one x.ne_zero).union
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one
      (Nat.cast_ne_zero.2 hp.ne_zero : (p : K) ≠ 0))).subset fun v hv ↦ ?_
  by_contra hvS
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hvS
  refine hv ?_
  dsimp only
  have hval (k : K) : Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  -- `p` is a unit of `𝒪[K_v]`, so it is prime to the residue cardinality `q` of `K_v`.
  have hpunit : IsUnit (p : 𝒪[v.adicCompletion K]) := by
    rw [v.isUnit_natCast_integer_adicCompletion_iff, ← HeightOneSpectrum.intValuation_eq_one_iff,
      ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    exact_mod_cast hvS.2
  have hcop : p.Coprime (Nat.card 𝓀[v.adicCompletion K]) := by
    let _ := Fintype.ofFinite 𝓀[v.adicCompletion K]
    obtain ⟨n, hℓ, hcard⟩ :=
      FiniteField.card 𝓀[v.adicCompletion K] (ringChar 𝓀[v.adicCompletion K])
    rw [Nat.card_eq_fintype_card, hcard]
    refine Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hℓ).2 fun hpℓ ↦ ?_)
    have h0 : (p : 𝓀[v.adicCompletion K]) = 0 := hpℓ ▸ ringChar.Nat.cast_ringChar
    rw [← map_natCast (IsLocalRing.residue 𝒪[v.adicCompletion K]),
      IsLocalRing.residue_eq_zero_iff] at h0
    exact h0 hpunit
  have hq : IsUnit (Nat.card 𝓀[v.adicCompletion K] : ℤ_[p]) :=
    PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
  -- By the unramified formula the character is `q ^ v(x)`, and `v(x) = 0`.
  have hx : normalizedValuation (v.adicCompletion K)
      (Units.map (algebraMap K (v.adicCompletion K)) x) = 1 := by
    rw [← WithZero.coe_inj, ← normalizedValuationWithZero_coe, WithZero.coe_one,
      HeightOneSpectrum.normalizedValuationWithZero_adicCompletion, Units.coe_map,
      MonoidHom.coe_ofClass, hval, hvS.1, inv_one]
  rw [abelianizedLocalCyclotomicCharacter_artinMap (v.adicCompletion K) (u := hq.unit) rfl, hx,
    toAdd_one, zpow_zero]

/-- **Norm functoriality over the finite places.** For `x ∈ Lˣ`, the product over the finite
places `v` of `K` of the `p`-adic cyclotomic characters of the local Artin symbols of
`N_{L/K} x` is the corresponding product for `x` over the finite places of `L`. -/
theorem finprod_abelianizedLocalCyclotomicCharacter_artinMap_normUnits (x : Lˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), abelianizedLocalCyclotomicCharacter p (v.adicCompletion K)
        (artinMap (v.adicCompletion K)
          (Units.map (algebraMap K (v.adicCompletion K)) (Algebra.normUnits K x))) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 L), abelianizedLocalCyclotomicCharacter p (w.adicCompletion L)
        (artinMap (w.adicCompletion L) (Units.map (algebraMap L (w.adicCompletion L)) x)) := by
  rw [← TauCeti.finprod_fiberwise (HeightOneSpectrum.under (𝓞 K)) _
    (hasFiniteMulSupport_abelianizedLocalCyclotomicCharacter_artinMap p x)]
  refine finprod_congr fun v ↦ ?_
  rw [abelianizedLocalCyclotomicCharacter_artinMap_normUnits_eq_finprod]
  let e : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} ≃
      {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Equiv.subtypeEquivRight fun w ↦
      ⟨fun hw ↦ hw ▸ inferInstance,
        fun hw ↦ HeightOneSpectrum.asIdeal_injective hw.over.symm⟩
  exact (finprod_comp_equiv e).symm

/-- **Norm functoriality over the infinite places.** For `x ∈ Lˣ`, the product over the infinite
places `v` of `K` of the `p`-adic cyclotomic characters of the archimedean Artin symbols of
`N_{L/K} x` is the corresponding product for `x` over the infinite places of `L`. -/
theorem prod_abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits (x : Lˣ) :
    ∏ v : InfinitePlace K, abelianizedLocalCyclotomicCharacter p v.Completion
        (infiniteArtinAt v (Units.map (algebraMap K v.Completion) (Algebra.normUnits K x))) =
      ∏ w : InfinitePlace L, abelianizedLocalCyclotomicCharacter p w.Completion
        (infiniteArtinAt w (Units.map (algebraMap L w.Completion) x)) := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L ↦ w.comap (algebraMap K L))]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits_eq_finprod,
    ← finprod_eq_prod_of_fintype]
  refine (finprod_comp_equiv (Equiv.subtypeEquivRight fun w ↦
    ⟨fun hw ↦ hw ▸ inferInstance, fun _ ↦ InfinitePlace.LiesOver.comap_eq w v⟩ :
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
        {w : InfinitePlace L // w.LiesOver v})).symm.trans (finprod_congr fun ⟨w, hw⟩ ↦ ?_)
  -- The equivalence does not move the underlying place.
  dsimp only [Equiv.subtypeEquivRight_apply]
  rfl

end TauCeti.ClassFieldTheory
