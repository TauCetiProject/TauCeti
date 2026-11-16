/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Lemmas
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.ArchimedeanValue
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue

import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
import TauCeti.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Hecke's finite and residue characters for a presentation

Let `χ` be a presentation at a modulus `𝔪` of an algebraic Hecke character of a number field `K`,
with unitary weight `χ_u`, ideal-side shift `σ`, and full archimedean value `χ_∞`
(`Grossencharacter.archimedeanValue`). In Neukirch's decomposition `χ((a)) = χ_f(a) χ_∞(a)` on
principal ideals (VII §6, (6.1)), Hecke's finite character on algebraic integers is defined from
the primary object by `χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)` (`Grossencharacter.finiteCharacter`).

Because principal ideles are trivial for `χ.toHeckeCharacter`, on any integer `a` prime to `𝔪`
this equals the inverse product of the local finite components of `χ.toHeckeCharacter` at the
primes dividing `𝔪` (`finiteCharacter_eq_prod_finiteComponent_inv`). Consequently `χ_f` is
multiplicative on `𝓞 K`, vanishes precisely when `(a)` is not coprime to `𝔪`, takes values of
norm `1` on integers prime to `𝔪`, equals `χ_∞(u)` on every global unit `u : (𝓞 K)ˣ`
(`finiteCharacter_unit`), and on nonzero integers depends only on the residue class modulo
`𝔪.finitePart` (`finiteCharacter_residue`).

Descending the local finite-component product along the surjection
`primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ` yields the unique multiplicative character
`χ.residueCharacter : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ` agreeing with `χ.finiteCharacter` on
every nonzero algebraic integer (`existsUnique_residueCharacter`). Keeping `finiteCharacter` and
`residueCharacter` separate is essential at trivial finite modulus `𝔪.finitePart = ⊤`: the
residue ring has one element, which is a unit where `residueCharacter` takes the value `1`,
whereas `finiteCharacter 0 = 0` since `(0)` is not coprime to `𝔪`. Moreover, `χ.residueCharacter`
detects the exact finite conductor of `χ.toHeckeCharacter`: an ideal `I ∣ 𝔪.finitePart` is
divisible by `χ.toHeckeCharacter.finiteConductor` if and only if `χ.residueCharacter` is trivial
on the units congruent to `1` modulo `I` (`finiteConductor_dvd_iff_residueCharacter_eq_one`).

Finally, `χ.finiteCharacter` extends uniquely to a function `χ.finiteCharacterK : Kˣ → ℂ`
multiplicative on `primeToSubgroup 𝔪` and vanishing outside it (`existsUnique_finiteCharacterK`),
with zero-extension `χ.finiteCharacterK' : K → ℂ` for evaluation on fractional ideals.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: Hecke's finite character `χ_f` on
  `𝓞 K`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: Hecke's residue character on
  `𝓞 K ⧸ 𝔪.finitePart` as a `MulChar`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacterK'`: the multiplicative extension to
  `primeToSubgroup 𝔪`, extended by zero to `Kˣ` and `K`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_prod_finiteComponent_inv`: on integers
  prime to `𝔪`, `finiteCharacter` is the inverse product of the finite components at
  `𝔪.support`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_mul`,
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_zero_iff`, and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_unit`.
* `TauCeti.LFunctions.Grossencharacter.existsUnique_residueCharacter` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_residue`.
* `TauCeti.LFunctions.Grossencharacter.finiteConductor_dvd_iff_residueCharacter_eq_one` and
  `TauCeti.LFunctions.Grossencharacter.exists_residueCharacter_ne_one_of_finiteConductor_eq`:
  characterization of divisibility by the finite conductor and primitivity at the conductor.
* `TauCeti.LFunctions.Grossencharacter.existsUnique_finiteCharacterK`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
open NumberField NumberField.InfinitePlace.Completion
open scoped NumberField nonZeroDivisors

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-! ### Hecke's finite character on algebraic integers -/

/-- **Hecke's finite character on algebraic integers**, derived from the primary object:
`χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)`, where `χ_∞` is the full archimedean value
(`archimedeanValue`). It is multiplicative on `𝓞 K`, vanishes off the elements generating ideals
coprime to `𝔪`, equals `χ_∞(u)` on global units `u : (𝓞 K)ˣ`, and on nonzero integers depends
only on the residue class modulo `𝔪.finitePart` (`finiteCharacter_residue`).

Note that `finiteCharacter χ 0 = 0`, whereas at trivial finite modulus `𝔪.finitePart = ⊤` the
residue character `residueCharacter χ` evaluates to `1` on the unique class `0`. -/
def finiteCharacter (χ : Grossencharacter K 𝔪) (a : 𝓞 K) : ℂ :=
  χ.unitaryWeight.1 (Ideal.span {a}) *
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
    χ.archimedeanValue (algebraMap (𝓞 K) K a)

/-- The defining equation of Hecke's finite character on integers. -/
theorem finiteCharacter_def (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacter a =
      χ.unitaryWeight.1 (Ideal.span {a}) *
        ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
        χ.archimedeanValue (algebraMap (𝓞 K) K a) :=
  (rfl)

/-- Hecke's finite character vanishes at `0`. -/
@[simp]
theorem finiteCharacter_zero (χ : Grossencharacter K 𝔪) : χ.finiteCharacter 0 = 0 := by
  simp [finiteCharacter]

/-- Hecke's finite character takes the value `1` at `1`. -/
@[simp]
theorem finiteCharacter_one (χ : Grossencharacter K 𝔪) : χ.finiteCharacter 1 = 1 := by
  simp [finiteCharacter, Ideal.span_singleton_one, Ideal.absNorm_top]

/-- Hecke's finite character vanishes at every integer whose principal ideal is not coprime to
`𝔪`. -/
theorem finiteCharacter_eq_zero_of_not_isCoprimeTo (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (ha : ¬ 𝔪.IsCoprimeTo (Ideal.span {a})) : χ.finiteCharacter a = 0 := by
  simp [finiteCharacter, χ.unitaryWeight_eq_zero _ ha]

/-- `compatibility`, restated: Hecke's finite character is `1` on integers congruent to `1`
modulo `𝔪`. -/
theorem finiteCharacter_eq_one_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : IsCongrOne 𝔪 x) {a : 𝓞 K} (ha : algebraMap (𝓞 K) K a = x) :
    χ.finiteCharacter a = 1 := by
  rw [finiteCharacter, ha, χ.archimedeanValue_eq_of_isCongrOne hx]
  exact χ.compatibility x hx a ha

/-- On a global unit `u : (𝓞 K)ˣ`, Hecke's finite character is the full archimedean value
`χ_∞(u)` (Neukirch's `χ_f(ε) χ_∞(ε)⁻¹ = 1` in the idelic sign convention). -/
theorem finiteCharacter_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    χ.finiteCharacter u = χ.archimedeanValue (algebraMap (𝓞 K) K u) := by
  have hspan : Ideal.span {(u : 𝓞 K)} = ⊤ := Ideal.span_singleton_eq_top.mpr u.isUnit
  simp [finiteCharacter, hspan, Ideal.absNorm_top]

/-- Membership of a global unit `x : Kˣ` in the `k`-th local unit filtration at `v` expressed
directly in terms of the global `v`-adic valuation on `K`. -/
private theorem unitsMap_algebraMap_mem_unitFiltration_iff (v : HeightOneSpectrum (𝓞 K))
    (k : ℕ) (x : Kˣ) :
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x ∈
        TauCeti.unitFiltration (v.adicCompletion K) k ↔
      v.valuation K (x : K) = 1 ∧ v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub]
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation']

/-- Shrinking a product of local finite components along `S ⊆ T` when `ψ` is unramified outside
`S` and `x` is a local unit at all primes of `T`. -/
private theorem prod_finiteComponent_subset (ψ : HeckeCharacter K)
    {S T : Finset (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (hzero : ∀ v ∈ T, v ∉ S → ψ.conductorExponent v = 0)
    {x : Kˣ} (hx : ∀ v ∈ T, v.valuation K (x : K) = 1) :
    (∏ v ∈ T,
        (ψ.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ)) =
      ∏ v ∈ S,
        (ψ.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ) := by
  refine (Finset.prod_subset hST fun v hvT hvS ↦ ?_).symm
  have hmem : Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x ∈
      TauCeti.unitFiltration (v.adicCompletion K) (ψ.conductorExponent v) := by
    rw [hzero v hvT hvS]
    exact (v.unitsMap_algebraMap_mem_unitFiltration_zero_iff x).mpr (hx v hvT)
  rw [ψ.finiteComponent_eq_one_of_mem_unitFiltration hmem, Units.val_one]

/-- A nonzero integer `a` lies in `primeToSubgroup 𝔪` (viewed in `Kˣ`) if and only if the ideal
`(a)` is coprime to `𝔪`. -/
private theorem mem_primeToSubgroup_iff_isCoprimeTo_span_singleton {a : 𝓞 K} {x : Kˣ}
    (ha : algebraMap (𝓞 K) K a = x) :
    x ∈ primeToSubgroup 𝔪 ↔ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  have ha0 : a ≠ 0 := fun h ↦ x.ne_zero (by rw [← ha, h, map_zero])
  rw [mem_primeToSubgroup, Modulus.isCoprimeTo_iff]
  refine ⟨fun hx ↦ ⟨Ideal.span_singleton_eq_bot.not.mpr ha0, fun v hv hdvd ↦ ?_⟩,
    fun ⟨_, h⟩ v hv ↦ ?_⟩
  · have hlt : v.valuation K (x : K) < 1 := by
      rw [← ha]
      exact (v.valuation_lt_one_iff_mem a).mpr (Ideal.dvd_span_singleton.mp hdvd)
    exact hlt.ne (hx v ((𝔪.mem_support_iff v).mp hv))
  · rw [← ha, v.valuation_of_algebraMap]
    refine v.intValuation_eq_one_iff.mpr fun hmem ↦ ?_
    exact h v ((𝔪.mem_support_iff v).mpr hv) (Ideal.dvd_span_singleton.mpr hmem)

/-- The finite-idele coordinate of the diagonal finite idele of `x : Kˣ` at `v` is the local
image of `x` in `(v.adicCompletion K)ˣ`. -/
private theorem ideleFiniteCoord_ofFiniteIdele_unitEmbedding (v : HeightOneSpectrum (𝓞 K))
    (x : Kˣ) :
    v.ideleFiniteCoord (IdeleGroup.ofFiniteIdele (𝓞 K) K (unitEmbedding (𝓞 K) K x)) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x := by
  rw [← v.ideleFiniteCoord_unitEmbedding x]
  refine Units.ext ?_
  simp only [HeightOneSpectrum.coe_ideleFiniteCoord, ← IdeleGroup.coe_toFiniteIdele,
    IdeleGroup.toFiniteIdele_ofFiniteIdele, IdeleGroup.toFiniteIdele_unitEmbedding]

/-- Triviality of `χ.toHeckeCharacter` on the principal idele of `x : Kˣ` pairs its full
archimedean value with the evaluation on the diagonal finite idele of `x`. -/
private theorem archimedeanValue_mul_ofFiniteIdele_unitEmbedding (χ : Grossencharacter K 𝔪)
    (x : Kˣ) :
    χ.archimedeanValue (x : K) *
        (χ.toHeckeCharacter
          (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 K) K (unitEmbedding (𝓞 K) K x))) : ℂ) =
      1 := by
  have hsplit :=
    congrArg (fun z : IdeleGroup (𝓞 K) K ↦ (χ.toHeckeCharacter (QuotientGroup.mk z) : ℂ))
      (IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele (IdeleGroup.unitEmbedding (𝓞 K) K x))
  have hprincipal :
      (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K x) : IdeleClassGroup (𝓞 K) K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  rw [hprincipal, map_one, Units.val_one, QuotientGroup.mk_mul, map_mul, Units.val_mul,
    QuotientGroup.mk_prod, map_prod, Units.coe_prod,
    IdeleGroup.toFiniteIdele_unitEmbedding] at hsplit
  have hinf :
      (∏ w : InfinitePlace K,
        (χ.toHeckeCharacter (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 K) K w
          (w.ideleInfiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K x)))) : ℂ)) =
        χ.archimedeanValue (x : K) := by
    rw [χ.archimedeanValue_eq_prod_infiniteComponent x]
    simp only [HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion_apply,
      InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  rw [hinf] at hsplit
  exact hsplit

/-- **Idelic formula for Hecke's finite character.** For `a ∈ 𝓞 K` generating an ideal prime to
`𝔪`, with image `x ∈ primeToSubgroup 𝔪`, `χ.finiteCharacter a` equals the inverse product of the
local finite components of `χ.toHeckeCharacter` at the primes dividing `𝔪`. -/
theorem finiteCharacter_eq_prod_finiteComponent_inv (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    {x : Kˣ} (ha : algebraMap (𝓞 K) K a = x) (hx : x ∈ primeToSubgroup 𝔪) :
    χ.finiteCharacter a =
      (∏ v ∈ 𝔪.support,
        (χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ))⁻¹ := by
  classical
  set ψ := χ.toHeckeCharacter
  set 𝔣 : Modulus K := ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩
  have h𝔣 : 𝔣 ∣ 𝔪 :=
    Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, Finset.empty_subset _⟩
  have hcop : 𝔪.IsCoprimeTo (Ideal.span {a}) :=
    (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton ha).mp hx
  have hx𝔣 : x ∈ primeToSubgroup 𝔣 :=
    primeToSubgroup_le_of_dvd (Modulus.dvd_iff.mp h𝔣).1 hx
  have hJ : Ideal.span {a} ∈ integralIdealsPrimeTo 𝔪 :=
    Modulus.mem_integralIdealsPrimeTo.mpr hcop
  have hxideal : toPrincipalIdeal (𝓞 K) K x ∈ idealsPrimeTo 𝔣 :=
    NumberFieldArithmetic.toPrincipalIdeal_mem_idealsAway_iff.mpr hx𝔣
  have hideal : NumberFieldArithmetic.integralIdealsAwayHom K 𝔣.support
        (integralIdealsPrimeToInclusion h𝔣 ⟨Ideal.span {a}, hJ⟩) =
      ⟨toPrincipalIdeal (𝓞 K) K x, hxideal⟩ :=
    Subtype.ext (Units.ext (by
      rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, coe_integralIdealsPrimeToInclusion,
        coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, ha]))
  let y : finiteIdelesAway K 𝔣.support := ⟨unitEmbedding (𝓞 K) K x, by
    rw [mem_finiteIdelesAway_iff]
    exact (toFractionalIdeal_mem_idealsAway_iff 𝔣.support _).mp
      ((toFractionalIdeal_unitEmbedding (R := 𝓞 K) x).symm ▸ hxideal)⟩
  have hyideal : toIdealsAway K 𝔣.support y = ⟨toPrincipalIdeal (𝓞 K) K x, hxideal⟩ :=
    Subtype.ext ((coe_toIdealsAway _ _).trans (toFractionalIdeal_unitEmbedding x))
  have hfin := χ.coe_idealCharacter_integralIdealsAwayHom h𝔣 ⟨Ideal.span {a}, hJ⟩
  rw [hideal, ← hyideal, ψ.idealCharacter_apply_toIdealsAway y, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.coe_prod] at hfin
  have hprod_eq := prod_finiteComponent_subset ψ (Modulus.support_mono h𝔣)
    (fun v _ hv𝔣 ↦ not_not.mp ((ψ.dvd_finiteConductor_iff v).not.mp
      fun hdvd ↦ hv𝔣 ((𝔣.mem_support_iff v).mpr hdvd)))
    (fun v hv𝔪 ↦ mem_primeToSubgroup.mp hx v ((𝔪.mem_support_iff v).mp hv𝔪))
  rw [finiteCharacter, ha, ← hfin, hprod_eq]
  simp only [y, ideleFiniteCoord_ofFiniteIdele_unitEmbedding]
  set P : ℂ := ∏ v ∈ 𝔣.support,
    (ψ.finiteComponent v (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ)
  set F : ℂ :=
    (ψ (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 K) K (unitEmbedding (𝓞 K) K x))) : ℂ)
  have hsplit : χ.archimedeanValue (x : K) * F = 1 :=
    χ.archimedeanValue_mul_ofFiniteIdele_unitEmbedding x
  calc
    F * P⁻¹ * χ.archimedeanValue (x : K) = (χ.archimedeanValue (x : K) * F) * P⁻¹ := by ring
    _ = P⁻¹ := by rw [hsplit, one_mul]

/-- Hecke's finite character vanishes at `a` if and only if `(a)` is not coprime to `𝔪`. -/
theorem finiteCharacter_eq_zero_iff (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacter a = 0 ↔ ¬ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  refine ⟨fun h0 hcop ↦ ?_, χ.finiteCharacter_eq_zero_of_not_isCoprimeTo⟩
  have ha0 : a ≠ 0 := fun h ↦
    (Modulus.isCoprimeTo_iff.mp hcop).1 (by rw [h, Ideal.span_singleton_zero])
  have hx0 : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  let x : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hx0
  have hx : x ∈ primeToSubgroup 𝔪 :=
    (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton (Units.val_mk0 hx0).symm).mpr hcop
  rw [χ.finiteCharacter_eq_prod_finiteComponent_inv (Units.val_mk0 hx0).symm hx] at h0
  exact inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ ↦ Units.ne_zero _) h0

/-- Hecke's finite character is nonzero at `a` if and only if `(a)` is coprime to `𝔪`. -/
theorem finiteCharacter_ne_zero_iff (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacter a ≠ 0 ↔ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  rw [ne_eq, χ.finiteCharacter_eq_zero_iff, not_not]

/-! ### Hecke's residue character -/

/-- The local finite-component product `x ↦ (∏_{v ∣ 𝔪} χ_v(x))⁻¹` as a unit-valued
homomorphism on `primeToSubgroup 𝔪`. -/
private def localFiniteProductHom (χ : Grossencharacter K 𝔪) :
    primeToSubgroup 𝔪 →* ℂˣ :=
  (∏ v ∈ 𝔪.support,
    (χ.toHeckeCharacter.finiteComponent v).toMonoidHom.comp
      ((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom).comp
        (primeToSubgroup 𝔪).subtype))⁻¹

private theorem localFiniteProductHom_apply (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) :
    χ.localFiniteProductHom x =
      (∏ v ∈ 𝔪.support,
        χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)))⁻¹ := by
  simp [localFiniteProductHom]

/-- Elements of `primeToSubgroup 𝔪` reducing to `1` modulo `𝔪.finitePart` lie in the kernel of
`localFiniteProductHom`, with no sign condition at the real places. -/
private theorem ker_residueHom_le_localFiniteProductHom (χ : Grossencharacter K 𝔪) :
    (residueHom 𝔪).ker ≤ χ.localFiniteProductHom.ker := by
  intro x hx
  rw [MonoidHom.mem_ker, localFiniteProductHom_apply, inv_eq_one]
  have hres : residue 𝔪 x = 1 := by
    simpa only [MonoidHom.mem_ker, Units.ext_iff, coe_residueHom, Units.val_one] using hx
  have hval := (residue_eq_one_iff x).mp hres
  refine Finset.prod_eq_one fun v hv ↦ ?_
  have hdvd : v.asIdeal ∣ 𝔪.finitePart := (𝔪.mem_support_iff v).mp hv
  refine χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
    (TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent v) ?_)
  exact (unitsMap_algebraMap_mem_unitFiltration_iff v (𝔪.exponent v) (x : Kˣ)).mpr
    ⟨mem_primeToSubgroup.mp x.2 v hdvd, hval v hdvd⟩

/-- The unit homomorphism `(𝓞 K ⧸ 𝔪.finitePart)ˣ →* ℂˣ` induced by `localFiniteProductHom`
via surjectivity of `residueHom 𝔪`. -/
private def residueUnitHom (χ : Grossencharacter K 𝔪) :
    (𝓞 K ⧸ 𝔪.finitePart)ˣ →* ℂˣ :=
  (residueHom 𝔪).liftOfSurjective (residueHom_surjective 𝔪)
    ⟨χ.localFiniteProductHom, χ.ker_residueHom_le_localFiniteProductHom⟩

private theorem residueUnitHom_residueHom (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) :
    χ.residueUnitHom (residueHom 𝔪 x) = χ.localFiniteProductHom x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

private theorem residueUnitHom_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueUnitHom = χ.residueUnitHom⁻¹ := by
  refine MonoidHom.ext fun u ↦ ?_
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔪 u
  rw [residueUnitHom_residueHom, MonoidHom.inv_apply, residueUnitHom_residueHom,
    localFiniteProductHom_apply, localFiniteProductHom_apply, inv_inv, toHeckeCharacter_inverse,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [HeckeCharacter.finiteComponent_inv,
    ← zpow_neg_one (χ.toHeckeCharacter.finiteComponent v),
    ContinuousMonoidHom.zpow_apply, zpow_neg_one, inv_inv]

/-- **Hecke's residue character** on `𝓞 K ⧸ 𝔪.finitePart` (Neukirch VII (6.1)), as a Mathlib
`MulChar`: multiplicative, `1` at `1`, `0` off the units, and agreeing with `χ.finiteCharacter`
on every nonzero algebraic integer (`residueCharacter_mk`, `existsUnique_residueCharacter`). -/
def residueCharacter (χ : Grossencharacter K 𝔪) : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ :=
  MulChar.ofUnitHom χ.residueUnitHom

/-- On the reduction of any element of `primeToSubgroup 𝔪`, `residueCharacter` evaluates the
inverse product of the local finite components at `𝔪.support`. -/
theorem residueCharacter_residue (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.residueCharacter (residue 𝔪 x) =
      (∏ v ∈ 𝔪.support,
        (χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)) : ℂ))⁻¹ := by
  rw [← coe_residueHom, residueCharacter, MulChar.ofUnitHom_coe, residueUnitHom_residueHom,
    localFiniteProductHom_apply, Units.val_inv_eq_inv_val, Units.coe_prod]

/-- A nonzero integer `a` maps to a unit of `𝓞 K ⧸ 𝔪.finitePart` if and only if `(a)` is
coprime to `𝔪`. -/
private theorem isUnit_mk_iff_isCoprimeTo_span_singleton {a : 𝓞 K} (ha : a ≠ 0) :
    IsUnit (Ideal.Quotient.mk 𝔪.finitePart a) ↔ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  rw [Ideal.Quotient.isUnit_mk_iff, Modulus.isCoprimeTo_iff_sup_eq_top,
    and_iff_right (Ideal.span_singleton_eq_bot.not.mpr ha)]

/-- On every nonzero integer `a`, the residue character agrees with `finiteCharacter`. -/
theorem residueCharacter_mk (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0) :
    χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  by_cases hcop : 𝔪.IsCoprimeTo (Ideal.span {a})
  · have hx0 : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
    let x : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hx0
    have hx : x ∈ primeToSubgroup 𝔪 :=
      (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton (Units.val_mk0 hx0).symm).mpr hcop
    have hres : residue 𝔪 ⟨x, hx⟩ = Ideal.Quotient.mk 𝔪.finitePart a :=
      residue_eq (a := a) (b := 1) ⟨x, hx⟩ (by simp) (by simp [x])
    rw [← hres, χ.residueCharacter_residue ⟨x, hx⟩,
      χ.finiteCharacter_eq_prod_finiteComponent_inv (Units.val_mk0 hx0).symm hx]
  · have hnu : ¬ IsUnit (Ideal.Quotient.mk 𝔪.finitePart a) :=
      (isUnit_mk_iff_isCoprimeTo_span_singleton ha).not.mpr hcop
    rw [MulChar.map_nonunit _ hnu, χ.finiteCharacter_eq_zero_of_not_isCoprimeTo hcop]

/-- **Existence and uniqueness of Hecke's residue character.** There is a unique multiplicative
character of `𝓞 K ⧸ 𝔪.finitePart` agreeing with `χ.finiteCharacter` on every nonzero element
of `𝓞 K`. Uniqueness holds because `𝔪.finitePart ≠ ⊥`, so every residue class has a nonzero
representative. -/
theorem existsUnique_residueCharacter (χ : Grossencharacter K 𝔪) :
    ∃! ρ : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ,
      ∀ a : 𝓞 K, a ≠ 0 →
        ρ (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  refine ⟨χ.residueCharacter, fun a ha ↦ χ.residueCharacter_mk ha, fun ρ hρ ↦ ?_⟩
  ext u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ 𝔪.finitePart)
  rw [← ha]
  by_cases ha0 : a = 0
  · subst ha0
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔪.finitePart_ne_bot
    have hmk : Ideal.Quotient.mk 𝔪.finitePart (0 : 𝓞 K) =
        Ideal.Quotient.mk 𝔪.finitePart m := by
      rw [map_zero, (Ideal.Quotient.eq_zero_iff_mem.mpr hm).symm]
    rw [hmk, hρ m hm0, χ.residueCharacter_mk hm0]
  · rw [hρ a ha0, χ.residueCharacter_mk ha0]

/-- **On nonzero integers, Hecke's finite character depends only on the residue class modulo
`𝔪.finitePart`**, with no sign condition at the real places. -/
theorem finiteCharacter_residue (χ : Grossencharacter K 𝔪) {a b : 𝓞 K} (ha : a ≠ 0)
    (hb : b ≠ 0)
    (h : Ideal.Quotient.mk 𝔪.finitePart a = Ideal.Quotient.mk 𝔪.finitePart b) :
    χ.finiteCharacter a = χ.finiteCharacter b := by
  rw [← χ.residueCharacter_mk ha, ← χ.residueCharacter_mk hb, h]

/-- Hecke's finite character is completely multiplicative on `𝓞 K`. -/
theorem finiteCharacter_mul (χ : Grossencharacter K 𝔪) (a b : 𝓞 K) :
    χ.finiteCharacter (a * b) = χ.finiteCharacter a * χ.finiteCharacter b := by
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · simp [hb]
    · rw [← χ.residueCharacter_mk (mul_ne_zero ha hb), map_mul, map_mul,
        χ.residueCharacter_mk ha, χ.residueCharacter_mk hb]

/-- Hecke's finite character respects natural-number powers on `𝓞 K`. -/
theorem finiteCharacter_pow (χ : Grossencharacter K 𝔪) (a : 𝓞 K) (n : ℕ) :
    χ.finiteCharacter (a ^ n) = χ.finiteCharacter a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, χ.finiteCharacter_mul, ih]

/-- The residue character of the inverse presentation is the inverse character. -/
theorem residueCharacter_inverse_eq_inv (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueCharacter = χ.residueCharacter⁻¹ := by
  rw [residueCharacter, residueCharacter, χ.residueUnitHom_inverse, MulChar.ofUnitHom_inv]

/-- Inversion conjugates the residue character, since `(𝓞 K ⧸ 𝔪.finitePart)ˣ` is finite. -/
@[simp]
theorem residueCharacter_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueCharacter = star χ.residueCharacter := by
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  rw [residueCharacter, residueCharacter, χ.residueUnitHom_inverse]
  exact MulChar.ofUnitHom_inv_eq_star χ.residueUnitHom

/-- Inversion conjugates Hecke's finite character on `𝓞 K`. -/
@[simp]
theorem finiteCharacter_inverse (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.inverse.finiteCharacter a = starRingEnd ℂ (χ.finiteCharacter a) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [← χ.inverse.residueCharacter_mk ha, χ.residueCharacter_inverse,
      MulChar.star_apply, χ.residueCharacter_mk ha]
    rfl

/-- Every value of the residue character on a unit of `𝓞 K ⧸ 𝔪.finitePart` has absolute
value `1`. -/
theorem norm_residueCharacter_unit (χ : Grossencharacter K 𝔪)
    (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) : ‖χ.residueCharacter u‖ = 1 := by
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  rw [residueCharacter, MulChar.ofUnitHom_coe]
  exact (((Units.coeHom ℂ).comp χ.residueUnitHom).isOfFinOrder
    (isOfFinOrder_of_finite u)).norm_eq_one

/-- Every value of Hecke's finite character on an integer coprime to `𝔪` has absolute value
`1`. -/
theorem norm_finiteCharacter_of_isCoprimeTo (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (ha : 𝔪.IsCoprimeTo (Ideal.span {a})) : ‖χ.finiteCharacter a‖ = 1 := by
  have ha0 : a ≠ 0 := fun h ↦
    (Modulus.isCoprimeTo_iff.mp ha).1 (by rw [h, Ideal.span_singleton_zero])
  obtain ⟨u, hu⟩ := (isUnit_mk_iff_isCoprimeTo_span_singleton ha0).mpr ha
  rw [← χ.residueCharacter_mk ha0, ← hu]
  exact χ.norm_residueCharacter_unit u

/-- Every value of Hecke's finite character has absolute value at most `1`. -/
theorem norm_finiteCharacter_le_one (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    ‖χ.finiteCharacter a‖ ≤ 1 := by
  by_cases ha : 𝔪.IsCoprimeTo (Ideal.span {a})
  · exact (χ.norm_finiteCharacter_of_isCoprimeTo ha).le
  · simp [χ.finiteCharacter_eq_zero_of_not_isCoprimeTo ha]

/-- At trivial finite modulus `𝔪.finitePart = ⊤`, the residue ring has one element, a unit, on
which the residue character is identically `1`. -/
theorem residueCharacter_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) (q : 𝓞 K ⧸ 𝔪.finitePart) : χ.residueCharacter q = 1 := by
  have h1 : q = 1 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [← map_one (Ideal.Quotient.mk 𝔪.finitePart), Ideal.Quotient.eq, h]
    exact Submodule.mem_top
  rw [h1, map_one]

/-- The residue character of the trivial ray class character is the trivial `MulChar`. -/
@[simp]
theorem residueCharacter_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).residueCharacter = 1 := by
  refine ((ofRayClassCharacter (1 : RayClassCharacter 𝔪)).existsUnique_residueCharacter).unique
    (fun a ha ↦ (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).residueCharacter_mk ha)
    fun a ha ↦ ?_
  by_cases hcop : 𝔪.IsCoprimeTo (Ideal.span {a})
  · obtain ⟨u, hu⟩ := (isUnit_mk_iff_isCoprimeTo_span_singleton ha).mpr hcop
    rw [← hu, MulChar.one_apply_coe, finiteCharacter, idealShift_ofRayClassCharacter,
      archimedeanValue_ofRayClassCharacter_one, mul_one, Complex.ofReal_zero, Complex.cpow_zero,
      mul_one, unitaryWeight_ofRayClassCharacter, RayClassCharacter.val_toUnitaryIdealWeight,
      RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo 1
        (Ideal.isPrimeTo_iff.mpr (Modulus.isCoprimeTo_iff.mp hcop))]
    simp
  · rw [MulChar.map_nonunit _ ((isUnit_mk_iff_isCoprimeTo_span_singleton ha).not.mpr hcop),
      (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter_eq_zero_of_not_isCoprimeTo
        hcop]

/-! ### Modulus change and finite-conductor characterization -/

/-- Two presentations of the same Hecke character at moduli with `𝔪.finitePart ∣ 𝔫.finitePart`
have compatible residue characters along `finiteUnitsMap`. -/
theorem residueCharacter_comp_finiteUnitsMap {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (hdvd : 𝔪.finitePart ∣ 𝔫.finitePart) (u : (𝓞 K ⧸ 𝔫.finitePart)ˣ) :
    ψ.residueCharacter u = χ.residueCharacter (finiteUnitsMap hdvd u) := by
  classical
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔫 u
  rw [finiteUnitsMap_residueHom, coe_residueHom, coe_residueHom, ψ.residueCharacter_residue x,
    χ.residueCharacter_residue (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x),
    Subgroup.coe_inclusion, ← h]
  congr 1
  have hsub : 𝔪.support ⊆ 𝔫.support := fun v hv ↦
    (𝔫.mem_support_iff v).mpr (((𝔪.mem_support_iff v).mp hv).trans hdvd)
  refine prod_finiteComponent_subset χ.toHeckeCharacter hsub (fun v _ hv𝔪 ↦ ?_)
    (fun v hv𝔫 ↦ mem_primeToSubgroup.mp x.2 v ((𝔫.mem_support_iff v).mp hv𝔫))
  have h0 : 𝔪.exponent v = 0 :=
    not_not.mp ((Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).not.mp hv𝔪)
  exact Nat.le_zero.mp (h0 ▸ χ.conductorExponent_le_exponent v)

/-- Two presentations of the same Hecke character agree on every integer whose principal ideal
is coprime to both moduli. -/
theorem finiteCharacter_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) {a : 𝓞 K}
    (h𝔪 : 𝔪.IsCoprimeTo (Ideal.span {a})) (h𝔫 : 𝔫.IsCoprimeTo (Ideal.span {a})) :
    χ.finiteCharacter a = ψ.finiteCharacter a := by
  have ha0 : a ≠ 0 := fun h0 ↦
    (Modulus.isCoprimeTo_iff.mp h𝔪).1 (by rw [h0, Ideal.span_singleton_zero])
  have hx0 : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  let x : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hx0
  have hx𝔪 : x ∈ primeToSubgroup 𝔪 :=
    (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton (Units.val_mk0 hx0).symm).mpr h𝔪
  have hx𝔫 : x ∈ primeToSubgroup 𝔫 :=
    (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton (Units.val_mk0 hx0).symm).mpr h𝔫
  set 𝔣 : Modulus K :=
    ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩
  have hprod (𝔮 : Modulus K) (θ : Grossencharacter K 𝔮)
      (hθ : θ.toHeckeCharacter = χ.toHeckeCharacter) (hx𝔮 : x ∈ primeToSubgroup 𝔮) :
      (∏ v ∈ 𝔮.support,
        (θ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ)) =
      ∏ v ∈ 𝔣.support,
        (χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ) := by
    have hdiv : χ.toHeckeCharacter.finiteConductor ∣ 𝔮.finitePart :=
      hθ ▸ θ.finiteConductor_dvd_finitePart
    have hsub : 𝔣.support ⊆ 𝔮.support := fun v hv ↦
      (𝔮.mem_support_iff v).mpr (((𝔣.mem_support_iff v).mp hv).trans hdiv)
    rw [hθ]
    exact prod_finiteComponent_subset χ.toHeckeCharacter hsub
      (fun v _ hv𝔣 ↦ not_not.mp ((χ.toHeckeCharacter.dvd_finiteConductor_iff v).not.mp
        fun hdvd ↦ hv𝔣 ((𝔣.mem_support_iff v).mpr hdvd)))
      (fun v hv𝔮 ↦ mem_primeToSubgroup.mp hx𝔮 v ((𝔮.mem_support_iff v).mp hv𝔮))
  rw [χ.finiteCharacter_eq_prod_finiteComponent_inv (Units.val_mk0 hx0).symm hx𝔪,
    ψ.finiteCharacter_eq_prod_finiteComponent_inv (Units.val_mk0 hx0).symm hx𝔫,
    hprod 𝔪 χ rfl hx𝔪, hprod 𝔫 ψ h.symm hx𝔫]

/-- Density of `K` in `K_{v₀}` produces a global element strictly within `exp (-n)` of any
local element `z : K_{v₀}`. -/
private theorem exists_global_approx_local (v₀ : HeightOneSpectrum (𝓞 K))
    (z : v₀.adicCompletion K) (n : ℕ) :
    ∃ a₀ : K, Valued.v (algebraMap K (v₀.adicCompletion K) a₀ - z) < WithZero.exp (-(n : ℤ)) := by
  let r₀ : WithZero (Multiplicative ℤ) := WithZero.exp (-(n : ℤ) - 1)
  have hball : {y : v₀.adicCompletion K | Valued.v (y - z) ≤ r₀} ∈ nhds z := by
    have hopen : IsOpen ((fun y : v₀.adicCompletion K ↦ y - z) ⁻¹'
        {y : v₀.adicCompletion K | Valued.v y ≤ r₀}) :=
      (v₀.isOpen_setOf_valued_le WithZero.exp_ne_zero).preimage (continuous_sub_right _)
    exact hopen.mem_nhds (by simp [r₀])
  obtain ⟨-, ⟨a₀, rfl⟩, ha₀⟩ := (v₀.denseRange_algebraMap K).inter_nhds_nonempty hball
  exact ⟨a₀, lt_of_le_of_lt ha₀ (WithZero.exp_lt_exp.mpr (by omega))⟩

/-- If `x : Kˣ` approximates a local unit `z` at `v₀` within `exp (-n)` (with `Valued.v z = 1`),
then `x * z⁻¹` lies in the `n`-th unit filtration at `v₀`. -/
private theorem mul_inv_mem_unitFiltration_of_sub_lt {v₀ : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    {x : Kˣ} {z : (v₀.adicCompletion K)ˣ} (hz1 : Valued.v (z : v₀.adicCompletion K) = 1)
    (hx1 : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K)) = 1)
    (hxz : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) <
      WithZero.exp (-(n : ℤ))) :
    Units.map (algebraMap K (v₀.adicCompletion K)).toMonoidHom x * z⁻¹ ∈
      TauCeti.unitFiltration (v₀.adicCompletion K) n := by
  rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff]
  refine ⟨?_, ?_⟩
  · simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      map_mul, hx1, one_mul, Units.val_inv_eq_inv_val, map_inv₀, hz1, inv_one]
  · have hsub :
        ((Units.map (algebraMap K (v₀.adicCompletion K)).toMonoidHom x * z⁻¹ :
          (v₀.adicCompletion K)ˣ) : v₀.adicCompletion K) - 1 =
        (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) *
          ((z : v₀.adicCompletion K))⁻¹ := by
      simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ z.ne_zero]
    rw [hsub, map_mul, map_inv₀, hz1, inv_one, mul_one]
    exact hxz.le

/-- Weak-approximation step for `finiteConductor_dvd_iff_residueCharacter_eq_one`: given a prime
`v₀ ∈ 𝔪.support` and a local unit `z ∈ U(K_{v₀}, k)` with `k ≤ 𝔪.exponent v₀`, there is a
global unit `x ∈ primeToSubgroup 𝔪` approximating `z` to level `𝔪.exponent v₀` at `v₀` and `1`
to level `𝔪.exponent v` at every other `v ∈ 𝔪.support`. -/
private theorem exists_primeToSubgroup_approx_localUnit {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∈ 𝔪.support) {k : ℕ} (hk : k ≤ 𝔪.exponent v₀)
    (z : (v₀.adicCompletion K)ˣ)
    (hz : z ∈ TauCeti.unitFiltration (v₀.adicCompletion K) k) :
    ∃ x : primeToSubgroup 𝔪,
      Units.map (algebraMap K (v₀.adicCompletion K)).toMonoidHom (x : Kˣ) * z⁻¹ ∈
          TauCeti.unitFiltration (v₀.adicCompletion K) (𝔪.exponent v₀) ∧
        (∀ v ∈ 𝔪.support, v ≠ v₀ →
          Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ) ∈
            TauCeti.unitFiltration (v.adicCompletion K) (𝔪.exponent v)) ∧
        v₀.valuation K (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_global_approx_local v₀ (z : v₀.adicCompletion K) (𝔪.exponent v₀)
  obtain ⟨x, hxf, -⟩ := exists_fieldUnit_valuation_sub_lt_and_signHom_eq (S := 𝔪.support)
    (fun v ↦ if v = v₀ then a₀ else 1)
    (fun v ↦ WithZero.exp (-(𝔪.exponent v : ℤ)))
    (fun _ _ ↦ WithZero.exp_ne_zero) 1
  have hvpos (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ 𝔪.support) :
      WithZero.exp (-(𝔪.exponent v : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    have hne : 𝔪.exponent v ≠ 0 := (Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).mp hv
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hxz : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) <
      WithZero.exp (-(𝔪.exponent v₀ : ℤ)) := by
    have hxa : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) -
        algebraMap K (v₀.adicCompletion K) a₀) < WithZero.exp (-(𝔪.exponent v₀ : ℤ)) := by
      rw [← map_sub, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation']
      simpa using hxf v₀ hv₀
    have heq : algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K) =
        (algebraMap K (v₀.adicCompletion K) (x : K) - algebraMap K (v₀.adicCompletion K) a₀) +
          (algebraMap K (v₀.adicCompletion K) a₀ - (z : v₀.adicCompletion K)) := by ring
    rw [heq]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hxa ha₀)
  have hz_mem := (HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff v₀).mp hz
  have hx0_val : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K)) = 1 := by
    have hlt : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) -
        (z : v₀.adicCompletion K)) < Valued.v (z : v₀.adicCompletion K) :=
      hxz.trans ((hvpos v₀ hv₀).trans_eq hz_mem.1.symm)
    rw [Valuation.map_eq_of_sub_lt _ hlt, hz_mem.1]
  have hx_mem : x ∈ primeToSubgroup 𝔪 := by
    refine mem_primeToSubgroup.mpr fun v hv ↦ ?_
    have hv' : v ∈ 𝔪.support := (𝔪.mem_support_iff v).mpr hv
    by_cases heq : v = v₀
    · subst heq
      simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using hx0_val
    · have hlt : v.valuation K ((x : K) - 1) < v.valuation K 1 := by
        rw [map_one]
        exact (by simpa [heq] using hxf v hv' : _ < _).trans (hvpos v hv')
      rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  refine ⟨⟨x, hx_mem⟩,
    mul_inv_mem_unitFiltration_of_sub_lt hz_mem.1 hx0_val hxz,
    fun v hv hne ↦ (unitsMap_algebraMap_mem_unitFiltration_iff v (𝔪.exponent v) x).mpr
      ⟨mem_primeToSubgroup.mp hx_mem v ((𝔪.mem_support_iff v).mp hv),
        (by simpa [hne] using hxf v hv : _ < _).le⟩,
    ?_⟩
  have hle : WithZero.exp (-(𝔪.exponent v₀ : ℤ)) ≤ WithZero.exp (-(k : ℤ)) :=
    WithZero.exp_le_exp.mpr (by omega)
  have hsub : Valued.v (algebraMap K (v₀.adicCompletion K) ((x : K) - 1)) ≤
      WithZero.exp (-(k : ℤ)) := by
    have heq : algebraMap K (v₀.adicCompletion K) ((x : K) - 1) =
        (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) +
          ((z : v₀.adicCompletion K) - 1) := by
      rw [map_sub, map_one]; ring
    rw [heq]
    exact (Valuation.map_add _ _ _).trans (max_le (hxz.le.trans hle) hz_mem.2)
  simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using hsub

/-- Forward direction of `finiteConductor_dvd_iff_residueCharacter_eq_one`. -/
private theorem residueCharacter_eq_one_of_finiteConductor_dvd (χ : Grossencharacter K 𝔪)
    {𝔫 : Modulus K} (hdvd : 𝔫.finitePart ∣ 𝔪.finitePart)
    (hcond : χ.toHeckeCharacter.finiteConductor ∣ 𝔫.finitePart)
    (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ)
    (hu : Ideal.Quotient.factor (Ideal.le_of_dvd hdvd) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1) :
    χ.residueCharacter u = 1 := by
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔪 u
  have hres𝔫 : residue 𝔫 (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x) = 1 := by
    have hf := finiteUnitsMap_residueHom hdvd x
    rw [Units.ext_iff, coe_finiteUnitsMap, coe_residueHom, coe_residueHom] at hf
    exact hf.symm.trans (by simpa only [coe_residueHom] using hu)
  have hval :=
    (residue_eq_one_iff (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x)).mp hres𝔫
  rw [coe_residueHom, χ.residueCharacter_residue x, inv_eq_one]
  refine Finset.prod_eq_one fun v hv ↦ ?_
  have hexp : χ.toHeckeCharacter.conductorExponent v ≤ 𝔫.exponent v := by
    rw [Modulus.exponent_def, v.le_count_associates_iff_le_pow 𝔫.finitePart_ne_bot,
      ← Ideal.dvd_iff_le]
    exact ((χ.toHeckeCharacter.pow_dvd_finiteConductor_iff v _).mpr le_rfl).trans hcond
  refine Units.val_eq_one.mpr
    (χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
      (TauCeti.unitFiltration_antitone hexp ?_))
  by_cases hvI : v.asIdeal ∣ 𝔫.finitePart
  · exact (unitsMap_algebraMap_mem_unitFiltration_iff v (𝔫.exponent v) (x : Kˣ)).mpr
      ⟨mem_primeToSubgroup.mp x.2 v ((𝔪.mem_support_iff v).mp hv), hval v hvI⟩
  · have h0 : 𝔫.exponent v = 0 :=
      not_not.mp ((Modulus.mem_support_iff_exponent_ne_zero 𝔫 v).not.mp
        ((𝔫.mem_support_iff v).not.mpr hvI))
    rw [h0]
    exact (v.unitsMap_algebraMap_mem_unitFiltration_zero_iff (x : Kˣ)).mpr
      (mem_primeToSubgroup.mp x.2 v ((𝔪.mem_support_iff v).mp hv))

/-- Converse direction of `finiteConductor_dvd_iff_residueCharacter_eq_one`. -/
private theorem finiteConductor_dvd_of_residueCharacter_eq_one (χ : Grossencharacter K 𝔪)
    {𝔫 : Modulus K} (hdvd : 𝔫.finitePart ∣ 𝔪.finitePart)
    (htriv : ∀ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
      Ideal.Quotient.factor (Ideal.le_of_dvd hdvd) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 →
        χ.residueCharacter u = 1) :
    χ.toHeckeCharacter.finiteConductor ∣ 𝔫.finitePart := by
  classical
  rw [Ideal.dvd_iff_le]
  refine (le_iInf fun v ↦ ?_).trans
    (Ideal.iInf_maxPowDividing_eq χ.toHeckeCharacter.finiteConductor_ne_bot).le
  rw [HeightOneSpectrum.maxPowDividing, χ.toHeckeCharacter.count_finiteConductor]
  refine (Ideal.dvd_iff_le.mp (𝔫.pow_exponent_dvd_finitePart v)).trans
    (Ideal.pow_le_pow_right ?_)
  by_cases hv : v ∈ 𝔪.support
  · rw [χ.toHeckeCharacter.conductorExponent_le_iff]
    intro z hz
    have hle_exp (w : HeightOneSpectrum (𝓞 K)) : 𝔫.exponent w ≤ 𝔪.exponent w := by
      rw [Modulus.exponent_def (m := 𝔪),
        w.le_count_associates_iff_le_pow 𝔪.finitePart_ne_bot, ← Ideal.dvd_iff_le]
      exact (𝔫.pow_exponent_dvd_finitePart w).trans hdvd
    obtain ⟨x, hxz, hother, hxv⟩ := exists_primeToSubgroup_approx_localUnit hv (hle_exp v) z hz
    have hres𝔫 : residue 𝔫 (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x) = 1 := by
      rw [residue_eq_one_iff]
      intro w hwI
      have hw𝔪 : w ∈ 𝔪.support := (𝔪.mem_support_iff w).mpr (hwI.trans hdvd)
      by_cases hwv : w = v
      · subst hwv
        exact hxv
      · have hw_mem :=
          (unitsMap_algebraMap_mem_unitFiltration_iff w (𝔪.exponent w) (x : Kˣ)).mp
            (hother w hw𝔪 hwv)
        exact hw_mem.2.trans (WithZero.exp_le_exp.mpr (by have := hle_exp w; omega))
    have hfactor : Ideal.Quotient.factor (Ideal.le_of_dvd hdvd)
        ((residueHom 𝔪 x : (𝓞 K ⧸ 𝔪.finitePart)ˣ) : 𝓞 K ⧸ 𝔪.finitePart) = 1 := by
      have hf := congrArg Units.val (finiteUnitsMap_residueHom hdvd x)
      simpa only [coe_finiteUnitsMap, coe_residueHom] using
        hf.trans ((coe_residueHom 𝔫 _).trans hres𝔫)
    have h1 := htriv (residueHom 𝔪 x) hfactor
    rw [coe_residueHom, χ.residueCharacter_residue x, inv_eq_one] at h1
    have hprod_single :
        (∏ w ∈ 𝔪.support,
          (χ.toHeckeCharacter.finiteComponent w
            (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom (x : Kˣ)) : ℂ)) =
        (χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)) : ℂ) := by
      refine Finset.prod_eq_single v (fun w hw hne ↦ ?_) (fun hnv ↦ absurd hv hnv)
      rw [χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
        (TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent w) (hother w hw hne)),
        Units.val_one]
    rw [hprod_single, Units.val_eq_one] at h1
    have hdiff : χ.toHeckeCharacter.finiteComponent v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ) * z⁻¹) = 1 :=
      χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
        (TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent v) hxz)
    rw [map_mul, map_inv, h1, one_mul, inv_eq_one] at hdiff
    exact hdiff
  · have h0 : 𝔪.exponent v = 0 :=
      not_not.mp ((Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).not.mp hv)
    exact (Nat.le_zero.mp (h0 ▸ χ.conductorExponent_le_exponent v)).le.trans (Nat.zero_le _)

/-- **Finite-conductor criterion for `residueCharacter`.** For an ideal `I ∣ 𝔪.finitePart`, the
finite conductor of `χ.toHeckeCharacter` divides `I` if and only if `χ.residueCharacter` is
trivial on every unit of `𝓞 K ⧸ 𝔪.finitePart` that reduces to `1` modulo `I`. -/
theorem finiteConductor_dvd_iff_residueCharacter_eq_one (χ : Grossencharacter K 𝔪)
    {I : Ideal (𝓞 K)} (hI : I ∣ 𝔪.finitePart) :
    χ.toHeckeCharacter.finiteConductor ∣ I ↔
      ∀ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
        Ideal.Quotient.factor (Ideal.le_of_dvd hI) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 →
          χ.residueCharacter u = 1 := by
  have hI0 : I ≠ ⊥ := fun hbot ↦ 𝔪.finitePart_ne_bot (by
    obtain ⟨J, hJ⟩ := hI
    rw [hJ, hbot, Ideal.bot_mul])
  exact ⟨fun hcond u hu ↦
      χ.residueCharacter_eq_one_of_finiteConductor_dvd (𝔫 := ⟨I, hI0, ∅⟩) hI hcond u hu,
    fun htriv ↦
      χ.finiteConductor_dvd_of_residueCharacter_eq_one (𝔫 := ⟨I, hI0, ∅⟩) hI htriv⟩

/-- **Primitivity of `residueCharacter` at the finite conductor.** When `𝔪.finitePart` equals
the finite conductor of `χ.toHeckeCharacter`, `χ.residueCharacter` does not factor through any
proper divisor `I` of `𝔪.finitePart`: there exists a residue unit congruent to `1` modulo `I`
on which `χ.residueCharacter` is nontrivial. -/
theorem exists_residueCharacter_ne_one_of_finiteConductor_eq (χ : Grossencharacter K 𝔪)
    (hcond : χ.toHeckeCharacter.finiteConductor = 𝔪.finitePart) {I : Ideal (𝓞 K)}
    (hI : I ∣ 𝔪.finitePart) (hIne : I ≠ 𝔪.finitePart) :
    ∃ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
      Ideal.Quotient.factor (Ideal.le_of_dvd hI) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 ∧
        χ.residueCharacter u ≠ 1 := by
  by_contra h
  push Not at h
  have hdvd : 𝔪.finitePart ∣ I :=
    hcond ▸ (χ.finiteConductor_dvd_iff_residueCharacter_eq_one hI).mpr h
  exact hIne (le_antisymm (Ideal.le_of_dvd hdvd) (Ideal.le_of_dvd hI))

/-! ### Multiplicative extension to `Kˣ` and `K` -/

open scoped Classical in
/-- **Hecke's finite character on `Kˣ`**: multiplicative on `primeToSubgroup 𝔪` (where it
evaluates the residue character on the reduction modulo `𝔪.finitePart`), and `0` outside
`primeToSubgroup 𝔪`. It is the unique function with these properties agreeing with
`finiteCharacter` on algebraic integers (`existsUnique_finiteCharacterK`). -/
def finiteCharacterK (χ : Grossencharacter K 𝔪) (x : Kˣ) : ℂ :=
  if hx : x ∈ primeToSubgroup 𝔪 then χ.residueCharacter (residue 𝔪 ⟨x, hx⟩) else 0

/-- On `primeToSubgroup 𝔪`, `finiteCharacterK` evaluates the residue character at the
reduction. -/
theorem finiteCharacterK_of_mem (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : x ∈ primeToSubgroup 𝔪) :
    χ.finiteCharacterK x = χ.residueCharacter (residue 𝔪 ⟨x, hx⟩) := by
  classical
  exact dite_eq_left hx

/-- Outside `primeToSubgroup 𝔪`, `finiteCharacterK` vanishes. -/
theorem finiteCharacterK_of_not_mem (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : x ∉ primeToSubgroup 𝔪) :
    χ.finiteCharacterK x = 0 := by
  classical
  exact dite_eq_right hx

/-- On nonzero algebraic integers, `finiteCharacterK` agrees with `finiteCharacter`. -/
theorem finiteCharacterK_algebraMap (χ : Grossencharacter K 𝔪) {a : 𝓞 K} {x : Kˣ}
    (ha : algebraMap (𝓞 K) K a = x) :
    χ.finiteCharacterK x = χ.finiteCharacter a := by
  have ha0 : a ≠ 0 := fun h ↦ x.ne_zero (by rw [← ha, h, map_zero])
  by_cases hx : x ∈ primeToSubgroup 𝔪
  · rw [χ.finiteCharacterK_of_mem hx,
      residue_eq (a := a) (b := 1) ⟨x, hx⟩ (by simp) (by simp [ha]),
      χ.residueCharacter_mk ha0]
  · rw [χ.finiteCharacterK_of_not_mem hx,
      χ.finiteCharacter_eq_zero_of_not_isCoprimeTo
        ((mem_primeToSubgroup_iff_isCoprimeTo_span_singleton ha).not.mp hx)]

/-- `finiteCharacterK` evaluates to `1` at `1`. -/
@[simp]
theorem finiteCharacterK_one (χ : Grossencharacter K 𝔪) : χ.finiteCharacterK 1 = 1 := by
  rw [χ.finiteCharacterK_algebraMap (a := 1) (x := 1) (map_one _), finiteCharacter_one]

/-- `finiteCharacterK` is multiplicative on `primeToSubgroup 𝔪`. -/
theorem finiteCharacterK_mul (χ : Grossencharacter K 𝔪) {x y : Kˣ}
    (hx : x ∈ primeToSubgroup 𝔪) (hy : y ∈ primeToSubgroup 𝔪) :
    χ.finiteCharacterK (x * y) = χ.finiteCharacterK x * χ.finiteCharacterK y := by
  rw [χ.finiteCharacterK_of_mem (mul_mem hx hy), χ.finiteCharacterK_of_mem hx,
    χ.finiteCharacterK_of_mem hy, ← map_mul χ.residueCharacter, ← map_mul (residue 𝔪)]
  rfl

/-- `finiteCharacterK` vanishes at `x : Kˣ` if and only if `x ∉ primeToSubgroup 𝔪`. -/
theorem finiteCharacterK_eq_zero_iff (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.finiteCharacterK x = 0 ↔ x ∉ primeToSubgroup 𝔪 := by
  by_cases hx : x ∈ primeToSubgroup 𝔪
  · refine ⟨fun h ↦ False.elim ?_, fun h ↦ absurd hx h⟩
    rw [χ.finiteCharacterK_of_mem hx, ← coe_residueHom] at h
    have hnorm := χ.norm_residueCharacter_unit (residueHom 𝔪 ⟨x, hx⟩)
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · exact ⟨fun _ ↦ hx, fun _ ↦ χ.finiteCharacterK_of_not_mem hx⟩

/-- Every value of `finiteCharacterK` on `primeToSubgroup 𝔪` has absolute value `1`. -/
theorem norm_finiteCharacterK_of_mem (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : x ∈ primeToSubgroup 𝔪) : ‖χ.finiteCharacterK x‖ = 1 := by
  rw [χ.finiteCharacterK_of_mem hx, ← coe_residueHom]
  exact χ.norm_residueCharacter_unit (residueHom 𝔪 ⟨x, hx⟩)

/-- Inverting an element of `Kˣ` conjugates its value under `finiteCharacterK`. -/
theorem finiteCharacterK_inv (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.finiteCharacterK x⁻¹ = starRingEnd ℂ (χ.finiteCharacterK x) := by
  by_cases hx : x ∈ primeToSubgroup 𝔪
  · have hxi : x⁻¹ ∈ primeToSubgroup 𝔪 := inv_mem hx
    rw [χ.finiteCharacterK_of_mem hxi, χ.finiteCharacterK_of_mem hx, ← coe_residueHom,
      ← coe_residueHom]
    have hinv : residueHom 𝔪 ⟨x⁻¹, hxi⟩ = (residueHom 𝔪 ⟨x, hx⟩)⁻¹ :=
      map_inv (residueHom 𝔪) ⟨x, hx⟩
    rw [hinv]
    set u : (𝓞 K ⧸ 𝔪.finitePart)ˣ := residueHom 𝔪 ⟨x, hx⟩
    have h1 : χ.residueCharacter (u⁻¹ : (𝓞 K ⧸ 𝔪.finitePart)ˣ) *
        χ.residueCharacter (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Complex.inv_eq_conj (χ.norm_residueCharacter_unit u)
  · rw [χ.finiteCharacterK_of_not_mem (fun h ↦ hx (inv_inv x ▸ inv_mem h)),
      χ.finiteCharacterK_of_not_mem hx, map_zero]

/-- On any element of `Kˣ` congruent to `1` modulo `𝔪`, `finiteCharacterK` takes the value
`1`. -/
theorem finiteCharacterK_eq_one_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : IsCongrOne 𝔪 x) : χ.finiteCharacterK x = 1 := by
  have hxp : x ∈ primeToSubgroup 𝔪 :=
    congruenceSubgroup_le_primeToSubgroup 𝔪 (mem_congruenceSubgroup.mpr hx)
  rw [χ.finiteCharacterK_of_mem hxp, ← coe_residueHom,
    residueHom_eq_one_of_mem_congruenceSubgroup (mem_congruenceSubgroup.mpr hx), Units.val_one,
    map_one]

/-- Inversion conjugates `finiteCharacterK` on all of `Kˣ`. -/
@[simp]
theorem finiteCharacterK_inverse (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.inverse.finiteCharacterK x = starRingEnd ℂ (χ.finiteCharacterK x) := by
  by_cases hx : x ∈ primeToSubgroup 𝔪
  · rw [χ.inverse.finiteCharacterK_of_mem hx, χ.finiteCharacterK_of_mem hx,
      χ.residueCharacter_inverse, MulChar.star_apply]
    rfl
  · rw [χ.inverse.finiteCharacterK_of_not_mem hx, χ.finiteCharacterK_of_not_mem hx, map_zero]

/-- Every element of `primeToSubgroup 𝔪` is a quotient of two nonzero algebraic integers in
`primeToSubgroup 𝔪`. -/
private theorem exists_primeToSubgroup_div_eq {x : Kˣ} (hx : x ∈ primeToSubgroup 𝔪) :
    ∃ (a b : 𝓞 K) (xa xb : Kˣ),
      algebraMap (𝓞 K) K a = xa ∧ algebraMap (𝓞 K) K b = xb ∧
        xa ∈ primeToSubgroup 𝔪 ∧ xb ∈ primeToSubgroup 𝔪 ∧ xa = xb * x := by
  obtain ⟨a, b, hb, hab⟩ :=
    𝔪.finitePart.exists_algebraMap_eq_mul_and_sub_one_mem_of_valuation_le_one
      (fun v hv ↦ (mem_primeToSubgroup.mp hx v hv).le)
  by_cases hb0 : b = 0
  · -- Then `-1 ∈ 𝔪.finitePart`, so `𝔪.finitePart = ⊤` and every nonzero integer is prime.
    have htop : 𝔪.finitePart = ⊤ := by
      rw [hb0, zero_sub] at hb
      have h1 : (1 : 𝓞 K) ∈ 𝔪.finitePart := by simpa using 𝔪.finitePart.neg_mem hb
      exact Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (x : K)
    have hq0 : algebraMap (𝓞 K) K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (nonZeroDivisors.ne_zero hq)
    have hpqx : algebraMap (𝓞 K) K p = algebraMap (𝓞 K) K q * (x : K) := by
      rw [← hpq, mul_div_cancel₀ _ hq0]
    have hp0 : algebraMap (𝓞 K) K p ≠ 0 := by
      rw [hpqx]
      exact mul_ne_zero hq0 x.ne_zero
    have hmem_all (y : Kˣ) : y ∈ primeToSubgroup 𝔪 :=
      mem_primeToSubgroup.mpr fun v hv ↦
        absurd (top_le_iff.mp (Ideal.le_of_dvd (htop ▸ hv))) v.isPrime.ne_top
    exact ⟨p, q, Units.mk0 _ hp0, Units.mk0 _ hq0, rfl, rfl, hmem_all _, hmem_all _,
      Units.ext hpqx⟩
  · have hxb0 : algebraMap (𝓞 K) K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb0
    let xb : Kˣ := Units.mk0 (algebraMap (𝓞 K) K b) hxb0
    have hxb : xb ∈ primeToSubgroup 𝔪 := by
      refine mem_primeToSubgroup.mpr fun v hv ↦ ?_
      rw [Units.val_mk0, v.valuation_of_algebraMap]
      refine v.intValuation_eq_one_iff.mpr fun hbv ↦ v.isPrime.ne_top ?_
      have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
        have hsub : b - 1 ∈ v.asIdeal := Ideal.le_of_dvd hv hb
        simpa using v.asIdeal.sub_mem hbv hsub
      exact Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
    have hxa0 : algebraMap (𝓞 K) K a ≠ 0 := by
      rw [hab]
      exact mul_ne_zero hxb0 x.ne_zero
    let xa : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hxa0
    have hxeq : xa = xb * x := Units.ext hab
    exact ⟨a, b, xa, xb, rfl, rfl, hxeq ▸ mul_mem hxb hx, hxb, hxeq⟩

/-- **Existence and uniqueness of the multiplicative extension to `Kˣ`.** There is a unique
function `Kˣ → ℂ` that is multiplicative on `primeToSubgroup 𝔪`, vanishes outside it, and
agrees with `χ.finiteCharacter` on algebraic integers. -/
theorem existsUnique_finiteCharacterK (χ : Grossencharacter K 𝔪) :
    ∃! f : Kˣ → ℂ,
      (∀ x y : Kˣ, x ∈ primeToSubgroup 𝔪 → y ∈ primeToSubgroup 𝔪 →
        f (x * y) = f x * f y) ∧
      (∀ x : Kˣ, x ∉ primeToSubgroup 𝔪 → f x = 0) ∧
      ∀ (a : 𝓞 K) (x : Kˣ), algebraMap (𝓞 K) K a = x → f x = χ.finiteCharacter a := by
  refine ⟨χ.finiteCharacterK,
    ⟨fun _ _ hx hy ↦ χ.finiteCharacterK_mul hx hy,
      fun _ hx ↦ χ.finiteCharacterK_of_not_mem hx,
      fun _ _ ha ↦ χ.finiteCharacterK_algebraMap ha⟩,
    fun f ⟨hmul, hzero, hint⟩ ↦ funext fun x ↦ ?_⟩
  by_cases hx : x ∈ primeToSubgroup 𝔪
  · obtain ⟨a, b, xa, xb, ha, hb, _, hxb, hxeq⟩ := exists_primeToSubgroup_div_eq hx
    have h1 : f xb * f x = χ.finiteCharacterK xb * χ.finiteCharacterK x := by
      rw [← hmul xb x hxb hx, ← χ.finiteCharacterK_mul hxb hx, ← hxeq, hint a xa ha,
        χ.finiteCharacterK_algebraMap ha]
    rw [hint b xb hb, ← χ.finiteCharacterK_algebraMap hb] at h1
    exact mul_left_cancel₀ ((χ.finiteCharacterK_eq_zero_iff xb).not.mpr (not_not.mpr hxb)) h1
  · rw [hzero x hx, χ.finiteCharacterK_of_not_mem hx]

open scoped Classical in
/-- **Hecke's finite character on `K`**, extended by `0` at `0`: the finite-character coefficient
evaluated on elements of fractional ideals. -/
def finiteCharacterK' (χ : Grossencharacter K 𝔪) (x : K) : ℂ :=
  if h : x = 0 then 0 else χ.finiteCharacterK (Units.mk0 x h)

/-- `finiteCharacterK'` vanishes at `0`. -/
@[simp]
theorem finiteCharacterK'_zero (χ : Grossencharacter K 𝔪) : χ.finiteCharacterK' 0 = 0 := by
  classical
  exact dite_eq_left rfl

/-- `finiteCharacterK'` evaluates to `1` at `1`. -/
@[simp]
theorem finiteCharacterK'_one (χ : Grossencharacter K 𝔪) : χ.finiteCharacterK' 1 = 1 := by
  classical
  rw [finiteCharacterK', dite_eq_right one_ne_zero, Units.mk0_one, finiteCharacterK_one]

/-- On nonzero elements of `K`, `finiteCharacterK'` agrees with `finiteCharacterK`. -/
theorem finiteCharacterK'_of_ne_zero (χ : Grossencharacter K 𝔪) {x : K} (hx : x ≠ 0) :
    χ.finiteCharacterK' x = χ.finiteCharacterK (Units.mk0 x hx) := by
  classical
  exact dite_eq_right hx

/-- On algebraic integers, `finiteCharacterK'` agrees with `finiteCharacter`. -/
@[simp]
theorem finiteCharacterK'_algebraMap (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacterK' (algebraMap (𝓞 K) K a) = χ.finiteCharacter a := by
  by_cases ha : a = 0
  · simp [ha]
  · have hx : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
    rw [χ.finiteCharacterK'_of_ne_zero hx,
      χ.finiteCharacterK_algebraMap (x := Units.mk0 _ hx) rfl]

/-- Multiplying any element of `K` by an element of `primeToSubgroup 𝔪` factors out the finite
character. -/
theorem finiteCharacterK'_mul_of_mem_left (χ : Grossencharacter K 𝔪) {u : Kˣ}
    (hu : u ∈ primeToSubgroup 𝔪) (x : K) :
    χ.finiteCharacterK' ((u : K) * x) = χ.finiteCharacterK u * χ.finiteCharacterK' x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hux : (u : K) * x ≠ 0 := mul_ne_zero u.ne_zero hx
    rw [χ.finiteCharacterK'_of_ne_zero hux, χ.finiteCharacterK'_of_ne_zero hx]
    have hunit : Units.mk0 ((u : K) * x) hux = u * Units.mk0 x hx := Units.ext rfl
    rw [hunit]
    by_cases hxm : Units.mk0 x hx ∈ primeToSubgroup 𝔪
    · exact χ.finiteCharacterK_mul hu hxm
    · have huxm : u * Units.mk0 x hx ∉ primeToSubgroup 𝔪 := fun h ↦
        hxm (by simpa using mul_mem (inv_mem hu) h)
      rw [χ.finiteCharacterK_of_not_mem huxm, χ.finiteCharacterK_of_not_mem hxm, mul_zero]

/-- Multiplying any element of `K` by a global unit `u : (𝓞 K)ˣ` factors out
`χ.finiteCharacter u`. This is the finite-character input to unit invariance of twisted theta
series on fractional ideals. -/
theorem finiteCharacterK'_mul_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (x : K) :
    χ.finiteCharacterK' (algebraMap (𝓞 K) K u * x) =
      χ.finiteCharacter u * χ.finiteCharacterK' x := by
  let uK : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  have hu : uK ∈ primeToSubgroup 𝔪 := unitsMap_mem_primeToSubgroup 𝔪 u
  have heq : algebraMap (𝓞 K) K u = (uK : K) := rfl
  rw [heq, χ.finiteCharacterK'_mul_of_mem_left hu x, χ.finiteCharacterK_algebraMap heq]

/-- Inversion conjugates `finiteCharacterK'` on all of `K`. -/
@[simp]
theorem finiteCharacterK'_inverse (χ : Grossencharacter K 𝔪) (x : K) :
    χ.inverse.finiteCharacterK' x = starRingEnd ℂ (χ.finiteCharacterK' x) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [χ.inverse.finiteCharacterK'_of_ne_zero hx, χ.finiteCharacterK'_of_ne_zero hx,
      χ.finiteCharacterK_inverse]

/-- Every value of `finiteCharacterK'` has absolute value at most `1`. -/
theorem norm_finiteCharacterK'_le_one (χ : Grossencharacter K 𝔪) (x : K) :
    ‖χ.finiteCharacterK' x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [χ.finiteCharacterK'_of_ne_zero hx]
    by_cases hxm : Units.mk0 x hx ∈ primeToSubgroup 𝔪
    · exact (χ.norm_finiteCharacterK_of_mem hxm).le
    · simp [χ.finiteCharacterK_of_not_mem hxm]

/-! ### Ray class presentations -/

/-- For the presentation of a ray class character `η`, the finite character at an integer `a`
prime to `𝔪` is the ray class value of the principal ideal `(a)` multiplied by the archimedean
sign product. -/
theorem finiteCharacter_ofRayClassCharacter (η : RayClassCharacter 𝔪) {a : 𝓞 K} {x : Kˣ}
    (ha : algebraMap (𝓞 K) K a = x) (hx : x ∈ primeToSubgroup 𝔪) :
    (ofRayClassCharacter η).finiteCharacter a =
      (η (principalRayClass 𝔪 ⟨x, hx⟩) : ℂ) *
        (ofRayClassCharacter η).archimedeanValue (x : K) := by
  have hcop : 𝔪.IsCoprimeTo (Ideal.span {a}) :=
    (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton ha).mp hx
  have hJ : Ideal.span {a} ∈ integralIdealsPrimeTo 𝔪 :=
    Modulus.mem_integralIdealsPrimeTo.mpr hcop
  obtain ⟨y, hy, hclass⟩ :=
    exists_idealClass_eq_principalRayClass (𝔪 := 𝔪) (J := ⟨Ideal.span {a}, hJ⟩) rfl
  have hxy : y = ⟨x, hx⟩ := Subtype.ext (Units.ext (hy.trans ha))
  rw [finiteCharacter, idealShift_ofRayClassCharacter, Complex.ofReal_zero, Complex.cpow_zero,
    mul_one, ha, unitaryWeight_ofRayClassCharacter, RayClassCharacter.val_toUnitaryIdealWeight,
    RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo η
      (Ideal.isPrimeTo_iff.mpr (Modulus.isCoprimeTo_iff.mp hcop)),
    RayClassCharacter.onIdeals_apply, hclass, hxy]

open scoped Classical in
/-- For the trivial ray class character at modulus `𝔪`, Hecke's finite character is the
indicator of integers generating ideals coprime to `𝔪`. -/
theorem finiteCharacter_ofRayClassCharacter_one (a : 𝓞 K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter a =
      if 𝔪.IsCoprimeTo (Ideal.span {a}) then 1 else 0 := by
  split_ifs with hcop
  · have ha0 : a ≠ 0 := fun h ↦
      (Modulus.isCoprimeTo_iff.mp hcop).1 (by rw [h, Ideal.span_singleton_zero])
    have hx0 : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
    let x : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hx0
    have hx : x ∈ primeToSubgroup 𝔪 :=
      (mem_primeToSubgroup_iff_isCoprimeTo_span_singleton (Units.val_mk0 hx0).symm).mpr hcop
    rw [finiteCharacter_ofRayClassCharacter 1 (Units.val_mk0 hx0).symm hx,
      archimedeanValue_ofRayClassCharacter_one]
    simp
  · exact (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter_eq_zero_of_not_isCoprimeTo
      hcop

end TauCeti.LFunctions.Grossencharacter
