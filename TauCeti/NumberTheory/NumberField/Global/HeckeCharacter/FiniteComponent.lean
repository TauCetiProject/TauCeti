/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Conductor
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Congruence

import TauCeti.Analysis.Normed.Algebra.NoSmallSubgroups
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The finite components and the finite conductor of a Hecke character

Let `χ` be a Hecke character of a number field `K` and let `v` be a finite place of `K`.
Restricting `χ` along the embedding of `K_vˣ` into the idele class group gives a continuous
character `χ_v` of `K_vˣ`, the **component of `χ` at `v`**.

The unit group `𝓞_vˣ` has the unit filtration `U(K_v, n)` (`TauCeti.unitFiltration`) as a basis of
open neighbourhoods of `1`, consisting of subgroups, while `ℂˣ` has no small subgroups. Hence
`χ_v` is trivial on `U(K_v, n)` for some `n`, and the least such `n` is the **conductor exponent**
`a_v(χ)`. More is true: `χ` is trivial on the finite part of an idele congruence subgroup, so a
single modulus `𝔪` bounds every conductor exponent, `a_v(χ) ≤ 𝔪.exponent v`. In particular
`χ_v` is trivial on `𝓞_vˣ`, that is, `χ` is unramified at `v`, for all but finitely many `v`. The
**finite conductor** of `χ` is the integral ideal

`𝔣(χ) = ∏_v v ^ a_v(χ)`,

whose `v`-adic exponent is `a_v(χ)`. It is defined for every Hecke character, including the ones
of infinite order, and the primes dividing it are exactly the finite places at which `χ` is
ramified. For a character of finite order it is the finite part of the conductor, the least modulus
from which the character comes: the finite part of the conductor is determined place by place by
the finite components.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.finiteComponent`: the character of `K_vˣ` obtained by
  restricting a Hecke character.
* `TauCeti.GlobalNumberFields.HeckeCharacter.conductorExponent`: the least `n` such that the
  component at `v` is trivial on `U(K_v, n)`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.finiteConductor`: the ideal `∏_v v ^ a_v(χ)`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.exists_modulus_finiteComponent_eq_one`: a single
  modulus `𝔪` such that every component `χ_v` is trivial on `U(K_v, 𝔪.exponent v)`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.conductorExponent_le_iff`: `a_v(χ) ≤ n` exactly when
  `χ_v` is trivial on `U(K_v, n)`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.eventually_conductorExponent_eq_zero`: `χ` is
  unramified at all but finitely many finite places.
* `TauCeti.GlobalNumberFields.HeckeCharacter.pow_dvd_finiteConductor_iff`: `v ^ n` divides the
  finite conductor exactly when `n ≤ a_v(χ)`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.finitePart_conductor`: for a character of finite
  order, the finite conductor is the finite part of the conductor
  `TauCeti.GlobalNumberFields.HeckeCharacter.conductor`, the least modulus from which the character
  comes.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.4 and §3.1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Filter Topology
open scoped NumberField

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-! ### The component at a finite place -/

/-- The **component of a Hecke character `χ` at a finite place `v`**: the continuous character of
`K_vˣ` obtained by composing `χ` with the embedding of `K_vˣ` into the idele class group. -/
def finiteComponent (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* ℂˣ :=
  χ.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 K) K v,
    IdeleClassGroup.continuous_ofAdicCompletion _ _ v⟩

/-- The component of `χ` at `v` evaluates `χ` on the idele class concentrated at `v`. -/
@[simp]
theorem finiteComponent_apply (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    χ.finiteComponent v u = χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) :=
  (rfl)

/-- The trivial Hecke character has trivial components. -/
@[simp]
theorem finiteComponent_one (v : HeightOneSpectrum (𝓞 K)) :
    (1 : HeckeCharacter K).finiteComponent v = 1 :=
  (rfl)

/-- Components of a product of Hecke characters are the products of the components. -/
@[simp]
theorem finiteComponent_mul (χ ψ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (χ * ψ).finiteComponent v = χ.finiteComponent v * ψ.finiteComponent v :=
  (rfl)

/-- Components of the inverse of a Hecke character are the inverses of the components. -/
@[simp]
theorem finiteComponent_inv (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ⁻¹.finiteComponent v = (χ.finiteComponent v)⁻¹ :=
  (rfl)

/-- Components of a power of a Hecke character are the powers of the components. -/
@[simp]
theorem finiteComponent_pow (χ : HeckeCharacter K) (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (χ ^ n).finiteComponent v = χ.finiteComponent v ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-! ### Triviality on the unit filtration -/

/-- A Hecke character is trivial on the finite parts of all ideles in a sufficiently small
idele congruence subgroup. This controls the entire finite idele, including its infinitely many
unit coordinates, rather than just each local component separately. -/
theorem exists_modulus_finitePart_eq_one (χ : HeckeCharacter K) :
    ∃ 𝔪 : Modulus K, ∀ x ∈ ideleCongruenceSubgroup 𝔪,
      χ (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 K) K
        (IdeleGroup.toFiniteIdele (𝓞 K) K x))) = 1 := by
  -- The finite parts of the ideles of a small enough idele congruence subgroup form a subgroup on
  -- which `χ` stays close to `1`, and `ℂˣ` has no small subgroups.
  -- `χ` as a character of the idele group, and a neighbourhood of `1` on which it kills every
  -- subgroup.
  let f : IdeleGroup (𝓞 K) K →ₜ* ℂˣ :=
    χ.comp (ContinuousMonoidHom.quotientMk (IdeleGroup.principalSubgroup (𝓞 K) K))
  obtain ⟨N, hN, hNker⟩ := f.exists_mem_nhds_one_forall_le_ker
  obtain ⟨𝔪, h𝔪⟩ := exists_ideleCongruenceSubgroup_ofFiniteIdele_mem_of_mem_nhds hN
  -- The finite parts of the ideles of `ideleCongruenceSubgroup 𝔪` form a subgroup inside `N`.
  let φ : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 K) K :=
    (IdeleGroup.ofFiniteIdele (𝓞 K) K).comp (IdeleGroup.toFiniteIdele (𝓞 K) K)
  have hker : (ideleCongruenceSubgroup 𝔪).map φ ≤ f.ker :=
    hNker _ (by rintro _ ⟨x, hx, rfl⟩; exact h𝔪 x hx)
  exact ⟨𝔪, fun x hx ↦ MonoidHom.mem_ker.mp (hker ⟨x, hx, rfl⟩)⟩

/-- **A Hecke character is trivial on a congruence subgroup at every finite place.** There is a
modulus `𝔪` such that at every finite place `v` the component of `χ` is trivial on the step
`U(K_v, 𝔪.exponent v)` of the unit filtration: on the units of `𝓞_v` when `v` does not divide `𝔪`,
and on the principal units of level `𝔪.exponent v` when it does. -/
theorem exists_modulus_finiteComponent_eq_one (χ : HeckeCharacter K) :
    ∃ 𝔪 : Modulus K, ∀ (v : HeightOneSpectrum (𝓞 K)),
      ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) (𝔪.exponent v),
        χ.finiteComponent v u = 1 := by
  obtain ⟨𝔪, h𝔪⟩ := χ.exists_modulus_finitePart_eq_one
  refine ⟨𝔪, fun v u hu ↦ ?_⟩
  -- An idele concentrated at a finite place is its own finite part.
  have hφ : IdeleGroup.ofFiniteIdele (𝓞 K) K
      (IdeleGroup.toFiniteIdele (𝓞 K) K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K v u :=
    Units.ext <| by
      rw [IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_toFiniteIdele,
        IdeleGroup.val_ofAdicCompletion_apply]
  have h := h𝔪 _ (ofAdicCompletion_mem_ideleCongruenceSubgroup_iff.mpr hu)
  simpa only [hφ, finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply] using h

/-- **The component of a Hecke character at a finite place is trivial on a step of the unit
filtration.** -/
theorem exists_finiteComponent_eq_one (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) n, χ.finiteComponent v u = 1 :=
  let ⟨𝔪, h𝔪⟩ := χ.exists_modulus_finiteComponent_eq_one
  ⟨𝔪.exponent v, h𝔪 v⟩

/-! ### The conductor exponent -/

/-- The **conductor exponent** `a_v(χ)` of a Hecke character `χ` at a finite place `v`: the least
`n` such that the component of `χ` at `v` is trivial on the step `U(K_v, n)` of the unit
filtration.  It vanishes exactly when `χ` is unramified at `v`
(`conductorExponent_eq_zero_iff`). -/
def conductorExponent (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  sInf {n | ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) n, χ.finiteComponent v u = 1}

/-- The component of `χ` at `v` is trivial on `U(K_v, a_v(χ))`. -/
theorem finiteComponent_eq_one_of_mem_unitFiltration (χ : HeckeCharacter K)
    {v : HeightOneSpectrum (𝓞 K)} {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ TauCeti.unitFiltration (v.adicCompletion K) (χ.conductorExponent v)) :
    χ.finiteComponent v u = 1 :=
  Nat.sInf_mem (χ.exists_finiteComponent_eq_one v) u hu

/-- **The characterizing property of the conductor exponent**: `a_v(χ) ≤ n` exactly when the
component of `χ` at `v` is trivial on `U(K_v, n)`. -/
theorem conductorExponent_le_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    χ.conductorExponent v ≤ n ↔
      ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) n, χ.finiteComponent v u = 1 :=
  ⟨fun h _ hu ↦ χ.finiteComponent_eq_one_of_mem_unitFiltration
    (TauCeti.unitFiltration_antitone h hu), fun h ↦ Nat.sInf_le h⟩

/-- **The conductor exponent vanishes exactly at the unramified places**, those at which the
component of `χ` is trivial on the units `U(K_v, 0)` of `𝓞_v`. -/
theorem conductorExponent_eq_zero_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ.conductorExponent v = 0 ↔
      ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) 0, χ.finiteComponent v u = 1 := by
  rw [← Nat.le_zero, conductorExponent_le_iff]

/-- **One modulus bounds every conductor exponent.** -/
theorem exists_modulus_conductorExponent_le (χ : HeckeCharacter K) :
    ∃ 𝔪 : Modulus K, ∀ v : HeightOneSpectrum (𝓞 K), χ.conductorExponent v ≤ 𝔪.exponent v :=
  let ⟨𝔪, h𝔪⟩ := χ.exists_modulus_finiteComponent_eq_one
  ⟨𝔪, fun v ↦ (χ.conductorExponent_le_iff v _).mpr (h𝔪 v)⟩

/-- **A Hecke character is unramified at all but finitely many finite places.** -/
theorem eventually_conductorExponent_eq_zero (χ : HeckeCharacter K) :
    ∀ᶠ v in cofinite, χ.conductorExponent v = 0 := by
  obtain ⟨𝔪, h𝔪⟩ := χ.exists_modulus_conductorExponent_le
  have hsub : {v | χ.conductorExponent v ≠ 0} ⊆ 𝔪.support := fun v hv ↦
    (Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).mpr fun h ↦ hv (Nat.le_zero.mp (h ▸ h𝔪 v))
  exact (𝔪.support.finite_toSet.subset hsub).eventually_cofinite_notMem.mono fun v hv ↦
    not_not.mp hv

/-- The trivial Hecke character is unramified everywhere. -/
@[simp]
theorem conductorExponent_one (v : HeightOneSpectrum (𝓞 K)) :
    (1 : HeckeCharacter K).conductorExponent v = 0 :=
  (conductorExponent_eq_zero_iff 1 v).mpr fun _ _ ↦ by simp

/-- A Hecke character and its inverse have the same conductor exponents. -/
@[simp]
theorem conductorExponent_inv (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ⁻¹.conductorExponent v = χ.conductorExponent v := by
  refine le_antisymm ((conductorExponent_le_iff _ v _).mpr fun u hu ↦ ?_)
    ((conductorExponent_le_iff _ v _).mpr fun u hu ↦ ?_)
  · rw [finiteComponent_inv, ← zpow_neg_one, ContinuousMonoidHom.zpow_apply,
      χ.finiteComponent_eq_one_of_mem_unitFiltration hu, one_zpow]
  · rw [← inv_inv χ, finiteComponent_inv, ← zpow_neg_one, ContinuousMonoidHom.zpow_apply,
      χ⁻¹.finiteComponent_eq_one_of_mem_unitFiltration hu, one_zpow]

/-- The conductor exponent of a product is at most the larger of the two conductor exponents. -/
theorem conductorExponent_mul_le (χ ψ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (χ * ψ).conductorExponent v ≤ max (χ.conductorExponent v) (ψ.conductorExponent v) := by
  refine (conductorExponent_le_iff _ v _).mpr fun u hu ↦ ?_
  rw [finiteComponent_mul, ContinuousMonoidHom.mul_apply,
    χ.finiteComponent_eq_one_of_mem_unitFiltration
      (TauCeti.unitFiltration_antitone (le_max_left _ _) hu),
    ψ.finiteComponent_eq_one_of_mem_unitFiltration
      (TauCeti.unitFiltration_antitone (le_max_right _ _) hu), one_mul]

/-! ### The finite conductor -/

/-- The **finite conductor** of a Hecke character `χ`: the integral ideal `∏_v v ^ a_v(χ)`, whose
`v`-adic exponent is the conductor exponent `a_v(χ)` (`pow_dvd_finiteConductor_iff`). Only
finitely many factors differ from `1` (`eventually_conductorExponent_eq_zero`). -/
def finiteConductor (χ : HeckeCharacter K) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ χ.conductorExponent v

/-- The finite conductor is the product of the prime powers `v ^ a_v(χ)`. -/
theorem finiteConductor_def (χ : HeckeCharacter K) :
    χ.finiteConductor = ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ χ.conductorExponent v :=
  (rfl)

/-- The factors of the product defining the finite conductor are trivial away from finitely many
places. -/
private theorem hasFiniteMulSupport_pow_conductorExponent (χ : HeckeCharacter K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.asIdeal ^ χ.conductorExponent v).Finite :=
  χ.eventually_conductorExponent_eq_zero.mono fun v hv ↦ by simp [hv]

/-- The finite conductor of a Hecke character is a nonzero ideal. -/
theorem finiteConductor_ne_bot (χ : HeckeCharacter K) : χ.finiteConductor ≠ ⊥ := by
  rw [finiteConductor_def, finprod_eq_prod_of_mulSupport_subset _
    χ.hasFiniteMulSupport_pow_conductorExponent.coe_toFinset.symm.subset, ← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
    pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)

/-- **The `v`-adic exponent of the finite conductor is the conductor exponent at `v`.** -/
@[simp]
theorem count_finiteConductor (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (Associates.mk v.asIdeal).count (Associates.mk χ.finiteConductor).factors =
      χ.conductorExponent v := by
  have hcoe : ((χ.finiteConductor : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 K),
        (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (χ.conductorExponent w : ℤ) := by
    rw [finiteConductor_def, FractionalIdeal.coeIdeal_finprod (nonZeroDivisors (𝓞 K)) K le_rfl]
    simp [FractionalIdeal.coeIdeal_pow]
  have h := FractionalIdeal.count_finprod K v (fun w ↦ (χ.conductorExponent w : ℤ))
    (χ.eventually_conductorExponent_eq_zero.mono fun w hw ↦ by simp [hw])
  rw [← hcoe, FractionalIdeal.count_coe K v (by
    rw [Ideal.zero_eq_bot]; exact χ.finiteConductor_ne_bot)] at h
  exact_mod_cast h

/-- **The characterizing property of the finite conductor**: `v ^ n` divides the finite conductor
exactly when `n` is at most the conductor exponent at `v`. -/
theorem pow_dvd_finiteConductor_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    v.asIdeal ^ n ∣ χ.finiteConductor ↔ n ≤ χ.conductorExponent v := by
  rw [← count_finiteConductor,
    HeightOneSpectrum.le_count_associates_iff_le_pow v χ.finiteConductor_ne_bot, Ideal.dvd_iff_le]

/-- **A prime divides the finite conductor exactly when `χ` is ramified there**, that is, when the
component of `χ` at `v` is nontrivial on the units of `𝓞_v`. -/
theorem dvd_finiteConductor_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ χ.finiteConductor ↔ χ.conductorExponent v ≠ 0 := by
  rw [← pow_one v.asIdeal, pow_dvd_finiteConductor_iff, Nat.one_le_iff_ne_zero]

/-- **The finite conductor is trivial exactly when `χ` is unramified at every finite place.** -/
theorem finiteConductor_eq_top_iff (χ : HeckeCharacter K) :
    χ.finiteConductor = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 K), χ.conductorExponent v = 0 := by
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · by_contra hv
    have hdvd : v.asIdeal ∣ ⊤ := h ▸ (χ.dvd_finiteConductor_iff v).mpr hv
    exact v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))
  · rw [finiteConductor_def, ← Ideal.one_eq_top]
    simp only [h, pow_zero, finprod_one]

/-- The trivial Hecke character has trivial finite conductor. -/
@[simp]
theorem finiteConductor_one : (1 : HeckeCharacter K).finiteConductor = ⊤ :=
  (finiteConductor_eq_top_iff 1).mpr conductorExponent_one

/-- A Hecke character and its inverse have the same finite conductor. -/
@[simp]
theorem finiteConductor_inv (χ : HeckeCharacter K) : χ⁻¹.finiteConductor = χ.finiteConductor := by
  simp [finiteConductor_def]

/-- The finite part of a Hecke character is trivial on the exact conductor filtration.
This controls arbitrary finite ideles, including their infinitely many local unit coordinates. -/
theorem finitePart_eq_one_of_forall_mem_unitFiltration (χ : HeckeCharacter K)
    (x : IdeleGroup (𝓞 K) K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K),
      v.ideleFiniteCoord x ∈ TauCeti.unitFiltration (v.adicCompletion K)
        (χ.conductorExponent v)) :
    χ (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 K) K
      (IdeleGroup.toFiniteIdele (𝓞 K) K x))) = 1 := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := χ.exists_modulus_finitePart_eq_one
  let z : IdeleGroup (𝓞 K) K :=
    ∏ v ∈ 𝔪.support, IdeleGroup.ofAdicCompletion (𝓞 K) K v (v.ideleFiniteCoord x)
  have hzχ : χ (QuotientGroup.mk z) = 1 := by
    rw [QuotientGroup.mk_prod, map_prod]
    exact Finset.prod_eq_one fun v _ ↦ χ.finiteComponent_eq_one_of_mem_unitFiltration (hx v)
  let y := IdeleGroup.ofFiniteIdele (𝓞 K) K
    (IdeleGroup.toFiniteIdele (𝓞 K) K x) * z⁻¹
  have hcoord (v : HeightOneSpectrum (𝓞 K)) :
      v.ideleFiniteCoord y = if v ∈ 𝔪.support then 1 else v.ideleFiniteCoord x := by
    have hfin : v.ideleFiniteCoord (IdeleGroup.ofFiniteIdele (𝓞 K) K
        (IdeleGroup.toFiniteIdele (𝓞 K) K x)) = v.ideleFiniteCoord x := by
      have h := congrArg v.ideleFiniteCoord (IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele x)
      simpa only [map_mul, map_prod, HeightOneSpectrum.ideleFiniteCoord_ofCompletion,
        Finset.prod_const_one, one_mul] using h
    simp only [y, map_mul, map_inv, hfin]
    have hzcoord : v.ideleFiniteCoord z =
        if v ∈ 𝔪.support then v.ideleFiniteCoord x else 1 :=
      HeightOneSpectrum.ideleFiniteCoord_prod_ofAdicCompletion v _ _
    rw [hzcoord]
    split_ifs <;> simp
  have hy : y ∈ ideleCongruenceSubgroup 𝔪 := by
    refine mem_ideleCongruenceSubgroup_iff.mpr ⟨fun v hv ↦ ?_, fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · rw [hcoord, ite_eq_right fun h ↦ hv ((Modulus.mem_support_iff 𝔪 v).mp h)]
      have hv := hx v
      rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff] at hv
      exact hv.1
    · rw [hcoord, ite_eq_left ((Modulus.mem_support_iff 𝔪 v).mpr hv)]
      simp
    · simp [y, z]
  have hyχ := h𝔪 y hy
  have hyfin : IdeleGroup.ofFiniteIdele (𝓞 K) K
      (IdeleGroup.toFiniteIdele (𝓞 K) K y) = y := by
    apply IdeleGroup.ext
    · intro w
      simp [y, z]
    · simp
  rw [hyfin] at hyχ
  dsimp only [y] at hyχ
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hzχ,
    inv_one, mul_one] at hyχ
  exact hyχ

/-! ### Agreement with the conductor of a finite-order character -/

/-- **A modulus from which `χ` comes bounds its conductor exponents**: if `χ` is the pullback of a
ray class character of `𝔫`, then `a_v(χ) ≤ 𝔫.exponent v` at every finite place `v`. -/
theorem conductorExponent_le_exponent_of_mem_range {χ : HeckeCharacter K} {𝔫 : Modulus K}
    (hχ : χ ∈ (ofRayClassCharacter 𝔫).range) (v : HeightOneSpectrum (𝓞 K)) :
    χ.conductorExponent v ≤ 𝔫.exponent v :=
  (χ.conductorExponent_le_iff v _).mpr fun _ hu ↦ by
    rw [finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply]
    exact MonoidHom.mem_ker.mp (mem_range_ofRayClassCharacter_iff.mp hχ (mem_raySubgroup_iff.mpr
      ⟨_, ofAdicCompletion_mem_ideleCongruenceSubgroup_iff.mpr hu, rfl⟩))

/-- **Lowering the finite exponents of a modulus to the conductor exponents.**  If `χ` is the
pullback of a ray class character of `𝔪`, then it is the pullback of a ray class character of
every modulus `𝔫` whose infinite part contains that of `𝔪` and whose exponent at every finite
place `v` is at least `a_v(χ)`. -/
theorem mem_range_ofRayClassCharacter_of_conductorExponent_le {χ : HeckeCharacter K}
    {𝔪 𝔫 : Modulus K} (hχ : χ ∈ (ofRayClassCharacter 𝔪).range)
    (hinf : 𝔪.infinitePart ⊆ 𝔫.infinitePart)
    (hexp : ∀ v : HeightOneSpectrum (𝓞 K), χ.conductorExponent v ≤ 𝔫.exponent v) :
    χ ∈ (ofRayClassCharacter 𝔫).range := by
  classical
  have h𝔪 := mem_range_ofRayClassCharacter_iff.mp hχ
  refine mem_range_ofRayClassCharacter_iff.mpr fun c hc ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
  have hfinite := χ.finitePart_eq_one_of_forall_mem_unitFiltration x fun v ↦
    TauCeti.unitFiltration_antitone (hexp v)
      (ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx v)
  let y := ∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (w.ideleInfiniteCoord x)
  have hsplit : y * IdeleGroup.ofFiniteIdele (𝓞 K) K
      (IdeleGroup.toFiniteIdele (𝓞 K) K x) = x :=
    IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele x
  have hycoord (w : InfinitePlace K) : w.ideleInfiniteCoord y = w.ideleInfiniteCoord x := by
    have h := congrArg w.ideleInfiniteCoord hsplit
    simpa only [map_mul, InfinitePlace.ideleInfiniteCoord_ofFiniteIdele, mul_one] using h
  have hy : y ∈ ideleCongruenceSubgroup 𝔪 := by
    refine mem_ideleCongruenceSubgroup_iff.mpr ⟨fun v _ ↦ ?_, fun v _ ↦ ?_, fun w hw ↦ ?_⟩
    · simp [y]
    · simp [y]
    · rw [hycoord]
      exact ideleCongruenceSubgroup.extensionEmbeddingOfIsReal_pos hx (hinf hw)
  have hyχ := MonoidHom.mem_ker.mp (h𝔪 (mem_raySubgroup_iff.mpr ⟨y, hy, rfl⟩))
  rw [MonoidHom.mem_ker, ← hsplit, map_mul, map_mul, hyχ, one_mul]
  exact hfinite

/-- **The finite exponents of the conductor of a finite-order Hecke character are its conductor
exponents.** -/
@[simp]
theorem exponent_conductor {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder)
    (v : HeightOneSpectrum (𝓞 K)) :
    (χ.conductor hχ).exponent v = χ.conductorExponent v := by
  refine le_antisymm ?_
    (conductorExponent_le_exponent_of_mem_range (mem_range_ofRayClassCharacter_conductor hχ) v)
  -- The modulus with finite part the finite conductor and the infinite part of the conductor.
  let 𝔫 : Modulus K := ⟨χ.finiteConductor, χ.finiteConductor_ne_bot, (χ.conductor hχ).infinitePart⟩
  have h𝔫 (v : HeightOneSpectrum (𝓞 K)) : 𝔫.exponent v = χ.conductorExponent v := by
    rw [Modulus.exponent_def]
    exact χ.count_finiteConductor v
  have hdvd : χ.conductor hχ ∣ 𝔫 := (conductor_dvd_iff hχ).mpr
    (mem_range_ofRayClassCharacter_of_conductorExponent_le
      (mem_range_ofRayClassCharacter_conductor hχ) subset_rfl fun v ↦ (h𝔫 v).ge)
  exact h𝔫 v ▸ Modulus.exponent_mono hdvd v

/-- **The finite part of the conductor of a finite-order Hecke character is its finite
conductor.** -/
@[simp]
theorem finitePart_conductor {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    (χ.conductor hχ).finitePart = χ.finiteConductor := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization (χ.conductor hχ).finitePart_ne_zero,
    finiteConductor_def]
  refine finprod_congr fun v ↦ ?_
  rw [HeightOneSpectrum.maxPowDividing, ← Modulus.exponent_def, exponent_conductor]

end HeckeCharacter

end TauCeti.GlobalNumberFields
