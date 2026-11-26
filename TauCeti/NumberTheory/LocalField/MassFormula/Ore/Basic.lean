/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.RingTheory.Polynomial.Eisenstein.Ore
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Valuation.ValuationRing
import TauCeti.NumberTheory.LocalField.NatCastValuation
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# Ore's realizability theorem for totally ramified extensions of local fields

Let `K` be a nonarchimedean local field and let `σ_K(n) = totallyRamifiedOfDegree K n` be the set
of totally ramified degree-`n` subextensions of `SeparableClosure K`. For `L ∈ σ_K(n)` with
discriminant exponent `d(L)`, the wild exponent is `c(L) = d(L) - n + 1`. Building on the general
DVR Ore conditions (`TauCeti.IsOreAdmissible 𝒪[K] n j` and `TauCeti.oreCoefficientDepth 𝒪[K] n j h`)
in `TauCeti.RingTheory.Polynomial.Eisenstein.Ore`, this module connects Ore admissibility to the
wild exponents of extensions in `σ_K(n)`.

## Main results

* `TauCeti.oreCoefficientDepth_of_natCast_ne_zero`: expression for `oreCoefficientDepth 𝒪[K] n j h`
  in terms of `natCastValuation K h hh`.
* `TauCeti.wildExponent_adjoin_eq_iff_of_eisenstein`: valuation criterion on Eisenstein
  coefficients for a root to generate an extension of wild exponent `j`.
* `TauCeti.exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff`,
  `TauCeti.setOf_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_empty_iff`: Ore's realizability
  theorem characterizing when `j` arises as the wild exponent of some `E ∈ σ_K(n)`.

## References

* Ø. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928),
  84–117.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, Colloques
  Internationaux du CNRS **143**, Paris, 1966, 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 1°.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter III, §6, Proposition 13.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped IntermediateField

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff natDegree_monicOfCoeff)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/-- When `(h : K) ≠ 0`, `oreCoefficientDepth 𝒪[K]` is expressed in terms of `natCastValuation`. -/
theorem oreCoefficientDepth_of_natCast_ne_zero (n j : ℕ) {h : ℕ} (hh : (h : K) ≠ 0) :
    oreCoefficientDepth 𝒪[K] n j h =
      max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh) := by
  rw [oreCoefficientDepth_def, TauCeti.IsDiscreteValuationRing.addVal_natCast K h hh,
    ← ENat.natCast_sub, ENat.toNat_natCast]

/-- **The Eisenstein derivative criterion for wild exponents.** Let `x : SeparableClosure K` be a
root of an Eisenstein polynomial `f : 𝒪[K][X]` of degree `n`. Then `K⟮x⟯` has wild exponent `j` if
and only if `IsOreAdmissible 𝒪[K] n j` holds, every lower coefficient `f.coeff h` (`1 ≤ h < n`) has
valuation at least `oreCoefficientDepth 𝒪[K] n j h`, and when `0 < j % n` the coefficient
`f.coeff (j % n)` has valuation equal to `oreCoefficientDepth 𝒪[K] n j (j % n)`. -/
theorem wildExponent_adjoin_eq_iff_of_eisenstein {n j : ℕ} {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) {x : SeparableClosure K}
    (hx : aeval x (f.map (algebraMap 𝒪[K] K)) = 0) :
    (K⟮x⟯).wildExponent = j ↔
      IsOreAdmissible 𝒪[K] n j ∧
        (∀ h, 1 ≤ h → h < n → (oreCoefficientDepth 𝒪[K] n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h)) ∧
        (0 < j % n → addVal 𝒪[K] (f.coeff (j % n)) = oreCoefficientDepth 𝒪[K] n j (j % n)) := by
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hf hdeg hx
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0, totallyRamifiedOfDegree_zero] at hmem
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein hf hx
  have hrel := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  have hshift :
      (((K⟮x⟯).wildExponent + n : ℕ) : ℕ∞) =
        ⨅ i : Fin f.natDegree,
          (f.natDegree • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + ((i : ℕ) + 1 : ℕ∞)) := by
    rw [hrel, Nat.cast_add, Nat.cast_one, hd, ENat.iInf_add]
    simp_rw [add_assoc]
  subst hdeg
  rw [← iInf_addVal_derivative_add_one_eq_iff hn hf rfl, eq_comm, ← hshift]
  norm_cast
  omega

/-- **Ore's realizability theorem**: for every nonarchimedean local field `K` (in either
characteristic) and all `n, j : ℕ`, some totally ramified extension `E ∈ σ_K(n)` inside
`SeparableClosure K` has wild exponent `j` if and only if `IsOreAdmissible 𝒪[K] n j`. -/
theorem exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff {n j : ℕ} :
    (∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j) ↔ IsOreAdmissible 𝒪[K] n j := by
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨f, x, -, hf, hdeg, hx, rfl⟩ :=
      exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hE
    exact ((wildExponent_adjoin_eq_iff_of_eisenstein hf hdeg hx).mp rfl).1
  · intro hadm
    have hn : 0 < n := hadm.pos
    obtain ⟨c, hf, hcoeff, hcrit⟩ := hadm.exists_monic_isEisensteinAt
    let f : 𝒪[K][X] := monicOfCoeff c
    have hdeg : f.natDegree = n := natDegree_monicOfCoeff c
    have hsep : (f.map (algebraMap 𝒪[K] K)).Separable :=
      hadm.separable_map_of_isEisensteinAt hf hdeg hcoeff hcrit
    have hdeg_pos : (f.map (algebraMap 𝒪[K] K)).degree ≠ 0 :=
      (natDegree_pos_iff_degree_pos.mp (by
        rw [natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hdeg]
        exact hn)).ne'
    obtain ⟨x, hxf⟩ := IsSepClosed.exists_aeval_eq_zero (SeparableClosure K) _ hdeg_pos hsep
    exact ⟨K⟮x⟯, adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hf hdeg hxf,
      (wildExponent_adjoin_eq_iff_of_eisenstein hf hdeg hxf).mpr ⟨hadm, hcoeff, hcrit⟩⟩

/-- A wild-exponent stratum `{E ∈ σ_K(n) | E.wildExponent = j}` is empty if and only if `(n, j)` is
not Ore-admissible. -/
theorem setOf_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_empty_iff {n j : ℕ} :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ ↔ ¬ IsOreAdmissible 𝒪[K] n j := by
  rw [Set.eq_empty_iff_forall_notMem]
  simpa [not_exists] using (exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff (K := K)).not

end TauCeti
