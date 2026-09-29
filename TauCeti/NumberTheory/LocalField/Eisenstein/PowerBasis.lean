/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Orthogonality
public import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# Valuations in an Eisenstein power basis of a local field

The first `e(L/K)` powers of a uniformizer of `L` occupy distinct congruence classes of the
additive valuation modulo `e(L/K)`.  Consequently, the valuation of an `𝒪[K]`-linear combination
of them is the minimum of its term valuations.  An integral generator satisfying an Eisenstein
polynomial is such a uniformizer, and its power basis has length `e(L/K)`.

## Main result

* `TauCeti.irreducible_of_eisenstein_adjoin_eq_top` shows that an integral generator satisfying
  an Eisenstein polynomial is a uniformizer.
* `TauCeti.inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top` and
  `TauCeti.ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top` record its characteristic
  total-ramification consequences.
* `TauCeti.addVal_sum_algebraMap_mul_pow_of_irreducible` computes the additive valuation of a
  linear combination of the first `e(L/K)` powers of a uniformizer of `L`.
* `TauCeti.addVal_sum_eisenstein_powerBasis` computes the additive valuation of a linear
  combination of powers of an Eisenstein integral generator.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 12.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

namespace TauCeti

private theorem eisenstein_adjoin_eq_top_data [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : Algebra.adjoin 𝒪[K] {ξ} = ⊤) :
    Irreducible ξ ∧ inertiaDegree K L = 1 ∧ ramificationIndex K L = f.natDegree := by
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have hassoc : Associated (minpoly 𝒪[K] ξ) f :=
    associated_minpoly_of_eisenstein_isRoot ξ f hf hroot
  have hnatDegree : (minpoly 𝒪[K] ξ).natDegree = f.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hassoc)
  have hdeg : 0 < f.natDegree := hnatDegree ▸ minpoly.natDegree_pos hint
  let pb : PowerBasis 𝒪[K] 𝒪[L] := PowerBasis.ofAdjoinEqTop' hint hgen
  have hpbdim : pb.dim = f.natDegree := by
    rw [PowerBasis.ofAdjoinEqTop'_dim hint hgen, hnatDegree]
  have hfc0 : Irreducible (f.coeff 0) := hf.irreducible_coeff_zero hdeg
  have hminc0 : Irreducible ((minpoly 𝒪[K] ξ).coeff 0) :=
    Associated.irreducible (hassoc.map Polynomial.constantCoeff).symm hfc0
  have hnormirr : Irreducible (Algebra.norm 𝒪[K] ξ) := by
    rw [← PowerBasis.ofAdjoinEqTop'_gen hint hgen,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simpa using
      (irreducible_units_mul ((-1 : 𝒪[K]ˣ) ^ (minpoly 𝒪[K] ξ).natDegree)).mpr hminc0
  have hξ0 : ξ ≠ 0 := by
    intro hξ
    apply hnormirr.ne_zero
    simp [hξ]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  obtain ⟨m, u, hξ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hξ0 hϖ
  have hξL : (ξ : L) ≠ 0 := fun h ↦ hξ0 (Subtype.ext h)
  have hϖL : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  let x : Lˣ := Units.mk0 (ξ : L) hξL
  have hx : x = Units.map (Subring.subtype 𝒪[L] : 𝒪[L] →* L) u *
      (Units.mk0 (ϖ : L) hϖL) ^ m := by
    apply Units.ext
    simpa [x] using congrArg ((↑·) : 𝒪[L] → L) hξ
  have hxval : (normalizedValuation L x).toAdd = (m : ℤ) := by
    rw [hx, map_mul, map_pow, normalizedValuation_integerUnits,
      normalizedValuation_irreducible hϖ, one_mul, toAdd_pow, toAdd_ofAdd,
      nsmul_eq_mul, mul_one]
  have hnormval : (normalizedValuation K (Algebra.normUnits K x)).toAdd = 1 := by
    have hnorm0 : ((Algebra.norm 𝒪[K] ξ : 𝒪[K]) : K) ≠ 0 :=
      fun h ↦ hnormirr.ne_zero (Subtype.ext h)
    have heq : Algebra.normUnits K x =
        Units.mk0 ((Algebra.norm 𝒪[K] ξ : 𝒪[K]) : K) hnorm0 := by
      apply Units.ext
      simp [x]
    rw [heq, normalizedValuation_irreducible hnormirr, toAdd_ofAdd]
  have hfm : inertiaDegree K L * m = 1 := by
    have h := toAdd_normalizedValuation_norm (K := K) x
    rw [hnormval, hxval] at h
    exact_mod_cast h.symm
  have hf_one : inertiaDegree K L = 1 := (mul_eq_one.mp hfm).1
  have hm_one : m = 1 := (mul_eq_one.mp hfm).2
  have hξirr : Irreducible ξ := by
    subst m
    exact Associated.irreducible ⟨u, by simpa [mul_comm] using hξ.symm⟩ hϖ
  have he_degree : ramificationIndex K L = f.natDegree := by
    have hef := ramificationIndex_mul_inertiaDegree (K := K) (L := L)
    rw [hf_one, mul_one, ← finrank_integerRing K L, PowerBasis.finrank pb, hpbdim] at hef
    exact hef
  exact ⟨hξirr, hf_one, he_degree⟩

/-- An integral generator satisfying an Eisenstein polynomial is a uniformizer of the extension
integer ring. -/
theorem irreducible_of_eisenstein_adjoin_eq_top [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : Algebra.adjoin 𝒪[K] {ξ} = ⊤) : Irreducible ξ :=
  (eisenstein_adjoin_eq_top_data f hf ξ hroot hgen).1

/-- An extension generated integrally by a root of an Eisenstein polynomial has inertia degree
one. -/
theorem inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : Algebra.adjoin 𝒪[K] {ξ} = ⊤) : inertiaDegree K L = 1 :=
  (eisenstein_adjoin_eq_top_data f hf ξ hroot hgen).2.1

/-- For an integral generator satisfying an Eisenstein polynomial, the ramification index is the
degree of that polynomial. -/
theorem ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top [Algebra K L]
    [ValuativeExtension K L] [Module.Finite K L]
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : Algebra.adjoin 𝒪[K] {ξ} = ⊤) : ramificationIndex K L = f.natDegree :=
  (eisenstein_adjoin_eq_top_data f hf ξ hroot hgen).2.2

/-- **Orthogonality of the powers of a uniformizer.** For a uniformizer `ϖ` of `L` and
coefficients `c i ∈ 𝒪[K]` indexed by `i < n ≤ e(L/K)`, the terms `c i * ϖ ^ i` have additive
valuations `e(L/K) v_K(c i) + i` in distinct classes modulo `e(L/K)`, so the additive valuation
of their sum is the least term valuation. -/
theorem addVal_sum_algebraMap_mul_pow_of_irreducible [Algebra K L] [ValuativeExtension K L]
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {n : ℕ} (hn : n ≤ ramificationIndex K L)
    (c : Fin n → 𝒪[K]) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ)) =
      ⨅ i, ramificationIndex K L • IsDiscreteValuationRing.addVal 𝒪[K] (c i) + (i : ℕ) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hterm (i : Fin n) :
      IsDiscreteValuationRing.addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ)) =
        ramificationIndex K L • IsDiscreteValuationRing.addVal 𝒪[K] (c i) + (i : ℕ) := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      addVal_algebraMap, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  have hdistinct : ∀ i j : Fin n, i ≠ j →
      algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ) ≠ 0 →
      algebraMap 𝒪[K] 𝒪[L] (c j) * ϖ ^ (j : ℕ) ≠ 0 →
      IsDiscreteValuationRing.addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (c i) * ϖ ^ (i : ℕ)) ≠
        IsDiscreteValuationRing.addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (c j) * ϖ ^ (j : ℕ)) := by
    intro i j hij hi0 hj0 hval
    have hci : c i ≠ 0 := by
      intro h
      apply hi0
      simp [h]
    have hcj : c j ≠ 0 := by
      intro h
      apply hj0
      simp [h]
    obtain ⟨ni, ui, hci'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hci hπ
    obtain ⟨nj, uj, hcj'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcj hπ
    rw [hterm, hterm, hci', hcj', IsDiscreteValuationRing.addVal_def' ui hπ ni,
      IsDiscreteValuationRing.addVal_def' uj hπ nj] at hval
    have hnat : ramificationIndex K L * ni + (i : ℕ) = ramificationIndex K L * nj + (j : ℕ) := by
      have hval' : ((ramificationIndex K L * ni + (i : ℕ) : ℕ) : ℕ∞) =
          ramificationIndex K L * nj + (j : ℕ) := by
        simpa [nsmul_eq_mul] using hval
      exact_mod_cast hval'
    have hmod := congrArg (fun m : ℕ ↦ m % ramificationIndex K L) hnat
    have hijval : (i : ℕ) = (j : ℕ) := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (i.isLt.trans_le hn),
        Nat.mod_eq_of_lt (j.isLt.trans_le hn)] using hmod
    exact hij (Fin.ext hijval)
  rw [IsDiscreteValuationRing.addVal_sum_eq_iInf_of_ne _ hdistinct]
  exact iInf_congr hterm

/-- The additive valuation of a linear combination in an Eisenstein power basis is the least
of its term valuations. -/
theorem addVal_sum_eisenstein_powerBasis [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L]
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : Algebra.adjoin 𝒪[K] {ξ} = ⊤) (c : Fin f.natDegree → 𝒪[K]) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ξ ^ (i : ℕ)) =
      ⨅ i, ramificationIndex K L • IsDiscreteValuationRing.addVal 𝒪[K] (c i) + (i : ℕ) :=
  addVal_sum_algebraMap_mul_pow_of_irreducible
    (irreducible_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen)
    (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen).ge c

end TauCeti
