/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Log
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.FormalGroup.BaseChange
import TauCeti.RingTheory.FormalGroup.Logarithm.Naturality

/-!
# Hazewinkel's logarithm

Fix a natural number `p` (in applications a prime) and a family `v = (v₁, v₂, …)` of elements of a
`ℚ`-algebra `K`. **Hazewinkel's logarithm coefficients** `mₙ = mₙ(v)` (`TauCeti.hazewinkelLogCoeff`)
are defined by `m₀ = 1` and, for `p ≠ 0` and `n ≥ 1`, the recursion

  `p mₙ = ∑_{0 ≤ i < n} mᵢ v_(n - i)^(pⁱ)`.

When `p > 1`, the power series `f(X) = ∑ₙ mₙ X^(pⁿ)` (`TauCeti.hazewinkelLog`) is a strict formal
coordinate, and
`F_v(X, Y) = f⁻¹(f(X) + f(Y))` (`TauCeti.hazewinkelFormalGroup`) is a commutative formal group law
with logarithm `f`. For `K = ℚ[v₁, v₂, …]` and `p` prime this is the formal group law of
Brown–Peterson theory written in Hazewinkel's generators, rationally: `BP_* ⊗ ℚ = ℚ[v₁, v₂, …]` with
logarithm `∑ mₙ X^(pⁿ)`. By Hazewinkel's functional equation lemma, applied through the second
recursion below, the coefficients of `F_v` then lie in `ℤ_(p)[v₁, v₂, …]`.

Unwinding the recursion, `mₙ` is the sum over all chains `0 = s₀ < s₁ < ⋯ < s_k = n` of
`∏ⱼ v_(sⱼ - sⱼ₋₁)^(p^(sⱼ₋₁)) / pᵏ`. The defining recursion splits off the last step of the chain;
splitting off the first step instead gives, for `p ≠ 0` and `n ≥ 1`,

  `p mₙ(v) = ∑_{1 ≤ i ≤ n} vᵢ m_(n - i)(v^(pⁱ))`,

where `v^(pⁱ)` is the family `(v₁^(pⁱ), v₂^(pⁱ), …)`
(`TauCeti.natCast_mul_hazewinkelLogCoeff_succ'`). This is the form in which `f` satisfies
Hazewinkel's functional equation `f(X) = X + ∑_{i ≥ 1} (vᵢ / p) (σⁱ f)(X^(pⁱ))` for the ring
endomorphism `σ` of `ℚ[v₁, v₂, …]` with `σ(vᵢ) = vᵢ^p`, since `σⁱ(mₙ(v)) = mₙ(v^(pⁱ))`
(`TauCeti.map_hazewinkelLogCoeff`).

Conversely, the recursion can be solved for `vₙ`, so the family `v` is determined by the
coefficients `mₙ`, and every family `(ℓₙ)` with `ℓ₀ = 1` is the family of Hazewinkel coefficients of
some `v`. Hence, when `p > 1`, the formal group laws over a `ℚ`-algebra whose logarithm has no terms
outside the degrees `pⁿ` are exactly the laws `F_v`, each for a unique `v`
(`TauCeti.existsUnique_eq_hazewinkelFormalGroup`). For `p` prime these are the `p`-typical formal
group laws over `K`, and this is the statement that `ℚ[v₁, v₂, …]` carries the universal
`p`-typical formal group law over `ℚ`-algebras.

The degrees `pⁿ` are distinct only when `p > 1`. The definition of `TauCeti.hazewinkelLog` takes
the coefficient of `X^k` to be `m_(log_p k)` when `k` is a power of `p` and `0` otherwise, so for
`p ≤ 1` (where the only such `k` is `1`) it is the coordinate `X`.

## Main definitions

* `TauCeti.hazewinkelLogCoeff`: Hazewinkel's logarithm coefficients `mₙ(v)`.
* `TauCeti.hazewinkelLog`: the strict formal coordinate `∑ₙ mₙ(v) X^(pⁿ)` (for `p > 1`).
* `TauCeti.hazewinkelFormalGroup`: the formal group law with logarithm `∑ₙ mₙ(v) X^(pⁿ)`
  (for `p > 1`).

## Main results

* `TauCeti.natCast_mul_hazewinkelLogCoeff_succ`: `p mₙ₊₁ = ∑_{i ≤ n} mᵢ v_(n + 1 - i)^(pⁱ)` for
  `p ≠ 0`.
* `TauCeti.natCast_mul_hazewinkelLogCoeff_succ'`:
  `p mₙ₊₁(v) = ∑_{i ≤ n} vᵢ₊₁ m_(n - i)(v^(p^(i + 1)))` for `p ≠ 0`.
* `TauCeti.map_hazewinkelLogCoeff`, `TauCeti.map_hazewinkelLog`,
  `TauCeti.map_hazewinkelFormalGroup`: compatibility with ring homomorphisms.
* `TauCeti.hazewinkelLogCoeff_injective`, `TauCeti.exists_hazewinkelLogCoeff_eq`: the coefficients
  `mₙ` determine `v`, and every family `ℓ` with `ℓ₀ = 1` occurs.
* `TauCeti.log_hazewinkelFormalGroup`: the logarithm of `F_v` is Hazewinkel's logarithm `f`.
* `TauCeti.eq_hazewinkelFormalGroup_iff`: a formal group law is `F_v` exactly when its logarithm is
  `f`.
* `TauCeti.existsUnique_eq_hazewinkelFormalGroup`: a formal group law whose logarithm is supported
  in the degrees `pⁿ` is `F_v` for a unique `v`.

## References

* M. Hazewinkel, *Constructing formal groups. I. The local one dimensional case*, J. Pure Appl.
  Algebra 9 (1977), 131–149.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978].
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Section 4.1 and
  Appendix A2.1.
-/

public section

open PowerSeries Finset

namespace TauCeti

variable {K L : Type*} [CommRing K] [Algebra ℚ K] [CommRing L] [Algebra ℚ L]

/-! ### The logarithm coefficients -/

variable (p : ℕ) in
/-- **Hazewinkel's logarithm coefficients** `mₙ(v)` of a family `v = (v₁, v₂, …)`: `m₀ = 1` and
`mₙ₊₁ = p⁻¹ ∑_{i ≤ n} mᵢ v_(n + 1 - i)^(pⁱ)`. -/
noncomputable def hazewinkelLogCoeff (v : ℕ+ → K) : ℕ → K
  | 0 => 1
  | n + 1 => (p : ℚ)⁻¹ • ∑ i : Fin (n + 1),
      hazewinkelLogCoeff v i * v (n - i).succPNat ^ p ^ (i : ℕ)

variable {p : ℕ} (v : ℕ+ → K)

@[simp]
theorem hazewinkelLogCoeff_zero : hazewinkelLogCoeff p v 0 = 1 := by
  rw [hazewinkelLogCoeff]

/-- The defining recursion `mₙ₊₁ = p⁻¹ ∑_{i ≤ n} mᵢ v_(n + 1 - i)^(pⁱ)`, as a sum over a range. -/
theorem hazewinkelLogCoeff_succ (n : ℕ) :
    hazewinkelLogCoeff p v (n + 1) = (p : ℚ)⁻¹ • ∑ i ∈ range (n + 1),
      hazewinkelLogCoeff p v i * v (n - i).succPNat ^ p ^ i := by
  rw [hazewinkelLogCoeff, Fin.sum_univ_eq_sum_range
    (fun i ↦ hazewinkelLogCoeff p v i * v (n - i).succPNat ^ p ^ i)]

@[simp]
theorem hazewinkelLogCoeff_one : hazewinkelLogCoeff p v 1 = (p : ℚ)⁻¹ • v 1 := by
  simp [hazewinkelLogCoeff_succ, show Nat.succPNat 0 = 1 from PNat.eq (Nat.succPNat_coe 0)]

/-- **The recursion for Hazewinkel's logarithm coefficients**:
`p mₙ₊₁ = ∑_{i ≤ n} mᵢ v_(n + 1 - i)^(pⁱ)`. -/
theorem natCast_mul_hazewinkelLogCoeff_succ (hp : p ≠ 0) (n : ℕ) :
    (p : K) * hazewinkelLogCoeff p v (n + 1) = ∑ i ∈ range (n + 1),
      hazewinkelLogCoeff p v i * v (n - i).succPNat ^ p ^ i := by
  rw [hazewinkelLogCoeff_succ, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
    ← eq_inv_smul_iff₀ (Nat.cast_ne_zero.2 hp)]

/-- In `p mₙ₊₁ = ∑ᵢ mᵢ v_(n + 1 - i)^(pⁱ)` the term `i = 0` is `vₙ₊₁`, and the other terms only
involve `v₁, …, vₙ`. -/
private theorem natCast_mul_hazewinkelLogCoeff_succ_eq_add (hp : p ≠ 0) (n : ℕ) :
    (p : K) * hazewinkelLogCoeff p v (n + 1) = v n.succPNat + ∑ i ∈ range n,
      hazewinkelLogCoeff p v (i + 1) * v (n - (i + 1)).succPNat ^ p ^ (i + 1) := by
  rw [natCast_mul_hazewinkelLogCoeff_succ v hp, sum_range_succ', add_comm]
  simp

/-- Hazewinkel's logarithm coefficients commute with ring homomorphisms of `ℚ`-algebras. -/
@[simp]
theorem map_hazewinkelLogCoeff (φ : K →+* L) (n : ℕ) :
    φ (hazewinkelLogCoeff p v n) = hazewinkelLogCoeff p (φ ∘ v) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp
    · rw [hazewinkelLogCoeff_succ, hazewinkelLogCoeff_succ, map_rat_smul, map_sum]
      refine congrArg _ (sum_congr rfl fun i hi ↦ ?_)
      rw [map_mul, map_pow, ih i (by grind), Function.comp_apply]

/-- Applying the `i`-th iterate of a coefficient Frobenius lift to a logarithm
coefficient replaces each generator by its `pⁱ`-th power. -/
theorem pow_apply_hazewinkelLogCoeff (σ : K →+* K) (hσ : ∀ j, σ (v j) = v j ^ p)
    (i n : ℕ) :
    (σ ^ i) (hazewinkelLogCoeff p v n) =
      hazewinkelLogCoeff p (fun j ↦ v j ^ p ^ i) n := by
  rw [map_hazewinkelLogCoeff]
  congr 1
  funext j
  simp only [Function.comp_apply]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, map_pow, hσ,
      ← pow_mul, ← pow_succ']

/-- **Hazewinkel's recursion**: `p mₙ₊₁(v) = ∑_{i ≤ n} vᵢ₊₁ m_(n - i)(v^(p^(i + 1)))`, where
`v^(pʲ)` is the family `(v₁^(pʲ), v₂^(pʲ), …)`. This splits off the first step of the chains
`0 = s₀ < ⋯ < s_k = n + 1` indexing the terms of `mₙ₊₁`, while
`TauCeti.natCast_mul_hazewinkelLogCoeff_succ` splits off the last one. -/
theorem natCast_mul_hazewinkelLogCoeff_succ' (hp : p ≠ 0) (n : ℕ) :
    (p : K) * hazewinkelLogCoeff p v (n + 1) = ∑ i ∈ range (n + 1),
      v i.succPNat * hazewinkelLogCoeff p (fun j ↦ v j ^ p ^ (i + 1)) (n - i) := by
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    rw [natCast_mul_hazewinkelLogCoeff_succ v hp, sum_range_succ', sum_range_succ]
    simp only [hazewinkelLogCoeff_zero, Nat.sub_zero, pow_zero, pow_one, one_mul, Nat.sub_self,
      mul_one]
    congr 1
    -- both sides are the sum of `f j l` over the pairs `j + l < n`
    set f : ℕ → ℕ → K := fun j l ↦ (p : ℚ)⁻¹ • (v j.succPNat *
      hazewinkelLogCoeff p (fun i ↦ v i ^ p ^ (j + 1)) l *
      v (n - 1 - (j + l)).succPNat ^ p ^ (j + 1 + l))
    have hl : ∀ k ∈ range n, hazewinkelLogCoeff p v (k + 1) * v (n - (k + 1)).succPNat ^ p ^ (k + 1)
        = ∑ j ∈ range (k + 1), f j (k - j) := by
      intro k hk
      -- `mₖ₊₁ = p⁻¹ (p mₖ₊₁)`, and the induction hypothesis expands `p mₖ₊₁`
      rw [← inv_natCast_smul_natCast_mul hp (hazewinkelLogCoeff p v (k + 1)),
        ih k (mem_range.1 hk) v]
      simp only [smul_mul_assoc, sum_mul, smul_sum]
      refine sum_congr rfl fun j hj ↦ ?_
      have hjk : j + (k - j) = k := by grind
      simp only [f, hjk, show j + 1 + (k - j) = k + 1 by omega,
        show n - 1 - k = n - (k + 1) by omega]
    have hr : ∀ j ∈ range n, v j.succPNat * hazewinkelLogCoeff p (fun i ↦ v i ^ p ^ (j + 1)) (n - j)
        = ∑ l ∈ range (n - j), f j l := by
      intro j hj
      -- expand `m_(n - j)` by its defining recursion
      obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by grind⟩
      rw [hm, hazewinkelLogCoeff_succ]
      simp only [mul_smul_comm, mul_sum, smul_sum]
      refine sum_congr rfl fun l hl ↦ ?_
      simp only [f, ← pow_mul, ← pow_add, mul_assoc,
        show m - l = n - 1 - (j + l) by omega]
    rw [sum_congr rfl hl, sum_congr rfl hr, sum_range_diag_flip]

/-- **The logarithm coefficients determine the family**: if `p ≠ 0`, then `v` is determined by
Hazewinkel's logarithm coefficients `mₙ(v)`. -/
theorem hazewinkelLogCoeff_injective (hp : p ≠ 0) :
    Function.Injective (hazewinkelLogCoeff p : (ℕ+ → K) → ℕ → K) := by
  intro v w h
  -- `vₙ₊₁ = p mₙ₊₁ - ∑ᵢ mᵢ₊₁ v_(n - i)^(p^(i + 1))` is determined by the `mᵢ` and `v₁, …, vₙ`
  have key : ∀ n : ℕ, v n.succPNat = w n.succPNat := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hv := natCast_mul_hazewinkelLogCoeff_succ_eq_add v hp n
      rw [h, sum_congr rfl fun i hi ↦ by rw [ih _ (by grind)]] at hv
      exact add_right_cancel (hv.symm.trans (natCast_mul_hazewinkelLogCoeff_succ_eq_add w hp n))
  funext j
  simpa using key j.natPred

variable (p) in
/-- The family `v` with prescribed Hazewinkel logarithm coefficients `ℓ`, indexed from `0`: by
`natCast_mul_hazewinkelLogCoeff_succ_eq_add`, `vₙ₊₁` is
`p ℓₙ₊₁ - ∑_(i < n) ℓᵢ₊₁ v_(n - i)^(p^(i + 1))`. -/
private noncomputable def coeffsOfHazewinkelLogCoeff (ℓ : ℕ → K) : ℕ → K
  | n => p * ℓ (n + 1) - ∑ i : Fin n,
      ℓ (i + 1) * coeffsOfHazewinkelLogCoeff ℓ (n - (i + 1)) ^ p ^ ((i : ℕ) + 1)
decreasing_by have := i.isLt; omega

/-- **Every normalised family is a family of logarithm coefficients**: if `p ≠ 0` and `ℓ₀ = 1`,
then `ℓ` is the family of Hazewinkel logarithm coefficients of some `v`. -/
theorem exists_hazewinkelLogCoeff_eq (hp : p ≠ 0) {ℓ : ℕ → K} (h₀ : ℓ 0 = 1) :
    ∃ v : ℕ+ → K, hazewinkelLogCoeff p v = ℓ := by
  set v : ℕ+ → K := fun j ↦ coeffsOfHazewinkelLogCoeff p ℓ j.natPred
  have hv (n : ℕ) : v n.succPNat = p * ℓ (n + 1) -
      ∑ i ∈ range n, ℓ (i + 1) * v (n - (i + 1)).succPNat ^ p ^ (i + 1) := by
    simp only [v, Nat.natPred_succPNat]
    rw [coeffsOfHazewinkelLogCoeff, Fin.sum_univ_eq_sum_range
      (fun i ↦ ℓ (i + 1) * coeffsOfHazewinkelLogCoeff p ℓ (n - (i + 1)) ^ p ^ (i + 1))]
  refine ⟨v, funext fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [hazewinkelLogCoeff_zero, h₀]
    · have h := natCast_mul_hazewinkelLogCoeff_succ_eq_add v hp n
      rw [sum_congr rfl fun i hi ↦ by rw [ih (i + 1) (by grind)], hv, sub_add_cancel] at h
      simp only [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ] at h
      exact smul_right_injective K (Nat.cast_ne_zero.2 hp : (p : ℚ) ≠ 0) h

/-! ### The logarithm and the formal group law -/

variable (p) in
/-- **Hazewinkel's logarithm**, a strict formal coordinate: for `p > 1` it is `∑ₙ mₙ(v) X^(pⁿ)`.
In general its coefficient of `X^k` is `m_(log_p k)(v)` if `k` is a power of `p` and `0` otherwise,
so for `p ≤ 1` it is `X`. -/
noncomputable def hazewinkelLog : FormalCoordinate K where
  toPowerSeries := PowerSeries.mk fun k ↦
    if p ^ Nat.log p k = k then hazewinkelLogCoeff p v (Nat.log p k) else 0
  constantCoeff_toPowerSeries := by
    simp [← coeff_zero_eq_constantCoeff_apply]
  isUnit_coeff_one := by simp

/-- The coefficient of `X^(pⁿ)` in Hazewinkel's logarithm is `mₙ(v)`. -/
@[simp]
theorem coeff_hazewinkelLog_pow (hp : 1 < p) (n : ℕ) :
    coeff (p ^ n) (hazewinkelLog p v).toPowerSeries = hazewinkelLogCoeff p v n := by
  simp [hazewinkelLog, Nat.log_pow hp]

/-- Hazewinkel's logarithm has no terms outside the degrees `pⁿ`. -/
@[simp]
theorem coeff_hazewinkelLog_eq_zero {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    coeff k (hazewinkelLog p v).toPowerSeries = 0 := by
  simp [hazewinkelLog, hk]

@[simp]
theorem coeff_one_hazewinkelLog : coeff 1 (hazewinkelLog p v).toPowerSeries = 1 := by
  simp [hazewinkelLog]

@[simp]
theorem linearCoeff_hazewinkelLog : FormalCoordinate.linearCoeff (hazewinkelLog p v) = 1 :=
  Units.ext (by simp)

/-- Hazewinkel's logarithm commutes with ring homomorphisms of `ℚ`-algebras. -/
@[simp]
theorem map_hazewinkelLog (φ : K →+* L) :
    FormalCoordinate.map φ (hazewinkelLog p v) = hazewinkelLog p (φ ∘ v) := by
  ext k
  simp only [FormalCoordinate.toPowerSeries_map, coeff_map, hazewinkelLog, coeff_mk]
  split_ifs <;> simp [map_hazewinkelLogCoeff]

variable (p) in
/-- **Hazewinkel's formal group law** `F_v(X, Y) = f⁻¹(f(X) + f(Y))`, where `f` is Hazewinkel's
logarithm `TauCeti.hazewinkelLog` (`∑ₙ mₙ(v) X^(pⁿ)` for `p > 1`). -/
noncomputable def hazewinkelFormalGroup : FormalGroup K :=
  (hazewinkelLog p v)⁻¹ • FormalGroup.𝔾ₐ

/-- Hazewinkel's formal group is the additive law transported by the inverse logarithm. -/
theorem hazewinkelFormalGroup_def :
    hazewinkelFormalGroup p v = (hazewinkelLog p v)⁻¹ • FormalGroup.𝔾ₐ := (rfl)

instance : (hazewinkelFormalGroup p v).IsComm :=
  FormalGroup.instIsCommSMul _ _

/-- The logarithm of Hazewinkel's formal group law is Hazewinkel's logarithm. -/
@[simp]
theorem log_hazewinkelFormalGroup :
    (hazewinkelFormalGroup p v).log = (hazewinkelLog p v).toPowerSeries := by
  rw [hazewinkelFormalGroup, FormalGroup.log_smul, FormalGroup.log_𝔾ₐ, inv_inv,
    subst_X (hazewinkelLog p v).hasSubst]
  simp

/-- A formal group law over a `ℚ`-algebra is Hazewinkel's formal group law of `v` exactly when its
logarithm is Hazewinkel's logarithm of `v`. -/
theorem eq_hazewinkelFormalGroup_iff {F : FormalGroup K} :
    F = hazewinkelFormalGroup p v ↔ F.log = (hazewinkelLog p v).toPowerSeries := by
  refine ⟨fun h ↦ h ▸ log_hazewinkelFormalGroup v, fun h ↦ ?_⟩
  rw [hazewinkelFormalGroup, ← F.logHom.smul_eq (by rw [FormalGroup.logHom_toPowerSeries, h]),
    inv_smul_smul]

/-- Hazewinkel's formal group law commutes with ring homomorphisms of `ℚ`-algebras. -/
@[simp]
theorem map_hazewinkelFormalGroup (φ : K →+* L) :
    (hazewinkelFormalGroup p v).map φ = hazewinkelFormalGroup p (φ ∘ v) := by
  rw [hazewinkelFormalGroup, FormalGroup.map_smul, map_inv, map_hazewinkelLog,
    FormalGroup.map_𝔾ₐ, hazewinkelFormalGroup]

/-- Hazewinkel's formal group law determines the family `v`. -/
theorem hazewinkelFormalGroup_injective (hp : 1 < p) :
    Function.Injective (hazewinkelFormalGroup p : (ℕ+ → K) → FormalGroup K) := by
  intro v w h
  have h' : (hazewinkelLog p v).toPowerSeries = (hazewinkelLog p w).toPowerSeries := by
    rw [← log_hazewinkelFormalGroup, ← log_hazewinkelFormalGroup, h]
  exact hazewinkelLogCoeff_injective (p := p) (by omega) <| funext fun n ↦ by
    rw [← coeff_hazewinkelLog_pow v hp, h', coeff_hazewinkelLog_pow w hp]

/-- **Universality of Hazewinkel's formal group law over `ℚ`-algebras**: a formal group law over a
`ℚ`-algebra whose logarithm has no terms outside the degrees `pⁿ` is Hazewinkel's formal group law
of a unique family `v`. -/
theorem existsUnique_eq_hazewinkelFormalGroup (hp : 1 < p) {F : FormalGroup K}
    (hF : ∀ k, (∀ n, p ^ n ≠ k) → coeff k F.log = 0) :
    ∃! v : ℕ+ → K, F = hazewinkelFormalGroup p v := by
  obtain ⟨v, hv⟩ := exists_hazewinkelLogCoeff_eq (p := p) (ℓ := fun n ↦ coeff (p ^ n) F.log)
    (by omega) (by simp [FormalGroup.coeff_one_log])
  have hFv : F = hazewinkelFormalGroup p v := by
    refine (eq_hazewinkelFormalGroup_iff v).2 (PowerSeries.ext fun k ↦ ?_)
    by_cases hk : ∃ n, p ^ n = k
    · obtain ⟨n, rfl⟩ := hk
      rw [coeff_hazewinkelLog_pow v hp, hv]
    · push Not at hk
      rw [hF k hk, coeff_hazewinkelLog_eq_zero v hk]
  exact ⟨v, hFv, fun w hw ↦ hazewinkelFormalGroup_injective hp (hw.symm.trans hFv)⟩

end TauCeti
