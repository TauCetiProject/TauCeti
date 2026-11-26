/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Frobenius
public import TauCeti.RingTheory.WittVector.Primitive.Basic
public import TauCeti.RingTheory.WittVector.Regular
-- Proof-only: `ε ^ (1 / p) - 1` is a `p`-th root of `ε - 1`.
import TauCeti.RingTheory.Perfect.Basic

/-!
# Cyclotomic period elements of Witt vectors

Let `S` be a perfect ring of characteristic `p`, so that the Witt vector Frobenius `φ` of `W(S)`
is an automorphism, and let `ε ∈ S`. Write `[-]` for Teichmüller representatives. This file
defines the cyclotomic period elements

* `μ = [ε] - 1` (`TauCeti.WittVector.cyclotomicMu`),
* `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` (`TauCeti.WittVector.cyclotomicXi`),
* `ξ' = φ(ξ) = ∑_{j < p} [ε] ^ j` (`TauCeti.WittVector.cyclotomicXiTilde`; usually written `ξ`
  with a tilde),
* `ξ_r = ∏_{j < r} φ⁻ʲ(ξ)` (`TauCeti.WittVector.cyclotomicXiLevel`) and
* `ξ'_r = φʳ(ξ_r) = ∏_{j < r} φʲ(ξ')` (`TauCeti.WittVector.cyclotomicXiTildeLevel`).

In the main example `S = O_C^♭` is the tilt of the ring of integers of a complete algebraically
closed extension `C` of `ℚ_p`, `W(S) = A_inf`, and `ε = (1, ζ_p, ζ_{p²}, …)` is a compatible system
of primitive `p`-power roots of unity; then `ξ` generates the kernel of Fontaine's map
`θ : A_inf → O_C` and `ξ'` the kernel of `θ ∘ φ⁻¹`
(`TauCeti.WittVector.ker_fontaineTheta_eq_span_cyclotomicXi`), while the finite Frobenius products
`ξ_r = ∏_{j < r} φ⁻ʲ(ξ)` generate the kernels of the specialization maps `θ_r : A_inf → W_r(O_C)`
and satisfy `⋂_{r ≥ 1} (ξ_r) = (μ)`.

The elements are natural in `S`: a ring homomorphism `f : S →+* T` sends them, under
`WittVector.map f`, to the elements formed from `f ε` (for `ξ`, `ξ'`, `ξ_r`, `ξ'_r` when `T` is
perfect too). At `ε = 1` they are `0`, `p`, `p`, `p^r`, and `p^r`. Hence if `f ε = 1`, then
`W(f)` kills `μ` and sends `ξ'` and `ξ'_r` to `p` and `p^r`, and also `ξ` and `ξ_r` when `T` is
reduced. In the main example `f` is the residue map `O_C^♭ → k` to the residue field and
`W(f) : A_inf → W(k)` is the specialization to the crystalline special fibre; unlike Fontaine's map,
it sends `ξ` to `p` rather than to `0`.

The geometric sum identity gives the factorisations `μ = ξ · φ⁻¹(μ)`, `φ(μ) = ξ' · μ`, and more
generally `μ = ξ_r · φ⁻ʳ(μ)` and `φʳ(μ) = ξ'_r · μ` in `W(S)`, without any division. If `ε - 1`
lies in the Jacobson radical of `S`, then modulo the Jacobson radical `ξ` becomes `p`, so `ξ` and
`ξ'` are distinguished: their first Witt coordinates are units. Note that `ξ_r` and `ξ'_r` are not
distinguished for `r ≥ 2`, since their `coeff 1` vanishes modulo the Jacobson radical; nevertheless,
whenever `ε - 1 ∈ S⁰`, their zeroth Witt coordinates lie in `S⁰`, making all of `μ`, `ξ`, `ξ'`,
`ξ_r`, and `ξ'_r` nonzerodivisors with `p`-torsion-free quotients and regular sequences with `p`
when `ε - 1 ∈ Ring.jacobson S` and `Nontrivial S`.

## Main definitions

* `TauCeti.WittVector.cyclotomicMu`, `TauCeti.WittVector.cyclotomicXi`,
  `TauCeti.WittVector.cyclotomicXiTilde`: the elements `μ`, `ξ` and `ξ'` of `W(S)`.
* `TauCeti.WittVector.cyclotomicXiLevel`, `TauCeti.WittVector.cyclotomicXiTildeLevel`: the
  finite Frobenius products `ξ_r` and `ξ'_r` in `W(S)`.

## Main results

* `TauCeti.WittVector.map_cyclotomicMu`, `TauCeti.WittVector.map_cyclotomicXi`,
  `TauCeti.WittVector.map_cyclotomicXiTilde`: naturality of `μ`, `ξ` and `ξ'`.
* `TauCeti.WittVector.map_cyclotomicXi_eq_natCast`,
  `TauCeti.WittVector.map_cyclotomicXiTilde_eq_natCast`: if `f ε = 1`, then `W(f)` sends `ξ` (for
  reduced `T`) and `ξ'` to `p`.
* `TauCeti.WittVector.cyclotomicMu_eq_cyclotomicXi_mul`: `μ = ξ · φ⁻¹(μ)`.
* `TauCeti.WittVector.frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul`: `φ(μ) = ξ' · μ`.
* `TauCeti.WittVector.cyclotomicXiTilde_eq_sum`: `ξ' = ∑_{j < p} [ε] ^ j`.
* `TauCeti.WittVector.frobeniusEquiv_symm_cyclotomicXi`,
  `TauCeti.WittVector.frobenius_cyclotomicXi`,
  `TauCeti.WittVector.cyclotomicXiTilde_eq_cyclotomicXi_pow`: `φ⁻¹(ξ(ε)) = ξ(ε ^ (1 / p))`,
  `φ(ξ) = ξ'` and `ξ'(ε) = ξ(ε ^ p)`.
* `TauCeti.WittVector.cyclotomicMu_eq_cyclotomicXiLevel_mul`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul`:
  `μ = ξ_r · φ⁻ʳ(μ)` and `φʳ(μ) = ξ'_r · μ`.
* `TauCeti.WittVector.isDistinguished_cyclotomicXi`,
  `TauCeti.WittVector.isDistinguished_cyclotomicXiTilde`: if `ε - 1` lies in the Jacobson radical
  of `S`, then `ξ` and `ξ'` are distinguished.
* Regularity lemmas (`mem_nonZeroDivisors`, `isSMulRegular_quotient_natCast`, `isRegular_pair`)
  for `cyclotomicMu`, `cyclotomicXi`, `cyclotomicXiTilde`, `cyclotomicXiLevel`, and
  `cyclotomicXiTildeLevel`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Example 3.16 and
  Proposition 3.17.
-/

public section

open _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

namespace TauCeti.WittVector

variable (p : ℕ) [hp : Fact p.Prime] {S T : Type*} [CommRing S] [CommRing T]

local notation "𝕎" => _root_.WittVector p

/-- The cyclotomic period element `μ = [ε] - 1` of `W(S)`. -/
noncomputable def cyclotomicMu (ε : S) : 𝕎 S :=
  teichmuller p ε - 1

theorem cyclotomicMu_def (ε : S) : cyclotomicMu p ε = teichmuller p ε - 1 := (rfl)

/-- For `ε = 1`, the period element `μ = [ε] - 1` vanishes. -/
@[simp]
theorem cyclotomicMu_one : cyclotomicMu p (1 : S) = 0 := by
  simp [cyclotomicMu_def]

/-- The period element `μ` is natural: `W(f)` sends `μ(ε) = [ε] - 1` to `μ(f ε) = [f ε] - 1`. -/
@[simp]
theorem map_cyclotomicMu (f : S →+* T) (ε : S) :
    map f (cyclotomicMu p ε) = cyclotomicMu p (f ε) := by
  simp [cyclotomicMu_def, map_teichmuller]

/-- In characteristic `p`, the Frobenius of `μ(ε) = [ε] - 1` is `μ(ε ^ p) = [ε ^ p] - 1`. -/
@[simp]
theorem frobenius_cyclotomicMu [CharP S p] (ε : S) :
    frobenius (cyclotomicMu p ε) = cyclotomicMu p (ε ^ p) := by
  simp [cyclotomicMu_def]

@[simp]
theorem cyclotomicMu_coeff_zero (ε : S) : (cyclotomicMu p ε).coeff 0 = ε - 1 := by
  rw [cyclotomicMu_def, ← constantCoeff_apply, map_sub, map_one, constantCoeff_apply,
    teichmuller_coeff_zero]

section Perfect

variable [CharP S p] [PerfectRing S p]

/-- The cyclotomic period element `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` of `W(S)`, for a perfect ring
`S` of characteristic `p`. It is defined without division, and `μ = ξ · φ⁻¹(μ)`
(`cyclotomicMu_eq_cyclotomicXi_mul`). -/
noncomputable def cyclotomicXi (ε : S) : 𝕎 S :=
  ∑ j ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv S p).symm ε) ^ j

theorem cyclotomicXi_def (ε : S) :
    cyclotomicXi p ε =
      ∑ j ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv S p).symm ε) ^ j :=
  (rfl)

/-- The cyclotomic period element `ξ' = φ(ξ)` of `W(S)`, the Frobenius twist of `cyclotomicXi`;
it equals `∑_{j < p} [ε] ^ j` (`cyclotomicXiTilde_eq_sum`). -/
noncomputable def cyclotomicXiTilde (ε : S) : 𝕎 S :=
  frobenius (cyclotomicXi p ε)

theorem cyclotomicXiTilde_def (ε : S) : cyclotomicXiTilde p ε = frobenius (cyclotomicXi p ε) :=
  (rfl)

/-- The Frobenius of `ξ` is `ξ'`. -/
@[simp]
theorem frobenius_cyclotomicXi (ε : S) : frobenius (cyclotomicXi p ε) = cyclotomicXiTilde p ε :=
  (rfl)

/-- `ξ' = ∑_{j < p} [ε] ^ j`. -/
theorem cyclotomicXiTilde_eq_sum (ε : S) :
    cyclotomicXiTilde p ε = ∑ j ∈ Finset.range p, teichmuller p ε ^ j := by
  rw [cyclotomicXiTilde_def, cyclotomicXi_def, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_pow, frobenius_teichmuller, ← map_pow, frobeniusEquiv_symm_pow_p]

/-- `ξ'(ε) = ξ(ε ^ p)`. -/
theorem cyclotomicXiTilde_eq_cyclotomicXi_pow (ε : S) :
    cyclotomicXiTilde p ε = cyclotomicXi p (ε ^ p) := by
  rw [cyclotomicXiTilde_eq_sum, cyclotomicXi_def, frobeniusEquiv_symm_pow]

/-- For `ε = 1`, the period element `ξ = ∑_{j < p} [1] ^ j` is `p`. -/
@[simp]
theorem cyclotomicXi_one : cyclotomicXi p (1 : S) = p := by
  simp [cyclotomicXi_def]

/-- For `ε = 1`, the period element `ξ' = ∑_{j < p} [1] ^ j` is `p`. -/
@[simp]
theorem cyclotomicXiTilde_one : cyclotomicXiTilde p (1 : S) = p := by
  simp [cyclotomicXiTilde_eq_sum]

/-- If a ring homomorphism `f` sends `ε` to `1`, then `W(f)` sends `ξ' = ∑_{j < p} [ε] ^ j` to
`p`. -/
theorem map_cyclotomicXiTilde_eq_natCast {f : S →+* T} {ε : S} (hε : f ε = 1) :
    map f (cyclotomicXiTilde p ε) = p := by
  simp [cyclotomicXiTilde_eq_sum, map_sum, map_teichmuller, hε]

/-- If a ring homomorphism `f` to a reduced ring sends `ε` to `1`, then `W(f)` sends
`ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` to `p`: `f (ε ^ (1 / p))` is then `1` too. Reducedness is needed:
otherwise `f (ε ^ (1 / p)) - 1` may be a nonzero element with vanishing `p`-th power. -/
theorem map_cyclotomicXi_eq_natCast [IsReduced T] {f : S →+* T} {ε : S} (hε : f ε = 1) :
    map f (cyclotomicXi p ε) = p := by
  -- `f (ε ^ (1 / p)) - 1` is a `p`-th root of `f (ε - 1) = 0`, so it vanishes
  have h : f ((_root_.frobeniusEquiv S p).symm ε) = 1 := by
    rw [← sub_eq_zero]
    refine IsReduced.eq_zero _ ⟨p, ?_⟩
    rw [← map_one f, ← map_sub, ← map_pow, frobeniusEquiv_symm_sub_one_pow]
    simp [hε]
  simp [cyclotomicXi_def, map_sum, map_teichmuller, h]

section Natural

variable [CharP T p] [PerfectRing T p]

/-- The period element `ξ` is natural for ring homomorphisms between perfect rings of
characteristic `p`: `W(f)` sends `ξ(ε)` to `ξ(f ε)`. -/
@[simp]
theorem map_cyclotomicXi (f : S →+* T) (ε : S) :
    map f (cyclotomicXi p ε) = cyclotomicXi p (f ε) := by
  simp [cyclotomicXi_def, map_sum, map_teichmuller, RingHom.map_frobeniusEquiv_symm]

/-- The period element `ξ'` is natural for ring homomorphisms between perfect rings of
characteristic `p`: `W(f)` sends `ξ'(ε)` to `ξ'(f ε)`. -/
@[simp]
theorem map_cyclotomicXiTilde (f : S →+* T) (ε : S) :
    map f (cyclotomicXiTilde p ε) = cyclotomicXiTilde p (f ε) := by
  simp [cyclotomicXiTilde_eq_sum, map_sum, map_teichmuller]

end Natural

/-- The inverse Frobenius of `μ(ε) = [ε] - 1` is `μ(ε ^ (1 / p)) = [ε ^ (1 / p)] - 1`. -/
@[simp]
theorem frobeniusEquiv_symm_cyclotomicMu (ε : S) :
    (frobeniusEquiv p S).symm (cyclotomicMu p ε) =
      cyclotomicMu p ((_root_.frobeniusEquiv S p).symm ε) := by
  simp [cyclotomicMu_def]

/-- The inverse Frobenius of `ξ(ε) = ∑_{j < p} [ε ^ (1 / p)] ^ j` is `ξ(ε ^ (1 / p))`. -/
@[simp]
theorem frobeniusEquiv_symm_cyclotomicXi (ε : S) :
    (frobeniusEquiv p S).symm (cyclotomicXi p ε) =
      cyclotomicXi p ((_root_.frobeniusEquiv S p).symm ε) := by
  simp [cyclotomicXi_def, map_sum]

/-- The inverse Frobenius of `ξ'` is `ξ`. -/
@[simp]
theorem frobeniusEquiv_symm_cyclotomicXiTilde (ε : S) :
    (frobeniusEquiv p S).symm (cyclotomicXiTilde p ε) = cyclotomicXi p ε :=
  (frobeniusEquiv p S).symm_apply_apply (cyclotomicXi p ε)

/-- **`μ = ξ · φ⁻¹(μ)`**: with `x = ε ^ (1 / p)`, this is the geometric sum identity
`[x] ^ p - 1 = (∑_{j < p} [x] ^ j) ([x] - 1)`. -/
theorem cyclotomicMu_eq_cyclotomicXi_mul (ε : S) :
    cyclotomicMu p ε = cyclotomicXi p ε * (frobeniusEquiv p S).symm (cyclotomicMu p ε) := by
  rw [frobeniusEquiv_symm_cyclotomicMu, cyclotomicXi_def, cyclotomicMu_def, cyclotomicMu_def,
    geom_sum_mul, ← map_pow, frobeniusEquiv_symm_pow_p]

/-- **`φ(μ) = ξ' · μ`**, the Frobenius twist of `cyclotomicMu_eq_cyclotomicXi_mul`. -/
theorem frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul (ε : S) :
    frobenius (cyclotomicMu p ε) = cyclotomicXiTilde p ε * cyclotomicMu p ε := by
  conv_lhs => rw [cyclotomicMu_eq_cyclotomicXi_mul]
  rw [map_mul, cyclotomicXiTilde_def, ← _root_.WittVector.frobeniusEquiv_apply,
    RingEquiv.apply_symm_apply]

/-- **`ξ` is distinguished** (Bhatt–Morrow–Scholze, Example 3.16). If `ε - 1` lies in the
Jacobson radical of `S`, then the first Witt coordinate of `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` is a
unit: modulo the Jacobson radical, `ε ^ (1 / p)` becomes `1` and `ξ` becomes `p`. -/
theorem isDistinguished_cyclotomicXi {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    (cyclotomicXi p ε).IsDistinguished := by
  set x := (_root_.frobeniusEquiv S p).symm ε
  -- `x - 1` is a `p`-th root of `ε - 1`, and the Jacobson radical is a radical ideal
  have hx : x - 1 ∈ Ring.jacobson S := by
    rw [← Ideal.jacobson_bot] at hε ⊢
    exact Ideal.isRadical_jacobson ⊥ ⟨p, by rwa [frobeniusEquiv_symm_sub_one_pow]⟩
  let q := Ideal.Quotient.mk (Ring.jacobson S)
  have : IsLocalHom q := isLocalHom_of_le_jacobson le_rfl
  have hq : map q (cyclotomicXi p ε) = p := by
    have hx1 : q x = 1 := by rw [← map_one q, Ideal.Quotient.eq]; exact hx
    simp [cyclotomicXi_def, map_teichmuller, x, hx1]
  rw [isDistinguished_iff, ← isUnit_map_iff q, ← map_coeff, hq]
  rcases subsingleton_or_nontrivial (S ⧸ Ring.jacobson S) with _ | _
  · exact isUnit_of_subsingleton _
  · have : CharP (S ⧸ Ring.jacobson S) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
      rw [← map_natCast q, CharP.cast_eq_zero, map_zero]
    rw [coeff_p_one]
    exact isUnit_one

/-- **`ξ'` is distinguished.** If `ε - 1` lies in the Jacobson radical of `S`, then the first Witt
coordinate of `ξ' = φ(ξ)` is a unit: it is the `p`-th power of that of `ξ`. -/
theorem isDistinguished_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    (cyclotomicXiTilde p ε).IsDistinguished := by
  rw [cyclotomicXiTilde_def, isDistinguished_frobenius_iff]
  exact isDistinguished_cyclotomicXi p hε

section Level

/-- The finite cyclotomic Frobenius product `ξ_r = ∏_{j < r} φ⁻ʲ(ξ)` in `W(S)`. -/
noncomputable def cyclotomicXiLevel (ε : S) (r : ℕ) : 𝕎 S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε)

/-- The Frobenius-twisted finite cyclotomic product
`ξ'_r = φʳ(ξ_r) = ∏_{j < r} φʲ⁺¹(ξ) = ∏_{j < r} φʲ(ξ')` in `W(S)`. -/
noncomputable def cyclotomicXiTildeLevel (ε : S) (r : ℕ) : 𝕎 S :=
  ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j + 1]) (cyclotomicXi p ε)

/-- Unfolding lemma for `cyclotomicXiLevel`. -/
theorem cyclotomicXiLevel_def (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε r =
      ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε) :=
  (rfl)

/-- Unfolding lemma for `cyclotomicXiTildeLevel`. -/
theorem cyclotomicXiTildeLevel_def (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r =
      ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j + 1]) (cyclotomicXi p ε) :=
  (rfl)

/-- At level `0`, `ξ_0 = 1`. -/
@[simp]
theorem cyclotomicXiLevel_zero (ε : S) : cyclotomicXiLevel p ε 0 = 1 := by
  simp [cyclotomicXiLevel_def]

/-- At level `0`, `ξ'_0 = 1`. -/
@[simp]
theorem cyclotomicXiTildeLevel_zero (ε : S) : cyclotomicXiTildeLevel p ε 0 = 1 := by
  simp [cyclotomicXiTildeLevel_def]

/-- At level `1`, `ξ_1 = ξ`. -/
@[simp]
theorem cyclotomicXiLevel_one (ε : S) : cyclotomicXiLevel p ε 1 = cyclotomicXi p ε := by
  simp [cyclotomicXiLevel_def]

/-- At level `1`, `ξ'_1 = ξ'`. -/
@[simp]
theorem cyclotomicXiTildeLevel_one (ε : S) :
    cyclotomicXiTildeLevel p ε 1 = cyclotomicXiTilde p ε := by
  simp [cyclotomicXiTildeLevel_def, _root_.WittVector.frobeniusEquiv_apply]

/-- Recursion for `ξ_{r + 1}` appending `φ⁻ʳ(ξ)`. -/
theorem cyclotomicXiLevel_succ (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε (r + 1) =
      cyclotomicXiLevel p ε r * ((frobeniusEquiv p S).symm^[r]) (cyclotomicXi p ε) :=
  Finset.prod_range_succ _ r

/-- Recursion for `ξ'_{r + 1}` appending `φ^{r + 1}(ξ)`. -/
theorem cyclotomicXiTildeLevel_succ (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε (r + 1) =
      cyclotomicXiTildeLevel p ε r * ((frobeniusEquiv p S)^[r + 1]) (cyclotomicXi p ε) :=
  Finset.prod_range_succ _ r

/-- Express `ξ'_r` as `∏_{j < r} φʲ(ξ')`. -/
theorem cyclotomicXiTildeLevel_eq_prod_xiTilde (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r =
      ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j]) (cyclotomicXiTilde p ε) := by
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Function.iterate_succ_apply, _root_.WittVector.frobeniusEquiv_apply, frobenius_cyclotomicXi]

/-- At level `2`, `ξ_2 = ξ · φ⁻¹(ξ)`. -/
theorem cyclotomicXiLevel_two (ε : S) :
    cyclotomicXiLevel p ε 2 = cyclotomicXi p ε * (frobeniusEquiv p S).symm (cyclotomicXi p ε) := by
  rw [cyclotomicXiLevel_succ, cyclotomicXiLevel_one, Function.iterate_one]

/-- At level `2`, `ξ'_2 = ξ' · φ(ξ')`. -/
theorem cyclotomicXiTildeLevel_two (ε : S) :
    cyclotomicXiTildeLevel p ε 2 =
      cyclotomicXiTilde p ε * frobenius (cyclotomicXiTilde p ε) := by
  rw [cyclotomicXiTildeLevel_eq_prod_xiTilde, Finset.prod_range_succ, Finset.prod_range_one,
    Function.iterate_zero, id_eq, Function.iterate_one, _root_.WittVector.frobeniusEquiv_apply]

private theorem iterate_frobeniusEquiv_mul (n : ℕ) (a b : 𝕎 S) :
    ((frobeniusEquiv p S)^[n]) (a * b) =
      ((frobeniusEquiv p S)^[n]) a * ((frobeniusEquiv p S)^[n]) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

private theorem iterate_frobeniusEquiv_symm_mul (n : ℕ) (a b : 𝕎 S) :
    ((frobeniusEquiv p S).symm^[n]) (a * b) =
      ((frobeniusEquiv p S).symm^[n]) a * ((frobeniusEquiv p S).symm^[n]) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

private theorem iterate_frobeniusEquiv_symm_cyclotomicXi_eq (n : ℕ) (ε : S) :
    ((frobeniusEquiv p S).symm^[n]) (cyclotomicXi p ε) =
      cyclotomicXi p (((_root_.frobeniusEquiv S p).symm^[n]) ε) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      frobeniusEquiv_symm_cyclotomicXi]

private theorem iterate_frobeniusEquiv_cyclotomicXiTilde_eq (n : ℕ) (ε : S) :
    ((frobeniusEquiv p S)^[n]) (cyclotomicXiTilde p ε) =
      cyclotomicXiTilde p (ε ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, _root_.WittVector.frobeniusEquiv_apply,
      cyclotomicXiTilde_eq_sum, cyclotomicXiTilde_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_pow, frobenius_teichmuller, ← map_pow, ← pow_mul, pow_succ', mul_comm]

/-- Recursion for `ξ_{r + 1}` factoring out `ξ`: `ξ_{r + 1} = ξ · φ⁻¹(ξ_r)`. -/
theorem cyclotomicXiLevel_succ' (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε (r + 1) =
      cyclotomicXi p ε * (frobeniusEquiv p S).symm (cyclotomicXiLevel p ε r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [cyclotomicXiLevel_succ, ih, mul_assoc, Function.iterate_succ_apply',
      ← map_mul (frobeniusEquiv p S).symm, ← cyclotomicXiLevel_succ, ← ih]

/-- Recursion for `ξ'_{r + 1}` factoring out `ξ'`: `ξ'_{r + 1} = ξ' · φ(ξ'_r)`. -/
theorem cyclotomicXiTildeLevel_succ' (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε (r + 1) =
      cyclotomicXiTilde p ε * frobenius (cyclotomicXiTildeLevel p ε r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [cyclotomicXiTildeLevel_succ, ih, mul_assoc]
    congr 1
    rw [← _root_.WittVector.frobeniusEquiv_apply, Function.iterate_succ_apply',
      ← map_mul (frobeniusEquiv p S), ← cyclotomicXiTildeLevel_succ,
      _root_.WittVector.frobeniusEquiv_apply, ih]

private theorem iterate_frobeniusEquiv_symm_cancel (r : ℕ) (x : 𝕎 S) :
    ((frobeniusEquiv p S)^[r]) (((frobeniusEquiv p S).symm^[r]) x) = x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply (frobeniusEquiv p S), Function.iterate_succ_apply',
      (frobeniusEquiv p S).apply_symm_apply, ih]

private theorem iterate_frobeniusEquiv_cancel (r : ℕ) (x : 𝕎 S) :
    ((frobeniusEquiv p S).symm^[r]) (((frobeniusEquiv p S)^[r]) x) = x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply (frobeniusEquiv p S).symm, Function.iterate_succ_apply',
      (frobeniusEquiv p S).symm_apply_apply, ih]

/-- `φʳ(ξ_r) = ξ'_r`. -/
theorem iterate_frobeniusEquiv_cyclotomicXiLevel (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (cyclotomicXiLevel p ε r) = cyclotomicXiTildeLevel p ε r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [cyclotomicXiLevel_succ', cyclotomicXiTildeLevel_succ, Function.iterate_succ_apply,
      map_mul, (frobeniusEquiv p S).apply_symm_apply, iterate_frobeniusEquiv_mul, ih,
      ← Function.iterate_succ_apply (frobeniusEquiv p S) r (cyclotomicXi p ε), mul_comm]

/-- `φ⁻ʳ(ξ'_r) = ξ_r`. -/
theorem iterate_frobeniusEquiv_symm_cyclotomicXiTildeLevel (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S).symm^[r]) (cyclotomicXiTildeLevel p ε r) = cyclotomicXiLevel p ε r := by
  rw [← iterate_frobeniusEquiv_cyclotomicXiLevel]
  exact iterate_frobeniusEquiv_cancel p r _

/-- At `ε = 1`, `ξ_r(1) = p ^ r`. -/
@[simp]
theorem cyclotomicXiLevel_one_eq_natCast (r : ℕ) :
    cyclotomicXiLevel p (1 : S) r = (p : 𝕎 S) ^ r := by
  have hpj (j : ℕ) : ((frobeniusEquiv p S).symm^[j]) (p : 𝕎 S) = p := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  have hprod : ∏ j ∈ Finset.range r, ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p (1 : S)) =
      ∏ _j ∈ Finset.range r, (p : 𝕎 S) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [cyclotomicXi_one, hpj j]
  rw [cyclotomicXiLevel_def, hprod, Finset.prod_const, Finset.card_range]

/-- At `ε = 1`, `ξ'_r(1) = p ^ r`. -/
@[simp]
theorem cyclotomicXiTildeLevel_one_eq_natCast (r : ℕ) :
    cyclotomicXiTildeLevel p (1 : S) r = (p : 𝕎 S) ^ r := by
  have hpj (j : ℕ) : ((frobeniusEquiv p S)^[j]) (p : 𝕎 S) = p := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  have hprod : ∏ j ∈ Finset.range r, ((frobeniusEquiv p S)^[j]) (cyclotomicXiTilde p (1 : S)) =
      ∏ _j ∈ Finset.range r, (p : 𝕎 S) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [cyclotomicXiTilde_one, hpj j]
  rw [cyclotomicXiTildeLevel_eq_prod_xiTilde, hprod, Finset.prod_const, Finset.card_range]

/-- `ξ_r ∣ ξ_s` whenever `r ≤ s`. -/
theorem cyclotomicXiLevel_dvd_cyclotomicXiLevel_of_le (ε : S) {r s : ℕ} (hrs : r ≤ s) :
    cyclotomicXiLevel p ε r ∣ cyclotomicXiLevel p ε s :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hrs)

/-- `ξ'_r ∣ ξ'_s` whenever `r ≤ s`. -/
theorem cyclotomicXiTildeLevel_dvd_cyclotomicXiTildeLevel_of_le (ε : S) {r s : ℕ} (hrs : r ≤ s) :
    cyclotomicXiTildeLevel p ε r ∣ cyclotomicXiTildeLevel p ε s :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hrs)

/-- **`μ = ξ_r · φ⁻ʳ(μ)`**: the iterated geometric sum factorisation in `W(S)`. -/
theorem cyclotomicMu_eq_cyclotomicXiLevel_mul (ε : S) (r : ℕ) :
    cyclotomicMu p ε =
      cyclotomicXiLevel p ε r * ((frobeniusEquiv p S).symm^[r]) (cyclotomicMu p ε) := by
  induction r with
  | zero => simp
  | succ r ih =>
    conv_lhs => rw [ih]
    rw [cyclotomicXiLevel_succ, Function.iterate_succ_apply (frobeniusEquiv p S).symm r, mul_assoc,
      ← iterate_frobeniusEquiv_symm_mul, ← cyclotomicMu_eq_cyclotomicXi_mul]

/-- **`φʳ(μ) = ξ'_r · μ`**, the Frobenius twist of `cyclotomicMu_eq_cyclotomicXiLevel_mul`. -/
theorem iterate_frobeniusEquiv_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul (ε : S) (r : ℕ) :
    ((frobeniusEquiv p S)^[r]) (cyclotomicMu p ε) =
      cyclotomicXiTildeLevel p ε r * cyclotomicMu p ε := by
  have h := congrArg ((frobeniusEquiv p S)^[r]) (cyclotomicMu_eq_cyclotomicXiLevel_mul p ε r)
  rw [iterate_frobeniusEquiv_mul, iterate_frobeniusEquiv_cyclotomicXiLevel,
    iterate_frobeniusEquiv_symm_cancel] at h
  exact h

/-- `ξ_r` divides `μ` in `W(S)`. -/
theorem cyclotomicXiLevel_dvd_cyclotomicMu (ε : S) (r : ℕ) :
    cyclotomicXiLevel p ε r ∣ cyclotomicMu p ε :=
  ⟨_, cyclotomicMu_eq_cyclotomicXiLevel_mul p ε r⟩

/-- `ξ'_r` divides `φʳ(μ)` in `W(S)`. -/
theorem cyclotomicXiTildeLevel_dvd_iterate_frobeniusEquiv_cyclotomicMu (ε : S) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ∣ ((frobeniusEquiv p S)^[r]) (cyclotomicMu p ε) :=
  ⟨_, iterate_frobeniusEquiv_cyclotomicMu_eq_cyclotomicXiTildeLevel_mul p ε r⟩

section LevelNatural

variable [CharP T p] [PerfectRing T p]

private theorem iterate_ring_frobeniusEquiv_symm_map (f : S →+* T) (j : ℕ) (x : S) :
    f (((_root_.frobeniusEquiv S p).symm^[j]) x) =
      ((_root_.frobeniusEquiv T p).symm^[j]) (f x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      RingHom.map_frobeniusEquiv_symm, ih]

/-- `WittVector.map f` sends `ξ_r(ε)` to `ξ_r(f ε)`. -/
@[simp]
theorem map_cyclotomicXiLevel (f : S →+* T) (ε : S) (r : ℕ) :
    map f (cyclotomicXiLevel p ε r) = cyclotomicXiLevel p (f ε) r := by
  simp only [cyclotomicXiLevel_def, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [iterate_frobeniusEquiv_symm_cyclotomicXi_eq, map_cyclotomicXi,
    iterate_frobeniusEquiv_symm_cyclotomicXi_eq, iterate_ring_frobeniusEquiv_symm_map]

/-- `WittVector.map f` sends `ξ'_r(ε)` to `ξ'_r(f ε)`. -/
@[simp]
theorem map_cyclotomicXiTildeLevel (f : S →+* T) (ε : S) (r : ℕ) :
    map f (cyclotomicXiTildeLevel p ε r) = cyclotomicXiTildeLevel p (f ε) r := by
  simp only [cyclotomicXiTildeLevel_eq_prod_xiTilde, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [iterate_frobeniusEquiv_cyclotomicXiTilde_eq, map_cyclotomicXiTilde, map_pow,
    iterate_frobeniusEquiv_cyclotomicXiTilde_eq]

end LevelNatural

/-- If `f ε = 1` and `T` is reduced, then `W(f)` sends `ξ_r` to `p ^ r`. -/
theorem map_cyclotomicXiLevel_eq_natCast [IsReduced T] {f : S →+* T} {ε : S}
    (hε : f ε = 1) (r : ℕ) :
    map f (cyclotomicXiLevel p ε r) = (p : 𝕎 T) ^ r := by
  simp only [cyclotomicXiLevel_def, map_prod]
  have hf (j : ℕ) : f (((_root_.frobeniusEquiv S p).symm^[j]) ε) = 1 := by
    induction j with
    | zero => exact hε
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← sub_eq_zero]
      refine IsReduced.eq_zero _ ⟨p, ?_⟩
      rw [← map_one f, ← map_sub, ← map_pow, frobeniusEquiv_symm_sub_one_pow]
      simp [ih]
  have hprod :
      ∏ j ∈ Finset.range r, map f (((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε)) =
        ∏ _j ∈ Finset.range r, (p : 𝕎 T) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [iterate_frobeniusEquiv_symm_cyclotomicXi_eq]
    exact map_cyclotomicXi_eq_natCast p (hf j)
  rw [hprod, Finset.prod_const, Finset.card_range]

/-- If `f ε = 1`, then `W(f)` sends `ξ'_r` to `p ^ r`. -/
theorem map_cyclotomicXiTildeLevel_eq_natCast {f : S →+* T} {ε : S} (hε : f ε = 1) (r : ℕ) :
    map f (cyclotomicXiTildeLevel p ε r) = (p : 𝕎 T) ^ r := by
  simp only [cyclotomicXiTildeLevel_eq_prod_xiTilde, map_prod]
  have hprod :
      ∏ j ∈ Finset.range r, map f (((frobeniusEquiv p S)^[j]) (cyclotomicXiTilde p ε)) =
        ∏ _j ∈ Finset.range r, (p : 𝕎 T) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [iterate_frobeniusEquiv_cyclotomicXiTilde_eq]
    exact map_cyclotomicXiTilde_eq_natCast p (by simp [hε])
  rw [hprod, Finset.prod_const, Finset.card_range]

end Level

section Regularity

/-- Zeroth Witt coordinate relation for `μ = ξ · φ⁻¹(μ)`: `ξ.coeff 0 · (ε ^ (1 / p) - 1) = ε - 1`.
-/
theorem cyclotomicXi_coeff_zero_mul (ε : S) :
    (cyclotomicXi p ε).coeff 0 * ((_root_.frobeniusEquiv S p).symm ε - 1) = ε - 1 := by
  simpa [mul_coeff_zero] using congrArg (·.coeff 0) (cyclotomicMu_eq_cyclotomicXi_mul p ε).symm

/-- Zeroth Witt coordinate relation for `φ(μ) = ξ' · μ`: `ξ'.coeff 0 · (ε - 1) = ε ^ p - 1`. -/
theorem cyclotomicXiTilde_coeff_zero_mul (ε : S) :
    (cyclotomicXiTilde p ε).coeff 0 * (ε - 1) = ε ^ p - 1 := by
  have h := congrArg (·.coeff 0) (frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul p ε).symm
  simpa [mul_coeff_zero, frobenius_cyclotomicMu] using h

private theorem iterate_frobeniusEquiv_symm_cyclotomicMu (r : ℕ) (ε : S) :
    ((frobeniusEquiv p S).symm^[r]) (cyclotomicMu p ε) =
      cyclotomicMu p (((_root_.frobeniusEquiv S p).symm^[r]) ε) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      frobeniusEquiv_symm_cyclotomicMu]

/-- Zeroth Witt coordinate relation for `μ = ξ_r · φ⁻ʳ(μ)`:
`ξ_r.coeff 0 · (ε ^ (1 / p ^ r) - 1) = ε - 1`. -/
theorem cyclotomicXiLevel_coeff_zero_mul (ε : S) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 * (((_root_.frobeniusEquiv S p).symm^[r]) ε - 1) =
      ε - 1 := by
  have h := congrArg (·.coeff 0) (cyclotomicMu_eq_cyclotomicXiLevel_mul p ε r).symm
  rw [mul_coeff_zero, iterate_frobeniusEquiv_symm_cyclotomicMu, cyclotomicMu_coeff_zero,
    cyclotomicMu_coeff_zero] at h
  exact h

private theorem coeff_iterate_frobeniusEquiv_zero (r : ℕ) (w : 𝕎 S) :
    (((frobeniusEquiv p S)^[r]) w).coeff 0 = w.coeff 0 ^ p ^ r := by
  induction r generalizing w with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih, _root_.WittVector.frobeniusEquiv_apply,
      coeff_frobenius_charP, ← pow_mul, pow_succ']

/-- The zeroth Witt coordinate of `ξ'_r` is the `p ^ r`-th power of that of `ξ_r`. -/
theorem cyclotomicXiTildeLevel_coeff_zero (ε : S) (r : ℕ) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 = (cyclotomicXiLevel p ε r).coeff 0 ^ p ^ r := by
  rw [← iterate_frobeniusEquiv_cyclotomicXiLevel, coeff_iterate_frobeniusEquiv_zero]

/-- If `ε - 1 ∈ S⁰`, then `ξ.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXi_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    (cyclotomicXi p ε).coeff 0 ∈ S⁰ :=
  (mul_mem_nonZeroDivisors.mp (by rwa [cyclotomicXi_coeff_zero_mul])).1

/-- If `ε - 1 ∈ S⁰`, then `ξ'.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    (cyclotomicXiTilde p ε).coeff 0 ∈ S⁰ := by
  rw [← frobenius_cyclotomicXi, coeff_frobenius_charP]
  exact pow_mem (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε) p

/-- If `ε - 1 ∈ S⁰`, then `ξ_r.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    (cyclotomicXiLevel p ε r).coeff 0 ∈ S⁰ :=
  (mul_mem_nonZeroDivisors.mp (by rwa [cyclotomicXiLevel_coeff_zero_mul])).1

/-- If `ε - 1 ∈ S⁰`, then `ξ'_r.coeff 0 ∈ S⁰`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰)
    (r : ℕ) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 ∈ S⁰ := by
  rw [cyclotomicXiTildeLevel_coeff_zero]
  exact pow_mem (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r) (p ^ r)

/-- If `ε - 1 ∈ Ring.jacobson S`, then `ξ.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXi_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    (cyclotomicXi p ε).coeff 0 ∈ Ring.jacobson S := by
  set x := (_root_.frobeniusEquiv S p).symm ε
  have hx : x - 1 ∈ Ring.jacobson S := by
    rw [← Ideal.jacobson_bot] at hε ⊢
    exact Ideal.isRadical_jacobson ⊥ ⟨p, by rwa [frobeniusEquiv_symm_sub_one_pow]⟩
  let q := Ideal.Quotient.mk (Ring.jacobson S)
  have hq : map q (cyclotomicXi p ε) = p := by
    have hx1 : q x = 1 := by rw [← map_one q, Ideal.Quotient.eq]; exact hx
    simp [cyclotomicXi_def, map_teichmuller, x, hx1]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 := congrArg (·.coeff 0) hq
  rw [map_coeff] at h0
  rw [h0, ← constantCoeff_apply, map_natCast]
  rcases subsingleton_or_nontrivial (S ⧸ Ring.jacobson S) with _ | _
  · exact Subsingleton.elim _ _
  · have : CharP (S ⧸ Ring.jacobson S) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
      rw [← map_natCast q, CharP.cast_eq_zero, map_zero]
    exact CharP.cast_eq_zero _ p

/-- If `ε - 1 ∈ Ring.jacobson S` and `1 ≤ r`, then `ξ_r.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXiLevel_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S)
    {r : ℕ} (hr : 1 ≤ r) :
    (cyclotomicXiLevel p ε r).coeff 0 ∈ Ring.jacobson S := by
  have hdvd : (cyclotomicXi p ε).coeff 0 ∣ (cyclotomicXiLevel p ε r).coeff 0 := by
    obtain ⟨c, hc⟩ := cyclotomicXiLevel_dvd_cyclotomicXiLevel_of_le p ε hr
    rw [cyclotomicXiLevel_one] at hc
    exact ⟨c.coeff 0, by simpa [mul_coeff_zero] using congrArg (·.coeff 0) hc⟩
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  exact Ideal.mul_mem_right c _ (cyclotomicXi_coeff_zero_mem_jacobson p hε)

/-- If `ε - 1 ∈ Ring.jacobson S` and `1 ≤ r`, then `ξ'_r.coeff 0 ∈ Ring.jacobson S`. -/
theorem cyclotomicXiTildeLevel_coeff_zero_mem_jacobson {ε : S} (hε : ε - 1 ∈ Ring.jacobson S)
    {r : ℕ} (hr : 1 ≤ r) :
    (cyclotomicXiTildeLevel p ε r).coeff 0 ∈ Ring.jacobson S := by
  rw [cyclotomicXiTildeLevel_coeff_zero]
  exact Ideal.pow_mem_of_mem _ (cyclotomicXiLevel_coeff_zero_mem_jacobson p hε hr) _
    (pow_pos hp.out.pos r)

private theorem not_isUnit_of_mem_jacobson [Nontrivial S] {a : S} (ha : a ∈ Ring.jacobson S) :
    ¬ IsUnit a := fun hu ↦ by
  have htop : Ring.jacobson S = ⊤ := Ideal.eq_top_of_isUnit_mem (Ring.jacobson S) ha hu
  rw [← Ideal.jacobson_bot, Ideal.jacobson_eq_top_iff] at htop
  exact bot_ne_top htop

/-- If `ε - 1 ∈ S⁰`, then `μ = [ε] - 1` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicMu_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicMu p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (by simpa using hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXi_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicXi p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ'` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiTilde_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) :
    cyclotomicXiTilde p ε ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `ξ_r` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiLevel_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    cyclotomicXiLevel p ε r ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `ξ'_r` is a nonzerodivisor in `W(S)`. -/
theorem cyclotomicXiTildeLevel_mem_nonZeroDivisors {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    cyclotomicXiTildeLevel p ε r ∈ (𝕎 S)⁰ :=
  mem_nonZeroDivisors_of_coeff_zero (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (μ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicMu {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicMu p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero (by simpa using hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXi {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXi p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ')` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiTilde p ε}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiLevel {ε : S} (hε : ε - 1 ∈ S⁰) (r : ℕ) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiLevel p ε r}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)

/-- If `ε - 1 ∈ S⁰`, then `W(S) ⧸ (ξ'_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (r : ℕ) :
    IsSMulRegular (𝕎 S ⧸ Ideal.span {cyclotomicXiTildeLevel p ε r}) (p : 𝕎 S) :=
  isSMulRegular_quotient_natCast_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)

section RegularPair

variable [Nontrivial S]

/-- If `ε - 1 ∈ S⁰` and `ε - 1 ∈ Ring.jacobson S`, then `[p, μ]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicMu {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicMu p ε] :=
  isRegular_pair_natCast_of_coeff_zero (by simpa using hε)
    (not_isUnit_of_mem_jacobson (by simpa using hJ))

/-- If `ε - 1 ∈ S⁰` and `ε - 1 ∈ Ring.jacobson S`, then `[μ, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicMu_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) :
    IsRegular (𝕎 S) [cyclotomicMu p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (by simpa using hε)
    (not_isUnit_of_mem_jacobson (by simpa using hJ))

/-- If `ε - 1 ∈ S⁰` and `ε - 1 ∈ Ring.jacobson S`, then `[p, ξ]` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXi {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXi p ε] :=
  isRegular_pair_natCast_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_of_mem_jacobson (cyclotomicXi_coeff_zero_mem_jacobson p hJ))

/-- If `ε - 1 ∈ S⁰` and `ε - 1 ∈ Ring.jacobson S`, then `[ξ, p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXi_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) :
    IsRegular (𝕎 S) [cyclotomicXi p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXi_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_of_mem_jacobson (cyclotomicXi_coeff_zero_mem_jacobson p hJ))

/-- If `ε - 1 ∈ S⁰` and `ε - 1 ∈ Ring.jacobson S`, then `[p, ξ']` is regular on `W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiTilde p ε] :=
  isRegular_pair_natCast_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_of_mem_jacobson (by
      simpa [← cyclotomicXiTildeLevel_one] using
        cyclotomicXiTildeLevel_coeff_zero_mem_jacobson p hJ le_rfl))

/-- If `ε - 1 ∈ S⁰` and `ε - 1 ∈ Ring.jacobson S`, then `[ξ', p]` is regular on `W(S)`. -/
theorem isRegular_pair_cyclotomicXiTilde_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) :
    IsRegular (𝕎 S) [cyclotomicXiTilde p ε, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXiTilde_coeff_zero_mem_nonZeroDivisors p hε)
    (not_isUnit_of_mem_jacobson (by
      simpa [← cyclotomicXiTildeLevel_one] using
        cyclotomicXiTildeLevel_coeff_zero_mem_jacobson p hJ le_rfl))

/-- If `ε - 1 ∈ S⁰`, `ε - 1 ∈ Ring.jacobson S`, and `1 ≤ r`, then `[p, ξ_r]` is regular on
`W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiLevel p ε r] :=
  isRegular_pair_natCast_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_of_mem_jacobson (cyclotomicXiLevel_coeff_zero_mem_jacobson p hJ hr))

/-- If `ε - 1 ∈ S⁰`, `ε - 1 ∈ Ring.jacobson S`, and `1 ≤ r`, then `[ξ_r, p]` is regular on
`W(S)`. -/
theorem isRegular_pair_cyclotomicXiLevel_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [cyclotomicXiLevel p ε r, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero (cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_of_mem_jacobson (cyclotomicXiLevel_coeff_zero_mem_jacobson p hJ hr))

/-- If `ε - 1 ∈ S⁰`, `ε - 1 ∈ Ring.jacobson S`, and `1 ≤ r`, then `[p, ξ'_r]` is regular on
`W(S)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTildeLevel {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [(p : 𝕎 S), cyclotomicXiTildeLevel p ε r] :=
  isRegular_pair_natCast_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_of_mem_jacobson (cyclotomicXiTildeLevel_coeff_zero_mem_jacobson p hJ hr))

/-- If `ε - 1 ∈ S⁰`, `ε - 1 ∈ Ring.jacobson S`, and `1 ≤ r`, then `[ξ'_r, p]` is regular on
`W(S)`. -/
theorem isRegular_pair_cyclotomicXiTildeLevel_natCast {ε : S} (hε : ε - 1 ∈ S⁰)
    (hJ : ε - 1 ∈ Ring.jacobson S) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎 S) [cyclotomicXiTildeLevel p ε r, (p : 𝕎 S)] :=
  isRegular_pair_of_coeff_zero
    (cyclotomicXiTildeLevel_coeff_zero_mem_nonZeroDivisors p hε r)
    (not_isUnit_of_mem_jacobson (cyclotomicXiTildeLevel_coeff_zero_mem_jacobson p hJ hr))

end RegularPair

end Regularity

end Perfect

end TauCeti.WittVector
