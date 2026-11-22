/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Frobenius
public import TauCeti.RingTheory.WittVector.Primitive.Basic

/-!
# Cyclotomic period elements of Witt vectors

Let `S` be a perfect ring of characteristic `p`, so that the Witt vector Frobenius `φ` of `W(S)`
is an automorphism, and let `ε ∈ S`. Write `[-]` for Teichmüller representatives. This file
defines the cyclotomic period elements

* `μ = [ε] - 1` (`TauCeti.WittVector.cyclotomicMu`),
* `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` (`TauCeti.WittVector.cyclotomicXi`),
* `ξ' = φ(ξ) = ∑_{j < p} [ε] ^ j` (`TauCeti.WittVector.cyclotomicXiTilde`; usually written `ξ`
  with a tilde).

In the main example `S = O_C^♭` is the tilt of the ring of integers of a complete algebraically
closed extension `C` of `ℚ_p`, `W(S) = A_inf`, and `ε = (1, ζ_p, ζ_{p²}, …)` is a compatible system
of primitive `p`-power roots of unity; then `ξ` generates the kernel of Fontaine's map
`θ : A_inf → O_C` and `ξ'` the kernel of `θ ∘ φ⁻¹`
(`TauCeti.WittVector.ker_fontaineTheta_eq_span_cyclotomicXi`).

The three elements are natural in `S`: a ring homomorphism `f : S →+* T` sends them, under
`WittVector.map f`, to the elements formed from `f ε` (for `ξ` and `ξ'` when `T` is perfect too).
At `ε = 1` they are `0`, `p` and `p`. Hence if `f ε = 1`, then `W(f)` kills `μ` and sends `ξ'` to
`p`, and also `ξ` when `T` is reduced. In the main example `f` is the residue map `O_C^♭ → k` to the
residue field and `W(f) : A_inf → W(k)` is the specialization to the crystalline special fibre;
unlike Fontaine's map, it sends `ξ` to `p` rather than to `0`.

The geometric sum identity gives the factorisations `μ = ξ · φ⁻¹(μ)` and `φ(μ) = ξ' · μ` in `W(S)`,
without any division. If `ε - 1` lies in the Jacobson radical of `S`, then modulo the Jacobson
radical `ξ` becomes `p`, so `ξ` and `ξ'` are distinguished: their first Witt coordinates are units.

## Main definitions

* `TauCeti.WittVector.cyclotomicMu`, `TauCeti.WittVector.cyclotomicXi`,
  `TauCeti.WittVector.cyclotomicXiTilde`: the elements `μ`, `ξ` and `ξ'` of `W(S)`.

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
* `TauCeti.WittVector.isDistinguished_cyclotomicXi`,
  `TauCeti.WittVector.isDistinguished_cyclotomicXiTilde`: if `ε - 1` lies in the Jacobson radical
  of `S`, then `ξ` and `ξ'` are distinguished.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Example 3.16 and
  Proposition 3.17.
-/

public section

open _root_.WittVector

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
    rw [← map_one f, ← map_sub, ← map_pow, sub_pow_char, frobeniusEquiv_symm_pow_p, one_pow,
      map_sub, hε, map_one, sub_self]
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
    exact Ideal.isRadical_jacobson ⊥ ⟨p, by rwa [sub_pow_char, one_pow, frobeniusEquiv_symm_pow_p]⟩
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

end Perfect

end TauCeti.WittVector
