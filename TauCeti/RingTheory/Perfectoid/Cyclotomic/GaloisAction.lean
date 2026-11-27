/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import TauCeti.RingTheory.Perfectoid.Cyclotomic.SpecializationKernel
public import TauCeti.RingTheory.Perfectoid.PreTilt.Action
public import TauCeti.RingTheory.WittVector.PadicInt

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed

/-!
# The Galois action on the cyclotomic periods of `A_inf`

Let `C` be a complete perfectoid nonarchimedean field of residue characteristic `p`, with
valuation ring `O_C`, tilt `O♭ = O_C♭` and `A_inf = W(O♭)`. Fix `ε ∈ O♭` such that the sharp of
`ε ^ (1 / p)` is a primitive `p`-th root of unity; then the sharp of `ε ^ (1 / p ^ n)` is a
primitive `p ^ n`-th root of unity `ζ_{p ^ n}` for every `n`, so `ε` is a compatible system of
`p`-power roots of unity. Such an `ε` exists when `C` is algebraically closed and `p ≠ 0` in
`C`. Let `μ = [ε] - 1` and `τ = [ε ^ (1 / p)] - 1` be the cyclotomic periods.

Let a group `G` act on `O_C` by ring automorphisms, for instance `Gal(PadicAlgCl p / ℚ_p)` on the
valuation ring of `ℂ_p`, and let `χ : G → ℤ_pˣ` be the cyclotomic character of the action, so
that `g (ζ) = ζ ^ χ(g)` for every root of unity `ζ` of `p`-power order. The group `G` acts on `O♭`
and on `A_inf`, and:

* `g(ε) = ε ^ χ(g)`, in the sense that the sharps of the `p ^ n`-th roots of `g(ε)` are those of
  `ε` raised to the power `χ(g) mod p ^ n`;
* `μ` divides `g(μ)`, and `g(τ)` is a unit multiple of `τ`;
* `μ²` divides `g(μ) - χ(g) μ`.

For the last statement write `g(μ) = [g(ε)] - 1 = μ c`. It suffices that `θ(φ ^ j c) = χ(g)` for
every `j ≥ 0`, since the elements killed by every `θ ∘ φ ^ j` are the multiples of `μ`
(`PreTilt.mem_span_mu_iff`). Approximate `χ(g)` by a natural number `b` modulo `p ^ N`. The
sharps of the `p ^ N`-th roots of `g(ε)` and `ε ^ b` agree, so `g(ε) = ε ^ b w ^ (p ^ N)` with
`w♯ = 1`, hence `[w] - 1 = μ d`. Expanding `[ε] ^ b [w] ^ (p ^ N) - 1` with geometric sums gives
`c = (∑_{i < b} [ε] ^ i) [w] ^ (p ^ N) + d ∑_{i < p ^ N} [w] ^ i`, and `θ ∘ φ ^ j` sends every
Teichmüller representative of an element with sharp `1` to `1`, so
`θ(φ ^ j c) = b + p ^ N θ(φ ^ j d) ≡ χ(g)` modulo `p ^ N`. As `O_C` is `p`-adically separated,
`θ(φ ^ j c) = χ(g)`.

## Main results

* `PreTilt.exists_isPrimitiveRoot_untilt_frobeniusEquiv_symm`: for `C` algebraically closed with
  `p ≠ 0` in `C`, there is `ε ∈ O♭` such that the sharp of `ε ^ (1 / p)` is a primitive `p`-th root
  of unity.
* `PreTilt.untilt_iterate_frobeniusEquiv_symm_smul`: `g(ε) = ε ^ χ(g)` on the sharps of the
  `p ^ n`-th roots.
* `PreTilt.mu_dvd_smul_mu`: `μ ∣ g(μ)`.
* `PreTilt.associated_smul_mu_frobeniusEquiv_symm`: `g(τ)` is a unit multiple of `τ`.
* `PreTilt.mu_sq_dvd_smul_mu_sub`: `μ² ∣ g(μ) - χ(g) μ`.

## References

* J.-M. Fontaine, *Le corps des périodes `p`-adiques*, Astérisque 223 (1994).
* P. Colmez, *Théorie d'Iwasawa des représentations de de Rham d'un corps local*, Ann. of Math.
  148 (1998).
-/

public section

open TauCeti.Perfectoid _root_.WittVector
open scoped NormedField Valued

namespace TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {G S : Type*} [Monoid G] [CommRing S] [MulSemiringAction G S]

/-- `g • μ(ε) = μ(g • ε)`: the action on Witt vectors moves the root system. -/
@[simp]
theorem smul_mu (g : G) (ε : S) : g • mu p ε = mu p (g • ε) := by
  rw [mu_eq, mu_eq, smul_sub, smul_teichmuller, smul_one]

end TauCeti.Perfectoid

namespace PreTilt

section Teichmuller

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- `θ` sends the image of `a ∈ ℤ_p` in `W(A♭)` to an element congruent modulo `p ^ N` to any
natural number representing `a mod p ^ N`. -/
private theorem natCast_pow_dvd_fontaineTheta_padicIntHom_sub (a : ℤ_[p]) (N : ℕ) :
    (p : A) ^ N ∣ fontaineTheta A p (TauCeti.WittVector.padicIntHom p (PreTilt A p) a) -
      (a.toZModPow N).val := by
  have h : (p : ℤ_[p]) ^ N ∣ a - (a.toZModPow N).val := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
      map_natCast, ZMod.natCast_zmod_val, sub_self]
  simpa only [map_pow, map_natCast, map_sub, RingHom.coe_comp, Function.comp_apply] using
    map_dvd ((fontaineTheta A p).comp (TauCeti.WittVector.padicIntHom p (PreTilt A p))) h

end Teichmuller

section Integers

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- **Existence of a compatible system of `p`-power roots of unity in the tilt.** If `C` is
algebraically closed and `p ≠ 0` in `C`, there is `ε ∈ O_C♭` such that the sharp of `ε ^ (1 / p)`
is a primitive `p`-th root of unity; the sharp of `ε ^ (1 / p ^ n)` is then a primitive `p ^ n`-th
root of unity for every `n` (`isPrimitiveRoot_untilt_iterate_frobeniusEquiv_symm`). -/
theorem exists_isPrimitiveRoot_untilt_frobeniusEquiv_symm [IsAlgClosed C] [NeZero (p : C)] :
    ∃ ε : PreTilt 𝒪[C] p,
      IsPrimitiveRoot (untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p := by
  -- a primitive `p`-th root of unity has norm one, so it lies in `O_C`, and it is the sharp of
  -- some `x ∈ O_C♭` because every element of `O_C` has a `p`-th root
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot C p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hζ1 : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hp0).mp (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  have : TauCeti.IsAbsolutelyIntegrallyClosed 𝒪[C] :=
    .of_isIntegrallyClosed_of_isAlgClosed C
  obtain ⟨x, hx⟩ := untilt_surjective (A := 𝒪[C]) (p := p)
    (fun a ↦ TauCeti.IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq a (Nat.pos_of_ne_zero hp0))
    ⟨ζ, Valued.integer.mem_iff.mpr hζ1.le⟩
  refine ⟨_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p x, ?_⟩
  rw [RingEquiv.symm_apply_apply, hx]
  exact hζ.of_map_of_injective (f := (𝒪[C]).subtype) Subtype.val_injective

/-- If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, then `O_C` has primitive
`p ^ n`-th roots of unity for every `n`, so the cyclotomic character of `O_C` is nontrivial. -/
private theorem hasEnoughRootsOfUnity (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) (n : ℕ) :
    HasEnoughRootsOfUnity 𝒪[C] (p ^ n) :=
  ⟨⟨_, isPrimitiveRoot_untilt_iterate_frobeniusEquiv_symm ε hε n⟩, rootsOfUnity.isCyclic _ _⟩

variable {G : Type*} [Group G] [MulSemiringAction G 𝒪[C]]

/-- **`g(ε) = ε ^ χ(g)`**: for a ring automorphism `g` of `O_C` with cyclotomic character `χ(g)`,
the sharp of the `p ^ n`-th root of `g(ε)` is the sharp of the `p ^ n`-th root of `ε` raised to the
power `χ(g) mod p ^ n`. -/
theorem untilt_iterate_frobeniusEquiv_symm_smul (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) (g : G) (n : ℕ) :
    ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm^[n] (g • ε)).untilt =
      ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm^[n] ε).untilt ^
        ((cyclotomicCharacter 𝒪[C] p (MulSemiringAction.toRingEquiv G 𝒪[C] g)).val.toZModPow
          n).val := by
  have := hasEnoughRootsOfUnity ε hε
  rw [iterate_frobeniusEquiv_symm_smul, untilt_smul,
    ← MulSemiringAction.toRingEquiv_apply_apply G]
  exact cyclotomicCharacter.spec p _ _ (by
    rw [untilt_iterate_frobeniusEquiv_symm_pow, ε.untilt_eq_one_of_isPrimitiveRoot hε])

end Integers

section PerfectoidField

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsPerfectoidTateRing p C] [Fact ¬IsUnit (p : 𝒪[C])]

/-- If `y♯ = 1`, then `μ` divides `[y] - 1`: the latter is killed by every `θ ∘ φ ^ j`. -/
theorem mu_dvd_mu_of_untilt_eq_one (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {y : PreTilt 𝒪[C] p} (hy : y.untilt = 1) : mu p ε ∣ mu p y :=
  Ideal.mem_span_singleton.mp
    ((mem_span_mu_iff ε hε).mpr (fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero y hy))

/-- The key congruence: let `[y] - 1 = μ c`. If the sharps of `y ^ (1 / p ^ N)` and of
`ε ^ (b / p ^ N)` agree, then `θ (φ ^ j c) ≡ b` modulo `p ^ N`. -/
private theorem natCast_pow_dvd_fontaineTheta_iterate_sub (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {y : PreTilt 𝒪[C] p} {c : WittVector p (PreTilt 𝒪[C] p)} (hc : mu p y = mu p ε * c)
    {N b : ℕ} (hN : ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm^[N] y).untilt =
      ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm^[N] ε).untilt ^ b) (j : ℕ) :
    (p : 𝒪[C]) ^ N ∣
      fontaineTheta 𝒪[C] p ((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j] c) - b := by
  set φ := _root_.frobeniusEquiv (PreTilt 𝒪[C] p) p
  have hε1 := ε.untilt_eq_one_of_isPrimitiveRoot hε
  -- write `y ^ (1 / p ^ N) = ε ^ (b / p ^ N) w` with `w♯ = 1`, so that `y = ε ^ b w ^ (p ^ N)`
  have he : (φ.symm^[N] ε).untilt ^ b ≠ 0 :=
    pow_ne_zero _ ((isPrimitiveRoot_untilt_iterate_frobeniusEquiv_symm ε hε N).ne_zero
      (pow_ne_zero N (Fact.out : p.Prime).ne_zero))
  obtain ⟨w, hw⟩ : (φ.symm^[N] ε) ^ b ∣ φ.symm^[N] y :=
    untilt_dvd_untilt_iff.mp (by rw [map_pow, hN])
  have hw1 : w.untilt = 1 := by
    have h := congrArg untilt hw
    rw [map_mul, map_pow, hN] at h
    exact ((mul_eq_left₀ he).mp h.symm)
  have hy : y = ε ^ b * w ^ p ^ N := by
    rw [← iterate_frobeniusEquiv_symm_pow_p_pow (PreTilt 𝒪[C] p) p y N, hw, mul_pow, ← pow_mul,
      mul_comm b, pow_mul, iterate_frobeniusEquiv_symm_pow_p_pow]
  obtain ⟨d, hd⟩ := mu_dvd_mu_of_untilt_eq_one ε hε hw1
  -- expand `[ε] ^ b [w] ^ (p ^ N) - 1` by geometric sums and cancel `μ`
  have hc' : c = (∑ i ∈ Finset.range b, teichmuller p ε ^ i) * teichmuller p w ^ p ^ N +
      d * ∑ i ∈ Finset.range (p ^ N), teichmuller p w ^ i := by
    refine mul_left_cancel₀ (mu_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε)) ?_
    rw [← hc, hy]
    simp only [mu_eq, map_mul, map_pow] at hd ⊢
    linear_combination (-teichmuller p w ^ p ^ N) * mul_geom_sum (teichmuller p ε) b +
      (∑ i ∈ Finset.range (p ^ N), teichmuller p w ^ i) * hd -
        mul_geom_sum (teichmuller p w) (p ^ N)
  -- `θ ∘ φ ^ j` is a ring homomorphism sending `[ε]` and `[w]` to `1`
  let Φ := (fontaineTheta 𝒪[C] p).comp ((frobeniusEquiv p (PreTilt 𝒪[C] p) :
    WittVector p (PreTilt 𝒪[C] p) →+* WittVector p (PreTilt 𝒪[C] p)) ^ j)
  have hΦ (x) : fontaineTheta 𝒪[C] p ((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j] x) = Φ x := by
    simp [Φ, RingHom.coe_pow]
  have hT : Φ (teichmuller p ε) = 1 := by
    rw [← hΦ, fontaineTheta_iterate_frobeniusEquiv_teichmuller, hε1, one_pow]
  have hU : Φ (teichmuller p w) = 1 := by
    rw [← hΦ, fontaineTheta_iterate_frobeniusEquiv_teichmuller, hw1, one_pow]
  refine ⟨Φ d, ?_⟩
  rw [hΦ, hc']
  simp [map_sum, hT, hU]
  ring

variable {G : Type*}

/-- `μ` divides `g(μ)` for every ring endomorphism `g` of `O_C`. -/
theorem mu_dvd_smul_mu [Monoid G] [MulSemiringAction G 𝒪[C]] (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) (g : G) :
    mu p ε ∣ g • mu p ε := by
  rw [smul_mu]
  exact mu_dvd_mu_of_untilt_eq_one ε hε
    (by rw [untilt_smul, ε.untilt_eq_one_of_isPrimitiveRoot hε, smul_one])

variable [Group G] [MulSemiringAction G 𝒪[C]]

/-- **`g(τ)` is a unit multiple of `τ`**, where `τ = [ε ^ (1 / p)] - 1` and `g` is a ring
automorphism of `O_C`. -/
theorem associated_smul_mu_frobeniusEquiv_symm (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) (g : G) :
    Associated (g • mu p ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε))
      (mu p ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) := by
  -- `g(τ) = φ⁻¹(g(μ))` is divisible by `φ⁻¹(μ) = τ` for every `g`, in particular for `g⁻¹`
  have hdvd (h : G) : mu p ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε) ∣
      h • mu p ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε) := by
    rw [← frobeniusEquiv_symm_mu, ← WittVector.frobeniusEquiv_symm_smul]
    exact map_dvd _ (mu_dvd_smul_mu ε hε h)
  refine associated_of_dvd_dvd ?_ (hdvd g)
  simpa [smul_smul] using map_dvd (MulSemiringAction.toRingHom G _ g) (hdvd g⁻¹)

/-- Let `[y] - 1 = μ c`, and `a ∈ ℤ_p` with `y = ε ^ a` in the sense that the sharps of the
`p ^ N`-th roots of `y` are those of `ε` raised to the power `a mod p ^ N`. Then `θ ∘ φ ^ j` sends
`c` to `a` for every `j`, so `μ` divides `c - a`. -/
private theorem mu_dvd_sub_padicIntHom (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {y : PreTilt 𝒪[C] p} {c : WittVector p (PreTilt 𝒪[C] p)} (hc : mu p y = mu p ε * c)
    {a : ℤ_[p]} (ha : ∀ N, ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm^[N] y).untilt =
      ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm^[N] ε).untilt ^ (a.toZModPow N).val) :
    mu p ε ∣ c - TauCeti.WittVector.padicIntHom p (PreTilt 𝒪[C] p) a := by
  rw [← Ideal.mem_span_singleton, mem_span_mu_iff ε hε]
  intro j
  have hA : (frobeniusEquiv p (PreTilt 𝒪[C] p))^[j] (TauCeti.WittVector.padicIntHom p _ a) =
      TauCeti.WittVector.padicIntHom p _ a := Function.iterate_fixed
    (by rw [WittVector.frobeniusEquiv_apply, TauCeti.WittVector.frobenius_padicIntHom]) j
  rw [iterate_map_sub, hA, map_sub, sub_eq_zero]
  -- `θ (φ ^ j c) ≡ b ≡ θ a` modulo `p ^ N` for every `N`, with `b ∈ ℕ` congruent to `a`
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : 𝒪[C])})).mpr fun N ↦ ?_
  rw [TauCeti.sModEq_span_singleton_pow_iff]
  simpa using dvd_sub (natCast_pow_dvd_fontaineTheta_iterate_sub ε hε hc (ha N) j)
    (natCast_pow_dvd_fontaineTheta_padicIntHom_sub a N)

/-- **`μ²` divides `g(μ) - χ(g) μ`** for every ring automorphism `g` of `O_C`, where `χ(g) ∈ ℤ_p`
is its cyclotomic character, acting on `A_inf` through `ℤ_p → A_inf`. -/
theorem mu_sq_dvd_smul_mu_sub (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) (g : G) :
    mu p ε ^ 2 ∣ g • mu p ε - TauCeti.WittVector.padicIntHom p (PreTilt 𝒪[C] p)
      (cyclotomicCharacter 𝒪[C] p (MulSemiringAction.toRingEquiv G 𝒪[C] g)) * mu p ε := by
  -- write `g(μ) = μ c`; then `μ` divides `c - χ(g)`
  obtain ⟨c, hc⟩ := mu_dvd_smul_mu ε hε g
  rw [smul_mu] at hc ⊢
  obtain ⟨e, he⟩ := mu_dvd_sub_padicIntHom ε hε hc (untilt_iterate_frobeniusEquiv_symm_smul ε hε g)
  exact ⟨e, by linear_combination hc + mu p ε * he⟩

end PerfectoidField

end PreTilt
