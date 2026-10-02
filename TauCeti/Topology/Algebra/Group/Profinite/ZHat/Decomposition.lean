/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Prime.Basic
public import TauCeti.Data.ZMod.Divisibility
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component

/-!
# The product decomposition of the profinite integers

The ring of profinite integers `Additive zHat` is the product of the rings of `ℓ`-adic integers
over all primes `ℓ`: the ring homomorphism `Additive zHat →+* ∀ ℓ : Nat.Primes, ℤ_[ℓ]` whose
components are the `ℓ`-adic components `zHat.component ℓ` is an isomorphism of topological rings
(`zHat.ringEquivPiPadicInt`, with `zHat.continuous_ringEquivPiPadicInt` and
`zHat.continuous_ringEquivPiPadicInt_symm`).

Both halves of the bijectivity are the Chinese remainder theorem at each finite level. A residue
modulo `n` is determined by its reductions modulo the prime powers dividing `n`, and reduction
modulo `ℓ ^ k` factors through the `ℓ`-adic component (`zHat.cast_toZMod_eq_toZModPow_component`),
so a profinite integer is determined by its components (`zHat.ext_of_component`). Conversely, a
family of `ℓ`-adic integers reduces, at each level `n`, to a residue modulo `n` assembled by
Mathlib's `ZMod.equivPi` from its reductions modulo the prime powers exactly dividing `n`; these
residues are compatible along divisibility, hence come from a profinite integer by the limit
property `zHat.existsUnique_forall_toZMod_eq`, whose components are the given family
(`zHat.exists_forall_component_eq`). Continuity of the inverse is the compactness of `zHat`.

The decomposition has idempotents: `zHat.idem ℓ`, written `ω_ℓ` in prose, is the profinite integer
with `ℓ`-adic component `1` and all other components `0`. It is idempotent, orthogonal to the
idempotents of the other primes, multiplication by it keeps the `ℓ`-adic component and kills the
others, and it reduces to `1` modulo every power of `ℓ` and to `0` modulo every `n` prime to `ℓ`.
In particular `ω_2 * (1 - ω_2) = 0` with both factors nonzero: the profinite integers are not a
domain (`zHat.not_isDomain`). The finite sums of the prime idempotents tend to `1`
(`zHat.tendsto_sum_idem`), expressing recovery from the prime factors in the product topology.

## Main definitions

* `TauCeti.zHat.ringEquivPiPadicInt`: the ring isomorphism
  `Additive zHat ≃+* ∀ ℓ : Nat.Primes, ℤ_[ℓ]` with components `zHat.component ℓ`.
* `TauCeti.zHat.idem`: the idempotent `ω_ℓ` of the `ℓ`-adic factor.

## Main results

* `TauCeti.zHat.ext_of_component`, `TauCeti.zHat.exists_forall_component_eq`: a profinite integer
  is determined by its `ℓ`-adic components, and every family of `ℓ`-adic integers occurs.
* `TauCeti.zHat.continuous_ringEquivPiPadicInt`, `TauCeti.zHat.continuous_ringEquivPiPadicInt_symm`:
  the decomposition is an isomorphism of topological rings.
* `TauCeti.zHat.component_idem`, `TauCeti.zHat.isIdempotentElem_idem`,
  `TauCeti.zHat.idem_mul_idem`, `TauCeti.zHat.idem_mul_idem_of_ne`,
  `TauCeti.zHat.idem_mul_eq_self_iff`: the components of `ω_ℓ`, its idempotence and orthogonality,
  and the characterization of `ω_ℓ * a = a`.
* `TauCeti.zHat.toZMod_idem_of_dvd_pow`, `TauCeti.zHat.toZMod_idem_of_not_dvd`: the reductions of
  `ω_ℓ` at the finite levels.
* `TauCeti.zHat.not_isDomain`: the profinite integers are not a domain.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
-/

public section

namespace TauCeti

namespace zHat

universe u

open Additive Multiplicative

section Components

/-- **Reduction modulo a prime power factors through the component.** For `p ^ k ∣ n`, reducing
`a` modulo `n` and then modulo `p ^ k` is reducing the `p`-adic component of `a` modulo `p ^ k`. -/
theorem cast_toZMod_eq_toZModPow_component (n : ℕ+) {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    (h : p ^ k ∣ n) (a : Additive zHat.{u}) :
    (ZMod.cast (toZMod n a) : ZMod (p ^ k)) = PadicInt.toZModPow k (component p a) := by
  rw [toZModPow_component]
  exact cast_toZMod (m := ⟨p ^ k, pow_pos hp.out.pos k⟩) h a

/-- **A profinite integer is determined by its `ℓ`-adic components.** -/
theorem ext_of_component {a b : Additive zHat.{u}}
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], component ℓ a = component ℓ b) : a = b :=
  -- Two residues modulo `n` with the same reductions modulo the prime powers dividing `n` agree,
  -- and each of these reductions is a reduction of a component.
  ext_of_toZMod fun n ↦ ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ by
    have := Fact.mk hp
    rw [cast_toZMod_eq_toZModPow_component n hpk, cast_toZMod_eq_toZModPow_component n hpk, h p]

/-- Two profinite integers are equal exactly when all their `ℓ`-adic components agree. -/
theorem ext_iff_component {a b : Additive zHat.{u}} :
    a = b ↔ ∀ (ℓ : ℕ) [Fact ℓ.Prime], component ℓ a = component ℓ b :=
  ⟨fun h _ _ ↦ by rw [h], ext_of_component⟩

variable (u : ∀ ℓ : Nat.Primes, ℤ_[ℓ])

/-- The residue modulo `n` of a family of `ℓ`-adic integers: the residue whose reduction modulo
`p ^ k`, for each prime power `p ^ k` exactly dividing `n`, is the reduction of the `p`-adic member
of the family, assembled by the Chinese remainder theorem `ZMod.equivPi`. It is the level-`n`
step of `zHat.exists_forall_component_eq`, and is characterized by `zHat.cast_residue`. -/
private noncomputable def residue (n : ℕ+) : ZMod n :=
  (ZMod.equivPi n n.ne_zero).symm fun p ↦
    have hp : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    PadicInt.toZModPow ((n : ℕ).factorization p) (u ⟨p, hp.out⟩)

/-- The reduction of `residue u n` modulo a prime power `p ^ k` dividing `n` is the reduction of
`u p` modulo `p ^ k`. -/
private theorem cast_residue (n : ℕ+) (p : Nat.Primes) {k : ℕ} (hk : k ≠ 0)
    (h : (p : ℕ) ^ k ∣ n) :
    (ZMod.cast (residue u n) : ZMod ((p : ℕ) ^ k)) = PadicInt.toZModPow k (u p) := by
  have hpn : (p : ℕ) ∈ (n : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨p.2, (dvd_pow_self (p : ℕ) hk).trans h, n.ne_zero⟩
  have hk' : k ≤ (n : ℕ).factorization p := (p.2.pow_dvd_iff_le_factorization n.ne_zero).mp h
  -- At the level `p ^ n.factorization p` the residue reduces to the reduction of `u p`, by
  -- construction; cast down to `p ^ k`.
  have hv : ZMod.equivPi n n.ne_zero (residue u n) ⟨p, hpn⟩ =
      PadicInt.toZModPow ((n : ℕ).factorization p) (u p) :=
    congr_fun ((ZMod.equivPi n n.ne_zero).apply_symm_apply _) ⟨p, hpn⟩
  have hcc := RingHom.congr_fun
    (ZMod.castHom_comp (pow_dvd_pow (p : ℕ) hk') (Nat.ordProj_dvd n p)) (residue u n)
  simp only [ZMod.equivPi_apply, RingHom.comp_apply, ZMod.castHom_apply] at hv hcc
  rw [← PadicInt.cast_toZModPow k _ hk', ← hv, hcc]

/-- **Every family of `ℓ`-adic integers is the family of components of a profinite integer.** -/
theorem exists_forall_component_eq :
    ∃ a : Additive zHat.{u}, ∀ ℓ : Nat.Primes, component ℓ a = u ℓ := by
  -- The residues `residue u n` are compatible along divisibility, because both sides have the
  -- same reductions modulo the prime powers dividing the smaller level.
  obtain ⟨a, ha, -⟩ := existsUnique_forall_toZMod_eq (residue u) fun m n h ↦
    ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp hk hpk ↦ by
      have hcc := RingHom.congr_fun (ZMod.castHom_comp hpk h) (residue u n)
      simp only [RingHom.comp_apply, ZMod.castHom_apply] at hcc ⊢
      exact hcc.trans ((cast_residue u n ⟨p, hp⟩ hk (hpk.trans h)).trans
        (cast_residue u m ⟨p, hp⟩ hk hpk).symm)
  refine ⟨a, fun ℓ ↦ ?_⟩
  -- At the levels `ℓ ^ (k + 1)` the component of `a` reduces to the reduction of `u ℓ`; the
  -- level `ℓ ^ 0` follows by casting down.
  have hk (k : ℕ) :
      PadicInt.toZModPow (k + 1) (component ℓ a) = PadicInt.toZModPow (k + 1) (u ℓ) := by
    let n : ℕ+ := ⟨(ℓ : ℕ) ^ (k + 1), pow_pos ℓ.2.pos _⟩
    rw [← cast_toZMod_eq_toZModPow_component n dvd_rfl a, ha n,
      cast_residue u n ℓ k.succ_ne_zero dvd_rfl]
  refine PadicInt.ext_of_toZModPow.mp fun k ↦ ?_
  rw [← PadicInt.cast_toZModPow k (k + 1) k.le_succ, hk k]
  exact PadicInt.cast_toZModPow k (k + 1) k.le_succ (u ℓ)

end Components

section ProductDecomposition

/-- **The product decomposition of the profinite integers.** The ring homomorphism from
`Additive zHat` to `∀ ℓ : Nat.Primes, ℤ_[ℓ]` with components the `ℓ`-adic components
`zHat.component ℓ` is a ring isomorphism: injective by `zHat.ext_of_component` and surjective by
`zHat.exists_forall_component_eq`. It is a homeomorphism (`zHat.continuous_ringEquivPiPadicInt`,
`zHat.continuous_ringEquivPiPadicInt_symm`), so an isomorphism of topological rings. -/
noncomputable def ringEquivPiPadicInt : Additive zHat.{u} ≃+* ∀ ℓ : Nat.Primes, ℤ_[ℓ] :=
  RingEquiv.ofBijective (RingHom.pi fun ℓ : Nat.Primes ↦ component.{u} ℓ)
    ⟨fun a b h ↦ ext_of_component fun ℓ _ ↦ congr_fun h ⟨ℓ, Fact.out⟩,
      fun u ↦ (exists_forall_component_eq u).imp fun _ h ↦ funext fun ℓ ↦ by
        rw [RingHom.pi_apply, h]⟩

/-- The components of the product decomposition are the `ℓ`-adic components. -/
@[simp]
theorem ringEquivPiPadicInt_apply (a : Additive zHat.{u}) (ℓ : Nat.Primes) :
    ringEquivPiPadicInt a ℓ = component ℓ a := by
  rfl

/-- The `ℓ`-adic component of the profinite integer with prescribed components is the prescribed
one. -/
@[simp]
theorem component_ringEquivPiPadicInt_symm (u : ∀ ℓ : Nat.Primes, ℤ_[ℓ]) (ℓ : Nat.Primes) :
    component ℓ (ringEquivPiPadicInt.{u}.symm u) = u ℓ := by
  rw [← ringEquivPiPadicInt_apply, RingEquiv.apply_symm_apply]

/-- The product decomposition is continuous: each component is. -/
theorem continuous_ringEquivPiPadicInt : Continuous ringEquivPiPadicInt.{u} :=
  continuous_pi fun ℓ ↦ by simpa only [ringEquivPiPadicInt_apply] using continuous_component ℓ

/-- The inverse of the product decomposition is continuous: a continuous bijection from the
compact space `Additive zHat` to the Hausdorff space `∀ ℓ, ℤ_[ℓ]` is a homeomorphism. -/
theorem continuous_ringEquivPiPadicInt_symm : Continuous ringEquivPiPadicInt.{u}.symm := by
  rw [← RingEquiv.coe_coe_toEquiv_symm]
  exact continuous_ringEquivPiPadicInt.continuous_symm_of_equiv_compact_to_t2

end ProductDecomposition

section Idempotents

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The idempotent of the `ℓ`-adic factor.** `zHat.idem ℓ`, written `ω_ℓ`, is the profinite
integer with `ℓ`-adic component `1` and all other components `0` (`zHat.component_idem`). -/
noncomputable def idem : Additive zHat.{u} :=
  ringEquivPiPadicInt.symm (Pi.single (⟨ℓ, Fact.out⟩ : Nat.Primes) 1)

/-- Under the product decomposition, `ω_ℓ` is the family with `1` at `ℓ` and `0` elsewhere. -/
@[simp]
theorem ringEquivPiPadicInt_idem :
    ringEquivPiPadicInt (idem.{u} ℓ) = (Pi.single ⟨ℓ, Fact.out⟩ 1 : ∀ ℓ : Nat.Primes, ℤ_[ℓ]) :=
  RingEquiv.apply_symm_apply _ _

/-- The `ℓ`-adic component of `ω_ℓ` is `1`. -/
@[simp]
theorem component_idem_self : component ℓ (idem.{u} ℓ) = 1 :=
  (component_ringEquivPiPadicInt_symm _ ⟨ℓ, Fact.out⟩).trans (Pi.single_eq_same _ _)

/-- The components of `ω_ℓ` at the other primes vanish. -/
@[simp]
theorem component_idem_of_ne {ℓ' : ℕ} [Fact ℓ'.Prime] (h : ℓ' ≠ ℓ) :
    component ℓ' (idem.{u} ℓ) = 0 := by
  refine (component_ringEquivPiPadicInt_symm _ ⟨ℓ', Fact.out⟩).trans ?_
  exact Pi.single_eq_of_ne (ι := Nat.Primes) (fun h' ↦ h (Subtype.mk_eq_mk.mp h')) _

/-- **The components of `ω_ℓ`**: `1` at `ℓ` and `0` at every other prime. -/
theorem component_idem (ℓ' : ℕ) [Fact ℓ'.Prime] :
    component ℓ' (idem.{u} ℓ) = if ℓ' = ℓ then 1 else 0 := by
  split_ifs with h
  · subst h
    exact component_idem_self ℓ'
  · exact component_idem_of_ne ℓ h

/-- `ω_ℓ` is idempotent. -/
theorem isIdempotentElem_idem : IsIdempotentElem (idem.{u} ℓ) :=
  ext_of_component fun p _ ↦ by
    rw [map_mul, component_idem]
    split_ifs <;> simp

/-- `ω_ℓ * ω_ℓ = ω_ℓ`: the idempotence of `ω_ℓ` as a rewrite rule. -/
@[simp]
theorem idem_mul_idem : idem.{u} ℓ * idem ℓ = idem ℓ :=
  (isIdempotentElem_idem ℓ).eq

/-- The idempotents of distinct primes are orthogonal. -/
@[simp]
theorem idem_mul_idem_of_ne {ℓ' : ℕ} [Fact ℓ'.Prime] (h : ℓ ≠ ℓ') :
    idem.{u} ℓ * idem ℓ' = 0 :=
  ext_of_component fun p _ ↦ by
    rw [map_mul, map_zero]
    by_cases hp : p = ℓ
    · subst hp
      rw [component_idem_self, component_idem_of_ne ℓ' h, mul_zero]
    · rw [component_idem_of_ne ℓ hp, zero_mul]

/-- Multiplication by `ω_ℓ` keeps the `ℓ`-adic component. -/
theorem component_idem_mul (a : Additive zHat.{u}) :
    component ℓ (idem ℓ * a) = component ℓ a := by
  rw [map_mul, component_idem_self, one_mul]

/-- Multiplication by `ω_ℓ` kills every other component. -/
theorem component_idem_mul_of_ne {ℓ' : ℕ} [Fact ℓ'.Prime] (h : ℓ' ≠ ℓ)
    (a : Additive zHat.{u}) : component ℓ' (idem ℓ * a) = 0 := by
  rw [map_mul, component_idem_of_ne ℓ h, zero_mul]

/-- **`ω_ℓ * a = a` exactly when every component of `a` other than the `ℓ`-adic one
vanishes.** -/
theorem idem_mul_eq_self_iff (a : Additive zHat.{u}) :
    idem ℓ * a = a ↔ ∀ (ℓ' : ℕ) [Fact ℓ'.Prime], ℓ' ≠ ℓ → component ℓ' a = 0 := by
  refine ⟨fun h ℓ' _ hne ↦ ?_, fun h ↦ ext_of_component fun p _ ↦ ?_⟩
  · rw [← h, component_idem_mul_of_ne ℓ hne]
  · by_cases hp : p = ℓ
    · subst hp
      exact component_idem_mul p a
    · rw [component_idem_mul_of_ne ℓ hp, h p hp]

/-- **Reduction of `ω_ℓ` modulo a power of `ℓ`.** `ω_ℓ` reduces to `1` modulo every `n` dividing a
power of `ℓ`, in particular modulo every `ℓ ^ k`. -/
theorem toZMod_idem_of_dvd_pow {n : ℕ+} {k : ℕ} (h : (n : ℕ) ∣ ℓ ^ k) :
    toZMod n (idem.{u} ℓ) = 1 := by
  rw [← cast_toZMod (n := ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩) h, ← toZModPow_component,
    component_idem_self, map_one]
  exact ZMod.cast_one h

/-- **Reduction of `ω_ℓ` modulo a level prime to `ℓ`.** `ω_ℓ` reduces to `0` modulo every `n` not
divisible by `ℓ`. -/
theorem toZMod_idem_of_not_dvd {n : ℕ+} (h : ¬ ℓ ∣ n) : toZMod n (idem.{u} ℓ) = 0 := by
  -- Modulo every prime power `p ^ k` dividing `n` the reduction is that of the `p`-adic component
  -- of `ω_ℓ`, which vanishes because `p ≠ ℓ`.
  refine ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp hk hpk ↦ ?_
  have := Fact.mk hp
  rw [cast_toZMod_eq_toZModPow_component n hpk, ZMod.cast_zero, component_idem_of_ne, map_zero]
  rintro rfl
  exact h ((dvd_pow_self p hk).trans hpk)

/-- `ω_ℓ` is not zero: its `ℓ`-adic component is `1`. -/
theorem idem_ne_zero : idem.{u} ℓ ≠ 0 := fun h ↦
  zero_ne_one <| by rw [← component_idem_self.{u} ℓ, h, map_zero]

/-- `ω_ℓ` is not one: its components at the other primes vanish. -/
theorem idem_ne_one : idem.{u} ℓ ≠ 1 := fun h ↦ by
  -- A prime other than `ℓ` sees the difference.
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (ℓ + 1)
  have := Fact.mk hpp
  exact one_ne_zero <| by rw [← component_idem_of_ne ℓ (Nat.lt_of_succ_le hp).ne', h, map_one]

/-- **The profinite integers are not a domain**: `ω_2 * (1 - ω_2) = 0` with both factors
nonzero. -/
theorem not_isDomain : ¬ IsDomain (Additive zHat.{u}) := fun _ ↦ by
  have h : idem.{u} 2 * (1 - idem 2) = 0 := by
    rw [mul_sub, mul_one, idem_mul_idem, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact idem_ne_zero 2 h
  · exact idem_ne_one 2 (sub_eq_zero.mp h).symm

end Idempotents

/-- The finite sums of the prime idempotents tend to `1` as the finite set of primes grows. -/
theorem tendsto_sum_idem :
    Filter.Tendsto (fun s : Finset Nat.Primes ↦ ∑ p ∈ s, idem.{u} p)
      Filter.atTop (nhds 1) := by
  classical
  have h : Filter.Tendsto
      (fun s : Finset Nat.Primes ↦ ringEquivPiPadicInt (∑ p ∈ s, idem.{u} p))
      Filter.atTop (nhds 1) := by
    refine tendsto_pi_nhds.mpr fun p ↦ ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop ({p} : Finset Nat.Primes)] with s hs
    have hp : p ∈ s := hs (Finset.mem_singleton_self p)
    simp only [ringEquivPiPadicInt_apply, map_sum, component_idem]
    simp_rw [Nat.Primes.coe_nat_inj]
    simp [hp]
  simpa only [Function.comp_def, RingEquiv.symm_apply_apply, map_one] using
    continuous_ringEquivPiPadicInt_symm.{u}.continuousAt.tendsto.comp h

end zHat

end TauCeti
