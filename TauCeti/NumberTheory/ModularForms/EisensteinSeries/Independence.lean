/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Subspace
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Linear independence of the Eisenstein series with character

In weight `k ≥ 3`, the normalized raised Eisenstein series `E_k^(psi, phi, t)`, indexed by
primitive, parity-compatible characters `psi` modulo `u` and `phi` modulo `v` and a raising
parameter `t` with `tuv ∣ N`, are linearly independent in `M_k(Γ₁(N))`
(Diamond–Shurman, Theorem 4.5.2). Consequently the Eisenstein subspace of `M_k(N, chi)` spanned
by the series of nebentypus `chi` has dimension the number of their indices.

The proof reads off Fourier coefficients, and its core is a statement about sequences, shared with
weight two. The `n`th coefficient of `E_k^(psi, phi, t)`, `n > 0`,
is the twisted divisor sum `sigma_(k-1)^(psi,phi)(n / t)` when `t ∣ n` and `0` otherwise. Given
a vanishing finite combination, let `t₀` be the least raising parameter carrying a nonzero
coefficient. At the indices `t₀ m` with `m` prime to `N` only the series with `t = t₀` contribute,
since every `t` divides `N`; so the twisted divisor sums of their character pairs satisfy a linear
relation on the integers prime to `N`. Raised to level `N`, distinct primitive characters stay
distinct, because the conductor of a primitive character is its modulus; hence that relation is
trivial by the independence of twisted divisor sums
(`DirichletCharacter.linearIndependent_twistedDivisorSum`).

At exponent `0`, the exponent of weight one, the twisted divisor sums are symmetric in the two
characters, so the sequences of an index `(psi, phi, t)` and of its exchange `(phi, psi, t)`
coincide. The same argument, with the independence of these sums over distinct unordered pairs of
characters (`DirichletCharacter.linearIndependent_twistedDivisorSum_zero`), shows that this is the
only coincidence.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.linearIndependent_twistedDivisorSum`: the sequences
  `n ↦ sigma_e^(psi,phi)(n / t)`, supported on the multiples of `t`, of distinct indices are
  linearly independent.
* `TauCeti.EisensteinSeries.CharIndex.linearIndepOn_twistedDivisorSum_zero`: at exponent `0`,
  the sequences of a set of indices containing no index together with a different exchange are
  linearly independent.
* `TauCeti.EisensteinSeries.CharIndex.linearIndependent_form`: the series `E_k^(psi, phi, t)`
  are linearly independent.
* `TauCeti.EisensteinSeries.CharIndex.linearIndependent_inCharSpace`: so are those of a fixed
  nebentypus `chi`, inside `M_k(N, chi)`.
* `TauCeti.finrank_eisensteinSubspace`: the Eisenstein subspace of `M_k(N, chi)` has dimension
  the number of indices with nebentypus `chi`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 4.5, Theorem 4.5.2.
-/

public section

noncomputable section

namespace TauCeti.EisensteinSeries.CharIndex

variable {N k : ℕ} [NeZero N]

/-- The reduction to a fixed raising parameter: the sequences `n ↦ sigma_e^(psi,phi)(n / t)`,
supported on the multiples of `t`, of the indices in `S` are linearly independent as soon as, for
each `t₀`, the twisted divisor sums of the character pairs raised to level `N` of the indices in
`S` with `t = t₀` are linearly independent on the integers prime to `N`. -/
private theorem linearIndepOn_twistedDivisorSum_of_forall {e : ℕ} {S : Set (CharIndex N k)}
    (h : ∀ t₀, LinearIndepOn ℂ (fun (a : CharIndex N k) (n : {n : ℕ // n.Coprime N}) ↦
      DirichletCharacter.twistedDivisorSum e (a.psi.changeLevel a.u_dvd)
        (a.phi.changeLevel a.v_dvd) n) {a | a ∈ S ∧ a.t = t₀}) :
    LinearIndepOn ℂ (fun (a : CharIndex N k) (n : {n : ℕ // n ≠ 0}) ↦
      if a.t ∣ (n : ℕ) then DirichletCharacter.twistedDivisorSum e a.psi a.phi (n / a.t)
      else 0) S := by
  classical
  rw [LinearIndepOn, linearIndependent_iff']
  intro s g hsum
  by_contra! hne
  obtain ⟨a₀, ha₀s, ha₀⟩ := hne
  -- The least raising parameter `t₀` among the indices with a nonzero coefficient.
  set s' := s.filter (g · ≠ 0)
  have hs' : (s'.image (·.1.t)).Nonempty :=
    ⟨a₀.1.t, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha₀s, ha₀⟩)⟩
  obtain ⟨a₁, ha₁, ht₁⟩ := Finset.mem_image.mp (Finset.min'_mem _ hs')
  set t₀ := (s'.image (·.1.t)).min' hs'
  have ht₀ : t₀ ≠ 0 := ht₁ ▸ ne_zero_of_dvd_ne_zero (NeZero.ne N) a₁.1.t_dvd
  -- At `t₀ m` with `m` prime to `N`, only the indices with `t = t₀` contribute.
  have hcoeff (m : ℕ) (hm : m.Coprime N) (hm₀ : m ≠ 0) :
      ∑ a ∈ s with a.1.t = t₀,
        g a * DirichletCharacter.twistedDivisorSum e a.1.psi a.1.phi m = 0 := by
    have h := congrFun hsum ⟨t₀ * m, mul_ne_zero ht₀ hm₀⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [Finset.sum_filter]
    refine (Finset.sum_congr rfl fun a ha ↦ ?_).trans h
    rcases eq_or_ne (g a) 0 with hga | hga
    · simp [hga]
    have hle : t₀ ≤ a.1.t :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha, hga⟩))
    by_cases hdvd : a.1.t ∣ t₀ * m
    · have hat : a.1.t = t₀ := le_antisymm
        (Nat.le_of_dvd (Nat.pos_of_ne_zero ht₀)
          (((hm.coprime_dvd_right a.1.t_dvd).symm).dvd_of_dvd_mul_right hdvd)) hle
      simp [hat, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero ht₀)]
    · have hat : a.1.t ≠ t₀ := fun hat ↦ hdvd (hat ▸ dvd_mul_right _ _)
      simp [hat, hdvd]
  -- The indices of `S` with `t = t₀`, as a subtype of the subtype `S`.
  let f (a : {a : S // a.1.t = t₀}) : {a | a ∈ S ∧ a.t = t₀} := ⟨a.1.1, a.1.2, a.2⟩
  have hf : Function.Injective f := fun a b hab ↦
    Subtype.ext (Subtype.ext (by simpa [f] using congrArg Subtype.val hab))
  have hli := (h t₀).comp f hf
  refine (Finset.mem_filter.mp ha₁).2 <|
    linearIndependent_iff'.mp hli (s.subtype (·.1.t = t₀)) (fun a ↦ g a.1) ?_ ⟨a₁, ht₁⟩
      (Finset.mem_subtype.mpr (Finset.mem_filter.mp ha₁).1)
  ext ⟨m, hm⟩
  rcases eq_or_ne m 0 with rfl | hm₀
  · simp
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply,
    f, DirichletCharacter.twistedDivisorSum_changeLevel_of_coprime _ _ _ _ _ hm]
  rw [Finset.sum_subtype_eq_sum_filter (fun a ↦ g a *
    DirichletCharacter.twistedDivisorSum e a.1.psi a.1.phi m)]
  exact hcoeff m hm hm₀

/-- The positive Fourier coefficients of the raised Eisenstein series of the indices, as
sequences: the sequences `n ↦ sigma_e^(psi,phi)(n / t)` on the multiples `n` of `t`, zero at the
other positive integers, attached to distinct indices `(psi, phi, t)` are linearly independent
for every exponent `e ≠ 0`. -/
theorem linearIndependent_twistedDivisorSum {e : ℕ} (he : e ≠ 0) :
    LinearIndependent ℂ fun (a : CharIndex N k) (n : {n : ℕ // n ≠ 0}) ↦
      if a.t ∣ (n : ℕ) then DirichletCharacter.twistedDivisorSum e a.psi a.phi (n / a.t)
      else 0 := by
  rw [← linearIndepOn_univ_iff]
  refine linearIndepOn_twistedDivisorSum_of_forall fun t₀ ↦ ?_
  -- The character pairs of the indices with `t = t₀`, raised to level `N`, are distinct.
  exact DirichletCharacter.linearIndependent_twistedDivisorSum (R := ℂ) (N := N) he
    fun a b hab ↦ Subtype.ext <| eq_of_changeLevel_eq (a.2.2.trans b.2.2.symm)
      (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- At exponent zero, where the twisted divisor sums are symmetric in the two characters, the
sequences `n ↦ sigma_0^(psi,phi)(n / t)` on the multiples `n` of `t`, zero at the other positive
integers, are linearly independent on any set `S` of indices containing no index together with
a different exchange `(phi, psi, t)`. -/
theorem linearIndepOn_twistedDivisorSum_zero {S : Set (CharIndex N k)}
    (hS : ∀ a ∈ S, a.swap ∈ S → a.swap = a) :
    LinearIndepOn ℂ (fun (a : CharIndex N k) (n : {n : ℕ // n ≠ 0}) ↦
      if a.t ∣ (n : ℕ) then DirichletCharacter.twistedDivisorSum 0 a.psi a.phi (n / a.t)
      else 0) S := by
  refine linearIndepOn_twistedDivisorSum_of_forall fun t₀ ↦ ?_
  -- The character pairs of the indices with `t = t₀`, raised to level `N`, are distinct as
  -- unordered pairs: equal in the other order, the second index is the exchange of the first.
  refine DirichletCharacter.linearIndependent_twistedDivisorSum_zero (R := ℂ) (N := N)
    fun a b hab ↦ Subtype.ext ?_
  have ht : a.1.t = b.1.t := a.2.2.trans b.2.2.symm
  rcases Sym2.eq_iff.mp hab with ⟨hpsi, hphi⟩ | ⟨hpsi, hphi⟩
  · exact eq_of_changeLevel_eq ht hpsi hphi
  · have hab' : a.1 = b.1.swap := eq_of_changeLevel_eq ht hpsi hphi
    rw [hab', hS b.1 b.2.1 (hab' ▸ a.2.1)]

/-- **Linear independence of the Eisenstein series with character** (Diamond–Shurman,
Theorem 4.5.2): in weight `k ≥ 3`, the normalized raised series `E_k^(psi, phi, t)` attached to
distinct indices are linearly independent. -/
theorem linearIndependent_form (hk : 3 ≤ (k : ℤ)) :
    LinearIndependent ℂ fun a : CharIndex N k ↦ a.form hk := by
  refine LinearIndependent.of_comp (LinearMap.pi fun n : {n : ℕ // n ≠ 0} ↦
    (PowerSeries.coeff (n : ℕ)).comp (ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods_Gamma1_map N) (k : ℤ))) ?_
  convert linearIndependent_twistedDivisorSum (N := N) (k := k) (e := k - 1) (by omega) using 1
  ext a n
  simp [qExpansion_form_coeff _ hk n.2]

/-- In weight `k ≥ 3`, the Eisenstein series `E_k^(psi, phi, t)` of nebentypus `chi` are linearly
independent in the character space `M_k(N, chi)`. -/
theorem linearIndependent_inCharSpace (chi : (ZMod N)ˣ →* ℂˣ) (hk : 3 ≤ (k : ℤ)) :
    LinearIndependent ℂ fun a : {a : CharIndex N k // a.nebentypus = chi} ↦
      a.1.inCharSpace hk a.2 := by
  refine LinearIndependent.of_comp (modFormCharSpace (k : ℤ) chi).subtype ?_
  convert (linearIndependent_form (N := N) hk).comp _ Subtype.val_injective using 1
  ext a
  simp

end TauCeti.EisensteinSeries.CharIndex

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N k : ℕ} [NeZero N]

/-- In weight `k ≥ 3`, the Eisenstein subspace of `M_k(N, chi)` has dimension the number of
indices `(psi, phi, t)` with induced nebentypus `chi`. -/
theorem finrank_eisensteinSubspace (chi : (ZMod N)ˣ →* ℂˣ) (hk : 3 ≤ (k : ℤ)) :
    Module.finrank ℂ (eisensteinSubspace chi hk) =
      Nat.card {a : CharIndex N k // a.nebentypus = chi} := by
  have hli := CharIndex.linearIndependent_inCharSpace chi hk
  rw [eisensteinSubspace_def, Module.finrank, rank_span hli,
    Cardinal.mk_range_eq _ hli.injective]
  rfl

end TauCeti
