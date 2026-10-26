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

The proof reads off Fourier coefficients. The `n`th coefficient of `E_k^(psi, phi, t)`, `n > 0`,
is the twisted divisor sum `sigma_(k-1)^(psi,phi)(n / t)` when `t ∣ n` and `0` otherwise. Given
a vanishing finite combination, let `t₀` be the least raising parameter carrying a nonzero
coefficient. At the indices `t₀ m` with `m` prime to `N` only the series with `t = t₀` contribute,
since every `t` divides `N`; so the twisted divisor sums of their character pairs satisfy a linear
relation on the integers prime to `N`. Raised to level `N`, distinct primitive characters stay
distinct, because the conductor of a primitive character is its modulus; hence that relation is
trivial by the independence of twisted divisor sums
(`DirichletCharacter.linearIndependent_twistedDivisorSum`).

## Main results

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

/-- **Linear independence of the Eisenstein series with character** (Diamond–Shurman,
Theorem 4.5.2): in weight `k ≥ 3`, the normalized raised series `E_k^(psi, phi, t)` attached to
distinct indices are linearly independent. -/
theorem linearIndependent_form (hk : 3 ≤ (k : ℤ)) :
    LinearIndependent ℂ fun a : CharIndex N k ↦ a.form hk := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra! hne
  obtain ⟨a₀, ha₀s, ha₀⟩ := hne
  -- The least raising parameter `t₀` among the indices with a nonzero coefficient.
  set s' := s.filter (g · ≠ 0)
  have hs' : (s'.image (·.t)).Nonempty :=
    ⟨a₀.t, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha₀s, ha₀⟩)⟩
  obtain ⟨a₁, ha₁, ht₁⟩ := Finset.mem_image.mp (Finset.min'_mem _ hs')
  set t₀ := (s'.image (·.t)).min' hs'
  have ht₀ : t₀ ≠ 0 := ht₁ ▸ ne_zero_of_dvd_ne_zero (NeZero.ne N) a₁.t_dvd
  -- At `t₀ m` with `m` prime to `N`, only the indices with `t = t₀` contribute.
  have hcoeff (m : ℕ) (hm : m.Coprime N) :
      ∑ a ∈ s with a.t = t₀, g a * DirichletCharacter.twistedDivisorSum (k - 1) a.psi a.phi m =
        0 := by
    rcases eq_or_ne m 0 with rfl | hm₀
    · simp
    have h := congrArg ((PowerSeries.coeff (t₀ * m)).comp
      (ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) (k : ℤ)))
      hsum
    simp only [map_sum, map_smul, map_zero, LinearMap.comp_apply,
      ModularForm.qExpansionLinearMap_apply, smul_eq_mul,
      qExpansion_form_coeff _ hk (mul_ne_zero ht₀ hm₀)] at h
    rw [Finset.sum_filter]
    refine (Finset.sum_congr rfl fun a ha ↦ ?_).trans h
    rcases eq_or_ne (g a) 0 with hga | hga
    · simp [hga]
    have hle : t₀ ≤ a.t :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha, hga⟩))
    by_cases hdvd : a.t ∣ t₀ * m
    · have hat : a.t = t₀ := le_antisymm
        (Nat.le_of_dvd (Nat.pos_of_ne_zero ht₀)
          (((hm.coprime_dvd_right a.t_dvd).symm).dvd_of_dvd_mul_right hdvd)) hle
      simp [hat, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero ht₀)]
    · have hat : a.t ≠ t₀ := fun hat ↦ hdvd (hat ▸ dvd_mul_right _ _)
      simp [hat, hdvd]
  -- The character pairs of the indices with `t = t₀`, raised to level `N`, are distinct.
  have hli := DirichletCharacter.linearIndependent_twistedDivisorSum (R := ℂ) (N := N)
    (ι := {a : CharIndex N k // a.t = t₀}) (e := k - 1) (by omega)
    (psi := fun a ↦ a.1.psi.changeLevel a.1.u_dvd) (phi := fun a ↦ a.1.phi.changeLevel a.1.v_dvd)
    fun a b hab ↦ Subtype.ext <| eq_of_changeLevel_eq (a.2.trans b.2.symm)
      (congrArg Prod.fst hab) (congrArg Prod.snd hab)
  refine (Finset.mem_filter.mp ha₁).2 <|
    linearIndependent_iff'.mp hli (s.subtype (·.t = t₀)) (fun a ↦ g a.1) ?_ ⟨a₁, ht₁⟩
      (Finset.mem_subtype.mpr (Finset.mem_filter.mp ha₁).1)
  ext ⟨m, hm⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    DirichletCharacter.twistedDivisorSum_changeLevel_of_coprime _ _ _ _ _ hm]
  rw [Finset.sum_subtype_eq_sum_filter (fun a ↦ g a *
    DirichletCharacter.twistedDivisorSum (k - 1) a.psi a.phi m)]
  exact hcoeff m hm

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
