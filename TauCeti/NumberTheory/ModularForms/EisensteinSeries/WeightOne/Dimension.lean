/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Subspace
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.Data.Nat.Factorization.GcdSplit
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Bounds
import TauCeti.NumberTheory.ModularForms.CharacterDecomp
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Gamma1
import TauCeti.NumberTheory.ModularForms.Cusps.Weight.One
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.ConstantTerm
import TauCeti.NumberTheory.ModularForms.Parity
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The weight-one cusp–Eisenstein decomposition with nebentypus

In weight one the Eisenstein series `E₁^{ψ,φ,t}` of the indices `(ψ, φ, t)` of nebentypus `χ`
(`TauCeti.EisensteinSeries.CharIndex.weightOneForm`) span a complement of the cusp forms in
`M₁(N, χ)`: this is the decomposition `M₁(N, χ) = S₁(N, χ) ⊕ E₁(N, χ)`
(`TauCeti.isCompl_weightOneEisensteinSubspace_range_cuspToModFormCharSpace`). At the levels
`N ∉ {1, 2, 4}` it gives

`2 dim M₁(Γ₁(N)) = 2 dim S₁(Γ₁(N)) + ε∞(Γ₁(N))`,

where `ε∞(Γ₁(N))` is the number of cusps of `Γ₁(N)`.

The series are known to span a space of half the number of indices
(`TauCeti.EisensteinSeries.two_mul_finrank_span_range_weightOneForm`), and a subspace of `M₁`
meeting the cusp forms only in `0` has at most that dimension
(`TauCeti.ModularForm.two_mul_finrank_le_card_cuspOrbit_of_disjoint`). So the decomposition comes
down to directness: a combination of the series that is a cusp form is zero. That is the
linear independence of the constant-term vectors of the series
(`TauCeti.EisensteinSeries.CharIndex.linearIndependent_constantTerms_weightOneForm`), proved as
follows.

Each series equals the series of the exchanged index (`CharIndex.weightOneForm_swap`), so it
suffices to take the indices whose first character `ψ` is even. At the cusp `1 / c` the constant
term of `E₁^{ψ,φ,t}` (`TauCeti.EisensteinSeries.constantTermAt_charE1MFRaise`) is

`A · P_{ψ,φ,t}(c) - B · P_{φ,ψ,t}(c)`, with `A ≠ 0`, where
`P_{ψ,φ,t}(c) = (g / t) · [v ∣ c / g] · ψ(-c / (g v)) · φ⁻¹(t / g)` and `g = gcd(c, t)`.

* Replacing `c` by `c m` with `m` prime to `N` multiplies `P_{ψ,φ,t}` by `ψ(m)` and `P_{φ,ψ,t}`
  by `φ(m)`. By orthogonality of the characters modulo `N`, a vanishing combination therefore
  vanishes on the part attached to each even character `ψ`. The terms `P_{φ,ψ,t}` drop out there,
  since `φ` is odd. Inside a fixed nebentypus, `ψ` determines `φ`, so only the raising parameter
  `t` still varies.
* The profiles `P_t = P_{ψ,φ,t}` for distinct `t` are linearly independent. For `s ≥ 1` put
  `Λ_s(H) = ∑_{d ∣ s squarefree} μ(d) ψ(d) H(v s / d)`. Raising the `p`-adic valuation of `c`
  beyond that of `t v` multiplies `P_t(c)` by `ψ(p)`, so `Λ_s(P_t) = 0` unless `s ∣ t`. Moreover
  `Λ_t(P_t) = ψ(-1) ∏_{p ∣ t} (1 - ψ(p) φ⁻¹(p) / p) ≠ 0`. Applying `Λ_t` for the largest `t`
  carrying a nonzero coefficient shows that coefficient is zero.

Diamond–Shurman obtain the upper bound on the dimension from the Riemann–Roch theorem. Here it
comes instead from the quadratic relation between constant terms of weight-one forms
(`TauCeti.NumberTheory.ModularForms.Cusps.Weight.One`).

## Main results

* `TauCeti.EisensteinSeries.CharIndex.linearIndependent_constantTerms_weightOneForm`: the
  constant-term vectors of the series of nebentypus `χ` with even first character are linearly
  independent.
* `TauCeti.disjoint_weightOneEisensteinSubspace_range_cuspToModFormCharSpace`: directness,
  `E₁(N, χ) ∩ S₁(N, χ) = 0`.
* `TauCeti.EisensteinSeries.isCompl_span_range_weightOneForm_cuspFormSubmodule`: the series span a
  complement of the cusp forms in `M₁(Γ₁(N))`.
* `two_mul_finrank_weight_one_modularForm_Gamma1_eq_two_mul_finrank_cuspForm_add_card_cuspOrbit`,
  in the namespace `TauCeti`: `2 dim M₁(Γ₁(N)) = 2 dim S₁(Γ₁(N)) + ε∞(Γ₁(N))` for
  `N ∉ {1, 2, 4}`.
* `TauCeti.weightOneEisensteinSubspace_eq_comap_span_range_weightOneForm`: the weight-one
  Eisenstein subspace of `M₁(N, χ)` consists of the forms of nebentypus `χ` in the span of all the
  series.
* `TauCeti.isCompl_weightOneEisensteinSubspace_range_cuspToModFormCharSpace`: the weight-one
  cusp–Eisenstein decomposition `M₁(N, χ) = S₁(N, χ) ⊕ E₁(N, χ)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8,
  Theorem 4.8.1, and §3.8 for the cusps of `Γ₁(N)`.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public noncomputable section

open Complex ModularForm CongruenceSubgroup Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.EisensteinSeries

/-! ### The constant-term profiles -/

section Profile

variable {u v : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The part of the constant term of `E₁^{ψ,φ,t}` at the cusp `1 / c` that carries the
character `ψ`: `(g / t) · [v ∣ c / g] · ψ(-c / (g v)) · φ⁻¹(t / g)` with `g = gcd(c, t)`. -/
private def profile (t c : ℕ) : ℂ :=
  (c.gcd t : ℂ) / t * if v ∣ c / c.gcd t then
    ψ (-((c / c.gcd t / v : ℕ) : ZMod u)) * φ⁻¹ ((t / c.gcd t : ℕ) : ZMod v) else 0

/-- Multiplying `c` by `m` multiplies the profile by `ψ(m)`, as long as this does not change the
gcd of `c` with `t v`. -/
private theorem profile_mul [NeZero v] {t c m : ℕ} (h : (t * v).gcd (c * m) = (t * v).gcd c) :
    profile ψ φ t (c * m) = ψ m * profile ψ φ t c := by
  have hg : (c * m).gcd t = c.gcd t := by
    have key (x : ℕ) : x.gcd t = ((t * v).gcd x).gcd t := by
      rw [Nat.gcd_assoc, Nat.gcd_eq_right ((Nat.gcd_dvd_right x t).mul_right v)]
    rw [key, h, ← key]
  have hdvd (x : ℕ) (hx : c.gcd t ∣ x) :
      v ∣ x / c.gcd t ↔ c.gcd t * v ∣ (t * v).gcd x := by
    rw [Nat.dvd_div_iff_mul_dvd hx, Nat.dvd_gcd_iff]
    exact ⟨fun h ↦ ⟨Nat.mul_dvd_mul_right (Nat.gcd_dvd_right c t) v, h⟩, fun h ↦ h.2⟩
  have hc : c.gcd t ∣ c := Nat.gcd_dvd_left c t
  have hiff : v ∣ c * m / c.gcd t ↔ v ∣ c / c.gcd t := by
    rw [hdvd _ (hc.mul_right m), hdvd _ hc, h]
  unfold profile
  simp only [hg]
  by_cases hv : v ∣ c / c.gcd t
  · obtain ⟨w, hw⟩ := hv
    have h2 : c * m / c.gcd t = v * (w * m) := by
      rw [Nat.mul_div_right_comm hc, hw, mul_assoc]
    have hv0 : 0 < v := Nat.pos_of_ne_zero (NeZero.ne v)
    simp only [hw, h2, dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ hv0]
    push_cast
    rw [← neg_mul, map_mul]
    ring
  · simp [hv, hiff.not.mpr hv]

/-- The profile at `c = v t / d` for a divisor `d` of `t` is `ψ(-1) φ⁻¹(d) / d`. -/
private theorem profile_mul_div [NeZero v] {t d : ℕ} (ht : t ≠ 0) (hd : d ∣ t) :
    profile ψ φ t (v * (t / d)) = ψ (-1) * (φ⁻¹ d / d) := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul ht
  have he0 : 0 < e := Nat.pos_of_ne_zero (right_ne_zero_of_mul ht)
  have hv0 : 0 < v := Nat.pos_of_ne_zero (NeZero.ne v)
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  unfold profile
  rw [Nat.gcd_mul_right v e d]
  by_cases hvd : v.Coprime d
  · rw [Nat.Coprime.gcd_eq_one hvd, one_mul, Nat.mul_div_cancel _ he0, Nat.mul_div_cancel _ he0,
      Nat.div_self hv0]
    have he : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he0.ne'
    simp only [dvd_refl, ite_true, Nat.cast_one]
    push_cast
    field_simp
  · -- `v` and `d` share a factor, so the divisibility fails and `φ⁻¹(d) = 0`
    have hk : 1 < v.gcd d := by
      have := Nat.gcd_pos_of_pos_left d hv0
      unfold Nat.Coprime at hvd
      omega
    have hndvd : ¬ v ∣ v * e / (v.gcd d * e) := by
      rw [Nat.mul_div_mul_right _ _ he0]
      intro h
      have hpos : 0 < v / v.gcd d :=
        Nat.div_pos (Nat.le_of_dvd hv0 (Nat.gcd_dvd_left v d)) (by omega)
      have := Nat.le_of_dvd hpos h
      have := Nat.div_lt_self hv0 hk
      omega
    have hφ : φ⁻¹ (d : ZMod v) = 0 :=
      MulChar.map_nonunit _ fun h ↦ hvd ((ZMod.isUnit_iff_coprime d v).mp h).symm
    simp [hndvd, hφ]

/-- The separating functional `Λ_s(H) = ∑_{d ∣ s squarefree} μ(d) ψ(d) H(v s / d)`, written as a
sum over the sets of prime factors of `s`. -/
private def separator (v s : ℕ) (H : ℕ → ℂ) : ℂ :=
  ∑ D ∈ s.primeFactors.powerset, (∏ p ∈ D, -ψ p) * H (v * (s / ∏ p ∈ D, p))

/-- The separating functional is linear. -/
private theorem separator_sum {s : ℕ} {T : Finset ℕ} (l : ℕ → ℂ) (H : ℕ → ℕ → ℂ) :
    separator ψ v s (fun c ↦ ∑ t ∈ T, l t * H t c) =
      ∑ t ∈ T, l t * separator ψ v s (H t) := by
  unfold separator
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- `Λ_t(P_t) = ψ(-1) ∏_{p ∣ t} (1 - ψ(p) φ⁻¹(p) / p)`. -/
private theorem separator_profile_self [NeZero v] {t : ℕ} (ht : t ≠ 0) :
    separator ψ v t (profile ψ φ t) =
      ψ (-1) * ∏ p ∈ t.primeFactors, (1 - ψ p * φ⁻¹ p / p) := by
  unfold separator
  have hterm (D : Finset ℕ) (hD : D ∈ t.primeFactors.powerset) :
      (∏ p ∈ D, -ψ p) * profile ψ φ t (v * (t / ∏ p ∈ D, p)) =
        ψ (-1) * ((∏ p ∈ D, -(ψ p * φ⁻¹ p / p)) * ∏ p ∈ t.primeFactors \ D, 1) := by
    rw [profile_mul_div ψ φ ht (Nat.prod_dvd_of_subset_primeFactors (Finset.mem_powerset.mp hD))]
    simp only [Finset.prod_const_one, mul_one, Nat.cast_prod, map_prod]
    rw [← Finset.prod_div_distrib, mul_left_comm, ← Finset.prod_mul_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun p _ ↦ by ring)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.prod_add]
  simp_rw [neg_add_eq_sub]

/-- `Λ_s(P_t) = 0` unless `s ∣ t`: at a prime `p` dividing `s` more often than `t`, the terms of
`d` and `d p` cancel. -/
private theorem separator_profile_of_not_dvd [NeZero v] {s t : ℕ} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : ¬ s ∣ t) : separator ψ v s (profile ψ φ t) = 0 := by
  obtain ⟨p, hp⟩ : ∃ p, t.factorization p < s.factorization p := by
    by_contra! H
    exact h ((Nat.factorization_le_iff_dvd hs ht).mp H)
  have hps : p ∈ s.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hps
  unfold separator
  rw [← Finset.insert_erase hps, Finset.sum_powerset_insert (Finset.notMem_erase p _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun D hD ↦ ?_
  have hDs : D ⊆ s.primeFactors := (Finset.mem_powerset.mp hD).trans (Finset.erase_subset _ _)
  have hpD : p ∉ D := fun h ↦ Finset.notMem_erase p _ (Finset.mem_powerset.mp hD h)
  rw [Finset.prod_insert hpD, Finset.prod_insert hpD]
  -- `s = p (∏ D) w`, where `p` divides `w` at least as often as it divides `t`
  obtain ⟨w, hw⟩ : p * ∏ q ∈ D, q ∣ s := by
    simpa [Finset.prod_insert hpD] using
      Nat.prod_dvd_of_subset_primeFactors (n := s) (Finset.insert_subset hps hDs)
  have hD0 : ∏ q ∈ D, q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq ↦
    (Nat.prime_of_mem_primeFactors (hDs hq)).ne_zero
  have hw' : s / ∏ q ∈ D, q = w * p := by
    rw [hw, mul_comm p, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hD0), mul_comm]
  have hw'' : s / (p * ∏ q ∈ D, q) = w := by
    rw [hw, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (mul_ne_zero hpp.ne_zero hD0))]
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hs (by simpa using hw)
  have hpD' : ¬ p ∣ ∏ q ∈ D, q := by
    rw [Prime.dvd_finsetProd_iff hpp.prime]
    rintro ⟨q, hq, hpq⟩
    exact hpD ((Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors (hDs hq))).mp
      hpq ▸ hq)
  have hwp : t.factorization p ≤ w.factorization p := by
    have := congrArg (fun n ↦ n.factorization p) hw
    simp only [Nat.factorization_mul (mul_ne_zero hpp.ne_zero hD0) hw0,
      Nat.factorization_mul hpp.ne_zero hD0, Finsupp.add_apply, hpp.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hpD'] at this
    omega
  have hgcd : (t * v).gcd (v * w * p) = (t * v).gcd (v * w) := by
    refine Nat.gcd_mul_prime_eq_of_factorization_le hpp (mul_ne_zero ht (NeZero.ne v))
      (mul_ne_zero (NeZero.ne v) hw0) ?_
    rw [Nat.factorization_mul ht (NeZero.ne v), Nat.factorization_mul (NeZero.ne v) hw0]
    simp only [Finsupp.add_apply]
    omega
  rw [hw', hw'', ← mul_assoc, profile_mul ψ φ hgcd]
  ring

/-- **The profiles of distinct raising parameters are linearly independent.** -/
private theorem eq_zero_of_forall_sum_profile_eq_zero [NeZero v] {T : Finset ℕ} (hT : 0 ∉ T)
    {l : ℕ → ℂ} (h : ∀ c, ∑ t ∈ T, l t * profile ψ φ t c = 0) : ∀ t ∈ T, l t = 0 := by
  by_contra! hne
  obtain ⟨t₁, ht₁T, ht₁⟩ := hne
  -- the largest raising parameter carrying a nonzero coefficient
  have hne : (T.filter (l · ≠ 0)).Nonempty := ⟨t₁, Finset.mem_filter.mpr ⟨ht₁T, ht₁⟩⟩
  set t₀ := (T.filter (l · ≠ 0)).max' hne
  have ht₀ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  have ht₀0 : t₀ ≠ 0 := fun h0 ↦ hT (h0 ▸ ht₀.1)
  have hsum := separator_sum ψ (v := v) (s := t₀) (T := T) l (profile ψ φ)
  simp_rw [h] at hsum
  rw [Finset.sum_eq_single t₀ _ (fun h ↦ (h ht₀.1).elim), separator_profile_self ψ φ ht₀0]
    at hsum
  · unfold separator at hsum
    simp only [mul_zero, Finset.sum_const_zero] at hsum
    refine ht₀.2 ((mul_eq_zero.mp hsum.symm).resolve_right (mul_ne_zero (fun h ↦ ?_)
      (Finset.prod_ne_zero_iff.mpr fun p hp ↦ DirichletCharacter.one_sub_mul_div_natCast_ne_zero
        ψ φ⁻¹ (Nat.prime_of_mem_primeFactors hp).one_lt)))
    simpa [h] using ψ.norm_neg_one
  · intro t htT htt₀
    rcases eq_or_ne (l t) 0 with hl | hl
    · rw [hl, zero_mul]
    have ht0 : t ≠ 0 := fun h0 ↦ hT (h0 ▸ htT)
    have hle : t ≤ t₀ := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨htT, hl⟩)
    have hdvd : ¬ t₀ ∣ t := fun hd ↦
      htt₀ (le_antisymm hle (Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hd))
    rw [separator_profile_of_not_dvd ψ φ ht₀0 ht0 hdvd, mul_zero]

end Profile

/-! ### Constant terms at the cusps `1 / c` -/

/-- The matrix `!![1, 0; c, 1]`, which represents the cusp `1 / c`. -/
private def lowerUnipotent (c : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (c : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

/-- The constant term of `E₁^{ψ,φ,t}` at the cusp `1 / c` in terms of the two profiles. -/
private theorem constantTermAt_lowerUnipotent_charE1MFRaise {u v N : ℕ} [NeZero u] [NeZero v]
    [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v) (hψ : ψ.IsPrimitive)
    (hφ : φ.IsPrimitive) {t : ℕ} (htuv : t * (u * v) ∣ N) (c : ℕ) :
    constantTermAt (lowerUnipotent c) (charE1MFRaise ψ φ t htuv) =
      (((u : ℂ) * v)⁻¹ * ∑ j : ZMod (u * v), ψ (j.val : ZMod u) * φ⁻¹ (j.val : ZMod v) *
          (π * cot (π * (j.val / (u * v))))) * profile ψ φ t c -
        φ (-1) * (gaussSum ψ ZMod.stdAddChar * gaussSum φ⁻¹ ZMod.stdAddChar / v) *
          (((u : ℂ) * v)⁻¹ * ∑ j : ZMod (u * v), ψ⁻¹ (j.val : ZMod u) * φ (j.val : ZMod v) *
            (π * cot (π * (j.val / (u * v))))) * profile φ ψ t c := by
  rw [constantTermAt_charE1MFRaise ψ φ hψ hφ htuv]
  have h10 : (lowerUnipotent c) 1 0 = c := rfl
  have h00 : (lowerUnipotent c) 0 0 = 1 := rfl
  simp only [h10, h00, mul_one, Int.gcd_natCast_natCast, ← Int.natCast_div,
    Int.natCast_dvd_natCast, Int.cast_natCast, Int.cast_neg, profile]
  have hφ1 (x : ZMod v) : φ x = φ (-1) * φ (-x) := by
    rw [← map_mul, neg_one_mul, neg_neg]
  by_cases hv : v ∣ c / c.gcd t <;> by_cases hu : u ∣ c / c.gcd t <;>
    simp only [hv, hu, ite_true, ite_false, hφ1 (((c / c.gcd t / u : ℕ)) : ZMod v)] <;> ring

namespace CharIndex

variable {N k : ℕ} [NeZero N]

/-- A function of the two characters of an index sees only their raises to level `N`. -/
private theorem apply_eq_of_changeLevel_eq {α : Sort*}
    (F : ∀ {u v : ℕ}, DirichletCharacter ℂ u → DirichletCharacter ℂ v → α) {a b : CharIndex N k}
    (hpsi : a.psi.changeLevel a.u_dvd = b.psi.changeLevel b.u_dvd)
    (hphi : a.phi.changeLevel a.v_dvd = b.phi.changeLevel b.v_dvd) :
    F a.psi a.phi = F b.psi b.phi := by
  have hu := u_eq_of_changeLevel_eq hpsi
  have hv := v_eq_of_changeLevel_eq hphi
  obtain ⟨u, v, t, psi, phi, _, _, _, _⟩ := a
  obtain ⟨u', v', t', psi', phi', _, _, _, _⟩ := b
  dsimp only at hu hv hpsi hphi ⊢
  subst hu hv
  obtain rfl := DirichletCharacter.changeLevel_injective _ hpsi
  obtain rfl := DirichletCharacter.changeLevel_injective _ hphi
  rfl

omit [NeZero N] in
/-- Two indices of the same nebentypus whose first characters have the same raise also have the
same raise of their second characters. -/
private theorem phi_changeLevel_eq_of_nebentypus_eq {a b : CharIndex N k}
    (hneb : a.nebentypus = b.nebentypus)
    (hpsi : a.psi.changeLevel a.u_dvd = b.psi.changeLevel b.u_dvd) :
    a.phi.changeLevel a.v_dvd = b.phi.changeLevel b.v_dvd := by
  rw [nebentypus_def, nebentypus_def, MulChar.toUnitHom_eq, MulChar.toUnitHom_eq] at hneb
  have h := MulChar.equivToUnitHom.injective hneb
  rw [hpsi] at h
  exact mul_left_cancel h

/-- The constant term of the weight-one series of an index at the cusp `1 / c`: a nonzero
multiple of the profile of `(ψ, φ, t)` minus a multiple of the profile of `(φ, ψ, t)`. -/
private theorem exists_constantTermAt_lowerUnipotent_weightOneForm (a : CharIndex N 1) :
    ∃ A B : ℂ, A ≠ 0 ∧ ∀ c : ℕ, constantTermAt (lowerUnipotent c) a.weightOneForm =
      A * profile a.psi a.phi a.t c - B * profile a.phi a.psi a.t c := by
  have : NeZero a.u := NeZero.of_dvd a.u_dvd
  have : NeZero a.v := NeZero.of_dvd a.v_dvd
  have hpar : a.psi (-1) * a.phi (-1) = -1 := by simpa using a.parity
  set κ : ℂ := (2 * (-2 * π * I) / a.v * gaussSum a.phi⁻¹ ZMod.stdAddChar)⁻¹
  have hE : a.weightOneForm = κ • charE1MFRaise a.psi a.phi a.t a.level_dvd := by
    rw [weightOneForm_def, normalizedCharE1MFRaise_eq_smul]
  have hκ : κ ≠ 0 := fun h0 ↦ a.weightOneForm_ne_zero (by rw [hE, h0, zero_smul])
  refine ⟨κ * (((a.u : ℂ) * a.v)⁻¹ * ∑ j : ZMod (a.u * a.v), a.psi (j.val : ZMod a.u) *
      a.phi⁻¹ (j.val : ZMod a.v) * (π * cot (π * (j.val / (a.u * a.v))))),
    κ * (a.phi (-1) * (gaussSum a.psi ZMod.stdAddChar * gaussSum a.phi⁻¹ ZMod.stdAddChar / a.v) *
      (((a.u : ℂ) * a.v)⁻¹ * ∑ j : ZMod (a.u * a.v), a.psi⁻¹ (j.val : ZMod a.u) *
        a.phi (j.val : ZMod a.v) * (π * cot (π * (j.val / (a.u * a.v)))))),
    mul_ne_zero hκ (mul_ne_zero (inv_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne _))
      (Nat.cast_ne_zero.mpr (NeZero.ne _))))
      (DirichletCharacter.sum_mul_inv_mul_pi_mul_cot_ne_zero a.psi a.phi hpar)), fun c ↦ ?_⟩
  rw [hE, _root_.map_smul, constantTermAt_lowerUnipotent_charE1MFRaise a.psi a.phi
    a.psi_primitive a.phi_primitive a.level_dvd c, smul_eq_mul]
  ring

open Classical in
/-- **Separating the characters.** If a combination of the constant terms at the cusps `1 / c`
of the series with even first character vanishes for every `c`, then so does the combination of
the profiles of the indices whose first character raises to a given even character `ρ`. -/
private theorem sum_profile_filter_eq_zero {χ : (ZMod N)ˣ →* ℂˣ}
    {s : Finset {a : CharIndex N 1 // a.nebentypus = χ ∧ a.psi (-1) = 1}}
    {g : {a : CharIndex N 1 // a.nebentypus = χ ∧ a.psi (-1) = 1} → ℂ}
    (A B : CharIndex N 1 → ℂ)
    (hc : ∀ c : ℕ, ∑ a ∈ s, g a * (A a.1 * profile a.1.psi a.1.phi a.1.t c -
      B a.1 * profile a.1.phi a.1.psi a.1.t c) = 0)
    (ρ : DirichletCharacter ℂ N) (hρ : ρ (-1) = 1) (c : ℕ) :
    ∑ a ∈ s with a.1.psi.changeLevel a.1.u_dvd = ρ,
      g a * A a.1 * profile a.1.psi a.1.phi a.1.t c = 0 := by
  -- replacing `c` by `c x` for a unit `x` multiplies the two profiles by the two characters
  have hscale (a : {a : CharIndex N 1 // a.nebentypus = χ ∧ a.psi (-1) = 1}) (x : ZMod N) :
      ρ⁻¹ x * (g a * (A a.1 * profile a.1.psi a.1.phi a.1.t (c * x.val) -
        B a.1 * profile a.1.phi a.1.psi a.1.t (c * x.val))) =
      g a * (A a.1 * profile a.1.psi a.1.phi a.1.t c * (ρ⁻¹ * a.1.psi.changeLevel a.1.u_dvd) x -
        B a.1 * profile a.1.phi a.1.psi a.1.t c * (ρ⁻¹ * a.1.phi.changeLevel a.1.v_dvd) x) := by
    have : NeZero a.1.u := NeZero.of_dvd a.1.u_dvd
    have : NeZero a.1.v := NeZero.of_dvd a.1.v_dvd
    by_cases hx : IsUnit x
    · have hcop : x.val.Coprime N := by simpa using ZMod.val_coe_unit_coprime hx.unit
      have hdvd (w : ℕ) (hw : a.1.t * w ∣ N) :
          (a.1.t * w).gcd (c * x.val) = (a.1.t * w).gcd c :=
        Nat.Coprime.gcd_mul_right_cancel_right c (hcop.coprime_dvd_right hw)
      rw [profile_mul _ _ (hdvd _ ((Nat.mul_dvd_mul_left _ (dvd_mul_left _ _)).trans
          a.1.level_dvd)),
        profile_mul _ _ (hdvd _ ((Nat.mul_dvd_mul_left _ (dvd_mul_right _ _)).trans
          a.1.level_dvd)),
        MulChar.mul_apply, MulChar.mul_apply,
        ← DirichletCharacter.changeLevel_natCast_of_coprime a.1.u_dvd _ hcop,
        ← DirichletCharacter.changeLevel_natCast_of_coprime a.1.v_dvd _ hcop,
        ZMod.natCast_zmod_val]
      ring
    · simp [MulChar.map_nonunit _ hx]
  have hsum := Finset.sum_eq_zero (s := (Finset.univ : Finset (ZMod N)))
    (f := fun x ↦ ρ⁻¹ x * ∑ a ∈ s, g a * (A a.1 * profile a.1.psi a.1.phi a.1.t (c * x.val) -
        B a.1 * profile a.1.phi a.1.psi a.1.t (c * x.val))) (fun x _ ↦ by rw [hc, mul_zero])
  simp_rw [Finset.mul_sum, hscale] at hsum
  rw [Finset.sum_comm] at hsum
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  -- orthogonality of the characters modulo `N`
  have horth (ψ : DirichletCharacter ℂ N) :
      ∑ x, (ρ⁻¹ * ψ) x = if ψ = ρ then (Fintype.card (ZMod N)ˣ : ℂ) else 0 := by
    split_ifs with h
    · rw [h, inv_mul_cancel, MulChar.sum_one_eq_card_units]
    · exact MulChar.sum_eq_zero_of_ne_one fun h' ↦ h (inv_mul_eq_one.mp h').symm
  simp only [horth] at hsum
  -- the second characters are odd while `ρ` is even
  have hphi (a : {a : CharIndex N 1 // a.nebentypus = χ ∧ a.psi (-1) = 1}) :
      a.1.phi.changeLevel a.1.v_dvd ≠ ρ := fun h ↦ by
    have hpar : a.1.psi (-1) * a.1.phi (-1) = -1 := by simpa using a.1.parity
    have h1 := congrArg (· (-1)) h
    simp only [DirichletCharacter.changeLevel_apply_neg_one, hρ] at h1
    rw [a.2.2, h1, one_mul] at hpar
    norm_num at hpar
  simp only [hphi, ite_false, mul_zero, Finset.sum_const_zero, sub_zero] at hsum
  have hcard : (Fintype.card (ZMod N)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_left_inj' hcard).mp ?_
  rw [zero_mul, Finset.sum_filter, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ ?_) hsum
  split_ifs <;> ring

/-- **Independence of the constant terms of the weight-one Eisenstein series.** The
constant-term vectors `γ ↦ constantTermAt γ E₁^{ψ,φ,t}` of the indices of nebentypus `χ` whose
first character is even are linearly independent. Every series of nebentypus `χ` is one of
these, since `E₁^{ψ,φ,t} = E₁^{φ,ψ,t}` and exactly one of `ψ` and `φ` is even. -/
theorem linearIndependent_constantTerms_weightOneForm (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ fun a : {a : CharIndex N 1 // a.nebentypus = χ ∧ a.psi (-1) = 1} ↦
      constantTerms a.1.weightOneForm := by
  classical
  refine LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ lowerUnipotent) ?_
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose A B hA hCT using exists_constantTermAt_lowerUnipotent_weightOneForm (N := N)
  have hc (c : ℕ) : ∑ a ∈ s, g a * (A a.1 * profile a.1.psi a.1.phi a.1.t c -
      B a.1 * profile a.1.phi a.1.psi a.1.t c) = 0 := by
    simpa [hCT] using congrFun hg c
  -- keep the indices whose first character raises to that of `i`
  set ρ := i.1.psi.changeLevel i.1.u_dvd
  have hsep := sum_profile_filter_eq_zero A B hc ρ (by simp [ρ, i.2.2])
  have : NeZero i.1.v := NeZero.of_dvd i.1.v_dvd
  set s' := s.filter (fun a ↦ a.1.psi.changeLevel a.1.u_dvd = ρ)
  have hmem {a} (ha : a ∈ s') : a.1.psi.changeLevel a.1.u_dvd = ρ := (Finset.mem_filter.mp ha).2
  have hphi {a} (ha : a ∈ s') : a.1.phi.changeLevel a.1.v_dvd = i.1.phi.changeLevel i.1.v_dvd :=
    phi_changeLevel_eq_of_nebentypus_eq (a.2.1.trans i.2.1.symm) (hmem ha)
  have his' : i ∈ s' := Finset.mem_filter.mpr ⟨hi, rfl⟩
  -- these indices have the characters of `i` and differ only in their raising parameters
  let T := s'.image fun a ↦ a.1.t
  let l (t : ℕ) : ℂ := ∑ a ∈ s' with a.1.t = t, g a * A a.1
  have hT : 0 ∉ T := by
    simp only [T, Finset.mem_image, not_exists, not_and]
    exact fun a _ h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ a.1.t_dvd))
  have hl := eq_zero_of_forall_sum_profile_eq_zero i.1.psi i.1.phi hT (l := l) (fun c ↦ ?_) i.1.t
    (Finset.mem_image_of_mem _ his')
  · have hli : l i.1.t = g i * A i.1 :=
      Finset.sum_eq_single_of_mem i (Finset.mem_filter.mpr ⟨his', rfl⟩) fun b hb hbi ↦
        (hbi (Subtype.ext (eq_of_changeLevel_eq (Finset.mem_filter.mp hb).2
          (hmem (Finset.mem_filter.mp hb).1) (hphi (Finset.mem_filter.mp hb).1)))).elim
    rw [hli] at hl
    exact (mul_eq_zero.mp hl).resolve_right (hA i.1)
  · rw [← hsep c, ← Finset.sum_fiberwise_of_maps_to
      (fun a ha ↦ Finset.mem_image_of_mem (fun a : {a : CharIndex N 1 // _} ↦ a.1.t) ha)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    obtain ⟨ha', rfl⟩ := Finset.mem_filter.mp ha
    rw [apply_eq_of_changeLevel_eq (fun ψ φ ↦ profile ψ φ a.1.t c) (hmem ha') (hphi ha')]

end CharIndex

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- The weight-one Eisenstein subspace of `M₁(N, χ)` is spanned by the series of the indices
whose first character is even. -/
private theorem weightOneEisensteinSubspace_le_span (χ : (ZMod N)ˣ →* ℂˣ) :
    weightOneEisensteinSubspace χ ≤ Submodule.span ℂ (Set.range
      fun a : {a : CharIndex N 1 // a.nebentypus = χ ∧ a.psi (-1) = 1} ↦
        a.1.weightOneInCharSpace a.2.1) := by
  refine weightOneEisensteinSubspace_le χ fun a hχ ↦ ?_
  rcases a.psi.even_or_odd with h | h
  · exact Submodule.subset_span ⟨⟨a, hχ, h⟩, rfl⟩
  · -- otherwise the exchanged index has the same series and an even first character
    have hpar : a.psi (-1) * a.phi (-1) = -1 := by simpa using a.parity
    have hphi : a.phi (-1) = 1 := by
      rw [DirichletCharacter.Odd] at h
      rw [h] at hpar
      linear_combination -hpar
    have hE : a.weightOneInCharSpace hχ =
        a.swap.weightOneInCharSpace (a.nebentypus_swap.trans hχ) := Subtype.ext (by simp)
    rw [hE]
    exact Submodule.subset_span ⟨⟨a.swap, a.nebentypus_swap.trans hχ, hphi⟩, rfl⟩

/-- **Directness of the weight-one cusp–Eisenstein decomposition**: a form of the weight-one
Eisenstein subspace of `M₁(N, χ)` that is a cusp form is zero. -/
theorem disjoint_weightOneEisensteinSubspace_range_cuspToModFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Disjoint (weightOneEisensteinSubspace χ) (LinearMap.range (cuspToModFormCharSpace 1 χ)) := by
  rw [range_cuspToModFormCharSpace_eq_ker_constantTerms]
  refine (Submodule.range_ker_disjoint ?_).mono_left (weightOneEisensteinSubspace_le_span χ)
  simpa [Function.comp_def] using CharIndex.linearIndependent_constantTerms_weightOneForm χ

/-- The weight-one Eisenstein subspace of `M₁(N, χ)` consists of the forms of nebentypus `χ` in the
span of all the weight-one Eisenstein series in `M₁(Γ₁(N))`. -/
theorem weightOneEisensteinSubspace_eq_comap_span_range_weightOneForm (χ : (ZMod N)ˣ →* ℂˣ) :
    weightOneEisensteinSubspace χ =
      (Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))).comap
        (modFormCharSpace 1 χ).subtype := by
  have h := span_range_inf_modFormCharSpace (CharIndex.weightOneForm (N := N))
    CharIndex.nebentypus CharIndex.weightOneForm_mem_modFormCharSpace χ
  rw [← map_subtype_weightOneEisensteinSubspace] at h
  ext f
  rw [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro hf
    have := h.symm ▸ Submodule.mem_map_of_mem (f := (modFormCharSpace 1 χ).subtype) hf
    exact (Submodule.mem_inf.mp this).1
  · intro hf
    obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp (h ▸ Submodule.mem_inf.mpr ⟨hf, f.2⟩)
    rwa [← Subtype.ext hgf]

end TauCeti

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- The diamond operators preserve the span of the weight-one Eisenstein series in
`M₁(Γ₁(N))`: each series has a nebentypus, so it is an eigenform of every diamond operator. -/
theorem diamondOp_mem_span_range_weightOneForm (d : (ZMod N)ˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1}
    (hf : f ∈ Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))) :
    diamondOp 1 d f ∈ Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N))) := by
  refine Submodule.span_induction (fun g hg ↦ ?_) (by simp)
    (fun x y _ _ hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun c x _ hx ↦ by rw [_root_.map_smul]; exact Submodule.smul_mem _ c hx) hf
  obtain ⟨a, rfl⟩ := hg
  rw [diamondOp_apply_of_mem_modFormCharSpace 1 a.nebentypus d
    a.weightOneForm_mem_modFormCharSpace]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The span of the weight-one Eisenstein series meets the cusp forms of `M₁(Γ₁(N))` only in
`0`: both are stable under the diamond operators, so this reduces to directness for each
nebentypus. -/
private theorem disjoint_span_range_weightOneForm_cuspFormSubmodule :
    Disjoint (Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N))))
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 1) := by
  set V := Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))
  set S := cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 1
  have hS (d : (ZMod N)ˣ) {f} (hf : f ∈ S) : diamondOp 1 d f ∈ S := by
    obtain ⟨g, rfl⟩ := hf
    rw [CuspForm.toModularFormₗ_eq_coe, diamondOp_coe_cuspForm]
    exact CuspForm.isCuspForm_toModularFormₗ _
  rw [disjoint_iff, ← iSup_inf_modFormCharSpace_of_invariant 1 (V ⊓ S) fun d f hf ↦ by
    rw [diamondOpHom_apply]
    exact ⟨diamondOp_mem_span_range_weightOneForm d hf.1, hS d hf.2⟩]
  refine iSup_eq_bot.mpr fun χ ↦ (Submodule.eq_bot_iff _).mpr fun f hf ↦ ?_
  obtain ⟨⟨hfV, hfS⟩, hfχ⟩ := hf
  have hfE : (⟨f, hfχ⟩ : modFormCharSpace 1 χ) ∈ weightOneEisensteinSubspace χ := by
    rw [weightOneEisensteinSubspace_eq_comap_span_range_weightOneForm]
    exact hfV
  exact congrArg Subtype.val (Submodule.disjoint_def.mp
    (disjoint_weightOneEisensteinSubspace_range_cuspToModFormCharSpace χ) _ hfE
    ((mem_range_cuspToModFormCharSpace_iff 1 χ _).mpr hfS))

variable (N) in
/-- A subspace of `M₁(Γ₁(N))` meeting the cusp forms only in `0` has at most half as many
dimensions as there are indices. Away from the levels `1`, `2` and `4` the indices are as many as
the cusps. At the levels `1` and `2` every form vanishes in odd weight, and at the level `4` the
irregular cusp `1/2` carries no constant term. -/
private theorem two_mul_finrank_le_card_of_disjoint
    {V : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 1)}
    (hV : Disjoint V (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 1)) :
    2 * Module.finrank ℂ V ≤ Nat.card (CharIndex N 1) := by
  by_cases hN : 2 < N ∧ N ≠ 4
  · rw [CharIndex.card_eq_card_cuspOrbit_Gamma1 hN.1 hN.2]
    exact TauCeti.ModularForm.two_mul_finrank_le_card_cuspOrbit_of_disjoint (Gamma1 N) hV
  obtain hN2 | rfl : N ∣ 2 ∨ N = 4 := by
    have := NeZero.ne N
    rcases (by omega : N = 1 ∨ N = 2 ∨ N = 4) with rfl | rfl | rfl <;> simp
  · have : Module.finrank ℂ V = 0 := by
      rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
      exact fun f _ ↦ ModularForm.eq_zero_of_odd_of_dvd_two hN2 odd_one f
    omega
  · rw [CharIndex.card_four]
    simpa using TauCeti.ModularForm.two_mul_finrank_le_natCard_of_disjoint (Gamma1 4)
      ![1, ModularGroup.S]
      (fun γ ↦ (cuspOrbitOfSL2Z_Gamma1_four γ).elim (fun h ↦ .inl ⟨0, h⟩) fun h ↦
        h.elim (fun h ↦ .inl ⟨1, h⟩) fun h ↦ .inr fun f ↦
          constantTermAt_eq_zero_of_odd
            (Subgroup.mem_map_of_mem _ (mul_neg_T_mul_inv_mem_Gamma1_four h))
            (by simp [ModularGroup.coe_T]) (by simp [ModularGroup.coe_T]) odd_one f) hV

/-- **The weight-one Eisenstein series span a complement of the cusp forms** in `M₁(Γ₁(N))`. -/
theorem isCompl_span_range_weightOneForm_cuspFormSubmodule :
    IsCompl (Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N))))
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 1) := by
  have h2 := two_mul_finrank_span_range_weightOneForm (N := N)
  set V := Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))
  set S := cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 1
  have hVS : Disjoint V S := disjoint_span_range_weightOneForm_cuspFormSubmodule
  refine ⟨hVS, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq (le_antisymm
    (Submodule.finrank_le _) ?_))⟩
  -- a complement `C` of the cusp forms has `2 dim C ≤ #indices = 2 dim V`
  obtain ⟨C, hC⟩ := S.exists_isCompl
  have h1 := two_mul_finrank_le_card_of_disjoint N hC.symm.disjoint
  have h3 := Submodule.finrank_add_eq_of_isCompl hC
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq V S
  rw [disjoint_iff.mp hVS, finrank_bot] at h4
  omega

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- **The weight-one cusp–Eisenstein decomposition of `M₁(N, χ)`** (Diamond–Shurman,
Theorem 4.8.1): the span of the weight-one Eisenstein series of nebentypus `χ` is a complement of
the image of `S₁(N, χ)` in `M₁(N, χ)`. -/
theorem isCompl_weightOneEisensteinSubspace_range_cuspToModFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) :
    IsCompl (weightOneEisensteinSubspace χ) (LinearMap.range (cuspToModFormCharSpace 1 χ)) := by
  rw [weightOneEisensteinSubspace_eq_comap_span_range_weightOneForm]
  exact isCompl_comap_subtype_range_cuspToModFormCharSpace
    isCompl_span_range_weightOneForm_cuspFormSubmodule
    (fun d _ hf ↦ diamondOp_mem_span_range_weightOneForm d hf) χ

/-- **The weight-one Eisenstein part of the dimension of `M₁(Γ₁(N))`**: at a level
`N ∉ {1, 2, 4}`, twice the dimension of `M₁(Γ₁(N))` exceeds twice that of `S₁(Γ₁(N))` by the
number `ε∞(Γ₁(N))` of cusps of `Γ₁(N)`. -/
theorem two_mul_finrank_weight_one_modularForm_Gamma1_eq_two_mul_finrank_cuspForm_add_card_cuspOrbit
    (hN : 2 < N) (hN4 : N ≠ 4) :
    2 * Module.finrank ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 1) =
      2 * Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) 1) +
        Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit := by
  have h := Submodule.finrank_add_eq_of_isCompl
    (isCompl_span_range_weightOneForm_cuspFormSubmodule (N := N))
  have hV := two_mul_finrank_span_range_weightOneForm_eq_card_cuspOrbit_Gamma1 (N := N) hN hN4
  rw [(CuspForm.equivCuspFormSubmodule _ _).finrank_eq]
  omega

end TauCeti
