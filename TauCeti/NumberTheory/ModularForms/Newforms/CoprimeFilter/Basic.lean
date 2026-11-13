/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Nat.Squarefree
import TauCeti.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported
public import TauCeti.NumberTheory.ModularForms.Newforms.QSupport

/-!
# Coprime-index filters on `M_k(Γ₁(N), χ)`: Miyake's Lemma 4.6.5

For a modular form `f ∈ M_k(Γ₁(N), χ)` and a positive integer `L`, keeping only the
coefficients of `f` at the indices coprime to `L` gives a modular form again:

`g = ∑_{(n, L) = 1} aₙ(f) qⁿ ∈ M_k(Γ₁(M), χ)`, where `M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`,

and `g` is a cusp form when `f` is. This is Miyake's Lemma 4.6.5. A prime of `L` that divides
`N` raises the level by a factor `p`, and a prime that does not by a factor `p²`. In Lean the
level is `N * (∏ p ∈ L.primeFactors with p ∣ N, p) * ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2`,
and the nebentypus of `g` is `χ` read modulo that level.

That level is the one Miyake's proof produces: at a prime `p` of `L` it reads `f` at level
`N' = N` if `p ∣ N` and `N' = p N` otherwise, and filters at `p N'`. A transcription of the
statement on p. 157 shows the two product conditions the other way round,
`N ∏_{p ∣ L, p ∤ N} p ∏_{p ∣ L, p ∣ N} p²`. That reading is false in general: for `N = 1`,
`L = 2` and `f = Δ` it gives level `2`, but the filter is `Δ(z) + 24 Δ(2z) + 2048 Δ(4z)`, which
is not in `S_12(Γ₁(2))`, a space spanned by `Δ(z)` and `Δ(2z)`. Miyake also assumes `k > 0` in
§4.6; the statements here hold for every weight.

Subtracting the filter from `f` leaves the complementary *`h`-form* `∑_{(n, L) ≠ 1} aₙ(f) qⁿ`,
which for a cusp form `f` is a cusp form at the same level.

## Main results

* `TauCeti.exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime`: Miyake's Lemma 4.6.5.
  For `f ∈ M_k(Γ₁(N), χ)` and a nonzero `L`, the filter of `f` at `L` lies in `M_k(Γ₁(M), χ)` at
  Miyake's level `M`, and it is a cusp form when `f` is.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`: the same filter on
  `S_k(Γ₁(N), χ)`, landing in `S_k(Γ₁(M), χ)`.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_mul`: when every prime of
  `L` divides `N`, the cusp-form filter read at level `L * N`. Miyake's level is then
  `∏ L.primeFactors * N`, which divides `L * N` and equals it exactly when `L` is squarefree.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero`: the `h`-form of a
  cusp form, for any nonzero `L`, at Miyake's level.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq`: the same
  `h`-form read at level `N * L ^ 2`, a multiple of Miyake's level.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd`: for an `f` vanishing at every
  index coprime to `p * L`, with every prime of `L` dividing `N`, the filter at level
  `∏ L.primeFactors * N` is also **supported on the multiples of `p`**. This is the hypothesis
  the Atkin–Lehner descent consumes.
  `TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd_mul` is the same result read at
  level `L * N`.

## Implementation notes

The construction runs on modular forms and handles one prime at a time. At a prime `q` dividing
the current level `M`, the witness is `F - V_q (T_q F)`, read at level `q * M`. Because `q ∣ M`,
`T_q` acts on coefficients by `aₘ(T_q F) = a_{qm}(F)`
(`HeckeRing.GL2.qExpansion_coeff_heckeTNat_of_primeFactors_subset`). `V_q` puts those coefficients
back at the multiples of `q` (`TauCeti.ModularForm.qExpansion_levelRaise_coeff_Gamma1`), so the
difference keeps exactly the coefficients of `F` at the indices prime to `q`. This single step
needs only that the prime factors of `q` divide the level, not that `q` is prime. Primality is
used to compose the steps, where `Nat.Coprime n (q * m)` splits as `¬ q ∣ n` and
`Nat.Coprime n m`.

A prime of `L` that does not divide `N` does not divide the starting level, so `f` is first read
at level `B * N`, where `B = ∏_{p ∣ L, p ∤ N} p`. Each prime of `L` then costs one more factor
`p`, and the filter lands at `∏ L.primeFactors * (B * N)`, which is Miyake's level.

The induction runs over the finite set of primes still to be peeled, with the base level
generalised. The target level is any multiple of the level the filter needs. It is reached by a
single `ModularForm.restrict` when no prime is left, so no form is transported along an equality
of levels.

Restriction, `T_q` and `V_q` all send cusp forms to cusp forms, so every step carries
`F.IsCuspForm → G.IsCuspForm` along. The cusp-form statements are read off from the modular-form
construction through `CuspForm.toModularFormₗ` and `TauCeti.coe_mem_modFormCharSpace_iff`, so
the file has a single construction.

## Provenance

Adapted from AINTLIB's `StrongMultiplicityOne/LevelChangeCharSpace.lean` (see References): the
declarations `miyake_4_6_5_single_prime_dvd_N` and `miyake_4_6_5_iterated_L`, with their
`q`-expansion and `ite`-composition helpers, and `miyake_h_form_general`. The source states
these for cusp forms only. Its filter `miyake_4_6_5_iterated_L` assumes a squarefree `L` whose
primes divide `N`, at level `L * N`. Its `h`-form `miyake_h_form_general` assumes a squarefree `L`,
at level `N * L ^ 2`. Deliberate differences from the source:

* The construction runs on modular forms and carries cuspidality along, so the file states the
  lemma for `M_k(Γ₁(N), χ)` as well as for cusp forms.
* The filter is stated for every nonzero `L`, at Miyake's level. Squarefreeness is assumed
  nowhere.
* The source's `hp : p.Prime` is dropped from the single-prime step and from its `q`-expansion
  computation, since neither proof uses it. The `Squarefree (∏ S)` hypothesis that the source
  threads through the recursion only to feed itself disappears once the conclusion is stated at
  a multiple of `∏ S * M`.
* The source handles the primes of `L` that do not divide `N` by a second recursion, at a level
  fixed in advance. That is the `miyake_4_6_5_single_prime_coprime_to_N` /
  `miyake_4_6_5_iterated_helper_general` / `miyake_4_6_5_iterated_L_general` chain, with its
  `dvd_conditions_*` side conditions and its `Eq.ndrec` cast along `p * (p * N) = N * p ^ 2`.
  Here one restriction to level `B * N` makes those primes divide the level, so the single
  recursion handles every prime of `L`.
* The `h`-form is one subtraction at Miyake's level. Its level-`N * L ^ 2` form is that `h`-form
  moved by one `CuspForm.restrict`, where the source casts with `Eq.ndrec`. The final
  `q`-expansion computation uses `ModularForm.qExpansion_sub` directly in place of the source's
  `sub_eq_add_neg` rewriting through `qExpansion_add` and `qExpansion_neg`.

`exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd` and its level-`L * N` form `_mul` state
AINTLIB's `miyake_g_p_supported`, which lives in
`StrongMultiplicityOne/DescentCosets.lean` at the same pinned commit and license. The source
states it for a squarefree `l'` and concludes membership in its `qSupportedOnDvdSubmodule`. Here
the primary statement holds for any `L` whose primes divide `N`, and the conclusion is the
`QExpansionSupportedOnDvd` predicate this repository already uses. The level-`L * N` form `_mul`
is derived from it by `CuspForm.restrict` rather than proved separately; for squarefree `L` the
two levels agree.

`coprime_prod_primeFactors_iff` is AINTLIB's `coprime_prod_primeFactors_iff_coprime`, which
lives one file up in `StrongMultiplicityOne.lean`. It is restated here for an arbitrary nonzero
`L` rather than for the ambient level, and proved from `Nat.dvd_prod_primeFactors_pow_self`
instead of by contradiction on a common prime divisor.

## References

* [Miyake, *Modular forms*][miyake1989], Lemma 4.6.5.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, files
  `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/LevelChangeCharSpace.lean`
  and `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne.lean`.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

open HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The `q`-expansion of `f - V_p (T_p f)`.** Read at level `p * N`, the level-raise of
`T_p f` reproduces exactly the coefficients of `f` at the indices divisible by `p`, so the
difference is `f` with those indices deleted. Primality of `p` is not needed: what makes
`T_p` act by `aₘ(T_p f) = a_{p m}(f)` is that `p`'s prime factors already divide `N`. -/
private theorem qExpansion_coeff_restrict_sub_levelRaise_heckeTNat {p : ℕ} [NeZero p]
    (hpN : p.primeFactors ⊆ N.primeFactors) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (n : ℕ) :
    (qExpansion 1 (_root_.ModularForm.restrict
          (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
          ModularForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p)
            (heckeTNat (N := N) k p f))).coeff n =
      if p ∣ n then 0 else (qExpansion 1 f).coeff n := by
  rw [_root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
    ModularForm.qExpansion_levelRaise_coeff_Gamma1 N _ n,
    qExpansion_coeff_heckeTNat_of_primeFactors_subset k p hpN f (n / p),
    _root_.ModularForm.coe_restrict]
  by_cases hpn : p ∣ n <;> simp [hpn, Nat.mul_div_cancel']

/-- **Composing a coprimality filter with a prime one.** Deleting the indices divisible by a
prime `q` from the indices coprime to `m` leaves exactly the indices coprime to `q * m`. -/
private theorem ite_coprime_ite_dvd_eq_ite_coprime_mul {α : Type*} [Zero α] {q : ℕ}
    (hq : q.Prime) (n m : ℕ) (a : α) :
    (if Nat.Coprime n m then (if q ∣ n then 0 else a) else 0) =
      if Nat.Coprime n (q * m) then a else 0 := by
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_comm, hq.coprime_iff_not_dvd, ite_and]
  split_ifs <;> rfl

/-- **Coprimality only sees the primes.** For nonzero `L`, an `n` is coprime to `L` exactly
when it is coprime to the product of `L`'s prime factors. -/
private theorem coprime_prod_primeFactors_iff {n L : ℕ} (hL : L ≠ 0) :
    Nat.Coprime n (L.primeFactors.prod id) ↔ Nat.Coprime n L :=
  ⟨fun h ↦ (h.pow_right L).coprime_dvd_right (Nat.dvd_prod_primeFactors_pow_self hL),
    fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd L)⟩

/-- **The filter at a single level-supported `p`.** From `f ∈ M_k(Γ₁(N), χ)` and a nonzero `p`
whose prime factors all divide `N`, the form `f - V_p (T_p f)` lies in `M_k(Γ₁(p * N), χ)` and
carries the coefficients of `f` at the indices *not* divisible by `p`, the rest deleted. It is a
cusp form when `f` is, since restriction, `T_p` and `V_p` all preserve cusp forms. `p` need be
neither prime nor a prime power; only its prime support is constrained. -/
private theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_dvd_zero
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) {p : ℕ} [NeZero p] (hpN : p.primeFactors ⊆ N.primeFactors) :
    ∃ g : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) ∧
      (f.IsCuspForm → g.IsCuspForm) ∧
      ∀ n, (qExpansion 1 g).coeff n = if p ∣ n then 0 else (qExpansion 1 f).coeff n := by
  refine ⟨_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
      ModularForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p) (heckeTNat (N := N) k p f),
    Submodule.sub_mem _ (ModularForm.restrict_mem_modFormCharSpace χ _ hf)
      (ModularForm.levelRaise_mem_modFormCharSpace N p χ
        (heckeTNat_mem_modFormCharSpace_of_primeFactors_subset k χ p hpN hf)),
    fun hfc ↦ Submodule.sub_mem _ (_root_.ModularForm.restrict_mem_cuspFormSubmodule _ hfc) ?_,
    qExpansion_coeff_restrict_sub_levelRaise_heckeTNat hpN f⟩
  -- `V_p (T_p f)` is the image of the cusp form `V_p (T_p f')` when `f` is that of `f'`
  obtain ⟨f', rfl⟩ := hfc
  refine ⟨CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p) (heckeTCuspNat (N := N) k p f'),
    ?_⟩
  ext τ
  simp [CuspForm.toModularFormₗ_eq_coe]

/-- **The filter at the primes of `S`.** For a finite set `S` of primes dividing `M` and
`f ∈ M_k(Γ₁(M), χ)`, there is, at every multiple `M'` of `∏ S * M`, a form in
`M_k(Γ₁(M'), χ)` that is a cusp form when `f` is and whose `q`-expansion is that of `f`
restricted to the indices coprime to `∏ S`.

The proof peels one prime of `S` at a time, each step multiplying the base level by that prime.
The target level `M'` stays fixed and is reached by one restriction once `S` is empty, so no
form is transported along an equality of levels. -/
private theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod {M M' : ℕ}
    {S : Finset ℕ} (hS : S ⊆ M.primeFactors) (hM' : S.prod id * M ∣ M') (χ : (ZMod M)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    ∃ g : ModularForm ((Gamma1 M').map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_left M _).trans hM'))) ∧
      (f.IsCuspForm → g.IsCuspForm) ∧
      ∀ n, (qExpansion 1 g).coeff n =
        if Nat.Coprime n (S.prod id) then (qExpansion 1 f).coeff n else 0 := by
  induction S using Finset.induction_on generalizing M with
  | empty =>
    have hMM' : M ∣ M' := by simpa using hM'
    refine ⟨_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hMM') f,
      ModularForm.restrict_mem_modFormCharSpace χ hMM' hf,
      _root_.ModularForm.restrict_mem_cuspFormSubmodule _, fun n ↦ ?_⟩
    simp [_root_.ModularForm.coe_restrict]
  | insert q S hqS ih =>
    have hqM : q ∈ M.primeFactors := hS (Finset.mem_insert_self q S)
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqM
    have : NeZero M := ⟨(Nat.mem_primeFactors.mp hqM).2.2⟩
    have : NeZero q := ⟨hq.ne_zero⟩
    -- filter `q` out at level `q * M`, then the rest of `S` from there
    obtain ⟨g₁, hg₁, hg₁c, hg₁q⟩ :=
      exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_dvd_zero χ hf (p := q)
        (by simpa [hq.primeFactors] using hqM)
    have hS' : S ⊆ (q * M).primeFactors := fun r hr ↦
      Nat.primeFactors_mono (Nat.dvd_mul_left M q) (NeZero.ne _) (hS (Finset.mem_insert_of_mem hr))
    have hM'' : S.prod id * (q * M) ∣ M' := by
      rwa [Finset.prod_insert hqS, id, mul_comm q, mul_assoc] at hM'
    obtain ⟨g, hg, hgc, hgq⟩ := ih hS' hM'' _ hg₁
    refine ⟨g, ?_, hgc ∘ hg₁c, fun n ↦ ?_⟩
    · simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg
    · rw [hgq n, hg₁q n, Finset.prod_insert hqS, id]
      exact ite_coprime_ite_dvd_eq_ite_coprime_mul hq n _ _

/-- **Miyake's level, as the filter reaches it.** Reading a form at level `B * N`, where `B` is
the product of the primes of `L` not dividing `N`, and then multiplying the level by each prime
of `L` once lands at `N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`. -/
private theorem prod_primeFactors_mul_prod_filter_not_dvd_mul (N L : ℕ) :
    L.primeFactors.prod id * ((∏ p ∈ L.primeFactors with ¬p ∣ N, p) * N) =
      N * (∏ p ∈ L.primeFactors with p ∣ N, p) * ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2 := by
  change (∏ p ∈ L.primeFactors, p) * _ = _
  rw [← Finset.prod_filter_mul_prod_filter_not L.primeFactors (· ∣ N), Finset.prod_pow]
  ring

/-- **Miyake's Lemma 4.6.5.** For `f ∈ M_k(Γ₁(N), χ)` and a positive integer `L`, the series
`∑_{(n, L) = 1} aₙ(f) qⁿ` is a modular form `g ∈ M_k(Γ₁(M), χ)` at level
`M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`,

and `g` is a cusp form when `f` is. The nebentypus of `g` is `χ` read modulo `M`. A prime of `L`
dividing `N` raises the level by a factor `p`, and one not dividing `N` by a factor `p²`. This is
the level Miyake's proof gives; the module documentation explains why the reading with the two
product conditions swapped, found in a transcription of the statement, cannot be right. The
same statement on `S_k(Γ₁(N), χ)` is
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) {L : ℕ}
    [NeZero L] :
    ∃ g : ModularForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      (f.IsCuspForm → g.IsCuspForm) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  -- read `f` at level `B * N`, where every prime of `L` divides the level, and filter there
  set B := ∏ p ∈ L.primeFactors with ¬p ∣ N, p
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero
  have hNB : N ∣ B * N := Nat.dvd_mul_left N B
  have hLB : L.primeFactors ⊆ (B * N).primeFactors := fun p hp ↦ by
    refine Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, ?_, Nat.mul_ne_zero hB (NeZero.ne N)⟩
    by_cases hpN : p ∣ N
    · exact dvd_mul_of_dvd_right hpN B
    · exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp, hpN⟩)) N
  obtain ⟨g, hg, hgc, hgq⟩ := exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod hLB
    (dvd_of_eq (prod_primeFactors_mul_prod_filter_not_dvd_mul N L)) (χ.comp (ZMod.unitsMap hNB))
    (ModularForm.restrict_mem_modFormCharSpace χ hNB hf)
  refine ⟨g, ?_, fun hfc ↦ hgc (_root_.ModularForm.restrict_mem_cuspFormSubmodule _ hfc),
    fun n ↦ ?_⟩
  · simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg
  · rw [hgq n, _root_.ModularForm.coe_restrict]
    simp only [coprime_prod_primeFactors_iff (NeZero.ne L)]

/-- **Miyake's Lemma 4.6.5 on cusp forms.** For `f ∈ S_k(Γ₁(N), χ)` and a positive integer `L`,
there is a cusp form `g ∈ S_k(Γ₁(M), χ)` at Miyake's level
`M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`, with the nebentypus `χ` read modulo `M`, whose
`q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

It is read off from `exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime` through the
inclusion `S_k → M_k`: the filter of a cusp form is a cusp form. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ}
    [NeZero L] :
    ∃ g : CuspForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  obtain ⟨g, hg, hgc, hgq⟩ := exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime χ
    ((coe_mem_modFormCharSpace_iff k χ f).mpr hf) (L := L)
  obtain ⟨g', rfl⟩ := hgc (ModularForm.CuspForm.isCuspForm_toModularFormₗ f)
  exact ⟨g', (coe_mem_modFormCharSpace_iff k _ g').mp hg, hgq⟩

omit [NeZero N] in
/-- **The cusp-form filter when every prime of `L` divides `N`.** No prime of `L` then has to be
brought into the level first, so the filter is available at every multiple of
`∏ L.primeFactors * N`, which is Miyake's level in this case. Unlike the general statement this
needs no `NeZero N`. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_subset
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} (hL : L ≠ 0) (hLN : L.primeFactors ⊆ N.primeFactors)
    {M : ℕ} (hM : L.primeFactors.prod id * N ∣ M) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_left N _).trans hM))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  obtain ⟨g, hg, hgc, hgq⟩ := exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod hLN
    hM χ ((coe_mem_modFormCharSpace_iff k χ f).mpr hf)
  obtain ⟨g', rfl⟩ := hgc (ModularForm.CuspForm.isCuspForm_toModularFormₗ f)
  refine ⟨g', (coe_mem_modFormCharSpace_iff k _ g').mp hg, fun n ↦ ?_⟩
  have h := hgq n
  simp only [coprime_prod_primeFactors_iff hL] at h
  exact h

omit [NeZero N] in
/-- **The coprime-index filter at level `L * N`, for `L` whose primes all divide `N`.** For
`f ∈ S_k(Γ₁(N), χ)` and a nonzero `L` whose primes all divide `N`, there is a cusp form `g` of
level `L * N`, with the nebentypus `χ` read at that level, whose `q`-expansion is that of `f`
restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

When every prime of `L` divides `N`, Miyake's level `N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`
is `∏ L.primeFactors * N`; it divides `L * N` and equals it exactly when `L` is squarefree. The
hypothesis on the primes of `L` matters for this level: a prime `p ∤ N` costs Miyake's level a
factor `p²`, more than `L * N` supplies when `p ^ 2 ∤ L`. For an arbitrary `L` see
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_mul
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} [NeZero L]
    (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (L * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 :=
  exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_subset χ hf (NeZero.ne L) hLN
    (mul_dvd_mul_right (by simpa using Nat.prod_primeFactors_dvd L) N)

/-- **The complementary filter (the `h`-form).** For `f ∈ S_k(Γ₁(N), χ)` and a positive integer
`L`, there is a cusp form `h` at Miyake's level `M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`,
with the nebentypus `χ` read modulo `M`, whose `q`-expansion is that of `f` restricted to the
indices *not* coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

It is `f` minus the filter of `exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`,
both read at level `M`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} [NeZero L] :
    ∃ h : CuspForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n := by
  have hNM : N ∣ N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
      ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2 := (Nat.dvd_mul_right N _).mul_right _
  obtain ⟨g, hg, hgq⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime χ hf (L := L)
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hNM) f - g,
    Submodule.sub_mem _ (CuspForm.restrict_mem_cuspFormCharSpace χ hNM hf) hg, fun n ↦ ?_⟩
  rw [FunLike.coe_sub, _root_.ModularForm.qExpansion_sub one_pos
    (one_mem_strictPeriods_Gamma1_map _), map_sub, CuspForm.coe_restrict, hgq n]
  split_ifs <;> simp

/-- **The `h`-form at level `N * L ^ 2`.** For `f ∈ S_k(Γ₁(N), χ)` and any nonzero `L`, there is
a cusp form `h` of level `N * L ^ 2`, with the nebentypus `χ` read at that level, whose
`q`-expansion is that of `f` restricted to the indices *not* coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

`N * L ^ 2` is the level at which the source this file adapts (AINTLIB's
`miyake_h_form_general`) states the `h`-form. It is a multiple of Miyake's level
`N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`, equal to it exactly when `L` is squarefree and coprime
to `N`, and `h` is the `h`-form of
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero` restricted along that
divisibility. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} [NeZero L] :
    ∃ h : CuspForm ((Gamma1 (N * L ^ 2)).map (mapGL ℝ)) k,
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_right N (L ^ 2)))) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n := by
  have hpd : L.primeFactors.prod id ∣ L := by simpa using Nat.prod_primeFactors_dvd L
  have hBd : ∏ p ∈ L.primeFactors with ¬p ∣ N, p ∣ L :=
    (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans hpd
  have hdvd : N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
      ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2 ∣ N * L ^ 2 := by
    rw [← prod_primeFactors_mul_prod_filter_not_dvd_mul]
    exact (mul_dvd_mul hpd (mul_dvd_mul_right hBd N)).trans (dvd_of_eq (by ring))
  obtain ⟨h, hh, hhq⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero χ hf
    (L := L)
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hdvd) h,
    CuspForm.restrict_mem_cuspFormCharSpace_comp χ _ hdvd hh, fun n ↦ ?_⟩
  rw [CuspForm.coe_restrict]
  exact hhq n

omit [NeZero N] in
/-- **The filter of a form vanishing off `p · L` is supported on the multiples of `p`.** If
`f ∈ S_k(Γ₁(N), χ)` has `aₙ(f) = 0` at every `n` coprime to `p · L`, then its coprime-to-`L`
filter — a cusp form of level `∏ L.primeFactors * N` whose `q`-expansion is `aₙ(f)` at the `n`
coprime to `L` and `0` elsewhere — satisfies `QExpansionSupportedOnDvd p`.

`QExpansionSupportedOnDvd p g` is the hypothesis of
`TauCeti.mem_cuspFormsOld_of_qExpansionSupportedOnDvd`, so this is what carries the coprime filter
into the level-lowering dichotomy. Here `L` may be any natural number whose primes divide `N`,
including `0`, where the witness is the zero form; `p` need not divide `N`, and no relation
between `p` and `L` is assumed. -/
theorem exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ} (hp : p.Prime)
    (hLN : L.primeFactors ⊆ N.primeFactors)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm ((Gamma1 (L.primeFactors.prod id * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N (L.primeFactors.prod id)))) ∧
        QExpansionSupportedOnDvd p g ∧
        ∀ n, (qExpansion 1 g).coeff n =
          if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · -- at `L = 0` only `n = 1` is coprime to `L`, and `hvan` kills that coefficient
    have h0 {M : ℕ} (n : ℕ) :
        (qExpansion 1 ⇑(0 : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)).coeff n = 0 := by
      simp [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero]
    refine ⟨0, Submodule.zero_mem _, ?_, fun n ↦ ?_⟩
    · rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff]
      exact fun n _ ↦ h0 n
    · rcases eq_or_ne n 1 with rfl | hn
      · rw [h0]
        simp [hvan 1 (by simp)]
      · rw [h0]
        simp [Nat.coprime_zero_right, hn]
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨g, hgχ, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_subset χ hf (NeZero.ne L) hLN
      dvd_rfl
  refine ⟨g, hgχ, ?_, hgq⟩
  rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff]
  intro n hn
  -- at an `n` off the multiples of `p`, primality gives `(n, p) = 1`, so the filter's two cases
  -- are `hvan` and the filter's own zero
  rw [hgq n]
  split_ifs with hcop
  · exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hn).symm hcop)
  · rfl

omit [NeZero N] in
/-- **The `p`-supported filter at level `L * N`.** This is
`TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd` read at level `L * N` instead of
`∏ L.primeFactors * N`: the former divides the latter, and the form is restricted along that
divisibility. For a squarefree `L` the two levels agree. -/
theorem exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd_mul
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ} (hp : p.Prime)
    (hLN : L.primeFactors ⊆ N.primeFactors)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm ((Gamma1 (L * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L))) ∧
        QExpansionSupportedOnDvd p g ∧
        ∀ n, (qExpansion 1 g).coeff n =
          if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  have hpd : L.primeFactors.prod id ∣ L := by simpa using Nat.prod_primeFactors_dvd L
  have hdvd : L.primeFactors.prod id * N ∣ L * N := mul_dvd_mul_right hpd N
  obtain ⟨g, hgχ, hgsupp, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd χ hf hp hLN hvan
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hdvd) g,
    CuspForm.restrict_mem_cuspFormCharSpace_comp χ _ hdvd hgχ, ?_, fun n ↦ ?_⟩
  · rwa [qExpansionSupportedOnDvd_iff, CuspForm.coe_restrict, ← qExpansionSupportedOnDvd_iff]
  · rw [CuspForm.coe_restrict]
    exact hgq n

end TauCeti
