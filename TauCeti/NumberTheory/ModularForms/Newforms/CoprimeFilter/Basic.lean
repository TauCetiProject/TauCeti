/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.QSupport
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ModularForms.CuspFormSubmodule
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Coprime-index filters on `M_k(Γ₁(N), χ)`: Miyake's Lemma 4.6.5

For a modular form `f ∈ M_k(Γ₁(N), χ)` and a positive integer `L`, keeping only the
coefficients of `f` at the indices coprime to `L` gives a modular form again:

`g = ∑_{(n, L) = 1} aₙ(f) qⁿ ∈ M_k(Γ₁(M), χ)`, where `M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`,

and `g` is a cusp form when `f` is. This is Miyake's Lemma 4.6.5. In Lean the level is
`N * (∏ p ∈ L.primeFactors with p ∣ N, p) * ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2`, and the
nebentypus of `g` is `χ` read modulo that level. The statements here hold for every weight `k`.

A prime of `L` that divides `N` raises the level by a factor `p`, and a prime that does not by a
factor `p²`. A single factor `p` is not enough for the second kind: for `N = 1`, `L = 2` and
`f = Δ` the filter is `Δ(z) + 24 Δ(2z) + 2048 Δ(4z)`, which is not in `S_12(Γ₁(2))`, a space
spanned by `Δ(z)` and `Δ(2z)`.

Miyake's level is the least common multiple of `N ∏_{p ∣ L} p` and `∏_{p ∣ L} p²`, so the levels
`M` with `N * ∏ p ∈ L.primeFactors, p ∣ M` and `(∏ p ∈ L.primeFactors, p) ^ 2 ∣ M` are exactly
its multiples. The filter and the `h`-form below are also stated at every such `M` (the `_of_dvd`
forms), so a caller can land at a level of its choice, such as `N * L ^ 2`, without a further
restriction.

Subtracting the filter from `f` leaves the complementary *`h`-form* `∑_{(n, L) ≠ 1} aₙ(f) qⁿ`,
again a modular form at the same level, and a cusp form when `f` is.

## Main results

* `TauCeti.exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime`: Miyake's Lemma 4.6.5.
  For `f ∈ M_k(Γ₁(N), χ)` and a nonzero `L`, the filter of `f` at `L` lies in `M_k(Γ₁(M), χ)` at
  Miyake's level `M`, and it is a cusp form when `f` is.
  `TauCeti.exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd` is the same
  statement at every multiple of Miyake's level.
* `TauCeti.exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_mul`: when
  `L.primeFactors ⊆ N.primeFactors`, the filter read at level `L * N`. Miyake's level is then
  `∏ L.primeFactors * N`, which divides `L * N`; for `N ≠ 0` the two are equal exactly when `L` is
  squarefree.
* `TauCeti.exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero`, with its forms
  `_zero_of_dvd` at every multiple of Miyake's level and `_zero_mul_sq` at level `N * L ^ 2`: the
  `h`-form.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime` and its `_of_dvd`,
  `_mul`, `_zero`, `_zero_of_dvd` and `_zero_mul_sq` forms: the same statements on
  `S_k(Γ₁(N), χ)`, landing in `S_k(Γ₁(M), χ)`.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd`: for an `f` vanishing at every
  index coprime to `p * L`, with `L.primeFactors ⊆ N.primeFactors`, the filter at level
  `∏ L.primeFactors * N` is also **supported on the multiples of `p`**. This is the hypothesis
  the Atkin–Lehner descent consumes.
  `TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd_mul` is the same result read at
  level `L * N`.

## Implementation notes

The filter is a twist. Write `R = ∏ p ∈ L.primeFactors, p`. The trivial Dirichlet character `1`
modulo `R` is `1` at the `n` coprime to `R` and `0` at the others
(`DirichletCharacter.one_natCast`), and `n` is coprime to `R` exactly when it is coprime to `L`
(`Nat.coprime_prod_primeFactors_right_iff`). The twist of `f` by this character
(`ModularForm.twist`, `CuspForm.twist`) has `q`-expansion `∑ 1(n) aₙ(f) qⁿ`
(`ModularForm.qExpansion_twist_coeff`), which is the filter. The twist is defined at every level
`M` with `N R ∣ M` and `R² ∣ M`, and its nebentypus is `χ · 1² = χ`
(`ModularForm.twist_mem_modFormCharSpace` and `MulChar.equivToUnitHom_one`). Twisting commutes
with the inclusion of cusp forms into modular forms (`ModularForm.twist_coe_cuspForm`), so the
filter of a cusp form is a cusp form. The `h`-form is `f` minus the filter, both read at the same
level.

## Provenance

The statements adapt AINTLIB's `StrongMultiplicityOne/LevelChangeCharSpace.lean` (see References):
the filter `miyake_4_6_5_iterated_L` and the `h`-form `miyake_h_form_general`. The source states
these for cusp forms only. Its filter assumes a squarefree `L` whose primes divide `N`, at level
`L * N`. Its `h`-form assumes a squarefree `L`, at level `N * L ^ 2`. Deliberate differences from
the source:

* The statements cover `M_k(Γ₁(N), χ)` as well as cusp forms, and need no `NeZero N`.
* The filter and the `h`-form are stated for every nonzero `L`, at Miyake's level and at every
  multiple of it. Squarefreeness is assumed nowhere.
* The proof is the twist by the trivial character modulo `∏ L.primeFactors`. The source instead
  peels one prime at a time through `f - V_p (T_p f)` (`miyake_4_6_5_single_prime_dvd_N`, with
  its `q`-expansion and `ite`-composition helpers), and handles the primes of `L` that do not
  divide `N` by a second recursion (`miyake_4_6_5_single_prime_coprime_to_N` /
  `miyake_4_6_5_iterated_helper_general` / `miyake_4_6_5_iterated_L_general`) with `Eq.ndrec`
  casts along equalities of levels.
* The `h`-form at level `N * L ^ 2` is the `_of_dvd` form at that level, where the source casts
  with `Eq.ndrec`. The final `q`-expansion computation uses `ModularForm.qExpansion_sub` directly
  in place of the source's `sub_eq_add_neg` rewriting through `qExpansion_add` and
  `qExpansion_neg`.

`exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd` and its level-`L * N` form `_mul` state
AINTLIB's `miyake_g_p_supported`, which lives in
`StrongMultiplicityOne/DescentCosets.lean` at the same pinned commit and license. The source
states it for a squarefree `l'` and concludes membership in its `qSupportedOnDvdSubmodule`. Here
the primary statement holds for any `L` with `L.primeFactors ⊆ N.primeFactors`, and the conclusion
is the `QExpansionSupportedOnDvd` predicate this repository already uses. The level-`L * N` form
`_mul` is derived from it by `CuspForm.restrict` rather than proved separately; for squarefree `L`
the two levels agree.

## References

* [Miyake, *Modular forms*][miyake1989], Lemma 4.6.5.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, files
  `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/LevelChangeCharSpace.lean`
  and `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} {k : ℤ}

/-- **The filter at a multiple of Miyake's level.** For `f ∈ M_k(Γ₁(N), χ)`, a positive integer
`L`, and a level `M` with `N * ∏ L.primeFactors ∣ M` and `(∏ L.primeFactors) ^ 2 ∣ M`, there is a
modular form `g ∈ M_k(Γ₁(M), χ)`, with the nebentypus `χ` read modulo `M`, that is a cusp form
when `f` is and whose `q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

The two conditions on `M` say that `M` is a multiple of Miyake's level
`N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`. The form `g` is the twist of `f` by the trivial
Dirichlet character modulo `∏ L.primeFactors`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) {L M : ℕ} [NeZero L]
    (hNM : N * ∏ p ∈ L.primeFactors, p ∣ M) (hLM : (∏ p ∈ L.primeFactors, p) ^ 2 ∣ M) :
    ∃ g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_of_mul_right_dvd hNM))) ∧
      (f.IsCuspForm → g.IsCuspForm) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  have : NeZero (∏ p ∈ L.primeFactors, p) :=
    ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) (Nat.prod_primeFactors_dvd L)⟩
  have hRM : (∏ p ∈ L.primeFactors, p) * ∏ p ∈ L.primeFactors, p ∣ M := by rwa [← sq]
  refine ⟨ModularForm.twist (1 : DirichletCharacter ℂ _) hNM hRM f, ?_, ?_, fun n ↦ ?_⟩
  · simpa using ModularForm.twist_mem_modFormCharSpace 1 hNM hRM hf
  · -- the twist of the image of a cusp form `f'` is the image of the twist of `f'`
    rintro ⟨f', rfl⟩
    refine ⟨CuspForm.twist (1 : DirichletCharacter ℂ _) hNM hRM f', ?_⟩
    rw [CuspForm.toModularFormₗ_eq_coe, CuspForm.toModularFormₗ_eq_coe,
      ModularForm.twist_coe_cuspForm]
  · simp only [ModularForm.qExpansion_twist_coeff, DirichletCharacter.one_natCast,
      Nat.coprime_prod_primeFactors_right_iff (NeZero.ne L), ite_mul, one_mul, zero_mul]

/-- **The filter on cusp forms at a multiple of Miyake's level.** For `f ∈ S_k(Γ₁(N), χ)`, a
positive integer `L`, and a level `M` with `N * ∏ L.primeFactors ∣ M` and
`(∏ L.primeFactors) ^ 2 ∣ M`, there is a cusp form `g ∈ S_k(Γ₁(M), χ)`, with the nebentypus `χ`
read modulo `M`, whose `q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

As for modular forms (`exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd`), `g` is
the twist of `f` by the trivial Dirichlet character modulo `∏ L.primeFactors`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L M : ℕ} [NeZero L]
    (hNM : N * ∏ p ∈ L.primeFactors, p ∣ M) (hLM : (∏ p ∈ L.primeFactors, p) ^ 2 ∣ M) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_of_mul_right_dvd hNM))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  have : NeZero (∏ p ∈ L.primeFactors, p) :=
    ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) (Nat.prod_primeFactors_dvd L)⟩
  have hRM : (∏ p ∈ L.primeFactors, p) * ∏ p ∈ L.primeFactors, p ∣ M := by rwa [← sq]
  refine ⟨CuspForm.twist (1 : DirichletCharacter ℂ _) hNM hRM f, ?_, fun n ↦ ?_⟩
  · simpa using CuspForm.twist_mem_cuspFormCharSpace 1 hNM hRM hf
  · simp only [CuspForm.qExpansion_twist_coeff, DirichletCharacter.one_natCast,
      Nat.coprime_prod_primeFactors_right_iff (NeZero.ne L), ite_mul, one_mul, zero_mul]

/-- **The `h`-form at a multiple of Miyake's level.** For `f ∈ M_k(Γ₁(N), χ)`, a positive
integer `L`, and a level `M` with `N * ∏ L.primeFactors ∣ M` and `(∏ L.primeFactors) ^ 2 ∣ M`,
there is a modular form `h ∈ M_k(Γ₁(M), χ)`, with the nebentypus `χ` read modulo `M`, that is a
cusp form when `f` is and whose `q`-expansion is that of `f` restricted to the indices *not*
coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

It is `f` minus the filter of
`exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd`, both read at level `M`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_of_dvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) {L M : ℕ} [NeZero L]
    (hNM : N * ∏ p ∈ L.primeFactors, p ∣ M) (hLM : (∏ p ∈ L.primeFactors, p) ^ 2 ∣ M) :
    ∃ h : ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      h ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_of_mul_right_dvd hNM))) ∧
      (f.IsCuspForm → h.IsCuspForm) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n := by
  have hNM' : N ∣ M := dvd_of_mul_right_dvd hNM
  obtain ⟨g, hg, hgc, hgq⟩ :=
    exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf hNM hLM
  refine ⟨_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hNM') f - g,
    Submodule.sub_mem _ (ModularForm.restrict_mem_modFormCharSpace χ hNM' hf) hg,
    fun hfc ↦ Submodule.sub_mem _ (_root_.ModularForm.restrict_mem_cuspFormSubmodule _ hfc)
      (hgc hfc), fun n ↦ ?_⟩
  rw [FunLike.coe_sub, _root_.ModularForm.qExpansion_sub one_pos
    (one_mem_strictPeriods_Gamma1_map _), map_sub, _root_.ModularForm.coe_restrict, hgq n]
  split_ifs <;> simp

/-- **The `h`-form of a cusp form at a multiple of Miyake's level.** For `f ∈ S_k(Γ₁(N), χ)`, a
positive integer `L`, and a level `M` with `N * ∏ L.primeFactors ∣ M` and
`(∏ L.primeFactors) ^ 2 ∣ M`, there is a cusp form `h ∈ S_k(Γ₁(M), χ)`, with the nebentypus `χ`
read modulo `M`, whose `q`-expansion is that of `f` restricted to the indices *not* coprime to
`L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

It is `f` minus the filter of
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd`, both read at level `M`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_of_dvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L M : ℕ} [NeZero L]
    (hNM : N * ∏ p ∈ L.primeFactors, p ∣ M) (hLM : (∏ p ∈ L.primeFactors, p) ^ 2 ∣ M) :
    ∃ h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_of_mul_right_dvd hNM))) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n := by
  have hNM' : N ∣ M := dvd_of_mul_right_dvd hNM
  obtain ⟨g, hg, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf hNM hLM
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hNM') f - g,
    Submodule.sub_mem _ (CuspForm.restrict_mem_cuspFormCharSpace χ hNM' hf) hg, fun n ↦ ?_⟩
  rw [FunLike.coe_sub, _root_.ModularForm.qExpansion_sub one_pos
    (one_mem_strictPeriods_Gamma1_map _), map_sub, CuspForm.coe_restrict, hgq n]
  split_ifs <;> simp

/-- **Miyake's level admits the filter.** `N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²` is a multiple
of `N ∏_{p ∣ L} p` and of `∏_{p ∣ L} p²`. The first because the primes of `L` not dividing `N`
enter it squared; the second because the primes of `L` dividing `N` already divide `N`. -/
private theorem mul_prod_primeFactors_dvd_and_sq_dvd (N L : ℕ) :
    N * ∏ p ∈ L.primeFactors, p ∣
        N * (∏ p ∈ L.primeFactors with p ∣ N, p) * ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2 ∧
      (∏ p ∈ L.primeFactors, p) ^ 2 ∣
        N * (∏ p ∈ L.primeFactors with p ∣ N, p) * ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2 := by
  have hA : ∏ p ∈ L.primeFactors with p ∣ N, p ∣ N := Finset.prod_primes_dvd N
    (fun p hp ↦ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime)
    fun p hp ↦ (Finset.mem_filter.mp hp).2
  rw [← Finset.prod_filter_mul_prod_filter_not L.primeFactors (· ∣ N), Finset.prod_pow, mul_pow]
  refine ⟨?_, mul_dvd_mul_right ?_ _⟩
  · rw [← mul_assoc]
    exact mul_dvd_mul_left _ (dvd_pow_self _ two_ne_zero)
  · rw [sq]
    exact mul_dvd_mul_right hA _

/-- **Miyake's Lemma 4.6.5.** For `f ∈ M_k(Γ₁(N), χ)` and a positive integer `L`, the series
`∑_{(n, L) = 1} aₙ(f) qⁿ` is a modular form `g ∈ M_k(Γ₁(M), χ)` at level
`M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`,

and `g` is a cusp form when `f` is. The nebentypus of `g` is `χ` read modulo `M`. A prime of `L`
dividing `N` raises the level by a factor `p`, and one not dividing `N` by a factor `p²`. The
same statement at every multiple of `M` is
`exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd`, and on `S_k(Γ₁(N), χ)` it
is `exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) {L : ℕ}
    [NeZero L] :
    ∃ g : ModularForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      (f.IsCuspForm → g.IsCuspForm) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 :=
  exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd N L).1 (mul_prod_primeFactors_dvd_and_sq_dvd N L).2

/-- **Miyake's Lemma 4.6.5 on cusp forms.** For `f ∈ S_k(Γ₁(N), χ)` and a positive integer `L`,
there is a cusp form `g ∈ S_k(Γ₁(M), χ)` at Miyake's level
`M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`, with the nebentypus `χ` read modulo `M`, whose
`q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

The same statement at every multiple of `M` is
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ}
    [NeZero L] :
    ∃ g : CuspForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 :=
  exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd N L).1 (mul_prod_primeFactors_dvd_and_sq_dvd N L).2

/-- **`L * N` admits the filter when `L.primeFactors ⊆ N.primeFactors`.** Then
`∏ L.primeFactors` divides both `L` and `N`, so `L * N` is a multiple of `N * ∏ L.primeFactors`
and of `(∏ L.primeFactors) ^ 2`. -/
private theorem mul_prod_primeFactors_dvd_and_sq_dvd_mul {N L : ℕ}
    (hLN : L.primeFactors ⊆ N.primeFactors) :
    N * ∏ p ∈ L.primeFactors, p ∣ L * N ∧ (∏ p ∈ L.primeFactors, p) ^ 2 ∣ L * N := by
  refine ⟨?_, ?_⟩
  · rw [mul_comm]
    exact mul_dvd_mul_right (Nat.prod_primeFactors_dvd L) N
  · rw [sq]
    exact mul_dvd_mul (Nat.prod_primeFactors_dvd L) (Nat.prod_dvd_of_subset_primeFactors hLN)

/-- **The filter at level `L * N`, for `L.primeFactors ⊆ N.primeFactors`.** For
`f ∈ M_k(Γ₁(N), χ)` and a nonzero `L` with `L.primeFactors ⊆ N.primeFactors` (for `N ≠ 0`: every
prime of `L` divides `N`; for `N = 0` this forces `L = 1`), there is a modular form `g` of level
`L * N`, with the nebentypus `χ` read at that level, that is a cusp form when `f` is and whose
`q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

Under this hypothesis Miyake's level `N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²` is
`∏ L.primeFactors * N`; it divides `L * N`, and for `N ≠ 0` it equals `L * N` exactly when `L` is
squarefree. The hypothesis on the primes of `L` matters for this level: a prime `p ∤ N` costs
Miyake's level a factor `p²`, more than `L * N` supplies when `p ^ 2 ∤ L`. For an arbitrary `L`
see `exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_mul
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) {L : ℕ} [NeZero L]
    (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : ModularForm ((Gamma1 (L * N)).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L))) ∧
      (f.IsCuspForm → g.IsCuspForm) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 :=
  exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul hLN).1
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul hLN).2

/-- **The cusp-form filter at level `L * N`, for `L.primeFactors ⊆ N.primeFactors`.** For
`f ∈ S_k(Γ₁(N), χ)` and a nonzero `L` with `L.primeFactors ⊆ N.primeFactors`, there is a cusp
form `g` of level `L * N`, with the nebentypus `χ` read at that level, whose `q`-expansion is that
of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

As for modular forms (`exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_mul`), Miyake's
level is then `∏ L.primeFactors * N`, which divides `L * N`. For an arbitrary `L` see
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_mul
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} [NeZero L]
    (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (L * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 :=
  exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul hLN).1
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul hLN).2

/-- **The `h`-form at Miyake's level.** For `f ∈ M_k(Γ₁(N), χ)` and a positive integer `L`, there
is a modular form `h` at Miyake's level `M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`, with the
nebentypus `χ` read modulo `M`, that is a cusp form when `f` is and whose `q`-expansion is that
of `f` restricted to the indices *not* coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

It is `f` minus the filter of `exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime`,
both read at level `M`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) {L : ℕ} [NeZero L] :
    ∃ h : ModularForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      h ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      (f.IsCuspForm → h.IsCuspForm) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n :=
  exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd N L).1 (mul_prod_primeFactors_dvd_and_sq_dvd N L).2

/-- **The `h`-form of a cusp form at Miyake's level.** For `f ∈ S_k(Γ₁(N), χ)` and a positive
integer `L`, there is a cusp form `h` at Miyake's level
`M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`, with the nebentypus `χ` read modulo `M`, whose
`q`-expansion is that of `f` restricted to the indices *not* coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

It is `f` minus the filter of `exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`,
both read at level `M`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} [NeZero L] :
    ∃ h : CuspForm ((Gamma1 (N * (∏ p ∈ L.primeFactors with p ∣ N, p) *
        ∏ p ∈ L.primeFactors with ¬p ∣ N, p ^ 2)).map (mapGL ℝ)) k,
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_right N _).mul_right _))) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n :=
  exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd N L).1 (mul_prod_primeFactors_dvd_and_sq_dvd N L).2

/-- **`N * L ^ 2` admits the filter.** It is a multiple of `N * ∏ L.primeFactors` and of
`(∏ L.primeFactors) ^ 2`, since `∏ L.primeFactors` divides `L`. -/
private theorem mul_prod_primeFactors_dvd_and_sq_dvd_mul_sq (N L : ℕ) :
    N * ∏ p ∈ L.primeFactors, p ∣ N * L ^ 2 ∧ (∏ p ∈ L.primeFactors, p) ^ 2 ∣ N * L ^ 2 :=
  ⟨mul_dvd_mul_left N ((Nat.prod_primeFactors_dvd L).trans (dvd_pow_self L two_ne_zero)),
    (pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd L) 2).trans (dvd_mul_left _ N)⟩

/-- **The `h`-form at level `N * L ^ 2`.** For `f ∈ M_k(Γ₁(N), χ)` and any nonzero `L`, there is
a modular form `h` of level `N * L ^ 2`, with the nebentypus `χ` read at that level, that is a
cusp form when `f` is and whose `q`-expansion is that of `f` restricted to the indices *not*
coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

`N * L ^ 2` is the level at which the source this file adapts (AINTLIB's
`miyake_h_form_general`) states the `h`-form. It is a multiple of Miyake's level
`N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`, and for `N ≠ 0` it is equal to it exactly when `L` is
squarefree and coprime to `N`. -/
theorem exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) {L : ℕ} [NeZero L] :
    ∃ h : ModularForm ((Gamma1 (N * L ^ 2)).map (mapGL ℝ)) k,
      h ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_right N (L ^ 2)))) ∧
      (f.IsCuspForm → h.IsCuspForm) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n :=
  exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul_sq N L).1
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul_sq N L).2

/-- **The `h`-form of a cusp form at level `N * L ^ 2`.** For `f ∈ S_k(Γ₁(N), χ)` and any nonzero
`L`, there is a cusp form `h` of level `N * L ^ 2`, with the nebentypus `χ` read at that level,
whose `q`-expansion is that of `f` restricted to the indices *not* coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

As for modular forms (`exists_mem_modFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq`),
`N * L ^ 2` is the source's level, a multiple of Miyake's. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} [NeZero L] :
    ∃ h : CuspForm ((Gamma1 (N * L ^ 2)).map (mapGL ℝ)) k,
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_right N (L ^ 2)))) ∧
      ∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n :=
  exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_of_dvd χ hf
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul_sq N L).1
    (mul_prod_primeFactors_dvd_and_sq_dvd_mul_sq N L).2

/-- **The filter of a form vanishing off `p · L` is supported on the multiples of `p`.** If
`f ∈ S_k(Γ₁(N), χ)` has `aₙ(f) = 0` at every `n` coprime to `p · L`, then its coprime-to-`L`
filter — a cusp form of level `∏ L.primeFactors * N` whose `q`-expansion is `aₙ(f)` at the `n`
coprime to `L` and `0` elsewhere — satisfies `QExpansionSupportedOnDvd p`.

`QExpansionSupportedOnDvd p g` is the hypothesis of
`TauCeti.mem_cuspFormsOld_of_qExpansionSupportedOnDvd`, so this is what carries the coprime filter
into the level-lowering dichotomy. Here `L` may be any natural number with
`L.primeFactors ⊆ N.primeFactors`, including `0`, where the witness is the zero form; `p` need not
divide `N`, and no relation between `p` and `L` is assumed. -/
theorem exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ} (hp : p.Prime)
    (hLN : L.primeFactors ⊆ N.primeFactors)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm ((Gamma1 ((∏ q ∈ L.primeFactors, q) * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N (∏ q ∈ L.primeFactors, q)))) ∧
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
  have hRN : (∏ q ∈ L.primeFactors, q) ^ 2 ∣ (∏ q ∈ L.primeFactors, q) * N := by
    rw [sq]
    exact mul_dvd_mul_left _ (Nat.prod_dvd_of_subset_primeFactors hLN)
  obtain ⟨g, hgχ, hgq⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_dvd χ hf
    (dvd_of_eq (mul_comm _ _)) hRN
  refine ⟨g, hgχ, ?_, hgq⟩
  rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff]
  intro n hn
  -- at an `n` off the multiples of `p`, primality gives `(n, p) = 1`, so the filter's two cases
  -- are `hvan` and the filter's own zero
  rw [hgq n]
  split_ifs with hcop
  · exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hn).symm hcop)
  · rfl

/-- **The `p`-supported filter at level `L * N`.** This is
`TauCeti.exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd` read at level `L * N` instead of
`∏ L.primeFactors * N`: the latter divides the former, and the form is restricted along that
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
  have hdvd : (∏ q ∈ L.primeFactors, q) * N ∣ L * N :=
    mul_dvd_mul_right (Nat.prod_primeFactors_dvd L) N
  obtain ⟨g, hgχ, hgsupp, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd χ hf hp hLN hvan
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hdvd) g,
    CuspForm.restrict_mem_cuspFormCharSpace_comp χ _ hdvd hgχ, ?_, fun n ↦ ?_⟩
  · rwa [qExpansionSupportedOnDvd_iff, CuspForm.coe_restrict, ← qExpansionSupportedOnDvd_iff]
  · rw [CuspForm.coe_restrict]
    exact hgq n

end TauCeti
