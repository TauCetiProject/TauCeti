/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace
public import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# Forms supported on multiples of an index prime to the level

A nonzero cusp form `F ∈ S_k(Γ₁(M), χ)` can have its `q`-expansion supported on the multiples
of `q` when `q` divides the level — the level-raises `V_q` from level `M / q` are exactly such
forms. When `q` is prime to `M` this cannot happen: such an `F` is `0`
(`TauCeti.eq_zero_of_qExpansionSupportedOnDvd_of_coprime`).

The argument first descends `F` at the same level: read at level `q M`, where `q` divides the
level, `F` is `V_q G` on coefficients for some `G ∈ S_k(Γ₁(M), χ)`
(`TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd`, which holds for every
`q ≠ 0`). For a prime `q ∤ M` the Hecke operator `T_q` is `U_q + χ(q) q^{k-1} V_q` on
coefficients, so `V_q F = (χ(q) q^{k-1})⁻¹ (T_q F - G)` is again a form of level `M`, and
iterating gives `V_{q^j} G ∈ S_k(Γ₁(M), χ)` for every `j`. Their `q`-expansions vanish below
`q^j`, so the Sturm bound forces `G = 0`, and then `F = 0`. A composite `q ≠ 1` prime to `M`
reduces to any of its prime factors.

The consequence used in newform theory is that a prime away from the level can be dropped from
a coprimality condition on the coefficients: if `a_n(h) = 0` at every `n` coprime to `L M`, then
`a_n(h) = 0` at every `n` coprime to `M`
(`TauCeti.qExpansion_coeff_eq_zero_of_forall_coprime_mul`). This is what
lets strong multiplicity one ignore finitely many primes outside the level.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd`: a form of level `M`
  supported on the multiples of `q` is `V_q` of a form of the same level and nebentypus, on
  coefficients.
* `TauCeti.eq_zero_of_qExpansionSupportedOnDvd_of_coprime`: for `q ≠ 1` prime to `M`, a form of
  `S_k(Γ₁(M), χ)` supported on the multiples of `q` is `0`.
* `TauCeti.qExpansion_coeff_eq_zero_of_forall_coprime_mul`: vanishing of
  the coefficients at the indices coprime to `L M` implies vanishing at those coprime to `M`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.8 and Theorem 4.6.12, where the auxiliary
  level `L` of strong multiplicity one is reduced to the level of the form.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1 (the action of `T_p` on `q`-expansions) and Section 5.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {M : ℕ} [NeZero M] {k : ℤ}

/-- **A form supported on the multiples of `q` is `V_q` of a form of the same level.** If
`F ∈ S_k(Γ₁(M), χ)` has its `q`-expansion supported on the multiples of `q`, then there is
`G ∈ S_k(Γ₁(M), χ)` with `a_n(F) = a_{n/q}(G)` for `q ∣ n` and `a_n(F) = 0` otherwise. Nothing
relates `q` to `M`: the descent is carried out at level `q M`, where `q` divides the level, and
the level `q M / q` it lands at is `M`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd {q : ℕ} [NeZero q]
    {χ : (ZMod M)ˣ →* ℂˣ} {F : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hFχ : F ∈ cuspFormCharSpace k χ) (hF : QExpansionSupportedOnDvd q F) :
    ∃ G ∈ cuspFormCharSpace k χ,
      ∀ n, (qExpansion 1 F).coeff n = if q ∣ n then (qExpansion 1 G).coeff (n / q) else 0 := by
  have hMq : M ∣ q * M / q := by rw [Nat.mul_div_cancel_left M (NeZero.pos q)]
  have hqM : q * M / q ∣ M := by rw [Nat.mul_div_cancel_left M (NeZero.pos q)]
  -- read `F` at level `q M` and descend there, to the level `q M / q`
  obtain ⟨G, hGχ, hG⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd
      (dvd_mul_right q M) (χ.comp (ZMod.unitsMap hMq))
      (G := CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left M q)) F)
      (by
        have := CuspForm.restrict_mem_cuspFormCharSpace χ (dvd_mul_left M q) hFχ
        rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp])
      (by
        rw [qExpansionSupportedOnDvd_iff, CuspForm.coe_restrict]
        exact qExpansionSupportedOnDvd_iff.mp hF)
  -- and read the descended form back at level `M`
  refine ⟨CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hqM) G, ?_, fun n ↦ ?_⟩
  · have := CuspForm.restrict_mem_cuspFormCharSpace _ hqM hGχ
    rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp, ZMod.unitsMap_self, MonoidHom.comp_id] at this
  · rw [CuspForm.coe_restrict, ← hG n, CuspForm.coe_restrict]

/-- **`T_q` on a `V_q`-image, for `q` prime to the level.** If `A, B ∈ S_k(Γ₁(M), χ)` and `A` is
`V_q B` on coefficients, then `C = (χ(q) q^{k-1})⁻¹ (T_q A - B)` is `V_q A` on coefficients,
since `a_n(T_q A) = a_{qn}(A) + χ(q) q^{k-1} a_{n/q}(A) = a_n(B) + χ(q) q^{k-1} a_{n/q}(A)`.
So `V_q A` is again a form of level `M`. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_coprime {q : ℕ}
    (hq : q.Prime) (hqM : q.Coprime M) {χ : (ZMod M)ˣ →* ℂˣ}
    {A B : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hA : A ∈ cuspFormCharSpace k χ)
    (hB : B ∈ cuspFormCharSpace k χ)
    (hAB : ∀ n, (qExpansion 1 A).coeff n = if q ∣ n then (qExpansion 1 B).coeff (n / q) else 0) :
    ∃ C ∈ cuspFormCharSpace k χ,
      ∀ n, (qExpansion 1 C).coeff n = if q ∣ n then (qExpansion 1 A).coeff (n / q) else 0 := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hΓ := one_mem_strictPeriods_Gamma1_map M
  set c : ℂ := (q : ℂ) ^ (k - 1) * (χ (ZMod.unitOfCoprime q hqM) : ℂ)
  have hq0 : (q : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne_zero)
  have hc : c ≠ 0 := mul_ne_zero hq0 (Units.ne_zero _)
  refine ⟨c⁻¹ • (heckeTCuspNat k q A - B), Submodule.smul_mem _ _
    (Submodule.sub_mem _ (heckeTCuspNat_mem_cuspFormCharSpace k χ hq hA) hB), fun n ↦ ?_⟩
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, PowerSeries.coeff_smul,
    FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓ, map_sub, heckeTCuspNat_def,
    qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hq A n, hAB (q * n),
    diamondOpCuspNat_of_coprime k hqM, diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hA,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, PowerSeries.coeff_smul, smul_eq_mul]
  simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left n hq.pos, add_sub_cancel_left]
  split_ifs
  · simp only [smul_eq_mul, c]
    field_simp
  · simp

/-- **Iterating `T_q` away from the level.** If `A, B ∈ S_k(Γ₁(M), χ)`, `A` is `V_q B` on
coefficients and `B ≠ 0`, then for every `j` some nonzero form of `S_k(Γ₁(M), χ)` has
`q`-expansion vanishing below `q ^ j`: the forms `V_{q^i} B` all have level `M`. -/
private theorem exists_ne_zero_forall_lt_pow_qExpansion_coeff_eq_zero {q : ℕ} (hq : q.Prime)
    (hqM : q.Coprime M) {χ : (ZMod M)ˣ →* ℂˣ} {A B : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hA : A ∈ cuspFormCharSpace k χ) (hB : B ∈ cuspFormCharSpace k χ)
    (hAB : ∀ n, (qExpansion 1 A).coeff n = if q ∣ n then (qExpansion 1 B).coeff (n / q) else 0)
    (hB0 : B ≠ 0) (j : ℕ) :
    ∃ C ∈ cuspFormCharSpace k χ, C ≠ 0 ∧ ∀ n < q ^ j, (qExpansion 1 C).coeff n = 0 := by
  have hΓ := one_mem_strictPeriods_Gamma1_map M
  -- a form which is `V_q` of a nonzero form is nonzero
  have hne : ∀ {A B : CuspForm ((Gamma1 M).map (mapGL ℝ)) k},
      (∀ n, (qExpansion 1 A).coeff n = if q ∣ n then (qExpansion 1 B).coeff (n / q) else 0) →
        B ≠ 0 → A ≠ 0 := fun {A B} hAB hB0 hA0 ↦ hB0 <|
    CuspForm.qExpansion_injective one_pos hΓ <| PowerSeries.ext fun n ↦ by
      have := hAB (q * n)
      simp only [hA0, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left n hq.pos] at this
      simpa [qExpansion_zero] using this.symm
  -- the pair `(V_{q^{j+1}} B, V_{q^j} B)`, with the second vanishing below `q ^ j`
  suffices key : ∃ A ∈ cuspFormCharSpace k χ, ∃ B ∈ cuspFormCharSpace k χ, B ≠ 0 ∧
      (∀ n < q ^ j, (qExpansion 1 B).coeff n = 0) ∧
      ∀ n, (qExpansion 1 A).coeff n = if q ∣ n then (qExpansion 1 B).coeff (n / q) else 0 by
    obtain ⟨-, -, C, hC, hC0, hCv, -⟩ := key
    exact ⟨C, hC, hC0, hCv⟩
  induction j with
  | zero =>
    refine ⟨A, hA, B, hB, hB0, fun n hn ↦ ?_, hAB⟩
    rw [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    exact CuspFormClass.qExpansion_coeff_zero B one_pos hΓ
  | succ j ih =>
    obtain ⟨A, hA, B, hB, hB0, hBv, hAB⟩ := ih
    obtain ⟨C, hC, hCA⟩ :=
      exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_coprime hq hqM hA hB hAB
    refine ⟨C, hC, A, hA, hne hAB hB0, fun n hn ↦ ?_, hCA⟩
    rw [hAB n]
    split_ifs with hqn
    · obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left m hq.pos]
      exact hBv m (by rw [pow_succ, mul_comm] at hn; exact Nat.lt_of_mul_lt_mul_right hn)
    · rfl

/-- **Away from the level, no nonzero form is supported on the multiples of an index.** For
`q ≠ 1` prime to `M`, a form `F ∈ S_k(Γ₁(M), χ)` whose `q`-expansion is supported on the
multiples of `q` is `0`. Compare the level-raises `V_q` from level `M / q`, which are nonzero
forms of this kind when `q ∣ M`. -/
theorem eq_zero_of_qExpansionSupportedOnDvd_of_coprime {q : ℕ} (hq : q ≠ 1)
    (hqM : q.Coprime M) {χ : (ZMod M)ˣ →* ℂˣ} {F : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hFχ : F ∈ cuspFormCharSpace k χ) (hF : QExpansionSupportedOnDvd q F) : F = 0 := by
  -- reduce to a prime factor `p` of `q`, on whose multiples `F` is still supported
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq
  have : NeZero p := ⟨hp.ne_zero⟩
  have hFp : QExpansionSupportedOnDvd p F := by
    rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff] at hF ⊢
    exact fun n hn ↦ hF n fun hqn ↦ hn (hpq.trans hqn)
  -- `F` is `V_p G`, and `G ≠ 0` if `F ≠ 0`
  obtain ⟨G, hGχ, hFG⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd hFχ hFp
  by_contra hF0
  have hG0 : G ≠ 0 := fun hG0 ↦ hF0 <| CuspForm.qExpansion_injective one_pos
    (one_mem_strictPeriods_Gamma1_map M) <| PowerSeries.ext fun n ↦ by
      rw [hFG n, hG0]
      simp [qExpansion_zero]
  -- so a nonzero form of level `M` vanishes past the Sturm bound, which is impossible
  set b := (k * (Gamma1 M).index).toNat / 12
  obtain ⟨B, -, hB0, hBv⟩ := exists_ne_zero_forall_lt_pow_qExpansion_coeff_eq_zero hp
    (hqM.coprime_dvd_left hpq) hFχ hGχ hFG hG0 (b + 1)
  refine hB0 (CuspForm.toModularFormₗ_injective ?_)
  rw [map_zero]
  refine ModularForm.sturm_bound_finiteIndex_SL2Z _ (lt_of_lt_of_le
    (by exact_mod_cast Nat.lt_succ_self b) (PowerSeries.nat_le_order _ _ fun i hi ↦ ?_))
  have hcoe : ⇑(CuspForm.toModularFormₗ B) = ⇑B := funext (CuspForm.toModularFormₗ_apply B)
  rw [strictWidthInfty_Gamma1, hcoe]
  exact hBv i (hi.trans (Nat.lt_pow_self hp.one_lt))

/-- **Dropping a prime away from the level from a coprimality condition.** If
`h ∈ S_k(Γ₁(M), χ)` has `a_n(h) = 0` at every `n` coprime to `q M`, for a prime `q` prime to
`M`, then `a_n(h) = 0` at every `n` coprime to `M`: its coprime-to-`M` filter is supported on
the multiples of `q`, at a level prime to `q`. -/
private theorem qExpansion_coeff_eq_zero_of_forall_coprime_prime_mul {q : ℕ} (hq : q.Prime)
    (hqM : q.Coprime M) {χ : (ZMod M)ˣ →* ℂˣ} {h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hχ : h ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, n.Coprime (q * M) → (qExpansion 1 h).coeff n = 0) (n : ℕ)
    (hn : n.Coprime M) : (qExpansion 1 h).coeff n = 0 := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have : NeZero (M.primeFactors.prod id * M) :=
    ⟨mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).ne_zero)
      (NeZero.ne M)⟩
  obtain ⟨g, hgχ, hgq, hg⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd χ hχ hq subset_rfl hvan
  have hqL : q.Coprime (M.primeFactors.prod id * M) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.prod_right fun p hp ↦ ?_) hqM
    exact hqM.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp)
  have hg0 := eq_zero_of_qExpansionSupportedOnDvd_of_coprime hq.ne_one hqL hgχ hgq
  have h1 := hg n
  rw [hg0, FunLike.coe_zero, qExpansion_zero, map_zero, eq_comm, ite_eq_right_iff] at h1
  exact h1 hn

/-- **Vanishing of the coefficients prime to `L M` implies vanishing of those prime to `M`.**
If `h ∈ S_k(Γ₁(M), χ)` has `a_n(h) = 0` at every `n` coprime to `L M`, for some `L ≠ 0`, then
`a_n(h) = 0` at every `n` coprime to `M`. The primes of `L` dividing `M` change nothing, and each
prime of `L` away from `M` is dropped by
`TauCeti.eq_zero_of_qExpansionSupportedOnDvd_of_coprime`. -/
theorem qExpansion_coeff_eq_zero_of_forall_coprime_mul {L : ℕ}
    (hL : L ≠ 0) {χ : (ZMod M)ˣ →* ℂˣ} {h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hχ : h ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, n.Coprime (L * M) → (qExpansion 1 h).coeff n = 0) (n : ℕ)
    (hn : n.Coprime M) : (qExpansion 1 h).coeff n = 0 := by
  -- peel one prime `q` off `L = q L'` at a time, working at level `L' M`
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  rcases eq_or_ne L 1 with rfl | hL1
  · exact hvan n (by rwa [one_mul])
  obtain ⟨q, hq, L', rfl⟩ := Nat.exists_prime_and_dvd hL1
  have hL' : L' ≠ 0 := right_ne_zero_of_mul hL
  have : NeZero (L' * M) := ⟨mul_ne_zero hL' (NeZero.ne M)⟩
  have hdvd : M ∣ L' * M := dvd_mul_left M L'
  refine ih L' (lt_mul_left (Nat.pos_of_ne_zero hL') hq.one_lt) hL' fun m hm ↦ ?_
  by_cases hqLM : q ∣ L' * M
  · -- `q` already divides `L' M`, so coprimality to `q L' M` is coprimality to `L' M`
    refine hvan m ?_
    rw [mul_assoc]
    exact Nat.Coprime.mul_right (hm.coprime_dvd_right hqLM) hm
  · -- `q` is prime to `L' M`, and is dropped at that level
    have := qExpansion_coeff_eq_zero_of_forall_coprime_prime_mul hq
      ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqLM)
      (CuspForm.restrict_mem_cuspFormCharSpace χ hdvd hχ)
      (fun m hm ↦ by rw [CuspForm.coe_restrict]; exact hvan m (by rwa [mul_assoc])) m hm
    rwa [CuspForm.coe_restrict] at this

end TauCeti
