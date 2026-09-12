/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace

/-!
# The squarefree decomposition of a form with vanishing coprime coefficients

Miyake's Lemma 4.6.7: a cusp form `f ∈ S_k(Γ₁(N), χ)` whose `q`-expansion vanishes at every index
coprime to a squarefree `l` is, coefficient by coefficient, a sum `∑_{q ∈ l.primeFactors} V_q F_q`
over the **primes** `q` dividing `l`, of
level-raises of forms `F_q` of level `N l² / q` with nebentypus lowered along `N l² / q ∣ N l²`:
`a_n(f) = ∑_{q ∈ l.primeFactors, q ∣ n} a_{n/q}(F_q)`. The prime peeled at each step is the one of
`Newforms/Descent/CharacterSpace.lean`
(`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd`).

## Main results

* `TauCeti.exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree`: Lemma 4.6.7.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/SquarefreeDecomp.lean`,
theorem `squarefree_decomp_with_lower_level` and its `Miyake467Decomp_*` helpers. The source
states the decomposition through a bundled `Prop`-valued definition and transports forms across
equalities of levels; here the conclusion is stated directly and levels are related by
divisibility (`CuspForm.ofLe`).

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {k : ℤ}

variable {N : ℕ} [NeZero N]

/-- The conclusion of Lemma 4.6.7 at level `N * l ^ 2`, as a predicate on `f`: families `F` and
`χ'` indexed by the primes of `l`, with `F q` of level `N * l ^ 2 / q` in the space of `χ' q`
lying over `χ`, and `a_n(f) = ∑_{q ∈ l.primeFactors, q ∣ n} a_{n/q}(F q)`, the sum over the primes
`q` dividing `l`. Only used to state the induction. -/
private def SquarefreeDecomposition (χ : (ZMod N)ˣ →* ℂˣ) (l : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ (F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (N * l ^ 2 / q)).map (mapGL ℝ)) k)
    (χ' : ∀ q ∈ l.primeFactors, (ZMod (N * l ^ 2 / q))ˣ →* ℂˣ),
    (∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq)) ∧
    (∀ q (hq : q ∈ l.primeFactors),
      (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero))
          N))) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2)))) ∧
    ∀ n, (qExpansion 1 f).coeff n = ∑ q ∈ l.primeFactors.attach,
      if q.1 ∣ n then (qExpansion 1 (F q.1 q.2)).coeff (n / q.1) else 0

omit [NeZero N] in
/-- Assembling the decomposition at `l = q * l'` from the data at the prime `q` and the families
over the primes of `l'`, all already read at the levels `N * l ^ 2` and `N * l ^ 2 / q'`. -/
private theorem squarefreeDecomposition_of_insert {χ : (ZMod N)ˣ →* ℂˣ} {l q l' : ℕ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hq : q.Prime) (hl : l = q * l')
    (hql' : q ∉ l'.primeFactors) (hl' : l' ≠ 0)
    (F' : ∀ q' ∈ l'.primeFactors, CuspForm ((Gamma1 (N * l ^ 2 / q')).map (mapGL ℝ)) k)
    (χ'' : ∀ q' ∈ l'.primeFactors, (ZMod (N * l ^ 2 / q'))ˣ →* ℂˣ)
    (hF' : ∀ q' (hq' : q' ∈ l'.primeFactors), F' q' hq' ∈ cuspFormCharSpace k (χ'' q' hq'))
    (hχ'' : ∀ q' (hq' : q' ∈ l'.primeFactors),
      (χ'' q' hq').comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right
        ((Nat.dvd_of_mem_primeFactors hq').trans (dvd_pow_self l' two_ne_zero) |>.trans
          (pow_dvd_pow_of_dvd (hl ▸ dvd_mul_left l' q) 2)) N))) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2))))
    (F : CuspForm ((Gamma1 (N * l ^ 2 / q)).map (mapGL ℝ)) k) (χ₁ : (ZMod (N * l ^ 2 / q))ˣ →* ℂˣ)
    (hF : F ∈ cuspFormCharSpace k χ₁)
    (hχ₁ : χ₁.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
      (dvd_mul_of_dvd_right ((hl ▸ dvd_mul_right q l').trans (dvd_pow_self l two_ne_zero)) N))) =
      χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2))))
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n =
      (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0) +
        ∑ q' ∈ l'.primeFactors.attach,
          if q'.1 ∣ n then (qExpansion 1 (F' q'.1 q'.2)).coeff (n / q'.1) else 0) :
    SquarefreeDecomposition χ l f := by
  have hpf : l.primeFactors = insert q l'.primeFactors := by
    rw [hl, Nat.primeFactors_mul hq.ne_zero hl', hq.primeFactors, Finset.singleton_union]
  have hmem : ∀ {q'}, q' ∈ l.primeFactors → q' ≠ q → q' ∈ l'.primeFactors := fun h hne ↦ by
    rw [hpf, Finset.mem_insert] at h
    exact h.resolve_left hne
  refine ⟨fun q' hq' ↦ if h : q' = q then h ▸ F else F' q' (hmem hq' h),
    fun q' hq' ↦ if h : q' = q then h ▸ χ₁ else χ'' q' (hmem hq' h), ?_, ?_, ?_⟩
  · intro q' hq'
    by_cases h : q' = q
    · subst h
      simpa using hF
    · simp only [h, ↓reduceDIte]
      exact hF' q' (hmem hq' h)
  · intro q' hq'
    by_cases h : q' = q
    · subst h
      simpa using hχ₁
    · simp only [h, ↓reduceDIte]
      exact hχ'' q' (hmem hq' h)
  · intro n
    rw [hcoeff n]
    symm
    -- both sums over `attach` become sums over the sets, the summand guarded by membership
    rw [← Finset.univ_eq_attach, ← Finset.sum_dite_of_true (fun _ hi ↦ hi) (fun q' hq' ↦
        if q' ∣ n then (qExpansion 1
          ((fun q' hq' ↦ if h : q' = q then h ▸ F else F' q' (hmem hq' h)) q' hq')).coeff (n / q')
        else 0) fun _ _ ↦ 0,
      Finset.sum_congr hpf fun _ _ ↦ rfl, Finset.sum_insert hql', ← Finset.univ_eq_attach,
      ← Finset.sum_dite_of_true (fun _ hi ↦ hi) (fun q' hq' ↦ if q' ∣ n then
        (qExpansion 1 (F' q' hq')).coeff (n / q') else 0) fun _ _ ↦ 0]
    have hqpf : q ∈ l.primeFactors := hpf ▸ Finset.mem_insert_self q _
    congr 1
    · rw [dite_eq_left hqpf]
      simp
    · refine Finset.sum_congr rfl fun q' hq' ↦ ?_
      have hne : q' ≠ q := fun h ↦ hql' (h ▸ hq')
      have hq'pf : q' ∈ l.primeFactors := hpf ▸ Finset.mem_insert_of_mem hq'
      rw [dite_eq_left hq'pf, dite_eq_left hq']
      simp [hne]

/-- **Peeling a prime off `f`.** The multiples-of-`q` part `h` of `f`, read at level `N q²`
(`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq`), is `V_q F` on
coefficients for a form `F` with a nebentypus `χ₁` over `χ`, read at the level `N (q l')² / q`
the decomposition wants. -/
private theorem exists_qExpansion_coeff_eq_ite_coprime_zero_and_ite_dvd {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {q : ℕ}
    (hqp : q.Prime) (l' : ℕ) :
    ∃ (h : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
      (F : CuspForm ((Gamma1 (N * (q * l') ^ 2 / q)).map (mapGL ℝ)) k)
      (χ₁ : (ZMod (N * (q * l') ^ 2 / q))ˣ →* ℂˣ),
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))) ∧
      F ∈ cuspFormCharSpace k χ₁ ∧
      χ₁.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right ((dvd_mul_right q l').trans (dvd_pow_self (q * l') two_ne_zero))
          N))) = χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N ((q * l') ^ 2))) ∧
      (∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n q then 0 else (qExpansion 1 f).coeff n) ∧
      ∀ n, (qExpansion 1 h).coeff n = if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0 := by
  have : NeZero q := ⟨hqp.ne_zero⟩
  obtain ⟨h, hhχ, hhcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq χ hf (L := q)
  have hNq2q : N * q ^ 2 / q = N * q := by rw [sq, ← mul_assoc, Nat.mul_div_cancel _ hqp.pos]
  have hqM : q ∣ N * q ^ 2 := dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N
  have hNMq : N ∣ N * q ^ 2 / q := by rw [hNq2q]; exact Nat.dvd_mul_right N q
  obtain ⟨F, hF, hFcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd hqM
      (χ.comp (ZMod.unitsMap hNMq))
      (by simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hhχ) (by
        rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff]
        intro n hn
        rw [hhcoeff n]
        split_ifs with hc
        · rfl
        · exact absurd (hqp.coprime_iff_not_dvd.mpr hn).symm hc)
  -- `F` read at the level `N (q l')² / q`
  have hNql : N * (q * l') ^ 2 / q = N * q * l' ^ 2 := by
    have h : N * (q * l') ^ 2 = N * q * l' ^ 2 * q := by ring
    rw [h, Nat.mul_div_cancel _ hqp.pos]
  have hdiv : N * q ^ 2 / q ∣ N * (q * l') ^ 2 / q := by
    rw [hNq2q, hNql]
    exact dvd_mul_right _ _
  refine ⟨h, _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hdiv) F,
    (χ.comp (ZMod.unitsMap hNMq)).comp (ZMod.unitsMap hdiv), hhχ,
    CuspForm.ofLe_mem_cuspFormCharSpace _ hdiv hF, ?_, hhcoeff,
    fun n ↦ by rw [hFcoeff n, CuspForm.coe_ofLe]⟩
  simp only [MonoidHom.comp_assoc, ZMod.unitsMap_comp]

omit [NeZero N] in
/-- **The rest after peeling.** For the multiples-of-`q` part `h` of `f`, the difference
`f' = f - h` at level `N q²` carries the coefficients of `f` at the indices coprime to `q`, so
`a_n(f) = a_n(h) + a_n(f')`. -/
private theorem exists_qExpansion_coeff_eq_ite_coprime_and_add {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {q : ℕ}
    {h : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k}
    (hhχ : h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))))
    (hhcoeff : ∀ n, (qExpansion 1 h).coeff n =
      if Nat.Coprime n q then 0 else (qExpansion 1 f).coeff n) :
    ∃ f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k,
      f' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))) ∧
      (∀ n, (qExpansion 1 f').coeff n =
        if Nat.Coprime n q then (qExpansion 1 f).coeff n else 0) ∧
      ∀ n, (qExpansion 1 f).coeff n = (qExpansion 1 h).coeff n + (qExpansion 1 f').coeff n := by
  have hNM : N ∣ N * q ^ 2 := Nat.dvd_mul_right N _
  set f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k :=
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hNM) f - h with hf'
  have hcoeff (n : ℕ) : (qExpansion 1 f').coeff n =
      if Nat.Coprime n q then (qExpansion 1 f).coeff n else 0 := by
    rw [hf', FunLike.coe_sub,
      _root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
      CuspForm.coe_ofLe, hhcoeff n]
    split_ifs <;> simp
  refine ⟨f', Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ hNM hf) hhχ, hcoeff,
    fun n ↦ ?_⟩
  rw [hcoeff n, hhcoeff n]
  split_ifs <;> simp

omit [NeZero N] in
/-- The base case of Lemma 4.6.7, `l = q` prime: the peeled prime is the whole decomposition. -/
private theorem squarefreeDecomposition_prime {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {q : ℕ} (hqp : q.Prime)
    {F : CuspForm ((Gamma1 (N * (q * 1) ^ 2 / q)).map (mapGL ℝ)) k}
    {χ₁ : (ZMod (N * (q * 1) ^ 2 / q))ˣ →* ℂˣ} (hF : F ∈ cuspFormCharSpace k χ₁)
    (hχ₁ : χ₁.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
      (dvd_mul_of_dvd_right ((dvd_mul_right q 1).trans (dvd_pow_self (q * 1) two_ne_zero)) N))) =
      χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N ((q * 1) ^ 2))))
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n =
      if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0) :
    SquarefreeDecomposition χ (q * 1) f := by
  have hempty : ∀ q', q' ∈ Nat.primeFactors 1 → False := fun q' hq' ↦ by
    rw [Nat.primeFactors_one] at hq'
    exact Finset.notMem_empty q' hq'
  refine squarefreeDecomposition_of_insert hqp rfl (fun h ↦ hempty q h) one_ne_zero
    (fun q' hq' ↦ (hempty q' hq').elim) (fun q' hq' ↦ (hempty q' hq').elim)
    (fun q' hq' ↦ (hempty q' hq').elim) (fun q' hq' ↦ (hempty q' hq').elim) F χ₁ hF hχ₁ fun n ↦ ?_
  rw [hcoeff n, Finset.sum_eq_zero fun x _ ↦ (hempty x.1 x.2).elim, add_zero]

/-- The inductive step of Lemma 4.6.7 at `l = q * l'`: peel `q`, apply the induction hypothesis
to the rest at level `N q²` and modulus `l'` (or, when `l' = 1`, nothing remains), and assemble. -/
private theorem squarefreeDecomposition_mul {m : ℕ}
    (ih : ∀ (l : ℕ), l.primeFactors.card = m → ∀ (N : ℕ) [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), f ∈ cuspFormCharSpace k χ →
      Squarefree l → (∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) →
      SquarefreeDecomposition χ l f)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {q l' : ℕ} (hqp : q.Prime) (hl'0 : l' ≠ 0)
    (hql' : q ∉ l'.primeFactors) (hcard : l'.primeFactors.card = m) (hsq : Squarefree l')
    (hvan : ∀ n, Nat.Coprime n (q * l') → (qExpansion 1 f).coeff n = 0) :
    SquarefreeDecomposition χ (q * l') f := by
  have : NeZero q := ⟨hqp.ne_zero⟩
  obtain ⟨h, F, χ₁, hhχ, hF, hχ₁, hhcoeff, hFcoeff⟩ :=
    exists_qExpansion_coeff_eq_ite_coprime_zero_and_ite_dvd hf hqp l'
  obtain ⟨f', hf'χ, hf'coeff, hsplit⟩ :=
    exists_qExpansion_coeff_eq_ite_coprime_and_add hf hhχ hhcoeff
  have hf'van (n : ℕ) (hn : Nat.Coprime n l') : (qExpansion 1 f').coeff n = 0 := by
    rw [hf'coeff n]
    split_ifs with hnq
    · exact hvan n (Nat.Coprime.mul_right hnq hn)
    · rfl
  by_cases hl'1 : l' = 1
  · -- `l = q` is prime: only the peeled prime contributes
    subst hl'1
    exact squarefreeDecomposition_prime hqp hF hχ₁ fun n ↦ by
      rw [hsplit n, hFcoeff n, hf'van n (Nat.coprime_one_right n), add_zero]
  · -- `l' > 1`: the induction hypothesis applies to `f'` at level `N q²`
    obtain ⟨F', χ'', hF', hχ'', hcoeff'⟩ :=
      ih l' hcard (N * q ^ 2) (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))) f' hf'χ hsq
        hf'van
    have hlev : N * q ^ 2 * l' ^ 2 = N * (q * l') ^ 2 := by ring
    have hlevq (q' : ℕ) : N * q ^ 2 * l' ^ 2 / q' = N * (q * l') ^ 2 / q' := by rw [hlev]
    refine squarefreeDecomposition_of_insert hqp rfl hql' hl'0
      (fun q' hq' ↦ _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_of_eq (hlevq q')))
        (F' q' hq'))
      (fun q' hq' ↦ (χ'' q' hq').comp (ZMod.unitsMap (dvd_of_eq (hlevq q')))) ?_ ?_ F χ₁ hF hχ₁
      fun n ↦ ?_
    · intro q' hq'
      exact CuspForm.ofLe_mem_cuspFormCharSpace _ _ (hF' q' hq')
    · intro q' hq'
      have := congrArg (fun ψ ↦ ψ.comp (ZMod.unitsMap (dvd_of_eq hlev))) (hχ'' q' hq')
      simp only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at this ⊢
      exact this
    · rw [hsplit n, hFcoeff n, hcoeff' n]
      congr 1
      exact Finset.sum_congr rfl fun q' _ ↦ by rw [CuspForm.coe_ofLe]

/-- **Miyake's Lemma 4.6.7: the squarefree decomposition.** If `f ∈ S_k(Γ₁(N), χ)` vanishes at
every index coprime to a squarefree `l`, then `a_n(f) = ∑_{q ∈ l.primeFactors, q ∣ n} a_{n/q}(F q)`,
the sum over the primes `q` dividing `l`, for forms
`F q ∈ S_k(Γ₁(N l² / q), χ' q)` with `χ' q` lying over `χ`: coefficient by coefficient,
`f = ∑_{q ∈ l.primeFactors} V_q (F q)`. -/
theorem exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {l : ℕ}
    (hsq : Squarefree l)
    (hvan : ∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) :
    ∃ (F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (N * l ^ 2 / q)).map (mapGL ℝ)) k)
      (χ' : ∀ q ∈ l.primeFactors, (ZMod (N * l ^ 2 / q))ˣ →* ℂˣ),
      (∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
          (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) N))) =
          χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2)))) ∧
      ∀ n, (qExpansion 1 f).coeff n = ∑ q ∈ l.primeFactors.attach,
        if q.1 ∣ n then (qExpansion 1 (F q.1 q.2)).coeff (n / q.1) else 0 := by
  suffices key : ∀ (m l : ℕ), l.primeFactors.card = m → ∀ (N : ℕ) [NeZero N]
      (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      f ∈ cuspFormCharSpace k χ → Squarefree l →
      (∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) → SquarefreeDecomposition χ l f from
    key _ l rfl N χ f hf hsq hvan
  intro m
  induction m with
  | zero =>
    -- no prime factors: `l = 1` (as `l ≠ 0`), every coefficient vanishes, the families are empty
    intro l hcard N _ χ f _ hsq hvan
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard) with rfl | rfl
    · exact absurd rfl hsq.ne_zero
    · exact ⟨fun q hq ↦ absurd hq (by simp), fun q hq ↦ absurd hq (by simp),
        fun q hq ↦ absurd hq (by simp), fun q hq ↦ absurd hq (by simp), fun n ↦ by
          rw [Finset.sum_eq_zero fun x _ ↦ absurd x.2 (by simp)]
          exact hvan n (Nat.coprime_one_right n)⟩
  | succ m ih =>
    intro l hcard N _ χ f hf hsq hvan
    obtain ⟨q, hq⟩ : l.primeFactors.Nonempty := Finset.card_pos.mp (hcard ▸ Nat.succ_pos m)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨l', rfl⟩ : ∃ l', l = q * l' := Nat.dvd_of_mem_primeFactors hq
    have hl'0 : l' ≠ 0 := right_ne_zero_of_mul hsq.ne_zero
    have hql' : q ∉ l'.primeFactors := fun h ↦
      (Nat.squarefree_iff_prime_squarefree.mp hsq q hqp)
        (Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_primeFactors h))
    refine squarefreeDecomposition_mul ih hf hqp hl'0 hql' ?_
      (hsq.squarefree_of_dvd (dvd_mul_left l' q)) hvan
    rw [Nat.primeFactors_mul hqp.ne_zero hl'0, hqp.primeFactors, Finset.singleton_union,
      Finset.card_insert_of_notMem hql'] at hcard
    omega

end TauCeti
