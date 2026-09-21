/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.Units
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Descent
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelCommute
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Commute
public import TauCeti.NumberTheory.ModularForms.Newforms.SquarefreeDecomposition

/-!
# The coefficient formula of the descent

For a prime `p ∣ N`, a squarefree `L` coprime to `p` whose primes divide `N`, and a cusp form
`f ∈ S_k(Γ₁(N), χ)` whose nebentypus is pulled back from level `N / p` and which vanishes at
every index coprime to `p L`, the descent `Φ = descendSlash k p N` satisfies

`a_m(Φ f) = (|family| / p) · a_m(g)`  for every `m` coprime to `L`,

where `g` is the coprime filter of `f` read at level `L N / p`. Rescaling by the nonzero
`|family| = descendMatrixCount p N` turns that into the **descent witness**: a cusp form
`F ∈ S_k(Γ₁(N / p), χ₀)` with `a_m(F) = a_{pm}(f)` at every `m` coprime to `L` — one prime
peeled off `f`, with its coefficients shifted by `p`. This is Miyake's Lemma 4.6.14, and the
inductive step of his Lemma 4.6.8.

The proof splits `f = Δ + V_p g` at level `L N`. The level-raise descends to
`(|family| / p) • g` (`Descent/LevelRaise/Commute.lean`), and the difference `Δ` vanishes at
every index coprime to `L`, so the squarefree decomposition writes it as `∑_{q ∈ l.primeFactors}
V_q F_q` (`SquarefreeDecomposition.lean`); the descent commutes with each `V_q` and kills it at
the indices coprime to `L`.

## Main results

* `TauCeti.qExpansion_coeff_descendSlash_eq_zero_of_coprime`: the descent of a form vanishing at
  the indices coprime to a squarefree `l` again vanishes there.
* `TauCeti.qExpansion_coeff_descendSlash_eq_of_coprime`: the coefficient formula above.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime`: the descent
  witness.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean` —
`miyake_4_6_14_coeff_formula` with its `delta_vanishing_*` helpers, and the rescaling of
`HeckeDescent.lean`. The source keeps the descent as an explicit coset list and transports forms
across equalities of levels by casts; here the descent is `descendSlash`/`descendCuspForm`,
levels are related by divisibility, and the vanishing half is stated on its own so that the
squarefree decomposition enters once.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemmas 4.6.8 and 4.6.14.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.7.
-/
public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N p L : ℕ} {k : ℤ}

/-- **The difference `f − V_p g` vanishes at the indices coprime to `L`.** At `n = p m` both
have the coefficient `a_{pm}(f)`; at `p ∤ n` the index is coprime to `p L`, so `a_n(f) = 0`,
and `V_p g` is supported on the multiples of `p`. -/
private theorem qExpansion_coeff_ofLe_sub_levelRaise_eq_zero (hp : p.Prime) (hpN : p ∣ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : ∀ m, (qExpansion 1 g).coeff m =
      if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0)
    (n : ℕ) (hn : Nat.Coprime n L) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 ⇑(_root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L)))) g)).coeff n = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
    map_sub, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
      (one_mem_strictPeriods_Gamma1_map _), _root_.CuspForm.coe_ofLe]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos, hg,
      ite_eq_left (Nat.coprime_mul_iff_left.mp hn).2, sub_self]
  · simp only [hpn, ↓reduceIte, sub_zero]
    exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hpn).symm hn)

/-- **The difference `f − V_p g` has the nebentypus of `f`, read at level `L N`.** -/
private theorem ofLe_sub_levelRaise_mem_cuspFormCharSpace (hp : p.Prime) (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L)))) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L)))) g ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_left N L))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ (dvd_mul_left N L) hf) ?_
  have h := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd
    (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L))) _ hg
  rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at h
  rwa [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

/-! ### The descent of the difference vanishes at the indices coprime to `L` -/

section Core

variable {M : ℕ}

private theorem descendSlash_smul_slash_scaleGL_eq_coe_levelRaise (hp : p.Prime) {l q : ℕ}
    (hpM : p ∣ M) (hq : q.Prime) (hql : q ∣ l) (hpl : Nat.Coprime p l)
    [NeZero (M * l ^ 2 / q)] (hpN' : p ∣ M * l ^ 2 / q) (hMN' : M ∣ M * l ^ 2 / q)
    (hle : q * (M * l ^ 2 / q / p) ∣ M * l ^ 2 / p)
    {χM : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χM = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {χ' : (ZMod (M * l ^ 2 / q))ˣ →* ℂˣ}
    (hχ' : χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) M))) =
      χM.comp (ZMod.unitsMap (Nat.dvd_mul_right M (l ^ 2))))
    {F : CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k} (hF : F ∈ cuspFormCharSpace k χ') :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ hcomp' : χ' = (χ₀.comp (ZMod.unitsMap ((Nat.div_dvd_div_iff_right hpM hpN').mpr
        hMN'))).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN')),
      descendSlash k p (M * l ^ 2) ((q : ℂ) ^ (1 - k) • (⇑F ∣[k] scaleGL q)) =
        ⇑(CuspForm.levelRaise q (Gamma1_map_le_conjAct_scaleGL_of_dvd hle)
          (descendCuspForm k hp hpN' hcomp' hF)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hqMl : q ∣ M * l ^ 2 := dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) M
  have : NeZero (M * l ^ 2) := ⟨fun h ↦ NeZero.ne (M * l ^ 2 / q) (by rw [h, Nat.zero_div])⟩
  have hcomp' := eq_comp_unitsMap_of_comp_unitsMap_eq hpM hMN' (Nat.div_dvd_of_dvd hqMl) hcomp hχ'
  refine ⟨hcomp', ?_⟩
  have h := descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_cuspFormCharSpace k hp hpN'
    (hpl.coprime_dvd_right hql) hcomp' hF
  rw [CuspForm.coe_levelRaise, Nat.mul_div_cancel' hqMl] at h
  rw [h, CuspForm.coe_levelRaise, coe_descendCuspForm]

/-- **Each peeled piece descends to a form supported on the multiples of its prime.** The
descent at level `M l²` of the level-raise `V_q F_q` is `V_q` of the bundled descent of `F_q`
(`descendSlash_smul_slash_scaleGL_eq_coe_levelRaise`), whose `m`-th coefficient vanishes when
`q ∤ m`. -/
private theorem exists_descendSlash_coe_levelRaise_eq_coe_and_coeff_eq_zero [NeZero M]
    (hp : p.Prime) (hpM : p ∣ M) {l : ℕ} (hl : l ≠ 0) (hpl : Nat.Coprime p l)
    {χ : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k}
    {χ' : ∀ q ∈ l.primeFactors, (ZMod (M * l ^ 2 / q))ˣ →* ℂˣ}
    (hF : ∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq))
    (hχ' : ∀ q (hq : q ∈ l.primeFactors),
      (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right
        ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) M))) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (l ^ 2))))
    {m : ℕ} (hm : Nat.Coprime m l) (q : {x // x ∈ l.primeFactors}) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
    ∃ W : CuspForm ((Gamma1 (M * l ^ 2 / p)).map (mapGL ℝ)) k,
      descendSlash k p (M * l ^ 2) ⇑(CuspForm.levelRaise q.1
        (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq (Nat.mul_div_cancel'
          (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors q.2).trans (dvd_pow_self l two_ne_zero)) M))))
        (F q.1 q.2)) = ⇑W ∧ (qExpansion 1 W).coeff m = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hq : q.1.Prime := Nat.prime_of_mem_primeFactors q.2
  have : NeZero q.1 := ⟨hq.ne_zero⟩
  have hql : q.1 ∣ l := Nat.dvd_of_mem_primeFactors q.2
  have hq2 : q.1 ∣ l ^ 2 := hql.trans (dvd_pow_self l two_ne_zero)
  have hqMl : q.1 ∣ M * l ^ 2 := dvd_mul_of_dvd_right hq2 M
  have hMN' : M ∣ M * l ^ 2 / q.1 := Dvd.intro _ (Nat.mul_div_assoc M hq2).symm
  have hpN' : p ∣ M * l ^ 2 / q.1 := hpM.trans hMN'
  have : NeZero (M * l ^ 2 / q.1) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (Nat.mul_ne_zero (NeZero.ne M) (pow_ne_zero 2 hl))) hqMl) hq.pos).ne'⟩
  have hle : q.1 * (M * l ^ 2 / q.1 / p) ∣ M * l ^ 2 / p :=
    dvd_of_eq (by rw [← Nat.mul_div_assoc q.1 hpN', Nat.mul_div_cancel' hqMl])
  obtain ⟨hcomp', hW⟩ := descendSlash_smul_slash_scaleGL_eq_coe_levelRaise hp hpM hq hql hpl
    hpN' hMN' hle hcomp (hχ' q.1 q.2) (hF q.1 q.2)
  refine ⟨_, by rw [CuspForm.coe_levelRaise]; exact hW, ?_⟩
  rw [CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
    (one_mem_strictPeriods_Gamma1_map _)]
  have hqm : ¬ q.1 ∣ m := fun h ↦
    hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (hm.coprime_dvd_right hql).symm h)
  simp only [hqm, ↓reduceIte]

/-- **The descent of a form vanishing off `l` vanishes at the indices coprime to `l`** (the core
of Miyake's Lemma 4.6.14). For `Δ ∈ S_k(Γ₁(M), χ)` with `χ` pulled back from `χ₀` modulo `M / p`,
vanishing at every index coprime to a squarefree `l` coprime to `p`, the descent
`descendSlash k p M Δ` has `a_m = 0` at every `m` coprime to `l`: `Δ = ∑_{q ∣ l} V_q F_q`, the
descent commutes with each `V_q`, and each `V_q` of a bundled descent is supported on the
multiples of `q`. -/
theorem qExpansion_coeff_descendSlash_eq_zero_of_coprime [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    {l : ℕ} (hsq : Squarefree l) (hpl : Nat.Coprime p l) {χ : (ZMod M)ˣ →* ℂˣ}
    {χ₀ : (ZMod (M / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {Δ : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hΔ : Δ ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n l → (qExpansion 1 Δ).coeff n = 0) (m : ℕ) (hm : Nat.Coprime m l) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 (descendSlash k p M ⇑Δ)).coeff m = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, χ', hF, hχ', hΔsum⟩ := exists_coe_eq_sum_coe_levelRaise_of_squarefree hsq hΔ hvan
  -- the descent at level `M` is the descent at level `M l²`
  have h08a := descendSlash_mul_left_of_coprime k hp hpM (hpl.pow_right 2) (f := ⇑Δ)
    fun ε hε ↦ SlashInvariantFormClass.slash_action_eq Δ _ (Subgroup.mem_map_of_mem _ hε)
  rw [Nat.mul_comm] at h08a
  rw [← h08a, hΔsum, descendSlash_finsetSum]
  -- each summand descends to `V_q` of a bundled descent, supported on the multiples of `q`
  have hterm := exists_descendSlash_coe_levelRaise_eq_coe_and_coeff_eq_zero hp hpM hsq.ne_zero
    hpl hcomp hF hχ' hm
  choose W hW hW0 using hterm
  have hsum := map_sum ((PowerSeries.coeff m).comp
    ((ModularForm.qExpansionLinearMap (h := 1) one_pos (one_mem_strictPeriods_Gamma1_map _)
      k).comp CuspForm.toModularFormₗ)) W l.primeFactors.attach
  simp only [LinearMap.comp_apply, ModularForm.qExpansionLinearMap_apply,
    CuspForm.toModularFormₗ_eq_coe, ModularFormClass.coe_modularForm] at hsum
  rw [Finset.sum_congr rfl fun q _ ↦ hW q, ← FunLike.coe_sum, hsum]
  exact Finset.sum_eq_zero fun q _ ↦ hW0 q

end Core

/-! ### The coefficient formula of the descent -/


/-- **The coefficients of the descent** (Miyake, Lemma 4.6.14). Let `f ∈ S_k(Γ₁(N), χ)` with `χ`
pulled back from `χ₀` modulo `N / p`, vanishing at every index coprime to `p L` for a squarefree
`L` coprime to `p`, and let `g` of level `L N / p` carry the coefficients of `f` along the
multiples of `p`: `a_m(g) = a_{pm}(f)` for `m` coprime to `L`, and `a_m(g) = 0` otherwise. Then
at every `m` coprime to `L`, `a_m(descendSlash k p N f) = (|family| / p) · a_m(g)`. -/
theorem qExpansion_coeff_descendSlash_eq_of_coprime [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    {L : ℕ} (hL : Squarefree L) (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ}
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L))))
    (hgcoeff : ∀ m, (qExpansion 1 g).coeff m =
      if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0)
    (m : ℕ) (hm : Nat.Coprime m L) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 (descendSlash k p N ⇑f)).coeff m =
      (descendMatrixCount p N : ℂ) / p * (qExpansion 1 g).coeff m := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (L * N) := ⟨Nat.mul_ne_zero hL.ne_zero (NeZero.ne N)⟩
  have hpM : p ∣ L * N := dvd_mul_of_dvd_right hpN L
  -- the descent at level `N` is the descent at level `L N`
  have h08a := descendSlash_mul_left_of_coprime k hp hpN hpL (f := ⇑f)
    fun ε hε ↦ SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hε)
  -- `f = Δ + V_p g` at level `L N`
  set Vg := CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
    (dvd_of_eq (Nat.mul_div_cancel' hpM))) g with hVg
  set Δ := _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f - Vg
    with hΔ
  have hfΔ : ⇑f = ⇑Δ + ⇑Vg := by
    rw [hΔ, FunLike.coe_sub, _root_.CuspForm.coe_ofLe, sub_add_cancel]
  -- the level-raise descends to a multiple of `g`
  have hVg' : descendSlash k p (L * N) ⇑Vg = ((descendMatrixCount p N : ℂ) / p) • ⇑g := by
    rw [hVg, CuspForm.coe_levelRaise, descendSlash_smul_slash_scaleGL k hp hpM g,
      descendMatrixCount_mul_left_of_coprime hpL N]
  -- the difference descends to a form vanishing at `m`
  have hχM := comp_unitsMap_eq_comp_unitsMap_of_comp_mul_left hpN (L := L) hcomp
  have hΔχ : Δ ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_left N L))) :=
    ofLe_sub_levelRaise_mem_cuspFormCharSpace hp hpN hcomp hf hg
  have hD0 : (qExpansion 1 (descendSlash k p (L * N) ⇑Δ)).coeff m = 0 :=
    qExpansion_coeff_descendSlash_eq_zero_of_coprime hp hpM hL hpL hχM hΔχ
      (qExpansion_coeff_ofLe_sub_levelRaise_eq_zero hp hpN hvan hgcoeff) m hm
  -- add the two `q`-expansions through the bundled descent
  rw [← h08a, hfΔ, descendSlash_add, hVg', ← coe_descendCuspForm k hp hpM hχM hΔχ,
    ← FunLike.coe_smul, ← FunLike.coe_add,
    FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map _),
    map_add, coe_descendCuspForm, hD0, zero_add, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul]


/-! ### The descent witness -/

/-- **The descent witness** (Miyake, Lemma 4.6.8, the inductive step). For `f ∈ S_k(Γ₁(N), χ)`
with `χ` pulled back from `χ₀` modulo `N / p`, vanishing at every index coprime to `p L` for a
squarefree `L` coprime to `p` whose primes divide `N`, there is `F ∈ S_k(Γ₁(N / p), χ₀)` with
`a_m(F) = a_{pm}(f)` at every `m` coprime to `L`: the descent of `f`, rescaled by
`p / |family|`, by the coefficient formula of the descent and the coprime-filter descent. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N) {L : ℕ} (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ F : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k, F ∈ cuspFormCharSpace k χ₀ ∧
      ∀ m, Nat.Coprime m L → (qExpansion 1 F).coeff m = (qExpansion 1 f).coeff (p * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg, hgcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul χ hf hp hpN hcomp hL hLN
      hpL hvan
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcount : (descendMatrixCount p N : ℂ) ≠ 0 := by
    by_cases h : p ^ 2 ∣ N
    · rw [descendMatrixCount_of_sq_dvd h]
      exact hp0
    · rw [descendMatrixCount_of_not_sq_dvd h]
      exact_mod_cast p.succ_ne_zero
  refine ⟨((p : ℂ) / descendMatrixCount p N) • descendCuspForm k hp hpN hcomp hf,
    Submodule.smul_mem _ _ (descendCuspForm_mem_cuspFormCharSpace k hp hpN hcomp hf),
    fun m hm ↦ ?_⟩
  rw [FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul, coe_descendCuspForm,
    qExpansion_coeff_descendSlash_eq_of_coprime hp hpN hL hpL hcomp hf hvan hg hgcoeff m hm,
    hgcoeff m, ite_eq_left hm]
  field_simp


end TauCeti
