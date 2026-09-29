/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.IsDemushkin
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Prescription
public import TauCeti.Topology.Algebra.Group.Profinite.Index.PadicUnits

/-!
# The existence theorem of the classification of Demushkin groups

The classification of Demushkin groups attaches to a Demushkin group `G` its rank `n` and the
image `A ≤ ℤ_pˣ` of its canonical character, the unique continuous character with the prescription
property (`TauCeti.HasPrescriptionProperty`). Labute's existence theorem (Theorem 1 with Remark 2,
after Serre) says which pairs `(n, A)`, with `A` a closed pro-`p` subgroup of `ℤ_pˣ`, occur:

1. `n` even and `p ^ n > (A : A^p)`;
2. `n` odd with `n ≥ 3`, so `p = 2`, and `A = {±1} × U^(f)` with `2 ≤ f ≤ ∞`;
3. `n = 1` and `A = {±1}`.

This file proves the realization half for every pair of the first and third situations, and for
the pairs of the second situation with finite `f`: each such pair is the pair of invariants of a
Demushkin group, exhibited as a one-relator pro-`p` group `⟨x₁, …, xₙ ∣ r⟩` on `n` generators,
presented by one of the normal-form words of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic`. The realizing group is
Demushkin of rank `n` (`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.IsDemushkin`),
it has exactly one continuous character with the prescription property
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Prescription`), and the image of
that character is `A`, which is what the statements here add: for each normal form, the image of
*every* character with the prescription property, read off the forced values of that character.
The pairs are matched to the words through the classification of the closed subgroups of `ℤ_pˣ`,
the principal unit groups for odd `p` and Labute's four families
`U^(f)`, `{±1} × U^(f)`, `{±1}`, `U^[f]` for `p = 2`:

| `A`                        | realizing relator                                    |
|----------------------------|------------------------------------------------------|
| `1`                        | `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, `q = 0`           |
| `U^(f) = 1 + p^f ℤ_p`      | `x₁^{p^f} (x₁, x₂) ⋯ (x_{n-1}, x_n)`                    |
| `{±1}`, `n` even           | `x₁² (x₁, x₂) ⋯ (x_{n-1}, x_n)`, `q = 2`                |
| `{±1} × U^(f)`, `n` even   | `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, `n ≥ 4` |
| `{±1} × U^(f)`, `n` odd    | `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`                |
| `U^[g]`, `n = 2`           | `x₁^{2 + 2^g} (x₁, x₂)`                                |
| `U^[g]`, `n ≥ 4`           | `x₁^{2 + 2^g} (x₁, x₂) x₃^{2^{g+1}} (x₃, x₄) ⋯`         |
| `{±1}`, `n = 1`            | `x₁²`, the group `ℤ/2`                                |

The condition `p ^ n > (A : A^p)` of the even case is exactly what excludes `n = 0` and, at
`p = 2`, the non-procyclic family `{±1} × U^(f)` in rank two, where `(A : A²) = 4`. The odd case
is proved for finite `f`; the endpoint `f = ∞`, with `A = {±1}` and relator `x₁² (x₂, x₃) ⋯`, has
no relator word here. The converse half of the existence theorem, that no other pair occurs, is
Labute's Theorem 1 through the normal forms of every Demushkin group and is not proved here.

## Main results

* `TauCeti.range_eq_unitsPrincipal_of_hasPrescriptionProperty_demushkinWordNeTwo`,
  `TauCeti.range_eq_bot_of_hasPrescriptionProperty_demushkinWordNeTwo`,
  `TauCeti.range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordNeTwo`,
  `TauCeti.range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoOdd`,
  `TauCeti.range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd_one`,
  `TauCeti.range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoEven`,
  `TauCeti.range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_two_pow`,
  `TauCeti.range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_two_pow`: the image of the
  canonical character of each normal form, as the image of any character with the prescription
  property; the last two are the twisted subgroups `U^[g]` of the words with `α = 2^g`.
* `TauCeti.exists_isDemushkin_range_eq_bot_of_even`,
  `TauCeti.exists_isDemushkin_range_eq_unitsPrincipal_of_even`,
  `TauCeti.exists_isDemushkin_range_eq_zpowers_neg_one_of_even`,
  `TauCeti.exists_isDemushkin_range_eq_unitsPlusMinus_of_even`,
  `TauCeti.exists_isDemushkin_range_eq_topologicalClosure_zpowers_of_even`: each family of closed
  subgroups of `ℤ_pˣ` is realized in even rank by the normal form of the table.
* `TauCeti.exists_isDemushkin_range_eq_of_even_of_lt`: **the existence theorem in even rank**: for
  `n` even and `A ≤ ℤ_pˣ` closed and pro-`p` with `(A : A^p) < p ^ n`, a Demushkin group of rank
  `n` presented on `n` generators by one relator, whose unique character with the prescription
  property has image `A`.
* `TauCeti.exists_isDemushkin_range_eq_unitsPlusMinus_of_odd`: **the existence theorem in odd rank
  `n ≥ 3`**, for `A = {±1} × U^(f)` with `2 ≤ f < ∞`.
* `TauCeti.exists_isDemushkin_one_range_eq_zpowers_neg_one`: **the existence theorem in rank
  one**, for `A = {±1}`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorem 1, Theorem 4 and its corollary, and Remark 2.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63),
  Theorem 3.2.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.10) and
  (3.9.19).
-/

public section

namespace TauCeti

open Subgroup

/-! ### The image of the canonical character of each normal form -/

section NeTwo

variable {p : ℕ} [Fact p.Prime] {q n : ℕ}
  {χ : presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)} →ₜ* ℤ_[p]ˣ}

/-- The image of a character with the prescription property of the `q ≠ 2` normal form is the
closed subgroup generated by its value on `x₂`, for `p ∣ q` and `n ≥ 2` even. -/
theorem range_eq_topologicalClosure_zpowers_of_hasPrescriptionProperty_demushkinWordNeTwo
    (hq : p ∣ q) (hn : Even n) (hn₁ : 1 < n) (hχ : HasPrescriptionProperty χ) :
    χ.toMonoidHom.range = (zpowers (χ (presentedProPGen p n _ 1))).topologicalClosure := by
  have h := eq_orientationNeTwo_of_hasPrescriptionProperty q n χ hq hn hn₁ hχ
  have hr := range_orientationNeTwo q n (χ (presentedProPGen p n _ 1))
    ((presentedProP.isProP p _ _).mem_unitsPrincipal_one χ _) hn₁
  rwa [← h] at hr

/-- **The image of the canonical character of the `q ≠ 2` normal form is `U^(f) = 1 + qℤ_p`**, for
`q = p ^ f` with `f ≥ 1`, and `f ≥ 2` when `p = 2`, and `n ≥ 2` even: any character with the
prescription property takes `x₂` to `(1 - q)⁻¹`, of exact level `f`. -/
theorem range_eq_unitsPrincipal_of_hasPrescriptionProperty_demushkinWordNeTwo (hn : Even n)
    (hn₁ : 1 < n) {f : ℕ} (hq : q = p ^ f) (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f)
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = unitsPrincipal p f := by
  have hq' : p ∣ q := hq ▸ dvd_pow_self p hf.ne'
  obtain ⟨h₁, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff q n χ hq' hn hn₁).1 hχ
  rw [range_eq_topologicalClosure_zpowers_of_hasPrescriptionProperty_demushkinWordNeTwo hq' hn hn₁
    hχ]
  subst hq
  push_cast at h₁
  exact topologicalClosure_zpowers_eq_unitsPrincipal_of_val_mul_one_sub_pow_eq_one hf hf₂ h₁

/-- **The image of the canonical character of the `q = 0` normal form is trivial**, for `n ≥ 2`
even: the relator `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` has no `p`-power part, and any character with
the prescription property takes `x₂` to `(1 - 0)⁻¹ = 1`. -/
theorem range_eq_bot_of_hasPrescriptionProperty_demushkinWordNeTwo (hn : Even n) (hn₁ : 1 < n)
    (hq : q = 0) (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = ⊥ := by
  subst hq
  obtain ⟨h₁, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff 0 n χ (dvd_zero p) hn hn₁).1 hχ
  rw [range_eq_topologicalClosure_zpowers_of_hasPrescriptionProperty_demushkinWordNeTwo (dvd_zero p)
    hn hn₁ hχ]
  have h₁' : χ (presentedProPGen p n _ 1) = 1 := Units.val_inj.1 (by simpa using h₁)
  rw [h₁', zpowers_one_eq_bot]
  exact (by rw [coe_bot]; exact isClosed_singleton :
    IsClosed ((⊥ : Subgroup ℤ_[p]ˣ) : Set ℤ_[p]ˣ)).subgroup_topologicalClosure_eq

end NeTwo

section NeTwoDyadic

variable {n : ℕ} {χ : presentedProP 2 (Fin n) {demushkinWordNeTwo 2 n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ}

/-- **The image of the canonical character of the `q = 2` even-rank form `x₁² (x₁, x₂) ⋯` is
`{±1}`**, for `n ≥ 2` even: any character with the prescription property takes `x₂` to
`(1 - 2)⁻¹ = -1`. This is the even-rank form with `α = 0` and level `f = ∞`, whose image is the
endpoint `V^(∞) = {±1}` of the table. -/
theorem range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordNeTwo (hn : Even n)
    (hn₁ : 1 < n) (hχ : HasPrescriptionProperty χ) :
    χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) := by
  obtain ⟨h₁, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff 2 n χ dvd_rfl hn hn₁).1 hχ
  rw [range_eq_topologicalClosure_zpowers_of_hasPrescriptionProperty_demushkinWordNeTwo dvd_rfl hn
    hn₁ hχ]
  have h₁' : χ (presentedProPGen 2 n _ 1) = -1 := by
    refine Units.val_inj.1 ?_
    rw [Units.val_neg, Units.val_one]
    push_cast at h₁
    linear_combination -h₁
  rw [h₁', topologicalClosure_zpowers_neg_one]

end NeTwoDyadic

section TwoOdd

variable {f n : ℕ}

/-- **The image of the canonical character of the `q = 2`, `n` odd normal form is
`{±1} × U^(f)`**, for `f ≥ 2` and `n ≥ 3` odd: any character with the prescription property takes
`x₁` to `-1` and `x₃` to `(1 - 2^f)⁻¹`. -/
theorem range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoOdd (hf : 2 ≤ f)
    (hn : Odd n) (hn₂ : 2 < n)
    {χ : presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = unitsPlusMinus f := by
  obtain ⟨-, h₂, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_iff f n χ (by omega) hn hn₂).1 hχ
  have h := eq_orientationTwoOdd_of_hasPrescriptionProperty f n χ (by omega) hn hn₂ hχ
  have hr := range_orientationTwoOdd_eq_unitsPlusMinus f n _ hn₂ hf h₂
  rwa [← h] at hr

/-- **The image of the canonical character of `ℤ/2` is `{±1}`**: presented on one generator by
`x₁²`, which is the odd word at rank one for every level `f`, any character with the prescription
property is the sign character `χ(x₁) = -1`. -/
theorem range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd_one
    {χ : presentedProP 2 (Fin 1) {demushkinWordTwoOdd f 1 (freeProPGen 2 1)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) := by
  have h₀ := (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one_iff f χ).1 hχ
  rw [← topologicalClosure_zpowers_neg_one]
  refine MonoidHom.range_eq_topologicalClosure_of_topologicalClosure_closure_eq_top
    presentedProP.topologicalClosure_closure_range_of_eq_top χ.continuous
    (MonoidHom.isClosed_range_of_continuous χ.continuous) ?_ (zpowers_le.mpr ⟨_, h₀⟩)
  rintro _ ⟨i, rfl⟩
  obtain rfl := Subsingleton.elim i 0
  rw [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, ← presentedProPGen_val,
    Fin.val_zero, h₀]
  exact le_topologicalClosure _ (mem_zpowers _)

end TwoOdd

section TwoEven

variable {a f n : ℕ}

/-- **The image of the canonical character of the `q = 2`, `n` even normal form when
`2^f ∣ α` is `{±1} × U^(f)`**, for `f ≥ 2` and `n ≥ 4` even: any character with the prescription
property takes `x₂` to `-(1 + α)⁻¹ ∈ -U^(f)` and `x₄` to `(1 - 2^f)⁻¹`. This includes `α = 0`. -/
theorem range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoEven (hf : 2 ≤ f)
    (hn : Even n) (hn₃ : 3 < n) (ha' : (2 : ℤ_[2]) ^ f ∣ (a : ℤ_[2]))
    {χ : presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = unitsPlusMinus f := by
  -- `2^f ∣ α` in `ℤ₂` with `f ≥ 1` makes `α` even.
  have ha : 2 ∣ a := by
    have h2 : ((2 : ℕ) : ℤ_[2]) ∣ ((a : ℤ) : ℤ_[2]) := by
      exact_mod_cast (dvd_pow_self (2 : ℤ_[2]) (by omega : f ≠ 0)).trans ha'
    exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (a : ℤ)).1
      ((PadicInt.norm_lt_one_iff_dvd _).2 h2)
  obtain ⟨h₁, h₃, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff a f n χ ha (by omega) hn
      hn₃).1 hχ
  have h := eq_orientationTwoEven_of_hasPrescriptionProperty a f n χ ha (by omega) hn hn₃ hχ
  have hr := range_orientationTwoEven_eq_unitsPlusMinus_of_dvd a f n _ _ hn₃ hf h₁ h₃ ha'
  rwa [← h] at hr

/-- **The image of the canonical character of the `q = 2`, `n` even normal form with `α = 2^g`
and level `f > g` is the twisted subgroup `U^[g]`**, the closed subgroup generated by `-1 + 2^g`,
for `g ≥ 2` and `n ≥ 4` even: any character with the prescription property takes `x₂` to
`-(1 + 2^g)⁻¹`, which generates `U^[g]`, and `x₄` to `(1 - 2^f)⁻¹ ∈ U^(f) ≤ U^(g+1) ≤ U^[g]`. The
level `f` is free above `g = v₂(α)`: every such level presents a group with the same invariants. -/
theorem range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_two_pow {g : ℕ} (hg : 2 ≤ g)
    (hgf : g < f) (hn : Even n) (hn₃ : 3 < n) {w : ℤ_[2]ˣ}
    (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g)
    {χ : presentedProP 2 (Fin n) {demushkinWordTwoEven (2 ^ g) f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = (zpowers w).topologicalClosure := by
  have ha : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
  obtain ⟨h₁, h₃, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff (2 ^ g) f n χ ha (by omega) hn
      hn₃).1 hχ
  have h := eq_orientationTwoEven_of_hasPrescriptionProperty (2 ^ g) f n χ ha (by omega) hn hn₃ hχ
  have hr := range_orientationTwoEven (2 ^ g) f n (χ (presentedProPGen 2 n _ 1))
    (χ (presentedProPGen 2 n _ 3)) hn₃
  rw [← h] at hr
  push_cast at h₁
  rw [hr, topologicalClosure_zpowers_sup_zpowers_eq_of_mem_unitsPrincipal_succ hg
    ((neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one h₁).mpr dvd_rfl)
    (fun h ↦ by
      have := (neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one h₁).mp h
      rw [pow_dvd_pow_iff (by norm_num : (2 : ℤ_[2]) ≠ 0) PadicInt.p_nonunit] at this
      omega)
    (unitsPrincipal_antitone 2 hgf
      ((mem_unitsPrincipal_iff_of_val_mul_one_sub_pow_eq_one (by exact_mod_cast h₃)).mpr le_rfl)),
    topologicalClosure_zpowers_eq_of_val_mul_one_add_two_pow_eq_neg_one hg h₁ hw]

end TwoEven

section TwoRankTwo

/-- **The image of the canonical character of the rank-two `q = 2` normal form with `α = 2^g` is
the twisted subgroup `U^[g]`**, the closed subgroup generated by `-1 + 2^g`, for `g ≥ 2`: any
character with the prescription property takes `x₂` to `-(1 + 2^g)⁻¹`. -/
theorem range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_two_pow {g : ℕ} (hg : 2 ≤ g)
    {w : ℤ_[2]ˣ} (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g)
    {χ : presentedProP 2 (Fin 2) {demushkinWordTwoRankTwo (2 ^ g) (freeProPGen 2 2)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = (zpowers w).topologicalClosure := by
  have ha : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
  obtain ⟨-, h₁⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff (2 ^ g) χ ha).1 hχ
  have h := eq_orientationTwoRankTwo_of_hasPrescriptionProperty (2 ^ g) χ ha hχ
  have hr := range_orientationTwoRankTwo (2 ^ g) (χ (presentedProPGen 2 2 _ 1))
  rw [← h] at hr
  push_cast at h₁
  rw [hr, topologicalClosure_zpowers_eq_of_val_mul_one_add_two_pow_eq_neg_one hg h₁ hw]

end TwoRankTwo

/-! ### The existence theorem

Each family of closed subgroups of `ℤ_pˣ` is realized by one normal form; the existence theorem
in even rank is the case analysis over the classification of the closed subgroups. -/

section Existence

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- **The trivial subgroup is realized in every even rank `n ≥ 2`**, by the relator
`(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` with `q = 0`, whose canonical character is trivial. -/
theorem exists_isDemushkin_range_eq_bot_of_even (hn : Even n) (hn0 : n ≠ 0) :
    ∃ r : freeProP p (Fin n), ∃ hG : IsDemushkin p (presentedProP p (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP p (Fin n) {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP p (Fin n) {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = ⊥ :=
  have hn₁ : 1 < n := by obtain ⟨k, hk⟩ := hn; omega
  ⟨demushkinWordNeTwo 0 n (freeProPGen p n),
    isDemushkin_presentedProP_demushkinWordNeTwo hn hn0 (dvd_zero p),
    demushkinRank_presentedProP_demushkinWordNeTwo (dvd_zero p) _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordNeTwo 0 n (dvd_zero p) hn hn₁,
    fun _ hχ ↦ range_eq_bot_of_hasPrescriptionProperty_demushkinWordNeTwo hn hn₁ rfl hχ⟩

/-- **The principal unit group `U^(f) = 1 + p^f ℤ_p` is realized in every even rank `n ≥ 2`**, for
`f ≥ 1`, and `f ≥ 2` when `p = 2`, by the relator `x₁^{p^f} (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_isDemushkin_range_eq_unitsPrincipal_of_even (hn : Even n) (hn0 : n ≠ 0) {f : ℕ}
    (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f) :
    ∃ r : freeProP p (Fin n), ∃ hG : IsDemushkin p (presentedProP p (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP p (Fin n) {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP p (Fin n) {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = unitsPrincipal p f :=
  have hn₁ : 1 < n := by obtain ⟨k, hk⟩ := hn; omega
  ⟨demushkinWordNeTwo (p ^ f) n (freeProPGen p n),
    isDemushkin_presentedProP_demushkinWordNeTwo hn hn0 (dvd_pow_self p hf.ne'),
    demushkinRank_presentedProP_demushkinWordNeTwo (dvd_pow_self p hf.ne') _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordNeTwo (p ^ f) n
      (dvd_pow_self p hf.ne') hn hn₁,
    fun _ hχ ↦ range_eq_unitsPrincipal_of_hasPrescriptionProperty_demushkinWordNeTwo hn hn₁ rfl hf
      hf₂ hχ⟩

/-- **The subgroup `{±1}` is realized in every even rank `n ≥ 2`**, by the relator
`x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` with `q = 2`: the even dyadic form with `α = 0` at level
`f = ∞`. -/
theorem exists_isDemushkin_range_eq_zpowers_neg_one_of_even (hn : Even n) (hn0 : n ≠ 0) :
    ∃ r : freeProP 2 (Fin n), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  have hn₁ : 1 < n := by obtain ⟨k, hk⟩ := hn; omega
  ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n),
    isDemushkin_presentedProP_demushkinWordNeTwo hn hn0 dvd_rfl,
    demushkinRank_presentedProP_demushkinWordNeTwo dvd_rfl _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordNeTwo 2 n dvd_rfl hn hn₁,
    fun _ hχ ↦ range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordNeTwo hn hn₁ hχ⟩

/-- **The subgroup `{±1} × U^(f)` is realized in every even rank `n ≥ 4`**, for `f ≥ 2`, by the
relator `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`: the even dyadic form with `α = 0`. -/
theorem exists_isDemushkin_range_eq_unitsPlusMinus_of_even (hn : Even n) (hn₄ : 4 ≤ n) {f : ℕ}
    (hf : 2 ≤ f) :
    ∃ r : freeProP 2 (Fin n), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = unitsPlusMinus f :=
  ⟨demushkinWordTwoEven 0 f n (freeProPGen 2 n),
    isDemushkin_presentedProP_demushkinWordTwoEven hn (by omega) (dvd_zero 2) (by omega),
    demushkinRank_presentedProP_demushkinWordTwoEven (dvd_zero 2) (by omega) _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoEven 0 f n (dvd_zero 2)
      (by omega) hn (by omega),
    fun _ hχ ↦ range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoEven hf hn
      (by omega) (by simp) hχ⟩

/-- **The twisted subgroup `U^[g]`, generated by `-1 + 2^g`, is realized in every even rank
`n ≥ 2`**, for `g ≥ 2`: by the relator `x₁^{2 + 2^g} (x₁, x₂)` in rank two, and by
`x₁^{2 + 2^g} (x₁, x₂) x₃^{2^{g+1}} (x₃, x₄) ⋯ (x_{n-1}, x_n)` in rank `n ≥ 4`; these are the even
dyadic forms with `α = 2^g` and `v₂(α) < f`. -/
theorem exists_isDemushkin_range_eq_topologicalClosure_zpowers_of_even (hn : Even n) (hn0 : n ≠ 0)
    {g : ℕ} (hg : 2 ≤ g) {w : ℤ_[2]ˣ} (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g) :
    ∃ r : freeProP 2 (Fin n), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = (zpowers w).topologicalClosure := by
  have ha : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
  rcases Nat.lt_or_ge n 4 with hn₄ | hn₄
  · obtain rfl : n = 2 := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact ⟨demushkinWordTwoRankTwo (2 ^ g) (freeProPGen 2 2),
      isDemushkin_presentedProP_demushkinWordTwoRankTwo ha,
      demushkinRank_presentedProP_demushkinWordTwoRankTwo ha _,
      existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo (2 ^ g) ha,
      fun _ hχ ↦ range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_two_pow hg hw hχ⟩
  · exact ⟨demushkinWordTwoEven (2 ^ g) (g + 1) n (freeProPGen 2 n),
      isDemushkin_presentedProP_demushkinWordTwoEven hn hn0 ha g.succ_pos,
      demushkinRank_presentedProP_demushkinWordTwoEven ha g.succ_pos _,
      existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoEven (2 ^ g) (g + 1) n ha
        g.succ_pos hn (by omega),
      fun _ hχ ↦ range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_two_pow hg g.lt_succ_self
        hn (by omega) hw hχ⟩

/-- **The existence theorem of the classification of Demushkin groups, even rank** (Labute,
Theorem 1 and Remark 2; Serre, Theorem 3.2). Let `n` be even and let `A ≤ ℤ_pˣ` be a closed pro-`p`
subgroup with `(A : A^p) < p ^ n` as supernatural numbers. Then there is a Demushkin group of rank
`n`, presented on `n` generators by a single relator `r`, which has exactly one continuous
character with the prescription property, and that character has image `A`.

The hypothesis `(A : A^p) < p ^ n` excludes `n = 0` and, at `p = 2`, the subgroups `{±1} × U^(f)`
in rank two, where `(A : A²) = 4`; every other closed pro-`p` subgroup is realized in every even
rank `n ≥ 2`. The pro-`p` hypothesis on `A` is used for odd `p`, where it places `A` inside the
principal units `1 + pℤ_p`; every closed subgroup of `ℤ_2ˣ` is pro-`2`. -/
theorem exists_isDemushkin_range_eq_of_even_of_lt {A : Subgroup ℤ_[p]ˣ}
    (hA : IsClosed (A : Set ℤ_[p]ˣ)) (hAp : IsProP p A) (hn : Even n)
    (hlt : profiniteIndex ((A.map (powMonoidHom p)).subgroupOf A) <
      Supernatural.primePower ⟨p, hp.out⟩ n) :
    ∃ r : freeProP p (Fin n), ∃ hG : IsDemushkin p (presentedProP p (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP p (Fin n) {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP p (Fin n) {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = A := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Supernatural.primePower (⟨p, hp.out⟩ : Nat.Primes) ((0 : ℕ) : ℕ∞) = ⊥ := by
      rw [Nat.cast_zero, Supernatural.primePower_zero (⟨p, hp.out⟩ : Nat.Primes),
        Supernatural.one_eq_bot]
    exact not_lt_bot (h1 ▸ hlt)
  by_cases hp2 : p = 2
  · subst hp2
    rcases eq_or_ne A ⊥ with rfl | hA'
    · exact exists_isDemushkin_range_eq_bot_of_even hn hn0
    rcases closedSubgroup_units_two_classification hA hA' with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | rfl |
      ⟨g, u, hg, hu, rfl⟩
    · exact exists_isDemushkin_range_eq_unitsPrincipal_of_even hn hn0 (by omega) fun _ ↦ hf
    · -- `(A : A²) = 4 < 2 ^ n` forces `n ≥ 4`.
      rw [profiniteIndex_subgroupOf_map_powMonoidHom_two_unitsPlusMinus hf] at hlt
      have h2n : (2 : ℕ∞) < n := (Supernatural.primePower_lt_primePower_iff _).1 hlt
      have hn₄ : 4 ≤ n := by
        obtain ⟨k, hk⟩ := hn
        have : 2 < n := by exact_mod_cast h2n
        omega
      exact exists_isDemushkin_range_eq_unitsPlusMinus_of_even hn hn₄ hf
    · exact exists_isDemushkin_range_eq_zpowers_neg_one_of_even hn hn0
    · exact exists_isDemushkin_range_eq_topologicalClosure_zpowers_of_even hn hn0 hg hu
  · -- Odd `p`: a closed pro-`p` subgroup of `ℤ_pˣ` is trivial or a principal unit group.
    rcases eq_or_ne A ⊥ with rfl | hA'
    · exact exists_isDemushkin_range_eq_bot_of_even hn hn0
    obtain ⟨f, hf, rfl⟩ := exists_eq_unitsPrincipal_of_isClosed one_pos (fun h ↦ absurd h hp2) hA
      hAp.le_unitsPrincipal_one hA'
    exact exists_isDemushkin_range_eq_unitsPrincipal_of_even hn hn0 hf fun h ↦ absurd h hp2

/-- **The existence theorem of the classification of Demushkin groups, odd rank `n ≥ 3`** (Labute,
Theorem 1; Serre, Theorem 3.2). For `n ≥ 3` odd and `2 ≤ f < ∞`, there is a Demushkin group of
rank `n`, presented on `n` generators by the single relator
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`, which has exactly one continuous character with the
prescription property, and that character has image `{±1} × U^(f)`. Here `p = 2`, the only prime
with Demushkin groups of odd rank. -/
theorem exists_isDemushkin_range_eq_unitsPlusMinus_of_odd (hn : Odd n) (hn₃ : 3 ≤ n) {f : ℕ}
    (hf : 2 ≤ f) :
    ∃ r : freeProP 2 (Fin n), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = unitsPlusMinus f :=
  ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
    isDemushkin_presentedProP_demushkinWordTwoOdd hn (by omega),
    demushkinRank_presentedProP_demushkinWordTwoOdd (by omega) _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd f n (by omega) hn
      (by omega),
    fun _ hχ ↦ range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoOdd hf hn
      (by omega) hχ⟩

/-- **The existence theorem of the classification of Demushkin groups, rank one** (Labute,
Remark 2 (iii); NSW (3.9.10)). There is a Demushkin group of rank `1`, presented on one generator by
the single relator `x₁²`, namely `ℤ/2`, which has exactly one continuous character with the
prescription property, and that character has image `{±1}`. -/
theorem exists_isDemushkin_one_range_eq_zpowers_neg_one :
    ∃ r : freeProP 2 (Fin 1), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin 1) {r}),
      demushkinRank hG = 1 ∧
      (∃! χ : presentedProP 2 (Fin 1) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin 1) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  ⟨demushkinWordTwoOdd 1 1 (freeProPGen 2 1), isDemushkin_presentedProP_demushkinWordTwoOdd odd_one
    one_pos, demushkinRank_presentedProP_demushkinWordTwoOdd one_pos _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one 1,
    fun _ hχ ↦ range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd_one hχ⟩

end Existence

end TauCeti
