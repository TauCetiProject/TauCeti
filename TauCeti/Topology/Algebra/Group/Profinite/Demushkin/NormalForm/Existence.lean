/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare
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

This file proves the realization half for every pair of the three situations: each such pair is
the pair of invariants of a Demushkin group, exhibited as a one-relator pro-`p` group
`⟨x₁, …, xₙ ∣ r⟩` on `n` generators, presented by one of the normal-form words of
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
| `{±1}`, `n` odd, `n ≥ 3`   | `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`, the level `f = ∞`      |
| `U^[g]`, `n = 2`           | `x₁^{2 + 2^g} (x₁, x₂)`                                |
| `U^[g]`, `n ≥ 4`           | `x₁^{2 + 2^g} (x₁, x₂) x₃^{2^{g+1}} (x₃, x₄) ⋯`         |
| `{±1}`, `n = 1`            | `x₁²`, the group `ℤ/2`                                |

The condition `p ^ n > (A : A^p)` of the even case is exactly what excludes `n = 0` and, at
`p = 2`, the non-procyclic family `{±1} × U^(f)` in rank two, where `(A : A²) = 4`. In the odd
case the endpoint `f = ∞` is the row `A = {±1} = {±1} × U^(∞)`, realized by the odd word at level
`f = ∞`, and the rank-one situation is its instance `n = 1`, where that word reads `x₁²`.

The converse half of the existence theorem, that no other pair occurs, is proved here for the
Demushkin groups with `q ≠ 2`, which are those whose canonical character lands in `1 + 4ℤ_2` when
`p = 2` (`TauCeti.demushkinQ_ne_two_iff_range_demushkinCharacter_le`). It needs no normal form:
the rank is even because the cup form is alternating
(`TauCeti.IsDemushkin.even_demushkinRank_of_demushkinQ_ne_two`), and the image is `1 + qℤ_p` or
trivial (`TauCeti.range_demushkinCharacter_eq_unitsPrincipal`), with `(A : A^p) ≤ p < p ^ n`. On
that locus the existence theorem is therefore an equivalence. For `q = 2` the converse is Labute's
Theorem 1 through the dyadic normal forms and is not proved here.

## Main results

* `TauCeti.range_eq_unitsPrincipal_of_hasPrescriptionProperty_demushkinWordNeTwo`,
  `TauCeti.range_eq_bot_of_hasPrescriptionProperty_demushkinWordNeTwo`,
  `TauCeti.range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordNeTwo`,
  `TauCeti.range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoOdd`,
  `TauCeti.range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd_one`,
  `TauCeti.range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOddTop`,
  `TauCeti.range_eq_unitsPlusMinus_of_hasPrescriptionProperty_demushkinWordTwoEven`,
  `TauCeti.range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_of_not_dvd`,
  `TauCeti.range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_of_not_dvd`: the image of
  the canonical character of each normal form, as the image of any character with the prescription
  property; the last two are the twisted subgroups `U^[g]` of the words whose exponent `α` has
  exact divisibility depth `g`, below the level `f` in the even-rank word on `n ≥ 4` generators
  and with no level condition in rank two.
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
* `TauCeti.exists_isDemushkin_range_eq_zpowers_neg_one_of_odd`: **the existence theorem in odd
  rank at level `f = ∞`**, for `A = {±1}` and every odd `n`.
* `TauCeti.exists_isDemushkin_one_range_eq_zpowers_neg_one`: **the existence theorem in rank
  one**, for `A = {±1}`, the instance `n = 1` of the previous statement.
* `TauCeti.IsDemushkin.profiniteIndex_subgroupOf_map_powMonoidHom_range_lt_of_demushkinQ_ne_two`:
  **the necessity half for `q ≠ 2`**: the image `A` of the canonical character of a Demushkin group
  of rank `n` with `q ≠ 2` has `(A : A^p) < p ^ n`.
* `TauCeti.exists_isDemushkin_range_demushkinCharacter_eq_iff`: **the existence theorem for
  `q ≠ 2` as an equivalence**: for `A ≤ ℤ_pˣ` closed and pro-`p`, contained in `1 + 4ℤ_2` when
  `p = 2`, the pair `(n, A)` is realized exactly when `n` is even and `(A : A^p) < p ^ n`.

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

section TwoOddTop

variable {n : ℕ}

/-- **The image of the canonical character of the `q = 2`, `n` odd normal form at level `f = ∞`
is `{±1}`**, for `n` odd: any character with the prescription property takes `x₁` to `-1` and every
other generator to `1`. -/
theorem range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOddTop (hn : Odd n)
    {χ : presentedProP 2 (Fin n) {demushkinWordTwoOddTop n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) := by
  rw [eq_orientationTwoOddTop_of_hasPrescriptionProperty n χ hn hχ]
  exact range_orientationTwoOddTop n hn.pos

end TwoOddTop

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

/-- **The image of the canonical character of the `q = 2`, `n` even normal form whose exponent
`α` has exact divisibility depth `g` below the level `f` is the twisted subgroup `U^[g]`**, the
closed subgroup generated by `-1 + 2^g`, for `g ≥ 2` and `n ≥ 4` even: any character with the
prescription property takes `x₂` to `-(1 + α)⁻¹`, which generates `U^[g]` because `-(1 + α)⁻¹` has
exact level `g`, and `x₄` to `(1 - 2^f)⁻¹ ∈ U^(f) ≤ U^(g+1) ≤ U^[g]`. Neither `α` within its
valuation nor the level `f` above `g = v₂(α)` is an invariant: every such pair presents a group
with the same invariants. -/
theorem range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_of_not_dvd {g : ℕ} (hg : 2 ≤ g)
    (hag : (2 : ℤ_[2]) ^ g ∣ (a : ℤ_[2])) (hag' : ¬ (2 : ℤ_[2]) ^ (g + 1) ∣ (a : ℤ_[2]))
    (hgf : g < f) (hn : Even n) (hn₃ : 3 < n) {w : ℤ_[2]ˣ}
    (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g)
    {χ : presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = (zpowers w).topologicalClosure := by
  have ha : 2 ∣ a := (dvd_pow_self 2 (by omega : g ≠ 0)).trans
    ((PadicInt.pow_p_dvd_natCast_iff g a).mp (by exact_mod_cast hag))
  obtain ⟨h₁, h₃, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff a f n χ ha (by omega) hn
      hn₃).1 hχ
  have h := eq_orientationTwoEven_of_hasPrescriptionProperty a f n χ ha (by omega) hn hn₃ hχ
  have hr := range_orientationTwoEven a f n (χ (presentedProPGen 2 n _ 1))
    (χ (presentedProPGen 2 n _ 3)) hn₃
  rw [← h] at hr
  -- `-χ(x₂)` has exact level `g` and `χ(x₄)` lies in `U^(g+1)`.
  have hv := (neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one h₁).mpr hag
  have hv' : -χ (presentedProPGen 2 n _ 1) ∉ unitsPrincipal 2 (g + 1) := fun h ↦
    hag' ((neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one h₁).mp h)
  have hu : χ (presentedProPGen 2 n _ 3) ∈ unitsPrincipal 2 (g + 1) :=
    unitsPrincipal_antitone 2 hgf
      ((mem_unitsPrincipal_iff_of_val_mul_one_sub_pow_eq_one (by exact_mod_cast h₃)).mpr le_rfl)
  rw [hr, topologicalClosure_zpowers_sup_zpowers_eq_of_mem_unitsPrincipal_succ hg hv hv' hu,
    topologicalClosure_zpowers_eq_of_val_mul_one_add_eq_neg_one hg hag hag' h₁ hw]

end TwoEven

section TwoRankTwo

/-- **The image of the canonical character of the rank-two `q = 2` normal form whose exponent `α`
has exact divisibility depth `g` is the twisted subgroup `U^[g]`**, the closed subgroup generated
by `-1 + 2^g`, for `g ≥ 2`: any character with the prescription property takes `x₂` to
`-(1 + α)⁻¹`, which generates `U^[g]` because `-(1 + α)⁻¹` has exact level `g`. -/
theorem range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_of_not_dvd {a g : ℕ}
    (hg : 2 ≤ g) (hag : (2 : ℤ_[2]) ^ g ∣ (a : ℤ_[2]))
    (hag' : ¬ (2 : ℤ_[2]) ^ (g + 1) ∣ (a : ℤ_[2])) {w : ℤ_[2]ˣ}
    (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g)
    {χ : presentedProP 2 (Fin 2) {demushkinWordTwoRankTwo a (freeProPGen 2 2)} →ₜ* ℤ_[2]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ.toMonoidHom.range = (zpowers w).topologicalClosure := by
  have ha : 2 ∣ a := (dvd_pow_self 2 (by omega : g ≠ 0)).trans
    ((PadicInt.pow_p_dvd_natCast_iff g a).mp (by exact_mod_cast hag))
  obtain ⟨-, h₁⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff a χ ha).1 hχ
  have h := eq_orientationTwoRankTwo_of_hasPrescriptionProperty a χ ha hχ
  have hr := range_orientationTwoRankTwo a (χ (presentedProPGen 2 2 _ 1))
  rw [← h] at hr
  rw [hr, topologicalClosure_zpowers_eq_of_val_mul_one_add_eq_neg_one hg hag hag' h₁ hw]

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
  -- `α = 2 ^ g` has exact divisibility depth `g`.
  have hag : (2 : ℤ_[2]) ^ g ∣ ((2 ^ g : ℕ) : ℤ_[2]) := by push_cast; exact dvd_rfl
  have hag' : ¬ (2 : ℤ_[2]) ^ (g + 1) ∣ ((2 ^ g : ℕ) : ℤ_[2]) := fun h ↦ by
    rw [Nat.cast_pow, Nat.cast_ofNat,
      pow_dvd_pow_iff (by norm_num : (2 : ℤ_[2]) ≠ 0) PadicInt.p_nonunit] at h
    omega
  rcases Nat.lt_or_ge n 4 with hn₄ | hn₄
  · obtain rfl : n = 2 := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact ⟨demushkinWordTwoRankTwo (2 ^ g) (freeProPGen 2 2),
      isDemushkin_presentedProP_demushkinWordTwoRankTwo ha,
      demushkinRank_presentedProP_demushkinWordTwoRankTwo ha _,
      existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo (2 ^ g) ha,
      fun _ hχ ↦ range_eq_of_hasPrescriptionProperty_demushkinWordTwoRankTwo_of_not_dvd hg hag hag'
        hw hχ⟩
  · exact ⟨demushkinWordTwoEven (2 ^ g) (g + 1) n (freeProPGen 2 n),
      isDemushkin_presentedProP_demushkinWordTwoEven hn hn0 ha g.succ_pos,
      demushkinRank_presentedProP_demushkinWordTwoEven ha g.succ_pos _,
      existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoEven (2 ^ g) (g + 1) n ha
        g.succ_pos hn (by omega),
      fun _ hχ ↦ range_eq_of_hasPrescriptionProperty_demushkinWordTwoEven_of_not_dvd hg hag hag'
        g.lt_succ_self hn (by omega) hw hχ⟩

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

/-- **The existence theorem of the classification of Demushkin groups, odd rank at level `f = ∞`**
(Labute, Theorem 1 and Remark 2; Serre, Theorem 3.2). For `n` odd, there is a Demushkin group of
rank `n`, presented on `n` generators by the single relator `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`, which
has exactly one continuous character with the prescription property, and that character has image
`{±1} = {±1} × U^(∞)`. Here `p = 2`, the only prime with Demushkin groups of odd rank. -/
theorem exists_isDemushkin_range_eq_zpowers_neg_one_of_odd (hn : Odd n) :
    ∃ r : freeProP 2 (Fin n), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}),
      demushkinRank hG = n ∧
      (∃! χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin n) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  ⟨demushkinWordTwoOddTop n (freeProPGen 2 n), isDemushkin_presentedProP_demushkinWordTwoOddTop hn,
    demushkinRank_presentedProP_demushkinWordTwoOddTop _,
    existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop n hn,
    fun _ hχ ↦ range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOddTop hn hχ⟩

/-- **The existence theorem of the classification of Demushkin groups, rank one** (Labute,
Remark 2 (iii); NSW (3.9.10)). There is a Demushkin group of rank `1`, presented on one generator by
the single relator `x₁²`, namely `ℤ/2`, which has exactly one continuous character with the
prescription property, and that character has image `{±1}`. This is the instance `n = 1` of the
odd-rank statement at level `f = ∞`, whose relator word reads `x₁²` at rank one. -/
theorem exists_isDemushkin_one_range_eq_zpowers_neg_one :
    ∃ r : freeProP 2 (Fin 1), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin 1) {r}),
      demushkinRank hG = 1 ∧
      (∃! χ : presentedProP 2 (Fin 1) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ) ∧
      ∀ χ : presentedProP 2 (Fin 1) {r} →ₜ* ℤ_[2]ˣ, HasPrescriptionProperty χ →
        χ.toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) :=
  exists_isDemushkin_range_eq_zpowers_neg_one_of_odd odd_one

end Existence

/-! ### The necessity half for `q ≠ 2` -/

section Necessity

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The necessity half of the existence theorem for `q ≠ 2`** (Labute, Theorem 1). For a
Demushkin group `G` of rank `n` with `q(G) ≠ 2`, the image `A` of its canonical character has
`(A : A^p) < p ^ n`. Indeed `A` is trivial, with `(A : A^p) = 1`, or the principal unit group
`1 + qℤ_p`, with `(A : A^p) = p`, while `n ≥ 2`. Together with the parity of the rank
(`TauCeti.IsDemushkin.even_demushkinRank_of_demushkinQ_ne_two`), this places `(n, A)` in the first
situation of the existence theorem. -/
theorem IsDemushkin.profiniteIndex_subgroupOf_map_powMonoidHom_range_lt_of_demushkinQ_ne_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (hG : IsDemushkin p G) (hq2 : demushkinQ hG ≠ 2) :
    profiniteIndex (((demushkinCharacter hG).toMonoidHom.range.map (powMonoidHom p)).subgroupOf
        (demushkinCharacter hG).toMonoidHom.range) <
      Supernatural.primePower ⟨p, hp.out⟩ (demushkinRank hG) := by
  -- The rank is even and positive, so `p ^ n > p ≥ (A : A^p)`.
  have hn : 1 < demushkinRank hG := by
    obtain ⟨k, hk⟩ := hG.even_demushkinRank_of_demushkinQ_ne_two hq2
    have := hG.demushkinRank_pos
    omega
  have hlt {m : ℕ∞} (hm : m ≤ 1) : Supernatural.primePower ⟨p, hp.out⟩ m <
      Supernatural.primePower ⟨p, hp.out⟩ (demushkinRank hG) :=
    (Supernatural.primePower_lt_primePower_iff _).2 (hm.trans_lt (by exact_mod_cast hn))
  rcases eq_or_ne (demushkinQ hG) 0 with h0 | h0
  · have hbot : (demushkinCharacter hG).toMonoidHom.range = ⊥ := by
      rw [ContinuousMonoidHom.coe_toMonoidHom]
      exact (range_demushkinCharacter_eq_bot_iff hG).2 h0
    rw [hbot, profiniteIndex_subgroupOf_map_powMonoidHom_eq_primePower (k := 0)
      (by simp) (by rw [relIndex_bot_right, pow_zero])]
    exact hlt (by norm_num)
  · obtain ⟨s, hs, hqs⟩ := hG.exists_demushkinQ_eq_pow h0
    have hs₂ : p = 2 → 2 ≤ s := fun hp2 ↦ by
      by_contra! hlt
      have hs1 : s = 1 := by omega
      exact hq2 (by rw [hqs, hp2, hs1, pow_one])
    rw [range_demushkinCharacter_eq_unitsPrincipal hG hqs hq2,
      profiniteIndex_subgroupOf_map_powMonoidHom_unitsPrincipal hs hs₂]
    exact hlt le_rfl

/-- **The existence theorem of the classification for `q ≠ 2`, as an equivalence** (Labute,
Theorem 1 and Remark 2; Demushkin and Serre). Let `A ≤ ℤ_pˣ` be a closed pro-`p` subgroup,
contained in `1 + 4ℤ_2` when `p = 2`; these are the possible images of the canonical characters of
the Demushkin groups with `q ≠ 2`
(`TauCeti.demushkinQ_ne_two_iff_range_demushkinCharacter_le`). Then `(n, A)` is the pair of
invariants of a Demushkin group, presented on `n` generators by one relator, exactly when `n` is
even and `(A : A^p) < p ^ n`. Together with
`TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_range_demushkinCharacter_eq`, this classifies
the Demushkin groups with `q ≠ 2` by their rank and the image of their canonical character. -/
theorem exists_isDemushkin_range_demushkinCharacter_eq_iff {n : ℕ} {A : Subgroup ℤ_[p]ˣ}
    (hA : IsClosed (A : Set ℤ_[p]ˣ)) (hAp : IsProP p A) (hA₂ : p = 2 → A ≤ unitsPrincipal p 2) :
    (∃ r : freeProP p (Fin n), ∃ hG : IsDemushkin p (presentedProP p (Fin n) {r}),
        demushkinRank hG = n ∧ (demushkinCharacter hG).toMonoidHom.range = A) ↔
      Even n ∧ profiniteIndex ((A.map (powMonoidHom p)).subgroupOf A) <
        Supernatural.primePower ⟨p, hp.out⟩ n := by
  refine ⟨?_, fun ⟨hn, hlt⟩ ↦ ?_⟩
  · rintro ⟨r, hG, hrank, rfl⟩
    have hq2 := (demushkinQ_ne_two_iff_range_demushkinCharacter_le hG).2 hA₂
    have hlt := hG.profiniteIndex_subgroupOf_map_powMonoidHom_range_lt_of_demushkinQ_ne_two hq2
    rw [hrank] at hlt
    exact ⟨hrank ▸ hG.even_demushkinRank_of_demushkinQ_ne_two hq2, hlt⟩
  · obtain ⟨r, hG, hrank, -, hrange⟩ := exists_isDemushkin_range_eq_of_even_of_lt hA hAp hn hlt
    exact ⟨r, hG, hrank, hrange _ (hasPrescriptionProperty_demushkinCharacter hG)⟩

end Necessity

end TauCeti
