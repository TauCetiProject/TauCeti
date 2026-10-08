/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries

/-!
# The classes of the Demushkin normal-form words in degree one

Let `H` be a profinite group, `p` a prime and `λ_k = λ_k(H)` its lower `p`-series, with graded
pieces `gr_k(H) = λ_k ⧸ λ_{k+1}`. The three normal-form relator words of the classification of
Demushkin groups,

* `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` for `p ∣ q`,
* `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)` for `f ≥ 2`,
* `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` for `4 ∣ a` and `f ≥ 2`,

together with the odd word at level `f = ∞`, `x₁² (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`,
read on any tuple `x : ℕ → H`, are products of `p`-th powers and Labute commutators
`(x, y) = x⁻¹y⁻¹xy`, so they lie in `λ_1(H)`, the pro-`p` Frattini subgroup; for this membership
alone the weaker hypotheses `f ≥ 1` and `2 ∣ a` suffice, and the classes are computed under
these weaker hypotheses. This file computes
their classes in `gr_1(H)`: the class of a Labute commutator is the bracket of the degree-zero
classes, the class of a `p`-th power `g ^ (p c)` is `c` times the `p`-power class `π ⟦g⟧`, and so
the class of a normal-form word is the sum of the brackets of its commutator pairs, plus
`(q / p) • π ξ₁` for the first word, `π ξ₁ + 2^{f-1} • π ξ₂` for the odd dyadic word,
`(1 + a/2) • π ξ₁ + 2^{f-1} • π ξ₃` for the even one and `π ξ₁` for the odd word at `f = ∞`, where
`ξ_i ∈ gr_0(H)` is the class of `x_i`. The factors `x₂^{2^f}` and `x₃^{2^f}` with `f ≥ 2`, and
`x₁^a` with `4 ∣ a`, are fourth powers and lie in `λ_2`, so under the normal-form hypotheses they
do not contribute; in particular the odd word at a finite level `f ≥ 2` and the odd word at
`f = ∞` have the same class.

These are the classes of the normal-form relators modulo `λ_2` (Labute, Proposition 4); the
theorem that a relator whose degree-one form is nondegenerate is carried into one of them by a
change of basis of the free pro-`p` group is proved in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm`.

## Main results

* `TauCeti.demushkinWordNeTwo_mem_pLowerCentralSeries_one`,
  `TauCeti.demushkinWordTwoOdd_mem_pLowerCentralSeries_one`,
  `TauCeti.demushkinWordTwoEven_mem_pLowerCentralSeries_one`,
  `TauCeti.demushkinWordTwoOddTop_mem_pLowerCentralSeries_one`: the words lie in `λ_1`.
* `TauCeti.gradedMk_labuteComm`: the class of `(x, y)` in `gr_1(H)` is the bracket `[ξ, η]` of the
  classes of `x` and `y`.
* `TauCeti.gradedMk_demushkinWordNeTwo`, `TauCeti.gradedMk_demushkinWordTwoOdd`,
  `TauCeti.gradedMk_demushkinWordTwoEven`, `TauCeti.gradedMk_demushkinWordTwoOddTop`: the classes
  of the four words in `gr_1(H)`;
  `TauCeti.gradedMk_demushkinWordTwoOdd_eq_gradedMk_demushkinWordTwoOddTop`: for `f ≥ 2` the odd
  word and the odd word at `f = ∞` have the same class.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Proposition 4.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

universe u

variable {p : ℕ} [Fact p.Prime] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]

/-! ### The words lie in `λ_1` -/

/-- For `p ∣ q`, the `q ≠ 2` normal-form word lies in `λ_1`. -/
theorem demushkinWordNeTwo_mem_pLowerCentralSeries_one {q : ℕ} (hq : p ∣ q) (n : ℕ) (x : ℕ → H) :
    demushkinWordNeTwo q n x ∈ pLowerCentralSeries p H 1 := by
  rw [pLowerCentralSeries_one_eq_proPFrattini Fact.out]
  exact demushkinWordNeTwo_mem_proPFrattini Fact.out hq n x

omit [Fact p.Prime] in
/-- For `f ≥ 1`, the `q = 2`, `n` odd normal-form word lies in `λ_1`. -/
theorem demushkinWordTwoOdd_mem_pLowerCentralSeries_one {f : ℕ} (hf : 0 < f) (n : ℕ) (x : ℕ → H) :
    demushkinWordTwoOdd f n x ∈ pLowerCentralSeries 2 H 1 := by
  rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
  exact demushkinWordTwoOdd_mem_proPFrattini hf n x

omit [Fact p.Prime] in
/-- The `q = 2`, `n` odd normal-form word at level `f = ∞` lies in `λ_1`. -/
theorem demushkinWordTwoOddTop_mem_pLowerCentralSeries_one (n : ℕ) (x : ℕ → H) :
    demushkinWordTwoOddTop n x ∈ pLowerCentralSeries 2 H 1 := by
  rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
  exact demushkinWordTwoOddTop_mem_proPFrattini n x

omit [Fact p.Prime] in
/-- For `a` even and `f ≥ 1`, the `q = 2`, `n` even normal-form word lies in `λ_1`. -/
theorem demushkinWordTwoEven_mem_pLowerCentralSeries_one {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f)
    (n : ℕ) (x : ℕ → H) : demushkinWordTwoEven a f n x ∈ pLowerCentralSeries 2 H 1 := by
  rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
  exact demushkinWordTwoEven_mem_proPFrattini ha hf n x

/-! ### The classes of commutators and of the words -/

omit [Fact p.Prime] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- **The class of a Labute commutator** `(x, y) = x⁻¹ y⁻¹ x y` in `gr_1(H)` is the bracket of the
classes of `x` and `y`: it is the group commutator `⁅x⁻¹, y⁻¹⁆`, and the bracket is bilinear. -/
theorem gradedMk_labuteComm (x y : H) (h : labuteComm x y ∈ pLowerCentralSeries p H 1) :
    gradedMk p H 1 ⟨labuteComm x y, h⟩ =
      gradedBracket p H 0 0 (gradedMkZero p H x) (gradedMkZero p H y) := by
  have h' : ⁅x⁻¹, y⁻¹⁆ ∈ pLowerCentralSeries p H 1 :=
    labuteComm_eq_commutatorElement_inv_inv x y ▸ h
  have : (⟨labuteComm x y, h⟩ : pLowerCentralSeries p H 1) = ⟨⁅x⁻¹, y⁻¹⁆, h'⟩ :=
    Subtype.ext (labuteComm_eq_commutatorElement_inv_inv x y)
  rw [this, ← gradedBracket_gradedMkZero, gradedMkZero_inv, gradedMkZero_inv, map_neg, map_neg,
    AddMonoidHom.neg_apply, neg_neg]

omit [Fact p.Prime] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H] in
private theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ((List.range N).map f).sum = ∑ a ∈ Finset.range N, f a := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The class in `gr_1(H)` of a product of Labute commutators is the sum of the brackets. -/
theorem gradedMk_list_prod_labuteComm (N : ℕ) (a b : ℕ → H)
    (h : ((List.range N).map fun i ↦ labuteComm (a i) (b i)).prod ∈ pLowerCentralSeries p H 1) :
    gradedMk p H 1 ⟨_, h⟩ =
      ∑ i ∈ Finset.range N,
        gradedBracket p H 0 0 (gradedMkZero p H (a i)) (gradedMkZero p H (b i)) := by
  have hmem (i : ℕ) : labuteComm (a i) (b i) ∈ pLowerCentralSeries p H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Fact.out]
    exact labuteComm_mem_proPFrattini Fact.out _ _
  have : (⟨_, h⟩ : pLowerCentralSeries p H 1) =
      ((List.range N).map fun i ↦ (⟨labuteComm (a i) (b i), hmem i⟩ :
        pLowerCentralSeries p H 1)).prod :=
    Subtype.ext (by rw [Subgroup.val_list_prod, List.map_map]; rfl)
  rw [this, gradedMk_list_prod, List.map_map, ← list_sum_map_range]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  exact gradedMk_labuteComm (a i) (b i) (hmem i)

/-- **The class of the `q ≠ 2` normal-form word** `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` in `gr_1`, for
`p ∣ q`: `(q / p) • π ξ₁ + [ξ₁, ξ₂] + ⋯ + [ξ_{n-1}, ξ_n]`. -/
theorem gradedMk_demushkinWordNeTwo {q : ℕ} (hq : p ∣ q) (n : ℕ) (x : ℕ → H) :
    gradedMk p H 1 ⟨demushkinWordNeTwo q n x,
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n x⟩ =
      (q / p) • gradedPow p H 0 (gradedMkZero p H (x 0)) +
        ∑ i ∈ Finset.range (n / 2),
          gradedBracket p H 0 0 (gradedMkZero p H (x (2 * i)))
            (gradedMkZero p H (x (2 * i + 1))) := by
  obtain ⟨c, rfl⟩ := hq
  rw [Nat.mul_div_cancel_left c (Fact.out : p.Prime).pos]
  have h1 : x 0 ^ (p * c) ∈ pLowerCentralSeries p H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Fact.out]
    exact pow_mem_proPFrattini_of_dvd (dvd_mul_right p c) _
  have h2 : ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i)) (x (2 * i + 1))).prod ∈
      pLowerCentralSeries p H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Fact.out]
    refine Subgroup.list_prod_mem _ ?_
    simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Fact.out _ _
  have : (⟨demushkinWordNeTwo (p * c) n x,
      demushkinWordNeTwo_mem_pLowerCentralSeries_one (dvd_mul_right p c) n x⟩ :
        pLowerCentralSeries p H 1) =
      ⟨x 0 ^ (p * c), h1⟩ * ⟨_, h2⟩ := Subtype.ext (demushkinWordNeTwo_def _ _ _)
  rw [this, gradedMk_mul, gradedMk_pow_mul, gradedMk_list_prod_labuteComm]

omit [Fact p.Prime] in
/-- **The class of the `q = 2`, `n` odd normal-form word** `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`
in `gr_1`, for `f ≥ 1`: `π ξ₁ + 2^{f-1} π ξ₂ + [ξ₂, ξ₃] + ⋯ + [ξ_{n-1}, ξ_n]`. The factor
`x₂^{2^f}` contributes `π ξ₂` when `f = 1` and nothing when `f ≥ 2`, being then a fourth power,
hence in `λ_2`. -/
theorem gradedMk_demushkinWordTwoOdd {f : ℕ} (hf : 0 < f) (n : ℕ) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoOdd f n x,
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n x⟩ =
      gradedPow 2 H 0 (gradedMkZero 2 H (x 0)) +
        2 ^ (f - 1) • gradedPow 2 H 0 (gradedMkZero 2 H (x 1)) +
        ∑ i ∈ Finset.range (n / 2),
          gradedBracket 2 H 0 0 (gradedMkZero 2 H (x (2 * i + 1)))
            (gradedMkZero 2 H (x (2 * i + 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ c, x 1 ^ (2 * c) ∈ pLowerCentralSeries 2 H 1 := fun c ↦ by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    exact pow_mem_proPFrattini_of_dvd (dvd_mul_right 2 c) _
  have h0 : x 0 ^ (2 * 1) ∈ pLowerCentralSeries 2 H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    exact pow_mem_proPFrattini_of_dvd (dvd_mul_right 2 1) _
  have h2 : ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i + 1)) (x (2 * i + 2))).prod ∈
      pLowerCentralSeries 2 H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    refine Subgroup.list_prod_mem _ ?_
    simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Nat.prime_two _ _
  have hf' : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have : (⟨demushkinWordTwoOdd f n x, demushkinWordTwoOdd_mem_pLowerCentralSeries_one hf n x⟩ :
        pLowerCentralSeries 2 H 1) =
      ⟨x 0 ^ (2 * 1), h0⟩ * ⟨x 1 ^ (2 * 2 ^ (f - 1)), hpow _⟩ * ⟨_, h2⟩ :=
    Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (demushkinWordTwoOdd_def f n x).trans (by rw [hf']))
  rw [this, gradedMk_mul, gradedMk_mul, gradedMk_pow_mul, gradedMk_pow_mul,
    gradedMk_list_prod_labuteComm, one_nsmul]

omit [Fact p.Prime] in
/-- **The class of the `q = 2`, `n` odd normal-form word at level `f = ∞`**
`x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` in `gr_1`: `π ξ₁ + [ξ₂, ξ₃] + ⋯ + [ξ_{n-1}, ξ_n]`. -/
theorem gradedMk_demushkinWordTwoOddTop (n : ℕ) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoOddTop n x,
        demushkinWordTwoOddTop_mem_pLowerCentralSeries_one n x⟩ =
      gradedPow 2 H 0 (gradedMkZero 2 H (x 0)) +
        ∑ i ∈ Finset.range (n / 2),
          gradedBracket 2 H 0 0 (gradedMkZero 2 H (x (2 * i + 1)))
            (gradedMkZero 2 H (x (2 * i + 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : x 0 ^ (2 * 1) ∈ pLowerCentralSeries 2 H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    exact pow_mem_proPFrattini_of_dvd (dvd_mul_right 2 1) _
  have h2 : ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i + 1)) (x (2 * i + 2))).prod ∈
      pLowerCentralSeries 2 H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    refine Subgroup.list_prod_mem _ ?_
    simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Nat.prime_two _ _
  have : (⟨demushkinWordTwoOddTop n x, demushkinWordTwoOddTop_mem_pLowerCentralSeries_one n x⟩ :
        pLowerCentralSeries 2 H 1) =
      ⟨x 0 ^ (2 * 1), h0⟩ * ⟨_, h2⟩ :=
    Subtype.ext (by
      rw [Subgroup.coe_mul]
      exact demushkinWordTwoOddTop_def n x)
  rw [this, gradedMk_mul, gradedMk_pow_mul, gradedMk_list_prod_labuteComm, one_nsmul]

omit [Fact p.Prime] in
/-- **For `f ≥ 2` the odd word and the odd word at `f = ∞` have the same class in `gr_1`**: the
factor `x₂^{2^f}` is a fourth power and lies in `λ_2`. This is the sense in which
`x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` is the normal form of `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`
modulo `λ_2`. -/
theorem gradedMk_demushkinWordTwoOdd_eq_gradedMk_demushkinWordTwoOddTop {f : ℕ} (hf : 2 ≤ f)
    (n : ℕ) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoOdd f n x,
        demushkinWordTwoOdd_mem_pLowerCentralSeries_one (zero_lt_two.trans_le hf) n x⟩ =
      gradedMk 2 H 1 ⟨demushkinWordTwoOddTop n x,
        demushkinWordTwoOddTop_mem_pLowerCentralSeries_one n x⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf' : 2 ^ (f - 1) = 2 ^ (f - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [gradedMk_demushkinWordTwoOdd (zero_lt_two.trans_le hf), gradedMk_demushkinWordTwoOddTop, hf',
    mul_nsmul, nsmul_gradedPiece_eq_zero]
  -- `rw [add_zero]` fails on the dependent index `gradedPiece 2 H (0 + 1)`.
  simp

omit [Fact p.Prime] in
/-- **The class of the `q = 2`, `n` even normal-form word**
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1`, for `a` even and `f ≥ 1`:
`(1 + a/2) π ξ₁ + [ξ₁, ξ₂] + 2^{f-1} π ξ₃ + [ξ₃, ξ₄] + ⋯ + [ξ_{n-1}, ξ_n]`. For `4 ∣ a` and `f ≥ 2`
the factors `x₁^a` and `x₃^{2^f}` are fourth powers, hence in `λ_2`, and the class is
`π ξ₁ + [ξ₁, ξ₂] + [ξ₃, ξ₄] + ⋯ + [ξ_{n-1}, ξ_n]`. -/
theorem gradedMk_demushkinWordTwoEven {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f) (n : ℕ) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoEven a f n x,
        demushkinWordTwoEven_mem_pLowerCentralSeries_one ha hf n x⟩ =
      (1 + a / 2) • gradedPow 2 H 0 (gradedMkZero 2 H (x 0)) +
        gradedBracket 2 H 0 0 (gradedMkZero 2 H (x 0)) (gradedMkZero 2 H (x 1)) +
        2 ^ (f - 1) • gradedPow 2 H 0 (gradedMkZero 2 H (x 2)) +
        ∑ i ∈ Finset.range (n / 2 - 1),
          gradedBracket 2 H 0 0 (gradedMkZero 2 H (x (2 * i + 2)))
            (gradedMkZero 2 H (x (2 * i + 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, rfl⟩ := ha
  have hpow : ∀ (g : H) (c : ℕ), g ^ (2 * c) ∈ pLowerCentralSeries 2 H 1 := fun g c ↦ by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    exact pow_mem_proPFrattini_of_dvd (dvd_mul_right 2 c) _
  have hc : labuteComm (x 0) (x 1) ∈ pLowerCentralSeries 2 H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    exact labuteComm_mem_proPFrattini Nat.prime_two _ _
  have h2 : ((List.range (n / 2 - 1)).map fun i ↦
      labuteComm (x (2 * i + 2)) (x (2 * i + 3))).prod ∈ pLowerCentralSeries 2 H 1 := by
    rw [pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two]
    refine Subgroup.list_prod_mem _ ?_
    simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Nat.prime_two _ _
  have hf' : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have : (⟨demushkinWordTwoEven (2 * b) f n x,
      demushkinWordTwoEven_mem_pLowerCentralSeries_one ⟨b, rfl⟩ hf n x⟩ :
        pLowerCentralSeries 2 H 1) =
      ⟨x 0 ^ (2 * (1 + b)), hpow _ _⟩ * ⟨labuteComm (x 0) (x 1), hc⟩ *
        ⟨x 2 ^ (2 * 2 ^ (f - 1)), hpow _ _⟩ * ⟨_, h2⟩ :=
    Subtype.ext (by
      have hb : 2 + 2 * b = 2 * (1 + b) := by ring
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact (demushkinWordTwoEven_def _ _ _ _).trans (by rw [hf', hb]))
  rw [this, gradedMk_mul, gradedMk_mul, gradedMk_mul, gradedMk_pow_mul, gradedMk_pow_mul,
    gradedMk_labuteComm, gradedMk_list_prod_labuteComm, Nat.mul_div_cancel_left b two_pos]

/-- **For `f ≥ 2` the even-rank dyadic word has the class of the `q ≠ 2` word with `q = 2 + a`**:
the factor `x₃^{2^f}` is a fourth power, hence lies in `λ_2`, so for `n ≥ 2` and `a` even the
classes in `gr_1` of `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` and of
`x₁^{2+a} (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` agree. -/
theorem gradedMk_demushkinWordTwoEven_eq_gradedMk_demushkinWordNeTwo {a f : ℕ} (ha : 2 ∣ a)
    (hf : 2 ≤ f) {n : ℕ} (hn : 2 ≤ n) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoEven a f n x,
        demushkinWordTwoEven_mem_pLowerCentralSeries_one ha (by omega) n x⟩ =
      gradedMk 2 H 1 ⟨demushkinWordNeTwo (2 + a) n x,
        demushkinWordNeTwo_mem_pLowerCentralSeries_one ((Nat.dvd_add_right dvd_rfl).2 ha) n x⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN⟩ : ∃ N, n / 2 = N + 1 := ⟨n / 2 - 1, by omega⟩
  -- The factor `x₃^{2^f}` contributes `2^{f-1} • π ξ₃ = 0`.
  have h2 : (2 ^ (f - 1)) • gradedPow 2 H 0 (gradedMkZero 2 H (x 2)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega),
      zero_smul]
  -- The first commutator of the `q ≠ 2` word is `(x₁, x₂)`, the others are those of the even word.
  have hsum : ∑ i ∈ Finset.range (n / 2), gradedBracket 2 H 0 0 (gradedMkZero 2 H (x (2 * i)))
      (gradedMkZero 2 H (x (2 * i + 1))) =
      gradedBracket 2 H 0 0 (gradedMkZero 2 H (x 0)) (gradedMkZero 2 H (x 1)) +
        ∑ i ∈ Finset.range (n / 2 - 1), gradedBracket 2 H 0 0 (gradedMkZero 2 H (x (2 * i + 2)))
          (gradedMkZero 2 H (x (2 * i + 3))) := by
    rw [hN, Nat.add_sub_cancel, Finset.sum_range_succ']
    exact (add_comm _ _).trans (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ ↦ by
      rw [Nat.mul_add_one, Nat.add_assoc (2 * i) 2 1]))
  rw [gradedMk_demushkinWordTwoEven ha (by omega),
    gradedMk_demushkinWordNeTwo ((Nat.dvd_add_right dvd_rfl).2 ha), hsum, h2,
    Nat.add_div_left a two_pos, add_comm (a / 2) 1]
  abel

end TauCeti
