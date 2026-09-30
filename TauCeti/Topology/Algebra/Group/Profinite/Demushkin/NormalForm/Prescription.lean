/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Orientation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Presentation
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The canonical characters of the Demushkin normal forms

Labute's classification attaches to a Demushkin group `G` its canonical character, the unique
continuous `χ : G → ℤ_pˣ` with the prescription property (`TauCeti.HasPrescriptionProperty`): every
reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` of the twisted coefficients is surjective. This file
computes that character on each of the normal-form presentations of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic`, proving Labute's Theorem 4
for the presented groups: **each normal form has exactly one continuous character with the
prescription property**, the standard orientation of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Orientation`, whose values on the
generators are

* `q ≠ 2`, relator `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`: `χ(x₂) = (1 - q)⁻¹`, all other
  `χ(x_i) = 1`;
* `q = 2`, `n` odd, relator `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`: `χ(x₁) = -1`,
  `χ(x₃) = (1 - 2^f)⁻¹`, all other `χ(x_i) = 1`; at level `f = ∞`, on the relator
  `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`, `χ(x₁) = -1` and all other `χ(x_i) = 1`;
* `q = 2`, `n` even, relator `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`:
  `χ(x₂) = -(1 + a)⁻¹`, `χ(x₄) = (1 - 2^f)⁻¹`, all other `χ(x_i) = 1`; in rank two, on the word
  `x₁^{2+a} (x₁, x₂)` with no level, `χ(x₁) = 1` and `χ(x₂) = -(1 + a)⁻¹`.

The values are stated as equations in `ℤ_p`, `χ(x₂) (1 - q) = 1` and so on, so that no inverse has
to be formed to state them.

The proof is the **forced computation on a derivation**. For a presented pro-`p` group the
prescription property of `χ` says that every continuous crossed homomorphism `F` of the free
group for `χ ∘ mk`, a continuous `F` with `F (x * y) = χ x * F y + F x`, kills the relator
(`TauCeti.presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero`). On a relator
word, `F` is computed from `F (x ^ k) = (1 + χ x + ⋯ + χ x ^ (k-1)) F x` and
`χ x * χ y * F (x, y) = (1 - χ y) F x + (χ x - 1) F y` on Labute's commutator `(x, y) = x⁻¹y⁻¹xy`:
its value is an `ℤ_p`-linear form in the values `F (x_i)`, with coefficients polynomial in the
`χ(x_i)`. Since `F` takes any prescribed values on the generators, the form must vanish
identically. Reading off its coefficients, one generator at a time, forces the values of `χ`
above: the commutator factor `(x_a, x_b)` containing `x_j` gives `χ(x_b) = 1` or `χ(x_a) = 1`, and
the generator carrying the `p`-th power gives the equation `q + χ(x₂)⁻¹ - 1 = 0`, respectively
`1 + χ(x₁) = 0` or `2 + a + χ(x₂)⁻¹ - 1 = 0`. Conversely, at the tabulated values the form
vanishes, so the standard orientation has the prescription property.

## Main results

* `TauCeti.IsCrossedHom.mul_mul_map_labuteComm`: the value of a crossed homomorphism on Labute's
  commutator; `TauCeti.IsCrossedHom.map_demushkinWordNeTwo`,
  `TauCeti.IsCrossedHom.map_demushkinWordTwoOdd`, `TauCeti.IsCrossedHom.map_demushkinWordTwoEven`,
  `TauCeti.IsCrossedHom.map_demushkinWordTwoRankTwo`,
  `TauCeti.IsCrossedHom.map_demushkinWordTwoOddTop`: its value on the five normal-form words;
  `TauCeti.IsCrossedHom.map_demushkinWordNeTwo_eq_zero`: at the tabulated character values the
  `q ≠ 2` word is killed, on any tuple.
* `TauCeti.hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff`,
  `TauCeti.hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_iff`,
  `TauCeti.hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff`,
  `TauCeti.hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff`,
  `TauCeti.hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_iff`: a continuous
  character of a normal-form presentation has the prescription property exactly when it takes the
  tabulated values; the `_of_apply_eq` versions are the existence halves, without the minimality
  and rank hypotheses.
* `TauCeti.hasPrescriptionProperty_orientationNeTwo`,
  `TauCeti.hasPrescriptionProperty_orientationTwoOdd`,
  `TauCeti.hasPrescriptionProperty_orientationTwoEven`,
  `TauCeti.hasPrescriptionProperty_orientationTwoRankTwo`,
  `TauCeti.hasPrescriptionProperty_orientationTwoOddTop`: the standard orientations have the
  prescription property; `TauCeti.eq_orientationNeTwo_of_hasPrescriptionProperty`,
  `TauCeti.eq_orientationTwoOdd_of_hasPrescriptionProperty`,
  `TauCeti.eq_orientationTwoEven_of_hasPrescriptionProperty`,
  `TauCeti.eq_orientationTwoRankTwo_of_hasPrescriptionProperty`,
  `TauCeti.eq_orientationTwoOddTop_of_hasPrescriptionProperty`: a character with the
  prescription property is the orientation with its own marked values.
* `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordNeTwo`,
  `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd`,
  `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoEven`,
  `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo`,
  `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop`: each
  normal form has exactly one continuous character with the prescription property; for the odd
  word at `f = ∞` this holds in every odd rank, including rank one.
* `TauCeti.hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one_iff` and
  `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one`: in rank
  one, where the odd word reads `x₁²` and the group is `ℤ/2`, the prescription property means
  `χ(x₁) = -1`, and the sign character is the unique character with it.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6 and Theorem 4, and Remark 2.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
-/

public section

namespace TauCeti

open Finset

/-! ### Crossed homomorphisms on Labute's commutator and on the normal-form words -/

section Words

variable {H : Type*} [Group H] {R : Type*} [CommRing R] {F' : Type*} [FunLike F' H Rˣ]
  [MonoidHomClass F' H Rˣ] {χ : F'} {F : H → R} (hF : IsCrossedHom χ F)
include hF

/-- The value of a crossed homomorphism on Labute's commutator `(x, y) = x⁻¹y⁻¹xy`, multiplied
through by `χ x * χ y`: it is read off `F (x * y) = F (y * x * (x, y))`. -/
theorem IsCrossedHom.mul_mul_map_labuteComm (x y : H) :
    (χ x : R) * χ y * F (labuteComm x y) = (1 - χ y) * F x + (χ x - 1) * F y := by
  have h : y * x * labuteComm x y = x * y := by
    rw [labuteComm_def]
    group
  have h1 := hF.map_mul (y * x) (labuteComm x y)
  rw [h, hF.map_mul x y, hF.map_mul y x, _root_.map_mul, Units.val_mul] at h1
  linear_combination -h1

/-- A crossed homomorphism vanishing at `x` and `y` vanishes at `(x, y)`. -/
theorem IsCrossedHom.map_labuteComm_eq_zero_of_eq_zero {x y : H} (hx : F x = 0) (hy : F y = 0) :
    F (labuteComm x y) = 0 := by
  have h := hF.mul_mul_map_labuteComm x y
  rw [hx, hy, mul_zero, mul_zero, add_zero, ← Units.val_mul] at h
  exact (Units.mul_right_eq_zero _).1 h

/-- A crossed homomorphism vanishes at `(x, y)` when the character is trivial at `x` and `y`. -/
theorem IsCrossedHom.map_labuteComm_eq_zero_of_eq_one {x y : H} (hx : χ x = 1) (hy : χ y = 1) :
    F (labuteComm x y) = 0 := by
  have h := hF.mul_mul_map_labuteComm x y
  rwa [hx, hy, Units.val_one, one_mul, one_mul, sub_self, zero_mul, zero_mul, add_zero] at h

/-- If a crossed homomorphism takes the value `1` at `x`, the value `0` at `y` and vanishes at
`(x, y)`, then the character is trivial at `y`. -/
theorem IsCrossedHom.eq_one_of_map_labuteComm_eq_zero_left {x y : H} (hx : F x = 1) (hy : F y = 0)
    (h : F (labuteComm x y) = 0) : χ y = 1 := by
  have h' := hF.mul_mul_map_labuteComm x y
  rw [h, hx, hy, mul_zero, mul_zero, mul_one, add_zero, eq_comm, sub_eq_zero, eq_comm] at h'
  exact Units.val_eq_one.1 h'

/-- If a crossed homomorphism takes the value `0` at `x`, the value `1` at `y` and vanishes at
`(x, y)`, then the character is trivial at `x`. -/
theorem IsCrossedHom.eq_one_of_map_labuteComm_eq_zero_right {x y : H} (hx : F x = 0) (hy : F y = 1)
    (h : F (labuteComm x y) = 0) : χ x = 1 := by
  have h' := hF.mul_mul_map_labuteComm x y
  rw [h, hx, hy, mul_zero, mul_zero, mul_one, zero_add, eq_comm, sub_eq_zero] at h'
  exact Units.val_eq_one.1 h'

/-- The value of a crossed homomorphism on a product of Labute commutators indexed by
`List.range m` is the sum of the values on the factors. -/
private theorem IsCrossedHom.map_list_range_prod_labuteComm (m : ℕ) (x y : ℕ → H) :
    F ((List.range m).map fun i ↦ labuteComm (x i) (y i)).prod =
      ∑ i ∈ range m, F (labuteComm (x i) (y i)) := by
  rw [hF.map_list_prod_of_forall_eq_one, List.map_map, Finset.sum_eq_multiset_sum,
    Finset.range_val, ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]
  · rfl
  · simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro i _
    rw [map_labuteComm, labuteComm_eq_one]

/-- The value of a crossed homomorphism on the `q ≠ 2` normal-form word
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem IsCrossedHom.map_demushkinWordNeTwo (q n : ℕ) (x : ℕ → H) :
    F (demushkinWordNeTwo q n x) =
      (χ (x 0) : R) ^ q * ∑ i ∈ range (n / 2), F (labuteComm (x (2 * i)) (x (2 * i + 1))) +
        (∑ j ∈ range q, (χ (x 0) : R) ^ j) * F (x 0) := by
  rw [demushkinWordNeTwo_def, hF.map_mul, hF.map_pow, _root_.map_pow, Units.val_pow_eq_pow_val,
    hF.map_list_range_prod_labuteComm]

/-- **A crossed homomorphism kills the `q ≠ 2` word at the tabulated character values.** For
`n ≥ 2` and a tuple `x` with `χ (x 1) * (1 - q) = 1` and `χ (x i) = 1` for `i ≠ 1` (the `0`-based
indices of the tuple: `χ(x₂) = (1 - q)⁻¹` and `χ(x_i) = 1` for `i ≠ 2`), the value of a crossed
homomorphism `F` on `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` is `(q + χ(x₂)⁻¹ - 1) F (x₁) = 0`. -/
theorem IsCrossedHom.map_demushkinWordNeTwo_eq_zero {q n : ℕ} (hn : 2 ≤ n) {x : ℕ → H}
    (h₁ : (χ (x 1) : R) * (1 - q) = 1) (h : ∀ i, i ≠ 1 → χ (x i) = 1) :
    F (demushkinWordNeTwo q n x) = 0 := by
  rw [hF.map_demushkinWordNeTwo, h 0 zero_ne_one, Units.val_one, one_pow, one_mul,
    Finset.sum_eq_single 0 (fun i _ hi ↦ hF.map_labuteComm_eq_zero_of_eq_one
      (h _ (by omega)) (h _ (by omega))) fun h0 ↦ absurd (mem_range.2 (by omega)) h0]
  -- The word evaluates to `F (x₁, x₂) + q F x₁`, and `χ(x₂) F (x₁, x₂) = (1 - χ(x₂)) F x₁`.
  have hc := hF.mul_mul_map_labuteComm (x 0) (x 1)
  rw [h 0 zero_ne_one, Units.val_one, one_mul, sub_self, zero_mul, add_zero] at hc
  simp only [Nat.mul_zero, Nat.zero_add, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  refine (Units.mul_right_eq_zero (χ (x 1))).1 ?_
  linear_combination hc - F (x 0) * h₁

/-- The value of a crossed homomorphism on the `q = 2`, `n` odd normal-form word
`x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`. -/
theorem IsCrossedHom.map_demushkinWordTwoOdd (f n : ℕ) (x : ℕ → H) :
    F (demushkinWordTwoOdd f n x) =
      (χ (x 0) : R) ^ 2 * (χ (x 1) : R) ^ 2 ^ f *
          ∑ i ∈ range (n / 2), F (labuteComm (x (2 * i + 1)) (x (2 * i + 2))) +
        (χ (x 0) : R) ^ 2 * ((∑ j ∈ range (2 ^ f), (χ (x 1) : R) ^ j) * F (x 1)) +
        ((χ (x 0) : R) + 1) * F (x 0) := by
  rw [demushkinWordTwoOdd_def]
  simp only [hF.map_mul, hF.map_pow, _root_.map_mul, _root_.map_pow, Units.val_mul,
    Units.val_pow_eq_pow_val, hF.map_list_range_prod_labuteComm, geom_sum_two]
  ring

/-- The value of a crossed homomorphism on the `q = 2`, `n` odd normal-form word at level
`f = ∞`, `x₁² (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`. -/
theorem IsCrossedHom.map_demushkinWordTwoOddTop (n : ℕ) (x : ℕ → H) :
    F (demushkinWordTwoOddTop n x) =
      (χ (x 0) : R) ^ 2 * ∑ i ∈ range (n / 2), F (labuteComm (x (2 * i + 1)) (x (2 * i + 2))) +
        ((χ (x 0) : R) + 1) * F (x 0) := by
  rw [demushkinWordTwoOddTop_def, hF.map_mul, hF.map_pow, _root_.map_pow,
    Units.val_pow_eq_pow_val, hF.map_list_range_prod_labuteComm, geom_sum_two]

/-- The value of a crossed homomorphism on the `q = 2`, `n` even normal-form word
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem IsCrossedHom.map_demushkinWordTwoEven (a f n : ℕ) (x : ℕ → H) :
    F (demushkinWordTwoEven a f n x) =
      (χ (x 0) : R) ^ (2 + a) * (χ (x 2) : R) ^ 2 ^ f *
          ∑ i ∈ range (n / 2 - 1), F (labuteComm (x (2 * i + 2)) (x (2 * i + 3))) +
        (χ (x 0) : R) ^ (2 + a) * ((∑ j ∈ range (2 ^ f), (χ (x 2) : R) ^ j) * F (x 2)) +
        (χ (x 0) : R) ^ (2 + a) * F (labuteComm (x 0) (x 1)) +
        (∑ j ∈ range (2 + a), (χ (x 0) : R) ^ j) * F (x 0) := by
  rw [demushkinWordTwoEven_def]
  simp only [hF.map_mul, hF.map_pow, _root_.map_mul, _root_.map_pow, Units.val_mul,
    Units.val_pow_eq_pow_val, hF.map_list_range_prod_labuteComm, map_labuteComm,
    labuteComm_eq_one, Units.val_one]
  ring

/-- The value of a crossed homomorphism on the rank-two `q = 2` normal-form word
`x₁^{2+a} (x₁, x₂)`. -/
theorem IsCrossedHom.map_demushkinWordTwoRankTwo (a : ℕ) (x : ℕ → H) :
    F (demushkinWordTwoRankTwo a x) =
      (χ (x 0) : R) ^ (2 + a) * F (labuteComm (x 0) (x 1)) +
        (∑ j ∈ range (2 + a), (χ (x 0) : R) ^ j) * F (x 0) := by
  rw [demushkinWordTwoRankTwo_def, hF.map_mul, hF.map_pow, _root_.map_pow,
    Units.val_pow_eq_pow_val]

end Words

/-! ### The `q ≠ 2` normal form -/

section NeTwo

variable {p : ℕ} [Fact p.Prime] (q n : ℕ)
  (χ : presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)} →ₜ* ℤ_[p]ˣ)

/-- **The tabulated values give the prescription property, `q ≠ 2`** (Labute, Theorem 4,
existence). A continuous character of the pro-`p` group presented by
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` with `χ(x₂) (1 - q) = 1` and `χ(x_i) = 1` for `i ≠ 2` has
the prescription property: on the relator, every crossed homomorphism for `χ ∘ mk` takes the value
`(q + χ(x₂)⁻¹ - 1) F(x₁) = 0`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_of_apply_eq
    (h₁ : (χ (presentedProPGen p n _ 1) : ℤ_[p]) * (1 - q) = 1)
    (h : ∀ i, i ≠ 1 → χ (presentedProPGen p n _ i) = 1) : HasPrescriptionProperty χ := by
  refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    fun F hFc hF r hr ↦ ?_
  rw [Set.mem_singleton_iff.mp hr]
  rcases le_or_gt 2 n with hn | hn
  · exact hF.map_demushkinWordNeTwo_eq_zero hn
      (by rw [presentedProP.comp_mk_freeProPGen]; exact h₁)
      fun i hi ↦ by rw [presentedProP.comp_mk_freeProPGen]; exact h i hi
  · -- For `n ≤ 1` the generator `x₂` is `1`, so `1 - q = 1` forces `q = 0` and the word is `1`.
    have hq : q = 0 := by
      rw [← presentedProP.comp_mk_freeProPGen, freeProPGen_eq_one_of_le p (by omega : n ≤ 1),
        map_one, Units.val_one, one_mul, sub_eq_self] at h₁
      exact_mod_cast h₁
    subst hq
    rw [demushkinWordNeTwo_def, pow_zero, one_mul, Nat.div_eq_of_lt hn, List.range_zero,
      List.map_nil, List.prod_nil, hF.map_one]

/-- **The prescription property forces the tabulated values, `q ≠ 2`** (Labute, Theorem 4, the
forced computation on a derivation). For `p ∣ q` and `n ≥ 2` even, a continuous character of the
pro-`p` group presented by `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` has the prescription property
exactly when `χ(x₂) (1 - q) = 1` and `χ(x_i) = 1` for every `i ≠ 2`. Evaluating the crossed
homomorphism with values `δ_{ij}` on the generators on the relator gives, for `j ≥ 3`, the vanishing
of `1 - χ(x_k)` for the partner `x_k` of `x_j` in the commutator part; for `j = 2` the vanishing of
`χ(x₁) - 1`; and for `j = 1` the equation `q + χ(x₂)⁻¹ - 1 = 0`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff (hq : p ∣ q) (hn : Even n)
    (hn₁ : 1 < n) :
    HasPrescriptionProperty χ ↔
      (χ (presentedProPGen p n _ 1) : ℤ_[p]) * (1 - q) = 1 ∧
        ∀ i, i ≠ 1 → χ (presentedProPGen p n _ i) = 1 := by
  refine ⟨fun hχ ↦ ?_, fun h ↦
    hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_of_apply_eq q n χ h.1 h.2⟩
  have hrels : ({demushkinWordNeTwo q n (freeProPGen p n)} : Set (freeProP p (Fin n))) ⊆
      proPFrattini p (freeProP p (Fin n)) :=
    Set.singleton_subset_iff.2 (demushkinWordNeTwo_mem_proPFrattini Fact.out hq n _)
  obtain ⟨k, hk⟩ := hn
  -- For the crossed homomorphism `F` with `F (x_i) = δ_{ij}`, only the commutator factor
  -- containing `x_j` contributes to the value on the relator.
  have hsum : ∀ j < n, ∀ F : freeProP p (Fin n) → ℤ_[p],
      IsCrossedHom (χ.comp (presentedProP.mk p _)) F →
      (∀ i, F (freeProPGen p n i) = if i = j then 1 else 0) →
      ∑ i ∈ range (n / 2), F (labuteComm (freeProPGen p n (2 * i)) (freeProPGen p n (2 * i + 1))) =
        F (labuteComm (freeProPGen p n (2 * (j / 2))) (freeProPGen p n (2 * (j / 2) + 1))) :=
    fun j hj F hF hFv ↦ Finset.sum_eq_single _
      (fun i _ hi ↦ hF.map_labuteComm_eq_zero_of_eq_zero
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)]))
      fun h0 ↦ absurd (mem_range.2 (by omega)) h0
  -- The value of `F` on the relator, for `F (x_i) = δ_{ij}` and `j ≠ 0`, is `χ(x₁)^q F (x_a, x_b)`
  -- for the commutator factor `(x_a, x_b)` containing `x_j`.
  have hval : ∀ j, 0 < j → j < n → ∀ F : freeProP p (Fin n) → ℤ_[p],
      IsCrossedHom (χ.comp (presentedProP.mk p _)) F →
      (∀ i, F (freeProPGen p n i) = if i = j then 1 else 0) →
      F (demushkinWordNeTwo q n (freeProPGen p n)) = 0 →
      F (labuteComm (freeProPGen p n (2 * (j / 2))) (freeProPGen p n (2 * (j / 2) + 1))) = 0 := by
    intro j hj₀ hj F hF hFv hFr
    rw [hF.map_demushkinWordNeTwo, hsum j hj F hF hFv, hFv 0, ite_eq_right (by omega), mul_zero,
      add_zero, ← Units.val_pow_eq_pow_val] at hFr
    exact (Units.mul_right_eq_zero _).1 hFr
  -- `j = 2`: `χ(x₁) = 1`.
  obtain ⟨F₁, hF₁, hF₁v, hF₁r⟩ := hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels hn₁
  have hx0 : χ (presentedProPGen p n _ 0) = 1 := by
    rw [← presentedProP.comp_mk_freeProPGen]
    exact hF₁.eq_one_of_map_labuteComm_eq_zero_right (by rw [hF₁v, ite_eq_right zero_ne_one])
      (by rw [hF₁v, ite_eq_left rfl]) (hval 1 one_pos hn₁ F₁ hF₁ hF₁v (hF₁r _ rfl))
  refine ⟨?_, fun i hi ↦ ?_⟩
  · -- `j = 1`: `q + χ(x₂)⁻¹ - 1 = 0`.
    obtain ⟨F₀, hF₀, hF₀v, hF₀r⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : 0 < n)
    have hr := hF₀r _ rfl
    rw [hF₀.map_demushkinWordNeTwo, hsum 0 (by omega) F₀ hF₀ hF₀v,
      presentedProP.comp_mk_freeProPGen, hx0, Units.val_one, one_pow, one_mul] at hr
    simp only [Nat.zero_div, Nat.mul_zero, Nat.zero_add, hF₀v, ite_eq_left, one_pow, sum_const,
      card_range, nsmul_eq_mul, mul_one] at hr
    have hc := hF₀.mul_mul_map_labuteComm (freeProPGen p n 0) (freeProPGen p n 1)
    rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx0, Units.val_one,
      one_mul, sub_self, zero_mul, add_zero, hF₀v, ite_eq_left rfl, mul_one] at hc
    linear_combination hc - (χ (presentedProPGen p n _ 1) : ℤ_[p]) * hr
  · by_cases hin : i < n
    · rcases Nat.lt_or_ge i 2 with h2 | h2
      · obtain rfl : i = 0 := by omega
        exact hx0
      -- `j ≥ 3`: the partner of `x_j` in its commutator factor has `χ = 1`.
      rw [← presentedProP.comp_mk_freeProPGen]
      rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
      · obtain ⟨F, hF, hFv, hFr⟩ :=
          hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i + 1 < n)
        have hc := hval (i + 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
        rw [(by omega : 2 * ((i + 1) / 2) = i)] at hc
        exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right (by omega)])
          (by rw [hFv, ite_eq_left rfl]) hc
      · obtain ⟨F, hF, hFv, hFr⟩ :=
          hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i - 1 < n)
        have hc := hval (i - 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
        rw [(by omega : 2 * ((i - 1) / 2) = i - 1), (by omega : i - 1 + 1 = i)] at hc
        exact hF.eq_one_of_map_labuteComm_eq_zero_left (by rw [hFv, ite_eq_left rfl])
          (by rw [hFv, ite_eq_right (by omega)]) hc
    · rw [presentedProPGen_eq_one_of_le p n _ (not_lt.1 hin), map_one]

/-- **The standard orientation of the `q ≠ 2` normal form has the prescription property**: for
`1 < n`, the character with `χ(x₂) = u`, `u (1 - q) = 1`, and `χ(x_i) = 1` otherwise. -/
theorem hasPrescriptionProperty_orientationNeTwo (hn₁ : 1 < n) (u : ℤ_[p]ˣ)
    (hu : u ∈ unitsPrincipal p 1) (hu' : (u : ℤ_[p]) * (1 - q) = 1) :
    HasPrescriptionProperty (orientationNeTwo q n u hu) :=
  hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_of_apply_eq q n _
    (by rw [orientationNeTwo_presentedProPGen_one q n u hu hn₁]; exact hu')
    fun _ hi ↦ orientationNeTwo_presentedProPGen_of_ne q n u hu hi

/-- **Uniqueness of the canonical character of the `q ≠ 2` normal form**: for `p ∣ q` and `n ≥ 2`
even, a character with the prescription property is the orientation with marked value its value
`χ(x₂)`. -/
theorem eq_orientationNeTwo_of_hasPrescriptionProperty (hq : p ∣ q) (hn : Even n) (hn₁ : 1 < n)
    (hχ : HasPrescriptionProperty χ) :
    χ = orientationNeTwo q n (χ (presentedProPGen p n _ 1))
      ((presentedProP.isProP p _ _).mem_unitsPrincipal_one χ _) := by
  obtain ⟨-, h⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff q n χ hq hn hn₁).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationNeTwo_of, ← presentedProPGen_val]
  split_ifs with hi
  · rw [hi]
  · exact h i hi

/-- **The `q ≠ 2` normal form has exactly one character with the prescription property** (Labute,
Theorem 4, for the normal form `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` with `p ∣ q` and `n ≥ 2`
even): the standard orientation, with `χ(x₂) = (1 - q)⁻¹` and `χ(x_i) = 1` otherwise. -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordNeTwo (hq : p ∣ q)
    (hn : Even n) (hn₁ : 1 < n) :
    ∃! χ : presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)} →ₜ* ℤ_[p]ˣ,
      HasPrescriptionProperty χ := by
  obtain ⟨m, rfl⟩ := hq
  have hunit : IsUnit (1 - ((p * m : ℕ) : ℤ_[p])) := by
    rw [sub_eq_add_neg]
    exact PadicInt.isUnit_one_add_of_dvd (dvd_neg.mpr (Nat.cast_dvd_cast (dvd_mul_right p m)))
  have hu' : ((hunit.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (1 - ((p * m : ℕ) : ℤ_[p])) = 1 :=
    hunit.val_inv_mul
  have hu : hunit.unit⁻¹ ∈ unitsPrincipal p 1 := by
    rw [mem_unitsPrincipal_iff, pow_one]
    refine ⟨(hunit.unit⁻¹ : ℤ_[p]ˣ) * m, ?_⟩
    push_cast at hu' ⊢
    linear_combination hu'
  refine ⟨orientationNeTwo _ n _ hu, hasPrescriptionProperty_orientationNeTwo _ n hn₁ _ hu hu',
    fun χ hχ ↦ ?_⟩
  obtain ⟨h₁, h⟩ := (hasPrescriptionProperty_presentedProP_demushkinWordNeTwo_iff _ n χ
    (dvd_mul_right p m) hn hn₁).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationNeTwo_of, ← presentedProPGen_val]
  split_ifs with hi
  · rw [hi]
    exact Units.val_inj.1 (by linear_combination ((hunit.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * h₁ -
      (χ (presentedProPGen p n _ 1) : ℤ_[p]) * hu')
  · exact h i hi

end NeTwo

/-! ### The `q = 2`, `n` odd normal form -/

section TwoOdd

variable (f n : ℕ)
  (χ : presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ)

/-- **The tabulated values give the prescription property, `q = 2` and `n` odd** (Labute,
Theorem 4, existence). A continuous character of the pro-`2` group presented by
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` with `χ(x₁) = -1`, `χ(x₃) (1 - 2^f) = 1` and `χ(x_i) = 1`
otherwise has the prescription property. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_of_apply_eq
    (h₀ : χ (presentedProPGen 2 n _ 0) = -1)
    (h₂ : (χ (presentedProPGen 2 n _ 2) : ℤ_[2]) * (1 - 2 ^ f) = 1)
    (h : ∀ i, i ≠ 0 → i ≠ 2 → χ (presentedProPGen 2 n _ i) = 1) : HasPrescriptionProperty χ := by
  refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    fun F hFc hF r hr ↦ ?_
  have h1 := h 1 one_ne_zero (by omega)
  rw [Set.mem_singleton_iff.mp hr, hF.map_demushkinWordTwoOdd, presentedProP.comp_mk_freeProPGen,
    presentedProP.comp_mk_freeProPGen, h₀, h1, Units.val_neg, Units.val_one,
    Finset.sum_eq_single 0 (fun i _ hi ↦
      hF.map_labuteComm_eq_zero_of_eq_one
        (by rw [presentedProP.comp_mk_freeProPGen]; exact h _ (by omega) (by omega))
        (by rw [presentedProP.comp_mk_freeProPGen]; exact h _ (by omega) (by omega))) fun h0' ↦ ?_]
  · -- The relator evaluates to `F (x₂, x₃) + 2^f F x₂`, and `χ(x₃) F (x₂, x₃) = (1 - χ(x₃)) F x₂`.
    have hc := hF.mul_mul_map_labuteComm (freeProPGen 2 n 1) (freeProPGen 2 n 2)
    rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, h1, Units.val_one,
      one_mul, sub_self, zero_mul, add_zero] at hc
    simp only [Nat.mul_zero, Nat.zero_add, neg_one_sq, one_pow, one_mul, mul_one, neg_add_cancel,
      zero_mul, add_zero, sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    refine (Units.mul_right_eq_zero (χ (presentedProPGen 2 n _ 2))).1 ?_
    linear_combination hc - F (freeProPGen 2 n 1) * h₂
  · -- For `n ≤ 1` the generator `x₂` is `1`, and `(1, x₃) = 1`.
    rw [mem_range, not_lt, Nat.le_zero] at h0'
    rw [freeProPGen_eq_one_of_le 2 (by omega : n ≤ 2 * 0 + 1)]
    simp [labuteComm_def, hF.map_one]

/-- **The prescription property forces `χ(x₁) = -1` on the `q = 2`, `n` odd normal form**, for
`n ≥ 1`, whenever the relator `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` lies in the Frattini
subgroup, as it does for `f ≥ 1` (`TauCeti.demushkinWordTwoOdd_mem_proPFrattini`) and at rank one
for every `f`, where it reads `x₁²`: the crossed homomorphism with `F(x₁) = 1` and `F(x_i) = 0`
otherwise takes the value `χ(x₁) + 1` on the relator. This is the one clause of the forced
computation that survives at rank one. -/
theorem apply_presentedProPGen_zero_eq_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd
    (hr : demushkinWordTwoOdd f n (freeProPGen 2 n) ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hn : 0 < n) (hχ : HasPrescriptionProperty χ) : χ (presentedProPGen 2 n _ 0) = -1 := by
  have hrels : ({demushkinWordTwoOdd f n (freeProPGen 2 n)} : Set (freeProP 2 (Fin n))) ⊆
      proPFrattini 2 (freeProP 2 (Fin n)) :=
    Set.singleton_subset_iff.2 hr
  obtain ⟨F, hF, hFv, hFr⟩ := hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels hn
  have hr := hFr _ rfl
  rw [hF.map_demushkinWordTwoOdd, Finset.sum_eq_zero fun i _ ↦
    hF.map_labuteComm_eq_zero_of_eq_zero (by rw [hFv, ite_eq_right (by omega)])
      (by rw [hFv, ite_eq_right (by omega)])] at hr
  simp only [hFv 0, hFv 1, ite_eq_left, ite_eq_right one_ne_zero, mul_zero, add_zero, zero_add,
    mul_one] at hr
  rw [← presentedProP.comp_mk_freeProPGen]
  exact Units.val_inj.1 (by rw [Units.val_neg, Units.val_one]; linear_combination hr)

/-- **The prescription property forces the tabulated values, `q = 2` and `n` odd** (Labute,
Theorem 4, the forced computation on a derivation). For `f ≥ 1` and `n ≥ 3` odd, a continuous
character of the pro-`2` group presented by `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` has the
prescription property exactly when `χ(x₁) = -1`, `χ(x₃) (1 - 2^f) = 1` and `χ(x_i) = 1` for every
other `i`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_iff (hf : 0 < f) (hn : Odd n)
    (hn₂ : 2 < n) :
    HasPrescriptionProperty χ ↔
      χ (presentedProPGen 2 n _ 0) = -1 ∧
        (χ (presentedProPGen 2 n _ 2) : ℤ_[2]) * (1 - 2 ^ f) = 1 ∧
        ∀ i, i ≠ 0 → i ≠ 2 → χ (presentedProPGen 2 n _ i) = 1 := by
  refine ⟨fun hχ ↦ ?_, fun h ↦
    hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_of_apply_eq f n χ h.1 h.2.1 h.2.2⟩
  have hrels : ({demushkinWordTwoOdd f n (freeProPGen 2 n)} : Set (freeProP 2 (Fin n))) ⊆
      proPFrattini 2 (freeProP 2 (Fin n)) :=
    Set.singleton_subset_iff.2 (demushkinWordTwoOdd_mem_proPFrattini hf n _)
  obtain ⟨k, hk⟩ := hn
  -- For the crossed homomorphism `F` with `F (x_i) = δ_{ij}`, `j ≥ 1`, only the commutator factor
  -- containing `x_j` contributes to the value on the relator.
  have hsum : ∀ j, 0 < j → j < n → ∀ F : freeProP 2 (Fin n) → ℤ_[2],
      IsCrossedHom (χ.comp (presentedProP.mk 2 _)) F →
      (∀ i, F (freeProPGen 2 n i) = if i = j then 1 else 0) →
      ∑ i ∈ range (n / 2),
          F (labuteComm (freeProPGen 2 n (2 * i + 1)) (freeProPGen 2 n (2 * i + 2))) =
        F (labuteComm (freeProPGen 2 n (2 * ((j - 1) / 2) + 1))
          (freeProPGen 2 n (2 * ((j - 1) / 2) + 2))) :=
    fun j hj₀ hj F hF hFv ↦ Finset.sum_eq_single _
      (fun i _ hi ↦ hF.map_labuteComm_eq_zero_of_eq_zero
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)]))
      fun h0 ↦ absurd (mem_range.2 (by omega)) h0
  -- For `j ≥ 3` that factor `(x_a, x_b)` has `F (x_a, x_b) = 0`.
  have hval : ∀ j, 2 ≤ j → j < n → ∀ F : freeProP 2 (Fin n) → ℤ_[2],
      IsCrossedHom (χ.comp (presentedProP.mk 2 _)) F →
      (∀ i, F (freeProPGen 2 n i) = if i = j then 1 else 0) →
      F (demushkinWordTwoOdd f n (freeProPGen 2 n)) = 0 →
      F (labuteComm (freeProPGen 2 n (2 * ((j - 1) / 2) + 1))
        (freeProPGen 2 n (2 * ((j - 1) / 2) + 2))) = 0 := by
    intro j hj₂ hj F hF hFv hFr
    rw [hF.map_demushkinWordTwoOdd, hsum j (by omega) hj F hF hFv] at hFr
    simp only [hFv 0, hFv 1, ite_eq_right (show (0 : ℕ) ≠ j by omega),
      ite_eq_right (show (1 : ℕ) ≠ j by omega), mul_zero, add_zero, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul] at hFr
    exact (Units.mul_right_eq_zero _).1 hFr
  -- `j = 1`: `χ(x₁) = -1`.
  have hx0 := apply_presentedProPGen_zero_eq_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd
    f n χ (demushkinWordTwoOdd_mem_proPFrattini hf n _) (by omega) hχ
  -- `j = 3`: `χ(x₂) = 1`.
  have hx1 : χ (presentedProPGen 2 n _ 1) = 1 := by
    obtain ⟨F, hF, hFv, hFr⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels hn₂
    have hc := hval 2 le_rfl hn₂ F hF hFv (hFr _ rfl)
    rw [(by omega : 2 * ((2 - 1) / 2) + 1 = 1), (by omega : 2 * ((2 - 1) / 2) + 2 = 2)] at hc
    rw [← presentedProP.comp_mk_freeProPGen]
    exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right (by omega)])
      (by rw [hFv, ite_eq_left rfl]) hc
  refine ⟨hx0, ?_, fun i hi₀ hi₂ ↦ ?_⟩
  · -- `j = 2`: `2^f + χ(x₃)⁻¹ - 1 = 0`.
    obtain ⟨F, hF, hFv, hFr⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : 1 < n)
    have hr := hFr _ rfl
    rw [hF.map_demushkinWordTwoOdd, hsum 1 one_pos (by omega) F hF hFv,
      presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx0, hx1] at hr
    simp only [Nat.sub_self, Nat.zero_div, Nat.zero_add, hFv 0, hFv 1, ite_eq_left,
      ite_eq_right zero_ne_one, Units.val_neg, Units.val_one, neg_one_sq, one_pow, one_mul,
      mul_one, mul_zero, add_zero, sum_const, card_range, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat] at hr
    have hc := hF.mul_mul_map_labuteComm (freeProPGen 2 n 1) (freeProPGen 2 n 2)
    rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx1, Units.val_one,
      one_mul, sub_self, zero_mul, add_zero, hFv 1, ite_eq_left rfl, mul_one] at hc
    linear_combination hc - (χ (presentedProPGen 2 n _ 2) : ℤ_[2]) * hr
  · by_cases hin : i < n
    · rcases Nat.lt_or_ge i 3 with h3 | h3
      · obtain rfl : i = 1 := by omega
        exact hx1
      -- `j ≥ 4`: the partner of `x_j` in its commutator factor has `χ = 1`.
      rw [← presentedProP.comp_mk_freeProPGen]
      rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
      · obtain ⟨F, hF, hFv, hFr⟩ :=
          hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i - 1 < n)
        have hc := hval (i - 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
        rw [(by omega : 2 * ((i - 1 - 1) / 2) + 1 = i - 1),
          (by omega : 2 * ((i - 1 - 1) / 2) + 2 = i)] at hc
        exact hF.eq_one_of_map_labuteComm_eq_zero_left (by rw [hFv, ite_eq_left rfl])
          (by rw [hFv, ite_eq_right (by omega)]) hc
      · obtain ⟨F, hF, hFv, hFr⟩ :=
          hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i + 1 < n)
        have hc := hval (i + 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
        rw [(by omega : 2 * ((i + 1 - 1) / 2) + 1 = i),
          (by omega : 2 * ((i + 1 - 1) / 2) + 2 = i + 1)] at hc
        exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right (by omega)])
          (by rw [hFv, ite_eq_left rfl]) hc
    · rw [presentedProPGen_eq_one_of_le 2 n _ (not_lt.1 hin), map_one]

/-- **The standard orientation of the `q = 2`, `n` odd normal form has the prescription
property**: for `2 < n`, the character with `χ(x₁) = -1`, `χ(x₃) = u`, `u (1 - 2^f) = 1`, and
`χ(x_i) = 1` otherwise. -/
theorem hasPrescriptionProperty_orientationTwoOdd (hn₂ : 2 < n) (u : ℤ_[2]ˣ)
    (hu : (u : ℤ_[2]) * (1 - 2 ^ f) = 1) : HasPrescriptionProperty (orientationTwoOdd f n u) :=
  hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_of_apply_eq f n _
    (orientationTwoOdd_presentedProPGen_zero f n u (by omega))
    (by rw [orientationTwoOdd_presentedProPGen_two f n u hn₂]; exact hu)
    fun _ hi₀ hi₂ ↦ orientationTwoOdd_presentedProPGen_of_ne f n u hi₀ hi₂

/-- **Uniqueness of the canonical character of the `q = 2`, `n` odd normal form**: for `f ≥ 1` and
`n ≥ 3` odd, a character with the prescription property is the orientation with marked value its
value `χ(x₃)`. -/
theorem eq_orientationTwoOdd_of_hasPrescriptionProperty (hf : 0 < f) (hn : Odd n) (hn₂ : 2 < n)
    (hχ : HasPrescriptionProperty χ) :
    χ = orientationTwoOdd f n (χ (presentedProPGen 2 n _ 2)) := by
  obtain ⟨h₀, -, h⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_iff f n χ hf hn hn₂).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoOdd_of, ← presentedProPGen_val]
  split_ifs with hi₀ hi₂
  · rw [hi₀]
    exact h₀
  · rw [hi₂]
  · exact h i hi₀ hi₂

/-- **The `q = 2`, `n` odd normal form has exactly one character with the prescription property**
(Labute, Theorem 4, for the normal form `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` with `f ≥ 1` and
`n ≥ 3` odd): the standard orientation, with `χ(x₁) = -1`, `χ(x₃) = (1 - 2^f)⁻¹` and `χ(x_i) = 1`
otherwise. -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd (hf : 0 < f)
    (hn : Odd n) (hn₂ : 2 < n) :
    ∃! χ : presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ,
      HasPrescriptionProperty χ := by
  obtain ⟨u, hu⟩ := exists_val_mul_one_sub_pow_eq_one 2 hf
  have hu' : (u : ℤ_[2]) * (1 - 2 ^ f) = 1 := by exact_mod_cast hu
  refine ⟨orientationTwoOdd f n u, hasPrescriptionProperty_orientationTwoOdd f n hn₂ u hu',
    fun χ hχ ↦ ?_⟩
  obtain ⟨h₀, h₂, h⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_iff f n χ hf hn hn₂).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoOdd_of, ← presentedProPGen_val]
  split_ifs with hi₀ hi₂
  · rw [hi₀]
    exact h₀
  · rw [hi₂]
    exact Units.val_inj.1 (by linear_combination (u : ℤ_[2]) * h₂ -
      (χ (presentedProPGen 2 n _ 2) : ℤ_[2]) * hu')
  · exact h i hi₀ hi₂

/-- **The prescription property in rank one** (Labute, Remark 2 (iii)). On one generator the
`q = 2`, `n` odd word `x₁² x₂^{2^f}` reads `x₁²` for every level `f`, the presented group is
`ℤ/2`, and a continuous character has the prescription property exactly when `χ(x₁) = -1`: on the
relator `x₁²` every crossed homomorphism takes the value `(χ(x₁) + 1) F(x₁)`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one_iff
    (χ : presentedProP 2 (Fin 1) {demushkinWordTwoOdd f 1 (freeProPGen 2 1)} →ₜ* ℤ_[2]ˣ) :
    HasPrescriptionProperty χ ↔ χ (presentedProPGen 2 1 _ 0) = -1 := by
  have hmem : demushkinWordTwoOdd f 1 (freeProPGen 2 1) ∈ proPFrattini 2 (freeProP 2 (Fin 1)) := by
    rw [demushkinWordTwoOdd_one f _ (freeProPGen_eq_one_of_le 2 le_rfl)]
    exact pow_mem_proPFrattini _
  refine ⟨apply_presentedProPGen_zero_eq_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOdd
    f 1 χ hmem one_pos, fun h₀ ↦ ?_⟩
  refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    fun F hFc hF r hr ↦ ?_
  rw [Set.mem_singleton_iff.mp hr, hF.map_demushkinWordTwoOdd, presentedProP.comp_mk_freeProPGen,
    h₀, freeProPGen_eq_one_of_le 2 le_rfl, hF.map_one, map_one]
  simp

/-- **`ℤ/2`, presented on one generator by `x₁²`, has exactly one character with the prescription
property**, the sign character `χ(x₁) = -1`, for every level `f`. -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one :
    ∃! χ : presentedProP 2 (Fin 1) {demushkinWordTwoOdd f 1 (freeProPGen 2 1)} →ₜ* ℤ_[2]ˣ,
      HasPrescriptionProperty χ := by
  refine ⟨orientationTwoOdd f 1 1,
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one_iff f _).2
      (orientationTwoOdd_presentedProPGen_zero f 1 1 one_pos), fun χ hχ ↦ ?_⟩
  refine presentedProP.hom_ext_of fun i ↦ ?_
  obtain rfl := Subsingleton.elim i 0
  rw [← presentedProPGen_val, Fin.val_zero,
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_one_iff f χ).1 hχ,
    orientationTwoOdd_presentedProPGen_zero f 1 1 one_pos]

end TwoOdd

/-! ### The `q = 2`, `n` odd normal form at level `f = ∞` -/

section TwoOddTop

variable (n : ℕ)
  (χ : presentedProP 2 (Fin n) {demushkinWordTwoOddTop n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ)

/-- **The tabulated values give the prescription property, `q = 2` and `n` odd, at level
`f = ∞`** (Labute, Theorem 4, existence). A continuous character of the pro-`2` group presented by
`x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` with `χ(x₁) = -1` and `χ(x_i) = 1` otherwise has the prescription
property: on the relator, every crossed homomorphism for `χ ∘ mk` takes the value
`(χ(x₁) + 1) F(x₁) = 0`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_of_apply_eq
    (h₀ : χ (presentedProPGen 2 n _ 0) = -1)
    (h : ∀ i, i ≠ 0 → χ (presentedProPGen 2 n _ i) = 1) : HasPrescriptionProperty χ := by
  refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    fun F hFc hF r hr ↦ ?_
  rw [Set.mem_singleton_iff.mp hr, hF.map_demushkinWordTwoOddTop,
    presentedProP.comp_mk_freeProPGen, h₀, Finset.sum_eq_zero fun i _ ↦
      hF.map_labuteComm_eq_zero_of_eq_one
        (by rw [presentedProP.comp_mk_freeProPGen]; exact h _ (by omega))
        (by rw [presentedProP.comp_mk_freeProPGen]; exact h _ (by omega))]
  simp

/-- **The prescription property forces `χ(x₁) = -1` on the `q = 2`, `n` odd normal form at level
`f = ∞`**, for `n ≥ 1`: the crossed homomorphism with `F(x₁) = 1` and `F(x_i) = 0` otherwise
takes the value `χ(x₁) + 1` on the relator `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem apply_presentedProPGen_zero_eq_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOddTop
    (hn : 0 < n) (hχ : HasPrescriptionProperty χ) : χ (presentedProPGen 2 n _ 0) = -1 := by
  have hrels : ({demushkinWordTwoOddTop n (freeProPGen 2 n)} : Set (freeProP 2 (Fin n))) ⊆
      proPFrattini 2 (freeProP 2 (Fin n)) :=
    Set.singleton_subset_iff.2 (demushkinWordTwoOddTop_mem_proPFrattini n _)
  obtain ⟨F, hF, hFv, hFr⟩ := hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels hn
  have hr := hFr _ rfl
  rw [hF.map_demushkinWordTwoOddTop, Finset.sum_eq_zero fun i _ ↦
    hF.map_labuteComm_eq_zero_of_eq_zero (by rw [hFv, ite_eq_right (by omega)])
      (by rw [hFv, ite_eq_right (by omega)])] at hr
  simp only [hFv 0, ite_eq_left, mul_zero, zero_add, mul_one] at hr
  rw [← presentedProP.comp_mk_freeProPGen]
  exact Units.val_inj.1 (by rw [Units.val_neg, Units.val_one]; linear_combination hr)

/-- **The prescription property forces the tabulated values, `q = 2` and `n` odd, at level
`f = ∞`** (Labute, Theorem 4, the forced computation on a derivation). For `n` odd, a continuous
character of the pro-`2` group presented by `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` has the prescription
property exactly when `χ(x₁) = -1` and `χ(x_i) = 1` for every other `i`. At `n = 1` this is the
rank-one statement for `ℤ/2`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_iff (hn : Odd n) :
    HasPrescriptionProperty χ ↔
      χ (presentedProPGen 2 n _ 0) = -1 ∧ ∀ i, i ≠ 0 → χ (presentedProPGen 2 n _ i) = 1 := by
  refine ⟨fun hχ ↦ ?_, fun h ↦
    hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_of_apply_eq n χ h.1 h.2⟩
  have hrels : ({demushkinWordTwoOddTop n (freeProPGen 2 n)} : Set (freeProP 2 (Fin n))) ⊆
      proPFrattini 2 (freeProP 2 (Fin n)) :=
    Set.singleton_subset_iff.2 (demushkinWordTwoOddTop_mem_proPFrattini n _)
  obtain ⟨k, hk⟩ := hn
  -- For the crossed homomorphism `F` with `F (x_i) = δ_{ij}`, `j ≥ 1`, only the commutator factor
  -- `(x_a, x_b)` containing `x_j` contributes to the value `χ(x₁)² F (x_a, x_b)` on the relator,
  -- so `F (x_a, x_b) = 0`.
  have hval : ∀ j, 0 < j → j < n → ∀ F : freeProP 2 (Fin n) → ℤ_[2],
      IsCrossedHom (χ.comp (presentedProP.mk 2 _)) F →
      (∀ i, F (freeProPGen 2 n i) = if i = j then 1 else 0) →
      F (demushkinWordTwoOddTop n (freeProPGen 2 n)) = 0 →
      F (labuteComm (freeProPGen 2 n (2 * ((j - 1) / 2) + 1))
        (freeProPGen 2 n (2 * ((j - 1) / 2) + 2))) = 0 := by
    intro j hj₀ hj F hF hFv hFr
    rw [hF.map_demushkinWordTwoOddTop, Finset.sum_eq_single ((j - 1) / 2)
      (fun i _ hi ↦ hF.map_labuteComm_eq_zero_of_eq_zero
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)]))
      (fun h0 ↦ absurd (mem_range.2 (by omega)) h0), hFv 0, ite_eq_right (by omega), mul_zero,
      add_zero, ← Units.val_pow_eq_pow_val] at hFr
    exact (Units.mul_right_eq_zero _).1 hFr
  refine ⟨apply_presentedProPGen_zero_eq_neg_one_of_hasPrescriptionProperty_demushkinWordTwoOddTop
    n χ (by omega) hχ, fun i hi₀ ↦ ?_⟩
  by_cases hin : i < n
  · rw [← presentedProP.comp_mk_freeProPGen]
    rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- `i ≥ 2` even: the partner of `x_i` in its commutator factor is `x_{i-1}`.
      obtain ⟨F, hF, hFv, hFr⟩ :=
        hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i - 1 < n)
      have hc := hval (i - 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
      rw [(by omega : 2 * ((i - 1 - 1) / 2) + 1 = i - 1),
        (by omega : 2 * ((i - 1 - 1) / 2) + 2 = i)] at hc
      exact hF.eq_one_of_map_labuteComm_eq_zero_left (by rw [hFv, ite_eq_left rfl])
        (by rw [hFv, ite_eq_right (by omega)]) hc
    · -- `i` odd: the partner is `x_{i+1}`, which exists because `n` is odd.
      obtain ⟨F, hF, hFv, hFr⟩ :=
        hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i + 1 < n)
      have hc := hval (i + 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
      rw [(by omega : 2 * ((i + 1 - 1) / 2) + 1 = i),
        (by omega : 2 * ((i + 1 - 1) / 2) + 2 = i + 1)] at hc
      exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right (by omega)])
        (by rw [hFv, ite_eq_left rfl]) hc
  · rw [presentedProPGen_eq_one_of_le 2 n _ (not_lt.1 hin), map_one]

/-- **The standard orientation of the `q = 2`, `n` odd normal form at level `f = ∞` has the
prescription property**, for `0 < n`. -/
theorem hasPrescriptionProperty_orientationTwoOddTop (hn : 0 < n) :
    HasPrescriptionProperty (orientationTwoOddTop n) :=
  hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_of_apply_eq n _
    (orientationTwoOddTop_presentedProPGen_zero n hn)
    fun _ hi₀ ↦ orientationTwoOddTop_presentedProPGen_of_ne n hi₀

/-- **Uniqueness of the canonical character of the `q = 2`, `n` odd normal form at level
`f = ∞`**: for `n` odd, a character with the prescription property is the standard orientation. -/
theorem eq_orientationTwoOddTop_of_hasPrescriptionProperty (hn : Odd n)
    (hχ : HasPrescriptionProperty χ) : χ = orientationTwoOddTop n := by
  obtain ⟨h₀, h⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop_iff n χ hn).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoOddTop_of, ← presentedProPGen_val]
  split_ifs with hi₀
  · rw [hi₀]
    exact h₀
  · exact h i hi₀

/-- **The `q = 2`, `n` odd normal form at level `f = ∞` has exactly one character with the
prescription property** (Labute, Theorem 4, for the normal form `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`
with `n` odd): the standard orientation, with `χ(x₁) = -1` and `χ(x_i) = 1` otherwise. -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoOddTop (hn : Odd n) :
    ∃! χ : presentedProP 2 (Fin n) {demushkinWordTwoOddTop n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ,
      HasPrescriptionProperty χ :=
  ⟨orientationTwoOddTop n, hasPrescriptionProperty_orientationTwoOddTop n hn.pos,
    fun χ hχ ↦ eq_orientationTwoOddTop_of_hasPrescriptionProperty n χ hn hχ⟩

end TwoOddTop

/-! ### The `q = 2`, `n` even normal form -/

section TwoEven

variable (a f n : ℕ)
  (χ : presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ)

/-- **The tabulated values give the prescription property, `q = 2` and `n` even** (Labute,
Theorem 4, existence). A continuous character of the pro-`2` group presented by
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with `χ(x₂) (1 + a) = -1`,
`χ(x₄) (1 - 2^f) = 1` and `χ(x_i) = 1` otherwise has the prescription property. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_of_apply_eq
    (h₁ : (χ (presentedProPGen 2 n _ 1) : ℤ_[2]) * (1 + a) = -1)
    (h₃ : (χ (presentedProPGen 2 n _ 3) : ℤ_[2]) * (1 - 2 ^ f) = 1)
    (h : ∀ i, i ≠ 1 → i ≠ 3 → χ (presentedProPGen 2 n _ i) = 1) : HasPrescriptionProperty χ := by
  refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    fun F hFc hF r hr ↦ ?_
  have h0 := h 0 zero_ne_one (by omega)
  have h2 := h 2 (by omega) (by omega)
  -- `χ(x₂) F (x₁, x₂) = (1 - χ(x₂)) F x₁` and `χ(x₄) F (x₃, x₄) = (1 - χ(x₄)) F x₃`.
  have hc01 := hF.mul_mul_map_labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1)
  rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, h0, Units.val_one,
    one_mul, sub_self, zero_mul, add_zero] at hc01
  rw [Set.mem_singleton_iff.mp hr, hF.map_demushkinWordTwoEven, presentedProP.comp_mk_freeProPGen,
    presentedProP.comp_mk_freeProPGen, h0, h2, Units.val_one, Finset.sum_eq_single 0 (fun i _ hi ↦
      hF.map_labuteComm_eq_zero_of_eq_one
        (by rw [presentedProP.comp_mk_freeProPGen]; exact h _ (by omega) (by omega))
        (by rw [presentedProP.comp_mk_freeProPGen]; exact h _ (by omega) (by omega))) fun h0' ↦ ?_]
  · have hc23 := hF.mul_mul_map_labuteComm (freeProPGen 2 n 2) (freeProPGen 2 n 3)
    rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, h2, Units.val_one,
      one_mul, sub_self, zero_mul, add_zero] at hc23
    simp only [Nat.mul_zero, Nat.zero_add, one_pow, one_mul, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
    refine (Units.mul_right_eq_zero (χ (presentedProPGen 2 n _ 3))).1
      ((Units.mul_right_eq_zero (χ (presentedProPGen 2 n _ 1))).1 ?_)
    linear_combination (χ (presentedProPGen 2 n _ 1) : ℤ_[2]) * hc23 +
      (χ (presentedProPGen 2 n _ 3) : ℤ_[2]) * hc01 -
      (χ (presentedProPGen 2 n _ 1) : ℤ_[2]) * F (freeProPGen 2 n 2) * h₃ +
      (χ (presentedProPGen 2 n _ 3) : ℤ_[2]) * F (freeProPGen 2 n 0) * h₁
  · -- For `n ≤ 3` the generator `x₄` is `1`, and `(x₃, 1) = 1`.
    rw [mem_range, not_lt, Nat.le_zero] at h0'
    rw [freeProPGen_eq_one_of_le 2 (by omega : n ≤ 2 * 0 + 3)]
    simp [labuteComm_def, hF.map_one]

/-- **The prescription property forces the tabulated values, `q = 2` and `n` even** (Labute,
Theorem 4, the forced computation on a derivation). For `2 ∣ a`, `f ≥ 1` and `n ≥ 4` even, a
continuous character of the pro-`2` group presented by
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` has the prescription property exactly when
`χ(x₂) (1 + a) = -1`, `χ(x₄) (1 - 2^f) = 1` and `χ(x_i) = 1` for every other `i`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff (ha : 2 ∣ a) (hf : 0 < f)
    (hn : Even n) (hn₃ : 3 < n) :
    HasPrescriptionProperty χ ↔
      (χ (presentedProPGen 2 n _ 1) : ℤ_[2]) * (1 + a) = -1 ∧
        (χ (presentedProPGen 2 n _ 3) : ℤ_[2]) * (1 - 2 ^ f) = 1 ∧
        ∀ i, i ≠ 1 → i ≠ 3 → χ (presentedProPGen 2 n _ i) = 1 := by
  refine ⟨fun hχ ↦ ?_, fun h ↦
    hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_of_apply_eq a f n χ h.1 h.2.1 h.2.2⟩
  have hrels : ({demushkinWordTwoEven a f n (freeProPGen 2 n)} : Set (freeProP 2 (Fin n))) ⊆
      proPFrattini 2 (freeProP 2 (Fin n)) :=
    Set.singleton_subset_iff.2 (demushkinWordTwoEven_mem_proPFrattini ha hf n _)
  obtain ⟨k, hk⟩ := hn
  -- For the crossed homomorphism `F` with `F (x_i) = δ_{ij}`, `j ≥ 2`, only the commutator factor
  -- containing `x_j` contributes to the value on the relator.
  have hsum : ∀ j, 2 ≤ j → j < n → ∀ F : freeProP 2 (Fin n) → ℤ_[2],
      IsCrossedHom (χ.comp (presentedProP.mk 2 _)) F →
      (∀ i, F (freeProPGen 2 n i) = if i = j then 1 else 0) →
      ∑ i ∈ range (n / 2 - 1),
          F (labuteComm (freeProPGen 2 n (2 * i + 2)) (freeProPGen 2 n (2 * i + 3))) =
        F (labuteComm (freeProPGen 2 n (2 * ((j - 2) / 2) + 2))
          (freeProPGen 2 n (2 * ((j - 2) / 2) + 3))) :=
    fun j hj₂ hj F hF hFv ↦ Finset.sum_eq_single _
      (fun i _ hi ↦ hF.map_labuteComm_eq_zero_of_eq_zero
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)]))
      fun h0 ↦ absurd (mem_range.2 (by omega)) h0
  -- For `j ≤ 2` no commutator factor beyond `(x₁, x₂)` contributes.
  have hsum₀ : ∀ j, j < 2 → ∀ F : freeProP 2 (Fin n) → ℤ_[2],
      IsCrossedHom (χ.comp (presentedProP.mk 2 _)) F →
      (∀ i, F (freeProPGen 2 n i) = if i = j then 1 else 0) →
      ∑ i ∈ range (n / 2 - 1),
        F (labuteComm (freeProPGen 2 n (2 * i + 2)) (freeProPGen 2 n (2 * i + 3))) = 0 :=
    fun j hj F hF hFv ↦ Finset.sum_eq_zero fun i _ ↦ hF.map_labuteComm_eq_zero_of_eq_zero
      (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)])
  -- For `j ≥ 5` the commutator factor `(x_a, x_b)` containing `x_j` has `F (x_a, x_b) = 0`.
  have hval : ∀ j, 4 ≤ j → j < n → ∀ F : freeProP 2 (Fin n) → ℤ_[2],
      IsCrossedHom (χ.comp (presentedProP.mk 2 _)) F →
      (∀ i, F (freeProPGen 2 n i) = if i = j then 1 else 0) →
      F (demushkinWordTwoEven a f n (freeProPGen 2 n)) = 0 →
      F (labuteComm (freeProPGen 2 n (2 * ((j - 2) / 2) + 2))
        (freeProPGen 2 n (2 * ((j - 2) / 2) + 3))) = 0 := by
    intro j hj₄ hj F hF hFv hFr
    rw [hF.map_demushkinWordTwoEven, hsum j (by omega) hj F hF hFv,
      hF.map_labuteComm_eq_zero_of_eq_zero (x := freeProPGen 2 n 0) (y := freeProPGen 2 n 1)
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)])] at hFr
    simp only [hFv 0, hFv 2, ite_eq_right (show (0 : ℕ) ≠ j by omega),
      ite_eq_right (show (2 : ℕ) ≠ j by omega), mul_zero, add_zero, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul] at hFr
    exact (Units.mul_right_eq_zero _).1 hFr
  -- `j = 2`: `χ(x₁) = 1`.
  have hx0 : χ (presentedProPGen 2 n _ 0) = 1 := by
    obtain ⟨F, hF, hFv, hFr⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : 1 < n)
    have hr := hFr _ rfl
    rw [hF.map_demushkinWordTwoEven, hsum₀ 1 one_lt_two F hF hFv] at hr
    simp only [hFv 0, hFv 2, ite_eq_right zero_ne_one, ite_eq_right (show (2 : ℕ) ≠ 1 by omega),
      mul_zero, add_zero, zero_add, ← Units.val_pow_eq_pow_val] at hr
    rw [← presentedProP.comp_mk_freeProPGen]
    exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right zero_ne_one])
      (by rw [hFv, ite_eq_left rfl]) ((Units.mul_right_eq_zero _).1 hr)
  -- `j = 4`: `χ(x₃) = 1`.
  have hx2 : χ (presentedProPGen 2 n _ 2) = 1 := by
    obtain ⟨F, hF, hFv, hFr⟩ := hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels hn₃
    have hr := hFr _ rfl
    rw [hF.map_demushkinWordTwoEven, hsum 3 (by omega) hn₃ F hF hFv,
      hF.map_labuteComm_eq_zero_of_eq_zero (x := freeProPGen 2 n 0) (y := freeProPGen 2 n 1)
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)])] at hr
    simp only [hFv 0, hFv 2, ite_eq_right (show (0 : ℕ) ≠ 3 by omega),
      ite_eq_right (show (2 : ℕ) ≠ 3 by omega), mul_zero, add_zero, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul] at hr
    rw [(by omega : 2 * ((3 - 2) / 2) + 2 = 2), (by omega : 2 * ((3 - 2) / 2) + 3 = 3)] at hr
    rw [← presentedProP.comp_mk_freeProPGen]
    exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right (by omega)])
      (by rw [hFv, ite_eq_left rfl]) ((Units.mul_right_eq_zero _).1 hr)
  refine ⟨?_, ?_, fun i hi₁ hi₃ ↦ ?_⟩
  · -- `j = 1`: `2 + a + χ(x₂)⁻¹ - 1 = 0`.
    obtain ⟨F, hF, hFv, hFr⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : 0 < n)
    have hr := hFr _ rfl
    rw [hF.map_demushkinWordTwoEven, hsum₀ 0 two_pos F hF hFv,
      presentedProP.comp_mk_freeProPGen, hx0, Units.val_one] at hr
    simp only [hFv 0, hFv 2, ite_eq_left, ite_eq_right (show (2 : ℕ) ≠ 0 by omega), one_pow,
      one_mul, mul_one, mul_zero, zero_add, add_zero, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_ofNat] at hr
    have hc := hF.mul_mul_map_labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1)
    rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx0, Units.val_one,
      one_mul, sub_self, zero_mul, add_zero, hFv 0, ite_eq_left rfl, mul_one] at hc
    linear_combination (χ (presentedProPGen 2 n _ 1) : ℤ_[2]) * hr - hc
  · -- `j = 3`: `2^f + χ(x₄)⁻¹ - 1 = 0`.
    obtain ⟨F, hF, hFv, hFr⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : 2 < n)
    have hr := hFr _ rfl
    rw [hF.map_demushkinWordTwoEven, hsum 2 le_rfl (by omega) F hF hFv,
      hF.map_labuteComm_eq_zero_of_eq_zero (x := freeProPGen 2 n 0) (y := freeProPGen 2 n 1)
        (by rw [hFv, ite_eq_right (by omega)]) (by rw [hFv, ite_eq_right (by omega)]),
      presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx0, hx2,
      Units.val_one] at hr
    simp only [Nat.sub_self, Nat.zero_div, Nat.zero_add, hFv 0, hFv 2, ite_eq_left,
      ite_eq_right (show (0 : ℕ) ≠ 2 by omega), one_pow, one_mul, mul_one, mul_zero, add_zero,
      sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hr
    have hc := hF.mul_mul_map_labuteComm (freeProPGen 2 n 2) (freeProPGen 2 n 3)
    rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx2, Units.val_one,
      one_mul, sub_self, zero_mul, add_zero, hFv 2, ite_eq_left rfl, mul_one] at hc
    linear_combination hc - (χ (presentedProPGen 2 n _ 3) : ℤ_[2]) * hr
  · by_cases hin : i < n
    · rcases Nat.lt_or_ge i 4 with h4 | h4
      · rcases (by omega : i = 0 ∨ i = 2) with rfl | rfl
        · exact hx0
        · exact hx2
      -- `j ≥ 5`: the partner of `x_j` in its commutator factor has `χ = 1`.
      rw [← presentedProP.comp_mk_freeProPGen]
      rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
      · obtain ⟨F, hF, hFv, hFr⟩ :=
          hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i + 1 < n)
        have hc := hval (i + 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
        rw [(by omega : 2 * ((i + 1 - 2) / 2) + 2 = i),
          (by omega : 2 * ((i + 1 - 2) / 2) + 3 = i + 1)] at hc
        exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right (by omega)])
          (by rw [hFv, ite_eq_left rfl]) hc
      · obtain ⟨F, hF, hFv, hFr⟩ :=
          hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by omega : i - 1 < n)
        have hc := hval (i - 1) (by omega) (by omega) F hF hFv (hFr _ rfl)
        rw [(by omega : 2 * ((i - 1 - 2) / 2) + 2 = i - 1),
          (by omega : 2 * ((i - 1 - 2) / 2) + 3 = i)] at hc
        exact hF.eq_one_of_map_labuteComm_eq_zero_left (by rw [hFv, ite_eq_left rfl])
          (by rw [hFv, ite_eq_right (by omega)]) hc
    · rw [presentedProPGen_eq_one_of_le 2 n _ (not_lt.1 hin), map_one]

/-- **The standard orientation of the `q = 2`, `n` even normal form has the prescription
property**: for `3 < n`, the character with `χ(x₂) = v`, `v (1 + a) = -1`, `χ(x₄) = u`,
`u (1 - 2^f) = 1`, and `χ(x_i) = 1` otherwise. -/
theorem hasPrescriptionProperty_orientationTwoEven (hn₃ : 3 < n) (v u : ℤ_[2]ˣ)
    (hv : (v : ℤ_[2]) * (1 + a) = -1) (hu : (u : ℤ_[2]) * (1 - 2 ^ f) = 1) :
    HasPrescriptionProperty (orientationTwoEven a f n v u) :=
  hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_of_apply_eq a f n _
    (by rw [orientationTwoEven_presentedProPGen_one a f n v u (by omega)]; exact hv)
    (by rw [orientationTwoEven_presentedProPGen_three a f n v u hn₃]; exact hu)
    fun _ hi₁ hi₃ ↦ orientationTwoEven_presentedProPGen_of_ne a f n v u hi₁ hi₃

/-- **Uniqueness of the canonical character of the `q = 2`, `n` even normal form**: for `2 ∣ a`,
`f ≥ 1` and `n ≥ 4` even, a character with the prescription property is the orientation with
marked values its values `χ(x₂)`, `χ(x₄)`. -/
theorem eq_orientationTwoEven_of_hasPrescriptionProperty (ha : 2 ∣ a) (hf : 0 < f) (hn : Even n)
    (hn₃ : 3 < n) (hχ : HasPrescriptionProperty χ) :
    χ = orientationTwoEven a f n (χ (presentedProPGen 2 n _ 1)) (χ (presentedProPGen 2 n _ 3)) := by
  obtain ⟨-, -, h⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff a f n χ ha hf hn hn₃).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoEven_of, ← presentedProPGen_val]
  split_ifs with hi₁ hi₃
  · rw [hi₁]
  · rw [hi₃]
  · exact h i hi₁ hi₃

/-- **The `q = 2`, `n` even normal form has exactly one character with the prescription
property** (Labute, Theorem 4, for the normal form
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with `2 ∣ a`, `f ≥ 1` and `n ≥ 4` even): the
standard orientation, with `χ(x₂) = -(1 + a)⁻¹`, `χ(x₄) = (1 - 2^f)⁻¹` and `χ(x_i) = 1`
otherwise. -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoEven (ha : 2 ∣ a)
    (hf : 0 < f) (hn : Even n) (hn₃ : 3 < n) :
    ∃! χ : presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)} →ₜ* ℤ_[2]ˣ,
      HasPrescriptionProperty χ := by
  obtain ⟨v, hv⟩ := exists_val_mul_one_add_eq_neg_one (a := (a : ℤ_[2]))
    (by simpa using (Nat.cast_dvd_cast ha : ((2 : ℕ) : ℤ_[2]) ∣ (a : ℤ_[2])))
  obtain ⟨u, hu⟩ := exists_val_mul_one_sub_pow_eq_one 2 hf
  have hu' : (u : ℤ_[2]) * (1 - 2 ^ f) = 1 := by exact_mod_cast hu
  refine ⟨orientationTwoEven a f n v u,
    hasPrescriptionProperty_orientationTwoEven a f n hn₃ v u hv hu', fun χ hχ ↦ ?_⟩
  obtain ⟨h₁, h₃, h⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEven_iff a f n χ ha hf hn hn₃).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoEven_of, ← presentedProPGen_val]
  split_ifs with hi₁ hi₃
  · rw [hi₁]
    exact Units.val_inj.1 (by linear_combination (χ (presentedProPGen 2 n _ 1) : ℤ_[2]) * hv -
      (v : ℤ_[2]) * h₁)
  · rw [hi₃]
    exact Units.val_inj.1 (by linear_combination (u : ℤ_[2]) * h₃ -
      (χ (presentedProPGen 2 n _ 3) : ℤ_[2]) * hu')
  · exact h i hi₁ hi₃

end TwoEven

/-! ### The `q = 2` normal form of rank two

On two generators the even normal form is the rank-two word `x₁^{2+a} (x₁, x₂)`, with no level:
only the marked value on `x₂` remains. -/

section TwoRankTwo

variable (a : ℕ)
  (χ : presentedProP 2 (Fin 2) {demushkinWordTwoRankTwo a (freeProPGen 2 2)} →ₜ* ℤ_[2]ˣ)

/-- **The tabulated values give the prescription property in rank two, `q = 2`**: a continuous
character of the pro-`2` group presented by `x₁^{2+a} (x₁, x₂)` with `χ(x₁) = 1` and
`χ(x₂) (1 + a) = -1` has the prescription property. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_of_apply_eq
    (h₀ : χ (presentedProPGen 2 2 _ 0) = 1)
    (h₁ : (χ (presentedProPGen 2 2 _ 1) : ℤ_[2]) * (1 + a) = -1) : HasPrescriptionProperty χ := by
  refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    fun F hFc hF r hr ↦ ?_
  have hc01 := hF.mul_mul_map_labuteComm (freeProPGen 2 2 0) (freeProPGen 2 2 1)
  rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, h₀, Units.val_one,
    one_mul, sub_self, zero_mul, add_zero] at hc01
  rw [Set.mem_singleton_iff.mp hr, hF.map_demushkinWordTwoRankTwo,
    presentedProP.comp_mk_freeProPGen, h₀]
  simp only [Units.val_one, one_pow, one_mul, sum_const, card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_ofNat]
  refine (Units.mul_right_eq_zero (χ (presentedProPGen 2 2 _ 1))).1 ?_
  linear_combination hc01 + F (freeProPGen 2 2 0) * h₁

/-- **The prescription property forces the tabulated values in rank two, `q = 2`** (Labute,
Theorem 4 and Remark, the case `n = 2`). For `2 ∣ a`, a continuous character of the pro-`2` group
presented by `x₁^{2+a} (x₁, x₂)` has the prescription property exactly when `χ(x₁) = 1` and
`χ(x₂) (1 + a) = -1`. -/
theorem hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff (ha : 2 ∣ a) :
    HasPrescriptionProperty χ ↔
      χ (presentedProPGen 2 2 _ 0) = 1 ∧ (χ (presentedProPGen 2 2 _ 1) : ℤ_[2]) * (1 + a) = -1 := by
  refine ⟨fun hχ ↦ ?_, fun h ↦
    hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_of_apply_eq a χ h.1 h.2⟩
  have hrels : ({demushkinWordTwoRankTwo a (freeProPGen 2 2)} : Set (freeProP 2 (Fin 2))) ⊆
      proPFrattini 2 (freeProP 2 (Fin 2)) :=
    Set.singleton_subset_iff.2 (demushkinWordTwoRankTwo_mem_proPFrattini ha _)
  -- `j = 2`: `χ(x₁) = 1`.
  have hx0 : χ (presentedProPGen 2 2 _ 0) = 1 := by
    obtain ⟨F, hF, hFv, hFr⟩ :=
      hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by norm_num : 1 < 2)
    have hr := hFr _ rfl
    rw [hF.map_demushkinWordTwoRankTwo] at hr
    simp only [hFv 0, ite_eq_right zero_ne_one, mul_zero, add_zero,
      ← Units.val_pow_eq_pow_val] at hr
    rw [← presentedProP.comp_mk_freeProPGen]
    exact hF.eq_one_of_map_labuteComm_eq_zero_right (by rw [hFv, ite_eq_right zero_ne_one])
      (by rw [hFv, ite_eq_left rfl]) ((Units.mul_right_eq_zero _).1 hr)
  refine ⟨hx0, ?_⟩
  -- `j = 1`: `2 + a + χ(x₂)⁻¹ - 1 = 0`.
  obtain ⟨F, hF, hFv, hFr⟩ :=
    hχ.exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite hrels (by norm_num : 0 < 2)
  have hr := hFr _ rfl
  rw [hF.map_demushkinWordTwoRankTwo, presentedProP.comp_mk_freeProPGen, hx0, Units.val_one] at hr
  simp only [hFv 0, ite_eq_left, one_pow, one_mul, mul_one, sum_const, card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat] at hr
  have hc := hF.mul_mul_map_labuteComm (freeProPGen 2 2 0) (freeProPGen 2 2 1)
  rw [presentedProP.comp_mk_freeProPGen, presentedProP.comp_mk_freeProPGen, hx0, Units.val_one,
    one_mul, sub_self, zero_mul, add_zero, hFv 0, ite_eq_left rfl, mul_one] at hc
  linear_combination (χ (presentedProPGen 2 2 _ 1) : ℤ_[2]) * hr - hc

/-- **The standard orientation of the rank-two `q = 2` normal form has the prescription property**:
the character with `χ(x₁) = 1` and `χ(x₂) = v`, `v (1 + a) = -1`. -/
theorem hasPrescriptionProperty_orientationTwoRankTwo (v : ℤ_[2]ˣ)
    (hv : (v : ℤ_[2]) * (1 + a) = -1) : HasPrescriptionProperty (orientationTwoRankTwo a v) :=
  hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_of_apply_eq a _
    (orientationTwoRankTwo_presentedProPGen_zero a v)
    (by rw [orientationTwoRankTwo_presentedProPGen_one]; exact hv)

/-- **Uniqueness of the canonical character of the rank-two `q = 2` normal form**: for `2 ∣ a`, a
character with the prescription property is the orientation with marked value its value `χ(x₂)`. -/
theorem eq_orientationTwoRankTwo_of_hasPrescriptionProperty (ha : 2 ∣ a)
    (hχ : HasPrescriptionProperty χ) :
    χ = orientationTwoRankTwo a (χ (presentedProPGen 2 2 _ 1)) := by
  obtain ⟨h₀, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff a χ ha).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoRankTwo_of, ← presentedProPGen_val]
  split_ifs with hi₁
  · rw [hi₁]
  · rw [(by omega : (i : ℕ) = 0)]
    exact h₀

/-- **The rank-two `q = 2` normal form has exactly one character with the prescription property**
(Labute, Theorem 4, for the normal form `x₁^{2+a} (x₁, x₂)` with `2 ∣ a`): the standard
orientation, with `χ(x₁) = 1` and `χ(x₂) = -(1 + a)⁻¹`. -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo (ha : 2 ∣ a) :
    ∃! χ : presentedProP 2 (Fin 2) {demushkinWordTwoRankTwo a (freeProPGen 2 2)} →ₜ* ℤ_[2]ˣ,
      HasPrescriptionProperty χ := by
  obtain ⟨v, hv⟩ := exists_val_mul_one_add_eq_neg_one (a := (a : ℤ_[2]))
    (by simpa using (Nat.cast_dvd_cast ha : ((2 : ℕ) : ℤ_[2]) ∣ (a : ℤ_[2])))
  refine ⟨orientationTwoRankTwo a v, hasPrescriptionProperty_orientationTwoRankTwo a v hv,
    fun χ hχ ↦ ?_⟩
  obtain ⟨h₀, h₁⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoRankTwo_iff a χ ha).1 hχ
  refine presentedProP.hom_ext_of fun i ↦ ?_
  rw [orientationTwoRankTwo_of, ← presentedProPGen_val]
  split_ifs with hi₁
  · rw [hi₁]
    exact Units.val_inj.1 (by linear_combination (χ (presentedProPGen 2 2 _ 1) : ℤ_[2]) * hv -
      (v : ℤ_[2]) * h₁)
  · rw [(by omega : (i : ℕ) = 0)]
    exact h₀

end TwoRankTwo

end TauCeti
