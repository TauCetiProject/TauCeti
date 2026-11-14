/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

/-!
# The root-lattice grading of a quantized enveloping algebra

Every defining relation of `TauCeti.QuantizedEnvelopingAlgebra D q` is homogeneous with respect to
the root lattice `D.rootLattice = ⨁ᵢ ℤ αᵢ ≤ X` when the generators are given the weights
`deg Eᵢ = αᵢ`, `deg Fᵢ = -αᵢ`, and `deg K_y = 0`:

* `K_0 = 1` and `K_y K_z = K_(y + z)` lie in degree `0`;
* `K_y Eᵢ = q^⟨αᵢ, y⟩ Eᵢ K_y` and `K_y Fᵢ = q^(-⟨αᵢ, y⟩) Fᵢ K_y` lie in degrees `αᵢ` and `-αᵢ`;
* `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)` lies in degree `0`, and `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` (`i ≠ j`)
  lies in degree `αᵢ - αⱼ`;
* the divided-power quantum Serre sums for `(i, j)` (`i ≠ j`) lie in degrees `(1 - aᵢⱼ) αᵢ + αⱼ` and
  `-(1 - aᵢⱼ) αᵢ - αⱼ`.

Consequently, the word spans `TauCeti.QuantizedEnvelopingAlgebra.rootGrading D q β` decompose
`QuantizedEnvelopingAlgebra D q` as an internal direct sum indexed by `D.rootLattice`, giving a
`GradedAlgebra` instance whenever `X` has decidable equality. On any element `u` of root-lattice
degree `β`, toral elements act by weight `⟨β, y⟩`:
`K_y u = q^⟨β, y⟩ (u K_y)` and `K_y u K_(-y) = q^⟨β, y⟩ u`.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.generatorDegree`: the root-lattice degree of a presentation
  generator (`Eᵢ ↦ αᵢ`, `Fᵢ ↦ -αᵢ`, `K_y ↦ 0`).
* `TauCeti.QuantizedEnvelopingAlgebra.rootGrading D q`: the `D.rootLattice`-indexed family of
  homogeneous `K`-submodules of `QuantizedEnvelopingAlgebra D q`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.isInternal_rootGrading` and `instGradedAlgebra`:
  `QuantizedEnvelopingAlgebra D q` is internally `D.rootLattice`-graded.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mul_of_mem_rootGrading` and
  `k_mul_mul_k_neg_of_mem_rootGrading`: toral commutation and conjugation on homogeneous elements of
  degree `β : D.rootLattice`, valid for every `q : K`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.2.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §4.7.
-/

public section

open Finset
open scoped DirectSum

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
  (D : CartanDatum ι X Y) (q : K)

/-- The root-lattice degree of a presentation generator: `αᵢ` on `Eᵢ`, `-αᵢ` on `Fᵢ`, and `0` on
`K_y`. -/
def generatorDegree : Generator ι Y → D.rootLattice
  | .e i => D.simpleRoot i
  | .f i => -D.simpleRoot i
  | .k _ => 0

@[simp]
theorem generatorDegree_e (i : ι) : generatorDegree D (.e i) = D.simpleRoot i := (rfl)

@[simp]
theorem generatorDegree_f (i : ι) : generatorDegree D (.f i) = -D.simpleRoot i := (rfl)

@[simp]
theorem generatorDegree_k (y : Y) : generatorDegree D (.k y) = 0 := (rfl)

/-- The `β`-homogeneous `K`-submodule of `QuantizedEnvelopingAlgebra D q` (`β : D.rootLattice`),
spanned by words in the presentation generators of total root-lattice degree `β`. -/
noncomputable def rootGrading (β : D.rootLattice) :
    Submodule K (QuantizedEnvelopingAlgebra D q) :=
  Submodule.span K {u | ∃ l : List (Generator ι Y),
    (l.map (generatorDegree D)).sum = β ∧ (l.map (generator D q)).prod = u}

theorem rootGrading_def (β : D.rootLattice) :
    rootGrading D q β = Submodule.span K {u | ∃ l : List (Generator ι Y),
      (l.map (generatorDegree D)).sum = β ∧ (l.map (generator D q)).prod = u} := (rfl)

section Membership

variable {D q}

/-- Any word in the presentation generators lies in the homogeneous piece of its total degree. -/
theorem prod_mem_rootGrading (l : List (Generator ι Y)) :
    (l.map (generator D q)).prod ∈ rootGrading D q (l.map (generatorDegree D)).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

theorem generator_mem_rootGrading (g : Generator ι Y) :
    generator D q g ∈ rootGrading D q (generatorDegree D g) := by
  simpa using prod_mem_rootGrading (D := D) (q := q) [g]

theorem e_mem_rootGrading (i : ι) :
    e D q i ∈ rootGrading D q (D.simpleRoot i) := by
  simpa using generator_mem_rootGrading (D := D) (q := q) (.e i)

theorem f_mem_rootGrading (i : ι) :
    f D q i ∈ rootGrading D q (-D.simpleRoot i) := by
  simpa using generator_mem_rootGrading (D := D) (q := q) (.f i)

theorem k_mem_rootGrading (y : Y) :
    k D q y ∈ rootGrading D q 0 := by
  simpa using generator_mem_rootGrading (D := D) (q := q) (.k y)

noncomputable instance : SetLike.GradedMonoid (rootGrading D q) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem {α β a b} ha hb := by
    have hmul : rootGrading D q α * rootGrading D q β ≤ rootGrading D q (α + β) := by
      rw [rootGrading_def, rootGrading_def, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l₁, rfl, rfl⟩, _, ⟨l₂, rfl, rfl⟩, rfl⟩
      simpa using prod_mem_rootGrading (D := D) (q := q) (l₁ ++ l₂)
    exact hmul (Submodule.mul_mem_mul ha hb)

theorem e_pow_mem_rootGrading (i : ι) (n : ℕ) :
    e D q i ^ n ∈ rootGrading D q (n • D.simpleRoot i) :=
  SetLike.pow_mem_graded n (e_mem_rootGrading i)

theorem f_pow_mem_rootGrading (i : ι) (n : ℕ) :
    f D q i ^ n ∈ rootGrading D q (n • (-D.simpleRoot i)) :=
  SetLike.pow_mem_graded n (f_mem_rootGrading i)

theorem quantumDividedPower_mem_rootGrading (qi : K) {β : D.rootLattice}
    {u : QuantizedEnvelopingAlgebra D q} (hu : u ∈ rootGrading D q β) (n : ℕ) :
    quantumDividedPower qi u n ∈ rootGrading D q (n • β) := by
  rw [quantumDividedPower_def]
  exact (rootGrading D q _).smul_mem _ (SetLike.pow_mem_graded n hu)

theorem eDividedPower_mem_rootGrading (i : ι) (n : ℕ) :
    eDividedPower D q i n ∈ rootGrading D q (n • D.simpleRoot i) :=
  quantumDividedPower_mem_rootGrading _ (e_mem_rootGrading i) n

theorem fDividedPower_mem_rootGrading (i : ι) (n : ℕ) :
    fDividedPower D q i n ∈ rootGrading D q (n • (-D.simpleRoot i)) :=
  quantumDividedPower_mem_rootGrading _ (f_mem_rootGrading i) n

/-! ### Toral weight action on homogeneous components -/

private theorem k_mul_word (y : Y) (l : List (Generator ι Y)) :
    k D q y * (l.map (generator D q)).prod =
      q ^ D.pairing ((l.map (generatorDegree D)).sum : X) y •
        ((l.map (generator D q)).prod * k D q y) := by
  rcases eq_or_ne q 0 with rfl | hq
  · induction l with
    | nil => simp
    | cons g t ih =>
      cases g with
      | e i => simp
      | f i => simp
      | k z =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons, generatorDegree_k, zero_add,
          generator_k]
        rw [← mul_assoc, (commute_k_k y z).eq, mul_assoc, ih, mul_smul_comm, mul_assoc]
  · induction l with
    | nil => simp
    | cons g t ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Submodule.coe_add, map_add,
        LinearMap.add_apply, zpow_add₀ hq]
      cases g with
      | e i =>
        simp only [generator_e, generatorDegree_e, D.coe_simpleRoot]
        rw [← mul_assoc, k_mul_e, smul_mul_assoc, mul_assoc, ih, mul_smul_comm, smul_smul,
          mul_assoc]
      | f i =>
        simp only [generator_f, generatorDegree_f, Submodule.coe_neg, D.coe_simpleRoot, map_neg,
          LinearMap.neg_apply]
        rw [← mul_assoc, k_mul_f, smul_mul_assoc, mul_assoc, ih, mul_smul_comm, smul_smul,
          mul_assoc]
      | k z =>
        simp only [generator_k, generatorDegree_k, Submodule.coe_zero, map_zero,
          LinearMap.zero_apply, zpow_zero, one_mul]
        rw [← mul_assoc, (commute_k_k y z).eq, mul_assoc, ih, mul_smul_comm, mul_assoc]

/-- Toral elements commute past a `β`-homogeneous element `u` with scalar factor `q^⟨β, y⟩`. -/
theorem k_mul_of_mem_rootGrading {β : D.rootLattice} {u : QuantizedEnvelopingAlgebra D q}
    (hu : u ∈ rootGrading D q β) (y : Y) :
    k D q y * u = q ^ D.pairing (β : X) y • (u * k D q y) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    rcases hu with ⟨l, rfl, rfl⟩
    exact k_mul_word y l
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, ha, hb, add_mul, smul_add]
  | smul c a _ ha => rw [mul_smul_comm, ha, smul_mul_assoc, smul_comm]

/-- Right-to-left form of `k_mul_of_mem_rootGrading`: `u K_y = q^(-⟨β, y⟩) (K_y u)`. -/
theorem mul_k_of_mem_rootGrading {β : D.rootLattice} {u : QuantizedEnvelopingAlgebra D q}
    (hu : u ∈ rootGrading D q β) (y : Y) :
    u * k D q y = q ^ (-D.pairing (β : X) y) • (k D q y * u) := by
  calc
    u * k D q y = k D q y * (k D q (-y) * u) * k D q y := by rw [k_mul_k_neg_mul]
    _ = q ^ (-D.pairing (β : X) y) • (k D q y * u) := by
      rw [k_mul_of_mem_rootGrading hu (-y), map_neg, mul_smul_comm, smul_mul_assoc]
      simp only [mul_assoc, k_neg_mul_k, mul_one]

/-- Conjugation by `K_y` acts on `rootGrading D q β` as multiplication by `q^⟨β, y⟩`. -/
theorem k_mul_mul_k_neg_of_mem_rootGrading {β : D.rootLattice} {u : QuantizedEnvelopingAlgebra D q}
    (hu : u ∈ rootGrading D q β) (y : Y) :
    k D q y * u * k D q (-y) = q ^ D.pairing (β : X) y • u := by
  rw [k_mul_of_mem_rootGrading hu y, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]

end Membership

/-! ### Internal direct sum decomposition and `GradedAlgebra` instance -/

section GradedAlgebra

variable [DecidableEq X]

private theorem of_eq_of {α β : D.rootLattice} {x : rootGrading D q α} {y : rootGrading D q β}
    (hdeg : α = β) (hval : (x : QuantizedEnvelopingAlgebra D q) = y) :
    DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) α x =
      DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β y := by
  subst hdeg
  congr 1
  exact Subtype.ext hval

private theorem of_mul_of_eq {α β γ : D.rootLattice} (x : rootGrading D q α)
    (y : rootGrading D q β) (hdeg : α + β = γ) :
    DirectSum.of (fun δ ↦ ↥(rootGrading D q δ)) α x *
        DirectSum.of (fun δ ↦ ↥(rootGrading D q δ)) β y =
      DirectSum.of (fun δ ↦ ↥(rootGrading D q δ)) γ
        ⟨(x : QuantizedEnvelopingAlgebra D q) * y,
          hdeg ▸ SetLike.mul_mem_graded x.2 y.2⟩ := by
  rw [DirectSum.of_mul_of]
  exact of_eq_of D q hdeg rfl

private theorem of_sub_of (β : D.rootLattice) (x y : rootGrading D q β) :
    DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β x -
        DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β y =
      DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β (x - y) :=
  (map_sub (DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β) x y).symm

private theorem pow_of_rootGrading (β : D.rootLattice) (x : rootGrading D q β) (n : ℕ) :
    DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β x ^ n =
      DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) (n • β)
        ⟨(x : QuantizedEnvelopingAlgebra D q) ^ n, SetLike.pow_mem_graded n x.2⟩ := by
  induction n with
  | zero =>
    rw [pow_zero, DirectSum.one_def]
    exact of_eq_of D q (zero_nsmul β).symm (pow_zero _).symm
  | succ n ih =>
    rw [pow_succ, ih, DirectSum.of_mul_of]
    exact of_eq_of D q (succ_nsmul β n).symm (pow_succ (x : QuantizedEnvelopingAlgebra D q) n).symm

private theorem quantumDividedPower_of_rootGrading (qi : K) (β : D.rootLattice)
    (x : rootGrading D q β) (n : ℕ) :
    quantumDividedPower qi (DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β x) n =
      DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) (n • β)
        ⟨quantumDividedPower qi (x : QuantizedEnvelopingAlgebra D q) n,
          quantumDividedPower_mem_rootGrading qi x.2 n⟩ := by
  rw [quantumDividedPower_def, pow_of_rootGrading, ← DirectSum.of_smul]
  exact of_eq_of D q rfl (quantumDividedPower_def qi (x : QuantizedEnvelopingAlgebra D q) n).symm

private noncomputable def decomposeTuple :
    GeneratorTuple D q (⨁ β : D.rootLattice, rootGrading D q β) where
  e i := DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (D.simpleRoot i)
    ⟨e D q i, e_mem_rootGrading i⟩
  f i := DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (-D.simpleRoot i)
    ⟨f D q i, f_mem_rootGrading i⟩
  k y := DirectSum.of (fun β ↦ ↥(rootGrading D q β)) 0
    ⟨k D q y, k_mem_rootGrading y⟩
  k_zero := by
    rw [DirectSum.one_def]
    exact of_eq_of D q rfl k_zero
  k_mul_k y z := by
    rw [of_mul_of_eq D q _ _ (zero_add 0)]
    exact of_eq_of D q rfl (k_mul_k y z)
  k_mul_e y i := by
    rw [of_mul_of_eq D q _ _ (zero_add _), of_mul_of_eq D q _ _ (add_zero _),
      ← DirectSum.of_smul]
    exact of_eq_of D q rfl (k_mul_e y i)
  k_mul_f y i := by
    rw [of_mul_of_eq D q _ _ (zero_add _), of_mul_of_eq D q _ _ (add_zero _),
      ← DirectSum.of_smul]
    exact of_eq_of D q rfl (k_mul_f y i)
  e_mul_f_sub_f_mul_e_self i := by
    rw [of_mul_of_eq D q _ _ (add_neg_cancel _), of_mul_of_eq D q _ _ (neg_add_cancel _),
      of_sub_of, of_sub_of, ← DirectSum.of_smul]
    exact of_eq_of D q rfl (e_mul_f_sub_f_mul_e_self i)
  e_mul_f_sub_f_mul_e_of_ne {i j} hij := by
    rw [of_mul_of_eq D q _ _ rfl, of_mul_of_eq D q _ _ (add_comm _ _), of_sub_of,
      ← map_zero (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (D.simpleRoot i + -D.simpleRoot j))]
    exact of_eq_of D q rfl (e_mul_f_sub_f_mul_e_of_ne hij)
  serre_e {i j} hij := by
    let deg := serreLength D i j • D.simpleRoot i + D.simpleRoot j
    rw [← sum_attach (range (serreLength D i j + 1))]
    have hterm : ∀ r ∈ (range (serreLength D i j + 1)).attach,
        (-1 : K) ^ r.1 •
          (quantumDividedPower (q ^ D.symmetrizer i)
              (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (D.simpleRoot i)
                ⟨e D q i, e_mem_rootGrading i⟩) r.1 *
            DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (D.simpleRoot j)
              ⟨e D q j, e_mem_rootGrading j⟩ *
            quantumDividedPower (q ^ D.symmetrizer i)
              (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (D.simpleRoot i)
                ⟨e D q i, e_mem_rootGrading i⟩) (serreLength D i j - r.1)) =
        DirectSum.of (fun β ↦ ↥(rootGrading D q β)) deg
          ⟨(-1 : K) ^ r.1 •
            (eDividedPower D q i r.1 * e D q j * eDividedPower D q i (serreLength D i j - r.1)),
            by
              have hr' : r.1 ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp r.2)
              have hdeg : r.1 • D.simpleRoot i + D.simpleRoot j +
                  (serreLength D i j - r.1) • D.simpleRoot i = deg := by
                rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr']
              exact hdeg ▸ (rootGrading D q _).smul_mem _
                (SetLike.mul_mem_graded
                  (SetLike.mul_mem_graded (eDividedPower_mem_rootGrading i r.1)
                    (e_mem_rootGrading j))
                  (eDividedPower_mem_rootGrading i (serreLength D i j - r.1)))⟩ :=
      fun r _ ↦ by
        have hr' : r.1 ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp r.2)
        have hdeg : r.1 • D.simpleRoot i + D.simpleRoot j +
            (serreLength D i j - r.1) • D.simpleRoot i = deg := by
          rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr']
        rw [quantumDividedPower_of_rootGrading, quantumDividedPower_of_rootGrading,
          of_mul_of_eq D q _ _ rfl, of_mul_of_eq D q _ _ hdeg, ← DirectSum.of_smul]
        exact of_eq_of D q rfl rfl
    rw [sum_congr rfl hterm, ← map_sum,
      ← map_zero (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) deg)]
    refine of_eq_of D q rfl ?_
    rw [Submodule.coe_sum, Submodule.coe_zero]
    exact (sum_attach (range (serreLength D i j + 1)) fun r ↦
      (-1 : K) ^ r •
        (eDividedPower D q i r * e D q j * eDividedPower D q i (serreLength D i j - r))).trans
      (serre_e (D := D) (q := q) hij)
  serre_f {i j} hij := by
    let deg := serreLength D i j • (-D.simpleRoot i) + (-D.simpleRoot j)
    rw [← sum_attach (range (serreLength D i j + 1))]
    have hterm : ∀ r ∈ (range (serreLength D i j + 1)).attach,
        (-1 : K) ^ r.1 •
          (quantumDividedPower (q ^ D.symmetrizer i)
              (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (-D.simpleRoot i)
                ⟨f D q i, f_mem_rootGrading i⟩) r.1 *
            DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (-D.simpleRoot j)
              ⟨f D q j, f_mem_rootGrading j⟩ *
            quantumDividedPower (q ^ D.symmetrizer i)
              (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (-D.simpleRoot i)
                ⟨f D q i, f_mem_rootGrading i⟩) (serreLength D i j - r.1)) =
        DirectSum.of (fun β ↦ ↥(rootGrading D q β)) deg
          ⟨(-1 : K) ^ r.1 •
            (fDividedPower D q i r.1 * f D q j * fDividedPower D q i (serreLength D i j - r.1)),
            by
              have hr' : r.1 ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp r.2)
              have hdeg : r.1 • (-D.simpleRoot i) + (-D.simpleRoot j) +
                  (serreLength D i j - r.1) • (-D.simpleRoot i) = deg := by
                rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr']
              exact hdeg ▸ (rootGrading D q _).smul_mem _
                (SetLike.mul_mem_graded
                  (SetLike.mul_mem_graded (fDividedPower_mem_rootGrading i r.1)
                    (f_mem_rootGrading j))
                  (fDividedPower_mem_rootGrading i (serreLength D i j - r.1)))⟩ :=
      fun r _ ↦ by
        have hr' : r.1 ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp r.2)
        have hdeg : r.1 • (-D.simpleRoot i) + (-D.simpleRoot j) +
            (serreLength D i j - r.1) • (-D.simpleRoot i) = deg := by
          rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr']
        rw [quantumDividedPower_of_rootGrading, quantumDividedPower_of_rootGrading,
          of_mul_of_eq D q _ _ rfl, of_mul_of_eq D q _ _ hdeg, ← DirectSum.of_smul]
        exact of_eq_of D q rfl rfl
    rw [sum_congr rfl hterm, ← map_sum,
      ← map_zero (DirectSum.of (fun β ↦ ↥(rootGrading D q β)) deg)]
    refine of_eq_of D q rfl ?_
    rw [Submodule.coe_sum, Submodule.coe_zero]
    exact (sum_attach (range (serreLength D i j + 1)) fun r ↦
      (-1 : K) ^ r •
        (fDividedPower D q i r * f D q j * fDividedPower D q i (serreLength D i j - r))).trans
      (serre_f (D := D) (q := q) hij)

private noncomputable def decomposeAlgHom :
    QuantizedEnvelopingAlgebra D q →ₐ[K] ⨁ β : D.rootLattice, rootGrading D q β :=
  lift (decomposeTuple D q)

private theorem decomposeAlgHom_generator (g : Generator ι Y) :
    decomposeAlgHom D q (generator D q g) =
      DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (generatorDegree D g)
        ⟨generator D q g, generator_mem_rootGrading g⟩ := by
  cases g with
  | e i =>
    simp only [decomposeAlgHom, generator_e, lift_e, decomposeTuple]
    exact of_eq_of D q (generatorDegree_e D i).symm rfl
  | f i =>
    simp only [decomposeAlgHom, generator_f, lift_f, decomposeTuple]
    exact of_eq_of D q (generatorDegree_f D i).symm rfl
  | k y =>
    simp only [decomposeAlgHom, generator_k, lift_k, decomposeTuple]
    exact of_eq_of D q (generatorDegree_k D y).symm rfl

private theorem coeAlgHom_comp_decomposeAlgHom :
    (DirectSum.coeAlgHom (rootGrading D q)).comp (decomposeAlgHom D q) =
      AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp [decomposeAlgHom, decomposeTuple]

private theorem decomposeAlgHom_prod (l : List (Generator ι Y)) :
    decomposeAlgHom D q (l.map (generator D q)).prod =
      DirectSum.of (fun β ↦ ↥(rootGrading D q β)) (l.map (generatorDegree D)).sum
        ⟨(l.map (generator D q)).prod, prod_mem_rootGrading l⟩ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, DirectSum.one_def]
    exact of_eq_of D q rfl rfl
  | cons g t ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, decomposeAlgHom_generator, ih,
      DirectSum.of_mul_of]
    exact of_eq_of D q rfl rfl

private theorem decomposeAlgHom_apply (β : D.rootLattice) (u : rootGrading D q β) :
    decomposeAlgHom D q (u : QuantizedEnvelopingAlgebra D q) =
      DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β u := by
  rcases u with ⟨u, hu⟩
  induction hu using Submodule.span_induction with
  | mem u hu =>
    rcases hu with ⟨l, rfl, rfl⟩
    exact decomposeAlgHom_prod D q l
  | zero =>
    rw [map_zero]
    exact (map_zero (DirectSum.of (fun γ ↦ ↥(rootGrading D q γ)) β)).symm
  | add a b _ _ ha hb =>
    rw [map_add, ha, hb, ← map_add]
    rfl
  | smul c a _ ha =>
    rw [map_smul, ha, ← DirectSum.of_smul]
    rfl

/-- The homogeneous submodules `rootGrading D q` form an internal direct sum decomposition of
`QuantizedEnvelopingAlgebra D q`. -/
theorem isInternal_rootGrading : DirectSum.IsInternal (rootGrading D q) := by
  let := GradedAlgebra.ofAlgHom (rootGrading D q) (decomposeAlgHom D q)
    (coeAlgHom_comp_decomposeAlgHom D q) (decomposeAlgHom_apply D q)
  exact DirectSum.Decomposition.isInternal (rootGrading D q)

noncomputable instance instGradedAlgebra : GradedAlgebra (rootGrading D q) :=
  (isInternal_rootGrading D q).gradedAlgebra

end GradedAlgebra

end TauCeti.QuantizedEnvelopingAlgebra
