/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

import Mathlib.Tactic

/-!
# Root-lattice grading on a quantized enveloping algebra

Every defining relation of `QuantizedEnvelopingAlgebra D q` is homogeneous when `Eᵢ` is assigned
degree `eᵢ ∈ ι →₀ ℤ`, `Fᵢ` is assigned degree `-eᵢ`, and every toral generator `K_y` is assigned
degree `0`. Consequently `QuantizedEnvelopingAlgebra D q` carries an internal `(ι →₀ ℤ)`-grading
for arbitrary `q : K` (including `q = 0` and roots of unity), without any finiteness hypothesis on
`ι` or freeness hypothesis on `X` and `Y`.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.generatorDegree`: the formal root-lattice degree in `ι →₀ ℤ`
  of a presentation generator.
* `TauCeti.QuantizedEnvelopingAlgebra.gradedPiece`: the `K`-submodule of elements of degree
  `c : ι →₀ ℤ`, spanned by generator words of total degree `c`.
* `TauCeti.QuantizedEnvelopingAlgebra.decomposeAlgHom`: the universal `K`-algebra homomorphism into
  `⨁ c, gradedPiece D q c`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.instGradedAlgebra`: `QuantizedEnvelopingAlgebra D q` is
  internally graded by `gradedPiece D q`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mul_mul_k_neg_of_mem_gradedPiece`: conjugating a
  homogeneous element of degree `c` by `K_y` scales it by `q^⟨∑ cᵢ αᵢ, y⟩`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §4.7.
-/

public section

open DirectSum

namespace TauCeti.QuantizedEnvelopingAlgebra

section Degree

variable {ι Y : Type*}

/-- The formal root-lattice degree in `ι →₀ ℤ` of a generator: `+eᵢ` on `Eᵢ`, `-eᵢ` on `Fᵢ`, and
`0` on every toral generator `K_y`. -/
noncomputable def generatorDegree : Generator ι Y → (ι →₀ ℤ)
  | .e i => Finsupp.single i 1
  | .f i => -Finsupp.single i 1
  | .k _ => 0

/-- `Eᵢ` has formal degree `Finsupp.single i 1`. -/
@[simp]
theorem generatorDegree_e (i : ι) :
    generatorDegree (.e i : Generator ι Y) = Finsupp.single i 1 :=
  (rfl)

/-- `Fᵢ` has formal degree `-Finsupp.single i 1`. -/
@[simp]
theorem generatorDegree_f (i : ι) :
    generatorDegree (.f i : Generator ι Y) = -Finsupp.single i 1 :=
  (rfl)

/-- Every toral generator `K_y` has formal degree `0`. -/
@[simp]
theorem generatorDegree_k (y : Y) :
    generatorDegree (.k y : Generator ι Y) = 0 :=
  (rfl)

end Degree

section Pieces

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- The homogeneous piece of `QuantizedEnvelopingAlgebra D q` of degree `c : ι →₀ ℤ`, spanned over
`K` by products of presentation generators whose degrees sum to `c`. -/
noncomputable def gradedPiece (D : CartanDatum ι X Y) (q : K) (c : ι →₀ ℤ) :
    Submodule K (QuantizedEnvelopingAlgebra D q) :=
  Submodule.span K
    {x | ∃ l : List (Generator ι Y),
      (l.map generatorDegree).sum = c ∧ (l.map (generator D q)).prod = x}

variable {D : CartanDatum ι X Y} {q : K}

/-- The multiplicative identity lies in degree `0`. -/
theorem one_mem_gradedPiece_zero : (1 : QuantizedEnvelopingAlgebra D q) ∈ gradedPiece D q 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

/-- Every presentation generator lies in the graded piece of its formal degree. -/
theorem generator_mem_gradedPiece (g : Generator ι Y) :
    generator D q g ∈ gradedPiece D q (generatorDegree g) :=
  Submodule.subset_span ⟨[g], by simp, by simp⟩

/-- `Eᵢ` lies in graded degree `Finsupp.single i 1`. -/
theorem e_mem_gradedPiece (i : ι) :
    e D q i ∈ gradedPiece D q (Finsupp.single i 1) := by
  simpa only [generator_e, generatorDegree_e] using
    generator_mem_gradedPiece (D := D) (q := q) (.e i)

/-- `Fᵢ` lies in graded degree `-Finsupp.single i 1`. -/
theorem f_mem_gradedPiece (i : ι) :
    f D q i ∈ gradedPiece D q (-Finsupp.single i 1) := by
  simpa only [generator_f, generatorDegree_f] using
    generator_mem_gradedPiece (D := D) (q := q) (.f i)

/-- Every toral generator `K_y` lies in graded degree `0`. -/
theorem k_mem_gradedPiece (y : Y) :
    k D q y ∈ gradedPiece D q 0 := by
  simpa only [generator_k, generatorDegree_k] using
    generator_mem_gradedPiece (D := D) (q := q) (.k y)

/-- `Kᵢ` lies in graded degree `0`. -/
theorem simpleK_mem_gradedPiece (i : ι) :
    simpleK D q i ∈ gradedPiece D q 0 := by
  rw [simpleK_def]
  exact k_mem_gradedPiece (D.simpleTorus i)

/-- `Kᵢ⁻¹` lies in graded degree `0`. -/
theorem simpleKInv_mem_gradedPiece (i : ι) :
    simpleKInv D q i ∈ gradedPiece D q 0 := by
  rw [simpleKInv_def]
  exact k_mem_gradedPiece (-D.simpleTorus i)

/-- Multiplication in `QuantizedEnvelopingAlgebra D q` adds degrees in `ι →₀ ℤ`. -/
theorem mul_mem_gradedPiece {c d : ι →₀ ℤ} {x y : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ gradedPiece D q c) (hy : y ∈ gradedPiece D q d) :
    x * y ∈ gradedPiece D q (c + d) := by
  have hle : gradedPiece D q c * gradedPiece D q d ≤ gradedPiece D q (c + d) := by
    rw [gradedPiece, gradedPiece, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l₁, rfl, rfl⟩, _, ⟨l₂, rfl, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨l₁ ++ l₂, by simp, by simp⟩
  exact hle (Submodule.mul_mem_mul hx hy)

/-- `gradedPiece D q` makes `QuantizedEnvelopingAlgebra D q` a `SetLike.GradedMonoid`. -/
instance instGradedMonoid (D : CartanDatum ι X Y) (q : K) :
    SetLike.GradedMonoid (gradedPiece D q) where
  one_mem := one_mem_gradedPiece_zero
  mul_mem _ _ _ _ := mul_mem_gradedPiece

/-- The `n`-th divided power `Eᵢ^(n)` has degree `n • Finsupp.single i 1`. -/
theorem quantumDividedPower_e_mem_gradedPiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n ∈
      gradedPiece D q (n • Finsupp.single i 1) := by
  rw [quantumDividedPower_def]
  exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded n (e_mem_gradedPiece i))

/-- The `n`-th divided power `Fᵢ^(n)` has degree `-(n • Finsupp.single i 1)`. -/
theorem quantumDividedPower_f_mem_gradedPiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n ∈
      gradedPiece D q (-(n • Finsupp.single i 1)) := by
  rw [quantumDividedPower_def, ← smul_neg]
  exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded n (f_mem_gradedPiece i))

private theorem k_mul_generator_mul_k_neg (y : Y) (g : Generator ι Y) :
    k D q y * generator D q g * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root (generatorDegree g)) y •
        generator D q g := by
  cases g with
  | e i => simp [k_mul_e_mul_k_neg]
  | f i => simp [k_mul_f_mul_k_neg]
  | k z =>
    simp only [generator_k, generatorDegree_k, map_zero, LinearMap.zero_apply, zpow_zero, one_smul]
    rw [← k_add, ← k_add, add_comm y z, add_neg_cancel_right]

private theorem k_mul_word_mul_k_neg (y : Y) (l : List (Generator ι Y)) :
    k D q y * (l.map (generator D q)).prod * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root (l.map generatorDegree).sum) y •
        (l.map (generator D q)).prod := by
  rcases eq_or_ne q 0 with rfl | hq
  · induction l with
    | nil => simp
    | cons g l ih =>
      cases g with
      | e i => simp
      | f i => simp
      | k z =>
        simp only [List.map_cons, List.prod_cons, generator_k, generatorDegree_k, List.sum_cons,
          zero_add]
        calc
          k D (0 : K) y * (k D (0 : K) z * (l.map (generator D (0 : K))).prod) *
              k D (0 : K) (-y) =
              k D (0 : K) z *
                (k D (0 : K) y * (l.map (generator D (0 : K))).prod * k D (0 : K) (-y)) := by
            rw [← mul_assoc (k D (0 : K) y), ← k_add, add_comm y z, k_add]
            simp only [mul_assoc]
          _ = (0 : K) ^
              D.pairing (Finsupp.linearCombination ℤ D.root (l.map generatorDegree).sum) y •
                (k D (0 : K) z * (l.map (generator D (0 : K))).prod) := by
            rw [ih, mul_smul_comm]
  · induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, LinearMap.add_apply]
      calc
        k D q y * (generator D q g * (l.map (generator D q)).prod) * k D q (-y) =
            (k D q y * generator D q g * k D q (-y)) *
              (k D q y * (l.map (generator D q)).prod * k D q (-y)) := by
          simp only [mul_assoc, k_neg_mul_k_mul]
        _ = q ^ (D.pairing (Finsupp.linearCombination ℤ D.root (generatorDegree g)) y +
              D.pairing (Finsupp.linearCombination ℤ D.root (l.map generatorDegree).sum) y) •
              (generator D q g * (l.map (generator D q)).prod) := by
          rw [k_mul_generator_mul_k_neg, ih, smul_mul_smul_comm, ← zpow_add₀ hq]

/-- Conjugating a homogeneous element `x ∈ gradedPiece D q c` by `K_y` multiplies it by
`q^⟨∑ cᵢ αᵢ, y⟩`. -/
theorem k_mul_mul_k_neg_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    k D q y * x * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • x := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, rfl, rfl⟩ := ha
    exact k_mul_word_mul_k_neg y l
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add, add_mul, ha, hb, smul_add]
  | smul r a _ ha =>
    rw [mul_smul_comm, smul_mul_assoc, ha, smul_comm]

/-- Commuting `K_y` past a homogeneous element `x ∈ gradedPiece D q c` multiplies by
`q^⟨∑ cᵢ αᵢ, y⟩`. -/
theorem k_mul_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    k D q y * x = q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • (x * k D q y) := by
  calc
    k D q y * x = (k D q y * x * k D q (-y)) * k D q y := by
      rw [mul_assoc, k_neg_mul_k, mul_one]
    _ = q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • (x * k D q y) := by
      rw [k_mul_mul_k_neg_of_mem_gradedPiece y hx, smul_mul_assoc]

private theorem serreTerm_mem_gradedPiece (u : K) (m r : ℕ)
    (hr : r ≤ m) {c d : ι →₀ ℤ} (x : gradedPiece D q c) (y : gradedPiece D q d) :
    (-1 : K) ^ r • (quantumDividedPower u x.1 r * y.1 * quantumDividedPower u x.1 (m - r)) ∈
      gradedPiece D q (m • c + d) := by
  rw [quantumDividedPower_def, quantumDividedPower_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : r • c + d + (m - r) • c = m • c + d := by
    rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr]
  exact hdeg ▸ mul_mem_gradedPiece
    (mul_mem_gradedPiece (Submodule.smul_mem _ _ (SetLike.pow_mem_graded r x.2)) y.2)
    (Submodule.smul_mem _ _ (SetLike.pow_mem_graded (m - r) x.2))

end Pieces

section GradedAlgebra

variable {ι X Y K : Type*} [DecidableEq ι] [AddCommGroup X] [AddCommGroup Y] [Field K]

private noncomputable abbrev ofGradedPiece {D : CartanDatum ι X Y} {q : K} (c : ι →₀ ℤ) :
    gradedPiece D q c →ₗ[K] ⨁ c', gradedPiece D q c' :=
  DirectSum.lof K (ι →₀ ℤ) (fun c' => gradedPiece D q c') c

private theorem ofGradedPiece_eq {D : CartanDatum ι X Y} {q : K} {c₁ c₂ : ι →₀ ℤ}
    {x : gradedPiece D q c₁} {y : gradedPiece D q c₂} (hc : c₁ = c₂)
    (hxy : (x : QuantizedEnvelopingAlgebra D q) = y) :
    ofGradedPiece c₁ x = ofGradedPiece c₂ y :=
  DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext hc hxy)

private theorem ofGradedPiece_mul {D : CartanDatum ι X Y} {q : K} {c d : ι →₀ ℤ}
    (x : gradedPiece D q c) (y : gradedPiece D q d) :
    ofGradedPiece c x * ofGradedPiece d y =
      ofGradedPiece (c + d) ⟨x.1 * y.1, mul_mem_gradedPiece x.2 y.2⟩ := by
  simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of]
  rfl

private theorem quantumSerre_ofGradedPiece {D : CartanDatum ι X Y} {q : K} (u : K) (m : ℕ)
    {c d : ι →₀ ℤ} (x : gradedPiece D q c) (y : gradedPiece D q d) :
    quantumSerre u m (ofGradedPiece c x) (ofGradedPiece d y) =
      ofGradedPiece (m • c + d)
        ⟨quantumSerre u m x.1 y.1, by
          rw [quantumSerre_def]
          exact Submodule.sum_mem _ fun r hr =>
            serreTerm_mem_gradedPiece u m r (Finset.mem_range_succ_iff.mp hr) x y⟩ := by
  rw [quantumSerre_def, ← Finset.sum_attach]
  have hterm : ∀ r : {r // r ∈ Finset.range (m + 1)},
      (-1 : K) ^ r.1 •
        (quantumDividedPower u (ofGradedPiece c x) r.1 * ofGradedPiece d y *
          quantumDividedPower u (ofGradedPiece c x) (m - r.1)) =
      ofGradedPiece (m • c + d)
        ⟨(-1 : K) ^ r.1 •
          (quantumDividedPower u x.1 r.1 * y.1 * quantumDividedPower u x.1 (m - r.1)),
          serreTerm_mem_gradedPiece u m r.1 (Finset.mem_range_succ_iff.mp r.2) x y⟩ := by
    intro r
    have hdp : ∀ n : ℕ,
        quantumDividedPower u (ofGradedPiece c x) n =
          ofGradedPiece (n • c) ⟨quantumDividedPower u x.1 n, by
            rw [quantumDividedPower_def]
            exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded n x.2)⟩ := by
      intro n
      simp only [quantumDividedPower_def, DirectSum.lof_eq_of, DirectSum.ofPow,
        ← DirectSum.of_smul]
      rfl
    rw [hdp r.1, hdp (m - r.1), ofGradedPiece_mul, ofGradedPiece_mul, ← LinearMap.map_smul]
    exact ofGradedPiece_eq
      (by rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp r.2)])
      rfl
  rw [Finset.sum_congr rfl (fun r _ => hterm r), ← map_sum]
  exact ofGradedPiece_eq rfl (by
    simp only [Submodule.coe_sum]
    rw [Finset.sum_attach _ (fun r =>
      (-1 : K) ^ r • (quantumDividedPower u x.1 r * y.1 * quantumDividedPower u x.1 (m - r))),
      ← quantumSerre_def])

/-- The universal `K`-algebra homomorphism decomposing elements of `QuantizedEnvelopingAlgebra D q`
into their `(ι →₀ ℤ)`-graded pieces. -/
noncomputable def decomposeAlgHom (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] ⨁ c, gradedPiece D q c :=
  lift
    { e i := ofGradedPiece (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩
      f i := ofGradedPiece (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩
      k y := ofGradedPiece 0 ⟨k D q y, k_mem_gradedPiece y⟩
      k_zero := by
        simp only [DirectSum.lof_eq_of, DirectSum.one_def]
        exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl k_zero)
      k_add y z := by
        rw [ofGradedPiece_mul]
        exact ofGradedPiece_eq (zero_add (0 : ι →₀ ℤ)).symm (k_add y z)
      k_mul_e i y := by
        rw [ofGradedPiece_mul, ofGradedPiece_mul, ← map_smul (ofGradedPiece _)]
        exact ofGradedPiece_eq ((zero_add _).trans (add_zero _).symm) (k_mul_e i y)
      k_mul_f i y := by
        rw [ofGradedPiece_mul, ofGradedPiece_mul, ← map_smul (ofGradedPiece _)]
        exact ofGradedPiece_eq ((zero_add _).trans (add_zero _).symm) (k_mul_f i y)
      commutator_self i := by
        have h1 : ofGradedPiece (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩ *
            ofGradedPiece (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩ =
            ofGradedPiece 0 ⟨e D q i * f D q i,
              (add_neg_cancel (Finsupp.single i (1 : ℤ))) ▸
                mul_mem_gradedPiece (e_mem_gradedPiece i) (f_mem_gradedPiece i)⟩ :=
          (ofGradedPiece_mul _ _).trans (ofGradedPiece_eq (add_neg_cancel _) rfl)
        have h2 : ofGradedPiece (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩ *
            ofGradedPiece (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩ =
            ofGradedPiece 0 ⟨f D q i * e D q i,
              (neg_add_cancel (Finsupp.single i (1 : ℤ))) ▸
                mul_mem_gradedPiece (f_mem_gradedPiece i) (e_mem_gradedPiece i)⟩ :=
          (ofGradedPiece_mul _ _).trans (ofGradedPiece_eq (neg_add_cancel _) rfl)
        rw [h1, h2, ← map_sub (ofGradedPiece 0), ← map_sub (ofGradedPiece 0),
          ← map_smul (ofGradedPiece 0)]
        exact ofGradedPiece_eq rfl (by
          simpa only [Submodule.coe_sub, SetLike.val_smul, simpleK_def, simpleKInv_def] using
            e_mul_f_sub_f_mul_e_self (D := D) (q := q) i)
      commutator_ne {i j} hij := by
        have h2 : ofGradedPiece (-Finsupp.single j 1) ⟨f D q j, f_mem_gradedPiece j⟩ *
            ofGradedPiece (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩ =
            ofGradedPiece (Finsupp.single i 1 + -Finsupp.single j 1)
              ⟨f D q j * e D q i,
                (add_comm (-Finsupp.single j (1 : ℤ)) _) ▸
                  mul_mem_gradedPiece (f_mem_gradedPiece j) (e_mem_gradedPiece i)⟩ :=
          (ofGradedPiece_mul _ _).trans (ofGradedPiece_eq (add_comm _ _) rfl)
        rw [ofGradedPiece_mul, h2, sub_eq_zero]
        exact ofGradedPiece_eq rfl (e_mul_f_of_ne hij)
      serre_e {i j} hij := by
        rw [quantumSerre_ofGradedPiece]
        exact (ofGradedPiece_eq rfl (serre_e_eq_zero hij)).trans (map_zero _)
      serre_f {i j} hij := by
        rw [quantumSerre_ofGradedPiece]
        exact (ofGradedPiece_eq rfl (serre_f_eq_zero hij)).trans (map_zero _) }

private theorem decomposeAlgHom_generator {D : CartanDatum ι X Y} {q : K} (g : Generator ι Y) :
    decomposeAlgHom D q (generator D q g) =
      DirectSum.of (fun c => gradedPiece D q c) (generatorDegree g)
        ⟨generator D q g, generator_mem_gradedPiece g⟩ := by
  cases g with
  | e i =>
    simp only [generator_e, decomposeAlgHom, lift_e, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (Sigma.subtype_ext (generatorDegree_e (Y := Y) i).symm rfl)
  | f i =>
    simp only [generator_f, decomposeAlgHom, lift_f, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (Sigma.subtype_ext (generatorDegree_f (Y := Y) i).symm rfl)
  | k y =>
    simp only [generator_k, decomposeAlgHom, lift_k, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (Sigma.subtype_ext (generatorDegree_k (ι := ι) y).symm rfl)

private theorem decomposeAlgHom_word {D : CartanDatum ι X Y} {q : K}
    (l : List (Generator ι Y)) :
    decomposeAlgHom D q (l.map (generator D q)).prod =
      DirectSum.of (fun c => gradedPiece D q c) (l.map generatorDegree).sum
        ⟨(l.map (generator D q)).prod, Submodule.subset_span ⟨l, rfl, rfl⟩⟩ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, DirectSum.one_def]
    rfl
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, decomposeAlgHom_generator, ih,
      DirectSum.of_mul_of]
    rfl

/-- `decomposeAlgHom D q` maps every element `x ∈ gradedPiece D q c` to its canonical inclusion in
degree `c`. -/
theorem decomposeAlgHom_apply_of_mem {D : CartanDatum ι X Y} {q : K} {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    decomposeAlgHom D q x = DirectSum.of (fun c' => gradedPiece D q c') c ⟨x, hx⟩ := by
  have aux : ∀ {y : QuantizedEnvelopingAlgebra D q}, y ∈ gradedPiece D q c →
      ∀ h : y ∈ gradedPiece D q c,
        decomposeAlgHom D q y = DirectSum.of (fun c' => gradedPiece D q c') c ⟨y, h⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl, rfl⟩ := ha
      exact fun _ => decomposeAlgHom_word l
    | zero => exact fun _ => (map_zero _).trans (map_zero _).symm
    | add a b ha hb iha ihb =>
      intro h
      rw [map_add, iha ha, ihb hb, ← map_add]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl rfl)
    | smul r a ha ih =>
      intro h
      rw [map_smul, ih ha, ← DirectSum.of_smul]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl rfl)
  exact aux hx hx

/-- `QuantizedEnvelopingAlgebra D q` is internally `(ι →₀ ℤ)`-graded by `gradedPiece D q`. -/
noncomputable instance instGradedAlgebra (D : CartanDatum ι X Y) (q : K) :
    GradedAlgebra (gradedPiece D q) :=
  GradedAlgebra.ofAlgHom (gradedPiece D q) (decomposeAlgHom D q)
    (by
      ext i
      · simp [decomposeAlgHom, DirectSum.lof_eq_of]
      · simp [decomposeAlgHom, DirectSum.lof_eq_of]
      · simp [decomposeAlgHom, DirectSum.lof_eq_of])
    (fun c x => decomposeAlgHom_apply_of_mem x.2)

end GradedAlgebra

end TauCeti.QuantizedEnvelopingAlgebra
