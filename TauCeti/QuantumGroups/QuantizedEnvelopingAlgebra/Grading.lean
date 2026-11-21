/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

/-!
# Root-lattice grading on a quantized enveloping algebra

Assigning `Eᵢ` degree `eᵢ ∈ ι →₀ ℤ`, `Fᵢ` degree `-eᵢ`, and `K_y` degree `0` equips
`QuantizedEnvelopingAlgebra D q` with an internal `(ι →₀ ℤ)`-grading (`instGradedAlgebra`) for
arbitrary `q : K`, without finiteness assumptions on `ι` or freeness assumptions on `X` and `Y`.
Conjugating `x ∈ gradedPiece D q c` by `K_y` scales it by `q^⟨∑ cᵢ αᵢ, y⟩`
(`k_mul_mul_k_neg_of_mem_gradedPiece`).

## References

* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, American Mathematical Society, 1996, §4.7.
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
@[simp] theorem generatorDegree_e (i : ι) :
    generatorDegree (.e i : Generator ι Y) = Finsupp.single i 1 := (rfl)
@[simp] theorem generatorDegree_f (i : ι) :
    generatorDegree (.f i : Generator ι Y) = -Finsupp.single i 1 := (rfl)
@[simp] theorem generatorDegree_k (y : Y) : generatorDegree (.k y : Generator ι Y) = 0 := (rfl)

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
theorem gradedPiece_def (D : CartanDatum ι X Y) (q : K) (c : ι →₀ ℤ) :
    gradedPiece D q c = Submodule.span K
      {x | ∃ l : List (Generator ι Y),
        (l.map generatorDegree).sum = c ∧ (l.map (generator D q)).prod = x} := (rfl)

variable {D : CartanDatum ι X Y} {q : K}

theorem word_mem_gradedPiece {c : ι →₀ ℤ} {l : List (Generator ι Y)}
    (hl : (l.map generatorDegree).sum = c) :
    (l.map (generator D q)).prod ∈ gradedPiece D q c :=
  Submodule.subset_span ⟨l, hl, rfl⟩
theorem gradedPiece_le_iff (c : ι →₀ ℤ) (p : Submodule K (QuantizedEnvelopingAlgebra D q)) :
    gradedPiece D q c ≤ p ↔
      ∀ l : List (Generator ι Y), (l.map generatorDegree).sum = c →
        (l.map (generator D q)).prod ∈ p := by
  rw [gradedPiece_def, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, by rintro h _ ⟨l, hl, rfl⟩; exact h l hl⟩

/-- Structural induction on `gradedPiece D q c` from generator words of degree `c` under zero,
addition, and `K`-scalar multiplication. -/
@[elab_as_elim]
theorem gradedPiece_induction {c : ι →₀ ℤ} {x : QuantizedEnvelopingAlgebra D q}
    {P : (x : QuantizedEnvelopingAlgebra D q) → x ∈ gradedPiece D q c → Prop}
    (hx : x ∈ gradedPiece D q c)
    (word : ∀ l : List (Generator ι Y), (hl : (l.map generatorDegree).sum = c) →
      P (l.map (generator D q)).prod (word_mem_gradedPiece hl))
    (zero : P 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (smul : ∀ (a : K) x hx, P x hx → P (a • x) (Submodule.smul_mem _ a hx)) : P x hx :=
  Submodule.span_induction (by rintro _ ⟨l, hl, rfl⟩; exact word l hl) zero add smul hx

theorem one_mem_gradedPiece_zero : (1 : QuantizedEnvelopingAlgebra D q) ∈ gradedPiece D q 0 :=
  word_mem_gradedPiece (l := []) rfl
theorem generator_mem_gradedPiece (g : Generator ι Y) :
    generator D q g ∈ gradedPiece D q (generatorDegree g) := by
  simpa using word_mem_gradedPiece (D := D) (q := q) (l := [g]) (add_zero _)
theorem e_mem_gradedPiece (i : ι) : e D q i ∈ gradedPiece D q (Finsupp.single i 1) := by
  simpa using generator_mem_gradedPiece (D := D) (q := q) (.e i)
theorem f_mem_gradedPiece (i : ι) : f D q i ∈ gradedPiece D q (-Finsupp.single i 1) := by
  simpa using generator_mem_gradedPiece (D := D) (q := q) (.f i)
theorem k_mem_gradedPiece (y : Y) : k D q y ∈ gradedPiece D q 0 := by
  simpa using generator_mem_gradedPiece (D := D) (q := q) (.k y)
theorem simpleK_mem_gradedPiece (i : ι) : simpleK D q i ∈ gradedPiece D q 0 :=
  simpleK_def D q i ▸ k_mem_gradedPiece (D.simpleTorus i)
theorem simpleKInv_mem_gradedPiece (i : ι) : simpleKInv D q i ∈ gradedPiece D q 0 :=
  simpleKInv_def D q i ▸ k_mem_gradedPiece (-D.simpleTorus i)
theorem mul_mem_gradedPiece {c d : ι →₀ ℤ} {x y : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ gradedPiece D q c) (hy : y ∈ gradedPiece D q d) :
    x * y ∈ gradedPiece D q (c + d) := by
  have hle : gradedPiece D q c * gradedPiece D q d ≤ gradedPiece D q (c + d) := by
    rw [gradedPiece_def, gradedPiece_def, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l₁, rfl, rfl⟩, _, ⟨l₂, rfl, rfl⟩, rfl⟩
    simpa using word_mem_gradedPiece (D := D) (q := q) (l := l₁ ++ l₂) (by simp)
  exact hle (Submodule.mul_mem_mul hx hy)

/-- Multiplication respects `gradedPiece D q`, giving a graded monoid structure for all `q : K`. -/
instance instGradedMonoid (D : CartanDatum ι X Y) (q : K) :
    SetLike.GradedMonoid (gradedPiece D q) where
  one_mem := one_mem_gradedPiece_zero
  mul_mem _ _ _ _ := mul_mem_gradedPiece

theorem quantumDividedPower_mem_gradedPiece (u : K) {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) (n : ℕ) :
    quantumDividedPower u x n ∈ gradedPiece D q (n • c) := by
  rw [quantumDividedPower_def]; exact Submodule.smul_mem _ _ (SetLike.pow_mem_graded n hx)
theorem quantumDividedPower_e_mem_gradedPiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n ∈
      gradedPiece D q (n • Finsupp.single i 1) :=
  quantumDividedPower_mem_gradedPiece _ (e_mem_gradedPiece i) n
theorem quantumDividedPower_f_mem_gradedPiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n ∈
      gradedPiece D q (-(n • Finsupp.single i 1)) := by
  rw [← smul_neg]; exact quantumDividedPower_mem_gradedPiece _ (f_mem_gradedPiece i) n

private theorem k_mul_generator_mul_k_neg (y : Y) (g : Generator ι Y) :
    k D q y * generator D q g * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root (generatorDegree g)) y •
        generator D q g := by
  cases g with
  | e i => simp [k_mul_e_mul_k_neg]
  | f i => simp [k_mul_f_mul_k_neg]
  | k z => simp [add_right_comm y z (-y)]

private theorem k_mul_word_mul_k_neg (y : Y) (l : List (Generator ι Y)) :
    k D q y * (l.map (generator D q)).prod * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root (l.map generatorDegree).sum) y •
        (l.map (generator D q)).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rcases eq_or_ne q 0 with rfl | hq
    · cases g with
      | e _ | f _ => simp
      | k z =>
        simp only [List.map_cons, List.prod_cons, generator_k, generatorDegree_k, List.sum_cons,
          zero_add]
        rw [← mul_assoc (k D (0 : K) y), k_mul_k, add_comm y z, ← k_mul_k,
          mul_assoc (k D (0 : K) z), mul_assoc (k D (0 : K) z), ih, mul_smul_comm]
    · simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, LinearMap.add_apply]
      have h : k D q y * (generator D q g * (l.map (generator D q)).prod) * k D q (-y) =
          (k D q y * generator D q g * k D q (-y)) *
            (k D q y * (l.map (generator D q)).prod * k D q (-y)) := by
        simp only [mul_assoc, ← mul_assoc (k D q (-y)), k_neg_mul_k, one_mul]
      rw [h, k_mul_generator_mul_k_neg, ih, smul_mul_smul_comm, ← zpow_add₀ hq]

/-- Conjugating `x ∈ gradedPiece D q c` by `K_y` multiplies it by `q^⟨∑ cᵢ αᵢ, y⟩`. -/
theorem k_mul_mul_k_neg_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    k D q y * x * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • x := by
  induction hx using gradedPiece_induction with
  | word l hl => simpa only [hl] using k_mul_word_mul_k_neg y l
  | zero => simp
  | add _ _ _ _ ha hb => rw [mul_add, add_mul, ha, hb, smul_add]
  | smul _ _ _ ha => rw [mul_smul_comm, smul_mul_assoc, ha, smul_comm]
theorem k_mul_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    k D q y * x = q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • (x * k D q y) := by
  rw [← mul_one (k D q y * x), ← k_neg_mul_k D q y, ← mul_assoc,
    k_mul_mul_k_neg_of_mem_gradedPiece y hx, smul_mul_assoc]
theorem mul_k_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    x * k D q y =
      q ^ (-D.pairing (Finsupp.linearCombination ℤ D.root c) y) • (k D q y * x) := by
  have h := k_mul_mul_k_neg_of_mem_gradedPiece (-y) hx
  rw [neg_neg, map_neg] at h
  rw [← one_mul (x * k D q y), ← k_mul_k_neg D q y, mul_assoc (k D q y),
    ← mul_assoc (k D q (-y)), h, mul_smul_comm]

private theorem serreTerm_mem_gradedPiece (u : K) (m r : ℕ) (hr : r ≤ m) {c d : ι →₀ ℤ}
    (x : gradedPiece D q c) (y : gradedPiece D q d) :
    (-1 : K) ^ r • (quantumDividedPower u x.val r * y.val * quantumDividedPower u x.val (m - r)) ∈
      gradedPiece D q (m • c + d) := by
  have hdeg : r • c + d + (m - r) • c = m • c + d := by
    rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr]
  exact Submodule.smul_mem _ _ <| hdeg ▸ mul_mem_gradedPiece
    (mul_mem_gradedPiece (quantumDividedPower_mem_gradedPiece u x.property r) y.property)
    (quantumDividedPower_mem_gradedPiece u x.property (m - r))

end Pieces

section GradedAlgebra

variable {ι X Y K : Type*} [DecidableEq ι] [AddCommGroup X] [AddCommGroup Y] [Field K]
  {D : CartanDatum ι X Y} {q : K}

private noncomputable abbrev ofGradedPiece (c : ι →₀ ℤ) :
    gradedPiece D q c →ₗ[K] ⨁ c', gradedPiece D q c' :=
  lof K (ι →₀ ℤ) (fun c' => gradedPiece D q c') c
private theorem ofGradedPiece_eq {c₁ c₂ : ι →₀ ℤ} {x : gradedPiece D q c₁} {y : gradedPiece D q c₂}
    (hc : c₁ = c₂) (hxy : (x : QuantizedEnvelopingAlgebra D q) = y) :
    ofGradedPiece c₁ x = ofGradedPiece c₂ y :=
  of_eq_of_gradedMonoid_eq (Sigma.subtype_ext hc hxy)
private theorem ofGradedPiece_mul {c d : ι →₀ ℤ} (x : gradedPiece D q c) (y : gradedPiece D q d) :
    ofGradedPiece c x * ofGradedPiece d y =
      ofGradedPiece (c + d) ⟨x.val * y.val, mul_mem_gradedPiece x.property y.property⟩ := by
  simp only [lof_eq_of, of_mul_of]; rfl
private theorem ofGradedPiece_mul_eq {c d m : ι →₀ ℤ}
    (x : gradedPiece D q c) (y : gradedPiece D q d) (h : c + d = m) :
    ofGradedPiece c x * ofGradedPiece d y =
      ofGradedPiece m ⟨x.val * y.val, h ▸ mul_mem_gradedPiece x.property y.property⟩ :=
  (ofGradedPiece_mul x y).trans (ofGradedPiece_eq h rfl)

private theorem serreSum_ofGradedPiece (D : CartanDatum ι X Y) (q : K) (i j : ι)
    {c : ι → (ι →₀ ℤ)} (x : ∀ l, gradedPiece D q (c l)) :
    serreSum D q (fun l => ofGradedPiece (c l) (x l)) i j =
      ofGradedPiece (D.serreLength i j • c i + c j)
        ⟨serreSum D q (fun l => (x l).val) i j, by
          rw [serreSum_def]
          exact Submodule.sum_mem _ fun r hr =>
            serreTerm_mem_gradedPiece (q ^ D.symmetrizer i) (D.serreLength i j) r
              (Finset.mem_range_succ_iff.mp hr) (x i) (x j)⟩ := by
  set u := q ^ D.symmetrizer i
  set m := D.serreLength i j
  have hdp (n : ℕ) : quantumDividedPower u (ofGradedPiece (c i) (x i)) n =
      ofGradedPiece (n • c i)
        ⟨quantumDividedPower u (x i).val n,
          quantumDividedPower_mem_gradedPiece u (x i).property n⟩ := by
    simp only [quantumDividedPower_def, lof_eq_of, ofPow, ← of_smul]; rfl
  have hterm (r : {r // r ∈ Finset.range (m + 1)}) :
      (-1 : K) ^ r.val • (quantumDividedPower u (ofGradedPiece (c i) (x i)) r.val *
        ofGradedPiece (c j) (x j) *
        quantumDividedPower u (ofGradedPiece (c i) (x i)) (m - r.val)) =
      ofGradedPiece (m • c i + c j) ⟨(-1 : K) ^ r.val •
        (quantumDividedPower u (x i).val r.val * (x j).val *
          quantumDividedPower u (x i).val (m - r.val)),
        serreTerm_mem_gradedPiece u m r.val (Finset.mem_range_succ_iff.mp r.property)
          (x i) (x j)⟩ := by
    rw [hdp r.val, hdp (m - r.val), ofGradedPiece_mul, ofGradedPiece_mul, ← LinearMap.map_smul]
    exact ofGradedPiece_eq
      (by rw [add_right_comm, ← add_nsmul,
        Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp r.property)])
      rfl
  rw [serreSum_def, ← Finset.sum_attach, Finset.sum_congr rfl fun r _ => hterm r, ← map_sum]
  exact ofGradedPiece_eq rfl (by
    simp only [Submodule.coe_sum, serreSum_def]
    exact Finset.sum_attach _ fun r =>
      (-1 : K) ^ r • (quantumDividedPower u (x i).val r * (x j).val *
        quantumDividedPower u (x i).val (m - r)))

private noncomputable def decomposeAlgHom (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] ⨁ c, gradedPiece D q c :=
  lift
    { e i := ofGradedPiece (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩
      f i := ofGradedPiece (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩
      k y := ofGradedPiece 0 ⟨k D q y, k_mem_gradedPiece y⟩
      k_zero := by
        simp only [lof_eq_of, one_def]
        exact of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl (k_zero D q))
      k_mul_k y z := by
        rw [ofGradedPiece_mul]
        exact ofGradedPiece_eq (zero_add 0) (k_mul_k D q y z)
      conjugate_e y i := by
        rw [ofGradedPiece_mul, ofGradedPiece_mul, ← map_smul (ofGradedPiece _)]
        exact ofGradedPiece_eq (by simp) (k_mul_e_mul_k_neg D q y i)
      conjugate_f y i := by
        rw [ofGradedPiece_mul, ofGradedPiece_mul, ← map_smul (ofGradedPiece _)]
        exact ofGradedPiece_eq (by simp) (k_mul_f_mul_k_neg D q y i)
      commutator_self i := by
        rw [ofGradedPiece_mul_eq _ _ (add_neg_cancel _),
          ofGradedPiece_mul_eq _ _ (neg_add_cancel _), ← map_sub (ofGradedPiece 0),
          ← map_sub (ofGradedPiece 0), ← map_smul (ofGradedPiece 0)]
        exact ofGradedPiece_eq rfl (by
          simpa only [Submodule.coe_sub, SetLike.val_smul, simpleK_def, simpleKInv_def] using
            e_mul_f_sub_f_mul_e_self D q i)
      commutator_ne {i j} hij := by
        rw [ofGradedPiece_mul, ofGradedPiece_mul_eq _ _ (add_comm _ _), sub_eq_zero]
        exact ofGradedPiece_eq rfl (commute_e_f D q hij).eq
      serre_e {i j} hij := (serreSum_ofGradedPiece D q i j _).trans <|
        (ofGradedPiece_eq rfl (serreE_eq_zero D q hij)).trans (map_zero _)
      serre_f {i j} hij := (serreSum_ofGradedPiece D q i j _).trans <|
        (ofGradedPiece_eq rfl (serreF_eq_zero D q hij)).trans (map_zero _) }

private theorem decomposeAlgHom_word {D : CartanDatum ι X Y} {q : K} (l : List (Generator ι Y)) :
    decomposeAlgHom D q (l.map (generator D q)).prod =
      of (fun c => gradedPiece D q c) (l.map generatorDegree).sum
        ⟨(l.map (generator D q)).prod, word_mem_gradedPiece rfl⟩ := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, one_def]; rfl
  | cons g l ih =>
    have hg : decomposeAlgHom D q (generator D q g) =
        of (fun c => gradedPiece D q c) (generatorDegree g)
          ⟨generator D q g, generator_mem_gradedPiece g⟩ := by
      cases g <;> simp only [generator_e, generator_f, generator_k, decomposeAlgHom, lift_e, lift_f,
        lift_k, lof_eq_of] <;> exact of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl rfl)
    simp only [List.map_cons, List.prod_cons, map_mul, hg, ih, of_mul_of]; rfl

private theorem decomposeAlgHom_apply_of_mem {D : CartanDatum ι X Y} {q : K} {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    decomposeAlgHom D q x = of (fun c' => gradedPiece D q c') c ⟨x, hx⟩ := by
  induction hx using gradedPiece_induction with
  | word l hl =>
    exact (decomposeAlgHom_word l).trans (of_eq_of_gradedMonoid_eq (Sigma.subtype_ext hl rfl))
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add _ _ _ _ iha ihb => rw [map_add, iha, ihb, ← map_add]; rfl
  | smul _ _ _ ih => rw [map_smul, ih, ← of_smul]; rfl

/-- `gradedPiece D q` forms an internal direct sum for every `q : K` (given `[DecidableEq ι]`),
giving unique finite homogeneous decompositions and a genuine `(ι →₀ ℤ)`-grading. -/
theorem isInternal_gradedPiece (D : CartanDatum ι X Y) (q : K) : IsInternal (gradedPiece D q) := by
  let := GradedAlgebra.ofAlgHom (gradedPiece D q) (decomposeAlgHom D q)
    (by ext <;> simp [decomposeAlgHom, lof_eq_of])
    (fun _ x => decomposeAlgHom_apply_of_mem x.property)
  exact Decomposition.isInternal (gradedPiece D q)

/-- `QuantizedEnvelopingAlgebra D q` is internally `(ι →₀ ℤ)`-graded by `gradedPiece D q`. -/
noncomputable instance instGradedAlgebra (D : CartanDatum ι X Y) (q : K) :
    GradedAlgebra (gradedPiece D q) :=
  (isInternal_gradedPiece D q).gradedAlgebra
@[simp] theorem decompose_e (i : ι) :
    decompose (gradedPiece D q) (e D q i) =
      of (fun c => gradedPiece D q c) (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (e_mem_gradedPiece i)
@[simp] theorem decompose_f (i : ι) :
    decompose (gradedPiece D q) (f D q i) =
      of (fun c => gradedPiece D q c) (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (f_mem_gradedPiece i)
@[simp] theorem decompose_k (y : Y) :
    decompose (gradedPiece D q) (k D q y) =
      of (fun c => gradedPiece D q c) 0 ⟨k D q y, k_mem_gradedPiece y⟩ :=
  decompose_of_mem (gradedPiece D q) (k_mem_gradedPiece y)
@[simp] theorem decompose_simpleK (i : ι) :
    decompose (gradedPiece D q) (simpleK D q i) =
      of (fun c => gradedPiece D q c) 0 ⟨simpleK D q i, simpleK_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (simpleK_mem_gradedPiece i)
@[simp] theorem decompose_simpleKInv (i : ι) :
    decompose (gradedPiece D q) (simpleKInv D q i) =
      of (fun c => gradedPiece D q c) 0 ⟨simpleKInv D q i, simpleKInv_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (simpleKInv_mem_gradedPiece i)

end GradedAlgebra
end TauCeti.QuantizedEnvelopingAlgebra
