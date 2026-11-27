/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Antipode

import Mathlib.Tactic.Abel

/-!
# Root-lattice grading on the Drinfeld–Jimbo quantized enveloping algebra

Assigning weight `αᵢ ∈ X` to `Eᵢ`, `-αᵢ` to `Fᵢ`, and `0` to `K_y` makes all defining relations of
`TauCeti.QuantizedEnvelopingAlgebra D q` homogeneous. For every `β ∈ X`, we define the homogeneous
subspace `grade D q β`, provide its characteristic description `grade_def` and elimination principle
`grade_induction`, prove vanishing outside `D.rootLattice`, establish toral conjugation
`K_y x K_(-y) = q ^ ⟨β, y⟩ • x` on `grade D q β` and compatibility with `rescale`,
`chevalleyInvolution`, and `antipodeLinearEquiv`, and equip `QuantizedEnvelopingAlgebra D q` with
its `GradedAlgebra (grade D q)` structure under `[DecidableEq X]`.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.generatorWeight`: generator weights in `X` (`αᵢ` on `Eᵢ`,
  `-αᵢ` on `Fᵢ`, `0` on `K_y`), valued in `D.rootLattice`.
* `TauCeti.QuantizedEnvelopingAlgebra.grade`, `grade_def`, `grade_induction`: the `β`-homogeneous
  `K`-submodule of `QuantizedEnvelopingAlgebra D q` and its word-span elimination principle.
* `TauCeti.QuantizedEnvelopingAlgebra.grade_eq_bot_of_notMem_rootLattice`: every homogeneous piece
  outside `D.rootLattice` is `⊥`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mul_mul_k_neg_of_mem_grade`, `k_mul_of_mem_grade`: toral
  conjugation `K_y x K_(-y) = q ^ ⟨β, y⟩ • x` on `grade D q β`.
* `TauCeti.QuantizedEnvelopingAlgebra.rescale_mem_grade`, `chevalleyInvolution_mem_grade`,
  `antipodeLinearEquiv_mem_grade`: interaction of symmetries and the antipode with the grading.
* `TauCeti.QuantizedEnvelopingAlgebra.instGradedAlgebra`: `GradedAlgebra (grade D q)` instance.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.2.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996, §4.7.
-/

public section

open Finset
open scoped DirectSum

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- Weight in `X` of a presentation symbol: `αᵢ` on `Eᵢ`, `-αᵢ` on `Fᵢ`, and `0` on `K_y`. -/
def generatorWeight (D : CartanDatum ι X Y) : Generator ι Y → X
  | .e i => D.root i
  | .f i => -D.root i
  | .k _ => 0

@[simp] theorem generatorWeight_e (D : CartanDatum ι X Y) (i : ι) :
    generatorWeight D (.e i) = D.root i := (rfl)
@[simp] theorem generatorWeight_f (D : CartanDatum ι X Y) (i : ι) :
    generatorWeight D (.f i) = -D.root i := (rfl)
@[simp] theorem generatorWeight_k (D : CartanDatum ι X Y) (y : Y) :
    generatorWeight D (.k y) = 0 := (rfl)

/-- Every generator weight belongs to `D.rootLattice`. -/
theorem generatorWeight_mem_rootLattice (D : CartanDatum ι X Y) (g : Generator ι Y) :
    generatorWeight D g ∈ D.rootLattice := by
  cases g with
  | e i => exact D.root_mem_rootLattice i
  | f i => exact D.rootLattice.neg_mem (D.root_mem_rootLattice i)
  | k _ => exact D.rootLattice.zero_mem

noncomputable section

/-- The `β`-homogeneous `K`-subspace of `QuantizedEnvelopingAlgebra D q`, spanned by products of
generator words whose weights sum to `β`. -/
def grade (D : CartanDatum ι X Y) (q : K) (β : X) : Submodule K (QuantizedEnvelopingAlgebra D q) :=
  Submodule.span K { x | ∃ w : List (Generator ι Y),
    (w.map (generatorWeight D)).sum = β ∧ (w.map (generator D q)).prod = x }

/-- Characteristic description of `grade D q β` as the `K`-span of generator words of total weight
`β`. -/
theorem grade_def (D : CartanDatum ι X Y) (q : K) (β : X) :
    grade D q β = Submodule.span K { x | ∃ w : List (Generator ι Y),
      (w.map (generatorWeight D)).sum = β ∧ (w.map (generator D q)).prod = x } := (rfl)

section Homogeneous

variable {D : CartanDatum ι X Y} {q : K}

/-- The product of a list of generators belongs to the homogeneous piece of its total weight. -/
theorem word_prod_mem_grade (w : List (Generator ι Y)) :
    (w.map (generator D q)).prod ∈ grade D q (w.map (generatorWeight D)).sum := by
  rw [grade_def]
  exact Submodule.subset_span ⟨w, rfl, rfl⟩

/-- Elimination principle for `grade D q β`: a predicate holding on generator words of total weight
`β` and on `0`, and closed under addition and `K`-scalar multiplication, holds on every element of
`grade D q β`. -/
@[elab_as_elim]
theorem grade_induction {β : X}
    {motive : (x : QuantizedEnvelopingAlgebra D q) → x ∈ grade D q β → Prop}
    (word : ∀ w : List (Generator ι Y), (hw : (w.map (generatorWeight D)).sum = β) →
      motive (w.map (generator D q)).prod (hw ▸ word_prod_mem_grade w))
    (zero : motive 0 (grade D q β).zero_mem)
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) ((grade D q β).add_mem hx hy))
    (smul : ∀ (c : K) x hx, motive x hx → motive (c • x) ((grade D q β).smul_mem c hx))
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ grade D q β) : motive x hx := by
  refine Submodule.span_induction ?_ zero add smul hx
  rintro _ ⟨w, rfl, rfl⟩
  exact word w rfl

theorem one_mem_grade_zero : (1 : QuantizedEnvelopingAlgebra D q) ∈ grade D q 0 :=
  word_prod_mem_grade (D := D) (q := q) []

theorem generator_mem_grade (g : Generator ι Y) :
    generator D q g ∈ grade D q (generatorWeight D g) := by
  simpa using word_prod_mem_grade (D := D) (q := q) [g]

theorem e_mem_grade (i : ι) : e D q i ∈ grade D q (D.root i) := by
  simpa using generator_mem_grade (D := D) (q := q) (.e i)
theorem f_mem_grade (i : ι) : f D q i ∈ grade D q (-D.root i) := by
  simpa using generator_mem_grade (D := D) (q := q) (.f i)
theorem k_mem_grade (y : Y) : k D q y ∈ grade D q 0 := by
  simpa using generator_mem_grade (D := D) (q := q) (.k y)
theorem simpleK_mem_grade (i : ι) : simpleK D q i ∈ grade D q 0 := by
  rw [simpleK_def]; exact k_mem_grade (D.simpleTorus i)
theorem simpleKInv_mem_grade (i : ι) : simpleKInv D q i ∈ grade D q 0 := by
  rw [simpleKInv_def]; exact k_mem_grade (-D.simpleTorus i)

/-- Multiplication maps `grade D q α × grade D q β` into `grade D q (α + β)`. -/
theorem grade_mul_le (α β : X) : grade D q α * grade D q β ≤ grade D q (α + β) := by
  rw [grade_def, grade_def, grade_def, Submodule.span_mul_span, Submodule.span_le,
    Set.mul_subset_iff]
  rintro _ ⟨w₁, rfl, rfl⟩ _ ⟨w₂, rfl, rfl⟩
  exact Submodule.subset_span ⟨w₁ ++ w₂, by simp, by simp⟩

instance instGradedMonoid (D : CartanDatum ι X Y) (q : K) : SetLike.GradedMonoid (grade D q) where
  one_mem := one_mem_grade_zero
  mul_mem _ _ _ _ ha hb := grade_mul_le _ _ (Submodule.mul_mem_mul ha hb)

theorem normalizedE_mem_grade (i : ι) : normalizedE D q i ∈ grade D q (D.root i) := by
  rw [normalizedE_def, ← zero_add (D.root i)]
  exact SetLike.mul_mem_graded (simpleKInv_mem_grade i) (e_mem_grade i)

theorem normalizedF_mem_grade (i : ι) : normalizedF D q i ∈ grade D q (-D.root i) := by
  rw [normalizedF_def, ← add_zero (-D.root i)]
  exact SetLike.mul_mem_graded (f_mem_grade i) (simpleK_mem_grade i)

theorem quantumDividedPower_mem_grade (q' : K) {α : X} {a : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (r : ℕ) : quantumDividedPower q' a r ∈ grade D q (r • α) := by
  rw [quantumDividedPower_def]
  exact (grade D q (r • α)).smul_mem _ (SetLike.pow_mem_graded r ha)

/-- Every homogeneous component outside `D.rootLattice` vanishes. -/
theorem grade_eq_bot_of_notMem_rootLattice {β : X} (hβ : β ∉ D.rootLattice) : grade D q β = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  induction hx using grade_induction with
  | word w hw =>
    refine (hβ ?_).elim
    rw [← hw]
    clear hw hβ
    induction w with
    | nil => exact D.rootLattice.zero_mem
    | cons g w ih => simpa using D.rootLattice.add_mem (generatorWeight_mem_rootLattice D g) ih
  | zero => rfl
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul _ _ _ hx => simp [hx]

private theorem k_mul_generator_mul_k_neg (g : Generator ι Y) (y : Y) :
    k D q y * generator D q g * k D q (-y) =
      q ^ D.pairing (generatorWeight D g) y • generator D q g := by
  cases g <;> simp [k_mul_e_mul_k_neg, k_mul_f_mul_k_neg]

private theorem k_mul_word_prod_mul_k_neg (w : List (Generator ι Y)) (y : Y) :
    k D q y * (w.map (generator D q)).prod * k D q (-y) =
      q ^ D.pairing (w.map (generatorWeight D)).sum y • (w.map (generator D q)).prod := by
  induction w with
  | nil => simp
  | cons g w ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, LinearMap.add_apply]
    calc k D q y * (generator D q g * (w.map (generator D q)).prod) * k D q (-y)
        = (k D q y * generator D q g * k D q (-y)) *
            (k D q y * (w.map (generator D q)).prod * k D q (-y)) := by
          simp [mul_assoc, k_mul_k_assoc]
      _ = (q ^ D.pairing (generatorWeight D g) y *
            q ^ D.pairing (w.map (generatorWeight D)).sum y) •
            (generator D q g * (w.map (generator D q)).prod) := by
          rw [k_mul_generator_mul_k_neg, ih, smul_mul_smul_comm]
      _ = _ := by
          rcases eq_or_ne q 0 with rfl | hq
          · -- `e_zero`/`f_zero` kill `e` and `f`; `k` has weight `0`, where `0 ^ 0 = 1`.
            cases g <;> simp
          · rw [← zpow_add₀ hq]

/-- **Toral conjugation on homogeneous pieces**: for `x ∈ grade D q β` and `y ∈ Y`,
`K_y * x * K_(-y) = q ^ ⟨β, y⟩ • x`. -/
theorem k_mul_mul_k_neg_of_mem_grade {β : X} {x : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ grade D q β) (y : Y) : k D q y * x * k D q (-y) = q ^ D.pairing β y • x := by
  induction hx using grade_induction with
  | word w hw => subst hw; exact k_mul_word_prod_mul_k_neg w y
  | zero => simp
  | add _ _ _ _ ha hb => simp [mul_add, add_mul, smul_add, ha, hb]
  | smul c _ _ ha => simp [ha, smul_comm c]

/-- Commuting a toral generator `K_y` past a homogeneous element `x ∈ grade D q β` multiplies by
`q ^ ⟨β, y⟩`. -/
theorem k_mul_of_mem_grade {β : X} {x : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ grade D q β) (y : Y) : k D q y * x = q ^ D.pairing β y • (x * k D q y) := by
  rw [← smul_mul_assoc, ← k_mul_mul_k_neg_of_mem_grade hx y, mul_assoc, mul_assoc, k_neg_mul_k,
    mul_one]

private theorem map_mem_grade_of_generator
    (f : QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) (φ : X →+ X)
    (hone : f 1 ∈ grade D q 0)
    (hmul : ∀ {α₁ α₂ a b}, f a ∈ grade D q α₁ → f b ∈ grade D q α₂ →
      f (a * b) ∈ grade D q (α₁ + α₂))
    (hgen : ∀ g, f (generator D q g) ∈ grade D q (φ (generatorWeight D g)))
    {β : X} {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ grade D q β) :
    f x ∈ grade D q (φ β) := by
  induction hx using grade_induction with
  | word w hw =>
    subst hw
    induction w with
    | nil => simpa using hone
    | cons g w ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add]
      exact hmul (hgen g) ih
  | zero => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact (grade D q (φ β)).add_mem ha hb
  | smul r _ _ ha => rw [map_smul]; exact (grade D q (φ β)).smul_mem r ha

/-- Diagonal rescaling automorphisms preserve every homogeneous subspace `grade D q β`. -/
theorem rescale_mem_grade (c : ι → Kˣ) {β : X} {x : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ grade D q β) : rescale D q c x ∈ grade D q β :=
  map_mem_grade_of_generator (rescale D q c).toLinearMap (AddMonoidHom.id X)
    (by simpa using one_mem_grade_zero)
    (fun ha hb => by simpa using SetLike.mul_mem_graded ha hb)
    (by
      rintro (i | i | y)
      · simpa using (grade D q (D.root i)).smul_mem (c i : K) (e_mem_grade i)
      · simpa using (grade D q (-D.root i)).smul_mem (c i : K)⁻¹ (f_mem_grade i)
      · simpa using k_mem_grade y)
    hx

/-- The Chevalley involution maps `grade D q β` into `grade D q (-β)`. -/
theorem chevalleyInvolution_mem_grade {β : X} {x : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ grade D q β) : chevalleyInvolution D q x ∈ grade D q (-β) :=
  map_mem_grade_of_generator (chevalleyInvolution D q).toLinearMap (-AddMonoidHom.id X)
    (by simpa using one_mem_grade_zero)
    (fun ha hb => by simpa using SetLike.mul_mem_graded ha hb)
    (by
      rintro (i | i | y)
      · simpa using f_mem_grade i
      · simpa using e_mem_grade i
      · simpa using k_mem_grade (-y))
    hx

/-- The antipode preserves every homogeneous subspace `grade D q β`. -/
theorem antipodeLinearEquiv_mem_grade {β : X} {x : QuantizedEnvelopingAlgebra D q}
    (hx : x ∈ grade D q β) : antipodeLinearEquiv D q x ∈ grade D q β :=
  map_mem_grade_of_generator (antipodeLinearEquiv D q).toLinearMap (AddMonoidHom.id X)
    (by simpa using one_mem_grade_zero)
    (fun ha hb => by simpa [add_comm] using SetLike.mul_mem_graded hb ha)
    (by
      rintro (i | i | y)
      · simpa [← normalizedE_def] using (grade D q (D.root i)).neg_mem (normalizedE_mem_grade i)
      · simpa [← normalizedF_def] using (grade D q (-D.root i)).neg_mem (normalizedF_mem_grade i)
      · simpa using k_mem_grade (-y))
    hx

private theorem serreSum_term_deg (w w' : X) {n r : ℕ} (hr : r ≤ n) :
    r • w + w' + (n - r) • w = n • w + w' := by
  rw [add_right_comm, ← add_nsmul, Nat.add_sub_of_le hr]

private theorem serreSum_term_mem_grade {wt : ι → X} {u : ι → QuantizedEnvelopingAlgebra D q}
    (hu : ∀ l, u l ∈ grade D q (wt l)) (i j : ι) {r : ℕ} (hr : r ≤ D.serreLength i j) :
    (-1 : K) ^ r • (quantumDividedPower (q ^ D.symmetrizer i) (u i) r * u j *
      quantumDividedPower (q ^ D.symmetrizer i) (u i) (D.serreLength i j - r)) ∈
        grade D q (D.serreLength i j • wt i + wt j) :=
  serreSum_term_deg (wt i) (wt j) hr ▸ (grade D q _).smul_mem _ (SetLike.mul_mem_graded
    (SetLike.mul_mem_graded (quantumDividedPower_mem_grade _ (hu i) r) (hu j))
    (quantumDividedPower_mem_grade _ (hu i) (D.serreLength i j - r)))

end Homogeneous

section GradedAlgebra

open DirectSum

variable [DecidableEq X] (D : CartanDatum ι X Y) (q : K)

private def inGrade {α : X} (a : QuantizedEnvelopingAlgebra D q) (ha : a ∈ grade D q α) :
    ⨁ β : X, grade D q β :=
  lof K X (fun β => ↥(grade D q β)) α ⟨a, ha⟩

private theorem inGrade_eq_of {α : X} (a : QuantizedEnvelopingAlgebra D q)
    (ha : a ∈ grade D q α) :
    inGrade D q a ha = of (fun β => ↥(grade D q β)) α ⟨a, ha⟩ :=
  lof_eq_of K X (fun β => ↥(grade D q β)) α ⟨a, ha⟩

private theorem inGrade_eq {α₁ α₂ : X} {a₁ a₂ : QuantizedEnvelopingAlgebra D q}
    {ha₁ : a₁ ∈ grade D q α₁} {ha₂ : a₂ ∈ grade D q α₂} (hdeg : α₁ = α₂) (hval : a₁ = a₂) :
    inGrade D q a₁ ha₁ = inGrade D q a₂ ha₂ := by
  subst hdeg hval; rfl

private theorem inGrade_cast {α₁ α₂ : X} (h : α₁ = α₂) (a : QuantizedEnvelopingAlgebra D q)
    (ha : a ∈ grade D q α₁) :
    inGrade D q a ha = inGrade D q a (h ▸ ha) := by
  subst h; rfl

private theorem inGrade_zero (α : X) :
    inGrade D q 0 (grade D q α).zero_mem = 0 :=
  map_zero _

private theorem inGrade_add {α : X} {a b : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (hb : b ∈ grade D q α) :
    inGrade D q a ha + inGrade D q b hb = inGrade D q (a + b) ((grade D q α).add_mem ha hb) :=
  (map_add (lof K X (fun β => ↥(grade D q β)) α) ⟨a, ha⟩ ⟨b, hb⟩).symm

private theorem inGrade_sub {α : X} {a b : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (hb : b ∈ grade D q α) :
    inGrade D q a ha - inGrade D q b hb = inGrade D q (a - b) ((grade D q α).sub_mem ha hb) :=
  (map_sub (lof K X (fun β => ↥(grade D q β)) α) ⟨a, ha⟩ ⟨b, hb⟩).symm

private theorem inGrade_smul {α : X} (c : K) {a : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) :
    c • inGrade D q a ha = inGrade D q (c • a) ((grade D q α).smul_mem c ha) :=
  (map_smul (lof K X (fun β => ↥(grade D q β)) α) c ⟨a, ha⟩).symm

private theorem inGrade_mul {α β : X} {a b : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (hb : b ∈ grade D q β) :
    inGrade D q a ha * inGrade D q b hb = inGrade D q (a * b) (SetLike.mul_mem_graded ha hb) := by
  simp only [inGrade, lof_eq_of, of_mul_of]
  exact congrArg (of _ _) (Subtype.ext (SetLike.coe_gMul _ _ _))

@[simp] private theorem coeAlgHom_inGrade {α : X} (a : QuantizedEnvelopingAlgebra D q)
    (ha : a ∈ grade D q α) : coeAlgHom (grade D q) (inGrade D q a ha) = a := by
  simp [inGrade, lof_eq_of]

private theorem inGrade_pow {α : X} {a : QuantizedEnvelopingAlgebra D q} (ha : a ∈ grade D q α)
    (n : ℕ) : (inGrade D q a ha) ^ n = inGrade D q (a ^ n) (SetLike.pow_mem_graded n ha) := by
  induction n with
  | zero => exact inGrade_eq D q (zero_nsmul α).symm (pow_zero a).symm
  | succ n ih =>
    rw [pow_succ, ih, inGrade_mul]
    exact inGrade_eq D q (succ_nsmul α n).symm (pow_succ a n).symm

private theorem inGrade_quantumDividedPower (q' : K) {α : X} {a : QuantizedEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (n : ℕ) :
    quantumDividedPower q' (inGrade D q a ha) n =
      inGrade D q (quantumDividedPower q' a n) (quantumDividedPower_mem_grade q' ha n) := by
  rw [quantumDividedPower_def, inGrade_pow, inGrade_smul]
  exact inGrade_eq D q rfl (quantumDividedPower_def q' a n).symm

private theorem inGrade_serreSum {wt : ι → X} {u : ι → QuantizedEnvelopingAlgebra D q}
    (hu : ∀ l, u l ∈ grade D q (wt l)) {i j : ι} (hserre : serreSum D q u i j = 0) :
    serreSum D q (fun l => inGrade D q (u l) (hu l)) i j = 0 := by
  let l := lof K X (fun β => ↥(grade D q β)) (D.serreLength i j • wt i + wt j)
  let s : grade D q (D.serreLength i j • wt i + wt j) :=
    ∑ r ∈ (range (D.serreLength i j + 1)).attach,
      ⟨_, serreSum_term_mem_grade hu i j (Nat.lt_succ_iff.mp (mem_range.mp r.property))⟩
  have hsum : serreSum D q (fun l' => inGrade D q (u l') (hu l')) i j = l s := by
    rw [serreSum_def, ← Finset.sum_attach, map_sum]
    refine Finset.sum_congr rfl fun ⟨r, hr⟩ _ => ?_
    rw [inGrade_quantumDividedPower, inGrade_quantumDividedPower, inGrade_mul, inGrade_mul,
      inGrade_smul]
    exact inGrade_eq D q (serreSum_term_deg _ _ (Nat.lt_succ_iff.mp (mem_range.mp hr))) rfl
  have hcoe := congrArg (coeAlgHom (grade D q)) hsum
  simp only [map_serreSum, coeAlgHom_inGrade, hserre, l, lof_eq_of, coeAlgHom_of] at hcoe
  have hs : s = 0 := Subtype.ext hcoe.symm
  rw [hsum, hs, map_zero]

/-- The `K`-algebra homomorphism decomposing `QuantizedEnvelopingAlgebra D q` into the direct sum
`⨁ β : X, grade D q β` of its weight-homogeneous components. -/
private def decomposeGrade : QuantizedEnvelopingAlgebra D q →ₐ[K] ⨁ β : X, grade D q β :=
  lift
    { e i := inGrade D q (e D q i) (e_mem_grade i)
      f i := inGrade D q (f D q i) (f_mem_grade i)
      k y := inGrade D q (k D q y) (k_mem_grade y)
      k_zero := inGrade_eq D q rfl (k_zero D q)
      k_mul_k y₁ y₂ :=
        (inGrade_mul D q _ _).trans (inGrade_eq D q (zero_add 0) (k_mul_k D q y₁ y₂))
      conjugate_e y i := by
        rw [inGrade_mul, inGrade_mul, inGrade_smul]
        exact inGrade_eq D q (by abel) (k_mul_e_mul_k_neg D q y i)
      conjugate_f y i := by
        rw [inGrade_mul, inGrade_mul, inGrade_smul]
        exact inGrade_eq D q (by abel) (k_mul_f_mul_k_neg D q y i)
      commutator_self i := by
        have hrel : e D q i * f D q i - f D q i * e D q i =
            (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
              (k D q (D.simpleTorus i) - k D q (-D.simpleTorus i)) := by
          simpa only [simpleK_def, simpleKInv_def] using e_mul_f_sub_f_mul_e_self D q i
        rw [inGrade_mul, inGrade_mul, inGrade_cast D q (add_neg_cancel (D.root i)),
          inGrade_cast D q (neg_add_cancel (D.root i)), inGrade_sub, inGrade_sub, inGrade_smul]
        exact inGrade_eq D q rfl hrel
      commutator_ne := fun {i j} hij => by
        rw [inGrade_mul, inGrade_mul,
          inGrade_cast D q (add_comm (-D.root j) (D.root i)) (f D q j * e D q i), inGrade_sub]
        exact (inGrade_eq D q rfl (e_mul_f_sub_f_mul_e_of_ne D q hij)).trans (inGrade_zero D q _)
      serre_e hij := inGrade_serreSum D q (fun l => e_mem_grade l) (serreE_eq_zero D q hij)
      serre_f hij := inGrade_serreSum D q (fun l => f_mem_grade l) (serreF_eq_zero D q hij) }

/-- Summing homogeneous components left-inverts `decomposeGrade`. -/
private theorem coeAlgHom_comp_decomposeGrade :
    (coeAlgHom (grade D q)).comp (decomposeGrade D q) = AlgHom.id K _ := by
  ext <;> simp [decomposeGrade]

private theorem decomposeGrade_word_prod (w : List (Generator ι Y)) :
    decomposeGrade D q (w.map (generator D q)).prod =
      inGrade D q (w.map (generator D q)).prod (word_prod_mem_grade w) := by
  induction w with
  | nil => exact map_one _
  | cons g w ih =>
    have hg : decomposeGrade D q (generator D q g) = inGrade D q _ (generator_mem_grade g) := by
      cases g <;> simp [decomposeGrade]
    calc decomposeGrade D q ((g :: w).map (generator D q)).prod
        = decomposeGrade D q (generator D q g) *
            decomposeGrade D q (w.map (generator D q)).prod := by
          rw [List.map_cons, List.prod_cons, map_mul]
      _ = inGrade D q (generator D q g * (w.map (generator D q)).prod)
            (SetLike.mul_mem_graded (generator_mem_grade g) (word_prod_mem_grade w)) := by
          rw [hg, ih, inGrade_mul]
      _ = inGrade D q ((g :: w).map (generator D q)).prod (word_prod_mem_grade (g :: w)) :=
          inGrade_eq D q (by simp) (by simp)

/-- Applying `decomposeGrade` to an element of `grade D q β` embeds it into the `β`-summand of
`⨁ α : X, grade D q α`. -/
private theorem decomposeGrade_coe (β : X) (x : grade D q β) :
    decomposeGrade D q (x : QuantizedEnvelopingAlgebra D q) = of (fun α => ↥(grade D q α)) β x := by
  rcases x with ⟨x, hx⟩
  rw [Submodule.coe_mk, ← inGrade_eq_of D q x hx]
  induction hx using grade_induction with
  | word w hw => exact (decomposeGrade_word_prod D q w).trans (inGrade_eq D q hw rfl)
  | zero => exact (map_zero _).trans (inGrade_zero D q β).symm
  | add _ _ ha hb iha ihb => rw [map_add, iha, ihb, inGrade_add]
  | smul c _ ha ih => rw [map_smul, ih, inGrade_smul]

/-- The `X`-graded `K`-algebra structure on `QuantizedEnvelopingAlgebra D q`, supported on
`D.rootLattice`. -/
instance instGradedAlgebra : GradedAlgebra (grade D q) :=
  -- Route through `Prop`-valued `IsInternal` so `decomposeGrade` can remain `private`.
  DirectSum.IsInternal.gradedAlgebra (by
    exact (GradedAlgebra.ofAlgHom (grade D q) (decomposeGrade D q)
      (coeAlgHom_comp_decomposeGrade D q) (decomposeGrade_coe D q)).toDecomposition.isInternal)

end GradedAlgebra

end

end QuantizedEnvelopingAlgebra

end TauCeti
