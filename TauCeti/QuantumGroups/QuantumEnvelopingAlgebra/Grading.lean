/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantumEnvelopingAlgebra.Basic

import Mathlib.Tactic.Abel

/-!
# Weight-lattice grading on the quantized enveloping algebra

Assigning degree `αᵢ ∈ X` to `Eᵢ`, `-αᵢ` to `Fᵢ`, and `0` to `K_y` makes all defining relations of
`QuantumEnvelopingAlgebra D q` homogeneous. We construct `grade D q β`, prove vanishing outside
`D.rootLattice`, prove toral conjugation `K_y x K_(-y) = q^⟨β, y⟩ • x` on `grade D q β`, and
establish `GradedAlgebra (grade D q)` under `[DecidableEq X]`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.2.
-/

public section

open scoped DirectSum

namespace TauCeti

/-- The root lattice `Q = ∑ᵢ ℤ αᵢ ⊆ X` of a Cartan datum, as a `ℤ`-submodule of `X`. -/
def CartanDatum.rootLattice {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (D : CartanDatum ι X Y) : Submodule ℤ X := Submodule.span ℤ (Set.range D.root)

theorem CartanDatum.root_mem_rootLattice {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (D : CartanDatum ι X Y) (i : ι) : D.root i ∈ D.rootLattice := Submodule.subset_span ⟨i, rfl⟩

namespace QuantumEnvelopingAlgebra

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

theorem generatorWeight_mem_rootLattice (D : CartanDatum ι X Y) (g : Generator ι Y) :
    generatorWeight D g ∈ D.rootLattice := by
  cases g with
  | e i => exact D.root_mem_rootLattice i
  | f i => exact D.rootLattice.neg_mem (D.root_mem_rootLattice i)
  | k _ => exact D.rootLattice.zero_mem

/-- The `β`-homogeneous subspace of `QuantumEnvelopingAlgebra D q`. -/
noncomputable def grade (D : CartanDatum ι X Y) (q : K) (β : X) :
    Submodule K (QuantumEnvelopingAlgebra D q) :=
  Submodule.span K { x | ∃ w : List (Generator ι Y),
    (w.map (generatorWeight D)).sum = β ∧ (w.map (generator D q)).prod = x }

section Homogeneous

variable {D : CartanDatum ι X Y} {q : K}

theorem word_prod_mem_grade (w : List (Generator ι Y)) :
    (w.map (generator D q)).prod ∈ grade D q (w.map (generatorWeight D)).sum :=
  Submodule.subset_span ⟨w, rfl, rfl⟩
theorem one_mem_grade_zero : (1 : QuantumEnvelopingAlgebra D q) ∈ grade D q 0 :=
  word_prod_mem_grade (D := D) (q := q) []
theorem generator_mem_grade (g : Generator ι Y) :
    generator D q g ∈ grade D q (generatorWeight D g) := by
  simpa using word_prod_mem_grade (D := D) (q := q) [g]
theorem e_mem_grade (i : ι) : e D q i ∈ grade D q (D.root i) := generator_mem_grade (.e i)
theorem f_mem_grade (i : ι) : f D q i ∈ grade D q (-D.root i) := generator_mem_grade (.f i)
theorem k_mem_grade (y : Y) : k D q y ∈ grade D q 0 := generator_mem_grade (.k y)

theorem grade_mul_le (α β : X) : grade D q α * grade D q β ≤ grade D q (α + β) := by
  rw [grade, grade, Submodule.span_mul_span, Submodule.span_le, Set.mul_subset_iff]
  rintro _ ⟨w₁, rfl, rfl⟩ _ ⟨w₂, rfl, rfl⟩
  exact Submodule.subset_span ⟨w₁ ++ w₂, by simp, by simp⟩

noncomputable instance instGradedMonoid (D : CartanDatum ι X Y) (q : K) :
    SetLike.GradedMonoid (grade D q) where
  one_mem := one_mem_grade_zero
  mul_mem _ _ _ _ ha hb := grade_mul_le _ _ (Submodule.mul_mem_mul ha hb)

theorem quantumDividedPower_mem_grade (q' : K) {α : X} {a : QuantumEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (r : ℕ) : quantumDividedPower q' a r ∈ grade D q (r • α) := by
  rw [quantumDividedPower_def]; exact (grade D q (r • α)).smul_mem _ (SetLike.pow_mem_graded r ha)

/-- Every homogeneous component outside `D.rootLattice` is zero. -/
theorem grade_eq_bot_of_notMem_rootLattice {β : X} (hβ : β ∉ D.rootLattice) : grade D q β = ⊥ := by
  rw [grade, Submodule.span_eq_bot]; rintro _ ⟨w, rfl, rfl⟩; refine (hβ ?_).elim; clear hβ
  induction w with
  | nil => exact D.rootLattice.zero_mem
  | cons g w ih => simpa using D.rootLattice.add_mem (generatorWeight_mem_rootLattice D g) ih

private theorem k_mul_generator_mul_k_neg (g : Generator ι Y) (y : Y) :
    k D q y * generator D q g * k D q (-y) =
      q ^ D.pairing (generatorWeight D g) y • generator D q g := by
  cases g with
  | e i => simp [k_mul_e, mul_assoc]
  | f i => simp [k_mul_f, mul_assoc]
  | k y' => have hy : y + y' + -y = y' := by abel
            rw [k_mul_k, k_mul_k, hy]; simp

private theorem k_mul_word_prod_mul_k_neg (w : List (Generator ι Y)) (y : Y) :
    k D q y * (w.map (generator D q)).prod * k D q (-y) =
      q ^ D.pairing (w.map (generatorWeight D)).sum y • (w.map (generator D q)).prod := by
  induction w with
  | nil => simp
  | cons g w ih =>
    rcases eq_or_ne q 0 with rfl | hq
    · cases g with
      | e _ | f _ => simp
      | k y' =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons, generatorWeight_k, zero_add]
        rw [← mul_assoc (k D 0 y), (commute_k y y').eq, mul_assoc (k D 0 y'), mul_assoc, ih,
          mul_smul_comm]
    · simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, LinearMap.add_apply]
      calc k D q y * (generator D q g * (w.map (generator D q)).prod) * k D q (-y)
          = (k D q y * generator D q g * k D q (-y)) *
              (k D q y * (w.map (generator D q)).prod * k D q (-y)) := by simp [mul_assoc]
        _ = _ := by rw [k_mul_generator_mul_k_neg, ih, smul_mul_smul_comm, ← zpow_add₀ hq]

/-- **Toral conjugation on homogeneous pieces**: `K_y x K_(-y) = q^⟨β, y⟩ • x` on `grade D q β`. -/
theorem k_mul_mul_k_neg_of_mem_grade {β : X} {x : QuantumEnvelopingAlgebra D q}
    (hx : x ∈ grade D q β) (y : Y) : k D q y * x * k D q (-y) = q ^ D.pairing β y • x := by
  induction hx using Submodule.span_induction with
  | mem _ ha => rcases ha with ⟨w, rfl, rfl⟩; exact k_mul_word_prod_mul_k_neg w y
  | zero => simp
  | add _ _ _ _ ha hb => simp [mul_add, add_mul, smul_add, ha, hb]
  | smul c _ _ ha => simp [ha, smul_comm c]

theorem serreTerm_mem_grade (q' : K) {N : ℕ} {α₁ α₂ : X}
    {a₁ a₂ : QuantumEnvelopingAlgebra D q} (ha₁ : a₁ ∈ grade D q α₁) (ha₂ : a₂ ∈ grade D q α₂)
    {p : ℕ × ℕ} (hp : p ∈ Finset.antidiagonal N) :
    (-1 : K) ^ p.1 • (quantumDividedPower q' a₁ p.1 * a₂ * quantumDividedPower q' a₁ p.2) ∈
      grade D q (N • α₁ + α₂) := by
  have hdeg : p.1 • α₁ + α₂ + p.2 • α₁ = N • α₁ + α₂ := by
    rw [← Finset.mem_antidiagonal.mp hp, add_nsmul]; abel
  exact hdeg ▸ (grade D q _).smul_mem _ (SetLike.mul_mem_graded
    (SetLike.mul_mem_graded (quantumDividedPower_mem_grade q' ha₁ p.1) ha₂)
    (quantumDividedPower_mem_grade q' ha₁ p.2))

end Homogeneous

section GradedAlgebra

variable [DecidableEq X] (D : CartanDatum ι X Y) (q : K)

private noncomputable def inGrade {α : X} (a : QuantumEnvelopingAlgebra D q)
    (ha : a ∈ grade D q α) : ⨁ β : X, grade D q β :=
  DirectSum.lof K X (fun β ↦ ↥(grade D q β)) α ⟨a, ha⟩

private theorem inGrade_eq {α₁ α₂ : X} {a₁ a₂ : QuantumEnvelopingAlgebra D q}
    {ha₁ : a₁ ∈ grade D q α₁} {ha₂ : a₂ ∈ grade D q α₂} (hdeg : α₁ = α₂) (hval : a₁ = a₂) :
    inGrade D q a₁ ha₁ = inGrade D q a₂ ha₂ := by subst hdeg hval; rfl
private theorem inGrade_one : inGrade D q 1 one_mem_grade_zero = 1 := rfl
private theorem inGrade_sub {α : X} {a b : QuantumEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (hb : b ∈ grade D q α) :
    inGrade D q a ha - inGrade D q b hb = inGrade D q (a - b) ((grade D q α).sub_mem ha hb) :=
  (map_sub (DirectSum.lof K X (fun β ↦ ↥(grade D q β)) α) ⟨a, ha⟩ ⟨b, hb⟩).symm
private theorem inGrade_smul {α : X} (c : K) {a : QuantumEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) :
    c • inGrade D q a ha = inGrade D q (c • a) ((grade D q α).smul_mem c ha) :=
  (map_smul (DirectSum.lof K X (fun β ↦ ↥(grade D q β)) α) c ⟨a, ha⟩).symm
private theorem inGrade_mul {α β : X} {a b : QuantumEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (hb : b ∈ grade D q β) :
    inGrade D q a ha * inGrade D q b hb = inGrade D q (a * b) (SetLike.mul_mem_graded ha hb) := by
  simp only [inGrade, DirectSum.lof_eq_of, DirectSum.of_mul_of]; rfl
@[simp] private theorem coeAlgHom_inGrade {α : X} (a : QuantumEnvelopingAlgebra D q)
    (ha : a ∈ grade D q α) : DirectSum.coeAlgHom (grade D q) (inGrade D q a ha) = a := by
  simp [inGrade, DirectSum.lof_eq_of]

private theorem inGrade_quantumDividedPower (q' : K) {α : X} {a : QuantumEnvelopingAlgebra D q}
    (ha : a ∈ grade D q α) (r : ℕ) :
    quantumDividedPower q' (inGrade D q a ha) r =
      inGrade D q (quantumDividedPower q' a r) (quantumDividedPower_mem_grade q' ha r) := by
  have hpow : ∀ n, (inGrade D q a ha) ^ n = inGrade D q (a ^ n) (SetLike.pow_mem_graded n ha) := by
    intro n; induction n with
    | zero =>
      rw [pow_zero, ← inGrade_one D q]; exact inGrade_eq D q (zero_nsmul α).symm (pow_zero a).symm
    | succ n ih =>
      rw [pow_succ, ih, inGrade_mul]; exact inGrade_eq D q (succ_nsmul α n).symm (pow_succ a n).symm
  rw [quantumDividedPower_def, hpow, inGrade_smul]
  exact inGrade_eq D q rfl (quantumDividedPower_def q' a r).symm

private theorem inGrade_serreElement (q' : K) (N : ℕ) {α₁ α₂ : X}
    {a₁ a₂ : QuantumEnvelopingAlgebra D q} (ha₁ : a₁ ∈ grade D q α₁)
    (ha₂ : a₂ ∈ grade D q α₂) (hserre : serreElement q' N a₁ a₂ = 0) :
    serreElement q' N (inGrade D q a₁ ha₁) (inGrade D q a₂ ha₂) = 0 := by
  rw [serreElement_def, ← Finset.sum_attach]
  let lof := DirectSum.lof K X (fun β ↦ ↥(grade D q β)) (N • α₁ + α₂)
  have hterm : ∀ p : { p // p ∈ Finset.antidiagonal N },
      (-1 : K) ^ p.1.1 • (quantumDividedPower q' (inGrade D q a₁ ha₁) p.1.1 * inGrade D q a₂ ha₂ *
          quantumDividedPower q' (inGrade D q a₁ ha₁) p.1.2) =
        lof ⟨_, serreTerm_mem_grade q' ha₁ ha₂ p.2⟩ := by
    rintro ⟨⟨r, s⟩, hp⟩
    rw [inGrade_quantumDividedPower, inGrade_quantumDividedPower, inGrade_mul, inGrade_mul,
      inGrade_smul]
    refine inGrade_eq D q ?_ rfl
    dsimp only; rw [← Finset.mem_antidiagonal.mp hp, add_nsmul]; abel
  rw [Finset.sum_congr rfl fun p _ ↦ hterm p, ← map_sum]
  convert map_zero lof; ext
  simp only [Submodule.coe_sum, ZeroMemClass.coe_zero]
  exact (Finset.sum_attach _ fun (p : ℕ × ℕ) ↦
    (-1 : K) ^ p.1 • (quantumDividedPower q' a₁ p.1 * a₂ * quantumDividedPower q' a₁ p.2)).trans
    ((serreElement_def q' N a₁ a₂).symm.trans hserre)

/-- The `K`-algebra homomorphism decomposing `U` into its `X`-graded components. -/
noncomputable def decomposeGrade : QuantumEnvelopingAlgebra D q →ₐ[K] ⨁ β : X, grade D q β :=
  lift
    { e i := inGrade D q (e D q i) (e_mem_grade i)
      f i := inGrade D q (f D q i) (f_mem_grade i)
      k y := inGrade D q (k D q y) (k_mem_grade y)
      k_zero := (inGrade_eq D q rfl k_zero).trans (inGrade_one D q)
      k_mul_k y₁ y₂ := (inGrade_mul D q _ _).trans (inGrade_eq D q (zero_add 0) (k_mul_k y₁ y₂))
      k_mul_e y i := by
        rw [inGrade_mul, inGrade_mul, inGrade_smul]; exact inGrade_eq D q (by abel) (k_mul_e y i)
      k_mul_f y i := by
        rw [inGrade_mul, inGrade_mul, inGrade_smul]; exact inGrade_eq D q (by abel) (k_mul_f y i)
      e_mul_f_sub_f_mul_e_self i := by
        have hm₁ : e D q i * f D q i ∈ grade D q 0 := by
          simpa using SetLike.mul_mem_graded (e_mem_grade (D := D) (q := q) i) (f_mem_grade i)
        have hm₂ : f D q i * e D q i ∈ grade D q 0 := by
          simpa using SetLike.mul_mem_graded (f_mem_grade (D := D) (q := q) i) (e_mem_grade i)
        rw [inGrade_mul, inGrade_mul, inGrade_eq D q (add_neg_cancel _) rfl (ha₂ := hm₁),
          inGrade_eq D q (neg_add_cancel _) rfl (ha₂ := hm₂), inGrade_sub, inGrade_sub,
          inGrade_smul]
        exact inGrade_eq D q rfl (e_mul_f_sub_f_mul_e_self i)
      e_mul_f_of_ne hij := by
        rw [inGrade_mul, inGrade_mul]; exact inGrade_eq D q (add_comm _ _) (e_mul_f_of_ne hij)
      serre_e hij := inGrade_serreElement D q _ _ (e_mem_grade _) (e_mem_grade _) (serre_e hij)
      serre_f hij := inGrade_serreElement D q _ _ (f_mem_grade _) (f_mem_grade _) (serre_f hij) }

theorem coeAlgHom_comp_decomposeGrade :
    (DirectSum.coeAlgHom (grade D q)).comp (decomposeGrade D q) =
      AlgHom.id K (QuantumEnvelopingAlgebra D q) := by ext <;> simp [decomposeGrade]
private theorem decomposeGrade_word_prod (w : List (Generator ι Y)) :
    decomposeGrade D q (w.map (generator D q)).prod =
      inGrade D q (w.map (generator D q)).prod (word_prod_mem_grade w) := by
  induction w with
  | nil => exact map_one (decomposeGrade D q)
  | cons g w ih =>
    have hg : decomposeGrade D q (generator D q g) =
        inGrade D q (generator D q g) (generator_mem_grade g) := by
      cases g <;> simp [decomposeGrade]
    simp only [List.map_cons, List.prod_cons, map_mul, hg, ih, inGrade_mul]; rfl
theorem decomposeGrade_coe (β : X) (x : grade D q β) :
    decomposeGrade D q (x : QuantumEnvelopingAlgebra D q) =
      DirectSum.of (fun α ↦ ↥(grade D q α)) β x := by
  rcases x with ⟨x, hx⟩; rw [← DirectSum.lof_eq_of K]
  induction hx using Submodule.span_induction with
  | mem _ ha => rcases ha with ⟨w, rfl, rfl⟩; exact decomposeGrade_word_prod D q w
  | zero => exact (map_zero _).trans (map_zero (DirectSum.lof K X (fun α ↦ ↥(grade D q α)) β)).symm
  | add _ _ ha hb iha ihb =>
    rw [map_add, iha, ihb]
    exact (map_add (DirectSum.lof K X (fun α ↦ ↥(grade D q α)) β) ⟨_, ha⟩ ⟨_, hb⟩).symm
  | smul c _ ha ih => rw [map_smul, ih]; exact inGrade_smul D q c ha
noncomputable instance instGradedAlgebra : GradedAlgebra (grade D q) :=
  GradedAlgebra.ofAlgHom (grade D q) (decomposeGrade D q)
    (coeAlgHom_comp_decomposeGrade D q) (decomposeGrade_coe D q)
end GradedAlgebra
end QuantumEnvelopingAlgebra
end TauCeti
