/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Free graded-commutative presentations

A presentation by homogeneous generators is free graded-commutative when its ordered monomials,
with odd generators occurring at most once, form a basis. We define this condition on an
internally integer-graded algebra and establish its basis, generation, and degree properties.
In particular such an algebra has no negative degrees, and its degree-zero piece consists of
scalars when all generators have positive degree. Algebra maps are determined by the generators.

No field or characteristic assumption is needed for these results. In characteristic two the
definition does not force odd squares to vanish: the restriction on exponents is a basis
condition, not a multiplication relation. The characteristic-zero universal property requires
additional arguments.

The presentation follows Félix–Halperin–Thomas, *Rational homotopy theory*, §3, and Hess,
*Rational homotopy theory: a brief introduction*, §1.
-/

public section

namespace TauCeti

/-- Finitely supported exponents in which generators of odd degree occur at most once. -/
abbrev ExponentVector {ι : Type*} (deg : ι → ℕ) :=
  {f : ι →₀ ℕ // ∀ i, Odd (deg i) → f i ≤ 1}

namespace ExponentVector

variable {ι : Type*} {deg : ι → ℕ}

/-- The empty exponent vector. -/
instance : Zero (ExponentVector deg) := ⟨⟨0, by simp⟩⟩

/-- The empty exponent vector has all exponents zero. -/
@[simp]
theorem coe_zero : ((0 : ExponentVector deg) : ι →₀ ℕ) = 0 := rfl

/-- A single power, subject to the odd-exponent bound. -/
noncomputable def single (i : ι) (n : ℕ) (h : Odd (deg i) → n ≤ 1) : ExponentVector deg :=
  ⟨Finsupp.single i n, by
    classical
    intro j hj
    by_cases hij : i = j
    · subst j
      simpa using h hj
    · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]⟩

/-- The underlying exponent function of a single power. -/
@[simp]
theorem coe_single (i : ι) (n : ℕ) (h : Odd (deg i) → n ≤ 1) :
    (single i n h : ι →₀ ℕ) = Finsupp.single i n := (rfl)

end ExponentVector

section Monomials

variable {ι A : Type*} [LinearOrder ι] [Monoid A]

/-- The product of the powers of the generators, in increasing index order. -/
noncomputable def standardMonomial (x : ι → A) (f : ι →₀ ℕ) : A :=
  (f.support.sort.map fun i ↦ x i ^ f i).prod

/-- The ordered product defining a standard monomial. -/
theorem standardMonomial_def (x : ι → A) (f : ι →₀ ℕ) :
    standardMonomial x f = (f.support.sort.map fun i ↦ x i ^ f i).prod := (rfl)

/-- The empty monomial is the unit. -/
@[simp]
theorem standardMonomial_zero (x : ι → A) : standardMonomial x 0 = 1 := by
  simp [standardMonomial_def]

/-- A monomial supported at one index is the corresponding power. -/
@[simp]
theorem standardMonomial_single (x : ι → A) (i : ι) (n : ℕ) :
    standardMonomial x (Finsupp.single i n) = x i ^ n := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  · simp [standardMonomial_def, Finsupp.support_single _ hn]

/-- Applying a monoid homomorphism to an ordered monomial applies it to each generator. -/
@[simp]
theorem _root_.MonoidHom.map_standardMonomial {B : Type*} [Monoid B] (φ : A →* B) (x : ι → A)
    (f : ι →₀ ℕ) : φ (standardMonomial x f) = standardMonomial (φ ∘ x) f := by
  simp [standardMonomial_def, map_list_prod, List.map_map, Function.comp_def]

end Monomials

section GradedMonomials

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [LinearOrder ι]
  {𝒜 : ℤ → Submodule R A} {x : ι → A} {deg : ι → ℕ}

/-- A monomial in homogeneous generators has the sum of the degrees of its factors. -/
theorem standardMonomial_mem [SetLike.GradedMonoid 𝒜] (hx : ∀ i, x i ∈ 𝒜 (deg i))
    (f : ι →₀ ℕ) : standardMonomial x f ∈ 𝒜 (Finsupp.weight deg f) := by
  classical
  have h := SetLike.list_prod_map_mem_graded (A := 𝒜) f.support.sort
    (fun i ↦ f i • (deg i : ℤ)) (fun i ↦ x i ^ f i)
    (fun i _ ↦ SetLike.pow_mem_graded (f i) (hx i))
  rw [← List.sum_toFinset _ (f.support.sort_nodup _), Finset.sort_toFinset] at h
  simpa only [standardMonomial_def, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum,
    Nat.cast_mul, nsmul_eq_mul, Nat.cast_id] using h

end GradedMonomials

section Presentations

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A] [LinearOrder ι]

/-- A free graded-commutative presentation: homogeneous generators commute with the Koszul sign,
and their ordered monomials, with odd exponents bounded by one, form a basis. -/
structure IsFreeGradedCommutative (𝒜 : ℤ → Submodule R A) (x : ι → A) (deg : ι → ℕ) :
    Prop where
  /-- The generators have the prescribed degrees. -/
  mem : ∀ i, x i ∈ 𝒜 (deg i)
  /-- The generators commute with the Koszul sign. -/
  mul_comm : ∀ i j, x i * x j = ((deg i : ℤ) * deg j).negOnePow • (x j * x i)
  /-- The standard monomials are linearly independent. -/
  linearIndependent : LinearIndependent R
    (fun f : ExponentVector deg ↦ standardMonomial x f.val)
  /-- The standard monomials span the algebra. -/
  span_eq_top : Submodule.span R
    (Set.range fun f : ExponentVector deg ↦ standardMonomial x f.val) = ⊤

variable {𝒜 : ℤ → Submodule R A} {x : ι → A} {deg : ι → ℕ}

namespace IsFreeGradedCommutative

variable (hx : IsFreeGradedCommutative 𝒜 x deg)

include hx

/-- The basis furnished by a free graded-commutative presentation. -/
noncomputable def basis : Module.Basis (ExponentVector deg) R A :=
  Module.Basis.mk hx.linearIndependent (by rw [hx.span_eq_top])

/-- Basis vectors are the standard monomials of the presentation. -/
@[simp]
theorem basis_apply (f : ExponentVector deg) : hx.basis f = standardMonomial x f.val :=
  Module.Basis.mk_apply _ _ _

/-- The presented generators generate the whole algebra. -/
theorem adjoin_eq_top : Algebra.adjoin R (Set.range x) = ⊤ := by
  apply Algebra.toSubmodule_eq_top.mp
  apply top_unique
  rw [← hx.span_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨f, rfl⟩
  simp only [standardMonomial_def]
  apply Subalgebra.list_prod_mem
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  exact (Algebra.adjoin R (Set.range x)).pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _

/-- Algebra maps out of a free presentation are determined by their generator images. -/
theorem algHom_ext {B : Type*} [Semiring B] [Algebra R B] {φ ψ : A →ₐ[R] B}
    (h : ∀ i, φ (x i) = ψ (x i)) : φ = ψ :=
  AlgHom.ext_of_adjoin_eq_top hx.adjoin_eq_top (by rintro _ ⟨i, rfl⟩; exact h i)

section Grading

variable [GradedAlgebra 𝒜]

/-- Each homogeneous piece is spanned by the standard monomials of that degree. -/
theorem piece_eq_span (p : ℤ) : 𝒜 p = Submodule.span R
    {a | ∃ f : ExponentVector deg, (Finsupp.weight deg f.val : ℤ) = p ∧
      standardMonomial x f.val = a} := by
  classical
  apply le_antisymm
  · intro a ha
    have hall : a ∈ Submodule.span R
        (Set.range fun f : ExponentVector deg ↦ standardMonomial x f.val) := by
      rw [hx.span_eq_top]
      trivial
    have hp : ∀ b, b ∈ Submodule.span R
        (Set.range fun f : ExponentVector deg ↦ standardMonomial x f.val) →
        GradedAlgebra.proj 𝒜 p b ∈ Submodule.span R
        {a | ∃ f : ExponentVector deg, (Finsupp.weight deg f.val : ℤ) = p ∧
          standardMonomial x f.val = a} := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨f, rfl⟩ := ha
        by_cases hf : (Finsupp.weight deg f.val : ℤ) = p
        · rw [GradedAlgebra.proj_apply,
            DirectSum.decompose_of_mem_same 𝒜 (hf ▸ standardMonomial_mem hx.mem f.val)]
          exact Submodule.subset_span ⟨f, hf, rfl⟩
        · rw [GradedAlgebra.proj_apply,
            DirectSum.decompose_of_mem_ne 𝒜 (standardMonomial_mem hx.mem f.val) hf]
          exact Submodule.zero_mem _
      | zero => simp
      | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
      | smul r a _ ha => simpa using Submodule.smul_mem _ r ha
    simpa only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]
      using hp a hall
  · apply Submodule.span_le.mpr
    rintro a ⟨f, hf, rfl⟩
    exact hf ▸ standardMonomial_mem hx.mem f.val

/-- A free presentation in nonnegative generator degrees has no negative homogeneous pieces. -/
theorem piece_eq_bot_of_neg {p : ℤ} (hp : p < 0) : 𝒜 p = ⊥ := by
  rw [hx.piece_eq_span]
  have hempty : {a | ∃ f : ExponentVector deg, (Finsupp.weight deg f.val : ℤ) = p ∧
      standardMonomial x f.val = a} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro f hf
    have := Nat.cast_nonneg (α := ℤ) (Finsupp.weight deg f.val)
    omega
  rw [hempty, Submodule.span_empty]

/-- With positive generator degrees, the degree-zero piece is precisely the scalar submodule. -/
theorem piece_zero_eq_span_one (hdeg : ∀ i, 0 < deg i) : 𝒜 0 = R ∙ (1 : A) := by
  rw [hx.piece_eq_span]
  congr 1
  ext a
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hf0 : f.val = 0 := by
      ext i
      have hi := Finsupp.le_weight deg (Nat.ne_of_gt (hdeg i)) f.val
      have hw : Finsupp.weight deg f.val = 0 := by omega
      simpa [hw] using hi
    simp [hf0]
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

end Grading
end IsFreeGradedCommutative
end Presentations
end TauCeti
