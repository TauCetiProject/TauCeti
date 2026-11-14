/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.LinearAlgebra.Basis.Algebra

/-!
# Descent of finite free algebras over a polynomial ring

A finite family of polynomials over `K` lifts over every intermediate field containing a
suitable finitely generated intermediate field of `K/k`.

A finite free commutative algebra over `K[X]`, with a specified basis, likewise descends over
every such intermediate field, together with any finitely many specified elements. The model
is the span of the original basis, and extension of scalars recovers the original algebra.
The map from `L[X]` to `K[X]` is `Polynomial.algebra`; the action of `L[X]` on the algebra
can be any caller-provided action compatible with this map and the original `K[X]` action.
-/

public section

open Polynomial

attribute [local instance] Polynomial.algebra

namespace Polynomial

/-- A finite family of polynomials lifts over every intermediate field containing a suitable
finitely generated intermediate field of `K/k`. -/
theorem exists_intermediateField_fg_lifts_finset (k : Type*) {K : Type*}
    [Field k] [Field K] [Algebra k K] (s : Finset K[X]) :
    ∃ L₀ : IntermediateField k K, L₀.FG ∧
      ∀ L : IntermediateField k K, L₀ ≤ L →
        ∀ p ∈ s, p ∈ lifts (algebraMap L K) := by
  classical
  let a : Finset K := s.biUnion fun p ↦ p.coeffs
  refine ⟨IntermediateField.adjoin k (a : Set K), IntermediateField.fg_adjoin_finset a, ?_⟩
  intro L hL p hp
  apply (lifts_iff_coeffs_subset_range p).mpr
  intro x hx
  refine ⟨⟨x, hL (IntermediateField.subset_adjoin k (a : Set K) ?_)⟩, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨p, hp, by simpa using hx⟩

end Polynomial

namespace Module.Basis

variable (k : Type*) {K B ι : Type*} [Field k] [Field K] [Algebra k K] [CommSemiring B]
  [Algebra K[X] B] [Finite ι]

/-- A finite free commutative algebra over `K[X]` descends with its chosen basis and finitely
many specified elements over every intermediate field containing a suitable finitely generated
one. The polynomial map to `K[X]` is `Polynomial.algebra`; the action on `B` can be any
compatible caller-provided algebra structure. -/
theorem exists_intermediateField_fg_subalgebra_basis (b : Basis ι K[X] B) (s : Finset B) :
    ∃ L₀ : IntermediateField k K, L₀.FG ∧
      ∀ L : IntermediateField k K, L₀ ≤ L →
        ∀ [Algebra L[X] B] [IsScalarTower L[X] K[X] B],
          ∃ C : Subalgebra L[X] B, ∃ c : Basis ι L[X] C,
            C.toSubmodule = Submodule.span L[X] (Set.range b) ∧
              (∀ i, (c i : B) = b i) ∧ (∀ x ∈ s, x ∈ C) ∧
                Algebra.IsPushout L[X] K[X] C B := by
  classical
  let _ := Fintype.ofFinite ι
  let t : Finset K[X] :=
    (Finset.univ.image fun i ↦ b.repr 1 i) ∪
      (Finset.univ.image fun ijl : ι × ι × ι ↦ b.repr (b ijl.1 * b ijl.2.1) ijl.2.2) ∪
      (s.biUnion fun x ↦ Finset.univ.image fun i ↦ b.repr x i)
  obtain ⟨L₀, hfg, hlifts⟩ := Polynomial.exists_intermediateField_fg_lifts_finset k t
  refine ⟨L₀, hfg, ?_⟩
  intro L hL _ _
  have hpoly (p : K[X]) (hp : p ∈ t) : p ∈ Set.range (algebraMap L[X] K[X]) := by
    rw [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
    exact (lifts_iff_set_range p).mp (hlifts L hL p hp)
  have h₁ (i : ι) : b.repr 1 i ∈ Set.range (algebraMap L[X] K[X]) :=
    hpoly _ (by simp [t])
  have hmul (i j l : ι) : b.repr (b i * b j) l ∈ Set.range (algebraMap L[X] K[X]) :=
    hpoly _ (by
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(i, j, l), Finset.mem_univ _, rfl⟩)
  let C := b.descendSubalgebra L[X] h₁ hmul
  let c := b.descendBasis L[X] h₁ hmul
  have hC := b.descendSubalgebra_toSubmodule L[X] h₁ hmul
  refine ⟨C, c, hC, b.coe_descendBasis_apply L[X] h₁ hmul, ?_, inferInstance⟩
  intro x hx
  apply (b.mem_descendSubalgebra_iff L[X] h₁ hmul x).mpr
  intro i
  apply hpoly
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨x, hx, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)

end Module.Basis
