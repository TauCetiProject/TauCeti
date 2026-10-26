/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Trace
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Perfect trace pairings between signed graded corners

Multiplication followed by the canonical componentwise trace pairs the degree `d` part of
`e_i Z e_j` perfectly with the degree `2 - d` part of `e_j Z e_i`. This holds over a commutative
ring, for every finite simple graph, including its isolated dual-number components.

The existing signed-corner spans reduce the pairing to dual vertex/volume or reverse-arrow
basis vectors, or to two zero modules. The existing componentwise trace Gram formula supplies
the coefficient one in each nonzero case; no scalar inversion or dimension argument is needed.
The induced equivalence with the dual is Mathlib's `LinearMap.toPerfPair`.

## Main declarations

* `TauCeti.zigzagAlgebraGradedCornerTracePairing`: the actual multiplication--trace restriction.
* `TauCeti.zigzagAlgebraGradedCornerTracePairing_isPerfPair`: perfectness in both arguments.


This is an internal graded pairing. It does not identify internal degree with cohomological
degree or assert Serre duality or cohomological sphericity of a projective module.

## References

The corner spans and trace Gram formula are those already formalized in
`TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Grading` and
`TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Trace`. The grading and trace
conventions follow Huerfano--Khovanov, *A category for the adjoint representation*, Section 3,
and Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "C" => fun (i j : V) (d : ℤ) ↦
  cornerSubmodule k (e i) (e j) ⊓ zigzagAlgebraIntegerGrade k G d
local notation "T" => LinearMap.compr₂ (LinearMap.mul k Z) (zigzagAlgebraTrace k G)

/-- Multiplication and the componentwise trace pair opposite corners in complementary signed
internal degrees. -/
noncomputable def zigzagAlgebraGradedCornerTracePairing (i j : V) (d : ℤ) :
    ↥(C i j d) →ₗ[k] ↥(C j i (2 - d)) →ₗ[k] k :=
  (T).compl₁₂ (C i j d).subtype (C j i (2 - d)).subtype

/-- The restricted pairing evaluates to the trace of the actual product in the public algebra. -/
@[simp]
theorem zigzagAlgebraGradedCornerTracePairing_apply (i j : V) (d : ℤ)
    (x : C i j d) (y : C j i (2 - d)) :
    zigzagAlgebraGradedCornerTracePairing k G i j d x y =
      zigzagAlgebraTrace k G ((x : Z) * (y : Z)) := (rfl)

private theorem trace_dual_spans_bijective (U W : Submodule k Z) (b : ZigzagBasisIndex G)
    (hU : U = k ∙ zigzagAlgebraBasis k G b)
    (hW : W = k ∙ zigzagAlgebraBasis k G (zigzagDualIndex G b)) :
    Function.Bijective ((T).compl₁₂ U.subtype W.subtype) := by
  classical
  let x₀ : U := ⟨zigzagAlgebraBasis k G b, by
    rw [hU]
    exact Submodule.mem_span_singleton_self _⟩
  let y₀ : W := ⟨zigzagAlgebraBasis k G (zigzagDualIndex G b), by
    rw [hW]
    exact Submodule.mem_span_singleton_self _⟩
  let p := (T).compl₁₂ U.subtype W.subtype
  have hx (x : U) : ∃ a : k, x = a • x₀ := by
    have hx' : (x : Z) ∈ k ∙ zigzagAlgebraBasis k G b := by
      rw [← hU]
      exact x.property
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx'
    exact ⟨a, Subtype.ext ha.symm⟩
  have hy (y : W) : ∃ a : k, y = a • y₀ := by
    have hy' : (y : Z) ∈ k ∙ zigzagAlgebraBasis k G (zigzagDualIndex G b) := by
      rw [← hW]
      exact y.property
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy'
    exact ⟨a, Subtype.ext ha.symm⟩
  have hunit : p x₀ y₀ = 1 := by
    -- Restriction and composition leave subtype/linear-map coercions; the Gram formula uses
    -- the corresponding product of the two ambient basis vectors.
    change zigzagAlgebraTrace k G
      (zigzagAlgebraBasis k G b * zigzagAlgebraBasis k G (zigzagDualIndex G b)) = 1
    rw [zigzagAlgebraTrace_zigzagAlgebraBasis_mul]
    simp
  -- Name the same restricted bilinear map used in the spanning calculations above.
  change Function.Bijective p
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hx x
    obtain ⟨b, rfl⟩ := hx y
    have hab := DFunLike.congr_fun hxy y₀
    have hab' : a = b := by
      simpa only [map_smul, LinearMap.smul_apply, hunit, smul_eq_mul, mul_one] using hab
    rw [hab']
  · intro f
    refine ⟨f y₀ • x₀, LinearMap.ext fun y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hy y
    simp only [map_smul, LinearMap.smul_apply, hunit, smul_eq_mul, mul_one]

private theorem trace_dual_spans_isPerfPair (U W : Submodule k Z) (b : ZigzagBasisIndex G)
    (hU : U = k ∙ zigzagAlgebraBasis k G b)
    (hW : W = k ∙ zigzagAlgebraBasis k G (zigzagDualIndex G b)) :
    ((T).compl₁₂ U.subtype W.subtype).IsPerfPair := by
  refine ⟨trace_dual_spans_bijective k G U W b hU hW, ?_⟩
  have hflip : ((T).compl₁₂ U.subtype W.subtype).flip =
      (T).compl₁₂ W.subtype U.subtype := by
    ext y x
    exact zigzagAlgebraTrace_mul_comm k G (x : Z) (y : Z)
  rw [hflip]
  apply trace_dual_spans_bijective k G W U (zigzagDualIndex G b) hW
  simpa only [zigzagDualIndex_involutive G b] using hU

/-- Opposite signed graded corners of the public componentwise zigzag algebra are in perfect
trace pairing over any commutative coefficient ring, including at isolated vertices. -/
instance zigzagAlgebraGradedCornerTracePairing_isPerfPair (i j : V) (d : ℤ) :
    (zigzagAlgebraGradedCornerTracePairing k G i j d).IsPerfPair := by
  classical
  -- Unfold the pairing once to apply the existing signed corner-span formulas to its domains.
  change ((T).compl₁₂ (C i j d).subtype (C j i (2 - d)).subtype).IsPerfPair
  have zero_case (U W : Submodule k Z) (hU : U = ⊥) (hW : W = ⊥) :
      ((T).compl₁₂ U.subtype W.subtype).IsPerfPair := by
    subst U
    subst W
    constructor <;> exact Function.bijective_of_subsingleton' _
  dsimp only
  by_cases hij : i = j
  · subst j
    by_cases h0 : d = 0
    · subst d
      apply trace_dual_spans_isPerfPair k G _ _ (.inl i) <;> simp
    · by_cases h2 : d = 2
      · subst d
        apply trace_dual_spans_isPerfPair k G _ _ (.inr (.inr i)) <;> simp
      · apply zero_case
        · simp [h0, h2]
        · have h20 : 2 - d ≠ 0 := by omega
          have h22 : 2 - d ≠ 2 := by omega
          simp [h20, h22]
  · by_cases hadj : G.Adj i j
    · by_cases h1 : d = 1
      · subst d
        apply trace_dual_spans_isPerfPair k G _ _
          (.inr (.inl (⟨(j, i), hadj.symm⟩ : G.Dart)))
        · rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj.symm]
          simp only [ite_true, cornerSubmodule_zigzagAlgebra_eq_span_of_adj k G hadj.symm]
        · rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj]
          simp [cornerSubmodule_zigzagAlgebra_eq_span_of_adj k G hadj,
            SimpleGraph.Dart.symm_mk]
      · apply zero_case
        · rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj.symm]
          simp [h1]
        · have h21 : 2 - d ≠ 1 := by omega
          rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj]
          simp [h21]
    · apply zero_case
      · rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij hadj]
        simp
      · have hadj' : ¬ G.Adj j i := fun h ↦ hadj h.symm
        rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G (Ne.symm hij) hadj']
        simp

end TauCeti
