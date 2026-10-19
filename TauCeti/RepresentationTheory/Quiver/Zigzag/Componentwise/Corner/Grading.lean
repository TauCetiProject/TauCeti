/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Adjacent
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Grading

/-!
# Signed graded corners of the componentwise zigzag algebra

A self corner has its vertex vector in degree zero and its volume vector in degree two.
This includes the infinitesimal at an isolated vertex. An adjacent corner is concentrated
in degree one. The existing corner spans and the homogeneous vertex–arrow–volume basis
determine their intersections with the signed grading.
These degree-wise dimensions compute graded vertex-projective Hom dimensions and the
coefficients of the graded Cartan matrix.

## References

The vertex–arrow–volume graded-corner calculation was previously formalized in
`TauCeti/RepresentationTheory/Quiver/Zigzag/CartanMatrix.lean` for the path-graded relation
quotient under the no-isolated-vertex hypothesis. Here the componentwise algebra and signed
grading retain the degree-two volume of every isolated dual-number factor.

The algebra and grading conventions follow Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*,
Section 2.
-/

public section

namespace TauCeti

universe u w

section CommRing

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "v" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inr (Sum.inr i))
local notation "A" => zigzagAlgebraIntegerGrade k G

private theorem project_of_mem {x : zigzagAlgebra k G} {n d : ℤ} (hx : x ∈ A n) :
    let _ := zigzagAlgebraIntegerGradedAlgebra k G
    GradedAlgebra.proj (A) d x = if d = n then x else 0 := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  dsimp only
  rw [GradedAlgebra.proj_apply]
  by_cases h : d = n
  · subst d
    rw [ite_eq_left rfl]
    exact DirectSum.decompose_of_mem_same _ hx
  · rw [ite_eq_right h]
    exact DirectSum.decompose_of_mem_ne _ hx (Ne.symm h)

private theorem self_corner_expansion (i : V) (d : ℤ) (x : zigzagAlgebra k G)
    (hc : x ∈ cornerSubmodule k (e i) (e i)) (hd : x ∈ A d) :
    x = (if d = 0 then (zigzagAlgebraBasis k G).repr x (Sum.inl i) • e i else 0) +
      if d = 2 then (zigzagAlgebraBasis k G).repr x (Sum.inr (Sum.inr i)) • v i else 0 := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  have he : e i ∈ A 0 := by
    simpa using (zigzagAlgebraIntegerGrade_ofNat k G 0).ge
      (zigzagAlgebraBasis_inl_mem_grade_zero k G i)
  have hv : v i ∈ A 2 := by
    simpa using (zigzagAlgebraIntegerGrade_ofNat k G 2).ge
      (zigzagAlgebraBasis_inr_inr_mem_grade_two k G i)
  have hfix := (mem_cornerSubmodule_iff k
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).1 hc
  have hx := hfix.symm.trans (zigzagAlgebraBasis_inl_mul_mul_self k G i x)
  have hp := congrArg (GradedAlgebra.proj (A) d) hx
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ hd] at hp
  rw [map_add, map_smul, map_smul, project_of_mem k G he, project_of_mem k G hv] at hp
  simpa only [smul_ite, smul_zero] using hp

/-- A self corner has its vertex and volume spans in degrees zero and two, respectively. -/
@[simp]
theorem cornerSubmodule_zigzagAlgebra_self_inf_integerGrade (i : V) (d : ℤ) :
    cornerSubmodule k (e i) (e i) ⊓ A d =
      if d = 0 then k ∙ e i else if d = 2 then k ∙ v i else ⊥ := by
  have he : e i ∈ A 0 := by
    simpa using (zigzagAlgebraIntegerGrade_ofNat k G 0).ge
      (zigzagAlgebraBasis_inl_mem_grade_zero k G i)
  have hv : v i ∈ A 2 := by
    simpa using (zigzagAlgebraIntegerGrade_ofNat k G 2).ge
      (zigzagAlgebraBasis_inr_inr_mem_grade_two k G i)
  by_cases h0 : d = 0
  · subst d
    rw [ite_eq_left rfl]
    refine le_antisymm ?_ ?_
    · rintro x ⟨hc, hd⟩
      have hx := self_corner_expansion k G i 0 x hc hd
      simp only [ite_eq_right (by decide : (0 : ℤ) ≠ 2), add_zero] at hx
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_inf]
      exact ⟨(mem_cornerSubmodule_iff k
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).2 (by simp), he⟩
  · rw [ite_eq_right h0]
    by_cases h2 : d = 2
    · subst d
      rw [ite_eq_left rfl]
      refine le_antisymm ?_ ?_
      · rintro x ⟨hc, hd⟩
        have hx := self_corner_expansion k G i 2 x hc hd
        simp only [ite_eq_right (by decide : (2 : ℤ) ≠ 0), zero_add] at hx
        rw [hx]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_inf]
        exact ⟨(mem_cornerSubmodule_iff k
          (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
          (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).2 (by simp), hv⟩
    · rw [ite_eq_right h2]
      apply eq_bot_iff.mpr
      rintro x ⟨hc, hd⟩
      rw [Submodule.mem_bot]
      simpa only [ite_eq_right h0, ite_eq_right h2, zero_add] using
        self_corner_expansion k G i d x hc hd

/-- An adjacent corner is concentrated in signed degree one. -/
@[simp]
theorem cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj {i j : V}
    (h : G.Adj j i) (d : ℤ) :
    cornerSubmodule k (e i) (e j) ⊓ A d =
      if d = 1 then cornerSubmodule k (e i) (e j) else ⊥ := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  have hgrade : cornerSubmodule k (e i) (e j) ≤ A 1 := by
    rw [cornerSubmodule_zigzagAlgebra_eq_span_of_adj k G h,
      Submodule.span_singleton_le_iff_mem]
    simpa using (zigzagAlgebraIntegerGrade_ofNat k G 1).ge
      (zigzagAlgebraBasis_inr_inl_mem_grade_one k G (⟨(j, i), h⟩ : G.Dart))
  by_cases hd : d = 1
  · subst d
    rw [ite_eq_left rfl]
    exact inf_eq_left.mpr hgrade
  · rw [ite_eq_right hd]
    apply eq_bot_iff.mpr
    rintro x ⟨hc, hx⟩
    rw [Submodule.mem_bot]
    exact (DirectSum.decompose_of_mem_same (A) hx).symm.trans
      (DirectSum.decompose_of_mem_ne (A) (hgrade hc) (Ne.symm hd))

end CommRing

section Field

variable (k : Type w) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "v" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inr (Sum.inr i))
local notation "A" => zigzagAlgebraIntegerGrade k G

open scoped Classical in
/-- The dimensions of all signed corners: self degrees zero and two, or an edge in degree one. -/
@[simp]
theorem finrank_cornerSubmodule_zigzagAlgebra_inf_integerGrade (i j : V) (d : ℤ) :
    Module.finrank k ↥(cornerSubmodule k (e i) (e j) ⊓ A d) =
      if i = j then if d = 0 ∨ d = 2 then 1 else 0
      else if G.Adj i j ∧ d = 1 then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    by_cases h0 : d = 0
    · have hc : cornerSubmodule k (e i) (e i) ⊓ A d = k ∙ e i := by
        simpa only [h0, ite_true] using
          cornerSubmodule_zigzagAlgebra_self_inf_integerGrade k G i d
      have hr : Module.finrank k (k ∙ e i) = 1 :=
        finrank_span_singleton ((zigzagAlgebraBasis k G).ne_zero (Sum.inl i))
      rw [hc]
      simpa only [h0, true_or, ite_true] using hr
    · by_cases h2 : d = 2
      · have hc : cornerSubmodule k (e i) (e i) ⊓ A d = k ∙ v i := by
          simpa only [h2, ite_eq_right (by decide : (2 : ℤ) ≠ 0), ite_true] using
            cornerSubmodule_zigzagAlgebra_self_inf_integerGrade k G i d
        have hr : Module.finrank k (k ∙ v i) = 1 :=
          finrank_span_singleton ((zigzagAlgebraBasis k G).ne_zero (Sum.inr (Sum.inr i)))
        rw [hc]
        simpa only [h2, or_true, ite_true] using hr
      · have hc : cornerSubmodule k (e i) (e i) ⊓ A d = ⊥ := by
          simpa only [h0, h2, ite_false] using
            cornerSubmodule_zigzagAlgebra_self_inf_integerGrade k G i d
        rw [hc]
        simp only [finrank_bot, h0, h2, false_or, ite_false]
  · rw [ite_eq_right hij]
    by_cases h : G.Adj i j
    · by_cases hd : d = 1
      · have hc : cornerSubmodule k (e i) (e j) ⊓ A d = cornerSubmodule k (e i) (e j) := by
          simpa only [hd, ite_true] using
            cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G h.symm d
        rw [hc]
        simpa only [h, hd, and_self, ite_true] using
          finrank_cornerSubmodule_zigzagAlgebra_of_adj k G h.symm
      · have hc : cornerSubmodule k (e i) (e j) ⊓ A d = ⊥ := by
          simpa only [hd, ite_false] using
            cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G h.symm d
        rw [hc]
        simp only [finrank_bot, hd, and_false, ite_false]
    · have hc : cornerSubmodule k (e i) (e j) ⊓ A d = ⊥ := by
        rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij h]
        simp
      rw [hc]
      simp only [finrank_bot, h, false_and, ite_false]

end Field

end TauCeti
