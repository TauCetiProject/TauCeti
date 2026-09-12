/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Generation of the special orthogonal group by pairs of reflections

For a finite-dimensional nondegenerate quadratic space in characteristic different from two,
the special orthogonal group is generated, even as a monoid, by products of two reflections.
This is the determinant-one form of the Cartan--Dieudonné theorem. It reduces questions about
all special orthogonal transformations to reflection pairs, as needed when proving connectedness
by putting those pairs in the identity component.

The full orthogonal group is generated as a monoid by individual reflections, as expressed by
`closure_reflectionOrthogonal_eq_top`.

## Main results

* `TauCeti.QuadraticMap.exists_even_reflectionOrthogonal_list_prod_eq` gives a dimension-bounded
  even reflection word for every determinant-one isometry of a nondegenerate space.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace TauCeti.QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [NeZero (2 : K)]

/-- Every special orthogonal transformation of a nondegenerate quadratic space is a product of an
even number of reflections, with length at most twice the dimension. -/
theorem exists_even_reflectionOrthogonal_list_prod_eq
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    ∃ l : List (QuadraticMap.orthogonalGroup Q),
      (∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)),
        QuadraticMap.reflectionOrthogonal Q v = r) ∧
      l.length ≤ 2 * Module.finrank K V ∧ Even l.length ∧
      l.prod = ⟨g, (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).1⟩ := by
  have hg := QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2
  obtain ⟨l, hlrefl, hllen, hprod⟩ := exists_reflectionOrthogonal_list_prod_eq Q hQ
    (⟨g, hg.1⟩ : QuadraticMap.orthogonalGroup Q)
  refine ⟨l, hlrefl, hllen, ?_, hprod⟩
  apply (neg_one_pow_eq_one_iff_even (R := Kˣ) ?_).mp
  · calc
      (-1 : Kˣ) ^ l.length = LinearEquiv.det (l.prod : V ≃ₗ[K] V) := by
        let detOrthogonal : QuadraticMap.orthogonalGroup Q →* Kˣ :=
          LinearEquiv.det.comp (QuadraticMap.orthogonalGroup Q).subtype
        have hdet : ∀ r ∈ l, detOrthogonal r = -1 := by
          intro r hr
          obtain ⟨v, _, rfl⟩ := hlrefl r hr
          simpa only [detOrthogonal, MonoidHom.coe_comp, Function.comp_apply,
            Subgroup.coe_subtype, QuadraticMap.coe_reflectionOrthogonal] using
            QuadraticMap.det_reflection Q v
        calc
          _ = (l.map detOrthogonal).prod := by
            symm
            rw [← List.length_map detOrthogonal]
            apply List.prod_eq_pow_length
            rw [List.forall_mem_map]
            exact hdet
          _ = detOrthogonal l.prod := (map_list_prod detOrthogonal l).symm
          _ = LinearEquiv.det (l.prod : V ≃ₗ[K] V) := rfl
      _ = 1 := by rw [hprod]; exact hg.2
  · intro h
    apply NeZero.ne (2 : K)
    have hneg : (-1 : K) = 1 := congrArg Units.val h
    calc
      (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [hneg]; ring

/-- Reflections generate the full orthogonal group as a monoid. -/
theorem closure_reflectionOrthogonal_eq_top
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Submonoid.closure {g : orthogonalGroup Q |
      ∃ (v : V) (_ : Invertible (Q v)), reflectionOrthogonal Q v = g} = ⊤ := by
  let S : Set (orthogonalGroup Q) :=
    {g | ∃ (v : V) (_ : Invertible (Q v)), reflectionOrthogonal Q v = g}
  have hfin : ∀ g ∈ S, IsOfFinOrder g := by
    rintro _ ⟨v, hv, rfl⟩
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by decide, by rw [pow_two, reflectionOrthogonal_mul_self]⟩
  rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder hfin]
  have htop : Subgroup.closure S = ⊤ :=
    subgroup_eq_top_of_reflection_mem Q hQ (Subgroup.closure S)
      (fun v hv ↦ Subgroup.subset_closure ⟨v, hv, rfl⟩)
  rw [htop, Subgroup.top_toSubmonoid]

/-- Every determinant-one orthogonal transformation belongs to any submonoid containing all
products of two reflections. No nonzero-dimensional hypothesis is required. -/
theorem specialOrthogonalGroup_le_of_reflection_mul_mem
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (M : Submonoid (V ≃ₗ[K] V))
    (hM : ∀ (v w : V) [Invertible (Q v)] [Invertible (Q w)],
      reflection Q v * reflection Q w ∈ M) :
    (specialOrthogonalGroup Q).toSubmonoid ≤ M := by
  have hind (g : orthogonalGroup Q) :
      (LinearEquiv.det g.val = 1 → g.val ∈ M) ∧
      (LinearEquiv.det g.val = -1 →
        ∀ (v : V) [Invertible (Q v)], reflection Q v * g.val ∈ M) := by
    refine Submonoid.induction_of_closure_eq_top_left
      (motive := fun g : orthogonalGroup Q ↦
        (LinearEquiv.det g.val = 1 → g.val ∈ M) ∧
        (LinearEquiv.det g.val = -1 →
          ∀ (v : V) [Invertible (Q v)], reflection Q v * g.val ∈ M))
      (closure_reflectionOrthogonal_eq_top Q hQ) g ?_ ?_
    · refine ⟨fun _ ↦ M.one_mem, ?_⟩
      intro h
      have hneg : (1 : K) = -1 := by simpa using congrArg Units.val h
      have htwo : (2 : K) = 0 := by linear_combination hneg
      exact (NeZero.ne (2 : K) htwo).elim
    · rintro _ ⟨w, hw, rfl⟩ y ih
      simp only [Subgroup.coe_mul, coe_reflectionOrthogonal, map_mul, det_reflection]
      constructor
      · intro h
        apply ih.2
        exact (neg_eq_iff_eq_neg.mp (by simpa using h))
      · intro h v hv
        have hy : LinearEquiv.det y.val = 1 := by
          simpa using h
        simpa only [mul_assoc] using M.mul_mem (hM v w) (ih.1 hy)
  intro g hg
  have hg' := mem_specialOrthogonalGroup_iff.mp hg
  exact (hind ⟨g, hg'.1⟩).1 hg'.2

/-- The monoid generated by pairs of reflections is exactly the special orthogonal group of
a finite-dimensional nondegenerate quadratic space in characteristic different from two. -/
theorem closure_reflection_mul_eq_specialOrthogonalGroup
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Submonoid.closure {g : V ≃ₗ[K] V |
      ∃ (v w : V) (_ : Invertible (Q v)) (_ : Invertible (Q w)),
        reflection Q v * reflection Q w = g} =
      (specialOrthogonalGroup Q).toSubmonoid := by
  apply le_antisymm
  · apply Submonoid.closure_le.mpr
    rintro _ ⟨v, w, hv, hw, rfl⟩
    apply mem_specialOrthogonalGroup_iff.mpr
    exact ⟨(orthogonalGroup Q).mul_mem
      (reflection_mem_orthogonalGroup Q v) (reflection_mem_orthogonalGroup Q w), by simp⟩
  · exact specialOrthogonalGroup_le_of_reflection_mul_mem Q hQ _
      (fun v w hv hw ↦ Submonoid.subset_closure ⟨v, w, hv, hw, rfl⟩)

end TauCeti.QuadraticMap
