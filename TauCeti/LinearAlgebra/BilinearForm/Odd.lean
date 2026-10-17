/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# Diagonalization of odd unimodular forms

A symmetric perfect pairing over a local ring has an orthogonal basis with unit
self-pairings whenever it represents a unit. In particular, odd unimodular dyadic
forms are diagonalizable, unlike even ones such as the hyperbolic plane.

Splitting off an arbitrary unit vector need not leave a form representing a unit.
If its complement has only nonunit norms, mix the vector with a vector in that
complement before splitting. This keeps the induction in the odd case.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

namespace TauCeti.BilinForm

open Module LinearMap.BilinForm

variable {R M : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] {B : LinearMap.BilinForm R M}

/-- The unit-vector adjustment used to keep the complementary form odd. -/
private theorem exists_isUnit_apply_self_orthogonal
    (hB : B.IsSymm) {x : M} (hx : IsUnit (B x x))
    (u w : B.orthogonal (R ∙ x))
    (hu : ¬ IsUnit (B u u)) (hw : ¬ IsUnit (B w w)) (huw : IsUnit (B u w)) :
    ∃ z : M, IsUnit (B z z) ∧
      ∃ y : B.orthogonal (R ∙ z), IsUnit (B y y) := by
  let q := IsLocalRing.residue R
  have hxu : B x u = 0 := u.property x (Submodule.mem_span_singleton_self x)
  have hxw : B x w = 0 := w.property x (Submodule.mem_span_singleton_self x)
  have hqu : q (B u u) = 0 := not_ne_iff.mp
    (fun h ↦ hu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h))
  have hqw : q (B w w) = 0 := not_ne_iff.mp
    (fun h ↦ hw ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h))
  let z := x + u
  have hzz : B z z = B x x + B u u := by
    simp [z, hxu, hB.eq u x]
  have hqzz : q (B z z) = q (B x x) := by simp [hzz, hqu]
  have hz : IsUnit (B z z) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    (hqzz ▸ (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hx)
  have hzw : B z w = B u w := by simp [z, hxw]
  obtain ⟨c, hc⟩ := (hz.dvd : B z z ∣ B z w)
  have hc' : c * B z z = B z w := by rw [hc]; ring
  have hy : w - c • z ∈ B.orthogonal (R ∙ z) := by
    simp [orthogonal, hc']
  have hnorm : B (w - c • z) (w - c • z) = B w w - c * B z w := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hB.eq w z]
    rw [hc']
    ring
  have hqc : q c ≠ 0 := by
    intro hzero
    have h := congrArg q hc'
    simp only [map_mul, hzero, zero_mul, hzw] at h
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr huw h.symm
  have hyunit : IsUnit (B (w - c • z) (w - c • z)) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [hnorm, map_sub, map_mul, hqw, zero_sub, neg_ne_zero, hzw]
    exact mul_ne_zero hqc ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr huw)
  exact ⟨z, hz, ⟨w - c • z, hy⟩, hyunit⟩

/-- A unit vector can be chosen with an odd complement unless that complement has rank zero. -/
private theorem exists_isUnit_apply_self_with_odd_complement
    [Free R M] [Module.Finite R M] [B.IsPerfPair] (hB : B.IsSymm)
    (hodd : ∃ x, IsUnit (B x x)) :
    ∃ x : M, IsUnit (B x x) ∧
      (finrank R (B.orthogonal (R ∙ x)) ≠ 0 →
        ∃ y : B.orthogonal (R ∙ x), IsUnit (B y y)) := by
  classical
  obtain ⟨x, hx⟩ := hodd
  by_cases ho : ∃ y : B.orthogonal (R ∙ x), IsUnit (B y y)
  · exact ⟨x, hx, fun _ ↦ ho⟩
  have heven : ∀ y : B.orthogonal (R ∙ x), ¬ IsUnit (B y y) := by
    simpa only [not_exists] using ho
  let N := B.orthogonal (R ∙ x)
  have hc := B.isCompl_span_singleton_orthogonal_of_isUnit x hx
  obtain ⟨hfinite, hfree⟩ := N.finite_free_of_isCompl hc.symm
  have hdouble := B.orthogonal_orthogonal_of_isCompl hB.isRefl
    (LinearMap.IsPerfPair.separatingRight (p := B) inferInstance) (R ∙ x) hc
  have hperf : (B.restrict N).IsPerfPair :=
    B.isPerfPair_restrict_of_isCompl_orthogonal hB N (by rw [hdouble]; exact hc.symm)
  by_cases hn : finrank R N = 0
  · exact ⟨x, hx, fun h ↦ (h hn).elim⟩
  let v := Module.finBasis R N
  let i : Fin (finrank R N) := ⟨0, Nat.pos_of_ne_zero hn⟩
  obtain ⟨w, hw⟩ := (LinearMap.IsPerfPair.bijective_left (B.restrict N)).surjective (v.coord i)
  have huw : B (v i) w = 1 := by
    have h := congrArg (fun f : Module.Dual R N ↦ f (v i)) hw
    simpa [restrict_apply, hB.eq (v i) w] using h
  obtain ⟨z, hz, y, hy⟩ := exists_isUnit_apply_self_orthogonal hB hx
    (v i) w (heven _) (heven _) (huw ▸ isUnit_one)
  exact ⟨z, hz, fun _ ↦ ⟨y, hy⟩⟩

/-- A symmetric perfect pairing on a finite free module over a local ring is
unit-diagonalizable if it represents a unit. No Henselian or residue-field
hypothesis is needed. -/
theorem exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self
    (hB : B.IsSymm) [B.IsPerfPair] {n : ℕ} (b : Basis (Fin n) R M)
    (hodd : ∃ x, IsUnit (B x x)) :
    ∃ c : Basis (Fin n) R M, B.iIsOrtho c ∧ ∀ i, IsUnit (B (c i) (c i)) := by
  classical
  let := Free.of_basis b
  let := Module.Finite.of_basis b
  induction n generalizing M with
  | zero => exact ⟨b, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
    -- A unit vector splits off; choose it so a nonzero complement stays odd.
    obtain ⟨x, hx, hoddN⟩ := exists_isUnit_apply_self_with_odd_complement hB hodd
    let N := B.orthogonal (R ∙ x)
    have hc := B.isCompl_span_singleton_orthogonal_of_isUnit x hx
    obtain ⟨hfinite, hfree⟩ := N.finite_free_of_isCompl hc.symm
    have hn : finrank R N = n := by
      have h : finrank R N + 1 = finrank R M :=
        finrank_orthogonal_span_singleton_add_one_of_dvd B
          hx.mem_nonZeroDivisors (fun _ ↦ hx.dvd)
      have hb := Module.finrank_eq_card_basis b
      simp only [Fintype.card_fin] at hb
      omega
    have hperf : (B.restrict N).IsPerfPair := by
      have hdouble := B.orthogonal_orthogonal_of_isCompl hB.isRefl
        (LinearMap.IsPerfPair.separatingRight (p := B) inferInstance) (R ∙ x) hc
      exact B.isPerfPair_restrict_of_isCompl_orthogonal hB N
        (by simpa only [N, hdouble] using hc.symm)
    have hbasis : ∃ v : Basis (Fin n) R N,
        (B.restrict N).iIsOrtho v ∧ ∀ i, IsUnit (B (v i) (v i)) := by
      by_cases hn0 : n = 0
      · rw [hn0] at hn ⊢
        exact ⟨Module.finBasisOfFinrankEq R N hn, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
      · exact ih (hB.restrict N) (Module.finBasisOfFinrankEq R N hn)
          (hoddN (by simpa [N, hn] using hn0))
    obtain ⟨v, hv, hu⟩ := hbasis
    obtain ⟨c, hc, hzero, hsucc⟩ :=
      hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton
        hx.mem_nonZeroDivisors (fun _ ↦ hx.dvd) hv
    exact ⟨c, hc, Fin.forall_fin_succ.mpr
      ⟨hzero ▸ hx, fun i ↦ (hsucc i) ▸ hu i⟩⟩

end TauCeti.BilinForm

end
