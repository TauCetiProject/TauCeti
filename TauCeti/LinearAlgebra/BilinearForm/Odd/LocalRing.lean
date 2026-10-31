/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.LocalRing
public import TauCeti.RingTheory.LocalRing.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Odd unimodular forms over local rings

A symmetric unimodular form over a local ring is **odd** when it represents a unit. Such a form
has an orthogonal basis whose self-pairings are all units. This is the diagonalization step for
odd unimodular lattices over `ℤ₂`.

The key point in residue characteristic two is that splitting off an arbitrary unit-norm vector
can leave an even orthogonal complement. When that happens, a unit off-diagonal entry in the
complement lets us replace the vector by one whose orthogonal complement again represents a unit.
Induction can therefore continue without assuming that two is invertible.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_orthogonal_isUnit_pair`: an odd unimodular form of rank at
  least two represents units on two orthogonal vectors.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self`: an odd
  unimodular form has a unit-diagonal orthogonal basis.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_orthogonal_span_singleton`: so does
  the orthogonal complement of a unit vector, once that complement represents a unit.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

namespace LinearMap.BilinForm

open Module TauCeti

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}

/-- **Two orthogonal unit values in an odd unimodular form.** A symmetric form of rank at least
two whose Gram determinant is a unit and which represents a unit has two orthogonal vectors with
unit self-pairings. The result needs no inverse of two. -/
theorem IsSymm.exists_orthogonal_isUnit_pair (hB : B.IsSymm) {n : ℕ}
    (b : Basis (Fin (n + 2)) R M) (hdet : IsUnit (B.toMatrix b).det)
    (hodd : ∃ x, IsUnit (B x x)) :
    ∃ x y : M, IsUnit (B x x) ∧ IsUnit (B y y) ∧ B x y = 0 := by
  classical
  obtain ⟨x, hx⟩ := hodd
  -- If the complement of the initial unit line has no unit norm, a unit off-diagonal entry there
  -- supplies a replacement vector whose complement does have one.
  obtain ⟨t, hTdet⟩ := hB.exists_basis_orthogonal_span_singleton_isUnit_det b hdet hx
  by_cases hTodd : ∃ y : B.orthogonal (R ∙ x), IsUnit (B.restrict _ y y)
  · obtain ⟨y, hy⟩ := hTodd
    refine ⟨x, y, hx, hy, ?_⟩
    exact y.2 x (Submodule.mem_span_singleton_self x)
  · have hdiag (y : B.orthogonal (R ∙ x)) :
        ¬ IsUnit (B.restrict _ y y) := fun hy ↦ hTodd ⟨y, hy⟩
    obtain ⟨i, -, hi⟩ :=
      exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det
        (B.restrict _) t (hdiag (t 0)) hTdet
    let e : M := t 0
    let f : M := t i
    have hxe : B x e = 0 := (t 0).2 x (Submodule.mem_span_singleton_self x)
    have hxf : B x f = 0 := (t i).2 x (Submodule.mem_span_singleton_self x)
    have hee : ¬ IsUnit (B e e) := by
      simpa only [e, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using
        hdiag (t 0)
    have hff : ¬ IsUnit (B f f) := by
      simpa only [f, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using
        hdiag (t i)
    have hef : IsUnit (B e f) := by
      simpa only [e, f, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using hi
    -- Replacing `x` by `x + e` keeps a unit norm and creates a unit pairing with `f`.
    let y := x + e
    have hyy_eq : B y y = B x x + B e e := by
      simp only [y, map_add, LinearMap.add_apply, hxe, hB.eq e x, zero_add, add_zero]
    have hyy : IsUnit (B y y) := hyy_eq ▸ isUnit_add_of_isUnit_of_not_isUnit hx hee
    have hyf : B y f = B e f := by
      simp only [y, map_add, LinearMap.add_apply, hxf, zero_add]
    have hyfu : IsUnit (B y f) := hyf ▸ hef
    let a : R := (↑hyy.unit⁻¹ : R) * B y f
    have ha : a * B y y = B y f := by
      calc
        a * B y y = (↑hyy.unit⁻¹ : R) * B y y * B y f := by simp only [a]; ring
        _ = B y f := by rw [hyy.val_inv_mul, one_mul]
    have hau : IsUnit a := hyy.unit⁻¹.isUnit.mul hyfu
    let z := f - a • y
    -- Orthogonally project `f` away from `y`; its remaining norm is still a unit.
    have hyz : B y z = 0 := by
      simp only [z, map_sub, map_smul, smul_eq_mul, ha, sub_self]
    have hzz_eq : B z z = B f f - a * B y f := by
      simp only [z, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hB.eq f y]
      rw [ha]
      ring
    have hzz : IsUnit (B z z) := hzz_eq ▸
      isUnit_sub_of_not_isUnit_of_isUnit hff (hau.mul hyfu)
    exact ⟨y, z, hyy, hzz, hyz⟩

/-- **Odd unimodular forms are diagonalizable over a local ring.** If a symmetric form has a
unit Gram determinant and represents a unit, then it has an orthogonal basis all of whose
self-pairings are units.

This is the odd counterpart of binary-block decomposition for even forms. In particular it
applies to type-I unimodular Jordan constituents over `ℤ₂`. -/
theorem IsSymm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self (hB : B.IsSymm)
    {n : ℕ} (b : Basis (Fin n) R M) (hdet : IsUnit (B.toMatrix b).det)
    (hodd : ∃ x, IsUnit (B x x)) :
    ∃ c : Basis (Fin n) R M, B.iIsOrtho c ∧ ∀ i, IsUnit (B (c i) (c i)) := by
  classical
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    rcases n with _ | _ | m
    · exact ⟨b, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
    · refine ⟨b, ?_, fun i ↦ ?_⟩
      · intro i j hij
        exact (hij (Fin.ext (by omega))).elim
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      rw [Matrix.det_fin_one] at hdet
      simpa only [toMatrix_apply] using hdet
    · obtain ⟨x, y, hx, hy, hxy⟩ := hB.exists_orthogonal_isUnit_pair b hdet hodd
      obtain ⟨t, hTdet⟩ := hB.exists_basis_orthogonal_span_singleton_isUnit_det b hdet hx
      have hyMem : y ∈ B.orthogonal (R ∙ x) :=
        mem_orthogonal_iff.mpr fun z hz ↦ by
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
          simp [hxy]
      obtain ⟨d, hd, hdu⟩ := ih (m + 1) (by omega) (hB.restrict _) t hTdet ⟨⟨y, hyMem⟩, hy⟩
      obtain ⟨c, hc, hcu, -⟩ :=
        hB.isRefl.exists_orthogonal_basis_isUnit_apply_self_eq_cons hx hd hdu
      exact ⟨c, hc, hcu⟩

/-- **The orthogonal complement of a unit vector in an odd unimodular form.** Let `B` be a
symmetric form whose Gram determinant in a basis of size `n + 1` is a unit over a local ring. If
`x` has unit self-pairing and is orthogonal to a vector `y` with unit self-pairing, then the
orthogonal complement of `x` has an orthogonal basis of size `n` all of whose self-pairings are
units.

Together with `LinearMap.BilinForm.IsRefl.exists_orthogonal_basis_isUnit_apply_self_eq_cons`,
this extends `x` to a unit-diagonal orthogonal basis of the whole module. -/
theorem IsSymm.exists_orthogonal_basis_isUnit_orthogonal_span_singleton (hB : B.IsSymm)
    {n : ℕ} (b : Basis (Fin (n + 1)) R M) (hdet : IsUnit (B.toMatrix b).det) {x y : M}
    (hx : IsUnit (B x x)) (hy : IsUnit (B y y)) (hxy : B x y = 0) :
    ∃ t : Basis (Fin n) R (B.orthogonal (R ∙ x)),
      (B.restrict (B.orthogonal (R ∙ x))).iIsOrtho t ∧ ∀ i, IsUnit (B (t i) (t i)) := by
  obtain ⟨t, hTdet⟩ := hB.exists_basis_orthogonal_span_singleton_isUnit_det b hdet hx
  have hyMem : y ∈ B.orthogonal (R ∙ x) :=
    mem_orthogonal_iff.mpr fun z hz ↦ by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      simp [hxy]
  exact (hB.restrict _).exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self t hTdet
    ⟨⟨y, hyMem⟩, hy⟩

end LinearMap.BilinForm

end
