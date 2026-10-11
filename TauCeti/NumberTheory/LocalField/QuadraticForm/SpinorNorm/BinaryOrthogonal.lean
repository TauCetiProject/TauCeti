/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.SpinorNorm.Basic
import Mathlib.GroupTheory.IndexNormal
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Binary

/-!
# The orthogonal spinor norm of an anisotropic binary form over a local field

For a nondegenerate anisotropic binary form `Q ≅ ⟨a, b⟩` over a nonarchimedean local field,
the spinor norm on `SO(Q)` has image the square classes of the norm group of the quadratic
extension `K(√(-a b))`, an index-two subgroup. The image on `O(Q)` additionally contains the
class of `a`. It is therefore all square classes exactly when `a` is not a norm; otherwise it
still has index two. This is the anisotropic binary row of the local spinor-norm calculation.

## Main results

* The surjectivity criterion identifies when the orthogonal spinor norm is onto.
* The two image-index theorems give indices two and one according to norm membership.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §55 and §63.
-/

public section

namespace CliffordAlgebra

open TauCeti QuadraticMap

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V]

/-- For an anisotropic binary form `Q ≅ ⟨a, b⟩` over a nonarchimedean local field, the
orthogonal spinor norm is surjective exactly when `a` is not a norm from `K(√(-a b))`.
The condition is independent of the chosen diagonalization, as the left side shows. -/
theorem orthogonalSpinorNorm_surjective_iff_not_mem_quadraticNormSubgroup_of_anisotropic_binary
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hani : Q.Anisotropic) {a b : Kˣ}
    (h : Q.Equivalent (weightedSumSquares K ![(a : K), (b : K)])) :
    letI : FiniteDimensional K V := by
      obtain ⟨e⟩ := h
      exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective
    Function.Surjective (orthogonalSpinorNorm Q hQ) ↔
      a ∉ quadraticNormSubgroup (-(a * b : K)) := by
  have : FiniteDimensional K V := by
    obtain ⟨e⟩ := h
    exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective
  let N := quadraticNormSubgroup (-(a * b : K))
  let H : Subgroup (Multiplicative (SquareClassGroup K)) := N.map squareClassHom
  have hV : Module.finrank K V = 2 := by
    obtain ⟨e⟩ := h
    simpa using e.toLinearEquiv.finrank_eq
  have hker : (squareClassHom (K := K)).ker ≤ N := fun x hx ↦
    square_le_quadraticNormSubgroup _ (Subgroup.mem_square.mpr (by simpa using hx))
  have hcomap : H.comap squareClassHom = N := N.comap_map_eq_self hker
  have hmem : squareClassHom a ∈ H ↔ a ∈ N := by
    rw [← hcomap]
    rfl
  have hindex : H.index = 2 := by
    simpa only [H, N, range_spinorNorm_of_equivalent_binary Q hQ h] using
      index_range_spinorNorm_of_finrank_eq_two_of_anisotropic Q hQ hV hani
  have hrange : (orthogonalSpinorNorm Q hQ).range =
      H ⊔ Subgroup.zpowers (squareClassHom a) :=
    range_orthogonalSpinorNorm_of_equivalent_binary Q hQ h
  constructor
  · intro hsurj ha
    have htop : ((orthogonalSpinorNorm Q hQ).range :
        Subgroup (Multiplicative (SquareClassGroup K))) = ⊤ := by
      apply eq_top_iff.mpr
      intro x _
      obtain ⟨g, rfl⟩ := hsurj x
      exact ⟨g, rfl⟩
    rw [hrange] at htop
    have hle : Subgroup.zpowers (squareClassHom a) ≤ H :=
      Subgroup.zpowers_le.mpr (hmem.mpr ha)
    have hH : H = ⊤ := by
      rw [sup_eq_left.mpr hle] at htop
      exact htop
    have : H.index = 1 := by rw [hH, Subgroup.index_top]
    omega
  · intro ha
    have hcoatom : IsCoatom H := Subgroup.isCoatom_of_index_prime (hindex ▸ Nat.prime_two)
    suffices htop : ((orthogonalSpinorNorm Q hQ).range :
        Subgroup (Multiplicative (SquareClassGroup K))) = ⊤ by
      intro x
      have hx : x ∈ ((orthogonalSpinorNorm Q hQ).range :
          Subgroup (Multiplicative (SquareClassGroup K))) := htop.symm ▸ Subgroup.mem_top x
      exact hx
    rw [hrange]
    exact (SetLike.isCoatom_iff.mp hcoatom).2 _ (squareClassHom a) le_sup_left
      (mt hmem.mp ha) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

/-- The orthogonal spinor-norm image of an anisotropic binary local form has index two when the
first diagonal coefficient is a norm from the discriminant extension. -/
theorem index_range_orthogonalSpinorNorm_of_anisotropic_binary_of_mem_quadraticNormSubgroup
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hani : Q.Anisotropic) {a b : Kˣ}
    (h : Q.Equivalent (weightedSumSquares K ![(a : K), (b : K)]))
    (ha : a ∈ quadraticNormSubgroup (-(a * b : K))) :
    letI : FiniteDimensional K V := by
      obtain ⟨e⟩ := h
      exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective
    ((orthogonalSpinorNorm Q hQ).range :
      Subgroup (Multiplicative (SquareClassGroup K))).index = 2 := by
  have : FiniteDimensional K V := by
    obtain ⟨e⟩ := h
    exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective
  have hV : Module.finrank K V = 2 := by
    obtain ⟨e⟩ := h
    simpa using e.toLinearEquiv.finrank_eq
  have hmem : squareClassHom a ∈
      (quadraticNormSubgroup (-(a * b : K))).map squareClassHom :=
    ⟨a, ha, rfl⟩
  rw [range_orthogonalSpinorNorm_of_equivalent_binary Q hQ h,
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr hmem),
    ← range_spinorNorm_of_equivalent_binary Q hQ h]
  exact index_range_spinorNorm_of_finrank_eq_two_of_anisotropic Q hQ hV hani

/-- If the first diagonal coefficient is not a norm, the orthogonal spinor norm of an
anisotropic binary local form is surjective, so its image has index one. -/
theorem index_range_orthogonalSpinorNorm_of_anisotropic_binary_of_not_mem_quadraticNormSubgroup
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hani : Q.Anisotropic) {a b : Kˣ}
    (h : Q.Equivalent (weightedSumSquares K ![(a : K), (b : K)]))
    (ha : a ∉ quadraticNormSubgroup (-(a * b : K))) :
    letI : FiniteDimensional K V := by
      obtain ⟨e⟩ := h
      exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective
    ((orthogonalSpinorNorm Q hQ).range :
      Subgroup (Multiplicative (SquareClassGroup K))).index = 1 := by
  have : FiniteDimensional K V := by
    obtain ⟨e⟩ := h
    exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective
  have hsurj :=
    (orthogonalSpinorNorm_surjective_iff_not_mem_quadraticNormSubgroup_of_anisotropic_binary
      Q hQ hani h).mpr ha
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.index_top]

end CliffordAlgebra
