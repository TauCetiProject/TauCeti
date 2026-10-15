/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.SemidirectProduct
public import TauCeti.Geometry.Manifold.Riemannian.Sol.Stabilizer

/-!
# The full isometry group of Sol

The full Riemannian isometry group of Sol is `Sol ⋊ D₄`. Every isometry factors uniquely
as a left translation followed by one of the eight dihedral automorphisms. The translation
is its value at the identity; removing that translation recovers its dihedral part.

This completes the faithful semidirect-product action from
`TauCeti.Geometry.Manifold.Riemannian.Sol.SemidirectProduct` using the stabilizer
classification from `TauCeti.Geometry.Manifold.Riemannian.Sol.Stabilizer`.
The result identifies the groups algebraically; no topology on the isometry group is used.
The equivalence and its computation rules follow the corresponding API for Nil in
`TauCeti.Geometry.Manifold.Riemannian.Nil.Stabilizer`.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 470–471 (Sol and its isometry group).
-/

public noncomputable section

open Manifold
open scoped ContDiff

namespace TauCeti.Sol

local notation "J" => 𝓘(ℝ, ℝ × ℝ × ℝ)

/-- Every Riemannian isometry of Sol is a left translation followed by a dihedral
isometry. Thus the canonical semidirect-product action exhausts the full isometry group. -/
theorem semidirectProductToIsom_surjective : Function.Surjective semidirectProductToIsom := by
  apply semidirectProductToIsom_surjective_iff.mpr
  intro Φ hΦ
  rw [range_dihedralToIsom_eq_stabilizer]
  simpa only [MulAction.mem_stabilizer_iff, RiemannianIsometry.smul_def] using hΦ

/-- The full Riemannian isometry group of Sol is `Sol ⋊ D₄`, with its canonical
translation and dihedral actions. This is an isomorphism of groups. -/
def semidirectProductIsomMulEquiv :
    Sol ⋊[dihedralMulAut] DihedralGroup 4 ≃* Isom J Sol :=
  MulEquiv.ofBijective semidirectProductToIsom
    ⟨semidirectProductToIsom_injective, semidirectProductToIsom_surjective⟩

/-- The full-group identification acts by the existing semidirect-product action. -/
@[simp] theorem semidirectProductIsomMulEquiv_apply
    (a : Sol ⋊[dihedralMulAut] DihedralGroup 4) :
    semidirectProductIsomMulEquiv a = semidirectProductToIsom a := (rfl)

/-- The translation part recovered from an arbitrary isometry is its value at the identity. -/
@[simp] theorem semidirectProductIsomMulEquiv_symm_apply_left (Φ : Isom J Sol) :
    (semidirectProductIsomMulEquiv.symm Φ).left = Φ 1 := by
  have h := congrArg (fun Ψ : Isom J Sol => Ψ 1)
    (semidirectProductIsomMulEquiv.apply_symm_apply Φ)
  simpa only [semidirectProductIsomMulEquiv_apply, semidirectProductToIsom_apply,
    dihedralToIsom_apply_one, mul_one] using h

/-- Removing the translation by the image of the identity recovers the dihedral part
of an arbitrary isometry. -/
@[simp] theorem dihedralToIsom_semidirectProductIsomMulEquiv_symm_apply_right
    (Φ : Isom J Sol) :
    dihedralToIsom (semidirectProductIsomMulEquiv.symm Φ).right = (toIsom (Φ 1))⁻¹ * Φ := by
  have h := semidirectProductIsomMulEquiv.apply_symm_apply Φ
  apply RiemannianIsometry.ext
  intro p
  have hp := DFunLike.congr_fun h p
  rw [semidirectProductIsomMulEquiv_apply, semidirectProductToIsom_apply,
    semidirectProductIsomMulEquiv_symm_apply_left] at hp
  simpa only [RiemannianIsometry.mul_apply, ← map_inv, toIsom_apply,
    inv_mul_cancel_left] using congrArg (fun q : Sol => (Φ 1)⁻¹ * q) hp

end TauCeti.Sol
