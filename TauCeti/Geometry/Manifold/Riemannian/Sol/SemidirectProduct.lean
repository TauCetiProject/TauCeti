/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.Geometry.Manifold.Riemannian.Sol.Isotropy

/-!
# The semidirect-product isometries of Sol

The eight dihedral isometries fixing the identity of Sol are also automorphisms of its
solvable group structure. They therefore act on the translations, giving a faithful
homomorphism from `Sol ⋊ D₄` to the Riemannian isometry group. Its image consists exactly of
isometries whose translation to fix the identity lies in the dihedral subgroup.

This separates the algebraic assembly of the isometry group from stabilizer exhaustion:
surjectivity holds precisely when every isometry fixing the identity is dihedral. No such
exhaustion result is assumed in constructing the action or proving its faithfulness.

The construction uses Mathlib's `SemidirectProduct.lift`, following the corresponding
translation and orthogonal-action assembly in `TauCeti.Geometry.Manifold.Riemannian.Nil`.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 470–471 (Sol and its isometry group).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff

namespace TauCeti.Sol

/-- The dihedral isometries act by automorphisms of the solvable group Sol. -/
def dihedralMulAut : DihedralGroup 4 →* MulAut Sol where
  toFun g :=
    { (dihedralToIsom g).toDiffeomorph.toEquiv with
      map_mul' := dihedralToIsom_map_mul g }
  map_one' := MulEquiv.ext fun p => by simp
  map_mul' g h := MulEquiv.ext fun p => by simp

/-- The group automorphism and the Riemannian isometry have the same underlying map. -/
@[simp]
theorem dihedralMulAut_apply (g : DihedralGroup 4) (p : Sol) :
    dihedralMulAut g p = dihedralToIsom g p := (rfl)

/-- The dihedral action on the solvable group is faithful. -/
theorem dihedralMulAut_injective : Function.Injective dihedralMulAut := by
  intro g h hgh
  apply dihedralToIsom_injective
  exact RiemannianIsometry.ext fun p => by
    simpa only [dihedralMulAut_apply] using DFunLike.congr_fun hgh p

/-- Conjugating a translation by a dihedral isometry translates by the transformed point. -/
theorem dihedralToIsom_conj_toIsom (g : DihedralGroup 4) (p : Sol) :
    dihedralToIsom g * toIsom p * (dihedralToIsom g)⁻¹ = toIsom (dihedralMulAut g p) := by
  apply RiemannianIsometry.ext
  intro q
  simp [dihedralToIsom_map_mul]

/-- Translations and dihedral automorphisms act on Sol by Riemannian isometries. -/
def semidirectProductToIsom :
    Sol ⋊[dihedralMulAut] DihedralGroup 4 →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol :=
  SemidirectProduct.lift toIsom dihedralToIsom fun g => MonoidHom.ext fun p =>
    (dihedralToIsom_conj_toIsom g p).symm

/-- The semidirect-product element `(p, g)` acts by first applying `g`, then translating by `p`. -/
@[simp]
theorem semidirectProductToIsom_apply
    (a : Sol ⋊[dihedralMulAut] DihedralGroup 4) (p : Sol) :
    semidirectProductToIsom a p = a.left * dihedralToIsom a.right p := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right a]
  rw [map_mul, RiemannianIsometry.mul_apply, semidirectProductToIsom,
    SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, toIsom_apply]

/-- The left factor of the semidirect product gives the translation isometries. -/
@[simp]
theorem semidirectProductToIsom_inl (p : Sol) :
    semidirectProductToIsom (SemidirectProduct.inl p) = toIsom p :=
  SemidirectProduct.lift_inl _ _ _ p

/-- The right factor of the semidirect product gives the dihedral isometries. -/
@[simp]
theorem semidirectProductToIsom_inr (g : DihedralGroup 4) :
    semidirectProductToIsom (SemidirectProduct.inr g) = dihedralToIsom g :=
  SemidirectProduct.lift_inr _ _ _ g

/-- Distinct semidirect-product elements give distinct Riemannian isometries of Sol. -/
theorem semidirectProductToIsom_injective : Function.Injective semidirectProductToIsom := by
  intro a b hab
  have hl : a.left = b.left := by
    simpa only [semidirectProductToIsom_apply, dihedralToIsom_apply_one, mul_one] using
      DFunLike.congr_fun hab 1
  refine SemidirectProduct.ext hl (dihedralToIsom_injective (RiemannianIsometry.ext fun p => ?_))
  exact mul_left_cancel (by
    simpa only [semidirectProductToIsom_apply, hl] using DFunLike.congr_fun hab p)

/-- The semidirect-product image consists exactly of isometries whose translation to fix the
identity is dihedral. The translation is determined by the image of the identity. -/
theorem mem_range_semidirectProductToIsom_iff (Φ : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol) :
    Φ ∈ semidirectProductToIsom.range ↔ toIsom ((Φ 1)⁻¹) * Φ ∈ dihedralToIsom.range := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a.right, RiemannianIsometry.ext fun p => ?_⟩
    simp only [semidirectProductToIsom_apply, dihedralToIsom_apply_one, mul_one,
      RiemannianIsometry.mul_apply, toIsom_apply, inv_mul_cancel_left]
  · rintro ⟨g, hg⟩
    refine ⟨⟨Φ 1, g⟩, RiemannianIsometry.ext fun p => ?_⟩
    have hp := DFunLike.congr_fun hg p
    simp only [RiemannianIsometry.mul_apply, toIsom_apply] at hp
    simp only [semidirectProductToIsom_apply]
    rw [hp, mul_inv_cancel_left]

/-- Identifying the full isometry group with the semidirect product reduces exactly to
exhausting the isometries fixing the identity by the eight dihedral isometries. -/
theorem semidirectProductToIsom_surjective_iff :
    Function.Surjective semidirectProductToIsom ↔
      ∀ Φ : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol, Φ 1 = 1 → Φ ∈ dihedralToIsom.range := by
  constructor
  · intro h Φ hΦ
    have hm := (mem_range_semidirectProductToIsom_iff Φ).mp (h Φ)
    simpa only [hΦ, inv_one, map_one, one_mul] using hm
  · intro h Φ
    apply (mem_range_semidirectProductToIsom_iff Φ).mpr
    apply h
    simp only [RiemannianIsometry.mul_apply, toIsom_apply, inv_mul_cancel]

end TauCeti.Sol
