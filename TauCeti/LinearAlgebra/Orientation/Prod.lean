/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basis
public import TauCeti.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Products of linear orientations

The canonical product orientation places the first factor before the second. Its construction
uses relative basis signs and actual product-basis determinants, including empty factor bases.
-/

public section
noncomputable section

open Module

namespace Orientation

variable {R E F : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  {m n : ℕ}

private def prodOfBases (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (b : Basis (Fin m) R E) (c : Basis (Fin n) R F) :
    Orientation R (E × F) (Fin (m + n)) :=
  let a := (signBasis o b : R) * (signBasis p c : R)
  rayOfNeZero R (a • ((b.prod c).reindex finSumFinEquiv).det) (by
    apply smul_ne_zero
    · exact mul_ne_zero (by exact_mod_cast (signBasis o b).ne_zero)
        (by exact_mod_cast (signBasis p c).ne_zero)
    · exact Basis.det_ne_zero _)

private theorem prodOfBases_eq (o : Orientation R E (Fin m))
    (p : Orientation R F (Fin n)) (b b' : Basis (Fin m) R E)
    (c c' : Basis (Fin n) R F) : prodOfBases o p b c = prodOfBases o p b' c' := by
  unfold prodOfBases
  rw [ray_eq_iff]
  let B := (b.prod c).reindex finSumFinEquiv
  let B' := (b'.prod c').reindex finSumFinEquiv
  have hdet : B.det B' = b.det b' * c.det c' := by
    rw [Basis.det_reindex]
    have he : (B' : Fin (m + n) → E × F) ∘ finSumFinEquiv = b'.prod c' := by
      funext i
      -- The reindexed basis is B'; display its application to use the reindex equation.
      change ((b'.prod c').reindex finSumFinEquiv) (finSumFinEquiv i) = _
      rw [Basis.reindex_apply, Equiv.symm_apply_apply]
    rw [he]
    exact Basis.det_prod b b' c c'
  -- Unfold the two local product bases inside their determinant rays.
  change SameRay R (_ • B.det) (_ • B'.det)
  rw [B.det.eq_smul_basis_det B', smul_smul, hdet]
  apply sameRay_smul_smul_of_mul_nonneg
  have hpos := mul_pos (signBasis_mul_det_mul_pos o b b') (signBasis_mul_det_mul_pos p c c')
  convert hpos.le using 1; ring

variable [Module.Free R E] [Module.Finite R E]
  [Module.Free R F] [Module.Finite R F]

/-- The canonical product of actual linear orientations, with the first factor before the second.
Both signs of each factor are retained, including in dimension zero. -/
def prod (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    Orientation R (E × F) (Fin (m + n)) :=
  prodOfBases o p (Module.finBasisOfFinrankEq R E hm) (Module.finBasisOfFinrankEq R F hn)

/-- The canonical product can be computed in any two factor bases using their relative signs. -/
theorem prod_eq_rayOfNeZero (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n)
    (b : Basis (Fin m) R E) (c : Basis (Fin n) R F) :
    prod o p hm hn =
      rayOfNeZero R (((signBasis o b : R) * (signBasis p c : R)) •
        ((b.prod c).reindex finSumFinEquiv).det) (by
          apply smul_ne_zero
          · exact mul_ne_zero (by exact_mod_cast (signBasis o b).ne_zero)
              (by exact_mod_cast (signBasis p c).ne_zero)
          · exact Basis.det_ne_zero _) := by
  exact prodOfBases_eq o p _ b _ c

/-- The product of two basis orientations is the orientation of their ordered product basis. -/
@[simp]
theorem prod_basis_orientation (b : Basis (Fin m) R E) (c : Basis (Fin n) R F)
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    prod b.orientation c.orientation hm hn =
      ((b.prod c).reindex finSumFinEquiv).orientation := by
  rw [prod_eq_rayOfNeZero _ _ hm hn b c]
  simp only [signBasis_orientation, Units.val_one, Int.cast_one, mul_one, one_smul]
  -- A basis orientation is by definition the ray of its nonzero determinant form.
  rfl

/-- Reversing the first factor reverses the product orientation, including dimension zero. -/
@[simp]
theorem prod_neg_left (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    prod (-o) p hm hn = -prod o p hm hn := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  rw [prod_eq_rayOfNeZero _ _ hm hn b c, prod_eq_rayOfNeZero _ _ hm hn b c]
  simp only [signBasis_neg, Units.val_neg, Int.cast_neg, neg_mul, neg_rayOfNeZero]
  congr 1
  module

/-- Reversing the second factor reverses the product orientation, including dimension zero. -/
@[simp]
theorem prod_neg_right (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    prod o (-p) hm hn = -prod o p hm hn := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  rw [prod_eq_rayOfNeZero _ _ hm hn b c, prod_eq_rayOfNeZero _ _ hm hn b c]
  simp only [signBasis_neg, Units.val_neg, Int.cast_neg, mul_neg, neg_rayOfNeZero]
  congr 1
  module

/-- Simultaneous reversal of both factors preserves the product orientation. -/
theorem prod_neg_neg (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    prod (-o) (-p) hm hn = prod o p hm hn := by
  rw [prod_neg_left, prod_neg_right]
  exact neg_neg (prod o p hm hn)

/-- The relative sign in a product basis is the product of the two relative factor signs. -/
theorem signBasis_prod (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n)
    (b : Basis (Fin m) R E) (c : Basis (Fin n) R F) :
    signBasis (prod o p hm hn) ((b.prod c).reindex finSumFinEquiv) =
      signBasis o b * signBasis p c := by
  rcases b.orientation_eq_or_eq_neg o with ho | ho <;>
    rcases c.orientation_eq_or_eq_neg p with hp | hp <;> subst o <;> subst p <;> simp

variable {E' F' : Type*} [AddCommGroup E'] [Module R E'] [AddCommGroup F'] [Module R F']
  [Module.Free R E'] [Module.Finite R E']
  [Module.Free R F'] [Module.Finite R F']

/-- Transporting a product orientation is the product of the transported factor orientations. -/
theorem map_prod (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n)
    (f : E ≃ₗ[R] E') (g : F ≃ₗ[R] F') :
    Orientation.map (Fin (m + n)) (f.prodCongr g) (prod o p hm hn) =
      prod (Orientation.map (Fin m) f o) (Orientation.map (Fin n) g p)
        (f.finrank_eq.symm.trans hm) (g.finrank_eq.symm.trans hn) := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  have hb : Orientation.map (Fin m) f b.orientation = (b.map f).orientation :=
    (b.orientation_map f).symm
  have hc : Orientation.map (Fin n) g c.orientation = (c.map g).orientation :=
    (c.orientation_map g).symm
  have he : (((b.prod c).reindex finSumFinEquiv).map (f.prodCongr g)) =
      (((b.map f).prod (c.map g)).reindex finSumFinEquiv) := by
    apply DFunLike.ext
    intro i
    rw [Basis.map_apply, Basis.reindex_apply, Basis.reindex_apply]
    rcases finSumFinEquiv.symm i with j | j <;> simp [Basis.prod_apply]
  have hbase : Orientation.map (Fin (m + n)) (f.prodCongr g)
      (prod b.orientation c.orientation hm hn) =
      prod (Orientation.map (Fin m) f b.orientation) (Orientation.map (Fin n) g c.orientation)
        (f.finrank_eq.symm.trans hm) (g.finrank_eq.symm.trans hn) := by
    rw [prod_basis_orientation, hb, hc, prod_basis_orientation, ← Basis.orientation_map, he]
  rcases b.orientation_eq_or_eq_neg o with ho | ho
  · rcases c.orientation_eq_or_eq_neg p with hp | hp
    · subst o
      subst p
      exact hbase
    · subst o
      subst p
      simpa only [prod_neg_right, Orientation.map_neg] using congrArg Neg.neg hbase
  · rcases c.orientation_eq_or_eq_neg p with hp | hp
    · subst o
      subst p
      simpa only [prod_neg_left, Orientation.map_neg] using congrArg Neg.neg hbase
    · subst o
      subst p
      simpa only [prod_neg_left, prod_neg_right, Orientation.map_neg] using
        congrArg (fun x ↦ - -x) hbase

end Orientation
