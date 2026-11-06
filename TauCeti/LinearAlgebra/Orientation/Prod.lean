/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basis
public import TauCeti.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.LinearAlgebra.Ray

/-!
# Products of linear orientations

The canonical product orientation places the first factor before the second. Its construction
uses relative basis signs and actual product-basis determinants, including empty factor bases.

Exchanging factors of dimensions `m` and `n` multiplies a product orientation by `(-1) ^ (m * n)`
(`Orientation.map_prodComm_prod`): the exchange moves each of the `m` basis vectors of the first
factor past each of the `n` basis vectors of the second.

Reassociating `(E × F) × G` as `E × (F × G)` carries the product orientation `(o × o') × o''` to
`o × (o' × o'')` (`Orientation.map_prodAssoc_prod`): both list the bases of the three factors in
the same order.
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

omit [Module.Free R E] [Module.Finite R E] in
/-- The product of the standard orientations of two copies of `R`, those of
`Basis.singleton (Fin 1) R`, is the orientation of the standard basis `((1, 0), (0, 1))` of
`R × R`. -/
theorem prod_singleton_orientation :
    prod (Basis.singleton (Fin 1) R).orientation (Basis.singleton (Fin 1) R).orientation
        (finrank_self R) (finrank_self R) = (Basis.finTwoProd R).orientation := by
  rw [prod_basis_orientation]
  congr 1
  -- The ordered product of the two standard bases of `R` is the standard basis of `R × R`.
  refine Basis.eq_of_apply_eq (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · have h0 : finSumFinEquiv.symm (0 : Fin (1 + 1)) = Sum.inl 0 :=
      finSumFinEquiv_symm_apply_castAdd 0
    rw [Basis.finTwoProd_zero]
    simp [Basis.prod_apply, h0]
  · have h1 : finSumFinEquiv.symm (1 : Fin (1 + 1)) = Sum.inr 0 :=
      finSumFinEquiv_symm_apply_natAdd 0
    rw [Basis.finTwoProd_one]
    simp [Basis.prod_apply, h1]

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

/-- Exchanging the factors multiplies a product orientation by `(-1) ^ (m * n)`, where `m` and `n`
are the dimensions of the factors. The index types are identified through `n + m = m + n`. -/
theorem map_prodComm_prod (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    Orientation.map (Fin (m + n)) (LinearEquiv.prodComm R E F) (prod o p hm hn) =
      (-1 : Rˣ) ^ (m * n) •
        Orientation.reindex R (F × E) (finCongr (add_comm n m)) (prod p o hn hm) := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  -- The exchange carries the product basis of `b` and `c` to that of `c` and `b`, read through
  -- the permutation of `Fin (m + n)` exchanging the first `m` and the last `n` indices.
  have he : ((b.prod c).reindex finSumFinEquiv).map (LinearEquiv.prodComm R E F) =
      (((c.prod b).reindex finSumFinEquiv).reindex (finCongr (add_comm n m))).reindex
        (finAddFlip.trans (finCongr (add_comm n m)) : Equiv.Perm (Fin (m + n))).symm := by
    refine Basis.eq_of_apply_eq fun k ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [Basis.prod_apply]
  have hbase : Orientation.map (Fin (m + n)) (LinearEquiv.prodComm R E F)
      (prod b.orientation c.orientation hm hn) =
      (-1 : Rˣ) ^ (m * n) • Orientation.reindex R (F × E) (finCongr (add_comm n m))
        (prod c.orientation b.orientation hn hm) := by
    -- The sign of the block swap, in the form `simp` produces from the reindexing in `he`.
    have hsign : Equiv.Perm.sign
        ((finCongr (add_comm m n)).trans (finAddFlip : Fin (m + n) ≃ Fin (n + m)).symm) =
        (-1) ^ (m * n) := by
      rw [← Equiv.Perm.sign_symm]
      simpa using TauCeti.sign_finAddFlip_trans_finCongr m n
    -- Convert both products to basis orientations, then read off the sign of the block swap.
    rw [prod_basis_orientation, prod_basis_orientation, ← Basis.orientation_map, he]
    simp [Basis.orientation_reindex, reindex_perm, hsign]
  rcases b.orientation_eq_or_eq_neg o with ho | ho <;>
    rcases c.orientation_eq_or_eq_neg p with hp | hp <;> subst o <;> subst p <;>
    simp only [prod_neg_left, prod_neg_right, Orientation.map_neg, Orientation.reindex_neg,
      Module.Ray.units_smul_neg, hbase]

/-- If the product `m * n` of the dimensions of the factors is even, exchanging the factors
carries the product orientation of `o` and `p` to that of `p` and `o`. -/
theorem map_prodComm_prod_of_even (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) (h : Even (m * n)) :
    Orientation.map (Fin (m + n)) (LinearEquiv.prodComm R E F) (prod o p hm hn) =
      Orientation.reindex R (F × E) (finCongr (add_comm n m)) (prod p o hn hm) := by
  rw [map_prodComm_prod, h.neg_one_pow, one_smul]

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

variable {G : Type*} [AddCommGroup G] [Module R G] [Module.Free R G] [Module.Finite R G] {p : ℕ}

/-- **Associativity of product orientations.** Reassociating `(E × F) × G` as `E × (F × G)`
carries the product orientation `(o × o') × o''` to `o × (o' × o'')`. The index types are
identified through `m + n + p = m + (n + p)`. -/
theorem map_prodAssoc_prod (o : Orientation R E (Fin m)) (o' : Orientation R F (Fin n))
    (o'' : Orientation R G (Fin p)) (hm : Module.finrank R E = m)
    (hn : Module.finrank R F = n) (hp : Module.finrank R G = p) :
    Orientation.map (Fin (m + n + p)) (LinearEquiv.prodAssoc R E F G)
        (prod (prod o o' hm hn) o'' (by rw [Module.finrank_prod, hm, hn]) hp) =
      Orientation.reindex R (E × F × G) (finCongr (add_assoc m n p).symm)
        (prod o (prod o' o'' hn hp) hm (by rw [Module.finrank_prod, hn, hp])) := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  let d := Module.finBasisOfFinrankEq R G hp
  have hbase : Orientation.map (Fin (m + n + p)) (LinearEquiv.prodAssoc R E F G)
      (prod (prod b.orientation c.orientation hm hn) d.orientation
        (by rw [Module.finrank_prod, hm, hn]) hp) =
      Orientation.reindex R (E × F × G) (finCongr (add_assoc m n p).symm)
        (prod b.orientation (prod c.orientation d.orientation hn hp) hm
          (by rw [Module.finrank_prod, hn, hp])) := by
    rw [prod_basis_orientation, prod_basis_orientation, prod_basis_orientation,
      prod_basis_orientation, ← Basis.orientation_map, Basis.map_prodAssoc_prod,
      Basis.orientation_reindex]
  rcases b.orientation_eq_or_eq_neg o with ho | ho <;>
    rcases c.orientation_eq_or_eq_neg o' with ho' | ho' <;>
    rcases d.orientation_eq_or_eq_neg o'' with ho'' | ho'' <;> subst o <;> subst o' <;>
    subst o'' <;>
    simp only [prod_neg_left, prod_neg_right, Orientation.map_neg, Orientation.reindex_neg, hbase]

end Orientation
