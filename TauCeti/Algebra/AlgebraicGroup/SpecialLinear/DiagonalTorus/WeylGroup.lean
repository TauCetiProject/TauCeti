/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.RootDatum
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA

/-!
# The Weyl group of the diagonal torus of the special linear group

The Weyl group of the diagonal root datum of `SL_{r+1}` is the symmetric group on the
`r + 1` coordinate lines. Reflections act on ordered root indices by transpositions, and
faithfulness follows because the coroots span the cocharacter lattice. This realizes the
identification integrally, including rank zero.

Over a commutative ring with cancellation by nonzero elements whose determinant-one diagonal
torus separates coordinates, composing with the matrix normalizer computation identifies the
normalizer quotient with this Weyl group. The root-index and character-lattice formulas specify
the identification; in particular a normalizer class with a transposition as its coordinate
permutation gives the corresponding reflection. The separation assumption concerns the group of
rational points and is essential over small finite fields. No scheme-theoretic normalizer
assertion is made here. In rank zero, both groups are trivial over any commutative ring,
without cancellation or separation assumptions.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 21.2 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 26.3.

The normalizer comparison follows the general-linear comparison in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.WeylGroup`. The root-datum computation uses
`TauCeti.DynkinType.typeAWeylGroupEquiv`, transported along
`TauCeti.SpecialLinear.diagonalRootDatumEquiv`.
-/

public section

namespace TauCeti.SpecialLinear

open SplitTorus

universe u v

noncomputable section

variable {r : ℕ}

/-- The Weyl group of the diagonal root datum of `SL_{r+1}` is the permutation group of the
coordinate lines. A permutation acts simultaneously on both entries of a root index. -/
def diagonalPermMulEquivWeylGroup (r : ℕ) :
    Equiv.Perm (Fin (r + 1)) ≃* (diagonalRootDatum.{u} r).weylGroup :=
  (DynkinType.typeAWeylGroupEquiv r).symm.trans (diagonalRootDatumEquiv r).weylGroupEquiv

/-- The Weyl element attached to a coordinate permutation acts componentwise on root indices. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_indexEquiv_apply
    (e : Equiv.Perm (Fin (r + 1))) (p : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalPermMulEquivWeylGroup.{u} r e).1.indexEquiv p =
      coordinatePermRootIndex e p := by
  have h := congrArg (fun f : Equiv.Perm (CoordinateRootIndex (Fin (r + 1))) ↦ f p)
    ((diagonalRootDatumEquiv.{u} r).weylGroupToPerm_weylGroupEquiv
      ((DynkinType.typeAWeylGroupEquiv r).symm e))
  rw [← DynkinType.typeARootPermHom_typeAWeylGroupEquiv, MulEquiv.apply_symm_apply] at h
  simp only [RootPairing.weylGroupToPerm, MonoidHom.domRestrict_apply,
    RootPairing.Equiv.indexHom_apply] at h
  rw [diagonalPermMulEquivWeylGroup, MulEquiv.trans_apply, h]
  apply Subtype.ext
  simpa only [diagonalRootDatumEquiv_indexEquiv, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Equiv.symm_symm, coordinatePermRootIndex_coe] using
    DynkinType.typeAIndexEquiv_symm_typeARootPermHom_apply r e p

/-- A transposition of coordinate lines is the reflection in their difference root. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_swap (i j : Fin (r + 1)) (hij : i ≠ j) :
    diagonalPermMulEquivWeylGroup.{u} r (Equiv.swap i j) =
      RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} r) ⟨(i, j), hij⟩ := by
  rw [diagonalPermMulEquivWeylGroup, MulEquiv.trans_apply,
    ← DynkinType.typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv r ⟨(i, j), hij⟩,
    MulEquiv.symm_apply_apply, RootPairing.Equiv.weylGroupEquiv_ofIdx,
    diagonalRootDatumEquiv_indexEquiv, Equiv.symm_apply_apply]

/-- A root reflection corresponds to the transposition of its two coordinate indices. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_symm_ofIdx
    (p : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalPermMulEquivWeylGroup.{u} r).symm
        (RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} r) p) =
      Equiv.swap p.1.1 p.1.2 := by
  apply (diagonalPermMulEquivWeylGroup r).injective
  rw [MulEquiv.apply_symm_apply, diagonalPermMulEquivWeylGroup_swap _ _ p.2]

/-- In fundamental-weight coordinates, the action of a permutation on a character is computed
by pairing with the inverse images of the simple coroots. -/
@[simp↓]
theorem diagonalPermMulEquivWeylGroup_smul_apply
    (e : Equiv.Perm (Fin (r + 1))) (x : ULift.{u} (Fin r) →₀ ℤ)
    (i : ULift.{u} (Fin r)) :
    (diagonalPermMulEquivWeylGroup.{u} r e • x) i =
      x.sum (fun j c => c *
        ((if e.symm i.down.castSucc ≤ j.down.castSucc then 1 else 0) -
          (if e.symm i.down.succ ≤ j.down.castSucc then 1 else 0))) := by
  let p : CoordinateRootIndex (Fin (r + 1)) :=
    ⟨(i.down.castSucc, i.down.succ), Fin.castSucc_lt_succ.ne⟩
  have he : (diagonalPermMulEquivWeylGroup.{u} r e).1.indexEquiv =
      coordinatePermRootIndex e :=
    Equiv.ext (diagonalPermMulEquivWeylGroup_indexEquiv_apply e)
  have h := RootPairing.coroot'_smul (diagonalRootDatum.{u} r)
    (diagonalPermMulEquivWeylGroup r e).1 p x
  rw [he, coordinatePermRootIndex_symm] at h
  simp only [RootPairing.coroot', LinearMap.flip_apply, diagonalRootDatum_toLinearMap,
    p, diagonalRootDatum_coroot_castSucc_succ, dotPairing_apply] at h
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
  simpa [diagonalRootDatum_coroot_apply, coordinatePermRootIndex_coe,
    Pi.single_apply, mul_ite, Subgroup.smul_def] using h

/-- In rank zero, the determinant-one diagonal normalizer quotient agrees with the Weyl
group over any commutative ring: both groups are trivial. -/
def diagonalNormalizerQuotientMulEquivWeylGroupOfSubsingleton
    (k : Type v) [CommRing k] [Subsingleton (Fin r.succ)] :
    Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1)) ≃*
      (diagonalRootDatum.{u} r).weylGroup := by
  let _ : Subsingleton (Fin (r + 1)) := ‹Subsingleton (Fin r.succ)›
  let _ : Unique (Subgroup.normalizerQuotient
    (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1))) := uniqueOfSubsingleton 1
  exact (MulEquiv.ofUnique :
    Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1)) ≃*
      Equiv.Perm (Fin (r + 1))).trans (diagonalPermMulEquivWeylGroup r)

/-- Every normalizer class maps to the identity Weyl element in rank zero. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroupOfSubsingleton_apply
    (k : Type v) [CommRing k] [Subsingleton (Fin r.succ)]
    (q : Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1))) :
    diagonalNormalizerQuotientMulEquivWeylGroupOfSubsingleton.{u} k q = 1 := by
  let _ : Subsingleton (Fin (r + 1)) := ‹Subsingleton (Fin r.succ)›
  rw [Subsingleton.elim q 1, map_one]

section IsCancelMulZero

variable {k : Type v} [CommRing k] [IsCancelMulZero k]
  (hsep : Matrix.SpecialLinearGroup.DiagonalTorusSeparatesCoordinates k (r + 1))

/-- The normalizer quotient of the determinant-one diagonal torus is the Weyl group of the
root datum of `SL_{r+1}`, whenever the torus separates coordinate lines. -/
def diagonalNormalizerQuotientMulEquivWeylGroup :
    Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1)) ≃*
      (diagonalRootDatum.{u} r).weylGroup := by
  classical
  by_cases hn : Subsingleton (Fin (r + 1))
  · let _ : Subsingleton (Fin r.succ) := hn
    exact diagonalNormalizerQuotientMulEquivWeylGroupOfSubsingleton k
  · exact (Matrix.SpecialLinearGroup.diagonalNormalizerQuotientMulEquivPerm hsep).trans
      (diagonalPermMulEquivWeylGroup r)

private theorem diagonalNormalizerQuotientMulEquivWeylGroup_eq :
    diagonalNormalizerQuotientMulEquivWeylGroup.{u} hsep =
      (Matrix.SpecialLinearGroup.diagonalNormalizerQuotientMulEquivPerm hsep).trans
        (diagonalPermMulEquivWeylGroup r) := by
  classical
  rw [diagonalNormalizerQuotientMulEquivWeylGroup]
  split
  · rename_i hn
    let _ := hn
    exact MulEquiv.toMonoidHom_injective (Subsingleton.elim _ _)
  · rfl

/-- A normalizer representative maps to the Weyl element of its coordinate permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_mk
    (g : Subgroup.normalizer (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1) :
      Set (Matrix.SpecialLinearGroup (Fin (r + 1)) k))) :
    diagonalNormalizerQuotientMulEquivWeylGroup.{u} hsep
        (g : Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1))) =
      diagonalPermMulEquivWeylGroup r
        (Matrix.SpecialLinearGroup.diagonalNormalizerPerm hsep g) := by
  simp [diagonalNormalizerQuotientMulEquivWeylGroup_eq]

/-- On root indices the normalizer quotient acts by its coordinate permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_indexEquiv_apply
    (q : Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1)))
    (p : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalNormalizerQuotientMulEquivWeylGroup.{u} hsep q).1.indexEquiv p =
      coordinatePermRootIndex
        (Matrix.SpecialLinearGroup.diagonalNormalizerQuotientMulEquivPerm hsep q) p := by
  simp [diagonalNormalizerQuotientMulEquivWeylGroup_eq]

/-- The character-lattice action of a normalizer class in fundamental-weight coordinates. -/
@[simp↓]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_smul_apply
    (q : Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1)))
    (x : ULift.{u} (Fin r) →₀ ℤ) (i : ULift.{u} (Fin r)) :
    (diagonalNormalizerQuotientMulEquivWeylGroup.{u} hsep q • x) i =
      let e := Matrix.SpecialLinearGroup.diagonalNormalizerQuotientMulEquivPerm hsep q
      x.sum (fun j c => c *
        ((if e.symm i.down.castSucc ≤ j.down.castSucc then 1 else 0) -
          (if e.symm i.down.succ ≤ j.down.castSucc then 1 else 0))) := by
  simp [diagonalNormalizerQuotientMulEquivWeylGroup_eq]

/-- A normalizer class is the reflection in a root exactly when its coordinate permutation is
the transposition of that root's two indices. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_eq_ofIdx_iff
    (q : Subgroup.normalizerQuotient (Matrix.SpecialLinearGroup.diagonalTorus k (r + 1)))
    (p : CoordinateRootIndex (Fin (r + 1))) :
    diagonalNormalizerQuotientMulEquivWeylGroup.{u} hsep q =
        RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} r) p ↔
      Matrix.SpecialLinearGroup.diagonalNormalizerQuotientMulEquivPerm hsep q =
        Equiv.swap p.1.1 p.1.2 := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup_eq,
    ← diagonalPermMulEquivWeylGroup_swap p.1.1 p.1.2 p.2]
  exact (diagonalPermMulEquivWeylGroup r).injective.eq_iff

end IsCancelMulZero

end

end TauCeti.SpecialLinear
