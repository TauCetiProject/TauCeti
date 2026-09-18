/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.RootDatum

/-!
# The simple roots of the special linear group

The roots `ε_i - ε_(i+1)` form the Bourbaki-numbered base of the diagonal root datum of
`SL_{r+1}`. Its Cartan matrix is `CartanMatrix.A r`, and its positive roots are precisely
`ε_a - ε_b` with `a < b`. This fixes the choice of positive roots corresponding to upper
triangular matrices, for use in the standard Borel and Weyl-group descriptions.

The base is transported from `DynkinType.typeASimplyConnectedBase` using Mathlib's
`RootPairing.Base.map`; no new linear-independence or spanning argument is needed.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
-/

public section

namespace TauCeti.SpecialLinear

open DynkinType

universe u

/-- The root index of the `i`-th simple root `ε_i - ε_(i+1)` of `SL_{r+1}`. -/
def diagonalSimpleRootIndex (r : ℕ) (i : Fin r) :
    SplitTorus.CoordinateRootIndex (Fin (r + 1)) :=
  ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ.ne⟩

@[simp] theorem diagonalSimpleRootIndex_fst (r : ℕ) (i : Fin r) :
    (diagonalSimpleRootIndex r i).1.1 = i.castSucc := (rfl)

@[simp] theorem diagonalSimpleRootIndex_snd (r : ℕ) (i : Fin r) :
    (diagonalSimpleRootIndex r i).1.2 = i.succ := (rfl)

/-- The consecutive-root indexing is injective. -/
theorem diagonalSimpleRootIndex_injective (r : ℕ) :
    Function.Injective (diagonalSimpleRootIndex r) := by
  intro i j h
  exact Fin.castSucc_injective r (congrArg (fun p => p.1.1) h)

/-- The Bourbaki base of the diagonal root datum of `SL_{r+1}`. -/
noncomputable def diagonalRootBase (r : ℕ) : (diagonalRootDatum.{u} r).Base :=
  (typeASimplyConnectedBase r).map (diagonalRootDatumEquiv r)

/-- The base consists exactly of the consecutive coordinate differences. -/
@[simp] theorem mem_diagonalRootBase_support (r : ℕ)
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    p ∈ (diagonalRootBase.{u} r).support ↔ ∃ i : Fin r, diagonalSimpleRootIndex r i = p := by
  classical
  simp only [diagonalRootBase, RootPairing.Base.support_map_eq, Finset.mem_image,
    mem_typeASimplyConnectedBase_support, diagonalRootDatumEquiv_indexEquiv]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    have he : k = typeASimpleIndex r ⟨k, hk⟩ := Fin.ext (by simp)
    calc
      _ = (typeAIndexEquiv r).symm (typeASimpleIndex r ⟨k, hk⟩) := by
        rw [typeAIndexEquiv_symm_typeASimpleIndex]
        rfl
      _ = (typeAIndexEquiv r).symm k := congrArg _ he.symm
  · rintro ⟨i, rfl⟩
    exact ⟨typeASimpleIndex r i, by simp, by
      rw [typeAIndexEquiv_symm_typeASimpleIndex]; rfl⟩

/-- The support is the image of the Bourbaki simple-root indexing. -/
theorem diagonalRootBase_support (r : ℕ) :
    (diagonalRootBase.{u} r).support = simpleSupport (diagonalSimpleRootIndex_injective r) := by
  ext p
  rw [mem_diagonalRootBase_support, mem_simpleSupport]

/-- The simple-root pairings are the entries of the type-`A_r` Cartan matrix. -/
theorem diagonalRootDatum_pairing_diagonalSimpleRootIndex (r : ℕ) (i j : Fin r) :
    (diagonalRootDatum.{u} r).pairing (diagonalSimpleRootIndex r i)
      (diagonalSimpleRootIndex r j) = CartanMatrix.A r i j := by
  simp only [diagonalRootDatum_pairing_apply, diagonalSimpleRootIndex_fst,
    diagonalSimpleRootIndex_snd, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- The diagonal root datum of `SL_{r+1}` with its consecutive-root base has Cartan type `A_r`. -/
theorem hasCartanType_diagonalRootDatum (r : ℕ) :
    HasCartanType (diagonalRootDatum.{u} r) (diagonalRootBase r) (.A r) :=
  hasCartanType_of_pairing_eq (diagonalSimpleRootIndex_injective r)
    (diagonalRootBase_support r) fun i j => by
      simpa using diagonalRootDatum_pairing_diagonalSimpleRootIndex.{u} r i j

private theorem diagonalRootBase_coroot_nonneg {r : ℕ}
    {p : SplitTorus.CoordinateRootIndex (Fin (r + 1))}
    (hp : (diagonalRootBase.{u} r).IsPos p) (i : ULift.{u} (Fin r)) :
    0 ≤ (diagonalRootDatum.{u} r).coroot p i := by
  obtain ⟨f, _, hf⟩ := exists_coroot_eq_sum_nat_of_mem_posRoots
    (diagonalRootDatum.{u} r) (diagonalRootBase r) ((mem_posRoots _ _ _).mpr hp)
  rw [hf, Finset.sum_apply]
  apply Finset.sum_nonneg
  intro j hj
  obtain ⟨k, rfl⟩ := (mem_diagonalRootBase_support r j).mp hj
  simp only [diagonalSimpleRootIndex, diagonalRootDatum_coroot_castSucc_succ,
    Pi.smul_apply, nsmul_eq_mul, Pi.single_apply]
  split_ifs <;> positivity

private theorem lt_of_diagonalRootBase_isPos {r : ℕ}
    {p : SplitTorus.CoordinateRootIndex (Fin (r + 1))}
    (hp : (diagonalRootBase.{u} r).IsPos p) : p.1.1 < p.1.2 := by
  by_contra hlt
  have hrev : p.1.2 < p.1.1 := lt_of_le_of_ne (not_lt.mp hlt) p.2.symm
  let i : Fin r := ⟨p.1.2, by have := p.1.1.isLt; simp only [Fin.lt_def] at hrev; omega⟩
  have h := diagonalRootBase_coroot_nonneg hp (ULift.up i)
  simp only [diagonalRootDatum_coroot_apply, Fin.le_def, Fin.val_castSucc,
    i, le_refl, ite_true] at h
  simp only [Fin.lt_def] at hrev
  split_ifs at h <;> omega

/-- A root of the diagonal torus of `SL_{r+1}` is positive exactly when its row index is
smaller than its column index. -/
@[simp] theorem diagonalRootBase_isPos_iff (r : ℕ)
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootBase.{u} r).IsPos p ↔ p.1.1 < p.1.2 := by
  refine ⟨lt_of_diagonalRootBase_isPos, fun hp => ?_⟩
  by_contra hpos
  have hneg : (diagonalRootBase.{u} r).IsPos ((diagonalRootDatum r).reflectionPerm p p) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots _ _ p).mpr ((mem_negRoots _ _ _).mpr hpos)
  have hrev := lt_of_diagonalRootBase_isPos hneg
  rw [diagonalRootDatum_reflectionPerm] at hrev
  simp only [SplitTorus.coordinatePermRootIndex_coe, Equiv.swap_apply_left,
    Equiv.swap_apply_right] at hrev
  exact (not_lt_of_gt hp) hrev

end TauCeti.SpecialLinear
