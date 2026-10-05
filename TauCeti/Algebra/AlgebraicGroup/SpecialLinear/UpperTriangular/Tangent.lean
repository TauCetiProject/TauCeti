/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Base
public import TauCeti.Algebra.Lie.GeneralLinear.Borel

/-!
# The Lie algebra of the upper-triangular subgroup of `SLₙ`

The differential of the upper-triangular subgroup inclusion identifies its tangent Lie algebra
with the upper-triangular trace-zero matrices. This holds over every commutative base ring and
every coefficient algebra, including in characteristics dividing `n`.

Over a nontrivial coefficient ring, the normalized matrix unit at a root of the diagonal root
datum of `SL_{r+1}` lies in this Lie algebra exactly when the root is positive for the
consecutive-root base. Thus the chosen upper-triangular Borel selects the existing positive
system, and contains the matrix units at its simple roots. This containment supplies the
Lie-algebra condition on the normalized simple-root vectors in a standard pinning.

The matrix Lie algebra reuses `TauCeti.upperTriangular`; the tangent equivalence restricts
`SpecialLinear.tangentLieEquivSl` along `HopfIdeal.quotientLieEquiv`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21, Example 21.2.
* B. Conrad, *Reductive Group Schemes*, §5.1.
-/

public section

namespace TauCeti.SpecialLinear.UpperTriangular

universe u w

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) (B : Type w) [CommRing B]

/-- The upper-triangular trace-zero matrices, as a Lie subalgebra of `slₙ`. -/
def matrixLieSubalgebra : LieSubalgebra B (LieAlgebra.SpecialLinear.sl (Fin n) B) :=
  (TauCeti.upperTriangular B (Fin n)).comap (LieAlgebra.SpecialLinear.sl (Fin n) B).incl

/-- Membership in the matrix Lie algebra of the upper-triangular subgroup is vanishing below
the diagonal. Trace zero is already part of the ambient special linear Lie algebra. -/
@[simp]
theorem mem_matrixLieSubalgebra_iff (X : LieAlgebra.SpecialLinear.sl (Fin n) B) :
    X ∈ matrixLieSubalgebra n B ↔ ∀ i j, j < i → (X : Matrix (Fin n) (Fin n) B) i j = 0 := by
  rw [matrixLieSubalgebra, LieSubalgebra.mem_comap]
  exact TauCeti.mem_upperTriangular_iff

variable {B} {R : Type u} [CommRing R] [Algebra R B]

/-- A tangent vector to `SLₙ` belongs to the Lie algebra of the upper-triangular closed subgroup
exactly when its tangent matrix vanishes below the diagonal.

Use this for explicit rewriting: `HopfIdeal.mem_lieSubalgebra_iff` already determines the
`simp` normal form of membership. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff
    (d : Derivation R (SpecialLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (SpecialLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) ↔
      ∀ i j, j < i → (SpecialLinear.tangentMatrix n d : Matrix (Fin n) (Fin n) B) i j = 0 := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
    (definingHopfIdeal_toIdeal R n)]
  constructor
  · intro hd i j hij
    rw [SpecialLinear.tangentMatrix_apply]
    rw [hd _ ⟨_, (GeneralLinear.UpperTriangular.mem_definingRelationSet_iff R n _).mpr
      ⟨i, j, hij, rfl⟩, rfl⟩, map_zero]
  · intro hd x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨i, j, hij, rfl⟩ :=
      (GeneralLinear.UpperTriangular.mem_definingRelationSet_iff R n y).mp hy
    exact (Bialgebra.CounitAlgebra.algEquivSelf R
      (SpecialLinear.coordinateHopfAlgebra R n) B).injective <| by
        rw [map_zero, ← SpecialLinear.tangentMatrix_apply]
        exact hd i j hij

/-- The special-linear tangent equivalence carries the Lie algebra of the upper-triangular
subgroup onto the upper-triangular trace-zero matrices. -/
theorem map_lieSubalgebra_definingHopfIdeal :
    (HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n)).map
        (SpecialLinear.tangentLieEquivSl (R := R) (B := B) n).toLieHom =
      matrixLieSubalgebra n B := by
  ext X
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simp only [mem_matrixLieSubalgebra_iff, LieEquiv.coe_coe]
    rw [SpecialLinear.tangentLieEquivSl_apply]
    exact (mem_lieSubalgebra_definingHopfIdeal_iff n d).mp hd
  · intro hX
    refine ⟨(SpecialLinear.tangentLieEquivSl (R := R) (B := B) n).symm X, ?_,
      (SpecialLinear.tangentLieEquivSl (R := R) (B := B) n).apply_symm_apply X⟩
    rw [mem_lieSubalgebra_definingHopfIdeal_iff,
      ← SpecialLinear.tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
    exact (mem_matrixLieSubalgebra_iff n B X).mp hX

/-- The tangent Lie algebra of the upper-triangular subgroup of `SLₙ` is the Lie algebra of
upper-triangular trace-zero matrices over the coefficient algebra. -/
noncomputable def tangentLieEquiv :
    Derivation R (coordinateHopfAlgebra R n)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃ₗ⁅B⁆
      matrixLieSubalgebra n B :=
  (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n)).trans
    ((SpecialLinear.tangentLieEquivSl (R := R) (B := B) n).ofSubalgebras _ _
      (map_lieSubalgebra_definingHopfIdeal n))

/-- The tangent equivalence is compatible with the differential of the inclusion into `SLₙ`. -/
@[simp]
theorem tangentLieEquiv_apply_coe
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    (tangentLieEquiv (R := R) (B := B) n d : LieAlgebra.SpecialLinear.sl (Fin n) B) =
      SpecialLinear.tangentMatrix n (HopfIdeal.quotientLieHom (definingHopfIdeal R n) d) := by
  simp only [tangentLieEquiv, LieEquiv.trans_apply, LieEquiv.ofSubalgebras_apply,
    HopfIdeal.quotientLieEquiv_apply_coe]
  exact SpecialLinear.tangentLieEquivSl_apply n _

/-- Descending an upper-triangular trace-zero matrix and then differentiating its inclusion
recovers that matrix. -/
@[simp]
theorem tangentMatrix_quotientLieHom_tangentLieEquiv_symm
    (X : matrixLieSubalgebra n B) :
    SpecialLinear.tangentMatrix n (HopfIdeal.quotientLieHom (definingHopfIdeal R n)
      ((tangentLieEquiv (R := R) (B := B) n).symm X)) = X := by
  rw [← tangentLieEquiv_apply_coe, LieEquiv.apply_symm_apply]

/-- An off-diagonal matrix unit lies in the upper-triangular special linear Lie algebra when
its row precedes its column, for every coefficient, including over the zero ring. -/
theorem single_mem_matrixLieSubalgebra (i j : Fin n) (hij : i < j) (c : B) :
    LieAlgebra.SpecialLinear.single i j hij.ne c ∈ matrixLieSubalgebra n B := by
  rw [matrixLieSubalgebra, LieSubalgebra.mem_comap]
  -- The inclusion of `slₙ` forgets trace zero; use the public matrix-unit computation rule.
  change (LieAlgebra.SpecialLinear.single i j hij.ne c : Matrix (Fin n) (Fin n) B) ∈
    TauCeti.upperTriangular B (Fin n)
  rw [LieAlgebra.SpecialLinear.val_single]
  exact TauCeti.single_mem_upperTriangular hij.le c

/-- A nonzero off-diagonal matrix unit lies in the upper-triangular special linear Lie algebra
exactly when its row precedes its column. -/
theorem single_mem_matrixLieSubalgebra_iff (i j : Fin n) (hij : i ≠ j)
    {c : B} (hc : c ≠ 0) :
    LieAlgebra.SpecialLinear.single i j hij c ∈ matrixLieSubalgebra n B ↔ i < j := by
  constructor
  · intro h
    rw [matrixLieSubalgebra, LieSubalgebra.mem_comap] at h
    -- The inclusion of `slₙ` forgets trace zero; use the public matrix-unit computation rule.
    change (LieAlgebra.SpecialLinear.single i j hij c : Matrix (Fin n) (Fin n) B) ∈
      TauCeti.upperTriangular B (Fin n) at h
    rw [LieAlgebra.SpecialLinear.val_single] at h
    exact lt_of_le_of_ne ((TauCeti.single_mem_upperTriangular_iff hc).mp h) hij
  · intro h
    exact single_mem_matrixLieSubalgebra n i j h c

/-- The normalized simple-root vectors lie in the Lie algebra of the chosen upper-triangular
Borel. This containment holds even over the zero ring. -/
theorem single_castSucc_succ_mem_matrixLieSubalgebra (r : ℕ) (i : Fin r) :
    LieAlgebra.SpecialLinear.single i.castSucc i.succ Fin.castSucc_lt_succ.ne (1 : B) ∈
      matrixLieSubalgebra (r + 1) B := by
  exact single_mem_matrixLieSubalgebra (r + 1) i.castSucc i.succ Fin.castSucc_lt_succ 1

/-- The normalized root tangent vector to `SL_{r+1}` lies in the Lie algebra of its chosen
upper-triangular Borel exactly when the root is positive.

Use this for explicit rewriting: `HopfIdeal.mem_lieSubalgebra_iff` already determines the
`simp` normal form of membership. -/
theorem tangentLieEquivSl_symm_single_mem_lieSubalgebra_iff_isPos [Nontrivial B] (r : ℕ)
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (SpecialLinear.tangentLieEquivSl (R := R) (B := B) (r + 1)).symm
        (LieAlgebra.SpecialLinear.single p.1.1 p.1.2 p.2 (1 : B)) ∈
        HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R (r + 1)) ↔
      (SpecialLinear.diagonalRootBase r).IsPos p := by
  rw [mem_lieSubalgebra_definingHopfIdeal_iff,
    ← SpecialLinear.tangentLieEquivSl_apply, LieEquiv.apply_symm_apply,
    ← mem_matrixLieSubalgebra_iff]
  rw [single_mem_matrixLieSubalgebra_iff _ _ _ _ one_ne_zero,
    SpecialLinear.diagonalRootBase_isPos_iff]

end TauCeti.SpecialLinear.UpperTriangular
