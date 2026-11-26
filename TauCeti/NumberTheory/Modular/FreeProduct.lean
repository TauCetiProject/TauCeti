/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.CoprodI.Basic
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Triangle.Group
import TauCeti.GroupTheory.TriangleGroup.FreeProduct

/-!
# Free-product presentation of `PSL(2, ℤ)`

Combining the geometric presentation `PSL(2, ℤ) ≃* TriangleGroup 3 2 0` with the free-product
splitting of `Δ(a, b, 0)` identifies the projective modular group with the free product
`ℤ/2ℤ ∗ ℤ/3ℤ`, both as a binary coproduct (`TauCeti.ModularGroup.coprodEquiv`) and as an indexed
coproduct over `Fin 2` (`TauCeti.ModularGroup.coprodIEquiv`). Under this isomorphism, the order-two
generator `S` corresponds to the canonical generator of `ℤ/2ℤ`, the order-three generator `R = S T`
corresponds to the canonical generator of `ℤ/3ℤ`, and the cusp translation `T = S R` corresponds to
their product in `ℤ/2ℤ ∗ ℤ/3ℤ`.

## Main definitions

* `TauCeti.ModularGroup.coprodEquiv`: the isomorphism
  `PSL(2, ℤ) ≃* Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3)`.
* `TauCeti.ModularGroup.coprodIEquiv`: the indexed-coproduct isomorphism
  `PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))`.

## References

* J.-P. Serre, *Trees*, Springer Monographs in Mathematics, 1980, Chapter I, §4.2.
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1.
-/

public section

noncomputable section

open scoped MatrixGroups Monoid.Coprod

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-! ### Free-product presentation `PSL(2, ℤ) ≃* ℤ/2ℤ ∗ ℤ/3ℤ` -/

/-- **Free-product decomposition of the modular group.** `PSL(2, ℤ)` is isomorphic to the free
product `Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3)`, sending `S` to `inl (ofAdd 1)`,
`R = S T` to `inr (ofAdd 1)`, and `T = S R` to `inl (ofAdd 1) * inr (ofAdd 1)`. -/
def coprodEquiv : PSL(2, ℤ) ≃* Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3) :=
  (triangleGroupEquiv.symm.trans (TriangleGroup.equivCoprod 3 2)).trans
    (MulEquiv.coprodComm (Multiplicative (ZMod 3)) (Multiplicative (ZMod 2)))

@[simp]
theorem coprodEquiv_coe_S : coprodEquiv (S : PSL(2, ℤ)) = Monoid.Coprod.inl (.ofAdd 1) := by
  simp [coprodEquiv, triangleGroupEquiv_symm_coe_S]

@[simp]
theorem coprodEquiv_coe_R : coprodEquiv (R : PSL(2, ℤ)) = Monoid.Coprod.inr (.ofAdd 1) := by
  simp [coprodEquiv, triangleGroupEquiv_symm_coe_R]

@[simp]
theorem coprodEquiv_coe_T :
    coprodEquiv (T : PSL(2, ℤ)) = Monoid.Coprod.inl (.ofAdd 1) * Monoid.Coprod.inr (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R, map_mul, coprodEquiv_coe_S, coprodEquiv_coe_R]

@[simp]
theorem coprodEquiv_coe_U :
    coprodEquiv (U : PSL(2, ℤ)) =
      Monoid.Coprod.inl (.ofAdd 1) * (Monoid.Coprod.inr (.ofAdd 1))⁻¹ *
        Monoid.Coprod.inl (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R_inv_mul_coe_S_inv, coe_S_inv, map_mul, map_mul, map_inv,
    coprodEquiv_coe_S, coprodEquiv_coe_R]

@[simp]
theorem coprodEquiv_symm_inl_ofAdd_intCast (k : ℤ) :
    coprodEquiv.symm (Monoid.Coprod.inl (.ofAdd (k : ZMod 2))) = (S : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inr_ofAdd_intCast (k : ℤ) :
    coprodEquiv.symm (Monoid.Coprod.inr (.ofAdd (k : ZMod 3))) = (R : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv, coe_R_eq_coe_S_mul_coe_T]

@[simp]
theorem coprodEquiv_symm_inl_ofAdd_natCast (k : ℕ) :
    coprodEquiv.symm (Monoid.Coprod.inl (.ofAdd (k : ZMod 2))) = (S : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inr_ofAdd_natCast (k : ℕ) :
    coprodEquiv.symm (Monoid.Coprod.inr (.ofAdd (k : ZMod 3))) = (R : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv, coe_R_eq_coe_S_mul_coe_T]

@[simp]
theorem coprodEquiv_symm_inl_ofAdd_one :
    coprodEquiv.symm (Monoid.Coprod.inl (.ofAdd 1)) = (S : PSL(2, ℤ)) := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inr_ofAdd_one :
    coprodEquiv.symm (Monoid.Coprod.inr (.ofAdd 1)) = (R : PSL(2, ℤ)) := by
  simp [coprodEquiv, coe_R_eq_coe_S_mul_coe_T]

/-- **Indexed free-product decomposition of the modular group.** `PSL(2, ℤ)` is isomorphic to the
indexed coproduct `Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))` over
`Fin 2`. -/
def coprodIEquiv :
    PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i)) :=
  coprodEquiv.trans
    (Monoid.CoprodI.finTwoEquivCoprod fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))).symm

@[simp]
theorem coprodIEquiv_coe_S :
    coprodIEquiv (S : PSL(2, ℤ)) =
      Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 0)
        ((Multiplicative.ofAdd (α := ZMod 2)) 1) := by
  refine (MulEquiv.trans_apply coprodEquiv
    (Monoid.CoprodI.finTwoEquivCoprod fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))).symm
    (S : PSL(2, ℤ))).trans ?_
  rw [coprodEquiv_coe_S]
  exact Monoid.CoprodI.finTwoEquivCoprod_symm_inl
    (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i)))
    ((Multiplicative.ofAdd (α := ZMod 2)) 1)

@[simp]
theorem coprodIEquiv_coe_R :
    coprodIEquiv (R : PSL(2, ℤ)) =
      Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 1)
        ((Multiplicative.ofAdd (α := ZMod 3)) 1) := by
  refine (MulEquiv.trans_apply coprodEquiv
    (Monoid.CoprodI.finTwoEquivCoprod fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))).symm
    (R : PSL(2, ℤ))).trans ?_
  rw [coprodEquiv_coe_R]
  exact Monoid.CoprodI.finTwoEquivCoprod_symm_inr
    (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i)))
    ((Multiplicative.ofAdd (α := ZMod 3)) 1)

/-- `coprodIEquiv.symm` sends the generator of the `i = 0` factor `ZMod 2` to `S`.

Not `@[simp]`: `Matrix.cons_val_zero` reduces `![2, 3] 0` inside the `DFunLike.coe` domain of
`Monoid.CoprodI.of`. -/
theorem coprodIEquiv_symm_of_zero_ofAdd_one :
    coprodIEquiv.symm
        (Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 0)
          ((Multiplicative.ofAdd (α := ZMod 2)) 1)) = (S : PSL(2, ℤ)) :=
  coprodIEquiv.symm_apply_eq.mpr coprodIEquiv_coe_S.symm

/-- `coprodIEquiv.symm` sends the generator of the `i = 1` factor `ZMod 3` to `R`.

Not `@[simp]`: `Matrix.cons_val_one` reduces `![2, 3] 1` inside the `DFunLike.coe` domain of
`Monoid.CoprodI.of`. -/
theorem coprodIEquiv_symm_of_one_ofAdd_one :
    coprodIEquiv.symm
        (Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 1)
          ((Multiplicative.ofAdd (α := ZMod 3)) 1)) = (R : PSL(2, ℤ)) :=
  coprodIEquiv.symm_apply_eq.mpr coprodIEquiv_coe_R.symm

end TauCeti.ModularGroup
