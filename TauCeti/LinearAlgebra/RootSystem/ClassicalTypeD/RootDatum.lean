/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.RootPairing
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import TauCeti.Algebra.Group.Submonoid.Closure

/-!
# The classical root datum of type `Dₙ` on `ℤⁿ`

The vectors `±e_a ± e_b` (`a ≠ b`) of `ℤⁿ`, the integral vectors of squared length two
(`TauCeti.DynkinType.TypeDRoot`), form a root datum on `ℤⁿ × ℤⁿ` paired by the dot product, each
root being its own coroot. It is the root datum of the split special orthogonal group `SO_{2n}`
relative to its diagonal torus `diag(t₁, …, tₙ, tₙ⁻¹, …, t₁⁻¹)`. It is defined for every `n`: it
has no roots for `n ≤ 1`, it is of type `A₁ × A₁` for `n = 2` and of type `A₃` for `n = 3`.
It is the root pairing of the norm-two shell (`Matrix.PosDef.normTwoShellRootPairing`) of the
identity matrix over `ℤ`, reindexed by `TauCeti.DynkinType.TypeDRoot`.

For `2 ≤ n` the Bourbaki simple roots `e_i - e_{i+1}` and `e_{n-2} + e_{n-1}`
(`TauCeti.DynkinType.typeDSimpleRoot`) form a base, by the expansion of every root in them with
coefficients of one sign (`TauCeti.DynkinType.typeDSimpleRootCoordinates_nonneg_or_nonpos`); for
`n = 2` and `n = 3` it is a base of type `A₁ × A₁` and `A₃`.

## Main declarations

* `TauCeti.DynkinType.typeDClassicalRootDatum`: the root datum.
* `TauCeti.DynkinType.flip_typeDClassicalRootDatum`: it is its own dual.
* `TauCeti.DynkinType.typeDClassicalBase`: the Bourbaki base for `2 ≤ n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §27.
-/

public section

open Function Set Matrix

namespace TauCeti.DynkinType

variable (n : ℕ)

/-- The integral vectors of squared length two are the norm-two shell of the identity matrix. -/
private def normTwoShellOneEquiv : (1 : Matrix (Fin n) (Fin n) ℤ).normTwoShell ≃ TypeDRoot n :=
  Equiv.subtypeEquivRight fun x => by rw [mem_normTwoShell, one_mulVec]

/-- **The classical root datum of type `Dₙ`**: the roots and coroots are the integral vectors
`±e_a ± e_b` of squared length two in `ℤⁿ`, paired by the dot product. It is the root datum of
`SO_{2n}` with its diagonal torus, defined as the root pairing of the norm-two shell of the identity
matrix. -/
noncomputable def typeDClassicalRootDatum : RootDatum (TypeDRoot n) (Fin n → ℤ) (Fin n → ℤ) :=
  (PosDef.one.normTwoShellRootPairing ℤ).map (normTwoShellOneEquiv n) (LinearEquiv.refl ℤ _)
    (LinearEquiv.refl ℤ _)

variable {n}

@[simp]
theorem typeDClassicalRootDatum_root (x : TypeDRoot n) :
    (typeDClassicalRootDatum n).root x = x.val := by
  simp [typeDClassicalRootDatum, RootPairing.map, normTwoShellOneEquiv]

@[simp]
theorem typeDClassicalRootDatum_coroot (x : TypeDRoot n) :
    (typeDClassicalRootDatum n).coroot x = x.val := by
  simp [typeDClassicalRootDatum, RootPairing.map, normTwoShellOneEquiv]

@[simp]
theorem typeDClassicalRootDatum_toLinearMap_apply (x y : Fin n → ℤ) :
    (typeDClassicalRootDatum n).toLinearMap x y = x ⬝ᵥ y := by
  simp [typeDClassicalRootDatum, RootPairing.map]

/-- The Cartan integers of the classical root datum of type `Dₙ` are dot products. -/
@[simp]
theorem typeDClassicalRootDatum_pairing (x y : TypeDRoot n) :
    (typeDClassicalRootDatum n).pairing x y = x.val ⬝ᵥ y.val := by
  rw [← RootPairing.root_coroot_eq_pairing, typeDClassicalRootDatum_toLinearMap_apply,
    typeDClassicalRootDatum_root, typeDClassicalRootDatum_coroot]

/-- **The classical root datum of type `Dₙ` is its own dual.** -/
theorem flip_typeDClassicalRootDatum :
    (typeDClassicalRootDatum n).flip = typeDClassicalRootDatum n := by
  apply RootPairing.ext
  · refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [RootPairing.flip_toLinearMap, LinearMap.flip_apply,
      typeDClassicalRootDatum_toLinearMap_apply, typeDClassicalRootDatum_toLinearMap_apply,
      dotProduct_comm]
  · ext x : 1
    rw [RootPairing.flip_root, typeDClassicalRootDatum_coroot, typeDClassicalRootDatum_root]
  · exact congrArg Set.range (funext fun x => by
      rw [RootPairing.flip_coroot, typeDClassicalRootDatum_root, typeDClassicalRootDatum_coroot])

/-! ### The Bourbaki base -/

section Base

variable (hn : 2 ≤ n)

/-- The roots of the classical root datum of type `Dₙ`, as a function. -/
private theorem coe_typeDClassicalRootDatum_root :
    ⇑(typeDClassicalRootDatum n).root = Subtype.val :=
  funext typeDClassicalRootDatum_root

/-- The coroots of the classical root datum of type `Dₙ`, as a function, are the roots. -/
private theorem coe_typeDClassicalRootDatum_coroot :
    ⇑(typeDClassicalRootDatum n).coroot = Subtype.val :=
  funext typeDClassicalRootDatum_coroot

/-- The `i`-th Bourbaki simple root of type `Dₙ`, as a root. -/
def typeDClassicalSimpleIndex (i : Fin n) : TypeDRoot n :=
  ⟨typeDSimpleRoot n hn i, by simp⟩

@[simp]
theorem typeDClassicalSimpleIndex_val (i : Fin n) :
    (typeDClassicalSimpleIndex hn i).val = typeDSimpleRoot n hn i :=
  (rfl)

theorem typeDClassicalSimpleIndex_injective : Injective (typeDClassicalSimpleIndex hn) :=
  fun _ _ h => (linearIndependent_typeDSimpleRoot hn).injective (congrArg Subtype.val h)

/-- Every root is a combination of the simple roots with coefficients of one sign. -/
private theorem mem_or_neg_mem_closure (x : TypeDRoot n) :
    x.val ∈ AddSubmonoid.closure
        (Subtype.val '' (↑(simpleSupport (typeDClassicalSimpleIndex_injective hn)) :
          Set (TypeDRoot n))) ∨
      -x.val ∈ AddSubmonoid.closure
        (Subtype.val '' (↑(simpleSupport (typeDClassicalSimpleIndex_injective hn)) :
          Set (TypeDRoot n))) := by
  rw [image_simpleSupport, ← sum_smul_typeDSimpleRootCoordinates hn (even_sum_typeDRoot x)]
  exact sum_smul_mem_or_neg_mem_closure _ _ (typeDSimpleRootCoordinates_nonneg_or_nonpos hn x)

/-- **The Bourbaki base of the classical root datum of type `Dₙ`**, for `2 ≤ n`: the simple roots
`e_i - e_{i+1}` and `e_{n-2} + e_{n-1}`. -/
noncomputable def typeDClassicalBase : (typeDClassicalRootDatum n).Base where
  support := simpleSupport (typeDClassicalSimpleIndex_injective hn)
  linearIndepOn_root := by
    rw [coe_typeDClassicalRootDatum_root]
    exact linearIndepOn_simpleSupport _ _ (linearIndependent_typeDSimpleRoot hn)
  linearIndepOn_coroot := by
    rw [coe_typeDClassicalRootDatum_coroot]
    exact linearIndepOn_simpleSupport _ _ (linearIndependent_typeDSimpleRoot hn)
  root_mem_or_neg_mem x := by
    rw [coe_typeDClassicalRootDatum_root]
    exact mem_or_neg_mem_closure hn x
  coroot_mem_or_neg_mem x := by
    rw [coe_typeDClassicalRootDatum_coroot]
    exact mem_or_neg_mem_closure hn x

/-- The support of the Bourbaki base consists of the simple roots. -/
theorem mem_typeDClassicalBase_support {x : TypeDRoot n} :
    x ∈ (typeDClassicalBase hn).support ↔ ∃ i, typeDClassicalSimpleIndex hn i = x :=
  mem_simpleSupport _

/-- The Bourbaki base of type `Dₙ` has `n` simple roots. -/
@[simp]
theorem card_typeDClassicalBase_support : (typeDClassicalBase hn).support.card = n := by
  simp [typeDClassicalBase]

end Base

/-! ### Checks -/

/-- In type `D₂ = A₁ × A₁` the two simple roots `e₀ - e₁` and `e₀ + e₁` are orthogonal. -/
example : typeDSimpleRoot 2 le_rfl 0 ⬝ᵥ typeDSimpleRoot 2 le_rfl 1 = 0 := by
  simp [dotProduct, Fin.sum_univ_two, Pi.single_apply]

/-- In type `D₃ = A₃` the simple roots `e₁ - e₂` and `e₁ + e₂` are orthogonal and both pair to
`-1` with `e₀ - e₁`: the Dynkin diagram is the chain `A₃` with `e₀ - e₁` in the middle. -/
example :
    typeDSimpleRoot 3 (by norm_num) 1 ⬝ᵥ typeDSimpleRoot 3 (by norm_num) 2 = 0 ∧
      typeDSimpleRoot 3 (by norm_num) 0 ⬝ᵥ typeDSimpleRoot 3 (by norm_num) 1 = -1 ∧
      typeDSimpleRoot 3 (by norm_num) 0 ⬝ᵥ typeDSimpleRoot 3 (by norm_num) 2 = -1 := by
  simp [dotProduct, Fin.sum_univ_three, Pi.single_apply]

end TauCeti.DynkinType
