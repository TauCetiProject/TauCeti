/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import TauCeti.Algebra.Group.Submonoid.Closure

/-!
# The classical root datum of type `Dₙ` on `ℤⁿ`

The vectors `±e_a ± e_b` (`a ≠ b`) of `ℤⁿ`, the integral vectors of squared length two
(`TauCeti.DynkinType.TypeDRoot`), form a root datum on `ℤⁿ × ℤⁿ` paired by the dot product, each
root being its own coroot. It is the root datum of the split special orthogonal group `SO_{2n}`
relative to its diagonal torus `diag(t₁, …, tₙ, tₙ⁻¹, …, t₁⁻¹)`. It is defined for every `n`: it
has no roots for `n ≤ 1`, it is of type `A₁ × A₁` for `n = 2` and of type `A₃` for `n = 3`.
Reflections are the classical reflections `TauCeti.DynkinType.typeDRootReflection`.

For `4 ≤ n` the Bourbaki simple roots `e_i - e_{i+1}` and `e_{n-2} + e_{n-1}` form a base, by
the expansion of every root in them with coefficients of one sign
(`TauCeti.DynkinType.typeDSimpleRootCoordinates_nonneg_or_nonpos`).

## Main declarations

* `TauCeti.DynkinType.typeDClassicalRootDatum`: the root datum.
* `TauCeti.DynkinType.flip_typeDClassicalRootDatum`: it is its own dual.
* `TauCeti.DynkinType.typeDClassicalBase`: the Bourbaki base for `4 ≤ n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §27.
-/

public section

open Function Set Matrix

namespace TauCeti.DynkinType

/-- The coordinates of a root of type `Dₙ` lie in `{-1, 0, 1}`. -/
theorem TypeDRoot.abs_le_one {n : ℕ} (x : TypeDRoot n) (i : Fin n) :
    -1 ≤ x.val i ∧ x.val i ≤ 1 := by
  have h := x.property
  have hle : x.val i * x.val i ≤ x.val ⬝ᵥ x.val :=
    Finset.single_le_sum (f := fun k => x.val k * x.val k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [h] at hle
  constructor <;> nlinarith

/-- There are finitely many roots of type `Dₙ`. -/
instance instFiniteTypeDRoot (n : ℕ) : Finite (TypeDRoot n) :=
  Finite.of_injective (fun x : TypeDRoot n => fun i => (⟨x.val i, x.abs_le_one i⟩ : Icc (-1 : ℤ) 1))
    fun _ _ h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))

variable (n : ℕ)

/-- **The classical root datum of type `Dₙ`**: the roots and coroots are the integral vectors
`±e_a ± e_b` of squared length two in `ℤⁿ`, paired by the dot product. It is the root datum of
`SO_{2n}` with its diagonal torus. -/
noncomputable def typeDClassicalRootDatum : RootDatum (TypeDRoot n) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin n)).toLinearMap
  root := Embedding.subtype _
  coroot := Embedding.subtype _
  root_coroot_two i := i.property
  reflectionPerm := typeDRootReflectionEquiv
  reflectionPerm_root i j := by
    change j.val - (j.val ⬝ᵥ i.val) • i.val = (typeDRootReflectionEquiv i j).val
    rw [typeDRootReflectionEquiv_apply, typeDRootReflection_val]
  reflectionPerm_coroot i j := by
    change j.val - (i.val ⬝ᵥ j.val) • i.val = (typeDRootReflectionEquiv i j).val
    rw [typeDRootReflectionEquiv_apply, typeDRootReflection_val, dotProduct_comm]

variable {n}

@[simp]
theorem typeDClassicalRootDatum_root (x : TypeDRoot n) :
    (typeDClassicalRootDatum n).root x = x.val :=
  (rfl)

@[simp]
theorem typeDClassicalRootDatum_coroot (x : TypeDRoot n) :
    (typeDClassicalRootDatum n).coroot x = x.val :=
  (rfl)

@[simp]
theorem typeDClassicalRootDatum_toLinearMap_apply (x y : Fin n → ℤ) :
    (typeDClassicalRootDatum n).toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

/-- The Cartan integers of the classical root datum of type `Dₙ` are dot products. -/
@[simp]
theorem typeDClassicalRootDatum_pairing (x y : TypeDRoot n) :
    (typeDClassicalRootDatum n).pairing x y = x.val ⬝ᵥ y.val :=
  (rfl)

/-- **The classical root datum of type `Dₙ` is its own dual.** -/
theorem flip_typeDClassicalRootDatum :
    (typeDClassicalRootDatum n).flip = typeDClassicalRootDatum n := by
  apply RootPairing.ext
  · refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [RootPairing.flip_toLinearMap, LinearMap.flip_apply,
      typeDClassicalRootDatum_toLinearMap_apply, typeDClassicalRootDatum_toLinearMap_apply,
      dotProduct_comm]
  · rfl
  · rfl

/-- There are no roots of type `D₁`: no integral vector of length one has squared length two. -/
instance instIsEmptyTypeDRootOne : IsEmpty (TypeDRoot 1) := by
  refine ⟨fun x => ?_⟩
  have h := x.property
  simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton] at h
  obtain ⟨h₁, h₂⟩ := x.abs_le_one default
  nlinarith

/-! ### The Bourbaki base -/

section Base

variable (hn : 4 ≤ n)

/-- The `i`-th Bourbaki simple root of type `Dₙ`, as a root. -/
def typeDClassicalSimpleIndex (i : Fin n) : TypeDRoot n :=
  ⟨typeDSimpleRoot n hn i, by
    rw [typeDSimpleRoot_dotProduct_typeDSimpleRoot]
    simp [CartanMatrix.D]⟩

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

/-- **The Bourbaki base of the classical root datum of type `Dₙ`**, for `4 ≤ n`: the simple roots
`e_i - e_{i+1}` and `e_{n-2} + e_{n-1}`. -/
noncomputable def typeDClassicalBase : (typeDClassicalRootDatum n).Base where
  support := simpleSupport (typeDClassicalSimpleIndex_injective hn)
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ (linearIndependent_typeDSimpleRoot hn)
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ (linearIndependent_typeDSimpleRoot hn)
  root_mem_or_neg_mem x := mem_or_neg_mem_closure hn x
  coroot_mem_or_neg_mem x := mem_or_neg_mem_closure hn x

/-- The support of the Bourbaki base consists of the simple roots. -/
theorem mem_typeDClassicalBase_support {x : TypeDRoot n} :
    x ∈ (typeDClassicalBase hn).support ↔ ∃ i, typeDClassicalSimpleIndex hn i = x :=
  mem_simpleSupport _

end Base

end TauCeti.DynkinType
