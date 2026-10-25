/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.FieldTheory.Galois.Abelian

/-!
# Norm calculations for the quadratic field `ℚ(√5)`

The concrete quadratic algebra has a generator of square five and degree two over `ℚ`.
Its idele-class norm quotient has order two, and a rational unit is a global norm exactly
when it is a norm at every finite and infinite place. These checks use the actual norm maps.
-/

public section

open NumberField

namespace TauCeti.Examples.QuadraticNorm

local instance instFactNotSquareFiveInt : Fact (¬ IsSquare (5 : ℤ)) :=
  ⟨fun h => Nat.prime_five.not_isSquare (Int.isSquare_natCast_iff.mp h)⟩
local instance instFactNotSquareFiveRat : Fact (¬ IsSquare (5 : ℚ)) :=
  Rat.instFactNotIsSquareIntCast 5

example : Module.finrank ℚ (QuadraticAlgebra ℚ 5 0) = 2 := QuadraticAlgebra.finrank_eq_two 5 0

local instance instIsAbelianGalois : IsAbelianGalois ℚ (QuadraticAlgebra ℚ 5 0) :=
  .of_isCyclic ℚ (QuadraticAlgebra ℚ 5 0)

example : Nat.card (IdeleClassGroup (𝓞 ℚ) ℚ ⧸
    (GlobalNumberFields.ideleClassNormMap ℚ (QuadraticAlgebra ℚ 5 0) :
      IdeleClassGroup (𝓞 (QuadraticAlgebra ℚ 5 0)) (QuadraticAlgebra ℚ 5 0) →*
        IdeleClassGroup (𝓞 ℚ) ℚ).range) = 2 := by
  rw [TauCeti.ClassFieldTheory.card_ideleClassNormQuotient]
  exact QuadraticAlgebra.finrank_eq_two 5 0

example : (QuadraticAlgebra.omega : QuadraticAlgebra ℚ 5 0) ^ 2 = 5 := by
  rw [QuadraticAlgebra.omega_pow_two_eq_add]
  norm_num [Algebra.smul_def]

example : Algebra.adjoin ℚ {(QuadraticAlgebra.omega : QuadraticAlgebra ℚ 5 0)} = ⊤ :=
  QuadraticAlgebra.adjoin_omega_eq_top

example (a : ℚˣ) : a ∈ normGroup ℚ (QuadraticAlgebra ℚ 5 0) ↔
    GlobalNumberFields.IsLocalNormEverywhere ℚ (QuadraticAlgebra ℚ 5 0) a :=
  ClassFieldTheory.isGlobalNorm_iff_isLocalNormEverywhere ℚ (QuadraticAlgebra ℚ 5 0) a

end TauCeti.Examples.QuadraticNorm
