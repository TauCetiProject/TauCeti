/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic

/-!
# Constants form integral bases in a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of a field `F` with exact
constant field `k`, and let `P` be a place of `F / k`.  A basis of constants — the `F`-basis of
`F'` given by a `k`-basis of `k'` — is an integral basis at `P`: its `𝒪_P`-span is the integral
closure of `𝒪_P` in `F'`.  Both the basis and its trace dual consist of constants, which are
integral over `𝒪_P`, and a basis whose trace dual is integral is an integral basis.

So the elements of `F'` integral over `𝒪_P` are exactly the `𝒪_P`-combinations of constants: the
local model of a constant field extension at `P` is `𝒪_P ⊗[k] k'`.  This is the local input to
the comparison of the Riemann–Roch spaces of `F / k` and `F' / k'`.

## Main result

* `TauCeti.Place.isIntegralBasis_constantBasis`: a basis of constants is an integral basis at
  every place of `F / k`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6, the proof of
Theorem 3.6.3.
-/

public section

open Module

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **A basis of constants is an integral basis at every place** (Stichtenoth, proof of
Theorem 3.6.3): for a finite separable extension of constants `k' / k` with `k` exact in `F` and
`F' = F · k'`, the `𝒪_P`-span of the image of a `k`-basis of `k'` is the integral closure of `𝒪_P`
in `F'`, for every place `P` of `F / k`. -/
theorem isIntegralBasis_constantBasis [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) {ι : Type*} [Finite ι] (b : Basis ι k k')
    (P : Place k F) : P.IsIntegralBasis F' (constantBasis hex h b) := by
  classical
  have := Module.Finite.of_basis b
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  have := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') h
  refine IsIntegralBasis.of_isIntegral_of_isIntegral_traceDual F' P _ (fun i ↦ ?_) fun i ↦ ?_
  · rw [constantBasis_apply]
    exact isIntegral_integers_algebraMap P _
  · rw [traceDual_constantBasis, constantBasis_apply]
    exact isIntegral_integers_algebraMap P _

end Place

end TauCeti
