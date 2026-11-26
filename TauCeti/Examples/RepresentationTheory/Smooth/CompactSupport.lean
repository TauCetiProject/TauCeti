/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Smooth.CompactSupport.OpenClosed

/-!
# Examples of the translation representation on `C_c^∞(X, M)`

This file tests the equivariant form of the open-closed sequence:
* a trivial action on the space gives a trivial representation;
* translation by `g` moves the support by `g`;
* translation sends the value at `x` to the value at `g • x`;
* for a `G`-stable open `U`, the translation representations on `C_c^∞(U, M)` and on the
  complement are smooth, extension by zero and restriction intertwine them, and restriction to
  the complement annihilates an extension by zero.
-/

open Function Pointwise TauCeti

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-! ### 1. A trivial action on the space gives a trivial representation -/

example (h : ∀ (g : G) (x : X), g • x = x) (g : G) :
    compactlySupportedRep ℤ G X ℤ g = 1 :=
  compactlySupportedRep_apply_eq_one (h g)

/-! ### 2. Translation by `g` moves the support by `g` -/

example (g : G) (f : LocallyConstant.compactlySupported ℤ X ℤ) :
    support (compactlySupportedRep ℤ G X ℤ g f : LocallyConstant X ℤ) = g • support f.val :=
  support_compactlySupportedRep_apply g f

/-! ### 3. Translation sends the mass at `x` to the mass at `g • x` -/

example (g : G) (f : LocallyConstant.compactlySupported ℤ X ℤ) (x : X) :
    (compactlySupportedRep ℤ G X ℤ g f : LocallyConstant X ℤ) (g • x) = f.val x :=
  compactlySupportedRep_apply_smul g f x

/-! ### 4. A `G`-stable open subset and its complement -/

section Stable

variable [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G X] [T2Space X]
  (U : SubMulAction G X) (hU : IsOpen (U : Set X))

example : (compactlySupportedRep ℤ G U ℤ).IsSmooth := inferInstance

example : (compactlySupportedRep ℤ G (Uᶜ : SubMulAction G X) ℤ).IsSmooth := inferInstance

example (g : G) (f : LocallyConstant.compactlySupported ℤ U ℤ) :
    compactlySupportedExtendByZero U hU (compactlySupportedRep ℤ G U ℤ g f) =
      compactlySupportedRep ℤ G X ℤ g (compactlySupportedExtendByZero U hU f) :=
  Representation.IntertwiningMap.isIntertwining _ _ (compactlySupportedExtendByZero U hU) g f

example (f : LocallyConstant.compactlySupported ℤ U ℤ) :
    compactlySupportedRestrict Uᶜ hU.isClosed_compl (compactlySupportedExtendByZero U hU f) = 0 :=
  (exact_compactlySupportedExtendByZero_restrict U hU).apply_apply_eq_zero f

end Stable
