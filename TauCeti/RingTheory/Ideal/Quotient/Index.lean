/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Data.SetLike.Fintype
import TauCeti.Algebra.Module.Submodule.Quotient

/-!
# Submodules between a module and an ideal multiple

For a finitely generated submodule `N` and an ideal `I` of finite index, the intermediate
submodules between `I • N` and `N` are the images of the submodules of the finite module `N / IN`.
In particular, a common denominator bounds the possible sublattices of a fixed integral lattice.
-/

public section

namespace Submodule

/-- If `R / I` is finite and `N` is finitely generated, only finitely many submodules lie
between `I • N` and `N`. -/
theorem finite_Icc_smul {R V : Type*} [CommRing R] [AddCommMonoid V] [Module R V]
    (N : Submodule R V) (hN : N.FG) (I : Ideal R) [Finite (R ⧸ I)] :
    (Set.Icc (I • N) N).Finite := by
  let := Module.addCommMonoidToAddCommGroup R (M := V)
  let K := I • (⊤ : Submodule R N)
  have := Module.Finite.of_fg hN
  have : Finite (N ⧸ K) := finite_quotient_smul I Module.Finite.fg_top
  have hK : K.map N.subtype = I • N := by simp only [K, map_smul'', map_subtype_top]
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ (iccOrderIsoQuotientOfMapEq K hK).symm.toEquiv)

end Submodule
