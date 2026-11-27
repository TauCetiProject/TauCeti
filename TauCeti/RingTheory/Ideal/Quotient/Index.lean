/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Data.SetLike.Fintype

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
  have : Finite (Set.Ici K) := Finite.of_equiv _ K.comapMkQRelIso.toEquiv
  refine (Set.finite_range fun P : Set.Ici K => P.val.map N.subtype).subset ?_
  intro M hM
  refine ⟨⟨M.comap N.subtype, fun x hx => hM.1 ((mem_smul_top_iff I N x).1 hx)⟩, ?_⟩
  exact (map_comap_subtype N M).trans (inf_eq_right.mpr hM.2)

end Submodule
