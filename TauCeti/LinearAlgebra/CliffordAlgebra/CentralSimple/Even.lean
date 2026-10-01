/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import Mathlib.RingTheory.SimpleRing.Congr
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Scaling
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Simplicity of the even Clifford algebra in odd dimension

For a regular quadratic form in odd dimension over a field of characteristic different from
two, its even Clifford algebra is a simple ring. Together with centrality and finite
dimensionality, this supplies the odd-dimensional algebra whose Brauer class defines the
Clifford invariant.

The reduction uses diagonalization and `TauCeti.CliffordAlgebra.evenProdSqEquiv`: splitting off a
nondegenerate line identifies the even algebra with the full Clifford algebra of a regular
form in one lower dimension. No square root or extension of the base field is needed for
this reduction. Finite dimensionality is inherited from the full Clifford algebra.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Theorem V.2.5.
-/

public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

open Module _root_.QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [NeZero (2 : K)] {Q : QuadraticForm K V}

/-- The even Clifford algebra of a regular odd-dimensional quadratic space is a simple ring.
Together with centrality and inherited finite dimensionality, this defines its Brauer class. -/
theorem isSimpleRing_even_of_odd_finrank (hQ : Q.Nondegenerate) (hV : Odd (finrank K V)) :
    IsSimpleRing (even Q) := by
  let : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨⟨n, w⟩, ⟨e⟩⟩ := exists_presentedForm_equivalent Q hQ
  have hn : Odd n := by
    have he : finrank K V = n := by simpa using e.toLinearEquiv.finrank_eq
    exact he ▸ hV
  cases n with
  | zero => simp at hn
  | succ n =>
    let P := presentedForm (⟨n, fun i => w i.succ⟩ : RegularFormPresentation K)
    let a : Kˣ := -(w 0)⁻¹
    have hP : ((a : K) • P).Nondegenerate :=
      (nondegenerate_smul_iff a.isUnit P).mpr (nondegenerate_presentedForm _)
    have en := e.trans (presentedFormConsIsometryEquiv w).symm
    have ec := en.trans (QuadraticMap.IsometryEquiv.prodComm _ P)
    let e := (evenEquivOfIsometry ec).trans (evenProdSqEquiv P (w 0))
    have hn' : Even n := by
      simpa [← Nat.not_even_iff_odd, Nat.even_add_one] using hn
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv
      (isSimpleRing_of_even_finrank hP (by simpa using hn'))

end TauCeti.CliffordAlgebra
