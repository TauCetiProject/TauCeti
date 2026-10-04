/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.Degree
public import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import Mathlib.RingTheory.SimpleRing.Congr
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Scaling
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# The even Clifford algebra in odd dimension is central simple

For a regular quadratic form in odd dimension over a field of characteristic different from
two, its even Clifford algebra is central and a simple ring. With finite dimensionality, inherited
from the full Clifford algebra, this is the odd-dimensional algebra whose Brauer class defines the
Clifford invariant.

The reduction uses diagonalization and `TauCeti.CliffordAlgebra.evenProdSMulSqEquiv`: splitting
off a nondegenerate line identifies the even algebra with the full Clifford algebra of a regular
form in one lower dimension, which is central simple by the even-dimensional theorem. No square
root or extension of the base field is needed for this reduction.

## Main results

* `TauCeti.CliffordAlgebra.exists_nonempty_algEquiv_even_of_odd_finrank`: the even algebra is
  isomorphic to the Clifford algebra of a regular form of even dimension.
* `TauCeti.CliffordAlgebra.isSimpleRing_even_of_odd_finrank`: the even algebra is a simple ring.
* `TauCeti.CliffordAlgebra.isCentral_even_of_odd_finrank`: the even algebra is central.
* `TauCeti.CliffordAlgebra.deg_even_of_odd_finrank`: its degree is
  `2 ^ ((finrank K V - 1) / 2)`.
* `TauCeti.CliffordAlgebra.deg_even_of_finrank_eq_five`: in dimension five its degree is four.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Theorem V.2.5.
-/

public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

open Module _root_.QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [NeZero (2 : K)] {Q : QuadraticForm K V}

/-- The even Clifford algebra of a regular odd-dimensional quadratic space is isomorphic to the
full Clifford algebra of a regular form in one lower, hence even, dimension: splitting off a line
`⟨a⟩` from `Q ≅ ⟨a⟩ ⊥ P` gives `even Q ≃ₐ[K] CliffordAlgebra (-a⁻¹ • P)`. The new form lives on
`Fin n → K`, so the isomorphism also moves the algebra into the universe of `K`. -/
theorem exists_nonempty_algEquiv_even_of_odd_finrank (hQ : Q.Nondegenerate)
    (hV : Odd (finrank K V)) :
    ∃ (n : ℕ) (P : QuadraticForm K (Fin n → K)), P.Nondegenerate ∧ Even n ∧
      Nonempty (even Q ≃ₐ[K] CliffordAlgebra P) := by
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
    -- By `Units.val_neg` (`rfl`), `↑a` is definitionally `-↑(w 0)⁻¹`, as in `e` below.
    have hP : ((a : K) • P).Nondegenerate :=
      (nondegenerate_smul_iff a.isUnit P).mpr (nondegenerate_presentedForm _)
    have en := e.trans (presentedFormConsIsometryEquiv w).symm
    have ec := en.trans (QuadraticMap.IsometryEquiv.prodComm _ P)
    have hn' : Even n := by
      simpa [← Nat.not_even_iff_odd, Nat.even_add_one] using hn
    exact ⟨n, _, hP, hn', ⟨(evenEquivOfIsometry ec).trans (evenProdSMulSqEquiv P (w 0))⟩⟩

/-- The even Clifford algebra of a regular odd-dimensional quadratic space is a simple ring.
Together with centrality and inherited finite dimensionality, this defines its Brauer class. -/
theorem isSimpleRing_even_of_odd_finrank (hQ : Q.Nondegenerate) (hV : Odd (finrank K V)) :
    IsSimpleRing (even Q) := by
  obtain ⟨n, P, hP, hn, ⟨e⟩⟩ := exists_nonempty_algEquiv_even_of_odd_finrank hQ hV
  exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv
    (isSimpleRing_of_even_finrank hP (by simpa using hn))

/-- **The even Clifford algebra of a regular odd-dimensional quadratic space is central** (Lam
V.2.5): its centre is the base field, although the centre of the full Clifford algebra is
two-dimensional in odd dimension. -/
theorem isCentral_even_of_odd_finrank (hQ : Q.Nondegenerate) (hV : Odd (finrank K V)) :
    Algebra.IsCentral K (even Q) := by
  obtain ⟨n, P, hP, hn, ⟨e⟩⟩ := exists_nonempty_algEquiv_even_of_odd_finrank hQ hV
  have hC := isCentral_of_even_finrank hP (by simpa using hn)
  -- `Algebra.IsCentral.of_algEquiv` needs both algebras in one universe, while `even Q` lives in
  -- that of `V`; its two-line proof is repeated for the universe-heterogeneous `e`.
  refine ⟨fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hC.1 ((MulEquivClass.apply_mem_center_iff e).mpr hx)
  exact ⟨k, by simpa [Algebra.ofId] using congr(e.symm $hk)⟩

/-- **The degree of the even Clifford algebra in odd dimension.** For a quadratic form on a
space of dimension `2m + 1`, the even Clifford algebra has dimension `2 ^ (2m)`, hence degree
`2 ^ m`. When the form is regular, the preceding results also make this algebra central simple. -/
theorem deg_even_of_odd_finrank (hV : Odd (finrank K V)) :
    Algebra.deg K (even Q) = 2 ^ ((finrank K V - 1) / 2) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV.pos
  apply Algebra.deg_eq_of_finrank_eq_sq
  rw [CliffordAlgebra.finrank_even Q]
  obtain ⟨m, hm⟩ := hV
  simp [hm, pow_mul, Nat.mul_comm]

/-- **A five-dimensional even Clifford algebra has degree four.** For a regular form, this is the
algebra-size part of the description of `Spin₅` as the unitary group of a degree-four central
simple algebra with its canonical symplectic involution. -/
theorem deg_even_of_finrank_eq_five (hV : finrank K V = 5) :
    Algebra.deg K (even Q) = 4 := by
  have hodd : Odd (finrank K V) := by
    rw [hV]
    exact ⟨2, by norm_num⟩
  rw [deg_even_of_odd_finrank (Q := Q) hodd, hV]
  norm_num

end TauCeti.CliffordAlgebra
