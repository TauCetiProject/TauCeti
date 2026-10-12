/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Imported publicly: exactly the modules defining what occurs in the exported statements, namely
-- `CliffordAlgebra`, `Algebra.IsCentral`, `IsSimpleRing`, `QuadraticMap.Nondegenerate` and
-- `FiniteDimensional` / `Module.finrank`.
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.RingTheory.SimpleRing.Defs
-- Non-public: the polarized structure theorem the proofs descend from, the separable closure,
-- Mathlib's base-change equivalence of Clifford algebras, the transport of simplicity along a ring
-- equivalence, the two descent lemmas for centrality and simplicity, and the base change of
-- nondegeneracy are used only inside proofs.
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.RingTheory.SimpleRing.Congr
import TauCeti.Algebra.CentralSimple.BaseChange
import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
import TauCeti.RepresentationTheory.Spin.Structure

/-!
# The Clifford algebra of an even-dimensional regular form is central simple

Let `Q` be a nondegenerate quadratic form on a finite-dimensional vector space `V` over a field `K`
of characteristic different from `2`. This file proves that when `finrank K V` is **even**, the
Clifford algebra `CliffordAlgebra Q` is a central simple `K`-algebra (Lam, *Introduction to
Quadratic Forms over Fields*, V.2.4; Chevalley, *The Algebraic Theory of Spinors*, II.2). It is
finite-dimensional by `CliffordAlgebra.instFinite`, so its Brauer class is defined: this is the even
half of the Clifford invariant of a regular quadratic form.

Both hypotheses matter. In odd dimension the Clifford algebra is classically not central, its
centre being spanned by `1` and the volume element, and the central simple algebra attached to the
form is its even subalgebra instead (Lam V.2.5); that case is not treated here. For the zero form on
a nonzero space the Clifford algebra is the exterior algebra, which is not simple.

## Main results

* `CliffordAlgebra.isCentral_of_even_finrank`: the Clifford algebra of a nondegenerate form in even
  dimension is central over `K`.
* `CliffordAlgebra.isSimpleRing_of_even_finrank`: it is a simple ring.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, GSM 67, AMS (2005), Theorem V.2.4.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open scoped TensorProduct

open Module

namespace CliffordAlgebra

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

section Invertible

-- The private helpers are stated with `Invertible (2 : K)`, which `QuadraticForm.baseChange` and
-- `TauCeti.QuadraticForm.Nondegenerate.baseChange` require; the public theorems assume only
-- `NeZero (2 : K)` and install the invertibility locally.
variable [Invertible (2 : K)]

omit [FiniteDimensional K V] in
/-- `2` stays invertible in a separable closure. -/
@[instance_reducible]
private noncomputable def invertibleTwoSepClosure : Invertible (2 : SeparableClosure K) :=
  (Invertible.map (algebraMap K (SeparableClosure K)) 2).copy 2 (map_ofNat _ _).symm

/-- Polarization data for the extension of a nondegenerate form to a separable closure. -/
private noncomputable def polarizationSepClosure (hQ : Q.Nondegenerate) :
    TauCeti.SpinPolarizationData (Q.baseChange (SeparableClosure K)) :=
  letI := invertibleTwoSepClosure (K := K)
  TauCeti.SpinPolarizationData.ofNondegenerate _
    (QuadraticForm.Nondegenerate.baseChange (L := SeparableClosure K) hQ)

end Invertible

omit [FiniteDimensional K V] in
/-- Extension of scalars preserves the parity of the dimension. -/
private theorem even_finrank_baseChange_sepClosure (heven : Even (finrank K V)) :
    Even (finrank (SeparableClosure K) (SeparableClosure K ⊗[K] V)) := by
  rwa [Module.finrank_baseChange]

variable [NeZero (2 : K)]

-- Both public theorems are proved by descent from a separable closure `Kˢ` of `K`. Over `Kˢ` the
-- extended form `Q.baseChange Kˢ` is still nondegenerate and carries polarization data
-- (`polarizationSepClosure`), so the even-dimensional structure theorem identifies its Clifford
-- algebra with the endomorphism algebra of the spinor module, which is central simple. Mathlib's
-- `CliffordAlgebra.equivBaseChange` identifies that Clifford algebra with the scalar extension
-- `Kˢ ⊗[K] CliffordAlgebra Q`, and centrality and simplicity descend along a field extension
-- (`TauCeti.Algebra.IsCentral.of_baseChange`, `TauCeti.IsSimpleRing.of_baseChange`).

/-- **The Clifford algebra of a nondegenerate form in even dimension is central.** Over a field of
characteristic different from `2`, if `Q` is nondegenerate on a finite-dimensional space of even
dimension, then the centre of `CliffordAlgebra Q` is the base field. -/
theorem isCentral_of_even_finrank (hQ : Q.Nondegenerate) (heven : Even (finrank K V)) :
    Algebra.IsCentral K (CliffordAlgebra Q) := by
  let : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let := invertibleTwoSepClosure (K := K)
  have h : Algebra.IsCentral (SeparableClosure K)
      (CliffordAlgebra (Q.baseChange (SeparableClosure K))) :=
    (polarizationSepClosure hQ).isCentral_cliffordAlgebra
      (even_finrank_baseChange_sepClosure heven)
  have : Algebra.IsCentral (SeparableClosure K) (SeparableClosure K ⊗[K] CliffordAlgebra Q) :=
    Algebra.IsCentral.of_algEquiv _ _ _ (equivBaseChange (SeparableClosure K) Q)
  exact TauCeti.Algebra.IsCentral.of_baseChange (L := SeparableClosure K)

/-- **The Clifford algebra of a nondegenerate form in even dimension is a simple ring.** Over a
field of characteristic different from `2`, if `Q` is nondegenerate on a finite-dimensional space of
even dimension, then `CliffordAlgebra Q` has no two-sided ideals other than `⊥` and `⊤`. Together
with `CliffordAlgebra.isCentral_of_even_finrank` and `CliffordAlgebra.instFinite`, it is a
finite-dimensional central simple `K`-algebra. -/
theorem isSimpleRing_of_even_finrank (hQ : Q.Nondegenerate) (heven : Even (finrank K V)) :
    IsSimpleRing (CliffordAlgebra Q) := by
  let : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let := invertibleTwoSepClosure (K := K)
  have h : IsSimpleRing (CliffordAlgebra (Q.baseChange (SeparableClosure K))) :=
    (polarizationSepClosure hQ).isSimpleRing_cliffordAlgebra
      (even_finrank_baseChange_sepClosure heven)
  have : IsSimpleRing (SeparableClosure K ⊗[K] CliffordAlgebra Q) :=
    IsSimpleRing.of_ringEquiv (equivBaseChange (SeparableClosure K) Q).toRingEquiv h
  exact TauCeti.IsSimpleRing.of_baseChange (K := K) (L := SeparableClosure K)

end CliffordAlgebra
