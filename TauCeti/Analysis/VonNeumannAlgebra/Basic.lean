/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Concrete von Neumann algebras as C⋆-algebras

A concrete von Neumann algebra is norm closed, since it is a double commutant.
Its elements therefore form a C⋆-algebra with the inherited operator norm and adjoint.
This allows the abstract continuous functional calculus and positive-functional APIs to
be applied directly to concrete algebras, including those acting on the zero Hilbert space.

The instances use Mathlib's generic subobject constructions, in particular
`StarSubalgebra.cstarAlgebra` and, for the order inherited from the Loewner order on operators,
`Subtype.starOrderedRing`. The underlying star subalgebra has the same instances;
no new norm, completion, or algebra carrier is introduced. We also provide the canonical
star algebra isomorphism `VonNeumannAlgebra.equivOfEq` between equal von Neumann algebras.
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Concrete von Neumann algebras are closed under complex scalar multiplication. -/
instance instSMulMemClass : SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {M} c {_} ha := SMulMemClass.smul_mem (s := M.toStarSubalgebra) c ha

/-- A concrete von Neumann algebra is closed in the operator norm topology. -/
instance isClosed (M : VonNeumannAlgebra H) : IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

/-- The underlying star subalgebra is closed in the same operator norm topology. -/
instance instIsClosedToStarSubalgebra (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  simpa only [coe_toStarSubalgebra] using M.isClosed

/-- Equal concrete von Neumann algebras on `H` are canonically star-isomorphic. -/
noncomputable def equivOfEq {M N : VonNeumannAlgebra H} (h : M = N) : M ≃⋆ₐ[ℂ] N :=
  StarAlgEquiv.ofAlgEquiv
    (Subalgebra.equivOfEq M.toStarSubalgebra.toSubalgebra N.toStarSubalgebra.toSubalgebra
      congr(($h).toStarSubalgebra.toSubalgebra))
    fun _ ↦ rfl

@[simp]
theorem coe_equivOfEq_apply {M N : VonNeumannAlgebra H} (h : M = N) (x : M) :
    ((equivOfEq h x : N) : H →L[ℂ] H) = x := by
  rfl

@[simp]
theorem equivOfEq_symm {M N : VonNeumannAlgebra H} (h : M = N) :
    (equivOfEq h).symm = equivOfEq h.symm := by
  rfl

/-- The order on a von Neumann algebra inherited from the Loewner order on operators makes it a
star-ordered ring, so that positive functionals on it are those of the C⋆-algebra `M`. This
specializes `Subtype.starOrderedRing`, whose instance search over the operators on a concrete
Hilbert space, such as a GNS space, otherwise rebuilds their continuous functional calculus and
fails. -/
instance instStarOrderedRingToStarSubalgebra (M : VonNeumannAlgebra H) :
    StarOrderedRing M.toStarSubalgebra :=
  Subtype.starOrderedRing _

end VonNeumannAlgebra
