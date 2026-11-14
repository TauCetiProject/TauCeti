/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.InnerProductSpace.Amplification

/-!
# Concrete von Neumann algebras as C⋆-algebras and operator matrices

A concrete von Neumann algebra is norm closed, since it is a double commutant.
Its elements therefore form a C⋆-algebra with the inherited operator norm and adjoint.
This allows the abstract continuous functional calculus and positive-functional APIs to
be applied directly to concrete algebras, including those acting on the zero Hilbert space.

The instances use Mathlib's generic subobject constructions, in particular
`StarSubalgebra.cstarAlgebra`. The underlying star subalgebra has the same instances;
no new norm, completion, or algebra carrier is introduced.

For a finite index type `ι`, `VonNeumannAlgebra.piLpMatrix` forms the matrix von Neumann algebra
`M_ι(M)` of operators on `PiLp 2 (fun _ : ι => H)` with matrix entries in `M`.
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

/-- The matrix von Neumann algebra `M_ι(M)` of operators on `PiLp 2 (fun _ : ι => H)` whose
`(i, j)` entries belong to `M`. -/
noncomputable def piLpMatrix (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    VonNeumannAlgebra (PiLp 2 (fun _ : ι => H)) where
  toStarSubalgebra := M.toStarSubalgebra.piLpMatrix ι
  centralizer_centralizer' := by
    have h := M.toStarSubalgebra.coe_piLpMatrix_centralizer_centralizer ι
    have hc := M.toStarSubalgebra.coe_piLpMatrix ι
    have hmid : {T : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) |
        ∀ i j, T.piLpEntry i j ∈ (M.toStarSubalgebra : Set (H →L[ℂ] H)).centralizer.centralizer} =
        {T | ∀ i j, T.piLpEntry i j ∈ M.toStarSubalgebra} := by
      ext T
      simp [M.centralizer_centralizer]
    exact h.trans (hmid.trans hc.symm)

@[simp]
theorem mem_piLpMatrix_iff {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)} :
    T ∈ M.piLpMatrix ι ↔ ∀ i j, T.piLpEntry i j ∈ M :=
  M.toStarSubalgebra.mem_piLpMatrix_iff

@[simp]
theorem coe_piLpMatrix (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (M.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) =
      {T | ∀ i j, T.piLpEntry i j ∈ M} :=
  M.toStarSubalgebra.coe_piLpMatrix ι

end VonNeumannAlgebra
