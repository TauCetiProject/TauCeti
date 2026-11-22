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
public import TauCeti.Analysis.VonNeumannAlgebra.MatrixAmplification

/-!
# Concrete von Neumann algebras as C⋆-algebras and operator matrices

A concrete von Neumann algebra is norm closed, since it is a double commutant.
Its elements therefore form a C⋆-algebra with the inherited operator norm and adjoint.
This allows the abstract continuous functional calculus and positive-functional APIs to
be applied directly to concrete algebras, including those acting on the zero Hilbert space.

The instances use Mathlib's generic subobject constructions, in particular
`StarSubalgebra.cstarAlgebra` and, for the order inherited from the Loewner order on operators,
`Subtype.starOrderedRing`. The underlying star subalgebra has the same instances;
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

/-- The order on a von Neumann algebra inherited from the Loewner order on operators makes it a
star-ordered ring, so that positive functionals on it are those of the C⋆-algebra `M`. This
specializes `Subtype.starOrderedRing`, whose instance search over the operators on a concrete
Hilbert space, such as a GNS space, otherwise rebuilds their continuous functional calculus and
fails. -/
instance instStarOrderedRingToStarSubalgebra (M : VonNeumannAlgebra H) :
    StarOrderedRing M.toStarSubalgebra :=
  Subtype.starOrderedRing _

/-- The matrix von Neumann algebra `M_ι(M)` of operators on `PiLp 2 (fun _ : ι => H)` whose
`(i, j)` entries belong to `M`. -/
noncomputable def piLpMatrix (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    VonNeumannAlgebra (PiLp 2 (fun _ : ι => H)) where
  toStarSubalgebra := M.toStarSubalgebra.piLpMatrix ι
  centralizer_centralizer' := by
    ext T
    change T ∈ (M.toStarSubalgebra.piLpMatrix ι : Set _).centralizer.centralizer ↔
      T ∈ M.toStarSubalgebra.piLpMatrix ι
    rw [M.toStarSubalgebra.mem_centralizer_centralizer_piLpMatrix_iff,
      StarSubalgebra.mem_piLpMatrix]
    simp [M.centralizer_centralizer]

/-- The underlying star subalgebra of `M.piLpMatrix ι` is `M.toStarSubalgebra.piLpMatrix ι`. -/
@[simp]
theorem toStarSubalgebra_piLpMatrix (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    (M.piLpMatrix ι).toStarSubalgebra = M.toStarSubalgebra.piLpMatrix ι :=
  (rfl)

@[simp]
theorem mem_piLpMatrix_iff {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)} :
    T ∈ M.piLpMatrix ι ↔ ∀ i j, T.piLpEntry i j ∈ M :=
  M.toStarSubalgebra.mem_piLpMatrix

@[simp]
theorem coe_piLpMatrix (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (M.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) =
      {T | ∀ i j, T.piLpEntry i j ∈ M} := by
  ext T
  exact M.toStarSubalgebra.mem_piLpMatrix

/-- Placing an element in a single `(i, j)` block belongs to `M.piLpMatrix ι` if and only if
the element belongs to `M`. -/
theorem singleEntryCLM_mem_piLpMatrix {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {i j : ι} {s : H →L[ℂ] H} :
    PiLp.singleEntryCLM i j s ∈ M.piLpMatrix ι ↔ s ∈ M :=
  M.toStarSubalgebra.singleEntryCLM_mem_piLpMatrix

/-- Diagonal amplification maps `M` into `M.piLpMatrix ι`. -/
theorem diagStarAlgHom_mem_piLpMatrix {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : H →L[ℂ] H} (hs : s ∈ M) :
    PiLp.diagStarAlgHom ℂ H ι s ∈ M.piLpMatrix ι :=
  M.toStarSubalgebra.diagStarAlgHom_mem_piLpMatrix hs

/-- The commutant of the matrix von Neumann algebra `M.piLpMatrix ι` consists of block-diagonal
operators with constant diagonal entry in `M.commutant`. -/
theorem coe_commutant_piLpMatrix (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    ((M.piLpMatrix ι).commutant :
        Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) =
      {R | (∀ i j, i ≠ j → R.piLpEntry i j = 0) ∧
        (∀ i j, R.piLpEntry i i = R.piLpEntry j j) ∧
        ∀ i, R.piLpEntry i i ∈ M.commutant} := by
  rw [coe_commutant, ← coe_toStarSubalgebra, toStarSubalgebra_piLpMatrix]
  ext R
  simp only [StarSubalgebra.mem_centralizer_piLpMatrix_iff, coe_toStarSubalgebra, ← coe_commutant,
    SetLike.mem_coe, Set.mem_ofPred_eq]

end VonNeumannAlgebra
