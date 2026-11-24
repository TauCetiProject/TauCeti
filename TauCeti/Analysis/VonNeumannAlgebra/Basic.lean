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
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Concrete von Neumann algebras: C⋆-structure, reducing subspaces, and orbit projections

A concrete von Neumann algebra is norm closed, since it is a double commutant.
Its elements therefore form a C⋆-algebra with the inherited operator norm and adjoint.
This allows the abstract continuous functional calculus and positive-functional APIs to
be applied directly to concrete algebras, including those acting on the zero Hilbert space.

The instances use Mathlib's generic subobject constructions, in particular
`StarSubalgebra.cstarAlgebra` and, for the order inherited from the Loewner order on operators,
`Subtype.starOrderedRing`. The underlying star subalgebra has the same instances;
no new norm, completion, or algebra carrier is introduced.

This file also records the correspondence between projections in `M` (or `M.commutant`) and
closed subspaces invariant under or reducing `M.commutant` (or `M`), together with the orbit
projection lemmas showing that for any `S : Set H`, the orthogonal projection onto the closed
span of `{x v | x ∈ M, v ∈ S}` lies in `M.commutant`
(`VonNeumannAlgebra.starProjection_topologicalClosure_span_mem_commutant`), and also in `M`
whenever `S` is invariant under `M.commutant`
(`VonNeumannAlgebra.starProjection_topologicalClosure_span_mem`).
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

/-! ### Reducing-subspace correspondence -/

/-- The orthogonal projection onto `U` lies in `M` if and only if `U` is invariant under every
operator in `M.commutant`. -/
theorem starProjection_mem_iff_mem_invtSubmodule {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M ↔
      ∀ y ∈ M.commutant, U ∈ Module.End.invtSubmodule (y : Module.End ℂ H) := by
  simpa [U.range_starProjection] using
    IsStarProjection.mem_iff (isStarProjection_starProjection (U := U)) M

/-- **Reducing-subspace correspondence (`M`).** The orthogonal projection onto `U` lies in `M` if
and only if `U` reduces every operator in `M.commutant`. -/
theorem starProjection_mem_iff_isReducing {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M ↔ ∀ y ∈ M.commutant, U.IsReducing (y : Module.End ℂ H) := by
  simp_rw [U.isReducing_coe_iff_commute_starProjection,
    Commute.symm_iff (a := U.starProjection), commute_iff_eq]
  rw [← mem_commutant_iff, M.commutant_commutant]

/-- The orthogonal projection onto `U` lies in `M.commutant` if and only if `U` is invariant under
every operator in `M`. -/
theorem starProjection_mem_commutant_iff_mem_invtSubmodule {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M.commutant ↔
      ∀ x ∈ M, U ∈ Module.End.invtSubmodule (x : Module.End ℂ H) := by
  simpa using starProjection_mem_iff_mem_invtSubmodule (M := M.commutant) U

/-- **Reducing-subspace correspondence (`M'`).** The orthogonal projection onto `U` lies in
`M.commutant` if and only if `U` reduces every operator in `M`. -/
theorem starProjection_mem_commutant_iff_isReducing {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M.commutant ↔ ∀ x ∈ M, U.IsReducing (x : Module.End ℂ H) := by
  simpa using starProjection_mem_iff_isReducing (M := M.commutant) U

/-- Projections onto orthogonal complements belong to `M` simultaneously. -/
@[simp]
theorem starProjection_orthogonal_mem_iff {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection ∈ M ↔ U.starProjection ∈ M := by
  simp_rw [starProjection_mem_iff_isReducing, U.isReducing_orthogonal_iff]

/-! ### Orbit projections -/

/-- For any set of vectors `S`, the orthogonal projection onto the closed span of the `M`-orbit
`{x v | x ∈ M, v ∈ S}` lies in `M.commutant`. -/
theorem starProjection_topologicalClosure_span_mem_commutant (M : VonNeumannAlgebra H)
    (S : Set H) :
    (Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}).topologicalClosure.starProjection ∈
      M.commutant := by
  set L₀ := Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}
  rw [starProjection_mem_commutant_iff_mem_invtSubmodule]
  intro z hz
  rw [Module.End.mem_invtSubmodule]
  refine Submodule.topologicalClosure_minimal _ ?_
    (L₀.isClosed_topologicalClosure.preimage z.continuous)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  exact Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨z * x, M.mul_mem hz hx, v, hv, mul_apply_eq_comp z x v⟩)

/-- If `S : Set H` is invariant under every operator in `M.commutant`, then the orthogonal
projection onto the closed span of `{x v | x ∈ M, v ∈ S}` lies in `M`. -/
theorem starProjection_topologicalClosure_span_mem (M : VonNeumannAlgebra H) {S : Set H}
    (hS : ∀ y ∈ M.commutant, Set.MapsTo y S S) :
    (Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}).topologicalClosure.starProjection ∈
      M := by
  set L₀ := Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}
  rw [starProjection_mem_iff_mem_invtSubmodule]
  intro y hy
  rw [Module.End.mem_invtSubmodule]
  refine Submodule.topologicalClosure_minimal _ ?_
    (L₀.isClosed_topologicalClosure.preimage y.continuous)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  refine Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨x, hx, y v, hS y hy hv, ?_⟩)
  simpa [mul_apply_eq_comp] using DFunLike.congr_fun (mem_commutant_iff.mp hy x hx) v

end VonNeumannAlgebra
