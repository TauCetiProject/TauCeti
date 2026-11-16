/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Detecting comodule fixed vectors on points

Let `M` be a right comodule over `H`, where `H` is both an algebra and a coalgebra over a
commutative semiring `R`. A point `g : H →ₐ[R] A` acts on the scalar extension `A ⊗[R] M` by
`TauCeti.Comodule.endOfPoint`, and it fixes `1 ⊗ m` whenever `m` is fixed by the coaction, that
is, whenever `m` lies in `TauCeti.Comodule.fixedSubcomodule`. This file proves two converses,
which say on which points the fixed vectors can be detected.

The first holds with no hypothesis on `R`, `H` or `M`. A vector `m` is fixed by the coaction as
soon as `1 ⊗ m` is fixed by one point `g` for which `M ⊗[R] H → M ⊗[R] A` is injective. When `H`
is commutative the identity of `H` is such a point, the universal point: the fixed vectors of
the comodule are exactly the vectors fixed by the universal point, hence exactly the vectors
fixed by every point with values in every commutative `R`-algebra. The universal point is needed
here. For the group `μ_p` over `𝔽_p` and its weight-one line, every point with values in a field
acts trivially, and no nonzero vector is fixed by the coaction.

The second is for a reduced commutative bialgebra `H` of finite type over a field `k`. A vector
`m : M` is fixed by the coaction if and only if every point of `H` valued in one algebraically
closed extension fixes `1 ⊗ m` in the scalar extension. Evaluating the pointwise fixed-vector
equation against every linear functional shows that every geometric point takes the corresponding
matrix coefficient of `m` to its trivial-comodule value. Reduced finite-type point separation then
identifies those coefficients in `H`. A finite-dimensional subspace containing the single tensor
`coact m - m ⊗ 1` has enough coordinate functionals to show that this tensor vanishes.

The representation-level restatements of the second criterion live in
`TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic`. That criterion is the bridge
in the Kolchin induction: a common fixed vector obtained from the geometric point representation is
thereby promoted to a fixed vector of the comodule itself. The first criterion is restated for
natural point representations in
`TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Invariants`.

## Main declarations

* `TauCeti.Comodule.endOfPoint_one_tmul_eq_iff`: a point fixes `1 ⊗ m` exactly when it sends the
  coefficients of `coact m` to those of `m ⊗ 1`.
* `TauCeti.Comodule.mem_fixedSubcomodule_iff_endOfPoint_of_injective`: a point at which
  `M ⊗[R] H → M ⊗[R] A` is injective detects the fixed vectors.
* `TauCeti.Comodule.mem_fixedSubcomodule_iff_endOfPoint_algEquiv` and
  `TauCeti.Comodule.mem_fixedSubcomodule_iff_endOfPoint_id`: the universal point, and every point
  that is an isomorphism, detects the fixed vectors.
* `TauCeti.Comodule.mem_fixedSubcomodule_iff_forall_endOfPoint`: the fixed vectors are the
  vectors fixed by every point with values in every commutative algebra.
* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq`: geometric-point detection of
  a fixed vector for a bialgebra comodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.8 and I.2.10, for the fixed vectors
  of a comodule as the vectors fixed by all points.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open WithConv

universe u v w x y

noncomputable section

section Universal

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Semiring

variable {A : Type x} [Semiring H] [Algebra R H] [Coalgebra R H] [Comodule R H M]
variable [CommSemiring A] [Algebra R A]

/-- A point `g` fixes the scalar extension `1 ⊗ m` of a vector exactly when pushing the
coefficients of `coact m` through `g` gives `m ⊗ 1`. -/
theorem endOfPoint_one_tmul_eq_iff (g : H →ₐ[R] A) (m : M) :
    endOfPoint M g (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m ↔
      g.toLinearMap.lTensor M (coact (R := R) (C := H) m) = m ⊗ₜ[R] (1 : A) := by
  rw [endOfPoint_tmul, one_smul, ← TensorProduct.comm_tmul R M A m 1,
    (TensorProduct.comm R M A).injective.eq_iff]

/-- A point `g : H →ₐ[R] A` for which `M ⊗[R] H → M ⊗[R] A` is injective detects the fixed
vectors of the comodule `M`: a vector is fixed by the coaction exactly when `g` fixes its scalar
extension.

The injectivity holds for the universal point, and for every injective `g` when `M` is flat. -/
theorem mem_fixedSubcomodule_iff_endOfPoint_of_injective (g : H →ₐ[R] A)
    (hg : Function.Injective (g.toLinearMap.lTensor M)) {m : M} :
    m ∈ fixedSubcomodule R H M ↔ endOfPoint M g (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m := by
  rw [endOfPoint_one_tmul_eq_iff, mem_fixedSubcomodule, ← hg.eq_iff]
  simp

/-- A point that is an isomorphism of algebras detects the fixed vectors of a comodule. Such
points are the universal point and its universe lifts. -/
theorem mem_fixedSubcomodule_iff_endOfPoint_algEquiv (e : H ≃ₐ[R] A) {m : M} :
    m ∈ fixedSubcomodule R H M ↔ endOfPoint M (e : H →ₐ[R] A) (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m :=
  mem_fixedSubcomodule_iff_endOfPoint_of_injective _ <| by
    rw [AlgEquiv.toAlgHom_toLinearMap, ← LinearEquiv.coe_lTensor, LinearEquiv.coe_coe]
    exact (e.toLinearEquiv.lTensor M).injective

end Semiring

section CommSemiring

variable [CommSemiring H] [Algebra R H] [Coalgebra R H] [Comodule R H M]

/-- The universal point of a commutative `H`, the identity of `H`, detects the fixed vectors of a
comodule: a vector is fixed by the coaction exactly when the universal point fixes its scalar
extension. -/
theorem mem_fixedSubcomodule_iff_endOfPoint_id {m : M} :
    m ∈ fixedSubcomodule R H M ↔
      endOfPoint M (AlgHom.id R H) (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m :=
  mem_fixedSubcomodule_iff_endOfPoint_of_injective _ <| by
    simpa using Function.injective_id

/-- The fixed vectors of a comodule are the vectors whose scalar extension is fixed by every
point with values in every commutative algebra: for an affine group, the invariants of the
comodule are the vectors fixed by the functor of points.

The value algebras range over a universe containing that of `H`, so that a universe lift of `H`,
with its universal point, is among them. -/
theorem mem_fixedSubcomodule_iff_forall_endOfPoint {m : M} :
    m ∈ fixedSubcomodule R H M ↔
      ∀ (A : Type max v y) [CommSemiring A] [Algebra R A] (g : H →ₐ[R] A),
        endOfPoint M g (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m := by
  refine ⟨fun hm A _ _ g ↦ endOfPoint_tmul_of_coact_eq_tmul_one (mem_fixedSubcomodule.mp hm) g 1,
    fun h ↦ ?_⟩
  exact (mem_fixedSubcomodule_iff_endOfPoint_algEquiv
    (ULift.algEquiv (R := R) (A := H)).symm).mpr (h (ULift.{y} H) _)

end CommSemiring

end Universal

section Bialgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing H] [Bialgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- A vector in a comodule over a reduced finite-type bialgebra is fixed by the coaction exactly
when every algebraically closed point fixes its scalar extension. -/
theorem coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : H →ₐ[k] K, endOfPoint M g (1 ⊗ₜ[k] m) = 1 ⊗ₜ[k] m := by
  constructor
  · intro hm g
    rw [endOfPoint_tmul, hm]
    simp
  · intro h
    have hcoeff (φ : Module.Dual k M) :
        matrixCoefficient (C := H) φ m = (φ m) • (1 : H) := by
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
      intro g
      have heval := congrArg
        (fun z ↦ TauCeti.Module.Dual.baseChangeEvaluation
          (R := k) (M := M) (A := K) (1 ⊗ₜ[k] φ) z) (h g)
      simpa [Algebra.smul_def] using heval
    let z := coact (R := k) (C := H) m - m ⊗ₜ[k] (1 : H)
    suffices z = 0 by exact sub_eq_zero.mp this
    obtain ⟨M', hM', hz⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
      ({z} : Set (M ⊗[k] H)) (Set.finite_singleton z)
    obtain ⟨z', hz'⟩ := hz (Set.mem_singleton z)
    let _ : Module.Finite k M' := hM'
    let b := Module.finBasis k M'
    have hz'zero : z' = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
      ext i
      rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
      obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
      rw [← hφ, LinearMap.rTensor_comp_apply, hz']
      simpa [z, matrixCoefficient_def, LinearMap.rTensor_def] using
        sub_eq_zero.mpr (hcoeff φ)
    rw [← hz', hz'zero, map_zero]

end Bialgebra

end

end TauCeti.Comodule
