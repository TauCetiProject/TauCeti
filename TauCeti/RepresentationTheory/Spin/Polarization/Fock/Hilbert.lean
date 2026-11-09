/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Metric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The native Hermitian Fock module

For an orthogonal complex structure `J` on a finite-dimensional Euclidean space and
`Q v = -‖v‖²`, the normalized Fock action acts on the exterior algebra of the holomorphic
polarization. Its Hermitian form makes the increasing wedges of an orthonormal polarization
basis orthonormal. Here this form supplies a native norm and complex inner product on that
same exterior algebra, so its Clifford action can be used with native adjoints, continuous
linear maps and the unitary half-spin action.

`fockInnerProductCore` chooses an orthonormal polarization basis to construct the form.
`fockInnerProductCore_inner` identifies it with the wedge Gram form for every such basis;
in particular the resulting metric is independent of that choice. Install the named
`fockNormedAddCommGroup` and `fockInnerProductSpace` locally, in that order. No global
norm or inner product instance on an exterior algebra is introduced.

The vacuum has norm one, and the normalized real Clifford action has native adjoint
`c(a)* = c(star a)`. Thus `c(v)* = -c(v)` for real vectors, with the normalization already
built into the Fock action. These identities supply the Hermitian hypothesis of the
half-spin representation and its restriction to either chirality eigenspace.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Matrix Module
open scoped ComplexOrder TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)

local notation "W" => SpinPolarizationData.W (J.spinPolarizationData hQJ hQnd)
local notation "S" => ExteriorAlgebra ℂ W

/-- An auxiliary orthonormal polarization basis used only to construct the intrinsic metric. -/
private def fockMetricBasis : Basis (Fin (finrank ℝ V / 2)) ℂ W :=
  (J.exists_basis_polar_tmulConj hQJ hQnd hQ (finrank ℝ V / 2)
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm).choose

private theorem fockMetricBasis_polar (i j : Fin (finrank ℝ V / 2)) :
    QuadraticMap.polar (Q.baseChange ℂ)
      (tmulConj V (J.fockMetricBasis hQJ hQnd hQ i : ℂ ⊗[ℝ] V))
      (J.fockMetricBasis hQJ hQnd hQ j) = if i = j then -2 else 0 :=
  (J.exists_basis_polar_tmulConj hQJ hQnd hQ (finrank ℝ V / 2)
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm).choose_spec i j

/-- The positive definite Hermitian form of the normalized Fock module, as a native
inner product core. Its increasing wedge basis is orthonormal for every orthonormal
basis of the holomorphic polarization. -/
@[instance_reducible]
def fockInnerProductCore : InnerProductSpace.Core ℂ S where
  inner s t := toLinearMapₛₗ₂ (starRingEnd ℂ)
    (J.fockMetricBasis hQJ hQnd hQ).ExteriorAlgebra
    (J.fockMetricBasis hQJ hQnd hQ).ExteriorAlgebra 1 s t
  conj_inner_symm s t := star_toLinearMapₛₗ₂_one_apply _ t s
  re_inner_nonneg s := (RCLike.nonneg_iff.mp (toLinearMapₛₗ₂_one_self_nonneg _ s)).1
  add_left s t u := by simp
  smul_left s t r := by simp
  definite s hs := (toLinearMapₛₗ₂_one_self_eq_zero_iff _).mp hs

/-- The Fock inner product core is the wedge Gram form for any orthonormal polarization
basis. In particular it does not depend on the auxiliary basis used in its construction. -/
theorem fockInnerProductCore_inner {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ W)
    (hb : ∀ i j, QuadraticMap.polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V))
      (b j) = if i = j then -2 else 0) (s t : S) :
    (J.fockInnerProductCore hQJ hQnd hQ).inner s t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra 1 s t := by
  exact LinearMap.congr_fun₂ (J.toLinearMapₛₗ₂_exteriorAlgebra_eq hQJ hQnd
    (J.fockMetricBasis hQJ hQnd hQ) (J.fockMetricBasis_polar hQJ hQnd hQ) b hb) s t

/-- The native normed additive group of the normalized Fock module. Use this as a local
instance before installing `fockInnerProductSpace`. -/
abbrev fockNormedAddCommGroup : NormedAddCommGroup S :=
  (J.fockInnerProductCore hQJ hQnd hQ).toNormedAddCommGroup

/-- The native complex inner product space of the normalized Fock module. Its norm is
`fockNormedAddCommGroup`, and its inner product is the basis-independent wedge Gram form. -/
abbrev fockInnerProductSpace :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    InnerProductSpace ℂ S :=
  InnerProductSpace.ofCore (J.fockInnerProductCore hQJ hQnd hQ).toCore

/-- The native inner product is the wedge Gram form of any orthonormal polarization basis. -/
theorem inner_fock {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Basis ι ℂ W)
    (hb : ∀ i j, QuadraticMap.polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V))
      (b j) = if i = j then -2 else 0) (s t : S) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ s t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra 1 s t :=
  J.fockInnerProductCore_inner hQJ hQnd hQ b hb s t

/-- Increasing wedge monomials of any orthonormal polarization basis are orthonormal
in the native Fock metric. -/
theorem orthonormal_fock {ι : Type*} [Finite ι] [LinearOrder ι] (b : Basis ι ℂ W)
    (hb : ∀ i j, QuadraticMap.polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V))
      (b j) = if i = j then -2 else 0) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    Orthonormal ℂ b.ExteriorAlgebra := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let := Fintype.ofFinite ι
  exact orthonormal_iff_ite.mpr fun i j ↦ by
    rw [J.inner_fock hQJ hQnd hQ b hb, toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]

/-- The vacuum of the normalized Fock module has inner product one with itself. -/
private theorem inner_fock_one_one : letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ (1 : S) 1 = 1 :=
  ExteriorAlgebra.toLinearMapₛₗ₂_apply_one_one (J.fockMetricBasis hQJ hQnd hQ)

/-- The vacuum of the normalized Fock module is a unit vector in the native norm. -/
@[simp]
theorem norm_fock_one : letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    ‖(1 : S)‖ = 1 := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), J.inner_fock_one_one hQJ hQnd hQ,
    RCLike.one_re, Real.sqrt_one]

/-- The native adjoint of the complexified Fock action uses conjugate-linear Clifford
conjugation. The complex-linear Clifford `star` is not its Hermitian adjoint. -/
@[simp↓]
theorem adjoint_fockAction (a : CliffordAlgebra (Q.baseChange ℂ)) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    LinearMap.adjoint (J.fockAction hQJ hQnd a) =
      J.fockAction hQJ hQnd (conjStar Q a) := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  apply Eq.symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro s t
  rw [J.inner_fock hQJ hQnd hQ _ (J.fockMetricBasis_polar hQJ hQnd hQ),
    J.inner_fock hQJ hQnd hQ _ (J.fockMetricBasis_polar hQJ hQnd hQ)]
  simpa only [conjStar_conjStar] using J.toLinearMapₛₗ₂_fockAction_left hQJ hQnd
    (J.fockMetricBasis hQJ hQnd hQ) (J.fockMetricBasis_polar hQJ hQnd hQ)
    (conjStar Q a) s t

/-- The native adjoint of the real Fock action is its Clifford-conjugate action. -/
@[simp↓]
theorem adjoint_realFockAction (a : CliffordAlgebra Q) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    LinearMap.adjoint (J.realFockAction hQJ hQnd a) =
      J.realFockAction hQJ hQnd (star a) := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [realFockAction_apply, realFockAction_apply,
    J.adjoint_fockAction hQJ hQnd hQ, conjStar_ofBaseChangeAux]

/-- Real Clifford generators act skew-adjointly on the native Hermitian Fock module. -/
theorem adjoint_realFockAction_ι (v : V) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    LinearMap.adjoint (J.realFockAction hQJ hQnd (ι Q v)) =
      -J.realFockAction hQJ hQnd (ι Q v) := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.adjoint_realFockAction hQJ hQnd hQ, star_ι, map_neg]

end TauCeti.AlmostComplexStructure
