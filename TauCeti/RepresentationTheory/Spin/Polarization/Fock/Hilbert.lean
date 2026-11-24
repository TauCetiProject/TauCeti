/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Metric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The native Hermitian Fock module

For an orthogonal complex structure `J` on a finite-dimensional Euclidean space `V` and
`Q v = -‖v‖²`, the normalized Fock action acts on the exterior algebra of the holomorphic
polarization `W`. Its basis-free Hermitian Gram form `J.fockGramForm` makes the increasing wedges
of any orthonormal polarization basis orthonormal. Here `J.fockGramForm` supplies a native norm and
complex inner product on that exterior algebra, so its Clifford action can be used with native
adjoints, continuous linear maps, and the unitary half-spin action.

`fockInnerProductCore` takes `J.fockGramForm` directly as its inner product and uses the existence
of an orthonormal polarization basis (`exists_basis_polar_tmulConj`) only to establish positivity
and definiteness. `fockInnerProductCore_inner` and `inner_fock` identify it with the wedge-basis
form of every orthonormal polarization basis, while `inner_fock_eq_zero_of_mem_exteriorPower`,
`inner_fock_ιMulti_ιMulti`, `inner_fock_ι_ι`, and `norm_fock_ιMulti_sq` give degree orthogonality
and the Gram-determinant formula
`⟪x₀ ∧ ⋯ ∧ x_{p-1}, y₀ ∧ ⋯ ∧ y_{p-1}⟫_ℂ = det ((innerₗ V).sesqComplexification (xᵢ, yⱼ))`. Install
the named `fockNormedAddCommGroup` and `fockInnerProductSpace` locally, in that order. No global
norm or inner product instance on an exterior algebra is introduced.

The vacuum has norm one, and the normalized real Clifford action has native adjoint
`c(a)* = c(star a)`. Thus `c(v)* = -c(v)` for real vectors, with the normalization already
built into the Fock action, so the real Fock action satisfies the geometric convention
`AlgHom.IsGeometricClifford`. By contrast, the unnormalized native action `spinAction (ι (1 ⊗ v))`
fails to be skew-adjoint whenever `v ≠ 0` (`adjoint_spinAction_ι_one_tmul_ne_neg`). These
identities supply the Hermitian hypothesis of the half-spin representation and its restriction to
either chirality eigenspace.

## Main definitions

* `TauCeti.AlmostComplexStructure.fockInnerProductCore`: the `InnerProductSpace.Core` given by
  `J.fockGramForm`.
* `TauCeti.AlmostComplexStructure.fockNormedAddCommGroup` and
  `TauCeti.AlmostComplexStructure.fockInnerProductSpace`: the local norm and complex inner product
  instances on `⋀ W`.

## Main results

* `TauCeti.AlmostComplexStructure.inner_fock_eq_fockGramForm` and
  `TauCeti.AlmostComplexStructure.inner_fock`: `inner ℂ` equals `J.fockGramForm` and the
  wedge-basis form of any orthonormal polarization basis.
* `TauCeti.AlmostComplexStructure.inner_fock_eq_zero_of_mem_exteriorPower`,
  `TauCeti.AlmostComplexStructure.inner_fock_ιMulti_ιMulti`,
  `TauCeti.AlmostComplexStructure.inner_fock_ι_ι`, and
  `TauCeti.AlmostComplexStructure.norm_fock_ιMulti_sq`: degree orthogonality, the Gram-determinant
  formula in every degree `p` (and its degree-one specialization), and the squared norm of a
  decomposable `p`-vector.
* `TauCeti.AlmostComplexStructure.orthonormal_fock` and
  `TauCeti.AlmostComplexStructure.norm_fock_one`: orthonormality of increasing wedge monomials and
  unit norm of the vacuum.
* `TauCeti.AlmostComplexStructure.adjoint_fockAction`,
  `TauCeti.AlmostComplexStructure.adjoint_realFockAction`,
  `TauCeti.AlmostComplexStructure.adjoint_realFockAction_ι`,
  `TauCeti.AlmostComplexStructure.isGeometricClifford_realFockAction`, and
  `TauCeti.AlmostComplexStructure.adjoint_spinAction_ι_one_tmul_ne_neg`: native adjoints of the
  normalized Fock actions, skew-adjointness of real vectors, the geometric convention
  `AlgHom.IsGeometricClifford`, and failure for the unnormalized `spinAction`.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds* (online author edition, `Lectures.pdf`),
  §2.2.4 and Proposition 12.1.19.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Matrix Module
open TauCeti.ExteriorAlgebra
open scoped ComplexOrder RealInnerProductSpace TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

local notation "W" => SpinPolarizationData.W (J.spinPolarizationData hQJ hQnd)
local notation "S" => ExteriorAlgebra ℂ W

/-- In the Euclidean convention `Q v = -‖v‖²`, `J.fockPolarForm` is the restriction to `W` of the
sesquilinear complexification of the real inner product `innerₗ V`. -/
theorem fockPolarForm_eq_sesqComplexification_innerₗ (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (x y : W) :
    J.fockPolarForm hQJ hQnd x y =
      LinearMap.BilinForm.sesqComplexification (innerₗ V) (x : ℂ ⊗[ℝ] V) (y : ℂ ⊗[ℝ] V) := by
  refine J.fockPolarForm_eq_sesqComplexification hQJ hQnd ⟨isSymm_inner.eq⟩ (fun v ↦ ?_) x y
  rw [hQ, innerₗ_apply_apply, real_inner_self_eq_norm_sq]

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- The positive definite Hermitian Gram form `J.fockGramForm` of the normalized Fock module, as a
native inner product core. Its increasing wedge basis is orthonormal for every orthonormal basis of
the holomorphic polarization. -/
@[instance_reducible]
def fockInnerProductCore : InnerProductSpace.Core ℂ S where
  inner s t := J.fockGramForm hQJ hQnd s t
  conj_inner_symm s t := J.star_fockGramForm_apply hQJ hQnd t s
  re_inner_nonneg s := by
    obtain ⟨b, hb⟩ := J.exists_basis_polar_tmulConj hQJ hQnd hQ (finrank ℝ V / 2)
      (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
    rw [← J.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm hQJ hQnd b hb]
    exact (RCLike.nonneg_iff.mp (toLinearMapₛₗ₂_one_self_nonneg b.ExteriorAlgebra s)).left
  add_left s t u := by simp
  smul_left s t r := by simp
  definite s hs := by
    obtain ⟨b, hb⟩ := J.exists_basis_polar_tmulConj hQJ hQnd hQ (finrank ℝ V / 2)
      (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
    rw [← J.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm hQJ hQnd b hb] at hs
    exact (toLinearMapₛₗ₂_one_self_eq_zero_iff b.ExteriorAlgebra).mp hs

/-- **The Fock inner product core equals the basis-free Fock Gram metric `J.fockGramForm`.** -/
theorem fockInnerProductCore_inner_eq_fockGramForm (s t : S) :
    (J.fockInnerProductCore hQJ hQnd hQ).inner s t = J.fockGramForm hQJ hQnd s t :=
  (rfl)

/-- The Fock inner product core agrees with the wedge-basis form for any orthonormal polarization
basis. -/
theorem fockInnerProductCore_inner {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ W)
    (hb : ∀ i j, QuadraticMap.polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V))
      (b j) = if i = j then -2 else 0) (s t : S) :
    (J.fockInnerProductCore hQJ hQnd hQ).inner s t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra 1 s t := by
  rw [J.fockInnerProductCore_inner_eq_fockGramForm hQJ hQnd hQ,
    J.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm hQJ hQnd b hb]

/-- The native normed additive group of the normalized Fock module. Use this as a local
instance before installing `fockInnerProductSpace`. -/
abbrev fockNormedAddCommGroup : NormedAddCommGroup S :=
  (J.fockInnerProductCore hQJ hQnd hQ).toNormedAddCommGroup

/-- The native complex inner product space of the normalized Fock module. Its norm is
`fockNormedAddCommGroup`, and its inner product is `J.fockGramForm`. -/
abbrev fockInnerProductSpace :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    InnerProductSpace ℂ S :=
  InnerProductSpace.ofCore (J.fockInnerProductCore hQJ hQnd hQ).toCore

/-- **The native complex inner product of the Fock module is `J.fockGramForm`.** -/
theorem inner_fock_eq_fockGramForm (s t : S) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ s t = J.fockGramForm hQJ hQnd s t :=
  J.fockInnerProductCore_inner_eq_fockGramForm hQJ hQnd hQ s t

/-- The native inner product agrees with the wedge-basis form of any orthonormal polarization
basis. -/
theorem inner_fock {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Basis ι ℂ W)
    (hb : ∀ i j, QuadraticMap.polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V))
      (b j) = if i = j then -2 else 0) (s t : S) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ s t =
      toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra 1 s t :=
  J.fockInnerProductCore_inner hQJ hQnd hQ b hb s t

/-- **Distinct exterior degrees are orthogonal** in the native Hermitian Fock module. -/
theorem inner_fock_eq_zero_of_mem_exteriorPower {p q : ℕ} (hpq : p ≠ q)
    {s t : S} (hs : s ∈ ⋀[ℂ]^p W) (ht : t ∈ ⋀[ℂ]^q W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ s t = 0 := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ]
  exact J.fockGramForm_eq_zero_of_mem_exteriorPower hQJ hQnd hpq hs ht

/-- **The Gram-determinant formula for the native Fock metric**: in every degree `p` (including
degree zero, where the empty determinant is `1`, and degrees above the rank), the native Fock
inner product of two decomposable wedges in `⋀ W` is the Gram determinant of the sesquilinear
complexification of the Euclidean inner product restricted to `W`. -/
theorem inner_fock_ιMulti_ιMulti (p : ℕ) (x y : Fin p → W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ (_root_.ExteriorAlgebra.ιMulti ℂ p x) (_root_.ExteriorAlgebra.ιMulti ℂ p y) =
      (Matrix.of fun i j ↦
        LinearMap.BilinForm.sesqComplexification (innerₗ V)
          (x i : ℂ ⊗[ℝ] V) (y j : ℂ ⊗[ℝ] V)).det := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ, fockGramForm_ιMulti]
  congr 1
  ext i j
  exact J.fockPolarForm_eq_sesqComplexification_innerₗ hQJ hQnd hQ (x i) (y j)

/-- In degree one, the native Fock inner product restricts to
`LinearMap.BilinForm.sesqComplexification (innerₗ V)` on `W`. -/
@[simp]
theorem inner_fock_ι_ι (x y : W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ (_root_.ExteriorAlgebra.ι ℂ x) (_root_.ExteriorAlgebra.ι ℂ y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ V) (x : ℂ ⊗[ℝ] V) y := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ, fockGramForm_ι_ι,
    J.fockPolarForm_eq_sesqComplexification_innerₗ hQJ hQnd hQ]

/-- The squared norm of a decomposable `p`-vector in the native Fock metric, cast to `ℂ`, is its
Gram determinant under `LinearMap.BilinForm.sesqComplexification (innerₗ V)`. -/
theorem norm_fock_ιMulti_sq (p : ℕ) (x : Fin p → W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    (‖_root_.ExteriorAlgebra.ιMulti ℂ p x‖ : ℂ) ^ 2 =
      (Matrix.of fun i j ↦
        LinearMap.BilinForm.sesqComplexification (innerₗ V) (x i : ℂ ⊗[ℝ] V) (x j)).det := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _).symm.trans
    (J.inner_fock_ιMulti_ιMulti hQJ hQnd hQ p x x)

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
    inner ℂ (1 : S) 1 = 1 := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ, J.fockGramForm_one_one hQJ hQnd]

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
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ, J.inner_fock_eq_fockGramForm hQJ hQnd hQ]
  simpa only [conjStar_conjStar] using
    J.fockGramForm_fockAction_left hQJ hQnd (conjStar Q a) s t

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

/-- The native Hermitian Fock module satisfies the geometric convention: `Q v = -‖v‖²`, and real
vectors act skew-Hermitianly. -/
theorem isGeometricClifford_realFockAction :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    (J.realFockAction hQJ hQnd).IsGeometricClifford := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  exact AlgHom.isGeometricClifford_iff_adjoint.mpr ⟨hQ, J.adjoint_realFockAction_ι hQJ hQnd hQ⟩

/-- For any nonzero real vector `v ≠ 0` in a Euclidean space `(V, J)` with `Q v = -‖v‖²`, the
unnormalized native action `spinAction (ι (1 ⊗ v))` is not skew-adjoint in
`fockInnerProductSpace`. -/
theorem adjoint_spinAction_ι_one_tmul_ne_neg {v : V} (hv : v ≠ 0) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    LinearMap.adjoint
        (spinAction _ (J.spinPolarizationData hQJ hQnd)
          (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v))) ≠
      -spinAction _ (J.spinPolarizationData hQJ hQnd)
        (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  have hQv : Q v ≠ 0 := by
    rw [hQ, neg_ne_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  intro hadj
  refine J.not_forall_fockGramForm_spinAction_ι_one_tmul_left hQJ hQnd hQv fun s t ↦ ?_
  rw [← J.inner_fock_eq_fockGramForm hQJ hQnd hQ, ← J.inner_fock_eq_fockGramForm hQJ hQnd hQ,
    ← LinearMap.adjoint_inner_right, hadj, LinearMap.neg_apply, inner_neg_right]

end TauCeti.AlmostComplexStructure
