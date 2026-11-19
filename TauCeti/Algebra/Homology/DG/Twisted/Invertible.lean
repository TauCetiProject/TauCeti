/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
import Mathlib.RingTheory.Nilpotent.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Invertible continuation cocycles

Let `(𝒜, d)` be a differential graded algebra and `ν` a continuation cocycle from a twisting
cocycle `mP` on `(P, ind)` to a twisting cocycle `mQ` on `(Q, indQ)`
(`TauCeti.ContinuationCocycle`). Its entries form a matrix `ν : P × Q → 𝒜`. This file shows that
when this matrix has a two-sided inverse `μ`, the inverse is again a continuation cocycle, from
`mQ` to `mP` (`TauCeti.ContinuationCocycle.inverse`). Its entries are automatically homogeneous
of the right degrees (`TauCeti.ContinuationCocycle.mem_graded_of_mul_eq_one`), and it satisfies
the continuation equation because, by the graded Leibniz rule applied to `ν μ = 1`,
`d μ = -(-1)^{|μ|} μ (d ν) μ`.

The two composites of `ν` and its inverse are the Kronecker cocycles on the nose, so `mP` and `mQ`
are homologous with vanishing parametrized cocycles (`TauCeti.ContinuationCocycle.homologous`),
and the continuation maps of `ν` and its inverse are mutually inverse isomorphisms of the twisted
complexes of every differential graded right module
(`TauCeti.ContinuationCocycle.continuationIso`): the twisted complexes are isomorphic, not merely
homotopy equivalent.

The main source of invertible continuation cocycles is unitriangularity. If `mP` and `mQ` live on
the same generators `(P, ind)` and `ν x y` is the Kronecker symbol whenever `ind x ≤ ind y`, then
`ν - 1` is strictly block triangular for the ranking by `ind`, hence nilpotent, and `ν` is a unit
(`TauCeti.ContinuationCocycle.isUnit_of_eq_one_of_le`). Over an algebra concentrated in
cohomological degrees `≤ 0`, such as the chains on a based loop space, the entries with
`ind x < ind y` vanish for degree reasons, so it suffices that `ν` is the Kronecker symbol on
pairs of equal index (`TauCeti.ContinuationCocycle.isUnit_of_nonpos`). This is the case of the
continuation cocycle `1 + q_* h` comparing two representing chain systems through a homotopy `h`
whose chains vanish on pairs of equal index.

## Main definitions

* `TauCeti.ContinuationCocycle.inverse ν μ`: the inverse continuation cocycle, for a two-sided
  inverse matrix `μ`.
* `TauCeti.ContinuationCocycle.homologous ν μ`: the resulting homology between `mP` and `mQ`.
* `TauCeti.ContinuationCocycle.continuationIso ν μ hM`: the isomorphism of twisted complexes.
* `TauCeti.ContinuationCocycle.continuationIsoOfIsUnit ν hν hM`: the same, for a continuation
  cocycle on one set of generators whose matrix is a unit.

## Main results

* `TauCeti.ContinuationCocycle.mem_graded_of_mul_eq_one`: a two-sided inverse of the matrix of a
  continuation cocycle has homogeneous entries of degrees `ind x - indQ y`.
* `TauCeti.ContinuationCocycle.comp_inverse`, `TauCeti.ContinuationCocycle.inverse_comp`: the
  composites with the inverse are the Kronecker cocycles.
* `TauCeti.ContinuationCocycle.isUnit_of_eq_one_of_le`: a unitriangular continuation cocycle is
  invertible.
* `TauCeti.ContinuationCocycle.isUnit_of_nonpos`: over a nonpositively graded algebra, it suffices
  that the cocycle is the Kronecker symbol on pairs of equal index.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–6.
-/

public section

open CategoryTheory DirectSum

namespace TauCeti

universe uR uA uM uP

/-! ### The inverse of a continuation cocycle -/

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}

namespace ContinuationCocycle

variable [DecidableEq P] [DecidableEq Q]

/-- **A two-sided inverse of a continuation cocycle is homogeneous**: if the matrix of
`ν : mP → mQ` has a two-sided inverse `μ`, then `μ y x` has degree `ind x - indQ y`. The
homogeneous components of `μ` of these degrees already form a right inverse of `ν`, so they are
`μ` itself. -/
theorem mem_graded_of_mul_eq_one (ν : ContinuationCocycle mP mQ) {μ : Matrix Q P A}
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) (y : Q) (x : P) :
    μ y x ∈ 𝒜 (ind x - indQ y) := by
  let μ' : Matrix Q P A := Matrix.of fun y x ↦ GradedRing.proj 𝒜 (ind x - indQ y) (μ y x)
  have hνμ' : Matrix.of ν.ν * μ' = 1 := by
    ext x x'
    -- Multiplying by the homogeneous `ν x y` shifts the component of `μ y x'` to degree
    -- `ind x' - ind x`, independently of `y`.
    have key : ∀ y, Matrix.of ν.ν x y * μ' y x' =
        GradedRing.proj 𝒜 (ind x' - ind x) (Matrix.of ν.ν x y * μ y x') := by
      intro y
      have := coe_decompose_mul_add_of_left_mem 𝒜 (j := ind x' - indQ y) (b := μ y x')
        (ν.mem_graded x y)
      rw [show indQ y - ind x + (ind x' - indQ y) = ind x' - ind x by ring] at this
      simp only [μ', Matrix.of_apply, GradedRing.proj_apply]
      exact this.symm
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun y _ ↦ key y, ← map_sum, ← Matrix.mul_apply,
      hνμ, Matrix.one_apply]
    split_ifs with hxx
    · rw [hxx, sub_self, GradedRing.proj_apply, decompose_of_mem_same _ (SetLike.one_mem_graded 𝒜)]
    · exact map_zero _
  have hμ : μ = μ' :=
    calc μ = μ * (Matrix.of ν.ν * μ') := by rw [hνμ', Matrix.mul_one]
      _ = μ * Matrix.of ν.ν * μ' := (Matrix.mul_assoc _ _ _).symm
      _ = μ' := by rw [hμν, Matrix.one_mul]
  rw [hμ]
  simp only [μ', Matrix.of_apply, GradedRing.proj_apply]
  exact SetLike.coe_mem _

/-- The continuation equation of a two-sided inverse `μ` of `ν : mP → mQ`, in matrix form:
`d μ = mQ μ - τ(μ) mP`. It follows from the graded Leibniz rule applied to `ν μ = 1`, which gives
`τ(ν) (d μ) = -(d ν) μ`, and from `τ(μ) τ(ν) = 1`. -/
private theorem map_eq_of_mul_eq_one (h : IsDGAlgebra 𝒜 d) (ν : ContinuationCocycle mP mQ)
    {μ : Matrix Q P A} (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) :
    μ.map d = Matrix.of mQ.m * μ - μ.signTwist indQ ind * Matrix.of mP.m := by
  set N : Matrix P Q A := Matrix.of ν.ν
  have hN : N.map d = Matrix.of mP.m * N - N.signTwist ind indQ * Matrix.of mQ.m :=
    (continuation_iff_map N (Matrix.of mP.m) (Matrix.of mQ.m)).1 ν.continuation
  have hσ : μ.signTwist indQ ind * N.signTwist ind indQ = 1 := by
    rw [← Matrix.signTwist_mul, hμν, Matrix.signTwist_one]
  have hdμ : N.signTwist ind indQ * μ.map d = -(N.map d * μ) := by
    refine eq_neg_of_add_eq_zero_right ?_
    rw [← h.map_mul_matrix_of_mem (F := N) ν.mem_graded, hνμ, h.map_one_matrix_eq_zero]
  calc μ.map d = μ.signTwist indQ ind * N.signTwist ind indQ * μ.map d := by
        rw [hσ, Matrix.one_mul]
    _ = μ.signTwist indQ ind * -(N.map d * μ) := by rw [Matrix.mul_assoc, hdμ]
    _ = μ.signTwist indQ ind * N.signTwist ind indQ * (Matrix.of mQ.m * μ) -
          μ.signTwist indQ ind * Matrix.of mP.m * (N * μ) := by
        rw [hN, Matrix.sub_mul, neg_sub, Matrix.mul_sub]
        simp only [Matrix.mul_assoc]
    _ = Matrix.of mQ.m * μ - μ.signTwist indQ ind * Matrix.of mP.m := by
        rw [hσ, hνμ, Matrix.one_mul, Matrix.mul_one]

/-- **The inverse of a continuation cocycle**: a two-sided inverse `μ` of the matrix of a
continuation cocycle `ν : mP → mQ` is a continuation cocycle `mQ → mP`. -/
def inverse (h : IsDGAlgebra 𝒜 d) (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) : ContinuationCocycle mQ mP where
  ν y x := μ y x
  mem_graded := ν.mem_graded_of_mul_eq_one hνμ hμν
  continuation := (continuation_iff_map μ (Matrix.of mQ.m) (Matrix.of mP.m)).2
    (map_eq_of_mul_eq_one h ν hνμ hμν)

@[simp]
theorem inverse_ν (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) :
    (ν.inverse h μ hνμ hμν).ν = μ :=
  (rfl)

/-- A continuation cocycle followed by its inverse is the Kronecker cocycle. -/
@[simp]
theorem comp_inverse (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) :
    ν.comp h (ν.inverse h μ hνμ hμν) = refl h.map_one_eq_zero mP := by
  ext x y
  rw [comp_ν, refl_ν, inverse_ν]
  exact congrFun (congrFun hνμ x) y

/-- The inverse of a continuation cocycle followed by the cocycle is the Kronecker cocycle. -/
@[simp]
theorem inverse_comp (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) :
    (ν.inverse h μ hνμ hμν).comp h ν = refl h.map_one_eq_zero mQ := by
  ext x y
  rw [comp_ν, refl_ν, inverse_ν]
  exact congrFun (congrFun hμν x) y

/-- **An invertible continuation cocycle makes its ends homologous**, with the inverse
continuation cocycle and vanishing parametrized cocycles: both composites are the Kronecker
cocycles. -/
def homologous (h : IsDGAlgebra 𝒜 d) (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) : Homologous h mP mQ where
  ν := ν
  ν' := ν.inverse h μ hνμ hμν
  homP := ParametrizedCocycle.ofEq (comp_inverse ν μ hνμ hμν).symm
  homQ := ParametrizedCocycle.ofEq (inverse_comp ν μ hνμ hμν).symm

@[simp]
theorem homologous_ν (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) :
    (ν.homologous h μ hνμ hμν).ν = ν :=
  (rfl)

@[simp]
theorem homologous_ν' (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) :
    (ν.homologous h μ hνμ hμν).ν' = ν.inverse h μ hνμ hμν :=
  (rfl)

/-- **The continuation isomorphism**: the continuation maps of an invertible continuation cocycle
and of its inverse are mutually inverse isomorphisms between the twisted complexes of a
differential graded right module. -/
noncomputable def continuationIso (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) (hM : IsDGRightModule h ℳ dM) :
    mP.twistedCochainComplex dM hM ≅ mQ.twistedCochainComplex dM hM where
  hom := ν.continuationHom hM
  inv := (ν.inverse h μ hνμ hμν).continuationHom hM
  hom_inv_id := by rw [← continuationHom_comp, comp_inverse, continuationHom_refl]
  inv_hom_id := by rw [← continuationHom_comp, inverse_comp, continuationHom_refl]

@[simp]
theorem continuationIso_hom (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) (hM : IsDGRightModule h ℳ dM) :
    (ν.continuationIso μ hνμ hμν hM).hom = ν.continuationHom hM :=
  (rfl)

@[simp]
theorem continuationIso_inv (ν : ContinuationCocycle mP mQ) (μ : Matrix Q P A)
    (hνμ : Matrix.of ν.ν * μ = 1) (hμν : μ * Matrix.of ν.ν = 1) (hM : IsDGRightModule h ℳ dM) :
    (ν.continuationIso μ hνμ hμν hM).inv = (ν.inverse h μ hνμ hμν).continuationHom hM :=
  (rfl)

/-! ### Unitriangular continuation cocycles -/

omit [GradedAlgebra 𝒜] in
/-- **A unitriangular continuation cocycle is invertible.** If `ν` is a continuation cocycle
between twisting cocycles on the same generators `(P, ind)` which is the Kronecker symbol on the
pairs `ind x ≤ ind y`, then `ν - 1` is strictly block triangular for the ranking by `ind`, hence
nilpotent, and `ν` is a unit. -/
theorem isUnit_of_eq_one_of_le {m₁ m₂ : TwistingCocycle 𝒜 d P ind}
    (ν : ContinuationCocycle m₁ m₂)
    (hν : ∀ x y, ind x ≤ ind y → ν.ν x y = (1 : Matrix P P A) x y) :
    IsUnit (Matrix.of ν.ν) := by
  have hN : IsNilpotent (Matrix.of ν.ν - 1) :=
    Matrix.isNilpotent_of_apply_eq_zero_of_le (b := fun x ↦ -ind x) fun x y hxy ↦ by
      rw [Matrix.sub_apply, Matrix.of_apply, hν x y (neg_le_neg_iff.1 hxy), sub_self]
  simpa using hN.isUnit_add_one

omit [GradedAlgebra 𝒜] in
/-- **A continuation cocycle over a nonpositively graded algebra is invertible when it is the
Kronecker symbol on the pairs of equal index.** Over an algebra concentrated in cohomological
degrees `≤ 0`, the entries `ν x y` with `ind x < ind y` vanish for degree reasons, so `ν` is
unitriangular. -/
theorem isUnit_of_nonpos {m₁ m₂ : TwistingCocycle 𝒜 d P ind} (ν : ContinuationCocycle m₁ m₂)
    (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥)
    (hν : ∀ x y, ind x = ind y → ν.ν x y = (1 : Matrix P P A) x y) :
    IsUnit (Matrix.of ν.ν) := by
  refine ν.isUnit_of_eq_one_of_le fun x y hxy ↦ hxy.lt_or_eq.elim (fun hlt ↦ ?_) (hν x y)
  rw [ν.ν_eq_zero_of_lt_of_nonpos h𝒜 hlt, Matrix.one_apply_ne fun hxy' ↦ (hxy' ▸ hlt).false]

/-- **The continuation isomorphism of a continuation cocycle whose matrix is a unit**, for
twisting cocycles on the same generators: the continuation maps of `ν` and of its inverse
matrix are mutually inverse isomorphisms of twisted complexes. -/
noncomputable def continuationIsoOfIsUnit {m₁ m₂ : TwistingCocycle 𝒜 d P ind}
    (ν : ContinuationCocycle m₁ m₂) (hν : IsUnit (Matrix.of ν.ν)) (hM : IsDGRightModule h ℳ dM) :
    m₁.twistedCochainComplex dM hM ≅ m₂.twistedCochainComplex dM hM :=
  ν.continuationIso ↑hν.unit⁻¹ hν.mul_val_inv hν.val_inv_mul hM

@[simp]
theorem continuationIsoOfIsUnit_hom {m₁ m₂ : TwistingCocycle 𝒜 d P ind}
    (ν : ContinuationCocycle m₁ m₂) (hν : IsUnit (Matrix.of ν.ν)) (hM : IsDGRightModule h ℳ dM) :
    (ν.continuationIsoOfIsUnit hν hM).hom = ν.continuationHom hM :=
  (rfl)

@[simp]
theorem continuationIsoOfIsUnit_inv {m₁ m₂ : TwistingCocycle 𝒜 d P ind}
    (ν : ContinuationCocycle m₁ m₂) (hν : IsUnit (Matrix.of ν.ν)) (hM : IsDGRightModule h ℳ dM) :
    (ν.continuationIsoOfIsUnit hν hM).inv =
      (ν.inverse h ↑hν.unit⁻¹ hν.mul_val_inv hν.val_inv_mul).continuationHom hM :=
  (rfl)

end ContinuationCocycle

end TauCeti
