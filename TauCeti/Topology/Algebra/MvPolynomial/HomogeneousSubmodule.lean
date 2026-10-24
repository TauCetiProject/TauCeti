/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.RingTheory.MvPolynomial.Jacobian
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# The coefficient space of homogeneous polynomials

Over a topological commutative semiring `R`, we give the homogeneous polynomials
`homogeneousSubmodule σ R n` of degree `n` the module topology: the finest topology making
addition and scalar multiplication continuous. For finitely many variables (`[Finite σ]`) they
form a finite free `R`-module, and this is the topology transported from the monomial
coordinates: the coefficient map `TauCeti.homogeneousCoeffEquiv n` is a continuous linear
equivalence with `R ^ S`, where `S` is the finite set of exponent vectors of degree `n`. Being
the module topology, it involves no choice of basis; over a complete field such as `ℂ` it is the
unique Hausdorff topological vector space topology on this finite-dimensional space.

A family of degrees `d : ι → ℕ` then gives the coefficient space
`∀ i, homogeneousSubmodule σ R (d i)` of families of homogeneous equations, with the product
topology; for a finite family (`[Finite ι]`) this is again the module topology. It
parametrizes families of homogeneous equations of fixed degrees, the zero equations included,
and so families of projective zero loci.
Arguments about such families, such as closedness of the incidence variety of pairs (equations,
common zero) or of the locus where the Jacobian drops rank, need evaluation and differentiation
to depend continuously on the coefficients and the point jointly.
This file provides those continuity statements; their analytic counterparts are in
`TauCeti.Analysis.MvPolynomial.HomogeneousSubmodule`.

## Main definitions

* `TauCeti.homogeneousCoeffEquiv n`: the monomial-coefficient equivalence of the degree-`n`
  homogeneous polynomials with `{s : σ →₀ ℕ // s.degree = n} → R`, as a continuous linear
  equivalence.
* `TauCeti.homogeneousPDeriv j n`: the partial derivative `∂/∂X_j`, from degree `n` to degree
  `n - 1`, as a continuous linear map.
* `TauCeti.homogeneousCoeffCLM n l`: the coefficient of the monomial with exponent vector `l`,
  as a continuous linear functional on the degree-`n` homogeneous polynomials.

## Main results

* `TauCeti.continuous_eval_homogeneousSubmodule`: evaluation `(p, v) ↦ p(v)` is jointly
  continuous.
* `TauCeti.continuous_jacobiMatrixAt_homogeneousSubmodule`: the Jacobian matrix of a family of
  homogeneous polynomials at a point depends continuously on the coefficients and the point
  jointly.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

variable [TopologicalSpace R]

/-- The homogeneous polynomials of degree `n` over a topological semiring carry the module
topology. -/
noncomputable instance instTopologicalSpaceHomogeneousSubmodule (n : ℕ) :
    TopologicalSpace (homogeneousSubmodule σ R n) :=
  moduleTopology R _

/-- The topology on a homogeneous component is, by definition, the module topology. -/
instance homogeneousSubmodule_isModuleTopology (n : ℕ) :
    IsModuleTopology R (homogeneousSubmodule σ R n) :=
  ⟨rfl⟩

instance homogeneousSubmodule_continuousAdd (n : ℕ) :
    ContinuousAdd (homogeneousSubmodule σ R n) :=
  IsModuleTopology.toContinuousAdd R _

instance homogeneousSubmodule_isTopologicalAddGroup {R : Type*} [CommRing R] [TopologicalSpace R]
    (n : ℕ) : IsTopologicalAddGroup (homogeneousSubmodule σ R n) :=
  IsModuleTopology.isTopologicalAddGroup R _

/-- The partial derivative `∂/∂X_j` lowers the degree of a homogeneous polynomial by one; as a map
of coefficient spaces it is continuous linear. -/
noncomputable def homogeneousPDeriv (j : σ) (n : ℕ) :
    homogeneousSubmodule σ R n →L[R] homogeneousSubmodule σ R (n - 1) where
  toLinearMap := (pderiv j).toLinearMap.restrict fun _ hp ↦ IsHomogeneous.pderiv hp
  cont := IsModuleTopology.continuous_of_linearMap _

@[simp]
theorem coe_homogeneousPDeriv_apply (j : σ) {n : ℕ} (p : homogeneousSubmodule σ R n) :
    (homogeneousPDeriv j n p : MvPolynomial σ R) = pderiv j (p : MvPolynomial σ R) :=
  (rfl)

variable [IsTopologicalSemiring R]

/-- The coefficient of the monomial with exponent vector `l`, as a continuous linear functional on
the homogeneous polynomials of degree `n`. -/
noncomputable def homogeneousCoeffCLM (n : ℕ) (l : σ →₀ ℕ) :
    homogeneousSubmodule σ R n →L[R] R where
  toLinearMap := (lcoeff R l).comp (homogeneousSubmodule σ R n).subtype
  cont := IsModuleTopology.continuous_of_linearMap _

@[simp]
theorem homogeneousCoeffCLM_apply {n : ℕ} (l : σ →₀ ℕ) (p : homogeneousSubmodule σ R n) :
    homogeneousCoeffCLM n l p = (p : MvPolynomial σ R).coeff l :=
  (rfl)

/-- The **monomial-coefficient equivalence**: a homogeneous polynomial of degree `n` in finitely
many variables is determined by its coefficients on the exponent vectors of degree `n`, and this
identification is a homeomorphism for the module topology. -/
noncomputable def homogeneousCoeffEquiv [Finite σ] (n : ℕ) :
    homogeneousSubmodule σ R n ≃L[R] ({s : σ →₀ ℕ // s.degree = n} → R) :=
  { (homogeneousMonomialBasis n).equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap _
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (homogeneousMonomialBasis n).equivFun.symm.toLinearMap }

/-- The underlying linear equivalence of `homogeneousCoeffEquiv n` is the coordinate equivalence
of the monomial basis. -/
theorem homogeneousCoeffEquiv_toLinearEquiv [Finite σ] (n : ℕ) :
    (homogeneousCoeffEquiv (σ := σ) (R := R) n).toLinearEquiv =
      (homogeneousMonomialBasis n).equivFun :=
  (rfl)

@[simp]
theorem homogeneousCoeffEquiv_apply [Finite σ] {n : ℕ} (p : homogeneousSubmodule σ R n)
    (s : {s : σ →₀ ℕ // s.degree = n}) :
    homogeneousCoeffEquiv n p s = (p : MvPolynomial σ R).coeff s := by
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv, homogeneousCoeffEquiv_toLinearEquiv,
    Module.Basis.equivFun_apply, homogeneousMonomialBasis_repr_apply]

@[simp]
theorem coe_homogeneousCoeffEquiv_symm_apply [Fintype σ] [DecidableEq σ] {n : ℕ}
    (a : {s : σ →₀ ℕ // s.degree = n} → R) :
    ((homogeneousCoeffEquiv n).symm a : MvPolynomial σ R) = ∑ s, monomial s.1 (a s) := by
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv, homogeneousCoeffEquiv_toLinearEquiv]
  simp [Module.Basis.equivFun_symm_apply, smul_monomial]

/-- Over a Hausdorff topological semiring, the coefficient space of homogeneous polynomials in
finitely many variables is Hausdorff. -/
instance homogeneousSubmodule_t2Space [Finite σ] [T2Space R] (n : ℕ) :
    T2Space (homogeneousSubmodule σ R n) :=
  (homogeneousCoeffEquiv n).toHomeomorph.isEmbedding.t2Space

/-- **Evaluation is jointly continuous** on the homogeneous polynomials of degree `n` in finitely
many variables: `(p, v) ↦ p(v)` is continuous in the coefficients and the point together. -/
theorem continuous_eval_homogeneousSubmodule [Finite σ] (n : ℕ) :
    Continuous fun q : homogeneousSubmodule σ R n × (σ → R) ↦
      eval q.2 (q.1 : MvPolynomial σ R) := by
  classical
  cases nonempty_fintype σ
  simp only [eval_coe_homogeneousSubmodule_eq_sum, ← homogeneousCoeffCLM_apply]
  exact continuous_finsetSum _ fun l _ ↦
    ((homogeneousCoeffCLM n l).continuous.comp continuous_fst).mul (by fun_prop)

/-- The partial derivative `∂p/∂X_j (v)` of a homogeneous polynomial is jointly continuous in the
coefficients of `p` and the point `v`. -/
theorem continuous_eval_pderiv_homogeneousSubmodule [Finite σ] (j : σ) (n : ℕ) :
    Continuous fun q : homogeneousSubmodule σ R n × (σ → R) ↦
      eval q.2 (pderiv j (q.1 : MvPolynomial σ R)) := by
  have h := (continuous_eval_homogeneousSubmodule (R := R) (n - 1)).comp
    (((homogeneousPDeriv j n).continuous.comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def, coe_homogeneousPDeriv_apply] using h

/-- The **Jacobian matrix of a family of homogeneous equations** at a point is jointly continuous
in the coefficients of the family and the point. -/
theorem continuous_jacobiMatrixAt_homogeneousSubmodule {ι : Type*} [Finite σ] (d : ι → ℕ) :
    Continuous fun q : (∀ i, homogeneousSubmodule σ R (d i)) × (σ → R) ↦
      jacobiMatrixAt (fun i ↦ (q.1 i : MvPolynomial σ R)) q.2 :=
  continuous_matrix fun i j ↦ by
    have h := (continuous_eval_pderiv_homogeneousSubmodule (R := R) j (d i)).comp
      (((continuous_apply i).comp continuous_fst).prodMk
        (continuous_snd : Continuous fun q : (∀ i, homogeneousSubmodule σ R (d i)) × (σ → R) ↦ q.2))
    simpa only [Function.comp_def, jacobiMatrixAt_apply] using h

end TauCeti
