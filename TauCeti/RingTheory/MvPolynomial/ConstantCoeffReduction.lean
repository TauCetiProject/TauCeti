/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.LinearAlgebra.Finsupp.LSum
public import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Constant coefficient reduction of maps between free polynomial modules

Setting every variable to zero reduces a linear map between free modules over `MvPolynomial σ R`
to an `R`-linear map. This file constructs that reduction over a commutative semiring and records
its compatibility with composition and linear operations.

For inputs in the `k`-th power of the ideal of variables, the coefficients of total degree `k`
are computed by the reduced map (`LinearMap.coeff_apply_of_mem_pow_idealOfVars`). For a weighted
homogeneous map, reduction respects the induced degrees on generators and commutes with filtering
by a set of degrees (`LinearMap.filter_constantCoeffReduction_apply`). These facts provide the
polynomial input to graded exactness arguments.
-/

public section

open Finsupp MvPolynomial

namespace LinearMap

variable {R σ ι κ : Type*}

section Reduction

variable [CommSemiring R] {μ : Type*}

/-- If `f₀` and `g₀` are the reductions of `f` and `g` modulo the variables, then `g₀ ∘ f₀` is the
reduction of `g ∘ f`. -/
theorem comp_apply_mapRange_constantCoeff
    (g : (κ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (μ →₀ MvPolynomial σ R))
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    {f₀ : (ι →₀ R) →ₗ[R] (κ →₀ R)} {g₀ : (κ →₀ R) →ₗ[R] (μ →₀ R)}
    (hf₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _))
    (hg₀ : ∀ x, g₀ (x.mapRange constantCoeff (map_zero _)) =
      (g x).mapRange constantCoeff (map_zero _)) (x : ι →₀ MvPolynomial σ R) :
    (g₀ ∘ₗ f₀) (x.mapRange constantCoeff (map_zero _)) =
      ((g ∘ₗ f) x).mapRange constantCoeff (map_zero _) := by
  rw [comp_apply, hf₀, hg₀, comp_apply]

/-- A reduction modulo the variables is determined by the map it reduces: reductions `f₀` of `f`
and `f₀'` of `f'` agree when `f = f'`. -/
theorem eq_of_mapRange_constantCoeff (f₀ f₀' : (ι →₀ R) →ₗ[R] (κ →₀ R))
    {f f' : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)}
    (hf₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _))
    (hf₀' : ∀ x, f₀' (x.mapRange constantCoeff (map_zero _)) =
      (f' x).mapRange constantCoeff (map_zero _)) (h : f = f') :
    f₀ = f₀' := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero _)
    (fun c ↦ ⟨C c, constantCoeff_C σ c⟩) x
  rw [hf₀, hf₀', h]

/-- The reduction of an `S`-linear map `f : (ι →₀ S) → (κ →₀ S)` modulo the variables, for
`S = R[V_v : v ∈ σ]`: the `R`-linear map `(ι →₀ R) → (κ →₀ R)` whose matrix coefficients are the
constant coefficients of those of `f`. It commutes with taking constant coefficients
(`LinearMap.constantCoeffReduction_mapRange_constantCoeff`). -/
noncomputable def constantCoeffReduction
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) :
    (ι →₀ R) →ₗ[R] (κ →₀ R) :=
  Finsupp.linearCombination R fun i ↦
    (f (Finsupp.single i 1)).mapRange constantCoeff (map_zero _)

/-- The matrix coefficients of the reduction of `f` modulo the variables are the constant
coefficients of those of `f`. -/
@[simp]
theorem constantCoeffReduction_single_apply
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) (i : ι) (c : R)
    (j : κ) :
    f.constantCoeffReduction (Finsupp.single i c) j =
      c * constantCoeff (f (Finsupp.single i 1) j) := by
  simp [constantCoeffReduction]

/-- **The reduction commutes with setting the variables to zero.** Applying
`constantCoeffReduction f` to the constant coefficients of `x` gives the constant coefficients of
`f x`. -/
@[simp]
theorem constantCoeffReduction_mapRange_constantCoeff
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    (x : ι →₀ MvPolynomial σ R) :
    f.constantCoeffReduction (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add _), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add _)]
  | single i p =>
    ext j
    rw [Finsupp.mapRange_single, constantCoeffReduction_single_apply, Finsupp.mapRange_apply,
      ← Finsupp.smul_single_one i p, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]

/-- The reduction of a composite is the composite of the reductions. -/
@[simp]
theorem constantCoeffReduction_comp
    (g : (κ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (μ →₀ MvPolynomial σ R))
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) :
    (g ∘ₗ f).constantCoeffReduction = g.constantCoeffReduction ∘ₗ f.constantCoeffReduction :=
  eq_of_mapRange_constantCoeff _ _ (constantCoeffReduction_mapRange_constantCoeff _)
    (comp_apply_mapRange_constantCoeff g f (constantCoeffReduction_mapRange_constantCoeff f)
      (constantCoeffReduction_mapRange_constantCoeff g)) rfl

/-- The identity map reduces to the identity map. -/
@[simp]
theorem constantCoeffReduction_id :
    (LinearMap.id : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (ι →₀ MvPolynomial σ R)).constantCoeffReduction = LinearMap.id := by
  exact eq_of_mapRange_constantCoeff _ _
    (constantCoeffReduction_mapRange_constantCoeff _) (fun _ ↦ rfl) rfl

/-- Reduction commutes with addition of linear maps. -/
@[simp]
theorem constantCoeffReduction_add
    (f g : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (f + g).constantCoeffReduction = f.constantCoeffReduction + g.constantCoeffReduction := by
  ext i c
  simp [mul_add]

/-- Reduction commutes with scalar multiplication of linear maps. -/
@[simp]
theorem constantCoeffReduction_smul (p : MvPolynomial σ R)
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (p • f).constantCoeffReduction = constantCoeff p • f.constantCoeffReduction := by
  ext i c
  simp [constantCoeffReduction_single_apply]

/-- The reduction of the zero map is zero. -/
@[simp]
theorem constantCoeffReduction_zero :
    constantCoeffReduction
      (0 : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) = 0 := by
  ext i c
  simp

end Reduction

section ReductionRing

variable [CommRing R]

/-- Reduction commutes with negation of linear maps. -/
@[simp]
theorem constantCoeffReduction_neg
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (-f).constantCoeffReduction = -f.constantCoeffReduction := by
  ext i c
  simp

/-- Reduction commutes with subtraction of linear maps. -/
@[simp]
theorem constantCoeffReduction_sub
    (f g : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (f - g).constantCoeffReduction = f.constantCoeffReduction - g.constantCoeffReduction := by
  ext i c
  simp [mul_sub]

end ReductionRing

section Coefficients

variable [CommSemiring R]

/-- On `J ^ k • (ι →₀ S)`, the coefficients of `f` in total degree `k` are computed by the
canonical reduction of `f` modulo the variables. -/
theorem coeff_apply_of_mem_pow_idealOfVars
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    {k : ℕ} {z : ι →₀ MvPolynomial σ R} (hz : ∀ i, z i ∈ idealOfVars σ R ^ k)
    {e : σ →₀ ℕ} (he : degree e = k) (j : κ) :
    (f z j).coeff e = f.constantCoeffReduction (z.mapRange (lcoeff R e) (map_zero _)) j := by
  rw [apply_apply_eq_finsuppSum_mul, apply_apply_eq_finsuppSum_mul,
    Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, coeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_mul_of_mem_pow_idealOfVars _ (hz i) _ he.le,
    constantCoeffReduction_single_apply, one_mul, lcoeff_apply]

end Coefficients

section Degrees

variable [CommSemiring R] {w : σ → ℤ} {g : ι → ℤ} {g' : κ → ℤ} {r : ℤ}

/-- The reduction of `f` moves the source generator degree `g` to the target degree `g'` by `r`. -/
theorem degree_eq_of_constantCoeffReduction_single_apply_ne_zero
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    (hhom : ∀ i j, IsWeightedHomogeneous w (f (Finsupp.single i 1) j) (g i + r - g' j))
    {i : ι} {j : κ} {c : R}
    (h : f.constantCoeffReduction (Finsupp.single i c) j ≠ 0) : g' j = g i + r := by
  rw [constantCoeffReduction_single_apply, constantCoeff_eq] at h
  have := hhom i j (right_ne_zero_of_mul h)
  rw [map_zero] at this
  omega

/-- The reduction of `f` commutes with restricting to generators in a set of degrees, up to the
shift by `r`. -/
theorem filter_constantCoeffReduction_apply
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    (hhom : ∀ i j, IsWeightedHomogeneous w (f (Finsupp.single i 1) j) (g i + r - g' j))
    (P : ℤ → Prop) [DecidablePred P] (u : ι →₀ R) :
    (f.constantCoeffReduction u).filter (fun j ↦ P (g' j)) =
      f.constantCoeffReduction (u.filter fun i ↦ P (g i + r)) := by
  induction u using Finsupp.induction_linear with
  | zero => rw [filter_zero, map_zero, filter_zero]
  | add u v hu hv => rw [map_add, filter_add, hu, hv, filter_add, map_add]
  | single i c =>
    by_cases hP : P (g i + r)
    · rw [filter_single_of_pos (p := fun i ↦ P (g i + r)) hP, filter_eq_self_iff]
      intro j hj
      rwa [degree_eq_of_constantCoeffReduction_single_apply_ne_zero f hhom hj]
    · rw [filter_single_of_neg (p := fun i ↦ P (g i + r)) hP, map_zero, filter_eq_zero_iff]
      intro j hj
      by_contra h
      exact hP (degree_eq_of_constantCoeffReduction_single_apply_ne_zero f hhom h ▸ hj)

end Degrees

end LinearMap
