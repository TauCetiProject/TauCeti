/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Data.Set.Card

/-!
# The weight model of a torus action at a fixed point

Let `ι` be a finite index set and let `α : ι → StrongDual ℝ 𝔱` be a family of weights on a real
normed space `𝔱` (the Lie algebra of a torus). On `ℂ^ι`, written in real coordinates
`z_i = q_i + i p_i` as `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` with the standard symplectic form
`ω = Σ dq_i ∧ dp_i`, the weights determine the linear action of `𝔱`

`ξ • z = (exp(i α_i(ξ)) z_i)_i`,

and its moment map

`μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i`.

This is the local model of a Hamiltonian torus action near a fixed point: by the equivariant
Darboux theorem, such an action is isomorphic near the fixed point to this model, with `α_i` the
weights of the isotropy representation, and the moment map is the model one up to the constant
value at the fixed point.

This file develops the model. The rotation `TauCeti.weightRotation θ` by angles `θ : ι → ℝ` is a
linear symplectomorphism, additive in `θ`, preserving `μ`; the action of `ξ` is the rotation by
the angles `α_i(ξ)`. Its generator `TauCeti.weightGenerator θ` is the velocity of the rotation, and
the Hamiltonian vector field of the component `μ^ξ = ⟨μ, ξ⟩` is the generator for the angles
`α_i(ξ)`, so `μ` is a moment map for the action and `t ↦ (t ξ) • z` is the integral curve of the
Hamiltonian vector field of `μ^ξ` through `z`. With the sign convention `ι_{X_H} ω = dH`, the
field of `-½ a (q² + p²)` is `a (-p ∂_q + q ∂_p)`, the generator of `z ↦ exp(i a t) z`; this fixes
the minus sign in `μ`.

The local invariants of the model are explicit:

* the image of `μ` is the cone `-cone{α_i}` spanned by the negated weights;
* the rotation by `θ` fixes `z` exactly when `θ_i ∈ 2πℤ` for every `i` with `z_i ≠ 0`, and the
  generator of `θ` vanishes at `z` exactly when `θ_i = 0` for those `i`;
* the image of the derivative of `μ` at `z` is the span of the weights `α_i` with `z_i ≠ 0`, and
  the orbit through `z` has dimension the rank of these weights.

Globally, the rotation by `θ` is the identity exactly when every `θ_i` lies in `2πℤ`, the full
torus `(ℝ / 2πℤ)^ι` moves `z` to `w` exactly when `|z_i| = |w_i|` for every `i`, and a point is
fixed by all of `𝔱` exactly when it vanishes along the nonzero weights. When the weights are
linearly independent:

* the moment map determines the moduli `|z_i|`, so every fibre of `μ` is a single orbit of `𝔱`;
* the only fixed point is the origin, the only point mapped to the apex `0` of the moment cone;
* the apex is an extreme point of the moment image.

Some such hypothesis is needed for the apex to be a vertex: finitely many dependent weights can
span a cone containing a line, so that `0` is not an extreme point of the image, or even all of
`𝔱*`, so that `0` is an interior point.

## Main definitions

* `TauCeti.weightRotation θ`: the rotation `z_i ↦ exp(i θ_i) z_i`.
* `TauCeti.weightGenerator θ`: its infinitesimal generator `z_i ↦ i θ_i z_i`.
* `TauCeti.weightMomentMap α`: the moment map `μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i`.
* `TauCeti.weightModelCoords`: the real coordinates `(q_i)_i ⊔ (p_i)_i` of `ℂ^ι`, indexed by
  `ι ⊕ ι`.
* `TauCeti.weightInfinitesimalAction α z`: the infinitesimal action `ξ ↦ ξ_M(z)` at `z`.

## Main results

* `TauCeti.stdSymplecticForm_weightRotation`: rotations are symplectic.
* `TauCeti.weightRotation_add`, `TauCeti.weightRotation_zero`: rotations form an action of the
  additive group `ι → ℝ`.
* `TauCeti.weightMomentMap_weightRotation`: `μ` is invariant under every rotation.
* `TauCeti.hamiltonianVectorField_weightMomentMap`: the Hamiltonian vector field of `μ^ξ` is the
  generator for the angles `α_i(ξ)`.
* `TauCeti.fderiv_weightMomentMap_apply_eq_zero_iff`: the critical points of `μ^ξ` are the zeros
  of the generator for the angles `α_i(ξ)`.
* `TauCeti.hasDerivAt_weightRotation_hamiltonianVectorField`: `t ↦ (t ξ) • z` is the integral
  curve of the Hamiltonian vector field of `μ^ξ` through `z`.
* `TauCeti.range_weightMomentMap`: the image of `μ` is the cone spanned by the `-α_i`.
* `TauCeti.weightRotation_apply_eq_self_iff`, `TauCeti.weightGenerator_apply_eq_zero_iff`: the
  stabilizer and the infinitesimal stabilizer of a point.
* `TauCeti.mem_ker_weightGenerator_iff`, `TauCeti.finrank_ker_weightGenerator`: the kernel of the
  generator of `θ` is the subspace of `z` with `z_i = 0` whenever `θ_i ≠ 0`, of dimension twice
  the number of `i` with `θ_i = 0`.
* `TauCeti.range_fderiv_weightMomentMap`: the image of `dμ_z` is the span of the weights `α_i`
  with `z_i ≠ 0`.
* `TauCeti.finrank_range_weightInfinitesimalAction`: the orbit through `z` has dimension the rank
  of the weights `α_i` with `z_i ≠ 0`.
* `TauCeti.weightRotation_eq_id_iff`: the kernel of the rotation action.
* `TauCeti.exists_weightRotation_apply_eq_iff`: the orbits of the full rotation torus.
* `TauCeti.forall_weightRotation_apply_eq_self_iff`: the fixed points of the action of `𝔱`.
* `TauCeti.weightMomentMap_eq_weightMomentMap_iff_exists_weightRotation`: for linearly independent
  weights, the fibres of the moment map are orbits of `𝔱`.
* `TauCeti.forall_weightRotation_apply_eq_self_iff_weightMomentMap_eq_zero`,
  `TauCeti.zero_mem_extremePoints_range_weightMomentMap`: for linearly independent weights, the
  fixed points are the preimage of the apex, which is an extreme point of the image.

## References

* Victor Guillemin and Shlomo Sternberg, *Convexity properties of the moment mapping*, Invent.
  Math. 67 (1982), Section 2.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Sections 22 and 27–29.
-/

public section

noncomputable section

namespace TauCeti

open Real

variable {ι : Type*} [Fintype ι]

/-- The rotation `z_i ↦ exp(i θ_i) z_i` of `ℂ^ι`, written in the real coordinates
`z_i = q_i + i p_i` of `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`. -/
def weightRotation (θ : ι → ℝ) :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ (WithLp.toLp 2 fun i ↦ cos (θ i) * x.1 i - sin (θ i) * x.2 i,
        WithLp.toLp 2 fun i ↦ sin (θ i) * x.1 i + cos (θ i) * x.2 i)
      map_add' := fun x y ↦ by ext i <;> simp <;> ring
      map_smul' := fun c x ↦ by ext i <;> simp <;> ring }

@[simp]
theorem weightRotation_apply_fst (θ : ι → ℝ) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : ι) : (weightRotation θ x).1 i = cos (θ i) * x.1 i - sin (θ i) * x.2 i :=
  (rfl)

@[simp]
theorem weightRotation_apply_snd (θ : ι → ℝ) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : ι) : (weightRotation θ x).2 i = sin (θ i) * x.1 i + cos (θ i) * x.2 i :=
  (rfl)

/-- The infinitesimal rotation `z_i ↦ i θ_i z_i` of `ℂ^ι`, that is `(q, p) ↦ (-θ p, θ q)`
coordinatewise: the velocity of `t ↦ weightRotation (t • θ)` at `t = 0`. -/
def weightGenerator (θ : ι → ℝ) :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ (WithLp.toLp 2 fun i ↦ -(θ i * x.2 i), WithLp.toLp 2 fun i ↦ θ i * x.1 i)
      map_add' := fun x y ↦ by ext i <;> simp <;> ring
      map_smul' := fun c x ↦ by ext i <;> simp <;> ring }

@[simp]
theorem weightGenerator_apply_fst (θ : ι → ℝ) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : ι) : (weightGenerator θ x).1 i = -(θ i * x.2 i) :=
  (rfl)

@[simp]
theorem weightGenerator_apply_snd (θ : ι → ℝ) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : ι) : (weightGenerator θ x).2 i = θ i * x.1 i :=
  (rfl)

@[simp]
theorem weightRotation_zero : weightRotation (0 : ι → ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext x i <;> simp

/-- Rotations compose by adding angles. -/
theorem weightRotation_add (θ θ' : ι → ℝ) :
    weightRotation (θ + θ') = (weightRotation θ).comp (weightRotation θ') := by
  ext x i <;> simp [cos_add, sin_add] <;> ring

/-- Rotations preserve the standard symplectic form. -/
theorem stdSymplecticForm_weightRotation (θ : ι → ℝ)
    (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    stdSymplecticForm (weightRotation θ x) (weightRotation θ y) = stdSymplecticForm x y := by
  simp only [stdSymplecticForm_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    weightRotation_apply_fst, weightRotation_apply_snd, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  linear_combination (y.2 i * x.1 i - y.1 i * x.2 i) * sin_sq_add_cos_sq (θ i)

/-- The velocity of the rotation by the angles `t • θ` is the generator of `θ`. -/
theorem hasDerivAt_weightRotation_smul (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ weightRotation (s • θ) x)
      (weightGenerator θ (weightRotation (t • θ) x)) t := by
  have h (f : ℝ → ι → ℝ) (f' : ι → ℝ) (hf : ∀ i, HasDerivAt (fun s ↦ f s i) (f' i) t) :
      HasDerivAt (fun s ↦ (WithLp.toLp 2 (f s) : EuclideanSpace ℝ ι)) (WithLp.toLp 2 f') t :=
    (PiLp.hasFDerivAt_toLp 2 (f t)).comp_hasDerivAt t (hasDerivAt_pi.2 hf)
  have hc (i : ι) : HasDerivAt (fun s ↦ cos (s * θ i)) (-sin (t * θ i) * θ i) t := by
    simpa using ((hasDerivAt_id t).mul_const (θ i)).cos
  have hs (i : ι) : HasDerivAt (fun s ↦ sin (s * θ i)) (cos (t * θ i) * θ i) t := by
    simpa using ((hasDerivAt_id t).mul_const (θ i)).sin
  convert (h _ _ fun i ↦ ((hc i).mul_const (x.1 i)).sub ((hs i).mul_const (x.2 i))).prodMk
    (h _ _ fun i ↦ ((hs i).mul_const (x.1 i)).add ((hc i).mul_const (x.2 i))) using 1
  · funext s
    ext i <;> simp
  · ext i <;> simp <;> ring

variable {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

/-- The moment map `μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i` of the action of `𝔱` on `ℂ^ι` with
weights `α`, in the real coordinates `z_i = q_i + i p_i`. -/
def weightMomentMap (α : ι → StrongDual ℝ 𝔱) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    StrongDual ℝ 𝔱 :=
  ∑ i, (-(1 / 2) * (x.1 i ^ 2 + x.2 i ^ 2)) • α i

theorem weightMomentMap_def (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α x = ∑ i, (-(1 / 2) * (x.1 i ^ 2 + x.2 i ^ 2)) • α i :=
  (rfl)

@[simp]
theorem weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (ξ : 𝔱) :
    weightMomentMap α x ξ = -(1 / 2) * ∑ i, α i ξ * (x.1 i ^ 2 + x.2 i ^ 2) := by
  rw [weightMomentMap_def, _root_.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by simp; ring

@[simp]
theorem weightMomentMap_zero (α : ι → StrongDual ℝ 𝔱) : weightMomentMap α 0 = 0 := by
  simp [weightMomentMap]

/-- The moment map is invariant under every rotation. -/
@[simp]
theorem weightMomentMap_weightRotation (α : ι → StrongDual ℝ 𝔱) (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α (weightRotation θ x) = weightMomentMap α x := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  simp only [weightRotation_apply_fst, weightRotation_apply_snd]
  linear_combination (x.1 i ^ 2 + x.2 i ^ 2) * sin_sq_add_cos_sq (θ i)

/-- The derivative of the moment map at `(q, p)`:
`(δq, δp) ↦ -Σ_i (q_i δq_i + p_i δp_i) α_i`. -/
theorem hasFDerivAt_weightMomentMap (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    HasFDerivAt (weightMomentMap α)
      (∑ i, ContinuousLinearMap.smulRight
        (-(x.1 i • (PiLp.proj 2 (fun _ ↦ ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _) +
          x.2 i • (PiLp.proj 2 (fun _ ↦ ℝ) i).comp (ContinuousLinearMap.snd ℝ _ _))) (α i))
      x := by
  rw [show weightMomentMap α = fun y ↦ ∑ i, (-(1 / 2) * (y.1 i ^ 2 + y.2 i ^ 2)) • α i from
    funext (weightMomentMap_def α)]
  refine HasFDerivAt.fun_sum fun i _ ↦ ?_
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ y.1 i)
      ((PiLp.proj 2 (fun _ ↦ ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x.1 i).comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ y.2 i)
      ((PiLp.proj 2 (fun _ ↦ ℝ) i).comp (ContinuousLinearMap.snd ℝ _ _)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x.2 i).comp x (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  refine ((((h1.pow 2).add (h2.pow 2)).const_mul (-(1 / 2) : ℝ)).smul_const
    (α i)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun ξ ↦ ?_
  simp only [one_div, Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_add,
    neg_smul, ContinuousLinearMap.smulRight_apply, add_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', PiLp.proj_apply, smul_eq_mul,
    ContinuousLinearMap.coe_snd']
  ring

/-- The derivative of the component `μ^ξ = ⟨μ, ξ⟩` of the moment map, in the form of Hamilton's
equations: its partial gradients at `(q, p)` are `-α(ξ) q` and `-α(ξ) p`, coordinatewise. -/
theorem hasFDerivAt_weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y ↦ weightMomentMap α y ξ)
      ((innerSL ℝ (WithLp.toLp 2 fun i ↦ -(α i ξ * x.1 i) : EuclideanSpace ℝ ι)).coprod
        (innerSL ℝ (WithLp.toLp 2 fun i ↦ -(α i ξ * x.2 i) : EuclideanSpace ℝ ι))) x := by
  refine ((ContinuousLinearMap.apply ℝ ℝ ξ).hasFDerivAt.comp x
    (hasFDerivAt_weightMomentMap α x)).congr_fderiv ?_
  ext v <;> simp [PiLp.inner_apply, mul_comm, mul_assoc]

/-- **The weight model is Hamiltonian.** The Hamiltonian vector field of the component
`μ^ξ = ⟨μ, ξ⟩` of the moment map is the generator of the rotation by the angles `α_i(ξ)`. -/
theorem hamiltonianVectorField_weightMomentMap (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    stdSymplecticForm.hamiltonianVectorField (fun y ↦ weightMomentMap α y ξ) x =
      weightGenerator (fun i ↦ α i ξ) x := by
  rw [stdSymplecticForm_hamiltonianVectorField (hasFDerivAt_weightMomentMap_apply α ξ x)]
  ext i <;> simp

/-- **Critical points of a component of the moment map.** A point is critical for `μ^ξ` exactly
when the generator `ξ_M`, the rotation generator for the angles `α_i(ξ)`, vanishes there. -/
theorem fderiv_weightMomentMap_apply_eq_zero_iff (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y ↦ weightMomentMap α y ξ) x = 0 ↔ weightGenerator (fun i ↦ α i ξ) x = 0 := by
  rw [← SymplecticForm.hamiltonianVectorField_eq_zero_iff stdSymplecticForm,
    hamiltonianVectorField_weightMomentMap]

/-- The curve `t ↦ (t ξ) • z` is the integral curve of the Hamiltonian vector field of `μ^ξ`
through `z`. -/
theorem hasDerivAt_weightRotation_hamiltonianVectorField (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ weightRotation (fun i ↦ α i (s • ξ)) x)
      (stdSymplecticForm.hamiltonianVectorField (fun y ↦ weightMomentMap α y ξ)
        (weightRotation (fun i ↦ α i (t • ξ)) x)) t := by
  simp only [map_smul, hamiltonianVectorField_weightMomentMap]
  exact hasDerivAt_weightRotation_smul (fun i ↦ α i ξ) x t

/-- **The local moment cone.** The image of the moment map is the convex cone spanned by the
negated weights `-α_i`. -/
theorem range_weightMomentMap (α : ι → StrongDual ℝ 𝔱) :
    Set.range (weightMomentMap α) = (PointedCone.hull ℝ (Set.range (-α)) : Set _) := by
  ext ν
  rw [SetLike.mem_coe, PointedCone.hull, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun i ↦ ⟨(1 / 2) * (x.1 i ^ 2 + x.2 i ^ 2), by positivity⟩, ?_⟩
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Nonneg.mk_smul, Pi.neg_apply, smul_neg, neg_mul]
    exact (neg_smul (1 / 2 * (x.1 i ^ 2 + x.2 i ^ 2)) (α i)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨(WithLp.toLp 2 fun i ↦ √(2 * c i), 0), Finset.sum_congr rfl fun i _ ↦ ?_⟩
    have h : √(2 * (c i : ℝ)) ^ 2 = 2 * c i := Real.sq_sqrt (mul_nonneg zero_le_two (c i).2)
    rw [← Nonneg.coe_smul, Pi.neg_apply, smul_neg, ← neg_smul]
    congr 1
    simp only [PiLp.zero_apply, h]
    ring

/-- **Stabilizers in the weight model.** The rotation by `θ` fixes `z` exactly when `θ_i ∈ 2πℤ`
for every coordinate `z_i = q_i + i p_i` that is nonzero. -/
theorem weightRotation_apply_eq_self_iff (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation θ x = x ↔ ∀ i, (x.1 i ≠ 0 ∨ x.2 i ≠ 0) → ∃ k : ℤ, k * (2 * π) = θ i := by
  -- A coordinate `q + i p` is fixed by the rotation by `a` exactly when it vanishes or `a ∈ 2πℤ`.
  have hrot (a q p : ℝ) : (cos a * q - sin a * p = q ∧ sin a * q + cos a * p = p) ↔
      (q = 0 ∧ p = 0) ∨ ∃ k : ℤ, k * (2 * π) = a := by
    rw [← cos_eq_one_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hqp : q = 0 ∧ p = 0
      · exact Or.inl hqp
      refine Or.inr ?_
      have hpos : 0 < q ^ 2 + p ^ 2 := by
        rcases not_and_or.mp hqp with hq | hp
        · positivity
        · positivity
      have h : (cos a - 1) * (q ^ 2 + p ^ 2) = 0 := by linear_combination q * h1 + p * h2
      linarith [(mul_eq_zero.mp h).resolve_right hpos.ne']
    · rintro (⟨rfl, rfl⟩ | h)
      · simp
      · have hs : sin a = 0 := by nlinarith [sin_sq_add_cos_sq a]
        simp [h, hs]
  simp only [Prod.ext_iff, PiLp.ext_iff, weightRotation_apply_fst, weightRotation_apply_snd]
  constructor
  · intro h i hi
    exact ((hrot _ _ _).mp ⟨h.1 i, h.2 i⟩).resolve_left (by tauto)
  · intro h
    have key (i : ι) := (hrot (θ i) (x.1 i) (x.2 i)).mpr <| by
      by_cases hi : x.1 i ≠ 0 ∨ x.2 i ≠ 0
      · exact Or.inr (h i hi)
      · exact Or.inl (by tauto)
    exact ⟨fun i ↦ (key i).1, fun i ↦ (key i).2⟩

/-- **Infinitesimal stabilizers in the weight model.** The generator of `θ` vanishes at `z` exactly
when `θ_i = 0` for every coordinate `z_i = q_i + i p_i` that is nonzero. -/
theorem weightGenerator_apply_eq_zero_iff (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightGenerator θ x = 0 ↔ ∀ i, (x.1 i ≠ 0 ∨ x.2 i ≠ 0) → θ i = 0 := by
  simp only [Prod.ext_iff, PiLp.ext_iff, weightGenerator_apply_fst, weightGenerator_apply_snd,
    Prod.fst_zero, Prod.snd_zero, PiLp.zero_apply, neg_eq_zero, mul_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases hi with hi | hi
    · exact (h2 i).resolve_right hi
    · exact (h1 i).resolve_right hi
  · intro h
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> by_cases hi : x.1 i ≠ 0 ∨ x.2 i ≠ 0
    · exact Or.inl (h i hi)
    · exact Or.inr (by tauto)
    · exact Or.inl (h i hi)
    · exact Or.inr (by tauto)

/-- The kernel of the generator of the rotation by the angles `θ` is the subspace of `z` with
`z_i = q_i + i p_i = 0` whenever `θ_i ≠ 0`. -/
theorem mem_ker_weightGenerator_iff (θ : ι → ℝ) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    x ∈ LinearMap.ker (weightGenerator θ).toLinearMap ↔
      ∀ i, θ i ≠ 0 → x.1 i = 0 ∧ x.2 i = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, weightGenerator_apply_eq_zero_iff]
  exact forall_congr' fun i ↦ by tauto

omit [Fintype ι] in
/-- The real coordinates `(q, p) ↦ (q_i)_i ⊔ (p_i)_i` of `ℂ^ι`, indexed by `ι ⊕ ι`. -/
def weightModelCoords :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ≃ₗ[ℝ] (ι ⊕ ι → ℝ) :=
  ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).prodCongr (WithLp.linearEquiv 2 ℝ (ι → ℝ))).trans
    (LinearEquiv.sumArrowLequivProdArrow ι ι ℝ ℝ).symm

omit [Fintype ι] in
@[simp]
theorem weightModelCoords_apply_inl (v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    weightModelCoords v (Sum.inl i) = v.1 i :=
  (rfl)

omit [Fintype ι] in
@[simp]
theorem weightModelCoords_apply_inr (v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    weightModelCoords v (Sum.inr i) = v.2 i :=
  (rfl)

omit [Fintype ι] in
@[simp]
theorem weightModelCoords_symm_apply_fst (u : ι ⊕ ι → ℝ) (i : ι) :
    (weightModelCoords.symm u).1 i = u (Sum.inl i) :=
  (rfl)

omit [Fintype ι] in
@[simp]
theorem weightModelCoords_symm_apply_snd (u : ι ⊕ ι → ℝ) (i : ι) :
    (weightModelCoords.symm u).2 i = u (Sum.inr i) :=
  (rfl)

/-- In the real coordinates `(q_i)_i ⊔ (p_i)_i`, the kernel of the generator of the rotation by the
angles `θ` is spanned by the coordinates whose angle vanishes. -/
theorem map_weightModelCoords_ker_weightGenerator (θ : ι → ℝ) :
    (LinearMap.ker (weightGenerator θ).toLinearMap).map weightModelCoords.toLinearMap =
      Pi.spanSubset ℝ {j | Sum.elim θ θ j = 0} := by
  ext u
  obtain ⟨v, rfl⟩ := weightModelCoords.surjective u
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_ker_weightGenerator_iff,
    Pi.mem_spanSubset_iff]
  constructor
  · rintro h (i | i) hi
    · exact (h i hi).1
    · exact (h i hi).2
  · exact fun h i hi ↦ ⟨h (Sum.inl i) hi, h (Sum.inr i) hi⟩

/-- **Fixed tangent directions in the weight model.** The kernel of the generator of the rotation
by the angles `θ` has dimension twice the number of `i` with `θ_i = 0`. -/
theorem finrank_ker_weightGenerator (θ : ι → ℝ) :
    Module.finrank ℝ (LinearMap.ker (weightGenerator θ).toLinearMap) =
      2 * {i | θ i = 0}.ncard := by
  rw [← weightModelCoords.finrank_map_eq, map_weightModelCoords_ker_weightGenerator,
    Pi.dim_spanSubset, Set.ncard_setOf_sumElim θ (· = 0)]

/-- **The image of the derivative of the moment map.** At `z`, the derivative of `μ` has image the
span of the weights `α_i` for which the coordinate `z_i = q_i + i p_i` is nonzero. -/
theorem range_fderiv_weightMomentMap (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    LinearMap.range (fderiv ℝ (weightMomentMap α) x).toLinearMap =
      Submodule.span ℝ (α '' {i | x.1 i ≠ 0 ∨ x.2 i ≠ 0}) := by
  rw [(hasFDerivAt_weightMomentMap α x).fderiv]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : x.1 i ≠ 0 ∨ x.2 i ≠ 0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · obtain ⟨h1, h2⟩ : x.1 i = 0 ∧ x.2 i = 0 := by tauto
      simp [h1, h2]
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    classical
    have hpos : 0 < x.1 i ^ 2 + x.2 i ^ 2 := by
      rcases hi with hi | hi
      · have := sq_pos_of_ne_zero hi; positivity
      · have := sq_pos_of_ne_zero hi; positivity
    refine ⟨-(x.1 i ^ 2 + x.2 i ^ 2)⁻¹ • (EuclideanSpace.single i (x.1 i),
      EuclideanSpace.single i (x.2 i)), ?_⟩
    simp only [ContinuousLinearMap.coe_coe, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp only [neg_add_rev, neg_smul, Prod.smul_mk, Prod.neg_mk, add_apply, neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', PiLp.proj_apply,
      PiLp.neg_apply, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_neg, neg_neg,
      ContinuousLinearMap.coe_fst']
    convert one_smul ℝ (α i) using 2
    field_simp
    ring

/-- The infinitesimal action `ξ ↦ ξ_M(z)` of `𝔱` at the point `z` of the weight model: the
generator of the rotation by the angles `α_i(ξ)`, evaluated at `z`. Its range is the tangent space
at `z` of the orbit through `z`. -/
def weightInfinitesimalAction (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    𝔱 →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι where
  toFun ξ := weightGenerator (fun i ↦ α i ξ) x
  map_add' ξ η := by ext i <;> simp <;> ring
  map_smul' c ξ := by ext i <;> simp <;> ring

@[simp]
theorem weightInfinitesimalAction_apply (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (ξ : 𝔱) :
    weightInfinitesimalAction α x ξ = weightGenerator (fun i ↦ α i ξ) x :=
  (rfl)

/-- The isotropy Lie algebra of `z`: `ξ` generates a vector field vanishing at `z` exactly when
`α_i(ξ) = 0` for every coordinate `z_i = q_i + i p_i` that is nonzero. -/
theorem mem_ker_weightInfinitesimalAction_iff (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (ξ : 𝔱) :
    ξ ∈ LinearMap.ker (weightInfinitesimalAction α x) ↔
      ∀ i, (x.1 i ≠ 0 ∨ x.2 i ≠ 0) → α i ξ = 0 := by
  rw [LinearMap.mem_ker, weightInfinitesimalAction_apply, weightGenerator_apply_eq_zero_iff]

/-- The moment map equation `ω(ξ_M(z), v) = dμ_z(v)(ξ)` of the weight model. -/
theorem stdSymplecticForm_weightInfinitesimalAction (α : ι → StrongDual ℝ 𝔱)
    (x v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (ξ : 𝔱) :
    stdSymplecticForm (weightInfinitesimalAction α x ξ) v =
      fderiv ℝ (weightMomentMap α) x v ξ := by
  rw [weightInfinitesimalAction_apply, ← hamiltonianVectorField_weightMomentMap,
    SymplecticForm.apply_hamiltonianVectorField,
    (hasFDerivAt_weightMomentMap_apply α ξ x).fderiv, (hasFDerivAt_weightMomentMap α x).fderiv]
  simp only [ContinuousLinearMap.coprod_apply, coe_innerSL_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, mul_neg, neg_add_rev, sum_apply,
    ContinuousLinearMap.smulRight_apply, add_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', PiLp.proj_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst']
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Orbit rank in the weight model.** The orbit through `z` has dimension the rank of the
weights `α_i` for which the coordinate `z_i = q_i + i p_i` is nonzero. -/
theorem finrank_range_weightInfinitesimalAction (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    Module.finrank ℝ (LinearMap.range (weightInfinitesimalAction α x)) =
      Module.finrank ℝ (Submodule.span ℝ (α '' {i | x.1 i ≠ 0 ∨ x.2 i ≠ 0})) := by
  let J : StrongDual ℝ 𝔱 →ₗ[ℝ] Module.Dual ℝ 𝔱 := ContinuousLinearMap.coeLM ℝ
  have hJ : Function.Injective J := ContinuousLinearMap.coe_injective
  let D := (stdSymplecticForm (V := EuclideanSpace ℝ ι)).toBilinForm.toDual
    (stdSymplecticForm (V := EuclideanSpace ℝ ι)).nondegenerate
  -- By the moment map equation and antisymmetry of `ω`, `dμ_z` is `-(A^* ∘ ω♭)` up to the
  -- inclusion `J` of the continuous dual, where `A` is the infinitesimal action at `z`.
  have key : J ∘ₗ (fderiv ℝ (weightMomentMap α) x).toLinearMap =
      -((weightInfinitesimalAction α x).dualMap ∘ₗ D.toLinearMap) := by
    refine LinearMap.ext fun v ↦ LinearMap.ext fun ξ ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.dualMap_apply,
      LinearEquiv.coe_coe, LinearMap.BilinForm.toDual_def, ContinuousLinearMap.coeLM_apply,
      ContinuousLinearMap.coe_coe, D, J]
    rw [← stdSymplecticForm_weightInfinitesimalAction, ← SymplecticForm.neg_eq]
  rw [← range_fderiv_weightMomentMap, (Submodule.equivMapOfInjective J hJ _).finrank_eq,
    ← LinearMap.range_comp, key, LinearMap.range_neg,
    LinearMap.range_comp_of_range_eq_top _ D.range,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

/-! ### Orbits of the rotation torus -/

/-- **The kernel of the rotation action.** The rotation by the angles `θ` is the identity of
`ℂ^ι` exactly when every `θ_j` lies in `2πℤ`. -/
theorem weightRotation_eq_id_iff (θ : ι → ℝ) :
    weightRotation θ = ContinuousLinearMap.id ℝ _ ↔ ∀ j, ∃ k : ℤ, k * (2 * π) = θ j := by
  refine ⟨fun h j ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun x ↦
    (weightRotation_apply_eq_self_iff θ x).2 fun j _ ↦ h j⟩
  have hx : weightRotation θ (WithLp.toLp 2 fun _ ↦ (1 : ℝ), 0) = (WithLp.toLp 2 fun _ ↦ 1, 0) := by
    rw [h, ContinuousLinearMap.id_apply]
  exact (weightRotation_apply_eq_self_iff θ _).1 hx j (Or.inl (by simp))

/-- **Orbits of the rotation torus.** Some rotation of `ℂ^ι` carries `z` to `w` exactly when
`|z_j| = |w_j|` for every `j`. -/
theorem exists_weightRotation_apply_eq_iff (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∃ θ, weightRotation θ x = y) ↔ ∀ j, x.1 j ^ 2 + x.2 j ^ 2 = y.1 j ^ 2 + y.2 j ^ 2 := by
  constructor
  · rintro ⟨θ, rfl⟩ j
    simp only [weightRotation_apply_fst, weightRotation_apply_snd]
    linear_combination -(x.1 j ^ 2 + x.2 j ^ 2) * sin_sq_add_cos_sq (θ j)
  · -- Two complex numbers of equal modulus differ by the rotation by the difference of their
    -- arguments.
    have hrotC (z w : ℂ) (hzw : ‖z‖ = ‖w‖) : ∃ θ : ℝ, cos θ * z.re - sin θ * z.im = w.re ∧
        sin θ * z.re + cos θ * z.im = w.im := by
      have hc := cos_add (w.arg - z.arg) z.arg
      have hs := sin_add (w.arg - z.arg) z.arg
      rw [sub_add_cancel] at hc hs
      refine ⟨w.arg - z.arg, ?_, ?_⟩
      · rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
          ← Complex.norm_mul_cos_arg w, ← hzw, hc]
        ring
      · rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
          ← Complex.norm_mul_sin_arg w, ← hzw, hs]
        ring
    intro h
    -- Apply this to the coordinates `q_j + i p_j` of the two points.
    have hrot (j : ι) : ∃ θ : ℝ, cos θ * x.1 j - sin θ * x.2 j = y.1 j ∧
        sin θ * x.1 j + cos θ * x.2 j = y.2 j := by
      refine hrotC ⟨x.1 j, x.2 j⟩ ⟨y.1 j, y.2 j⟩ ?_
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_mk, Complex.normSq_mk]
      linear_combination h j
    choose θ hθ using hrot
    exact ⟨θ, by ext j <;> simp [hθ]⟩

/-- **Fixed points of the weight action.** A point of `ℂ^ι` is fixed by the action of every
`ξ ∈ 𝔱` exactly when its coordinates `z_j` vanish along the nonzero weights `α_j`. -/
theorem forall_weightRotation_apply_eq_self_iff (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ ξ, weightRotation (fun j ↦ α j ξ) x = x) ↔ ∀ j, α j ≠ 0 → x.1 j = 0 ∧ x.2 j = 0 := by
  simp only [weightRotation_apply_eq_self_iff]
  constructor
  · intro h j hj
    by_contra hx
    obtain ⟨η, hη⟩ : ∃ η, α j η ≠ 0 := by
      by_contra! H
      exact hj (ContinuousLinearMap.ext H)
    -- The element `ξ = (π / α_j(η)) η` rotates the `j`-th coordinate by the angle `π`.
    obtain ⟨k, hk⟩ := h ((π / α j η) • η) j (by tauto)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hη] at hk
    have h2k : ((2 * k : ℤ) : ℝ) = (1 : ℤ) :=
      mul_right_cancel₀ pi_ne_zero (by push_cast; linear_combination hk)
    have := Int.cast_injective h2k
    omega
  · intro h ξ j hj
    by_cases hα : α j = 0
    · exact ⟨0, by simp [hα]⟩
    · exact absurd (h j hα) (by tauto)

/-! ### Linearly independent weights -/

/-- For linearly independent weights, the moment map determines the moduli `|z_j|`: two points of
`ℂ^ι` have the same moment image exactly when `|z_j| = |w_j|` for every `j`. -/
theorem weightMomentMap_eq_weightMomentMap_iff {α : ι → StrongDual ℝ 𝔱}
    (hα : LinearIndependent ℝ α) (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α x = weightMomentMap α y ↔
      ∀ j, x.1 j ^ 2 + x.2 j ^ 2 = y.1 j ^ 2 + y.2 j ^ 2 := by
  refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
  · have hsum : ∑ j, ((-(1 / 2) * (x.1 j ^ 2 + x.2 j ^ 2)) - (-(1 / 2) * (y.1 j ^ 2 + y.2 j ^ 2)))
        • α j = 0 := by
      rw [Finset.sum_congr rfl fun j _ ↦ sub_smul _ _ (α j), Finset.sum_sub_distrib,
        ← weightMomentMap_def, ← weightMomentMap_def, h, sub_self]
    linarith [Fintype.linearIndependent_iff.1 hα _ hsum j]
  · simp only [weightMomentMap_def, h]

/-- **Fibres of the moment map are orbits.** For linearly independent weights, two points of
`ℂ^ι` have the same moment image exactly when the action of some `ξ ∈ 𝔱` carries one to the
other. -/
theorem weightMomentMap_eq_weightMomentMap_iff_exists_weightRotation {α : ι → StrongDual ℝ 𝔱}
    (hα : LinearIndependent ℝ α) (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α x = weightMomentMap α y ↔ ∃ ξ, weightRotation (fun j ↦ α j ξ) x = y := by
  refine ⟨fun h ↦ ?_, fun ⟨ξ, hξ⟩ ↦ hξ ▸ (weightMomentMap_weightRotation α _ x).symm⟩
  obtain ⟨θ, rfl⟩ := (exists_weightRotation_apply_eq_iff x y).2
    ((weightMomentMap_eq_weightMomentMap_iff hα x y).1 h)
  -- Linearly independent functionals take every family of values `θ` simultaneously.
  have hli : LinearIndependent ℝ fun j ↦ ⇑(α j) :=
    Fintype.linearIndependent_iff.2 fun g hg ↦ Fintype.linearIndependent_iff.1 hα g
      (ContinuousLinearMap.ext fun ξ ↦ by simpa using congrFun hg ξ)
  have hθ : θ ∈ Submodule.span ℝ (Set.range (flip fun j ↦ ⇑(α j))) := by
    rw [span_flip_eq_top_iff_linearIndependent.2 hli]
    trivial
  let A : 𝔱 →ₗ[ℝ] ι → ℝ := LinearMap.pi fun j ↦ (α j : 𝔱 →ₗ[ℝ] ℝ)
  have hA : Set.range (flip fun j ↦ ⇑(α j)) = (LinearMap.range A : Set (ι → ℝ)) := by
    ext v
    simp [A, flip, funext_iff]
  rw [hA, Submodule.span_eq] at hθ
  obtain ⟨ξ, hξ⟩ := hθ
  exact ⟨ξ, by rw [← hξ]; rfl⟩

/-- For linearly independent weights, the origin is the only point of `ℂ^ι` mapped to the apex
`0` of the moment cone. -/
@[simp]
theorem weightMomentMap_eq_zero_iff {α : ι → StrongDual ℝ 𝔱} (hα : LinearIndependent ℝ α)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : weightMomentMap α x = 0 ↔ x = 0 := by
  rw [← weightMomentMap_zero α, weightMomentMap_eq_weightMomentMap_iff hα]
  simp only [Prod.fst_zero, Prod.snd_zero, PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, Prod.ext_iff, PiLp.ext_iff]
  refine ⟨fun h ↦ ⟨fun j ↦ ?_, fun j ↦ ?_⟩, fun h j ↦ by simp [h.1 j, h.2 j]⟩ <;>
    nlinarith [h j, sq_nonneg (x.1 j), sq_nonneg (x.2 j)]

/-- **Fixed points lie over the apex.** For linearly independent weights, a point of `ℂ^ι` is
fixed by the whole action of `𝔱` exactly when its moment image is the apex `0` of the moment
cone, and then it is the origin. -/
theorem forall_weightRotation_apply_eq_self_iff_weightMomentMap_eq_zero
    {α : ι → StrongDual ℝ 𝔱} (hα : LinearIndependent ℝ α)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ ξ, weightRotation (fun j ↦ α j ξ) x = x) ↔ weightMomentMap α x = 0 := by
  rw [forall_weightRotation_apply_eq_self_iff, weightMomentMap_eq_zero_iff hα]
  simp only [fun j ↦ hα.ne_zero j, ne_eq, not_false_eq_true, forall_const, Prod.ext_iff,
    PiLp.ext_iff, Prod.fst_zero, Prod.snd_zero, PiLp.zero_apply]
  exact ⟨fun h ↦ ⟨fun j ↦ (h j).1, fun j ↦ (h j).2⟩, fun h j ↦ ⟨h.1 j, h.2 j⟩⟩

/-- **The apex is a vertex.** For linearly independent weights, the apex `0` of the moment cone
is an extreme point of the image of the moment map. -/
theorem zero_mem_extremePoints_range_weightMomentMap {α : ι → StrongDual ℝ 𝔱}
    (hα : LinearIndependent ℝ α) :
    (0 : StrongDual ℝ 𝔱) ∈ Set.extremePoints ℝ (Set.range (weightMomentMap α)) := by
  refine mem_extremePoints_iff_left.2 ⟨⟨0, weightMomentMap_zero α⟩, ?_⟩
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ ⟨s, t, hs, ht, -, hst⟩
  -- The coefficients of `s μ(x) + t μ(y)` in the independent weights all vanish.
  have hsum : ∑ j, (s * (-(1 / 2) * (x.1 j ^ 2 + x.2 j ^ 2)) +
      t * (-(1 / 2) * (y.1 j ^ 2 + y.2 j ^ 2))) • α j = 0 := by
    rw [Finset.sum_congr rfl fun j _ ↦ (add_smul _ _ (α j)).trans
        (congrArg₂ (· + ·) (mul_smul _ _ _) (mul_smul _ _ _)), Finset.sum_add_distrib,
      ← Finset.smul_sum, ← Finset.smul_sum, ← weightMomentMap_def, ← weightMomentMap_def, hst]
  have hx (j : ι) : x.1 j ^ 2 + x.2 j ^ 2 = 0 := by
    have hc := Fintype.linearIndependent_iff.1 hα _ hsum j
    have hx : 0 ≤ s * (x.1 j ^ 2 + x.2 j ^ 2) := by positivity
    have hy : 0 ≤ t * (y.1 j ^ 2 + y.2 j ^ 2) := by positivity
    exact (mul_eq_zero.1 (by linarith : s * (x.1 j ^ 2 + x.2 j ^ 2) = 0)).resolve_left hs.ne'
  rw [← weightMomentMap_zero α, weightMomentMap_eq_weightMomentMap_iff hα]
  simpa using hx

/-! ### Rotations by multiples of `2π` -/

/-- The action of `2π v` fixes `z` exactly when the weights along the nonzero coordinates of `z`
take integer values at `v`. -/
theorem weightRotation_two_pi_smul_apply_eq_self_iff (α : ι → StrongDual ℝ 𝔱) (v : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation (fun j ↦ α j ((2 * π) • v)) x = x ↔
      ∀ j, (x.1 j ≠ 0 ∨ x.2 j ≠ 0) → ∃ k : ℤ, α j v = k := by
  rw [weightRotation_apply_eq_self_iff]
  refine forall₂_congr fun j _ ↦ exists_congr fun k ↦ ?_
  rw [map_smul, smul_eq_mul, mul_comm (2 * π), mul_left_inj' two_pi_pos.ne', eq_comm]

end TauCeti
