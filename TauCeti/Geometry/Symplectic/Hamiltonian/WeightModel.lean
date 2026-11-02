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
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.WithLp

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

## Main definitions

* `TauCeti.weightRotation θ`: the rotation `z_i ↦ exp(i θ_i) z_i`.
* `TauCeti.weightGenerator θ`: its infinitesimal generator `z_i ↦ i θ_i z_i`.
* `TauCeti.weightMomentMap α`: the moment map `μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i`.
* `TauCeti.weightInfinitesimalAction α z`: the infinitesimal action `ξ ↦ ξ_M(z)` at `z`.

## Main results

* `TauCeti.stdSymplecticForm_weightRotation`: rotations are symplectic.
* `TauCeti.weightRotation_add`, `TauCeti.weightRotation_zero`: rotations form an action of the
  additive group `ι → ℝ`.
* `TauCeti.weightMomentMap_weightRotation`: `μ` is invariant under every rotation.
* `TauCeti.hamiltonianVectorField_weightMomentMap`: the Hamiltonian vector field of `μ^ξ` is the
  generator for the angles `α_i(ξ)`.
* `TauCeti.hasDerivAt_weightRotation_hamiltonianVectorField`: `t ↦ (t ξ) • z` is the integral
  curve of the Hamiltonian vector field of `μ^ξ` through `z`.
* `TauCeti.range_weightMomentMap`: the image of `μ` is the cone spanned by the `-α_i`.
* `TauCeti.weightRotation_apply_eq_self_iff`, `TauCeti.weightGenerator_apply_eq_zero_iff`: the
  stabilizer and the infinitesimal stabilizer of a point.
* `TauCeti.range_fderiv_weightMomentMap`: the image of `dμ_z` is the span of the weights `α_i`
  with `z_i ≠ 0`.
* `TauCeti.finrank_range_weightInfinitesimalAction`: the orbit through `z` has dimension the rank
  of the weights `α_i` with `z_i ≠ 0`.

## References

* Victor Guillemin and Shlomo Sternberg, *Convexity properties of the moment mapping*, Invent.
  Math. 67 (1982), Section 2.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Sections 22 and 27.
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

end TauCeti
