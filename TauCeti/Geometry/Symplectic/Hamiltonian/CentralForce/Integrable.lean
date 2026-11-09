/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Planar central forces are completely integrable

A particle of mass `m ≠ 0` in the plane, moving in a central potential `U`, has the energy
`H(q, p) = ‖p‖² / (2m) + U(‖q‖)` and the angular momentum `L(q, p) = q₁p₂ - q₂p₁`, written in an
orthonormal basis `b` of the plane `V`. Their **energy–momentum map** is
`F = (H, L) : V × V → ℝ²` (`TauCeti.centralForceEnergyMomentum`). This file determines where `H`
and `L` are functionally independent, and concludes that `F` is a completely integrable system.

Off the collision set `q = 0`, the point `(q, p)` is a critical point of `F` exactly when the
radial momentum vanishes, `⟪q, p⟫ = 0`, and `U'(‖q‖) = L² / (m ‖q‖³)`
(`TauCeti.isRegularPoint_centralForceEnergyMomentum_iff`). In terms of the effective potential
`U_ℓ(r) = ℓ² / (2 m r²) + U(r)` of the reduced radial motion, these are the points with `p_r = 0`
and `U_ℓ'(‖q‖) = 0` for `ℓ = L(q, p)`: the points of the circular orbits. At such a point the
Hamiltonian vector field of `H` is `L / (m ‖q‖²)` times that of `L`
(`TauCeti.stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_eq_smul`), so circular
orbits are relative equilibria of the rotational symmetry. The critical values of `F` are the pairs
`(U_ℓ(r), ℓ)` with `r > 0` a critical point of `U_ℓ`
(`TauCeti.image_centralForceEnergyMomentum_setOf_not_isRegularPoint`).

On the punctured phase space `{(q, p) | q ≠ 0}` (`TauCeti.puncturedPhaseSpace`), the cotangent
bundle of the punctured plane, `H` and `L` Poisson-commute, and the points with `⟪q, p⟫ ≠ 0` are
dense and regular. So for every potential smooth on `(0, ∞)`, such as the Kepler potential, `F` is a
completely integrable system there (`TauCeti.isIntegrableSystem_centralForceEnergyMomentum`).

## Main declarations

* `TauCeti.centralForceEnergyMomentum`: the energy–momentum map `(H, L)`.
* `TauCeti.isRegularPoint_centralForceEnergyMomentum_iff`: `H` and `L` are independent at
  `(q, p)` with `q ≠ 0` unless `⟪q, p⟫ = 0` and `U'(‖q‖) = L² / (m ‖q‖³)`.
* `TauCeti.stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_eq_smul`: on circular
  orbits `X_H = (L / (m ‖q‖²)) X_L`.
* `TauCeti.image_centralForceEnergyMomentum_setOf_not_isRegularPoint`: the critical values.
* `TauCeti.puncturedPhaseSpace`: the open set `{(q, p) | q ≠ 0}`.
* `TauCeti.isIntegrableSystem_centralForceEnergyMomentum`: `(H, L)` is a completely integrable
  system on the punctured phase space.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 49.
-/

public section

open Function Module Set
open scoped InnerProductSpace ContDiff Manifold Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V]

/-! ### The punctured phase space -/

variable (V) in
/-- The phase space `{(q, p) | q ≠ 0}` of a particle kept away from the centre of force: the
cotangent bundle `(V \ {0}) × V` of the punctured configuration space, as an open subset of
`V × V`. Singular central potentials such as the Kepler potential `-κ / ‖q‖` are smooth there. -/
def puncturedPhaseSpace : TopologicalSpace.Opens (V × V) :=
  ⟨{x | x.1 ≠ 0}, isOpen_ne_fun continuous_fst continuous_const⟩

@[simp]
theorem mem_puncturedPhaseSpace {x : V × V} : x ∈ puncturedPhaseSpace V ↔ x.1 ≠ 0 :=
  Iff.rfl

variable [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V)


/-- The **energy–momentum map** `(H, L)` of a particle of mass `m` in the central potential `U`
in the plane, where `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` is the energy and `L = q₁p₂ - q₂p₁` is the
angular momentum in the coordinates of the orthonormal basis `b`. -/
noncomputable def centralForceEnergyMomentum (m : ℝ) (U : ℝ → ℝ) (x : V × V) : Fin 2 → ℝ :=
  ![centralForceHamiltonian m U x, angularMomentum (b 0) (b 1) x]

@[simp]
theorem centralForceEnergyMomentum_zero (m : ℝ) (U : ℝ → ℝ) (x : V × V) :
    centralForceEnergyMomentum b m U x 0 = centralForceHamiltonian m U x :=
  (rfl)

@[simp]
theorem centralForceEnergyMomentum_one (m : ℝ) (U : ℝ → ℝ) (x : V × V) :
    centralForceEnergyMomentum b m U x 1 = angularMomentum (b 0) (b 1) x :=
  (rfl)

/-- Away from the collision set, the derivative of the energy–momentum map has the two rows
`dH = ((U'(‖q‖) / ‖q‖) q, p / m)` and `dL = (⟪p, b₁⟫ b₀ - ⟪p, b₀⟫ b₁, ⟪q, b₀⟫ b₁ - ⟪q, b₁⟫ b₀)`,
written as pairs of partial gradients. -/
theorem hasFDerivAt_centralForceEnergyMomentum {m : ℝ} {U : ℝ → ℝ} {U' : ℝ} {x : V × V}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) :
    HasFDerivAt (centralForceEnergyMomentum b m U)
      (ContinuousLinearMap.pi ![
        (innerSL ℝ ((U' / ‖x.1‖) • x.1)).coprod (innerSL ℝ (m⁻¹ • x.2)),
        (innerSL ℝ (⟪x.2, b 1⟫_ℝ • b 0 - ⟪x.2, b 0⟫_ℝ • b 1)).coprod
          (innerSL ℝ (⟪x.1, b 0⟫_ℝ • b 1 - ⟪x.1, b 1⟫_ℝ • b 0))]) x := by
  have h : centralForceEnergyMomentum b m U =
      fun y i ↦ (![centralForceHamiltonian m U, angularMomentum (b 0) (b 1)] : Fin 2 → _) i y := by
    funext y i
    fin_cases i <;> rfl
  rw [h, hasFDerivAt_pi]
  intro i
  fin_cases i
  · exact hasFDerivAt_centralForceHamiltonian hU hq
  · exact hasFDerivAt_angularMomentum (b 0) (b 1) x

/-- On a circular orbit, where `⟪q, p⟫ = 0` and `U' = L² / (m ‖q‖³)`, the partial gradients of the
energy are those of the angular momentum multiplied by the angular velocity `L / (m ‖q‖²)`. -/
private theorem smul_eq_smul_of_circular {m U' : ℝ} {q p : V} (hq : q ≠ 0)
    (h0 : ⟪q, p⟫_ℝ = 0) (hU' : U' = angularMomentum (b 0) (b 1) (q, p) ^ 2 / (m * ‖q‖ ^ 3)) :
    (U' / ‖q‖) • q = (angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)) •
        (⟪p, b 1⟫_ℝ • b 0 - ⟪p, b 0⟫_ℝ • b 1) ∧
      m⁻¹ • p = (angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2)) •
        (⟪q, b 0⟫_ℝ • b 1 - ⟪q, b 1⟫_ℝ • b 0) := by
  have hb : ∀ i j, ⟪b i, b j⟫_ℝ = if i = j then 1 else 0 := orthonormal_iff_ite.1 b.orthonormal
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hqq := b.real_inner_fin_two q q
  rw [real_inner_self_eq_norm_sq] at hqq
  have hqp := (b.real_inner_fin_two q p).symm.trans h0
  set L := angularMomentum (b 0) (b 1) (q, p) with hL
  rw [angularMomentum_apply] at hL
  -- In the plane, `p ⊥ q` forces `‖q‖² p = L (-q₁, q₀)`.
  have hp₀ : ‖q‖ ^ 2 * ⟪p, b 0⟫_ℝ = -⟪q, b 1⟫_ℝ * L := by
    rw [hL, hqq]; linear_combination ⟪q, b 0⟫_ℝ * hqp
  have hp₁ : ‖q‖ ^ 2 * ⟪p, b 1⟫_ℝ = ⟪q, b 0⟫_ℝ * L := by
    rw [hL, hqq]; linear_combination ⟪q, b 1⟫_ℝ * hqp
  constructor <;> refine InnerProductSpace.ext_inner_left_basis b.toBasis fun i ↦ ?_ <;>
    fin_cases i <;> simp [inner_smul_right, inner_sub_right, hb, real_inner_comm, hU'] <;>
    field_simp
  · linear_combination -L * m⁻¹ * hp₁
  · linear_combination L * m⁻¹ * hp₀
  · linear_combination m⁻¹ * hp₀
  · linear_combination m⁻¹ * hp₁

/-- The reverse direction of `isRegularPoint_centralForceEnergyMomentum_iff`: off the collision set,
a vanishing combination `s dH + t dL` forces `s = t = 0` unless `⟪q, p⟫ = 0` and
`U' = L² / (m ‖q‖³)`. -/
private theorem eq_zero_of_smul_add_smul_eq_zero {m U' : ℝ} (hm : m ≠ 0) {q p : V} (hq : q ≠ 0)
    (hnc : ¬(⟪q, p⟫_ℝ = 0 ∧ U' = angularMomentum (b 0) (b 1) (q, p) ^ 2 / (m * ‖q‖ ^ 3)))
    {s t : ℝ}
    (hst : s • ⇑((innerSL ℝ ((U' / ‖q‖) • q)).coprod (innerSL ℝ (m⁻¹ • p))) +
      t • ⇑((innerSL ℝ (⟪p, b 1⟫_ℝ • b 0 - ⟪p, b 0⟫_ℝ • b 1)).coprod
        (innerSL ℝ (⟪q, b 0⟫_ℝ • b 1 - ⟪q, b 1⟫_ℝ • b 0))) = 0) :
    s = 0 ∧ t = 0 := by
  have hb : ∀ i j, ⟪b i, b j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 b.orthonormal
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hqp := b.real_inner_fin_two q p
  have hqq := b.real_inner_fin_two q q
  rw [real_inner_self_eq_norm_sq] at hqq
  set L := angularMomentum (b 0) (b 1) (q, p) with hL
  rw [angularMomentum_apply] at hL
  set q₀ := ⟪q, b 0⟫_ℝ with hq₀
  set q₁ := ⟪q, b 1⟫_ℝ with hq₁
  set p₀ := ⟪p, b 0⟫_ℝ with hp₀
  set p₁ := ⟪p, b 1⟫_ℝ with hp₁
  set r := ‖q‖
  have e (v w : V) := congrFun hst (v, w)
  have e₁ := e (b 0) 0
  have e₂ := e (b 1) 0
  have e₃ := e 0 (b 0)
  have e₄ := e 0 (b 1)
  simp [hb, ← hq₀, ← hq₁, ← hp₀, ← hp₁] at e₁ e₂ e₃ e₄
  field_simp at e₁ e₂ e₃ e₄
  rcases eq_or_ne s 0 with rfl | hs
  · -- With `s = 0`, the last two equations say `t q = 0`.
    have h : t ^ 2 * r ^ 2 * m = 0 := by
      rw [hqq]
      linear_combination (t * q₀) * e₄ - (t * q₁) * e₃
    exact ⟨rfl, pow_eq_zero_iff two_ne_zero |>.1 <| (mul_eq_zero.1 <|
      (mul_eq_zero.1 h).resolve_right hm).resolve_right (pow_ne_zero 2 hr)⟩
  · -- With `s ≠ 0`, the momentum is perpendicular to `q` and `s r U' = -t L`,
    -- `s L = -m t r²`, which together say `U'(r) = L² / (m r³)`.
    refine (hnc ⟨?_, ?_⟩).elim
    · have h : s * ⟪q, p⟫_ℝ = 0 := by
        rw [hqp]
        linear_combination q₀ * e₃ + q₁ * e₄
      exact (mul_eq_zero.1 h).resolve_left hs
    · have hA : s * r * U' + t * L = 0 := by
        refine (mul_eq_zero.1 (?_ : r * (s * r * U' + t * L) = 0)).resolve_left hr
        rw [hL]
        linear_combination q₀ * e₁ + q₁ * e₂ + s * U' * hqq
      have hB : s * L + m * t * r ^ 2 = 0 := by
        rw [hL]
        linear_combination q₀ * e₄ - q₁ * e₃ + m * t * hqq
      rw [eq_div_iff (mul_ne_zero hm (pow_ne_zero 3 hr))]
      have h : s ^ 2 * (U' * (m * r ^ 3) - L ^ 2) = 0 := by
        linear_combination m * r ^ 2 * s * hA - s * L * hB
      exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (pow_ne_zero 2 hs))

/-- **The critical points of a planar central force.** At a point `(q, p)` off the collision set
`q = 0`, the differentials of the energy `H` and of the angular momentum `L` are linearly dependent
exactly when the radial momentum `⟪q, p⟫ / ‖q‖` vanishes and `U'(‖q‖) = L² / (m ‖q‖³)`. With the
effective potential `U_L(r) = L² / (2 m r²) + U(r)`, the second condition says that `‖q‖` is a
critical point of `U_L`: the point lies on a circular orbit, or is a rest point when `L = 0`.
Everywhere else `(H, L)` is a submersion. -/
theorem isRegularPoint_centralForceEnergyMomentum_iff {m : ℝ} (hm : m ≠ 0) {U : ℝ → ℝ}
    {U' : ℝ} {x : V × V} (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) :
    IsRegularPoint 𝓘(ℝ, V × V) 𝓘(ℝ, Fin 2 → ℝ) (centralForceEnergyMomentum b m U) x ↔
      ¬(⟪x.1, x.2⟫_ℝ = 0 ∧ U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) := by
  -- Joint surjectivity of two functionals onto `ℝ²` is their linear independence.
  have hsurj (f g : V × V →L[ℝ] ℝ) : Surjective (ContinuousLinearMap.pi ![f, g]) ↔
      ∀ s t : ℝ, s • ⇑f + t • ⇑g = 0 → s = 0 ∧ t = 0 := by
    rw [← LinearIndependent.pair_iff, ← span_flip_eq_top_iff_linearIndependent]
    have hflip : flip ![⇑f, ⇑g] = ⇑(ContinuousLinearMap.pi ![f, g]).toLinearMap := by
      funext v i
      fin_cases i <;> rfl
    rw [hflip, ← LinearMap.coe_range, Submodule.span_eq, LinearMap.range_eq_top,
      ContinuousLinearMap.coe_coe]
  rw [isRegularPoint_iff_surjective_fderiv,
    (hasFDerivAt_centralForceEnergyMomentum b hU hq).fderiv, hsurj]
  obtain ⟨q, p⟩ := x
  dsimp only at hq hU ⊢
  refine ⟨fun h ⟨h0, hU'⟩ ↦ ?_, fun hnc s t hst ↦ ?_⟩
  · -- At a critical point `dH = (L / (m r²)) dL`.
    obtain ⟨hvq, hvp⟩ := smul_eq_smul_of_circular b hq h0 hU'
    obtain ⟨h1, -⟩ := h 1 (-(angularMomentum (b 0) (b 1) (q, p) / (m * ‖q‖ ^ 2))) <| by
      rw [hvq, hvp]
      funext v
      simp
      ring
    exact one_ne_zero h1
  · exact eq_zero_of_smul_add_smul_eq_zero b hm hq hnc hst

/-- **Circular orbits are relative equilibria.** At a point `(q, p)` with `⟪q, p⟫ = 0` and
`U'(‖q‖) = L² / (m ‖q‖³)`, the Hamiltonian vector field of the energy is the Hamiltonian vector
field of the angular momentum, the infinitesimal rotation of the plane, multiplied by the angular
velocity `L / (m ‖q‖²)`: there the motion is tangent to the rotation of the circle of radius
`‖q‖`. -/
theorem stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_eq_smul
    [FiniteDimensional ℝ V] {m : ℝ} {U : ℝ → ℝ} {U' : ℝ} {x : V × V}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (h0 : ⟪x.1, x.2⟫_ℝ = 0)
    (hU' : U' = angularMomentum (b 0) (b 1) x ^ 2 / (m * ‖x.1‖ ^ 3)) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) x =
      (angularMomentum (b 0) (b 1) x / (m * ‖x.1‖ ^ 2)) •
        (stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1)) x := by
  obtain ⟨q, p⟩ := x
  obtain ⟨hvq, hvp⟩ := smul_eq_smul_of_circular b hq h0 hU'
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian hU hq,
    stdSymplecticForm_hamiltonianVectorField_angularMomentum]
  dsimp only
  rw [hvq, hvp, Prod.smul_mk, ← smul_neg, neg_sub]

/-- **The critical values of a planar central force.** The images under the energy–momentum map
of the critical points off the collision set are the pairs `(U_ℓ(r), ℓ)` of an effective energy
`U_ℓ(r) = ℓ² / (2 m r²) + U(r)` and an angular momentum `ℓ` such that `r > 0` is a critical point
of the effective potential, `U'(r) = ℓ² / (m r³)`. -/
theorem image_centralForceEnergyMomentum_setOf_not_isRegularPoint {m : ℝ} (hm : m ≠ 0)
    {U : ℝ → ℝ} (hU : DifferentiableOn ℝ U (Ioi 0)) :
    centralForceEnergyMomentum b m U '' {x | x.1 ≠ 0 ∧
        ¬IsRegularPoint 𝓘(ℝ, V × V) 𝓘(ℝ, Fin 2 → ℝ) (centralForceEnergyMomentum b m U) x} =
      {v | ∃ r > 0, deriv U r = v 1 ^ 2 / (m * r ^ 3) ∧ v 0 = v 1 ^ 2 / (2 * m * r ^ 2) + U r} := by
  have hU' {r : ℝ} (hr : 0 < r) : HasDerivAt U (deriv U r) r :=
    (hU.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  ext v
  constructor
  · rintro ⟨⟨q, p⟩, ⟨hq, hx⟩, rfl⟩
    dsimp only at hq
    have hr : 0 < ‖q‖ := norm_pos_iff.2 hq
    rw [isRegularPoint_centralForceEnergyMomentum_iff b hm (hU' hr) hq, not_not] at hx
    obtain ⟨h0, hd⟩ := hx
    refine ⟨‖q‖, hr, hd, ?_⟩
    -- With `p ⊥ q`, the bivector identity reads `L² = ‖q‖² ‖p‖²`.
    have hL := sq_angularMomentum b (q, p)
    dsimp only at hL
    rw [h0] at hL
    simp only [centralForceEnergyMomentum_zero, centralForceEnergyMomentum_one,
      centralForceHamiltonian_apply, hL]
    field_simp
    ring
  · rintro ⟨r, hr, hd, hv⟩
    have hb : ∀ i j, ⟪b i, b j⟫_ℝ = if i = j then 1 else 0 := orthonormal_iff_ite.1 b.orthonormal
    have hn (i : Fin 2) : ‖b i‖ = 1 := b.orthonormal.1 i
    -- The circular orbit of radius `r` through `r b₀`, with angular momentum `v 1`.
    have hq : r • b 0 ≠ 0 := smul_ne_zero hr.ne' (b.orthonormal.ne_zero 0)
    have hnq : ‖r • b 0‖ = r := by rw [norm_smul, hn, mul_one, Real.norm_of_nonneg hr.le]
    have hL : angularMomentum (b 0) (b 1) (r • b 0, (v 1 / r) • b 1) = v 1 := by
      simp [inner_smul_left, hb]
      field_simp
    refine ⟨(r • b 0, (v 1 / r) • b 1), ⟨hq, ?_⟩, ?_⟩
    · rw [isRegularPoint_centralForceEnergyMomentum_iff b hm (hnq ▸ hU' hr) hq, not_not]
      refine ⟨by simp [inner_smul_left, inner_smul_right, hb], ?_⟩
      dsimp only
      rw [hL, hnq, hd]
    · funext i
      fin_cases i
      · simp only [Fin.zero_eta, centralForceEnergyMomentum_zero, centralForceHamiltonian_apply,
          hnq, norm_smul, hn, mul_one, Real.norm_eq_abs, hv]
        rw [abs_div, abs_of_pos hr, div_pow, sq_abs]
        field_simp
      · exact hL

/-- Away from the collision set, the energy–momentum map is `C^n` at `(q, p)` when the potential
is `C^n` at `‖q‖`. -/
theorem contDiffAt_centralForceEnergyMomentum {m : ℝ} {U : ℝ → ℝ} {n : WithTop ℕ∞} {x : V × V}
    (hU : ContDiffAt ℝ n U ‖x.1‖) (hq : x.1 ≠ 0) :
    ContDiffAt ℝ n (centralForceEnergyMomentum b m U) x := by
  refine contDiffAt_pi.2 fun i ↦ ?_
  fin_cases i
  · have hn : ContDiffAt ℝ n (fun y : V × V ↦ U ‖y.1‖) x :=
      hU.comp x ((contDiffAt_norm ℝ hq).comp x contDiffAt_fst)
    have h : (fun y : V × V ↦ centralForceEnergyMomentum b m U y 0) =
        fun y ↦ ‖y.2‖ ^ 2 / (2 * m) + U ‖y.1‖ :=
      funext fun y ↦ centralForceHamiltonian_apply m U y.1 y.2
    rw [Fin.zero_eta, h]
    exact ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt.div_const _ |>.add hn
  · have h : (fun y : V × V ↦ centralForceEnergyMomentum b m U y 1) =
        fun y ↦ ⟪y.1, b 0⟫_ℝ * ⟪y.2, b 1⟫_ℝ - ⟪y.1, b 1⟫_ℝ * ⟪y.2, b 0⟫_ℝ :=
      funext fun y ↦ angularMomentum_apply (b 0) (b 1) y.1 y.2
    rw [Fin.mk_one, h]
    exact (((contDiff_fst.inner ℝ contDiff_const).mul (contDiff_snd.inner ℝ contDiff_const)).sub
      ((contDiff_fst.inner ℝ contDiff_const).mul (contDiff_snd.inner ℝ contDiff_const))).contDiffAt

/-- The points of the punctured phase space with nonzero radial momentum, `⟪q, p⟫ ≠ 0`, are
dense. -/
theorem dense_setOf_inner_ne_zero :
    Dense {x : puncturedPhaseSpace V | ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ≠ 0} := by
  rintro ⟨⟨q, p⟩, hq⟩
  rcases ne_or_eq ⟪q, p⟫_ℝ 0 with h | h
  · exact subset_closure h
  -- When `⟪q, p⟫ = 0`, the points `(q, p + ε q)` with `ε ≠ 0` have `⟪q, p + ε q⟫ = ε ‖q‖² ≠ 0`.
  have hq' : q ≠ 0 := hq
  let g (ε : ℝ) : puncturedPhaseSpace V := ⟨(q, p + ε • q), hq⟩
  have hg : Filter.Tendsto g (𝓝[≠] 0) (𝓝 ⟨(q, p), hq⟩) := by
    have hc : Continuous g := (continuous_const.prodMk
      (continuous_const.add (continuous_id.smul continuous_const))).subtype_mk _
    simpa [g] using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  refine mem_closure_of_tendsto hg ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa [g, inner_add_right, inner_smul_right, h, hq'] using hε

/-- **Planar central forces are completely integrable.** On the punctured phase space
`{(q, p) | q ≠ 0}` of the plane, with the restriction of the standard symplectic form, the energy
`H = ‖p‖² / (2m) + U(‖q‖)` of a potential `U` smooth on `(0, ∞)` and the angular momentum
`L = q₁p₂ - q₂p₁` form a completely integrable system. They Poisson-commute, and they are
independent away from the circular orbits, a nowhere dense set. -/
theorem isIntegrableSystem_centralForceEnergyMomentum [FiniteDimensional ℝ V] {m : ℝ}
    (hm : m ≠ 0) {U : ℝ → ℝ} (hU : ContDiffOn ℝ ∞ U (Ioi 0)) :
    SmoothTwoForm.IsIntegrableSystem
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceEnergyMomentum b m U ∘ Subtype.val) := by
  have hF (x : puncturedPhaseSpace V) := contDiffAt_centralForceEnergyMomentum b (m := m)
    (hU.contDiffAt (Ioi_mem_nhds (norm_pos_iff.2 x.2))) x.2
  have hval (x : puncturedPhaseSpace V) :
      IsRegularPoint 𝓘(ℝ, V × V) 𝓘(ℝ, V × V) (Subtype.val : puncturedPhaseSpace V → V × V) x := by
    rw [isRegularPoint_iff, Manifold.mfderiv_subtype_val]
    exact (Manifold.tangentSpaceOpenEquiv x).surjective
  have hdiff (x : puncturedPhaseSpace V) (i : Fin 2) :
      MDifferentiableAt 𝓘(ℝ, V × V) 𝓘(ℝ) (fun y ↦ centralForceEnergyMomentum b m U y i) x :=
    ((contDiffAt_pi.1 (hF x) i).differentiableAt (by simp)).mdifferentiableAt
  refine ⟨fun x ↦ (hF x).contMDiffAt.comp x (contMDiff_subtype_val x), fun i j x ↦ ?_, ?_, ?_⟩
  · -- The bracket is computed on `V × V`, where `{H, L} = 0`.
    have hr : 0 < ‖(x : V × V).1‖ := norm_pos_iff.2 x.2
    have hU' : HasDerivAt U (deriv U ‖(x : V × V).1‖) ‖(x : V × V).1‖ :=
      ((hU.differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
    -- Each component of `F ∘ Subtype.val` is the corresponding component of `F` composed with
    -- `Subtype.val`, by definition of composition.
    have hcomp (k : Fin 2) : (fun y : puncturedPhaseSpace V ↦
        (centralForceEnergyMomentum b m U ∘ Subtype.val) y k) =
          (fun y ↦ centralForceEnergyMomentum b m U y k) ∘ Subtype.val := rfl
    rw [hcomp, hcomp,
      ((SymplecticForm.isNondegenerate_constSmooth _).mpullback_subtype_val _).poissonBracket_comp
        (SymplecticForm.isNondegenerate_constSmooth _) contMDiff_subtype_val rfl
        (isRegularPoint_iff.1 (hval x)) (hdiff x i) (hdiff x j),
      SymplecticForm.poissonBracket_constSmooth]
    have h := stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum (m := m)
      hU' x.2 (b 0) (b 1)
    fin_cases i <;> fin_cases j
    · exact SymplecticForm.poissonBracket_self _ _ _
    · exact h
    · simpa [← SymplecticForm.neg_poissonBracket _ (centralForceHamiltonian m U)] using h
    · exact SymplecticForm.poissonBracket_self _ _ _
  · -- Points with nonzero radial momentum are regular, and they are dense.
    refine Dense.mono (s₁ := {x : puncturedPhaseSpace V | ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ≠ 0})
      (fun x hx ↦ ?_) ?_
    · have hr : 0 < ‖(x : V × V).1‖ := norm_pos_iff.2 x.2
      have hU' : HasDerivAt U (deriv U ‖(x : V × V).1‖) ‖(x : V × V).1‖ :=
        ((hU.differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
      refine (isRegularPoint_centralForceEnergyMomentum_iff b hm hU' x.2).2 ?_ |>.comp (hval x)
      exact fun h ↦ hx h.1
    · exact dense_setOf_inner_ne_zero
  · rw [Module.finrank_prod, Module.finrank_eq_card_basis b.toBasis]
    simp

end TauCeti
