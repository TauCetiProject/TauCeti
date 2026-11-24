/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Quasilinear.Existence

/-!
# The Leray–Schauder homotopy for quasilinear divergence-form equations

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set, let `A : Ω × ℝ → Mat(n + 1, ℝ)` be a Carathéodory
coefficient, uniformly elliptic and bounded with constants `λ, Λ` in each value of its second
argument, and let `g ∈ H¹(Ω)` and `ℓ ∈ H⁻¹(Ω)`. Freezing the coefficient at `v ∈ L²(Ω)` and solving
the linear problem `-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, gives the frozen solution `S v`
(`TauCeti.PDE.frozenSolution`). Its value `T v ∈ L²(Ω)` defines a continuous map `T` of `L²(Ω)`
with relatively compact range, whose fixed points are the values of the weak solutions of the
quasilinear Dirichlet problem

`-div (A(x, u) ∇u) = ℓ` in `Ω`, `u - g ∈ H¹₀(Ω)`.

The Leray–Schauder method (Schaefer's form, `TauCeti.schaeferFixedPoint`) deforms this fixed-point
equation through the family `v = θ T v`, `0 ≤ θ ≤ 1`, and asks for a bound on its solutions that
does not depend on `θ`. This file identifies the deformed equations with the quasilinear problems
with scaled data: since the frozen solution is homogeneous in `(g, ℓ)`
(`TauCeti.PDE.smul_frozenSolution`), `v = θ T v` holds exactly when `v` is the value of a weak
solution `u` of

`-div (A(x, u) ∇u) = θ ℓ` in `Ω`, `u - θ g ∈ H¹₀(Ω)`

(`TauCeti.PDE.eq_smul_value_frozenSolution_iff`). The energy bound for this problem therefore
bounds every solution of the deformed equation, uniformly in `θ ∈ [0, 1]`: for `Ω ⊆ B(z, R)`,

`‖v‖_{L²} ≤ θ (‖g‖ + 2 ((2R)² + 1) (‖ℓ‖ + Λ ‖g‖) / λ)`

(`TauCeti.PDE.norm_le_of_eq_smul_value_frozenSolution`), so the solutions of the deformed equations
form a bounded subset of `L²(Ω)` (`TauCeti.PDE.isBounded_setOf_eq_smul_value_frozenSolution`). This
bound over `0 ≤ θ ≤ 1` implies the a priori hypothesis of Schaefer's theorem, which ranges over
`0 < θ < 1`. The solution `u = θ S v`
of the deformed problem is the frozen solution with data `θ g` and `θ ℓ`.

## Main declarations

* `TauCeti.PDE.eq_smul_value_frozenSolution_iff`: the solutions of `v = θ T v` are the values of
  the weak solutions of the quasilinear problem with data `θ g` and `θ ℓ`.
* `TauCeti.PDE.norm_le_of_eq_smul_value_frozenSolution`: the a priori bound, linear in `θ`.
* `TauCeti.PDE.isBounded_setOf_eq_smul_value_frozenSolution`: the solutions of the deformed
  equations, `0 ≤ θ ≤ 1`, form a bounded set.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 11.3 (the Leray–Schauder theorem in Schaefer's form) and Section 11.3 (its application
  to quasilinear Dirichlet problems through the family `u = σ T u` and a priori estimates
  uniform in `σ`).
-/

public section

open MeasureTheory Metric Set TopologicalSpace

namespace TauCeti

namespace PDE

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ} {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}

/-- **The Leray–Schauder deformation of the quasilinear Dirichlet problem.** Let `T` be the map
of `L²(Ω)` sending `v` to the value `T v` of the frozen solution `S v` of
`-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`. Then `v = θ T v` exactly when `v` is the value of a
weak solution `u` of the quasilinear problem with scaled data,

`-div (A(x, u) ∇u) = θ ℓ` in `Ω`, `u - θ g ∈ H¹₀(Ω)`.

At `θ = 1` these are the fixed points of `T`, the weak solutions of the quasilinear problem, and at
`θ = 0` the only solution is `v = 0`. -/
theorem eq_smul_value_frozenSolution_iff
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) (θ : ℝ)
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    v = θ • W1p.value (frozenSolution A g ℓ v) ↔
      ∃ u : W1p volume Omega 2, W1p.value u = v ∧ u - θ • g ∈ w1p0Submodule volume Omega 2 ∧
        ∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = (θ • ℓ) φ := by
  have hv := Lp.aestronglyMeasurable v
  have key : θ • W1p.value (frozenSolution A g ℓ v) =
      W1p.value (frozenSolution A (θ • g) (θ • ℓ) v) := by
    rw [← smul_frozenSolution hA hAm hAc hΩ g ℓ θ hv]
    exact (W1p.value_smul θ _).symm
  constructor
  · intro h
    replace h := h.trans key
    refine ⟨_, h.symm, frozenSolution_sub_mem_w1p0Submodule hA hAm hAc hΩ _ _ hv, fun φ => ?_⟩
    -- The coefficient frozen at `u` is the coefficient frozen at `v`, since the value of `u` is
    -- `v`. We use `congrArg` rather than `rw`: the closing `rfl` of `rw` unfolds the energy form.
    exact (congrArg (fun w : Lp ℝ 2 (volume.restrict (Omega : Set _)) =>
      energyFormH1 (fun x => A x (w x)) 0 0 (frozenSolution A (θ • g) (θ • ℓ) v) φ) h).symm.trans
      (forall_energyFormH1_frozenSolution_eq hA hAm hAc hΩ _ _ hv φ)
  · rintro ⟨u, rfl, hug, hu⟩
    exact (congrArg W1p.value
      (eq_frozenSolution_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hA hAm hAc hΩ hv hug
        hu)).trans key.symm

/-- **The a priori bound along the Leray–Schauder deformation.** Let `Ω ⊆ B(z, R)`. Every
solution `v ∈ L²(Ω)` of `v = θ T v`, where `T v` is the value of the frozen solution `S v` of
`-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, satisfies

`‖v‖ ≤ |θ| (‖g‖ + 2 ((2R)² + 1) (‖ℓ‖ + Λ ‖g‖) / λ)`.

The bound depends on `A` only through `λ` and `Λ`; for `0 ≤ θ ≤ 1` it is uniform in `θ`. -/
theorem norm_le_of_eq_smul_value_frozenSolution
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) {θ : ℝ}
    {v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hv : v = θ • W1p.value (frozenSolution A g ℓ v)) :
    ‖v‖ ≤ |θ| * (‖g‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam) := by
  have hS := norm_frozenSolution_sub_le hA hAm hAc hball g ℓ (Lp.aestronglyMeasurable v)
  have hvS : ‖W1p.value (frozenSolution A g ℓ v)‖ ≤
      ‖g‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam :=
    (W1p.norm_value_le _).trans ((norm_le_norm_add_norm_sub' _ g).trans (by linarith))
  calc ‖v‖ = ‖θ • W1p.value (frozenSolution A g ℓ v)‖ := congrArg norm hv
    _ = |θ| * ‖W1p.value (frozenSolution A g ℓ v)‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |θ| * (‖g‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam) :=
        mul_le_mul_of_nonneg_left hvS (abs_nonneg θ)

/-- **Boundedness of the Leray–Schauder family.** The solutions `v ∈ L²(Ω)` of the deformed
equations `v = θ T v`, `0 ≤ θ ≤ 1`, where `T v` is the value of the frozen solution `S v` of
`-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, form a bounded set. It implies the a priori hypothesis
of Schaefer's fixed-point theorem `TauCeti.schaeferFixedPoint`, which ranges over `0 < θ < 1`. -/
theorem isBounded_setOf_eq_smul_value_frozenSolution
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    Bornology.IsBounded
      {v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) |
        ∃ θ ∈ Icc (0 : ℝ) 1, v = θ • W1p.value (frozenSolution A g ℓ v)} := by
  obtain ⟨R, hball⟩ := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  refine isBounded_iff_forall_norm_le.2
    ⟨‖g‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam, ?_⟩
  rintro v ⟨θ, hθ, hv⟩
  have hK : 0 ≤ ‖g‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam := by
    have hlam := (hA 0).pos
    have hLam := (hA 0).upper_nonneg
    exact add_nonneg (norm_nonneg g) (div_nonneg (mul_nonneg (by positivity)
      (add_nonneg (norm_nonneg ℓ) (mul_nonneg hLam (norm_nonneg g)))) hlam.le)
  refine (norm_le_of_eq_smul_value_frozenSolution hA hAm hAc hball g ℓ hv).trans ?_
  exact mul_le_of_le_one_left hK ((abs_of_nonneg hθ.1).trans_le hθ.2)

end PDE

end TauCeti
