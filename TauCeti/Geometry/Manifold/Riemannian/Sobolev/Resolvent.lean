/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenspace

/-!
# The resolvent of the Laplacian on a closed manifold

Let `M` be a closed manifold with a continuous Riemannian metric, its Riemannian volume `dV` and
the Sobolev space `H¹(M)` (`TauCeti.Manifold.SobolevH1`) with its Dirichlet form `D`. For `t > 0`
and `f ∈ L²(M)`, the weak form of the equation `(Δ⁺ + t) u = f` for the nonnegative Laplacian
`Δ⁺ = -div grad` asks for `u ∈ H¹(M)` with

`D(u, v) + t ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}` for every `v ∈ H¹(M)`.

The shifted form `D + t ⟪·, ·⟫_{L²}` (`ContinuousLinearMap.shiftedForm`)
is coercive on `H¹(M)`, with constant `min 1 t`, since the squared `H¹` norm is
`D(u, u) + ‖u‖²_{L²}` (`TauCeti.Manifold.SobolevH1.norm_sq_eq_dirichletForm_add`). So
by the Lax–Milgram theorem the equation has exactly one solution, which depends continuously on `f`.
This is the **resolvent** `(Δ⁺ + t)⁻¹ : L²(M) → H¹(M)`
(`TauCeti.Manifold.SobolevH1.resolvent`), characterized by the variational equation
(`TauCeti.Manifold.SobolevH1.dirichletForm_resolvent_add`,
`TauCeti.Manifold.SobolevH1.eq_resolvent`). On the values of a weak `μ`-eigenfunction it is
multiplication by `(μ + t)⁻¹` (`TauCeti.Manifold.SobolevH1.resolvent_toLp_of_mem_weakEigenspace`).

## Main definitions

* `TauCeti.Manifold.SobolevH1.resolvent`: the resolvent `(Δ⁺ + t)⁻¹ : L²(M) →L[ℝ] H¹(M)` for
  `t > 0`.

## Main results

* `TauCeti.Manifold.SobolevH1.isCoercive_shiftedForm_dirichletForm`: `D + t ⟪·, ·⟫_{L²}` is coercive
  for `t > 0`.
* `TauCeti.Manifold.SobolevH1.dirichletForm_resolvent_add`: the resolvent solves the weak equation.
* `TauCeti.Manifold.SobolevH1.eq_resolvent`: the solution of the weak equation is unique.
* `TauCeti.Manifold.SobolevH1.resolvent_toLp_of_mem_weakEigenspace`: the resolvent on weak
  eigenfunctions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.2 (the Lax–Milgram theorem and
  weak solutions of `Lu + t u = f`).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- For `t > 0` the shifted form `D + t ⟪·, ·⟫_{L²}` is coercive, with constant `min 1 t`. -/
theorem isCoercive_shiftedForm_dirichletForm {t : ℝ} (ht : 0 < t) :
    IsCoercive ((toLp (I := I) (M := M)).shiftedForm dirichletForm t) := by
  refine ⟨min 1 t, lt_min one_pos ht, fun u ↦ ?_⟩
  have hD := dirichletForm_self_nonneg u
  rw [mul_assoc, ← sq, norm_sq_eq_dirichletForm_add, shiftedForm_dirichletForm_apply,
    real_inner_self_eq_norm_sq]
  nlinarith [min_le_left 1 t, min_le_right 1 t, sq_nonneg ‖toLp u‖]

variable (I M) in
/-- The **resolvent** `(Δ⁺ + t)⁻¹ : L²(M) → H¹(M)` of the nonnegative Laplacian `Δ⁺ = -div grad`
for `t > 0`: it sends `f ∈ L²(M)` to the unique `u ∈ H¹(M)` with
`D(u, v) + t ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}` for every `v ∈ H¹(M)`
(`TauCeti.Manifold.SobolevH1.dirichletForm_resolvent_add`,
`TauCeti.Manifold.SobolevH1.eq_resolvent`). In the convention `R(λ) = (λ - A)⁻¹` it is the
resolvent of the Laplace–Beltrami operator `Δ = div grad = -Δ⁺` at `λ = t`. -/
def resolvent {t : ℝ} (ht : 0 < t) : Lp ℝ 2 (riemannianVolume I M) →L[ℝ] SobolevH1 I M :=
  (isCoercive_shiftedForm_dirichletForm ht).formSolutionMap toLp

/-- **The resolvent solves the weak equation** `(Δ⁺ + t) u = f`:
`D(u, v) + t ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}` for `u = (Δ⁺ + t)⁻¹ f` and every `v ∈ H¹(M)`. -/
theorem dirichletForm_resolvent_add {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (riemannianVolume I M))
    (v : SobolevH1 I M) :
    dirichletForm (resolvent I M ht f) v + t * ⟪toLp (resolvent I M ht f), toLp v⟫_ℝ =
      ⟪f, toLp v⟫_ℝ := by
  have h := (isCoercive_shiftedForm_dirichletForm ht).apply_formSolutionMap toLp f v
  rwa [shiftedForm_dirichletForm_apply] at h

/-- **Uniqueness of weak solutions.** If `u ∈ H¹(M)` satisfies
`D(u, v) + t ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}` for every `v ∈ H¹(M)`, then `u = (Δ⁺ + t)⁻¹ f`. -/
theorem eq_resolvent {t : ℝ} (ht : 0 < t) {f : Lp ℝ 2 (riemannianVolume I M)} {u : SobolevH1 I M}
    (hu : ∀ v, dirichletForm u v + t * ⟪toLp u, toLp v⟫_ℝ = ⟪f, toLp v⟫_ℝ) :
    u = resolvent I M ht f :=
  (isCoercive_shiftedForm_dirichletForm ht).eq_formSolutionMap toLp fun v ↦ by
    rw [shiftedForm_dirichletForm_apply, hu]

/-- `u = (Δ⁺ + t)⁻¹ f` exactly when `u` solves the weak equation
`D(u, v) + t ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}` for every `v ∈ H¹(M)`. -/
theorem eq_resolvent_iff {t : ℝ} (ht : 0 < t) {f : Lp ℝ 2 (riemannianVolume I M)}
    {u : SobolevH1 I M} :
    u = resolvent I M ht f ↔
      ∀ v, dirichletForm u v + t * ⟪toLp u, toLp v⟫_ℝ = ⟪f, toLp v⟫_ℝ :=
  ⟨fun hu ↦ hu ▸ dirichletForm_resolvent_add ht f, eq_resolvent ht⟩

/-- **The resolvent on eigenfunctions.** For a weak `μ`-eigenfunction `w` of `Δ⁺` and `t > 0`,
`(Δ⁺ + t)⁻¹` sends the value of `w` in `L²(M)` to `(μ + t)⁻¹ w`. -/
theorem resolvent_toLp_of_mem_weakEigenspace {t : ℝ} (ht : 0 < t) {μ : ℝ} {w : SobolevH1 I M}
    (hw : w ∈ weakEigenspace I M μ) : resolvent I M ht (toLp w) = (μ + t)⁻¹ • w := by
  by_cases hw₀ : toLp w = 0
  · -- then `D(w, w) = μ ‖w‖²_{L²} = 0`, so `w` has `H¹` norm zero
    have hD := mem_weakEigenspace_iff.1 hw w
    rw [hw₀, inner_zero_left, mul_zero] at hD
    have hw' : w = 0 := by
      rw [← norm_eq_zero, ← sq_eq_zero_iff, norm_sq_eq_dirichletForm_add, hD, hw₀, norm_zero]
      simp
    simp [hw']
  refine (eq_resolvent ht fun v ↦ ?_).symm
  have hμt : μ + t ≠ 0 :=
    (add_pos_of_nonneg_of_pos (nonneg_of_mem_weakEigenspace_of_toLp_ne_zero hw hw₀) ht).ne'
  rw [map_smul, map_smul, smul_apply, inner_smul_left, mem_weakEigenspace_iff.1 hw v, smul_eq_mul,
    RCLike.conj_to_real]
  field_simp

end TauCeti.Manifold.SobolevH1
