/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Translation
public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# Translations and time rotations of Floer cylinders

Let `ω` be a two-form on a manifold `M`. A Floer cylinder is a map `u : ℝ × ℝ → M` solving
`∂_s u - X_{K_s} + J (∂_t u - X_{K_t}) = 0` for a Hamiltonian one-form `K = K_s ds + K_t dt` and
almost complex structures `J`. Translating the domain by `c`, `w ↦ u (w + c)`, translates the
perturbed derivative (`TauCeti.SmoothTwoForm.perturbedMFDeriv_comp_add_right`). So where the data
`K` and `J` are invariant under `c`, the translate of a solution is again a solution. This is
stated pointwise as `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_add_right`.
For autonomous data, a Hamiltonian `H` on `M` with `K = H dt` and almost complex structures
depending only on the target point, this holds for every `c`. So the translations
`u ↦ u(· + a, ·)` and the time rotations `u ↦ u(·, · + θ)`, the translation flows
`TauCeti.translationFlow` along `(1, 0)` and `(0, 1)`, preserve the differentiable solutions
(`TauCeti.SmoothTwoForm.isInvariant_translationFlow_setOf_autonomous`).

The maps fixed by all time rotations are those with `∂_t u = 0`
(`MDifferentiable.forall_periodic_smul_iff`). On them the autonomous Floer equation reduces to the
ordinary differential equation `∂_s u = J X_H(u)`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_autonomous_iff`). Away from them, for
cylinders with a constant end, the stabilizer of the translation and rotation action is finite
(`TauCeti.exists_periodic_iff_of_tendsto_atBot`), and no constant combination of `∂_s u` and
`∂_t u` vanishes identically (`MDifferentiable.eq_zero_of_forall_mfderiv_apply_eq_zero`). These
are the inputs, on classical solutions, to the dimension count for autonomous Floer cylinders
which are not time-independent.

These are statements about classical solutions; no Sobolev completion, regularity or
transversality is asserted.

## Main results

* `TauCeti.SmoothTwoForm.perturbedMFDeriv_comp_add_right`: the perturbed derivative of a
  translate is the translate of the perturbed derivative, for the translated data.
* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_add_right`: translates of
  solutions are solutions where the data are invariant.
* `TauCeti.SmoothTwoForm.isInvariant_translationFlow_setOf_autonomous`: the translation flows
  preserve the differentiable solutions of the autonomous Floer equation.
* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_autonomous_iff`: on a map with
  `∂_t u = 0` the autonomous Floer equation is `∂_s u = J X_H(u)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the translation action on connecting trajectories and on
  time-independent solutions for autonomous Hamiltonians.
-/

public section

open Function
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] (ω : SmoothTwoForm I M)

/-- **The perturbed derivative of a translate.** The perturbed derivative of `w ↦ u (w + c)` for
the translated data `w ↦ K (w + c)` at `z` is the perturbed derivative of `u` for `K` at `z + c`. -/
theorem perturbedMFDeriv_comp_add_right (Ks Kt : ℝ × ℝ → M → ℝ) {u : ℝ × ℝ → M} {z c : ℝ × ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (z + c)) :
    ω.perturbedMFDeriv (fun w ↦ Ks (w + c)) (fun w ↦ Kt (w + c)) (fun w ↦ u (w + c)) z =
      ω.perturbedMFDeriv Ks Kt u (z + c) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, mfderiv_comp_add_right hu]
  -- The two sides differ only in how the tangent spaces at `u (z + c)` are written.
  rfl

/-- **Translations preserve Floer solutions.** If `u` solves the Floer equation at `z + c`, and the
Hamiltonian one-form `K = Ks ds + Kt dt` takes the same value at `z + c` as at `z`, then the
translate `w ↦ u (w + c)` solves the Floer equation at `z`, for the same almost complex structure
on the tangent space at `u (z + c)`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_add_right {Ks Kt : ℝ × ℝ → M → ℝ}
    {u : ℝ × ℝ → M} {z c : ℝ × ℝ} (hKs : Ks (z + c) = Ks z) (hKt : Kt (z + c) = Kt z)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (z + c))
    {J : AlmostComplexStructure (TangentSpace I (u (z + c)))}
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u (z + c)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt (fun w ↦ u (w + c)) z).toLinearMap := by
  -- At `z` the perturbed derivative only sees the values of the data at `z`.
  have hK : ω.perturbedMFDeriv (fun w ↦ Ks (w + c)) (fun w ↦ Kt (w + c)) (fun w ↦ u (w + c)) z =
      ω.perturbedMFDeriv Ks Kt (fun w ↦ u (w + c)) z := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hKs, hKt]
  rwa [← ω.perturbedMFDeriv_comp_add_right Ks Kt hu, hK] at hF

/-- **The translation flows preserve autonomous Floer cylinders.** For a Hamiltonian `H` on `M`
and almost complex structures `J` depending only on the target point, the continuous maps
`u : ℝ × ℝ → M` which are differentiable and solve `∂_s u + J (∂_t u - X_H(u)) = 0` form an
invariant set of the translation flow along every vector `v`; for `v = (1, 0)` and `v = (0, 1)`
these are the translations and the time rotations of the cylinder. -/
theorem isInvariant_translationFlow_setOf_autonomous (H : M → ℝ)
    (J : (x : M) → AlmostComplexStructure (TangentSpace I x)) (v : ℝ × ℝ) :
    IsInvariant (translationFlow v)
      {u : C(ℝ × ℝ, M) | MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u ∧
        ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (u z))
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z).toLinearMap} := by
  intro t u ⟨hu, hF⟩
  have he : ⇑(translationFlow v t u) = fun w ↦ u (w + t • v) :=
    funext fun w ↦ translationFlow_apply v t u w
  rw [Set.mem_ofPred_eq, he]
  refine ⟨fun z ↦ (hu (z + t • v)).comp z
    (differentiableAt_id.add_const (t • v)).mdifferentiableAt, fun z ↦ ?_⟩
  exact ω.isComplexLinearMap_perturbedMFDeriv_comp_add_right rfl rfl (hu (z + t • v))
    (hF (z + t • v))

/-- **Time-independent autonomous Floer cylinders.** At a point where `∂_t u = 0`, for instance on
a map fixed by all time rotations, the autonomous Floer equation
`∂_s u + J (∂_t u - X_H(u)) = 0` says `∂_s u = J X_H(u)`. -/
theorem isComplexLinearMap_perturbedMFDeriv_autonomous_iff (H : M → ℝ) {u : ℝ × ℝ → M}
    {z : ℝ × ℝ} (J : AlmostComplexStructure (TangentSpace I (u z)))
    (hz : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1) = 0) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z).toLinearMap ↔
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0) = J (ω.hamiltonianVectorField H (u z)) := by
  rw [isComplexLinearMap_perturbedMFDeriv_iff, stdComplexLineImag_eq, stdComplexLineReal_eq, hz,
    hamiltonianVectorField_const, Pi.zero_apply, sub_zero, zero_sub, map_neg, ← sub_eq_add_neg,
    sub_eq_zero]

end TauCeti.SmoothTwoForm
