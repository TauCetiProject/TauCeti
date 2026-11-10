/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# The Floer equation in a symplectic chart

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `φ : M → V` be a map into a vector space with a constant symplectic
form `ω₀` which pulls `ω₀` back to `ω` at a point `x`:

`ω_x(v, w) = ω₀(dφ_x v, dφ_x w)`.

A Darboux chart (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) has this property at
every point of its source. This file shows that, at such a point, every ingredient of the
inhomogeneous Floer equation `(du - X_K)^{0,1} = 0` on the manifold is carried by `dφ_x` to the
corresponding ingredient of the Floer equation on `(V, ω₀)` for the coordinate expressions
`K'(z, y)` of the Hamiltonians, with `K(z, ·) = K'(z, ·) ∘ φ` near `x`. So solutions of the
Floer equation in `M` whose image stays in the chart are, read in the chart, solutions of the
Floer equation of a symplectic vector space, with the same energy density. This is how the
analysis of `TauCeti.Geometry.Symplectic.Floer`, carried out for a symplectic vector space target,
applies to a manifold target.

* The differential of `φ` is injective at `x`, since it pulls back the nondegenerate form `ω₀` to
  the nondegenerate form `ω_x` (`TauCeti.SmoothTwoForm.IsNondegenerate.injective_mvfderiv`).
* If `dφ_x` is also surjective, it carries the Hamiltonian vector field of `g ∘ φ` at `x` to the
  Hamiltonian vector field of `g` for `ω₀` at `φ x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_hamiltonianVectorField_comp`). This is a
  pointwise form of the naturality of Hamiltonian vector fields
  (`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp`), which asks for a
  globally defined smooth map.
* For `u : ℝ × ℝ → M` with `u z = x`, the perturbed derivative `d(φ ∘ u) - X_{K'}` of the coordinate
  map is `dφ_x ∘ (du - X_K)` (`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`), and
  the Floer energy densities agree
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp`).
* If `dφ_x ∘ J = J' ∘ dφ_x`, that is, `J'` is the structure `J` read in the chart, then `φ ∘ u`
  solves the coordinate Floer equation for `J'` at `z` exactly when `u` solves the Floer equation
  for `J` (`TauCeti.SmoothTwoForm.IsNondegenerate.isComplexLinearMap_perturbedFDeriv_comp_iff`),
  and `J'` is tamed by `ω₀` when `J` is tamed by `ω_x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.tames_of_isComplexLinearMap_mvfderiv`).

All statements are pointwise and need differentiability only at the point; the chart is any map
with the pullback property there, not necessarily a chart of the manifold structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 8.1
  (the inhomogeneous Cauchy–Riemann equation and its energy).
-/

public section

open Function
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {φ : M → V} {x : M}

/-- **A symplectic chart is an immersion.** If `φ` pulls the symplectic form `ω₀` back to the
nondegenerate form `ω` at `x`, its differential at `x` is injective. -/
theorem injective_mvfderiv (hω : ω.IsNondegenerate)
    (hform : ∀ v w : TangentSpace I x, ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w)) :
    Injective (mvfderiv I φ x) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- `v` pairs to zero with every tangent vector, so it vanishes by nondegeneracy of `ω_x`.
  refine (hω.symplecticFormAt x).separatingLeft v fun w ↦ ?_
  have h := (hω.symplecticFormAt_apply x v w).trans (hform v w)
  rw [hv] at h
  exact h.trans (LinearMap.map_zero₂ _ _)

/-- **Taming in a symplectic chart.** Let `φ` have surjective differential at `x` and pull the
symplectic form `ω₀` back to the nondegenerate form `ω` at `x`. If `J` is tamed by `ω_x` and `J'`
is `J` read in the chart, `dφ ∘ J = J' ∘ dφ`, then `J'` is tamed by `ω₀`. -/
theorem tames_of_isComplexLinearMap_mvfderiv (hω : ω.IsNondegenerate)
    (hsurj : Surjective (mvfderiv I φ x))
    (hform : ∀ v w : TangentSpace I x, ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    {J : AlmostComplexStructure (TangentSpace I x)} {J' : AlmostComplexStructure V}
    (hJ : IsComplexLinearMap J J' (mvfderiv I φ x).toLinearMap)
    (hJt : (hω.symplecticFormAt x).Tames J) : ω₀.Tames J' := by
  intro w hw
  obtain ⟨v, rfl⟩ := hsurj w
  have hJv := LinearMap.congr_fun hJ v
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hJv
  rw [← hJv, ← hform, ← symplecticFormAt_apply]
  exact hJt v fun hv ↦ hw (by rw [hv, map_zero])

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]

/-- **Hamiltonian vector fields in a symplectic chart.** Let `φ` be differentiable at `x`, with
surjective differential there, and pull the symplectic form `ω₀` back to the nondegenerate form
`ω` at `x`. For a function `g` differentiable at `φ x`, the differential of `φ` carries the
Hamiltonian vector field of `g ∘ φ` at `x` to the Hamiltonian vector field of `g` for `ω₀` at
`φ x`. -/
theorem mvfderiv_hamiltonianVectorField_comp (hω : ω.IsNondegenerate)
    (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ x) (hsurj : Surjective (mvfderiv I φ x))
    (hform : ∀ v w : TangentSpace I x, ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    {g : V → ℝ} (hg : DifferentiableAt ℝ g (φ x)) :
    mvfderiv I φ x (ω.hamiltonianVectorField (g ∘ φ) x) = ω₀.hamiltonianVectorField g (φ x) := by
  refine (ω₀.eq_hamiltonianVectorField_iff g (φ x) _).2 fun w ↦ ?_
  obtain ⟨v, rfl⟩ := hsurj w
  -- Both sides are `d(g ∘ φ)_x v`: the left one because `φ` pulls `ω₀` back to `ω`.
  rw [← hform, hω.eval₂_hamiltonianVectorField, mvfderiv_comp_apply_of_differentiableAt hg hφ]

variable {Ks Kt : ℝ × ℝ → M → ℝ} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- **The perturbed derivative in a symplectic chart.** Let `φ` be differentiable at `u z` with
surjective differential there, pulling the symplectic form `ω₀` back to the nondegenerate form `ω`
at `u z`, and let the Hamiltonians `Ks z`, `Kt z` agree near `u z` with `Ks' z ∘ φ`, `Kt' z ∘ φ`
for functions `Ks' z`, `Kt' z` differentiable at `φ (u z)`. If `u` is differentiable at `z`, the
perturbed derivative `d(φ ∘ u) - X_{K'}` of the coordinate map for `ω₀` is the differential of `φ`
applied to the perturbed derivative `du - X_K` of `u` for `ω`. -/
theorem perturbedFDeriv_comp (hω : ω.IsNondegenerate) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z)) (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z))) :
    ω₀.perturbedFDeriv Ks' Kt' (φ ∘ u) z =
      (mvfderiv I φ (u z)).comp (ω.perturbedMFDeriv Ks Kt u z) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hd : fderiv ℝ (φ ∘ u) z v = mvfderiv I φ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v) :=
    (mvfderiv_eq_fderiv_apply (φ ∘ u) z v).symm.trans (mvfderiv_comp_apply z hφ hu v)
  rw [SymplecticForm.perturbedFDeriv_apply, ContinuousLinearMap.comp_apply, perturbedMFDeriv_apply,
    map_sub, map_sub, map_smul, map_smul, hd, comp_apply, hKs.hamiltonianVectorField_eq,
    hKt.hamiltonianVectorField_eq, hω.mvfderiv_hamiltonianVectorField_comp hφ hsurj hform hKs',
    hω.mvfderiv_hamiltonianVectorField_comp hφ hsurj hform hKt', mvfderiv_apply_eq_mfderiv_apply]

/-- **The energy density in a symplectic chart.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`, the Floer energy density of the
coordinate map `φ ∘ u` for `ω₀` and the coordinate Hamiltonians is the Floer energy density of `u`
for `ω`. -/
theorem floerEnergyDensity_comp (hω : ω.IsNondegenerate)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z))
    (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z))) :
    ω₀.floerEnergyDensity Ks' Kt' (φ ∘ u) z = ω.floerEnergyDensity Ks Kt u z := by
  rw [SymplecticForm.floerEnergyDensity_def, floerEnergyDensity_def,
    hω.perturbedFDeriv_comp hu hφ hsurj hform hKs hKt hKs' hKt', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hform]

/-- **The Floer equation in a symplectic chart.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`, let `J'` be the structure `J` on
`T_(u z) M` read in the chart, `dφ ∘ J = J' ∘ dφ`. Then the coordinate map `φ ∘ u` solves the
Floer equation for `ω₀` and `J'` at `z` exactly when `u` solves the Floer equation for `ω` and
`J`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_iff (hω : ω.IsNondegenerate)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z))
    (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z)))
    {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V}
    (hJ : IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv Ks' Kt' (φ ∘ u) z).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap := by
  rw [hω.perturbedFDeriv_comp hu hφ hsurj hform hKs hKt hKs' hKt']
  refine ⟨fun h ↦ ?_, fun h ↦ hJ.comp h⟩
  -- The differential of `φ` is injective and intertwines `J` with `J'`.
  rw [isComplexLinearMap_stdComplexLine_iff] at h ⊢
  refine hω.injective_mvfderiv hform ?_
  have hJv := LinearMap.congr_fun hJ (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp] at h hJv ⊢
  exact h.trans hJv.symm

end TauCeti.SmoothTwoForm.IsNondegenerate
