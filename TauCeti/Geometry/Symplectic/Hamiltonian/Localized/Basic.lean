/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Manifold
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Localized Hamiltonians with prescribed vector field

A Hamiltonian depending smoothly on a finite-dimensional parameter can realize any prescribed
Hamiltonian vector at a single parameter/target point, while having compact support in any
neighborhood of that point. The Hamiltonian itself can be chosen to vanish at that point.

This supplies localized coefficient variations for inhomogeneous Cauchy–Riemann equations.
Localization is in the product of the parameter and target spaces, so distinct domain points
can be separated even when their target images coincide. This specializes the manifold
construction to a constant symplectic form; it is not a transversality theorem.

This is the vector-space specialization of the manifold realization theorem, applied to the
constant smooth two-form associated to `ω`.

Along a map `u` from the parameter space that is continuous on a set `Ω`, the vector fields
`z ↦ ρ(z) v` with `ρ` a test function supported in `Ω` are realized at once, as
`z ↦ X_{K z}(u z)` for a single smooth compactly supported `K` localized near the graph of `u`
(`TauCeti.SymplecticForm.exists_contDiff_hamiltonianVectorField_comp_eq_smul`). Here `K` is
`ρ(z) ω(v, x)` multiplied by a cutoff equal to `1` near that graph.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on localized Hamiltonian perturbations in the universal Cauchy–Riemann equation.
-/

public section

open Set Topology Manifold Function

namespace TauCeti.SymplecticForm

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Any vector is the Hamiltonian vector of a smooth, compactly supported parameter-dependent
Hamiltonian localized in a prescribed neighborhood of `(p, x)`. Its value at `(p, x)` is zero.
No condition on the derivative of a map through `(p, x)` is required. -/
theorem exists_contDiff_hamiltonianVectorField_eq (ω : SymplecticForm V)
    (p : P) (x v : V) {U : Set (P × V)} (hU : U ∈ 𝓝 (p, x)) :
    ∃ K : P → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ U ∧
      K p x = 0 ∧ ω.hamiltonianVectorField (K p) x = v := by
  obtain ⟨K, hK, hKc, hKU, hK0, hKv⟩ :=
    SmoothTwoForm.exists_contMDiff_hamiltonianVectorField_eq (J := 𝓘(ℝ, P))
      (σ := ω.constSmooth) p x ((isNondegenerate_constSmooth ω).isInvertible_flat x) v hU
  refine ⟨K, ?_, hKc, hKU, hK0, ?_⟩
  · exact contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp hK)
  · rw [hamiltonianVectorField_constSmooth] at hKv
    exact hKv

/-- Along a map `u` continuous on a set `Ω` of parameters, every vector field of the form
`z ↦ ρ(z) v`, for a test function `ρ` supported in `Ω` and a constant vector `v`, is realized as
`z ↦ X_{δK z}(u z)` by a smooth Hamiltonian variation `δK`. The variation has compact support in
the product of the parameter space and the target, inside any prescribed open neighbourhood `U` of
the graph of `u` over `Ω`. -/
theorem exists_contDiff_hamiltonianVectorField_comp_eq_smul (ω : SymplecticForm V)
    {Ω : Set P} {u : P → V} (hu : ContinuousOn u Ω) {U : Set (P × V)} (hU : IsOpen U)
    (hΩU : ∀ z ∈ Ω, (z, u z) ∈ U) {ρ : P → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hρΩ : tsupport ρ ⊆ Ω) (v : V) :
    ∃ δK : P → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) ∧ HasCompactSupport (uncurry δK) ∧
      tsupport (uncurry δK) ⊆ U ∧ ∀ z, ω.hamiltonianVectorField (δK z) (u z) = ρ z • v := by
  -- The graph of `u` over the support of `ρ` is a compact subset of `U`.
  set C : Set (P × V) := (fun z ↦ (z, u z)) '' tsupport ρ
  have hC : IsCompact C :=
    hρc.isCompact.image_of_continuousOn
      ((continuousOn_id.prodMk hu).mono hρΩ)
  have hCU : C ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hΩU z (hρΩ hz)
  -- A smooth cutoff equal to `1` near this graph, with compact support in `U`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ := hC.exists_contDiff_cutoff hU hCU
  let ℓ : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ω.toBilinForm v)
  -- The variation is `χ` times the smooth function `(z, x) ↦ ρ z * ℓ x`.
  have hδK : uncurry (fun z x ↦ ρ z * (χ (z, x) * ℓ x)) =
      χ * fun p : P × V ↦ ρ p.1 * ℓ p.2 := by
    ext ⟨z, x⟩
    simp only [uncurry_apply_pair, Pi.mul_apply]
    ring
  refine ⟨fun z x ↦ ρ z * (χ (z, x) * ℓ x), ?_, ?_, ?_, fun z ↦ ?_⟩
  · exact (hρ.comp contDiff_fst).mul (hχ.mul (ℓ.contDiff.comp contDiff_snd))
  · rw [hδK]
    exact hχc.mul_right
  · rw [hδK]
    exact (tsupport_mul_subset_left).trans hχU
  · by_cases hz : z ∈ tsupport ρ
    · -- Near `u z`, the cutoff is `1` and the variation is the linear Hamiltonian `ρ z • ω v`.
      have hmem : (z, u z) ∈ C := mem_image_of_mem _ hz
      have hev : ∀ᶠ x in 𝓝 (u z), χ (z, x) = 1 :=
        ((continuous_const.prodMk continuous_id).tendsto (u z)).eventually
          (mem_interior_iff_mem_nhds.mp (hχ1 hmem))
      have heq : (fun x ↦ ρ z * (χ (z, x) * ℓ x)) =ᶠ[𝓝 (u z)] fun x ↦ ρ z * ω v x :=
        hev.mono fun x hx ↦ by simp only [hx, one_mul, ℓ, LinearMap.coe_toContinuousLinearMap']
      -- The Hamiltonian vector field depends only on the germ, by the locality lemma for the
      -- constant smooth two-form of `ω`.
      rw [← hamiltonianVectorField_constSmooth, heq.hamiltonianVectorField_eq,
        hamiltonianVectorField_constSmooth, hamiltonianVectorField_const_mul,
        hamiltonianVectorField_contraction]
    · simp [image_eq_zero_of_notMem_tsupport hz]

end TauCeti.SymplecticForm
