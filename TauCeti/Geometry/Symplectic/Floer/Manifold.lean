/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Energy
public import TauCeti.Geometry.Symplectic.Floer.Energy

/-!
# The Floer energy identity for manifold targets

For a map `u : ℝ × ℝ → M` and a Hamiltonian one-form `K = Ks ds + Kt dt`, the
perturbed derivative takes values in the actual tangent space `T_(u z) M`. Its symplectic
area density satisfies

`ω(du - X_K) = ω(du) + d(K(u)) - R_K(u)`.

Here `R_K = ∂s Kt - ∂t Ks - {Ks, Kt}` uses the intrinsic Hamiltonian vector fields,
with convention `ι_(X_H) ω = dH`. The identity holds for differentiable maps and jointly
differentiable Hamiltonians on the domain times the manifold. Neither closedness of the
two-form nor the Floer equation is needed for this pointwise identity. For solutions of
the equation the density is nonnegative under tameness, and is half the standard quadratic
energy density. The almost complex structure may be chosen independently at each domain
point, as is needed for domain-dependent perturbations.

This is the local-coordinate-domain energy identity for arbitrary manifold targets, not
a compactness theorem or an identity involving caps at punctured ends. On a vector-space
target with constant form it recovers the vector-space definitions.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian perturbations, curvature, and the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8.
-/

public noncomputable section

open Function
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The curvature `∂s Kt - ∂t Ks - {Ks, Kt}` of a Hamiltonian one-form with manifold target. -/
def hamiltonianCurvature (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (z : ℝ × ℝ) (x : M) : ℝ :=
  fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal -
    fderiv ℝ (fun w ↦ Ks w x) z stdComplexLineImag - ω.poissonBracket (Ks z) (Kt z) x

/-- The defining curvature formula, separating domain derivatives and target Poisson bracket. -/
theorem hamiltonianCurvature_def (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature Ks Kt z x =
      fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ Ks w x) z stdComplexLineImag - ω.poissonBracket (Ks z) (Kt z) x :=
  (rfl)

/-- The intrinsic perturbed derivative `du - X_K`, valued in `T_(u z) M`.
As with `mfderiv`, using this as an actual differential requires differentiability of `u`. -/
def perturbedMFDeriv (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] TangentSpace I (u z) :=
  -- On the model domain the tangent space is definitionally `ℝ × ℝ`; the type
  -- annotation supplies this identification before forming differences of maps.
  let du : ℝ × ℝ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z
  du - (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Ks z) (u z)) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Kt z) (u z))

/-- Evaluation of the perturbed derivative on a domain tangent vector. -/
theorem perturbedMFDeriv_apply (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z v : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z v = mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v -
      v.1 • ω.hamiltonianVectorField (Ks z) (u z) -
      v.2 • ω.hamiltonianVectorField (Kt z) (u z) :=
  (rfl)

/-- The real-coordinate component is `∂s u - X_(Ks)`. -/
@[simp]
theorem perturbedMFDeriv_apply_stdComplexLineReal (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) := by
  simp [perturbedMFDeriv_apply]

/-- The imaginary-coordinate component is `∂t u - X_(Kt)`. -/
@[simp]
theorem perturbedMFDeriv_apply_stdComplexLineImag (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) := by
  simp [perturbedMFDeriv_apply]

/-- The symplectic area density of `du - X_K` for a manifold target. -/
def floerEnergyDensity (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) : ℝ :=
  SmoothBundleForm.eval₂ ω (u z) (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
    (ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag)

/-- Floer energy density is the two-form evaluated on the two perturbed coordinate derivatives. -/
theorem floerEnergyDensity_def (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.floerEnergyDensity Ks Kt u z =
      SmoothBundleForm.eval₂ ω (u z) (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
        (ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag) :=
  (rfl)

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {u : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- The pointwise energy identity for a manifold target: symplectic area plus the exterior
derivative of `K(u)`, minus Hamiltonian curvature. -/
theorem IsNondegenerate.floerEnergyDensity_eq [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hKs : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Ks) (z, u z))
    (hKt : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Kt) (z, u z)) :
    ω.floerEnergyDensity Ks Kt u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) +
      (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) -
      ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- Apply the manifold chain rule along the graph, then split the total derivative
  -- into its domain and target slices using Mathlib's product derivative formula.
  have hgraph (K : ℝ × ℝ → M → ℝ)
      (hK : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry K) (z, u z))
      (v : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ K w (u w)) z v =
        fderiv ℝ (fun w ↦ K w (u z)) z v +
          mvfderiv I (K z) (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v) := by
    have hc := mvfderiv_comp_apply z hK (mdifferentiableAt_id.prodMk hu)
      ((NormedSpace.fromTangentSpace z).symm v)
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hc
    -- `erw` allows the model-space tangent normed instances to be identified
    -- while computing the differential of the graph.
    erw [mfderiv_prodMk mdifferentiableAt_id hu, mfderiv_id] at hc
    erw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_prod_eq_add_apply hK,
      mfderiv_eq_fderiv] at hc
    -- The remaining model tangent identifications and product evaluations preserve
    -- the underlying vectors definitionally.
    exact hc
  rw [floerEnergyDensity_def, hamiltonianCurvature_def, poissonBracket_def,
    perturbedMFDeriv_apply_stdComplexLineReal, perturbedMFDeriv_apply_stdComplexLineImag,
    hgraph Kt hKt, hgraph Ks hKs]
  -- The Hamiltonian contractions are precisely the target terms of the chain rule.
  have hs := hω.eval₂_hamiltonianVectorField (Ks z) (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)
  have ht : SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (ω.hamiltonianVectorField (Kt z) (u z)) =
        -mvfderiv I (Kt z) (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal) := by
    rw [SmoothBundleForm.eval₂_swap, hω.eval₂_hamiltonianVectorField]
  simp only [← SmoothForm.bilinFormAt_apply, map_sub, LinearMap.sub_apply] at hs ht ⊢
  rw [hs, ht]
  ring

/-- On a solution the density is half the standard quadratic energy density of the perturbed
derivative. The almost complex structure here is a structure on a single tangent fiber. -/
theorem floerEnergyDensity_eq_stdComplexLineEnergyDensity_div_two
    {J : AlmostComplexStructure (TangentSpace I (u z))}
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) (hω : ω.IsNondegenerate) :
    ω.floerEnergyDensity Ks Kt u z =
      (hω.symplecticFormAt (u z)).stdComplexLineEnergyDensity J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap / 2 := by
  rw [h.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm]
  simp only [floerEnergyDensity_def, IsNondegenerate.symplecticFormAt_apply,
    ContinuousLinearMap.coe_coe]
  ring

/-- A Floer solution has nonnegative energy density for a tamed structure on the target fiber. -/
theorem floerEnergyDensity_nonneg {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hω : ω.IsNondegenerate) (hJ : (hω.symplecticFormAt (u z)).Tames J)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    0 ≤ ω.floerEnergyDensity Ks Kt u z := by
  simpa only [floerEnergyDensity_def, IsNondegenerate.symplecticFormAt_apply,
    ContinuousLinearMap.coe_coe] using
      h.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg hJ

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A constant smooth two-form has the same Hamiltonian curvature as the vector-space form. -/
@[simp]
theorem hamiltonianCurvature_constSmooth (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (z : ℝ × ℝ) (x : V) :
    ω.constSmooth.hamiltonianCurvature Ks Kt z x = ω.hamiltonianCurvature Ks Kt z x := by
  rw [SmoothTwoForm.hamiltonianCurvature_def, hamiltonianCurvature_def,
    poissonBracket_constSmooth]

/-- Under the canonical target tangent identification the intrinsic perturbed derivative
for a constant form is the vector-space perturbed derivative. -/
theorem perturbedMFDeriv_constSmooth_apply (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z v : ℝ × ℝ) :
    NormedSpace.fromTangentSpace (u z) (ω.constSmooth.perturbedMFDeriv Ks Kt u z v) =
      ω.perturbedFDeriv Ks Kt u z v := by
  rw [NormedSpace.fromTangentSpace_apply, SmoothTwoForm.perturbedMFDeriv_apply,
    perturbedFDeriv_apply, hamiltonianVectorField_constSmooth, hamiltonianVectorField_constSmooth]
  -- The source and target tangent identifications are identities on a model space.
  rw [mfderiv_eq_fderiv]
  rfl

/-- The intrinsic energy density for a constant form agrees with the vector-space density. -/
@[simp]
theorem floerEnergyDensity_constSmooth (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.constSmooth.floerEnergyDensity Ks Kt u z = ω.floerEnergyDensity Ks Kt u z := by
  rw [SmoothTwoForm.floerEnergyDensity_def, floerEnergyDensity_def,
    fromTangentSpace_constSmooth_apply, perturbedMFDeriv_constSmooth_apply,
    perturbedMFDeriv_constSmooth_apply]

end TauCeti.SymplecticForm
