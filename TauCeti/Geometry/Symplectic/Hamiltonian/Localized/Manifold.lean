/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Localized
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Localized Hamiltonians on manifolds

Smooth parameter-dependent Hamiltonians with compact support in any neighborhood of `(p, x)`
realize arbitrary Hamiltonian vectors at that point. Only invertibility of the flat map at
`x` is needed; closedness of the two-form and compactness of the target are not required.
The parameter can itself range over a manifold.

Adding a real multiple of such a Hamiltonian gives an exact affine change of the Hamiltonian
vector at `(p, x)`, and hence realizes the prescribed derivative in that real coefficient via
`TauCeti.SmoothTwoForm.hasDerivAt_hamiltonianVectorField_add_smul`. Localization in the product
separates distinct domain points even when their target images coincide. These are
pointwise coefficient directions, not surjectivity or regularity theorems for a curve operator.

The construction uses `TauCeti.exists_contMDiff_hasCompactSupport_mvfderiv_eq` on the product
manifold, with differential zero in the parameter direction and `σ_x(v, ·)` in the target
direction.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on localized Hamiltonian variations of the inhomogeneous Cauchy–Riemann equation.
-/

public noncomputable section

open Set Topology Manifold
open scoped ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M Q G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [TopologicalSpace G] {J : ModelWithCorners ℝ Q G}
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold J ∞ P] [T2Space P]
  {σ : SmoothTwoForm I M}

/-- A compactly supported smooth family of Hamiltonians realizes any vector at `(p, x)` and
vanishes there. Support can be confined to any neighborhood in the parameter/target product.
The two-form need only have invertible flat at the chosen target point. -/
theorem exists_contMDiff_hamiltonianVectorField_eq (p : P) (x : M)
    (hσ : (σ.flat x).IsInvertible) (v : TangentSpace I x)
    {U : Set (P × M)} (hU : U ∈ 𝓝 (p, x)) :
    ∃ K : P → M → ℝ, ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ U ∧
      K p x = 0 ∧ σ.hamiltonianVectorField (K p) x = v := by
  let L : E →L[ℝ] ℝ := σ.flat x v
  obtain ⟨f, hf, hfc, hfU, hf0, hfd⟩ :=
    exists_contMDiff_hasCompactSupport_mvfderiv_eq (I := J.prod I) (p, x) (0 : ℝ)
      (L.comp (ContinuousLinearMap.snd ℝ Q E)) hU
  -- Uncurrying `Function.curry f` is definitionally `f` by product eta, so the support and
  -- smoothness witnesses apply unchanged.
  refine ⟨Function.curry f, hf, hfc, hfU, hf0, ?_⟩
  have hslice : mvfderiv I (Function.curry f p) x = σ.flat x v := by
    rw [mvfderiv_curry_right p x (hf.mdifferentiable (by simp)).mdifferentiableAt, hfd]
    ext w
    -- Compute in the model first: `simp` cannot infer the model instances from a tangent
    -- synonym. Its underlying vector is unchanged when we apply this identity to `w`.
    have hproj (u : E) :
        L ((ContinuousLinearMap.snd ℝ Q E) ((ContinuousLinearMap.inr ℝ Q E) u)) = L u := by
      simp
    exact hproj w
  rw [hamiltonianVectorField_def, hslice]
  exact hσ.inverse_apply_self v

end TauCeti.SmoothTwoForm
