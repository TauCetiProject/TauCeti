/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Localized
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# Localized Hamiltonians on manifolds

Smooth parameter-dependent Hamiltonians with compact support in any neighborhood of `(p, x)`
realize arbitrary Hamiltonian vectors at that point. Only invertibility of the flat map at
`x` is needed; closedness of the two-form, compactness of the target and nonconstancy of a
curve through `x` are not required. The parameter can itself range over a manifold.

Adding a real multiple of such a Hamiltonian gives an exact affine change of the Hamiltonian
vector at `(p, x)`, and hence realizes the prescribed parameter derivative. Localization in the
product separates distinct domain points even when their target images coincide. These are
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
  refine ⟨Function.curry f, hf, hfc, hfU, hf0, ?_⟩
  have hslice : mvfderiv I (Function.curry f p) x = σ.flat x v := by
    have hd := mvfderiv_comp_of_eq (hf.mdifferentiable (by simp)).mdifferentiableAt
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (rfl : (p, x) = (p, x))
    dsimp only [id_eq] at hd
    rw [hfd, mfderiv_prod_right] at hd
    exact hd.trans (by rfl)
  rw [hamiltonianVectorField_def, hslice]
  exact hσ.inverse_apply_self v

/-- A localized smooth Hamiltonian gives an exact affine perturbation of the Hamiltonian
vector at a chosen parameter/target point. This remains valid at constant curves. -/
theorem exists_contMDiff_hamiltonianVectorField_add_smul_eq (p : P) (x : M)
    (hσ : (σ.flat x).IsInvertible) (v : TangentSpace I x) (H : P → M → ℝ)
    (hH : MDifferentiableAt I 𝓘(ℝ) (H p) x) {U : Set (P × M)} (hU : U ∈ 𝓝 (p, x)) :
    ∃ K : P → M → ℝ, ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ U ∧
      K p x = 0 ∧ ∀ r : ℝ,
        σ.hamiltonianVectorField (H p + r • K p) x =
          σ.hamiltonianVectorField (H p) x + r • v := by
  obtain ⟨K, hK, hKc, hKU, hK0, hKv⟩ :=
    exists_contMDiff_hamiltonianVectorField_eq (J := J) p x hσ v hU
  have hKd : MDifferentiableAt I 𝓘(ℝ) (K p) x :=
    ((hK.mdifferentiable (by simp)).comp
      (mdifferentiable_const.prodMk mdifferentiable_id)).mdifferentiableAt
  refine ⟨K, hK, hKc, hKU, hK0, fun r => ?_⟩
  rw [hamiltonianVectorField_add hH (hKd.const_smul r),
    hamiltonianVectorField_const_smul, hKv]

/-- Localized Hamiltonian variations realize every parameter derivative of the Hamiltonian
vector at a fixed target point. The derivative is read in the model of that tangent fiber and
is independent of the parameter value. -/
theorem exists_contMDiff_hasDerivAt_hamiltonianVectorField (p : P) (x : M)
    (hσ : (σ.flat x).IsInvertible) (v : TangentSpace I x) (H : P → M → ℝ)
    (hH : MDifferentiableAt I 𝓘(ℝ) (H p) x) {U : Set (P × M)} (hU : U ∈ 𝓝 (p, x)) :
    ∃ K : P → M → ℝ, ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ U ∧
      K p x = 0 ∧ ∀ r : ℝ, HasDerivAt
        (fun t : ℝ => (σ.hamiltonianVectorField (H p + t • K p) x : E)) v r := by
  obtain ⟨K, hK, hKc, hKU, hK0, hKv⟩ :=
    exists_contMDiff_hamiltonianVectorField_add_smul_eq (J := J) p x hσ v H hH hU
  refine ⟨K, hK, hKc, hKU, hK0, fun r => ?_⟩
  -- Work in the model explicitly: instance search does not put a norm on the fiber synonym.
  let w : E := σ.hamiltonianVectorField (H p) x
  let v' : E := v
  have hd : HasDerivAt (fun t : ℝ => w + t • v') v' r := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id r).smul_const v').const_add w
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hKv)

end TauCeti.SmoothTwoForm
