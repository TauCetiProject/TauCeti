/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import TauCeti.Topology.Instances.Matrix

/-!
# Spectral projectors, continuity and measurability of the Hermitian functional calculus

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ` (any `RCLike` field) and a real function `f`,
Mathlib's continuous functional calculus defines the matrix `cfc f A`. Every real function is
continuous on the finite spectrum of `A`, so `cfc f A` is meaningful for arbitrary `f`. This file
relates it to the eigenspaces of `A` and studies its dependence on `A`.

*Eigenvectors and spectral projectors.* The Euclidean operator of `cfc f A` multiplies an
eigenvector of `A` with eigenvalue `μ` by `f μ`, so it is the functional calculus
`LinearMap.IsSymmetric.cfc` of the symmetric operator `Matrix.toEuclideanLin A`. For a set
`Ω ⊆ ℝ`, the Euclidean operator of the star projection `cfc (Ω.indicator 1) A` (see
`TauCeti.isStarProjection_cfc_indicator`) is therefore the orthogonal projection onto the sum
`Module.End.pointSpectralSubspace A.toEuclideanLin Ω` of the eigenspaces of `A` at eigenvalues in
`Ω`. For `Ω = [c, ∞)` this is the fixed-threshold spectral projector `P_[c,∞)(A)`, the cluster
object used for spectral subspaces in the presence of eigenvalue multiplicity.

*Continuity.* For continuous `f`, the map `A ↦ cfc f A` is continuous on the Hermitian matrices
for the entrywise topology. This is Mathlib's continuity of the isometric functional calculus in
its operator variable, which is available for matrices under the scoped `ℓ²` operator norm.

*Measurability.* For continuous `f`, the map `A ↦ cfc f A` is Borel measurable on all of
`Matrix n n 𝕜`: it is continuous on the closed set of Hermitian matrices and zero off it. Since the
spectrum of a matrix is finite, pointwise convergence `F k → f` gives `cfc (F k) A → cfc f A`, so
measurability passes to pointwise limits of continuous functions. The indicator of a closed set is
such a limit, so spectral projectors `A ↦ cfc (Ω.indicator 1) A` for closed `Ω`, in particular the
fixed-threshold projectors, are Borel measurable even though they are not continuous. Composing
with a measurable random matrix `ω ↦ A ω` gives measurability of `ω ↦ cfc f (A ω)` and of
`ω ↦ P_[c,∞)(A ω)`; no Hermitian hypothesis on `A ω` is needed for this.

## Main results

* `Matrix.IsHermitian.toEuclideanLin_cfc_apply_of_apply_eq_smul` — `cfc f A` acts by `f μ` on an
  eigenvector of `A` with eigenvalue `μ`;
* `Matrix.IsHermitian.toEuclideanLin_cfc` — the Euclidean operator of `cfc f A` is the symmetric
  functional calculus `LinearMap.IsSymmetric.cfc f` of `A.toEuclideanLin`;
* `Matrix.IsHermitian.toEuclideanLin_cfc_indicator` — the Euclidean operator of
  `cfc (Ω.indicator 1) A` is the orthogonal projection onto the point-spectral subspace
  `Module.End.pointSpectralSubspace A.toEuclideanLin Ω`;
* `TauCeti.continuousOn_matrix_cfc` — for continuous `f`, `A ↦ cfc f A` is continuous on the
  Hermitian matrices;
* `TauCeti.tendsto_matrix_cfc_fun` — pointwise convergence of functions gives convergence of
  their functional calculi at every matrix;
* `TauCeti.measurable_matrix_cfc` — for continuous `f`, `A ↦ cfc f A` is measurable;
* `TauCeti.measurable_matrix_cfc_of_tendsto` — the same for pointwise limits of continuous `f`;
* `TauCeti.measurable_matrix_cfc_indicator` — for closed `Ω`, the spectral projector
  `A ↦ cfc (Ω.indicator 1) A` is measurable.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  §§2.5 and 7.2 (the spectral theorem and functions of Hermitian matrices).
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.3
  (spectral projectors of Hermitian matrices).
-/

public section

open Filter Polynomial Topology

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The functional calculus `cfc f A` of a Hermitian matrix multiplies an eigenvector of `A`
with eigenvalue `μ` by `f μ`. -/
theorem IsHermitian.toEuclideanLin_cfc_apply_of_apply_eq_smul (hA : A.IsHermitian) (f : ℝ → ℝ)
    {μ : ℝ} {x : EuclideanSpace 𝕜 n} (hx : toEuclideanLin A x = (μ : 𝕜) • x) :
    toEuclideanLin (cfc f A) x = (f μ : 𝕜) • x := by
  obtain rfl | hx0 := eq_or_ne x 0
  · simp
  -- Replace `f` by a polynomial `q` agreeing with it on the spectrum of `A` and at `μ`.
  classical
  set s : Finset ℝ := (finite_real_spectrum (A := A)).toFinset ∪ {μ}
  set q : ℝ[X] := Lagrange.interpolate s id f
  have hq : ∀ t ∈ s, q.eval t = f t := fun t ht ↦
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) ht
  have hcfc : cfc f A = aeval A (q.map (algebraMap ℝ 𝕜)) := by
    rw [aeval_map_algebraMap, ← cfc_polynomial q A hA.isSelfAdjoint]
    exact cfc_congr fun t ht ↦ (hq t (by simp [s, ht])).symm
  have haeval : toEuclideanLin (aeval A (q.map (algebraMap ℝ 𝕜))) =
      aeval (toEuclideanLin A) (q.map (algebraMap ℝ 𝕜)) :=
    -- `toLinAlgEquiv` at the standard basis of `EuclideanSpace 𝕜 n` is `toEuclideanLin` by
    -- definition, so `aeval` commutes with `toEuclideanLin` as with any algebra homomorphism.
    (aeval_algHom_apply (toLinAlgEquiv (EuclideanSpace.basisFun n 𝕜).toBasis) A _).symm
  rw [hcfc, haeval,
    Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hx, hx0⟩]
  -- Both sides are `aeval μ q` once `f μ` is replaced by `q.eval μ`.
  rw [← hq μ (by simp [s]), ofReal_eval, eval_map_algebraMap]

/-- The Euclidean operator of the functional calculus `cfc f A` of a Hermitian matrix is the
functional calculus `LinearMap.IsSymmetric.cfc f` of the symmetric operator `A.toEuclideanLin`. -/
theorem IsHermitian.toEuclideanLin_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    toEuclideanLin (cfc f A) = (isSymmetric_toEuclideanLin_iff.mpr hA).cfc f :=
  (LinearMap.IsSymmetric.eq_cfc_iff _ f).mpr fun _ _ hx ↦
    hA.toEuclideanLin_cfc_apply_of_apply_eq_smul f hx

/-- **The spectral projector of a Hermitian matrix.** For `Ω ⊆ ℝ`, the Euclidean operator of
`cfc (Ω.indicator 1) A` is the orthogonal projection onto the sum of the eigenspaces of `A` at
eigenvalues in `Ω`. For `Ω = Set.Ici c` this is the fixed-threshold projector `P_[c,∞)(A)`. -/
theorem IsHermitian.toEuclideanLin_cfc_indicator (hA : A.IsHermitian) (Ω : Set ℝ) :
    toEuclideanLin (cfc (Ω.indicator 1) A) =
      (Module.End.pointSpectralSubspace (toEuclideanLin A) Ω).starProjection := by
  rw [hA.toEuclideanLin_cfc, LinearMap.IsSymmetric.coe_starProjection_pointSpectralSubspace]

end Matrix

namespace TauCeti

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Continuity of the Hermitian functional calculus.** For a continuous `f : ℝ → ℝ`, the map
`A ↦ cfc f A` is continuous on the Hermitian matrices. -/
theorem continuousOn_matrix_cfc {f : ℝ → ℝ} (hf : Continuous f) :
    ContinuousOn (cfc f : Matrix n n 𝕜 → Matrix n n 𝕜) {A | A.IsHermitian} := by
  -- Mathlib's continuity of `cfc` in its operator variable needs the isometric calculus, which
  -- matrices carry for the scoped `ℓ²` operator norm; that norm induces the entrywise topology.
  -- The lemma is stated over `ℝ`, so it also needs `Matrix n n 𝕜` as a normed `ℝ`-algebra; we
  -- extend the existing `ℝ`-algebra structure rather than restricting scalars, to avoid a diamond.
  open scoped Matrix.Norms.L2Operator in
  let : NormedAlgebra ℝ (Matrix n n 𝕜) :=
    { (inferInstance : Algebra ℝ (Matrix n n 𝕜)) with
      norm_smul_le r A := by
        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r A]
        exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs]) }
  exact ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) (t := {A : Matrix n n 𝕜 | A.IsHermitian})
    f univ_mem continuousOn_id (fun _ hA ↦ Matrix.IsHermitian.isSelfAdjoint hA) hf.continuousOn

/-- If `F k → f` pointwise along a filter `l`, then `cfc (F k) A → cfc f A` for every square
matrix `A`. No continuity is needed, because the spectrum of a matrix is finite. -/
theorem tendsto_matrix_cfc_fun {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hFf : ∀ t, Tendsto (fun k ↦ F k t) l (𝓝 (f t))) (A : Matrix n n 𝕜) :
    Tendsto (fun k ↦ cfc (F k) A) l (𝓝 (cfc f A)) :=
  tendsto_cfc_fun_of_finite_spectrum Matrix.finite_real_spectrum fun t _ ↦ hFf t

/-- **Measurability of the Hermitian functional calculus.** For a continuous `f : ℝ → ℝ`, the
map `A ↦ cfc f A` is Borel measurable on `Matrix n n 𝕜`. It is continuous on the closed set of
Hermitian matrices and zero elsewhere. -/
theorem measurable_matrix_cfc {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (cfc f : Matrix n n 𝕜 → Matrix n n 𝕜) := by
  classical
  have h : cfc f = {A : Matrix n n 𝕜 | A.IsHermitian}.piecewise (cfc f) 0 := by
    ext1 A
    by_cases hA : A.IsHermitian
    · simp [hA]
    · have hA' : ¬IsSelfAdjoint A := by rwa [← Matrix.isHermitian_iff_isSelfAdjoint]
      simp [hA, cfc_apply_of_not_predicate A hA']
  rw [h]
  exact (continuousOn_matrix_cfc hf).measurable_piecewise continuousOn_const
    (isClosed_eq (by fun_prop) continuous_id).measurableSet

/-- If `f : ℝ → ℝ` is a pointwise limit of continuous functions, then `A ↦ cfc f A` is Borel
measurable on `Matrix n n 𝕜`, although it need not be continuous on the Hermitian matrices. -/
theorem measurable_matrix_cfc_of_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ k, Continuous (F k)) (hFf : ∀ t, Tendsto (fun k ↦ F k t) atTop (𝓝 (f t))) :
    Measurable (cfc f : Matrix n n 𝕜 → Matrix n n 𝕜) :=
  measurable_of_tendsto_metrizable (fun k ↦ measurable_matrix_cfc (hF k))
    (tendsto_pi_nhds.2 (tendsto_matrix_cfc_fun hFf))

/-- **Measurability of spectral projectors.** For a closed set `Ω ⊆ ℝ`, the spectral projector
`A ↦ cfc (Ω.indicator 1) A` is Borel measurable on `Matrix n n 𝕜`. For `Ω = Set.Ici c` this is
the fixed-threshold projector `P_[c,∞)(A)`. -/
theorem measurable_matrix_cfc_indicator {Ω : Set ℝ} (hΩ : IsClosed Ω) :
    Measurable (cfc (Ω.indicator 1) : Matrix n n 𝕜 → Matrix n n 𝕜) := by
  -- The thickened indicators of `Ω` are continuous and tend pointwise to its indicator.
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun _ ↦ Nat.one_div_pos_of_nat
  refine measurable_matrix_cfc_of_tendsto (F := fun k t ↦ thickenedIndicator (hδ k) Ω t)
    (fun k ↦ NNReal.continuous_coe.comp (thickenedIndicator (hδ k) Ω).continuous) fun t ↦ ?_
  have h := (NNReal.continuous_coe.tendsto _).comp <| tendsto_pi_nhds.1
    (thickenedIndicator_tendsto_indicator_closure hδ tendsto_one_div_add_atTop_nhds_zero_nat Ω) t
  rw [hΩ.closure_eq] at h
  have h1 : Ω.indicator 1 t = ((Ω.indicator (fun _ ↦ (1 : NNReal)) t : NNReal) : ℝ) := by
    by_cases ht : t ∈ Ω <;> simp [ht]
  rw [h1]
  exact h

end TauCeti
