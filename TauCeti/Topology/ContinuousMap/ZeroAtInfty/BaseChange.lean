/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Coefficient extension of operators on model spaces

A bounded unital ring homomorphism `f : R →+* S` extends the matrix of an operator
`C₀(J, R) →L[R] C₀(I, R)` coefficientwise to an operator over `S`. Null columns and a
uniform entry bound ensure that the extended matrix defines a continuous linear map.
The construction respects identities, addition, scalar multiplication and composition,
including composition of coefficient homomorphisms. Its matrix characterizes it uniquely.
Over Tate target scalars it is Lipschitz in operator norm, so it preserves operator-norm sums
and sends the closure of the polynomials in an endomorphism `u` into the closure of the
polynomials in its extension.

The coefficient rings need not have a common ground field. Tate data on the source supplies
the entry bound; the target need only be complete and ultrametric.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {I J K R S : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [TopologicalSpace K] [DiscreteTopology K] [DecidableEq K]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- Extend the matrix coefficients of an operator along a bounded ring homomorphism.
Boundedness is a proposition, so the construction is independent of its witness. -/
noncomputable def mapCoeffs (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) : C₀(J, S) →L[S] C₀(I, S) :=
  (u.matrixCoeff.map f).toZeroAtInftyCLM
    (fun j ↦ by
      obtain ⟨C, hC⟩ := hf
      simpa only [Function.comp_def, map_zero, Matrix.map_apply] using
        ((AddMonoidHomClass.continuous_of_bound f C hC).tendsto 0).comp
        (u.tendsto_matrixCoeff_cofinite j))
    (by
      obtain ⟨C, hC⟩ := hf
      exact ⟨C * ‖u‖, fun i j ↦ (hC _).trans
        (mul_le_mul_of_nonneg_left (u.norm_matrixCoeff_le i j) C.coe_nonneg)⟩)

/-- The extended operator has the coefficientwise extended matrix. -/
@[simp]
theorem matrixCoeff_mapCoeffs (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).matrixCoeff = u.matrixCoeff.map f := by
  simp [mapCoeffs]

/-- Matrix coefficients uniquely determine coefficient extension. -/
theorem eq_mapCoeffs_iff (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (v : C₀(J, S) →L[S] C₀(I, S)) :
    v = u.mapCoeffs f hf ↔ v.matrixCoeff = u.matrixCoeff.map f := by
  rw [← matrixCoeff_inj, matrixCoeff_mapCoeffs]

/-- The norm of an extended matrix entry is bounded by the homomorphism bound times
its original norm. -/
theorem norm_matrixCoeff_mapCoeffs_le (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) (i : I) (j : J) :
    ‖(u.mapCoeffs f ⟨C, hf⟩).matrixCoeff i j‖ ≤ C * ‖u.matrixCoeff i j‖ := by
  simpa using hf (u.matrixCoeff i j)

/-- A norm bound for coefficient extension. -/
theorem ringOpNorm_mapCoeffs_le (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) : ‖u.mapCoeffs f ⟨C, hf⟩‖ ≤ C * ‖u‖ := by
  apply ringOpNorm_le_of_forall_norm_matrixCoeff_le _ (by positivity)
  intro i j
  exact (u.norm_matrixCoeff_mapCoeffs_le f C hf i j).trans
    (mul_le_mul_of_nonneg_left (u.norm_matrixCoeff_le i j) C.coe_nonneg)

@[simp]
theorem mapCoeffs_zero (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (0 : C₀(J, R) →L[R] C₀(I, R)).mapCoeffs f hf = 0 := by
  apply matrixCoeff_injective
  ext i j
  simp

@[simp]
theorem mapCoeffs_add (u v : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u + v).mapCoeffs f hf = u.mapCoeffs f hf + v.mapCoeffs f hf := by
  apply matrixCoeff_injective
  ext i j
  simp

@[simp]
theorem mapCoeffs_neg (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (-u).mapCoeffs f hf = -u.mapCoeffs f hf := by
  apply matrixCoeff_injective
  ext i j
  simp

@[simp]
theorem mapCoeffs_sub (u v : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u - v).mapCoeffs f hf = u.mapCoeffs f hf - v.mapCoeffs f hf := by
  apply matrixCoeff_injective
  ext i j
  simp

@[simp]
theorem mapCoeffs_sum {ι : Type*} (s : Finset ι) (u : ι → C₀(J, R) →L[R] C₀(I, R))
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (∑ k ∈ s, u k).mapCoeffs f hf = ∑ k ∈ s, (u k).mapCoeffs f hf := by
  apply matrixCoeff_injective
  ext i j
  simp [Matrix.sum_apply]

@[simp]
theorem mapCoeffs_smul (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (r : R) :
    (r • u).mapCoeffs f hf = f r • u.mapCoeffs f hf := by
  apply matrixCoeff_injective
  ext i j
  simp

@[simp]
theorem mapCoeffs_one [DecidableEq I] (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (1 : C₀(I, R) →L[R] C₀(I, R)).mapCoeffs f hf = 1 := by
  apply matrixCoeff_injective
  ext i j
  simp [Matrix.one_apply]

/-- Coefficient extension preserves composition of operators. -/
@[simp]
theorem mapCoeffs_comp (u : C₀(J, R) →L[R] C₀(I, R))
    (v : C₀(K, R) →L[R] C₀(J, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.comp v).mapCoeffs f hf = (u.mapCoeffs f hf).comp (v.mapCoeffs f hf) := by
  apply matrixCoeff_injective
  ext i k
  obtain ⟨C, hC⟩ := hf
  have hsum := (u.hasSum_matrixCoeff_comp v i k).map f
    (AddMonoidHomClass.continuous_of_bound f C hC)
  have hsum' := (u.mapCoeffs f ⟨C, hC⟩).hasSum_matrixCoeff_comp (v.mapCoeffs f ⟨C, hC⟩) i k
  simp only [matrixCoeff_mapCoeffs, Matrix.map_apply] at hsum'
  rw [matrixCoeff_mapCoeffs, Matrix.map_apply]
  exact hsum.unique (by simpa only [Function.comp_def, map_mul] using hsum')

/-- Coefficient extension is multiplicative on endomorphisms. -/
@[simp]
theorem mapCoeffs_mul (u v : C₀(J, R) →L[R] C₀(J, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u * v).mapCoeffs f hf = u.mapCoeffs f hf * v.mapCoeffs f hf :=
  mapCoeffs_comp u v f hf

@[simp]
theorem mapCoeffs_pow (u : C₀(J, R) →L[R] C₀(J, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (n : ℕ) :
    (u ^ n).mapCoeffs f hf = u.mapCoeffs f hf ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mapCoeffs_mul, ih, pow_succ]

section Topology

variable [TauCeti.NormedRing.IsTate S]

/-- Coefficient extension along a homomorphism with bound `C` is `C`-Lipschitz in operator
norm. -/
theorem lipschitzWith_mapCoeffs (f : R →+* S) (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    LipschitzWith C fun u : C₀(J, R) →L[R] C₀(I, R) ↦ u.mapCoeffs f ⟨C, hf⟩ :=
  LipschitzWith.of_dist_le_mul fun u v ↦ by
    simpa only [dist_eq_norm, ← mapCoeffs_sub] using ringOpNorm_mapCoeffs_le (u - v) f C hf

/-- Coefficient extension is continuous in operator norm. -/
theorem continuous_mapCoeffs (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    Continuous fun u : C₀(J, R) →L[R] C₀(I, R) ↦ u.mapCoeffs f hf := by
  obtain ⟨C, hC⟩ := hf
  exact (lipschitzWith_mapCoeffs f C hC).continuous

/-- Coefficient extension preserves operator-norm sums. -/
theorem _root_.HasSum.mapCoeffs {ι : Type*} {u : ι → C₀(J, R) →L[R] C₀(I, R)}
    {v : C₀(J, R) →L[R] C₀(I, R)} (h : HasSum u v) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    HasSum (fun k ↦ (u k).mapCoeffs f hf) (v.mapCoeffs f hf) := by
  simpa only [HasSum, Function.comp_def, mapCoeffs_sum] using
    ((continuous_mapCoeffs f hf).tendsto v).comp h

/-- Coefficient extension sends the operator-norm closure of the polynomials in `u` into the
closure of the polynomials in the extension of `u`. -/
theorem mapCoeffs_mem_closure_adjoin {u v : C₀(J, R) →L[R] C₀(J, R)} (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hv : v ∈ closure (Algebra.adjoin R {u} : Set (C₀(J, R) →L[R] C₀(J, R)))) :
    v.mapCoeffs f hf ∈
      closure (Algebra.adjoin S {u.mapCoeffs f hf} : Set (C₀(J, S) →L[S] C₀(J, S))) := by
  refine map_mem_closure (continuous_mapCoeffs f hf) hv fun w hw ↦ ?_
  simp only [SetLike.mem_coe]
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    exact Algebra.self_mem_adjoin_singleton S _
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, mapCoeffs_smul, mapCoeffs_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _
  | add x y _ _ hx hy =>
    rw [mapCoeffs_add]
    exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    rw [mapCoeffs_mul]
    exact Subalgebra.mul_mem _ hx hy

end Topology

section Identity

variable [IsUltrametricDist R] [CompleteSpace R]

/-- Extension along the identity homomorphism is the original operator. -/
@[simp]
theorem mapCoeffs_id (u : C₀(J, R) →L[R] C₀(I, R))
    (hf : ∃ C : ℝ≥0, ∀ r : R, ‖(RingHom.id R) r‖ ≤ C * ‖r‖) :
    u.mapCoeffs (RingHom.id R) hf = u := by
  apply matrixCoeff_injective
  ext i j
  simp

end Identity

/-- Successive coefficient extensions agree with extension along the composite homomorphism. -/
theorem mapCoeffs_mapCoeffs [TauCeti.NormedRing.IsTate S]
    {T : Type*} [NormedCommRing T] [IsUltrametricDist T] [CompleteSpace T]
    (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S) (g : S →+* T)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hg : ∃ D : ℝ≥0, ∀ s, ‖g s‖ ≤ D * ‖s‖)
    (hgf : ∃ E : ℝ≥0, ∀ r, ‖(g.comp f) r‖ ≤ E * ‖r‖) :
    (u.mapCoeffs f hf).mapCoeffs g hg = u.mapCoeffs (g.comp f) hgf := by
  apply matrixCoeff_injective
  ext i j
  simp

end ContinuousLinearMap
