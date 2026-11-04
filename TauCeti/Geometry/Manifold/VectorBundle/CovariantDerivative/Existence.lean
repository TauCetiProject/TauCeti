/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame

/-!
# Existence of covariant derivatives

Every `C^(n+1)` real vector bundle of finite rank over a σ-compact Hausdorff smooth manifold
modelled on a finite-dimensional space carries a `C^n` covariant derivative
(`CovariantDerivative.exists_contMDiffCovariantDerivative`); in particular the type
`CovariantDerivative I F V` of covariant derivatives on a `C^1` such bundle is nonempty. Here `n`
ranges over `ℕ∞`: the derivative is built with smooth partitions of unity, so the analytic case is
not covered.

The proof is the classical one. Covariant derivatives on a vector bundle form an affine space, and
the defining conditions (additivity and the Leibniz rule at a point) are pointwise and affine in the
derivative. Hence if `∇ⁱ` is a covariant derivative over an open set `Uᵢ` and `ρ` is a partition of
unity with `tsupport ρᵢ ⊆ Uᵢ`, the locally finite sum `∑ᶠ i, ρᵢ • ∇ⁱ` is a covariant derivative on
the whole manifold (`CovariantDerivative.ofPartitionOfUnity`): at each point only the `∇ⁱ` defined
there contribute, and the coefficients sum to one, so the derivative of `ρᵢ` never enters. When
`ρ` is smooth and each `∇ⁱ` is `C^n` on `Uᵢ`, the glued derivative is `C^n`. Applying this to the
flat derivatives `TauCeti.Manifold.frameCovariantDerivative` of the local frames of the bundle
trivializations gives existence.

A covariant derivative is the basic input of the analysis of sections of a vector bundle: it
splits the first-jet sequence of the bundle, defines curvature, and gives the connection
Laplacians and the Sobolev norms of sections. The existence theorem lets these constructions be
carried out on every bundle without first exhibiting a connection.

## Main definitions and results

* `PartitionOfUnity.IsSubordinate.isCovariantDerivativeOn_finsum_smul`: a sum of local covariant
  derivatives weighted by a subordinate partition of unity on `s` is a covariant derivative on
  `s`.
* `SmoothPartitionOfUnity.IsSubordinate.contMDiffCovariantDerivativeOn_finsum_smul`: such a sum
  weighted by a smooth partition of unity is `C^n` when each local derivative is.
* `CovariantDerivative.ofPartitionOfUnity`: the global covariant derivative glued from local ones
  along a partition of unity, with `CovariantDerivative.ofPartitionOfUnity_apply` computing it
  and `CovariantDerivative.contMDiffCovariantDerivative_ofPartitionOfUnity` its regularity.
* `CovariantDerivative.exists_contMDiffCovariantDerivative`: existence of a `C^n` covariant
  derivative on a `C^(n+1)` finite-rank vector bundle, and the instance
  `CovariantDerivative.instNonempty`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, Springer, 2018,
  Proposition 4.5 (existence of connections in vector bundles).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience,
  1963, Ch. II, Theorem 2.1 (the same partition-of-unity argument for principal connections).
-/

public section

noncomputable section

open Bundle Set Function
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V]
  {ι : Type*} {U : ι → Set M}
  {cov : ι → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}

namespace PartitionOfUnity

variable {s : Set M} {ρ : PartitionOfUnity ι M s}

/-- A partition of unity reads a weighted sum of fibre elements as a finite sum over the indices
whose weight is nonzero at the point. -/
private theorem finsum_smul_eq_sum {A : Type*} [AddCommGroup A] [Module ℝ A] (x : M)
    (φ : ι → A) : ∑ᶠ i, ρ i x • φ i = ∑ i ∈ ρ.finsupport x, ρ i x • φ i :=
  (ρ.sum_finsupport_smul_eq_finsum (φ := fun i _ ↦ φ i)).symm

/-- **Gluing covariant derivatives along a partition of unity.** If `cov i` is a covariant
derivative over `U i` and `ρ` is a partition of unity on `s` subordinate to `U`, then
`∑ᶠ i, ρ i • cov i` is a covariant derivative over `s`. -/
theorem IsSubordinate.isCovariantDerivativeOn_finsum_smul (hρ : ρ.IsSubordinate U)
    (hcov : ∀ i, IsCovariantDerivativeOn F (cov i) (U i)) :
    IsCovariantDerivativeOn F (fun σ x ↦ ∑ᶠ i, ρ i x • cov i σ x) s := by
  -- Only the indices with `ρ i x ≠ 0` contribute at `x`, and `x ∈ U i` for each of them.
  have hU {x : M} {i : ι} (hi : i ∈ ρ.finsupport x) : x ∈ U i :=
    hρ i (subset_tsupport _ ((ρ.mem_finsupport x).1 hi))
  refine ⟨fun {σ σ' x} hσ hσ' _ ↦ ?_, fun {σ g x} hσ hg hx ↦ ?_⟩
  · simp only [finsum_smul_eq_sum x, ← Finset.sum_add_distrib, ← smul_add]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [(hcov i).add hσ hσ' (hU hi)]
  · simp only [finsum_smul_eq_sum x]
    calc ∑ i ∈ ρ.finsupport x, ρ i x • cov i (g • σ) x
        = ∑ i ∈ ρ.finsupport x, (g x • ρ i x • cov i σ x +
            ρ i x • (mvfderiv I g x).smulRight (σ x)) :=
          Finset.sum_congr rfl fun i hi ↦ by
            rw [(hcov i).leibniz hσ hg (hU hi), smul_add, smul_comm]
      _ = g x • ∑ i ∈ ρ.finsupport x, ρ i x • cov i σ x +
            (mvfderiv I g x).smulRight (σ x) := by
          rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul,
            ρ.sum_finsupport hx, one_smul]

end PartitionOfUnity

namespace SmoothPartitionOfUnity

variable [IsManifold I 1 M] [VectorBundle ℝ F V]

/-- A sum of `C^n` local covariant derivatives weighted by a subordinate smooth partition of unity
is `C^n`: it sends `C^(n+1)` sections to `C^n` sections of `Hom(TM, V)`. -/
theorem IsSubordinate.contMDiffCovariantDerivativeOn_finsum_smul
    {ρ : SmoothPartitionOfUnity ι I M} (hρ : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    {n : ℕ∞} (hcov : ∀ i, ContMDiffCovariantDerivativeOn F n (cov i) (U i)) :
    ContMDiffCovariantDerivativeOn F n (fun σ x ↦ ∑ᶠ i, ρ i x • cov i σ x) univ where
  contMDiff {σ} hσ := by
    rw [contMDiffOn_univ]
    refine ContMDiff.finsum_section_of_locallyFinite
      (t := fun i x ↦ ρ i x • cov i σ x) ?_ fun i ↦ ?_
    · refine ρ.locallyFinite.subset fun i x hx ↦ ?_
      exact left_ne_zero_of_smul hx
    · exact ContMDiffOn.smul_section_of_tsupport
        (((ρ i).contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn) (hU i) (hρ i)
        ((hcov i).contMDiff (hσ.mono (subset_univ _)))

end SmoothPartitionOfUnity

namespace CovariantDerivative

/-- The covariant derivative glued from covariant derivatives `cov i` over the sets `U i` along a
partition of unity `ρ` subordinate to `U`: it is `∑ᶠ i, ρ i • cov i`. -/
def ofPartitionOfUnity (ρ : PartitionOfUnity ι M) (hρ : ρ.IsSubordinate U)
    (hcov : ∀ i, IsCovariantDerivativeOn F (cov i) (U i)) : CovariantDerivative I F V where
  toFun σ x := ∑ᶠ i, ρ i x • cov i σ x
  isCovariantDerivativeOnUniv := hρ.isCovariantDerivativeOn_finsum_smul hcov

@[simp]
theorem ofPartitionOfUnity_apply (ρ : PartitionOfUnity ι M) (hρ : ρ.IsSubordinate U)
    (hcov : ∀ i, IsCovariantDerivativeOn F (cov i) (U i)) (σ : Π x : M, V x) (x : M) :
    ofPartitionOfUnity ρ hρ hcov σ x = ∑ᶠ i, ρ i x • cov i σ x :=
  (rfl)

variable [VectorBundle ℝ F V]

/-- The covariant derivative glued along a smooth partition of unity from `C^n` local covariant
derivatives over open sets is `C^n`. -/
theorem contMDiffCovariantDerivative_ofPartitionOfUnity [IsManifold I 1 M]
    {ρ : SmoothPartitionOfUnity ι I M}
    (hρ : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ i, IsCovariantDerivativeOn F (cov i) (U i)) {n : ℕ∞}
    (hcov' : ∀ i, ContMDiffCovariantDerivativeOn F n (cov i) (U i)) :
    ContMDiffCovariantDerivative (ofPartitionOfUnity ρ.toPartitionOfUnity hρ hcov) n :=
  ⟨hρ.contMDiffCovariantDerivativeOn_finsum_smul hU hcov'⟩

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [FiniteDimensional ℝ F]

/-- **Existence of covariant derivatives.** A `C^k` real vector bundle of finite rank over a
σ-compact Hausdorff smooth manifold modelled on a finite-dimensional space carries a `C^n`
covariant derivative whenever `n + 1 ≤ k`. -/
theorem exists_contMDiffCovariantDerivative {n : ℕ∞} {k : ℕ∞ω} [ContMDiffVectorBundle k F V I]
    (hk : n + 1 ≤ k) : ∃ cov : CovariantDerivative I F V, ContMDiffCovariantDerivative cov n := by
  have : ContMDiffVectorBundle 1 F V I := .of_le (le_add_self.trans hk)
  let b := Module.Basis.ofVectorSpace ℝ F
  -- The flat derivative of the frame of the preferred trivialization at each point.
  let e (x : M) := trivializationAt F V x
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun x ↦ (e x).baseSet) (fun x ↦ (e x).open_baseSet)
    fun x _ ↦ mem_iUnion.2 ⟨x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  exact ⟨_, contMDiffCovariantDerivative_ofPartitionOfUnity hρ (fun x ↦ (e x).open_baseSet)
    (fun x ↦ TauCeti.Manifold.isCovariantDerivativeOn_frameCovariantDerivative b)
    fun x ↦ TauCeti.Manifold.contMDiffCovariantDerivativeOn_frameCovariantDerivative b
      (m := ∞) (by exact_mod_cast le_top) hk⟩

/-- A `C^1` real vector bundle of finite rank over a σ-compact Hausdorff smooth manifold modelled
on a finite-dimensional space carries a covariant derivative. -/
instance instNonempty [ContMDiffVectorBundle 1 F V I] : Nonempty (CovariantDerivative I F V) :=
  let ⟨cov, _⟩ := exists_contMDiffCovariantDerivative (n := 0) (k := 1) (by simp)
  ⟨cov⟩

end CovariantDerivative
