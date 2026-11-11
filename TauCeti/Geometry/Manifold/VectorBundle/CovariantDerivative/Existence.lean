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
(`CovariantDerivative.exists_contMDiffCovariantDerivative`). Here `n` ranges over `ℕ∞`: the
derivative is built with smooth partitions of unity, so the analytic case is not covered.
Separately, using topological partitions of unity, the type `CovariantDerivative I F V` of
covariant derivatives on a `C^1` finite-rank bundle over any paracompact Hausdorff manifold is
nonempty (`CovariantDerivative.instNonempty`).

The proof is the classical one. Covariant derivatives on a vector bundle form an affine space, and
the defining conditions (additivity and the Leibniz rule at a point) are pointwise and affine in the
derivative. Hence if `∇ⁱ` is a covariant derivative over an open set `Uᵢ` and `ρ` is a partition of
unity with `tsupport ρᵢ ⊆ Uᵢ`, the locally finite sum `∑ᶠ i, ρᵢ • ∇ⁱ` is a covariant derivative on
the whole manifold (`CovariantDerivative.ofPartitionOfUnity`): at each point only the `∇ⁱ` defined
there contribute, and the coefficients sum to one, so the derivative of `ρᵢ` never enters. When
`ρ` is smooth and each `∇ⁱ` is `C^n` on `Uᵢ`, the glued derivative is `C^n`. Applying this to the
flat derivatives `TauCeti.Manifold.frameCovariantDerivative` of the local frames of the bundle
trivializations gives existence.

The gluing lemma is the locally finite version of Mathlib's
`IsCovariantDerivativeOn.finite_affine_combination`, from which it is derived pointwise, and its
regularity statement is the locally finite version of
`ContMDiffCovariantDerivativeOn.finite_affine_combination`.

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
  derivative on a `C^(n+1)` finite-rank vector bundle.
* `CovariantDerivative.instNonempty`: a `C^1` finite-rank vector bundle over a paracompact
  Hausdorff manifold carries a covariant derivative, with `instNonemptyOfSigmaCompact` covering
  σ-compact Hausdorff manifolds modelled on finite-dimensional spaces.

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

/-- **Gluing covariant derivatives along a partition of unity.** If `cov i` is a covariant
derivative over `U i` and `ρ` is a partition of unity on `s` subordinate to `U`, then
`∑ᶠ i, ρ i • cov i` is a covariant derivative over `s`. -/
theorem IsSubordinate.isCovariantDerivativeOn_finsum_smul (hρ : ρ.IsSubordinate U)
    (hcov : ∀ i, IsCovariantDerivativeOn F (cov i) (U i)) :
    IsCovariantDerivativeOn F (fun σ x ↦ ∑ᶠ i, ρ i x • cov i σ x) s := by
  -- At `x`, the sum is the finite affine combination of the `cov i` with `ρ i x ≠ 0`, each of
  -- which is a covariant derivative at `x` since `x ∈ tsupport (ρ i) ⊆ U i`.
  have key {x : M} (hx : x ∈ s) := IsCovariantDerivativeOn.finite_affine_combination
    (s := (Finset.univ : Finset (ρ.finsupport x))) (u := {x})
    (cov := fun i : ρ.finsupport x ↦ cov i) (f := fun i _ ↦ ρ i x)
    (fun i ↦ (hcov i).mono (singleton_subset_iff.2
      (hρ i (subset_tsupport _ ((ρ.mem_finsupport x).1 i.2)))))
    (by ext; simp [Finset.sum_attach _ fun i ↦ ρ i x, ρ.sum_finsupport hx])
  -- `ρ.sum_finsupport_smul_eq_finsum` stated for the constant families of fibre elements at `x`;
  -- rewriting with it backwards directly needs higher-order unification and does not fire.
  have hsum {x : M} (φ : ι → TangentSpace I x →L[ℝ] V x) :
      ∑ᶠ i, ρ i x • φ i = ∑ i : ρ.finsupport x, ρ i x • φ i := by
    rw [Finset.sum_coe_sort _ fun i ↦ ρ i x • φ i]
    exact (ρ.sum_finsupport_smul_eq_finsum (φ := fun i _ ↦ φ i)).symm
  refine ⟨fun {σ σ' x} hσ hσ' hx ↦ ?_, fun {σ g x} hσ hg hx ↦ ?_⟩
  · simpa only [hsum] using (key hx).add hσ hσ' rfl
  · simpa only [hsum] using (key hx).leibniz hσ hg rfl

end PartitionOfUnity

namespace SmoothPartitionOfUnity

variable [IsManifold I 1 M] [VectorBundle ℝ F V]

/-- A sum of `C^n` local covariant derivatives weighted by a subordinate smooth partition of unity
is `C^n`: it sends `C^(n+1)` sections to `C^n` sections of `Hom(TM, V)`. -/
theorem IsSubordinate.contMDiffCovariantDerivativeOn_finsum_smul
    {s : Set M} {ρ : SmoothPartitionOfUnity ι I M s} (hρ : ρ.IsSubordinate U)
    (hU : ∀ i, IsOpen (U i)) {n : ℕ∞}
    (hcov : ∀ i, ContMDiffCovariantDerivativeOn F n (cov i) (U i)) :
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

/-- A `C^1` real vector bundle of finite rank over a paracompact Hausdorff manifold carries a
covariant derivative: the flat derivatives of the local frames of its trivializations glue along a
partition of unity. -/
instance instNonempty [T2Space M] [ParacompactSpace M] [FiniteDimensional ℝ F]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] :
    Nonempty (CovariantDerivative I F V) :=
  let b := Module.Basis.ofVectorSpace ℝ F
  let ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x ↦ (trivializationAt F V x).baseSet) (fun x ↦ (trivializationAt F V x).open_baseSet)
    fun x _ ↦ mem_iUnion.2 ⟨x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  ⟨ofPartitionOfUnity ρ hρ
    fun _ ↦ TauCeti.Manifold.isCovariantDerivativeOn_frameCovariantDerivative b⟩

/-- A `C^1` real vector bundle of finite rank over a σ-compact Hausdorff manifold modelled on a
finite-dimensional space carries a covariant derivative. Such a manifold is locally compact, hence
paracompact, so this is `instNonempty`; it is stated separately because instance search does not
derive paracompactness of a manifold from σ-compactness. -/
instance instNonemptyOfSigmaCompact [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] :
    Nonempty (CovariantDerivative I F V) :=
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  instNonempty

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

end CovariantDerivative
