/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded.Contraction

/-!
# The comparison of a graded representation with the total coinduced resolution

Let `M` be a discrete topological representation of `G` with a `ℤ`-grading `ℳ` by invariant
submodules and an equivariant differential `d` of degree one, and let
`c : TopRep.ResolutionContraction X (M.gradedCochainComplex ℳ hρ d hd hdd)` contract the
complex it assembles onto `X`. The comparison `c.comparison` maps that complex, degree by degree,
into the coinduced resolution of `X`. When `M` is the direct sum of its pieces
(`DirectSum.Decomposition ℳ`), these components add up to a single morphism of representations
on the total modules,

```text
κ : M ⟶ X.gradedResolutionTopRep,      κ v = ∑ₙ Fⁿ (vₙ),
```

applying the degree-`n` component `Fⁿ` of the comparison to the degree-`n` part `vₙ` of `v` and
discarding the parts of negative degree (`TopRep.ResolutionContraction.gradedComparison`). It has
degree zero and lies over the identity of `X`. It commutes with the differentials on the pieces of
non-negative degree, and on all of `M` as soon as `d` does not leave the negative degrees, that is,
kills `ℳ (-1)`. For smooth discrete `X` over a compact group, a homogeneous cocycle `z` of `M`
fixed by `G` and the homogeneous cocycle `κ z` of the total coinduced resolution have the same
class in `Hⁿ(G, X)` (`TopRep.ResolutionContraction.gradedCohomologyClass_gradedComparison`).

Constructions on total modules, such as tensor induction, act on morphisms of representations
rather than on families of components, so this is the form in which a contracted graded
representation, such as a tensor-induced resolution, is compared with the total coinduced
resolution. In Evens' multiplicative transfer along a tower `V ≤ U ≤ G` of compact open subgroups,
the norm from `V` to `U` of a cocycle is the class of a cocycle of the tensor-induced resolution
from `V` to `U`; its image under `κ` is a cocycle of the total coinduced resolution with the same
class, which is the kind of cocycle the norm from `U` to `G` is computed on.

## Main definitions

* `TopRep.ResolutionContraction.gradedComparison`: the comparison on total modules.

## Main results

* `TopRep.ResolutionContraction.gradedComparison_apply_of_mem`: on `ℳ n` it is the degree-`n`
  component of `c.comparison`, included in degree `n`.
* `TopRep.ResolutionContraction.gradedComparison_apply_of_mem_of_neg`: it vanishes in negative
  degrees.
* `TopRep.ResolutionContraction.isHomogeneous_gradedComparison`: it has degree zero.
* `TopRep.ResolutionContraction.gradedComparison_ι_apply`: it carries the augmentation of `c` to
  the augmentation of the total resolution.
* `TopRep.ResolutionContraction.gradedComparison_differential_apply_of_mem`: it commutes with the
  differentials on the pieces of non-negative degree.
* `TopRep.ResolutionContraction.gradedComparison_differential`: it commutes with the
  differentials when `d` kills `ℳ (-1)`.
* `TopRep.ResolutionContraction.gradedCohomologyClass_gradedComparison`: it preserves classes of
  homogeneous cocycles.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Comparison Theorem 2.2.6 and its dual
  2.3.7, for the comparison of a resolution with one by relatively injective objects.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5, for the comparison of tensor-induced resolutions.
-/

public section

open CategoryTheory

namespace TopRep

namespace ResolutionContraction

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : TopRep.{max v w} k G} {ℳ : ℤ → Submodule k M.V}
  {hρ : ∀ n g x, x ∈ ℳ n → M.ρ g x ∈ ℳ n} {d : M ⟶ M}
  {hd : TauCeti.LinearMap.IsHomogeneous d.hom.toLinearMap ℳ ℳ 1} {hdd : d ≫ d = 0}
  {X : TopRep.{max v w} k G} (c : ResolutionContraction X (M.gradedCochainComplex ℳ hρ d hd hdd))

/-- The comparison on the piece `ℳ p`: the degree-`n` component of `c.comparison`, included in
degree `n` of the total resolution, for `p = n`, and zero for negative `p`. -/
private noncomputable def gradedComparisonPiece :
    (p : ℤ) → ℳ p →ₗ[k] X.gradedResolutionModule
  -- The degree-`n` term of `gradedCochainComplex` is the subrepresentation on `ℳ n`
  -- (`TopRep.gradedCochainComplex_X`), so the component applies to elements of `ℳ n`.
  | (n : ℕ) =>
    DirectSum.lof k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n ∘ₗ
      (c.comparison.f n).hom.toLinearMap
  | Int.negSucc _ => 0

private theorem gradedComparisonPiece_natCast (n : ℕ) (v : ℳ n) :
    c.gradedComparisonPiece n v =
      DirectSum.lof k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n ((c.comparison.f n).hom v) :=
  (rfl)

private theorem gradedComparisonPiece_of_neg {p : ℤ} (hp : p < 0) (v : ℳ p) :
    c.gradedComparisonPiece p v = 0 := by
  cases p with
  | ofNat n => exact absurd hp (Int.natCast_nonneg n).not_gt
  | negSucc m => rfl

variable [DirectSum.Decomposition ℳ]

/-- The linear map underlying `gradedComparison`. -/
private noncomputable def gradedComparisonLinearMap : M.V →ₗ[k] X.gradedResolutionModule :=
  DirectSum.toModule k ℤ _ c.gradedComparisonPiece ∘ₗ
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

private theorem gradedComparisonLinearMap_of_mem {p : ℤ} {v : M.V} (hv : v ∈ ℳ p) :
    c.gradedComparisonLinearMap v = c.gradedComparisonPiece p ⟨v, hv⟩ := by
  rw [gradedComparisonLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℳ hv]
  exact DirectSum.toModule_lof k p _

private theorem gradedComparisonLinearMap_equivariant (g : G) (v : M.V) :
    c.gradedComparisonLinearMap (M.ρ g v) =
      X.gradedResolutionRepresentation g (c.gradedComparisonLinearMap v) := by
  classical
  induction v using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [map_zero, map_zero, map_zero]
  | @homogeneous p v =>
    obtain ⟨v, hv⟩ := v
    rw [c.gradedComparisonLinearMap_of_mem (hρ p g v hv), c.gradedComparisonLinearMap_of_mem hv]
    rcases lt_or_ge p 0 with hp | hp
    · rw [c.gradedComparisonPiece_of_neg hp, c.gradedComparisonPiece_of_neg hp, map_zero]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      rw [c.gradedComparisonPiece_natCast, c.gradedComparisonPiece_natCast,
        gradedResolutionRepresentation_lof]
      congr 1
      refine (congrArg (c.comparison.f n).hom (Subtype.ext ?_)).trans
        (hom_comm_apply (c.comparison.f n) g ⟨v, hv⟩)
      exact (gradedCochainComplex_ρ_apply M ℳ hρ d hd hdd n g ⟨v, hv⟩).symm
  | add v w hv hw => simp only [map_add, hv, hw]

variable [DiscreteTopology k] [DiscreteTopology M.V]

/-- **The comparison on total modules.** Through the decomposition of `M` into its pieces, the
degree-`n` components `Fⁿ` of the comparison `c.comparison` assemble to the morphism
`v ↦ ∑ₙ Fⁿ (vₙ)` from `M` to the total coinduced resolution of `X`, where `vₙ` is the part of `v`
in `ℳ n`; the parts of negative degree are sent to zero. -/
noncomputable def gradedComparison : M ⟶ X.gradedResolutionTopRep where
  hom' :=
    { toContinuousLinearMap := ⟨c.gradedComparisonLinearMap, continuous_of_discreteTopology⟩
      isIntertwining' g := by
        ext v
        exact (c.gradedComparisonLinearMap_equivariant g v).trans
          (X.gradedResolutionTopRep_ρ_apply g _).symm }

/-- On the piece `ℳ n`, the comparison on total modules is the degree-`n` component of
`c.comparison`, included in degree `n` of the total resolution. -/
theorem gradedComparison_apply_of_mem {n : ℕ} {v : M.V} (hv : v ∈ ℳ n) :
    (c.gradedComparison).hom v =
      DirectSum.lof k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n ((c.comparison.f n).hom ⟨v, hv⟩) :=
  c.gradedComparisonLinearMap_of_mem hv

/-- The comparison on total modules vanishes on the pieces of negative degree. -/
theorem gradedComparison_apply_of_mem_of_neg {p : ℤ} (hp : p < 0) {v : M.V} (hv : v ∈ ℳ p) :
    (c.gradedComparison).hom v = 0 :=
  (c.gradedComparisonLinearMap_of_mem hv).trans (c.gradedComparisonPiece_of_neg hp _)

/-- The comparison on total modules has degree zero. -/
theorem isHomogeneous_gradedComparison :
    TauCeti.LinearMap.IsHomogeneous (c.gradedComparison).hom.toLinearMap ℳ
      X.gradedResolutionPiece 0 := by
  classical
  refine TauCeti.LinearMap.isHomogeneous_def.2 fun p v hv ↦ ?_
  rw [add_zero]
  rcases lt_or_ge p 0 with hp | hp
  · exact (c.gradedComparison_apply_of_mem_of_neg hp hv).symm ▸ zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact (c.gradedComparison_apply_of_mem hv).symm ▸ X.lof_mem_gradedResolutionPiece n _

/-- The comparison on total modules carries `ℳ p` into the piece of degree `p` of the total
resolution. -/
theorem gradedComparison_mem_gradedResolutionPiece {p : ℤ} {v : M.V} (hv : v ∈ ℳ p) :
    (c.gradedComparison).hom v ∈ X.gradedResolutionPiece p := by
  have h := c.isHomogeneous_gradedComparison.map_mem hv
  rw [add_zero] at h
  exact h

/-- The comparison on total modules carries a vector fixed by `G` to a vector fixed by `G`. -/
theorem gradedResolutionTopRep_ρ_gradedComparison {v : M.V} (hv : ∀ g, M.ρ g v = v) (g : G) :
    X.gradedResolutionTopRep.ρ g ((c.gradedComparison).hom v) = (c.gradedComparison).hom v := by
  rw [← hom_comm_apply, hv]

/-- **The comparison lies over the identity of `X`**: it carries the augmentation of `c` to the
augmentation of the total coinduced resolution, by constant functions in degree zero. -/
@[simp]
theorem gradedComparison_ι_apply (x : X.V) :
    (c.gradedComparison).hom (c.ι.hom x).1 = X.gradedResolutionAugmentation x := by
  classical
  rw [c.gradedComparison_apply_of_mem (n := 0) (c.ι.hom x).2, gradedResolutionAugmentation_apply,
    ← c.ι_comp_comparison_f_zero, comp_apply]
  -- The degree-zero object of `gradedCochainComplex` is the subtype `ℳ 0`, so the element
  -- rebuilt from `(c.ι.hom x).1` is `c.ι.hom x` by subtype eta.
  exact congrArg _ (congrArg (c.comparison.f 0).hom (Subtype.eta _ _))

/-- **The comparison commutes with the differentials on the pieces of non-negative degree.** -/
theorem gradedComparison_differential_apply_of_mem {n : ℕ} {v : M.V} (hv : v ∈ ℳ n) :
    X.gradedResolutionTopRepDifferential.hom ((c.gradedComparison).hom v) =
      (c.gradedComparison).hom (d.hom v) := by
  classical
  have hdv : d.hom v ∈ ℳ (n + 1 : ℕ) := by exact_mod_cast hd.map_mem hv
  rw [c.gradedComparison_apply_of_mem hdv, c.gradedComparison_apply_of_mem hv,
    gradedResolutionTopRepDifferential_apply, gradedResolutionDifferential_lof]
  congr 1
  refine (c.d_comparison_f_apply n ⟨v, hv⟩).trans
    (congrArg (c.comparison.f (n + 1)).hom (Subtype.ext ?_))
  exact gradedCochainComplex_d_apply M ℳ hρ d hd hdd n ⟨v, hv⟩

/-- The comparison carries a homogeneous cocycle of non-negative degree to a cocycle of the total
coinduced resolution. -/
theorem gradedResolutionTopRepDifferential_gradedComparison_eq_zero {n : ℕ} {z : M.V}
    (hz : z ∈ ℳ n) (hdz : d.hom z = 0) :
    X.gradedResolutionTopRepDifferential.hom ((c.gradedComparison).hom z) = 0 := by
  rw [c.gradedComparison_differential_apply_of_mem hz, hdz, map_zero]

/-- **The comparison commutes with the differentials**, provided `d` kills the piece `ℳ (-1)`,
so that it does not carry the discarded negative degrees into degree zero. This holds in
particular when the pieces of negative degree vanish. -/
theorem gradedComparison_differential (hneg : ∀ v ∈ ℳ (-1), d.hom v = 0) :
    d ≫ c.gradedComparison = c.gradedComparison ≫ X.gradedResolutionTopRepDifferential := by
  classical
  ext v
  simp only [hom_comp, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply]
  induction v using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp only [map_zero]
  | @homogeneous p v =>
    obtain ⟨v, hv⟩ := v
    have hdv : d.hom v ∈ ℳ (p + 1) := hd.map_mem hv
    rcases lt_or_ge p 0 with hp | hp
    · rw [c.gradedComparison_apply_of_mem_of_neg hp hv, map_zero]
      rcases lt_or_ge (p + 1) 0 with hp' | hp'
      · exact c.gradedComparison_apply_of_mem_of_neg hp' hdv
      · obtain rfl : p = -1 := by omega
        simp only [hneg v hv, map_zero]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      exact (c.gradedComparison_differential_apply_of_mem hv).symm
  | add v w hv hw => simp only [map_add, hv, hw]

/-- **The comparison preserves classes.** For smooth discrete `X` over a compact group, a
homogeneous cocycle `z ∈ ℳ n` fixed by `G` has the same class in `Hⁿ(G, X)` through `c` as the
homogeneous cocycle `κ z` of the total coinduced resolution through its evaluation-at-`1`
contraction `TopRep.gradedResolutionContraction`. -/
theorem gradedCohomologyClass_gradedComparison [CompactSpace G] (hX : TauCeti.IsSmoothDiscrete k X)
    {n : ℕ} {z : M.V} (hz : z ∈ ℳ n) (hinv : ∀ g, M.ρ g z = z) (hdz : d.hom z = 0) :
    (gradedResolutionContraction hX).gradedCohomologyClass ((c.gradedComparison).hom z)
        (c.gradedComparison_mem_gradedResolutionPiece hz)
        (c.gradedResolutionTopRep_ρ_gradedComparison hinv)
        (c.gradedResolutionTopRepDifferential_gradedComparison_eq_zero hz hdz) =
      c.gradedCohomologyClass z hz hinv hdz := by
  rw [gradedCohomologyClass_def, cohomologyClass_def,
    ← gradedCohomologyClass_gradedResolutionContraction hX]
  · congr 1
    rw [c.gradedComparison_apply_of_mem hz, ContIntertwiningMap.mapInvariants_apply]
    exact congrArg _ (congrArg (c.comparison.f n).hom
      (Subtype.ext (gradedCochainComplexInvariant_val M ℳ hρ d hd hdd n z hz hinv).symm))
  · rw [ContIntertwiningMap.mapInvariants_apply, ← comp_apply, c.comparison.comm, comp_apply,
      gradedCochainComplex_d_invariant M ℳ hρ d hd hdd hz hinv hdz, map_zero]

end ResolutionContraction

end TopRep
