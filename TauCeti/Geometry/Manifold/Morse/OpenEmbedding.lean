/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Geometry.Manifold.Morse.RelCWComplex
public import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Morse deformations of a space with an open manifold part

Let `X` be a topological space, `F : X → ℝ` a continuous function, and `j : M → X` an open
embedding of a manifold whose complement `A = X \ range j` lies where `F` is small. Then the
deformations of the sublevels of `F ∘ j` on `M` given by Morse theory extend by the identity over
`A` to deformations of the sublevels of `F` on `X`. The point is that near `A` the deformations
fixing a lower sublevel `{F ∘ j ≤ a}` of `M` are already the identity: the set
`{F < a}` is an open neighbourhood of `A` in `X` on which the transported deformation is the
identity (`Topology.IsOpenEmbedding.exists_deformation_of_preimage`).

No property of `X` beyond its topology is used: `X` may be singular along `A`. The typical
example is a compact pair `(X, A)` whose complement `X \ A` is a manifold, with a continuous
function `F` vanishing on `A` whose positive superlevel sets are compact subsets of `X \ A`. Then
for `0 < a` the sublevels `{F ≤ a}` of `X` are neighbourhoods of `A` and every band
`F⁻¹[a, b]` is compact. The two theorems below then describe, one band at a time, how a sublevel
of `F` is obtained from a lower one, up to a deformation fixing the lower sublevel and hence `A`:
nothing changes across a band without critical points of `F ∘ j`, and across a critical level one
cell is attached at each critical point on the level.

## Main results

* `TauCeti.exists_sublevelDeformation_of_isOpenEmbedding`: across a compact band without critical
  points, `{F ≤ b}` strong deformation retracts onto `{F ≤ a}`.
* `TauCeti.IsMorse.exists_relCWComplex_sublevel_deformation_of_isOpenEmbedding`: across a critical
  level `c`, `{F ≤ c + ε}` strong deformation retracts onto `{F ≤ c - ε}` together with the image
  of a finite relative CW complex over `{F ∘ j ≤ c - ε}` with one cell for each critical point on
  the level, of dimension its Morse index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1 and 3.2, and Section 7.
-/

public section

open Function Set Topology Topology.RelCWComplex
open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  {X : Type*} [TopologicalSpace X] {j : M → X} {F : X → ℝ}

/-- **Deformation across a band without critical points, extended over the complement of an open
manifold part.** Let `j : M → X` be an open embedding of a manifold into a space `X`, and
`F : X → ℝ` a continuous function, smooth on `M`, with `F < a` off the range of `j`. If the band
`F⁻¹[a, b]` is compact and `F ∘ j` has no critical point there, then the sublevel `{F ≤ b}` strong
deformation retracts onto `{F ≤ a}`. -/
theorem exists_sublevelDeformation_of_isOpenEmbedding (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hFj : ContMDiff I 𝓘(ℝ) ∞ (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ F (j x) → F (j x) ≤ b → mfderiv I 𝓘(ℝ) (F ∘ j) x ≠ 0)
    (hA : ∀ x ∉ range j, F x < a) :
    ∃ r : C({x | F x ≤ b}, {x | F x ≤ a}), (∀ x, r (sublevelInclusion F a b hab x) = x) ∧
      Nonempty (ContinuousMap.HomotopyRel ((sublevelInclusion F a b hab).comp r)
        (ContinuousMap.id _) {x | F x ≤ a}) := by
  obtain ⟨r, -, ⟨G⟩⟩ :=
    exists_sublevelDeformation hFj hab (hj.isInducing.isCompact_comp_preimage_Icc hA hcompact) hreg
  -- Both sublevel inclusions are inclusions of sets.
  rw [sublevelInclusion_eq_inclusion] at G ⊢
  exact hj.exists_deformation_of_preimage _ _ rfl rfl (isOpen_lt hF continuous_const)
    (fun x hx ↦ hA x hx.2) (inter_subset_right.trans (ofPred_subset_ofPred.2 fun _ hx ↦ hx.le)) r G

/-- **Milnor's cell attachment across a critical level, extended over the complement of an open
manifold part.** Let `j : M → X` be an open embedding of a manifold into a space `X`, and
`F : X → ℝ` a continuous function with `F ∘ j` Morse and `F < c - δ` off the range of `j`. If the
band `F⁻¹[c - δ, c + δ]` is compact, then for some `0 < ε ≤ δ` the sublevel `{F ≤ c + ε}` strong
deformation retracts onto `{F ≤ c - ε} ∪ j '' C`, where `C ⊆ {F ∘ j ≤ c + ε}` is a finite CW
complex relative to `{F ∘ j ≤ c - ε}` whose `m`-cells correspond to the critical points of index
`m` of `F ∘ j` on the level `c`. The deformation fixes every point outside the range of `j`. -/
theorem IsMorse.exists_relCWComplex_sublevel_deformation_of_isOpenEmbedding
    (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (F ⁻¹' Icc (c - δ) (c + δ))) (hA : ∀ x ∉ range j, F x < c - δ) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ ∃ (C : Set M) (_ : RelCWComplex C {x | (F ∘ j) x ≤ c - ε})
      (_ : RelCWComplex.Finite C) (_ : C ⊆ {x | (F ∘ j) x ≤ c + ε}),
      (∀ m, Nonempty (cell C m ≃
        {p : ↥(criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' {c}) //
          manifoldMorseIndex I (F ∘ j) p = m})) ∧
      ∃ r : C({x | F x ≤ c + ε}, ↥({x | F x ≤ c + ε} ∩ ({x | F x ≤ c - ε} ∪ j '' C))),
        (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
        Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
          (ContinuousMap.id _) {x | (x : X) ∈ {x | F x ≤ c - ε} ∪ j '' C}) := by
  obtain ⟨ε, hε, hεδ, C, _, hfin, hC, hcell, r, -, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_deformation hδ
      (hj.isInducing.isCompact_comp_preimage_Icc hA hcompact)
  -- The lower sublevel of `F ∘ j` is the base of `C ⊆ {F ∘ j ≤ c + ε}`, so `C` is the preimage of
  -- the target.
  have hpre : j ⁻¹' ({x | F x ≤ c + ε} ∩ ({x | F x ≤ c - ε} ∪ j '' C)) = C := by
    rw [preimage_inter, preimage_union, hj.injective.preimage_image,
      union_eq_right.2 RelCWComplex.base_subset_complex]
    exact inter_eq_right.2 hC
  obtain ⟨r', hr', H'⟩ := hj.exists_deformation_of_preimage (V := {x | F x < c - ε})
    inter_subset_left hC rfl hpre (isOpen_lt hF continuous_const)
    (fun x hx ↦ (hA x hx.2).trans_le (by linarith))
    (fun _ hx ↦ ⟨hx.1,
      .inl (inter_subset_right.trans (ofPred_subset_ofPred.2 fun _ hx ↦ hx.le) hx)⟩) r G
  refine ⟨ε, hε, hεδ, C, inferInstance, hfin, hC, hcell, r', hr', ?_⟩
  -- Points of `{F ≤ c + ε}` lie in the target exactly when they lie in its second factor.
  convert H' using 3
  exact funext fun x ↦ propext (and_iff_right x.2).symm

end TauCeti
