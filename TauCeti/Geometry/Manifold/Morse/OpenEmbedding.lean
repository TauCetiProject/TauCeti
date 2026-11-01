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
# Morse theory on an open part of a space

Let `X` be a topological space and `e : M → X` an open embedding of a manifold `M`, and let
`F : X → ℝ` be continuous, with `F ∘ e` smooth. The space `X` need not be a manifold: for
example, `X` may be a projective variety and `e` the inclusion of its affine part `X \ A` off a
hyperplane section `A = X ∩ H`, which is a manifold when every singular point of `X` lies on
`H`, with `F` a reciprocal distance function which vanishes exactly on `A`. Suppose that `F`
is small off the range of `e`. Then Morse theory of `F ∘ e` on `M` describes how the sublevels
`X_a = {F ≤ a}` of `X` change, while the part of `X` outside the range of `e` stays fixed.

If the band `(F ∘ e)⁻¹[a, b]` is compact and free of critical points, and `F < a` off the range
of `e`, then `X_a` is a strong deformation retract of `X_b`
(`TauCeti.exists_sublevelDeformation_of_isOpenEmbedding`). If `F ∘ e` is a Morse function with a
compact band around a critical value `c`, and `F < c - δ` off the range of `e`, then for small
`ε > 0` the sublevel `X_{c+ε}` strong deformation retracts onto a finite CW complex relative to
`X_{c-ε}`, whose `m`-cells correspond to the critical points of index `m` on the level `c`
(`TauCeti.IsMorse.exists_relCWComplex_sublevel_deformation_of_isOpenEmbedding`). In both cases
the deformation is the one given by Morse theory on `M`
(`TauCeti.exists_sublevelDeformation`, `TauCeti.IsMorse.exists_sublevel_union_cells_deformation`),
transported along `e` and extended by the identity to the rest of `X`
(`ContinuousMap.HomotopicRel.exists_inter_deformation_of_isOpenEmbedding`). This is possible
because these deformations fix the lower sublevel pointwise, and the set `{F < a}`, which is open
and contains every point off the range of `e`, lies in that lower sublevel.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1 and 3.2.
-/

public section

open Function Set Topology Metric Topology.RelCWComplex
open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Deformation

variable {M X : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace X] {e : M → X} {F : X → ℝ}

/-- **Deformation of sublevels across a band without critical points in an open part.** Let
`e : M → X` be an open embedding of a manifold into a topological space and `F : X → ℝ` a
continuous function such that `F ∘ e` is smooth. If `a ≤ b`, the band `(F ∘ e)⁻¹[a, b]` is
compact and contains no critical point of `F ∘ e`, and `F < a` off the range of `e`, then the
sublevel `{F ≤ a}` of `X` is a strong deformation retract of `{F ≤ b}`. -/
theorem exists_sublevelDeformation_of_isOpenEmbedding (he : IsOpenEmbedding e)
    (hF : Continuous F) (hf : ContMDiff I 𝓘(ℝ) ∞ (F ∘ e)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact ((F ∘ e) ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ F (e x) → F (e x) ≤ b → mfderiv I 𝓘(ℝ) (F ∘ e) x ≠ 0)
    (hA : ∀ x ∉ range e, F x < a) :
    ∃ r : C({x | F x ≤ b}, {x | F x ≤ a}), (∀ x, r (sublevelInclusion F a b hab x) = x) ∧
      Nonempty (((sublevelInclusion F a b hab).comp r).HomotopyRel (ContinuousMap.id _)
        {x | F x ≤ a}) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  have hsub : {x | (F ∘ e) x ≤ a} ⊆ e ⁻¹' {x | F x ≤ b} ∩ e ⁻¹' {x | F x ≤ a} :=
    fun x hx ↦ ⟨le_trans hx hab, hx⟩
  obtain ⟨r', hr', ⟨G'⟩⟩ := ContinuousMap.HomotopicRel.exists_inter_deformation_of_isOpenEmbedding
    he (isOpen_lt hF continuous_const) (fun x _ ↦ or_iff_not_imp_left.2 (hA x))
    (fun x hx ↦ le_of_lt hx.2) rfl rfl ((ContinuousMap.inclusion hsub).comp r)
    (G.cast (by ext; simp) rfl)
  refine ⟨(ContinuousMap.inclusion inter_subset_right).comp r', fun x ↦ ?_,
    ⟨G'.cast (by ext; simp) rfl⟩⟩
  have hx : sublevelInclusion F a b hab x = ContinuousMap.inclusion
      (inter_subset_left : {x | F x ≤ b} ∩ {x | F x ≤ a} ⊆ _) ⟨x, hab.trans' x.2, x.2⟩ :=
    Subtype.ext (by simp)
  rw [hx]
  exact congrArg (ContinuousMap.inclusion inter_subset_right) (hr' ⟨x, hab.trans' x.2, x.2⟩)

end Deformation

section CellAttachment

/- Classical relative CW complexes index the cells of a subset of `X` by types in the universe of
`X`. The cells here are indexed by critical points of `F ∘ e`, so `M` and `X` share a universe. -/
variable {M X : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace X] {e : M → X} {F : X → ℝ}

/-- **Milnor's cell attachment theorem in CW form, in an open part.** Let `e : M → X` be an open
embedding of a Hausdorff manifold into a topological space and `F : X → ℝ` a continuous function
such that `F ∘ e` is a Morse function. Let `c` be a value with a compact band
`(F ∘ e)⁻¹[c - δ, c + δ]`, and suppose that `F < c - δ` off the range of `e`. Then for some
`0 < ε ≤ δ` the sublevel `{F ≤ c + ε}` of `X` strong deformation retracts onto a finite CW complex
`C ⊆ {F ≤ c + ε}` relative to the lower sublevel `{F ≤ c - ε}`, whose `m`-cells correspond to the
critical points of index `m` of `F ∘ e` on the level `c`. The part of `X` off the range of `e` lies
in `{F ≤ c - ε}`, so it is fixed by the deformation. -/
theorem IsMorse.exists_relCWComplex_sublevel_deformation_of_isOpenEmbedding
    (he : IsOpenEmbedding e) (hF : Continuous F) (hf : IsMorse I (F ∘ e)) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact ((F ∘ e) ⁻¹' Icc (c - δ) (c + δ)))
    (hA : ∀ x ∉ range e, F x < c - δ) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ ∃ (C : Set X) (_ : RelCWComplex C {x | F x ≤ c - ε})
      (_ : RelCWComplex.Finite C) (hC : C ⊆ {x | F x ≤ c + ε}),
      (∀ m, Nonempty (cell C m ≃
        {p : ↥(criticalPoints I (F ∘ e) ∩ (F ∘ e) ⁻¹' {c}) //
          manifoldMorseIndex I (F ∘ e) p = m})) ∧
      ∃ r : C({x | F x ≤ c + ε}, C), (∀ x, r (ContinuousMap.inclusion hC x) = x) ∧
        Nonempty (((ContinuousMap.inclusion hC).comp r).HomotopyRel (ContinuousMap.id _)
          {x | (x : X) ∈ C}) := by
  obtain ⟨ε, hε, hεδ, ψ, hψ, hψp, r, -, ⟨G⟩⟩ :=
    hf.exists_sublevel_union_cells_deformation hδ hcompact
  have hk : ∀ p : ↥(criticalPoints I (F ∘ e) ∩ (F ∘ e) ⁻¹' {c}),
      manifoldMorseIndex I (F ∘ e) p ≤ Module.finrank ℝ E := fun _ ↦ manifoldMorseIndex_le_finrank
  have hball : ∀ p, closedBall 0 √ε ⊆ (ψ p).target := fun p ↦
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith))).trans (hψp p).2.2.1
  have : Finite ↥(criticalPoints I (F ∘ e) ∩ (F ∘ e) ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  -- The normalized Morse charts of `M`, read on `X` through `e`.
  let φ p := (ψ p).toOpenPartialHomeomorph.lift_openEmbedding he
  have hφ : Pairwise (Disjoint on fun p ↦ (φ p).source) := fun p q hpq ↦
    (disjoint_image_iff he.injective).2 (hψ hpq)
  have hφF : ∀ p, ∀ y ∈ (φ p).source, F y = c + ∑ i, (if i.val < manifoldMorseIndex I (F ∘ e) p
      then -1 else 1) * φ p y i ^ 2 := by
    rintro p _ ⟨x, hx, rfl⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact (hψp p).2.2.2 x hx
  set S := {x | F x ≤ c - ε} ∪ ⋃ p, (φ p).source ∩ φ p ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧
    ∀ i : Fin (Module.finrank ℝ E), manifoldMorseIndex I (F ∘ e) p ≤ i.val → y i = 0}
  -- The cells lie in `{F ≤ c}`.
  have hS : S ⊆ {x | F x ≤ c + ε} := by
    rintro x (hx | hx)
    · exact le_trans (b := c - ε) hx (by linarith)
    obtain ⟨p, hx⟩ := mem_iUnion.1 hx
    rw [← OpenPartialHomeomorph.morseCellMap_image_closedBall (hball p) (hk p) hε] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact le_trans (b := c) (OpenPartialHomeomorph.apply_morseCellMap_le (hball p) (hφF p) (hk p)
      hε.le (mem_closedBall_zero_iff.1 hw)) (by linarith)
  have hpre : e ⁻¹' S = {x | (F ∘ e) x ≤ c - ε} ∪ ⋃ p, (ψ p).source ∩ ψ p ⁻¹'
      {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ i : Fin (Module.finrank ℝ E), manifoldMorseIndex I (F ∘ e) p ≤ i.val →
        y i = 0} := by
    ext x
    simp only [S, φ, preimage_union, preimage_iUnion, preimage_inter, mem_union, mem_iUnion,
      mem_inter_iff, mem_preimage, OpenPartialHomeomorph.lift_openEmbedding_source,
      he.injective.mem_set_image, OpenPartialHomeomorph.lift_openEmbedding_apply]
    -- The sides differ only by the coercion of `ψ p` to an open partial homeomorphism.
    exact Iff.rfl
  obtain ⟨r', hr', ⟨G'⟩⟩ := ContinuousMap.HomotopicRel.exists_inter_deformation_of_isOpenEmbedding
    (A := {x | F x ≤ c + ε}) (V := {x | F x < c - ε}) he (isOpen_lt hF continuous_const)
    (fun x _ ↦ or_iff_not_imp_left.2 fun hx ↦ (hA x hx).trans_le (by linarith))
    (fun x hx ↦ mem_union_left _ (le_of_lt hx.2 : F x ≤ c - ε)) rfl hpre r G
  refine ⟨ε, hε, hεδ, S, morseRelCWComplex hF φ hφ (manifoldMorseIndex I (F ∘ e) ·) hk hε hball
    hφF, finite_morseRelCWComplex _ _ _ _ _ _ _ _, hS,
    fun m ↦ ⟨morseRelCWComplexCellEquiv _ _ _ _ _ _ _ _ m⟩,
    (ContinuousMap.inclusion inter_subset_right).comp r', fun x ↦ ?_,
    ⟨G'.cast (by ext; rfl) rfl⟩⟩
  exact congrArg (ContinuousMap.inclusion inter_subset_right) (hr' ⟨x, hS x.2, x.2⟩)

end CellAttachment

end TauCeti
