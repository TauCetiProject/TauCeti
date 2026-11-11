/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Topology.CWComplex.Classical.AdjunctionModel
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# The CW model of a manifold with a Morse function

Let `f` be a Morse function on a compact boundaryless manifold `M`. Then `M` is homotopy
equivalent to a finite CW complex with one `λ`-cell for each critical point of `f` of index `λ`
(`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`). In particular every compact smooth
boundaryless manifold, which carries a Morse function by `TauCeti.exists_isMorse`, has finite CW
type (`TauCeti.FiniteCWType.of_isManifold`).

The model is built one critical level at a time, along the sublevels `M_a = {f ≤ a}`. Across a
compact band without critical points the sublevel keeps its homotopy type
(`TauCeti.exists_sublevelHomotopyEquiv`). Across a critical value `c`, for small `ε > 0` the
sublevel `M_{c+ε}` is homotopy equivalent to `M_{c-ε}` with one `λ`-disc attached at each critical
point of index `λ` on the level (`TauCeti.IsMorse.exists_morseCellAttachment_deformation`). If
`W` is a CW complex homotopy equivalent to `M_{c-ε}`, the attaching maps can be moved into the
skeleta of `W` by cellular approximation, and attaching the discs to `W` along them gives a CW
complex homotopy equivalent to `M_{c+ε}`, with the cells of `W` and one new `λ`-cell for each
critical point (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`). So if
`M_a` has a finite CW model `W`, then `M_b` has a finite CW model whose number of `λ`-cells is that
of `W` plus the number of critical points of index `λ` with value in `(a, b]`, when `a ≤ b` are
regular values with compact band `f⁻¹[a, b]`
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel`). Only the homotopy type and the cell
counts of the new model are recorded: no inclusion of `W` as a subcomplex, nor any compatibility
with the inclusion `M_a ⊆ M_b`, is provided. For compact `M`,
starting below the minimum of `f`, where the sublevel is empty, and ending above its maximum, where
the sublevel is `M`, gives the CW model of `M`.

## Main results

* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel`: if `M_a` has a finite CW model,
  then so does `M_b`, with one more `λ`-cell in the count for each critical point of index `λ`
  with value in `(a, b]`. No map between the two models is supplied.
* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`: **the CW model of a compact
  manifold.** A compact boundaryless manifold with a Morse function `f` is homotopy equivalent to
  a finite CW complex whose `λ`-cells are counted by the critical points of `f` of index `λ`.
* `TauCeti.IsMorse.finiteCWType` and `TauCeti.FiniteCWType.of_isManifold`: compact boundaryless
  smooth manifolds have finite CW type.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof (Lemmas 3.6 and 3.7).
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex CategoryTheory Limits
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **Crossing a critical level by an adjunction space.** If the band `f⁻¹[c - δ, c + δ]` of a
Morse function is compact, then for some `0 < ε ≤ δ` the sublevel `M_{c+ε}` is homotopy equivalent
to the space obtained from `M_{c-ε}` by attaching one `λ`-disc for each critical point of index
`λ` on the level `c`, and these are the only critical points with values in `[c - ε, c + ε]`. -/
private theorem IsMorse.exists_homotopyEquiv_sigmaDiskAdjunction (hf : IsMorse I f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} ∧
      ∃ a : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
          C(TopCat.diskBoundary.{u} (manifoldMorseIndex I f p), {x | f x ≤ c - ε}),
        letI := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
          manifoldMorseIndex I f p
        Nonempty (relCWAdjunctionSpace (univ.sigma fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
          (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p)))) (sigmaDiskAttachingMap a) ≃ₕ
            {x | f x ≤ c + ε}) := by
  -- Shrink the band so that its only critical points lie on the level `c`.
  obtain ⟨δ', hδ', hδ'δ, hsub⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  have hcompact' : IsCompact (f ⁻¹' Icc (c - δ') (c + δ')) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith)))
  obtain ⟨ε, hε, hεδ', ψ, -, -, hball, hψ, g, hg, hH⟩ :=
    hf.exists_morseCellAttachment_deformation hδ' hcompact'
  -- The comparison map from the cell attachment to `M_{c+ε}` is a homotopy equivalence.
  let Φ := morseCellComparison (fun p ↦ (ψ p).toOpenPartialHomeomorph)
    (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball hψ
  have hgΦ : g.comp Φ.hom = ContinuousMap.id _ := ContinuousMap.ext hg
  let e : (morseCellAttachment (fun p ↦ (ψ p).toOpenPartialHomeomorph)
      (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball hψ :
        TopCat.{u}) ≃ₕ {x | f x ≤ c + ε} :=
    ⟨Φ.hom, g, hgΦ ▸ .refl _, hH.homotopic.symm⟩
  refine ⟨ε, hε, hεδ'.trans hδ'δ,
    fun x hx ↦ hsub ⟨hx.1, Icc_subset_Icc (by linarith) (by linarith) hx.2⟩,
    fun p ↦ ((ψ p).toOpenPartialHomeomorph.morseAttachingMap manifoldMorseIndex_le_finrank hε.le
      (hball p) (hψ p)).hom, ⟨?_⟩⟩
  -- The adjunction space is the pushout defining the cell attachment.
  exact (TopCat.homeoOfIso ((sigmaDiskAdjunctionIsoPushout fun p ↦
    (ψ p).toOpenPartialHomeomorph.morseAttachingMap manifoldMorseIndex_le_finrank hε.le
      (hball p) (hψ p)) ≪≫ (isPushout_morseCellAttachment (fun p ↦ (ψ p).toOpenPartialHomeomorph)
        (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hball hψ
        hε.le).isoPushout.symm)).toHomotopyEquiv.trans e

variable (I f) in
/-- For every finite CW model `W` of `M_s = {f ≤ s}` there is a finite CW model of `M_t` with,
in each dimension `m`, as many `m`-cells as `W` plus one for each critical point of index `m` with
value in `(s, t]`. No map between the two models is required. -/
private def CWModelExtends (s t : ℝ) (_ : s ≤ t) : Prop :=
  ∀ (W : Type u) [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    [RelCWComplex.Finite (univ : Set W)], (W ≃ₕ {x | f x ≤ s}) →
      ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W')),
        RelCWComplex.Finite (univ : Set W') ∧ Nonempty (W' ≃ₕ {x | f x ≤ t}) ∧
        ∀ m, ENat.card (cell (univ : Set W') m) = ENat.card (cell (univ : Set W) m) +
          {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m}.encard

/-- Across a compact band without critical points, the CW model is unchanged. -/
private theorem cwModelExtends_of_forall_notMem (hf : IsMorse I f) {s t : ℝ} (hst : s ≤ t)
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc s t) :
    CWModelExtends I f s t hst := by
  intro W _ _ _ _ e
  obtain ⟨e', -⟩ := exists_sublevelHomotopyEquiv hf.contMDiff hst hcompact
    fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩
  refine ⟨W, _, ‹_›, ‹_›, ‹_›, ⟨e.trans e'⟩, fun m ↦ ?_⟩
  have : {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ hcrit x hx.1.1 (Ioc_subset_Icc_self hx.1.2)
  rw [this, encard_empty, add_zero]

/-- Across one critical level, the CW model gains one `λ`-cell for each critical point of index
`λ` on the level. -/
private theorem IsMorse.exists_cwModelExtends_level (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ CWModelExtends I f (c - ε) (c + ε) (by linarith) := by
  obtain ⟨ε, hε, hεδ, hsub, a, ⟨e⟩⟩ := hf.exists_homotopyEquiv_sigmaDiskAdjunction hδ hcompact
  refine ⟨ε, hε, hεδ, fun W _ _ _ _ h ↦ ?_⟩
  have : Finite ↥(criticalPoints I f ∩ f ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  let := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
    manifoldMorseIndex I f p
  -- Attach the discs to `W` along attaching maps moved into its skeleta.
  obtain ⟨b, hb, -, Ψ, -⟩ := h.exists_homotopyEquiv_sigmaDiskAdjunction a
  let := sigmaDiskAdjunctionCWComplex _ b hb
  refine ⟨_, _, inferInstance, sigmaDiskAdjunctionCWComplex _ b hb,
    finite_sigmaDiskAdjunctionCWComplex _ b hb, ⟨Ψ.trans e⟩, fun m ↦ ?_⟩
  rw [ENat.card_congr (sigmaDiskAdjunctionCWComplexCellEquiv _ b hb m), ENat.card_sum,
    encard_ofPred]
  congr 1
  -- The new `m`-cells are the critical points of index `m` on the level `c`, which are those with
  -- values in `(c - ε, c + ε]`.
  refine ENat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
    (· ∈ criticalPoints I f ∩ f ⁻¹' {c}) (manifoldMorseIndex I f · = m)).trans
      (Equiv.subtypeEquivRight fun x ↦ ?_))
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ioc]
  constructor
  · rintro ⟨⟨hx, rfl⟩, hi⟩
    exact ⟨⟨hx, by linarith, by linarith⟩, hi⟩
  · rintro ⟨⟨hx, h₁, h₂⟩, hi⟩
    exact ⟨⟨hx, hsub ⟨hx, h₁.le, h₂⟩⟩, hi⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The CW models compose along `s ≤ m ≤ t`. -/
private theorem CWModelExtends.trans {s m t : ℝ} {hsm : s ≤ m} {hmt : m ≤ t}
    (h₁ : CWModelExtends I f s m hsm) (h₂ : CWModelExtends I f m t hmt) :
    CWModelExtends I f s t (hsm.trans hmt) := by
  intro W _ _ _ _ e
  obtain ⟨W₁, _, _, _, _, ⟨e₁⟩, hc₁⟩ := h₁ W e
  obtain ⟨W₂, _, _, _, _, ⟨e₂⟩, hc₂⟩ := h₂ W₁ e₁
  refine ⟨W₂, _, ‹_›, ‹_›, ‹_›, ⟨e₂⟩, fun i ↦ ?_⟩
  have hdisj : Disjoint
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s m | manifoldMorseIndex I f x = i}
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc m t | manifoldMorseIndex I f x = i} :=
    disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.1.2.2) hx'.1.2.1
  rw [hc₂, hc₁, add_assoc, ← encard_union_eq hdisj, ← Ioc_union_Ioc_eq_Ioc hsm hmt]
  congr 2
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_union]
  tauto

/-- **CW models of sublevels.** Let `f` be a Morse function and `a ≤ b` regular values of `f`
with compact band `f⁻¹[a, b]`. If `W` is a finite CW complex homotopy equivalent to the sublevel
`M_a = {f ≤ a}`, then `M_b` is homotopy equivalent to a finite CW complex `W'` whose number of
`m`-cells, in each dimension `m`, is that of `W` plus the number of critical points of index `m`
with value in `(a, b]`. Only this existence and these cell counts are asserted: `W` is not claimed
to be a subcomplex of `W'`, and no compatibility with the inclusion `M_a ⊆ M_b` is supplied. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u) [TopologicalSpace W] [T2Space W]
    [CWComplex (univ : Set W)] [RelCWComplex.Finite (univ : Set W)] (e : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W')),
      RelCWComplex.Finite (univ : Set W') ∧ Nonempty (W' ≃ₕ {x | f x ≤ b}) ∧
      ∀ m, ENat.card (cell (univ : Set W') m) = ENat.card (cell (univ : Set W) m) +
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}.encard :=
  hf.band_induction (P := CWModelExtends I f) hab hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ cwModelExtends_of_forall_notMem hf hst hcompact hcrit)
    (fun _ _ _ _ _ hδ hcompact ↦ hf.exists_cwModelExtends_level hδ hcompact)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) W e

/-- **The CW model of a compact manifold.** A compact boundaryless manifold `M` carrying a Morse
function `f` is homotopy equivalent to a finite CW complex with one `m`-cell for each critical
point of `f` of index `m`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv [CompactSpace M] (hf : IsMorse I f) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ M) ∧
      ∀ m, ENat.card (cell (univ : Set W) m) = criticalCount I f m := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  -- Below the minimum of `f` the sublevel is empty, the empty CW complex.
  have : IsEmpty {x | f x ≤ a} := ⟨fun x ↦ (not_le.2 (hf' x).1) x.2⟩
  obtain ⟨W, _, _, _, hfin, ⟨e⟩, hcount⟩ := hf.exists_cwComplex_homotopyEquiv_sublevel hab
    hcompact ha hb PEmpty.{u + 1} Homeomorph.empty.toHomotopyEquiv
  -- Above the maximum of `f` the sublevel is all of `M`.
  have hM : {x | f x ≤ b} = univ := eq_univ_of_forall fun x ↦ (hf' x).2
  refine ⟨W, _, ‹_›, ‹_›, hfin,
    ⟨e.trans ((Homeomorph.setCongr hM).trans (Homeomorph.Set.univ M)).toHomotopyEquiv⟩,
    fun m ↦ ?_⟩
  have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ (map m j 0).elim⟩
  rw [hcount, (ENat.card_eq_zero_iff_empty _).2 this, zero_add, criticalCount_def]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  have := hf' x
  tauto

/-- A compact boundaryless manifold carrying a Morse function has finite CW type. -/
theorem IsMorse.finiteCWType [CompactSpace M] (hf : IsMorse I f) : FiniteCWType M := by
  obtain ⟨W, _, _, _, _, ⟨e⟩, -⟩ := hf.exists_finite_cwComplex_homotopyEquiv
  exact (e.symm.trans (Homeomorph.Set.univ W).symm.toHomotopyEquiv).finiteCWType

variable (I M) in
include I in
/-- **Compact manifolds have finite CW type.** A compact boundaryless smooth manifold with a
finite-dimensional model is homotopy equivalent to a finite CW complex. -/
theorem FiniteCWType.of_isManifold [CompactSpace M] : FiniteCWType M :=
  (exists_isMorse (I := I) (M := M)).choose_spec.finiteCWType

end TauCeti
