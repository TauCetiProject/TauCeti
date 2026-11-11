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
import TauCeti.Topology.Homotopy.Extension.Pushout

/-!
# The CW model of a manifold with a Morse function

Let `f` be a Morse function on a compact boundaryless manifold `M`. Then `M` is homotopy
equivalent to a finite CW complex whose `λ`-cells are labelled by the critical points of `f` of
index `λ` (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`). In particular every compact
smooth boundaryless manifold, which carries a Morse function by `TauCeti.exists_isMorse`, has
finite CW type (`TauCeti.FiniteCWType.of_isManifold`).

The model is built one critical level at a time, along the sublevels `M_a = {f ≤ a}`. Across a
compact band without critical points the inclusion of sublevels is a homotopy equivalence
(`TauCeti.exists_sublevelHomotopyEquiv`). Across a critical value `c`, for small `ε > 0` the
sublevel `M_{c+ε}` is homotopy equivalent to `M_{c-ε}` with one `λ`-disc attached at each critical
point of index `λ` on the level, by a map which is the inclusion on `M_{c-ε}`
(`TauCeti.IsMorse.exists_morseCellAttachment_deformation`). If `h : W → M_{c-ε}` is a homotopy
equivalence from a CW complex, the attaching maps can be moved into the skeleta of `W` by cellular
approximation, and attaching the discs to `W` along them gives a CW complex `W'` containing `W` as
a subcomplex, with a homotopy equivalence `W' → M_{c+ε}` which is `h` followed by the inclusion on
`W` (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`).

So if `a ≤ b` are regular values with compact band `f⁻¹[a, b]` and `h : W → M_a` is a homotopy
equivalence from a CW complex, there is a CW complex `W'` with a closed embedding `j : W → W'`,
whose image has the homotopy extension property, and a homotopy equivalence `h' : W' → M_b` such
that `h' ∘ j` is `h` followed by the inclusion `M_a ⊆ M_b`. The `m`-cells of `W'` are the
`m`-cells of `W`, with their characteristic maps followed by `j`, together with one cell for each
critical point of index `m` with value in `(a, b]`
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel`).
The comparison maps commute strictly with the inclusions of the models and of the sublevels, and
both inclusions are closed cofibrations (for the sublevels at regular values,
`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`), which is what a
tower of models along an exhaustion of `M` by sublevels requires. For compact `M`, starting below
the minimum of `f`, where the sublevel is empty, and ending above its maximum, where the sublevel
is `M`, gives the CW model of `M`.

## Main results

* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel`: a CW model of `M_a` extends to a CW
  model of `M_b` along a closed cofibration, compatibly with the inclusion `M_a ⊆ M_b`, by one new
  `λ`-cell for each critical point of index `λ` with value in `(a, b]`.
* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`: **the CW model of a compact
  manifold.** A compact boundaryless manifold with a Morse function `f` is homotopy equivalent to
  a finite CW complex whose `λ`-cells are in bijection with the critical points of `f` of index
  `λ`.
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
`λ` on the level `c`, by a homotopy equivalence which is the inclusion on `M_{c-ε}`, and these
are the only critical points with values in `[c - ε, c + ε]`. -/
private theorem IsMorse.exists_homotopyEquiv_sigmaDiskAdjunction (hf : IsMorse I f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} ∧
      ∃ a : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
          C(TopCat.diskBoundary.{u} (manifoldMorseIndex I f p), {x | f x ≤ c - ε}),
        letI := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
          manifoldMorseIndex I f p
        ∃ e : relCWAdjunctionSpace (univ.sigma fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
            (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p)))) (sigmaDiskAttachingMap a) ≃ₕ
              {x | f x ≤ c + ε},
          ∀ x, e (pushout.inr (relCWBaseInclusion (univ.sigma
            fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
              (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p)))))
                (TopCat.ofHom (sigmaDiskAttachingMap a)) x) =
            sublevelInclusion f (c - ε) (c + ε) (by linarith) x := by
  let := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
    manifoldMorseIndex I f p
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
  -- The adjunction space is the pushout defining the cell attachment.
  let α := fun p ↦ (ψ p).toOpenPartialHomeomorph.morseAttachingMap manifoldMorseIndex_le_finrank
    hε.le (hball p) (hψ p)
  let hP := isPushout_morseCellAttachment (fun p ↦ (ψ p).toOpenPartialHomeomorph)
    (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hball hψ hε.le
  let ι := sigmaDiskAdjunctionIsoPushout α ≪≫ hP.isoPushout.symm
  refine ⟨ε, hε, hεδ'.trans hδ'δ,
    fun x hx ↦ hsub ⟨hx.1, Icc_subset_Icc (by linarith) (by linarith) hx.2⟩,
    fun p ↦ (α p).hom, (TopCat.homeoOfIso ι).toHomotopyEquiv.trans e, fun x ↦ Subtype.ext ?_⟩
  -- On `M_{c-ε}`, the identification of the two pushouts is the inclusion of `M_{c-ε}`.
  have hι : ι.hom (pushout.inr (relCWBaseInclusion (univ.sigma
      fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
        (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p)))))
          (TopCat.ofHom (sigmaDiskAttachingMap fun p ↦ (α p).hom)) x) =
      morseCellAttachmentIncl (fun p ↦ (ψ p).toOpenPartialHomeomorph) (manifoldMorseIndex I f ·)
        (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball hψ x := by
    rw [← ConcreteCategory.comp_apply, Iso.trans_hom, Iso.symm_hom,
      inr_sigmaDiskAdjunctionIsoPushout_hom_assoc, hP.inl_isoPushout_inv]
  rw [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
    TopCat.homeoOfIso_apply, hι, coe_sublevelInclusion_apply]
  exact coe_morseCellComparison_morseCellAttachmentIncl _ _ _ _ _ hε.le x

variable (I f) in
/-- For every CW model `h : W → M_s` of `M_s = {f ≤ s}` there is a CW model `h' : W' → M_t` of
`M_t` with a closed embedding `j : W → W'` such that `h' ∘ j` is `h` followed by the inclusion
`M_s ⊆ M_t`, and whose `m`-cells are those of `W`, with their characteristic maps followed by `j`,
together with one cell for each critical point of index `m` with value in `(s, t]`. The image of
`j` has the homotopy extension property. -/
private def CWModelExtends (s t : ℝ) (hst : s ≤ t) : Prop :=
  ∀ (W : Type u) [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    (h : W ≃ₕ {x | f x ≤ s}),
      ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
        (j : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ t}), IsClosedEmbedding j ∧
        HasHomotopyExtensionProperty (range j) ∧
        (∀ w, h' (j w) = sublevelInclusion f s t hst (h w)) ∧
        ∀ m, ∃ c : cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
            ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m},
          ∀ i x, map m (c.symm (.inl i)) x = j (map m i x)

/-- Across a compact band without critical points, the CW model is unchanged. -/
private theorem cwModelExtends_of_forall_notMem (hf : IsMorse I f) {s t : ℝ} (hst : s ≤ t)
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc s t) :
    CWModelExtends I f s t hst := by
  intro W _ _ _ h
  obtain ⟨e, he⟩ := exists_sublevelHomotopyEquiv hf.contMDiff hst hcompact
    fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩
  refine ⟨W, _, ‹_›, ‹_›, .id W, h.trans e, .id, ?_, fun w ↦ Subtype.ext ?_, fun m ↦ ?_⟩
  · rw [ContinuousMap.coe_id, range_id]
    exact isClopen_univ.hasHomotopyExtensionProperty
  · rw [ContinuousMap.HomotopyEquiv.trans_apply, ContinuousMap.id_apply,
      coe_sublevelInclusion_apply]
    exact he (h w)
  have : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m} :=
    ⟨fun x ↦ hcrit x x.2.1.1 (Ioc_subset_Icc_self x.2.1.2)⟩
  exact ⟨(Equiv.sumEmpty _ _).symm, fun _ _ ↦ rfl⟩

/-- Across one critical level, the CW model gains one `λ`-cell for each critical point of index
`λ` on the level. -/
private theorem IsMorse.exists_cwModelExtends_level (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ CWModelExtends I f (c - ε) (c + ε) (by linarith) := by
  obtain ⟨ε, hε, hεδ, hsub, a, e, he⟩ := hf.exists_homotopyEquiv_sigmaDiskAdjunction hδ hcompact
  refine ⟨ε, hε, hεδ, fun W _ _ _ h ↦ ?_⟩
  let := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
    manifoldMorseIndex I f p
  -- Attach the discs to `W` along attaching maps moved into its skeleta.
  obtain ⟨b, hb, -, Ψ, hΨ⟩ := h.exists_homotopyEquiv_sigmaDiskAdjunction a
  let := sigmaDiskAdjunctionCWComplex _ b hb
  refine ⟨_, _, inferInstance, sigmaDiskAdjunctionCWComplex _ b hb,
    (pushout.inr (relCWBaseInclusion _) (TopCat.ofHom (sigmaDiskAttachingMap b))).hom,
    Ψ.trans e, isClosedEmbedding_pushout_inr_relCWBaseInclusion _,
    (IsPushout.of_hasPushout _ _).hasHomotopyExtensionProperty_range_inr
      (isEmbedding_relCWBaseInclusion _) (hasHomotopyExtensionProperty_range_relCWBaseInclusion _),
    fun w ↦ ?_, fun m ↦ ?_⟩
  · rw [ContinuousMap.HomotopyEquiv.trans_apply]
    exact (congrArg e (hΨ w)).trans (he (h w))
  -- The new `m`-cells are the critical points of index `m` on the level `c`, which are those with
  -- values in `(c - ε, c + ε]`.
  let σ : {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = m} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (c - ε) (c + ε) | manifoldMorseIndex I f x = m} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (· ∈ criticalPoints I f ∩ f ⁻¹' {c}) (manifoldMorseIndex I f · = m)).trans
      (Equiv.subtypeEquivRight fun x ↦ by
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ioc]
        constructor
        · rintro ⟨⟨hx, rfl⟩, hi⟩
          exact ⟨⟨hx, by linarith, by linarith⟩, hi⟩
        · rintro ⟨⟨hx, h₁, h₂⟩, hi⟩
          exact ⟨⟨hx, hsub ⟨hx, h₁.le, h₂⟩⟩, hi⟩)
  exact ⟨(sigmaDiskAdjunctionCWComplexCellEquiv _ b hb m).trans (Equiv.sumCongr (.refl _) σ),
    fun i x ↦ by simp⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The CW models compose along `s ≤ m ≤ t`. -/
private theorem CWModelExtends.trans {s m t : ℝ} {hsm : s ≤ m} {hmt : m ≤ t}
    (h₁ : CWModelExtends I f s m hsm) (h₂ : CWModelExtends I f m t hmt) :
    CWModelExtends I f s t (hsm.trans hmt) := by
  intro W _ _ _ h
  obtain ⟨W₁, _, _, _, j₁, h₁', hj₁, hA₁, hh₁, hc₁⟩ := h₁ W h
  obtain ⟨W₂, _, _, _, j₂, h₂', hj₂, hA₂, hh₂, hc₂⟩ := h₂ W₁ h₁'
  refine ⟨W₂, _, ‹_›, ‹_›, j₂.comp j₁, h₂', hj₂.comp hj₁, ?_, fun w ↦ ?_, fun i ↦ ?_⟩
  · rw [ContinuousMap.coe_comp, range_comp]
    exact hA₁.image_of_isEmbedding hj₂.isEmbedding hA₂
  · rw [ContinuousMap.comp_apply, hh₂, hh₁, sublevelInclusion_sublevelInclusion]
  obtain ⟨c₁, hc₁⟩ := hc₁ i
  obtain ⟨c₂, hc₂⟩ := hc₂ i
  -- The critical points with values in `(s, t]` are those with values in `(s, m]` or in `(m, t]`.
  have hdisj : Disjoint
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s m | manifoldMorseIndex I f x = i}
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc m t | manifoldMorseIndex I f x = i} :=
    disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.1.2.2) hx'.1.2.1
  have hunion : {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s m | manifoldMorseIndex I f x = i} ∪
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc m t | manifoldMorseIndex I f x = i} =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = i} := by
    rw [← Ioc_union_Ioc_eq_Ioc hsm hmt]
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_union]
    tauto
  classical
  refine ⟨c₂.trans ((Equiv.sumCongr c₁ (.refl _)).trans ((Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (.refl _) ((Equiv.Set.union hdisj).symm.trans (Set.equivOfEq hunion))))),
    fun k x ↦ ?_⟩
  simp [hc₁, hc₂]

/-- **Compatible CW models of sublevels.** Let `f` be a Morse function and `a ≤ b` regular values
of `f` with compact band `f⁻¹[a, b]`, and let `h : W → M_a` be a homotopy equivalence from a CW
complex `W` to the sublevel `M_a = {f ≤ a}`. Then there are a CW complex `W'`, a closed embedding
`j : W → W'` whose image has the homotopy extension property, and a homotopy equivalence
`h' : W' → M_b` such that `h' ∘ j` is `h` followed by the inclusion `M_a ⊆ M_b`. For each `m`, the
`m`-cells of `W'` are the `m`-cells of `W`, whose characteristic maps in `W'` are those in `W`
followed by `j`, together with one cell for each critical point of index `m` with value in
`(a, b]`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u) [TopologicalSpace W] [T2Space W]
    [CWComplex (univ : Set W)] (h : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (j : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}), IsClosedEmbedding j ∧
      HasHomotopyExtensionProperty (range j) ∧
      (∀ w, h' (j w) = sublevelInclusion f a b hab (h w)) ∧
      ∀ m, ∃ c : cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ i x, map m (c.symm (.inl i)) x = j (map m i x) :=
  hf.band_induction (P := CWModelExtends I f) hab hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ cwModelExtends_of_forall_notMem hf hst hcompact hcrit)
    (fun _ _ _ _ _ hδ hcompact ↦ hf.exists_cwModelExtends_level hδ hcompact)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) W h

/-- **The CW model of a compact manifold.** A compact boundaryless manifold `M` carrying a Morse
function `f` is homotopy equivalent to a finite CW complex whose `m`-cells are in bijection with
the critical points of `f` of index `m`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv [CompactSpace M] (hf : IsMorse I f) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ M) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  -- Below the minimum of `f` the sublevel is empty, the empty CW complex.
  have : IsEmpty {x | f x ≤ a} := ⟨fun x ↦ (not_le.2 (hf' x).1) x.2⟩
  obtain ⟨W, _, _, _, _, e, -, -, -, hc⟩ := hf.exists_cwComplex_homotopyEquiv_sublevel hab
    hcompact ha hb PEmpty.{u + 1} Homeomorph.empty.toHomotopyEquiv
  -- The `m`-cells of `W` are the critical points of index `m`, since all values lie in `(a, b]`.
  have hcell (m : ℕ) : cell (univ : Set W) m ≃
      ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} := by
    have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ (map m j 0).elim⟩
    refine (hc m).choose.trans ((Equiv.emptySum _ _).trans (Set.equivOfEq ?_))
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    have := hf' x
    tauto
  -- Above the maximum of `f` the sublevel is all of `M`.
  have hM : {x | f x ≤ b} = univ := eq_univ_of_forall fun x ↦ (hf' x).2
  have : Finite (criticalPoints I f) := hf.finite_criticalPoints.to_subtype
  refine ⟨W, _, ‹_›, ‹_›, RelCWComplex.finite_of_finite_cells (.of_equiv _
      ((Equiv.sigmaFiberEquiv fun x : criticalPoints I f ↦ manifoldMorseIndex I f x).symm.trans
        (Equiv.sigmaCongrRight fun m ↦ ?_))),
    ⟨e.trans ((Homeomorph.setCongr hM).trans (Homeomorph.Set.univ M)).toHomotopyEquiv⟩,
    fun m ↦ ⟨hcell m⟩⟩
  exact (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ criticalPoints I f)
    (manifoldMorseIndex I f · = m)).trans (hcell m).symm

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
