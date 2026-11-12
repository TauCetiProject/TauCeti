/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Adjunction
public import TauCeti.Topology.CWComplex.Classical.AdjunctionModel
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
import TauCeti.Geometry.Manifold.Morse.Deformation.Cofibration
import TauCeti.Geometry.Manifold.Morse.Exhaustion
import TauCeti.Geometry.Manifold.Morse.Generic.Basic
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.Category.TopCat.DisjointOpens
import TauCeti.Topology.CWComplex.Classical.TowerUnion
import TauCeti.Topology.Homotopy.Extension.Tower
import TauCeti.Topology.Homotopy.Extension.Pushout

/-!
# The CW model of a manifold with a Morse function

Let `f` be a Morse function on a compact boundaryless manifold `M`. Then `M` is homotopy
equivalent to a finite CW complex whose `λ`-cells are labelled by the critical points of `f` of
index `λ` (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`). In particular every compact
smooth boundaryless manifold, which carries a Morse function by `TauCeti.exists_isMorse`, has
finite CW type (`TauCeti.FiniteCWType.of_isManifold`).

The model is built one critical level at a time, along the sublevels `M_a = {f ≤ a}`. Across a
compact band without critical points the sublevel keeps its homotopy type
(`TauCeti.exists_sublevelHomotopyEquiv`). Across a critical value `c`, for small `ε > 0` the
sublevel `M_{c+ε}` is homotopy equivalent to `M_{c-ε}` with one `λ`-disc attached at each critical
point of index `λ` on the level (`TauCeti.IsMorse.exists_morseCellAttachment_deformation`). If
`W` is a CW complex homotopy equivalent to `M_{c-ε}`, the attaching maps can be moved into the
skeleta of `W` by cellular approximation, and attaching the discs to `W` along them gives a CW
complex homotopy equivalent to `M_{c+ε}`, with the cells of `W` and one new `λ`-cell for each
critical point (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`). This
equivalence is the given one on `W`, and the equivalence of the attachment with `M_{c+ε}` is the
inclusion on `M_{c-ε}`, so the new model contains the old one as a subcomplex and its homotopy
equivalence extends the old one.

So when `a ≤ b` are regular values with compact band `f⁻¹[a, b]`, every CW model
`h : W ≃ₕ M_a` extends to a CW model `h' : W' ≃ₕ M_b`: there is a closed embedding `ι : W → W'`
whose image has the homotopy extension property, carrying the cells of `W` to cells of `W'` with
their characteristic maps, `h' ∘ ι` is `h` followed by the inclusion `M_a ⊆ M_b`, and the other
`λ`-cells of `W'` correspond to the critical points of index `λ` with value in `(a, b]`
(`TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel`). Iterated along an
increasing sequence of regular values, this gives CW models of the sublevels, each a subcomplex of
the next along a closed cofibration, whose homotopy equivalences to the sublevels commute with the
inclusions. The inclusions of sublevels at regular values are closed cofibrations too
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`), which is what
a tower of models along an exhaustion of `M` by sublevels requires. For compact
`M`, starting below the minimum of `f`, where the sublevel is empty, and ending above its maximum,
where the sublevel is `M`, gives the CW model of `M`.

If `f` is proper and bounded below, but `M` need not be compact, the sublevels at an increasing
sequence of regular values `a n → ∞` exhaust `M`, starting from the empty sublevel
(`TauCeti.IsMorse.exists_regular_sublevel_exhaustion`). Iterating the extension along it gives a
tower `W 0 → W 1 → ⋯` of CW models of the sublevels `M_{a n}` along cellular closed cofibrations.
Its colimit is a CW complex (`TauCeti.exists_cwComplex_of_isColimit`), Hausdorff because the
inclusions of the models extend disjoint open sets
(`TauCeti.TopCat.t2Space_of_isColimit_of_map_succ`), and its cells are the critical points of `f`.
Both the colimit and `M` carry the topology coherent with their towers of closed cofibrations, so
the homotopy equivalences of the stages assemble to a homotopy equivalence of the colimit with `M`
(`TauCeti.exists_homotopyEquiv_of_isCoherentWith`). This is the CW model of `M`
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`); it has infinitely many cells when `f` has
infinitely many critical points.

The same construction works for relative CW complexes: a CW model `h : W ≃ₕ M_a` relative to a
base `D ⊆ W` extends to a CW model of `M_b` relative to the image of `D`
(`TauCeti.IsMorse.exists_relCWComplex_extension_homotopyEquiv_sublevel`), since cellular
approximation moves the attaching maps into the relative skeleta of `W`. Starting from `M_a`
itself, a CW complex relative to itself with no cells, this gives the relative CW model of a
regular band: `M_b` is homotopy equivalent, by a homotopy equivalence which is the inclusion on
`M_a`, to `M_a` with one `λ`-cell attached for each critical point of index `λ` with value in
`(a, b]`, arranged as a CW complex relative to `M_a`
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`). No CW structure on `M_a` and no
compactness of `M` is needed.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_extension_homotopyEquiv_sublevel`: a relative CW model of
  `M_a` extends to a relative CW model of `M_b` along a closed cofibration, with one new `λ`-cell
  for each critical point of index `λ` with value in `(a, b]`.
* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`: **the relative CW model of a
  regular band.** `M_b` is homotopy equivalent to a CW complex relative to a copy of `M_a`, with
  one `λ`-cell for each critical point of index `λ` with value in `(a, b]`.
* `TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel`: a CW model of `M_a`
  extends to a CW model of `M_b` containing it as a subcomplex along a closed cofibration, with
  one new `λ`-cell for each critical point of index `λ` with value in `(a, b]`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel`: if `M_a` has a finite CW model,
  then so does `M_b`, with one more `λ`-cell in the count for each critical point of index `λ`
  with value in `(a, b]`.
* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`: **the CW model of a compact
  manifold.** A compact boundaryless manifold with a Morse function `f` is homotopy equivalent to
  a finite CW complex whose `λ`-cells are in bijection with the critical points of `f` of index
  `λ`.
* `TauCeti.IsMorse.finiteCWType` and `TauCeti.FiniteCWType.of_isManifold`: compact boundaryless
  smooth manifolds have finite CW type.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a manifold with a proper
  Morse function bounded below.** `M` is homotopy equivalent to a Hausdorff CW complex whose
  `λ`-cells are in bijection with the critical points of `f` of index `λ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof (Lemmas 3.6 and 3.7).
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorem 5.7, for the relative CW model of a regular band.
-/

public section

noncomputable section

open Set Filter Topology Topology.RelCWComplex CategoryTheory Limits
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **Crossing a critical level by an adjunction space.** If the band `f⁻¹[c - δ, c + δ]` of a
Morse function is compact, then for some `0 < ε ≤ δ` the sublevel `M_{c+ε}` is homotopy equivalent
to the space obtained from `M_{c-ε}` by attaching one `λ`-disc for each critical point of index
`λ` on the level `c`, by a homotopy equivalence which is the inclusion on `M_{c-ε}`, and these are
the only critical points with values in `[c - ε, c + ε]`. -/
private theorem IsMorse.exists_homotopyEquiv_sigmaDiskAdjunction (hf : IsMorse I f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} ∧
      ∃ a : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
          C(TopCat.diskBoundary.{u} (manifoldMorseIndex I f p), {x | f x ≤ c - ε}),
        letI := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
          manifoldMorseIndex I f p
        ∃ e : relCWAdjunctionSpace (univ.sigma fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
            (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p)))) (sigmaDiskAttachingMap a) ≃ₕ
              {x | f x ≤ c + ε},
          ∀ z, (e (pushout.inr (relCWBaseInclusion
            (univ.sigma fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
              (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p)))))
              (TopCat.ofHom (sigmaDiskAttachingMap a)) z) : M) = z := by
  -- Shrink the band so that its only critical points lie on the level `c`, and cross it.
  obtain ⟨ε, hε, hεδ, hsub⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  obtain ⟨ε', hε', -, -, ψ, -, -, hball, hψ, r, -, h⟩ :=
    hf.exists_homotopyEquiv_sigmaDiskAdjunctionSpace (a := c - ε) (b := c + ε) (by linarith)
      (by linarith) (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
        (preimage_mono (Icc_subset_Icc (by linarith) (by linarith))))
      fun x hx hfx ↦ hsub ⟨hx, hfx⟩
  exact ⟨ε, hε, hεδ, hsub, _, h⟩

variable (I f) in
/-- Every relative CW model `h : W ≃ₕ M_s` of the sublevel `M_s = {f ≤ s}`, a CW complex `W`
relative to a base `D`, extends to a relative CW model `h' : W' ≃ₕ M_t` relative to the image of
`D`: `W` is embedded in `W'` along a closed embedding `ι` whose image has the homotopy extension
property and which extends disjoint open sets, `h'` restricts to `h` on `W`, and in each dimension
`m` the cells of `W'` are those of `W` together with one cell for each critical point of index `m`
with value in `(s, t]`. -/
private def CWModelExtends (s t : ℝ) (_ : s ≤ t) : Prop :=
  ∀ (W : Type u) [TopologicalSpace W] [T2Space W] (D : Set W) [RelCWComplex (univ : Set W) D]
    (h : W ≃ₕ {x | f x ≤ s}),
      ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (ι : C(W, W')) (D' : Set W')
        (_ : RelCWComplex (univ : Set W') D') (h' : W' ≃ₕ {x | f x ≤ t}),
        D' = ι '' D ∧ IsClosedEmbedding ι ∧ HasHomotopyExtensionProperty (range ι) ∧
        TopCat.extendsDisjointOpens (TopCat.ofHom ι) ∧ (∀ w, (h' (ι w) : M) = h w) ∧
        ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
            ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m},
          ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x)

/-- Across a compact band without critical points, the CW model is unchanged. -/
private theorem cwModelExtends_of_forall_notMem (hf : IsMorse I f) {s t : ℝ} (hst : s ≤ t)
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc s t) :
    CWModelExtends I f s t hst := by
  intro W _ _ D _ h
  obtain ⟨e', he'⟩ := exists_sublevelHomotopyEquiv hf.contMDiff hst hcompact
    fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩
  have (m : ℕ) : IsEmpty
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m} :=
    ⟨fun x ↦ hcrit x x.2.1.1 (Ioc_subset_Icc_self x.2.1.2)⟩
  refine ⟨W, _, ‹_›, .id W, D, ‹_›, h.trans e', (image_id D).symm, .id, ?_, ?_,
    fun w ↦ he' (h w), fun m ↦ (Equiv.sumEmpty _ _).symm, fun m j x ↦ rfl⟩
  · rw [ContinuousMap.coe_id, range_id]
    exact isClopen_univ.hasHomotopyExtensionProperty
  · rw [TopCat.ofHom_id]
    exact MorphismProperty.id_mem _ _

/-- Across one critical level, the CW model gains one `λ`-cell for each critical point of index
`λ` on the level. -/
private theorem IsMorse.exists_cwModelExtends_level (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ CWModelExtends I f (c - ε) (c + ε) (by linarith) := by
  obtain ⟨ε, hε, hεδ, hsub, a, e, he⟩ := hf.exists_homotopyEquiv_sigmaDiskAdjunction hδ hcompact
  refine ⟨ε, hε, hεδ, fun W _ _ D _ h ↦ ?_⟩
  let := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
    manifoldMorseIndex I f p
  -- Attach the discs to `W` along attaching maps moved into its skeleta.
  obtain ⟨b, hb, -, Ψ, hΨ⟩ := h.exists_homotopyEquiv_sigmaDiskAdjunction a
  let := sigmaDiskAdjunctionRelCWComplex _ b hb
  -- The new `m`-cells are the critical points of index `m` on the level `c`, which are those with
  -- values in `(c - ε, c + ε]`.
  let T (m : ℕ) : {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = m} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (c - ε) (c + ε) | manifoldMorseIndex I f x = m} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ criticalPoints I f ∩ f ⁻¹' {c})
      (manifoldMorseIndex I f · = m)).trans <| Equiv.subtypeEquivRight fun x ↦ by
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ioc, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hx, rfl⟩, hi⟩
          exact ⟨⟨hx, by linarith, by linarith⟩, hi⟩
        · rintro ⟨⟨hx, h₁, h₂⟩, hi⟩
          exact ⟨⟨hx, hsub ⟨hx, h₁.le, h₂⟩⟩, hi⟩
  refine ⟨_, _, inferInstance, (pushout.inr _ (TopCat.ofHom (sigmaDiskAttachingMap b))).hom, _,
    sigmaDiskAdjunctionRelCWComplex _ b hb, Ψ.trans e, rfl,
    isClosedEmbedding_pushout_inr_relCWBaseInclusion _,
    (IsPushout.of_hasPushout _ _).hasHomotopyExtensionProperty_range_inr
      (isEmbedding_relCWBaseInclusion _) (hasHomotopyExtensionProperty_range_relCWBaseInclusion _),
    ?_, fun w ↦ ?_,
    fun m ↦ (sigmaDiskAdjunctionRelCWComplexCellEquiv _ b hb m).trans
      (Equiv.sumCongr (.refl _) (T m)), fun m j x ↦ ?_⟩
  · -- Attaching the discs is the cobase change of the coproduct of the boundary inclusions of the
    -- discs, which extend disjoint open sets.
    rw [TopCat.ofHom_hom, (Iso.eq_comp_inv _).2
      (inr_sigmaDiskAdjunctionIsoPushout_hom (Z := TopCat.of W) fun p ↦ TopCat.ofHom (b p))]
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isPushout
      (IsPushout.of_hasPushout _ _) (MorphismProperty.colimMap _ fun _ ↦
        TopCat.extendsDisjointOpens_diskBoundaryInclusion _)) (MorphismProperty.of_isIso _ _)
  · rw [ContinuousMap.HomotopyEquiv.trans_apply, hΨ, he]
  · simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The CW models compose along `s ≤ m ≤ t`. -/
private theorem CWModelExtends.trans {s m t : ℝ} {hsm : s ≤ m} {hmt : m ≤ t}
    (h₁ : CWModelExtends I f s m hsm) (h₂ : CWModelExtends I f m t hmt) :
    CWModelExtends I f s t (hsm.trans hmt) := by
  classical
  intro W _ _ D _ h
  obtain ⟨W₁, _, _, ι₁, D₁, _, h₁', rfl, hι₁, hA₁, hd₁, hh₁, e₁, he₁⟩ := h₁ W D h
  obtain ⟨W₂, _, _, ι₂, D₂, _, h₂', rfl, hι₂, hA₂, hd₂, hh₂, e₂, he₂⟩ := h₂ W₁ (ι₁ '' D) h₁'
  -- The critical points with values in `(s, t]` are those with values in `(s, m]` or `(m, t]`.
  let U (i : ℕ) :
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s m | manifoldMorseIndex I f x = i} ⊕
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc m t | manifoldMorseIndex I f x = i} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = i} :=
    (Equiv.Set.union (s := {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s m | manifoldMorseIndex I f x = i})
      (t := {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc m t | manifoldMorseIndex I f x = i})
      (disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.1.2.2) hx'.1.2.1)).symm.trans
      (Set.equivOfEq <| by
        ext x
        simp only [mem_union, mem_ofPred_eq, mem_inter_iff, mem_preimage,
          ← Ioc_union_Ioc_eq_Ioc hsm hmt]
        tauto)
  refine ⟨W₂, _, ‹_›, ι₂.comp ι₁, _, ‹_›, h₂', image_image ι₂ ι₁ D, hι₂.comp hι₁, ?_,
    MorphismProperty.comp_mem _ (TopCat.ofHom ι₁) (TopCat.ofHom ι₂) hd₁ hd₂,
    fun w ↦ (hh₂ _).trans (hh₁ w),
    fun i ↦ (e₂ i).trans ((Equiv.sumCongr (e₁ i) (.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (.refl _) (U i)))), fun i j x ↦ ?_⟩
  · rw [ContinuousMap.coe_comp, range_comp]
    exact hA₁.image_of_isEmbedding hι₂.isEmbedding hA₂
  simp [he₁, he₂]

/-- Across a compact band between regular values, every relative CW model extends. -/
private theorem IsMorse.cwModelExtends (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) : CWModelExtends I f a b hab :=
  hf.band_induction (P := CWModelExtends I f) hab hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ cwModelExtends_of_forall_notMem hf hst hcompact hcrit)
    (fun _ _ _ _ _ hδ hcompact ↦ hf.exists_cwModelExtends_level hδ hcompact)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂)

/-- **Extending relative CW models of sublevels.** Let `f` be a Morse function and `a ≤ b` regular
values of `f` with compact band `f⁻¹[a, b]`, and let `h : W ≃ₕ M_a` be a homotopy equivalence from a
CW complex `W` relative to a base `D` to the sublevel `M_a = {f ≤ a}`. Then there are a space `W'`
which is a CW complex relative to the image `D'` of `D` under a closed embedding `ι : W → W'` whose
image has the homotopy extension property, and a homotopy equivalence `h' : W' ≃ₕ M_b` extending
`h`: `h' ∘ ι` is `h` followed by the inclusion `M_a ⊆ M_b`. The cells of `W` are cells of `W'`
along `ι`, with the same characteristic maps followed by `ι`, and in each dimension `m` the other
`m`-cells of `W'` correspond to the critical points of index `m` with value in `(a, b]`. -/
theorem IsMorse.exists_relCWComplex_extension_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u) [TopologicalSpace W] [T2Space W] (D : Set W)
    [RelCWComplex (univ : Set W) D] (h : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (ι : C(W, W')) (D' : Set W')
      (_ : RelCWComplex (univ : Set W') D') (h' : W' ≃ₕ {x | f x ≤ b}),
      D' = ι '' D ∧ IsClosedEmbedding ι ∧ HasHomotopyExtensionProperty (range ι) ∧
      (∀ w, (h' (ι w) : M) = h w) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, ι, D', _, h', hD', hι, hA, -, hh, e, he⟩ :=
    hf.cwModelExtends hab hcompact ha hb W D h
  exact ⟨W', _, ‹_›, ι, D', ‹_›, h', hD', hι, hA, hh, e, he⟩

/-- **Extending CW models of sublevels.** Let `f` be a Morse function and `a ≤ b` regular values of
`f` with compact band `f⁻¹[a, b]`, and let `h : W ≃ₕ M_a` be a homotopy equivalence from a CW
complex `W` to the sublevel `M_a = {f ≤ a}`. Then there are a CW complex `W'`, a closed embedding
`ι : W → W'` whose image has the homotopy extension property, and a homotopy equivalence
`h' : W' ≃ₕ M_b` extending `h`: `h' ∘ ι` is `h` followed
by the inclusion `M_a ⊆ M_b`. The cells of `W` are cells of `W'` along `ι`, with the same
characteristic maps followed by `ι`, and in each dimension `m` the other `m`-cells of `W'`
correspond to the critical points of index `m` with value in `(a, b]`. -/
theorem IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u) [TopologicalSpace W] [T2Space W]
    [CWComplex (univ : Set W)] (h : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (ι : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}),
      IsClosedEmbedding ι ∧ HasHomotopyExtensionProperty (range ι) ∧
      (∀ w, (h' (ι w) : M) = h w) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, ι, D', _, h', hD', hι, hA, hh, e, he⟩ :=
    hf.exists_relCWComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W ∅ h
  -- The base of `W'` is the image of the empty base of `W`.
  rw [image_empty] at hD'
  subst hD'
  exact ⟨W', _, ‹_›, RelCWComplex.toCWComplex _, ι, h', hι, hA, hh, e, he⟩

/-- **The relative CW model of a regular band.** Let `f` be a Morse function and `a ≤ b` regular
values of `f` with compact band `f⁻¹[a, b]`. Then the sublevel `M_b = {f ≤ b}` is homotopy
equivalent to a CW complex `X` relative to a copy of `M_a = {f ≤ a}`, with one `m`-cell for each
critical point of index `m` with value in `(a, b]`: there are a closed embedding `j : M_a → X`, a
relative CW structure on `X` with base the image of `j`, and a homotopy equivalence
`h : X ≃ₕ M_b` such that `h ∘ j` is the inclusion `M_a ⊆ M_b`. No CW structure on `M_a` is
needed. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C({x | f x ≤ a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ {x | f x ≤ b}),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  -- Start from `M_a`, a CW complex relative to itself with no cells.
  let := relCWComplexSelf (univ : Set {x | f x ≤ a}) isClosed_univ
  obtain ⟨X, _, _, j, D', _, h, hD', hj, -, hh, e, -⟩ :=
    hf.exists_relCWComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb {x | f x ≤ a}
      univ (.refl _)
  rw [image_univ] at hD'
  subst hD'
  exact ⟨X, _, ‹_›, j, ‹_›, h, hj, hh, ⟨fun m ↦ (e m).trans (Equiv.emptySum _ _)⟩⟩

/-- **CW models of sublevels.** Let `f` be a Morse function and `a ≤ b` regular values of `f`
with compact band `f⁻¹[a, b]`. If `W` is a finite CW complex homotopy equivalent to the sublevel
`M_a = {f ≤ a}`, then `M_b` is homotopy equivalent to a finite CW complex `W'` whose number of
`m`-cells, in each dimension `m`, is that of `W` plus the number of critical points of index `m`
with value in `(a, b]`. The model `W'` can be chosen to contain `W` as a subcomplex
(`TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel`). -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u) [TopologicalSpace W] [T2Space W]
    [CWComplex (univ : Set W)] [RelCWComplex.Finite (univ : Set W)] (e : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W')),
      RelCWComplex.Finite (univ : Set W') ∧ Nonempty (W' ≃ₕ {x | f x ≤ b}) ∧
      ∀ m, ENat.card (cell (univ : Set W') m) = ENat.card (cell (univ : Set W) m) +
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}.encard := by
  obtain ⟨W', _, _, _, -, h', -, -, -, c, -⟩ :=
    hf.exists_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W e
  -- Only finitely many critical points lie in the compact band.
  have hS : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set W))
  have := hS.to_subtype
  have : Finite (Σ m, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) :=
    .of_injective (fun x ↦ (⟨x.2, x.2.2.1⟩ : ↥(criticalPoints I f ∩ f ⁻¹' Ioc a b)))
      fun ⟨_, _, hx⟩ ⟨_, _, hy⟩ hxy ↦ by
        cases Subtype.ext_iff.1 hxy
        cases hx.2.symm.trans hy.2
        rfl
  refine ⟨W', _, ‹_›, ‹_›, RelCWComplex.finite_of_finite_cells
    (.of_equiv _ ((Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight c).symm)),
    ⟨h'⟩, fun m ↦ ?_⟩
  rw [ENat.card_congr (c m), ENat.card_sum, ENat.card_coe_set_eq]

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
  obtain ⟨W, _, _, _, -, e, -, -, -, c, -⟩ := hf.exists_cwComplex_extension_homotopyEquiv_sublevel
    hab hcompact ha hb PEmpty.{u + 1} Homeomorph.empty.toHomotopyEquiv
  -- The `m`-cells of `W` are the critical points of index `m`, since all values lie in `(a, b]`.
  have hcell (m : ℕ) : cell (univ : Set W) m ≃
      ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} := by
    have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ (map m j 0).elim⟩
    refine (c m).trans ((Equiv.emptySum _ _).trans (Set.equivOfEq ?_))
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

variable (f) in
/-- A CW model of the sublevel `M_s = {f ≤ s}`: a Hausdorff CW complex with a homotopy equivalence
to the sublevel. -/
private structure SublevelCWModel (s : ℝ) where
  /-- The CW complex. -/
  W : Type u
  [top : TopologicalSpace W]
  [t2 : T2Space W]
  [cw : CWComplex (univ : Set W)]
  /-- The homotopy equivalence with the sublevel. -/
  h : W ≃ₕ {x | f x ≤ s}

attribute [local instance] SublevelCWModel.top SublevelCWModel.t2 SublevelCWModel.cw

/-- A CW model of `M_s` extends to a CW model of `M_t` across a compact band between regular
values, along a closed cofibration which extends disjoint open sets and preserves the cells. -/
private theorem IsMorse.exists_sublevelCWModel_extension (hf : IsMorse I f) {s t : ℝ}
    (hst : s ≤ t) (hcompact : IsCompact (f ⁻¹' Icc s t)) (hs : IsRegularValue I 𝓘(ℝ) f s)
    (ht : IsRegularValue I 𝓘(ℝ) f t) (S : SublevelCWModel f s) :
    ∃ (S' : SublevelCWModel f t) (ι : C(S.W, S'.W)), IsClosedEmbedding ι ∧
      HasHomotopyExtensionProperty (range ι) ∧ TopCat.extendsDisjointOpens (TopCat.ofHom ι) ∧
      (∀ w, (S'.h (ι w) : M) = S.h w) ∧
      ∃ e : ∀ m, cell (univ : Set S'.W) m ≃ cell (univ : Set S.W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, ι, D', _, h', hD', hι, hA, hd, hh, e, he⟩ :=
    hf.cwModelExtends hst hcompact hs ht S.W ∅ S.h
  -- The base of `W'` is the image of the empty base of `S.W`.
  rw [image_empty] at hD'
  subst hD'
  let := RelCWComplex.toCWComplex (univ : Set W')
  exact ⟨⟨W', h'⟩, ι, hι, hA, hd, hh, e, he⟩

/-- The tower of CW models obtained from `S₀` by applying the extensions `next n`. -/
private def sublevelCWModelTower {a : ℕ → ℝ} (S₀ : SublevelCWModel f (a 0))
    (next : ∀ n, SublevelCWModel f (a n) → SublevelCWModel f (a (n + 1))) :
    ∀ n, SublevelCWModel f (a n)
  | 0 => S₀
  | n + 1 => next n (sublevelCWModelTower S₀ next n)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If `a` is a strictly increasing sequence tending to infinity with `a 0` below every value of
`f`, the critical points of index `m` are split by the intervals `(a k, a (k + 1)]` containing
their values. -/
private def sigmaCriticalPointsIocEquiv {a : ℕ → ℝ} (ha : StrictMono a)
    (htop : Tendsto a atTop atTop) (ha0 : ∀ x, a 0 < f x) (m : ℕ) :
    (Σ k, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) |
      manifoldMorseIndex I f x = m}) ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
  -- Each value lies in at most one of the intervals.
  have hIoc {k k' : ℕ} {x : M} (hx : f x ∈ Ioc (a k) (a (k + 1)))
      (hx' : f x ∈ Ioc (a k') (a (k' + 1))) : k ≤ k' := by
    by_contra! hk
    linarith [hx.1, hx'.2, ha.monotone (Nat.succ_le_of_lt hk)]
  Equiv.ofBijective (fun p ↦ ⟨p.2.1, p.2.2.1.1, p.2.2.2⟩) <| by
    refine ⟨fun ⟨k, x, hx⟩ ⟨k', x', hx'⟩ h ↦ ?_, fun ⟨x, hx, hm⟩ ↦ ?_⟩
    · obtain rfl : x = x' := congrArg Subtype.val h
      exact Sigma.subtype_ext (le_antisymm (hIoc hx.1.2 hx'.1.2) (hIoc hx'.1.2 hx.1.2)) rfl
    · -- The interval containing `f x` ends at the first `a (k + 1)` above `f x`.
      have hex : ∃ n, f x ≤ a n := (htop.eventually_ge_atTop (f x)).exists
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero fun h0 ↦
        (ha0 x).not_ge (h0 ▸ Nat.find_spec hex)
      have hle : f x ≤ a (k + 1) := hk ▸ Nat.find_spec hex
      have hlt : a k < f x := lt_of_not_ge (Nat.find_min hex (hk ▸ k.lt_succ_self))
      exact ⟨⟨k, x, ⟨hx, hlt, hle⟩, hm⟩, rfl⟩

/-- **The CW model of a manifold with a proper Morse function.** A boundaryless manifold `M`
carrying a proper Morse function `f` which is bounded below is homotopy equivalent to a Hausdorff
CW complex whose `m`-cells are in bijection with the critical points of `f` of index `m`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      Nonempty (W ≃ₕ M) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨a, K, ha, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x := by
    have hx : x ∉ K 0 := hK0 ▸ notMem_empty x
    rw [hK] at hx
    exact lt_of_not_ge hx
  -- The tower of CW models `S n` of the sublevels `M_{a n}`, starting from the empty sublevel,
  -- with the cell-preserving closed cofibrations `j n : S n → S (n + 1)`.
  choose S' ι hι hA hd hh e he using fun n (S : SublevelCWModel f (a n)) ↦
    hf.exists_sublevelCWModel_extension (ha.monotone n.le_succ)
      (hp.isCompact_preimage isCompact_Icc) (hreg n) (hreg (n + 1)) S
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (ha0 x).not_ge x.2⟩
  let S := sublevelCWModelTower ⟨PEmpty.{u + 1}, Homeomorph.empty.toHomotopyEquiv⟩ S'
  let j (n : ℕ) : C((S n).W, (S (n + 1)).W) := ι n (S n)
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun n ↦ TopCat.of (S n).W) fun n ↦ TopCat.ofHom (j n)
  have hF (n : ℕ) : F.map (homOfLE n.le_succ) = TopCat.ofHom (j n) :=
    Functor.ofSequence_map_homOfLE_succ _ n
  have hFce (n : ℕ) : IsClosedEmbedding (F.map (homOfLE n.le_succ)) := hF n ▸ hι n (S n)
  -- The colimit `X` of the tower, with the closed embeddings `φ n` of its stages.
  let X : TopCat.{u} := colimit F
  let φ (n : ℕ) : C((S n).W, X) := (colimit.ι F n).hom
  have hφ (n : ℕ) (w : (S n).W) : φ (n + 1) (j n w) = φ n w := by
    have := colimit.w_apply F (homOfLE n.le_succ) w
    rw [hF] at this
    exact this
  have hce (n : ℕ) : IsClosedEmbedding (φ n) :=
    TopCat.isClosedEmbedding_ι_of_isColimit
      (fun _ _ ↦ TopCat.isClosedEmbedding_map_of_isWellOrderContinuous F fun n _ ↦ hFce n)
      (colimit.isColimit F) n
  -- `X` is a Hausdorff CW complex, whose cells are born one stage at a time.
  have : ∀ n, T2Space (F.obj n) := fun n ↦ (S n).t2
  have : T2Space X :=
    TopCat.t2Space_of_isColimit_of_map_succ (fun n ↦ hF n ▸ hd n (S n)) (colimit.isColimit F)
  let _ (n : ℕ) : CWComplex (univ : Set (F.obj n)) := (S n).cw
  let eF (k m : ℕ) : cell (univ : Set (F.obj (k + 1))) m ≃ cell (univ : Set (F.obj k)) m ⊕
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m} :=
    e k (S k) m
  let ιF (k m : ℕ) (i : cell (univ : Set (F.obj k)) m) : cell (univ : Set (F.obj (k + 1))) m :=
    (eF k m).symm (.inl i)
  obtain ⟨_, eX, -, -⟩ := exists_cwComplex_of_isColimit hFce ιF
    (fun k m i x ↦ by rw [hF]; exact he k (S k) m i x) (colimit.isColimit F)
  -- The `m`-cells born at stage `k + 1` are the critical points of index `m` with values in
  -- `(a k, a (k + 1)]`, and no cell is born at stage `0`.
  have hnew (k m : ℕ) : {i : cell (univ : Set (F.obj (k + 1))) m // i ∉ range (ιF k m)} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m} := by
    have hnot (x) : (eF k m).symm (.inr x) ∉ range (ιF k m) := by
      rintro ⟨i, hi⟩
      simpa [ιF] using congrArg (eF k m) hi
    refine (Equiv.ofBijective (fun x ↦ ⟨(eF k m).symm (.inr x), hnot x⟩)
      ⟨fun x y hxy ↦ Sum.inr_injective ((eF k m).symm.injective (congrArg Subtype.val hxy)),
        fun i ↦ ?_⟩).symm
    obtain ⟨i, hi⟩ := i
    rcases h : eF k m i with i' | x
    · exact (hi ⟨i', by simp [ιF, ← h]⟩).elim
    · exact ⟨x, Subtype.ext (by simp [← h])⟩
  have : ∀ m, IsEmpty (cell (univ : Set (F.obj 0)) m) :=
    fun m ↦ ⟨fun i ↦ (map m i 0 : PEmpty).elim⟩
  -- The homotopy equivalences of the stages with the sublevels induce a map `Φ : X → M`.
  let g : F ⟶ (Functor.const ℕ).obj (TopCat.of M) := NatTrans.ofSequence
    (fun n ↦ TopCat.ofHom ⟨fun w ↦ ((S n).h w : M),
      continuous_subtype_val.comp (S n).h.toFun.continuous⟩) fun n ↦ by
      rw [hF]
      ext w
      exact hh n (S n) w
  let Φ : C(X, M) := (colimit.desc F ⟨TopCat.of M, g⟩).hom
  have hΦ (n : ℕ) (w : (S n).W) : Φ (φ n w) = (S n).h w :=
    ConcreteCategory.congr_hom (colimit.ι_desc ⟨TopCat.of M, g⟩ n) w
  -- On the images `A n` of the stages, `Φ` is the homotopy equivalence with the sublevels. Both
  -- towers consist of closed cofibrations and carry the coherent topology, so `Φ` is a homotopy
  -- equivalence.
  let A (n : ℕ) : Set X := range (φ n)
  let E (n : ℕ) : (S n).W ≃ₜ A n := (hce n).isEmbedding.toHomeomorph
  have hAH (n : ℕ) : HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1))) := by
    have hset : E (n + 1) '' range (j n) = (↑) ⁻¹' A n := by
      ext y
      obtain ⟨w, rfl⟩ := (E (n + 1)).surjective y
      rw [(E (n + 1)).injective.mem_set_image, mem_preimage, IsEmbedding.toHomeomorph_apply_coe]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨v, (hφ n v).symm⟩
      · rintro ⟨v, hv⟩
        exact ⟨v, (hce (n + 1)).injective ((hφ n v).trans hv)⟩
    exact hset ▸ (hA n (S n)).image (E (n + 1))
  have hBH (n : ℕ) :
      HasHomotopyExtensionProperty ((↑) ⁻¹' {x | f x ≤ a n} : Set {x | f x ≤ a (n + 1)}) := by
    have := hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue hf.contMDiff
      (ha n.lt_succ_self) (hp.isCompact_preimage isCompact_Icc) (hreg n) (ha.monotone n.le_succ)
    have hset : range (sublevelInclusion f (a n) (a (n + 1)) (ha.monotone n.le_succ)) =
        (↑) ⁻¹' {x | f x ≤ a n} := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        rw [mem_preimage, coe_sublevelInclusion_apply]
        exact x.2
      · exact fun hy ↦ ⟨⟨y, hy⟩, Subtype.ext (coe_sublevelInclusion_apply _ _ _)⟩
    exact hset ▸ this
  have hBc : IsCoherentWith (range fun n ↦ {x | f x ≤ a n}) := .of_nhds fun x ↦ by
    obtain ⟨n, hn⟩ := (htop.eventually_gt_atTop (f x)).exists
    exact ⟨_, mem_range_self n, Filter.mem_of_superset
      ((isOpen_lt hf.contMDiff.continuous continuous_const).mem_nhds hn) fun _ hy ↦ le_of_lt hy⟩
  obtain ⟨h, -, -⟩ := exists_homotopyEquiv_of_isCoherentWith (A := A)
    (B := fun n ↦ {x | f x ≤ a n}) (monotone_nat_of_le_succ fun n ↦ by
      rintro _ ⟨w, rfl⟩
      exact ⟨j n w, hφ n w⟩)
    (fun _ _ hnm ↦ sublevel_mono f (ha.monotone hnm))
    (TopCat.iUnion_range_ι_of_isColimit (colimit.isColimit F))
    (eq_univ_of_forall fun x ↦ mem_iUnion.2 (htop.eventually_ge_atTop (f x)).exists)
    (TopCat.isCoherentWith_range_ι_of_isColimit (colimit.isColimit F)) hBc hAH hBH Φ
    (fun n ↦ (E n).symm.toHomotopyEquiv.trans (S n).h) fun n x ↦ by
      obtain ⟨w, rfl⟩ := (E n).surjective x
      rw [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
        Homeomorph.symm_apply_apply, ← hΦ]
      exact congrArg Φ ((hce n).isEmbedding.toHomeomorph_apply_coe w).symm
  exact ⟨X, _, ‹_›, ‹_›, ⟨h⟩, fun m ↦ ⟨(eX m).trans <| (Equiv.emptySum _ _).trans <|
    (Equiv.sigmaCongrRight fun k ↦ hnew k m).trans (sigmaCriticalPointsIocEquiv ha htop ha0 m)⟩⟩

end TauCeti
