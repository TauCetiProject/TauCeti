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
import TauCeti.Topology.Category.TopCat.Normal
import TauCeti.Topology.CWComplex.Classical.CompactSupport
import TauCeti.Topology.CWComplex.Classical.Image
import TauCeti.Topology.CWComplex.Classical.TowerUnion
import TauCeti.Topology.Homotopy.Extension.Pushout
import TauCeti.Topology.Homotopy.Extension.Tower

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

For a proper Morse function bounded below on a possibly noncompact `M`, the sublevels at an
increasing sequence of regular values `a 0 < a 1 < ⋯` tending to infinity exhaust `M`, starting
from the empty sublevel `M_{a 0}` (`TauCeti.IsMorse.exists_regular_sublevel_exhaustion`). The
extension step gives finite CW models `W k ≃ₕ M_{a k}`, each a subcomplex of the next along a
closed cofibration. Their colimit `X` is Hausdorff, since it is a sequential colimit of compact
Hausdorff spaces along closed embeddings, and it is a CW complex as the union of the tower of its
subcomplexes `W k` (`TauCeti.cwSubcomplexTowerUnion`). Both `X` and `M` carry the topology
coherent with their towers of closed cofibrations, so the homotopy equivalences of the stages,
which commute with the inclusions, glue to a homotopy equivalence `X ≃ₕ M`
(`TauCeti.exists_homotopyEquiv_of_isCoherentWith`). The `m`-cells of `X` are born at the stages,
one for each critical point of index `m` in each band `f⁻¹(a k, a (k + 1)]`, so they correspond to
all the critical points of index `m` (`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`). There may
be infinitely many of them, and then `X` has infinitely many cells.

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
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a proper Morse function.**
  A boundaryless manifold with a proper Morse function `f` bounded below is homotopy equivalent to a
  Hausdorff CW complex whose `λ`-cells are in bijection with the critical points of `f` of index
  `λ`.
* `TauCeti.IsMorse.finiteCWType` and `TauCeti.FiniteCWType.of_isManifold`: compact boundaryless
  smooth manifolds have finite CW type.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof (Lemmas 3.6 and 3.7).
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorem 5.7, for the relative CW model of a regular band.
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- Only finitely many critical points have values in a compact band. -/
private theorem IsMorse.finite_sigma_criticalPoints_inter_preimage_Ioc (hf : IsMorse I f)
    {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b)) :
    Finite (Σ m, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  have hS : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := hS.to_subtype
  exact .of_injective (fun x ↦ (⟨x.2, x.2.2.1⟩ : ↥(criticalPoints I f ∩ f ⁻¹' Ioc a b)))
    fun ⟨_, _, hx⟩ ⟨_, _, hy⟩ hxy ↦ by
      cases Subtype.ext_iff.1 hxy
      cases hx.2.symm.trans hy.2
      rfl

variable (I f) in
/-- Every relative CW model `h : W ≃ₕ M_s` of the sublevel `M_s = {f ≤ s}`, a CW complex `W`
relative to a base `D`, extends to a relative CW model `h' : W' ≃ₕ M_t` relative to the image of
`D`: `W` is embedded in `W'` along a closed embedding `ι` whose image has the homotopy extension
property, `h'` restricts to `h` on `W`, and in each dimension `m` the cells of `W'` are those of `W`
together with one cell for each critical point of index `m` with value in `(s, t]`. -/
private def CWModelExtends (s t : ℝ) (_ : s ≤ t) : Prop :=
  ∀ (W : Type u) [TopologicalSpace W] [T2Space W] (D : Set W) [RelCWComplex (univ : Set W) D]
    (h : W ≃ₕ {x | f x ≤ s}),
      ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (ι : C(W, W')) (D' : Set W')
        (_ : RelCWComplex (univ : Set W') D') (h' : W' ≃ₕ {x | f x ≤ t}),
        D' = ι '' D ∧ IsClosedEmbedding ι ∧ HasHomotopyExtensionProperty (range ι) ∧
        (∀ w, (h' (ι w) : M) = h w) ∧
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
  refine ⟨W, _, ‹_›, .id W, D, ‹_›, h.trans e', (image_id D).symm, .id, ?_,
    fun w ↦ he' (h w), fun m ↦ (Equiv.sumEmpty _ _).symm, fun m j x ↦ rfl⟩
  rw [ContinuousMap.coe_id, range_id]
  exact isClopen_univ.hasHomotopyExtensionProperty

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
    fun w ↦ ?_,
    fun m ↦ (sigmaDiskAdjunctionRelCWComplexCellEquiv _ b hb m).trans
      (Equiv.sumCongr (.refl _) (T m)), fun m j x ↦ ?_⟩
  · rw [ContinuousMap.HomotopyEquiv.trans_apply, hΨ, he]
  · simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The CW models compose along `s ≤ m ≤ t`. -/
private theorem CWModelExtends.trans {s m t : ℝ} {hsm : s ≤ m} {hmt : m ≤ t}
    (h₁ : CWModelExtends I f s m hsm) (h₂ : CWModelExtends I f m t hmt) :
    CWModelExtends I f s t (hsm.trans hmt) := by
  classical
  intro W _ _ D _ h
  obtain ⟨W₁, _, _, ι₁, D₁, _, h₁', rfl, hι₁, hA₁, hh₁, e₁, he₁⟩ := h₁ W D h
  obtain ⟨W₂, _, _, ι₂, D₂, _, h₂', rfl, hι₂, hA₂, hh₂, e₂, he₂⟩ := h₂ W₁ (ι₁ '' D) h₁'
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
    fun w ↦ (hh₂ _).trans (hh₁ w),
    fun i ↦ (e₂ i).trans ((Equiv.sumCongr (e₁ i) (.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (.refl _) (U i)))), fun i j x ↦ ?_⟩
  · rw [ContinuousMap.coe_comp, range_comp]
    exact hA₁.image_of_isEmbedding hι₂.isEmbedding hA₂
  simp [he₁, he₂]

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
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) :=
  hf.band_induction (P := CWModelExtends I f) hab hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ cwModelExtends_of_forall_notMem hf hst hcompact hcrit)
    (fun _ _ _ _ _ hδ hcompact ↦ hf.exists_cwModelExtends_level hδ hcompact)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) W D h

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
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set W))
  have := hf.finite_sigma_criticalPoints_inter_preimage_Ioc hcompact
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

/-! ### The CW model of a proper Morse function -/

variable (f) in
/-- A finite CW model of the sublevel `M_b = {f ≤ b}`: a finite CW complex in a Hausdorff space
`W`, with a homotopy equivalence `W ≃ₕ M_b`. -/
private structure SublevelCWModel (b : ℝ) : Type (u + 1) where
  /-- The space of the model. -/
  W : Type u
  [topologicalSpace : TopologicalSpace W]
  [t2Space : T2Space W]
  [cwComplex : CWComplex (univ : Set W)]
  [finite : RelCWComplex.Finite (univ : Set W)]
  /-- The homotopy equivalence with the sublevel. -/
  equiv : W ≃ₕ {x | f x ≤ b}

attribute [instance] SublevelCWModel.topologicalSpace SublevelCWModel.t2Space
  SublevelCWModel.cwComplex SublevelCWModel.finite

/-- One step of the tower of CW models: a finite CW model of `M_a` extends along a closed
cofibration to a finite CW model of `M_b`, with one new `m`-cell for each critical point of index
`m` with value in `(a, b]`. -/
private theorem IsMorse.exists_sublevelCWModel_extension (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (s : SublevelCWModel f a) :
    ∃ (t : SublevelCWModel f b) (ι : C(s.W, t.W)), IsClosedEmbedding ι ∧
      HasHomotopyExtensionProperty (range ι) ∧ (∀ w, (t.equiv (ι w) : M) = s.equiv w) ∧
      ∃ e : ∀ m, cell (univ : Set t.W) m ≃ cell (univ : Set s.W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', hι, hA, hh, e, he⟩ :=
    hf.exists_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb s.W s.equiv
  have := hf.finite_sigma_criticalPoints_inter_preimage_Ioc hcompact
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set s.W))
  have : RelCWComplex.Finite (univ : Set W') := RelCWComplex.finite_of_finite_cells
    (.of_equiv _ ((Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight e).symm))
  exact ⟨⟨W', h'⟩, ι, hι, hA, hh, e, he⟩

omit [T2Space M] in
/-- **The union of a tower of CW models of sublevels.** Let `a` be strictly increasing such that
every value of `f` lies below some `a k`, and each inclusion `M_{a k} ⊆ M_{a (k+1)}` is a closed
cofibration. Suppose given finite CW models `W k` of the sublevels `M_{a k}`, each embedded in the
next along a closed cofibration `ι k` compatible with the homotopy equivalences, and carrying cells
to cells along `c k`. Then `M` is homotopy equivalent to a Hausdorff CW complex whose `m`-cells are
the `m`-cells of `W 0` together with the `m`-cells of each `W (k + 1)` not coming from `W k`. -/
private theorem exists_cwComplex_homotopyEquiv_of_tower (hfc : Continuous f) {a : ℕ → ℝ}
    (ha : StrictMono a) (hcov : ∀ x, ∃ k, f x < a k)
    (hHEP : ∀ k, HasHomotopyExtensionProperty
      (range (sublevelInclusion f (a k) (a (k + 1)) (ha.monotone k.le_succ))))
    (W : ∀ k, SublevelCWModel f (a k)) (ι : ∀ k, C((W k).W, (W (k + 1)).W))
    (hι : ∀ k, IsClosedEmbedding (ι k)) (hA : ∀ k, HasHomotopyExtensionProperty (range (ι k)))
    (hh : ∀ k w, ((W (k + 1)).equiv (ι k w) : M) = (W k).equiv w)
    (c : ∀ k m, cell (univ : Set (W k).W) m → cell (univ : Set (W (k + 1)).W) m)
    (hc : ∀ k m j, ⇑(map m (c k m j)) = ι k ∘ map m j) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (X ≃ₕ M) ∧ ∀ m, Nonempty (cell (univ : Set X) m ≃
        cell (univ : Set (W 0).W) m ⊕
          Σ k, {j : cell (univ : Set (W (k + 1)).W) m // j ∉ range (c k m)}) := by
  -- The colimit `X` of the sequence of models, and the inclusions `j k` of the models into it.
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun k ↦ TopCat.of (W k).W) fun k ↦ TopCat.ofHom (ι k)
  have hF (k : ℕ) : F.map (homOfLE (Nat.le_add_right k 1)) = TopCat.ofHom (ι k) :=
    Functor.ofSequence_map_homOfLE_succ _ k
  have hFemb ⦃i l : ℕ⦄ (hil : i ≤ l) : IsClosedEmbedding (F.map (homOfLE hil)) :=
    TopCat.isClosedEmbedding_map_of_isWellOrderContinuous F (fun k _ ↦ by
      -- `Order.succ k` is `k + 1` by definition, so this is `hF k`.
      have : F.map (homOfLE (Order.le_succ k)) = TopCat.ofHom (ι k) := hF k
      rw [this]
      exact hι k) hil
  let hX := colimit.isColimit F
  let X := colimit F
  let j (k : ℕ) : C((W k).W, X) := (colimit.ι F k).hom
  have hj (k : ℕ) : IsClosedEmbedding (j k) := TopCat.isClosedEmbedding_ι_of_isColimit hFemb hX k
  have hjι (k : ℕ) (w : (W k).W) : j (k + 1) (ι k w) = j k w := by
    have := ConcreteCategory.congr_hom (colimit.w F (homOfLE (Nat.le_add_right k 1))) w
    rw [hF] at this
    -- Composition in `TopCat` is composition of maps, so `this` is the claim.
    exact this
  -- The images `S k` of the models increase, cover `X`, and `X` carries their coherent topology.
  let S (k : ℕ) : Set X := range (j k)
  have hS : Monotone S := monotone_nat_of_le_succ fun k ↦ by
    rintro _ ⟨w, rfl⟩
    exact ⟨ι k w, hjι k w⟩
  have hSX : ⋃ k, S k = univ := eq_univ_of_forall fun x ↦ by
    obtain ⟨k, w, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget TopCat) hX) x
    exact mem_iUnion.2 ⟨k, w, rfl⟩
  have hSc : IsCoherentWith (range S) := ⟨fun u hu ↦ (TopCat.isOpen_iff_of_isColimit _ hX u).2
    fun k ↦ (hu _ (mem_range_self k)).preimage ((j k).continuous.subtype_mk mem_range_self)⟩
  -- Each `S k` is a CW complex, the image of `W k`, and these form a tower.
  let _ (k : ℕ) : RelCWComplex (S k) ∅ :=
    (hj k).relCWComplex (C := univ) (D := ∅) image_univ (image_empty _)
  let _ (k : ℕ) : CWComplex (S k) := RelCWComplex.toCWComplex (S k)
  let ε (k m : ℕ) : cell (S k) m ≃ cell (univ : Set (W k).W) m :=
    (hj k).relCWComplexCellEquiv image_univ (image_empty _) m
  have hmapS (k m : ℕ) (i : cell (S k) m) : ⇑(map m i) = j k ∘ map m (ε k m i) :=
    (hj k).coe_map_relCWComplex image_univ (image_empty _) m i
  let cS (k m : ℕ) (i : cell (S k) m) : cell (S (k + 1)) m := (ε (k + 1) m).symm (c k m (ε k m i))
  have hcS (k m : ℕ) (i : cell (S k) m) : ⇑(map m (cS k m i)) = ⇑(map m i) := by
    rw [hmapS, hmapS, Equiv.apply_symm_apply, hc]
    funext x
    exact hjι k _
  -- `X` is Hausdorff: the models are compact Hausdorff, hence normal, so `X` is normal and `T1`.
  have (k : ℕ) : NormalSpace (F.obj k) :=
    have : CompactSpace (W k).W := isCompact_univ_iff.1 (isCompact_of_finite isCompact_empty)
    inferInstanceAs (NormalSpace (W k).W)
  have (k : ℕ) : T1Space (F.obj k) := inferInstanceAs (T1Space (W k).W)
  have : NormalSpace X := TopCat.normalSpace_of_isColimit (fun k ↦ hFemb k.le_succ) hX
  have : T1Space X := TopCat.t1Space_of_isColimit (fun _ _ hil ↦ (hFemb hil).injective) hX
  -- The homotopy equivalences of the models glue to a map `g : X → M`.
  let cM : Cocone F :=
    { pt := TopCat.of M
      ι := NatTrans.ofSequence
        (fun k ↦ TopCat.ofHom ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp
          (W k).equiv.toFun)) fun k ↦ by
        rw [hF]
        ext w
        exact hh k w }
  let g : C(X, M) := (hX.desc cM).hom
  have hg (k : ℕ) (w : (W k).W) : g (j k w) = (W k).equiv w :=
    ConcreteCategory.congr_hom (hX.fac cM k) w
  -- On the stages, `g` restricts to the homotopy equivalences `S k ≃ₜ W k ≃ₕ M_{a k}`.
  let e (k : ℕ) : S k ≃ₕ {x | f x ≤ a k} :=
    (hj k).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans (W k).equiv
  have he (k : ℕ) (x : S k) : (e k x : M) = g x := by
    obtain ⟨_, w, rfl⟩ := x
    rw [hg]
    exact congrArg (fun v ↦ ((W k).equiv v : M)) ((hj k).isEmbedding.toHomeomorph_symm_apply w)
  -- Both towers consist of closed cofibrations, so `g` is a homotopy equivalence.
  have hSH (k : ℕ) : HasHomotopyExtensionProperty ((↑) ⁻¹' S k : Set (S (k + 1))) := by
    convert (hA k).image (hj (k + 1)).isEmbedding.toHomeomorph using 1
    ext ⟨_, w, rfl⟩
    simp only [mem_preimage, mem_image, mem_range, exists_exists_eq_and, Subtype.ext_iff,
      IsEmbedding.toHomeomorph_apply_coe, (hj (k + 1)).injective.eq_iff, S]
    exact ⟨fun ⟨v, hv⟩ ↦ ⟨v, (hj (k + 1)).injective ((hjι k v).trans hv)⟩,
      fun ⟨v, hv⟩ ↦ ⟨v, (hjι k v).symm.trans (congrArg _ hv)⟩⟩
  have hBH (k : ℕ) :
      HasHomotopyExtensionProperty ((↑) ⁻¹' {x | f x ≤ a k} : Set {x | f x ≤ a (k + 1)}) := by
    have hr : range (sublevelInclusion f (a k) (a (k + 1)) (ha.monotone k.le_succ)) =
        (↑) ⁻¹' {x | f x ≤ a k} := by
      rw [sublevelInclusion_eq_inclusion]
      exact range_inclusion (ofPred_subset_ofPred.2 fun _ hx ↦ hx.trans (ha.monotone k.le_succ))
    exact hr ▸ hHEP k
  obtain ⟨h, -, -⟩ := exists_homotopyEquiv_of_isCoherentWith (B := fun k ↦ {x | f x ≤ a k}) hS
    (fun _ _ hkl _ hx ↦ hx.trans (ha.monotone hkl)) hSX
    (eq_univ_of_forall fun x ↦ mem_iUnion.2 ((hcov x).imp fun _ hk ↦ hk.le)) hSc
    (.of_nhds fun x ↦ let ⟨k, hk⟩ := hcov x; ⟨_, mem_range_self k,
      Filter.mem_of_superset ((isOpen_lt hfc continuous_const).mem_nhds hk) fun _ hy ↦ le_of_lt hy⟩)
    hSH hBH g e he
  -- The cells of the union of the `S k` are the new cells of the stages.
  refine ⟨X, inferInstance, inferInstance, ?_⟩
  rw [← hSX]
  refine ⟨cwSubcomplexTowerUnion hcS fun A _ hA ↦
    hSc.isClosed_of_forall_isClosed_inter (forall_mem_range.2 hA), ⟨h⟩, fun m ↦ ⟨?_⟩⟩
  refine (cwSubcomplexTowerUnionCellEquiv _ _ m).trans ((Equiv.sigmaNatSucc _).trans
    (Equiv.sumCongr ((Equiv.subtypeUnivEquiv (isNewTowerCell_zero cS)).trans (ε 0 m))
      (Equiv.sigmaCongrRight fun k ↦ (Equiv.subtypeEquivRight
        fun i ↦ isNewTowerCell_succ_iff cS i).trans ((ε (k + 1) m).subtypeEquiv fun i ↦ ?_))))
  refine not_congr ⟨fun ⟨v, hv⟩ ↦ ⟨ε k m v, ?_⟩, fun ⟨v, hv⟩ ↦ ⟨(ε k m).symm v, ?_⟩⟩
  · simp [cS, ← hv]
  · simp [cS, hv]

/-- The sequence of CW models obtained from a model `s` of `M_{a 0}` by applying extension steps
`t k : SublevelCWModel f (a k) → SublevelCWModel f (a (k + 1))`. -/
private def SublevelCWModel.iterate {a : ℕ → ℝ} (s : SublevelCWModel f (a 0))
    (t : ∀ k, SublevelCWModel f (a k) → SublevelCWModel f (a (k + 1))) :
    ∀ k, SublevelCWModel f (a k)
  | 0 => s
  | k + 1 => t k (iterate s t k)

/-- If the values of `f` lie above `a 0` and below some `a k`, for `a` strictly increasing, then
every point lies in exactly one band `f⁻¹(a k, a (k + 1)]`. -/
private def sigmaIocEquiv {a : ℕ → ℝ} (ha : StrictMono a) (ha0 : ∀ x, a 0 < f x)
    (hcov : ∀ x, ∃ k, f x < a k) (P : M → Prop) :
    (Σ k, ↥{x | P x ∧ f x ∈ Ioc (a k) (a (k + 1))}) ≃ {x // P x} :=
  .ofBijective (fun p ↦ ⟨p.2, p.2.2.1⟩) <| by
    classical
    refine ⟨fun ⟨k, x, hx⟩ ⟨l, y, hy⟩ hxy ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
    · obtain rfl : x = y := congrArg Subtype.val hxy
      obtain rfl : k = l := by
        by_contra hkl
        rcases Nat.lt_or_gt_of_ne hkl with hkl | hkl
        · exact (hx.2.2.trans (ha.monotone hkl)).not_gt hy.2.1
        · exact (hy.2.2.trans (ha.monotone hkl)).not_gt hx.2.1
      rfl
    · -- The band of `x` is that below the first `a k` above `f x`.
      have hex : ∃ k, f x ≤ a k := (hcov x).imp fun _ hk ↦ hk.le
      obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 :=
        Nat.exists_eq_succ_of_ne_zero fun h ↦ (ha0 x).not_ge (h ▸ Nat.find_spec hex)
      refine ⟨⟨k, x, hx, not_le.1 (Nat.find_min hex (hk ▸ k.lt_succ_self)), hk ▸ Nat.find_spec hex⟩,
        rfl⟩

/-- **The CW model of a proper Morse function** (Milnor, Theorem 3.5). A boundaryless manifold
`M` carrying a proper Morse function `f` which is bounded below is homotopy equivalent to a
Hausdorff CW complex whose `m`-cells are in bijection with the critical points of `f` of index
`m`. There may be infinitely many critical points, and then infinitely many cells. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (X ≃ₕ M) ∧ ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨a, K, ha, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x :=
    not_le.1 fun hx ↦ (eq_empty_iff_forall_notMem.1 hK0 x) (by rw [hK]; exact hx)
  have hcov (x : M) : ∃ k, f x < a k := (htop.eventually_gt_atTop (f x)).exists
  have hcompact (k : ℕ) : IsCompact (f ⁻¹' Icc (a k) (a (k + 1))) :=
    hp.isCompact_preimage isCompact_Icc
  -- The tower of finite CW models of the sublevels `M_{a k}`, starting from the empty sublevel.
  choose t ι hι hA hh e he using fun k (s : SublevelCWModel f (a k)) ↦
    hf.exists_sublevelCWModel_extension (ha.monotone k.le_succ) (hcompact k) (hreg k)
      (hreg (k + 1)) s
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (ha0 x).not_ge x.2⟩
  let W := SublevelCWModel.iterate ⟨PEmpty.{u + 1}, Homeomorph.empty.toHomotopyEquiv⟩ t
  obtain ⟨X, _, _, _, h, hcell⟩ := exists_cwComplex_homotopyEquiv_of_tower hf.contMDiff.continuous
    ha hcov (fun k ↦ hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
      hf.contMDiff (ha k.lt_succ_self) (hcompact k) (hreg k) _)
    W (fun k ↦ ι k (W k)) (fun k ↦ hι k (W k)) (fun k ↦ hA k (W k)) (fun k ↦ hh k (W k))
    (fun k m j ↦ (e k (W k) m).symm (.inl j)) fun k m j ↦ funext (he k (W k) m j)
  refine ⟨X, _, ‹_›, ‹_›, h, fun m ↦ ⟨(hcell m).some.trans ?_⟩⟩
  -- The model of the empty sublevel has no cells, and the new cells at each later stage are the
  -- critical points in the corresponding band.
  have : IsEmpty (W 0).W := inferInstanceAs (IsEmpty PEmpty)
  have : IsEmpty (cell (univ : Set (W 0).W) m) := ⟨fun j ↦ isEmptyElim (map m j 0)⟩
  refine (Equiv.emptySum _ _).trans ((Equiv.sigmaCongrRight fun k ↦ ?_).trans
    (sigmaIocEquiv ha ha0 hcov (· ∈ {x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})))
  refine ((e k (W k) m).subtypeEquiv (q := (· ∈ range Sum.inr)) fun j ↦ ?_).trans
    ((Equiv.ofInjective _ Sum.inr_injective).symm.trans (Equiv.subtypeEquivRight fun x ↦ ?_))
  · rw [← compl_range_inl, mem_compl_iff]
    exact not_congr (exists_congr fun _ ↦ Equiv.symm_apply_eq _)
  · simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    tauto

end TauCeti
