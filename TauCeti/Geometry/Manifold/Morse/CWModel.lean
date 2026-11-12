/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SuccPred.IntervalSucc
public import TauCeti.Geometry.Manifold.Morse.Cell.Adjunction
public import TauCeti.Topology.CWComplex.Classical.AdjunctionModel
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
import TauCeti.Geometry.Manifold.Morse.Deformation.Cofibration
import TauCeti.Geometry.Manifold.Morse.Exhaustion
import TauCeti.Geometry.Manifold.Morse.Generic.Basic
import TauCeti.Topology.CWComplex.Classical.SequentialColimit
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

For a proper Morse function bounded below, on a manifold which need not be compact, the sublevels
at a sequence of regular values tending to infinity exhaust `M`, starting from the empty sublevel
below the minimum. Iterating the extension along them gives a sequence of CW models, each a
subcomplex of the next along a closed cofibration. Their colimit is a Hausdorff CW complex with one
`λ`-cell for each critical point of index `λ` (`TauCeti.exists_cwComplex_univ_of_isColimit`), and
it is homotopy equivalent to `M`, since the sublevels form a tower of closed cofibrations too
(`TauCeti.exists_homotopyEquiv_of_isColimit_of_isCoherentWith`). This is the CW model of `M`
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`); there may be infinitely many cells.

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

/-- A CW model of the sublevel `X_s = {g ≤ s}` of a function `g : X → ℝ`: a Hausdorff CW complex
with a homotopy equivalence to `X_s`. -/
private structure SublevelCWModel {X : Type u} [TopologicalSpace X] (g : X → ℝ) (s : ℝ) where
  /-- The CW complex. -/
  W : Type u
  [topologicalSpace : TopologicalSpace W]
  [t2Space : T2Space W]
  [cwComplex : CWComplex (univ : Set W)]
  /-- The homotopy equivalence with the sublevel. -/
  equiv : W ≃ₕ {x | g x ≤ s}

attribute [instance] SublevelCWModel.topologicalSpace SublevelCWModel.t2Space
  SublevelCWModel.cwComplex

/-- If the values of `f` exceed `a 0` and the levels `a` increase to infinity, then the critical
points of index `m` are the disjoint union over `k` of those with values in `(a k, a (k + 1)]`. -/
private def criticalPointsSigmaEquiv {a : ℕ → ℝ} (ha : StrictMono a)
    (htop : Filter.Tendsto a Filter.atTop Filter.atTop) (ha0 : ∀ x, a 0 < f x) (m : ℕ) :
    (Σ k, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) |
        manifoldMorseIndex I f x = m}) ≃
      ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
  (unionEqSigmaOfDisjoint (t := fun k ↦ {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) |
      manifoldMorseIndex I f x = m}) fun k l hkl ↦
      ((Monotone.pairwise_disjoint_on_Ioc_succ ha.monotone hkl).preimage f).mono
        (fun _ hx ↦ hx.1.2) fun _ hx ↦ hx.1.2).symm.trans <|
    Set.equivOfEq <| by
      have hU : ⋃ k, Ioc (a k) (a (k + 1)) = Ioi (a 0) :=
        iUnion_Ioc_map_succ_eq_Ioi (fun k ↦ ha.monotone (Nat.zero_le k))
          (Filter.not_bddAbove_of_tendsto_atTop htop)
      ext x
      have hx : ∃ k, f x ∈ Ioc (a k) (a (k + 1)) := mem_iUnion.1 (hU ▸ ha0 x)
      simp only [mem_iUnion, mem_ofPred_eq, mem_inter_iff, mem_preimage]
      exact ⟨fun ⟨_, ⟨hc, _⟩, hm⟩ ↦ ⟨hc, hm⟩, fun ⟨hc, hm⟩ ↦
        let ⟨k, hk⟩ := hx; ⟨k, ⟨hc, hk⟩, hm⟩⟩

/-- **A tower of CW models of sublevels.** Let `f` be a Morse function and `a` a strictly
increasing sequence of regular values with compact bands `f⁻¹[a k, a (k + 1)]`, below all values
of `f`. Then there are CW models `s k` of the sublevels `M_{a k}`, the first one empty, with closed
embeddings `ι k` of each into the next whose images have the homotopy extension property,
compatible with the homotopy equivalences to the sublevels. Each `ι k` carries the cells of
`s k` to cells of `s (k + 1)` with their characteristic maps, and the other `m`-cells of
`s (k + 1)` are the critical points of index `m` with values in `(a k, a (k + 1)]`. -/
private theorem IsMorse.exists_sublevelCWModel_tower (hf : IsMorse I f) {a : ℕ → ℝ}
    (ha : StrictMono a) (hcompact : ∀ k, IsCompact (f ⁻¹' Icc (a k) (a (k + 1))))
    (hreg : ∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) (ha0 : ∀ x, a 0 < f x) :
    ∃ (s : ∀ k, SublevelCWModel f (a k)) (ι : ∀ k, C((s k).W, (s (k + 1)).W)),
      IsEmpty (s 0).W ∧ (∀ k, IsClosedEmbedding (ι k)) ∧
      (∀ k, HasHomotopyExtensionProperty (range (ι k))) ∧
      (∀ k w, ((s (k + 1)).equiv (ι k w) : M) = (s k).equiv w) ∧
      ∃ e : ∀ k m, cell (univ : Set (s (k + 1)).W) m ≃ cell (univ : Set (s k).W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) |
            manifoldMorseIndex I f x = m},
        ∀ k m j x, map m ((e k m).symm (.inl j)) x = ι k (map m j x) := by
  -- Each CW model extends across the next band.
  have step (k : ℕ) (s : SublevelCWModel f (a k)) :
      ∃ (s' : SublevelCWModel f (a (k + 1))) (ι : C(s.W, s'.W)),
        IsClosedEmbedding ι ∧ HasHomotopyExtensionProperty (range ι) ∧
        (∀ w, (s'.equiv (ι w) : M) = s.equiv w) ∧
        ∃ e : ∀ m, cell (univ : Set s'.W) m ≃ cell (univ : Set s.W) m ⊕
            ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) |
              manifoldMorseIndex I f x = m},
          ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
    obtain ⟨W', _, _, _, ι, h', hι, hA, hh, e, he⟩ :=
      hf.exists_cwComplex_extension_homotopyEquiv_sublevel (ha.monotone k.le_succ) (hcompact k)
        (hreg k) (hreg (k + 1)) s.W s.equiv
    exact ⟨⟨W', h'⟩, ι, hι, hA, hh, e, he⟩
  choose next ι hι hA hh e he using step
  -- Below `a 0` the sublevel is empty, with the empty CW complex as its model.
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.2⟩
  let s₀ : SublevelCWModel f (a 0) := ⟨PEmpty.{u + 1}, Homeomorph.empty.toHomotopyEquiv⟩
  exact ⟨fun k ↦ Nat.rec (motive := fun k ↦ SublevelCWModel f (a k)) s₀ next k,
    fun k ↦ ι k _, inferInstanceAs (IsEmpty PEmpty), fun k ↦ hι k _, fun k ↦ hA k _,
    fun k ↦ hh k _, fun k ↦ e k _, fun k ↦ he k _⟩

/-- **The CW model of a manifold with a proper Morse function.** Let `f` be a Morse function on a
boundaryless manifold `M` which is proper and bounded below. Then `M` is homotopy equivalent to a
Hausdorff CW complex whose `m`-cells are in bijection with the critical points of `f` of index
`m`, for every `m` (Milnor, *Morse Theory*, Theorem 3.5). Infinitely many critical points of one
index give infinitely many cells of that dimension.

The CW complex is the colimit of CW models of the sublevels at an increasing sequence of regular
values tending to infinity, each obtained from the previous one by attaching one cell for each
critical point crossed and containing it as a subcomplex along a closed cofibration
(`TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel`). The sublevels exhaust `M`
along closed cofibrations as well, so the homotopy equivalences of the stages glue to a homotopy
equivalence of the colimit with `M`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      Nonempty (W ≃ₕ M) ∧ ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨a, K, ha, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x :=
    not_le.1 fun h ↦ (hK0 ▸ hK 0 ▸ h : x ∈ (∅ : Set M))
  have hcompact (k : ℕ) : IsCompact (f ⁻¹' Icc (a k) (a (k + 1))) :=
    (K.isCompact (k + 1)).of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (by rw [hK]; exact preimage_mono Icc_subset_Iic_self)
  obtain ⟨s, ι, hs0, hι, hA, hh, e, he⟩ := hf.exists_sublevelCWModel_tower ha hcompact hreg ha0
  -- The sequence of models and its colimit, a Hausdorff CW complex.
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun k ↦ TopCat.of (s k).W) fun k ↦ TopCat.ofHom (ι k)
  have hF (k : ℕ) : F.map (homOfLE k.le_succ) = TopCat.ofHom (ι k) :=
    Functor.ofSequence_map_homOfLE_succ _ k
  let _ (k : ℕ) : T2Space (F.obj k) := (s k).t2Space
  let _ (k : ℕ) : CWComplex (univ : Set (F.obj k)) := (s k).cwComplex
  have hFι (k : ℕ) : IsClosedEmbedding (F.map (homOfLE k.le_succ)) := by
    rw [hF]
    exact hι k
  have hFA (k : ℕ) : HasHomotopyExtensionProperty (range (F.map (homOfLE k.le_succ))) := by
    rw [hF]
    exact hA k
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  have : T2Space c.pt := TopCat.t2Space_of_isColimit_of_extendsDisjointOpens_map
    (fun k ↦ TopCat.extendsDisjointOpens_of_hasHomotopyExtensionProperty _ (hFι k).isInducing
      (hFA k)) hc
  let ιc (k m : ℕ) : cell (univ : Set (F.obj k)) m → cell (univ : Set (F.obj (k + 1))) m :=
    fun j ↦ (e k m).symm (.inl j)
  obtain ⟨_, hcell⟩ := exists_cwComplex_univ_of_isColimit (ι := ιc)
    (fun k m j x ↦ by rw [hF]; exact he k m j x) hFι hc
  -- The stages are homotopy equivalent to the sublevels, which exhaust `M` along cofibrations.
  obtain ⟨h, -⟩ := exists_homotopyEquiv_of_isColimit_of_isCoherentWith hFι hFA hc
    (B := fun k ↦ {x | f x ≤ a k}) (fun _ _ hkl _ hx ↦ hx.trans (ha.monotone hkl))
    (eq_univ_of_forall fun x ↦ mem_iUnion.2 (htop.eventually_ge_atTop (f x)).exists)
    (IsCoherentWith.of_nhds fun x ↦
      let ⟨k, hk⟩ := (htop.eventually_gt_atTop (f x)).exists
      ⟨_, mem_range_self k, Filter.mem_of_superset
        ((isOpen_lt hf.contMDiff.continuous continuous_const).mem_nhds hk) fun _ hy ↦ hy.le⟩)
    (fun k ↦ by
      have := hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue hf.contMDiff
        (ha k.lt_succ_self) (hcompact k) (hreg k) (ha.monotone k.le_succ)
      -- The range of the inclusion of sublevels is the preimage of the smaller sublevel.
      convert this using 1
      ext x
      exact ⟨fun hx ↦ ⟨⟨x, hx⟩, Subtype.ext (coe_sublevelInclusion_apply _ _ _)⟩,
        by rintro ⟨y, rfl⟩; rw [mem_preimage, coe_sublevelInclusion_apply]; exact y.2⟩)
    (fun k ↦ (s k).equiv) fun k x ↦ by rw [hF]; exact hh k x
  refine ⟨c.pt, _, ‹_›, ‹_›, ⟨h⟩, fun m ↦ ?_⟩
  -- The first stage is empty, and the cells of the stage `k + 1` not coming from the stage `k`
  -- are the critical points with values in `(a k, a (k + 1)]`.
  have : IsEmpty (cell (univ : Set (F.obj 0)) m) := ⟨fun j ↦ hs0.elim (map m j 0)⟩
  have hnew (k : ℕ) : (range (ιc k m))ᶜ = range fun t ↦ (e k m).symm (.inr t) := by
    ext j
    constructor
    · intro hj
      cases hej : e k m j with
      | inl i => exact absurd ⟨i, (e k m).symm_apply_eq.2 hej.symm⟩ hj
      | inr t => exact ⟨t, (e k m).symm_apply_eq.2 hej.symm⟩
    · rintro ⟨t, rfl⟩ ⟨i, hi⟩
      exact Sum.inl_ne_inr ((e k m).symm.injective hi)
  exact ⟨(hcell m).some.trans <| (Equiv.emptySum _ _).trans <|
    (Equiv.sigmaCongrRight fun k ↦ (Set.equivOfEq (hnew k)).trans
      (Equiv.ofInjective _ ((e k m).symm.injective.comp Sum.inr_injective)).symm).trans
    (criticalPointsSigmaEquiv ha htop ha0 m)⟩

end TauCeti
