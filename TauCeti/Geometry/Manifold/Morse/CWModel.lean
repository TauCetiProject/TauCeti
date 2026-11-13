/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Adjunction
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
a tower of models along an exhaustion of `M` by sublevels requires. For a compact sublevel `M_a`
at a regular value, starting below the minimum of `f` on `M_a`, where the sublevel is empty, gives
a finite CW model of `M_a` with one `λ`-cell for each critical point of index `λ` in it
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact`). This applies on a
compact manifold and for a proper function bounded below. For compact `M`, ending above the
maximum of `f`, where the sublevel is `M`, gives the CW model of `M`.

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
* `TauCeti.IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel`: the same, where a
  finite CW model of `M_a` extends to a finite CW model of `M_b`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel`: if `M_a` has a finite CW model,
  then so does `M_b`, with one more `λ`-cell in the count for each critical point of index `λ`
  with value in `(a, b]`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact`: a compact regular
  sublevel has a finite CW model with one cell for each critical point in it.
* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`: **the CW model of a compact
  manifold.** A compact boundaryless manifold with a Morse function `f` is homotopy equivalent to
  a finite CW complex whose `λ`-cells are in bijection with the critical points of `f` of index
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If only finitely many critical points lie in `S`, then only finitely many pairs of an index `m`
and a critical point of index `m` in `S` exist. -/
theorem finite_sigma_criticalPoints_inter {S : Set M} (hS : (criticalPoints I f ∩ S).Finite) :
    Finite (Σ m, ↥{x ∈ criticalPoints I f ∩ S | manifoldMorseIndex I f x = m}) :=
  have := hS.to_subtype
  .of_injective (fun x ↦ (⟨x.2, x.2.2.1⟩ : ↥(criticalPoints I f ∩ S)))
    fun ⟨_, _, hx⟩ ⟨_, _, hy⟩ hxy ↦ by
      cases Subtype.ext_iff.1 hxy
      cases hx.2.symm.trans hy.2
      rfl

/-- **Extending finite CW models of sublevels.** Let `f` be a Morse function and `a ≤ b` regular
values of `f` with compact band `f⁻¹[a, b]`, and let `h : W ≃ₕ M_a` be a homotopy equivalence from a
finite CW complex `W` to the sublevel `M_a = {f ≤ a}`. Then the extension `h' : W' ≃ₕ M_b` of
`TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel` can be taken with `W'` a finite
CW complex: the compact band holds only finitely many critical points, so `W'` has finitely many
new cells. -/
theorem IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u)
    [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)] [RelCWComplex.Finite (univ : Set W)]
    (h : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (ι : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}),
      RelCWComplex.Finite (univ : Set W') ∧ IsClosedEmbedding ι ∧
      HasHomotopyExtensionProperty (range ι) ∧ (∀ w, (h' (ι w) : M) = h w) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', hι, hA, hh, e, he⟩ :=
    hf.exists_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W h
  -- Only finitely many critical points lie in the compact band.
  have hS : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set W))
  have := finite_sigma_criticalPoints_inter hS
  exact ⟨W', _, ‹_›, ‹_›, ι, h', RelCWComplex.finite_of_finite_cells
    (.of_equiv _ ((Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight e).symm)),
    hι, hA, hh, e, he⟩

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
(`TauCeti.IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel`). -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (W : Type u) [TopologicalSpace W] [T2Space W]
    [CWComplex (univ : Set W)] [RelCWComplex.Finite (univ : Set W)] (e : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W')),
      RelCWComplex.Finite (univ : Set W') ∧ Nonempty (W' ≃ₕ {x | f x ≤ b}) ∧
      ∀ m, ENat.card (cell (univ : Set W') m) = ENat.card (cell (univ : Set W) m) +
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}.encard := by
  obtain ⟨W', _, _, _, -, h', hfin, -, -, -, c, -⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W e
  refine ⟨W', _, ‹_›, ‹_›, hfin, ⟨h'⟩, fun m ↦ ?_⟩
  rw [ENat.card_congr (c m), ENat.card_sum, ENat.card_coe_set_eq]

/-- **CW models of compact sublevels.** Let `f` be a Morse function and `a` a regular value with
compact sublevel `M_a = {f ≤ a}`. Then `M_a` is homotopy equivalent to a finite CW complex whose
`m`-cells correspond to the critical points of index `m` in `M_a`. The hypotheses hold for every
regular value on a compact manifold, and for every regular value of a proper function bounded
below. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact (hf : IsMorse I f) {a : ℝ}
    (hcompact : IsCompact {x | f x ≤ a}) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ a}) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m}) := by
  -- Below the minimum of `f` on the compact set `M_a` the sublevel is empty.
  obtain ⟨l, hl⟩ := hcompact.bddBelow_image hf.contMDiff.continuous.continuousOn
  have ha₀ (x : M) : min l a - 1 < f x := by
    rcases le_or_gt (f x) a with hx | hx
    · linarith [min_le_left l a, hl (mem_image_of_mem f (show x ∈ {x | f x ≤ a} from hx))]
    · linarith [min_le_right l a]
  have hband : IsCompact (f ⁻¹' Icc (min l a - 1) a) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous) fun _ hx ↦ hx.2
  have : IsEmpty {x | f x ≤ min l a - 1} := ⟨fun x ↦ (not_le.2 (ha₀ x)) x.2⟩
  obtain ⟨W, _, _, _, -, h, -, -, -, e, -⟩ := hf.exists_cwComplex_extension_homotopyEquiv_sublevel
    (by linarith [min_le_right l a]) hband
    (isRegularValue_of_notMem_range fun ⟨x, hx⟩ ↦ (ha₀ x).ne' hx) ha PEmpty.{u + 1}
    Homeomorph.empty.toHomotopyEquiv
  -- The empty CW complex has no cells, and every critical point in `M_a` lies above `min l a - 1`.
  have (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ (map m j 0).elim⟩
  have hS (m : ℕ) : {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (min l a - 1) a |
      manifoldMorseIndex I f x = m} =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m} := by
    ext x
    simp [ha₀ x]
  have := finite_sigma_criticalPoints_inter (hf.finite_criticalPoints_inter (K := f ⁻¹' Iic a)
    hcompact)
  let c (m : ℕ) : cell (univ : Set W) m ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m} :=
    (e m).trans ((Equiv.emptySum _ _).trans (Set.equivOfEq (hS m)))
  exact ⟨W, _, ‹_›, ‹_›,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm), ⟨h⟩,
    fun m ↦ ⟨c m⟩⟩

/-- **The CW model of a compact manifold.** A compact boundaryless manifold `M` carrying a Morse
function `f` is homotopy equivalent to a finite CW complex whose `m`-cells are in bijection with
the critical points of `f` of index `m`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv [CompactSpace M] (hf : IsMorse I f) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ M) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  -- Above the maximum of `f` the sublevel is all of `M`.
  obtain ⟨_, b, -, -, -, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  have hM : {x | f x ≤ b} = univ := eq_univ_of_forall fun x ↦ (hf' x).2
  obtain ⟨W, _, _, _, hfin, ⟨e⟩, c⟩ := hf.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact
    (hM ▸ isCompact_univ) hb
  refine ⟨W, _, ‹_›, ‹_›, hfin,
    ⟨e.trans ((Homeomorph.setCongr hM).trans (Homeomorph.Set.univ M)).toHomotopyEquiv⟩,
    fun m ↦ ⟨(c m).some.trans (Set.equivOfEq ?_)⟩⟩
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic]
  have := (hf' x).2
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
