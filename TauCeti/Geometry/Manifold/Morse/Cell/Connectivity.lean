/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.CellDimension
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Exhaustion
public import TauCeti.Geometry.Manifold.Morse.OpenEmbedding

import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Low-degree connectivity across Morse bands and compactified pairs

Let `X` be a Hausdorff space, `F : X → ℝ` a continuous function, and `j : M → X` an open embedding
of a boundaryless manifold on which `F ∘ j` is Morse. Across a compact band `F⁻¹[a, b]` with
`F < a` outside `range j`, where `a ≤ b` are regular values of `F ∘ j` and every critical point of
`F ∘ j` in the band has Morse index at least `n`, only cells of dimension at least `n` are attached:

* in homotopy, the sublevel pair `({F ≤ b}, {F ≤ a})` has trivial relative homotopy sets in degrees
  `1 ≤ k < n` (`TauCeti.IsMorse.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding`), and
  the inclusion `{F ≤ a} ↪ {F ≤ b}` induces surjections `π_k({F ≤ a}, x₀) → π_k({F ≤ b}, x₀)` for
  `k < n` and bijections for `k + 1 < n`;
* in homology, the relative singular homology `H_k({F ≤ b}, {F ≤ a}; R)` vanishes for `k < n` in
  every abelian category with coproducts
  (`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_isOpenEmbedding`), so
  `{F ≤ a} ↪ {F ≤ b}` induces epimorphisms on `H_k` for `k < n` and isomorphisms for `k + 1 < n`.

Taking `j = id` specializes these statements to a Morse function on `M` itself.

Now suppose `A ⊆ X` lies in `{F ≤ 0}`, `F ≤ 0` outside `range j`, `F` is bounded above, every
positive band `F⁻¹[a, b]` is compact, and `A` sits inside a subset `W ⊆ X` containing some positive
sublevel `{F ≤ δ}` (`δ > 0`) such that the inclusion `A ↪ W` is a weak homotopy equivalence (or
induces homology isomorphisms in the relevant degrees, for instance when `W` deformation retracts
onto `A`). Choosing a regular value `0 < a < δ` sandwiches `{F ≤ a}` into `A ↪ {F ≤ a} ↪ W ↪ X`:
the composite `A ↪ W` is an equivalence while `{F ≤ a} ↪ X` has the low-degree connectivity above,
forcing the inclusion `A ↪ X` to inherit the same low-degree homotopy and homology connectivity
without any smoothness assumption on `X` along `A`.

## Main results

* `TauCeti.IsMorse.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding`,
  `TauCeti.IsMorse.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding`,
  `TauCeti.IsMorse.bijective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding`: homotopy
  connectivity across a compact band on a space with an open manifold part (and their manifold
  specializations without `_of_isOpenEmbedding`).
* `TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_isOpenEmbedding`,
  `TauCeti.IsMorse.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding`,
  `TauCeti.IsMorse.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding`: low-degree homology
  vanishing and inclusion-induced epimorphisms/isomorphisms across a compact band (and their
  manifold specializations without `_of_isOpenEmbedding`).
* `TauCeti.IsMorse.subsingleton_relHomotopyGroup_ofSubset_of_isOpenEmbedding`,
  `TauCeti.IsMorse.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding`,
  `TauCeti.IsMorse.bijective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding`,
  `TauCeti.IsMorse.isZero_singularHomology_ofSubset_of_isOpenEmbedding`: homotopy and homology
  connectivity of `(X, A)` when `A` has a weak-equivalence / degreewise homology-isomorphic
  neighbourhood containing a positive sublevel of `F`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1 and 3.2, and Section 7 (Theorem 7.4).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12.
-/

public section

noncomputable section

open CategoryTheory Limits Function Set Topology Topology.RelCWComplex
open scoped ContDiff ContinuousMap Manifold Topology.Homotopy

universe u v w

namespace TauCeti

section BandInduction

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X]
  {j : M → X} {F : X → ℝ} {n : ℕ}

/-- Around a level `c` in `(a, b)` where all critical points of `F ∘ j` in `F⁻¹[a, b]` have Morse
index at least `n`, find `0 < ε ≤ δ` isolating `c` and a finite relative CW complex
`(C', {F ≤ c - ε})` inside `{F ≤ c + ε}` with no cells of dimension `< n` onto which `{F ≤ c + ε}`
strongly deformation retracts. -/
private theorem IsMorse.exists_relCWComplex_sublevel_isEmpty_cell (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b c δ : ℝ} (hδ : 0 < δ) (hδa : a < c - δ)
    (hδb : c + δ < b) (hcpt : IsCompact (F ⁻¹' Icc (c - δ) (c + δ)))
    (hAc : ∀ x ∉ range j, F x < c - δ)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p) :
    ∃ ε, ∃ _ : 0 < ε, ε ≤ δ ∧
      criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc (c - ε) (c + ε) ⊆ (F ∘ j) ⁻¹' {c} ∧
      ∃ (C' : Set X) (_ : RelCWComplex C' {x | F x ≤ c - ε})
        (_ : RelCWComplex.Finite C') (hC' : C' ⊆ {x | F x ≤ c + ε}),
        (∀ m < n, IsEmpty (cell C' m)) ∧
        ∃ r : C({x | F x ≤ c + ε}, C'),
          LeftInverse r (ContinuousMap.inclusion hC') ∧
          Nonempty (((ContinuousMap.inclusion hC').comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : X) ∈ C'}) := by
  obtain ⟨δ', hδ', hδ'δ, hsub⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ
    (hj.isInducing.isCompact_comp_preimage_Icc hAc hcpt)
  have hcpt' : IsCompact (F ⁻¹' Icc (c - δ') (c + δ')) :=
    hcpt.of_isClosed_subset (isClosed_Icc.preimage hF)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith)))
  obtain ⟨ε, hε, hεδ', C', instCW, instFin, hC', hcell, r, hri, hG⟩ :=
    hf.exists_relCWComplex_sublevel_of_isOpenEmbedding hj hF hδ' hcpt'
      fun x hx ↦ (hAc x hx).trans_le (by linarith)
  refine ⟨ε, hε, hεδ'.trans hδ'δ,
    fun p hp ↦ hsub ⟨hp.1, Icc_subset_Icc (by linarith) (by linarith) hp.2⟩,
    C', instCW, instFin, hC', fun m hm ↦ (hcell m).some.isEmpty_congr.2
      ⟨fun ⟨⟨p, hp, hpc⟩, hpm⟩ ↦ ?_⟩, r, hri, hG⟩
  have hpc' : F (j p) = c := hpc
  have := hindex p ⟨hp, by
    simp only [mem_preimage, mem_Icc, Function.comp_apply]
    constructor <;> linarith⟩
  dsimp only at hpm
  omega

/-- Induction across the finitely many critical levels in a compact band `F⁻¹[a, b]` between regular
values of `F ∘ j` whose critical points all have Morse index at least `n`, supplying the strong
deformation retraction on regular bands and the finite high-index relative CW complex across each
critical level. -/
private theorem IsMorse.sublevelBand_induction (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b))
    (hA : ∀ x ∉ range j, F x < a) (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a)
    (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    {P : ∀ s t : ℝ, s ≤ t → Prop}
    (hreg : ∀ {s t : ℝ} (hst : s ≤ t) (r : C({x | F x ≤ t}, {x | F x ≤ s})),
      LeftInverse r (ContinuousMap.inclusion (sublevel_mono F hst)) →
      (((ContinuousMap.inclusion (sublevel_mono F hst)).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : X) ∈ {x | F x ≤ s}}) →
      P s t hst)
    (hcell : ∀ {c ε : ℝ} (hε : 0 < ε) (C' : Set X) [RelCWComplex C' {x | F x ≤ c - ε}]
      [RelCWComplex.Finite C'] (hC' : C' ⊆ {x | F x ≤ c + ε}),
      (∀ m < n, IsEmpty (cell C' m)) →
      ∀ (r : C({x | F x ≤ c + ε}, C')), LeftInverse r (ContinuousMap.inclusion hC') →
      (((ContinuousMap.inclusion hC').comp r).HomotopyRel
        (ContinuousMap.id _) {y | (y : X) ∈ C'}) →
      P (c - ε) (c + ε) (by linarith))
    (htrans : ∀ {s m t : ℝ} (hsm : s ≤ m) (hmt : m ≤ t),
      P s m hsm → P m t hmt → P s t (hsm.trans hmt)) :
    P a b hab := by
  rw [isRegularValue_iff_notMem_image_criticalPoints] at ha hb
  have hcompact_sub {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) : IsCompact (F ⁻¹' Icc s t) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hF) (preimage_mono (Icc_subset_Icc hs ht))
  have hreg_band {s t : ℝ} (hst : s ≤ t) (hs : a ≤ s) (ht : t ≤ b)
      (hAs : ∀ x ∉ range j, F x < s)
      (hcrit : ∀ p ∈ criticalPoints I (F ∘ j), F (j p) ∉ Icc s t) : P s t hst := by
    obtain ⟨r, hri, ⟨G⟩⟩ := exists_sublevelDeformation_of_isOpenEmbedding hj hF hf.contMDiff hst
      (hcompact_sub hs ht)
      (fun p hsp hpt hp ↦ hcrit p (mem_criticalPoints_iff_mfderiv_eq_zero.2 hp) ⟨hsp, hpt⟩) hAs
    rw [sublevelInclusion_eq_inclusion] at hri G
    exact hreg hst r hri G
  suffices ∀ K : ℕ, ∀ s, ∀ has : a ≤ s, ∀ hsb : s ≤ b,
      (criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc s b).ncard = K →
      s ∉ (F ∘ j) '' criticalPoints I (F ∘ j) → P s b hsb from
    this _ a le_rfl hab rfl ha
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
  intro s has hsb hK hs
  have hAs (x : X) (hx : x ∉ range j) : F x < s := (hA x hx).trans_le has
  have hS := hf.finite_criticalPoints_inter
    (hj.isInducing.isCompact_comp_preimage_Icc hAs (hcompact_sub has le_rfl))
  rcases (criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc s b).eq_empty_or_nonempty with hS₀ | hSne
  · exact hreg_band hsb has le_rfl hAs fun p hp hpb ↦ hS₀.subset ⟨hp, hpb⟩
  -- Cut the band around the lowest critical value `c = F (j p)` in `[s, b]`.
  obtain ⟨p, ⟨hp, hpsb⟩, hpmin⟩ :=
    hS.isCompact.exists_isMinOn hSne hf.contMDiff.continuous.continuousOn
  have hsc : s < F (j p) := hpsb.1.lt_of_ne fun h ↦ hs ⟨p, hp, h.symm⟩
  have hcb : F (j p) < b := hpsb.2.lt_of_ne fun h ↦ hb ⟨p, hp, h⟩
  set δ : ℝ := min (F (j p) - s) (b - F (j p)) / 2 with hδ_def
  have hδ : 0 < δ := half_pos (lt_min (sub_pos.2 hsc) (sub_pos.2 hcb))
  have hδs : s < F (j p) - δ := by linarith [hδ_def, min_le_left (F (j p) - s) (b - F (j p))]
  have hδb : F (j p) + δ < b := by linarith [hδ_def, min_le_right (F (j p) - s) (b - F (j p))]
  obtain ⟨ε, hε, hεδ, hsub, C', _, _, hC', hempty, r, hri, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_isEmpty_cell hj hF hδ (has.trans_lt hδs) hδb
      (hcompact_sub (has.trans hδs.le) hδb.le) (fun x hx ↦ (hAs x hx).trans hδs) hindex
  have hmid : P (F (j p) - ε) (F (j p) + ε) (by linarith) :=
    hcell hε C' hC' hempty r hri G
  have hlow : P s (F (j p) - ε) (by linarith) :=
    hreg_band _ has (by linarith) hAs fun q hq hqI ↦ by
      have : F (j p) ≤ F (j q) := hpmin ⟨hq, hqI.1, hqI.2.trans (by linarith)⟩
      linarith [hqI.2]
  have hlt : (criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc (F (j p) + ε) b).ncard < K := by
    rw [← hK]
    refine ncard_lt_ncard ⟨fun q hq ↦ ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩, fun h ↦ ?_⟩ hS
    have : F (j p) + ε ≤ F (j p) := (h ⟨hp, hpsb⟩).2.1
    linarith
  have hup : P (F (j p) + ε) b (by linarith) :=
    ih _ hlt _ (by linarith) (by linarith) rfl fun ⟨q, hq, hqc⟩ ↦ by
      have hqc' : F (j q) = F (j p) + ε := hqc
      have : F (j q) = F (j p) := hsub ⟨hq, by
        simp only [mem_preimage, mem_Icc, Function.comp_apply]
        constructor <;> linarith⟩
      linarith
  exact htrans (by linarith) (by linarith)
    (htrans (by linarith) (by linarith) hlow hmid) hup

end BandInduction

section SublevelHomotopy

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X] [T2Space X]
  {j : M → X} {F : X → ℝ} {n : ℕ}

/-- Low-degree homotopy connectivity of `{F ≤ a} ↪ {F ≤ b}`, indexed by `Fin k` so that it
contains no universe parameter. -/
private structure SublevelBandConnected (F : X → ℝ) (n : ℕ) (a b : ℝ) (hab : a ≤ b) : Prop where
  exists_joined (hn : 0 < n) (y : {x | F x ≤ b}) :
    ∃ x, Joined (ContinuousMap.inclusion (sublevel_mono F hab) x) y
  surjective {k : ℕ} (hk : k < n) (x : {x | F x ≤ a}) :
    Surjective (HomotopyGroup.map (N := Fin k) (ContinuousMap.inclusion (sublevel_mono F hab))
      (rfl : ContinuousMap.inclusion (sublevel_mono F hab) x =
        ContinuousMap.inclusion (sublevel_mono F hab) x))
  injective {k : ℕ} (hk : k + 1 < n) (x : {x | F x ≤ a}) :
    Injective (HomotopyGroup.map (N := Fin k) (ContinuousMap.inclusion (sublevel_mono F hab))
      (rfl : ContinuousMap.inclusion (sublevel_mono F hab) x =
        ContinuousMap.inclusion (sublevel_mono F hab) x))

omit [T2Space X] in
private theorem SublevelBandConnected.trans {a m b : ℝ} {ham : a ≤ m} {hmb : m ≤ b}
    (h₁ : SublevelBandConnected F n a m ham) (h₂ : SublevelBandConnected F n m b hmb) :
    SublevelBandConnected F n a b (ham.trans hmb) := by
  have hcomp (k : ℕ) (x : {x | F x ≤ a}) :
      HomotopyGroup.map (N := Fin k) (ContinuousMap.inclusion (sublevel_mono F hmb)) rfl ∘
        HomotopyGroup.map (ContinuousMap.inclusion (sublevel_mono F ham))
          (rfl : _ = ContinuousMap.inclusion (sublevel_mono F ham) x) =
      HomotopyGroup.map (ContinuousMap.inclusion (sublevel_mono F (ham.trans hmb))) rfl :=
    HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.ext fun _ ↦ rfl) rfl rfl rfl
  refine ⟨fun hn y ↦ ?_, fun hk x ↦ hcomp _ x ▸ (h₂.surjective hk _).comp (h₁.surjective hk x),
    fun hk x ↦ hcomp _ x ▸ (h₂.injective hk _).comp (h₁.injective hk x)⟩
  obtain ⟨z, hz⟩ := h₂.exists_joined hn y
  obtain ⟨x, hx⟩ := h₁.exists_joined hn z
  exact ⟨x, (hx.map (ContinuousMap.inclusion (sublevel_mono F hmb)).continuous).trans hz⟩

private theorem sublevelBandConnected_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p) :
    SublevelBandConnected F n a b hab := by
  refine hf.sublevelBand_induction hj hF hab hcompact hA ha hb hindex
    (P := SublevelBandConnected F n) (fun hst r hri G ↦ ?_)
    (fun {c ε} hε C' _ _ hC' hempty r hri G ↦ ?_) (fun _ _ h₁ h₂ ↦ h₁.trans h₂)
  · have he := (ContinuousMap.HomotopyEquiv.ofDeformationRetraction
        (ContinuousMap.inclusion (sublevel_mono F hst)) r hri
        ⟨G.toHomotopy⟩).isWeakHomotopyEquivalence
    exact ⟨fun _ ↦ he.exists_joined, fun _ x ↦ (he.bijective _ x).surjective,
      fun _ x ↦ (he.bijective _ x).injective⟩
  · have hg := (ContinuousMap.HomotopyEquiv.ofDeformationRetraction
      (ContinuousMap.inclusion hC') r hri ⟨G.toHomotopy⟩).isWeakHomotopyEquivalence
    have hgf : (ContinuousMap.inclusion hC').comp (ContinuousMap.inclusion base_subset_complex) =
        (ContinuousMap.inclusion (sublevel_mono F (a := c - ε) (b := c + ε) (by linarith))).comp
          (ContinuousMap.id _) :=
      ContinuousMap.ext fun _ ↦ rfl
    exact ⟨fun hn ↦ exists_joined_of_isEmpty_cell_of_comp_eq hempty hn .id hg hgf,
      fun hk ↦ surjective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq hempty
        (by simpa using hk) .id hg hgf,
      fun hk ↦ injective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq hempty
        (by simpa using hk) .id hg hgf⟩

/-- **Path connectivity across a Morse band with indices at least `1`.** Across a compact band
`F⁻¹[a, b]` between regular values of `F ∘ j` with `F < a` outside `range j`, if `0 < n` and every
critical point in the band has index at least `n`, every point of `{F ≤ b}` is joined by a path in
`{F ≤ b}` to `{F ≤ a}`. -/
theorem IsMorse.exists_joined_sublevelInclusion_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hn : 0 < n) (y : {x | F x ≤ b}) :
    ∃ x, Joined (sublevelInclusion F a b hab x) y := by
  rw [sublevelInclusion_eq_inclusion]
  exact (sublevelBandConnected_of_isOpenEmbedding hj hF hf hab hcompact hA ha hb
    hindex).exists_joined hn y

/-- **Surjectivity on `π_k` for `k < n` across a Morse band.** Across a compact band `F⁻¹[a, b]`
between regular values of `F ∘ j` with `F < a` outside `range j`, if every critical point in the
band has index at least `n`, then `{F ≤ a} ↪ {F ≤ b}` induces surjections on `π_k` for `k < n`. -/
theorem IsMorse.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N < n) (x : {x | F x ≤ a}) :
    Surjective (HomotopyGroup.map (N := N) (sublevelInclusion F a b hab)
      (rfl : sublevelInclusion F a b hab x = sublevelInclusion F a b hab x)) := by
  rw [HomotopyGroup.surjective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl,
    ← HomotopyGroup.congrEquiv_symm_comp_map_comp_congrEquiv _ rfl (Finite.equivFin N)]
  exact (Equiv.surjective _).comp
    (((sublevelBandConnected_of_isOpenEmbedding hj hF hf hab hcompact hA ha hb
      hindex).surjective hN x).comp (Equiv.surjective _))

/-- **Injectivity on `π_k` for `k + 1 < n` across a Morse band.** Across a compact band `F⁻¹[a, b]`
between regular values of `F ∘ j` with `F < a` outside `range j`, if every critical point in the
band has index at least `n`, then `{F ≤ a} ↪ {F ≤ b}` induces injections on `π_k` for
`k + 1 < n`. -/
theorem IsMorse.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N + 1 < n) (x : {x | F x ≤ a}) :
    Injective (HomotopyGroup.map (N := N) (sublevelInclusion F a b hab)
      (rfl : sublevelInclusion F a b hab x = sublevelInclusion F a b hab x)) := by
  rw [HomotopyGroup.injective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl,
    ← HomotopyGroup.congrEquiv_symm_comp_map_comp_congrEquiv _ rfl (Finite.equivFin N)]
  exact (Equiv.injective _).comp
    (((sublevelBandConnected_of_isOpenEmbedding hj hF hf hab hcompact hA ha hb
      hindex).injective hN x).comp (Equiv.injective _))

/-- **Bijectivity on `π_k` for `k + 1 < n` across a Morse band.** -/
theorem IsMorse.bijective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N + 1 < n) (x : {x | F x ≤ a}) :
    Bijective (HomotopyGroup.map (N := N) (sublevelInclusion F a b hab)
      (rfl : sublevelInclusion F a b hab x = sublevelInclusion F a b hab x)) :=
  ⟨hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha hb
      hindex hN x,
    hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha hb
      hindex (by omega) x⟩

/-- **Relative homotopy vanishing below the Morse index bound across a compact band.** Across a
compact band `F⁻¹[a, b]` between regular values of `F ∘ j` with `F < a` outside `range j`, if every
critical point in the band has index at least `n`, then `π_{k+1}({F ≤ b}, {F ≤ a}, x₀)` is trivial
for `k + 1 < n` and every `x₀ ∈ {F ≤ a}`. -/
theorem IsMorse.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N + 1 < n) (x : {x | F x ≤ a}) :
    Subsingleton (RelHomotopyGroup N ⟨sublevelPair F hab, x⟩) :=
  RelHomotopyGroup.subsingleton_of_injective_of_surjective
    ((HomotopyGroup.injective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl).1
      (hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha
        hb hindex hN x))
    ((HomotopyGroup.surjective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl).1
      (hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha
        hb hindex (by rw [_root_.Finite.card_option]; exact hN) x))

/-- **Path connectivity across a Morse band with indices at least `1` on a manifold.** -/
theorem IsMorse.exists_joined_sublevelInclusion {f : M → ℝ} (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hn : 0 < n) (y : {x | f x ≤ b}) :
    ∃ x, Joined (sublevelInclusion f a b hab x) y :=
  hf.exists_joined_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab hcompact
    (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hn y

/-- **Relative homotopy vanishing below the Morse index bound on a manifold.** -/
theorem IsMorse.subsingleton_relHomotopyGroup_sublevelPair {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N + 1 < n) (x : {x | f x ≤ a}) :
    Subsingleton (RelHomotopyGroup N ⟨sublevelPair f hab, x⟩) :=
  hf.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding .id hf.contMDiff.continuous hab
    hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

/-- **Surjectivity on `π_k` for `k < n` across a Morse band on a manifold.** -/
theorem IsMorse.surjective_homotopyGroupMap_sublevelInclusion {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N < n) (x : {x | f x ≤ a}) :
    Surjective (HomotopyGroup.map (N := N) (sublevelInclusion f a b hab)
      (rfl : sublevelInclusion f a b hab x = sublevelInclusion f a b hab x)) :=
  hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous
    hab hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

/-- **Injectivity on `π_k` for `k + 1 < n` across a Morse band on a manifold.** -/
theorem IsMorse.injective_homotopyGroupMap_sublevelInclusion {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N + 1 < n) (x : {x | f x ≤ a}) :
    Injective (HomotopyGroup.map (N := N) (sublevelInclusion f a b hab)
      (rfl : sublevelInclusion f a b hab x = sublevelInclusion f a b hab x)) :=
  hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous
    hab hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

/-- **Bijectivity on `π_k` for `k + 1 < n` across a Morse band on a manifold.** -/
theorem IsMorse.bijective_homotopyGroupMap_sublevelInclusion {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N + 1 < n) (x : {x | f x ≤ a}) :
    Bijective (HomotopyGroup.map (N := N) (sublevelInclusion f a b hab)
      (rfl : sublevelInclusion f a b hab x = sublevelInclusion f a b hab x)) :=
  hf.bijective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab
    hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

end SublevelHomotopy

section SublevelHomology

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X] [T2Space X]
  {j : M → X} {F : X → ℝ} {n : ℕ}
  {A_cat : Type v} [Category.{w} A_cat] [Abelian A_cat] [HasCoproducts.{u} A_cat]

/-- **Relative singular homology vanishes below the Morse index bound across a compact band.** Let
`F⁻¹[a, b]` be a compact band between regular values of `F ∘ j` with `F < a` outside `range j`. If
every critical point of `F ∘ j` in the band has Morse index at least `n`, then
`H_k({F ≤ b}, {F ≤ a}; R)` vanishes for every `k < n`. -/
theorem IsMorse.isZero_singularHomology_sublevelPair_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    IsZero ((sublevelPair F hab).singularHomology R k) := by
  revert k
  refine hf.sublevelBand_induction hj hF hab hcompact hA ha hb hindex
    (P := fun s t hst ↦ ∀ {k : ℕ}, k < n → IsZero ((sublevelPair F hst).singularHomology R k))
    (fun {_ _} hst r _ G {k} _ ↦ ?_)
    (fun {_ _} _ C' _ _ hC' hempty r _ G {k} hk ↦ ?_)
    (fun {_ _ _} hsm hmt h₁ h₂ {k} hk ↦ ?_)
  · refine TopPair.isZero_singularHomology_of_homotopy (f := TopPair.ofInclusionMap
        (X := TopCat.of X) (sublevel_mono F hst) (sublevel_mono F hst)
        ((ContinuousMap.inclusion (sublevel_mono F hst)).comp r) fun x _ ↦ (r x).2)
      ?_ (TopCat.ofHom r) (by ext x; exact (TopPair.ofInclusionMap_fst_apply
        (hst := sublevel_mono F hst) (hst' := sublevel_mono F hst) _ _ x).symm) R k
    rw [← TopPair.ofInclusionMap_id]
    refine TopPair.ofInclusionHomotopy G.symm.toHomotopy fun τ x hx ↦ ?_
    have h : G.symm.toHomotopy (τ, x) = x := G.symm.eq_fst τ hx
    rw [h]
    exact hx
  · have : IsEmpty (cell C' k) := hempty k hk
    have : ∀ m, HasExactColimitsOfShape (Discrete (cell C' m)) A_cat := fun m ↦
      have : _root_.Finite (cell C' m) := FiniteType.finite_cell m
      @hasExactColimitsOfShape_discrete_finite A_cat _ _ Abelian.hasFiniteBiproducts _ _
    have hzero := isZero_singularHomology_complexBasePair_of_isEmpty_cell C' R k
    rw [complexBasePair_eq_ofInclusion] at hzero
    have hiso := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
      (X := TopCat.of X) base_subset_complex hC' r G R k
    exact hzero.of_iso (@asIso _ _ _ _ _ hiso).symm
  · let T := TopTriple.ofInclusions (X := TopCat.of X) (sublevel_mono F hsm) (sublevel_mono F hmt)
    exact (T.singularHomology_exact_total R k).isZero_X₂
      ((h₁ hk).eq_of_src _ _) ((h₂ hk).eq_of_tgt _ _)

/-- **Epimorphism on `H_k` for `k < n` across a Morse band.** -/
theorem IsMorse.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    Epi (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion F a b hab))) R k) := by
  rw [sublevelInclusion_eq_inclusion]
  exact (sublevelPair F hab).epi_homologyMap_map_of_isZero R
    (hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding hj hF hab hcompact hA ha hb hindex
      R hk)

/-- **Isomorphism on `H_k` for `k + 1 < n` across a Morse band.** -/
theorem IsMorse.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} (hk : k + 1 < n) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion F a b hab))) R k) := by
  rw [sublevelInclusion_eq_inclusion]
  exact (sublevelPair F hab).isIso_homologyMap_map_of_isZero R
    (hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding hj hF hab hcompact hA ha hb hindex
      R hk)
    (hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding hj hF hab hcompact hA ha hb hindex
      R (by omega))

/-- **Relative singular homology vanishes below the Morse index bound on a manifold.** -/
theorem IsMorse.isZero_singularHomology_sublevelPair {f : M → ℝ}
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    IsZero ((sublevelPair f hab).singularHomology R k) :=
  hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding .id hf.contMDiff.continuous hab
    hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex R hk

/-- **Epimorphism on `H_k` for `k < n` across a Morse band on a manifold.** -/
theorem IsMorse.epi_homologyMap_sublevelInclusion {f : M → ℝ}
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    Epi (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion f a b hab))) R k) :=
  hf.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab hcompact
    (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex R hk

/-- **Isomorphism on `H_k` for `k + 1 < n` across a Morse band on a manifold.** -/
theorem IsMorse.isIso_homologyMap_sublevelInclusion {f : M → ℝ}
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (R : A_cat) {k : ℕ} (hk : k + 1 < n) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion f a b hab))) R k) :=
  hf.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab hcompact
    (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex R hk

end SublevelHomology

section PairConnectivity

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X] [T2Space X]
  {j : M → X} {F : X → ℝ} {A W : Set X} {n : ℕ}

omit [T2Space X] in
/-- When `F x ≤ b` for every `x : X`, the sublevel `{x | F x ≤ b}` is homeomorphic to `X` via
`Subtype.val`. -/
private def sublevelHomeoUniv {F : X → ℝ} {b : ℝ} (hFb : ∀ x, F x ≤ b) :
    {x | F x ≤ b} ≃ₜ X :=
  (Homeomorph.setCongr (eq_univ_of_forall hFb)).trans (Homeomorph.Set.univ X)

omit [FiniteDimensional ℝ E] [T2Space M] [T2Space X] in
/-- Choose a regular value `0 < a < δ` of `F ∘ j` and an upper bound `b > F` so `{F ≤ a} ⊆ W` and
`{F ≤ b} = univ`. -/
private theorem IsMorse.exists_sandwich_levels (hj : IsOpenEmbedding j)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) :
    ∃ (a b : ℝ) (_ : a ≤ b),
      0 < a ∧ A ⊆ {x | F x ≤ a} ∧ {x | F x ≤ a} ⊆ W ∧ (∀ x ∉ range j, F x < a) ∧
      (∀ x, F x < b) ∧ IsRegularValue I 𝓘(ℝ) (F ∘ j) a ∧ IsRegularValue I 𝓘(ℝ) (F ∘ j) b ∧
      IsCompact (F ⁻¹' Icc a b) := by
  obtain ⟨δ, hδ_pos, hδW⟩ := hδ
  obtain ⟨M₀, hM₀⟩ := hbdd
  have hA_third (x : X) (hx : x ∉ range j) : F x < δ / 3 := (hA x hx).trans_lt (by linarith)
  obtain ⟨a, ⟨ha₁, ha₂⟩, ha_reg⟩ := hf.exists_isRegularValue_mem_Ioo
    (a := δ / 3) (b := 2 * δ / 3) (by linarith)
    (hj.isInducing.isCompact_comp_preimage_Icc hA_third
      (hcompact _ _ (by linarith) (by linarith)))
  have ha_pos : 0 < a := by linarith
  let b : ℝ := max a M₀ + 1
  have hab : a ≤ b := by linarith [le_max_left a M₀]
  have hFb (x : X) : F x < b :=
    (hM₀ (mem_range_self x)).trans_lt (by linarith [le_max_right a M₀])
  refine ⟨a, b, hab, ha_pos, fun x hx ↦ (hAF x hx).trans ha_pos.le,
    fun x hx ↦ hδW (hx.out.trans (by linarith)), fun x hx ↦ (hA x hx).trans_lt ha_pos, hFb,
    ha_reg, isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨p, _, hp⟩ ↦ (hFb (j p)).ne hp,
    hcompact a b ha_pos hab⟩

/-- **Path connectivity of `(X, A)` from a high-index Morse function on the open manifold part.**
If `0 < n`, every critical point of `F ∘ j` has index at least `n`, and `A ↪ W` is a weak homotopy
equivalence on a set `W` containing a positive sublevel `{F ≤ δ}`, then every point of `X` is
joined by a path in `X` to a point of `A`. -/
theorem IsMorse.exists_joined_of_isOpenEmbedding (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hn : 0 < n) (x : X) :
    ∃ a : A, Joined (a : X) x := by
  obtain ⟨a, b, hab, -, -, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  obtain ⟨y, hy⟩ := hf.exists_joined_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt
    ha_reg hb_reg (fun p hp ↦ hindex p hp.1) hn ⟨x, (hFb x).le⟩
  rw [sublevelInclusion_eq_inclusion] at hy
  obtain ⟨a₀, ha₀⟩ := hW.exists_joined (ContinuousMap.inclusion haW y)
  exact ⟨a₀, (ha₀.map continuous_subtype_val).trans (hy.map continuous_subtype_val)⟩

/-- **Surjectivity of `π_k(A, a₀) → π_k(X, a₀)` for `k < n` on a compactified pair.** -/
theorem IsMorse.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N < n) (a₀ : A) :
    Surjective (HomotopyGroup.map (N := N) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X))) := by
  obtain ⟨a, b, hab, -, hAa, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let eb := sublevelHomeoUniv fun x ↦ (hFb x).le
  let α : C(A, {x | F x ≤ a}) := ContinuousMap.inclusion hAa
  let β : C({x | F x ≤ a}, W) := ContinuousMap.inclusion haW
  let γ : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let inc : C({x | F x ≤ a}, {x | F x ≤ b}) := ContinuousMap.inclusion (sublevel_mono F hab)
  have hγβ : HomotopyGroup.map (N := N) γ rfl ∘
      HomotopyGroup.map β (rfl : β (α a₀) = β (α a₀)) =
      HomotopyGroup.map eb.toHomotopyEquiv.toFun rfl ∘ HomotopyGroup.map inc rfl := by
    rw [HomotopyGroup.map_comp_map, HomotopyGroup.map_comp_map]
    exact funext (HomotopyGroup.map_congr (ContinuousMap.ext fun _ ↦ rfl) _ _)
  have hsurj_inc : Surjective (HomotopyGroup.map (N := N) inc (rfl : inc (α a₀) = inc (α a₀))) :=
    (HomotopyGroup.surjective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl).1
      (hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt
        ha_reg hb_reg (fun p hp ↦ hindex p hp.1) hN (α a₀))
  have hsurj_γβ : Surjective (HomotopyGroup.map (N := N) γ rfl ∘
      HomotopyGroup.map β (rfl : β (α a₀) = β (α a₀))) := by
    rw [hγβ]
    exact (eb.toHomotopyEquiv.isWeakHomotopyEquivalence.map_bijective N _).surjective.comp hsurj_inc
  have hsurj_γ : Surjective (HomotopyGroup.map (N := N) γ
      (rfl : γ (ContinuousMap.inclusion hAW a₀) = γ (ContinuousMap.inclusion hAW a₀))) :=
    hsurj_γβ.of_comp
  have hcomp : HomotopyGroup.map (N := N) γ rfl ∘
      HomotopyGroup.map (ContinuousMap.inclusion hAW)
        (rfl : ContinuousMap.inclusion hAW a₀ = ContinuousMap.inclusion hAW a₀) =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X)) :=
    HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.ext fun _ ↦ rfl) rfl rfl rfl
  exact hcomp ▸ hsurj_γ.comp (hW.map_bijective N a₀).surjective

/-- **Injectivity of `π_k(A, a₀) → π_k(X, a₀)` for `k + 1 < n` on a compactified pair.** -/
theorem IsMorse.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N + 1 < n) (a₀ : A) :
    Injective (HomotopyGroup.map (N := N) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X))) := by
  obtain ⟨a, b, hab, -, hAa, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let eb := sublevelHomeoUniv fun x ↦ (hFb x).le
  let α : C(A, {x | F x ≤ a}) := ContinuousMap.inclusion hAa
  let β : C({x | F x ≤ a}, W) := ContinuousMap.inclusion haW
  let inc : C({x | F x ≤ a}, {x | F x ≤ b}) := ContinuousMap.inclusion (sublevel_mono F hab)
  have hβα : HomotopyGroup.map (N := N) β rfl ∘
      HomotopyGroup.map α (rfl : α a₀ = α a₀) =
      HomotopyGroup.map (ContinuousMap.inclusion hAW) rfl :=
    HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.ext fun _ ↦ rfl) rfl rfl rfl
  have hinj_α : Injective (HomotopyGroup.map (N := N) α (rfl : α a₀ = α a₀)) :=
    (hβα.symm ▸ (hW.map_bijective N a₀).injective).of_comp
  have hinj_inc : Injective (HomotopyGroup.map (N := N) inc (rfl : inc (α a₀) = inc (α a₀))) :=
    (HomotopyGroup.injective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl).1
      (hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt
        ha_reg hb_reg (fun p hp ↦ hindex p hp.1) hN (α a₀))
  have hinj_rest : Injective (HomotopyGroup.map (N := N) eb.toHomotopyEquiv.toFun rfl ∘
      HomotopyGroup.map inc (rfl : inc (α a₀) = inc (α a₀))) :=
    (eb.toHomotopyEquiv.isWeakHomotopyEquivalence.map_bijective N _).injective.comp hinj_inc
  have hcomp : (HomotopyGroup.map (N := N) eb.toHomotopyEquiv.toFun rfl ∘
        HomotopyGroup.map inc rfl) ∘
      HomotopyGroup.map α (rfl : α a₀ = α a₀) =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X)) := by
    rw [HomotopyGroup.map_comp_map, HomotopyGroup.map_comp_map]
    exact funext (HomotopyGroup.map_congr (ContinuousMap.ext fun _ ↦ rfl) _ _)
  exact hcomp ▸ hinj_rest.comp hinj_α

/-- **Bijectivity of `π_k(A, a₀) → π_k(X, a₀)` for `k + 1 < n` on a compactified pair.** -/
theorem IsMorse.bijective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N + 1 < n) (a₀ : A) :
    Bijective (HomotopyGroup.map (N := N) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X))) :=
  ⟨hf.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex hW
      hδ hN a₀,
    hf.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex
      hW hδ (by omega) a₀⟩

/-- **Injectivity on path components of `A ↪ X` when `1 < n`.** -/
theorem IsMorse.joined_subtypeVal_iff_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hn : 1 < n) {a₀ a₁ : A} :
    Joined (a₀ : X) (a₁ : X) ↔ Joined a₀ a₁ :=
  ContinuousMap.joined_iff_of_injective_homotopyGroupMap ⟨Subtype.val, continuous_subtype_val⟩
    (hf.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding (N := Fin 0) hj hF hbdd hA hAF
      hcompact hindex hW hδ (by simpa using hn) a₀)

/-- **Relative homotopy vanishing `π_{k+1}(X, A, a₀) = 0` for `k + 1 < n` on a compactified
pair.** -/
theorem IsMorse.subsingleton_relHomotopyGroup_ofSubset_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N + 1 < n) (a₀ : A) :
    Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset (X := TopCat.of X) A, a₀⟩) :=
  RelHomotopyGroup.subsingleton_of_injective_of_surjective
    (hf.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex
      hW hδ hN a₀)
    (hf.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex
      hW hδ (by rw [_root_.Finite.card_option]; exact hN) a₀)

section Homology

variable {A_cat : Type v} [Category.{w} A_cat] [Abelian A_cat] [HasCoproducts.{u} A_cat]

/-- **Epimorphism `H_k(A; R) ⟶ H_k(X; R)` for `k < n` on a compactified pair.** If `A ↪ W` induces
a singular homology isomorphism in degree `k` on a set `W` containing a positive sublevel `{F ≤ δ}`,
then `A ↪ X` induces an epimorphism `H_k(A; R) ⟶ H_k(X; R)` for `k < n`. -/
theorem IsMorse.epi_homologyMap_subtypeVal_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k < n) :
    Epi (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))) R k) := by
  obtain ⟨a, b, hab, -, -, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let ebIso := TopCat.isoOfHomeo (X := TopCat.of ↥{x | F x ≤ b}) (Y := TopCat.of X)
    (sublevelHomeoUniv fun x ↦ (hFb x).le)
  let H := (AlgebraicTopology.singularHomologyFunctor A_cat k).obj R
  let β : TopCat.of ↥{x | F x ≤ a} ⟶ TopCat.of W := TopCat.ofHom (ContinuousMap.inclusion haW)
  let γ : TopCat.of W ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let iAW : TopCat.of A ⟶ TopCat.of W := TopCat.ofHom (ContinuousMap.inclusion hAW)
  have : Epi (H.map (TopCat.ofHom (sublevelInclusion F a b hab))) := by
    rw [singularHomologyFunctor_obj_map]
    exact hf.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt ha_reg hb_reg
      (fun p hp ↦ hindex p hp.1) R hk
  have hβγ : β ≫ γ = TopCat.ofHom (sublevelInclusion F a b hab) ≫ ebIso.hom := by
    dsimp only [ebIso]
    rw [sublevelInclusion_eq_inclusion, TopCat.isoOfHomeo_hom]
    ext x
    rfl
  have : Epi (H.map β ≫ H.map γ) := by
    rw [← H.map_comp, hβγ, H.map_comp]
    exact epi_comp (H.map (TopCat.ofHom (sublevelInclusion F a b hab))) (H.map ebIso.hom)
  have : Epi (H.map γ) := epi_of_epi (H.map β) (H.map γ)
  have : IsIso (H.map iAW) := by
    rwa [singularHomologyFunctor_obj_map]
  have hcomp : iAW ≫ γ = TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) := by
    ext x
    rfl
  have hepi : Epi (H.map iAW ≫ H.map γ) := epi_comp (H.map iAW) (H.map γ)
  rw [← H.map_comp, hcomp] at hepi
  dsimp only [H] at hepi
  rwa [singularHomologyFunctor_obj_map] at hepi

/-- **Monomorphism `H_k(A; R) ⟶ H_k(X; R)` for `k + 1 < n` on a compactified pair.** If `A ↪ W`
induces a singular homology isomorphism in degree `k` on a set `W` containing a positive sublevel
`{F ≤ δ}`, then `A ↪ X` induces a monomorphism `H_k(A; R) ⟶ H_k(X; R)` for `k + 1 < n`. -/
theorem IsMorse.mono_homologyMap_subtypeVal_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k + 1 < n) :
    Mono (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))) R k) := by
  obtain ⟨a, b, hab, -, hAa, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let ebIso := TopCat.isoOfHomeo (X := TopCat.of ↥{x | F x ≤ b}) (Y := TopCat.of X)
    (sublevelHomeoUniv fun x ↦ (hFb x).le)
  let H := (AlgebraicTopology.singularHomologyFunctor A_cat k).obj R
  let α : TopCat.of A ⟶ TopCat.of ↥{x | F x ≤ a} := TopCat.ofHom (ContinuousMap.inclusion hAa)
  let β : TopCat.of ↥{x | F x ≤ a} ⟶ TopCat.of W := TopCat.ofHom (ContinuousMap.inclusion haW)
  have hαβ : α ≫ β = TopCat.ofHom (ContinuousMap.inclusion hAW) := by
    ext x
    rfl
  have : IsIso (H.map (TopCat.ofHom (ContinuousMap.inclusion hAW))) := by
    rwa [singularHomologyFunctor_obj_map]
  have : Mono (H.map α ≫ H.map β) := by
    rw [← H.map_comp, hαβ]
    infer_instance
  have : Mono (H.map α) := mono_of_mono (H.map α) (H.map β)
  have : IsIso (H.map (TopCat.ofHom (sublevelInclusion F a b hab))) := by
    rw [singularHomologyFunctor_obj_map]
    exact hf.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt ha_reg
      hb_reg (fun p hp ↦ hindex p hp.1) R hk
  have hcomp : α ≫ TopCat.ofHom (sublevelInclusion F a b hab) ≫ ebIso.hom =
      TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) := by
    dsimp only [ebIso]
    rw [sublevelInclusion_eq_inclusion, TopCat.isoOfHomeo_hom]
    ext x
    rfl
  let rest := TopCat.ofHom (sublevelInclusion F a b hab) ≫ ebIso.hom
  have : Mono (H.map rest) := by
    dsimp only [rest]
    rw [H.map_comp]
    exact mono_comp (H.map (TopCat.ofHom (sublevelInclusion F a b hab))) (H.map ebIso.hom)
  have hmono : Mono (H.map α ≫ H.map rest) := mono_comp (H.map α) (H.map rest)
  rw [← H.map_comp] at hmono
  dsimp only [rest, H] at hmono
  rwa [hcomp, singularHomologyFunctor_obj_map] at hmono

/-- **Isomorphism `H_k(A; R) ≅ H_k(X; R)` for `k + 1 < n` on a compactified pair.** If `A ↪ W`
induces a singular homology isomorphism in degree `k` on a set `W` containing a positive sublevel
`{F ≤ δ}`, then `A ↪ X` induces an isomorphism `H_k(A; R) ≅ H_k(X; R)` for `k + 1 < n`. -/
theorem IsMorse.isIso_homologyMap_subtypeVal_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k + 1 < n) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))) R k) := by
  let f : TopCat.of A ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have : Mono (SSet.homologyMap (TopCat.toSSet.map f) R k) :=
    hf.mono_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R hW hδ hk
  have : Epi (SSet.homologyMap (TopCat.toSSet.map f) R k) :=
    hf.epi_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R hW hδ
      (by omega)
  exact isIso_of_mono_of_epi (SSet.homologyMap (TopCat.toSSet.map f) R k)

/-- **Relative singular homology vanishing `H_k(X, A; R) = 0` for `k < n` on a compactified
pair.** If `A ↪ W` induces singular homology isomorphisms in degree `k` and (when `k > 0`) degree
`k - 1` on a set `W` containing a positive sublevel `{F ≤ δ}`, then `H_k(X, A; R) = 0` for
`k < n`. -/
theorem IsMorse.isZero_singularHomology_ofSubset_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : ∀ m, m = k ∨ m + 1 = k → IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R m))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k < n) :
    IsZero ((TopPair.ofSubset (X := TopCat.of X) A).singularHomology R k) := by
  let P := TopPair.ofSubset (X := TopCat.of X) A
  have hepi : Epi (SSet.homologyMap (TopCat.toSSet.map P.map) R k) :=
    hf.epi_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R
      (hW k (.inl rfl)) hδ hk
  have hπ : P.singularHomologyπ R k = 0 :=
    (cancel_epi (SSet.homologyMap (TopCat.toSSet.map P.map) R k)).1
      ((P.homologyMap_comp_singularHomologyπ R k).trans comp_zero.symm)
  rcases k with _ | k
  · exact (IsZero.iff_id_eq_zero _).2 <| (cancel_epi (P.singularHomologyπ R 0)).1 <|
      (Category.comp_id _).trans (hπ.trans comp_zero.symm)
  · have hmono : Mono (SSet.homologyMap (TopCat.toSSet.map P.map) R k) :=
      hf.mono_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R
        (hW k (.inr rfl)) hδ hk
    have hδ₀ : P.singularHomologyδ R (k + 1) k rfl = 0 :=
      (cancel_mono (SSet.homologyMap (TopCat.toSSet.map P.map) R k)).1
        ((P.singularHomologyδ_comp R (k + 1) k rfl).trans zero_comp.symm)
    exact (P.singularHomology_exact_relative R (k + 1) k rfl).isZero_X₂ hπ hδ₀

end Homology

end PairConnectivity

end TauCeti
