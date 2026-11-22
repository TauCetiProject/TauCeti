/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Topology.VectorBundle.Orientation.RankDegreeHomology
public import TauCeti.Topology.VectorBundle.Orientation.TwistedHomology.Basic
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Topology.VectorBundle.EulerClass

/-!
# The homology across a Morse–Bott level in the degree of the index

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on the level
`f = c`, with Morse index `r` along it, and let `g` be a smooth fibre metric on its normal bundle.
The negative normal spaces relative to `g` form a real vector bundle `ν⁻ → S` of rank `r`, the
negative normal bundle. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all its
critical points lie on `i`. Bott's theorem identifies the relative homology across the level with
the homology of `S` shifted by the index and twisted by the orientation local system `o(ν⁻)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`):
`Hⱼ({f ≤ b}, {f ≤ a}; ℤ) ≅ H_{j - r}(S; o(ν⁻))`. This file proves this identification in the
degrees `j < r`, and also in the degree `j = r` when the index `r` is positive, with no
orientation of `ν⁻`:

* below the index the relative homology vanishes, with any coefficients
  (`isZero_singularHomology_sublevelPair_of_lt`), and likewise the relative cohomology when the
  chain coefficients are projective (`isZero_singularCohomology_sublevelPair_of_lt`);
* in the degree of a positive index, `Hᵣ({f ≤ b}, {f ≤ a}; ℤ) ≅ H₀(S; o(ν⁻))`
  (`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, stated for index `r + 1`).

The relative homology across the level is that of the Thom pair `(ν⁻, ν⁻₀)`
(`nonempty_singularHomology_sublevelPair_iso_thomPair`), whose homology vanishes below the rank
(`TauCeti.isZero_singularHomology_thomPair_of_compactSpace`) and is `H₀(S; o(ν⁻))` in the rank
degree (`TauCeti.thomPairSingularHomologyIsoTwistedHomology`).

For a connected critical submanifold of positive index the group `H₀(S; o(ν⁻))` is `ℤ` when `ν⁻`
is orientable and `ℤ/2` when it is not, so the integral homology across the level in the degree of
the index detects the orientability of the negative normal bundle:

* `Hᵣ({f ≤ b}, {f ≤ a}; ℤ) ≅ ℤ` exactly when `ν⁻` is orientable
  (`nonempty_vectorBundleOrientation_iff_nonempty_singularHomology_sublevelPair_linearEquiv`);
* `Hᵣ({f ≤ b}, {f ≤ a}; ℤ) ≅ ℤ/2` when it is not
  (`nonempty_singularHomology_sublevelPair_linearEquiv_quotient_two`).

For instance, a critical circle of index one whose negative normal bundle is a Möbius line
contributes `ℤ/2` in degree one, not the group `H₀(S¹; ℤ) = ℤ` that constant coefficients would
give.

For the twisted-homology and orientability statements in the second part, `M`, `S` and the model
space of `M` live in `Type`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module Set Topology
open TauCeti.VectorBundleOrientationCover TauCeti.LocalCoefficientSystem
open scoped ContDiff Manifold

universe u

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

section VanishingBelowIndex

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' : Type*} {S : Type u} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
  (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
  (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)

omit [SecondCountableTopology M] [FiniteDimensional ℝ E'] [J.Boundaryless] [IsManifold J ∞ S] in
include hfs hcompact hcrit in
/-- If the critical submanifold is empty, the band has no critical points, so it carries no
relative homology. -/
private theorem isZero_singularHomology_sublevelPair_of_isEmpty [IsEmpty S]
    {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C) (k : ℕ) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularHomology R k) :=
  isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hfs _ hcompact
    (fun _ hax hxb hx ↦ isEmptyElim (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx,
      hax, hxb⟩).choose) R k

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a Morse–Bott level the relative homology vanishes below the index.** Let
`i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `f = c` along `i` and Morse
index `r` at every point of `i`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and
all its critical points lie on `i`. Then `Hₖ({f ≤ b}, {f ≤ a}) = 0` for `k < r`, with coefficients
in any abelian category with coproducts. -/
theorem isZero_singularHomology_sublevelPair_of_lt {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C) {k : ℕ} (hk : k < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularHomology R k) := by
  cases isEmpty_or_nonempty S with
  | inl _ => exact isZero_singularHomology_sublevelPair_of_isEmpty hfs hac hcb hcompact hcrit R k
  | inr _ =>
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
    have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
      hc hac.le hcb.le hcompact hcrit
    have : T2Space S := i.isEmbedding.t2Space
    -- Choose a smooth fibre metric `g` on the normal bundle, modelled on a Euclidean space; the
    -- negative normal spaces relative to `g` form a vector bundle of rank `r`.
    let P₀ := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E'))
    have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := finrank_euclideanSpace_fin
    let := i.normalSpaceFiberBundle hn hdim
    let := i.normalSpaceVectorBundle hn hdim
    have := i.normalSpaceContMDiffVectorBundle hn (m := ∞) (by simp) hdim
    obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤)
      (F := P₀) (E := fun s ↦ i.NormalSpace s hn)
    have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    have hVu := hV.hasLocalSubbundleFrames.comp_equiv Equiv.ulift
    let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    let := hVu.fiberBundle
    have := hVu.vectorBundle
    have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
      rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
    obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
      hcrit hdim g hr R k
    have hzero : IsZero ((thomPair (ULift.{u} (Fin r) → ℝ)
        fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s).singularHomology R k) :=
      isZero_singularHomology_thomPair_of_compactSpace R (hrank.symm ▸ hk)
    exact hzero.of_iso (e ≪≫ TopPair.singularHomologyMapIso R
      (subbundleThomPairModelIso P₀ (Fin r → ℝ) (ULift.{u} (Fin r) → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)) k)

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a Morse–Bott level the relative cohomology vanishes below the index.** Under the
hypotheses of `isZero_singularHomology_sublevelPair_of_lt`, the relative singular cohomology
`Hᵐ({f ≤ b}, {f ≤ a}; R, N)` vanishes for every `m < r` whenever the chain coefficient object
`R` is projective. -/
theorem isZero_singularCohomology_sublevelPair_of_lt {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (N : C) {m : ℕ} (hmr : m < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularCohomology R k N m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R N m fun _ hj ↦
    h.isZero_singularHomology_sublevelPair_of_lt hfs hc hac hcb hcompact hcrit hr R
      (hj.trans_lt hmr)

end VanishingBelowIndex

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' : Type*} {S : Type} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)
  (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
  (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
  (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
  (g : letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a Morse–Bott level, in the degree of the index, the relative homology is the zeroth
homology of the critical submanifold with orientation coefficients.** Let `i : S → M` be a
nondegenerate critical submanifold of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, with `f = c` along `i`, and let `g` be a smooth fibre
metric on its normal bundle. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all
its critical points lie on `i`. Suppose that the negative normal spaces relative to `g` have
continuous local frames of size `r + 1`, so that they form the negative normal bundle `ν⁻` of rank
`r + 1`; the Morse index of `f` along `i` is then `r + 1`, and conversely such frames exist when
the Morse index is `r + 1` at every point of `i`
(`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`). Then
`H_{r+1}({f ≤ b}, {f ≤ a}; ℤ) ≅ H₀(S; o(ν⁻))`, where `o(ν⁻)` is the orientation local system of
`ν⁻`. No orientation of `ν⁻` is assumed. -/
theorem nonempty_singularHomology_sublevelPair_iso_twistedHomology {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin (r + 1)) (h.negativeNormalSpace hn g.toRiemannianMetric)) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (r + 1) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (r + 1) ≅
      twistedHomology.{0, 0, 0} (signLocalSystem (Fin (r + 1) → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) ℤ
        ((Fintype.card_fin (r + 1)).trans (finrank_fin_fun ℝ).symm)) 0) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin (r + 1) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  cases isEmpty_or_nonempty S with
  | inl _ =>
    -- Over an empty critical submanifold both groups vanish.
    have : IsEmpty (TopCat.of S) := inferInstanceAs (IsEmpty S)
    exact ⟨(isZero_singularHomology_sublevelPair_of_isEmpty hfs hac hcb hcompact hcrit _ _).iso
      (isZero_twistedHomology_of_isEmpty _ 0)⟩
  | inr _ =>
    -- The frames have size the dimension of the negative normal spaces, which is the index.
    have hr (s : S) : manifoldMorseIndex I f (i s) = r + 1 := by
      rw [← h.finrank_negativeNormalSpace hn g.toRiemannianMetric, hV.finrank_eq,
        Fintype.card_fin]
    obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
      hcrit hdim g hr (ModuleCat.of ℤ (ULift.{0} ℤ)) (r + 1)
    exact ⟨e ≪≫ thomPairSingularHomologyIsoTwistedHomology (Fin (r + 1) → ℝ) _
      (finrank_fin_fun ℝ)⟩

include h hfs hc hac hcb hcompact hcrit in
/-- **The homology across a connected Morse–Bott level detects the orientability of the negative
normal bundle.** Under the hypotheses of
`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, with `S` connected, the integral
relative homology `H_{r+1}({f ≤ b}, {f ≤ a}; ℤ)` in the degree of the index is isomorphic to `ℤ`
exactly when the negative normal bundle `ν⁻` is orientable. -/
theorem nonempty_vectorBundleOrientation_iff_nonempty_singularHomology_sublevelPair_linearEquiv
    [ConnectedSpace S] {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin (r + 1)) (h.negativeNormalSpace hn g.toRiemannianMetric)) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (r + 1) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    Nonempty (VectorBundleOrientation (Fin (r + 1) → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (Fin (r + 1))) ↔
      Nonempty (((sublevelPair f (hac.trans hcb).le).singularHomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (r + 1) : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ℤ) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin (r + 1) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := J.locallyPathConnectedSpace_of_chartedSpace S
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_twistedHomology hn hfs hc hac hcb
    hcompact hcrit hdim g hV
  rw [VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv
    ((Fintype.card_fin (r + 1)).trans (finrank_fin_fun ℝ).symm) (two_ne_zero : (2 : ℤ) ≠ 0)]
  exact ⟨fun ⟨φ⟩ ↦ ⟨e.toLinearEquiv ≪≫ₗ φ⟩, fun ⟨φ⟩ ↦ ⟨e.symm.toLinearEquiv ≪≫ₗ φ⟩⟩

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a connected Morse–Bott level with non-orientable negative normal bundle the integral
homology in the degree of the index is `ℤ/2`.** Under the hypotheses of
`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, with `S` connected and the negative
normal bundle `ν⁻` not orientable, `H_{r+1}({f ≤ b}, {f ≤ a}; ℤ) ≅ ℤ ⧸ 2ℤ`. -/
theorem nonempty_singularHomology_sublevelPair_linearEquiv_quotient_two [ConnectedSpace S]
    {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin (r + 1)) (h.negativeNormalSpace hn g.toRiemannianMetric))
    (ho : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin (r + 1) → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      haveI := hV.vectorBundle
      IsEmpty (VectorBundleOrientation (Fin (r + 1) → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (Fin (r + 1)))) :
    Nonempty (((sublevelPair f (hac.trans hcb).le).singularHomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (r + 1) : ModuleCat.{0} ℤ) ≃ₗ[ℤ]
      ℤ ⧸ Ideal.span {(2 : ℤ)}) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin (r + 1) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := J.locallyPathConnectedSpace_of_chartedSpace S
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_twistedHomology hn hfs hc hac hcb
    hcompact hcrit hdim g hV
  -- Any orientation of a single fibre serves as the base point of the identification.
  let o := (Module.finBasisOfFinrankEq ℝ _
    ((hV.finrank_eq s).trans (Fintype.card_fin (r + 1)))).orientation
  exact ⟨e.toLinearEquiv ≪≫ₗ twistedHomology₀EquivQuotientTwo
    ((Fintype.card_fin (r + 1)).trans (finrank_fin_fun ℝ).symm) ho o⟩

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
