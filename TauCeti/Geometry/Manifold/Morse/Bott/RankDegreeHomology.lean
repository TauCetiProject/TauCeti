/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.TwistedHomology
public import TauCeti.Topology.VectorBundle.Orientation.TwistedHomology.Basic
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# The homology across a Morse–Bott level in the degree of the index

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on the level
`f = c`, with Morse index `r` along it, and let `g` be a smooth fibre metric on its normal bundle.
The negative normal spaces relative to `g` form a real vector bundle `ν⁻ → S` of rank `r`, the
negative normal bundle. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all its
critical points lie on `i`. Bott's theorem identifies the relative homology across the level with
the homology of `S` shifted by the index and twisted by the orientation local system `o(ν⁻)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`): over every commutative ring `K`,
`Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K) ≅ Hₚ(S; o(ν⁻) ⊗ K)`
(`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`, in
`TauCeti.Geometry.Manifold.Morse.Bott.Thom.TwistedHomology`). This file treats the degrees up to
the index:

* below the index the relative homology vanishes, with coefficients in any abelian category with
  coproducts (`isZero_singularHomology_sublevelPair_of_lt`), since the homology of the Thom pair
  `(ν⁻, ν⁻₀)` vanishes below the rank over the compact base `S`
  (`TauCeti.isZero_singularHomology_thomPair_of_compactSpace`);
* in the degree of the index the relative homology is `H₀(S; o(ν⁻) ⊗ K)`.

For a connected critical submanifold the group `H₀(S; o(ν⁻) ⊗ K)` is `K` when `ν⁻` is orientable
and `K ⧸ 2K` when it is not, so the relative homology across the level in the degree of the index
detects the orientability of the negative normal bundle:

* if `2 ≠ 0` in `K`, `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ K` exactly when `ν⁻` is orientable
  (`nonempty_vectorBundleOrientation_iff_nonempty_singularHomology_sublevelPair_linearEquiv`);
* `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ K ⧸ 2K` when it is not
  (`nonempty_singularHomology_sublevelPair_linearEquiv_quotient_two`).

For instance, with `K = ℤ`, a critical circle of index one whose negative normal bundle is a
Möbius line contributes `ℤ/2` in degree one, not the group `H₀(S¹; ℤ) = ℤ` that constant
coefficients would give.

The manifolds and the ring lie in any one universe.

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

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)
  (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
  (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
  (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)

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
  | inl _ =>
    exact isZero_singularHomology_sublevelPair_of_isEmpty hfs (hac.trans hcb).le hcompact hcrit R k
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
    have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E'))) =
        finrank ℝ E - finrank ℝ E' := finrank_euclideanSpace_fin
    let := i.normalSpaceFiberBundle hn hdim
    let := i.normalSpaceVectorBundle hn hdim
    have := i.normalSpaceContMDiffVectorBundle hn (m := ∞) (by simp) hdim
    obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤)
      (F := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E')))
          (E := fun s ↦ i.isImmersion.NormalSpace s hn)
    let := subbundleTopology (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E')))
      (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    let := hV.fiberBundle
    have := hV.vectorBundle
    obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
      hcrit hdim g hr R k
    exact (isZero_singularHomology_thomPair_of_compactSpace R (by simpa using hk)).of_iso e

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
  (g : letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiffRiemannianMetric J ∞ P fun s ↦ i.isImmersion.NormalSpace s hn)

include h hfs hc hac hcb hcompact hcrit in
/-- **The homology across a connected Morse–Bott level detects the orientability of the negative
normal bundle.** Under the hypotheses of
`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, with `S` connected and the negative
normal bundle `ν⁻` of rank `r`, let `K` be a commutative ring in which `2 ≠ 0`, for instance `ℤ`.
Then the relative homology `Hᵣ({f ≤ b}, {f ≤ a}; K)` in the degree of the index is isomorphic to
`K` exactly when `ν⁻` is orientable. -/
theorem nonempty_vectorBundleOrientation_iff_nonempty_singularHomology_sublevelPair_linearEquiv
    [ConnectedSpace S] {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric))
    (K : Type u) [CommRing K] (h2 : (2 : K) ≠ 0) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    Nonempty (VectorBundleOrientation (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (Fin r)) ↔
      Nonempty (((sublevelPair f (hac.trans hcb).le).singularHomology
        (ModuleCat.of K K) r : ModuleCat.{u} K) ≃ₗ[K] K) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := J.locallyPathConnectedSpace_of_chartedSpace S
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_twistedHomology hn hfs hc hac hcb
    hcompact hcrit hdim g hV K (add_zero r)
  rw [VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv
    ((Fintype.card_fin r).trans (finrank_fin_fun ℝ).symm) h2]
  exact ⟨fun ⟨φ⟩ ↦ ⟨e.toLinearEquiv ≪≫ₗ φ⟩, fun ⟨φ⟩ ↦ ⟨e.symm.toLinearEquiv ≪≫ₗ φ⟩⟩

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a connected Morse–Bott level with non-orientable negative normal bundle the homology
in the degree of the index is `K ⧸ 2K`.** Under the hypotheses of
`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, with `S` connected and the negative
normal bundle `ν⁻` of rank `r` not orientable, `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ K ⧸ 2K` for every
commutative ring `K`; for `K = ℤ` this is `ℤ/2`. -/
theorem nonempty_singularHomology_sublevelPair_linearEquiv_quotient_two [ConnectedSpace S]
    {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric))
    (ho : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      haveI := hV.vectorBundle
      IsEmpty (VectorBundleOrientation (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (Fin r)))
    (K : Type u) [CommRing K] :
    Nonempty (((sublevelPair f (hac.trans hcb).le).singularHomology
        (ModuleCat.of K K) r : ModuleCat.{u} K) ≃ₗ[K] K ⧸ Ideal.span {(2 : K)}) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := J.locallyPathConnectedSpace_of_chartedSpace S
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_twistedHomology hn hfs hc hac hcb
    hcompact hcrit hdim g hV K (add_zero r)
  -- Any orientation of a single fibre serves as the base point of the identification.
  let o := (Module.finBasisOfFinrankEq ℝ _
    ((hV.finrank_eq s).trans (Fintype.card_fin r))).orientation
  exact ⟨e.toLinearEquiv ≪≫ₗ twistedHomology₀EquivQuotientTwo
    ((Fintype.card_fin r).trans (finrank_fin_fun ℝ).symm) ho o⟩

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
