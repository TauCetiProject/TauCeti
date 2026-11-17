/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Topology.VectorBundle.Attachment

/-!
# Relative homology across the level of a compact Morse–Bott submanifold

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f`, on the
level `f = c`, and let `g` be a smooth fibre metric on its normal bundle. Write `M_t = {f ≤ t}`.
Crossing the level attaches the negative disc bundle: for a Morse–Bott normal form `Θ` near the
zero section of the normal bundle and all small `ε > 0` such that the band `f⁻¹[c-ε, c+ε]` is
compact and all its critical points lie on `i`, the sublevel `M_{c+ε}` strong deformation
retracts onto `M_{c-ε} ∪ Θ(D_ε)`, where `D_ε` is the negative disc bundle of size `ε`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in
the namespace `TauCeti.SmoothEmbedding`).

This file reads that attachment in relative singular homology. The image `Θ(D_ε)` lies in the
critical sublevel `M_c`, since the normal Hessian is negative on the negative normal spaces, and
the deformation fixes `M_{c-ε} ∪ Θ(D_ε)`. So, for the same `ε`, the inclusion of pairs

`(M_{c-ε} ∪ Θ(D_ε), M_{c-ε}) ⟶ (M_{c+ε}, M_{c-ε})`

induces isomorphisms on relative singular homology, with coefficients in any preadditive category
with coproducts and homology (`exists_isIso_singularHomologyMap_negativeDiscBundle`).

The width `ε` can be replaced by arbitrary regular levels: if `a < c < b`, the band `f⁻¹[a, b]` is
compact and its critical points lie on the submanifold, then `c` is its only critical value, so
`Hₙ(M_b, M_a)` is isomorphic to `Hₙ(M_{c+ε}, M_{c-ε})`
(`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`), hence to the relative homology of the
lower sublevel with the negative disc bundle attached
(`nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`). Groups `Hₙ(M_b, M_a)` of this
kind, between consecutive regular levels, are the first-page terms of the spectral sequence of the
filtration of a manifold by the sublevels of `f`; this identifies the contribution of a compact
Morse–Bott critical submanifold through its negative disc bundle. For an isolated nondegenerate
critical point the base is a point and the disc bundle is a cell of dimension the Morse index.

The relative homology across the critical level can also be read off a parametrization of the
negative disc bundle. Write the normal form as `f = c - s + t` on a tube `W`, and suppose that the
negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}` is parametrized by the disc bundle `D_ρ(V)` of a
fibre gauge `ρ` on a real vector bundle `V → B`, for instance the negative normal bundle with a
fibre metric: a map `g` restricting to a closed embedding of `D_ρ(V)` onto the negative disc bundle,
and of the sphere bundle `S_ρ(V)` onto its boundary `{t = 0, s = ε}`. Then `g` induces a map of
pairs `(D_ρ(V), S_ρ(V)) ⟶ (M_{c+ε}, M_{c-ε})` which is an isomorphism on relative singular
homology in every degree
(`TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`), so
`Hₙ(M_{c+ε}, M_{c-ε})` is the relative homology `Hₙ(V, V₀)` of the Thom pair of `V`
(`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`). The Thom isomorphism, which this
file does not use, identifies the homology of the Thom pair with the homology of the base `B`,
shifted by the rank of `V` and with coefficients twisted by the orientation of `V`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isIso_singularHomologyMap_negativeDiscBundle`: the inclusion of the lower sublevel with
  the negative disc bundle attached into the upper sublevel, relative to the lower sublevel,
  induces isomorphisms on relative singular homology.
* `nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`: the relative homology of the
  sublevels at two regular levels around the critical level is the relative homology of the lower
  sublevel with the negative disc bundle attached.

In the namespace `TauCeti`:

* `exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`: a parametrization of
  the negative disc bundle induces isomorphisms `Hₙ(D_ρ(V), S_ρ(V)) ≅ Hₙ(M_{c+ε}, M_{c-ε})`.
* `nonempty_singularHomology_sublevelPair_iso_thomPair`: the relative homology across the
  critical level is that of the Thom pair, `Hₙ(M_{c+ε}, M_{c-ε}) ≅ Hₙ(V, V₀)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

namespace SmoothEmbedding

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- **The relative homology across the level of a Morse–Bott submanifold is carried by its
negative disc bundle.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth
function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `S`
nonempty and `f = c` along `i`, and let `g` be a smooth fibre metric on its normal bundle.

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on `i`. Then the negative disc bundle `D_ε` relative to `g` lies in the source
of `Θ`, the set `{f ≤ c - ε} ∪ Θ(D_ε)` lies in `{f ≤ c + ε}`, and the inclusion of pairs
`({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε}) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on
relative singular homology, in every degree and for every coefficient object. Such an `ε` exists
only when `S` is compact, since the image of `i` is then the closed set of critical points of the
compact band. -/
theorem exists_isIso_singularHomologyMap_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∃ hA : {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆
            {y | f y ≤ c + ε},
          ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Preadditive A]
            [CategoryWithHomology A] (R : A) (n : ℕ),
            IsIso ((TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
                {y | f y ≤ c - ε} ⊆
                  {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)
              ).singularHomologyMap (TopPair.ofInclusionMap (Y := TopCat.of M) _
                (sublevel_mono f (a := c - ε) (b := c + ε) (by linarith))
                (ContinuousMap.inclusion hA) fun _ hx ↦ hx) R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  by_cases hS : CompactSpace S
  swap
  · -- If `S` is not compact, no `ε` satisfies the hypotheses, and only the normal form remains.
    obtain ⟨Θ, hΘz, hΘi, -, hΘf⟩ := h.exists_morseBott_partialDiffeomorph_normalBundle hn
      (k := ⊤) (by simp) hdim isOpen_univ (subset_univ _) (hfs.contMDiffOn.of_le (by simp))
    refine ⟨Θ, hΘz, hΘi, fun x hx ↦ by rw [hΘf x hx, hc], 1, one_pos,
      fun ε hε _ hcompact hcrit ↦ ?_⟩
    exact (hS (h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
      (hfs.of_le (by simp)) hc (by linarith) (by linarith) hcompact hcrit)).elim
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  set D := h.negativeDiscBundle hn P g.toRiemannianMetric ε
  obtain ⟨hD, r, -, ⟨G⟩⟩ := hmain ε ⟨hε, hεε₀⟩ hcompact hcrit
  -- The disc bundle lies in the critical sublevel, since the normal Hessian is negative on the
  -- negative normal spaces.
  have hA : {y | f y ≤ c - ε} ∪ Θ '' D ⊆ {y | f y ≤ c + ε} := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact sublevel_mono f (by linarith) hy
    · have hneg := (h.toIsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx |>.1
      have hle : h.normalHessian hn x.proj x.2 x.2 ≤ 0 := by
        rcases eq_or_ne x.2 0 with h0 | h0
        · simp [h0]
        · exact (h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn _ hneg h0).le
      rw [mem_ofPred_eq, hΘf x (hD hx)]
      linarith
  -- The deformation retracts `{f ≤ c + ε}` onto `{f ≤ c - ε} ∪ Θ(D_ε)`, fixing it pointwise.
  refine ⟨hD, hA, fun {A} _ _ _ _ R n ↦
    TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel (X := TopCat.of M)
      subset_union_left hA ((ContinuousMap.inclusion inter_subset_right).comp r)
      (G.cast (ContinuousMap.ext fun _ ↦ rfl) rfl) R n⟩

/-- **The relative homology of a critical band of a Morse–Bott submanifold.** Let `i : S → M` be
a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, with `S` nonempty and `f = c` along `i`, and let `g`
be a smooth fibre metric on its normal bundle. Let `a < c < b` be such that the band `f⁻¹[a, b]`
is compact and all its critical points lie on `i`; then `S` is compact.

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for every
`0 < ε < ε₀` the negative disc bundle `D_ε` relative to `g` lies in the source of `Θ` and the
relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to
`Hₙ({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε})`, in every degree and for every coefficient object. -/
theorem nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆
                {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)
              ).singularHomology R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_isIso_singularHomologyMap_negativeDiscBundle hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, min ε₀ (min (c - a) (b - c)),
    lt_min hε₀ (lt_min (by linarith) (by linarith)), fun ε hε ↦ ?_⟩
  obtain ⟨hε0, hεm⟩ := hε
  have hε₁ : ε < ε₀ := hεm.trans_le (min_le_left _ _)
  have hεa : ε < c - a := hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < b - c := hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε' : Icc (c - ε) (c + ε) ⊆ Icc a b := Icc_subset_Icc (by linarith) (by linarith)
  have hcompact' : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) (preimage_mono hε')
  -- Every critical point of the band lies on the submanifold, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨s, rfl⟩ := hcrit ⟨hx, hfx⟩
    exact hc s
  obtain ⟨hD, _, hiso⟩ := hmain ε hε0 hε₁ hcompact' fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  refine ⟨hD, fun {A} _ _ _ R n ↦ ⟨singularHomologySublevelPairIsoOfCriticalValue hfs hac hcb
    (by linarith : c - ε < c) (by linarith : c < c + ε) hcompact hcompact' hlev
    (fun x hx hfx ↦ hlev x hx (hε' hfx)) R n ≪≫ (@asIso _ _ _ _ _ (hiso R n)).symm⟩⟩

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

/-! ### The negative disc bundle parametrized by a vector bundle -/

section ThomPair

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type u} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **The relative homology across a Morse–Bott critical level is that of the disc-sphere pair of
the negative bundle.** Let `f` be smooth, with the quadratic normal form `f = c - s + t` on a tube
`W` and the scaling `φ` of the positive directions of
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`, whose hypotheses are repeated here.
Let `ρ` be a fibre gauge on a real vector bundle `V → B`, for instance a fibre norm which is
continuous on the total space, and let `g` restrict to a closed embedding of the disc bundle
`D_ρ(V)` onto the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}`, carrying the sphere bundle
`S_ρ(V)` onto `{x ∈ W | t x = 0, s x = ε}`. Then `g` induces a map of pairs
`(D_ρ(V), S_ρ(V)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` which is an isomorphism on relative singular
homology, with coefficients in any abelian category with coproducts, in every degree. -/
theorem exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hW : IsOpen W) (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W)
    (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x)
    (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hdir : ∀ x ∈ W, t x ≠ 0 → ∃ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) s x v = 0 ∧ mfderiv I 𝓘(ℝ) t x v ≠ 0)
    (φ : C(unitInterval × W, W)) (hφs : ∀ τ x, s (φ (τ, x)) = s x)
    (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x) (hφ₁ : ∀ x, φ (1, x) = x)
    (hφ₀ : ∀ τ (x : W), t x = 0 → φ (τ, x) = x) (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ W)
    (hρ : IsFiberGauge ρ)
    (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g))
    (hgD : g '' gaugeDiscBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' gaugeSphereBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x = ε}) :
    ∃ ψ : gaugeDiscSpherePair ρ ⟶ sublevelPair f (a := c - ε) (b := c + ε) (by linarith),
      (∀ v : gaugeDiscBundle ρ, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      ∀ {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ),
        IsIso (TopPair.singularHomologyMap ψ R n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevel_union_negativeDiscBundle_deformation hfs hW hs ht hs₀ ht₀
    hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit
  refine exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle hρ
    (sublevel_mono f (by linarith)) (isClosed_le hfs.continuous continuous_const) hg hgD
    (fun x ⟨hxW, htx, _⟩ ↦ ?_) (fun v hv ↦ ?_) r G
  · -- On the negative disc bundle `f = c - s ≤ c`.
    rw [mem_ofPred_eq, hf x hxW, htx]
    linarith [hs₀ x hxW]
  · -- A point of the disc bundle lies in `{f ≤ c - ε}` exactly when `s = ε` there, that is, when
    -- it is the image of a point of the sphere bundle.
    obtain ⟨hxW, htx, hsx⟩ : g v ∈ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε} := hgD ▸ mem_image_of_mem g hv
    rw [mem_ofPred_eq, hf _ hxW, htx]
    refine ⟨fun hle ↦ ?_, fun hvS ↦ ?_⟩
    · obtain ⟨w, hw, hwv⟩ : g v ∈ g '' gaugeSphereBundle ρ := hgS ▸ ⟨hxW, htx, by linarith⟩
      obtain rfl : w = v :=
        congrArg Subtype.val
          (@hg.injective ⟨w, gaugeSphereBundle_subset_gaugeDiscBundle ρ hw⟩ ⟨v, hv⟩ hwv)
      exact hw
    · have : g v ∈ {x | x ∈ W ∧ t x = 0 ∧ s x = ε} := hgS ▸ mem_image_of_mem g hvS
      linarith [this.2.2]

/-- **The relative homology across a Morse–Bott critical level is that of the Thom pair of the
negative bundle.** Under the hypotheses of
`TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`, the relative singular
homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R)` is isomorphic to the relative homology `Hₙ(V, V₀; R)`
of the Thom pair of `V`, `V₀` the complement of the zero section, for coefficients in any abelian
category with coproducts. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hW : IsOpen W) (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W)
    (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x)
    (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hdir : ∀ x ∈ W, t x ≠ 0 → ∃ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) s x v = 0 ∧ mfderiv I 𝓘(ℝ) t x v ≠ 0)
    (φ : C(unitInterval × W, W)) (hφs : ∀ τ x, s (φ (τ, x)) = s x)
    (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x) (hφ₁ : ∀ x, φ (1, x) = x)
    (hφ₀ : ∀ τ (x : W), t x = 0 → φ (τ, x) = x) (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ W)
    (hρ : IsFiberGauge ρ)
    (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g))
    (hgD : g '' gaugeDiscBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' gaugeSphereBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x = ε})
    {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n ≅
      (thomPair F V).singularHomology R n) := by
  obtain ⟨ψ, -, hψ⟩ := exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle hfs hW
    hs ht hs₀ ht₀ hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS
  have := hψ R n
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n
  exact ⟨(asIso (TopPair.singularHomologyMap ψ R n)).symm ≪≫
    asIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n)⟩

end ThomPair

end TauCeti
