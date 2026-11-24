/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.GaugeDiscBundle
public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# Relative cohomology across the level of a Morse–Bott critical submanifold

Let `f` be a smooth function on a boundaryless manifold `M`, in the quadratic normal form
`f = c - s + t` on a tube `W` around a critical submanifold on the level `c`, and write
`M_t = {f ≤ t}`. Crossing the level attaches the negative disc bundle
`{x ∈ W | t x = 0, s x ≤ ε}` to `M_{c-ε}`
(`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`). Suppose that this negative disc
bundle is parametrized by the disc bundle `D_ρ(V)` of a fibre gauge `ρ` on a real vector bundle
`V → B` of rank `r`: a map `g` restricting to a closed embedding of `D_ρ(V)` onto it and carrying
the sphere bundle `S_ρ(V)` onto its boundary `{t = 0, s = ε}`. This file computes the relative
cohomology `Hⁿ(M_{c+ε}, M_{c-ε})` from these data, which is Bott's description of the contribution
of a critical submanifold of index `r`: the cohomology of the base, shifted up by the index.

* The map of pairs `(D_ρ(V), S_ρ(V)) ⟶ (M_{c+ε}, M_{c-ε})` induced by `g` is an isomorphism on
  relative singular cohomology with arbitrary coefficients, in every degree
  (`TauCeti.exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle`), so
  `Hⁿ(M_{c+ε}, M_{c-ε}) ≅ Hⁿ(V, V₀)` for the Thom pair of `V`
  (`TauCeti.nonempty_singularCohomology_sublevelPair_iso_thomPair`). These are the cohomological
  forms of `TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle` and
  `TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`.
* For a commutative ring `K`, a Thom class `u ∈ Hʳ(V, V₀; K)` and a `K`-module `N`, the Thom
  isomorphism `a ↦ π^*a ⌣ u` (`TauCeti.thomMap`) then gives
  `Hᵖ⁺ʳ(M_{c+ε}, M_{c-ε}; N) ≅ Hᵖ(B; N)` in every degree `p`
  (`TauCeti.nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass`).
* Such a Thom class exists with no orientation when `2 = 0` in `K`, as for `K = ZMod 2`
  (`TauCeti.nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_two_eq_zero`),
  and for every commutative ring `K`, in particular for `ℤ`, when `V` is oriented
  (`nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_vectorBundleOrientation`).

The Thom isomorphism in cohomology holds over every commutative ring and for every module of
coefficients, so the last statement gives the integral cohomology across the level of a critical
submanifold whose negative bundle is oriented, for instance a complex vector bundle. For a
non-orientable negative bundle and a ring in which `2 ≠ 0` the cohomology of the base must be
twisted by the orientation of `V`, which this file does not treat.

The base `B` is compact, since `g` embeds the disc bundle, which contains the zero section, as a
closed subset of the compact set `{x ∈ W | s x + 2 t x ≤ 2ε}`
(`TauCeti.compactSpace_of_isClosedEmbedding_gaugeDiscBundle`); the Thom isomorphism is used over a
compact base (`TauCeti.thomEquivOfCompactSpace`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Theorem 10.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology Module
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type u} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **The relative cohomology across a Morse–Bott critical level is that of the disc-sphere pair of
the negative bundle.** Under the hypotheses of
`TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`, where `g` restricts
to a closed embedding of the disc bundle `D_ρ(V)` onto the negative disc bundle
`{x ∈ W | t x = 0, s x ≤ ε}` of the quadratic normal form `f = c - s + t`, carrying the sphere
bundle `S_ρ(V)` onto `{x ∈ W | t x = 0, s x = ε}`, the map of pairs
`(D_ρ(V), S_ρ(V)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induced by `g` is an isomorphism on relative
singular cohomology, with arbitrary coefficients, in every degree. -/
theorem exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle
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
      ∀ {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
        (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ),
        IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevel_union_negativeDiscBundle_deformation hfs hW hs ht hs₀ ht₀
    hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit
  exact exists_isIso_singularCohomologyMap_of_homotopyRel_attach_discBundle hρ
    (sublevel_mono f (by linarith)) (isClosed_le hfs.continuous continuous_const) hg hgD
    (fun x hx ↦ (apply_le_of_mem_negativeDiscBundle hf hs₀ hx).trans (by linarith))
    (fun v hv ↦ apply_le_sub_iff_mem_gaugeSphereBundle hf (injOn_iff_injective.2 hg.injective) hgD
      hgS hv) r G

/-- **The relative cohomology across a Morse–Bott critical level is that of the Thom pair of the
negative bundle.** Under the hypotheses of
`TauCeti.exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle`, the relative
singular cohomology `Hⁿ({f ≤ c + ε}, {f ≤ c - ε})` is isomorphic to the relative cohomology
`Hⁿ(V, V₀)` of the Thom pair of `V`, `V₀` the complement of the zero section, with arbitrary
coefficients. -/
theorem nonempty_singularCohomology_sublevelPair_iso_thomPair
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
    {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularCohomology
        R k N n ≅ (thomPair F V).singularCohomology R k N n) := by
  obtain ⟨ψ, -, hψ⟩ := exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle hfs
    hW hs ht hs₀ ht₀ hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS
  have := hψ R k N n
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R k N n
  exact ⟨asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ n) ≪≫
    (asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (gaugeDiscSpherePairMap hρ) n)).symm⟩

/-- **Across a Morse–Bott level the relative cohomology is the shifted cohomology of the critical
submanifold.** Under the hypotheses of
`TauCeti.exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle`, where the
negative disc bundle of the quadratic normal form `f = c - s + t` is parametrized by the disc
bundle of a real vector bundle `V → B` of rank `r`, let `u` be a Thom class of `V` with
coefficients in a commutative ring `K`. Then
`Hᵖ⁺ʳ({f ≤ c + ε}, {f ≤ c - ε}; N) ≅ Hᵖ(B; N)` for every `K`-module `N` and every degree `p`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass
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
    {K : Type u} [CommRing K]
    {u : (thomPair F V).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F V u) (N : ModuleCat.{u} K) (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularCohomology
        (ModuleCat.of K K) K N (p + finrank ℝ F) ≅
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K N p) := by
  obtain ⟨e⟩ := nonempty_singularCohomology_sublevelPair_iso_thomPair hfs hW hs ht hs₀ ht₀ hf hdir
    φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS (ModuleCat.of K K) K N (p + finrank ℝ F)
  have := compactSpace_of_isClosedEmbedding_gaugeDiscBundle hε.le hK hρ hg hgD
  exact ⟨e ≪≫ (thomEquivOfCompactSpace F V N p _ rfl u hu).toModuleIso.symm⟩

variable [FiniteDimensional ℝ F]

/-- **Across a Morse–Bott level the relative cohomology in characteristic two is the shifted
cohomology of the critical submanifold, with no orientation.** Under the hypotheses of
`TauCeti.exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle`, where the
negative disc bundle of the quadratic normal form `f = c - s + t` is parametrized by the disc
bundle of a real vector bundle `V → B` of rank `r`, let `K` be a commutative ring in which
`2 = 0`, such as `ZMod 2`. Then `Hᵖ⁺ʳ({f ≤ c + ε}, {f ≤ c - ε}; N) ≅ Hᵖ(B; N)` for every
`K`-module `N` and every degree `p`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_two_eq_zero
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
    (K : Type u) [CommRing K] (h2 : (2 : K) = 0) (N : ModuleCat.{u} K)
    (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularCohomology
        (ModuleCat.of K K) K N (p + finrank ℝ F) ≅
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K N p) :=
  let ⟨_, hu⟩ := exists_isThomClass_of_two_eq_zero (F := F) (E := V) K h2
  nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass hfs hW hs ht hs₀
    ht₀ hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS hu N p

/-- **Across a Morse–Bott level with oriented negative bundle the relative cohomology is the
shifted cohomology of the critical submanifold.** Under the hypotheses of
`TauCeti.exists_isIso_singularCohomologyMap_sublevelPair_of_negativeDiscBundle`, where the
negative disc bundle of the quadratic normal form `f = c - s + t` is parametrized by the disc
bundle of an oriented real vector bundle `V → B` of rank `r`, for every commutative ring `K`,
for instance `ℤ`, `Hᵖ⁺ʳ({f ≤ c + ε}, {f ≤ c - ε}; N) ≅ Hᵖ(B; N)` for every `K`-module `N` and every
degree `p`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_vectorBundleOrientation
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
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F V ι) (K : Type u) [CommRing K] (N : ModuleCat.{u} K) (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularCohomology
        (ModuleCat.of K K) K N (p + finrank ℝ F) ≅
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K N p) :=
  let ⟨_, hu⟩ := o.exists_isThomClass hι K
  nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass hfs hW hs ht hs₀
    ht₀ hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS hu N p

end TauCeti
