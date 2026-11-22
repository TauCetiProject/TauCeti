/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Homology
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
public import TauCeti.Topology.VectorBundle.Thom.TwistedHomology

/-!
# The shifted homology of the critical submanifold across a Morse–Bott level

Let `f` be a smooth function on a boundaryless manifold `M`, in the quadratic normal form
`f = c - s + t` on a tube `W` around a critical submanifold on the level `c`, and suppose that the
negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}` is parametrized by the disc bundle `D_ρ(V)` of a
real vector bundle `V → B` of rank `r`, as in
`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`. That theorem identifies the
relative homology `Hₙ(M_{c+ε}, M_{c-ε})` of the sublevels `M_t = {f ≤ t}` with the homology
`Hₙ(V, V₀)` of the Thom pair of `V`. This file applies the Thom isomorphism to it, which gives
Bott's description of the contribution of a critical submanifold of index `r`: the homology of the
base, shifted up by the index.

* Below the index the relative homology vanishes: `Hₙ(M_{c+ε}, M_{c-ε}) = 0` for `n < r`, with
  coefficients in any abelian category with coproducts and exact filtered colimits
  (`TauCeti.isZero_singularHomology_sublevelPair_of_lt_finrank`).
* For a field `K` and a Thom class of `V` with coefficients in `K`,
  `Hₚ₊ᵣ(M_{c+ε}, M_{c-ε}; K) ≅ Hₚ(B; K)` in every degree `p`
  (`TauCeti.nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass`).
* Such a Thom class exists with no orientation when `1` is the only unit of `K`, as for
  `K = ZMod 2`
  (`TauCeti.nonempty_singularHomology_sublevelPair_iso_singularHomology_of_subsingleton_units`),
  and for every field when `V` is oriented
  (`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_vectorBundleOrientation`).
* For a non-orientable negative bundle the shifted homology of the base must be taken with
  coefficients twisted by the orientation local system `o(V)`: if `2` is invertible in a
  commutative ring `K`, for instance `K = ℚ`, then `Hₚ₊ᵣ(M_{c+ε}, M_{c-ε}; K) ≃ Hₚ(B; o(V) ⊗ K)`
  with no orientation of `V`
  (`TauCeti.nonempty_singularHomology_sublevelPair_linearEquiv_twistedHomology`).

The homology Thom isomorphisms used here (`TauCeti.homologyThomIso` and
`TauCeti.thomPairSingularHomologyLinearEquivTwistedHomology`) hold in every rank and over any
base, so neither the rank nor compactness of `B` is restricted.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Theorem 10.4.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Set Topology Module
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : B → Type u} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **Across a Morse–Bott level the relative homology vanishes below the index.** In the setting
of `TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`, where the negative disc bundle of
the quadratic normal form `f = c - s + t` is parametrized by the disc bundle of a real vector
bundle `V → B` of rank `r`, the relative homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε})` is zero for
`n < r`, with coefficients in any abelian category with coproducts and exact filtered colimits. -/
theorem isZero_singularHomology_sublevelPair_of_lt_finrank
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
    {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C]
    [HasFilteredColimitsOfSize.{u, u} C] [AB5OfSize.{u, u} C] (R : C) {n : ℕ}
    (hn : n < finrank ℝ F) :
    IsZero ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n) :=
  let ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_thomPair hfs hW hs ht hs₀ ht₀ hf hdir φ
    hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS R n
  (isZero_singularHomology_thomPair R hn).of_iso e

omit [FiniteDimensional ℝ F] in
/-- **Across a Morse–Bott level the relative homology is the shifted homology of the critical
submanifold.** In the setting of `TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`,
let the negative disc bundle of the quadratic normal form `f = c - s + t` be parametrized by the
disc bundle of a real vector bundle `V → B` of rank `r`, and let `u` be a Thom class of `V`
with coefficients in a field `K`. Then `H_{p + r}({f ≤ c + ε}, {f ≤ c - ε}; K) ≅ Hₚ(B; K)` for
every degree `p`. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass
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
    {K : Type u} [Field K]
    {u : (thomPair F V).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F V u) (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology
        (ModuleCat.of K K) (finrank ℝ F + p) ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of B)) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_thomPair hfs hW hs ht hs₀ ht₀ hf hdir φ
    hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS (ModuleCat.of K K) (finrank ℝ F + p)
  exact ⟨e ≪≫ homologyThomIso F V p _ rfl u hu⟩

/-- **Across a Morse–Bott level the relative homology mod `2` is the shifted homology of the
critical submanifold, with no orientation.** In the setting of
`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`, let the negative disc bundle of the
quadratic normal form `f = c - s + t` be parametrized by the disc bundle of a real vector bundle
`V → B` of rank `r`, and let `K` be a field whose only unit is `1`, such as `ZMod 2`. Then
`H_{p + r}({f ≤ c + ε}, {f ≤ c - ε}; K) ≅ Hₚ(B; K)` for every degree `p`. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_of_subsingleton_units
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
    (K : Type u) [Field K] [Subsingleton Kˣ] (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology
        (ModuleCat.of K K) (finrank ℝ F + p) ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B)) :=
  let ⟨_, hu, _⟩ := existsUnique_isThomClass_of_subsingleton_units (F := F) (E := V) K
  nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass hfs hW hs ht hs₀ ht₀
    hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS hu p

/-- **Across a Morse–Bott level with oriented negative bundle the relative homology is the shifted
homology of the critical submanifold.** In the setting of
`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`, let the negative disc bundle of the
quadratic normal form `f = c - s + t` be parametrized by the disc bundle of an oriented real vector
bundle `V → B` of rank `r`. Then
`H_{p + r}({f ≤ c + ε}, {f ≤ c - ε}; K) ≅ Hₚ(B; K)` for every field `K`, for instance `ℚ`, and
every degree `p`. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_of_vectorBundleOrientation
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
    {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ F) (o : VectorBundleOrientation F V ι) (K : Type u) [Field K]
    (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology
        (ModuleCat.of K K) (finrank ℝ F + p) ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B)) :=
  let ⟨_, hu⟩ := o.exists_isThomClass hι K
  nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass hfs hW hs ht hs₀ ht₀
    hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS hu p

/-- **Across a Morse–Bott level the relative homology is the shifted homology of the critical
submanifold with orientation-twisted coefficients.** In the setting of
`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`, let the negative disc bundle of the
quadratic normal form `f = c - s + t` be parametrized by the disc bundle of a real vector bundle
`V → B` of rank `r`, not necessarily orientable, and let `K` be a commutative ring in which `2` is
invertible, for instance `ℚ`. Then `H_{p + r}({f ≤ c + ε}, {f ≤ c - ε}; K) ≃ Hₚ(B; o(V) ⊗ K)` for
every degree `p`, where `o(V)` is the orientation local system of `V`. -/
theorem nonempty_singularHomology_sublevelPair_linearEquiv_twistedHomology
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
    (K : Type u) [CommRing K] [Invertible (2 : K)] (p : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology
        (C := ModuleCat.{u} K) (ModuleCat.of K K) (finrank ℝ F + p) ≃ₗ[K]
      LocalCoefficientSystem.twistedHomology.{u, u, u}
        (VectorBundleOrientationCover.signLocalSystem F V K (Fintype.card_fin (finrank ℝ F)))
        p) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_thomPair hfs hW hs ht hs₀ ht₀ hf hdir φ
    hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS (ModuleCat.of K K) (finrank ℝ F + p)
  -- The twisted Thom isomorphism is normalized by a generator of `Hʳ(F, F ∖ {0}; K)` and an
  -- orientation of `F`; any choice will do here.
  obtain ⟨u, hu⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (mem_univ 0)
  exact ⟨e.toLinearEquiv.trans (thomPairSingularHomologyLinearEquivTwistedHomology
    (Fintype.card_fin _) (Module.finBasis ℝ F).orientation hu rfl)⟩

end TauCeti
