/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Topology.VectorBundle.Attachment

/-!
# Relative homology across a Morse–Bott critical level

Near a nondegenerate critical submanifold of index `λ` with critical value `c`, a Morse–Bott
function has the normal form `f = c - s + t` on a tube `W`, where `s = ‖u‖²` and `t = ‖v‖²` are
the squared norms of the negative and positive components of a normal vector. Crossing the level
attaches the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}` to the lower sublevel
`M_{c-ε} = {f ≤ c - ε}`, up to a strong deformation retraction of `M_{c+ε}`
(`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`).

This file reads off the relative homology of the sublevel pair `(M_{c+ε}, M_{c-ε})`
(`TauCeti.sublevelPair`). Suppose that the negative disc bundle is parametrized by the unit disc
bundle `D(V)` of a real vector bundle `V → B`, for instance the negative normal bundle with a
fibre metric: a map `g` restricting to a closed embedding of `D(V)` onto the negative disc bundle,
and of the unit sphere bundle `S(V)` onto its boundary `{t = 0, s = ε}`. Then `g` induces a map
of pairs `(D(V), S(V)) ⟶ (M_{c+ε}, M_{c-ε})` which is an isomorphism on relative singular homology
in every degree
(`TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`), so
`Hₙ(M_{c+ε}, M_{c-ε})` is the relative homology `Hₙ(V, V₀)` of the Thom pair of `V`
(`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`). The Thom isomorphism, which this
file does not use, identifies the homology of the Thom pair with the homology of the base `B`,
the critical submanifold, shifted by the rank `λ` of `V` and with coefficients twisted by the
orientation of `V`. For an isolated nondegenerate critical point the base is a point, and the Thom
pair is the pair `(ℝ^λ, ℝ^λ ∖ 0)` of Milnor's attachment of a `λ`-cell.

## Main results

* `TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`: the parametrization
  of the negative disc bundle induces isomorphisms `Hₙ(D(V), S(V)) ≅ Hₙ(M_{c+ε}, M_{c-ε})`.
* `TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`: the relative homology across the
  critical level is that of the Thom pair, `Hₙ(M_{c+ε}, M_{c-ε}) ≅ Hₙ(V, V₀)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
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

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type u} [∀ b, NormedAddCommGroup (V b)] [∀ b, NormedSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {g : TotalSpace F V → M}

/-- **The relative homology across a Morse–Bott critical level is that of the disc-sphere pair of
the negative bundle.** Let `f` be smooth, with the quadratic normal form `f = c - s + t` on a tube
`W` and the scaling `φ` of the positive directions of
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`, whose hypotheses are repeated here.
Let `V → B` be a real vector bundle whose fibre norm is continuous on the total space, and let `g`
restrict to a closed embedding of the unit disc bundle `D(V)` onto the negative disc bundle
`{x ∈ W | t x = 0, s x ≤ ε}`, carrying the unit sphere bundle `S(V)` onto
`{x ∈ W | t x = 0, s x = ε}`. Then `g` induces a map of pairs
`(D(V), S(V)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` which is an isomorphism on relative singular homology,
with coefficients in any abelian category with coproducts, in every degree. -/
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
    (hnorm : Continuous fun v : TotalSpace F V ↦ ‖v.2‖)
    (hg : IsClosedEmbedding ((discBundle F V).domRestrict g))
    (hgD : g '' discBundle F V = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' sphereBundle F V = {x | x ∈ W ∧ t x = 0 ∧ s x = ε}) :
    ∃ ψ : discSpherePair F V ⟶ sublevelPair f (a := c - ε) (b := c + ε) (by linarith),
      (∀ v : discBundle F V, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      ∀ {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ),
        IsIso (TopPair.singularHomologyMap ψ R n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevel_union_negativeDiscBundle_deformation hfs hW hs ht hs₀ ht₀
    hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit
  refine exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle hnorm
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
    · obtain ⟨w, hw, hwv⟩ : g v ∈ g '' sphereBundle F V := hgS ▸ ⟨hxW, htx, by linarith⟩
      obtain rfl : w = v :=
        congrArg Subtype.val (@hg.injective ⟨w, sphereBundle_subset_discBundle F V hw⟩ ⟨v, hv⟩ hwv)
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
    (hnorm : Continuous fun v : TotalSpace F V ↦ ‖v.2‖)
    (hg : IsClosedEmbedding ((discBundle F V).domRestrict g))
    (hgD : g '' discBundle F V = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' sphereBundle F V = {x | x ∈ W ∧ t x = 0 ∧ s x = ε})
    {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n ≅
      (thomPair F V).singularHomology R n) := by
  obtain ⟨ψ, -, hψ⟩ := exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle hfs hW
    hs ht hs₀ ht₀ hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hnorm hg hgD hgS
  have := hψ R n
  have := isIso_singularHomologyMap_discSpherePairMap F V hnorm R n
  exact ⟨(asIso (TopPair.singularHomologyMap ψ R n)).symm ≪≫
    asIso (TopPair.singularHomologyMap (discSpherePairMap F V) R n)⟩

end TauCeti
