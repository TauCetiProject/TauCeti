/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Topology.Maps.Strict.Basic
public import TauCeti.RingTheory.Huber.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.Topology.Algebra.GroupCompletion

/-!
# Glueing squares and glueing data over complete Tate rings

Kedlaya and Liu abstract Kiehl's descent of finite projective modules across two-piece rational
covers into the notion of a *glueing square* of complete Hausdorff Tate rings (`R → R₁, R₂ → R₁₂`)
together with *glueing data* of modules (`M₁, M₂, M₁₂` with `R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂`).

In Definition 2.7.3 of *Relative p-adic Hodge theory: Foundations*, condition (c) asks for the
map of Berkovich spectra `ℳ(R₁ ⊕ R₂) → ℳ(R)` to be surjective. The proof of Proposition 2.7.5
uses this hypothesis through its algebraic consequence: every maximal ideal of `R` is the
contraction of a prime ideal of `R₁ × R₂` (so a finitely generated submodule `N ≤ M` whose
images in `R₁ ⊗_R M` and `R₂ ⊗_R M` generate those base changes cannot lie inside `𝔪 M` for any
maximal ideal `𝔪` of `R`, hence equals `M` by Nakayama's lemma). Following that proof,
`TauCeti.Huber.GlueingSquare` records the prime-contraction property directly, avoiding any
auxiliary Berkovich spectrum construction while remaining valid for arbitrary adic spaces where
the adic spectrum replaces `ℳ`.

Over complete Hausdorff Tate rings, topological strictness of the sequence
`0 → R → R₁ × R₂ → R₁₂ → 0` is automatic from algebraic exactness and continuity via Henkel's open
mapping theorem (`TauCeti.Huber.GlueingSquare.of_exact`): the image of `R → R₁ × R₂` equals the
kernel of `(r₁, r₂) ↦ r₁ - r₂`, which is closed because `R₁₂` is Hausdorff, and the surjective
difference map `R₁ × R₂ → R₁₂` is an open quotient map onto the completely metrisable Baire target
`R₁₂`.

## Main definitions

* `TauCeti.Huber.GlueingSquare R R₁ R₂ R₁₂`: a glueing square of topological rings.
* `TauCeti.Huber.GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂`: modules `M₁`, `M₂`, `M₁₂` equipped with
  `R₁₂`-linear isomorphisms `ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂`.
* `TauCeti.Huber.GlueingDatum.sections R D`: the `R`-submodule of `(m₁, m₂) ∈ M₁ × M₂` satisfying
  the cocycle condition `D.ψ₁ (1 ⊗ₜ m₁) = D.ψ₂ (1 ⊗ₜ m₂)`.
* `TauCeti.Huber.GlueingDatum.ofModule R₁ R₂ R₁₂ R N`: the canonical glueing datum attached to an
  `R`-module `N`.
* `TauCeti.Huber.GlueingDatum.toSectionsOfModule` and
  `TauCeti.Huber.GlueingDatum.equivSectionsOfModule`: the canonical map
  `N →ₗ[R] (ofModule … N).sections R`, upgraded to an `R`-linear isomorphism whenever
  `0 → R → R₁ × R₂ → R₁₂` is exact and `N` is flat (in particular, projective).

## Main results

* `TauCeti.Huber.GlueingSquare.of_exact`: upgrades algebraic exactness, surjectivity of the
  difference map, dense range, and maximal-ideal lifting to a full `GlueingSquare`, supplying
  `isInducing` and `isStrictMap_sub` from the open mapping theorem over `R`.
* `TauCeti.Huber.GlueingSquare.congr`: transports a `GlueingSquare` across homeomorphic `R`-algebra
  isomorphisms on the three cover pieces.
* `TauCeti.Huber.GlueingSquare.symm`: swapping `R₁` and `R₂` preserves `GlueingSquare` as soon as
  `algebraMap R₁ R₁₂` also has dense range.
* `TauCeti.Huber.GlueingSquare.id` and `TauCeti.Huber.GlueingSquare.of_subsingleton_right`:
  identity and degenerate glueing squares.
* `TauCeti.Huber.GlueingSquare.equivSectionsOfModule`: for a flat (hence any projective) `R`-module
  `N` on a glueing square, `N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.7, Definition 2.7.3 and Proposition 2.7.5.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology UniformSpace Uniformity TensorProduct

namespace TauCeti.Huber

section Basic

variable (R R₁ R₂ R₁₂ : Type*) [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [TopologicalSpace R] [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂]

/-- A *glueing square* of topological rings `R → R₁, R₂ → R₁₂` (Kedlaya–Liu, Definition 2.7.3,
with condition (c) phrased via its prime-ideal contraction consequence used in Proposition 2.7.5):
continuous algebra maps making `0 → R → R₁ × R₂ → R₁₂ → 0`, `(r₁, r₂) ↦ r₁ - r₂`, topologically
strict exact, with `algebraMap R₂ R₁₂` of dense range and every maximal ideal of `R` the
contraction of a prime ideal of `R₁ × R₂`. -/
structure GlueingSquare : Prop where
  /-- Continuity of `R → R₁`. -/
  continuous_algebraMap₁ : Continuous (algebraMap R R₁)
  /-- Continuity of `R → R₂`. -/
  continuous_algebraMap₂ : Continuous (algebraMap R R₂)
  /-- Continuity of `R₁ → R₁₂`. -/
  continuous_algebraMap₁₂ : Continuous (algebraMap R₁ R₁₂)
  /-- Continuity of `R₂ → R₁₂`. -/
  continuous_algebraMap₂₁₂ : Continuous (algebraMap R₂ R₁₂)
  /-- Injectivity of `R → R₁ × R₂`. -/
  injective : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)
  /-- Exactness in the middle of `0 → R → R₁ × R₂ → R₁₂`. -/
  exact_sub : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2
  /-- Surjectivity of `(r₁, r₂) ↦ r₁ - r₂`. -/
  surjective_sub :
    Function.Surjective fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2
  /-- The inclusion `R → R₁ × R₂` induces the topology of `R`. -/
  isInducing : Topology.IsInducing fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)
  /-- The difference map `R₁ × R₂ → R₁₂` is topologically strict. -/
  isStrictMap_sub :
    Topology.IsStrictMap fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2
  /-- `algebraMap R₂ R₁₂` has dense range in `R₁₂`. -/
  denseRange : DenseRange (algebraMap R₂ R₁₂)
  /-- Every maximal ideal of `R` is the contraction of a prime ideal of `R₁ × R₂`. -/
  exists_prime_comap_eq : ∀ m : Ideal R, m.IsMaximal → ∃ p : Ideal (R₁ × R₂), p.IsPrime ∧
    p.comap ((algebraMap R R₁).prod (algebraMap R R₂)) = m

variable {R R₁ R₂ R₁₂}

/-- In a glueing square, the diagonal inclusion `R → R₁ × R₂` is a topological embedding. -/
theorem GlueingSquare.isEmbedding (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsEmbedding fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r) :=
  ⟨h.isInducing, h.injective⟩

/-- In a glueing square, the difference map `R₁ × R₂ → R₁₂` is a quotient map. -/
theorem GlueingSquare.isQuotientMap_sub (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsQuotientMap fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 :=
  Topology.isQuotientMap_iff_isStrictMap_surjective.mpr ⟨h.isStrictMap_sub, h.surjective_sub⟩

/-- Swapping `R₁` and `R₂` in a glueing square yields a glueing square as soon as
`algebraMap R₁ R₁₂` also has dense range. Note that `DenseRange (algebraMap R₁ R₁₂)` is genuinely
an additional hypothesis: for a simple Laurent cover `R⟨f⟩, R⟨1/f⟩ → R⟨f, 1/f⟩`, `R⟨1/f⟩` has
dense image in `R⟨f, 1/f⟩` because `1/f` is already present in `R⟨1/f⟩`, whereas `R⟨f⟩` need not
have dense image when `f` is not invertible in `R⟨f⟩`. -/
theorem GlueingSquare.symm [ContinuousNeg R₁₂] (h : GlueingSquare R R₁ R₂ R₁₂)
    (hd₁ : DenseRange (algebraMap R₁ R₁₂)) :
    GlueingSquare R R₂ R₁ R₁₂ where
  continuous_algebraMap₁ := h.continuous_algebraMap₂
  continuous_algebraMap₂ := h.continuous_algebraMap₁
  continuous_algebraMap₁₂ := h.continuous_algebraMap₂₁₂
  continuous_algebraMap₂₁₂ := h.continuous_algebraMap₁₂
  injective _ _ heq :=
    h.injective (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))
  exact_sub x := by
    rw [sub_eq_zero, eq_comm, ← sub_eq_zero, h.exact_sub (x.2, x.1)]
    exact ⟨fun ⟨r, hr⟩ ↦ ⟨r, Prod.ext (congrArg Prod.snd hr) (congrArg Prod.fst hr)⟩,
      fun ⟨r, hr⟩ ↦ ⟨r, Prod.ext (congrArg Prod.snd hr) (congrArg Prod.fst hr)⟩⟩
  surjective_sub y := by
    obtain ⟨⟨a, b⟩, hab⟩ := h.surjective_sub (-y)
    refine ⟨(b, a), ?_⟩
    dsimp only at hab ⊢
    rw [← neg_sub, hab, neg_neg]
  isInducing := (Homeomorph.prodComm R₁ R₂).isInducing.comp h.isInducing
  isStrictMap_sub := by
    have hcomp : (fun x : R₂ × R₁ ↦ algebraMap R₂ R₁₂ x.1 - algebraMap R₁ R₁₂ x.2) =
        (Homeomorph.neg R₁₂) ∘
          (fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) ∘
            (Homeomorph.prodComm R₂ R₁) := by
      ext ⟨x₂, x₁⟩
      exact (neg_sub (algebraMap R₁ R₁₂ x₁) (algebraMap R₂ R₁₂ x₂)).symm
    rw [hcomp, Homeomorph.comp_isStrictMap_iff, Homeomorph.isStrictMap_comp_iff]
    exact h.isStrictMap_sub
  denseRange := hd₁
  exists_prime_comap_eq m hm := by
    obtain ⟨p, hp, hpm⟩ := h.exists_prime_comap_eq m hm
    let swap : R₂ × R₁ →+* R₁ × R₂ := (RingHom.snd R₂ R₁).prod (RingHom.fst R₂ R₁)
    refine ⟨p.comap swap, hp.comap swap, ?_⟩
    rw [Ideal.comap_comap]
    exact hpm

omit [TopologicalSpace R] [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂] in
private theorem exact_sub_congr {L₁ L₂ L₁₂ : Type*}
    [CommRing L₁] [CommRing L₂] [CommRing L₁₂] [Algebra R L₁] [Algebra R L₂]
    [Algebra L₁ L₁₂] [Algebra L₂ L₁₂]
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R L₁ r, algebraMap R L₂ r))
      fun y : L₁ × L₂ ↦ algebraMap L₁ L₁₂ y.1 - algebraMap L₂ L₁₂ y.2)
    (e₁ : L₁ ≃ₐ[R] R₁) (e₂ : L₂ ≃ₐ[R] R₂) (e₁₂ : L₁₂ ≃+* R₁₂)
    (hcomp₁ : ∀ x : L₁, e₁₂ (algebraMap L₁ L₁₂ x) = algebraMap R₁ R₁₂ (e₁ x))
    (hcomp₂ : ∀ x : L₂, e₁₂ (algebraMap L₂ L₁₂ x) = algebraMap R₂ R₁₂ (e₂ x)) :
    Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 := fun x ↦ by
  have hx : algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 =
      e₁₂ (algebraMap L₁ L₁₂ (e₁.symm x.1) - algebraMap L₂ L₁₂ (e₂.symm x.2)) := by
    simp [map_sub, hcomp₁, hcomp₂]
  dsimp only
  rw [hx, map_eq_zero_iff e₁₂ e₁₂.injective, hexact (e₁.symm x.1, e₂.symm x.2)]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩⟩
  · exact Prod.ext (by simpa using congrArg e₁ (congrArg Prod.fst hr))
      (by simpa using congrArg e₂ (congrArg Prod.snd hr))
  · exact Prod.ext (by simpa using congrArg e₁.symm (congrArg Prod.fst hr))
      (by simpa using congrArg e₂.symm (congrArg Prod.snd hr))

/-- Transport a `GlueingSquare` across homeomorphic `R`-algebra equivalences on `R₁`, `R₂`, and
`R₁₂` intertwining the transition homomorphisms to the overlap ring. -/
theorem GlueingSquare.congr [Algebra R R₁₂] {L₁ L₂ L₁₂ : Type*}
    [CommRing L₁] [CommRing L₂] [CommRing L₁₂]
    [TopologicalSpace L₁] [TopologicalSpace L₂] [TopologicalSpace L₁₂]
    [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₁₂] [Algebra L₂ L₁₂] [Algebra R L₁₂]
    (h : GlueingSquare R L₁ L₂ L₁₂)
    (e₁ : L₁ ≃ₐ[R] R₁) (he₁ : Continuous e₁) (he₁_symm : Continuous e₁.symm)
    (e₂ : L₂ ≃ₐ[R] R₂) (he₂ : Continuous e₂) (he₂_symm : Continuous e₂.symm)
    (e₁₂ : L₁₂ ≃ₐ[R] R₁₂) (he₁₂ : Continuous e₁₂) (he₁₂_symm : Continuous e₁₂.symm)
    (hcomp₁ : ∀ x : L₁, e₁₂ (algebraMap L₁ L₁₂ x) = algebraMap R₁ R₁₂ (e₁ x))
    (hcomp₂ : ∀ x : L₂, e₁₂ (algebraMap L₂ L₁₂ x) = algebraMap R₂ R₁₂ (e₂ x)) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  let H₁ : L₁ ≃ₜ R₁ := ⟨e₁.toEquiv, he₁, he₁_symm⟩
  let H₂ : L₂ ≃ₜ R₂ := ⟨e₂.toEquiv, he₂, he₂_symm⟩
  let H₁₂ : L₁₂ ≃ₜ R₁₂ := ⟨e₁₂.toEquiv, he₁₂, he₁₂_symm⟩
  have hι : (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)) =
      (H₁.prodCongr H₂) ∘ fun r : R ↦ (algebraMap R L₁ r, algebraMap R L₂ r) := by
    ext r <;> simp [H₁, H₂]
  have hδ : (fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) =
      H₁₂ ∘ (fun y : L₁ × L₂ ↦ algebraMap L₁ L₁₂ y.1 - algebraMap L₂ L₁₂ y.2) ∘
        (H₁.prodCongr H₂).symm := by
    ext ⟨x₁, x₂⟩; simp [H₁, H₂, H₁₂, map_sub, hcomp₁, hcomp₂]
  have hmap₁ : (algebraMap R₁ R₁₂ : R₁ → R₁₂) = H₁₂ ∘ algebraMap L₁ L₁₂ ∘ H₁.symm := by
    ext x; simp [H₁, H₁₂, hcomp₁]
  have hmap₂ : (algebraMap R₂ R₁₂ : R₂ → R₁₂) = H₁₂ ∘ algebraMap L₂ L₁₂ ∘ H₂.symm := by
    ext x; simp [H₂, H₁₂, hcomp₂]
  refine
    { continuous_algebraMap₁ := (funext fun r ↦ (e₁.commutes r).symm) ▸
        he₁.comp h.continuous_algebraMap₁
      continuous_algebraMap₂ := (funext fun r ↦ (e₂.commutes r).symm) ▸
        he₂.comp h.continuous_algebraMap₂
      continuous_algebraMap₁₂ := hmap₁ ▸ he₁₂.comp (h.continuous_algebraMap₁₂.comp he₁_symm)
      continuous_algebraMap₂₁₂ := hmap₂ ▸ he₁₂.comp (h.continuous_algebraMap₂₁₂.comp he₂_symm)
      injective := hι ▸ (H₁.prodCongr H₂).injective.comp h.injective
      exact_sub := exact_sub_congr h.exact_sub e₁ e₂ e₁₂.toRingEquiv hcomp₁ hcomp₂
      surjective_sub :=
        hδ ▸ H₁₂.surjective.comp (h.surjective_sub.comp (H₁.prodCongr H₂).symm.surjective)
      isInducing := hι ▸ (H₁.prodCongr H₂).isInducing.comp h.isInducing
      isStrictMap_sub := by
        rw [hδ, Homeomorph.comp_isStrictMap_iff, Homeomorph.isStrictMap_comp_iff]
        exact h.isStrictMap_sub
      denseRange := hmap₂ ▸ H₁₂.surjective.denseRange.comp
        (h.denseRange.comp H₂.symm.surjective.denseRange h.continuous_algebraMap₂₁₂) he₁₂
      exists_prime_comap_eq := fun m hm ↦ by
        obtain ⟨p, hp, hpm⟩ := h.exists_prime_comap_eq m hm
        let ψ := RingHom.prodMap e₁.symm.toRingHom e₂.symm.toRingHom
        refine ⟨p.comap ψ, hp.comap ψ, ?_⟩
        rw [Ideal.comap_comap]
        convert hpm using 2
        ext r <;> simp [ψ] }

end Basic

section OfExact

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R]
  [UniformSpace R₁] [IsUniformAddGroup R₁] [IsTopologicalRing R₁] [IsHuberRing R₁]
  [CompleteSpace R₁] [T0Space R₁]
  [UniformSpace R₂] [IsUniformAddGroup R₂] [IsTopologicalRing R₂] [IsHuberRing R₂]
  [CompleteSpace R₂] [T0Space R₂]
  [UniformSpace R₁₂] [IsUniformAddGroup R₁₂] [IsTopologicalRing R₁₂] [IsHuberRing R₁₂]
  [CompleteSpace R₁₂] [T2Space R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]

/-- Smart constructor for `GlueingSquare`: over a complete Tate ring `R` with complete Hausdorff
Huber cover rings `R₁`, `R₂`, `R₁₂`, both `isInducing` and `isStrictMap_sub` follow automatically
from continuity, algebraic exactness, and surjectivity of the difference map by Henkel's open
mapping theorem (`LinearMap.isQuotientMap_of_isTateRing` and
`LinearMap.isStrictMap_of_isClosed_range_of_isTateRing`). -/
theorem GlueingSquare.of_exact
    (hc₁ : Continuous (algebraMap R R₁))
    (hc₂ : Continuous (algebraMap R R₂))
    (hc₁₂ : Continuous (algebraMap R₁ R₁₂))
    (hc₂₁₂ : Continuous (algebraMap R₂ R₁₂))
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2)
    (hsurj : Function.Surjective fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2)
    (hdense : DenseRange (algebraMap R₂ R₁₂))
    (hprime : ∀ m : Ideal R, m.IsMaximal → ∃ p : Ideal (R₁ × R₂), p.IsPrime ∧
      p.comap ((algebraMap R R₁).prod (algebraMap R R₂)) = m) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  have : ContinuousSMul R R₁ := continuousSMul_of_algebraMap R R₁ hc₁
  have : ContinuousSMul R R₂ := continuousSMul_of_algebraMap R R₂ hc₂
  have hcR₁₂ : Continuous (algebraMap R R₁₂) := by
    have hcomp : (algebraMap R R₁₂ : R → R₁₂) = algebraMap R₁ R₁₂ ∘ algebraMap R R₁ :=
      funext (IsScalarTower.algebraMap_apply R R₁ R₁₂)
    exact hcomp ▸ hc₁₂.comp hc₁
  have : ContinuousSMul R R₁₂ := continuousSMul_of_algebraMap R R₁₂ hcR₁₂
  have : (𝓤 R₁).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 R₂).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 R₁₂).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓝 (0 : R₁ × R₂)).IsCountablyGenerated := by
    rw [Prod.zero_eq_mk, nhds_prod_eq]
    infer_instance
  let ι : R →ₗ[R] R₁ × R₂ := (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)
  let δ : (R₁ × R₂) →ₗ[R] R₁₂ :=
    (IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
      (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂)
  have hι_cont : Continuous ι := hc₁.prodMk hc₂
  have hδ_cont : Continuous δ :=
    (hc₁₂.comp continuous_fst).sub (hc₂₁₂.comp continuous_snd)
  have hrange : (ι.range : Set (R₁ × R₂)) =
      {x | algebraMap R₁ R₁₂ x.1 = algebraMap R₂ R₁₂ x.2} := by
    ext x
    exact (hexact x).symm.trans sub_eq_zero
  have hclosed : IsClosed (ι.range : Set (R₁ × R₂)) := by
    rw [hrange]
    exact isClosed_eq (hc₁₂.comp continuous_fst) (hc₂₁₂.comp continuous_snd)
  have hι_strict : Topology.IsStrictMap ι :=
    ι.isStrictMap_of_isClosed_range_of_isTateRing hι_cont.continuousAt hclosed
  have hι_emb : Topology.IsEmbedding ι :=
    Topology.isEmbedding_iff_isStrictMap_injective.mpr ⟨hι_strict, hinj⟩
  have hδ_strict : Topology.IsStrictMap δ :=
    (δ.isQuotientMap_of_isTateRing hsurj hδ_cont.continuousAt).isStrictMap
  exact
    { continuous_algebraMap₁ := hc₁
      continuous_algebraMap₂ := hc₂
      continuous_algebraMap₁₂ := hc₁₂
      continuous_algebraMap₂₁₂ := hc₂₁₂
      injective := hinj
      exact_sub := hexact
      surjective_sub := hsurj
      isInducing := hι_emb.isInducing
      isStrictMap_sub := hδ_strict
      denseRange := hdense
      exists_prime_comap_eq := hprime }

/-- The identity glueing square `R → R, R → R` on any topological ring `R`. -/
theorem GlueingSquare.id (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalAddGroup R] :
    GlueingSquare R R R R where
  continuous_algebraMap₁ := continuous_id
  continuous_algebraMap₂ := continuous_id
  continuous_algebraMap₁₂ := continuous_id
  continuous_algebraMap₂₁₂ := continuous_id
  injective _ _ h := congrArg Prod.fst h
  exact_sub := fun ⟨a, b⟩ ↦ by simp [sub_eq_zero, eq_comm]
  surjective_sub y := ⟨(y, 0), by simp⟩
  isInducing := Topology.IsInducing.of_comp
    (continuous_id.prodMk continuous_id) continuous_fst Topology.IsInducing.id
  isStrictMap_sub :=
    (Topology.IsQuotientMap.of_inverse (continuous_id.prodMk continuous_const)
      (continuous_fst.sub continuous_snd) fun y : R ↦ sub_zero y).isStrictMap
  denseRange := denseRange_id
  exists_prime_comap_eq m hm := by
    have : m.IsPrime := hm.isPrime
    refine ⟨m.comap (RingHom.fst R R), Ideal.IsPrime.comap _, ?_⟩
    rw [Ideal.comap_comap]
    exact Ideal.comap_id m

/-- A degenerate glueing square `R → R, R₂ → R₁₂` in which `R₂` and `R₁₂` are subsingleton rings
(for instance when one piece of a rational cover has denominator `0`). -/
theorem GlueingSquare.of_subsingleton_right {R R₂ R₁₂ : Type*} [CommRing R] [CommRing R₂]
    [CommRing R₁₂] [TopologicalSpace R] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
    [Algebra R R₂] [Algebra R R₁₂] [Algebra R₂ R₁₂] [Subsingleton R₂] [Subsingleton R₁₂] :
    GlueingSquare R R R₂ R₁₂ where
  continuous_algebraMap₁ := continuous_id
  continuous_algebraMap₂ := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  continuous_algebraMap₁₂ := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  continuous_algebraMap₂₁₂ := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  injective _ _ h := congrArg Prod.fst h
  exact_sub := fun ⟨r, _⟩ ↦
    ⟨fun _ ↦ ⟨r, Prod.ext rfl (Subsingleton.elim _ _)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  surjective_sub _ := ⟨(0, 0), Subsingleton.elim _ _⟩
  isInducing := Topology.IsInducing.of_comp
    (continuous_id.prodMk (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _))
    continuous_fst Topology.IsInducing.id
  isStrictMap_sub :=
    (Topology.IsQuotientMap.of_inverse
      (continuous_const : Continuous fun _ : R₁₂ ↦ (0 : R × R₂))
      (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _)
      fun _ : R₁₂ ↦ Subsingleton.elim _ _).isStrictMap
  denseRange _ := subset_closure ⟨(0 : R₂), Subsingleton.elim _ _⟩
  exists_prime_comap_eq m hm := by
    have : m.IsPrime := hm.isPrime
    refine ⟨m.comap (RingHom.fst R R₂), Ideal.IsPrime.comap _, ?_⟩
    rw [Ideal.comap_comap]
    exact Ideal.comap_id m

end OfExact

/-! ### Glueing data and modules of sections -/

section GlueingDatum

variable {R₁ R₂ R₁₂ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [Algebra R₁ R₁₂] [Algebra R₂ R₁₂]
  {M₁ M₂ M₁₂ : Type*} [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂] [Module R₂ M₂]
  [AddCommGroup M₁₂] [Module R₁₂ M₁₂]

variable (R₁ R₂ R₁₂ M₁ M₂ M₁₂) in
/-- A *glueing datum* on `R₁, R₂ → R₁₂`: modules `M₁` over `R₁`, `M₂` over `R₂`, `M₁₂` over
`R₁₂`, and `R₁₂`-linear isomorphisms `ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂`
(Kedlaya–Liu, Definition 2.7.3). -/
structure GlueingDatum where
  /-- Identification `R₁₂ ⊗_{R₁} M₁ ≃ₗ[R₁₂] M₁₂`. -/
  ψ₁ : R₁₂ ⊗[R₁] M₁ ≃ₗ[R₁₂] M₁₂
  /-- Identification `R₁₂ ⊗_{R₂} M₂ ≃ₗ[R₁₂] M₂` onto `M₁₂`. -/
  ψ₂ : R₁₂ ⊗[R₂] M₂ ≃ₗ[R₁₂] M₁₂

/-- Swapping the two pieces of a glueing datum. -/
def GlueingDatum.symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    GlueingDatum R₂ R₁ R₁₂ M₂ M₁ M₁₂ where
  ψ₁ := D.ψ₂
  ψ₂ := D.ψ₁

@[simp]
theorem GlueingDatum.symm_ψ₁ (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.symm.ψ₁ = D.ψ₂ := by rfl

@[simp]
theorem GlueingDatum.symm_ψ₂ (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.symm.ψ₂ = D.ψ₁ := by rfl

section Sections

variable (R : Type*) [CommRing R] [Algebra R R₁] [Algebra R R₂]
  [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
  [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]

/-- The `R`-module of sections `{(m₁, m₂) ∈ M₁ × M₂ | ψ₁(1 ⊗ m₁) = ψ₂(1 ⊗ m₂)}` of a glueing
datum, over a base ring `R` mapping compatibly to `R₁`, `R₂`, `R₁₂`. -/
def GlueingDatum.sections (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : Submodule R (M₁ × M₂) where
  carrier := {x | D.ψ₁ (1 ⊗ₜ x.1) = D.ψ₂ (1 ⊗ₜ x.2)}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  zero_mem' := by simp
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd] at hx ⊢
    rw [← algebraMap_smul R₁ r x.1, ← algebraMap_smul R₂ r x.2, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, ← algebraMap_smul R₁₂ (algebraMap R R₁ r),
      ← algebraMap_smul R₁₂ (algebraMap R R₂ r), map_smul, map_smul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hx]

@[simp]
theorem GlueingDatum.mem_sections_iff {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
    [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {x : M₁ × M₂} :
    x ∈ D.sections R ↔ D.ψ₁ (1 ⊗ₜ x.1) = D.ψ₂ (1 ⊗ₜ x.2) := by
  rfl

/-- First projection from the module of sections to `M₁`. -/
def GlueingDatum.fst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R →ₗ[R] M₁ :=
  (LinearMap.fst R M₁ M₂).comp (D.sections R).subtype

/-- Second projection from the module of sections to `M₂`. -/
def GlueingDatum.snd (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R →ₗ[R] M₂ :=
  (LinearMap.snd R M₁ M₂).comp (D.sections R).subtype

@[simp]
theorem GlueingDatum.fst_apply {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
    [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.fst R x = x.1.1 := by rfl

@[simp]
theorem GlueingDatum.snd_apply {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
    [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.snd R x = x.1.2 := by rfl

/-- Over a subsingleton overlap module `M₁₂`, the cocycle condition is vacuous and the sections
identify with `M₁ × M₂`. -/
def GlueingDatum.sectionsEquivProdOfSubsingleton [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R ≃ₗ[R] M₁ × M₂ :=
  LinearEquiv.ofTop (D.sections R) (Submodule.eq_top_iff'.mpr fun _ ↦ Subsingleton.elim _ _)

end Sections

section OfModule

variable (R₁ R₂ R₁₂) in
/-- The canonical glueing datum `(R₁ ⊗_R N, R₂ ⊗_R N, R₁₂ ⊗_R N)` attached to an `R`-module `N`. -/
def GlueingDatum.ofModule (R : Type*) [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
    (N : Type*) [AddCommGroup N] [Module R N] :
    GlueingDatum R₁ R₂ R₁₂ (R₁ ⊗[R] N) (R₂ ⊗[R] N) (R₁₂ ⊗[R] N) where
  ψ₁ := AlgebraTensorModule.cancelBaseChange R R₁ R₁₂ R₁₂ N
  ψ₂ := AlgebraTensorModule.cancelBaseChange R R₂ R₁₂ R₁₂ N

variable {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
  [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
  {N : Type*} [AddCommGroup N] [Module R N]

@[simp]
theorem GlueingDatum.ofModule_ψ₁_tmul (r₁₂ : R₁₂) (r₁ : R₁) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₁ (r₁₂ ⊗ₜ (r₁ ⊗ₜ n)) = (r₁ • r₁₂) ⊗ₜ n :=
  AlgebraTensorModule.cancelBaseChange_tmul R R₁ R₁₂ r₁₂ n r₁

@[simp]
theorem GlueingDatum.ofModule_ψ₂_tmul (r₁₂ : R₁₂) (r₂ : R₂) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂ (r₁₂ ⊗ₜ (r₂ ⊗ₜ n)) = (r₂ • r₁₂) ⊗ₜ n :=
  AlgebraTensorModule.cancelBaseChange_tmul R R₂ R₁₂ r₁₂ n r₂

variable (R₁ R₂ R₁₂ R N) in
/-- The canonical `R`-linear comparison map `n ↦ (1 ⊗ n, 1 ⊗ n)` from an `R`-module `N` into the
sections of its associated glueing datum `GlueingDatum.ofModule`. -/
def GlueingDatum.toSectionsOfModule :
    N →ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R where
  toFun n := ⟨((1 : R₁) ⊗ₜ[R] n, (1 : R₂) ⊗ₜ[R] n), by simp⟩
  map_add' x y := by ext <;> simp [TensorProduct.tmul_add]
  map_smul' r x := by ext <;> simp [TensorProduct.tmul_smul]

@[simp]
theorem GlueingDatum.coe_toSectionsOfModule_apply (n : N) :
    (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) =
      ((1 : R₁) ⊗ₜ[R] n, (1 : R₂) ⊗ₜ[R] n) := by
  rfl

private theorem ofModule_cocycle_eq_rTensor (z : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :
    LinearMap.rTensor N
      ((IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
        (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂))
      ((TensorProduct.prodLeft R R R₁ R₂ N).symm z) =
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₁ (1 ⊗ₜ z.1) -
      (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂ (1 ⊗ₜ z.2) := by
  rcases z with ⟨z₁, z₂⟩
  dsimp only
  rw [show (z₁, z₂) = (z₁, (0 : R₂ ⊗[R] N)) + ((0 : R₁ ⊗[R] N), z₂) by simp,
    map_add, map_add, sub_eq_add_neg]
  congr 1
  · induction z₁ using TensorProduct.inductionOn with
    | tmul a n =>
      rw [show (0 : R₂ ⊗[R] N) = (0 : R₂) ⊗ₜ[R] n by simp, TensorProduct.prodLeft_symm_tmul]
      simp [Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      rw [show (x + y, (0 : R₂ ⊗[R] N)) = (x, 0) + (y, 0) by simp,
        map_add, map_add, hx, hy, TensorProduct.tmul_add, map_add]
  · induction z₂ using TensorProduct.inductionOn with
    | tmul b n =>
      rw [show (0 : R₁ ⊗[R] N) = (0 : R₁) ⊗ₜ[R] n by simp, TensorProduct.prodLeft_symm_tmul]
      simp [Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      rw [show ((0 : R₁ ⊗[R] N), x + y) = (0, x) + (0, y) by simp,
        map_add, map_add, hx, hy, TensorProduct.tmul_add, map_add, neg_add]

/-- Whenever `0 → R → R₁ × R₂ → R₁₂` is exact and `N` is a flat `R`-module, the canonical map
`GlueingDatum.toSectionsOfModule` is bijective: flat base change preserves both injectivity of
`R → R₁ × R₂` and exactness at `(R₁ × R₂) ⊗_R N`. -/
theorem GlueingDatum.bijective_toSectionsOfModule_of_flat [Module.Flat R N]
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) :
    Function.Bijective (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N) := by
  let ι : R →ₗ[R] R₁ × R₂ := (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)
  let δ : (R₁ × R₂) →ₗ[R] R₁₂ :=
    (IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
      (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂)
  let e := TensorProduct.prodLeft R R R₁ R₂ N
  have hιN_inj : Function.Injective (ι.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hinj
  have hexN : Function.Exact (ι.rTensor N) (δ.rTensor N) :=
    Module.Flat.rTensor_exact N hexact
  have hval : ∀ n : N,
      e (ι.rTensor N ((TensorProduct.lid R N).symm n)) =
        (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :=
    fun n ↦ by simp [e, ι]
  refine ⟨fun n₁ n₂ hn ↦ ?_, fun ⟨z, hz⟩ ↦ ?_⟩
  · have hsub : (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n₁ : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) =
        (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n₂ : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :=
      congrArg Subtype.val hn
    rw [← hval n₁, ← hval n₂] at hsub
    exact (TensorProduct.lid R N).symm.injective (hιN_inj (e.injective hsub))
  · have hker : δ.rTensor N (e.symm z) = 0 := by
      rw [ofModule_cocycle_eq_rTensor z, sub_eq_zero]
      exact hz
    obtain ⟨w, hw⟩ := (hexN (e.symm z)).mp hker
    refine ⟨TensorProduct.lid R N w, Subtype.ext ?_⟩
    rw [← hval, LinearEquiv.symm_apply_apply, hw, LinearEquiv.apply_symm_apply]

/-- For a flat `R`-module `N` over an exact ring diagram `0 → R → R₁ × R₂ → R₁₂`, the sections of
`GlueingDatum.ofModule R₁ R₂ R₁₂ R N` are canonically `R`-linearly isomorphic to `N`. -/
noncomputable def GlueingDatum.equivSectionsOfModule [Module.Flat R N]
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) :
    N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R :=
  LinearEquiv.ofBijective (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N)
    (GlueingDatum.bijective_toSectionsOfModule_of_flat hinj hexact)

@[simp]
theorem GlueingDatum.equivSectionsOfModule_apply [Module.Flat R N]
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) (n : N) :
    GlueingDatum.equivSectionsOfModule hinj hexact n =
      GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n := by
  rfl

end OfModule

end GlueingDatum

section GlueingSquareSections

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [TopologicalSpace R] [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]

/-- On any glueing square, a flat (in particular, any projective) `R`-module `N` is canonically
isomorphic to the sections of its induced glueing datum `GlueingDatum.ofModule R₁ R₂ R₁₂ R N`. -/
noncomputable def GlueingSquare.equivSectionsOfModule (h : GlueingSquare R R₁ R₂ R₁₂)
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R N] :
    N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R :=
  GlueingDatum.equivSectionsOfModule h.injective h.exact_sub

@[simp]
theorem GlueingSquare.equivSectionsOfModule_apply (h : GlueingSquare R R₁ R₂ R₁₂)
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R N] (n : N) :
    h.equivSectionsOfModule N n = GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n := by
  rfl

end GlueingSquareSections

end TauCeti.Huber

end
