/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Basic
public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.Glueing.Datum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.RingTheory.Huber.OpenMapping

/-!
# Glueing squares over complete Tate rings

Kedlaya and Liu abstract Kiehl's descent of finite projective modules across two-piece rational
covers into a *glueing square* of complete Hausdorff Tate rings (`R → R₁, R₂ → R₁₂`) together with
algebraic *glueing data* (`TauCeti.Huber.GlueingDatum`).

Following Kedlaya–Liu Proposition 2.7.5, `TauCeti.Huber.GlueingSquare` phrases condition (c) of
Definition 2.7.3 directly through its algebraic prime-contraction consequence (every maximal ideal
of `R` contracts from a prime ideal of `R₁ × R₂`), which applies equally to arbitrary adic spaces.
Over complete Hausdorff Tate rings, topological strictness of `0 → R → R₁ × R₂ → R₁₂ → 0` follows
automatically from algebraic exactness and continuity via Henkel's open mapping theorem
(`TauCeti.Huber.GlueingSquare.of_exact`).

## Main definitions

* `TauCeti.Huber.GlueingSquare R R₁ R₂ R₁₂`: a glueing square of topological rings.

## Main results

* `TauCeti.Huber.GlueingSquare.comp_algebraMap_eq` and
  `TauCeti.Huber.GlueingSquare.algebraMap_algebraMap`: commutativity of the square.
* `TauCeti.Huber.GlueingSquare.isOpenQuotientMap_sub`: openness of the difference quotient map
  when `R₁` and `R₂` have continuous addition.
* `TauCeti.Huber.GlueingSquare.of_exact`: upgrades algebraic exactness, surjectivity of the
  difference map, dense range, and maximal-ideal lifting to a full `GlueingSquare` via the open
  mapping theorem.
* `TauCeti.Huber.GlueingSquare.congr`, `TauCeti.Huber.GlueingSquare.symm`,
  `TauCeti.Huber.GlueingSquare.id`, and `TauCeti.Huber.GlueingSquare.of_subsingleton_right`:
  transport, symmetry, identity, and degenerate constructors.
* `TauCeti.Huber.GlueingSquare.equivSectionsOfModule`: for a flat `R`-module `N` on a glueing
  square, `N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R`.

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

/-- The two composite ring homomorphisms `R →+* R₁₂` in a glueing square agree. -/
theorem GlueingSquare.comp_algebraMap_eq (h : GlueingSquare R R₁ R₂ R₁₂) :
    (algebraMap R₁ R₁₂).comp (algebraMap R R₁) =
      (algebraMap R₂ R₁₂).comp (algebraMap R R₂) :=
  RingHom.ext fun r ↦ sub_eq_zero.mp ((h.exact_sub _).mpr ⟨r, rfl⟩)

/-- Pointwise commutativity of a glueing square `R → R₁, R₂ → R₁₂`. -/
theorem GlueingSquare.algebraMap_algebraMap (h : GlueingSquare R R₁ R₂ R₁₂) (r : R) :
    algebraMap R₁ R₁₂ (algebraMap R R₁ r) = algebraMap R₂ R₁₂ (algebraMap R R₂ r) :=
  RingHom.congr_fun h.comp_algebraMap_eq r

/-- In a glueing square, the diagonal inclusion `R → R₁ × R₂` is a topological embedding. -/
theorem GlueingSquare.isEmbedding (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsEmbedding fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r) :=
  ⟨h.isInducing, h.injective⟩

/-- In a glueing square, the difference map `R₁ × R₂ → R₁₂` is a quotient map. -/
theorem GlueingSquare.isQuotientMap_sub (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsQuotientMap fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 :=
  Topology.isQuotientMap_iff_isStrictMap_surjective.mpr ⟨h.isStrictMap_sub, h.surjective_sub⟩

/-- In a glueing square, when `R₁` and `R₂` have continuous addition, the difference map
`R₁ × R₂ → R₁₂` is an open quotient map. -/
theorem GlueingSquare.isOpenQuotientMap_sub [ContinuousAdd R₁] [ContinuousAdd R₂]
    (h : GlueingSquare R R₁ R₂ R₁₂) :
    IsOpenQuotientMap
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 :=
  AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
    (φ := (algebraMap R₁ R₁₂).toAddMonoidHom.comp (AddMonoidHom.fst R₁ R₂) -
      (algebraMap R₂ R₁₂).toAddMonoidHom.comp (AddMonoidHom.snd R₁ R₂))
    h.isQuotientMap_sub

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
  injective _ _ heq := h.injective (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))
  exact_sub x := by
    rw [sub_eq_zero, eq_comm, ← sub_eq_zero, h.exact_sub (x.2, x.1)]
    exact ⟨fun ⟨r, hr⟩ ↦ ⟨r, Prod.ext (congrArg Prod.snd hr) (congrArg Prod.fst hr)⟩,
      fun ⟨r, hr⟩ ↦ ⟨r, Prod.ext (congrArg Prod.snd hr) (congrArg Prod.fst hr)⟩⟩
  surjective_sub y := let ⟨⟨a, b⟩, hab⟩ := h.surjective_sub (-y)
    ⟨(b, a), by dsimp only at hab ⊢; rw [← neg_sub, hab, neg_neg]⟩
  isInducing := (Homeomorph.prodComm R₁ R₂).isInducing.comp h.isInducing
  isStrictMap_sub := by
    have hcomp : (fun x : R₂ × R₁ ↦ algebraMap R₂ R₁₂ x.1 - algebraMap R₁ R₁₂ x.2) =
        (Homeomorph.neg R₁₂) ∘ (fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) ∘
          (Homeomorph.prodComm R₂ R₁) :=
      funext fun ⟨_, _⟩ ↦ (neg_sub _ _).symm
    rw [hcomp, Homeomorph.comp_isStrictMap_iff, Homeomorph.isStrictMap_comp_iff]
    exact h.isStrictMap_sub
  denseRange := hd₁
  exists_prime_comap_eq m hm := by
    obtain ⟨p, hp, hpm⟩ := h.exists_prime_comap_eq m hm
    let swap : R₂ × R₁ →+* R₁ × R₂ := (RingHom.snd R₂ R₁).prod (RingHom.fst R₂ R₁)
    exact ⟨p.comap swap, hp.comap swap, by rw [Ideal.comap_comap]; exact hpm⟩

/-- Transport a `GlueingSquare` across homeomorphic `R`-algebra equivalences on `R₁`, `R₂` and a
homeomorphic ring equivalence on `R₁₂` intertwining the transition homomorphisms to the overlap
ring. -/
theorem GlueingSquare.congr {L₁ L₂ L₁₂ : Type*}
    [CommRing L₁] [CommRing L₂] [CommRing L₁₂]
    [TopologicalSpace L₁] [TopologicalSpace L₂] [TopologicalSpace L₁₂]
    [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₁₂] [Algebra L₂ L₁₂]
    (h : GlueingSquare R L₁ L₂ L₁₂)
    (e₁ : L₁ ≃ₐ[R] R₁) (he₁ : Continuous e₁) (he₁_symm : Continuous e₁.symm)
    (e₂ : L₂ ≃ₐ[R] R₂) (he₂ : Continuous e₂) (he₂_symm : Continuous e₂.symm)
    (e₁₂ : L₁₂ ≃+* R₁₂) (he₁₂ : Continuous e₁₂) (he₁₂_symm : Continuous e₁₂.symm)
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
  have hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 := by
    let ιL : R →+ L₁ × L₂ := ((algebraMap R L₁).prod (algebraMap R L₂)).toAddMonoidHom
    let ιR : R →+ R₁ × R₂ := ((algebraMap R R₁).prod (algebraMap R R₂)).toAddMonoidHom
    let δL : L₁ × L₂ →+ L₁₂ :=
      (algebraMap L₁ L₁₂).toAddMonoidHom.comp (AddMonoidHom.fst L₁ L₂) -
        (algebraMap L₂ L₁₂).toAddMonoidHom.comp (AddMonoidHom.snd L₁ L₂)
    let δR : R₁ × R₂ →+ R₁₂ :=
      (algebraMap R₁ R₁₂).toAddMonoidHom.comp (AddMonoidHom.fst R₁ R₂) -
        (algebraMap R₂ R₁₂).toAddMonoidHom.comp (AddMonoidHom.snd R₁ R₂)
    exact (Function.Exact.iff_of_ladder_addEquiv (AddEquiv.refl R)
      (e₁.toAddEquiv.prodCongr e₂.toAddEquiv) e₁₂.toAddEquiv
      (f₁₂ := ιL) (f₂₃ := δL) (g₁₂ := ιR) (g₂₃ := δR)
      (AddMonoidHom.ext fun r ↦ Prod.ext (e₁.commutes r).symm (e₂.commutes r).symm)
      (AddMonoidHom.ext fun ⟨x₁, x₂⟩ ↦ by
        simp [δL, δR, hcomp₁, hcomp₂]; rfl)).mpr h.exact_sub
  exact ⟨(funext fun r ↦ (e₁.commutes r).symm) ▸ he₁.comp h.continuous_algebraMap₁,
    (funext fun r ↦ (e₂.commutes r).symm) ▸ he₂.comp h.continuous_algebraMap₂,
    hmap₁ ▸ he₁₂.comp (h.continuous_algebraMap₁₂.comp he₁_symm),
    hmap₂ ▸ he₁₂.comp (h.continuous_algebraMap₂₁₂.comp he₂_symm),
    hι ▸ (H₁.prodCongr H₂).injective.comp h.injective,
    hexact,
    hδ ▸ H₁₂.surjective.comp (h.surjective_sub.comp (H₁.prodCongr H₂).symm.surjective),
    hι ▸ (H₁.prodCongr H₂).isInducing.comp h.isInducing,
    by rw [hδ, Homeomorph.comp_isStrictMap_iff, Homeomorph.isStrictMap_comp_iff]
       exact h.isStrictMap_sub,
    hmap₂ ▸ H₁₂.surjective.denseRange.comp
      (h.denseRange.comp H₂.symm.surjective.denseRange h.continuous_algebraMap₂₁₂) he₁₂,
    fun m hm ↦ by
      obtain ⟨p, hp, hpm⟩ := h.exists_prime_comap_eq m hm
      let ψ := RingHom.prodMap e₁.symm.toRingHom e₂.symm.toRingHom
      refine ⟨p.comap ψ, hp.comap ψ, ?_⟩
      rw [Ideal.comap_comap]
      convert hpm using 2
      ext r <;> simp [ψ]⟩

end Basic

section OfExact

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R]
  [UniformSpace R₁] [IsUniformAddGroup R₁] [IsTopologicalRing R₁] [IsHuberRing R₁]
  [CompleteSpace R₁] [T0Space R₁]
  [UniformSpace R₂] [IsUniformAddGroup R₂] [IsTopologicalRing R₂] [IsHuberRing R₂]
  [CompleteSpace R₂] [T0Space R₂]
  [UniformSpace R₁₂] [IsUniformAddGroup R₁₂] [IsTopologicalRing R₁₂] [IsHuberRing R₁₂]
  [CompleteSpace R₁₂] [T0Space R₁₂]
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
  have hcR₁₂ : Continuous (algebraMap R R₁₂) :=
    (hc₁₂.comp hc₁).congr fun r ↦ (IsScalarTower.algebraMap_apply R R₁ R₁₂ r).symm
  have : ContinuousSMul R R₁₂ := continuousSMul_of_algebraMap R R₁₂ hcR₁₂
  have : (𝓤 R₁).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 R₂).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 R₁₂).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓝 (0 : R₁ × R₂)).IsCountablyGenerated := by
    rw [Prod.zero_eq_mk, nhds_prod_eq]; infer_instance
  let ι : R →ₗ[R] R₁ × R₂ := (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)
  let δ : (R₁ × R₂) →ₗ[R] R₁₂ :=
    (IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
      (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂)
  have hι_cont : Continuous ι := hc₁.prodMk hc₂
  have hδ_cont : Continuous δ := (hc₁₂.comp continuous_fst).sub (hc₂₁₂.comp continuous_snd)
  have hclosed : IsClosed (ι.range : Set (R₁ × R₂)) := by
    have hrange : (ι.range : Set (R₁ × R₂)) = {x | algebraMap R₁ R₁₂ x.1 = algebraMap R₂ R₁₂ x.2} :=
      Set.ext fun x ↦ (hexact x).symm.trans sub_eq_zero
    rw [hrange]
    exact isClosed_eq (hc₁₂.comp continuous_fst) (hc₂₁₂.comp continuous_snd)
  have hι_emb : Topology.IsEmbedding ι :=
    Topology.isEmbedding_iff_isStrictMap_injective.mpr
      ⟨ι.isStrictMap_of_isClosed_range_of_isTateRing hι_cont.continuousAt hclosed, hinj⟩
  exact ⟨hc₁, hc₂, hc₁₂, hc₂₁₂, hinj, hexact, hsurj, hι_emb.isInducing,
    (δ.isQuotientMap_of_isTateRing hsurj hδ_cont.continuousAt).isStrictMap, hdense, hprime⟩

/-- The identity glueing square `R → R, R → R` on any topological ring `R` with continuous
subtraction. -/
theorem GlueingSquare.id (R : Type*) [CommRing R] [TopologicalSpace R] [ContinuousSub R] :
    GlueingSquare R R R R where
  continuous_algebraMap₁ := continuous_id
  continuous_algebraMap₂ := continuous_id
  continuous_algebraMap₁₂ := continuous_id
  continuous_algebraMap₂₁₂ := continuous_id
  injective _ _ h := congrArg Prod.fst h
  exact_sub := fun ⟨_, _⟩ ↦ by simp [sub_eq_zero, eq_comm]
  surjective_sub y := ⟨(y, 0), by simp⟩
  isInducing := Topology.IsInducing.of_comp
    (continuous_id.prodMk continuous_id) continuous_fst Topology.IsInducing.id
  isStrictMap_sub :=
    (Topology.IsQuotientMap.of_inverse (continuous_id.prodMk continuous_const)
      (continuous_fst.sub continuous_snd) fun y : R ↦ sub_zero y).isStrictMap
  denseRange := denseRange_id
  exists_prime_comap_eq m hm :=
    have := hm.isPrime
    ⟨m.comap (RingHom.fst R R), Ideal.IsPrime.comap _,
      by rw [Ideal.comap_comap]; exact Ideal.comap_id m⟩

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
  exists_prime_comap_eq m hm :=
    have := hm.isPrime
    ⟨m.comap (RingHom.fst R R₂), Ideal.IsPrime.comap _,
      by rw [Ideal.comap_comap]; exact Ideal.comap_id m⟩

end OfExact

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
  simp [GlueingSquare.equivSectionsOfModule]

end GlueingSquareSections

end TauCeti.Huber

end
