/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Basic
public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Glueing.Datum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.RingTheory.Huber.OpenMapping

/-!
# Glueing squares of topological rings

Kedlaya and Liu abstract Kiehl's descent of finite projective modules across two-piece rational
covers into a *glueing square* of topological rings (`R → R₁, R₂ → R₁₂`,
`TauCeti.Huber.GlueingSquare`) together with algebraic *glueing data* (`TauCeti.GlueingDatum`).

Following Kedlaya–Liu Proposition 2.7.5, `TauCeti.Huber.GlueingSquare` phrases condition (c) via
prime contraction (every maximal ideal of `R` contracts from a prime ideal of `R₁ × R₂`). By
Henkel's open mapping theorem, `TauCeti.Huber.GlueingSquare.of_exact` deduces `isInducing` and
`isStrictMap_sub` from continuity, algebraic exactness, surjectivity of `(r₁, r₂) ↦ r₁ - r₂`,
dense range of `R₂ → R₁₂`, and prime contraction.

## Main definitions

* `TauCeti.Huber.GlueingSquare R R₁ R₂ R₁₂`: a glueing square of topological rings.

## Main results

* `TauCeti.Huber.GlueingSquare.comp_algebraMap_eq` and `algebraMap_algebraMap`.
* `TauCeti.Huber.GlueingSquare.isEmbedding`, `range_algebraMap_prod`, `lift`, `continuous_lift`,
  `eq_lift`, `isClosed_range_algebraMap_prod`, and `isClosedEmbedding`.
* `TauCeti.Huber.GlueingSquare.isOpenQuotientMap_sub`, `of_exact`, `congr`, `symm`, `id`, and
  `of_subsingleton_right`.
* `TauCeti.Huber.GlueingSquare.equivSectionsOfModule`: flat module recovery on a glueing square.

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
with condition (c) via its prime-ideal contraction consequence): continuous algebra maps making
`0 → R → R₁ × R₂ → R₁₂ → 0` topologically strict exact, with `algebraMap R₂ R₁₂` of dense range
and every maximal ideal of `R` contracting from a prime ideal of `R₁ × R₂`. -/
structure GlueingSquare : Prop where
  /-- Continuity of `R₁ → R₁₂`. -/
  continuous_algebraMap₁₁₂ : Continuous (algebraMap R₁ R₁₂)
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
  denseRange_algebraMap₂₁₂ : DenseRange (algebraMap R₂ R₁₂)
  /-- Every maximal ideal of `R` is the contraction of a prime ideal of `R₁ × R₂`. -/
  exists_prime_comap_eq : ∀ m : Ideal R, m.IsMaximal → ∃ p : Ideal (R₁ × R₂), p.IsPrime ∧
    p.comap ((algebraMap R R₁).prod (algebraMap R R₂)) = m

variable {R R₁ R₂ R₁₂}

/-- The structure map `R → R₁` of a glueing square is continuous. -/
theorem GlueingSquare.continuous_algebraMap₁ (h : GlueingSquare R R₁ R₂ R₁₂) :
    Continuous (algebraMap R R₁) := continuous_fst.comp h.isInducing.continuous
/-- The structure map `R → R₂` of a glueing square is continuous. -/
theorem GlueingSquare.continuous_algebraMap₂ (h : GlueingSquare R R₁ R₂ R₁₂) :
    Continuous (algebraMap R R₂) := continuous_snd.comp h.isInducing.continuous
/-- The two composite ring homomorphisms `R →+* R₁₂` in a glueing square agree. -/
theorem GlueingSquare.comp_algebraMap_eq (h : GlueingSquare R R₁ R₂ R₁₂) :
    (algebraMap R₁ R₁₂).comp (algebraMap R R₁) = (algebraMap R₂ R₁₂).comp (algebraMap R R₂) :=
  RingHom.ext fun r ↦ sub_eq_zero.mp ((h.exact_sub _).mpr ⟨r, rfl⟩)
/-- Pointwise commutativity of a glueing square `R → R₁, R₂ → R₁₂`. -/
theorem GlueingSquare.algebraMap_algebraMap (h : GlueingSquare R R₁ R₂ R₁₂) (r : R) :
    algebraMap R₁ R₁₂ (algebraMap R R₁ r) = algebraMap R₂ R₁₂ (algebraMap R R₂ r) :=
  RingHom.congr_fun h.comp_algebraMap_eq r
/-- In a glueing square, the product inclusion `R → R₁ × R₂` is a topological embedding. -/
theorem GlueingSquare.isEmbedding (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsEmbedding fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r) :=
  ⟨h.isInducing, h.injective⟩
/-- The range of `R → R₁ × R₂` is the equalizer of `R₁ → R₁₂` and `R₂ → R₁₂`. -/
theorem GlueingSquare.range_algebraMap_prod (h : GlueingSquare R R₁ R₂ R₁₂) :
    Set.range (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)) =
      {x : R₁ × R₂ | algebraMap R₁ R₁₂ x.1 = algebraMap R₂ R₁₂ x.2} :=
  Set.ext fun x ↦ (h.exact_sub x).symm.trans sub_eq_zero

section Lift
variable {T : Type*} [Semiring T]

/-- Pullback universal property of a glueing square: lift compatible `f₁ : T →+* R₁` and
`f₂ : T →+* R₂` along `R → R₁ × R₂`. -/
noncomputable def GlueingSquare.lift (h : GlueingSquare R R₁ R₂ R₁₂) (f₁ : T →+* R₁)
    (f₂ : T →+* R₂) (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂) : T →+* R :=
  let φ t := (h.exact_sub (f₁ t, f₂ t)).mp (sub_eq_zero.mpr (RingHom.congr_fun hf t))
  let h1 t : algebraMap R R₁ (φ t).choose = f₁ t := congrArg Prod.fst (φ t).choose_spec
  let h2 t : algebraMap R R₂ (φ t).choose = f₂ t := congrArg Prod.snd (φ t).choose_spec
  { toFun t := (φ t).choose
    map_one' := h.injective (Prod.ext ((h1 1).trans <| (map_one f₁).trans (map_one _).symm)
      ((h2 1).trans <| (map_one f₂).trans (map_one _).symm))
    map_zero' := h.injective (Prod.ext ((h1 0).trans <| (map_zero f₁).trans (map_zero _).symm)
      ((h2 0).trans <| (map_zero f₂).trans (map_zero _).symm))
    map_add' a b := h.injective (Prod.ext ((h1 _).trans <| (map_add f₁ a b).trans <|
      (congrArg₂ (· + ·) (h1 a).symm (h1 b).symm).trans (map_add (algebraMap R R₁) _ _).symm)
      ((h2 _).trans <| (map_add f₂ a b).trans <|
      (congrArg₂ (· + ·) (h2 a).symm (h2 b).symm).trans (map_add (algebraMap R R₂) _ _).symm))
    map_mul' a b := h.injective (Prod.ext ((h1 _).trans <| (map_mul f₁ a b).trans <|
      (congrArg₂ (· * ·) (h1 a).symm (h1 b).symm).trans (map_mul (algebraMap R R₁) _ _).symm)
      ((h2 _).trans <| (map_mul f₂ a b).trans <|
      (congrArg₂ (· * ·) (h2 a).symm (h2 b).symm).trans (map_mul (algebraMap R R₂) _ _).symm)) }

@[simp] theorem GlueingSquare.algebraMap_lift_left (h : GlueingSquare R R₁ R₂ R₁₂) (f₁ : T →+* R₁)
    (f₂ : T →+* R₂) (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂) (t : T) :
    algebraMap R R₁ (h.lift f₁ f₂ hf t) = f₁ t :=
  congrArg Prod.fst ((h.exact_sub _).mp (sub_eq_zero.mpr (RingHom.congr_fun hf t))).choose_spec
@[simp] theorem GlueingSquare.algebraMap_lift_right (h : GlueingSquare R R₁ R₂ R₁₂)
    (f₁ : T →+* R₁) (f₂ : T →+* R₂)
    (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂) (t : T) :
    algebraMap R R₂ (h.lift f₁ f₂ hf t) = f₂ t :=
  congrArg Prod.snd ((h.exact_sub _).mp (sub_eq_zero.mpr (RingHom.congr_fun hf t))).choose_spec
@[simp] theorem GlueingSquare.comp_lift_left (h : GlueingSquare R R₁ R₂ R₁₂) (f₁ : T →+* R₁)
    (f₂ : T →+* R₂) (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂) :
    (algebraMap R R₁).comp (h.lift f₁ f₂ hf) = f₁ := RingHom.ext (h.algebraMap_lift_left f₁ f₂ hf)
@[simp] theorem GlueingSquare.comp_lift_right (h : GlueingSquare R R₁ R₂ R₁₂) (f₁ : T →+* R₁)
    (f₂ : T →+* R₂) (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂) :
    (algebraMap R R₂).comp (h.lift f₁ f₂ hf) = f₂ := RingHom.ext (h.algebraMap_lift_right f₁ f₂ hf)
/-- The universal lift `h.lift f₁ f₂ hf` is continuous whenever `f₁` and `f₂` are. -/
theorem GlueingSquare.continuous_lift [TopologicalSpace T] (h : GlueingSquare R R₁ R₂ R₁₂)
    {f₁ : T →+* R₁} {f₂ : T →+* R₂}
    (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) : Continuous (h.lift f₁ f₂ hf) :=
  h.isInducing.continuous_iff.mpr <| by
    simpa only [Function.comp_def, algebraMap_lift_left, algebraMap_lift_right] using hc₁.prodMk hc₂
/-- Two ring homomorphisms into `R` agree if their compositions with `R → R₁` and `R → R₂` do. -/
theorem GlueingSquare.ringHom_ext (h : GlueingSquare R R₁ R₂ R₁₂) {g₁ g₂ : T →+* R}
    (h₁ : (algebraMap R R₁).comp g₁ = (algebraMap R R₁).comp g₂)
    (h₂ : (algebraMap R R₂).comp g₁ = (algebraMap R R₂).comp g₂) : g₁ = g₂ :=
  RingHom.ext fun t ↦ h.injective (Prod.ext (RingHom.congr_fun h₁ t) (RingHom.congr_fun h₂ t))
/-- Uniqueness of the universal lift `h.lift f₁ f₂ hf`. -/
theorem GlueingSquare.eq_lift (h : GlueingSquare R R₁ R₂ R₁₂) {f₁ : T →+* R₁} {f₂ : T →+* R₂}
    (hf : (algebraMap R₁ R₁₂).comp f₁ = (algebraMap R₂ R₁₂).comp f₂) {g : T →+* R}
    (hg₁ : (algebraMap R R₁).comp g = f₁) (hg₂ : (algebraMap R R₂).comp g = f₂) :
    g = h.lift f₁ f₂ hf := h.ringHom_ext (hg₁.trans (h.comp_lift_left f₁ f₂ hf).symm)
  (hg₂.trans (h.comp_lift_right f₁ f₂ hf).symm)
end Lift

/-- With Hausdorff overlap `R₁₂`, the range of `R → R₁ × R₂` is closed. -/
theorem GlueingSquare.isClosed_range_algebraMap_prod [T2Space R₁₂]
    (h : GlueingSquare R R₁ R₂ R₁₂) :
    IsClosed (Set.range fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)) :=
  h.range_algebraMap_prod.symm ▸ isClosed_eq (h.continuous_algebraMap₁₁₂.comp continuous_fst)
    (h.continuous_algebraMap₂₁₂.comp continuous_snd)
/-- With Hausdorff overlap `R₁₂`, `R → R₁ × R₂` is a closed embedding. -/
theorem GlueingSquare.isClosedEmbedding [T2Space R₁₂] (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsClosedEmbedding fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r) :=
  ⟨h.isEmbedding, h.isClosed_range_algebraMap_prod⟩
/-- In a glueing square, the difference map `R₁ × R₂ → R₁₂` is a quotient map. -/
theorem GlueingSquare.isQuotientMap_sub (h : GlueingSquare R R₁ R₂ R₁₂) :
    Topology.IsQuotientMap fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 :=
  Topology.isQuotientMap_iff_isStrictMap_surjective.mpr ⟨h.isStrictMap_sub, h.surjective_sub⟩
/-- With continuous addition on `R₁` and `R₂`, `R₁ × R₂ → R₁₂` is an open quotient map. -/
theorem GlueingSquare.isOpenQuotientMap_sub [ContinuousAdd R₁] [ContinuousAdd R₂]
    (h : GlueingSquare R R₁ R₂ R₁₂) :
    IsOpenQuotientMap fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 :=
  AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
    (φ := (algebraMap R₁ R₁₂).toAddMonoidHom.comp (AddMonoidHom.fst R₁ R₂) -
      (algebraMap R₂ R₁₂).toAddMonoidHom.comp (AddMonoidHom.snd R₁ R₂))
    h.isQuotientMap_sub

/-- Swapping `R₁` and `R₂` in a glueing square yields a glueing square whenever
`algebraMap R₁ R₁₂` also has dense range. -/
theorem GlueingSquare.symm [ContinuousNeg R₁₂] (h : GlueingSquare R R₁ R₂ R₁₂)
    (hd₁ : DenseRange (algebraMap R₁ R₁₂)) : GlueingSquare R R₂ R₁ R₁₂ where
  continuous_algebraMap₁₁₂ := h.continuous_algebraMap₂₁₂
  continuous_algebraMap₂₁₂ := h.continuous_algebraMap₁₁₂
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
          (Homeomorph.prodComm R₂ R₁) := funext fun ⟨_, _⟩ ↦ (neg_sub _ _).symm
    rw [hcomp, Homeomorph.comp_isStrictMap_iff, Homeomorph.isStrictMap_comp_iff]
    exact h.isStrictMap_sub
  denseRange_algebraMap₂₁₂ := hd₁
  exists_prime_comap_eq m hm := by
    obtain ⟨p, hp, hpm⟩ := h.exists_prime_comap_eq m hm
    let swap : R₂ × R₁ →+* R₁ × R₂ := (RingHom.snd R₂ R₁).prod (RingHom.fst R₂ R₁)
    exact ⟨p.comap swap, hp.comap swap, by rw [Ideal.comap_comap]; exact hpm⟩

/-- Transport a `GlueingSquare` across homeomorphic `R`-algebra equivalences on `R₁`, `R₂` and a
homeomorphic ring equivalence on `R₁₂`. -/
theorem GlueingSquare.congr {L₁ L₂ L₁₂ : Type*} [CommRing L₁] [CommRing L₂] [CommRing L₁₂]
    [TopologicalSpace L₁] [TopologicalSpace L₂] [TopologicalSpace L₁₂]
    [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₁₂] [Algebra L₂ L₁₂] (h : GlueingSquare R L₁ L₂ L₁₂)
    (e₁ : L₁ ≃ₐ[R] R₁) (he₁ : Continuous e₁) (he₁_symm : Continuous e₁.symm)
    (e₂ : L₂ ≃ₐ[R] R₂) (he₂ : Continuous e₂) (he₂_symm : Continuous e₂.symm)
    (e₁₂ : L₁₂ ≃+* R₁₂) (he₁₂ : Continuous e₁₂) (he₁₂_symm : Continuous e₁₂.symm)
    (hcomp₁ : ∀ x : L₁, e₁₂ (algebraMap L₁ L₁₂ x) = algebraMap R₁ R₁₂ (e₁ x))
    (hcomp₂ : ∀ x : L₂, e₁₂ (algebraMap L₂ L₁₂ x) = algebraMap R₂ R₁₂ (e₂ x)) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  let H₁ : L₁ ≃ₜ R₁ := ⟨e₁.toEquiv, he₁, he₁_symm⟩; let H₂ : L₂ ≃ₜ R₂ := ⟨e₂.toEquiv, he₂, he₂_symm⟩
  let H₁₂ : L₁₂ ≃ₜ R₁₂ := ⟨e₁₂.toEquiv, he₁₂, he₁₂_symm⟩
  have hι : (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)) =
      (H₁.prodCongr H₂) ∘ fun r : R ↦ (algebraMap R L₁ r, algebraMap R L₂ r) := by
    ext <;> simp [H₁, H₂]
  have hδ : (fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) =
      H₁₂ ∘ (fun y : L₁ × L₂ ↦ algebraMap L₁ L₁₂ y.1 - algebraMap L₂ L₁₂ y.2) ∘
        (H₁.prodCongr H₂).symm := by ext ⟨_, _⟩; simp [H₁, H₂, H₁₂, map_sub, hcomp₁, hcomp₂]
  have hmap₁ : (algebraMap R₁ R₁₂ : R₁ → R₁₂) = H₁₂ ∘ algebraMap L₁ L₁₂ ∘ H₁.symm := by
    ext; simp [H₁, H₁₂, hcomp₁]
  have hmap₂ : (algebraMap R₂ R₁₂ : R₂ → R₁₂) = H₁₂ ∘ algebraMap L₂ L₁₂ ∘ H₂.symm := by
    ext; simp [H₂, H₁₂, hcomp₂]
  exact {
    continuous_algebraMap₁₁₂ := hmap₁ ▸ he₁₂.comp (h.continuous_algebraMap₁₁₂.comp he₁_symm)
    continuous_algebraMap₂₁₂ := hmap₂ ▸ he₁₂.comp (h.continuous_algebraMap₂₁₂.comp he₂_symm)
    injective := hι ▸ (H₁.prodCongr H₂).injective.comp h.injective
    exact_sub := (Function.Exact.iff_of_ladder_addEquiv (AddEquiv.refl R)
      (e₁.toAddEquiv.prodCongr e₂.toAddEquiv) e₁₂.toAddEquiv
      (f₁₂ := ((algebraMap R L₁).prod (algebraMap R L₂)).toAddMonoidHom)
      (f₂₃ := (algebraMap L₁ L₁₂).toAddMonoidHom.comp (AddMonoidHom.fst L₁ L₂) -
        (algebraMap L₂ L₁₂).toAddMonoidHom.comp (AddMonoidHom.snd L₁ L₂))
      (g₁₂ := ((algebraMap R R₁).prod (algebraMap R R₂)).toAddMonoidHom)
      (g₂₃ := (algebraMap R₁ R₁₂).toAddMonoidHom.comp (AddMonoidHom.fst R₁ R₂) -
        (algebraMap R₂ R₁₂).toAddMonoidHom.comp (AddMonoidHom.snd R₁ R₂))
      (AddMonoidHom.ext fun r ↦ Prod.ext (e₁.commutes r).symm (e₂.commutes r).symm)
      (AddMonoidHom.ext fun ⟨_, _⟩ ↦ by
        simp [AddMonoidHom.sub_apply, AddEquiv.prodCongr, hcomp₁, hcomp₂])).mpr h.exact_sub
    surjective_sub :=
      hδ ▸ H₁₂.surjective.comp (h.surjective_sub.comp (H₁.prodCongr H₂).symm.surjective)
    isInducing := hι ▸ (H₁.prodCongr H₂).isInducing.comp h.isInducing
    isStrictMap_sub := by
      rw [hδ, Homeomorph.comp_isStrictMap_iff, Homeomorph.isStrictMap_comp_iff]
      exact h.isStrictMap_sub
    denseRange_algebraMap₂₁₂ := hmap₂ ▸ H₁₂.surjective.denseRange.comp
      (h.denseRange_algebraMap₂₁₂.comp H₂.symm.surjective.denseRange
        h.continuous_algebraMap₂₁₂) he₁₂
    exists_prime_comap_eq := fun m hm ↦ by
      obtain ⟨p, hp, hpm⟩ := h.exists_prime_comap_eq m hm
      refine ⟨p.comap (RingHom.prodMap e₁.symm.toRingHom e₂.symm.toRingHom), hp.comap _, ?_⟩
      rw [Ideal.comap_comap]; convert hpm using 2; ext r <;> simp }
end Basic

section OfExact
variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R]
  [CompleteSpace R] [UniformSpace R₁] [IsUniformAddGroup R₁] [IsTopologicalRing R₁]
  [IsHuberRing R₁] [CompleteSpace R₁] [T0Space R₁] [UniformSpace R₂] [IsUniformAddGroup R₂]
  [IsTopologicalRing R₂] [IsHuberRing R₂] [CompleteSpace R₂] [T0Space R₂]
  [UniformSpace R₁₂] [IsUniformAddGroup R₁₂] [IsTopologicalRing R₁₂] [IsHuberRing R₁₂]
  [CompleteSpace R₁₂] [T0Space R₁₂] [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂]
  [Algebra R₂ R₁₂] [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]

/-- Smart constructor for `GlueingSquare`: over a complete Tate ring `R` with complete Hausdorff
Huber rings `R₁`, `R₂`, `R₁₂`, `isInducing` and `isStrictMap_sub` follow from Henkel's open
mapping theorem. -/
theorem GlueingSquare.of_exact (hc₁ : Continuous (algebraMap R R₁))
    (hc₂ : Continuous (algebraMap R R₂)) (hc₁₁₂ : Continuous (algebraMap R₁ R₁₂))
    (hc₂₁₂ : Continuous (algebraMap R₂ R₁₂))
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2)
    (hsurj :
      Function.Surjective fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2)
    (hdense : DenseRange (algebraMap R₂ R₁₂))
    (hprime : ∀ m : Ideal R, m.IsMaximal → ∃ p : Ideal (R₁ × R₂), p.IsPrime ∧
      p.comap ((algebraMap R R₁).prod (algebraMap R R₂)) = m) : GlueingSquare R R₁ R₂ R₁₂ := by
  have := continuousSMul_of_algebraMap R R₁ hc₁; have := continuousSMul_of_algebraMap R R₂ hc₂
  have := continuousSMul_of_algebraMap R R₁₂
    ((hc₁₁₂.comp hc₁).congr fun r ↦ (IsScalarTower.algebraMap_apply R R₁ R₁₂ r).symm)
  have : (𝓤 R₁).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 R₂).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 R₁₂).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : (𝓝 (0 : R₁ × R₂)).IsCountablyGenerated := by
    rw [Prod.zero_eq_mk, nhds_prod_eq]; infer_instance
  let ι : R →ₗ[R] R₁ × R₂ := (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)
  let δ : (R₁ × R₂) →ₗ[R] R₁₂ :=
    (IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
      (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂)
  have hclosed : IsClosed (ι.range : Set (R₁ × R₂)) := by
    rw [show (ι.range : Set (R₁ × R₂)) = {x | algebraMap R₁ R₁₂ x.1 = algebraMap R₂ R₁₂ x.2} from
      Set.ext fun x ↦ (hexact x).symm.trans sub_eq_zero]
    exact isClosed_eq (hc₁₁₂.comp continuous_fst) (hc₂₁₂.comp continuous_snd)
  have hι_emb : Topology.IsEmbedding ι := Topology.isEmbedding_iff_isStrictMap_injective.mpr
    ⟨ι.isStrictMap_of_isClosed_range_of_isTateRing (hc₁.prodMk hc₂).continuousAt hclosed, hinj⟩
  exact {
    continuous_algebraMap₁₁₂ := hc₁₁₂, continuous_algebraMap₂₁₂ := hc₂₁₂, injective := hinj,
    exact_sub := hexact, surjective_sub := hsurj, isInducing := hι_emb.isInducing,
    isStrictMap_sub := (δ.isQuotientMap_of_isTateRing hsurj ((hc₁₁₂.comp continuous_fst).sub
      (hc₂₁₂.comp continuous_snd)).continuousAt).isStrictMap,
    denseRange_algebraMap₂₁₂ := hdense, exists_prime_comap_eq := hprime }
/-- The identity glueing square `R → R, R → R` on any topological ring with continuous sub. -/
theorem GlueingSquare.id (R : Type*) [CommRing R] [TopologicalSpace R] [ContinuousSub R] :
    GlueingSquare R R R R where
  continuous_algebraMap₁₁₂ := continuous_id; continuous_algebraMap₂₁₂ := continuous_id
  injective _ _ h := congrArg Prod.fst h
  exact_sub := fun ⟨_, _⟩ ↦ by simp [sub_eq_zero, eq_comm]
  surjective_sub y := ⟨(y, 0), by simp⟩
  isInducing := Topology.IsInducing.of_comp
    (continuous_id.prodMk continuous_id) continuous_fst Topology.IsInducing.id
  isStrictMap_sub := (Topology.IsQuotientMap.of_inverse (continuous_id.prodMk continuous_const)
    (continuous_fst.sub continuous_snd) fun y : R ↦ sub_zero y).isStrictMap
  denseRange_algebraMap₂₁₂ := denseRange_id
  exists_prime_comap_eq m hm := ⟨m.comap (RingHom.fst R R), hm.isPrime.comap _,
    by rw [Ideal.comap_comap]; exact Ideal.comap_id m⟩
/-- A degenerate glueing square `R → R, R₂ → R₁₂` with subsingleton `R₂`, `R₁₂`. -/
theorem GlueingSquare.of_subsingleton_right {R R₂ R₁₂ : Type*} [CommRing R] [CommRing R₂]
    [CommRing R₁₂] [TopologicalSpace R] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
    [Algebra R R₂] [Algebra R R₁₂] [Algebra R₂ R₁₂] [Subsingleton R₂] [Subsingleton R₁₂] :
    GlueingSquare R R R₂ R₁₂ where
  continuous_algebraMap₁₁₂ := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  continuous_algebraMap₂₁₂ := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  injective _ _ h := congrArg Prod.fst h
  exact_sub := fun ⟨r, _⟩ ↦
    ⟨fun _ ↦ ⟨r, Prod.ext rfl (Subsingleton.elim _ _)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  surjective_sub _ := ⟨(0, 0), Subsingleton.elim _ _⟩
  isInducing := Topology.IsInducing.of_comp
    (continuous_id.prodMk (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _))
    continuous_fst Topology.IsInducing.id
  isStrictMap_sub := (Topology.IsQuotientMap.of_inverse
    (continuous_const : Continuous fun _ : R₁₂ ↦ (0 : R × R₂))
    (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _)
    fun _ : R₁₂ ↦ Subsingleton.elim _ _).isStrictMap
  denseRange_algebraMap₂₁₂ _ := subset_closure ⟨(0 : R₂), Subsingleton.elim _ _⟩
  exists_prime_comap_eq m hm := ⟨m.comap (RingHom.fst R R₂), hm.isPrime.comap _,
    by rw [Ideal.comap_comap]; exact Ideal.comap_id m⟩
end OfExact

section GlueingSquareSections
variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [TopologicalSpace R] [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
/-- On any glueing square, a flat `R`-module `N` is canonically isomorphic to the sections of
`GlueingDatum.ofModule R₁ R₂ R₁₂ R N`. -/
noncomputable def GlueingSquare.equivSectionsOfModule (h : GlueingSquare R R₁ R₂ R₁₂)
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R N] :
    N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R :=
  GlueingDatum.equivSectionsOfModule h.injective h.exact_sub
@[simp] theorem GlueingSquare.equivSectionsOfModule_apply (h : GlueingSquare R R₁ R₂ R₁₂)
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R N] (n : N) :
    h.equivSectionsOfModule N n = GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n := by
  simp [GlueingSquare.equivSectionsOfModule]
end GlueingSquareSections
end TauCeti.Huber
end
