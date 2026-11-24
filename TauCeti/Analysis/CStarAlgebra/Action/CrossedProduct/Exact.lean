/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Quotient
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Ideal
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Surjective

/-!
# Exactness and quotient isomorphisms of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G` on a (possibly nonunital)
C⋆-algebra `A` with left Haar measure `μ`, and let `I` be a closed `α`-invariant two-sided ideal of
`A`. Dana Williams's Proposition 3.19 states that the induced full crossed-product homomorphisms

`0 → I ⋊_α G → A ⋊_α G → (A ⧸ I) ⋊_α G → 0`

form a short exact sequence of C⋆-algebras, so `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊_α G`.

Isometric injectivity on the left
(`TauCeti.CStarAction.Hom.isometry_fullCrossedProductMap_of_injective`,
`IsInvariant.isometry_fullCrossedProductMap_subtypeHom`) and surjectivity on the right
(`TauCeti.CStarAction.Hom.surjective_fullCrossedProductMap`) were established separately. Here we
prove exactness in the middle for any right-exact sequence `D --(φ)--> A --(q)--> B → 0` of
`G`-C⋆-algebras (without requiring `φ` to be injective), identify the two-sided ideal kernels of
induced surjective crossed-product maps, and construct the canonical `⋆`-isomorphisms of quotient
full crossed products.

None of the results require `T2Space G`, separability, σ-finiteness, or unitality. All resulting
`StarAlgEquiv`s between C⋆-algebras are automatically isometric via `StarAlgEquiv.isometry`.

## Main declarations

* `TauCeti.CStarAction.Hom.fullCrossedProductMap_exact`,
  `IsInvariant.fullCrossedProductMap_subtypeHom_exact`, and
  `IsInvariant.fullCrossedProductMap_idealSubtypeHom_exact`: exactness in the middle of full
  crossed-product sequences (Williams, Proposition 3.19).
* `IsInvariant.ker_fullCrossedProductMap_eq_fullCrossedProductIdeal`,
  `IsInvariant.ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal`,
  `TauCeti.CStarAction.Hom.ker_fullCrossedProductMap`, and
  `TauCeti.CStarAction.ker_fullCrossedProductMap_quotientMkHom`: two-sided ideal kernel
  identifications for surjective crossed-product maps.
* `IsInvariant.quotientFullCrossedProductEquiv`, `IsInvariant.quotientIdealFullCrossedProductEquiv`,
  `TauCeti.CStarAction.Hom.quotientKerFullCrossedProductEquiv`, and
  `TauCeti.CStarAction.quotientFullCrossedProductEquiv`: canonical `⋆`-isomorphisms identifying
  `(A ⋊_α G) ⧸ (I ⋊_α G)` with `B ⋊_β G` and `(A ⧸ I) ⋊_α G`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
* Iain Raeburn, *On crossed products and Takai duality*, Proc. Edinburgh Math. Soc. 31 (1988),
  321–330.
-/

public section

noncomputable section

open MeasureTheory Topology TauCeti
open scoped CStarAlgebra MultiplierAlgebra

universe u v w

/-! ### Exactness in the middle and two-sided ideal kernels -/

namespace TauCeti.CStarAction

private theorem mul_mem_of_ker {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {α : CStarAction G A} {β : CStarAction G B} {s : Set A}
    (q : Hom α β) (hker : ∀ a, q a = 0 ↔ a ∈ s) (a : A) {x : A} (hx : x ∈ s) : a * x ∈ s :=
  (hker (a * x)).mp <| by rw [map_mul, (hker x).mpr hx, mul_zero]

section ExactSequence

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B} (μ : Measure G) [μ.IsHaarMeasure]

/-- Any dense-range `⋆`-homomorphism `ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] C` annihilating an
equivariantly embedded crossed product vanishes on `ker (q.fullCrossedProductMap μ)`. -/
private theorem map_eq_zero_of_fullCrossedProductMap_eq_zero {D : Type v} {C : Type w}
    [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra C] {γ : CStarAction G D}
    (φ : Hom γ α) (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → a ∈ Set.range φ)
    (ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] C) (hψ : DenseRange ψ)
    (hψφ : ∀ z, ψ (φ.fullCrossedProductMap μ z) = 0)
    {x : FullCrossedProduct α μ} (hx : q.fullCrossedProductMap μ x = 0) :
    ψ x = 0 := by
  have hΦ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).IsMultiplierNondegenerate := by
    rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense]
    simp only [NonUnitalStarAlgHom.comp_apply]
    exact (NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp
      (φ := DoubleCentralizer.coeHom (𝕜 := ℂ)) hψ).mp
      NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom
  have hM : ∀ a, q a = 0 →
      (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ).coefficient a =
        0 := by
    intro a ha
    obtain ⟨d, rfl⟩ := hker a ha
    refine (((((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
      ).forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff μ φ).mp ?_) d
    intro y hy
    obtain ⟨z, rfl⟩ := (φ.fullCrossedProductMap μ).mem_range.mp hy
    rw [NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom]
    simp [hψφ z]
  have hN : ((((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
      ).descend q hq hM).integratedFull μ (q.fullCrossedProductMap μ x) =
      ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) x := by simp
  rw [hx, map_zero] at hN
  exact DoubleCentralizer.coe_injective (𝕜 := ℂ) (by simpa using hN.symm)

namespace Hom

/-- **Exactness of full crossed products** (Williams, Proposition 3.19). For any equivariant
homomorphism `φ : Hom γ α` and surjective equivariant homomorphism `q : Hom α β` forming an exact
pair `Function.Exact φ q`, the induced maps `D ⋊_γ G → A ⋊_α G → B ⋊_β G` form an exact pair. -/
theorem fullCrossedProductMap_exact
    {D : Type v} [NonUnitalCStarAlgebra D] {γ : CStarAction G D}
    (φ : Hom γ α) (q : Hom α β) (hq : Function.Surjective q) (hker : Function.Exact φ q) :
    Function.Exact (φ.fullCrossedProductMap μ) (q.fullCrossedProductMap μ) := by
  refine fun x => ⟨fun hx => ?_, fun ⟨z, hz⟩ => hz ▸
    φ.fullCrossedProductMap_fullCrossedProductMap_eq_zero μ q hker.apply_apply_eq_zero z⟩
  have hker' : ∀ a, q a = 0 ↔ a ∈ φ.toNonUnitalStarAlgHom.range := fun a =>
    (hker a).trans (NonUnitalStarAlgHom.mem_range _).symm
  have hmul : ∀ a : A, ∀ y ∈ φ.toNonUnitalStarAlgHom.range,
      a * y ∈ φ.toNonUnitalStarAlgHom.range :=
    fun a _ hy => mul_mem_of_ker q hker' a hy
  let J := (IsInvariant.range φ).fullCrossedProductIdeal μ hmul
  have hmemJ (y : FullCrossedProduct α μ) :
      y ∈ J ↔ y ∈ Set.range (φ.fullCrossedProductMap μ) := by
    rw [← SetLike.mem_coe, (IsInvariant.range φ).coe_fullCrossedProductIdeal μ hmul,
      ← NonUnitalStarAlgHom.coe_range, ← φ.range_fullCrossedProductMap μ,
      NonUnitalStarAlgHom.coe_range]
  have hmk : TwoSidedIdeal.Quotient.mkStarAlgHom J x = 0 :=
    map_eq_zero_of_fullCrossedProductMap_eq_zero μ φ q hq (fun a ha => (hker a).mp ha)
      (TwoSidedIdeal.Quotient.mkStarAlgHom J)
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective J).denseRange
      (fun z => (TwoSidedIdeal.Quotient.mkStarAlgHom_apply J _).trans <|
        TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr ((hmemJ _).mpr ⟨z, rfl⟩))
      hx
  exact (hmemJ x).mp <| TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp <|
    (TwoSidedIdeal.Quotient.mkStarAlgHom_apply J x).symm.trans hmk

end Hom

end ExactSequence

end TauCeti.CStarAction

/-! ### Invariant-ideal exactness and canonical quotient `⋆`-isomorphisms -/

namespace IsInvariant

open CStarAction CStarAction.FullCrossedProduct

section StarSubalgebra

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Exactness of the ideal sequence of full crossed products: if `q : Hom α β` is surjective with
kernel the closed `α`-invariant subalgebra `I`, then `I ⋊_α G → A ⋊_α G → B ⋊_β G` is exact. -/
theorem fullCrossedProductMap_subtypeHom_exact
    {q : Hom α β} (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    Function.Exact (hI.subtypeHom.fullCrossedProductMap μ) (q.fullCrossedProductMap μ) :=
  hI.subtypeHom.fullCrossedProductMap_exact μ q hq fun a => by simp [hker a]

/-- For a surjective equivariant `q : Hom α β` with kernel `I : NonUnitalStarSubalgebra ℂ A`, the
two-sided ideal kernel of `q.fullCrossedProductMap μ` is `hI.fullCrossedProductIdeal μ _`. -/
theorem ker_fullCrossedProductMap_eq_fullCrossedProductIdeal
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      hI.fullCrossedProductIdeal μ
        (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero])) := by
  ext x
  rw [TwoSidedIdeal.mem_ker, ← SetLike.mem_coe, hI.coe_fullCrossedProductIdeal]
  exact hI.fullCrossedProductMap_subtypeHom_exact μ hq hker x

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` associated to a surjective
equivariant homomorphism `q : Hom α β` with kernel `I : NonUnitalStarSubalgebra ℂ A`. -/
def quotientFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (FullCrossedProduct α μ) ⧸
        hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero])) ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective
    (q.surjective_fullCrossedProductMap μ hq.denseRange)
    (hI.ker_fullCrossedProductMap_eq_fullCrossedProductIdeal μ q hq hker)

@[simp]
theorem quotientFullCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) (x : FullCrossedProduct α μ) :
    hI.quotientFullCrossedProductEquiv μ q hq hker
        (TwoSidedIdeal.Quotient.mk
          (hI.fullCrossedProductIdeal μ
            (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero]))) x) =
      q.fullCrossedProductMap μ x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_mk _ _ x

@[simp]
theorem quotientFullCrossedProductEquiv_comp_mkStarAlgHom (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom
          (hI.fullCrossedProductIdeal μ
            (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero])))) =
      q.fullCrossedProductMap μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_comp_mkStarAlgHom _ _

@[simp]
theorem quotientFullCrossedProductEquiv_symm_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) (x : FullCrossedProduct α μ) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk
        (hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero]))) x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_apply _ _ x

@[simp]
theorem quotientFullCrossedProductEquiv_symm_of_convolutionMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (f : ConvolutionAlgebra α μ) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).symm (of β μ (q.convolutionMap μ f)) =
      TwoSidedIdeal.Quotient.mk
        (hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero]))) (of α μ f) := by
  rw [← q.fullCrossedProductMap_of μ f,
    hI.quotientFullCrossedProductEquiv_symm_fullCrossedProductMap]

@[simp]
theorem quotientFullCrossedProductEquiv_symm_comp_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).symm.toNonUnitalStarAlgHom.comp
        (q.fullCrossedProductMap μ) =
      TwoSidedIdeal.Quotient.mkStarAlgHom
        (hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).mp (by rw [map_mul, (hker _).mpr hx, mul_zero]))) :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_comp _ _

end StarSubalgebra

section TwoSidedIdeal

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Exactness in the middle for `I : TwoSidedIdeal A` and a surjective `q : Hom α β` with kernel
`I`. -/
theorem fullCrossedProductMap_idealSubtypeHom_exact
    {q : Hom α β} (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    Function.Exact (hI.idealSubtypeHom.fullCrossedProductMap μ) (q.fullCrossedProductMap μ) :=
  hI.idealSubtypeHom.fullCrossedProductMap_exact μ q hq fun a => by simp [hker a]

/-- For a surjective `q : Hom α β` with kernel `I : TwoSidedIdeal A`, the two-sided ideal kernel of
`q.fullCrossedProductMap μ` is `hI.idealFullCrossedProductIdeal μ`. -/
theorem ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) = hI.idealFullCrossedProductIdeal μ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, ← SetLike.mem_coe, hI.coe_idealFullCrossedProductIdeal]
  exact hI.fullCrossedProductMap_idealSubtypeHom_exact μ hq hker x

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` associated to a surjective
equivariant homomorphism `q : Hom α β` with kernel `I : TwoSidedIdeal A`. -/
def quotientIdealFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (FullCrossedProduct α μ) ⧸ hI.idealFullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective
    (q.surjective_fullCrossedProductMap μ hq.denseRange)
    (hI.ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal μ q hq hker)

@[simp]
theorem quotientIdealFullCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) (x : FullCrossedProduct α μ) :
    hI.quotientIdealFullCrossedProductEquiv μ q hq hker
        (TwoSidedIdeal.Quotient.mk (hI.idealFullCrossedProductIdeal μ) x) =
      q.fullCrossedProductMap μ x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_mk _ _ x

@[simp]
theorem quotientIdealFullCrossedProductEquiv_comp_mkStarAlgHom (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (hI.quotientIdealFullCrossedProductEquiv μ q hq hker).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom (hI.idealFullCrossedProductIdeal μ)) =
      q.fullCrossedProductMap μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_comp_mkStarAlgHom _ _

@[simp]
theorem quotientIdealFullCrossedProductEquiv_symm_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) (x : FullCrossedProduct α μ) :
    (hI.quotientIdealFullCrossedProductEquiv μ q hq hker).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk (hI.idealFullCrossedProductIdeal μ) x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_apply _ _ x

@[simp]
theorem quotientIdealFullCrossedProductEquiv_symm_of_convolutionMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (f : ConvolutionAlgebra α μ) :
    (hI.quotientIdealFullCrossedProductEquiv μ q hq hker).symm (of β μ (q.convolutionMap μ f)) =
      TwoSidedIdeal.Quotient.mk (hI.idealFullCrossedProductIdeal μ) (of α μ f) := by
  rw [← q.fullCrossedProductMap_of μ f,
    hI.quotientIdealFullCrossedProductEquiv_symm_fullCrossedProductMap]

@[simp]
theorem quotientIdealFullCrossedProductEquiv_symm_comp_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (hI.quotientIdealFullCrossedProductEquiv μ q hq hker).symm.toNonUnitalStarAlgHom.comp
        (q.fullCrossedProductMap μ) =
      TwoSidedIdeal.Quotient.mkStarAlgHom (hI.idealFullCrossedProductIdeal μ) :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_comp _ _

end TwoSidedIdeal

end IsInvariant

namespace TauCeti.CStarAction

open FullCrossedProduct

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B} (μ : Measure G) [μ.IsHaarMeasure]

namespace Hom

/-- For any surjective equivariant homomorphism `q : Hom α β`, the kernel of
`q.fullCrossedProductMap μ` is the embedded crossed product of `ker q`. -/
theorem ker_fullCrossedProductMap (q : Hom α β) (hq : Function.Surjective q) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      (IsInvariant.ker q).idealFullCrossedProductIdeal μ :=
  (IsInvariant.ker q).ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal μ q hq fun _ =>
    (TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).symm

/-- Exactness of `(ker q) ⋊_α G → A ⋊_α G → B ⋊_β G` for any surjective equivariant homomorphism
`q : Hom α β`. -/
theorem fullCrossedProductMap_idealSubtypeHom_ker_exact
    (q : Hom α β) (hq : Function.Surjective q) :
    Function.Exact ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ)
      (q.fullCrossedProductMap μ) :=
  (IsInvariant.ker q).fullCrossedProductMap_idealSubtypeHom_exact μ hq fun _ =>
    (TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).symm

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (ker q ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` induced by a surjective
equivariant homomorphism `q : Hom α β`. -/
def quotientKerFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q) :
    (FullCrossedProduct α μ) ⧸ (IsInvariant.ker q).idealFullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  (IsInvariant.ker q).quotientIdealFullCrossedProductEquiv μ q hq fun _ =>
    (TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).symm

@[simp]
theorem quotientKerFullCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.quotientKerFullCrossedProductEquiv μ hq
        (TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) x) =
      q.fullCrossedProductMap μ x :=
  (IsInvariant.ker q).quotientIdealFullCrossedProductEquiv_mk μ q hq _ x

@[simp]
theorem quotientKerFullCrossedProductEquiv_comp_mkStarAlgHom (q : Hom α β)
    (hq : Function.Surjective q) :
    (q.quotientKerFullCrossedProductEquiv μ hq).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom
          ((IsInvariant.ker q).idealFullCrossedProductIdeal μ)) =
      q.fullCrossedProductMap μ :=
  (IsInvariant.ker q).quotientIdealFullCrossedProductEquiv_comp_mkStarAlgHom μ q hq _

@[simp]
theorem quotientKerFullCrossedProductEquiv_symm_fullCrossedProductMap
    (q : Hom α β) (hq : Function.Surjective q) (x : FullCrossedProduct α μ) :
    (q.quotientKerFullCrossedProductEquiv μ hq).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) x :=
  (IsInvariant.ker q).quotientIdealFullCrossedProductEquiv_symm_fullCrossedProductMap μ q hq _ x

@[simp]
theorem quotientKerFullCrossedProductEquiv_symm_of_convolutionMap
    (q : Hom α β) (hq : Function.Surjective q) (f : ConvolutionAlgebra α μ) :
    (q.quotientKerFullCrossedProductEquiv μ hq).symm (of β μ (q.convolutionMap μ f)) =
      TwoSidedIdeal.Quotient.mk
        ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) (of α μ f) :=
  (IsInvariant.ker q).quotientIdealFullCrossedProductEquiv_symm_of_convolutionMap μ q hq _ f

@[simp]
theorem quotientKerFullCrossedProductEquiv_symm_comp_fullCrossedProductMap
    (q : Hom α β) (hq : Function.Surjective q) :
    (q.quotientKerFullCrossedProductEquiv μ hq).symm.toNonUnitalStarAlgHom.comp
        (q.fullCrossedProductMap μ) =
      TwoSidedIdeal.Quotient.mkStarAlgHom ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) :=
  (IsInvariant.ker q).quotientIdealFullCrossedProductEquiv_symm_comp_fullCrossedProductMap μ q hq _

end Hom

/-- The kernel of `(α.quotientMkHom I hI).fullCrossedProductMap μ` is
`hI.idealFullCrossedProductIdeal μ`. -/
@[simp]
theorem ker_fullCrossedProductMap_quotientMkHom (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    TwoSidedIdeal.ker ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      hI.idealFullCrossedProductIdeal μ :=
  hI.ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal μ (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) fun a =>
      (α.quotientMkHom_apply I hI a ▸ TwoSidedIdeal.Quotient.eq_zero_iff_mem)

/-- Exactness of `I ⋊_α G → A ⋊_α G → (A ⧸ I) ⋊_α G` for any closed `α`-invariant two-sided ideal
`I`. -/
theorem fullCrossedProductMap_idealSubtypeHom_quotientMkHom_exact (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Exact (hI.idealSubtypeHom.fullCrossedProductMap μ)
      ((α.quotientMkHom I hI).fullCrossedProductMap μ) :=
  hI.fullCrossedProductMap_idealSubtypeHom_exact μ (α.quotientMkHom_surjective I hI) fun a =>
    (α.quotientMkHom_apply I hI a ▸ TwoSidedIdeal.Quotient.eq_zero_iff_mem)

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊_α G` for a closed
`α`-invariant two-sided ideal `I : TwoSidedIdeal A`. -/
def quotientFullCrossedProductEquiv (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (FullCrossedProduct α μ) ⧸ hI.idealFullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct (α.quotient I hI) μ :=
  hI.quotientIdealFullCrossedProductEquiv μ (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) fun a =>
      (α.quotientMkHom_apply I hI a ▸ TwoSidedIdeal.Quotient.eq_zero_iff_mem)

@[simp]
theorem quotientFullCrossedProductEquiv_mk (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (x : FullCrossedProduct α μ) :
    α.quotientFullCrossedProductEquiv μ I hI
        (TwoSidedIdeal.Quotient.mk (hI.idealFullCrossedProductIdeal μ) x) =
      (α.quotientMkHom I hI).fullCrossedProductMap μ x :=
  hI.quotientIdealFullCrossedProductEquiv_mk μ _ _ _ x

@[simp]
theorem quotientFullCrossedProductEquiv_comp_mkStarAlgHom (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (α.quotientFullCrossedProductEquiv μ I hI).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom (hI.idealFullCrossedProductIdeal μ)) =
      (α.quotientMkHom I hI).fullCrossedProductMap μ :=
  hI.quotientIdealFullCrossedProductEquiv_comp_mkStarAlgHom μ _ _ _

@[simp]
theorem quotientFullCrossedProductEquiv_symm_fullCrossedProductMap (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (x : FullCrossedProduct α μ) :
    (α.quotientFullCrossedProductEquiv μ I hI).symm
        ((α.quotientMkHom I hI).fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk (hI.idealFullCrossedProductIdeal μ) x :=
  hI.quotientIdealFullCrossedProductEquiv_symm_fullCrossedProductMap μ _ _ _ x

@[simp]
theorem quotientFullCrossedProductEquiv_symm_of_convolutionMap (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (f : ConvolutionAlgebra α μ) :
    (α.quotientFullCrossedProductEquiv μ I hI).symm
        (of (α.quotient I hI) μ ((α.quotientMkHom I hI).convolutionMap μ f)) =
      TwoSidedIdeal.Quotient.mk (hI.idealFullCrossedProductIdeal μ) (of α μ f) :=
  hI.quotientIdealFullCrossedProductEquiv_symm_of_convolutionMap μ _ _ _ f

@[simp]
theorem quotientFullCrossedProductEquiv_symm_comp_fullCrossedProductMap (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (α.quotientFullCrossedProductEquiv μ I hI).symm.toNonUnitalStarAlgHom.comp
        ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      TwoSidedIdeal.Quotient.mkStarAlgHom (hI.idealFullCrossedProductIdeal μ) :=
  hI.quotientIdealFullCrossedProductEquiv_symm_comp_fullCrossedProductMap μ _ _ _

end TauCeti.CStarAction
