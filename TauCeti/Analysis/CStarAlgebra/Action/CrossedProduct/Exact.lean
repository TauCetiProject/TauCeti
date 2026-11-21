/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Quotient
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Ideal
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Surjective
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Universal

/-!
# The invariant-ideal short exact sequence of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G` on a (possibly nonunital)
C⋆-algebra `A` with left Haar measure `μ`, and let `I` be a closed `α`-invariant two-sided ideal of
`A`. Dana Williams's Proposition 3.19 states that the induced full crossed-product homomorphisms

`0 → I ⋊_α G → A ⋊_α G → (A ⧸ I) ⋊_α G → 0`

form a short exact sequence of C⋆-algebras, so `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊_α G`.

Isometric injectivity on the left
(`TauCeti.CStarAction.Hom.isometry_fullCrossedProductMap_of_injective`,
`IsInvariant.isometry_fullCrossedProductMap_subtypeHom`) and surjectivity on the right
(`TauCeti.CStarAction.Hom.surjective_fullCrossedProductMap`) were established separately. Here we
complete the short exact sequence by proving exactness in the middle and constructing the resulting
canonical `⋆`-isomorphisms of quotient full crossed products, for any exact sequence
`0 → D → A → B → 0` of `G`-C⋆-algebras as well as for closed `α`-invariant ideals and the concrete
quotient `α.quotient I hI`.

None of the results require `T2Space G`, separability, σ-finiteness, or unitality. All resulting
`StarAlgEquiv`s between C⋆-algebras are automatically isometric via `StarAlgEquiv.isometry`.

## Main declarations

* `TauCeti.CStarAction.Hom.fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap`,
  `CStarAction.fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap_subtypeHom`,
  `TauCeti.CStarAction.Hom.ker_fullCrossedProductMap`, and
  `TauCeti.CStarAction.ker_fullCrossedProductMap_quotientMkHom`: exactness in the middle and
  two-sided ideal kernel identifications.
* `TauCeti.CStarAction.Hom.fullCrossedProductMap_exact` and
  `TauCeti.CStarAction.fullCrossedProductMap_exact`: the short exact sequence of full crossed
  products (Williams, Proposition 3.19).
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

/-! ### Exactness in the middle, kernel identifications, and the short exact sequence -/

namespace TauCeti.CStarAction

private theorem mul_mem_of_ker {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {α : CStarAction G A} {β : CStarAction G B} {s : Set A}
    (q : Hom α β) (hker : ∀ a, q a = 0 ↔ a ∈ s) (a : A) {x : A} (hx : x ∈ s) : a * x ∈ s :=
  (hker (a * x)).1 <| by rw [map_mul, (hker x).2 hx, mul_zero]

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
      (φ := DoubleCentralizer.coeHom (𝕜 := ℂ)) hψ).1
      NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom
  have hM : ∀ a, q a = 0 →
      (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ).coefficient a =
        0 := by
    intro a ha
    obtain ⟨d, rfl⟩ := hker a ha
    refine (((((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
      ).forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff μ φ).1 ?_) d
    intro y hy
    obtain ⟨z, rfl⟩ := (φ.fullCrossedProductMap μ).mem_range.1 hy
    rw [NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom]
    simp [hψφ z]
  have hN : ((((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
      ).descend q hq hM).integratedFull μ (q.fullCrossedProductMap μ x) =
      ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) x := by simp
  rw [hx, map_zero] at hN
  exact DoubleCentralizer.coe_injective (𝕜 := ℂ) (by simpa using hN.symm)

namespace Hom

/-- Exactness in the middle for full crossed products along a short exact sequence
`0 → D --(φ)--> A --(q)--> B → 0` of `G`-C⋆-algebras. -/
theorem fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap
    {D : Type v} [NonUnitalCStarAlgebra D] {γ : CStarAction G D}
    (φ : Hom γ α) (hφ : Function.Injective φ)
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ Set.range φ)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔ x ∈ Set.range (φ.fullCrossedProductMap μ) := by
  refine ⟨fun hx => ?_, fun ⟨z, hz⟩ => hz ▸
    φ.fullCrossedProductMap_fullCrossedProductMap_eq_zero μ q
      (fun d => (hker (φ d)).2 ⟨d, rfl⟩) z⟩
  have hker' : ∀ a, q a = 0 ↔ a ∈ φ.toNonUnitalStarAlgHom.range := fun a =>
    (hker a).trans (NonUnitalStarAlgHom.mem_range _).symm
  have hmul : ∀ a : A, ∀ y ∈ φ.toNonUnitalStarAlgHom.range,
      a * y ∈ φ.toNonUnitalStarAlgHom.range :=
    fun a _ hy => mul_mem_of_ker q hker' a hy
  let J := (IsInvariant.range φ).fullCrossedProductIdeal μ hmul
  have hmemJ (y : FullCrossedProduct α μ) :
      y ∈ J ↔ y ∈ Set.range (φ.fullCrossedProductMap μ) := by
    rw [(IsInvariant.range φ).mem_fullCrossedProductIdeal μ hmul,
      ← NonUnitalStarAlgHom.coe_range, ← φ.range_fullCrossedProductMap_of_injective μ hφ,
      NonUnitalStarAlgHom.coe_range]
  have hmk : TwoSidedIdeal.Quotient.mkStarAlgHom J x = 0 :=
    map_eq_zero_of_fullCrossedProductMap_eq_zero μ φ q hq (fun a ha => (hker a).1 ha)
      (TwoSidedIdeal.Quotient.mkStarAlgHom J)
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective J).denseRange
      (fun z => (TwoSidedIdeal.Quotient.mkStarAlgHom_apply J _).trans <|
        TwoSidedIdeal.Quotient.eq_zero_iff_mem.2 ((hmemJ _).2 ⟨z, rfl⟩))
      hx
  exact (hmemJ x).1 <| TwoSidedIdeal.Quotient.eq_zero_iff_mem.1 <|
    (TwoSidedIdeal.Quotient.mkStarAlgHom_apply J x).symm.trans hmk

/-- Short exact sequence of full crossed products induced by an arbitrary short exact sequence
`0 → D --(φ)--> A --(q)--> B → 0` of `G`-C⋆-algebras (Williams, Proposition 3.19). -/
theorem fullCrossedProductMap_exact
    {D : Type v} [NonUnitalCStarAlgebra D] {γ : CStarAction G D}
    (φ : Hom γ α) (hφ : Function.Injective φ)
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ Set.range φ) :
    Function.Injective (φ.fullCrossedProductMap μ) ∧
      Function.Surjective (q.fullCrossedProductMap μ) ∧
      ∀ x, q.fullCrossedProductMap μ x = 0 ↔ x ∈ Set.range (φ.fullCrossedProductMap μ) :=
  ⟨φ.fullCrossedProductMap_injective μ hφ
      (fun a d => mul_mem_of_ker q hker a ⟨d, rfl⟩),
    q.surjective_fullCrossedProductMap μ hq.denseRange,
    φ.fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap μ hφ q hq hker⟩

end Hom

/-- Exactness in the middle for full crossed products: if `q : Hom α β` is surjective with kernel
`I`, then `q.fullCrossedProductMap μ` vanishes at `x` precisely when `x` lies in the range of
`hI.subtypeHom.fullCrossedProductMap μ`. -/
theorem fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap_subtypeHom
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) :=
  hI.subtypeHom.fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap μ
    (fun _ _ h => Subtype.ext (by simpa using h)) q hq (fun a => by simp [hker a]) x

/-- For a surjective equivariant `q : Hom α β` with kernel `I : NonUnitalStarSubalgebra ℂ A`, the
two-sided ideal kernel of `q.fullCrossedProductMap μ` is `hI.fullCrossedProductIdeal μ _`. -/
theorem ker_fullCrossedProductMap_eq_fullCrossedProductIdeal
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      hI.fullCrossedProductIdeal μ
        (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero])) := by
  ext x
  rw [TwoSidedIdeal.mem_ker, hI.mem_fullCrossedProductIdeal]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap_subtypeHom
    μ I hI q hq hker x

/-- Exactness in the middle for `I : TwoSidedIdeal A` and a surjective `q : Hom α β` with kernel
`I`. -/
theorem fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap_idealSubtypeHom
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  hI.idealSubtypeHom.fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap μ
    hI.idealSubtypeHom_injective q hq (fun a => by simp [hker a]) x

/-- For a surjective `q : Hom α β` with kernel `I : TwoSidedIdeal A`, the two-sided ideal kernel of
`q.fullCrossedProductMap μ` is `hI.idealFullCrossedProductIdeal μ`. -/
theorem ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) = hI.idealFullCrossedProductIdeal μ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, hI.mem_idealFullCrossedProductIdeal μ]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_fullCrossedProductMap_idealSubtypeHom
    μ I hI q hq hker x

namespace Hom

/-- For any surjective equivariant homomorphism `q : Hom α β`, the kernel of
`q.fullCrossedProductMap μ` is the embedded crossed product of `ker q`. -/
theorem ker_fullCrossedProductMap (q : Hom α β) (hq : Function.Surjective q) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      (IsInvariant.ker q).idealFullCrossedProductIdeal μ :=
  ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal μ
    (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom) (IsInvariant.ker q) q hq fun _ =>
      (TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).symm

/-- Pointwise kernel characterization of `q.fullCrossedProductMap μ` for surjective `q : Hom α β`.
-/
theorem fullCrossedProductMap_eq_zero_iff (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← TwoSidedIdeal.mem_ker, q.ker_fullCrossedProductMap μ hq,
    IsInvariant.mem_idealFullCrossedProductIdeal]

end Hom

/-- The kernel of `(α.quotientMkHom I hI).fullCrossedProductMap μ` is
`hI.idealFullCrossedProductIdeal μ`. -/
@[simp]
theorem ker_fullCrossedProductMap_quotientMkHom (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    TwoSidedIdeal.ker ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      hI.idealFullCrossedProductIdeal μ :=
  ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal μ I hI (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) fun a =>
      (α.quotientMkHom_apply I hI a ▸ TwoSidedIdeal.Quotient.eq_zero_iff_mem)

/-- `(α.quotientMkHom I hI).fullCrossedProductMap μ x = 0` precisely when `x` lies in the range of
`hI.idealSubtypeHom.fullCrossedProductMap μ`. -/
theorem fullCrossedProductMap_quotientMkHom_eq_zero_iff (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (x : FullCrossedProduct α μ) :
    (α.quotientMkHom I hI).fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← TwoSidedIdeal.mem_ker, α.ker_fullCrossedProductMap_quotientMkHom μ I hI,
    hI.mem_idealFullCrossedProductIdeal μ]

/-- The invariant-ideal short exact sequence of full crossed products (Williams, Proposition 3.19):
if `q : Hom α β` is surjective with kernel the closed `α`-invariant ideal `I`, then the induced
homomorphisms `I ⋊ G → A ⋊ G → B ⋊ G` are injective on the left, surjective on the right, and
exact in the middle. -/
theorem fullCrossedProductMap_exact
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    Function.Injective (hI.subtypeHom.fullCrossedProductMap μ) ∧
      Function.Surjective (q.fullCrossedProductMap μ) ∧
      ∀ x, q.fullCrossedProductMap μ x = 0 ↔
        x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) :=
  hI.subtypeHom.fullCrossedProductMap_exact μ
    (fun _ _ h => Subtype.ext (by simpa using h)) q hq fun a => by simp [hker a]

end ExactSequence

end TauCeti.CStarAction

/-! ### Canonical quotient `⋆`-isomorphisms of full crossed products -/

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

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` associated to a surjective
equivariant homomorphism `q : Hom α β` with kernel `I : NonUnitalStarSubalgebra ℂ A`. -/
def quotientFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (FullCrossedProduct α μ) ⧸
        hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero])) ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective
    (q.surjective_fullCrossedProductMap μ hq.denseRange)
    (ker_fullCrossedProductMap_eq_fullCrossedProductIdeal μ I hI q hq hker)

@[simp]
theorem quotientFullCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) (x : FullCrossedProduct α μ) :
    hI.quotientFullCrossedProductEquiv μ q hq hker
        (TwoSidedIdeal.Quotient.mk
          (hI.fullCrossedProductIdeal μ
            (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero]))) x) =
      q.fullCrossedProductMap μ x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_mk _ _ x

@[simp]
theorem quotientFullCrossedProductEquiv_comp_mkStarAlgHom (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom
          (hI.fullCrossedProductIdeal μ
            (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero])))) =
      q.fullCrossedProductMap μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_comp_mkStarAlgHom _ _

@[simp]
theorem quotientFullCrossedProductEquiv_symm_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) (x : FullCrossedProduct α μ) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk
        (hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero]))) x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_apply _ _ x

@[simp]
theorem quotientFullCrossedProductEquiv_symm_of_convolutionMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (f : ConvolutionAlgebra α μ) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).symm (of β μ (q.convolutionMap μ f)) =
      TwoSidedIdeal.Quotient.mk
        (hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero]))) (of α μ f) := by
  rw [← q.fullCrossedProductMap_of μ f,
    hI.quotientFullCrossedProductEquiv_symm_fullCrossedProductMap]

@[simp]
theorem quotientFullCrossedProductEquiv_symm_comp_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (hI.quotientFullCrossedProductEquiv μ q hq hker).symm.toNonUnitalStarAlgHom.comp
        (q.fullCrossedProductMap μ) =
      TwoSidedIdeal.Quotient.mkStarAlgHom
        (hI.fullCrossedProductIdeal μ
          (fun a _ hx => (hker _).1 (by rw [map_mul, (hker _).2 hx, mul_zero]))) :=
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

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` associated to a surjective
equivariant homomorphism `q : Hom α β` with kernel `I : TwoSidedIdeal A`. -/
def quotientIdealFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    (FullCrossedProduct α μ) ⧸ hI.idealFullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective
    (q.surjective_fullCrossedProductMap μ hq.denseRange)
    (ker_fullCrossedProductMap_eq_idealFullCrossedProductIdeal μ I hI q hq hker)

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
