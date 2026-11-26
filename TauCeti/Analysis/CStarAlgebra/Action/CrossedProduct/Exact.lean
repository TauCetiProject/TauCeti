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
# Exactness and quotient isomorphism of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G` on a (possibly nonunital)
C⋆-algebra `A` with left Haar measure `μ`, and let `I` be a closed `α`-invariant two-sided ideal of
`A`. Dana Williams's Proposition 3.19 states that the induced full crossed-product homomorphisms

`0 → I ⋊_α G → A ⋊_α G → (A ⧸ I) ⋊_α G → 0`

form a short exact sequence of C⋆-algebras.

Isometric injectivity on the left
(`TauCeti.CStarAction.Hom.isometry_fullCrossedProductMap_of_injective`,
`IsInvariant.isometry_fullCrossedProductMap_subtypeHom`,
`IsInvariant.isometry_fullCrossedProductMap_idealSubtypeHom`) and surjectivity on the right
(`TauCeti.CStarAction.Hom.surjective_fullCrossedProductMap`) were established separately. Here we
prove exactness in the middle for any right-exact sequence `D --(φ)--> A --(q)--> B → 0` of
`G`-C⋆-algebras (without requiring `φ` to be injective), deduce exactness for the quotient action
`α.quotient I hI`, identify the two-sided ideal kernel of `q.fullCrossedProductMap μ` for any
surjective `q`, and construct the canonical `⋆`-isomorphism
`(A ⋊_α G) ⧸ (ker q ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G`.

None of the results require `T2Space G`, separability, σ-finiteness, or unitality. The resulting
`StarAlgEquiv` between C⋆-algebras is automatically isometric via `StarAlgEquiv.isometry`.

## Main declarations

* `TauCeti.CStarAction.Hom.fullCrossedProductMap_exact` and
  `TauCeti.CStarAction.fullCrossedProductMap_idealSubtypeHom_quotientMkHom_exact`: exactness in the
  middle of full crossed-product sequences (Williams, Proposition 3.19).
* `TauCeti.CStarAction.Hom.ker_fullCrossedProductMap`: two-sided ideal kernel identification for
  surjective induced crossed-product maps.
* `TauCeti.CStarAction.Hom.quotientKerFullCrossedProductEquiv`: canonical `⋆`-isomorphism
  `(A ⋊_α G) ⧸ (ker q ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` for a surjective equivariant `q : Hom α β`.

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
  have hΦ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).IsMultiplierNondegenerate :=
    NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom_comp hψ
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

/-! ### Kernel identification and canonical quotient `⋆`-isomorphism -/

open FullCrossedProduct

/-- For any surjective equivariant homomorphism `q : Hom α β`, the kernel of
`q.fullCrossedProductMap μ` is the embedded crossed product of `ker q`. -/
theorem ker_fullCrossedProductMap (q : Hom α β) (hq : Function.Surjective q) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      (IsInvariant.ker q).idealFullCrossedProductIdeal μ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, ← SetLike.mem_coe,
    (IsInvariant.ker q).coe_idealFullCrossedProductIdeal]
  exact (IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap_exact μ q hq
    (fun a => by simp [TwoSidedIdeal.mem_ker]) x

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (ker q ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` induced by a surjective
equivariant homomorphism `q : Hom α β`. -/
def quotientKerFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q) :
    (FullCrossedProduct α μ) ⧸ (IsInvariant.ker q).idealFullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective
    (q.surjective_fullCrossedProductMap μ hq.denseRange)
    (q.ker_fullCrossedProductMap μ hq)

@[simp]
theorem quotientKerFullCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.quotientKerFullCrossedProductEquiv μ hq
        (TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) x) =
      q.fullCrossedProductMap μ x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_mk _ _ x

@[simp]
theorem quotientKerFullCrossedProductEquiv_comp_mkStarAlgHom (q : Hom α β)
    (hq : Function.Surjective q) :
    (q.quotientKerFullCrossedProductEquiv μ hq).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom
          ((IsInvariant.ker q).idealFullCrossedProductIdeal μ)) =
      q.fullCrossedProductMap μ :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_comp_mkStarAlgHom _ _

@[simp]
theorem quotientKerFullCrossedProductEquiv_symm_fullCrossedProductMap
    (q : Hom α β) (hq : Function.Surjective q) (x : FullCrossedProduct α μ) :
    (q.quotientKerFullCrossedProductEquiv μ hq).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) x :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_apply _ _ x

@[simp]
theorem quotientKerFullCrossedProductEquiv_symm_of_convolutionMap
    (q : Hom α β) (hq : Function.Surjective q) (f : ConvolutionAlgebra α μ) :
    (q.quotientKerFullCrossedProductEquiv μ hq).symm (of β μ (q.convolutionMap μ f)) =
      TwoSidedIdeal.Quotient.mk
        ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) (of α μ f) := by
  rw [← q.fullCrossedProductMap_of μ f,
    q.quotientKerFullCrossedProductEquiv_symm_fullCrossedProductMap μ hq]

@[simp]
theorem quotientKerFullCrossedProductEquiv_symm_comp_fullCrossedProductMap
    (q : Hom α β) (hq : Function.Surjective q) :
    (q.quotientKerFullCrossedProductEquiv μ hq).symm.toNonUnitalStarAlgHom.comp
        (q.fullCrossedProductMap μ) =
      TwoSidedIdeal.Quotient.mkStarAlgHom ((IsInvariant.ker q).idealFullCrossedProductIdeal μ) :=
  NonUnitalStarAlgHom.quotientEquivOfSurjective_symm_comp _ _

end Hom

/-- Exactness of `I ⋊_α G → A ⋊_α G → (A ⧸ I) ⋊_α G` for any closed `α`-invariant two-sided ideal
`I`. -/
theorem fullCrossedProductMap_idealSubtypeHom_quotientMkHom_exact (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Exact (hI.idealSubtypeHom.fullCrossedProductMap μ)
      ((α.quotientMkHom I hI).fullCrossedProductMap μ) :=
  hI.idealSubtypeHom.fullCrossedProductMap_exact μ (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) fun a => by
      simp [TwoSidedIdeal.Quotient.eq_zero_iff_mem]

end ExactSequence

end TauCeti.CStarAction
