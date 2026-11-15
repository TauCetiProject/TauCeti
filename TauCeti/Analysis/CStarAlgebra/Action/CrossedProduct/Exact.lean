/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Quotient
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Disintegration
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Ideal
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Surjective
import TauCeti.Analysis.CStarAlgebra.Representation.GNS

/-!
# The invariant-ideal short exact sequence of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G` on a C⋆-algebra `A`, and
let `q : Hom α β` be a surjective equivariant `⋆`-homomorphism whose kernel is a closed
`α`-invariant ideal `I` of `A` (in particular, the canonical quotient projection
`α.quotientMkHom I hI : Hom α (α.quotient I hI)` onto `A ⧸ I` for a closed invariant
`I : TwoSidedIdeal A`).

We prove that the induced full crossed-product homomorphisms form a short exact sequence
`0 → I ⋊ G → A ⋊ G → B ⋊ G → 0` (Williams, *Crossed Products of C*-Algebras*, Proposition 3.19):
* `hI.subtypeHom.fullCrossedProductMap μ` is an isometric closed embedding
  (`IsInvariant.isometry_fullCrossedProductMap_subtypeHom`);
* for any locally compact group `G` (even without `T2Space G`), the kernel of
  `q.fullCrossedProductMap μ` equals the embedded range of `hI.subtypeHom.fullCrossedProductMap μ`,
  so `TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
  (IsInvariant.ker q).fullCrossedProductIdeal μ`;
* when `G` is Hausdorff (`[T2Space G]`), `q.fullCrossedProductMap μ` is surjective, yielding the
  full short exact sequence `fullCrossedProductMap_exact` and the canonical isometric
  `⋆`-isomorphisms `(A ⋊_α G) ⧸ (I ⋊ G) ≃⋆ₐ[ℂ] B ⋊_β G` and
  `(A ⋊_α G) ⧸ (I ⋊ G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊ G`.

We also record universal descent of `⋆`-homomorphisms along `q.fullCrossedProductMap μ` and the
boundary cases `I = ⊥` and `I = ⊤`. No unitality, separability, or global σ-finiteness is assumed.

## Main statements

* `TauCeti.CStarAction.fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom` and
  `TauCeti.CStarAction.Hom.ker_fullCrossedProductMap`: middle exactness and two-sided ideal kernel
  identification without `T2Space G`.
* `TauCeti.CStarAction.fullCrossedProductMap_exact` and
  `TauCeti.CStarAction.fullCrossedProductMap_quotientMkHom_exact`: the invariant-ideal short exact
  sequence of full crossed products.
* `TauCeti.CStarAction.Hom.quotientFullCrossedProductEquiv` and
  `TauCeti.CStarAction.quotientFullCrossedProductEquiv`: canonical isometric `⋆`-isomorphisms
  `(A ⋊_α G) ⧸ (ker q ⋊ G) ≃⋆ₐ[ℂ] B ⋊_β G` and `(A ⋊_α G) ⧸ (I ⋊ G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊ G`.
* `TauCeti.CStarAction.fullCrossedProductIdeal_bot` and
  `TauCeti.CStarAction.fullCrossedProductIdeal_top`: boundary specializations at `I = ⊥` and
  `I = ⊤`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19, p. 93.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace TauCeti.CStarAction

universe u v

section MiddleExact

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  (μ : Measure G) [μ.IsHaarMeasure]

/-- If `q : Hom α β` vanishes on a closed invariant `⋆`-subalgebra `I`, the composite of
`q.fullCrossedProductMap μ` with `hI.subtypeHom.fullCrossedProductMap μ` is zero. -/
theorem fullCrossedProductMap_comp_subtypeHom_eq_zero
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hI_le : ∀ a ∈ I, q a = 0) :
    (q.fullCrossedProductMap μ).comp (hI.subtypeHom.fullCrossedProductMap μ) = 0 := by
  rw [← Hom.fullCrossedProductMap_comp]
  refine FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun f => ?_
  simp only [NonUnitalStarAlgHom.comp_apply, Hom.fullCrossedProductMap_of,
    NonUnitalStarAlgHom.zero_apply]
  have hf0 : (q.comp hI.subtypeHom).convolutionMap μ f = 0 := by
    apply ConvolutionAlgebra.ext
    ext s
    simp [hI_le _ (f.ofConv s).2]
  rw [hf0, map_zero]

/-- Pointwise form of `fullCrossedProductMap_comp_subtypeHom_eq_zero`. -/
theorem fullCrossedProductMap_subtypeHom_apply_eq_zero
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hI_le : ∀ a ∈ I, q a = 0) (y : FullCrossedProduct hI.restrict μ) :
    q.fullCrossedProductMap μ (hI.subtypeHom.fullCrossedProductMap μ y) = 0 :=
  DFunLike.congr_fun (fullCrossedProductMap_comp_subtypeHom_eq_zero μ I hI q hI_le) y

/-- If `q : Hom α β` vanishes on a closed invariant two-sided ideal `I`, the composite of
`q.fullCrossedProductMap μ` with `hI.idealSubtypeHom.fullCrossedProductMap μ` is zero. -/
theorem fullCrossedProductMap_comp_idealSubtypeHom_eq_zero
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hI_le : ∀ a ∈ I, q a = 0) :
    (q.fullCrossedProductMap μ).comp (hI.idealSubtypeHom.fullCrossedProductMap μ) = 0 := by
  refine NonUnitalStarAlgHom.ext fun y => ?_
  rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.zero_apply]
  have hy : hI.idealSubtypeHom.fullCrossedProductMap μ y ∈
      (hI.toNonUnitalStarSubalgebra.subtypeHom.fullCrossedProductMap μ).range := by
    rw [← hI.range_fullCrossedProductMap_idealSubtypeHom_eq μ]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hy
  rw [← hz]
  exact fullCrossedProductMap_subtypeHom_apply_eq_zero μ I.toNonUnitalStarSubalgebra
    hI.toNonUnitalStarSubalgebra q
    (fun a ha => hI_le a (I.mem_toNonUnitalStarSubalgebra.mp ha)) z

/-- The quotient crossed-product map vanishes on the embedded ideal crossed product. -/
@[simp]
theorem fullCrossedProductMap_quotientMkHom_comp_idealSubtypeHom
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    ((α.quotientMkHom I hI).fullCrossedProductMap μ).comp
      (hI.idealSubtypeHom.fullCrossedProductMap μ) = 0 :=
  fullCrossedProductMap_comp_idealSubtypeHom_eq_zero μ I hI (α.quotientMkHom I hI) fun _ ha =>
    (α.quotientMkHom_apply I hI _).trans (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr ha)

/-- Middle exactness of full crossed products: for a surjective equivariant homomorphism
`q : Hom α β` whose kernel is a closed invariant `⋆`-subalgebra `I`, an element of `A ⋊_α G` maps
to `0` in `B ⋊_β G` if and only if it lies in the image of `I ⋊ G`. This holds without `T2Space G`.
-/
theorem fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) := by
  refine ⟨fun hx => ?_, ?_⟩
  · -- `I = ker q` is automatically a two-sided ideal of `A`, so its crossed-product image `J` is a
    -- closed two-sided ideal of `FullCrossedProduct α μ`.
    have hmul : ∀ a : A, ∀ y ∈ I, a * y ∈ I := fun a y hy =>
      (hker (a * y)).1 (by rw [map_mul, (hker y).2 hy, mul_zero])
    let J : TwoSidedIdeal (FullCrossedProduct α μ) := hI.fullCrossedProductStarIdeal μ hmul
    have : IsClosed (J : Set (FullCrossedProduct α μ)) :=
      hI.isClosed_fullCrossedProductStarIdeal μ hmul
    rw [← hI.mem_fullCrossedProductStarIdeal μ hmul, ← TwoSidedIdeal.Quotient.eq_zero_iff_mem]
    -- Separate points in the C⋆-quotient `(A ⋊_α G) ⧸ J` by nondegenerate representations,
    -- disintegrate each representation on `A ⋊_α G`, and descend its covariant pair along `q`.
    refine TauCeti.CStarAlgebra.eq_iff_forall_isNondegenerate.2 fun H _ _ _ ρ hρ => ?_
    rw [map_zero]
    let L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
      ρ.comp (TwoSidedIdeal.Quotient.mkStarAlgHom J)
    have hLy (z : FullCrossedProduct α μ) : L z = ρ (TwoSidedIdeal.Quotient.mk J z) := by
      simp [L]
    have hL : L.IsNondegenerate :=
      ρ.isNondegenerate_comp_of_surjective (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective J) hρ
    let P : CovariantRepresentation α H := L.toCovariantRepresentation hL
    have hP_I : ∀ a ∈ I, P.coefficient a = 0 := by
      refine (hI.forall_mem_range_fullCrossedProductMap_subtypeHom_integratedFull_eq_zero_iff μ
        P).1 fun y hy => ?_
      have hyJ : y ∈ J := (hI.mem_fullCrossedProductStarIdeal μ hmul).2 hy
      calc P.integratedFull μ y
          = ρ (TwoSidedIdeal.Quotient.mk J y) := by
              rw [L.integratedFull_toCovariantRepresentation hL, hLy]
        _ = ρ 0 := by rw [TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr hyJ]
        _ = 0 := map_zero ρ
    let Q : CovariantRepresentation β H :=
      P.descend q hq fun a ha => hP_I a ((hker a).1 ha)
    calc ρ (TwoSidedIdeal.Quotient.mk J x)
        = L x := (hLy x).symm
      _ = P.integratedFull μ x := by rw [L.integratedFull_toCovariantRepresentation hL]
      _ = (Q.comap q).integratedFull μ x := by rw [P.comap_descend q hq]
      _ = Q.integratedFull μ (q.fullCrossedProductMap μ x) :=
          (Q.integratedFull_fullCrossedProductMap_apply μ q x).symm
      _ = Q.integratedFull μ 0 := by rw [hx]
      _ = 0 := map_zero _
  · rintro ⟨y, rfl⟩
    exact fullCrossedProductMap_subtypeHom_apply_eq_zero μ I hI q (fun a ha => (hker a).2 ha) y

/-- For a surjective equivariant homomorphism `q : Hom α β`, the two-sided ideal kernel of
`q.fullCrossedProductMap μ` is `(IsInvariant.ker q).fullCrossedProductIdeal μ`. -/
theorem Hom.ker_fullCrossedProductMap (q : Hom α β) (hq : Function.Surjective q) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      (IsInvariant.ker q).fullCrossedProductIdeal μ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, IsInvariant.mem_fullCrossedProductIdeal,
    ← NonUnitalStarAlgHom.coe_range,
    (IsInvariant.ker q).range_fullCrossedProductMap_idealSubtypeHom_eq μ,
    NonUnitalStarAlgHom.coe_range]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom μ
    (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom).toNonUnitalStarSubalgebra
    (IsInvariant.ker q).toNonUnitalStarSubalgebra q hq
    (fun a => by
      rw [TwoSidedIdeal.mem_toNonUnitalStarSubalgebra, TwoSidedIdeal.mem_ker,
        Hom.coe_toNonUnitalStarAlgHom])
    x

/-- For a surjective equivariant homomorphism `q : Hom α β`, an element of `A ⋊_α G` maps to `0` in
`B ⋊_β G` if and only if it lies in the embedded crossed product of `ker q`. -/
theorem Hom.fullCrossedProductMap_eq_zero_iff (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← TwoSidedIdeal.mem_ker, q.ker_fullCrossedProductMap μ hq,
    IsInvariant.mem_fullCrossedProductIdeal]

/-- The two-sided ideal kernel of the full crossed-product quotient homomorphism attached to a
closed invariant ideal `I` is `hI.fullCrossedProductIdeal μ`. -/
@[simp]
theorem ker_fullCrossedProductMap_quotientMkHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    TwoSidedIdeal.ker ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      hI.fullCrossedProductIdeal μ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, IsInvariant.mem_fullCrossedProductIdeal,
    ← NonUnitalStarAlgHom.coe_range,
    hI.range_fullCrossedProductMap_idealSubtypeHom_eq μ,
    NonUnitalStarAlgHom.coe_range]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom μ
    I.toNonUnitalStarSubalgebra hI.toNonUnitalStarSubalgebra
    (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI)
    (fun a => by
      rw [α.quotientMkHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem,
        TwoSidedIdeal.mem_toNonUnitalStarSubalgebra])
    x

/-- An element of `A ⋊_α G` maps to `0` in `(A ⧸ I) ⋊ G` if and only if it lies in the embedded
crossed product of `I`. -/
theorem fullCrossedProductMap_quotientMkHom_eq_zero_iff (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (x : FullCrossedProduct α μ) :
    (α.quotientMkHom I hI).fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← TwoSidedIdeal.mem_ker, ker_fullCrossedProductMap_quotientMkHom,
    IsInvariant.mem_fullCrossedProductIdeal]

end MiddleExact

section ShortExactSequence

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The ideal exact sequence of full crossed products (Williams, Proposition 3.19, p. 93): let
`q : A → B` be a surjective equivariant homomorphism whose kernel is the closed invariant ideal
`I`, so that `B` is the quotient `A/I` with the descended action. Then the induced maps
`I ⋊ G → A ⋊ G → B ⋊ G` form a short exact sequence: the first is injective, the second
surjective, and the kernel of the second is the range of the first. -/
theorem fullCrossedProductMap_exact
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : CStarAction.Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    Function.Injective (hI.subtypeHom.fullCrossedProductMap μ) ∧
      Function.Surjective (q.fullCrossedProductMap μ) ∧
      ∀ x, q.fullCrossedProductMap μ x = 0 ↔
        x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) :=
  ⟨hI.fullCrossedProductMap_subtypeHom_injective μ fun a y hy =>
      (hker (a * y)).1 (by rw [map_mul, (hker y).2 hy, mul_zero]),
    q.surjective_fullCrossedProductMap μ hq.denseRange,
    fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom μ I hI q hq hker⟩

/-- Bundled `TwoSidedIdeal` form of the invariant-ideal short exact sequence
`0 → I ⋊ G → A ⋊ G → (A ⧸ I) ⋊ G → 0` of full crossed products. -/
theorem fullCrossedProductMap_quotientMkHom_exact (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Injective (hI.idealSubtypeHom.fullCrossedProductMap μ) ∧
      Function.Surjective ((α.quotientMkHom I hI).fullCrossedProductMap μ) ∧
      ∀ x, (α.quotientMkHom I hI).fullCrossedProductMap μ x = 0 ↔
        x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  ⟨hI.fullCrossedProductMap_idealSubtypeHom_injective μ,
    surjective_fullCrossedProductMap_quotientMkHom μ α I hI,
    fullCrossedProductMap_quotientMkHom_eq_zero_iff μ I hI⟩

/-- For a surjective equivariant homomorphism `q : Hom α β`, the quotient of
`FullCrossedProduct α μ` by the embedded crossed product of `ker q` is canonically isometrically
`⋆`-isomorphic to `FullCrossedProduct β μ`. -/
def Hom.quotientFullCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q) :
    FullCrossedProduct α μ ⧸ (IsInvariant.ker q).fullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq (q.ker_fullCrossedProductMap μ hq).symm).trans
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (q.surjective_fullCrossedProductMap μ hq.denseRange))

@[simp]
theorem Hom.quotientFullCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.quotientFullCrossedProductEquiv μ hq
      (TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).fullCrossedProductIdeal μ) x) =
      q.fullCrossedProductMap μ x := by
  simp [Hom.quotientFullCrossedProductEquiv]

@[simp]
theorem Hom.quotientFullCrossedProductEquiv_symm_apply (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    (q.quotientFullCrossedProductEquiv μ hq).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).fullCrossedProductIdeal μ) x :=
  (q.quotientFullCrossedProductEquiv μ hq).symm_apply_eq.mpr
    (q.quotientFullCrossedProductEquiv_mk μ hq x).symm

/-- Canonical isometric `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊ G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊ G` for a closed
`α`-invariant two-sided ideal `I` of `A`. -/
def quotientFullCrossedProductEquiv (α : CStarAction G A) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    FullCrossedProduct α μ ⧸ hI.fullCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct (α.quotient I hI) μ :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq
    (ker_fullCrossedProductMap_quotientMkHom μ I hI).symm).trans
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (surjective_fullCrossedProductMap_quotientMkHom μ α I hI))

@[simp]
theorem quotientFullCrossedProductEquiv_mk (α : CStarAction G A) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (x : FullCrossedProduct α μ) :
    quotientFullCrossedProductEquiv μ α I hI
      (TwoSidedIdeal.Quotient.mk (hI.fullCrossedProductIdeal μ) x) =
      (α.quotientMkHom I hI).fullCrossedProductMap μ x := by
  simp [quotientFullCrossedProductEquiv]

@[simp]
theorem quotientFullCrossedProductEquiv_symm_apply (α : CStarAction G A) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (x : FullCrossedProduct α μ) :
    (quotientFullCrossedProductEquiv μ α I hI).symm
      ((α.quotientMkHom I hI).fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk (hI.fullCrossedProductIdeal μ) x :=
  (quotientFullCrossedProductEquiv μ α I hI).symm_apply_eq.mpr
    (quotientFullCrossedProductEquiv_mk μ α I hI x).symm

/-- Universal descent along `q.fullCrossedProductMap μ`: any `⋆`-homomorphism out of
`FullCrossedProduct α μ` that vanishes on the embedded crossed product of `ker q` factors uniquely
through `FullCrossedProduct β μ`. -/
def Hom.liftFullCrossedProduct {D : Type*} [NonUnitalNonAssocSemiring D]
    [DistribMulAction ℂ D] [Star D] (q : Hom α β) (hq : Function.Surjective q)
    (ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] D)
    (hψ : ∀ y, ψ ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ y) = 0) :
    FullCrossedProduct β μ →⋆ₙₐ[ℂ] D :=
  (q.fullCrossedProductMap μ).liftOfSurjective
    (q.surjective_fullCrossedProductMap μ hq.denseRange) ψ <| by
      rw [q.ker_fullCrossedProductMap μ hq]
      intro x hx
      obtain ⟨y, rfl⟩ := (IsInvariant.mem_fullCrossedProductIdeal _ μ).1 hx
      exact (TwoSidedIdeal.mem_ker ψ).2 (hψ y)

@[simp]
theorem Hom.liftFullCrossedProduct_apply {D : Type*} [NonUnitalNonAssocSemiring D]
    [DistribMulAction ℂ D] [Star D] (q : Hom α β) (hq : Function.Surjective q)
    (ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] D)
    (hψ : ∀ y, ψ ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ y) = 0)
    (x : FullCrossedProduct α μ) :
    q.liftFullCrossedProduct μ hq ψ hψ (q.fullCrossedProductMap μ x) = ψ x :=
  (q.fullCrossedProductMap μ).liftOfSurjective_apply _ ψ _ x

@[simp]
theorem Hom.liftFullCrossedProduct_comp {D : Type*} [NonUnitalNonAssocSemiring D]
    [DistribMulAction ℂ D] [Star D] (q : Hom α β) (hq : Function.Surjective q)
    (ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] D)
    (hψ : ∀ y, ψ ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ y) = 0) :
    (q.liftFullCrossedProduct μ hq ψ hψ).comp (q.fullCrossedProductMap μ) = ψ :=
  (q.fullCrossedProductMap μ).liftOfSurjective_comp _ ψ _

/-- Uniqueness of universal descent along `q.fullCrossedProductMap μ`. -/
theorem Hom.eq_liftFullCrossedProduct_iff {D : Type*} [NonUnitalNonAssocSemiring D]
    [DistribMulAction ℂ D] [Star D] {q : Hom α β} (hq : Function.Surjective q)
    {ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] D}
    (hψ : ∀ y, ψ ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ y) = 0)
    {θ : FullCrossedProduct β μ →⋆ₙₐ[ℂ] D} :
    θ = q.liftFullCrossedProduct μ hq ψ hψ ↔ θ.comp (q.fullCrossedProductMap μ) = ψ :=
  (q.fullCrossedProductMap μ).eq_liftOfSurjective_iff _ _

end ShortExactSequence

section BoundaryCases

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) (μ : Measure G) [μ.IsHaarMeasure]

/-- At the zero ideal `⊥`, the embedded crossed-product ideal in `FullCrossedProduct α μ` is `⊥`. -/
@[simp]
theorem fullCrossedProductIdeal_bot :
    (IsInvariant.bot_ideal α).fullCrossedProductIdeal μ = ⊥ := by
  have : Subsingleton (⊥ : TwoSidedIdeal A) :=
    ⟨fun x y =>
      Subtype.ext (((TwoSidedIdeal.mem_bot A).mp x.2).trans
        ((TwoSidedIdeal.mem_bot A).mp y.2).symm)⟩
  ext x
  rw [IsInvariant.mem_fullCrossedProductIdeal, TwoSidedIdeal.mem_bot]
  refine ⟨?_, fun hx => ⟨0, by rw [hx, map_zero]⟩⟩
  rintro ⟨y, rfl⟩
  rw [Subsingleton.elim y 0, map_zero]

/-- At the zero ideal `⊥`, the quotient crossed-product homomorphism
`FullCrossedProduct α μ →⋆ₙₐ[ℂ] FullCrossedProduct (α.quotient ⊥ _) μ` is bijective, without
assuming `T2Space G`. -/
theorem bijective_fullCrossedProductMap_quotientMkHom_bot :
    Function.Bijective ((α.quotientMkHom ⊥ (IsInvariant.bot_ideal α)).fullCrossedProductMap μ) := by
  refine (α.quotientMkHom ⊥ (IsInvariant.bot_ideal α)).bijective_fullCrossedProductMap μ
    ⟨?_, α.quotientMkHom_surjective ⊥ (IsInvariant.bot_ideal α)⟩
  rw [← Hom.coe_toNonUnitalStarAlgHom, ← TwoSidedIdeal.ker_eq_bot]
  exact α.ker_quotientMkHom ⊥ (IsInvariant.bot_ideal α)

/-- At the top ideal `⊤`, the ideal inclusion induces a bijective homomorphism of full crossed
products. -/
theorem bijective_fullCrossedProductMap_idealSubtypeHom_top :
    Function.Bijective (((IsInvariant.top_ideal α).idealSubtypeHom).fullCrossedProductMap μ) :=
  ((IsInvariant.top_ideal α).idealSubtypeHom).bijective_fullCrossedProductMap μ
    ⟨(IsInvariant.top_ideal α).idealSubtypeHom_injective,
      fun a => ⟨⟨a, TwoSidedIdeal.mem_top A⟩,
        (IsInvariant.top_ideal α).idealSubtypeHom_apply ⟨a, TwoSidedIdeal.mem_top A⟩⟩⟩

/-- At the top ideal `⊤`, the embedded crossed-product ideal in `FullCrossedProduct α μ` is `⊤`. -/
@[simp]
theorem fullCrossedProductIdeal_top :
    (IsInvariant.top_ideal α).fullCrossedProductIdeal μ = ⊤ := by
  ext x
  simp only [IsInvariant.mem_fullCrossedProductIdeal, TwoSidedIdeal.mem_top, iff_true]
  exact (bijective_fullCrossedProductMap_idealSubtypeHom_top α μ).surjective x

end BoundaryCases

end TauCeti.CStarAction
