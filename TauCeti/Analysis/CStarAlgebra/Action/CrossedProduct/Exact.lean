/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Quotient
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Disintegration
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Ideal
public import TauCeti.Analysis.CStarAlgebra.Representation.GNS

/-!
# Exactness of the ideal sequence of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G` on a C⋆-algebra `A`,
let `I` be a closed `α`-invariant star subalgebra of `A`, and let `q : Hom α β` be a surjective
equivariant homomorphism whose kernel is `I`, for instance the projection onto the quotient
`A ⧸ I` with its descended action. The induced maps of full crossed products

`I ⋊ G → A ⋊ G → B ⋊ G`

are exact in the middle: the kernel of `q.fullCrossedProductMap μ` is the range of
`hI.subtypeHom.fullCrossedProductMap μ`. Together with injectivity of the first map,
`IsInvariant.fullCrossedProductMap_subtypeHom_injective`, and surjectivity of the second,
`Hom.surjective_fullCrossedProductMap`, this is the short exact sequence
`0 → I ⋊ G → A ⋊ G → B ⋊ G → 0`.

The range `J` of the first map is a closed two-sided ideal of `A ⋊ G`. A faithful nondegenerate
representation of the C⋆-quotient `(A ⋊ G) ⧸ J` (Gelfand–Naimark) pulls back to a nondegenerate
representation of `A ⋊ G` vanishing on `J`. That representation is the integrated form of a
covariant pair whose coefficient representation vanishes on `I`, so the pair descends along `q`
and the representation factors through `q.fullCrossedProductMap μ`.

No unitality, separability or global σ-finiteness is assumed.

## Main statements

* `TauCeti.CStarAction.Hom.fullCrossedProductMap_exact`: exactness of the full crossed-product
  maps induced by the inclusion of `I` and by `q`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
-/

public section

noncomputable section

open MeasureTheory TauCeti.CStarAction.FullCrossedProduct
open scoped CStarAlgebra

namespace TauCeti.CStarAction.Hom

universe u v

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B} (μ : Measure G) [μ.IsHaarMeasure]
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  {q : Hom α β} (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)

/-- The composite `I ⋊ G → A ⋊ G → B ⋊ G` vanishes when `q` vanishes on `I`. -/
private theorem fullCrossedProductMap_subtypeHom_eq_zero (h : ∀ a ∈ I, q a = 0)
    (y : FullCrossedProduct hI.restrict μ) :
    q.fullCrossedProductMap μ (hI.subtypeHom.fullCrossedProductMap μ y) = 0 := by
  induction y using FullCrossedProduct.induction_on with
  | hp =>
    exact isClosed_eq ((map_continuous _).comp (map_continuous _)) continuous_const
  | ih f =>
    have hf : q.convolutionMap μ (hI.subtypeHom.convolutionMap μ f) = 0 := by
      apply CompactlySupportedL1.ext
      ext s
      simp [h _ (f.ofConv s).property]
    rw [fullCrossedProductMap_of, fullCrossedProductMap_of, hf, map_zero]

include hq hker in
/-- **Exactness of the ideal sequence of full crossed products.** For a surjective equivariant
homomorphism `q` with kernel the closed invariant subalgebra `I`, the kernel of the induced map
`A ⋊ G → B ⋊ G` is the range of the map `I ⋊ G → A ⋊ G` induced by the inclusion. -/
theorem fullCrossedProductMap_exact :
    Function.Exact (hI.subtypeHom.fullCrossedProductMap μ) (q.fullCrossedProductMap μ) := by
  refine fun x => ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸
    fullCrossedProductMap_subtypeHom_eq_zero μ hI (fun a ha => (hker a).2 ha) y⟩
  -- The range of `I ⋊ G` is a closed two-sided ideal `J` of `A ⋊ G`.
  have hmul (a : A) (y : A) (hy : y ∈ I) : a * y ∈ I :=
    (hker _).1 (by rw [map_mul, (hker y).2 hy, mul_zero])
  let J := hI.fullCrossedProductIdeal μ hmul
  -- Represent `(A ⋊ G) ⧸ J` faithfully and pull the representation back to `A ⋊ G`.
  obtain ⟨H, _, _, _, L, hLinj, hLnd⟩ :=
    TauCeti.CStarAlgebra.exists_faithful_nondegenerate_representation
      (FullCrossedProduct α μ ⧸ J)
  let L' := L.comp (TwoSidedIdeal.Quotient.mkStarAlgHom J)
  have hL' : L'.IsNondegenerate :=
    (NonUnitalStarAlgHom.isNondegenerate_comp_iff
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective J).denseRange).2 hLnd
  -- `L'` integrates a covariant pair whose coefficient representation vanishes on `I`.
  let P := L'.toCovariantRepresentation hL'
  have hP : P.integratedFull μ = L' := L'.integratedFull_toCovariantRepresentation hL'
  have hPq (a : A) (ha : q a = 0) : P.coefficient a = 0 := by
    refine (hI.forall_mem_range_fullCrossedProductMap_subtypeHom_integratedFull_eq_zero_iff
      μ P).1 (fun y hy => ?_) a ((hker a).1 ha)
    rw [hP, NonUnitalStarAlgHom.comp_apply, TwoSidedIdeal.Quotient.mkStarAlgHom_apply,
      TwoSidedIdeal.Quotient.eq_zero_iff_mem.2 ((hI.mem_fullCrossedProductIdeal μ hmul).2 hy),
      map_zero]
  -- The pair descends along `q`, so `L'` factors through `q.fullCrossedProductMap μ`.
  have hLx : L' x = 0 := by
    rw [← hP, ← P.comap_descend q hq hPq,
      ← CovariantRepresentation.integratedFull_fullCrossedProductMap_apply, hx, map_zero]
  have hmk : TwoSidedIdeal.Quotient.mk J x = 0 :=
    hLinj (by simpa only [L', NonUnitalStarAlgHom.comp_apply,
      TwoSidedIdeal.Quotient.mkStarAlgHom_apply, map_zero] using hLx)
  exact (hI.mem_fullCrossedProductIdeal μ hmul).1 (TwoSidedIdeal.Quotient.eq_zero_iff_mem.1 hmk)

end TauCeti.CStarAction.Hom
