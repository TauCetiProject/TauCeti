/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.Algebra.Homology.SpectralSequence.Stabilization
public import TauCeti.CategoryTheory.Subobject.Limits
import Mathlib.Order.Bounds.OrderIso

/-!
# The limit page of a spectral sequence

Given a spectral sequence `E : SpectralSequence C c r₀` in an abelian category `C`, the cycle
tower `r ↦ Z_r(pq)` and boundary tower `r ↦ B_r(pq)` at a position `pq : κ` satisfy
`B_r(pq) ≤ Z_{r'}(pq)` for all `r, r' ≥ r₀`
(`CategoryTheory.SpectralSequence.boundariesSubobject_le_cyclesSubobject_of_le`).

This module defines:

* `CategoryTheory.SpectralSequence.HasInfCyclesAt`,
  `CategoryTheory.SpectralSequence.HasInfBoundariesAt`, and
  `CategoryTheory.SpectralSequence.HasLimitPageAt`: existence of the greatest lower bound `Z_∞(pq)`
  of the cycle tower, the least upper bound `B_∞(pq)` of the boundary tower, and both together.
* `CategoryTheory.SpectralSequence.infCyclesSubobject`,
  `CategoryTheory.SpectralSequence.infBoundariesSubobject`,
  `CategoryTheory.SpectralSequence.limitPage`, and
  `CategoryTheory.SpectralSequence.limitPagePresentation`: the infinite cycles `Z_∞(pq)`, infinite
  boundaries `B_∞(pq)`, limit page `E_∞(pq) := Z_∞(pq) / B_∞(pq)`, and its tautological
  subquotient presentation inside `(E.page r₀).X pq`.
* Existence without limit hypotheses on `C` at regular, coregular, stabilizing, or vanishing
  positions (`hasInfCyclesAt_of_isRegularAt`, `hasInfBoundariesAt_of_isCoregularAt`,
  `hasLimitPageAt_of_stabilizesAt`, `hasLimitPageAt_of_isZero_page_X`), together with the
  canonical isomorphism `limitPageIsoOfStabilizesAt : E.limitPage pq ≅ (E.page s h.le).X pq`
  compatible with `pageXIsoOfStabilizesAt`.
* Existence in general from countable products and countable coproducts in `C`
  (`hasInfCyclesAt_of_hasCountableProducts`, `hasInfBoundariesAt_of_hasCountableCoproducts`,
  `hasLimitPageAt_of_hasCountableProducts_hasCountableCoproducts`), realized via
  `Subobject.iInfCokernel` and `Subobject.iSupImage`.
* Functoriality (`Hom.limitPageMap`, `limitPageIsoOfIso`, `limitPageFunctor`) and agreement with
  page components at stabilizing positions (`Hom.limitPageMap_comp_limitPageIsoOfStabilizesAt_hom`).
* Rebasing (`hasLimitPageAt_fromPage_iff`, `limitPageFromPageIso`, and
  `limitPageFromPageIso_hom_naturality`): computing the limit page from the towers started at any
  page `s ≥ r₀` yields a canonically isomorphic object.
* Vanishing (`isZero_limitPage_of_isZero_page_X`): if `(E.page r hr).X pq` is zero for some `r` and
  the limit page exists, then `E.limitPage pq` is zero.

## References

* Stacks Project, Tag 011O (Definition 20.2).
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for spectral sequences*,
  Definition 2.3 (2024).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.SpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Defs

variable (E : SpectralSequence C c r₀)

/-- `E` has infinite cycles at `pq` if the cycle tower `{Z_r(pq) | r ≥ r₀}` admits a greatest
lower bound in `Subobject ((E.page r₀).X pq)`. -/
class HasInfCyclesAt (pq : κ) : Prop where
  exists_isGLB :
    ∃ Z : Subobject ((E.page r₀).X pq),
      IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z

/-- `E` has infinite boundaries at `pq` if the boundary tower `{B_r(pq) | r ≥ r₀}` admits a least
upper bound in `Subobject ((E.page r₀).X pq)`. -/
class HasInfBoundariesAt (pq : κ) : Prop where
  exists_isLUB :
    ∃ B : Subobject ((E.page r₀).X pq),
      IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) B

/-- `E` has a limit page at `pq` if both the infinite cycles `Z_∞(pq)` and the infinite boundaries
`B_∞(pq)` exist in `Subobject ((E.page r₀).X pq)`. -/
class HasLimitPageAt (pq : κ) : Prop extends E.HasInfCyclesAt pq, E.HasInfBoundariesAt pq

/-- The infinite cycle subobject `Z_∞(pq)` of `(E.page r₀).X pq`, defined as the greatest lower
bound of the cycle tower `{Z_r(pq) | r ≥ r₀}`. -/
noncomputable def infCyclesSubobject (pq : κ) [E.HasInfCyclesAt pq] :
    Subobject ((E.page r₀).X pq) :=
  HasInfCyclesAt.exists_isGLB.choose

/-- `E.infCyclesSubobject pq` is the greatest lower bound of the cycle tower at `pq`. -/
lemma isGLB_infCyclesSubobject (pq : κ) [E.HasInfCyclesAt pq] :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (E.infCyclesSubobject pq) :=
  HasInfCyclesAt.exists_isGLB.choose_spec

lemma infCyclesSubobject_le (pq : κ) [E.HasInfCyclesAt pq] (r : ℤ) (hr : r₀ ≤ r) :
    E.infCyclesSubobject pq ≤ E.cyclesSubobject pq r hr :=
  (E.isGLB_infCyclesSubobject pq).1 ⟨⟨r, hr⟩, rfl⟩

lemma le_infCyclesSubobject {pq : κ} [E.HasInfCyclesAt pq] {W : Subobject ((E.page r₀).X pq)}
    (hW : ∀ r (hr : r₀ ≤ r), W ≤ E.cyclesSubobject pq r hr) :
    W ≤ E.infCyclesSubobject pq :=
  (E.isGLB_infCyclesSubobject pq).2 (by rintro _ ⟨⟨r, hr⟩, rfl⟩; exact hW r hr)

lemma infCyclesSubobject_eq_of_isGLB {pq : κ} [E.HasInfCyclesAt pq]
    {Z : Subobject ((E.page r₀).X pq)}
    (hZ : IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z) :
    E.infCyclesSubobject pq = Z :=
  (E.isGLB_infCyclesSubobject pq).unique hZ

/-- The infinite boundary subobject `B_∞(pq)` of `(E.page r₀).X pq`, defined as the least upper
bound of the boundary tower `{B_r(pq) | r ≥ r₀}`. -/
noncomputable def infBoundariesSubobject (pq : κ) [E.HasInfBoundariesAt pq] :
    Subobject ((E.page r₀).X pq) :=
  HasInfBoundariesAt.exists_isLUB.choose

/-- `E.infBoundariesSubobject pq` is the least upper bound of the boundary tower at `pq`. -/
lemma isLUB_infBoundariesSubobject (pq : κ) [E.HasInfBoundariesAt pq] :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (E.infBoundariesSubobject pq) :=
  HasInfBoundariesAt.exists_isLUB.choose_spec

lemma le_infBoundariesSubobject (pq : κ) [E.HasInfBoundariesAt pq] (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.infBoundariesSubobject pq :=
  (E.isLUB_infBoundariesSubobject pq).1 ⟨⟨r, hr⟩, rfl⟩

lemma infBoundariesSubobject_le {pq : κ} [E.HasInfBoundariesAt pq]
    {W : Subobject ((E.page r₀).X pq)}
    (hW : ∀ r (hr : r₀ ≤ r), E.boundariesSubobject pq r hr ≤ W) :
    E.infBoundariesSubobject pq ≤ W :=
  (E.isLUB_infBoundariesSubobject pq).2 (by rintro _ ⟨⟨r, hr⟩, rfl⟩; exact hW r hr)

lemma infBoundariesSubobject_eq_of_isLUB {pq : κ} [E.HasInfBoundariesAt pq]
    {B : Subobject ((E.page r₀).X pq)}
    (hB : IsLUB
      (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) B) :
    E.infBoundariesSubobject pq = B :=
  (E.isLUB_infBoundariesSubobject pq).unique hB

/-- Every infinite boundary is an infinite cycle: `B_∞(pq) ≤ Z_∞(pq)`. -/
lemma infBoundariesSubobject_le_infCyclesSubobject (pq : κ)
    [E.HasInfBoundariesAt pq] [E.HasInfCyclesAt pq] :
    E.infBoundariesSubobject pq ≤ E.infCyclesSubobject pq :=
  E.infBoundariesSubobject_le fun r hr ↦
    E.le_infCyclesSubobject fun r' hr' ↦
      E.boundariesSubobject_le_cyclesSubobject_of_le pq r r' hr hr'

/-- The limit page object `E_∞(pq)` at position `pq`, defined as the quotient `Z_∞(pq) / B_∞(pq)`
(the cokernel of `Subobject.ofLE (E.infBoundariesSubobject pq) (E.infCyclesSubobject pq) _`). -/
@[expose]
noncomputable def limitPage (pq : κ) [E.HasLimitPageAt pq] : C :=
  cokernel (Subobject.ofLE (E.infBoundariesSubobject pq) (E.infCyclesSubobject pq)
    (E.infBoundariesSubobject_le_infCyclesSubobject pq))

/-- The canonical subquotient presentation of `E.limitPage pq` inside `(E.page r₀).X pq`, with
bottom `B_∞(pq)` and top `Z_∞(pq)`. -/
noncomputable abbrev limitPagePresentation (pq : κ) [E.HasLimitPageAt pq] :
    TauCeti.SubquotientPresentation ((E.page r₀).X pq) (E.limitPage pq) :=
  TauCeti.SubquotientPresentation.quotient (E.infBoundariesSubobject pq)
    (E.infCyclesSubobject pq) (E.infBoundariesSubobject_le_infCyclesSubobject pq)

end Defs

section Stabilized

variable (E : SpectralSequence C c r₀)

/-- If the cycle tower at `pq` is constant from page `s` onward, then `Z_s(pq)` is its greatest
lower bound. -/
lemma isGLB_cyclesSubobject_of_eventually_eq {pq : κ} {s : ℤ} (hs : r₀ ≤ s)
    (hconst : ∀ r (hsr : s ≤ r),
      E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (E.cyclesSubobject pq s hs) := by
  refine ⟨?_, fun W hW ↦ hW ⟨⟨s, hs⟩, rfl⟩⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  have heq : E.cyclesSubobject pq (max s r) (hs.trans (le_max_left s r)) =
      E.cyclesSubobject pq s hs := hconst (max s r) (le_max_left s r)
  exact heq.symm.le.trans (E.cyclesSubobject_le_of_le pq hr (le_max_right s r))

/-- If the boundary tower at `pq` is constant from page `s` onward, then `B_s(pq)` is its least
upper bound. -/
lemma isLUB_boundariesSubobject_of_eventually_eq {pq : κ} {s : ℤ} (hs : r₀ ≤ s)
    (hconst : ∀ r (hsr : s ≤ r),
      E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (E.boundariesSubobject pq s hs) := by
  refine ⟨?_, fun W hW ↦ hW ⟨⟨s, hs⟩, rfl⟩⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  have heq : E.boundariesSubobject pq (max s r) (hs.trans (le_max_left s r)) =
      E.boundariesSubobject pq s hs := hconst (max s r) (le_max_left s r)
  exact (E.boundariesSubobject_le_of_le pq hr (le_max_right s r)).trans heq.le

/-- A spectral sequence that is regular at `pq` has infinite cycles at `pq`, with no limit
hypotheses on `C`. -/
lemma hasInfCyclesAt_of_isRegularAt {pq : κ} (h : E.IsRegularAt pq) : E.HasInfCyclesAt pq := by
  obtain ⟨s, hs, hconst⟩ := (E.isRegularAt_iff_eventually_cyclesSubobject_eq pq).1 h
  exact ⟨E.cyclesSubobject pq s hs, E.isGLB_cyclesSubobject_of_eventually_eq hs hconst⟩

/-- A spectral sequence that is coregular at `pq` has infinite boundaries at `pq`, with no colimit
hypotheses on `C`. -/
lemma hasInfBoundariesAt_of_isCoregularAt {pq : κ} (h : E.IsCoregularAt pq) :
    E.HasInfBoundariesAt pq := by
  obtain ⟨s, hs, hconst⟩ := (E.isCoregularAt_iff_eventually_boundariesSubobject_eq pq).1 h
  exact ⟨E.boundariesSubobject pq s hs, E.isLUB_boundariesSubobject_of_eventually_eq hs hconst⟩

/-- A spectral sequence that stabilizes at `pq` from some page `s` has a limit page at `pq`, with
no limit or colimit hypotheses on `C`. -/
lemma hasLimitPageAt_of_stabilizesAt {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) :
    E.HasLimitPageAt pq where
  toHasInfCyclesAt := E.hasInfCyclesAt_of_isRegularAt h.isRegularAt
  toHasInfBoundariesAt := E.hasInfBoundariesAt_of_isCoregularAt h.isCoregularAt

/-- If `E` stabilizes at `pq` from page `s`, then `Z_∞(pq) = Z_s(pq)`. -/
lemma infCyclesSubobject_eq_of_stabilizesAt {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s)
    [E.HasInfCyclesAt pq] :
    E.infCyclesSubobject pq = E.cyclesSubobject pq s h.le :=
  E.infCyclesSubobject_eq_of_isGLB
    (E.isGLB_cyclesSubobject_of_eventually_eq h.le fun r hsr ↦ h.cyclesSubobject_eq r hsr)

/-- If `E` stabilizes at `pq` from page `s`, then `B_∞(pq) = B_s(pq)`. -/
lemma infBoundariesSubobject_eq_of_stabilizesAt {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s)
    [E.HasInfBoundariesAt pq] :
    E.infBoundariesSubobject pq = E.boundariesSubobject pq s h.le :=
  E.infBoundariesSubobject_eq_of_isLUB
    (E.isLUB_boundariesSubobject_of_eventually_eq h.le fun r hsr ↦ h.boundariesSubobject_eq r hsr)

/-- **Stabilized limit isomorphism.** If `E` stabilizes at `pq` from page `s`, then `E.limitPage pq`
is canonically isomorphic to `(E.page s h.le).X pq`. -/
noncomputable def limitPageIsoOfStabilizesAt {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s)
    [E.HasLimitPageAt pq] :
    E.limitPage pq ≅ (E.page s h.le).X pq :=
  TauCeti.SubquotientPresentation.isoOfEq
    (P := E.limitPagePresentation pq)
    (P' := E.pagePresentation pq s h.le)
    (E.infBoundariesSubobject_eq_of_stabilizesAt h)
    (E.infCyclesSubobject_eq_of_stabilizesAt h)

/-- Compatibility of `limitPageIsoOfStabilizesAt` with the subquotient presentation
projections. -/
@[reassoc]
lemma π_comp_limitPageIsoOfStabilizesAt_hom {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s)
    [E.HasLimitPageAt pq] :
    (E.limitPagePresentation pq).π ≫ (E.limitPageIsoOfStabilizesAt h).hom =
      Subobject.ofLE (E.infCyclesSubobject pq) (E.cyclesSubobject pq s h.le)
          (E.infCyclesSubobject_eq_of_stabilizesAt h).le ≫
        (E.pagePresentation pq s h.le).π :=
  TauCeti.SubquotientPresentation.π_isoOfEq_hom _ _ _ _

/-- **Compatibility with stabilization isomorphisms.** Composing `limitPageIsoOfStabilizesAt` at
page `s` with the stabilization isomorphism `pageXIsoOfStabilizesAt` from `s` to `r ≥ s` yields
`limitPageIsoOfStabilizesAt` at page `r`. -/
theorem limitPageIsoOfStabilizesAt_trans_pageXIsoOfStabilizesAt {pq : κ} {s r : ℤ}
    (h : E.StabilizesAt pq s) (hsr : s ≤ r) [E.HasLimitPageAt pq] :
    E.limitPageIsoOfStabilizesAt h ≪≫ E.pageXIsoOfStabilizesAt h r hsr =
      E.limitPageIsoOfStabilizesAt (h.mono hsr) := by
  rw [limitPageIsoOfStabilizesAt, pageXIsoOfStabilizesAt_eq_isoOfEq, limitPageIsoOfStabilizesAt]
  exact TauCeti.SubquotientPresentation.isoOfEq_trans _ _ _ _

/-- If `(E.page r hr).X pq` is zero for some `r ≥ r₀`, then `E` stabilizes at `pq` from page `r`,
so `E` has a limit page at `pq` without limit hypotheses on `C`. -/
lemma hasLimitPageAt_of_isZero_page_X (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (hzero : IsZero ((E.page r hr).X pq)) :
    E.HasLimitPageAt pq :=
  E.hasLimitPageAt_of_stabilizesAt (E.stabilizesAt_of_isZero_page_X hr hzero)

/-- **Vanishing of the limit page.** If `(E.page r hr).X pq` is zero for some `r ≥ r₀` and the
limit page exists at `pq`, then `E.limitPage pq` is zero. -/
theorem isZero_limitPage_of_isZero_page_X (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    [E.HasLimitPageAt pq] (hzero : IsZero ((E.page r hr).X pq)) :
    IsZero (E.limitPage pq) :=
  hzero.of_iso (E.limitPageIsoOfStabilizesAt (E.stabilizesAt_of_isZero_page_X hr hzero))

end Stabilized

section CountableLimits

variable (E : SpectralSequence C c r₀)

/-- If `C` has countable products, every spectral sequence has infinite cycles at every position. -/
instance hasInfCyclesAt_of_hasCountableProducts [HasCountableProducts C] (pq : κ) :
    E.HasInfCyclesAt pq :=
  ⟨Subobject.iInfCokernel (fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property),
    Subobject.isGLB_iInfCokernel _⟩

/-- When `C` has countable products, `Z_∞(pq)` is the kernel subobject of the map from
`(E.page r₀).X pq` to the product of the cokernels of the `Z_r(pq)`. -/
lemma infCyclesSubobject_eq_iInfCokernel [HasCountableProducts C] (pq : κ) :
    E.infCyclesSubobject pq =
      Subobject.iInfCokernel (fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) :=
  E.infCyclesSubobject_eq_of_isGLB (Subobject.isGLB_iInfCokernel _)

/-- If `C` has countable coproducts, every spectral sequence has infinite boundaries at every
position. -/
instance hasInfBoundariesAt_of_hasCountableCoproducts [HasCountableCoproducts C] (pq : κ) :
    E.HasInfBoundariesAt pq :=
  ⟨Subobject.iSupImage (fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property),
    Subobject.isLUB_iSupImage _⟩

/-- When `C` has countable coproducts, `B_∞(pq)` is the image subobject of the map from the
coproduct of the `B_r(pq)` into `(E.page r₀).X pq`. -/
lemma infBoundariesSubobject_eq_iSupImage [HasCountableCoproducts C] (pq : κ) :
    E.infBoundariesSubobject pq =
      Subobject.iSupImage (fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) :=
  E.infBoundariesSubobject_eq_of_isLUB (Subobject.isLUB_iSupImage _)

/-- If `C` has countable products and countable coproducts, every spectral sequence has a limit
page at every position. -/
instance hasLimitPageAt_of_hasCountableProducts_hasCountableCoproducts
    [HasCountableProducts C] [HasCountableCoproducts C] (pq : κ) :
    E.HasLimitPageAt pq := {}

end CountableLimits

section Functoriality

variable {E E' E'' : SpectralSequence C c r₀}

/-- A morphism of spectral sequences carries `Z_∞(E, pq)` into `Z_∞(E', pq)` (via pullback). -/
lemma Hom.infCyclesSubobject_le_pullback (f : E ⟶ E') (pq : κ)
    [E.HasInfCyclesAt pq] [E'.HasInfCyclesAt pq] :
    E.infCyclesSubobject pq ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.infCyclesSubobject pq) := by
  have hgc := (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc
  refine (hgc _ _).1 (E'.le_infCyclesSubobject fun r hr ↦ ?_)
  exact (hgc _ _).2
    ((E.infCyclesSubobject_le pq r hr).trans (f.cyclesSubobject_le_pullback pq r hr))

/-- A morphism of spectral sequences carries `B_∞(E, pq)` into `B_∞(E', pq)` (via direct image). -/
lemma Hom.exists_infBoundariesSubobject_le (f : E ⟶ E') (pq : κ)
    [E.HasInfBoundariesAt pq] [E'.HasInfBoundariesAt pq] :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.infBoundariesSubobject pq) ≤
      E'.infBoundariesSubobject pq := by
  have hgc := (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc
  refine (hgc _ _).2 (E.infBoundariesSubobject_le fun r hr ↦ ?_)
  exact ((hgc _ _).1 (f.exists_boundariesSubobject_le pq r hr)).trans
    (hgc.monotone_u (E'.le_infBoundariesSubobject pq r hr))

/-- A morphism of spectral sequences carries `Z_∞(E, pq)` into `Z_∞(E', pq)` (in `Factors` form). -/
lemma Hom.factors_infCyclesSubobject (f : E ⟶ E') (pq : κ)
    [E.HasInfCyclesAt pq] [E'.HasInfCyclesAt pq] :
    (E'.infCyclesSubobject pq).Factors ((E.infCyclesSubobject pq).arrow ≫ (f.hom r₀).f pq) :=
  (Subobject.le_pullback_iff _ _ _).1 (f.infCyclesSubobject_le_pullback pq)

/-- A morphism of spectral sequences carries `B_∞(E, pq)` into `B_∞(E', pq)` (in `Factors` form). -/
lemma Hom.factors_infBoundariesSubobject (f : E ⟶ E') (pq : κ)
    [E.HasInfBoundariesAt pq] [E'.HasInfBoundariesAt pq] :
    (E'.infBoundariesSubobject pq).Factors
      ((E.infBoundariesSubobject pq).arrow ≫ (f.hom r₀).f pq) :=
  (Subobject.exists_le_iff _ _ _).1 (f.exists_infBoundariesSubobject_le pq)

/-- The morphism `E.limitPage pq ⟶ E'.limitPage pq` induced on limit pages by a morphism
`f : E ⟶ E'` of spectral sequences. -/
noncomputable def Hom.limitPageMap (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ⟶ E'.limitPage pq :=
  (E.limitPagePresentation pq).map (E'.limitPagePresentation pq) ((f.hom r₀).f pq)
    (f.factors_infBoundariesSubobject pq) (f.factors_infCyclesSubobject pq)

/-- Compatibility of `Hom.limitPageMap` with the subquotient presentation projections. -/
@[reassoc]
lemma Hom.π_comp_limitPageMap (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (E.limitPagePresentation pq).π ≫ f.limitPageMap pq =
      (E'.infCyclesSubobject pq).factorThru ((E.infCyclesSubobject pq).arrow ≫ (f.hom r₀).f pq)
          (f.factors_infCyclesSubobject pq) ≫
        (E'.limitPagePresentation pq).π :=
  TauCeti.SubquotientPresentation.π_comp_map _ _ _ _ _

@[simp]
lemma Hom.limitPageMap_id (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    (𝟙 E : E ⟶ E).limitPageMap pq = 𝟙 (E.limitPage pq) :=
  TauCeti.SubquotientPresentation.map_id (E.limitPagePresentation pq) _ _

@[simp]
lemma Hom.limitPageMap_comp (f : E ⟶ E') (g : E' ⟶ E'') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] [E''.HasLimitPageAt pq] :
    (f ≫ g).limitPageMap pq = f.limitPageMap pq ≫ g.limitPageMap pq :=
  (TauCeti.SubquotientPresentation.map_comp (E.limitPagePresentation pq)
    (E'.limitPagePresentation pq) (E''.limitPagePresentation pq)
    ((f.hom r₀).f pq) ((g.hom r₀).f pq) _ _ _ _ _ _).symm

/-- **Agreement at stabilizing positions.** If `E` and `E'` both stabilize at `pq` from page `s`,
then `f.limitPageMap pq` agrees with `(f.hom s h.le).f pq` under `limitPageIsoOfStabilizesAt`. -/
theorem Hom.limitPageMap_comp_limitPageIsoOfStabilizesAt_hom (f : E ⟶ E')
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) (h' : E'.StabilizesAt pq s)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    f.limitPageMap pq ≫ (E'.limitPageIsoOfStabilizesAt h').hom =
      (E.limitPageIsoOfStabilizesAt h).hom ≫ (f.hom s h.le).f pq := by
  rw [limitPageIsoOfStabilizesAt, limitPageIsoOfStabilizesAt, ← f.pagePresentation_map pq s h.le]
  exact (TauCeti.SubquotientPresentation.isoOfEq_hom_comp_map _ _ _ _ ((f.hom r₀).f pq)
    _ _ _ _).symm

/-- The isomorphism `E.limitPage pq ≅ E'.limitPage pq` induced by an isomorphism of spectral
sequences `e : E ≅ E'`. -/
noncomputable def limitPageIsoOfIso (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ≅ E'.limitPage pq where
  hom := e.hom.limitPageMap pq
  inv := e.inv.limitPageMap pq
  hom_inv_id := by rw [← Hom.limitPageMap_comp, Iso.hom_inv_id, Hom.limitPageMap_id]
  inv_hom_id := by rw [← Hom.limitPageMap_comp, Iso.inv_hom_id, Hom.limitPageMap_id]

@[simp]
lemma limitPageIsoOfIso_hom (e : E ≅ E') (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).hom = e.hom.limitPageMap pq :=
  (rfl)

@[simp]
lemma limitPageIsoOfIso_inv (e : E ≅ E') (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).inv = e.inv.limitPageMap pq :=
  (rfl)

private lemma range_cyclesSubobject_eq_map_image (e : E ≅ E') (pq : κ) :
    (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E'.cyclesSubobject pq r.val r.property) =
      (Subobject.mapIsoToOrderIso (pageXIsoOfIso e r₀ le_rfl pq)) ''
        (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) := by
  rw [← Set.range_comp']
  exact congrArg Set.range (funext fun r ↦ (map_cyclesSubobject_of_iso e pq r.val r.property).symm)

private lemma range_boundariesSubobject_eq_map_image (e : E ≅ E') (pq : κ) :
    (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E'.boundariesSubobject pq r.val r.property) =
      (Subobject.mapIsoToOrderIso (pageXIsoOfIso e r₀ le_rfl pq)) ''
        (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) := by
  rw [← Set.range_comp']
  exact congrArg Set.range
    (funext fun r ↦ (map_boundariesSubobject_of_iso e pq r.val r.property).symm)

/-- Existence of infinite cycles at `pq` is invariant under isomorphisms of spectral sequences. -/
theorem hasInfCyclesAt_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.HasInfCyclesAt pq ↔ E'.HasInfCyclesAt pq := by
  let φ := Subobject.mapIsoToOrderIso (pageXIsoOfIso e r₀ le_rfl pq)
  constructor
  · intro h
    refine ⟨φ (E.infCyclesSubobject pq), ?_⟩
    rw [range_cyclesSubobject_eq_map_image e pq]
    exact (OrderIso.isGLB_image' φ).2 (E.isGLB_infCyclesSubobject pq)
  · intro h
    refine ⟨φ.symm (E'.infCyclesSubobject pq), ?_⟩
    have hglb := E'.isGLB_infCyclesSubobject pq
    rw [range_cyclesSubobject_eq_map_image e pq] at hglb
    exact (OrderIso.isGLB_image φ).1 hglb

/-- Existence of infinite boundaries at `pq` is invariant under isomorphisms of spectral
sequences. -/
theorem hasInfBoundariesAt_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.HasInfBoundariesAt pq ↔ E'.HasInfBoundariesAt pq := by
  let φ := Subobject.mapIsoToOrderIso (pageXIsoOfIso e r₀ le_rfl pq)
  constructor
  · intro h
    refine ⟨φ (E.infBoundariesSubobject pq), ?_⟩
    rw [range_boundariesSubobject_eq_map_image e pq]
    exact (OrderIso.isLUB_image' φ).2 (E.isLUB_infBoundariesSubobject pq)
  · intro h
    refine ⟨φ.symm (E'.infBoundariesSubobject pq), ?_⟩
    have hlub := E'.isLUB_infBoundariesSubobject pq
    rw [range_boundariesSubobject_eq_map_image e pq] at hlub
    exact (OrderIso.isLUB_image φ).1 hlub

/-- Existence of a limit page at `pq` is invariant under isomorphisms of spectral sequences. -/
theorem hasLimitPageAt_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.HasLimitPageAt pq ↔ E'.HasLimitPageAt pq :=
  ⟨fun _ ↦ {
      toHasInfCyclesAt := (hasInfCyclesAt_iff_of_iso e pq).1 inferInstance
      toHasInfBoundariesAt := (hasInfBoundariesAt_iff_of_iso e pq).1 inferInstance
    },
    fun _ ↦ {
      toHasInfCyclesAt := (hasInfCyclesAt_iff_of_iso e pq).2 inferInstance
      toHasInfBoundariesAt := (hasInfBoundariesAt_iff_of_iso e pq).2 inferInstance
    }⟩

/-- Isomorphic spectral sequences have corresponding infinite cycles under the first-page
isomorphism. -/
lemma map_infCyclesSubobject_of_iso (e : E ≅ E') (pq : κ)
    [E.HasInfCyclesAt pq] [E'.HasInfCyclesAt pq] :
    (Subobject.map (pageXIsoOfIso e r₀ le_rfl pq).hom).obj (E.infCyclesSubobject pq) =
      E'.infCyclesSubobject pq := by
  symm
  refine E'.infCyclesSubobject_eq_of_isGLB ?_
  rw [range_cyclesSubobject_eq_map_image e pq]
  exact (OrderIso.isGLB_image' (Subobject.mapIsoToOrderIso (pageXIsoOfIso e r₀ le_rfl pq))).2
    (E.isGLB_infCyclesSubobject pq)

/-- Isomorphic spectral sequences have corresponding infinite boundaries under the first-page
isomorphism. -/
lemma map_infBoundariesSubobject_of_iso (e : E ≅ E') (pq : κ)
    [E.HasInfBoundariesAt pq] [E'.HasInfBoundariesAt pq] :
    (Subobject.map (pageXIsoOfIso e r₀ le_rfl pq).hom).obj (E.infBoundariesSubobject pq) =
      E'.infBoundariesSubobject pq := by
  symm
  refine E'.infBoundariesSubobject_eq_of_isLUB ?_
  rw [range_boundariesSubobject_eq_map_image e pq]
  exact (OrderIso.isLUB_image' (Subobject.mapIsoToOrderIso (pageXIsoOfIso e r₀ le_rfl pq))).2
    (E.isLUB_infBoundariesSubobject pq)

/-- When `C` has countable products and countable coproducts, taking the limit page at position
`pq` defines a functor `SpectralSequence C c r₀ ⥤ C`. -/
@[expose, simps]
noncomputable def limitPageFunctor (C : Type u) [Category.{v} C] [Abelian C]
    [HasCountableProducts C] [HasCountableCoproducts C]
    {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ) (pq : κ) :
    SpectralSequence C c r₀ ⥤ C where
  obj E := E.limitPage pq
  map f := f.limitPageMap pq
  map_id E := Hom.limitPageMap_id E pq
  map_comp f g := Hom.limitPageMap_comp f g pq

end Functoriality

section Rebasing

variable (E : SpectralSequence C c r₀)

private lemma isGLB_cyclesSubobject_tail_iff (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    (Z : Subobject ((E.page r₀).X pq)) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z ↔
      IsGLB (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.cyclesSubobject pq r.val (hs.trans r.property)) Z := by
  have hsub :
      (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.val (hs.trans r.property)) ⊆
        Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property := by
    rintro _ ⟨⟨r, hsr⟩, rfl⟩
    exact ⟨⟨r, hs.trans hsr⟩, rfl⟩
  have hcoinit : IsCoinitialFor
      (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.val (hs.trans r.property)) := by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    exact ⟨_, ⟨⟨max r s, le_max_right r s⟩, rfl⟩,
      E.cyclesSubobject_le_of_le pq hr (le_max_left r s)⟩
  exact isGLB_congr (Set.Subset.antisymm (lowerBounds_mono_set hsub)
    (lowerBounds_mono_of_isCoinitialFor hcoinit))

private lemma isLUB_boundariesSubobject_tail_iff (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    (B : Subobject ((E.page r₀).X pq)) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) B ↔
      IsLUB (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property)) B := by
  have hsub :
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
          E.boundariesSubobject pq r.val (hs.trans r.property)) ⊆
        Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property := by
    rintro _ ⟨⟨r, hsr⟩, rfl⟩
    exact ⟨⟨r, hs.trans hsr⟩, rfl⟩
  have hcofin : IsCofinalFor
      (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property)) := by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    exact ⟨_, ⟨⟨max r s, le_max_right r s⟩, rfl⟩,
      E.boundariesSubobject_le_of_le pq hr (le_max_left r s)⟩
  exact isLUB_congr (Set.Subset.antisymm (upperBounds_mono_set hsub)
    (upperBounds_mono_of_isCofinalFor hcofin))

private lemma range_cyclesSubobject_tail_eq_preimage_image (s : ℤ) (hs : r₀ ≤ s) (pq : κ) :
    (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.val (hs.trans r.property)) =
      (E.pagePresentation pq s hs).preimage ''
        (Set.range fun r : {r : ℤ // s ≤ r} ↦
          (E.fromPage s hs).cyclesSubobject pq r.val r.property) := by
  rw [← Set.range_comp']
  exact congrArg Set.range
    (funext fun r ↦ E.cyclesSubobject_eq_preimage_fromPage s hs pq r.val r.property)

private lemma range_boundariesSubobject_tail_eq_preimage_image (s : ℤ) (hs : r₀ ≤ s) (pq : κ) :
    (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.boundariesSubobject pq r.val (hs.trans r.property)) =
      (E.pagePresentation pq s hs).preimage ''
        (Set.range fun r : {r : ℤ // s ≤ r} ↦
          (E.fromPage s hs).boundariesSubobject pq r.val r.property) := by
  rw [← Set.range_comp']
  exact congrArg Set.range
    (funext fun r ↦ E.boundariesSubobject_eq_preimage_fromPage s hs pq r.val r.property)

/-- Existence of infinite cycles at `pq` is unaffected by rebasing to page `s ≥ r₀`. -/
theorem hasInfCyclesAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s) (pq : κ) :
    (E.fromPage s hs).HasInfCyclesAt pq ↔ E.HasInfCyclesAt pq := by
  have hne : (Set.range fun r : {r : ℤ // s ≤ r} ↦
      (E.fromPage s hs).cyclesSubobject pq r.val r.property).Nonempty := ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨(E.pagePresentation pq s hs).preimage Z, ?_⟩
    rw [E.isGLB_cyclesSubobject_tail_iff s hs pq,
      E.range_cyclesSubobject_tail_eq_preimage_image s hs pq]
    exact ((E.pagePresentation pq s hs).isGLB_preimage_iff hne).2 hZ
  · rintro ⟨W, hW⟩
    rw [E.isGLB_cyclesSubobject_tail_iff s hs pq,
      E.range_cyclesSubobject_tail_eq_preimage_image s hs pq] at hW
    have himg := (E.pagePresentation pq s hs).preimage_image_of_isGLB hne hW
    refine ⟨(E.pagePresentation pq s hs).image W,
      ((E.pagePresentation pq s hs).isGLB_preimage_iff hne).1 ?_⟩
    simpa only [himg] using hW

/-- Existence of infinite boundaries at `pq` is unaffected by rebasing to page `s ≥ r₀`. -/
theorem hasInfBoundariesAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s) (pq : κ) :
    (E.fromPage s hs).HasInfBoundariesAt pq ↔ E.HasInfBoundariesAt pq := by
  have hne : (Set.range fun r : {r : ℤ // s ≤ r} ↦
      (E.fromPage s hs).boundariesSubobject pq r.val r.property).Nonempty := ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨(E.pagePresentation pq s hs).preimage B, ?_⟩
    rw [E.isLUB_boundariesSubobject_tail_iff s hs pq,
      E.range_boundariesSubobject_tail_eq_preimage_image s hs pq]
    exact ((E.pagePresentation pq s hs).isLUB_preimage_iff hne).2 hB
  · rintro ⟨W, hW⟩
    rw [E.isLUB_boundariesSubobject_tail_iff s hs pq,
      E.range_boundariesSubobject_tail_eq_preimage_image s hs pq] at hW
    have himg := (E.pagePresentation pq s hs).preimage_image_of_isLUB hne hW
    refine ⟨(E.pagePresentation pq s hs).image W,
      ((E.pagePresentation pq s hs).isLUB_preimage_iff hne).1 ?_⟩
    simpa only [himg] using hW

/-- Existence of a limit page at `pq` is unaffected by rebasing to page `s ≥ r₀`. -/
theorem hasLimitPageAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s) (pq : κ) :
    (E.fromPage s hs).HasLimitPageAt pq ↔ E.HasLimitPageAt pq :=
  ⟨fun _ ↦ {
      toHasInfCyclesAt := (E.hasInfCyclesAt_fromPage_iff s hs pq).1 inferInstance
      toHasInfBoundariesAt := (E.hasInfBoundariesAt_fromPage_iff s hs pq).1 inferInstance
    },
    fun _ ↦ {
      toHasInfCyclesAt := (E.hasInfCyclesAt_fromPage_iff s hs pq).2 inferInstance
      toHasInfBoundariesAt := (E.hasInfBoundariesAt_fromPage_iff s hs pq).2 inferInstance
    }⟩

/-- **Rebasing infinite cycles.** For `s ≥ r₀`, `Z_∞(pq)` of `E` is the preimage along the page-`s`
presentation of `Z_∞(pq)` of `E.fromPage s hs`. -/
lemma infCyclesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    [E.HasInfCyclesAt pq] [(E.fromPage s hs).HasInfCyclesAt pq] :
    E.infCyclesSubobject pq =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infCyclesSubobject pq) := by
  have hne : (Set.range fun r : {r : ℤ // s ≤ r} ↦
      (E.fromPage s hs).cyclesSubobject pq r.val r.property).Nonempty := ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  refine E.infCyclesSubobject_eq_of_isGLB ?_
  rw [E.isGLB_cyclesSubobject_tail_iff s hs pq,
    E.range_cyclesSubobject_tail_eq_preimage_image s hs pq]
  exact ((E.pagePresentation pq s hs).isGLB_preimage_iff hne).2
    ((E.fromPage s hs).isGLB_infCyclesSubobject pq)

/-- **Rebasing infinite boundaries.** For `s ≥ r₀`, `B_∞(pq)` of `E` is the preimage along the
page-`s` presentation of `B_∞(pq)` of `E.fromPage s hs`. -/
lemma infBoundariesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    [E.HasInfBoundariesAt pq] [(E.fromPage s hs).HasInfBoundariesAt pq] :
    E.infBoundariesSubobject pq =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infBoundariesSubobject pq) := by
  have hne : (Set.range fun r : {r : ℤ // s ≤ r} ↦
      (E.fromPage s hs).boundariesSubobject pq r.val r.property).Nonempty := ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  refine E.infBoundariesSubobject_eq_of_isLUB ?_
  rw [E.isLUB_boundariesSubobject_tail_iff s hs pq,
    E.range_boundariesSubobject_tail_eq_preimage_image s hs pq]
  exact ((E.pagePresentation pq s hs).isLUB_preimage_iff hne).2
    ((E.fromPage s hs).isLUB_infBoundariesSubobject pq)

/-- **Rebasing isomorphism for the limit page.** Computing the limit page of `E` from the towers
built at page `s ≥ r₀` yields an object canonically isomorphic to `E.limitPage pq`. -/
noncomputable def limitPageFromPageIso (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    [E.HasLimitPageAt pq] [(E.fromPage s hs).HasLimitPageAt pq] :
    (E.fromPage s hs).limitPage pq ≅ E.limitPage pq :=
  TauCeti.SubquotientPresentation.isoOfEq
    (P := (E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq))
    (P' := E.limitPagePresentation pq)
    (E.infBoundariesSubobject_eq_preimage_fromPage s hs pq).symm
    (E.infCyclesSubobject_eq_preimage_fromPage s hs pq).symm

/-- Compatibility of `limitPageFromPageIso` with the subquotient presentation projections. -/
@[reassoc]
lemma π_comp_limitPageFromPageIso_hom (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    [E.HasLimitPageAt pq] [(E.fromPage s hs).HasLimitPageAt pq] :
    ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).π ≫
        (E.limitPageFromPageIso s hs pq).hom =
      Subobject.ofLE
          ((E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infCyclesSubobject pq))
          (E.infCyclesSubobject pq)
          (E.infCyclesSubobject_eq_preimage_fromPage s hs pq).symm.le ≫
        (E.limitPagePresentation pq).π :=
  TauCeti.SubquotientPresentation.π_isoOfEq_hom _ _ _ _

/-- **Naturality of the rebasing isomorphism.** A morphism `f : E ⟶ E'` of spectral sequences
commutes with `limitPageFromPageIso`. -/
theorem limitPageFromPageIso_hom_naturality {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq]
    [(E.fromPage s hs).HasLimitPageAt pq] [(E'.fromPage s hs).HasLimitPageAt pq] :
    (f.fromPageMap s hs).limitPageMap pq ≫ (E'.limitPageFromPageIso s hs pq).hom =
      (E.limitPageFromPageIso s hs pq).hom ≫ f.limitPageMap pq := by
  let p := E.pagePresentation pq s hs
  let p' := E'.pagePresentation pq s hs
  let q := (E.fromPage s hs).limitPagePresentation pq
  let q' := (E'.fromPage s hs).limitPagePresentation pq
  have hBq : q'.B.Factors (q.B.arrow ≫
      p.map p' ((f.hom r₀).f pq)
        (f.factors_boundariesSubobject pq s hs) (f.factors_cyclesSubobject pq s hs)) := by
    rw [f.pagePresentation_map pq s hs]
    exact (f.fromPageMap s hs).factors_infBoundariesSubobject pq
  have hZq : q'.Z.Factors (q.Z.arrow ≫
      p.map p' ((f.hom r₀).f pq)
        (f.factors_boundariesSubobject pq s hs) (f.factors_cyclesSubobject pq s hs)) := by
    rw [f.pagePresentation_map pq s hs]
    exact (f.fromPageMap s hs).factors_infCyclesSubobject pq
  have hmap : (p.trans q).map (p'.trans q') ((f.hom r₀).f pq)
      (p.factors_preimage_of_factors_map p' ((f.hom r₀).f pq)
        (f.factors_boundariesSubobject pq s hs) (f.factors_cyclesSubobject pq s hs) hBq)
      (p.factors_preimage_of_factors_map p' ((f.hom r₀).f pq)
        (f.factors_boundariesSubobject pq s hs) (f.factors_cyclesSubobject pq s hs) hZq) =
      (f.fromPageMap s hs).limitPageMap pq := by
    rw [TauCeti.SubquotientPresentation.trans_map p p' q q' ((f.hom r₀).f pq)
      (f.factors_boundariesSubobject pq s hs) (f.factors_cyclesSubobject pq s hs) hBq hZq]
    have h1 : ∀ (g : (E.page s hs).X pq ⟶ (E'.page s hs).X pq)
        (_ : g = ((f.fromPageMap s hs).hom s le_rfl).f pq)
        (hB : q'.B.Factors (q.B.arrow ≫ g))
        (hZ : q'.Z.Factors (q.Z.arrow ≫ g)),
        q.map q' g hB hZ = (f.fromPageMap s hs).limitPageMap pq := by
      rintro _ rfl _ _
      rfl
    exact h1 _ (f.pagePresentation_map pq s hs) _ _
  rw [limitPageFromPageIso, limitPageFromPageIso, ← hmap]
  exact (TauCeti.SubquotientPresentation.isoOfEq_hom_comp_map _ _ _ _ ((f.hom r₀).f pq)
    _ _ _ _).symm

end Rebasing

end CategoryTheory.SpectralSequence
