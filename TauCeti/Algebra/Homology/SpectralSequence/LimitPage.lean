/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.Algebra.Homology.SpectralSequence.Stabilization
public import TauCeti.CategoryTheory.Subobject.Lattice
import Mathlib.Order.Bounds.OrderIso

/-!
# The limit page `E_∞` of a spectral sequence

For a spectral sequence `E : SpectralSequence C c r₀` and a position `pq : κ`, the cycle tower
`Z_r(pq)` (`CategoryTheory.SpectralSequence.cyclesSubobject`) is decreasing and the boundary tower
`B_r(pq)` (`CategoryTheory.SpectralSequence.boundariesSubobject`) is increasing, with
`B_r(pq) ≤ Z_{r'}(pq)` for all `r, r' ≥ r₀`.

When the cycle tower has a greatest lower bound `Z_∞(pq)` (`HasCyclesInf`) and the boundary tower
has a least upper bound `B_∞(pq)` (`HasBoundariesSup`) in `Subobject ((E.page r₀).X pq)`, we have
`B_∞(pq) ≤ Z_∞(pq)`, and the **limit page** `E_∞(pq)` is the quotient `Z_∞(pq) / B_∞(pq)`
(`CategoryTheory.SpectralSequence.limitPage`), equipped with its subquotient presentation inside
`(E.page r₀).X pq` (`CategoryTheory.SpectralSequence.limitPagePresentation`).

Both bounds exist unconditionally when `C` has countable products (`HasCountableProducts C`) and
countable coproducts (`HasCountableCoproducts C`); regularity (`IsRegularAt`) guarantees the cycle
infimum `Z_∞(pq)` and coregularity (`IsCoregularAt`) guarantees the boundary supremum `B_∞(pq)`,
so together they guarantee both, as happens at every stabilizing position (`StabilizesAt`). When
`E` stabilizes at `pq` from page `s`, each `(E.page r).X pq` for `r ≥ s` is canonically
isomorphic to `E_∞(pq)` (`StabilizesAt.limitPageIso`), compatibly with `StabilizesAt.pageXIso`.

A morphism `f : E ⟶ E'` induces `limitPageMap f pq : E.limitPage pq ⟶ E'.limitPage pq`,
compatible with `(f.hom r).f pq` at stabilizing positions. Rebased spectral sequences
`E.fromPage s hs` have canonically isomorphic limit pages (`limitPageFromPageIso`), and any
object vanishing on some page `r ≥ r₀` has zero limit page (`isZero_limitPage_of_isZero`).

## Main definitions

* `CategoryTheory.SpectralSequence.cyclesSet`,
  `CategoryTheory.SpectralSequence.boundariesSet`: the sets of cycle and boundary subobjects
  across pages `r ≥ r₀`.
* `CategoryTheory.SpectralSequence.HasCyclesInf`,
  `CategoryTheory.SpectralSequence.HasBoundariesSup`,
  `CategoryTheory.SpectralSequence.HasLimitPage`: existence predicates for `Z_∞(pq)`, `B_∞(pq)`,
  and `E_∞(pq)`.
* `CategoryTheory.SpectralSequence.cyclesInf`,
  `CategoryTheory.SpectralSequence.boundariesSup`: the infinite cycle and boundary subobjects
  `Z_∞(pq)` and `B_∞(pq)`.
* `CategoryTheory.SpectralSequence.limitPage`,
  `CategoryTheory.SpectralSequence.limitPagePresentation`: the limit page object `E_∞(pq)` and
  its subquotient presentation inside `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.StabilizesAt.limitPageIso`: the canonical isomorphism
  `(E.page r).X pq ≅ E.limitPage pq` at a stabilizing position.
* `CategoryTheory.SpectralSequence.limitPageMap`,
  `CategoryTheory.SpectralSequence.limitPageIsoOfIso`,
  `CategoryTheory.SpectralSequence.limitPageFunctor`: functoriality of `E_∞(pq)`.
* `CategoryTheory.SpectralSequence.limitPageFromPageIso`: canonical isomorphism between the limit
  page of `E.fromPage s hs` and that of `E`.

## References

* [Stacks, Tag 011N](https://stacks.math.columbia.edu/tag/011N), the construction of `E_∞` after
  Definition 20.1.
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, §2.
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits Subobject TauCeti

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section SetsAndExistence

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- The set of cycle subobjects `{Z_r(pq) | r ≥ r₀}` in `Subobject ((E.page r₀).X pq)`. -/
noncomputable def cyclesSet : Set (Subobject ((E.page r₀).X pq)) :=
  Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property

/-- The set of boundary subobjects `{B_r(pq) | r ≥ r₀}` in `Subobject ((E.page r₀).X pq)`. -/
noncomputable def boundariesSet : Set (Subobject ((E.page r₀).X pq)) :=
  Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property

variable {E pq}

lemma mem_cyclesSet_iff {S : Subobject ((E.page r₀).X pq)} :
    S ∈ E.cyclesSet pq ↔ ∃ (r : ℤ) (hr : r₀ ≤ r), E.cyclesSubobject pq r hr = S := by
  simp [cyclesSet]

lemma mem_boundariesSet_iff {S : Subobject ((E.page r₀).X pq)} :
    S ∈ E.boundariesSet pq ↔ ∃ (r : ℤ) (hr : r₀ ≤ r), E.boundariesSubobject pq r hr = S := by
  simp [boundariesSet]

lemma cyclesSubobject_mem_cyclesSet (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq r hr ∈ E.cyclesSet pq :=
  ⟨⟨r, hr⟩, rfl⟩

lemma boundariesSubobject_mem_boundariesSet (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ∈ E.boundariesSet pq :=
  ⟨⟨r, hr⟩, rfl⟩

lemma cyclesSet_nonempty : (E.cyclesSet pq).Nonempty :=
  ⟨_, E.cyclesSubobject_mem_cyclesSet r₀ le_rfl⟩

lemma boundariesSet_nonempty : (E.boundariesSet pq).Nonempty :=
  ⟨_, E.boundariesSubobject_mem_boundariesSet r₀ le_rfl⟩

variable (E pq)

/-- `E` has an infinite cycle subobject `Z_∞(pq)` when `{Z_r(pq) | r ≥ r₀}` has a greatest lower
bound in `Subobject ((E.page r₀).X pq)`. -/
class HasCyclesInf : Prop where
  /-- The cycle tower at `pq` has a greatest lower bound. -/
  exists_isGLB : ∃ Z : Subobject ((E.page r₀).X pq), IsGLB (E.cyclesSet pq) Z

/-- `E` has an infinite boundary subobject `B_∞(pq)` when `{B_r(pq) | r ≥ r₀}` has a least upper
bound in `Subobject ((E.page r₀).X pq)`. -/
class HasBoundariesSup : Prop where
  /-- The boundary tower at `pq` has a least upper bound. -/
  exists_isLUB : ∃ B : Subobject ((E.page r₀).X pq), IsLUB (E.boundariesSet pq) B

/-- `E` has a limit page `E_∞(pq)` when both `Z_∞(pq)` and `B_∞(pq)` exist. -/
class HasLimitPage : Prop extends E.HasCyclesInf pq, E.HasBoundariesSup pq

lemma hasLimitPage_of_hasCyclesInf_of_hasBoundariesSup [E.HasCyclesInf pq]
    [E.HasBoundariesSup pq] : E.HasLimitPage pq :=
  ⟨⟩

/-- When `C` has countable products, every spectral sequence in `C` has `Z_∞(pq)` at every
position `pq`, constructed as a kernel into a countable product of cokernels. -/
instance HasCyclesInf.of_hasCountableProducts [HasCountableProducts C] : E.HasCyclesInf pq where
  exists_isGLB := ⟨_, isGLB_range_kernelSubobject_piLift
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)⟩

/-- When `C` has countable coproducts, every spectral sequence in `C` has `B_∞(pq)` at every
position `pq`, constructed as an image of a countable coproduct. -/
instance HasBoundariesSup.of_hasCountableCoproducts [HasCountableCoproducts C] :
    E.HasBoundariesSup pq where
  exists_isLUB := ⟨_, isLUB_range_imageSubobject_sigmaDesc
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)⟩

/-- When `C` has countable products and countable coproducts, every spectral sequence in `C` has
a limit page `E_∞(pq)` at every position `pq`. -/
instance (priority := 100) hasLimitPage_of_hasCountableProducts_of_hasCountableCoproducts
    [HasCountableProducts C] [HasCountableCoproducts C] : E.HasLimitPage pq :=
  ⟨⟩

end SetsAndExistence

section LimitSubobjects

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- The infinite cycle subobject `Z_∞(pq)` of `(E.page r₀).X pq`, the greatest lower bound of
`{Z_r(pq) | r ≥ r₀}`. -/
noncomputable def cyclesInf [E.HasCyclesInf pq] : Subobject ((E.page r₀).X pq) :=
  Classical.choose (HasCyclesInf.exists_isGLB (E := E) (pq := pq))

/-- The infinite boundary subobject `B_∞(pq)` of `(E.page r₀).X pq`, the least upper bound of
`{B_r(pq) | r ≥ r₀}`. -/
noncomputable def boundariesSup [E.HasBoundariesSup pq] : Subobject ((E.page r₀).X pq) :=
  Classical.choose (HasBoundariesSup.exists_isLUB (E := E) (pq := pq))

lemma isGLB_cyclesInf [E.HasCyclesInf pq] : IsGLB (E.cyclesSet pq) (E.cyclesInf pq) :=
  Classical.choose_spec (HasCyclesInf.exists_isGLB (E := E) (pq := pq))

lemma isLUB_boundariesSup [E.HasBoundariesSup pq] :
    IsLUB (E.boundariesSet pq) (E.boundariesSup pq) :=
  Classical.choose_spec (HasBoundariesSup.exists_isLUB (E := E) (pq := pq))

variable {E pq}

lemma cyclesInf_le [E.HasCyclesInf pq] (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesInf pq ≤ E.cyclesSubobject pq r hr :=
  (E.isGLB_cyclesInf pq).1 (cyclesSubobject_mem_cyclesSet r hr)

lemma le_cyclesInf [E.HasCyclesInf pq] {S : Subobject ((E.page r₀).X pq)}
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), S ≤ E.cyclesSubobject pq r hr) :
    S ≤ E.cyclesInf pq :=
  (E.isGLB_cyclesInf pq).2 (by rintro _ ⟨⟨r, hr⟩, rfl⟩; exact h hr)

lemma cyclesInf_eq_of_isGLB [E.HasCyclesInf pq] {Z : Subobject ((E.page r₀).X pq)}
    (h : IsGLB (E.cyclesSet pq) Z) : E.cyclesInf pq = Z :=
  (E.isGLB_cyclesInf pq).unique h

lemma boundariesSubobject_le_boundariesSup [E.HasBoundariesSup pq] (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.boundariesSup pq :=
  (E.isLUB_boundariesSup pq).1 (boundariesSubobject_mem_boundariesSet r hr)

lemma boundariesSup_le [E.HasBoundariesSup pq] {S : Subobject ((E.page r₀).X pq)}
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), E.boundariesSubobject pq r hr ≤ S) :
    E.boundariesSup pq ≤ S :=
  (E.isLUB_boundariesSup pq).2 (by rintro _ ⟨⟨r, hr⟩, rfl⟩; exact h hr)

lemma boundariesSup_eq_of_isLUB [E.HasBoundariesSup pq] {B : Subobject ((E.page r₀).X pq)}
    (h : IsLUB (E.boundariesSet pq) B) : E.boundariesSup pq = B :=
  (E.isLUB_boundariesSup pq).unique h

variable (E pq)

/-- Explicit construction of `Z_∞(pq)` when `C` has countable products, as a kernel into the
product of the quotients `(E.page r₀).X pq / Z_r(pq)`. -/
lemma cyclesInf_eq_kernelSubobject_piLift [HasCountableProducts C] :
    E.cyclesInf pq = kernelSubobject (Pi.lift fun r : {r : ℤ // r₀ ≤ r} ↦
      cokernel.π (E.cyclesSubobject pq r.val r.property).arrow) :=
  cyclesInf_eq_of_isGLB (isGLB_range_kernelSubobject_piLift
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property))

/-- Explicit construction of `B_∞(pq)` when `C` has countable coproducts, as the image of the map
from the coproduct of the `B_r(pq)`. -/
lemma boundariesSup_eq_imageSubobject_sigmaDesc [HasCountableCoproducts C] :
    E.boundariesSup pq = imageSubobject (Sigma.desc fun r : {r : ℤ // r₀ ≤ r} ↦
      (E.boundariesSubobject pq r.val r.property).arrow) :=
  boundariesSup_eq_of_isLUB (isLUB_range_imageSubobject_sigmaDesc
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property))

/-- Every infinite boundary is an infinite cycle: `B_∞(pq) ≤ Z_∞(pq)`. -/
lemma boundariesSup_le_cyclesInf [E.HasCyclesInf pq] [E.HasBoundariesSup pq] :
    E.boundariesSup pq ≤ E.cyclesInf pq :=
  boundariesSup_le fun r hr ↦
    le_cyclesInf fun r' hr' ↦ E.boundariesSubobject_le_cyclesSubobject pq r r' hr hr'

end LimitSubobjects

section LimitPage

variable (E : SpectralSequence C c r₀) (pq : κ) [E.HasCyclesInf pq] [E.HasBoundariesSup pq]

/-- The **limit page** `E_∞(pq)` of a spectral sequence `E` at position `pq`, defined as the
subquotient `Z_∞(pq) / B_∞(pq)` inside `(E.page r₀).X pq`. -/
@[expose] noncomputable def limitPage : C :=
  cokernel (ofLE (E.boundariesSup pq) (E.cyclesInf pq) (E.boundariesSup_le_cyclesInf pq))

/-- The canonical subquotient presentation of `E.limitPage pq` inside `(E.page r₀).X pq`, by
`B_∞(pq) ≤ Z_∞(pq)`. -/
@[expose] noncomputable def limitPagePresentation :
    SubquotientPresentation ((E.page r₀).X pq) (E.limitPage pq) :=
  SubquotientPresentation.quotient _ _ (E.boundariesSup_le_cyclesInf pq)

@[simp]
lemma limitPagePresentation_B : (E.limitPagePresentation pq).B = E.boundariesSup pq :=
  (rfl)

@[simp]
lemma limitPagePresentation_Z : (E.limitPagePresentation pq).Z = E.cyclesInf pq :=
  (rfl)

@[simp]
lemma π_limitPagePresentation :
    (E.limitPagePresentation pq).π =
      cokernel.π (ofLE (E.boundariesSup pq) (E.cyclesInf pq) (E.boundariesSup_le_cyclesInf pq)) :=
  SubquotientPresentation.π_quotient _ _ _

end LimitPage

section Stabilization

variable {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}

/-- When the differential leaving `pq` vanishes from page `s` on, `Z_s(pq)` is the greatest lower
bound of `{Z_r(pq) | r ≥ r₀}`. -/
lemma isGLB_cyclesSubobject_of_dFrom_eq_zero (hs : r₀ ≤ s)
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0) :
    IsGLB (E.cyclesSet pq) (E.cyclesSubobject pq s hs) := by
  refine ⟨?_, fun T hT ↦ hT (cyclesSubobject_mem_cyclesSet s hs)⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  calc E.cyclesSubobject pq s hs
      = E.cyclesSubobject pq (max r s) (hs.trans (le_max_right r s)) :=
        (E.cyclesSubobject_eq_of_dFrom_eq_zero pq hs h _ (le_max_right r s)).symm
    _ ≤ E.cyclesSubobject pq r hr :=
        E.cyclesSubobject_anti pq hr (le_max_left r s)

/-- When the differential entering `pq` vanishes from page `s` on, `B_s(pq)` is the least upper
bound of `{B_r(pq) | r ≥ r₀}`. -/
lemma isLUB_boundariesSubobject_of_dTo_eq_zero (hs : r₀ ≤ s)
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0) :
    IsLUB (E.boundariesSet pq) (E.boundariesSubobject pq s hs) := by
  refine ⟨?_, fun T hT ↦ hT (boundariesSubobject_mem_boundariesSet s hs)⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  calc E.boundariesSubobject pq r hr
      ≤ E.boundariesSubobject pq (max r s) (hr.trans (le_max_left r s)) :=
        E.boundariesSubobject_mono pq hr (le_max_left r s)
    _ = E.boundariesSubobject pq s hs :=
        E.boundariesSubobject_eq_of_dTo_eq_zero pq hs h _ (le_max_right r s)

/-- A spectral sequence regular at `pq` has an infinite cycle subobject `Z_∞(pq)`. -/
lemma IsRegularAt.hasCyclesInf (h : E.IsRegularAt pq) : E.HasCyclesInf pq := by
  obtain ⟨s, hs, h'⟩ := (E.isRegularAt_iff pq).1 h
  exact ⟨⟨E.cyclesSubobject pq s hs, isGLB_cyclesSubobject_of_dFrom_eq_zero hs h'⟩⟩

/-- A spectral sequence coregular at `pq` has an infinite boundary subobject `B_∞(pq)`. -/
lemma IsCoregularAt.hasBoundariesSup (h : E.IsCoregularAt pq) : E.HasBoundariesSup pq := by
  obtain ⟨s, hs, h'⟩ := (E.isCoregularAt_iff pq).1 h
  exact ⟨⟨E.boundariesSubobject pq s hs, isLUB_boundariesSubobject_of_dTo_eq_zero hs h'⟩⟩

lemma cyclesInf_eq_of_dFrom_eq_zero [E.HasCyclesInf pq] (hs : r₀ ≤ s)
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0) :
    E.cyclesInf pq = E.cyclesSubobject pq s hs :=
  cyclesInf_eq_of_isGLB (isGLB_cyclesSubobject_of_dFrom_eq_zero hs h)

lemma boundariesSup_eq_of_dTo_eq_zero [E.HasBoundariesSup pq] (hs : r₀ ≤ s)
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0) :
    E.boundariesSup pq = E.boundariesSubobject pq s hs :=
  boundariesSup_eq_of_isLUB (isLUB_boundariesSubobject_of_dTo_eq_zero hs h)

lemma StabilizesAt.hasCyclesInf (h : E.StabilizesAt pq s) : E.HasCyclesInf pq :=
  h.isRegularAt.hasCyclesInf

lemma StabilizesAt.hasBoundariesSup (h : E.StabilizesAt pq s) : E.HasBoundariesSup pq :=
  h.isCoregularAt.hasBoundariesSup

/-- A spectral sequence stabilizing at `pq` has a limit page `E_∞(pq)`. -/
lemma StabilizesAt.hasLimitPage (h : E.StabilizesAt pq s) : E.HasLimitPage pq :=
  { toHasCyclesInf := h.hasCyclesInf
    toHasBoundariesSup := h.hasBoundariesSup }

lemma hasLimitPage_of_isZero {r : ℤ} (hr : r₀ ≤ r) (h : IsZero ((E.page r hr).X pq)) :
    E.HasLimitPage pq :=
  (stabilizesAt_of_isZero hr h).hasLimitPage

lemma StabilizesAt.cyclesInf_eq (h : E.StabilizesAt pq s) [E.HasCyclesInf pq] :
    E.cyclesInf pq = E.cyclesSubobject pq s h.le :=
  cyclesInf_eq_of_dFrom_eq_zero h.le h.dFrom_eq_zero

lemma StabilizesAt.boundariesSup_eq (h : E.StabilizesAt pq s) [E.HasBoundariesSup pq] :
    E.boundariesSup pq = E.boundariesSubobject pq s h.le :=
  boundariesSup_eq_of_dTo_eq_zero h.le h.dTo_eq_zero

/-- When `E` stabilizes at `pq` from page `s`, the object `(E.page r hr).X pq` at any page
`r ≥ s` is canonically isomorphic to `E.limitPage pq`. -/
noncomputable def StabilizesAt.limitPageIso (h : E.StabilizesAt pq s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    (r : ℤ) (hr : r₀ ≤ r) (hsr : s ≤ r) :
    (E.page r hr).X pq ≅ E.limitPage pq :=
  (E.pagePresentation pq r hr).isoOfEq (E.limitPagePresentation pq)
    ((E.pagePresentation_B pq r hr).trans
      ((h.boundariesSubobject_eq hr hsr).trans
        (h.boundariesSup_eq.symm.trans (E.limitPagePresentation_B pq).symm)))
    ((E.pagePresentation_Z pq r hr).trans
      ((h.cyclesSubobject_eq hr hsr).trans
        (h.cyclesInf_eq.symm.trans (E.limitPagePresentation_Z pq).symm)))

/-- `StabilizesAt.pageXIso` followed by `StabilizesAt.limitPageIso` agrees with
`StabilizesAt.limitPageIso` at the starting page `s`. -/
lemma StabilizesAt.pageXIso_comp_limitPageIso (h : E.StabilizesAt pq s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    (r : ℤ) (hr : r₀ ≤ r) (hsr : s ≤ r) :
    h.pageXIso r hr hsr ≪≫ h.limitPageIso r hr hsr = h.limitPageIso s h.le le_rfl := by
  rw [h.pageXIso_eq_isoOfEq r hr hsr, StabilizesAt.limitPageIso, StabilizesAt.limitPageIso,
    SubquotientPresentation.isoOfEq_trans]

/-- The canonical identification `StabilizesAt.limitPageIso` is independent of the starting page
used to witness stabilization. -/
lemma StabilizesAt.limitPageIso_trans (h : E.StabilizesAt pq s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    {r₁ r₂ : ℤ} (hr₂ : r₀ ≤ r₂) (hsr₁ : s ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    (h.mono hsr₁).limitPageIso r₂ hr₂ hr₁₂ = h.limitPageIso r₂ hr₂ (hsr₁.trans hr₁₂) := by
  rfl

end Stabilization

section Naturality

variable {E E' : SpectralSequence C c r₀} {pq : κ}

/-- A morphism `f : E ⟶ E'` maps `Z_∞(E, pq)` into `Z_∞(E', pq)` under its first-page
component. -/
lemma cyclesInf_le_pullback (f : E ⟶ E') [E.HasCyclesInf pq] [E'.HasCyclesInf pq] :
    E.cyclesInf pq ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cyclesInf pq) := by
  rw [← (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le]
  refine le_cyclesInf fun r hr ↦ ?_
  rw [(Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le]
  exact (cyclesInf_le r hr).trans (E.cyclesSubobject_le_pullback pq f r hr)

lemma exists_cyclesInf_le (f : E ⟶ E') [E.HasCyclesInf pq] [E'.HasCyclesInf pq] :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.cyclesInf pq) ≤ E'.cyclesInf pq :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.2 (cyclesInf_le_pullback f)

/-- A morphism `f : E ⟶ E'` maps `B_∞(E, pq)` into `B_∞(E', pq)` under its first-page
component. -/
lemma boundariesSup_le_pullback (f : E ⟶ E') [E.HasBoundariesSup pq] [E'.HasBoundariesSup pq] :
    E.boundariesSup pq ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.boundariesSup pq) :=
  boundariesSup_le fun r hr ↦
    (E.boundariesSubobject_le_pullback pq f r hr).trans
      ((Subobject.pullback _).monotone (boundariesSubobject_le_boundariesSup r hr))

lemma exists_boundariesSup_le (f : E ⟶ E') [E.HasBoundariesSup pq] [E'.HasBoundariesSup pq] :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.boundariesSup pq) ≤ E'.boundariesSup pq :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.2 (boundariesSup_le_pullback f)

private noncomputable def cyclesInfMap (f : E ⟶ E') (pq : κ)
    [E.HasCyclesInf pq] [E'.HasCyclesInf pq] :
    (E.cyclesInf pq : C) ⟶ E'.cyclesInf pq :=
  (E'.cyclesInf pq).factorThru ((E.cyclesInf pq).arrow ≫ (f.hom r₀).f pq)
    ((pullback_factors_iff _ _ _).1 (factors_of_le _ (cyclesInf_le_pullback f) (factors_self _)))

@[reassoc (attr := simp)]
private lemma cyclesInfMap_arrow (f : E ⟶ E') (pq : κ)
    [E.HasCyclesInf pq] [E'.HasCyclesInf pq] :
    cyclesInfMap f pq ≫ (E'.cyclesInf pq).arrow = (E.cyclesInf pq).arrow ≫ (f.hom r₀).f pq :=
  factorThru_arrow _ _ _

private noncomputable def boundariesSupMap (f : E ⟶ E') (pq : κ)
    [E.HasBoundariesSup pq] [E'.HasBoundariesSup pq] :
    (E.boundariesSup pq : C) ⟶ E'.boundariesSup pq :=
  (E'.boundariesSup pq).factorThru ((E.boundariesSup pq).arrow ≫ (f.hom r₀).f pq)
    ((pullback_factors_iff _ _ _).1
      (factors_of_le _ (boundariesSup_le_pullback f) (factors_self _)))

@[reassoc (attr := simp)]
private lemma boundariesSupMap_arrow (f : E ⟶ E') (pq : κ)
    [E.HasBoundariesSup pq] [E'.HasBoundariesSup pq] :
    boundariesSupMap f pq ≫ (E'.boundariesSup pq).arrow =
      (E.boundariesSup pq).arrow ≫ (f.hom r₀).f pq :=
  factorThru_arrow _ _ _

private lemma boundariesSupMap_comp_ofLE (f : E ⟶ E') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    ofLE (E.boundariesSup pq) (E.cyclesInf pq) (E.boundariesSup_le_cyclesInf pq) ≫
        cyclesInfMap f pq =
      boundariesSupMap f pq ≫
        ofLE (E'.boundariesSup pq) (E'.cyclesInf pq) (E'.boundariesSup_le_cyclesInf pq) := by
  rw [← cancel_mono (E'.cyclesInf pq).arrow]
  simp

/-- The morphism `E.limitPage pq ⟶ E'.limitPage pq` on limit pages induced by a morphism
`f : E ⟶ E'` of spectral sequences. -/
noncomputable def limitPageMap (f : E ⟶ E') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    E.limitPage pq ⟶ E'.limitPage pq :=
  cokernel.map _ _ (boundariesSupMap f pq) (cyclesInfMap f pq)
    (boundariesSupMap_comp_ofLE f pq).symm

/-- A morphism `f : E ⟶ E'` maps `E.limitPagePresentation pq` to `E'.limitPagePresentation pq`,
through its first-page component and over `limitPageMap f pq`. -/
lemma limitPagePresentation_mapsTo (f : E ⟶ E') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    (E.limitPagePresentation pq).MapsTo (E'.limitPagePresentation pq) ((f.hom r₀).f pq)
      (limitPageMap f pq) :=
  SubquotientPresentation.mapsTo_iff.2 ⟨cyclesInfMap f pq, cyclesInfMap_arrow f pq, by
    simp only [π_limitPagePresentation, limitPageMap, cokernel.map]
    exact (cokernel.π_desc _ _ _).symm⟩

@[simp]
lemma limitPageMap_id (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq] :
    limitPageMap (𝟙 E) pq = 𝟙 (E.limitPage pq) := by
  rw [← cancel_epi (E.limitPagePresentation pq).π]
  have h : cyclesInfMap (𝟙 E) pq = 𝟙 _ := by
    rw [← cancel_mono (E.cyclesInf pq).arrow, cyclesInfMap_arrow, Category.id_comp, id_hom,
      HomologicalComplex.id_f, Category.comp_id]
  simp [limitPageMap, limitPage, h]

@[simp, reassoc]
lemma limitPageMap_comp {E'' : SpectralSequence C c r₀} (f : E ⟶ E') (g : E' ⟶ E'') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq]
    [E''.HasCyclesInf pq] [E''.HasBoundariesSup pq] :
    limitPageMap (f ≫ g) pq = limitPageMap f pq ≫ limitPageMap g pq := by
  obtain ⟨ψf, hψf, hψfπ⟩ :=
    SubquotientPresentation.mapsTo_iff.1 (limitPagePresentation_mapsTo f pq)
  obtain ⟨ψg, hψg, hψgπ⟩ :=
    SubquotientPresentation.mapsTo_iff.1 (limitPagePresentation_mapsTo g pq)
  obtain ⟨ψfg, hψfg, hψfgπ⟩ :=
    SubquotientPresentation.mapsTo_iff.1 (limitPagePresentation_mapsTo (f ≫ g) pq)
  have hψ : ψfg = ψf ≫ ψg := by
    rw [← cancel_mono (E''.limitPagePresentation pq).Z.arrow, hψfg, Category.assoc, hψg,
      reassoc_of% hψf]
    simp [comp_hom]
  rw [← cancel_epi (E.limitPagePresentation pq).π, ← hψfgπ, hψ, Category.assoc, hψgπ,
    ← Category.assoc, hψfπ, Category.assoc]

/-- At a position where both `E` and `E'` stabilize from page `s`, `limitPageMap f pq` agrees
with `(f.hom r hr).f pq` under the canonical identifications `StabilizesAt.limitPageIso`. -/
@[reassoc]
lemma StabilizesAt.limitPageIso_hom_comp_limitPageMap (f : E ⟶ E') {s : ℤ}
    (h : E.StabilizesAt pq s) (h' : E'.StabilizesAt pq s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq]
    (r : ℤ) (hr : r₀ ≤ r) (hsr : s ≤ r) :
    (h.limitPageIso r hr hsr).hom ≫ limitPageMap f pq =
      (f.hom r hr).f pq ≫ (h'.limitPageIso r hr hsr).hom :=
  (E.pagePresentation_mapsTo pq f r hr).isoOfEq_hom (limitPagePresentation_mapsTo f pq) _ _ _ _

section Iso

private lemma map_pageFunctor_isoApp_inv (e : E ≅ E') (pq : κ)
    (S : Subobject ((E'.page r₀).X pq)) :
    (Subobject.map (HomologicalComplex.Hom.isoApp
        ((pageFunctor C c r₀ r₀ le_rfl).mapIso e) pq).inv).obj S =
      (Subobject.pullback ((e.hom.hom r₀).f pq)).obj S := by
  let φ := HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀ le_rfl).mapIso e) pq
  have hS : (Subobject.map φ.hom).obj ((Subobject.map φ.inv).obj S) = S :=
    (Subobject.mapIsoToOrderIso φ).right_inv S
  have hφ : φ.hom = (e.hom.hom r₀).f pq := by simp [φ]
  rw [← hφ]
  conv_rhs => rw [← hS]
  exact (Subobject.pullback_map_self _ _).symm

private lemma pullback_cyclesSet_of_iso (e : E ≅ E') (pq : κ) :
    (Subobject.mapIsoToOrderIso
        (HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀ le_rfl).mapIso e) pq).symm) ''
        (E'.cyclesSet pq) =
      E.cyclesSet pq := by
  ext S
  simp only [pageFunctor_obj, Set.mem_image, mem_cyclesSet_iff, Subobject.mapIsoToOrderIso_apply,
    Iso.symm_hom, map_pageFunctor_isoApp_inv]
  constructor
  · rintro ⟨T, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (E.pullback_cyclesSubobject_of_iso pq e r hr).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨E'.cyclesSubobject pq r hr, ⟨r, hr, rfl⟩, E.pullback_cyclesSubobject_of_iso pq e r hr⟩

private lemma pullback_boundariesSet_of_iso (e : E ≅ E') (pq : κ) :
    (Subobject.mapIsoToOrderIso
        (HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀ le_rfl).mapIso e) pq).symm) ''
        (E'.boundariesSet pq) =
      E.boundariesSet pq := by
  ext S
  simp only [pageFunctor_obj, Set.mem_image, mem_boundariesSet_iff,
    Subobject.mapIsoToOrderIso_apply, Iso.symm_hom, map_pageFunctor_isoApp_inv]
  constructor
  · rintro ⟨T, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (E.pullback_boundariesSubobject_of_iso pq e r hr).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨E'.boundariesSubobject pq r hr, ⟨r, hr, rfl⟩,
      E.pullback_boundariesSubobject_of_iso pq e r hr⟩

lemma HasCyclesInf.of_iso (e : E ≅ E') [E.HasCyclesInf pq] : E'.HasCyclesInf pq := by
  let o := Subobject.mapIsoToOrderIso
    (HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀ le_rfl).mapIso e) pq).symm
  refine ⟨⟨o.symm (E.cyclesInf pq), ?_⟩⟩
  rw [← OrderIso.isGLB_image (f := o), pullback_cyclesSet_of_iso e pq]
  exact E.isGLB_cyclesInf pq

lemma hasCyclesInf_iff_of_iso (e : E ≅ E') (pq : κ) : E.HasCyclesInf pq ↔ E'.HasCyclesInf pq :=
  ⟨fun _ ↦ HasCyclesInf.of_iso e, fun _ ↦ HasCyclesInf.of_iso e.symm⟩

lemma HasBoundariesSup.of_iso (e : E ≅ E') [E.HasBoundariesSup pq] : E'.HasBoundariesSup pq := by
  let o := Subobject.mapIsoToOrderIso
    (HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀ le_rfl).mapIso e) pq).symm
  refine ⟨⟨o.symm (E.boundariesSup pq), ?_⟩⟩
  rw [← OrderIso.isLUB_image (f := o), pullback_boundariesSet_of_iso e pq]
  exact E.isLUB_boundariesSup pq

lemma hasBoundariesSup_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.HasBoundariesSup pq ↔ E'.HasBoundariesSup pq :=
  ⟨fun _ ↦ HasBoundariesSup.of_iso e, fun _ ↦ HasBoundariesSup.of_iso e.symm⟩

lemma HasLimitPage.of_iso (e : E ≅ E') [E.HasLimitPage pq] : E'.HasLimitPage pq :=
  { toHasCyclesInf := HasCyclesInf.of_iso e
    toHasBoundariesSup := HasBoundariesSup.of_iso e }

lemma hasLimitPage_iff_of_iso (e : E ≅ E') (pq : κ) : E.HasLimitPage pq ↔ E'.HasLimitPage pq :=
  ⟨fun _ ↦ HasLimitPage.of_iso e, fun _ ↦ HasLimitPage.of_iso e.symm⟩

/-- An isomorphism of spectral sequences induces an isomorphism of their limit pages. -/
noncomputable def limitPageIsoOfIso (e : E ≅ E') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    E.limitPage pq ≅ E'.limitPage pq where
  hom := limitPageMap e.hom pq
  inv := limitPageMap e.inv pq
  hom_inv_id := by rw [← limitPageMap_comp, e.hom_inv_id, limitPageMap_id]
  inv_hom_id := by rw [← limitPageMap_comp, e.inv_hom_id, limitPageMap_id]

@[simp]
lemma limitPageIsoOfIso_hom (e : E ≅ E') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    (limitPageIsoOfIso e pq).hom = limitPageMap e.hom pq := by
  rfl

@[simp]
lemma limitPageIsoOfIso_inv (e : E ≅ E') (pq : κ)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    (limitPageIsoOfIso e pq).inv = limitPageMap e.inv pq := by
  rfl

end Iso

/-- Taking the limit page at `pq` as a functor `SpectralSequence C c r₀ ⥤ C`, when `C` has
countable products and countable coproducts. -/
@[expose, simps]
noncomputable def limitPageFunctor (C : Type*) [Category* C] [Abelian C]
    [HasCountableProducts C] [HasCountableCoproducts C]
    {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ) (pq : κ) :
    SpectralSequence C c r₀ ⥤ C where
  obj E := E.limitPage pq
  map f := limitPageMap f pq

end Naturality

section Rebase

variable (E : SpectralSequence C c r₀) (pq : κ)

private lemma preimage_cyclesSet_fromPage (s : ℤ) (hs : r₀ ≤ s) :
    (E.pagePresentation pq s hs).preimage '' ((E.fromPage s hs).cyclesSet pq) =
      Set.range (fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.val (hs.trans r.property)) := by
  ext S
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, mem_cyclesSet_iff]
  constructor
  · rintro ⟨T, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (E.preimage_fromPage_cyclesSubobject pq s hs r hr).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, E.preimage_fromPage_cyclesSubobject pq s hs r hr⟩

private lemma preimage_boundariesSet_fromPage (s : ℤ) (hs : r₀ ≤ s) :
    (E.pagePresentation pq s hs).preimage '' ((E.fromPage s hs).boundariesSet pq) =
      Set.range (fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property)) := by
  ext S
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, mem_boundariesSet_iff]
  constructor
  · rintro ⟨T, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (E.preimage_fromPage_boundariesSubobject pq s hs r hr).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, E.preimage_fromPage_boundariesSubobject pq s hs r hr⟩

private lemma lowerBounds_cyclesSet_eq_fromPage (s : ℤ) (hs : r₀ ≤ s) :
    lowerBounds (E.cyclesSet pq) =
      lowerBounds (Set.range (fun r : {r : ℤ // s ≤ r} ↦
        E.cyclesSubobject pq r.val (hs.trans r.property))) := by
  ext L
  simp only [mem_lowerBounds, Set.mem_range, Subtype.exists, mem_cyclesSet_iff]
  constructor
  · rintro h _ ⟨r, hr, rfl⟩
    exact h _ ⟨r, hs.trans hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩
    exact (h _ ⟨max r s, le_max_right r s, rfl⟩).trans
      (E.cyclesSubobject_anti pq hr (le_max_left r s))

private lemma upperBounds_boundariesSet_eq_fromPage (s : ℤ) (hs : r₀ ≤ s) :
    upperBounds (E.boundariesSet pq) =
      upperBounds (Set.range (fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property))) := by
  ext U
  simp only [mem_upperBounds, Set.mem_range, Subtype.exists, mem_boundariesSet_iff]
  constructor
  · rintro h _ ⟨r, hr, rfl⟩
    exact h _ ⟨r, hs.trans hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩
    exact (E.boundariesSubobject_mono pq hr (le_max_left r s)).trans
      (h _ ⟨max r s, le_max_right r s, rfl⟩)

lemma hasCyclesInf_fromPage_iff (s : ℤ) (hs : r₀ ≤ s) :
    (E.fromPage s hs).HasCyclesInf pq ↔ E.HasCyclesInf pq := by
  constructor
  · rintro ⟨⟨Z, hZ⟩⟩
    refine ⟨⟨(E.pagePresentation pq s hs).preimage Z, ?_⟩⟩
    rw [IsGLB, lowerBounds_cyclesSet_eq_fromPage E pq s hs,
      ← preimage_cyclesSet_fromPage E pq s hs]
    exact (E.pagePresentation pq s hs).isGLB_preimage_iff
      ((E.fromPage s hs).cyclesSet_nonempty) |>.2 hZ
  · rintro ⟨⟨Z, hZ⟩⟩
    have hZ' : IsGLB
        ((E.pagePresentation pq s hs).preimage '' ((E.fromPage s hs).cyclesSet pq)) Z := by
      rw [preimage_cyclesSet_fromPage, IsGLB, ← lowerBounds_cyclesSet_eq_fromPage E pq s hs]
      exact hZ
    refine ⟨⟨(E.pagePresentation pq s hs).image Z, ?_⟩⟩
    rw [← (E.pagePresentation pq s hs).isGLB_preimage_iff ((E.fromPage s hs).cyclesSet_nonempty),
      (E.pagePresentation pq s hs).preimage_image_of_isGLB
        ((E.fromPage s hs).cyclesSet_nonempty) hZ']
    exact hZ'

lemma hasBoundariesSup_fromPage_iff (s : ℤ) (hs : r₀ ≤ s) :
    (E.fromPage s hs).HasBoundariesSup pq ↔ E.HasBoundariesSup pq := by
  constructor
  · rintro ⟨⟨B, hB⟩⟩
    refine ⟨⟨(E.pagePresentation pq s hs).preimage B, ?_⟩⟩
    rw [IsLUB, upperBounds_boundariesSet_eq_fromPage E pq s hs,
      ← preimage_boundariesSet_fromPage E pq s hs]
    exact (E.pagePresentation pq s hs).isLUB_preimage_iff
      ((E.fromPage s hs).boundariesSet_nonempty) |>.2 hB
  · rintro ⟨⟨B, hB⟩⟩
    have hB' : IsLUB
        ((E.pagePresentation pq s hs).preimage '' ((E.fromPage s hs).boundariesSet pq)) B := by
      rw [preimage_boundariesSet_fromPage, IsLUB, ← upperBounds_boundariesSet_eq_fromPage E pq s hs]
      exact hB
    refine ⟨⟨(E.pagePresentation pq s hs).image B, ?_⟩⟩
    rw [← (E.pagePresentation pq s hs).isLUB_preimage_iff
        ((E.fromPage s hs).boundariesSet_nonempty),
      (E.pagePresentation pq s hs).preimage_image_of_isLUB
        ((E.fromPage s hs).boundariesSet_nonempty) hB']
    exact hB'

lemma hasLimitPage_fromPage_iff (s : ℤ) (hs : r₀ ≤ s) :
    (E.fromPage s hs).HasLimitPage pq ↔ E.HasLimitPage pq :=
  ⟨fun h ↦
    { toHasCyclesInf := (E.hasCyclesInf_fromPage_iff pq s hs).1 h.toHasCyclesInf
      toHasBoundariesSup := (E.hasBoundariesSup_fromPage_iff pq s hs).1 h.toHasBoundariesSup },
   fun h ↦
    { toHasCyclesInf := (E.hasCyclesInf_fromPage_iff pq s hs).2 h.toHasCyclesInf
      toHasBoundariesSup := (E.hasBoundariesSup_fromPage_iff pq s hs).2 h.toHasBoundariesSup }⟩

instance HasCyclesInf.fromPage (s : ℤ) (hs : r₀ ≤ s) [E.HasCyclesInf pq] :
    (E.fromPage s hs).HasCyclesInf pq :=
  (E.hasCyclesInf_fromPage_iff pq s hs).2 inferInstance

instance HasBoundariesSup.fromPage (s : ℤ) (hs : r₀ ≤ s) [E.HasBoundariesSup pq] :
    (E.fromPage s hs).HasBoundariesSup pq :=
  (E.hasBoundariesSup_fromPage_iff pq s hs).2 inferInstance

instance HasLimitPage.fromPage (s : ℤ) (hs : r₀ ≤ s) [E.HasLimitPage pq] :
    (E.fromPage s hs).HasLimitPage pq :=
  (E.hasLimitPage_fromPage_iff pq s hs).2 inferInstance

/-- Under the page-`s` presentation, the infinite cycles of `E.fromPage s hs` correspond to
`E.cyclesInf pq`. -/
lemma preimage_fromPage_cyclesInf (s : ℤ) (hs : r₀ ≤ s) [E.HasCyclesInf pq] :
    (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).cyclesInf pq) = E.cyclesInf pq := by
  refine (cyclesInf_eq_of_isGLB ?_).symm
  rw [IsGLB, lowerBounds_cyclesSet_eq_fromPage E pq s hs,
    ← preimage_cyclesSet_fromPage E pq s hs]
  exact (E.pagePresentation pq s hs).isGLB_preimage_iff
    ((E.fromPage s hs).cyclesSet_nonempty) |>.2 ((E.fromPage s hs).isGLB_cyclesInf pq)

/-- Under the page-`s` presentation, the infinite boundaries of `E.fromPage s hs` correspond to
`E.boundariesSup pq`. -/
lemma preimage_fromPage_boundariesSup (s : ℤ) (hs : r₀ ≤ s) [E.HasBoundariesSup pq] :
    (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).boundariesSup pq) =
      E.boundariesSup pq := by
  refine (boundariesSup_eq_of_isLUB ?_).symm
  rw [IsLUB, upperBounds_boundariesSet_eq_fromPage E pq s hs,
    ← preimage_boundariesSet_fromPage E pq s hs]
  exact (E.pagePresentation pq s hs).isLUB_preimage_iff
    ((E.fromPage s hs).boundariesSet_nonempty) |>.2 ((E.fromPage s hs).isLUB_boundariesSup pq)

/-- The canonical isomorphism between the limit page of a rebased spectral sequence
`E.fromPage s hs` and the limit page of `E`. -/
noncomputable def limitPageFromPageIso (s : ℤ) (hs : r₀ ≤ s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq] :
    (E.fromPage s hs).limitPage pq ≅ E.limitPage pq :=
  ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).isoOfEq
    (E.limitPagePresentation pq)
    (by rw [SubquotientPresentation.trans_B, limitPagePresentation_B,
      E.preimage_fromPage_boundariesSup pq s hs, limitPagePresentation_B])
    (by rw [SubquotientPresentation.trans_Z, limitPagePresentation_Z,
      E.preimage_fromPage_cyclesInf pq s hs, limitPagePresentation_Z])

/-- Compatibility of `limitPageFromPageIso` with the subquotient projections. -/
@[reassoc]
lemma π_limitPageFromPageIso_hom (s : ℤ) (hs : r₀ ≤ s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq] :
    ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).π ≫
      (E.limitPageFromPageIso pq s hs).hom =
      ofLE _ _ (by rw [SubquotientPresentation.trans_Z, limitPagePresentation_Z,
        E.preimage_fromPage_cyclesInf pq s hs, limitPagePresentation_Z]) ≫
        (E.limitPagePresentation pq).π :=
  SubquotientPresentation.π_isoOfEq_hom _ _ _ _

/-- Naturality of `limitPageFromPageIso` with respect to morphisms of spectral sequences. -/
@[reassoc]
lemma limitPageFromPageIso_hom_comp_limitPageMap {E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s)
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    [E'.HasCyclesInf pq] [E'.HasBoundariesSup pq] :
    (E.limitPageFromPageIso pq s hs).hom ≫ limitPageMap f pq =
      limitPageMap (fromPageMap s hs f) pq ≫ (E'.limitPageFromPageIso pq s hs).hom := by
  have hmaps := (E.fromPage s hs).limitPagePresentation_mapsTo (fromPageMap s hs f) pq
  rw [fromPageMap_hom] at hmaps
  exact ((E.pagePresentation_mapsTo pq f s hs).trans hmaps).isoOfEq_hom
    (E.limitPagePresentation_mapsTo f pq) _ _ _ _

end Rebase

section Vanishing

variable {E : SpectralSequence C c r₀} {pq : κ}

lemma isZero_limitPage_iff_boundariesSup_eq_cyclesInf
    [E.HasCyclesInf pq] [E.HasBoundariesSup pq] :
    IsZero (E.limitPage pq) ↔ E.boundariesSup pq = E.cyclesInf pq :=
  (E.limitPagePresentation pq).isZero_iff_B_eq_Z

/-- If `(E.page r hr).X pq` vanishes on some page `r ≥ r₀`, then `E.limitPage pq` vanishes. -/
lemma isZero_limitPage_of_isZero [E.HasCyclesInf pq] [E.HasBoundariesSup pq]
    {r : ℤ} (hr : r₀ ≤ r) (h : IsZero ((E.page r hr).X pq)) :
    IsZero (E.limitPage pq) := by
  rw [isZero_limitPage_iff_boundariesSup_eq_cyclesInf]
  have hBZ : E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
    (E.isZero_page_X_iff pq r hr).1 h
  exact le_antisymm (E.boundariesSup_le_cyclesInf pq)
    ((cyclesInf_le r hr).trans (hBZ.symm.trans_le (boundariesSubobject_le_boundariesSup r hr)))

end Vanishing

end CategoryTheory.SpectralSequence
