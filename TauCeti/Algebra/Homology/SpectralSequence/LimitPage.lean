/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.Algebra.Homology.SpectralSequence.Tower
public import TauCeti.CategoryTheory.Subobject.Limits

/-!
# The limit page of a spectral sequence

Given a spectral sequence `E : SpectralSequence C c r₀` in an abelian category `C` and a position
`pq : κ`, the descending cycle tower `{Z_r(pq) | r ≥ r₀}` and ascending boundary tower
`{B_r(pq) | r ≥ r₀}` live in `Subobject ((E.page r₀).X pq)` with `B_{r₁}(pq) ≤ Z_{r₂}(pq)` for all
`r₁, r₂ ≥ r₀`. When the greatest lower bound `Z_∞(pq)` of the cycles and the least upper bound
`B_∞(pq)` of the boundaries exist (`CategoryTheory.SpectralSequence.HasLimitPageAt`), we have
`B_∞(pq) ≤ Z_∞(pq)` and the **limit page** `E_∞(pq)` is the cokernel of
`Subobject.ofLE B_∞(pq) Z_∞(pq)`.

## Main definitions and results

* `CategoryTheory.SpectralSequence.HasLimitPageAt`: existence of the greatest lower bound `Z_∞(pq)`
  of the cycle tower and the least upper bound `B_∞(pq)` of the boundary tower.
* `CategoryTheory.SpectralSequence.infiniteCycles`, `infiniteBoundaries`, `limitPage`, and
  `limitPagePresentation`: `Z_∞(pq)`, `B_∞(pq)`, `E_∞(pq)`, and its subquotient presentation inside
  `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.hasLimitPageAt_of_stabilisesAt` and `limitPageIsoPageX`: at a
  stabilising position, `E_∞(pq)` exists in any abelian category and is canonically isomorphic to
  `(E.page s).X pq`, compatibly with `pageXIsoOfStabilises`.
* `hasLimitPageAt_of_hasCountableProducts_of_hasCountableCoproducts`: if `C` has countable products
  and coproducts, `E_∞(pq)` exists at every position, with `Z_∞(pq)` as a kernel subobject of a
  product of cokernels and `B_∞(pq)` as an image subobject of a coproduct.
* `CategoryTheory.SpectralSequence.Hom.limitPageMap`: functoriality of `E_∞(pq)` with respect to
  morphisms of spectral sequences, agreeing with the page components at stabilising positions.
* `CategoryTheory.SpectralSequence.hasLimitPageAt_fromPage_iff` and `limitPageIsoFromPage`:
  invariance of `HasLimitPageAt` and `E_∞(pq)` under rebasing to a later page `s ≥ r₀`.
* `CategoryTheory.SpectralSequence.isZero_limitPage_of_isZero_page_X`: vanishing of
  `(E.page r).X pq` on any page implies vanishing of `E_∞(pq)`.

## References

* Stacks Project, Tag 011O (Definition 12.20.2).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.SpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Defs

/-- A spectral sequence `E` *has a limit page at `pq`* if the cycle tower `{Z_r(pq) | r ≥ r₀}` has
a greatest lower bound and the boundary tower `{B_r(pq) | r ≥ r₀}` has a least upper bound in
`Subobject ((E.page r₀).X pq)`. -/
class HasLimitPageAt (E : SpectralSequence C c r₀) (pq : κ) : Prop where
  exists_isGLB_cycles :
    ∃ Z, IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2) Z
  exists_isLUB_boundaries :
    ∃ B, IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2) B

/-- The infinite-cycle subobject `Z_∞(pq) = ⋀_{r ≥ r₀} Z_r(pq)` in
`Subobject ((E.page r₀).X pq)`. -/
noncomputable def infiniteCycles (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    Subobject ((E.page r₀).X pq) :=
  (HasLimitPageAt.exists_isGLB_cycles (E := E) (pq := pq)).choose

/-- The infinite-boundary subobject `B_∞(pq) = ⋁_{r ≥ r₀} B_r(pq)` in
`Subobject ((E.page r₀).X pq)`. -/
noncomputable def infiniteBoundaries (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    Subobject ((E.page r₀).X pq) :=
  (HasLimitPageAt.exists_isLUB_boundaries (E := E) (pq := pq)).choose

theorem isGLB_infiniteCycles (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2)
      (E.infiniteCycles pq) :=
  (HasLimitPageAt.exists_isGLB_cycles (E := E) (pq := pq)).choose_spec

theorem isLUB_infiniteBoundaries (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2)
      (E.infiniteBoundaries pq) :=
  (HasLimitPageAt.exists_isLUB_boundaries (E := E) (pq := pq)).choose_spec

theorem infiniteCycles_eq_of_isGLB (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq]
    {Z : Subobject ((E.page r₀).X pq)}
    (hZ : IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2) Z) :
    E.infiniteCycles pq = Z :=
  (E.isGLB_infiniteCycles pq).unique hZ

theorem infiniteBoundaries_eq_of_isLUB (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq]
    {B : Subobject ((E.page r₀).X pq)}
    (hB : IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2) B) :
    E.infiniteBoundaries pq = B :=
  (E.isLUB_infiniteBoundaries pq).unique hB

theorem infiniteCycles_le_cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasLimitPageAt pq] (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.infiniteCycles pq ≤ E.cyclesSubobject pq r hr :=
  (E.isGLB_infiniteCycles pq).1 ⟨⟨r, hr⟩, rfl⟩

theorem le_infiniteCycles_iff (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq]
    {S : Subobject ((E.page r₀).X pq)} :
    S ≤ E.infiniteCycles pq ↔ ∀ (r : ℤ) (hr : r₀ ≤ r), S ≤ E.cyclesSubobject pq r hr := by
  constructor
  · intro h r hr
    exact h.trans (E.infiniteCycles_le_cyclesSubobject pq r hr)
  · intro h
    refine (E.isGLB_infiniteCycles pq).2 ?_
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    exact h r hr

theorem boundariesSubobject_le_infiniteBoundaries (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasLimitPageAt pq] (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr ≤ E.infiniteBoundaries pq :=
  (E.isLUB_infiniteBoundaries pq).1 ⟨⟨r, hr⟩, rfl⟩

theorem infiniteBoundaries_le_iff (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq]
    {S : Subobject ((E.page r₀).X pq)} :
    E.infiniteBoundaries pq ≤ S ↔ ∀ (r : ℤ) (hr : r₀ ≤ r), E.boundariesSubobject pq r hr ≤ S := by
  constructor
  · intro h r hr
    exact (E.boundariesSubobject_le_infiniteBoundaries pq r hr).trans h
  · intro h
    refine (E.isLUB_infiniteBoundaries pq).2 ?_
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    exact h r hr

/-- Infinite boundaries lie inside infinite cycles: `B_∞(pq) ≤ Z_∞(pq)`. -/
theorem infiniteBoundaries_le_infiniteCycles (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasLimitPageAt pq] :
    E.infiniteBoundaries pq ≤ E.infiniteCycles pq :=
  (E.infiniteBoundaries_le_iff pq).mpr fun r₁ h₁ ↦
    (E.le_infiniteCycles_iff pq).mpr fun r₂ h₂ ↦
      E.boundariesSubobject_le_cyclesSubobject_of_any pq r₁ r₂ h₁ h₂

/-- The limit page object `E_∞(pq) = Z_∞(pq) / B_∞(pq)` at position `pq`. -/
@[expose]
noncomputable def limitPage (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] : C :=
  cokernel (Subobject.ofLE (E.infiniteBoundaries pq) (E.infiniteCycles pq)
    (E.infiniteBoundaries_le_infiniteCycles pq))

/-- The canonical subquotient presentation of `E.limitPage pq` inside `(E.page r₀).X pq`, with
denominator `B_∞(pq)` and numerator `Z_∞(pq)`. -/
noncomputable abbrev limitPagePresentation (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasLimitPageAt pq] :
    TauCeti.SubquotientPresentation ((E.page r₀).X pq) (E.limitPage pq) :=
  TauCeti.SubquotientPresentation.ofLE (E.infiniteBoundaries pq) (E.infiniteCycles pq)
    (E.infiniteBoundaries_le_infiniteCycles pq)

/-- The limit page `E_∞(pq)` vanishes if and only if `B_∞(pq) = Z_∞(pq)`. -/
theorem isZero_limitPage_iff_infiniteBoundaries_eq_infiniteCycles (E : SpectralSequence C c r₀)
    (pq : κ) [E.HasLimitPageAt pq] :
    IsZero (E.limitPage pq) ↔ E.infiniteBoundaries pq = E.infiniteCycles pq :=
  (E.limitPagePresentation pq).isZero_iff

/-- If `(E.page r).X pq` vanishes on some page `r ≥ r₀` and the limit page exists, then `E_∞(pq)`
vanishes. -/
theorem isZero_limitPage_of_isZero_page_X (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r) (h : IsZero ((E.page r hr).X pq)) [E.HasLimitPageAt pq] :
    IsZero (E.limitPage pq) := by
  rw [isZero_limitPage_iff_infiniteBoundaries_eq_infiniteCycles]
  refine le_antisymm (E.infiniteBoundaries_le_infiniteCycles pq) ?_
  calc
    E.infiniteCycles pq ≤ E.cyclesSubobject pq r hr :=
      E.infiniteCycles_le_cyclesSubobject pq r hr
    _ = E.boundariesSubobject pq r hr :=
      ((E.isZero_page_X_iff_boundariesSubobject_eq_cyclesSubobject pq r hr).mp h).symm
    _ ≤ E.infiniteBoundaries pq := E.boundariesSubobject_le_infiniteBoundaries pq r hr

end Defs

section Existence

/-- If all differentials leaving `pq` vanish from page `s` onward, then `Z_s(pq)` is the greatest
lower bound of the cycle tower. -/
theorem isGLB_cyclesSubobject_of_forall_dFrom_eq_zero (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2)
      (E.cyclesSubobject pq s hs) := by
  refine ⟨?_, fun M hM ↦ hM ⟨⟨s, hs⟩, rfl⟩⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  dsimp only
  rcases le_total s r with hsr | hrs
  · rw [E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs h r hsr]
  · exact E.cyclesSubobject_anti pq hr hrs

/-- If all differentials entering `pq` vanish from page `s` onward, then `B_s(pq)` is the least
upper bound of the boundary tower. -/
theorem isLUB_boundariesSubobject_of_forall_dTo_eq_zero (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2)
      (E.boundariesSubobject pq s hs) := by
  refine ⟨?_, fun M hM ↦ hM ⟨⟨s, hs⟩, rfl⟩⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  dsimp only
  rcases le_total s r with hsr | hrs
  · rw [E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs h r hsr]
  · exact E.boundariesSubobject_mono pq hr hrs

/-- Regularity at `pq` implies that the greatest lower bound `Z_∞(pq)` exists. -/
theorem exists_isGLB_cyclesSubobject_of_isRegularAt (E : SpectralSequence C c r₀) (pq : κ)
    (h : E.IsRegularAt pq) :
    ∃ Z, IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2) Z := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨E.cyclesSubobject pq s hs, E.isGLB_cyclesSubobject_of_forall_dFrom_eq_zero pq hs h⟩

/-- Coregularity at `pq` implies that the least upper bound `B_∞(pq)` exists. -/
theorem exists_isLUB_boundariesSubobject_of_isCoregularAt (E : SpectralSequence C c r₀) (pq : κ)
    (h : E.IsCoregularAt pq) :
    ∃ B, IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2) B := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨E.boundariesSubobject pq s hs, E.isLUB_boundariesSubobject_of_forall_dTo_eq_zero pq hs h⟩

/-- If `E` is both regular and coregular at `pq`, then `E` has a limit page at `pq` in any abelian
category. -/
theorem hasLimitPageAt_of_isRegularAt_of_isCoregularAt (E : SpectralSequence C c r₀) (pq : κ)
    (hreg : E.IsRegularAt pq) (hcoreg : E.IsCoregularAt pq) :
    E.HasLimitPageAt pq where
  exists_isGLB_cycles := E.exists_isGLB_cyclesSubobject_of_isRegularAt pq hreg
  exists_isLUB_boundaries := E.exists_isLUB_boundariesSubobject_of_isCoregularAt pq hcoreg

/-- If `E` stabilises at `pq` from page `s`, then `E` has a limit page at `pq` in any abelian
category. -/
theorem hasLimitPageAt_of_stabilisesAt (E : SpectralSequence C c r₀) (pq : κ) {s : ℤ}
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) :
    E.HasLimitPageAt pq :=
  E.hasLimitPageAt_of_isRegularAt_of_isCoregularAt pq h.isRegularAt h.isCoregularAt

theorem infiniteCycles_eq_of_stabilisesAt (E : SpectralSequence C c r₀) (pq : κ) {s : ℤ}
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) [E.HasLimitPageAt pq] :
    E.infiniteCycles pq = E.cyclesSubobject pq s hs :=
  E.infiniteCycles_eq_of_isGLB pq
    (E.isGLB_cyclesSubobject_of_forall_dFrom_eq_zero pq hs (fun _ hsr ↦ h.dFrom_eq_zero hsr))

theorem infiniteBoundaries_eq_of_stabilisesAt (E : SpectralSequence C c r₀) (pq : κ) {s : ℤ}
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) [E.HasLimitPageAt pq] :
    E.infiniteBoundaries pq = E.boundariesSubobject pq s hs :=
  E.infiniteBoundaries_eq_of_isLUB pq
    (E.isLUB_boundariesSubobject_of_forall_dTo_eq_zero pq hs (fun _ hsr ↦ h.dTo_eq_zero hsr))

/-- In an abelian category with countable products, the kernel subobject of the canonical map
`(E.page r₀).X pq ⟶ ∏_{r ≥ r₀} cokernel (Z_r(pq)).arrow` is the greatest lower bound of the cycle
tower. -/
theorem isGLB_cyclesSubobject_kernelSubobject_piLift [HasCountableProducts C]
    (E : SpectralSequence C c r₀) (pq : κ) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2)
      (kernelSubobject (Pi.lift fun r : {r : ℤ // r₀ ≤ r} ↦
        cokernel.π (E.cyclesSubobject pq r.1 r.2).arrow)) :=
  Subobject.isGLB_kernelSubobject_piLift (fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2)

/-- In an abelian category with countable coproducts, the image subobject of the canonical map
`∐_{r ≥ r₀} B_r(pq) ⟶ (E.page r₀).X pq` is the least upper bound of the boundary tower. -/
theorem isLUB_boundariesSubobject_imageSubobject_sigmaDesc [HasCountableCoproducts C]
    (E : SpectralSequence C c r₀) (pq : κ) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2)
      (imageSubobject (Sigma.desc fun r : {r : ℤ // r₀ ≤ r} ↦
        (E.boundariesSubobject pq r.1 r.2).arrow)) :=
  Subobject.isLUB_imageSubobject_sigmaDesc
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2)

/-- Explicit presentation of `Z_∞(pq)` in an abelian category with countable products. -/
theorem infiniteCycles_eq_kernelSubobject_piLift [HasCountableProducts C]
    (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    E.infiniteCycles pq =
      kernelSubobject (Pi.lift fun r : {r : ℤ // r₀ ≤ r} ↦
        cokernel.π (E.cyclesSubobject pq r.1 r.2).arrow) :=
  E.infiniteCycles_eq_of_isGLB pq (E.isGLB_cyclesSubobject_kernelSubobject_piLift pq)

/-- Explicit presentation of `B_∞(pq)` in an abelian category with countable coproducts. -/
theorem infiniteBoundaries_eq_imageSubobject_sigmaDesc [HasCountableCoproducts C]
    (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    E.infiniteBoundaries pq =
      imageSubobject (Sigma.desc fun r : {r : ℤ // r₀ ≤ r} ↦
        (E.boundariesSubobject pq r.1 r.2).arrow) :=
  E.infiniteBoundaries_eq_of_isLUB pq (E.isLUB_boundariesSubobject_imageSubobject_sigmaDesc pq)

/-- In an abelian category with countable products and countable coproducts, every spectral
sequence has a limit page at every position. -/
instance hasLimitPageAt_of_hasCountableProducts_of_hasCountableCoproducts
    [HasCountableProducts C] [HasCountableCoproducts C]
    (E : SpectralSequence C c r₀) (pq : κ) :
    E.HasLimitPageAt pq where
  exists_isGLB_cycles := ⟨_, E.isGLB_cyclesSubobject_kernelSubobject_piLift pq⟩
  exists_isLUB_boundaries := ⟨_, E.isLUB_boundariesSubobject_imageSubobject_sigmaDesc pq⟩

/-- If `E` is regular at `pq` and `C` has countable coproducts, then `E` has a limit page at
`pq`. -/
theorem hasLimitPageAt_of_isRegularAt_of_hasCountableCoproducts [HasCountableCoproducts C]
    (E : SpectralSequence C c r₀) (pq : κ) (hreg : E.IsRegularAt pq) :
    E.HasLimitPageAt pq where
  exists_isGLB_cycles := E.exists_isGLB_cyclesSubobject_of_isRegularAt pq hreg
  exists_isLUB_boundaries := ⟨_, E.isLUB_boundariesSubobject_imageSubobject_sigmaDesc pq⟩

/-- If `E` is coregular at `pq` and `C` has countable products, then `E` has a limit page at
`pq`. -/
theorem hasLimitPageAt_of_hasCountableProducts_of_isCoregularAt [HasCountableProducts C]
    (E : SpectralSequence C c r₀) (pq : κ) (hcoreg : E.IsCoregularAt pq) :
    E.HasLimitPageAt pq where
  exists_isGLB_cycles := ⟨_, E.isGLB_cyclesSubobject_kernelSubobject_piLift pq⟩
  exists_isLUB_boundaries := E.exists_isLUB_boundariesSubobject_of_isCoregularAt pq hcoreg

end Existence

section StabilisedIso

/-- At a stabilising position `pq` from page `s`, the canonical isomorphism
`E.limitPage pq ≅ (E.page s).X pq`. -/
noncomputable def limitPageIsoPageX (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) [E.HasLimitPageAt pq] :
    E.limitPage pq ≅ (E.page s hs).X pq :=
  (E.limitPagePresentation pq).mapInducedIso (E.pagePresentation pq s hs) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Subobject.exists_iso_map, Subobject.map_id]
      exact E.infiniteCycles_eq_of_stabilisesAt pq hs h)
    (by
      rw [Iso.refl_hom, Subobject.exists_iso_map, Subobject.map_id]
      exact E.infiniteBoundaries_eq_of_stabilisesAt pq hs h)

/-- Compatibility of `limitPageIsoPageX` with `pageXIsoOfStabilises`: the identification of
`E_∞(pq)` with page `s` followed by the stabilisation isomorphism from page `s` to page `r ≥ s`
equals the identification of `E_∞(pq)` with page `r`. -/
theorem limitPageIsoPageX_trans_pageXIsoOfStabilises (E : SpectralSequence C c r₀) (pq : κ)
    {s r : ℤ} (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (hsr : s ≤ r) [E.HasLimitPageAt pq] :
    E.limitPageIsoPageX pq s hs h ≪≫ E.pageXIsoOfStabilises pq s hs h r hsr =
      E.limitPageIsoPageX pq r (hs.trans hsr) (h.of_le hsr) := by
  ext
  simp only [Iso.trans_hom, limitPageIsoPageX, TauCeti.SubquotientPresentation.mapInducedIso_hom,
    Iso.refl_hom]
  have heq :
      (E.limitPagePresentation pq).mapInduced (E.pagePresentation pq r (hs.trans hsr)) (𝟙 _)
          (by
            rw [Subobject.exists_iso_map, Subobject.map_id]
            exact (E.infiniteCycles_eq_of_stabilisesAt pq (hs.trans hsr) (h.of_le hsr)).le)
          (by
            rw [Subobject.exists_iso_map, Subobject.map_id]
            exact (E.infiniteBoundaries_eq_of_stabilisesAt pq (hs.trans hsr) (h.of_le hsr)).le) =
        ((E.limitPagePresentation pq).transIso (Iso.refl _)).mapInduced
          ((E.pagePresentation pq s hs).transIso (E.pageXIsoOfStabilises pq s hs h r hsr))
          (𝟙 _)
          (by
            rw [Subobject.exists_iso_map, Subobject.map_id]
            exact (E.infiniteCycles_eq_of_stabilisesAt pq hs h).le)
          (by
            rw [Subobject.exists_iso_map, Subobject.map_id]
            exact (E.infiniteBoundaries_eq_of_stabilisesAt pq hs h).le) := by
    simp only [pagePresentation_eq_transIso_pageXIsoOfStabilises E pq s hs h r hsr,
      TauCeti.SubquotientPresentation.transIso_refl]
  rw [heq, TauCeti.SubquotientPresentation.mapInduced_transIso, Iso.refl_inv, Category.id_comp]

end StabilisedIso

section Functoriality

/-- A morphism `f : E ⟶ E'` maps `Z_∞(E, pq)` into `Z_∞(E', pq)` via direct image along
`(f.hom r₀).f pq`. -/
theorem Hom.exists_infiniteCycles_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.infiniteCycles pq) ≤ E'.infiniteCycles pq :=
  (E'.le_infiniteCycles_iff pq).mpr fun r hr ↦
    ((Subobject.exists ((f.hom r₀).f pq)).monotone
      (E.infiniteCycles_le_cyclesSubobject pq r hr)).trans (f.exists_cyclesSubobject_le pq r hr)

/-- Adjoint form: `Z_∞(E, pq)` lies below the pullback of `Z_∞(E', pq)` along `(f.hom r₀).f pq`. -/
theorem Hom.infiniteCycles_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.infiniteCycles pq ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.infiniteCycles pq) :=
  (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le.mp (f.exists_infiniteCycles_le pq)

/-- A morphism `f : E ⟶ E'` maps `B_∞(E, pq)` into `B_∞(E', pq)` via direct image along
`(f.hom r₀).f pq`. -/
theorem Hom.exists_infiniteBoundaries_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.infiniteBoundaries pq) ≤ E'.infiniteBoundaries pq :=
  (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le.mpr <|
    (E.infiniteBoundaries_le_iff pq).mpr fun r hr ↦
      (f.boundariesSubobject_le_pullback pq r hr).trans
        ((Subobject.pullback ((f.hom r₀).f pq)).monotone
          (E'.boundariesSubobject_le_infiniteBoundaries pq r hr))

/-- Adjoint form: `B_∞(E, pq)` lies below the pullback of `B_∞(E', pq)` along `(f.hom r₀).f pq`. -/
theorem Hom.infiniteBoundaries_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.infiniteBoundaries pq ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.infiniteBoundaries pq) :=
  (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le.mp
    (f.exists_infiniteBoundaries_le pq)

/-- The morphism `E_∞(f, pq) : E.limitPage pq ⟶ E'.limitPage pq` induced by a morphism
`f : E ⟶ E'` of spectral sequences when both have limit pages at `pq`. -/
noncomputable def Hom.limitPageMap {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ⟶ E'.limitPage pq :=
  (E.limitPagePresentation pq).mapInduced (E'.limitPagePresentation pq) ((f.hom r₀).f pq)
    (f.exists_infiniteCycles_le pq) (f.exists_infiniteBoundaries_le pq)

@[simp]
theorem limitPageMap_id (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    (𝟙 E : E ⟶ E).limitPageMap pq = 𝟙 (E.limitPage pq) := by
  dsimp only [Hom.limitPageMap]
  have hid : ((𝟙 E : E ⟶ E).hom r₀).f pq = 𝟙 ((E.page r₀).X pq) := rfl
  simpa only [hid] using (E.limitPagePresentation pq).mapInduced_id
    (by rw [Subobject.exists_iso_map, Subobject.map_id])
    (by rw [Subobject.exists_iso_map, Subobject.map_id])

@[reassoc, simp]
theorem limitPageMap_comp {E E' E'' : SpectralSequence C c r₀} (f : E ⟶ E') (g : E' ⟶ E'')
    (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] [E''.HasLimitPageAt pq] :
    (f ≫ g).limitPageMap pq = f.limitPageMap pq ≫ g.limitPageMap pq := by
  dsimp only [Hom.limitPageMap]
  exact (E.limitPagePresentation pq).mapInduced_comp (E'.limitPagePresentation pq)
    (E''.limitPagePresentation pq) ((f.hom r₀).f pq) ((g.hom r₀).f pq)
    (f.exists_infiniteCycles_le pq) (f.exists_infiniteBoundaries_le pq)
    (g.exists_infiniteCycles_le pq) (g.exists_infiniteBoundaries_le pq)

/-- Agreement of `limitPageMap` with the page-`s` component `(f.hom s).f pq` at a stabilising
position. -/
@[reassoc]
theorem Hom.limitPageMap_comp_limitPageIsoPageX_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (pq : κ) (s : ℤ) (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (h' : E'.StabilisesAt pq s hs)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    f.limitPageMap pq ≫ (E'.limitPageIsoPageX pq s hs h').hom =
      (E.limitPageIsoPageX pq s hs h).hom ≫ (f.hom s hs).f pq := by
  have h1 := (E.limitPagePresentation pq).mapInduced_comp (E'.limitPagePresentation pq)
    (E'.pagePresentation pq s hs) ((f.hom r₀).f pq) (𝟙 _)
    (f.exists_infiniteCycles_le pq) (f.exists_infiniteBoundaries_le pq)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E'.infiniteCycles_eq_of_stabilisesAt pq hs h').le)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E'.infiniteBoundaries_eq_of_stabilisesAt pq hs h').le)
  have h2 := (E.limitPagePresentation pq).mapInduced_comp (E.pagePresentation pq s hs)
    (E'.pagePresentation pq s hs) (𝟙 _) ((f.hom r₀).f pq)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E.infiniteCycles_eq_of_stabilisesAt pq hs h).le)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E.infiniteBoundaries_eq_of_stabilisesAt pq hs h).le)
    (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs)
  rw [← f.mapInduced_pagePresentation pq s hs]
  simp only [Hom.limitPageMap, limitPageIsoPageX, TauCeti.SubquotientPresentation.mapInducedIso_hom,
    Iso.refl_hom, ← h1, ← h2, Category.comp_id, Category.id_comp]

/-- Existence of a limit page at `pq` is transported along isomorphisms of spectral sequences. -/
theorem hasLimitPageAt_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] :
    E'.HasLimitPageAt pq := by
  let f := (e.hom.hom r₀).f pq
  let g := (e.inv.hom r₀).f pq
  have hfg : f ≫ g = 𝟙 _ := by
    have := congrArg (fun u : E ⟶ E ↦ (u.hom r₀).f pq) e.hom_inv_id
    simpa only [comp_hom, id_hom, HomologicalComplex.comp_f, HomologicalComplex.id_f] using this
  have hgf : g ≫ f = 𝟙 _ := by
    have := congrArg (fun u : E' ⟶ E' ↦ (u.hom r₀).f pq) e.inv_hom_id
    simpa only [comp_hom, id_hom, HomologicalComplex.comp_f, HomologicalComplex.id_f] using this
  have hcancel_gf : ∀ S, (Subobject.exists f).obj ((Subobject.exists g).obj S) = S := fun S ↦ by
    rw [← Subobject.exists_comp, hgf, Subobject.exists_iso_map, Subobject.map_id]
  have hcancel_fg : ∀ S, (Subobject.exists g).obj ((Subobject.exists f).obj S) = S := fun S ↦ by
    rw [← Subobject.exists_comp, hfg, Subobject.exists_iso_map, Subobject.map_id]
  refine ⟨⟨(Subobject.exists f).obj (E.infiniteCycles pq), ?_, ?_⟩,
    ⟨(Subobject.exists f).obj (E.infiniteBoundaries pq), ?_, ?_⟩⟩
  · rintro _ ⟨⟨r, hr⟩, rfl⟩
    dsimp only
    rw [← exists_cyclesSubobject_eq_of_iso e pq r hr]
    exact (Subobject.exists f).monotone (E.infiniteCycles_le_cyclesSubobject pq r hr)
  · intro M hM
    rw [← hcancel_gf M]
    refine (Subobject.exists f).monotone ((E.le_infiniteCycles_iff pq).mpr fun r hr ↦ ?_)
    have h1 := (Subobject.exists g).monotone (hM ⟨⟨r, hr⟩, rfl⟩)
    dsimp only at h1
    rwa [← exists_cyclesSubobject_eq_of_iso e pq r hr, hcancel_fg] at h1
  · rintro _ ⟨⟨r, hr⟩, rfl⟩
    dsimp only
    rw [← exists_boundariesSubobject_eq_of_iso e pq r hr]
    exact (Subobject.exists f).monotone (E.boundariesSubobject_le_infiniteBoundaries pq r hr)
  · intro M hM
    rw [← hcancel_gf M]
    refine (Subobject.exists f).monotone ((E.infiniteBoundaries_le_iff pq).mpr fun r hr ↦ ?_)
    have h1 := (Subobject.exists g).monotone (hM ⟨⟨r, hr⟩, rfl⟩)
    dsimp only at h1
    rwa [← exists_boundariesSubobject_eq_of_iso e pq r hr, hcancel_fg] at h1

/-- Isomorphic spectral sequences have limit pages at the same positions. -/
theorem hasLimitPageAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) :
    E.HasLimitPageAt pq ↔ E'.HasLimitPageAt pq :=
  ⟨fun _ ↦ hasLimitPageAt_of_iso e pq, fun _ ↦ hasLimitPageAt_of_iso e.symm pq⟩

/-- An isomorphism `e : E ≅ E'` induces an isomorphism `E.limitPage pq ≅ E'.limitPage pq`. -/
noncomputable def limitPageIsoOfIso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ≅ E'.limitPage pq where
  hom := e.hom.limitPageMap pq
  inv := e.inv.limitPageMap pq
  hom_inv_id := by rw [← limitPageMap_comp, Iso.hom_inv_id, limitPageMap_id]
  inv_hom_id := by rw [← limitPageMap_comp, Iso.inv_hom_id, limitPageMap_id]

@[simp]
theorem limitPageIsoOfIso_hom {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).hom = e.hom.limitPageMap pq := by
  rfl

@[simp]
theorem limitPageIsoOfIso_inv {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).inv = e.inv.limitPageMap pq := by
  rfl

end Functoriality

section Rebasing

private theorem isGLB_cyclesSubobject_iff_fromPage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (Z : Subobject ((E.page r₀).X pq)) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2) Z ↔
      IsGLB (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.1 (hs.trans r.2)) Z := by
  have hlb :
      lowerBounds (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2) =
        lowerBounds
          (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.1 (hs.trans r.2)) := by
    ext M
    constructor
    · rintro hM _ ⟨⟨r, hr⟩, rfl⟩
      exact hM ⟨⟨r, hs.trans hr⟩, rfl⟩
    · rintro hM _ ⟨⟨r, hr⟩, rfl⟩
      exact (hM ⟨⟨max r s, le_max_right r s⟩, rfl⟩).trans
        (E.cyclesSubobject_anti pq hr (le_max_left r s))
  simp only [IsGLB, IsGreatest, hlb]

private theorem isLUB_boundariesSubobject_iff_fromPage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (B : Subobject ((E.page r₀).X pq)) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2) B ↔
      IsLUB
        (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.boundariesSubobject pq r.1 (hs.trans r.2)) B := by
  have hub :
      upperBounds (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2) =
        upperBounds
          (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.boundariesSubobject pq r.1 (hs.trans r.2)) := by
    ext M
    constructor
    · rintro hM _ ⟨⟨r, hr⟩, rfl⟩
      exact hM ⟨⟨r, hs.trans hr⟩, rfl⟩
    · rintro hM _ ⟨⟨r, hr⟩, rfl⟩
      exact (E.boundariesSubobject_mono pq hr (le_max_left r s)).trans
        (hM ⟨⟨max r s, le_max_right r s⟩, rfl⟩)
  simp only [IsLUB, IsLeast, hub]

private theorem range_cyclesSubobject_fromPage_eq (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) :
    (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.1 (hs.trans r.2)) =
      (E.pagePresentation pq s hs).preimage ''
        (Set.range fun r : {r : ℤ // s ≤ r} ↦ (E.fromPage s hs).cyclesSubobject pq r.1 r.2) := by
  ext T
  simp only [Set.mem_range, Set.mem_image, Subtype.exists]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(E.fromPage s hs).cyclesSubobject pq r hr, ⟨r, hr, rfl⟩,
      (E.cyclesSubobject_eq_preimage_fromPage pq s hs r hr).symm⟩
  · rintro ⟨S, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, E.cyclesSubobject_eq_preimage_fromPage pq s hs r hr⟩

private theorem range_boundariesSubobject_fromPage_eq (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) :
    (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.boundariesSubobject pq r.1 (hs.trans r.2)) =
      (E.pagePresentation pq s hs).preimage ''
        (Set.range fun r : {r : ℤ // s ≤ r} ↦
          (E.fromPage s hs).boundariesSubobject pq r.1 r.2) := by
  ext T
  simp only [Set.mem_range, Set.mem_image, Subtype.exists]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(E.fromPage s hs).boundariesSubobject pq r hr, ⟨r, hr, rfl⟩,
      (E.boundariesSubobject_eq_preimage_fromPage pq s hs r hr).symm⟩
  · rintro ⟨S, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, E.boundariesSubobject_eq_preimage_fromPage pq s hs r hr⟩

/-- Rebasing invariance of `HasLimitPageAt`: `E.fromPage s hs` has a limit page at `pq` if and only
if `E` does. -/
theorem hasLimitPageAt_fromPage_iff (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).HasLimitPageAt pq ↔ E.HasLimitPageAt pq := by
  have hneZ :
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        (E.fromPage s hs).cyclesSubobject pq r.1 r.2).Nonempty :=
    ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  have hneB :
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        (E.fromPage s hs).boundariesSubobject pq r.1 r.2).Nonempty :=
    ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  have hZ :
      (∃ Z, IsGLB
          (Set.range fun r : {r : ℤ // s ≤ r} ↦ (E.fromPage s hs).cyclesSubobject pq r.1 r.2) Z) ↔
        ∃ Z, IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.1 r.2) Z := by
    rw [← (E.pagePresentation pq s hs).exists_isGLB_preimage_iff hneZ,
      ← E.range_cyclesSubobject_fromPage_eq pq s hs]
    exact exists_congr fun Z ↦ (E.isGLB_cyclesSubobject_iff_fromPage pq s hs Z).symm
  have hB :
      (∃ B, IsLUB
          (Set.range fun r : {r : ℤ // s ≤ r} ↦
            (E.fromPage s hs).boundariesSubobject pq r.1 r.2) B) ↔
        ∃ B, IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.1 r.2) B := by
    rw [← (E.pagePresentation pq s hs).exists_isLUB_preimage_iff hneB,
      ← E.range_boundariesSubobject_fromPage_eq pq s hs]
    exact exists_congr fun B ↦ (E.isLUB_boundariesSubobject_iff_fromPage pq s hs B).symm
  exact ⟨fun h ↦ ⟨hZ.mp h.exists_isGLB_cycles, hB.mp h.exists_isLUB_boundaries⟩,
    fun h ↦ ⟨hZ.mpr h.exists_isGLB_cycles, hB.mpr h.exists_isLUB_boundaries⟩⟩

/-- Under rebasing to page `s ≥ r₀`, `Z_∞(E, pq)` is the preimage under `E.pagePresentation pq s`
of `Z_∞(E.fromPage s, pq)`. -/
theorem infiniteCycles_eq_preimage_fromPage (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) [E.HasLimitPageAt pq] [(E.fromPage s hs).HasLimitPageAt pq] :
    E.infiniteCycles pq =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infiniteCycles pq) := by
  have hne :
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        (E.fromPage s hs).cyclesSubobject pq r.1 r.2).Nonempty :=
    ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  refine E.infiniteCycles_eq_of_isGLB pq ?_
  rw [E.isGLB_cyclesSubobject_iff_fromPage pq s hs, E.range_cyclesSubobject_fromPage_eq pq s hs]
  exact ((E.pagePresentation pq s hs).isGLB_preimage_iff hne).mpr
    ((E.fromPage s hs).isGLB_infiniteCycles pq)

/-- Under rebasing to page `s ≥ r₀`, `B_∞(E, pq)` is the preimage under `E.pagePresentation pq s`
of `B_∞(E.fromPage s, pq)`. -/
theorem infiniteBoundaries_eq_preimage_fromPage (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) [E.HasLimitPageAt pq] [(E.fromPage s hs).HasLimitPageAt pq] :
    E.infiniteBoundaries pq =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infiniteBoundaries pq) := by
  have hne :
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        (E.fromPage s hs).boundariesSubobject pq r.1 r.2).Nonempty :=
    ⟨_, ⟨⟨s, le_rfl⟩, rfl⟩⟩
  refine E.infiniteBoundaries_eq_of_isLUB pq ?_
  rw [E.isLUB_boundariesSubobject_iff_fromPage pq s hs,
    E.range_boundariesSubobject_fromPage_eq pq s hs]
  exact ((E.pagePresentation pq s hs).isLUB_preimage_iff hne).mpr
    ((E.fromPage s hs).isLUB_infiniteBoundaries pq)

/-- The canonical isomorphism `E.limitPage pq ≅ (E.fromPage s hs).limitPage pq` showing that the
limit page is invariant under rebasing to a later page `s ≥ r₀`. -/
noncomputable def limitPageIsoFromPage (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) [E.HasLimitPageAt pq] [(E.fromPage s hs).HasLimitPageAt pq] :
    E.limitPage pq ≅ (E.fromPage s hs).limitPage pq :=
  (E.limitPagePresentation pq).mapInducedIso
    ((E.pagePresentation pq s hs).comp ((E.fromPage s hs).limitPagePresentation pq))
    (Iso.refl _)
    (by
      rw [Iso.refl_hom, Subobject.exists_iso_map, Subobject.map_id]
      exact E.infiniteCycles_eq_preimage_fromPage pq s hs)
    (by
      rw [Iso.refl_hom, Subobject.exists_iso_map, Subobject.map_id]
      exact E.infiniteBoundaries_eq_preimage_fromPage pq s hs)

@[simp]
theorem limitPageIsoFromPage_self (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    E.limitPageIsoFromPage pq r₀ le_rfl = Iso.refl (E.limitPage pq) := by
  ext
  simp only [limitPageIsoFromPage, TauCeti.SubquotientPresentation.mapInducedIso_hom,
    Iso.refl_hom]
  have heq :
      (E.limitPagePresentation pq).mapInduced
          ((E.pagePresentation pq r₀ le_rfl).comp (E.limitPagePresentation pq)) (𝟙 _)
          (by
            rw [Subobject.exists_iso_map, Subobject.map_id]
            exact (E.infiniteCycles_eq_preimage_fromPage pq r₀ le_rfl).le)
          (by
            rw [Subobject.exists_iso_map, Subobject.map_id]
            exact (E.infiniteBoundaries_eq_preimage_fromPage pq r₀ le_rfl).le) =
        (E.limitPagePresentation pq).mapInduced (E.limitPagePresentation pq) (𝟙 _)
          (by rw [Subobject.exists_iso_map, Subobject.map_id])
          (by rw [Subobject.exists_iso_map, Subobject.map_id]) := by
    simp only [pagePresentation_base, TauCeti.SubquotientPresentation.id_comp]
  rw [heq, TauCeti.SubquotientPresentation.mapInduced_id]

private theorem mapInduced_comp_fromPage_limitPagePresentation {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s)
    [(E.fromPage s hs).HasLimitPageAt pq] [(E'.fromPage s hs).HasLimitPageAt pq] :
    ∃ (hZ : (Subobject.exists ((f.hom r₀).f pq)).obj
        ((E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infiniteCycles pq)) ≤
        (E'.pagePresentation pq s hs).preimage ((E'.fromPage s hs).infiniteCycles pq))
      (hB : (Subobject.exists ((f.hom r₀).f pq)).obj
        ((E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infiniteBoundaries pq)) ≤
        (E'.pagePresentation pq s hs).preimage ((E'.fromPage s hs).infiniteBoundaries pq)),
      ((E.pagePresentation pq s hs).comp ((E.fromPage s hs).limitPagePresentation pq)).mapInduced
          ((E'.pagePresentation pq s hs).comp ((E'.fromPage s hs).limitPagePresentation pq))
          ((f.hom r₀).f pq) hZ hB =
        (f.fromPage s hs).limitPageMap pq := by
  have hZp_step :
      (Subobject.exists ((E.pagePresentation pq s hs).mapInduced (E'.pagePresentation pq s hs)
        ((f.hom r₀).f pq) (f.exists_cyclesSubobject_le pq s hs)
        (f.exists_boundariesSubobject_le pq s hs))).obj ((E.fromPage s hs).infiniteCycles pq) ≤
        (E'.fromPage s hs).infiniteCycles pq := by
    rw [f.mapInduced_pagePresentation pq s hs]
    exact (f.fromPage s hs).exists_infiniteCycles_le pq
  have hBp_step :
      (Subobject.exists ((E.pagePresentation pq s hs).mapInduced (E'.pagePresentation pq s hs)
        ((f.hom r₀).f pq) (f.exists_cyclesSubobject_le pq s hs)
        (f.exists_boundariesSubobject_le pq s hs))).obj ((E.fromPage s hs).infiniteBoundaries pq) ≤
        (E'.fromPage s hs).infiniteBoundaries pq := by
    rw [f.mapInduced_pagePresentation pq s hs]
    exact (f.fromPage s hs).exists_infiniteBoundaries_le pq
  refine ⟨((E.pagePresentation pq s hs).exists_preimage_le_preimage_iff
      (E'.pagePresentation pq s hs) ((f.hom r₀).f pq)
      (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs)
      _ _).mpr hZp_step,
    ((E.pagePresentation pq s hs).exists_preimage_le_preimage_iff
      (E'.pagePresentation pq s hs) ((f.hom r₀).f pq)
      (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs)
      _ _).mpr hBp_step, ?_⟩
  rw [(E.pagePresentation pq s hs).mapInduced_comp_presentation
    (E'.pagePresentation pq s hs) ((E.fromPage s hs).limitPagePresentation pq)
    ((E'.fromPage s hs).limitPagePresentation pq) ((f.hom r₀).f pq)
    (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs)
    hZp_step hBp_step]
  simp only [Hom.limitPageMap, Hom.fromPage_hom, f.mapInduced_pagePresentation pq s hs]

/-- Naturality of the rebasing isomorphism `limitPageIsoFromPage` with respect to morphisms of
spectral sequences. -/
@[reassoc]
theorem Hom.limitPageMap_comp_limitPageIsoFromPage_hom {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq]
    [(E.fromPage s hs).HasLimitPageAt pq] [(E'.fromPage s hs).HasLimitPageAt pq] :
    f.limitPageMap pq ≫ (E'.limitPageIsoFromPage pq s hs).hom =
      (E.limitPageIsoFromPage pq s hs).hom ≫ (f.fromPage s hs).limitPageMap pq := by
  obtain ⟨hZp, hBp, hcomp_p⟩ := mapInduced_comp_fromPage_limitPagePresentation f pq s hs
  have h1 := (E.limitPagePresentation pq).mapInduced_comp (E'.limitPagePresentation pq)
    ((E'.pagePresentation pq s hs).comp ((E'.fromPage s hs).limitPagePresentation pq))
    ((f.hom r₀).f pq) (𝟙 _)
    (f.exists_infiniteCycles_le pq) (f.exists_infiniteBoundaries_le pq)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E'.infiniteCycles_eq_preimage_fromPage pq s hs).le)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E'.infiniteBoundaries_eq_preimage_fromPage pq s hs).le)
  have h2 := (E.limitPagePresentation pq).mapInduced_comp
    ((E.pagePresentation pq s hs).comp ((E.fromPage s hs).limitPagePresentation pq))
    ((E'.pagePresentation pq s hs).comp ((E'.fromPage s hs).limitPagePresentation pq))
    (𝟙 _) ((f.hom r₀).f pq)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E.infiniteCycles_eq_preimage_fromPage pq s hs).le)
    (by
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact (E.infiniteBoundaries_eq_preimage_fromPage pq s hs).le)
    hZp hBp
  rw [← hcomp_p]
  simp only [Hom.limitPageMap, limitPageIsoFromPage,
    TauCeti.SubquotientPresentation.mapInducedIso_hom, Iso.refl_hom, ← h1, ← h2,
    Category.comp_id, Category.id_comp]

end Rebasing

end CategoryTheory.SpectralSequence
