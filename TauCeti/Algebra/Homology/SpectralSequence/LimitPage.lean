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
import Mathlib.Order.Bounds.OrderIso

/-!
# The limit page of a spectral sequence

When the cycle tower `{Z_r(pq) | r ≥ r₀}` has a greatest lower bound `Z_∞(pq)` and the boundary
tower `{B_r(pq) | r ≥ r₀}` has a least upper bound `B_∞(pq)` in `Subobject ((E.page r₀).X pq)`
(`HasLimitPageAt`), we have `B_∞(pq) ≤ Z_∞(pq)` and define the **limit page**
`E_∞(pq) = cokernel (Subobject.ofLE B_∞(pq) Z_∞(pq))` (`limitPage`, `limitPagePresentation`).

* Existence at stabilising positions (`hasLimitPageAt_of_stabilisesAt`, `limitPageIsoPageX`) and
  globally under `[HasCountableProducts C] [HasCountableCoproducts C]`
  (`hasLimitPageAt_of_hasCountableProducts_of_hasCountableCoproducts`).
* Functoriality (`Hom.limitPageMap`, `limitPageIsoOfIso`), rebasing invariance
  (`hasLimitPageAt_fromPage_iff`, `limitPageIsoFromPage`), and vanishing propagation
  (`isZero_limitPage_of_isZero_page_X`).

## References

* Stacks Project, Tag 011O (Definition 12.20.2).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001.
-/

public section

open CategoryTheory Limits
open TauCeti (SubquotientPresentation)

namespace CategoryTheory.SpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Defs

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- `E` *has a limit page at `pq`* if the cycle tower `{Z_r(pq) | r ≥ r₀}` has a GLB and the
boundary tower `{B_r(pq) | r ≥ r₀}` has a LUB in `Subobject ((E.page r₀).X pq)`. -/
class HasLimitPageAt : Prop where
  exists_isGLB_cycles :
    ∃ Z, IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z
  exists_isLUB_boundaries :
    ∃ B, IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) B

variable [E.HasLimitPageAt pq]

/-- The infinite-cycle subobject `Z_∞(pq) = ⋀_{r ≥ r₀} Z_r(pq)`. -/
noncomputable def infiniteCycles : Subobject ((E.page r₀).X pq) :=
  (HasLimitPageAt.exists_isGLB_cycles (E := E) (pq := pq)).choose

/-- The infinite-boundary subobject `B_∞(pq) = ⋁_{r ≥ r₀} B_r(pq)`. -/
noncomputable def infiniteBoundaries : Subobject ((E.page r₀).X pq) :=
  (HasLimitPageAt.exists_isLUB_boundaries (E := E) (pq := pq)).choose

theorem isGLB_infiniteCycles :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (E.infiniteCycles pq) :=
  (HasLimitPageAt.exists_isGLB_cycles (E := E) (pq := pq)).choose_spec

theorem isLUB_infiniteBoundaries :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (E.infiniteBoundaries pq) :=
  (HasLimitPageAt.exists_isLUB_boundaries (E := E) (pq := pq)).choose_spec

theorem infiniteCycles_eq_of_isGLB {Z : Subobject ((E.page r₀).X pq)}
    (hZ : IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z) :
    E.infiniteCycles pq = Z := (E.isGLB_infiniteCycles pq).unique hZ

theorem infiniteBoundaries_eq_of_isLUB {B : Subobject ((E.page r₀).X pq)}
    (hB : IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      B) :
    E.infiniteBoundaries pq = B := (E.isLUB_infiniteBoundaries pq).unique hB

theorem infiniteCycles_le_cyclesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.infiniteCycles pq ≤ E.cyclesSubobject pq r hr :=
  (E.isGLB_infiniteCycles pq).1 ⟨⟨r, hr⟩, rfl⟩

theorem le_infiniteCycles_iff {S : Subobject ((E.page r₀).X pq)} :
    S ≤ E.infiniteCycles pq ↔ ∀ (r : ℤ) (hr : r₀ ≤ r), S ≤ E.cyclesSubobject pq r hr :=
  ⟨fun h r hr ↦ h.trans (E.infiniteCycles_le_cyclesSubobject pq r hr),
   fun h ↦ (E.isGLB_infiniteCycles pq).2 fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ hEq ▸ h r hr⟩

theorem boundariesSubobject_le_infiniteBoundaries (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr ≤ E.infiniteBoundaries pq :=
  (E.isLUB_infiniteBoundaries pq).1 ⟨⟨r, hr⟩, rfl⟩

theorem infiniteBoundaries_le_iff {S : Subobject ((E.page r₀).X pq)} :
    E.infiniteBoundaries pq ≤ S ↔ ∀ (r : ℤ) (hr : r₀ ≤ r), E.boundariesSubobject pq r hr ≤ S :=
  ⟨fun h r hr ↦ (E.boundariesSubobject_le_infiniteBoundaries pq r hr).trans h,
   fun h ↦ (E.isLUB_infiniteBoundaries pq).2 fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ hEq ▸ h r hr⟩

/-- Infinite boundaries lie inside infinite cycles: `B_∞(pq) ≤ Z_∞(pq)`. -/
theorem infiniteBoundaries_le_infiniteCycles : E.infiniteBoundaries pq ≤ E.infiniteCycles pq :=
  (E.infiniteBoundaries_le_iff pq).mpr fun r₁ h₁ ↦ (E.le_infiniteCycles_iff pq).mpr fun r₂ h₂ ↦
    E.boundariesSubobject_le_cyclesSubobject_of_any pq r₁ r₂ h₁ h₂

/-- The limit page object `E_∞(pq) = Z_∞(pq) / B_∞(pq)` at position `pq`. -/
noncomputable def limitPage : C :=
  cokernel (Subobject.ofLE (E.infiniteBoundaries pq) (E.infiniteCycles pq)
    (E.infiniteBoundaries_le_infiniteCycles pq))

/-- The canonical subquotient presentation of `E.limitPage pq` inside `(E.page r₀).X pq`. -/
noncomputable def limitPagePresentation :
    SubquotientPresentation ((E.page r₀).X pq) (E.limitPage pq) :=
  SubquotientPresentation.quotient (E.infiniteBoundaries pq) (E.infiniteCycles pq)
    (E.infiniteBoundaries_le_infiniteCycles pq)

@[simp]
theorem limitPagePresentation_B : (E.limitPagePresentation pq).B = E.infiniteBoundaries pq := by
  rw [limitPagePresentation, SubquotientPresentation.quotient_B]

@[simp]
theorem limitPagePresentation_Z : (E.limitPagePresentation pq).Z = E.infiniteCycles pq := by
  rw [limitPagePresentation, SubquotientPresentation.quotient_Z]

/-- The limit page `E_∞(pq)` vanishes if and only if `B_∞(pq) = Z_∞(pq)`. -/
theorem isZero_limitPage_iff_infiniteBoundaries_eq_infiniteCycles :
    IsZero (E.limitPage pq) ↔ E.infiniteBoundaries pq = E.infiniteCycles pq := by
  simpa using (E.limitPagePresentation pq).isZero_iff

/-- If `(E.page r).X pq` vanishes on some page `r ≥ r₀`, then `E_∞(pq)` vanishes. -/
theorem isZero_limitPage_of_isZero_page_X (r : ℤ) (hr : r₀ ≤ r) (h : IsZero ((E.page r hr).X pq)) :
    IsZero (E.limitPage pq) :=
  (E.isZero_limitPage_iff_infiniteBoundaries_eq_infiniteCycles pq).mpr <|
    le_antisymm (E.infiniteBoundaries_le_infiniteCycles pq) <|
      (E.infiniteCycles_le_cyclesSubobject pq r hr).trans <|
        ((E.isZero_page_X_iff_boundariesSubobject_eq_cyclesSubobject pq r hr).mp h).symm.trans_le
          (E.boundariesSubobject_le_infiniteBoundaries pq r hr)

end Defs

section Existence

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- If differentials leaving `pq` vanish from page `s` onward, `Z_s(pq)` is the cycle GLB. -/
theorem isGLB_cyclesSubobject_of_forall_dFrom_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (E.cyclesSubobject pq s hs) :=
  ⟨fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ hEq ▸ (le_total s r).elim
      (fun hsr ↦ (E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs h r hsr).ge)
      (fun hrs ↦ E.cyclesSubobject_anti pq hr hrs),
   fun _ hM ↦ hM ⟨⟨s, hs⟩, rfl⟩⟩

/-- If differentials entering `pq` vanish from page `s` onward, `B_s(pq)` is the boundary LUB. -/
theorem isLUB_boundariesSubobject_of_forall_dTo_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (E.boundariesSubobject pq s hs) :=
  ⟨fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ hEq ▸ (le_total s r).elim
      (fun hsr ↦ (E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs h r hsr).le)
      (fun hrs ↦ E.boundariesSubobject_mono pq hr hrs),
   fun _ hM ↦ hM ⟨⟨s, hs⟩, rfl⟩⟩

/-- Regularity at `pq` implies that the greatest lower bound `Z_∞(pq)` exists. -/
theorem exists_isGLB_cyclesSubobject_of_isRegularAt (h : E.IsRegularAt pq) :
    ∃ Z, IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z := by
  obtain ⟨s, hs, h⟩ := (E.isRegularAt_iff pq).mp h
  exact ⟨E.cyclesSubobject pq s hs, E.isGLB_cyclesSubobject_of_forall_dFrom_eq_zero pq hs h⟩

/-- Coregularity at `pq` implies that the least upper bound `B_∞(pq)` exists. -/
theorem exists_isLUB_boundariesSubobject_of_isCoregularAt (h : E.IsCoregularAt pq) :
    ∃ B, IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦
      E.boundariesSubobject pq r.val r.property) B := by
  obtain ⟨s, hs, h⟩ := (E.isCoregularAt_iff pq).mp h
  exact ⟨E.boundariesSubobject pq s hs, E.isLUB_boundariesSubobject_of_forall_dTo_eq_zero pq hs h⟩

/-- If `E` is both regular and coregular at `pq`, then `E` has a limit page at `pq`. -/
theorem hasLimitPageAt_of_isRegularAt_of_isCoregularAt (hreg : E.IsRegularAt pq)
    (hcoreg : E.IsCoregularAt pq) : E.HasLimitPageAt pq where
  exists_isGLB_cycles := E.exists_isGLB_cyclesSubobject_of_isRegularAt pq hreg
  exists_isLUB_boundaries := E.exists_isLUB_boundariesSubobject_of_isCoregularAt pq hcoreg

/-- If `E` stabilises at `pq` from page `s`, then `E` has a limit page at `pq`. -/
theorem hasLimitPageAt_of_stabilisesAt {s : ℤ} (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) :
    E.HasLimitPageAt pq :=
  E.hasLimitPageAt_of_isRegularAt_of_isCoregularAt pq h.isRegularAt h.isCoregularAt

theorem infiniteCycles_eq_of_stabilisesAt {s : ℤ} (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs)
    [E.HasLimitPageAt pq] : E.infiniteCycles pq = E.cyclesSubobject pq s hs :=
  E.infiniteCycles_eq_of_isGLB pq
    (E.isGLB_cyclesSubobject_of_forall_dFrom_eq_zero pq hs fun _ ↦ h.dFrom_eq_zero)

theorem infiniteBoundaries_eq_of_stabilisesAt {s : ℤ} (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs)
    [E.HasLimitPageAt pq] : E.infiniteBoundaries pq = E.boundariesSubobject pq s hs :=
  E.infiniteBoundaries_eq_of_isLUB pq
    (E.isLUB_boundariesSubobject_of_forall_dTo_eq_zero pq hs fun _ ↦ h.dTo_eq_zero)

/-- With countable products, `kernelSubobject (Pi.lift (cokernel.π (Z_r).arrow))` is `Z_∞`. -/
theorem isGLB_cyclesSubobject_kernelSubobject_piLift [HasCountableProducts C] :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (kernelSubobject (Pi.lift fun r : {r : ℤ // r₀ ≤ r} ↦
        cokernel.π (E.cyclesSubobject pq r.val r.property).arrow)) :=
  Subobject.isGLB_kernelSubobject_piLift
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)

/-- With countable coproducts, `imageSubobject (Sigma.desc (B_r).arrow)` is the boundary LUB. -/
theorem isLUB_boundariesSubobject_imageSubobject_sigmaDesc [HasCountableCoproducts C] :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (imageSubobject (Sigma.desc fun r : {r : ℤ // r₀ ≤ r} ↦
        (E.boundariesSubobject pq r.val r.property).arrow)) :=
  Subobject.isLUB_imageSubobject_sigmaDesc
    (fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)

/-- Explicit presentation of `Z_∞(pq)` in an abelian category with countable products. -/
theorem infiniteCycles_eq_kernelSubobject_piLift [HasCountableProducts C] [E.HasLimitPageAt pq] :
    E.infiniteCycles pq = kernelSubobject (Pi.lift fun r : {r : ℤ // r₀ ≤ r} ↦
      cokernel.π (E.cyclesSubobject pq r.val r.property).arrow) :=
  E.infiniteCycles_eq_of_isGLB pq (E.isGLB_cyclesSubobject_kernelSubobject_piLift pq)

/-- Explicit presentation of `B_∞(pq)` in an abelian category with countable coproducts. -/
theorem infiniteBoundaries_eq_imageSubobject_sigmaDesc [HasCountableCoproducts C]
    [E.HasLimitPageAt pq] :
    E.infiniteBoundaries pq = imageSubobject (Sigma.desc fun r : {r : ℤ // r₀ ≤ r} ↦
      (E.boundariesSubobject pq r.val r.property).arrow) :=
  E.infiniteBoundaries_eq_of_isLUB pq (E.isLUB_boundariesSubobject_imageSubobject_sigmaDesc pq)

/-- With countable products and coproducts, every spectral sequence has a limit page everywhere. -/
instance hasLimitPageAt_of_hasCountableProducts_of_hasCountableCoproducts
    [HasCountableProducts C] [HasCountableCoproducts C] : E.HasLimitPageAt pq where
  exists_isGLB_cycles := ⟨_, E.isGLB_cyclesSubobject_kernelSubobject_piLift pq⟩
  exists_isLUB_boundaries := ⟨_, E.isLUB_boundariesSubobject_imageSubobject_sigmaDesc pq⟩

/-- If `E` is regular at `pq` and `C` has countable coproducts, `E` has a limit page at `pq`. -/
theorem hasLimitPageAt_of_isRegularAt_of_hasCountableCoproducts [HasCountableCoproducts C]
    (hreg : E.IsRegularAt pq) : E.HasLimitPageAt pq where
  exists_isGLB_cycles := E.exists_isGLB_cyclesSubobject_of_isRegularAt pq hreg
  exists_isLUB_boundaries := ⟨_, E.isLUB_boundariesSubobject_imageSubobject_sigmaDesc pq⟩

/-- If `E` is coregular at `pq` and `C` has countable products, `E` has a limit page at `pq`. -/
theorem hasLimitPageAt_of_hasCountableProducts_of_isCoregularAt [HasCountableProducts C]
    (hcoreg : E.IsCoregularAt pq) : E.HasLimitPageAt pq where
  exists_isGLB_cycles := ⟨_, E.isGLB_cyclesSubobject_kernelSubobject_piLift pq⟩
  exists_isLUB_boundaries := E.exists_isLUB_boundariesSubobject_of_isCoregularAt pq hcoreg

variable [E.HasLimitPageAt pq]

/-- At a stabilising position `pq` from page `s`, the canonical iso `E.limitPage pq ≅ E_s(pq)`. -/
noncomputable def limitPageIsoPageX (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) :
    E.limitPage pq ≅ (E.page s hs).X pq :=
  (E.limitPagePresentation pq).isoOfEq (E.pagePresentation pq s hs)
    (by simpa using E.infiniteBoundaries_eq_of_stabilisesAt pq hs h)
    (by simpa using E.infiniteCycles_eq_of_stabilisesAt pq hs h)

/-- Compatibility of `limitPageIsoPageX` with `pageXIsoOfStabilises`. -/
theorem limitPageIsoPageX_trans_pageXIsoOfStabilises {s r : ℤ} (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (hsr : s ≤ r) :
    E.limitPageIsoPageX pq s hs h ≪≫ E.pageXIsoOfStabilises pq s hs h r hsr =
      E.limitPageIsoPageX pq r (hs.trans hsr) (h.of_le hsr) := by
  refine (E.limitPagePresentation pq).mapIso_injective ?_
  rw [← SubquotientPresentation.mapIso_trans, limitPageIsoPageX,
    SubquotientPresentation.mapIso_isoOfEq,
    ← E.pagePresentation_eq_mapIso_pageXIsoOfStabilises pq s hs h r hsr,
    limitPageIsoPageX, SubquotientPresentation.mapIso_isoOfEq]

end Existence

section Functoriality

section

variable {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
  [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq]

/-- A morphism `f : E ⟶ E'` maps `Z_∞(E, pq)` into `Z_∞(E', pq)`. -/
theorem Hom.exists_infiniteCycles_le :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.infiniteCycles pq) ≤ E'.infiniteCycles pq :=
  (E'.le_infiniteCycles_iff pq).mpr fun r hr ↦
    ((Subobject.exists _).monotone (E.infiniteCycles_le_cyclesSubobject pq r hr)).trans
      (f.exists_cyclesSubobject_le pq r hr)

/-- Adjoint form: `Z_∞(E, pq)` lies below the pullback of `Z_∞(E', pq)`. -/
theorem Hom.infiniteCycles_le_pullback :
    E.infiniteCycles pq ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.infiniteCycles pq) :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mp (f.exists_infiniteCycles_le pq)

/-- A morphism `f : E ⟶ E'` maps `B_∞(E, pq)` into `B_∞(E', pq)`. -/
theorem Hom.exists_infiniteBoundaries_le :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.infiniteBoundaries pq) ≤ E'.infiniteBoundaries pq :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mpr <|
    (E.infiniteBoundaries_le_iff pq).mpr fun r hr ↦
      (f.boundariesSubobject_le_pullback pq r hr).trans
        ((Subobject.pullback _).monotone (E'.boundariesSubobject_le_infiniteBoundaries pq r hr))

/-- Adjoint form: `B_∞(E, pq)` lies below the pullback of `B_∞(E', pq)`. -/
theorem Hom.infiniteBoundaries_le_pullback :
    E.infiniteBoundaries pq ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.infiniteBoundaries pq) :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mp (f.exists_infiniteBoundaries_le pq)

/-- The morphism `E_∞(f, pq) : E.limitPage pq ⟶ E'.limitPage pq` induced by `f : E ⟶ E'`. -/
noncomputable def Hom.limitPageMap : E.limitPage pq ⟶ E'.limitPage pq :=
  (E.limitPagePresentation pq).mapInduced (E'.limitPagePresentation pq) ((f.hom r₀).f pq)
    (by simpa only [limitPagePresentation_Z] using f.exists_infiniteCycles_le pq)
    (by simpa only [limitPagePresentation_B] using f.exists_infiniteBoundaries_le pq)

/-- Agreement of `limitPageMap` with `(f.hom s).f pq` at a stabilising position. -/
@[reassoc]
theorem Hom.limitPageMap_comp_limitPageIsoPageX_hom (s : ℤ) (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (h' : E'.StabilisesAt pq s hs) :
    f.limitPageMap pq ≫ (E'.limitPageIsoPageX pq s hs h').hom =
      (E.limitPageIsoPageX pq s hs h).hom ≫ (f.hom s hs).f pq := by
  refine (E.limitPagePresentation pq).hom_ext ?_
  rw [← f.mapInduced_pagePresentation pq s hs]
  simp only [Hom.limitPageMap, limitPageIsoPageX,
    SubquotientPresentation.π_mapInduced_assoc, SubquotientPresentation.π_isoOfEq_hom,
    SubquotientPresentation.π_isoOfEq_hom_assoc, SubquotientPresentation.π_mapInduced]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ (E'.pagePresentation pq s hs).π) ?_
  rw [← cancel_mono (E'.pagePresentation pq s hs).Z.arrow]
  simp

end

@[simp]
theorem limitPageMap_id (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    (𝟙 E : E ⟶ E).limitPageMap pq = 𝟙 (E.limitPage pq) := by
  dsimp only [Hom.limitPageMap]
  simpa only [id_hom, HomologicalComplex.id_f] using (E.limitPagePresentation pq).mapInduced_id

@[reassoc, simp]
theorem limitPageMap_comp {E E' E'' : SpectralSequence C c r₀} (f : E ⟶ E') (g : E' ⟶ E'')
    (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] [E''.HasLimitPageAt pq] :
    (f ≫ g).limitPageMap pq = f.limitPageMap pq ≫ g.limitPageMap pq :=
  (E.limitPagePresentation pq).mapInduced_comp (E'.limitPagePresentation pq)
    (E''.limitPagePresentation pq) ((f.hom r₀).f pq) ((g.hom r₀).f pq)
    (f.exists_infiniteCycles_le pq) (f.exists_infiniteBoundaries_le pq)
    (g.exists_infiniteCycles_le pq) (g.exists_infiniteBoundaries_le pq)

section

variable {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
include e

/-- Existence of a limit page at `pq` is transported along isomorphisms of spectral sequences. -/
theorem hasLimitPageAt_of_iso [E.HasLimitPageAt pq] : E'.HasLimitPageAt pq := by
  let i : (E.page r₀).X pq ≅ (E'.page r₀).X pq :=
    (pageFunctor C c r₀ r₀ le_rfl ⋙ HomologicalComplex.eval C (c r₀) pq).mapIso e
  have hi : i.hom = (e.hom.hom r₀).f pq := by
    simp only [i, Functor.mapIso_hom, pageFunctor_obj, Functor.comp_map, pageFunctor_map,
      HomologicalComplex.eval_map]
  let φ := Subobject.mapIsoToOrderIso i
  have hφ : ∀ S, φ S = (Subobject.exists ((e.hom.hom r₀).f pq)).obj S := fun S ↦ by
    rw [Subobject.mapIsoToOrderIso_apply, ← Subobject.exists_iso_map, hi]
  have hZ : φ '' (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) =
      Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E'.cyclesSubobject pq r.val r.property := by
    rw [← Set.range_comp]; congr 1; funext r
    exact (hφ _).trans (exists_cyclesSubobject_eq_of_iso e pq r.val r.property)
  have hB : φ ''
      (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) =
      Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E'.boundariesSubobject pq r.val r.property := by
    rw [← Set.range_comp]; congr 1; funext r
    exact (hφ _).trans (exists_boundariesSubobject_eq_of_iso e pq r.val r.property)
  exact ⟨⟨φ (E.infiniteCycles pq), hZ ▸ (OrderIso.isGLB_image' φ).mpr (E.isGLB_infiniteCycles pq)⟩,
    ⟨φ (E.infiniteBoundaries pq),
      hB ▸ (OrderIso.isLUB_image' φ).mpr (E.isLUB_infiniteBoundaries pq)⟩⟩

/-- Isomorphic spectral sequences have limit pages at the same positions. -/
theorem hasLimitPageAt_iff_of_iso : E.HasLimitPageAt pq ↔ E'.HasLimitPageAt pq :=
  ⟨fun _ ↦ hasLimitPageAt_of_iso e pq, fun _ ↦ hasLimitPageAt_of_iso e.symm pq⟩

/-- An isomorphism `e : E ≅ E'` induces an isomorphism `E.limitPage pq ≅ E'.limitPage pq`. -/
noncomputable def limitPageIsoOfIso [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ≅ E'.limitPage pq where
  hom := e.hom.limitPageMap pq
  inv := e.inv.limitPageMap pq
  hom_inv_id := by rw [← limitPageMap_comp, Iso.hom_inv_id, limitPageMap_id]
  inv_hom_id := by rw [← limitPageMap_comp, Iso.inv_hom_id, limitPageMap_id]

@[simp]
theorem limitPageIsoOfIso_hom [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).hom = e.hom.limitPageMap pq := by rfl

@[simp]
theorem limitPageIsoOfIso_inv [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).inv = e.inv.limitPageMap pq := by rfl

end

end Functoriality

section Rebasing

section

variable (E : SpectralSequence C c r₀) (pq : κ)

private theorem isGLB_cyclesSubobject_iff_fromPage (s : ℤ) (hs : r₀ ≤ s)
    (Z : Subobject ((E.page r₀).X pq)) :
    IsGLB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property) Z ↔
      IsGLB (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.cyclesSubobject pq r.val (hs.trans r.property)) Z := by
  have hsub : (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.cyclesSubobject pq r.val (hs.trans r.property)) ⊆
      Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property :=
    fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ ⟨⟨r, hs.trans hr⟩, hEq⟩
  have hco : IsCoinitialFor
      (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.cyclesSubobject pq r.val r.property)
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.cyclesSubobject pq r.val (hs.trans r.property)) :=
    fun _ ⟨⟨r, hr⟩, hEq⟩ ↦
      ⟨E.cyclesSubobject pq (max r s) (hr.trans (le_max_left r s)),
        ⟨⟨max r s, le_max_right r s⟩, rfl⟩,
        hEq ▸ E.cyclesSubobject_anti pq hr (le_max_left r s)⟩
  exact isGLB_congr (le_antisymm (lowerBounds_mono_set hsub)
    (lowerBounds_mono_of_isCoinitialFor hco))

private theorem isLUB_boundariesSubobject_iff_fromPage (s : ℤ) (hs : r₀ ≤ s)
    (B : Subobject ((E.page r₀).X pq)) :
    IsLUB (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property) B ↔
      IsLUB (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property)) B := by
  have hsub : (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property)) ⊆
      Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property :=
    fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ ⟨⟨r, hs.trans hr⟩, hEq⟩
  have hcof : IsCofinalFor
      (Set.range fun r : {r : ℤ // r₀ ≤ r} ↦ E.boundariesSubobject pq r.val r.property)
      (Set.range fun r : {r : ℤ // s ≤ r} ↦
        E.boundariesSubobject pq r.val (hs.trans r.property)) :=
    fun _ ⟨⟨r, hr⟩, hEq⟩ ↦
      ⟨E.boundariesSubobject pq (max r s) (hr.trans (le_max_left r s)),
        ⟨⟨max r s, le_max_right r s⟩, rfl⟩,
        hEq ▸ E.boundariesSubobject_mono pq hr (le_max_left r s)⟩
  exact isLUB_congr (le_antisymm (upperBounds_mono_set hsub)
    (upperBounds_mono_of_isCofinalFor hcof))

private theorem range_cyclesSubobject_fromPage_eq (s : ℤ) (hs : r₀ ≤ s) :
    (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.cyclesSubobject pq r.val (hs.trans r.property)) =
      (E.pagePresentation pq s hs).preimage ''
        (Set.range fun r : {r : ℤ // s ≤ r} ↦
          (E.fromPage s hs).cyclesSubobject pq r.val r.property) := by
  rw [← Set.range_comp]; congr 1; funext r
  exact E.cyclesSubobject_eq_preimage_fromPage pq s hs r.val r.property

private theorem range_boundariesSubobject_fromPage_eq (s : ℤ) (hs : r₀ ≤ s) :
    (Set.range fun r : {r : ℤ // s ≤ r} ↦ E.boundariesSubobject pq r.val (hs.trans r.property)) =
      (E.pagePresentation pq s hs).preimage ''
        (Set.range fun r : {r : ℤ // s ≤ r} ↦
          (E.fromPage s hs).boundariesSubobject pq r.val r.property) := by
  rw [← Set.range_comp]; congr 1; funext r
  exact E.boundariesSubobject_eq_preimage_fromPage pq s hs r.val r.property

/-- Rebasing invariance of `HasLimitPageAt`: `E.fromPage s hs` has a limit page at `pq` iff `E`
does. -/
theorem hasLimitPageAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).HasLimitPageAt pq ↔ E.HasLimitPageAt pq := by
  have : Nonempty {r : ℤ // s ≤ r} := ⟨⟨s, le_rfl⟩⟩
  have hZ := (E.pagePresentation pq s hs).exists_isGLB_preimage_iff
    (Set.range_nonempty fun r : {r : ℤ // s ≤ r} ↦
      (E.fromPage s hs).cyclesSubobject pq r.val r.property)
  rw [← E.range_cyclesSubobject_fromPage_eq pq s hs] at hZ
  have hZ' := hZ.symm.trans
    (exists_congr fun Z ↦ (E.isGLB_cyclesSubobject_iff_fromPage pq s hs Z).symm)
  have hB := (E.pagePresentation pq s hs).exists_isLUB_preimage_iff
    (Set.range_nonempty fun r : {r : ℤ // s ≤ r} ↦
      (E.fromPage s hs).boundariesSubobject pq r.val r.property)
  rw [← E.range_boundariesSubobject_fromPage_eq pq s hs] at hB
  have hB' := hB.symm.trans
    (exists_congr fun B ↦ (E.isLUB_boundariesSubobject_iff_fromPage pq s hs B).symm)
  exact ⟨fun ⟨z, b⟩ ↦ ⟨hZ'.mp z, hB'.mp b⟩, fun ⟨z, b⟩ ↦ ⟨hZ'.mpr z, hB'.mpr b⟩⟩

/-- Under rebasing to page `s ≥ r₀`, `Z_∞(E, pq)` is the preimage of `Z_∞(E.fromPage s, pq)`. -/
theorem infiniteCycles_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) [E.HasLimitPageAt pq]
    [(E.fromPage s hs).HasLimitPageAt pq] :
    E.infiniteCycles pq =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infiniteCycles pq) := by
  have : Nonempty {r : ℤ // s ≤ r} := ⟨⟨s, le_rfl⟩⟩
  refine E.infiniteCycles_eq_of_isGLB pq ?_
  rw [E.isGLB_cyclesSubobject_iff_fromPage pq s hs, E.range_cyclesSubobject_fromPage_eq pq s hs]
  exact ((E.pagePresentation pq s hs).isGLB_preimage_iff (Set.range_nonempty _)).mpr
    ((E.fromPage s hs).isGLB_infiniteCycles pq)

/-- Under rebasing to page `s ≥ r₀`, `B_∞(E, pq)` is the preimage of `B_∞(E.fromPage s, pq)`. -/
theorem infiniteBoundaries_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) [E.HasLimitPageAt pq]
    [(E.fromPage s hs).HasLimitPageAt pq] :
    E.infiniteBoundaries pq =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).infiniteBoundaries pq) := by
  have : Nonempty {r : ℤ // s ≤ r} := ⟨⟨s, le_rfl⟩⟩
  refine E.infiniteBoundaries_eq_of_isLUB pq ?_
  rw [E.isLUB_boundariesSubobject_iff_fromPage pq s hs,
    E.range_boundariesSubobject_fromPage_eq pq s hs]
  exact ((E.pagePresentation pq s hs).isLUB_preimage_iff (Set.range_nonempty _)).mpr
    ((E.fromPage s hs).isLUB_infiniteBoundaries pq)

/-- The canonical rebasing isomorphism `E.limitPage pq ≅ (E.fromPage s hs).limitPage pq`. -/
noncomputable def limitPageIsoFromPage (s : ℤ) (hs : r₀ ≤ s) [E.HasLimitPageAt pq]
    [(E.fromPage s hs).HasLimitPageAt pq] : E.limitPage pq ≅ (E.fromPage s hs).limitPage pq :=
  (E.limitPagePresentation pq).isoOfEq
    ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq))
    (by simpa using E.infiniteBoundaries_eq_preimage_fromPage pq s hs)
    (by simpa using E.infiniteCycles_eq_preimage_fromPage pq s hs)

@[simp]
theorem limitPageIsoFromPage_self [E.HasLimitPageAt pq] :
    E.limitPageIsoFromPage pq r₀ le_rfl = Iso.refl (E.limitPage pq) := by
  refine (E.limitPagePresentation pq).mapIso_injective ?_
  rw [limitPageIsoFromPage, SubquotientPresentation.mapIso_isoOfEq,
    SubquotientPresentation.mapIso_refl, pagePresentation_base,
    SubquotientPresentation.refl_trans]

end

/-- Naturality of the rebasing isomorphism `limitPageIsoFromPage`. -/
@[reassoc]
theorem Hom.limitPageMap_comp_limitPageIsoFromPage_hom {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq]
    [(E.fromPage s hs).HasLimitPageAt pq] [(E'.fromPage s hs).HasLimitPageAt pq] :
    f.limitPageMap pq ≫ (E'.limitPageIsoFromPage pq s hs).hom =
      (E.limitPageIsoFromPage pq s hs).hom ≫ (f.fromPage s hs).limitPageMap pq := by
  have hm := f.mapInduced_pagePresentation pq s hs
  have hZs : (Subobject.exists ((E.pagePresentation pq s hs).mapInduced
        (E'.pagePresentation pq s hs) ((f.hom r₀).f pq)
        (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs))).obj
        ((E.fromPage s hs).limitPagePresentation pq).Z ≤
      ((E'.fromPage s hs).limitPagePresentation pq).Z := by
    rw [limitPagePresentation_Z, limitPagePresentation_Z, hm]
    simpa only [Hom.fromPage_hom] using (f.fromPage s hs).exists_infiniteCycles_le pq
  have hBs : (Subobject.exists ((E.pagePresentation pq s hs).mapInduced
        (E'.pagePresentation pq s hs) ((f.hom r₀).f pq)
        (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs))).obj
        ((E.fromPage s hs).limitPagePresentation pq).B ≤
      ((E'.fromPage s hs).limitPagePresentation pq).B := by
    rw [limitPagePresentation_B, limitPagePresentation_B, hm]
    simpa only [Hom.fromPage_hom] using (f.fromPage s hs).exists_infiniteBoundaries_le pq
  have hZtr : (Subobject.exists ((f.hom r₀).f pq)).obj
        ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).Z ≤
      ((E'.pagePresentation pq s hs).trans
        ((E'.fromPage s hs).limitPagePresentation pq)).Z :=
    ((E.pagePresentation pq s hs).exists_preimage_le_preimage_iff (E'.pagePresentation pq s hs)
      ((f.hom r₀).f pq) (f.exists_cyclesSubobject_le pq s hs)
      (f.exists_boundariesSubobject_le pq s hs) _ _).mpr hZs
  have hBtr : (Subobject.exists ((f.hom r₀).f pq)).obj
        ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).B ≤
      ((E'.pagePresentation pq s hs).trans
        ((E'.fromPage s hs).limitPagePresentation pq)).B :=
    ((E.pagePresentation pq s hs).exists_preimage_le_preimage_iff (E'.pagePresentation pq s hs)
      ((f.hom r₀).f pq) (f.exists_cyclesSubobject_le pq s hs)
      (f.exists_boundariesSubobject_le pq s hs) _ _).mpr hBs
  have hcomp : ((E.pagePresentation pq s hs).trans
        ((E.fromPage s hs).limitPagePresentation pq)).mapInduced
      ((E'.pagePresentation pq s hs).trans ((E'.fromPage s hs).limitPagePresentation pq))
      ((f.hom r₀).f pq) hZtr hBtr = (f.fromPage s hs).limitPageMap pq := by
    refine (SubquotientPresentation.mapInduced_trans (E.pagePresentation pq s hs)
      (E'.pagePresentation pq s hs) _ _ ((f.hom r₀).f pq) _ _ hZs hBs).trans ?_
    exact SubquotientPresentation.mapInduced_congr rfl rfl
      (hm.trans (by simp [Hom.fromPage_hom])) _ _ _ _
  have hleE : (E.limitPagePresentation pq).Z ≤
      ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).Z := by
    simpa using (E.infiniteCycles_eq_preimage_fromPage pq s hs).le
  have hleE' : (E'.limitPagePresentation pq).Z ≤
      ((E'.pagePresentation pq s hs).trans ((E'.fromPage s hs).limitPagePresentation pq)).Z := by
    simpa using (E'.infiniteCycles_eq_preimage_fromPage pq s hs).le
  refine (E.limitPagePresentation pq).hom_ext ?_
  calc (E.limitPagePresentation pq).π ≫ f.limitPageMap pq ≫
        (E'.limitPageIsoFromPage pq s hs).hom
    _ = (E.limitPagePresentation pq).liftZ (E'.limitPagePresentation pq) ((f.hom r₀).f pq)
          (by simpa only [limitPagePresentation_Z] using f.exists_infiniteCycles_le pq) ≫
          Subobject.ofLE (E'.limitPagePresentation pq).Z
            ((E'.pagePresentation pq s hs).trans
              ((E'.fromPage s hs).limitPagePresentation pq)).Z hleE' ≫
          ((E'.pagePresentation pq s hs).trans
            ((E'.fromPage s hs).limitPagePresentation pq)).π := by
        rw [Hom.limitPageMap, SubquotientPresentation.π_mapInduced_assoc,
          limitPageIsoFromPage, SubquotientPresentation.π_isoOfEq_hom]
    _ = Subobject.ofLE (E.limitPagePresentation pq).Z
            ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).Z
            hleE ≫
          ((E.pagePresentation pq s hs).trans ((E.fromPage s hs).limitPagePresentation pq)).liftZ
            ((E'.pagePresentation pq s hs).trans ((E'.fromPage s hs).limitPagePresentation pq))
            ((f.hom r₀).f pq) hZtr ≫
          ((E'.pagePresentation pq s hs).trans
            ((E'.fromPage s hs).limitPagePresentation pq)).π := by
        rw [← Category.assoc, ← Category.assoc]
        refine congrArg (· ≫ ((E'.pagePresentation pq s hs).trans
          ((E'.fromPage s hs).limitPagePresentation pq)).π) ?_
        rw [← cancel_mono ((E'.pagePresentation pq s hs).trans
          ((E'.fromPage s hs).limitPagePresentation pq)).Z.arrow]
        simp only [Category.assoc, Subobject.ofLE_arrow, SubquotientPresentation.liftZ_arrow,
          Subobject.ofLE_arrow_assoc]
    _ = (E.limitPagePresentation pq).π ≫ (E.limitPageIsoFromPage pq s hs).hom ≫
          (f.fromPage s hs).limitPageMap pq := by
        rw [← hcomp, limitPageIsoFromPage, SubquotientPresentation.π_isoOfEq_hom_assoc,
          SubquotientPresentation.π_mapInduced]

end Rebasing

end CategoryTheory.SpectralSequence
