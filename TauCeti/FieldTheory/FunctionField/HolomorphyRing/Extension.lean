/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence

/-!
# Holomorphy rings in an extension: `𝒪'_P` is the integral closure of `𝒪_P`

Let `F' / k'` be an extension of the algebraic function field `F / k`, integral both on the
constants and on the functions. Every place `P'` of `F' / k'` restricts to a place
`P'.restrict k F` of `F / k` (`TauCeti.Place.restrict`), and at a single place `P` the integral
closure `𝒪'_P` of `𝒪_P` in `F'` is already known to be the intersection of the valuation rings
of the fibre over `P` (`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`). This file
extends that computation from one place to a set of them: for a set `S` of places of `F / k`, the
intersection of the valuation rings `𝒪_{P'}` over the places `P'` lying over `S` is the integral
closure of the holomorphy ring `𝒪_S = ⋂_{P ∈ S} 𝒪_P` in `F'`. So integrality over an arbitrary
holomorphy ring is regularity above its defining set of places.

It also reads the fibre back off the integral closure: the places of `F' / k'` at which every
function of `𝒪'_P` is regular are exactly the places over `P`, and likewise over a set.

## Main results

* `TauCeti.coe_holomorphyRing_setOf_restrict_mem` and
  `TauCeti.mem_holomorphyRing_setOf_restrict_mem_iff_isIntegral`: the holomorphy ring of the
  places lying over `S` is the integral closure of `𝒪_S` in `F'`, in set and membership form.
* `TauCeti.coe_integralClosure_integers_subset_integers_iff`: the places of `F' / k'` at which
  every function of `𝒪'_P` is regular are exactly the places over `P`, so `𝒪'_P` remembers the
  fibre; `TauCeti.coe_integralClosure_holomorphyRing_subset_integers_iff` is the version over a
  set of places.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.2 and III.3.  The description of the integral closure of `𝒪_P` in `F'` as the
  intersection of the valuation rings of the places over `P` is the opening result of
  Section III.3, on which its local integral bases rest.
-/

public section

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral k k'] [Algebra.IsIntegral F F']

section Engine

variable (k F)

/-- **Separating a non-integral function by a place.** If `z : F'` is not integral over a
`k`-algebra `R` acting on `F'` through `F`, there is a place `P'` of `F' / k'` at which `z` is
irregular while every function of `R` is regular at the place of `F / k` below `P'`. This
separation statement extends the one-place integral-closure criterion to arbitrary holomorphy
rings. -/
private theorem exists_place_of_not_isIntegral (hF' : IsFunctionField k' F')
    {R : Type*} [CommRing R] [Algebra k R] [Algebra R F] [Algebra R F']
    [IsScalarTower k R F'] [IsScalarTower R F F'] {z : F'} (hz : ¬ IsIntegral R z) :
    ∃ P' : Place k' F',
      (∀ r : R, algebraMap R F r ∈ (P'.restrict k F).integers) ∧ z ∉ P'.integers := by
  obtain ⟨V, hRV, hzV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure R F').toSubring) hz
  have hk' : ∀ c : k', algebraMap k' F' c ∈ V := fun c ↦
    hRV (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  have hV : V ≠ ⊤ := fun h ↦ hzV (h ▸ ValuationSubring.mem_top _)
  have hint : (Place.ofValuationSubring hF' hk' hV).integers = V :=
    Place.integers_ofValuationSubring hF' hk' hV
  refine ⟨Place.ofValuationSubring hF' hk' hV, fun r ↦ ?_, fun h ↦ hzV (hint ▸ h)⟩
  rw [Place.mem_integers_restrict_iff, hint, ← IsScalarTower.algebraMap_apply R F F']
  exact hRV (Subalgebra.algebraMap_mem (integralClosure R F') r)

end Engine

/-! ### The integral closure of a holomorphy ring -/

/-- **The integral closure of a holomorphy ring**, over a set of places: a function of `F'` is
regular at every place of `F' / k'` lying over `S` exactly when it is integral over the holomorphy
ring `𝒪_S` (Stichtenoth, Section III.3). -/
theorem mem_holomorphyRing_setOf_restrict_mem_iff_isIntegral (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') {S : Set (Place k F)} {z : F'} :
    z ∈ holomorphyRing {P' : Place k' F' | P'.restrict k F ∈ S} ↔
      IsIntegral ↥(holomorphyRing S) z := by
  rw [mem_holomorphyRing_iff]
  refine ⟨fun hz ↦ by_contra fun hint ↦ ?_, fun hint P' hP' ↦ ?_⟩
  · obtain ⟨P', hP', hzP'⟩ := exists_place_of_not_isIntegral k F hF' hint
    refine hzP' (hz P' ((coe_holomorphyRing_subset_integers_iff hF).mp fun x hx ↦ ?_))
    simpa using hP' ⟨x, hx⟩
  · refine P'.mem_integers_of_isIntegral (fun r ↦ ?_) hint
    rw [IsScalarTower.algebraMap_apply ↥(holomorphyRing S) F F']
    exact (Place.mem_integers_restrict_iff k F P' _).mp (mem_holomorphyRing_iff.mp r.2 _ hP')

/-- **The integral closure of a holomorphy ring**, over a set of places: the holomorphy ring of
the places of `F' / k'` lying over `S` is the integral closure of `𝒪_S` in `F'` (Stichtenoth,
Section III.3). -/
theorem coe_holomorphyRing_setOf_restrict_mem (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (S : Set (Place k F)) :
    (holomorphyRing {P' : Place k' F' | P'.restrict k F ∈ S} : Set F') =
      integralClosure ↥(holomorphyRing S) F' :=
  Set.ext fun _ ↦ mem_holomorphyRing_setOf_restrict_mem_iff_isIntegral hF hF'

/-! ### Recovering the fibre from the integral closure -/

/-- The places of `F' / k'` at which every function of the integral closure of `𝒪_S` is regular
are exactly the places lying over `S` (Stichtenoth, Corollary 3.2.8 read through the theorem
above). -/
@[simp]
theorem coe_integralClosure_holomorphyRing_subset_integers_iff (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (S : Set (Place k F)) (P' : Place k' F') :
    (integralClosure ↥(holomorphyRing S) F' : Set F') ⊆ P'.integers ↔ P'.restrict k F ∈ S := by
  rw [← coe_holomorphyRing_setOf_restrict_mem hF hF' S,
    coe_holomorphyRing_subset_integers_iff hF', Set.mem_ofPred_eq]

/-- The places of `F' / k'` at which every function of `𝒪'_P` is regular are exactly the places
lying over `P`, so the fibre over `P` is recovered from `𝒪'_P` (Stichtenoth, Corollary 3.2.8 read
through `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`).  Unlike the version over
a set of places, this needs no hypothesis on `F / k`. -/
@[simp]
theorem coe_integralClosure_integers_subset_integers_iff (hF' : IsFunctionField k' F')
    (P : Place k F) (P' : Place k' F') :
    (integralClosure ↥P.integers F' : Set F') ⊆ P'.integers ↔ P'.restrict k F = P := by
  have h : (integralClosure ↥P.integers F' : Set F') =
      holomorphyRing {Q' : Place k' F' | Q'.restrict k F = P} := by
    ext z
    simp only [SetLike.mem_coe, mem_holomorphyRing_iff]
    exact Place.isIntegral_iff_forall_restrict_eq_mem_integers hF' P
  rw [h, coe_holomorphyRing_subset_integers_iff hF', Set.mem_ofPred_eq]

end TauCeti
