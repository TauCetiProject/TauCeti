/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Equalizer
public import TauCeti.RingTheory.Ideal.FixedPoints

/-!
# Fixed-point Hopf ideals of bialgebra endomorphisms

Given a family `f : ι → (H →ₐc[R] H)` of bialgebra endomorphisms of a commutative Hopf algebra `H`
over a commutative ring `R`, the supremum `⨆ i, TauCeti.HopfIdeal.equalizer (f i) (BialgHom.id R H)`
is a Hopf ideal `TauCeti.HopfIdeal.fixedPoints f`. Its underlying ideal is the ring-theoretic
fixed-point ideal `TauCeti.fixedPointsIdeal f`, so the quotient Hopf algebra
`H ⧸ (TauCeti.HopfIdeal.fixedPoints f).toIdeal` corepresents the closed subgroup scheme fixed by
every `f i`.

## Main definitions

* `TauCeti.HopfIdeal.fixedPoints`: the fixed-point Hopf ideal of a family of bialgebra
  endomorphisms of a commutative Hopf algebra.

## Main results

* `TauCeti.HopfIdeal.fixedPoints_toIdeal`: the underlying ideal of `HopfIdeal.fixedPoints f` is
  `TauCeti.fixedPointsIdeal f`.
* `TauCeti.HopfIdeal.fixedPoints_le_iff` and `TauCeti.HopfIdeal.fixedPoints_le_ker_iff`:
  universal properties among Hopf ideals and ring homomorphisms out of `H`.
* `TauCeti.HopfIdeal.fixedPoints_eq_bot_iff`: the fixed-point Hopf ideal vanishes if and only if
  every endomorphism in the family is the identity.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.1,
  p. 293.
-/

public section

namespace TauCeti

namespace HopfIdeal

universe u v

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {ι : Sort*}

/-- The **fixed-point Hopf ideal** of a family of bialgebra endomorphisms of a commutative Hopf
algebra, defined as the supremum of the equalizer Hopf ideals with the identity.

The quotient `H ⧸ (fixedPoints f).toIdeal` is the coordinate Hopf algebra of the closed subgroup
scheme of `Spec H` fixed by every `f i`. -/
def fixedPoints (f : ι → H →ₐc[R] H) : HopfIdeal R H :=
  ⨆ i, equalizer (f i) (BialgHom.id R H)

/-- The ideal underlying `HopfIdeal.fixedPoints f` is the fixed-point ideal `fixedPointsIdeal f`. -/
@[simp]
theorem fixedPoints_toIdeal (f : ι → H →ₐc[R] H) :
    (fixedPoints f).toIdeal = fixedPointsIdeal f := by
  rw [fixedPoints, iSup_toIdeal, fixedPointsIdeal_eq_iSup]
  refine iSup_congr fun i ↦ ?_
  rw [equalizer_toIdeal, equalizerIdeal_eq_span]
  rfl

/-- Membership in `HopfIdeal.fixedPoints f` agrees with membership in `fixedPointsIdeal f`. -/
@[simp]
theorem mem_fixedPoints {f : ι → H →ₐc[R] H} {x : H} :
    x ∈ fixedPoints f ↔ x ∈ fixedPointsIdeal f := by
  rw [← mem_toIdeal, fixedPoints_toIdeal]

/-- Every difference `f i a - a` lies in `HopfIdeal.fixedPoints f`. -/
theorem sub_mem_fixedPoints (f : ι → H →ₐc[R] H) (i : ι) (a : H) :
    f i a - a ∈ fixedPoints f :=
  mem_fixedPoints.mpr (sub_mem_fixedPointsIdeal f i a)

/-- Universal property of `HopfIdeal.fixedPoints f` among Hopf ideals of `H`. -/
theorem fixedPoints_le_iff {f : ι → H →ₐc[R] H} {J : HopfIdeal R H} :
    fixedPoints f ≤ J ↔ ∀ i a, f i a - a ∈ J := by
  rw [← toIdeal_le_toIdeal, fixedPoints_toIdeal, fixedPointsIdeal_le_iff]
  rfl

/-- A ring homomorphism out of `H` kills `HopfIdeal.fixedPoints f` if and only if it is invariant
under every `f i`. -/
theorem fixedPoints_le_ker_iff {A : Type*} [Ring A] {f : ι → H →ₐc[R] H} (φ : H →+* A) :
    (fixedPoints f).toIdeal ≤ RingHom.ker φ ↔ ∀ i a, φ (f i a) = φ a := by
  rw [fixedPoints_toIdeal]
  exact fixedPointsIdeal_le_ker_iff φ

/-- The fixed-point Hopf ideal vanishes if and only if every `f i` is the identity bialgebra
endomorphism. -/
theorem fixedPoints_eq_bot_iff {f : ι → H →ₐc[R] H} :
    fixedPoints f = ⊥ ↔ ∀ i, f i = BialgHom.id R H := by
  rw [← le_bot_iff, ← toIdeal_le_toIdeal, fixedPoints_toIdeal, bot_toIdeal, le_bot_iff,
    fixedPointsIdeal_eq_bot_iff]
  exact forall_congr' fun i ↦ by rw [BialgHom.ext_iff]; rfl

/-- The fixed-point Hopf ideal of a constant family of identity bialgebra endomorphisms is zero. -/
@[simp]
theorem fixedPoints_id (ι : Sort*) :
    fixedPoints (fun _ : ι ↦ BialgHom.id R H) = ⊥ :=
  fixedPoints_eq_bot_iff.mpr fun _ ↦ rfl

/-- Reindexing along a surjection does not change the fixed-point Hopf ideal. -/
theorem fixedPoints_comp_surjective {κ : Sort*} (f : ι → H →ₐc[R] H) {e : κ → ι}
    (he : Function.Surjective e) : fixedPoints (f ∘ e) = fixedPoints f := by
  ext x
  rw [mem_fixedPoints, mem_fixedPoints, fixedPointsIdeal_comp_surjective f he]

end HopfIdeal

end TauCeti
