/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.ScalarMap
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The multiplier ring of a period lattice and its analytic endomorphisms

The **multiplier ring** of a lattice `Λ ⊆ ℂ` is the subring `{α ∈ ℂ | α Λ ⊆ Λ}`, the left order
`L.lattice.leftOrder` of the lattice (`Submodule.leftOrder`). Through the scalar maps of
`PeriodPair.scalarPointHom`, it acts on the points `E_Λ(ℂ)` of the Weierstrass curve of `Λ`: this
is the ring homomorphism `PeriodPair.endRingHom`, which is injective. So the multiplier ring acts
by analytic endomorphisms of the complex uniformization.

Writing `α ω₁ = a ω₁ + b ω₂` and `α ω₂ = e ω₁ + f ω₂` with integers `a, b, e, f`, the
determinant `a f - b e` of the integer matrix `[[a, e], [b, f]]` of `α` is its norm `|α|²`
(`PeriodPair.intCast_mul_sub_mul_eq_normSq`, with the rest of the lattice arithmetic of
multipliers in `TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair`: every multiplier is an
algebraic integer of degree at most two, and the real multipliers are exactly the integers). So
the degree `[Λ : α Λ]` of the endomorphism of `α ≠ 0`, that is the cardinality of its kernel, is
`|α|²`.

## Main definitions

* `PeriodPair.endRingHom`: the action of the multiplier ring `L.lattice.leftOrder` on `E_Λ(ℂ)` by
  the scalar maps.

## Main results

* `PeriodPair.endRingHom_injective`: the action is faithful.
* `PeriodPair.natCard_ker_endRingHom`: the degree of the endomorphism of `α ≠ 0` is `|α|²`
  (stated with `Nat.card`, so that it also holds at `α = 0`).

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.5.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.2.
-/

public noncomputable section

namespace PeriodPair

variable {L L' : PeriodPair}

/-! ### The action of the multiplier ring -/

variable (L)

/-- The action of the multiplier ring `L.lattice.leftOrder = {α | α Λ ⊆ Λ}` on the points of the
Weierstrass curve by the scalar maps: these give analytic endomorphisms of `E_Λ(ℂ)`. -/
def endRingHom : L.lattice.leftOrder →+* AddMonoid.End L.weierstrassCurve.toAffine.Point where
  toFun α := scalarPointHom (α : ℂ) (Submodule.mem_leftOrder_iff.mp α.property)
  map_one' := scalarPointHom_one
  map_mul' α β := (scalarPointHom_comp (Submodule.mem_leftOrder_iff.mp β.property)
    (Submodule.mem_leftOrder_iff.mp α.property)).symm
  map_zero' := scalarPointHom_zero
  map_add' α β := scalarPointHom_add (Submodule.mem_leftOrder_iff.mp α.property)
    (Submodule.mem_leftOrder_iff.mp β.property)

/-- The endomorphism of a multiplier `α` is the scalar map of `α`. -/
lemma endRingHom_apply (α : L.lattice.leftOrder) :
    L.endRingHom α = scalarPointHom (α : ℂ) (Submodule.mem_leftOrder_iff.mp α.property) :=
  (rfl)

/-- The endomorphism of a multiplier `α` sends `P(z)` to `P(α z)`. -/
@[simp]
lemma endRingHom_weierstrassPoint (α : L.lattice.leftOrder) (z : ℂ) :
    L.endRingHom α (L.weierstrassPoint z) = L.weierstrassPoint (α * z) :=
  scalarPointHom_weierstrassPoint _ (Submodule.mem_leftOrder_iff.mp α.property) z

/-- The action of the multiplier ring is faithful. -/
theorem endRingHom_injective : Function.Injective L.endRingHom := by
  refine (injective_iff_map_eq_zero _).mpr fun α hα ↦ ?_
  rw [endRingHom_apply] at hα
  exact Subtype.ext ((scalarPointHom_eq_zero_iff _).mp hα)

/-- **The degree of an endomorphism is the norm.** The `Nat.card` of the kernel of the
endomorphism of a multiplier `α` is `|α|²`: for `α ≠ 0` the kernel is finite with `|α|²` elements,
and for `α = 0` both sides vanish, since the kernel is the whole infinite group of points and
`Nat.card` of an infinite type is `0`. -/
theorem natCard_ker_endRingHom (α : L.lattice.leftOrder) :
    (Nat.card (L.endRingHom α).ker : ℝ) = Complex.normSq α := by
  obtain rfl | hα := eq_or_ne α 0
  · have hker : (L.endRingHom 0).ker = ⊤ := by rw [map_zero]; exact AddMonoidHom.ker_zero
    rw [hker, Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_eq_zero_of_infinite]
    simp
  have hα' : (α : ℂ) ≠ 0 := fun h ↦ hα (Subtype.ext h)
  have hαΛ := Submodule.mem_leftOrder_iff.mp α.property
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (hαΛ _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (hαΛ _ L.ω₂_mem_lattice)
  have h := natCard_ker_scalarPointHom (Units.mk0 _ hα') hαΛ
  rw [relIndex_lattice_smul_eq_natAbs (Units.mk0 _ hα') hab hef] at h
  simp only [Units.val_mk0] at h
  rw [endRingHom_apply, h, Nat.cast_natAbs, Int.cast_abs, intCast_mul_sub_mul_eq_normSq hab hef,
    abs_of_nonneg (Complex.normSq_nonneg _)]

end PeriodPair
