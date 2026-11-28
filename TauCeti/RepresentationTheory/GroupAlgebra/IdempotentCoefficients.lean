/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RepresentationTheory.Character

import TauCeti.Algebra.MonoidAlgebra.Trace
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RepresentationTheory.CharacterTable.Values

/-!
# Coefficients of central idempotents in finite group algebras

If `e` is a central idempotent of `k[G]`, the character of its summand of the regular
representation has value `|G| * e.coeff (g⁻¹)` at `g`. In particular, multiplying the coefficients
by `|G|` makes them algebraic integers. Over `ℂ` the original coefficients have norm at most
one under every field automorphism. These bounds control the use of a scaled central idempotent
on lattices and at archimedean places without choosing its irreducible constituents.

The coefficient bounds are the input to the good-projection estimates
`New.Data.goodProjTranslate_mem_integralForms` and `New.Data.normSqAt_goodProjTranslate_le`
in `lsernau/grh-lean` (`72fead1`, `grh/src/New/UpperBound/Size/ArchimedeanSize.lean`).
-/

public section

namespace MonoidAlgebra

open Module

variable {k G : Type*} [Field k] [Group G] [Finite G] {e : MonoidAlgebra k G}

/-- The scaled coefficients at inverse elements of a central idempotent give the character
of its summand of the left regular representation. -/
theorem exists_character_eq_card_mul_coeff_inv (he : IsIdempotentElem e)
    (hc : e ∈ Subring.center (MonoidAlgebra k G)) :
    ∃ ρ : Representation k G (LinearMap.range (Algebra.lmul k (MonoidAlgebra k G) e)),
      ∀ g, ρ.character g = (Nat.card G : k) * e.coeff g⁻¹ := by
  let l := Algebra.lmul k (MonoidAlgebra k G)
  let reg : Representation k G (MonoidAlgebra k G) :=
    l.toMonoidHom.comp (MonoidAlgebra.of k G)
  have hcomm (g : G) : Commute (l e) (reg g) := by
    have hg : Commute (MonoidAlgebra.of k G g) e := Subring.mem_center_iff.mp hc _
    exact hg.symm.map l
  have hstable (g : G) : (l e).range ≤ (l e).range.comap (reg g) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨reg g x, ?_⟩
    exact LinearMap.congr_fun (hcomm g).eq x
  refine ⟨reg.subrepresentation (l e).range hstable, fun g ↦ ?_⟩
  have hidem : l e * l e = (1 : k) • l e := by
    simpa using (he.map l).eq
  have ht := TauCeti.LinearMap.trace_mul_eq_mul_trace_restrict_range hidem (hcomm g) (hstable g)
  rw [one_mul] at ht
  unfold Representation.character
  rw [Representation.subrepresentation_apply, ← ht]
  have hmul : l e * reg g = LinearMap.mulLeft k (e * single g 1) :=
    (l.map_mul e (MonoidAlgebra.of k G g)).symm
  rw [hmul, trace_mulLeft]
  simp

omit [Finite G] in
/-- Multiplying any coefficient of a central idempotent by the order of the group gives an
algebraic integer, over any coefficient field. For an infinite group, `Nat.card` is zero. -/
theorem isIntegral_card_mul_coeff_of_isIdempotentElem (he : IsIdempotentElem e)
    (hc : e ∈ Subring.center (MonoidAlgebra k G)) (g : G) :
    IsIntegral ℤ ((Nat.card G : k) * e.coeff g) := by
  rcases finite_or_infinite G with hG | hG
  · obtain ⟨ρ, hρ⟩ := exists_character_eq_card_mul_coeff_inv he hc
    have h := ρ.isIntegral_character g⁻¹
    rwa [hρ g⁻¹, inv_inv] at h
  · simpa using (isIntegral_zero : IsIntegral ℤ (0 : k))

/-- Every coefficient of a complex central idempotent has norm at most one, including after
applying any field automorphism of `ℂ`. -/
theorem norm_map_coeff_le_one_of_isIdempotentElem {e : MonoidAlgebra ℂ G}
    (he : IsIdempotentElem e) (hc : e ∈ Subring.center (MonoidAlgebra ℂ G))
    (σ : ℂ ≃+* ℂ) (g : G) : ‖σ (e.coeff g)‖ ≤ 1 := by
  let e' := mapRingEquiv G σ e
  have hc' : e' ∈ Subring.center (MonoidAlgebra ℂ G) :=
    MulEquivClass.apply_mem_center (mapRingEquiv G σ) hc
  obtain ⟨ρ, hρ⟩ := exists_character_eq_card_mul_coeff_inv (he.map (mapRingEquiv G σ)) hc'
  have hb := ρ.norm_char_le_finrank (orderOf_pos g⁻¹).ne' (pow_orderOf_eq_one g⁻¹)
  have hdim := (Algebra.lmul ℂ (MonoidAlgebra ℂ G) e').finrank_range_le
  have hcard : finrank ℂ (MonoidAlgebra ℂ G) = Nat.card G :=
    finrank_eq_nat_card_basis (MonoidAlgebra.basis G ℂ)
  rw [hcard] at hdim
  have hle := hb.trans (Nat.cast_le.mpr hdim)
  rw [hρ, inv_inv, norm_mul, Complex.norm_natCast, coeff_mapRingEquiv] at hle
  have hcardPos : (0 : ℝ) < Nat.card G := Nat.cast_pos.mpr Nat.card_pos
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hle) hcardPos

end MonoidAlgebra
