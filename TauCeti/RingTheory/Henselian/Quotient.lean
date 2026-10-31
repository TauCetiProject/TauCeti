/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Basic

/-!
# Quotients of henselian pairs

If `(R, I)` is henselian and `φ : R →+* S` is surjective, then `(S, I.map φ)` is
henselian. In particular, one can quotient by any ideal, not only an ideal contained
in `I`. This permanence result is used when changing the ambient ring of a henselian pair.

## References

* Stacks Project, Lemma 15.11.8 (09XK), the quotient case of integral permanence.
-/

public section

open Polynomial

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring map carries a henselian pair to a henselian pair. There is no
condition on its kernel relative to the henselian ideal. -/
theorem henselianRing_of_surjective (φ : R →+* S) (hφ : Function.Surjective φ)
    (I : Ideal R) [HenselianRing R I] : HenselianRing S (I.map φ) := by
  have hJac : I.map φ ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_jacobson_of_surjective hφ]
    exact HenselianRing.jac.trans (Ideal.jacobson_mono bot_le)
  refine ⟨hJac, fun f _ a₀ ha₀ hd => ?_⟩
  /- A polynomial over S lifts to a polynomial g over R, but its approximate root and
  invertible derivative need not lift with the same properties. Multiplying g by a
  lift of the inverse derivative and correcting its constant and linear terms in
  ker φ gives a polynomial with value in I and derivative exactly one. Apply
  Polynomial.exists_isRoot_sub_mem, the nonmonic form of Hensel's lemma, to this
  corrected polynomial. -/
  have := isLocalHom_of_le_jacobson_bot (I.map φ) hJac
  obtain ⟨u, hu⟩ := isUnit_of_map_unit (Ideal.Quotient.mk (I.map φ)) _ hd
  obtain ⟨b, hb⟩ := hφ (↑u⁻¹ : S)
  obtain ⟨a, rfl⟩ := hφ a₀
  obtain ⟨g, rfl⟩ := Polynomial.map_surjective φ hφ f
  obtain ⟨i, hi, hfi⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp ha₀
  have hder : φ b * φ (g.derivative.eval a) = 1 := by
    rw [hb, ← eval_map_apply, ← derivative_map, ← hu]
    exact Units.inv_mul u
  -- Both corrections vanish after applying φ; over R they make the derivative one
  -- and the value b * i, so no lifting of units along φ is needed.
  let h : R[X] := C b * g + C (1 - b * g.derivative.eval a) * (X - C a) -
    C (b * (g.eval a - i))
  have heval : h.eval a = b * i := by
    simp [h]
    ring
  have hderiv : h.derivative.eval a = 1 := by
    simp [h]
  obtain ⟨x, hx, hxa⟩ := Polynomial.exists_isRoot_sub_mem (J := I) h
    (heval ▸ I.mul_mem_left b hi) (by simp [hderiv])
  have hroot : φ b * (g.map φ).eval (φ x) = 0 := by
    have heq := congrArg φ hx.eq_zero
    have hconst : φ (g.eval a) = φ i := by
      simpa only [eval_map_apply] using hfi.symm
    simpa [h, map_sub, map_add, map_mul, hder, hconst, eval_map_apply] using heq
  refine ⟨φ x, ?_, ?_⟩
  · rw [IsRoot.def]
    exact (IsUnit.of_mul_eq_one _ hder).mul_right_eq_zero.mp hroot
  · simpa only [map_sub] using Ideal.mem_map_of_mem φ hxa

end RingHom

namespace Ideal

/-- Quotienting a henselian pair `(R, I)` by any ideal `J` gives a henselian pair
`(R/J, I(R/J))`, even when `J` is not contained in `I`. -/
instance henselianRing_quotient {R : Type*} [CommRing R] (I J : Ideal R)
    [HenselianRing R I] : HenselianRing (R ⧸ J) (I.map (Ideal.Quotient.mk J)) :=
  (Ideal.Quotient.mk J).henselianRing_of_surjective Ideal.Quotient.mk_surjective I

end Ideal
