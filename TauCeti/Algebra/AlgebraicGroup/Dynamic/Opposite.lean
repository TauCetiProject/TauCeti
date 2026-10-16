/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
import TauCeti.Algebra.Polynomial.Laurent.Polynomial

/-!
# Opposite dynamic parabolics

The cocharacter opposite to `λ` is `t ↦ λ(t⁻¹)`. The intersection of the dynamic parabolics
of these two cocharacters is their common Levi subgroup. This holds over every commutative
value semiring: a Laurent-valued conjugation family that extends over both ends has only
its constant coefficient, so it centralizes the cocharacter.

This identifies the Levi as an intersection of closed subgroups, without reductivity or
smoothness assumptions. The polynomial-extension criterion is from
`TauCeti.Algebra.Polynomial.Laurent.Polynomial`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open WithConv

namespace TauCeti.Cocharacter

variable {R H A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [CommSemiring A] [Algebra R A]

/-- Reversing the cocharacter inverts the variable of the conjugation family. -/
theorem conjugate_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    conjugate A l.oppositeCocharacter g =
      AlgHom.mapValue (LaurentPolynomial.invert.toAlgHom.restrictScalars R)
        (conjugate A l g) := by
  rw [mapValue_conjugate]
  have hu : Units.map (LaurentPolynomial.invert.toAlgHom.restrictScalars R).toMonoidHom
      (LaurentPolynomial.genericUnit A) = (LaurentPolynomial.genericUnit A)⁻¹ := by
    ext
    simp [LaurentPolynomial.genericUnit_val, LaurentPolynomial.genericUnit_inv]
  have hc : (LaurentPolynomial.invert.toAlgHom.restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      IsScalarTower.toAlgHom R A (LaurentPolynomial A) := by
    ext a : 1
    exact LaurentPolynomial.invert_C a
  rw [hu, hc, map_inv, conjugate_apply, genericPoint_oppositeCocharacter,
    genericPoint_eq_pointsHom, inv_inv]
  rw [constPoint_apply, AlgHom.mapValue_apply]

/-- Opposite cocharacters have the same Levi subgroup. -/
@[simp]
theorem levi_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    levi A l.oppositeCocharacter = levi A l := by
  ext g
  simp only [mem_levi_iff, conjugate_apply, genericPoint_oppositeCocharacter,
    mul_inv_eq_iff_eq_mul]
  exact Commute.inv_left_iff

private theorem coeff_conjugate_eq_zero_of_mem_parabolic
    (l : H →ₐc[R] LaurentPolynomial R) {g : WithConv (H →ₐ[R] A)}
    (hg : g ∈ parabolic A l) (h : H) {n : ℤ} (hn : n < 0) :
    ((conjugate A l g).ofConv h).coeff n = 0 := by
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  apply exists_toLaurent_eq_iff.mp ⟨F.ofConv h, ?_⟩ n hn
  simpa only [ofPolyPoint_apply, ofConv_toConv, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Polynomial.coe_toLaurentAlg] using
    congrArg (fun x : WithConv (H →ₐ[R] LaurentPolynomial A) ↦ x.ofConv h) hF

/-- The two opposite dynamic parabolics meet exactly in their common Levi subgroup. -/
@[simp]
theorem parabolic_inf_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    parabolic A l ⊓ parabolic A l.oppositeCocharacter = levi A l := by
  apply le_antisymm
  · intro g hg
    have hc (h : H) : (conjugate A l g).ofConv h =
        LaurentPolynomial.C (((conjugate A l g).ofConv h).coeff 0) := by
      ext n
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · rw [coeff_conjugate_eq_zero_of_mem_parabolic l hg.1 h hn]
        simp only [LaurentPolynomial.C_apply, ne_of_lt hn, ite_false]
      · simp
      · have hz := coeff_conjugate_eq_zero_of_mem_parabolic
          l.oppositeCocharacter hg.2 h (neg_neg_of_pos hn)
        rw [conjugate_oppositeCocharacter] at hz
        simpa [AlgHom.mapValue_apply, ne_of_gt hn] using hz
    let e : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) (1 : Aˣ)).restrictScalars R
    have heval : AlgHom.mapValue e (conjugate A l g) = g := by
      rw [mapValue_conjugate]
      have hu : Units.map e.toMonoidHom (LaurentPolynomial.genericUnit A) = 1 := by
        ext
        simp [e]
      have he : e.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) = AlgHom.id R A := by
        ext a
        simp [e]
      rw [hu, he]
      simp
    rw [mem_levi_iff]
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    have hevalh := congrArg (fun x : WithConv (H →ₐ[R] A) ↦ x.ofConv h) heval
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at hevalh
    rw [hc] at hevalh
    have hzero : ((conjugate A l g).ofConv h).coeff 0 = g.ofConv h := by
      simpa only [e, AlgHom.restrictScalars_apply, laurentEval_C,
        Algebra.algebraMap_self, RingHom.id_apply] using hevalh
    rw [constPoint_apply]
    exact (hc h).trans (congrArg LaurentPolynomial.C hzero)
  · exact le_inf levi_le_parabolic (by rw [← levi_oppositeCocharacter l]; exact levi_le_parabolic)

end TauCeti.Cocharacter
