/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import Mathlib.RingTheory.FiniteStability

/-!
# Geometric connectedness of dynamic unipotent subgroups

The dynamic unipotent subgroup of a cocharacter in an affine group of finite type over a
field is geometrically connected. No smoothness, reducedness or reductivity is required.

The extending conjugation family of a unipotent point stays inside the dynamic unipotent
subgroup, including at the origin. It therefore gives a polynomial path from the identity
to that point in the representing closed subgroup. After any algebraically closed field
extension, these paths make every idempotent invariant under all point translations;
finite-type point separation then proves connectedness.

The proof uses the coefficient-ideal representation in `Dynamic.Unipotent.Representability`,
the quotient-point lifting API, the base-change adjunction for convolution points, and
`HopfAlgebra.rightTranslationAlgHom_eq_self_of_path`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 2 and 13.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.Cocharacter

universe u v w

noncomputable section

section Ring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing A] [Algebra R A]
variable (l : H →ₐc[R] LaurentPolynomial R)

/-- The polynomial extension of the conjugation family of a dynamic unipotent point
remains inside the represented dynamic unipotent subgroup. -/
theorem extend_mem_unipotent {g : WithConv (H →ₐ[R] A)} (hg : g ∈ unipotent A l) :
    extend A l ⟨g, unipotent_le_parabolic hg⟩ ∈ unipotent (Polynomial A) l := by
  rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro h hh
  apply Polynomial.toLaurent_injective
  have hc := conjugate_mem_unipotent hg
  rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hc
  have hz := hc h hh
  rw [← ofPolyPoint_extend ⟨g, unipotent_le_parabolic hg⟩, ofPolyPoint_apply] at hz
  simpa only [ofConv_toConv, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_toLaurentAlg, map_zero] using hz

/-- Every point of the represented dynamic unipotent subgroup has a polynomial path
inside that subgroup, specializing to the point at one and the identity at zero. -/
theorem exists_polynomial_path_unipotent
    (g : WithConv (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
      l.unipotentDefiningHopfIdeal →ₐ[R] A)) :
    ∃ F : WithConv (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        l.unipotentDefiningHopfIdeal →ₐ[R] Polynomial A),
      AlgHom.mapValue ((Polynomial.aeval (1 : A)).restrictScalars R) F = g ∧
      AlgHom.mapValue ((Polynomial.aeval (0 : A)).restrictScalars R) F = 1 := by
  let B := _root_.CommHopfAlgCat.of R H
  let I := l.unipotentDefiningHopfIdeal
  let p := CommHopfAlgCat.quotientPointsHom B I (CommAlgCat.of R A) g
  have hp : p ∈ unipotent A l := by
    rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal]
    exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup B I (CommAlgCat.of R A) g
  let E := extend A l ⟨p, unipotent_le_parabolic hp⟩
  have hE : ∀ h ∈ I, E.ofConv h = 0 := by
    have hm := extend_mem_unipotent l hp
    rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hm
    exact hm
  refine ⟨CommHopfAlgCat.liftQuotientPoint B I (CommAlgCat.of R (Polynomial A)) E hE, ?_, ?_⟩
  · apply CommHopfAlgCat.quotientPointsHom_injective B I (CommAlgCat.of R A)
    rw [← CommHopfAlgCat.mapValue_quotientPointsHom,
      CommHopfAlgCat.quotientPointsHom_liftQuotientPoint]
    simpa only [AlgHom.mapValue_apply] using toConv_aeval_one_comp_extend
      (⟨p, unipotent_le_parabolic hp⟩ : parabolic A l)
  · apply CommHopfAlgCat.quotientPointsHom_injective B I (CommAlgCat.of R A)
    rw [← CommHopfAlgCat.mapValue_quotientPointsHom,
      CommHopfAlgCat.quotientPointsHom_liftQuotientPoint, map_one]
    obtain ⟨_, hz⟩ := mem_unipotent_iff.mp hp
    simpa only [limit_apply, evalZeroPoint_apply, AlgHom.mapValue_apply] using hz

end Ring

/-- The dynamic unipotent subgroup of a finite-type affine group over a field is
geometrically connected, without smoothness or reducedness assumptions. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
    {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (l : H →ₐc[k] LaurentPolynomial k) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) l.unipotentDefiningHopfIdeal) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let Q := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) l.unipotentDefiningHopfIdeal
  let e (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :=
    AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := Q) (R := A)
  have hc : ConnectedSpace (PrimeSpectrum (K ⊗[k] Q)) := by
    apply HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      (K := K) (H := K ⊗[k] Q)
    intro x hx g
    obtain ⟨F, hFone, hFzero⟩ := exists_polynomial_path_unipotent l ((e K).symm g)
    apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path x hx g (e (Polynomial K) F)
      (Polynomial.aeval (1 : K)) (Polynomial.aeval (0 : K))
    · rw [AlgHom.mapValue_baseChangePointsMulEquiv, hFone, MulEquiv.apply_symm_apply]
    · rw [AlgHom.mapValue_baseChangePointsMulEquiv, hFzero, map_one]
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k Q K).toRingEquiv).connectedSpace_iff.mpr hc

end

end TauCeti.Cocharacter
