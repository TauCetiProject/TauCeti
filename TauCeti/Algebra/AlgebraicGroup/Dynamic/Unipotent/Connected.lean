/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Stability
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import Mathlib.RingTheory.FiniteStability

/-!
# Geometric connectedness of cocharacter-stable subgroups of dynamic unipotent subgroups

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group `G = Spec H` over a field. A closed subgroup
`K ⊆ G` is stable under conjugation by `λ` when its Hopf ideal is stable under the coefficients of
universal conjugation (`TauCeti.HopfIdeal.IsCocharacterStable`, from `Dynamic.Stability`).

Every closed subgroup of finite type of the dynamic unipotent subgroup `U(λ)` that is stable under
conjugation by `λ` is geometrically connected, without smoothness or reducedness assumptions.
This is the contraction argument: the conjugation family `t ↦ λ(t) g λ(t)⁻¹` of a point `g` of
such a subgroup `K` extends over the origin, where its value is the identity, and it stays inside
`K` there too (`TauCeti.Cocharacter.extend_mem_quotientPointsSubgroup`). It therefore gives a
polynomial path from the identity to `g` inside `K`. After any algebraically closed field extension,
these paths make every idempotent invariant under all point translations; finite-type point
separation then proves connectedness.

When `G` is of finite type, the dynamic unipotent subgroup itself is `λ`-stable and of finite type,
so it is geometrically connected. More generally, if `λ` factors through the dynamic parabolic
`P(μ)` of a second cocharacter `μ`, for instance when `λ` and `μ` are cocharacters of a common
torus, then `U(μ)` is `λ`-stable, and for `G` of finite type the intersection `U(λ) ∩ U(μ)` is
geometrically connected. Classically, for a regular cocharacter `λ` of a maximal torus `T` of a
connected reductive group, `U(λ)` is the unipotent radical `U⁺` of a Borel subgroup containing `T`,
and for `n` in the normalizer of `T` the subgroups `U⁺ ∩ n U⁺ n⁻¹` and `U⁺ ∩ n U⁻ n⁻¹` are the
intersections `U(λ) ∩ U(μ)` for the cocharacters `μ = n λ^{±1} n⁻¹` of `T`; these identifications
are not proved here.

## Main declarations

* `TauCeti.Cocharacter.exists_polynomial_path_of_isCocharacterStable`: every point of a stable
  closed subgroup of `U(λ)` is joined to the identity by a polynomial path inside it.
* `TauCeti.Cocharacter.geometricallyConnectedCommHopfAlgProperty_quotient_of_isCocharacterStable`:
  a stable closed subgroup of finite type of `U(λ)` is geometrically connected.
* `geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal`:
  `U(λ)` is geometrically connected when `G` is of finite type.
* `geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal_sup`: so is
  `U(λ) ∩ U(μ)` when `λ` factors through `P(μ)`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 2 and 13.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

universe u v w

noncomputable section

namespace TauCeti

namespace Cocharacter

section Ring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing A] [Algebra R A]
variable {l : H →ₐc[R] LaurentPolynomial R}

/-- **Contraction to the identity.** Every point of a closed subgroup of the dynamic unipotent
subgroup `U(l)` that is stable under conjugation by `l` is joined to the identity by a polynomial
path inside that subgroup: the extended conjugation family `t ↦ l(t) g l(t)⁻¹`, which is `g` at
one and the identity at zero. -/
theorem exists_polynomial_path_of_isCocharacterStable {I : HopfIdeal R H}
    (hU : l.unipotentDefiningHopfIdeal ≤ I) (hI : I.IsCocharacterStable l)
    (g : WithConv (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) I →ₐ[R] A)) :
    ∃ F : WithConv (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) I →ₐ[R]
        Polynomial A),
      AlgHom.mapValue ((Polynomial.aeval (1 : A)).restrictScalars R) F = g ∧
      AlgHom.mapValue ((Polynomial.aeval (0 : A)).restrictScalars R) F = 1 := by
  let B := _root_.CommHopfAlgCat.of R H
  let p := CommHopfAlgCat.quotientPointsHom B I (CommAlgCat.of R A) g
  have hpI : p ∈ CommHopfAlgCat.quotientPointsSubgroup B I (CommAlgCat.of R A) :=
    CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup B I (CommAlgCat.of R A) g
  have hp : p ∈ unipotent A l := by
    rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal]
    exact CommHopfAlgCat.quotientPointsSubgroup_le_of_le B hU _ hpI
  let q : parabolic A l := ⟨p, unipotent_le_parabolic hp⟩
  have hE : ∀ h ∈ I, (extend A l q).ofConv h = 0 :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp
      (extend_mem_quotientPointsSubgroup hI q hpI)
  refine ⟨CommHopfAlgCat.liftQuotientPoint B I (CommAlgCat.of R (Polynomial A)) _ hE, ?_, ?_⟩
  · apply CommHopfAlgCat.quotientPointsHom_injective B I (CommAlgCat.of R A)
    rw [← CommHopfAlgCat.mapValue_quotientPointsHom,
      CommHopfAlgCat.quotientPointsHom_liftQuotientPoint]
    simpa only [AlgHom.mapValue_apply] using toConv_aeval_one_comp_extend q
  · apply CommHopfAlgCat.quotientPointsHom_injective B I (CommAlgCat.of R A)
    rw [← CommHopfAlgCat.mapValue_quotientPointsHom,
      CommHopfAlgCat.quotientPointsHom_liftQuotientPoint, map_one]
    obtain ⟨_, hz⟩ := mem_unipotent_iff.mp hp
    simpa only [limit_apply, evalZeroPoint_apply, AlgHom.mapValue_apply] using hz

end Ring

section Field

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {l : H →ₐc[k] LaurentPolynomial k}

/-- **A cocharacter-stable closed subgroup of `U(l)` is geometrically connected.** Over a field,
every closed subgroup of finite type of the dynamic unipotent subgroup that is stable under
conjugation by `l` is geometrically connected, without smoothness or reducedness assumptions. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_of_isCocharacterStable
    {I : HopfIdeal k H} [Algebra.FiniteType k (H ⧸ I.toIdeal)]
    (hU : l.unipotentDefiningHopfIdeal ≤ I) (hI : I.IsCocharacterStable l) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let Q := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I
  let e (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :=
    AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := Q) (R := A)
  have hc : ConnectedSpace (PrimeSpectrum (K ⊗[k] Q)) := by
    apply HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      (K := K) (H := K ⊗[k] Q)
    intro x hx g
    obtain ⟨F, hFone, hFzero⟩ := exists_polynomial_path_of_isCocharacterStable hU hI ((e K).symm g)
    apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path x hx g (e (Polynomial K) F)
      (Polynomial.aeval (1 : K)) (Polynomial.aeval (0 : K))
    · rw [AlgHom.mapValue_baseChangePointsMulEquiv, hFone, MulEquiv.apply_symm_apply]
    · rw [AlgHom.mapValue_baseChangePointsMulEquiv, hFzero, map_one]
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k Q K).toRingEquiv).connectedSpace_iff.mpr hc

variable [Algebra.FiniteType k H]

/-- The dynamic unipotent subgroup of a finite-type affine group over a field is
geometrically connected, without smoothness or reducedness assumptions. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
    (l : H →ₐc[k] LaurentPolynomial k) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) l.unipotentDefiningHopfIdeal) :=
  geometricallyConnectedCommHopfAlgProperty_quotient_of_isCocharacterStable le_rfl
    HopfIdeal.isCocharacterStable_unipotentDefiningHopfIdeal

/-- **`U(l) ∩ U(m)` is geometrically connected when `l` factors through `P(m)`**, for instance
when `l` and `m` are cocharacters of a common torus. The intersection is a closed subgroup of
`U(l)` stable under conjugation by `l`. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal_sup
    {m : H →ₐc[k] LaurentPolynomial k}
    (hlm : (parabolicDefiningHopfIdeal m).toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
        (l.unipotentDefiningHopfIdeal ⊔ m.unipotentDefiningHopfIdeal)) :=
  geometricallyConnectedCommHopfAlgProperty_quotient_of_isCocharacterStable le_sup_left
    (HopfIdeal.isCocharacterStable_unipotentDefiningHopfIdeal.sup
      (HopfIdeal.isCocharacterStable_unipotentDefiningHopfIdeal_of_le_ker hlm))

end Field

end Cocharacter

end TauCeti

end
