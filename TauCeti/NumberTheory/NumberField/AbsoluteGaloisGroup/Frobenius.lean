/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Transitivity
public import TauCeti.RingTheory.Invariant.Profinite.Frobenius
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed

/-!
# Frobenius elements and the residue action in the absolute Galois group

Let `F` be a perfect field (for instance a number field), `G_F = Field.absoluteGaloisGroup F`, `O`
the integral closure of `𝓞 F` in `F^alg = AlgebraicClosure F`, and `Q` a prime of `O` over the
prime `P = Q ∩ 𝓞 F`. The group `G_F` is profinite and acts continuously on the discrete ring `O`
with invariant ring `𝓞 F` (`TauCeti.GaloisRep.continuousSMul_integralClosure`,
`TauCeti.GaloisRep.isInvariant_integralClosure`), so the profinite results of
`TauCeti.RingTheory.Invariant.Profinite` apply to the decomposition group `D_Q`, the inertia group
`I_Q` and the arithmetic Frobenius predicate of `TauCeti.GaloisRep`. This file states them in that
vocabulary, with no topology on `O` in the statements.

* `D_Q` and `I_Q` are closed in `G_F`.
* If the residue ring `𝓞 F ⧸ P` is finite, for instance if `F` is a number field and `Q ≠ ⊥`,
  then an arithmetic Frobenius at `Q` exists, and the closure of the subgroup it generates
  together with `I_Q` generates `D_Q`.
* `D_Q / I_Q ≃* Aut((O ⧸ Q)/(𝓞 F ⧸ P))`. For `Q` maximal, `O ⧸ Q` is an algebraic closure of
  `𝓞 F ⧸ P`, and a Galois extension of it when `𝓞 F ⧸ P` is perfect; so `D_Q / I_Q` is the
  absolute Galois group `Gal(k_v^alg / k_v)` of the residue field of the place `v` below `Q`.

Algebraic closedness of `O ⧸ Q` needs no Galois theory: `O` is absolutely integrally closed (a
root in `F^alg` of a monic polynomial over `O` is integral over `𝓞 F`), and so is every quotient
of `O`.

## Main definitions

* `TauCeti.GaloisRep.decompositionGroupQuotientInertiaEquiv`: `D_Q / I_Q ≃* Aut((O ⧸ Q)/(𝓞 F ⧸ P))`.

## Main results

* `TauCeti.GaloisRep.isClosed_decompositionGroup`, `TauCeti.GaloisRep.isClosed_inertiaGroup`:
  `D_Q` and `I_Q` are closed.
* `TauCeti.GaloisRep.exists_isArithFrobAtIntegralPrime`: a Frobenius at `Q` exists when
  `𝓞 F ⧸ P` is finite; `TauCeti.GaloisRep.exists_isArithFrobAtIntegralPrime_of_ne_bot` is the
  number-field form.
* `TauCeti.GaloisRep.topologicalClosure_zpowers_sup_inertiaGroup_eq_decompositionGroup`:
  `D_Q = cl⟨σ⟩ ⊔ I_Q` for a Frobenius `σ` at `Q`.
* `TauCeti.GaloisRep.isAlgClosure_quotient`: `O ⧸ Q` is an algebraic closure of `𝓞 F ⧸ P`.
* `TauCeti.GaloisRep.isGalois_quotient`: `O ⧸ Q` is Galois over a perfect `𝓞 F ⧸ P`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, and Chapter II, §9.
* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, 1973, 3.12.
-/

public section

noncomputable section

open NumberField Pointwise

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F]

/-- The discrete topology on `O`, used only inside proofs. No statement of this file mentions a
topology on `O`. -/
private abbrev topologicalSpaceIntegralClosure :
    TopologicalSpace (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
  ⊥

attribute [local instance] topologicalSpaceIntegralClosure

private theorem discreteTopology_integralClosure :
    DiscreteTopology (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
  ⟨rfl⟩

attribute [local instance] discreteTopology_integralClosure continuousSMul_integralClosure

/-! ### Closedness of decomposition and inertia groups -/

/-- The decomposition group `D_Q` of an ideal `Q` of `O` is closed in `G_F`. -/
theorem isClosed_decompositionGroup (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) :
    IsClosed (decompositionGroup F Q : Set (Field.absoluteGaloisGroup F)) :=
  Q.isClosed_stabilizer

/-- The inertia group `I_Q` of an ideal `Q` of `O` is closed in `G_F`. -/
theorem isClosed_inertiaGroup (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) :
    IsClosed (inertiaGroup F Q : Set (Field.absoluteGaloisGroup F)) :=
  Q.isClosed_inertia

/-! ### Arithmetic Frobenius elements -/

/-- **Arithmetic Frobenius elements exist in `G_F`.** For a perfect field `F` and a prime `Q` of
`O` whose residue ring `𝓞 F ⧸ Q ∩ 𝓞 F` below is finite, some `σ ∈ G_F` is an arithmetic Frobenius
at `Q`. -/
theorem exists_isArithFrobAtIntegralPrime [PerfectField F]
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.IsPrime]
    [Finite (𝓞 F ⧸ Q.under (𝓞 F))] :
    ∃ σ : Field.absoluteGaloisGroup F, IsArithFrobAtIntegralPrime σ Q :=
  IsArithFrobAt.exists_of_isInvariant_of_profinite _ _ Q

/-- **Arithmetic Frobenius elements exist in `G_F` for a number field.** At every nonzero prime
`Q` of the ring `O` of algebraic integers of `F^alg`, some `σ ∈ G_F` is an arithmetic Frobenius. -/
theorem exists_isArithFrobAtIntegralPrime_of_ne_bot [NumberField F]
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : Field.absoluteGaloisGroup F, IsArithFrobAtIntegralPrime σ Q :=
  have := Ideal.finiteQuotientOfFreeOfNeBot _ (Ideal.under_ne_bot (𝓞 F) hQ)
  exists_isArithFrobAtIntegralPrime Q

/-- **A Frobenius and inertia generate the decomposition group**, as a product of subsets: for an
arithmetic Frobenius `σ` at a prime `Q` of `O`, every element of `D_Q` is `s * i` with `s` in the
closure of the powers of `σ` and `i ∈ I_Q`. -/
theorem topologicalClosure_zpowers_mul_inertiaGroup_eq_decompositionGroup
    {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))} [Q.IsPrime]
    {σ : Field.absoluteGaloisGroup F} (hσ : IsArithFrobAtIntegralPrime σ Q) :
    ((Subgroup.zpowers σ).topologicalClosure : Set (Field.absoluteGaloisGroup F)) *
      (inertiaGroup F Q : Set (Field.absoluteGaloisGroup F)) = decompositionGroup F Q :=
  Ideal.topologicalClosure_zpowers_mul_inertia_eq_stabilizer_of_isArithFrobAt Q hσ

/-- **A Frobenius and inertia generate the decomposition group**: for an arithmetic Frobenius `σ`
at a prime `Q` of `O`, `D_Q` is generated by the closure of `⟨σ⟩` and `I_Q`. -/
theorem topologicalClosure_zpowers_sup_inertiaGroup_eq_decompositionGroup
    {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))} [Q.IsPrime]
    {σ : Field.absoluteGaloisGroup F} (hσ : IsArithFrobAtIntegralPrime σ Q) :
    (Subgroup.zpowers σ).topologicalClosure ⊔ inertiaGroup F Q = decompositionGroup F Q :=
  Ideal.topologicalClosure_zpowers_sup_inertia_eq_stabilizer_of_isArithFrobAt Q hσ

/-! ### The residue action -/

variable (P : Ideal (𝓞 F))
  (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.LiesOver P]

/-- **`D_Q / I_Q` is the residue automorphism group**: for a prime `Q` of `O` over a prime `P` of
`𝓞 F`, the action of `D_Q` on `O ⧸ Q` induces `D_Q / I_Q ≃* Aut((O ⧸ Q)/(𝓞 F ⧸ P))`. For `Q`
maximal and `𝓞 F ⧸ P` perfect this is `Gal(k_v^alg / k_v)` (`TauCeti.GaloisRep.isGalois_quotient`,
`TauCeti.GaloisRep.isAlgClosure_quotient`). -/
def decompositionGroupQuotientInertiaEquiv [PerfectField F] [Q.IsPrime] :
    decompositionGroup F Q ⧸ Q.inertia (decompositionGroup F Q) ≃*
      ((integralClosure (𝓞 F) (AlgebraicClosure F) ⧸ Q) ≃ₐ[𝓞 F ⧸ P]
        (integralClosure (𝓞 F) (AlgebraicClosure F) ⧸ Q)) :=
  Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite _ P Q

/-- `decompositionGroupQuotientInertiaEquiv` sends the class of `σ ∈ D_Q` to the residue
automorphism `Ideal.Quotient.stabilizerHom` induced by `σ`. -/
@[simp]
theorem decompositionGroupQuotientInertiaEquiv_mk [PerfectField F] [Q.IsPrime]
    (σ : decompositionGroup F Q) :
    decompositionGroupQuotientInertiaEquiv P Q σ =
      Ideal.Quotient.stabilizerHom Q P (Field.absoluteGaloisGroup F) σ :=
  Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite_mk _ P Q σ

/-- `decompositionGroupQuotientInertiaEquiv` sends the class of `σ ∈ D_Q` to the automorphism
`x mod Q ↦ σ x mod Q`. -/
theorem decompositionGroupQuotientInertiaEquiv_mk_apply [PerfectField F] [Q.IsPrime]
    (σ : decompositionGroup F Q) (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    decompositionGroupQuotientInertiaEquiv P Q σ (Ideal.Quotient.mk Q x) =
      Ideal.Quotient.mk Q ((σ : Field.absoluteGaloisGroup F) • x) := by
  rw [decompositionGroupQuotientInertiaEquiv_mk, Ideal.Quotient.stabilizerHom_apply,
    Subgroup.smul_def]

attribute [local instance] Ideal.Quotient.field in
/-- **The residue extension is an algebraic closure**: for a maximal ideal `Q` of `O` over a
maximal ideal `P` of `𝓞 F`, `O ⧸ Q` is an algebraic closure of `𝓞 F ⧸ P`. No hypothesis on `F` is
needed. -/
theorem isAlgClosure_quotient [P.IsMaximal] [Q.IsMaximal] :
    IsAlgClosure (𝓞 F ⧸ P) (integralClosure (𝓞 F) (AlgebraicClosure F) ⧸ Q) where
  isAlgClosed := isAbsolutelyIntegrallyClosed_iff_isAlgClosed.mp inferInstance
  isAlgebraic := Algebra.IsIntegral.isAlgebraic

attribute [local instance] Ideal.Quotient.field in
/-- **The residue extension is Galois over a perfect residue field**: for a maximal ideal `Q` of
`O` over `P` with `𝓞 F ⧸ P` perfect, for instance finite, `O ⧸ Q` is a Galois extension of
`𝓞 F ⧸ P`. -/
theorem isGalois_quotient [P.IsMaximal] [Q.IsMaximal] [PerfectField (𝓞 F ⧸ P)] :
    IsGalois (𝓞 F ⧸ P) (integralClosure (𝓞 F) (AlgebraicClosure F) ⧸ Q) :=
  have := isAlgClosure_quotient P Q
  IsGalois.mk

end TauCeti.GaloisRep
