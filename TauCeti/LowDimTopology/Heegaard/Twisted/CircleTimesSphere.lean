/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.LowDimTopology.Heegaard.CircleTimesSphere
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# The twisted hat complex of the genus-one diagram of `S¹ × S²`

The genus-one Heegaard diagram `TauCeti.HeegaardRegionSystem.circleTimesSphere 0` of `S¹ × S²`,
with its basepoint in the annulus, has two generators `p₀` and `p₁`, and the hat differential
counts the two bigons `B₁` and `B₂` from `p₀` to `p₁`. They cancel modulo two, so the untwisted
hat complex is `𝔽₂²` with zero differential, of rank two
(`TauCeti.HeegaardRegionSystem.hatDifferential_circleTimesSphere_zero`).

The periodic domains are the multiples of `P = B₁ - B₂`, so the group ring of the periodic
domains is the ring `R = 𝔽₂[t, t⁻¹]` of Laurent polynomials in `t = t^P`. Take `p₀` as the
reference generator, with reference domains `0` at `p₀` and `B₂` at `p₁`. The labels of the
bigons are then `B₁ - B₂ = P` and `B₂ - B₂ = 0`, so the twisted hat differential is

`∂ p₀ = (1 + t) p₁`, `∂ p₁ = 0`,

the Koszul complex of `1 + t`. Since `R` has no zero divisors and `1 + t ≠ 0`, the cycles are the
multiples of `p₁`, and the boundaries are the multiples of `(1 + t) p₁`, so the homology is
`R ⧸ (1 + t)`. This quotient is `𝔽₂`: in characteristic two `1 + t = t - 1`, and as `t`
generates the group of periodic domains, `t - 1` generates the kernel of the augmentation
`R → 𝔽₂`. So, informally, the twisted homology has rank one over `𝔽₂`, as `HF̂(S¹ × S²)` with
twisted coefficients does, while the untwisted complex has rank two. The results below give the
cycles, the boundaries and the quotient; the homology module itself is not packaged as a single
statement. The augmentation of the twisted differential is the untwisted one at the level of chains
(`TauCeti.HeegaardRegionSystem.mapRange_augmentation_twistedHatDifferential`); the difference of
the two homologies is the failure of the non-flat augmentation to commute with homology.

## Main definitions

* `TauCeti.HeegaardRegionSystem.circleTimesSpherePeriodicDomain`: the periodic domain `B₁ - B₂`.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereReferenceDomains`: the reference domains `0` at
  `p₀` and `B₂` at `p₁`.

## Main results

* `TauCeti.HeegaardRegionSystem.closure_circleTimesSpherePeriodicDomain`: the monomial `t`
  generates the group of periodic domains.
* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_circleTimesSphere_zero_zero_one`: the
  twisted coefficient from `p₀` to `p₁` is `1 + t`.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_circleTimesSphere_zero`: the twisted hat
  differential sends a chain `c` to `c(p₀) (1 + t) p₁`.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_circleTimesSphere_zero_eq_zero_iff`: its
  cycles are the chains vanishing at `p₀`.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereQuotientEquiv`: `R ⧸ (1 + t) ≃ 𝔽₂` (informally,
  the twisted homology at `p₁`).

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §8 (Floer homology with twisted
  coefficients, and the twisted Floer homology of `S¹ × S²`).
-/

public section

open MonoidAlgebra

namespace TauCeti

namespace HeegaardRegionSystem

/-- The periodic domain `B₁ - B₂` of the genus-one diagram of `S¹ × S²` with its basepoint in the
annulus, the difference of its two bigons. -/
def circleTimesSpherePeriodicDomain : (circleTimesSphere 0).periodicDomains :=
  ⟨Pi.single 1 1 - Pi.single 2 1, by
    rw [periodicDomains_circleTimesSphere_zero]
    exact AddSubgroup.mem_zmultiples _⟩

@[simp]
theorem coe_circleTimesSpherePeriodicDomain :
    (circleTimesSpherePeriodicDomain : Fin 3 → ℤ) = Pi.single 1 1 - Pi.single 2 1 :=
  (rfl)

/-- The periodic domain `B₁ - B₂` is not zero. -/
theorem circleTimesSpherePeriodicDomain_ne_zero : circleTimesSpherePeriodicDomain ≠ 0 := by
  intro h
  have := congrFun (congrArg Subtype.val h) 1
  simp at this

/-- The monomial `t` of the periodic domain `B₁ - B₂` generates the group of periodic domains,
written multiplicatively. -/
theorem closure_circleTimesSpherePeriodicDomain :
    Subgroup.closure {Multiplicative.ofAdd circleTimesSpherePeriodicDomain} = ⊤ := by
  refine eq_top_iff.mpr fun Q _ => ?_
  obtain ⟨⟨D, hD⟩, rfl⟩ := Multiplicative.ofAdd.surjective Q
  have hD' := hD
  rw [periodicDomains_circleTimesSphere_zero] at hD'
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hD'
  have hk : (⟨k • (Pi.single 1 1 - Pi.single 2 1), hD⟩ : (circleTimesSphere 0).periodicDomains) =
      k • circleTimesSpherePeriodicDomain :=
    Subtype.ext (by simp)
  rw [hk, ofAdd_zsmul]
  exact Subgroup.zpow_mem _ (Subgroup.subset_closure rfl) k

/-- The reference domains of the genus-one diagram of `S¹ × S²` with its basepoint in the annulus:
the reference generator is `p₀`, with reference domain `0` at `p₀` and the bigon `B₂` at `p₁`. -/
def circleTimesSphereReferenceDomains : (circleTimesSphere 0).ReferenceDomains where
  base _ := circleTimesSphereGenerator 0 0
  domain x := ![0, Pi.single 2 1] ((circleTimesSphere 0).point x 0)
  isDomainBetween_domain x := by
    obtain ⟨a, rfl⟩ := (circleTimesSphereGenerator_bijective 0).2 x
    fin_cases a
    · simp
    · simpa using isDomainBetween_circleTimesSphere_single_two 0
  domain_basepoint x z := by
    generalize (circleTimesSphere 0).point x 0 = a
    fin_cases a <;> simp
  base_eq_base _ _ := rfl

/-- The reference generator of every generator is `p₀`. -/
@[simp]
theorem circleTimesSphereReferenceDomains_base (x : (circleTimesSphere 0).Generator) :
    circleTimesSphereReferenceDomains.base x = circleTimesSphereGenerator 0 0 :=
  (rfl)

/-- The reference domain is `0` at `p₀` and the bigon `B₂` at `p₁`. -/
@[simp]
theorem circleTimesSphereReferenceDomains_domain (a : Fin 2) :
    circleTimesSphereReferenceDomains.domain (circleTimesSphereGenerator 0 a) =
      ![0, Pi.single 2 1] a := by
  simp only [circleTimesSphereReferenceDomains]
  rw [circleTimesSphereGenerator_point]

/-- The twisted coefficient from `p₀` to `p₁` of the genus-one diagram of `S¹ × S²` is `1 + t`:
the bigon `B₂` has label `0` and the bigon `B₁` has label `B₁ - B₂`. -/
theorem twistedHatCoefficient_circleTimesSphere_zero_zero_one :
    (circleTimesSphere 0).twistedHatCoefficient circleTimesSphereReferenceDomains ![0, 1, 1]
      (circleTimesSphereGenerator 0 0) (circleTimesSphereGenerator 0 1) =
      1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) 1 := by
  classical
  have hD := hatDomains_circleTimesSphere_zero_zero_one
  have h1 : (Pi.single 1 1 : Fin 3 → ℤ) ∈ (circleTimesSphere 0).hatDomains ![0, 1, 1]
      (circleTimesSphereGenerator 0 0) (circleTimesSphereGenerator 0 1) := by
    simp [hD]
  have h2 : (Pi.single 2 1 : Fin 3 → ℤ) ∈ (circleTimesSphere 0).hatDomains ![0, 1, 1]
      (circleTimesSphereGenerator 0 0) (circleTimesSphereGenerator 0 1) := by
    simp [hD]
  have := (weaklyAdmissible_circleTimesSphere_zero.finite_hatDomains ![0, 1, 1]
    (circleTimesSphereGenerator 0 0) (circleTimesSphereGenerator 0 1)).fintype
  have huniv : (Finset.univ : Finset ((circleTimesSphere 0).hatDomains ![0, 1, 1]
      (circleTimesSphereGenerator 0 0) (circleTimesSphereGenerator 0 1))) =
      {⟨_, h2⟩, ⟨_, h1⟩} := by
    ext ⟨D, hDm⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
      true_iff]
    rw [hD] at hDm
    simpa [or_comm] using hDm
  have hne : (⟨_, h2⟩ : (circleTimesSphere 0).hatDomains ![0, 1, 1]
      (circleTimesSphereGenerator 0 0) (circleTimesSphereGenerator 0 1)) ≠ ⟨_, h1⟩ := by
    simp [funext_iff, Fin.forall_fin_succ, Pi.single_apply]
  rw [twistedHatCoefficient_eq_sum, huniv, Finset.sum_pair hne, one_def]
  congr 2 <;> refine congrArg Multiplicative.ofAdd (Subtype.ext ?_) <;>
    simp [ReferenceDomains.label_def]

/-- The twisted coefficients of the genus-one diagram of `S¹ × S²`: `1 + t` from `p₀` to `p₁`,
and `0` otherwise. -/
theorem twistedHatCoefficient_circleTimesSphere_zero (a b : Fin 2) :
    (circleTimesSphere 0).twistedHatCoefficient circleTimesSphereReferenceDomains ![0, 1, 1]
      (circleTimesSphereGenerator 0 a) (circleTimesSphereGenerator 0 b) =
      if a = 0 ∧ b = 1 then 1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) 1
      else 0 := by
  fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one, and_true,
    ite_true, one_ne_zero, zero_ne_one, and_false, ite_false]
  · exact weaklyAdmissible_circleTimesSphere_zero.twistedHatCoefficient_self _ _ _
  · exact twistedHatCoefficient_circleTimesSphere_zero_zero_one
  · exact twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty
      hatDomains_circleTimesSphere_zero_one_zero
  · exact weaklyAdmissible_circleTimesSphere_zero.twistedHatCoefficient_self _ _ _

/-- The twisted hat differential of the genus-one diagram of `S¹ × S²` sends a chain `c` to
`c(p₀) (1 + t) p₁`. -/
theorem twistedHatDifferential_circleTimesSphere_zero
    (c : (circleTimesSphere 0).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) :
    (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains ![0, 1, 1] c =
      Finsupp.single (circleTimesSphereGenerator 0 1)
        (c (circleTimesSphereGenerator 0 0) *
          (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) 1)) := by
  refine Finsupp.ext fun y => ?_
  rw [← circleTimesSphereGenerator_snd_zero 0 y, twistedHatDifferential_apply,
    Finsupp.sum_fintype _ _ (by simp),
    ← Fintype.sum_bijective _ (circleTimesSphereGenerator_bijective 0) _ _ fun _ => rfl,
    Fin.sum_univ_two]
  generalize (y.2 0 : Fin 2) = b
  fin_cases b <;> simp [twistedHatCoefficient_circleTimesSphere_zero,
    (circleTimesSphereGenerator_bijective 0).1.eq_iff]

/-- The cycles of the twisted hat complex of the genus-one diagram of `S¹ × S²` are the chains
vanishing at `p₀`: the coefficient `1 + t` is not a zero divisor. -/
theorem twistedHatDifferential_circleTimesSphere_zero_eq_zero_iff
    (c : (circleTimesSphere 0).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) :
    (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains ![0, 1, 1] c =
      0 ↔ c (circleTimesSphereGenerator 0 0) = 0 := by
  have : UniqueSums (circleTimesSphere 0).periodicDomains :=
    UniqueSums.of_injective_addHom (circleTimesSphere 0).periodicDomains.subtype.toAddHom
      Subtype.val_injective inferInstance
  have hne : (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) 1 :
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) ≠ 0 := by
    intro h
    have := congrArg (fun f => f.coeff 1) h
    simp [one_def, coeff_single, circleTimesSpherePeriodicDomain_ne_zero] at this
  rw [twistedHatDifferential_circleTimesSphere_zero, Finsupp.single_eq_zero, mul_eq_zero,
    or_iff_left hne]

/-- In the group ring of the periodic domains of the genus-one diagram of `S¹ × S²`, the ideal
generated by `1 + t` is the kernel of the augmentation. -/
theorem span_one_add_single_circleTimesSpherePeriodicDomain :
    Ideal.span {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)} =
      RingHom.ker (augmentation (ZMod 2)
        (Multiplicative (circleTimesSphere 0).periodicDomains)) := by
  rw [TauCeti.MonoidAlgebra.ker_augmentation_eq_span_of_closure_eq_top (ZMod 2)
    closure_circleTimesSpherePeriodicDomain]
  simp [sub_eq_add_neg, add_comm, one_def, ← single_neg]

/-- The quotient `R ⧸ (1 + t)` of the group ring of the periodic domains of the genus-one diagram
of `S¹ × S²` is `𝔽₂`, through the augmentation. Informally, this quotient is the twisted homology
at `p₁` (see the module docstring), but the homology module itself is not defined here. -/
noncomputable def circleTimesSphereQuotientEquiv :
    (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
      Ideal.span {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)})
      ≃ₗ[ZMod 2] ZMod 2 :=
  (Ideal.quotientEquivAlgOfEq (ZMod 2)
    span_one_add_single_circleTimesSpherePeriodicDomain).toLinearEquiv ≪≫ₗ
    _root_.MonoidAlgebra.quotientKerAugmentationEquiv (ZMod 2) _

/-- The equivalence `R ⧸ (1 + t) ≃ 𝔽₂` is induced by the augmentation. -/
@[simp]
theorem circleTimesSphereQuotientEquiv_mk
    (f : MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) :
    circleTimesSphereQuotientEquiv (Ideal.Quotient.mk _ f) = augmentation (ZMod 2) _ f := by
  simp [circleTimesSphereQuotientEquiv, Ideal.quotientEquivAlgOfEq_mk]

end HeegaardRegionSystem

end TauCeti
