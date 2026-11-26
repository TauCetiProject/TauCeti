/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.LowDimTopology.Heegaard.CircleTimesSphere
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic
public import TauCeti.RingTheory.Regular.Tor
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Ring.Regular

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

That failure is measured by `Tor`. Multiplication by `1 + t` is injective on `R`
(`TauCeti.HeegaardRegionSystem.isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain`), so
the twisted complex `R → R` is a free resolution of its homology `R ⧸ (1 + t)`. With coefficients in
an `R`-module `X`, the complex becomes `X → X`, multiplication by `1 + t`, whose cycles at `p₀` are
the `(1 + t)`-torsion `X[1 + t]`
(`lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff`), which is
`Tor₁^R(X, R ⧸ (1 + t))` (`ModuleCat.torOneQuotientSpanSingletonIso`); its homology at `p₁` is
`X ⧸ (1 + t) X = X ⊗_R R ⧸ (1 + t)` (not formalized here). For `X = 𝔽₂ = R ⧸ (1 + t)`, with `R`
acting through the augmentation, `1 + t` acts by zero and the two classes `p₀` and `p₁` of the
augmented complex survive. What is formalized is that `Tor₁^R(R ⧸ (1 + t), R ⧸ (1 + t))` is
abstractly `𝔽₂` (`TauCeti.HeegaardRegionSystem.circleTimesSphereTorOneAddEquiv`); this is
`Tor₁^R(R ⧸ (1 + t), 𝔽₂)` via `R ⧸ (1 + t) ≃ 𝔽₂`
(`TauCeti.HeegaardRegionSystem.circleTimesSphereQuotientEquiv`). Informally, and not formalized
here, it accounts for the class `p₀` that the augmented twisted homology
`R ⧸ (1 + t) ⊗_R 𝔽₂ = 𝔽₂` misses.

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
* `TauCeti.HeegaardRegionSystem.isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain`:
  multiplication by `1 + t` is injective.
* `lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff`: with coefficients
  in `X`, the chain `x ⊗ p₀` is a cycle exactly when `x ∈ X[1 + t]`.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereTorOneAddEquiv`:
  `Tor₁^R(R ⧸ (1 + t), R ⧸ (1 + t))` is abstractly `𝔽₂`, with
  `circleTimesSphereTorOneAddEquiv_apply`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §8 (Floer homology with twisted
  coefficients, and the twisted Floer homology of `S¹ × S²`).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830), §10
  (twisted coefficients and the change of coefficients to `𝔽₂`).
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

/-- The coefficient `1 + t` of the twisted hat differential of the genus-one diagram of `S¹ × S²` is
not zero. -/
theorem one_add_single_circleTimesSpherePeriodicDomain_ne_zero :
    (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) 1 :
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) ≠ 0 := by
  intro h
  have := congrArg (fun f => f.coeff 1) h
  simp [one_def, coeff_single, circleTimesSpherePeriodicDomain_ne_zero] at this

/-- Multiplication by `1 + t` is injective on the group ring of the periodic domains of the
genus-one diagram of `S¹ × S²`: the twisted hat complex `R → R` is a free resolution of its
homology `R ⧸ (1 + t)`. -/
theorem isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain :
    IsSMulRegular (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains))
      (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)) :=
  (IsRegular.of_ne_zero' one_add_single_circleTimesSpherePeriodicDomain_ne_zero).left.isSMulRegular

/-- The cycles of the twisted hat complex of the genus-one diagram of `S¹ × S²` are the chains
vanishing at `p₀`: the coefficient `1 + t` is not a zero divisor. -/
theorem twistedHatDifferential_circleTimesSphere_zero_eq_zero_iff
    (c : (circleTimesSphere 0).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) :
    (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains ![0, 1, 1] c =
      0 ↔ c (circleTimesSphereGenerator 0 0) = 0 := by
  rw [twistedHatDifferential_circleTimesSphere_zero, Finsupp.single_eq_zero, mul_eq_zero,
    or_iff_left one_add_single_circleTimesSpherePeriodicDomain_ne_zero]

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

/-! ### Changing coefficients: the derived comparison

The augmentation `R → 𝔽₂` is not flat, so the homology of the augmented complex is not the
augmented homology. The difference is a `Tor` group. -/

/-- With coefficients in an `R`-module `X`, the chain `x ⊗ p₀` of the twisted hat complex
`X ⊗_R CF` of the genus-one diagram of `S¹ × S²` is a cycle exactly when `(1 + t) • x = 0`, that
is, when `x` lies in the `(1 + t)`-torsion of `X`. This torsion is
`Tor₁^R(X, R ⧸ (1 + t))` (`ModuleCat.torOneQuotientSpanSingletonIso`), the `Tor` term of `X`
against the twisted homology. -/
theorem lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff
    {X : Type*} [AddCommGroup X]
    [Module (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) X]
    (x : X) :
    ((circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
        ![0, 1, 1]).lTensor X (x ⊗ₜ Finsupp.single (circleTimesSphereGenerator 0 0) 1) = 0 ↔
      x ∈ Submodule.torsionBy
        (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) X
        (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) 1) := by
  -- Reading off coefficients, `X ⊗_R (Generator →₀ R) ≃ (Generator →₀ X)`, detects zero.
  have h := (TensorProduct.finsuppScalarRight
    (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains))
    (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) X
    (circleTimesSphere 0).Generator).injective
  rw [← map_eq_zero_iff _ h, Finsupp.ext_iff]
  simp [twistedHatDifferential_circleTimesSphere_zero, Finsupp.single_apply, ite_smul,
    Submodule.mem_torsionBy_iff, add_smul, ite_add_ite]

open CategoryTheory in
/-- **`Tor₁` of the twisted homology against itself is `𝔽₂`.** For the twisted hat complex of the
genus-one diagram of `S¹ × S²`, with homology `R ⧸ (1 + t)`, the group
`Tor₁^R(R ⧸ (1 + t), R ⧸ (1 + t))` is abstractly `𝔽₂`, where `R ⧸ (1 + t)` is also `𝔽₂` with `R`
acting through the augmentation (`TauCeti.HeegaardRegionSystem.circleTimesSphereQuotientEquiv`).

The augmented complex `𝔽₂ ⊗_R CF` has zero differential
(`TauCeti.HeegaardRegionSystem.hatDifferential_circleTimesSphere_zero`), so its homology has the two
classes `p₀` and `p₁`. Informally, and not formalized here (this equivalence is abstract, with no
map to that homology), the class `p₁` is `R ⧸ (1 + t) ⊗_R 𝔽₂ = 𝔽₂`, the augmented
twisted homology, and the class `p₀` is this `Tor₁`: the chains `x ⊗ p₀` that are cycles are those
with `(1 + t) • x = 0` (`lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff`),
and `1 + t` acts by zero on `𝔽₂`. -/
noncomputable def circleTimesSphereTorOneAddEquiv :
    ((Tor (ModuleCat.{0}
        (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains))) 1).obj
      (ModuleCat.of _
        (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
          Ideal.span
            {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)}))).obj
      (ModuleCat.of _
        (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
          Ideal.span
            {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)})) ≃+
      ZMod 2 :=
  (ModuleCat.torOneQuotientSpanSingletonSelfIso
    isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain).toLinearEquiv.toAddEquiv.trans
    circleTimesSphereQuotientEquiv.toAddEquiv

/-- The equivalence `Tor₁^R(R ⧸ (1 + t), R ⧸ (1 + t)) ≃ 𝔽₂` is
`ModuleCat.torOneQuotientSpanSingletonSelfIso` followed by the augmentation
`circleTimesSphereQuotientEquiv`. -/
@[simp]
theorem circleTimesSphereTorOneAddEquiv_apply (x) :
    circleTimesSphereTorOneAddEquiv x =
      circleTimesSphereQuotientEquiv ((ModuleCat.torOneQuotientSpanSingletonSelfIso
        isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain).hom x) := by
  simp [circleTimesSphereTorOneAddEquiv]

end HeegaardRegionSystem

end TauCeti
