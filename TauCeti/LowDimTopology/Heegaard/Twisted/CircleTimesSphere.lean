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
public import TauCeti.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.MonoidAlgebra.Basic
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
`R → 𝔽₂`. So the twisted homology
(`TauCeti.HeegaardRegionSystem.circleTimesSphereTwistedHomologyEquiv`) has rank one over `𝔽₂`, as
`HF̂(S¹ × S²)` with twisted coefficients does, while the untwisted complex has rank two. The
augmentation of the twisted differential is the untwisted one at the level of chains
(`TauCeti.HeegaardRegionSystem.mapRange_augmentation_twistedHatDifferential`); the difference of
the two homologies is the failure of the non-flat augmentation to commute with homology.

That failure is measured by `Tor`. Multiplication by `1 + t` is injective on `R`
(`TauCeti.HeegaardRegionSystem.isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain`), so
the twisted complex `R → R` is a free resolution of its homology `R ⧸ (1 + t)`. With coefficients in
an `R`-module `X`, the complex becomes `X → X`, multiplication by `1 + t`, whose cycles at `p₀` are
the `(1 + t)`-torsion `X[1 + t]`
(`lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff`), which is
`Tor₁^R(X, R ⧸ (1 + t))` (`ModuleCat.torOneQuotientSpanSingletonIso`); its homology at `p₁` is
`X ⧸ (1 + t) X = X ⊗_R R ⧸ (1 + t)`. Together, the homology of `X ⊗_R CF` is
`Tor₁^R(X, R ⧸ (1 + t)) × X ⊗_R R ⧸ (1 + t)`
(`TauCeti.HeegaardRegionSystem.circleTimesSphereLTensorHomologyEquiv`), the universal coefficient
decomposition of the free complex `CF`: the class of `x ⊗ c`, for a twisted cycle `c`, is
`x ⊗ [c]` in the second factor, and the class of `x ⊗ p₀`, for `x ∈ X[1 + t]`, lies in the `Tor`
factor. For `X = 𝔽₂ = R ⧸ (1 + t)`, with `R` acting through the augmentation, `1 + t` acts by zero,
the differential of the augmented complex vanishes, and its homology is `𝔽₂ × 𝔽₂`
(`TauCeti.HeegaardRegionSystem.circleTimesSphereAugmentedHomologyEquiv`). The class of `p₁` is
the augmented twisted homology `R ⧸ (1 + t) ⊗_R 𝔽₂ = 𝔽₂`, and the class of `p₀`, which the
augmented twisted homology misses, generates `Tor₁^R(R ⧸ (1 + t), 𝔽₂) = 𝔽₂`
(`TauCeti.HeegaardRegionSystem.circleTimesSphereTorOneAddEquiv`).

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
* `TauCeti.HeegaardRegionSystem.circleTimesSphereQuotientEquiv`: `R ⧸ (1 + t) ≃ 𝔽₂`.
* `TauCeti.HeegaardRegionSystem.isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain`:
  multiplication by `1 + t` is injective.
* `lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff`: with coefficients
  in `X`, the chain `x ⊗ p₀` is a cycle exactly when `x ∈ X[1 + t]`.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereTorOneAddEquiv`:
  `Tor₁^R(R ⧸ (1 + t), R ⧸ (1 + t))` is abstractly `𝔽₂`, with
  `circleTimesSphereTorOneAddEquiv_apply`.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereTwistedHomologyEquiv`: the twisted homology is
  `R ⧸ (1 + t)`.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereLTensorHomologyEquiv`: with coefficients in `X`,
  the homology is `Tor₁^R(X, R ⧸ (1 + t)) × X ⊗_R R ⧸ (1 + t)`, with
  `circleTimesSphereLTensorHomologyEquiv_mk_tmul` and
  `circleTimesSphereLTensorHomologyEquiv_mk_tmul_single_zero`.
* `TauCeti.HeegaardRegionSystem.lTensor_twistedHatDifferential_circleTimesSphere_zero_eq_zero`:
  the differential vanishes with coefficients on which `1 + t` acts by zero.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereAugmentedHomologyEquiv`: with coefficients in
  `𝔽₂ = R ⧸ (1 + t)` the homology is `𝔽₂ × 𝔽₂`, the class of `p₀` generating the `Tor` factor
  (`circleTimesSphereAugmentedHomologyEquiv_mk_tmul_single_zero`) and the class of `p₁` the
  augmented twisted homology (`circleTimesSphereAugmentedHomologyEquiv_mk_tmul_single_one`).

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
  rw [twistedHatCoefficient_of_hatDomains_eq_pair hatDomains_circleTimesSphere_zero_zero_one
    (by simp [funext_iff, Fin.forall_fin_succ, Pi.single_apply]), add_comm, one_def]
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
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) ≠ 0 :=
  one_add_single_ne_zero (by simpa using circleTimesSpherePeriodicDomain_ne_zero) _

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

/-- Every multiple of `p₁` is a cycle of the twisted hat complex of the genus-one diagram of
`S¹ × S²`. -/
theorem twistedHatDifferential_circleTimesSphere_zero_single_one_eq_zero
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) :
    (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains ![0, 1, 1]
      (Finsupp.single (circleTimesSphereGenerator 0 1) a) = 0 :=
  (twistedHatDifferential_circleTimesSphere_zero_eq_zero_iff _).mpr
    (Finsupp.single_eq_of_ne (circleTimesSphereGenerator_zero_ne_one 0))

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
of `S¹ × S²` is `𝔽₂`, through the augmentation. This quotient is the twisted homology
(`TauCeti.HeegaardRegionSystem.circleTimesSphereTwistedHomologyEquiv`). -/
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

/-- The equivalence `R ⧸ (1 + t) ≃ 𝔽₂` sends `1` to `1`. -/
@[simp]
theorem circleTimesSphereQuotientEquiv_one : circleTimesSphereQuotientEquiv 1 = 1 := by
  rw [← map_one (Ideal.Quotient.mk _), circleTimesSphereQuotientEquiv_mk, map_one]

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

The augmented complex `𝔽₂ ⊗_R CF` has zero differential, so its homology has the two classes `p₀`
and `p₁`. The class `p₁` is `R ⧸ (1 + t) ⊗_R 𝔽₂ = 𝔽₂`, the augmented twisted homology, and the
class `p₀` generates this `Tor₁`
(`TauCeti.HeegaardRegionSystem.circleTimesSphereAugmentedHomologyEquiv`). -/
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

/-! ### The twisted homology and the homology with coefficients

Splitting the chains into their coefficients at `p₀` and at `p₁` turns the twisted complex, and
the twisted complex with coefficients in any `R`-module `X`, into the cone of multiplication by
`1 + t` (`LinearMap.mappingCone`). -/

/-- The twisted hat differential of the genus-one diagram of `S¹ × S²` squares to zero. -/
theorem twistedHatDifferential_circleTimesSphere_zero_comp_self :
    (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains ![0, 1, 1] ∘ₗ
      (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
        ![0, 1, 1] = 0 := by
  refine LinearMap.ext fun c => ?_
  have h := (circleTimesSphereGenerator_zero_ne_one 0).symm
  simp [twistedHatDifferential_circleTimesSphere_zero, h]

section Coefficients

variable (X : Type*) [AddCommGroup X]
  [Module (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) X]

/-- The chains of the genus-one diagram of `S¹ × S²` with coefficients in `X`, split into their
coefficients at `p₀` and at `p₁`. -/
private noncomputable def circleTimesSphereChainEquiv :
    ((circleTimesSphere 0).Generator →₀ X) ≃ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)] X × X :=
  Finsupp.linearEquivFunOnFinite _ X _ ≪≫ₗ
    LinearEquiv.funCongrLeft _ X (Equiv.ofBijective _ (circleTimesSphereGenerator_bijective 0)) ≪≫ₗ
    LinearEquiv.finTwoArrow _ X

private theorem circleTimesSphereChainEquiv_apply (c : (circleTimesSphere 0).Generator →₀ X) :
    circleTimesSphereChainEquiv X c =
      (c (circleTimesSphereGenerator 0 0), c (circleTimesSphereGenerator 0 1)) :=
  (rfl)

open scoped TensorProduct

/-- The chains of the genus-one diagram of `S¹ × S²` with coefficients in `X`, written as
`X ⊗_R CF`, split into their coefficients at `p₀` and at `p₁`. -/
private noncomputable def circleTimesSphereTensorChainEquiv :
    X ⊗[MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)]
        ((circleTimesSphere 0).Generator →₀
          MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) ≃ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)] X × X :=
  TensorProduct.finsuppScalarRight _ _ X _ ≪≫ₗ circleTimesSphereChainEquiv X

private theorem circleTimesSphereTensorChainEquiv_tmul (x : X)
    (c : (circleTimesSphere 0).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) :
    circleTimesSphereTensorChainEquiv X (x ⊗ₜ c) =
      (c (circleTimesSphereGenerator 0 0) • x, c (circleTimesSphereGenerator 0 1) • x) := by
  simp [circleTimesSphereTensorChainEquiv, circleTimesSphereChainEquiv_apply]

/-- With coefficients in `X`, the twisted hat complex of the genus-one diagram of `S¹ × S²` is the
cone of multiplication by `1 + t` on `X`. -/
private theorem circleTimesSphereTensorChainEquiv_comp_lTensor :
    (circleTimesSphereTensorChainEquiv X).toLinearMap ∘ₗ
        ((circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
          ![0, 1, 1]).lTensor X =
      LinearMap.mappingCone 0 0 (DistribSMul.toLinearMap _ X
          (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2))) ∘ₗ
        (circleTimesSphereTensorChainEquiv X).toLinearMap := by
  have h := (circleTimesSphereGenerator_zero_ne_one 0).symm
  refine TensorProduct.ext' fun x c => ?_
  simp [circleTimesSphereTensorChainEquiv_tmul, twistedHatDifferential_circleTimesSphere_zero, h,
    mul_smul]

/-- The twisted hat complex of the genus-one diagram of `S¹ × S²` is the cone of multiplication by
`1 + t` on `R`. -/
private theorem circleTimesSphereChainEquiv_comp_twistedHatDifferential :
    (circleTimesSphereChainEquiv _).toLinearMap ∘ₗ
        (circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
          ![0, 1, 1] =
      LinearMap.mappingCone 0 0 (DistribSMul.toLinearMap _ _
          (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2))) ∘ₗ
        (circleTimesSphereChainEquiv _).toLinearMap := by
  have h := (circleTimesSphereGenerator_zero_ne_one 0).symm
  refine LinearMap.ext fun c => ?_
  simp [circleTimesSphereChainEquiv_apply, twistedHatDifferential_circleTimesSphere_zero, h,
    mul_comm]

/-- If `1 + t` acts by zero on `X`, then the twisted hat differential of the genus-one diagram of
`S¹ × S²` with coefficients in `X` vanishes. For `X = R ⧸ (1 + t) = 𝔽₂` this is the vanishing of
the untwisted hat differential (`hatDifferential_circleTimesSphere_zero`). -/
theorem lTensor_twistedHatDifferential_circleTimesSphere_zero_eq_zero
    (hX : Module.IsTorsionBy _ X
      (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2))) :
    ((circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
      ![0, 1, 1]).lTensor X = 0 := by
  have h := circleTimesSphereTensorChainEquiv_comp_lTensor X
  rw [show DistribSMul.toLinearMap _ X _ = 0 from LinearMap.ext hX] at h
  refine LinearMap.ext fun t => (circleTimesSphereTensorChainEquiv X).injective ?_
  rw [LinearMap.zero_apply, map_zero, ← Prod.mk_zero_zero]
  simpa using congr($h t)

/-- **The twisted homology of `S¹ × S²`.** The twisted hat homology of the genus-one diagram of
`S¹ × S²` is `R ⧸ (1 + t)`: a cycle vanishes at `p₀`, and its class goes to the class of its
coefficient at `p₁`. -/
noncomputable def circleTimesSphereTwistedHomologyEquiv :
    ((circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
        ![0, 1, 1]).homology twistedHatDifferential_circleTimesSphere_zero_comp_self ≃ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)]
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
        Ideal.span
          {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)} :=
  (circleTimesSphereChainEquiv _).homologyEquiv _ (LinearMap.mappingCone_zero_zero_comp_self _)
      circleTimesSphereChainEquiv_comp_twistedHatDifferential ≪≫ₗ
    LinearMap.mappingConeZeroZeroHomologyEquiv _ ≪≫ₗ
    LinearEquiv.prodCongr
      (LinearEquiv.ofEq _ ⊥ (LinearMap.ker_eq_bot.mpr fun _ _ h =>
        isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain (by simpa using h)))
      (Submodule.quotEquivOfEq _ _ <| by
        ext a
        simp [Ideal.mem_span_singleton', mul_comm, eq_comm]) ≪≫ₗ
    LinearEquiv.uniqueProd

/-- The class of a twisted cycle `c` goes to the class of its coefficient at `p₁`. -/
@[simp]
theorem circleTimesSphereTwistedHomologyEquiv_mk
    (c : LinearMap.ker ((circleTimesSphere 0).twistedHatDifferential
      circleTimesSphereReferenceDomains ![0, 1, 1])) :
    circleTimesSphereTwistedHomologyEquiv (Submodule.Quotient.mk c) =
      Ideal.Quotient.mk _ ((c : (circleTimesSphere 0).Generator →₀
        MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains))
          (circleTimesSphereGenerator 0 1)) := by
  simp only [circleTimesSphereTwistedHomologyEquiv, circleTimesSphereChainEquiv_apply,
    LinearEquiv.trans_apply, LinearEquiv.homologyEquiv_mk,
    LinearMap.mappingConeZeroZeroHomologyEquiv_mk, LinearEquiv.prodCongr_apply,
    LinearEquiv.uniqueProd_apply]
  rw [Submodule.quotEquivOfEq_mk, Ideal.Quotient.mk_eq_mk]

end Coefficients

section Tor

open scoped TensorProduct

variable (X : Type) [AddCommGroup X]
  [Module (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)) X]

open CategoryTheory in
/-- **Changing the coefficients of the twisted complex of `S¹ × S²`.** With coefficients in an
`R`-module `X`, the homology of `X ⊗_R CF` is `Tor₁^R(X, R ⧸ (1 + t)) × X ⊗_R R ⧸ (1 + t)`, where
`R ⧸ (1 + t)` is the twisted homology (`circleTimesSphereTwistedHomologyEquiv`). This is the
universal coefficient decomposition of the free complex `CF`: the second factor is the twisted
homology with its coefficients changed, and receives the class of `x ⊗ c` for every twisted
cycle `c` (`circleTimesSphereLTensorHomologyEquiv_mk_tmul`); the first factor is the `Tor`
correction, and receives the class of `x ⊗ p₀` when `(1 + t) • x = 0`
(`circleTimesSphereLTensorHomologyEquiv_mk_tmul_single_zero`). -/
noncomputable def circleTimesSphereLTensorHomologyEquiv :
    (((circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
        ![0, 1, 1]).lTensor X).homology
        (LinearMap.lTensor_comp_lTensor_eq_zero _ X
          twistedHatDifferential_circleTimesSphere_zero_comp_self) ≃ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)]
      ((Tor (ModuleCat.{0}
          (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains))) 1).obj
        (ModuleCat.of _ X)).obj (ModuleCat.of _
          (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
            Ideal.span
              {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)})) ×
        X ⊗[MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)]
          (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
            Ideal.span
              {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)}) :=
  (circleTimesSphereTensorChainEquiv X).homologyEquiv _
      (LinearMap.mappingCone_zero_zero_comp_self _)
      (circleTimesSphereTensorChainEquiv_comp_lTensor X) ≪≫ₗ
    ModuleCat.mappingConeSMulHomologyEquiv
      isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain X

/-- For a twisted cycle `c`, the class of `x ⊗ c` goes to `x ⊗ [c]` in the second factor, where
`[c]` is the twisted homology class of `c` in `R ⧸ (1 + t)`. -/
@[simp]
theorem circleTimesSphereLTensorHomologyEquiv_mk_tmul (x : X)
    (c : LinearMap.ker ((circleTimesSphere 0).twistedHatDifferential
      circleTimesSphereReferenceDomains ![0, 1, 1])) :
    circleTimesSphereLTensorHomologyEquiv X
        (Submodule.Quotient.mk ⟨x ⊗ₜ (c : (circleTimesSphere 0).Generator →₀
          MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains)),
          LinearMap.tmul_mem_ker_lTensor x c.property⟩) =
      (0, x ⊗ₜ circleTimesSphereTwistedHomologyEquiv (Submodule.Quotient.mk c)) := by
  have hc := (twistedHatDifferential_circleTimesSphere_zero_eq_zero_iff c).mp c.property
  simp only [circleTimesSphereLTensorHomologyEquiv, LinearEquiv.trans_apply,
    LinearEquiv.homologyEquiv_mk, ModuleCat.mappingConeSMulHomologyEquiv_mk,
    circleTimesSphereTwistedHomologyEquiv_mk, circleTimesSphereTensorChainEquiv_tmul, hc, zero_smul]
  refine Prod.ext (map_zero _) ?_
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]

/-- For `x` with `(1 + t) • x = 0`, the class of `x ⊗ p₀` goes to the class of `x` in
`Tor₁^R(X, R ⧸ (1 + t))` (`ModuleCat.torOneQuotientSpanSingletonIso`), in the first factor. -/
@[simp]
theorem circleTimesSphereLTensorHomologyEquiv_mk_tmul_single_zero (x : X)
    (hx : x ∈ Submodule.torsionBy _ X
      (1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2))) :
    circleTimesSphereLTensorHomologyEquiv X
        (Submodule.Quotient.mk ⟨x ⊗ₜ Finsupp.single (circleTimesSphereGenerator 0 0) 1,
          (lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff x).mpr hx⟩) =
      ((ModuleCat.torOneQuotientSpanSingletonIso
          isSMulRegular_one_add_single_circleTimesSpherePeriodicDomain (ModuleCat.of _ X)).inv
        ⟨x, hx⟩, 0) := by
  simp [circleTimesSphereLTensorHomologyEquiv, circleTimesSphereTensorChainEquiv_tmul,
    circleTimesSphereGenerator_zero_ne_one]

open CategoryTheory in
/-- **The augmented complex of `S¹ × S²` has two classes.** With coefficients in
`R ⧸ (1 + t) = 𝔽₂`, on which `R` acts through the augmentation, the twisted hat complex of the
genus-one diagram of `S¹ × S²` has zero differential
(`lTensor_twistedHatDifferential_circleTimesSphere_zero_eq_zero`), and its homology is
`𝔽₂ × 𝔽₂`. The first factor is `Tor₁^R(𝔽₂, R ⧸ (1 + t)) ≃ 𝔽₂`
(`circleTimesSphereTorOneAddEquiv`) and holds the class of `p₀`; the second is the augmented
twisted homology `𝔽₂ ⊗_R R ⧸ (1 + t) ≃ 𝔽₂` and holds the class of `p₁`. So the class that the
twisted homology `R ⧸ (1 + t)`, of rank one, loses is the `Tor` class of `p₀`. -/
noncomputable def circleTimesSphereAugmentedHomologyEquiv :
    (((circleTimesSphere 0).twistedHatDifferential circleTimesSphereReferenceDomains
        ![0, 1, 1]).lTensor
        (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
          Ideal.span
            {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)})
      ).homology
        (LinearMap.lTensor_comp_lTensor_eq_zero _ _
          twistedHatDifferential_circleTimesSphere_zero_comp_self) ≃+
      ZMod 2 × ZMod 2 :=
  (circleTimesSphereLTensorHomologyEquiv _).toAddEquiv.trans <|
    AddEquiv.prodCongr circleTimesSphereTorOneAddEquiv
      ((Module.isTorsionBy_quotient_span_singleton _).tensorQuotEquiv.toAddEquiv.trans
        circleTimesSphereQuotientEquiv.toAddEquiv)

/-- The class of `1 ⊗ p₀` in the augmented complex of `S¹ × S²` is the generator of the `Tor`
factor. -/
theorem circleTimesSphereAugmentedHomologyEquiv_mk_tmul_single_zero :
    circleTimesSphereAugmentedHomologyEquiv
        (Submodule.Quotient.mk ⟨1 ⊗ₜ Finsupp.single (circleTimesSphereGenerator 0 0) 1,
          (lTensor_twistedHatDifferential_circleTimesSphere_zero_tmul_eq_zero_iff _).mpr
            ((Submodule.mem_torsionBy_iff _ _).mpr
              (Module.isTorsionBy_quotient_span_singleton _ (x := 1)))⟩) = (1, 0) := by
  have h := circleTimesSphereLTensorHomologyEquiv_mk_tmul_single_zero _ 1
    ((Submodule.mem_torsionBy_iff _ _).mpr (Module.isTorsionBy_quotient_span_singleton _ (x := 1)))
  simp [circleTimesSphereAugmentedHomologyEquiv, AddEquiv.prodCongr, h]

/-- The class of `1 ⊗ p₁` in the augmented complex of `S¹ × S²` is the generator of the augmented
twisted homology. -/
theorem circleTimesSphereAugmentedHomologyEquiv_mk_tmul_single_one :
    circleTimesSphereAugmentedHomologyEquiv
        (Submodule.Quotient.mk ⟨1 ⊗ₜ Finsupp.single (circleTimesSphereGenerator 0 1) 1,
          LinearMap.tmul_mem_ker_lTensor _
            (twistedHatDifferential_circleTimesSphere_zero_single_one_eq_zero 1)⟩) = (0, 1) := by
  have h := circleTimesSphereLTensorHomologyEquiv_mk_tmul
    (MonoidAlgebra (ZMod 2) (Multiplicative (circleTimesSphere 0).periodicDomains) ⧸
      Ideal.span {1 + single (Multiplicative.ofAdd circleTimesSpherePeriodicDomain) (1 : ZMod 2)}) 1
    ⟨_, twistedHatDifferential_circleTimesSphere_zero_single_one_eq_zero 1⟩
  simp [circleTimesSphereAugmentedHomologyEquiv, AddEquiv.prodCongr, h]

end Tor

end HeegaardRegionSystem

end TauCeti
