/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Algebraic
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteComponent
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Shift
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Presentations of algebraic Hecke characters

An algebraic Hecke character of a number field `K` (Weil's type `A₀`) is an idele class character
`χ` whose archimedean restriction agrees on the identity component with the character
`x ↦ ∏_τ τ(x) ^ n_τ` of integer exponents `n_τ`, one for each embedding `τ : K →+* ℂ`. Its
L-function is a Dirichlet series over the ideals, and Hecke's theta-series proof of its
functional equation works with the ideal-theoretic shadow of `χ`: the values of its unitary
part at the prime ideals, the exponents `n_τ`, and a modulus outside of which `χ` is unramified.

A `TauCeti.LFunctions.Grossencharacter K 𝔪` records all of these at a modulus `𝔪`, with the idele
class character as the primary object and every other field pinned to it:

* `unitaryWeight` is the completely multiplicative ideal weight of the unitary part `χ_u`: at a
  prime `𝔭 ∤ 𝔪` it is the local component of `χ_u` at any uniformizer of `K_𝔭`, and it vanishes
  at the ideals not prime to `𝔪`;
* `infinityType` is the algebraic infinity type `n`, agreeing with the archimedean restriction of
  `χ` on the identity component, and on the nose at the real places outside `𝔪`;
* `χ` is trivial on the ideles of `ideleCongruenceSubgroup 𝔪` with all archimedean coordinates
  `1`. Triviality on the whole congruence subgroup, which contains the archimedean identity
  components, would force finite order.

A presentation is therefore determined by its Hecke character (`Grossencharacter.ext`). Every
finite-order character of a ray class group is presented (`Grossencharacter.ofRayClassCharacter`),
with the ray-class weight, the zero infinity type, and the presented L-function of the ray class
character (`Grossencharacter.lFunctionC_ofRayClassCharacter`).

The real shift is not a field. On ideals the convention is `χ = χ_u N^σ`: at a uniformizer `π_𝔭`
of a prime `𝔭 ∤ 𝔪`, `χ(π_𝔭) = χ_u(𝔭) N𝔭 ^ σ` (`Grossencharacter.toHeckeCharacter_primeIdele`).
Since `‖π_𝔭‖ = N𝔭⁻¹`, this ideal-side shift `σ = Grossencharacter.idealShift` is the negative of
the idelic shift `HeckeCharacter.shift`, which is defined by `|χ| = ‖·‖ ^ shift`. The presented
L-function `Grossencharacter.lFunctionC` is the canonical meromorphic continuation of
`∑_𝔞 χ_u(𝔞) N𝔞 ^ (σ - s)` from its half-plane of absolute convergence `Re s > 1 + σ`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter`: a presentation of an algebraic Hecke character at a
  modulus.
* `TauCeti.LFunctions.Grossencharacter.idealShift`: the ideal-side shift.
* `TauCeti.LFunctions.Grossencharacter.ofRayClassCharacter`: the presentation of a ray class
  character.
* `TauCeti.LFunctions.Grossencharacter.lFunctionC`: the presented L-function.

## Main results

* `TauCeti.LFunctions.Grossencharacter.ext`: a presentation is determined by its Hecke character.
* `TauCeti.LFunctions.Grossencharacter.isAlgebraic`: the presented Hecke character is algebraic.
* `TauCeti.LFunctions.Grossencharacter.toHeckeCharacter_primeIdele`: the value at a prime idele.
* `TauCeti.LFunctions.Grossencharacter.lFunctionC_ofRayClassCharacter`: the presented L-function
  of a ray class character is its Hecke L-function.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open Set IsDedekindDomain NumberField
open scoped NumberField NNReal

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **A presentation of an algebraic Hecke character at a modulus `𝔪`.** The idele class character
`toHeckeCharacter` is the primary object, and every other field is pinned to it, so that a
presentation is determined by its Hecke character (`Grossencharacter.ext`).

* `unitaryWeight` is the ideal weight of the unitary part: at a prime `v ∤ 𝔪` it is the local
  component of `toHeckeCharacter.unitaryPart` at any uniformizer of `K_v`, and it vanishes at the
  ideals not prime to `𝔪`.
* `infinityType` is the algebraic infinity type of the archimedean restriction: they agree on the
  identity component, which witnesses that `toHeckeCharacter` is algebraic, and their parities
  agree at the real places outside `𝔪`.
* `𝔪` is a modulus of definition: `toHeckeCharacter` is trivial on the ideles of
  `ideleCongruenceSubgroup 𝔪` whose archimedean coordinates are all `1`. -/
structure Grossencharacter (K : Type*) [Field K] [NumberField K] (𝔪 : Modulus K) where
  /-- The presented idele class character. -/
  toHeckeCharacter : HeckeCharacter K
  /-- The ideal weight of the unitary part, extended by zero at the ideals not prime to `𝔪`. -/
  unitaryWeight : UnitaryIdealWeight K
  /-- The integer exponents of the archimedean restriction, one at each complex embedding. -/
  infinityType : AlgebraicInfinityType K
  /-- The character is trivial on the finite part of the congruence subgroup of `𝔪`. -/
  eq_one_of_mem : ∀ y ∈ ideleCongruenceSubgroup 𝔪,
    (∀ w : InfinitePlace K, w.ideleInfiniteCoord y = 1) →
      toHeckeCharacter (y : IdeleClassGroup (𝓞 K) K) = 1
  /-- The archimedean restriction agrees with `infinityType` on the identity component. -/
  agreesOnIdentityComponent : toHeckeCharacter.infinityType.AgreesOnIdentityComponent
    (AlgebraicInfinityType.toContinuous infinityType)
  /-- At the real places outside `𝔪`, no sign twist is presented. -/
  realParity_eq : ∀ w, w ∉ 𝔪.infinitePart →
    toHeckeCharacter.infinityType.realParity w =
      (AlgebraicInfinityType.toContinuous infinityType).realParity w
  /-- The weight vanishes at the ideals not prime to `𝔪`. -/
  unitaryWeight_eq_zero : ∀ I : Ideal (𝓞 K), ¬ 𝔪.IsCoprimeTo I → unitaryWeight.1 I = 0
  /-- At a prime `v ∤ 𝔪`, the weight is the local component of the unitary part at a
  uniformizer. -/
  unitaryWeight_apply : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.finitePart →
    ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = WithZero.exp (-1) →
      unitaryWeight.1 v.asIdeal = toHeckeCharacter.unitaryPart.finiteComponent v u

namespace Grossencharacter

variable {𝔪 : Modulus K}

/-- **The presented Hecke character is algebraic**, of Weil's type `A₀`, with algebraic infinity
type `infinityType`. -/
theorem isAlgebraic (χ : Grossencharacter K 𝔪) : χ.toHeckeCharacter.IsAlgebraic :=
  HeckeCharacter.isAlgebraic_iff_exists_agreesOnIdentityComponent.mpr
    ⟨χ.infinityType, χ.agreesOnIdentityComponent⟩

/-- The weight of a presentation vanishes at the primes dividing the modulus. -/
theorem unitaryWeight_apply_of_dvd (χ : Grossencharacter K 𝔪) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔪.finitePart) : χ.unitaryWeight.1 v.asIdeal = 0 :=
  χ.unitaryWeight_eq_zero _ fun h ↦
    (Modulus.isCoprimeTo_iff.mp h).2 v ((𝔪.mem_support_iff v).mpr hv) dvd_rfl

/-- **A presentation is determined by its Hecke character.** The infinity type is determined on
the identity component (`AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff`), and
the weight is determined at every prime: at the primes of `𝔪` it vanishes, and at the others it is
a local component of the unitary part. -/
@[ext]
theorem ext {χ ψ : Grossencharacter K 𝔪} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ = ψ := by
  have hn : χ.infinityType = ψ.infinityType :=
    AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff.mp
      (χ.agreesOnIdentityComponent.symm.trans (h ▸ ψ.agreesOnIdentityComponent))
  have hw : χ.unitaryWeight = ψ.unitaryWeight := by
    refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
    by_cases hv : v.asIdeal ∣ 𝔪.finitePart
    · rw [χ.unitaryWeight_apply_of_dvd hv, ψ.unitaryWeight_apply_of_dvd hv]
    · -- Compare the two weights at a uniformizer of `K_v`.
      have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
      have hu := v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu
      rw [χ.unitaryWeight_apply v hv u hu, ψ.unitaryWeight_apply v hv u hu, h]
  cases χ
  cases ψ
  simp_all

/-- The presentations at `𝔪` embed into the Hecke characters. -/
theorem toHeckeCharacter_injective :
    Function.Injective (toHeckeCharacter : Grossencharacter K 𝔪 → HeckeCharacter K) :=
  fun _ _ ↦ ext

/-! ### The shift -/

/-- **The ideal-side shift** `σ` of the convention `χ = χ_u N ^ σ` on ideals
(`toHeckeCharacter_primeIdele`). It is the **negative** of the idelic shift
`HeckeCharacter.shift`, defined by `|χ| = ‖·‖ ^ shift`, because a uniformizer at `𝔭` has idele
norm `N𝔭⁻¹`. -/
def idealShift (χ : Grossencharacter K 𝔪) : ℝ :=
  -χ.toHeckeCharacter.shift

/-- The defining equation of the ideal-side shift. -/
theorem idealShift_def (χ : Grossencharacter K 𝔪) :
    χ.idealShift = -χ.toHeckeCharacter.shift :=
  (rfl)

/-- **The value at a prime idele.** At a uniformizer `π_v` of `K_v`, `v ∤ 𝔪`, the presented Hecke
character is the unitary weight times the norm to the ideal-side shift:
`χ(π_v) = χ_u(v) N(v) ^ idealShift`. -/
theorem toHeckeCharacter_primeIdele (χ : Grossencharacter K 𝔪) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ 𝔪.finitePart) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = WithZero.exp (-1)) :
    ((χ.toHeckeCharacter.finiteComponent v u : ℂˣ) : ℂ) =
      χ.unitaryWeight.1 v.asIdeal * (v.asIdeal.absNorm : ℂ) ^ (χ.idealShift : ℂ) := by
  -- Split `χ = χ_u ‖·‖ ^ shift`; a uniformizer idele has norm `N(v)⁻¹`.
  rw [← χ.toHeckeCharacter.unitaryPart_mul_normPow_shift, HeckeCharacter.finiteComponent_mul,
    ContinuousMonoidHom.mul_apply, Units.val_mul, ← χ.unitaryWeight_apply v hv u hu]
  -- `N(v)` is a natural number, so its argument is `0 ≠ π` and `(N(v)⁻¹) ^ s = N(v) ^ (-s)`.
  have harg : (v.asIdeal.absNorm : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  simp [IdeleClassGroup.ofAdicCompletion_apply,
    coe_ideleNorm_ofAdicCompletion_of_valued_eq_exp_neg_one v hu, idealShift_def,
    Complex.inv_cpow _ _ harg, Complex.cpow_neg]

/-! ### The presentation of a ray class character -/

/-- **The presentation of a ray class character** `η` of `𝔪`: the Hecke character
`HeckeCharacter.ofRayClassCharacter 𝔪 η`, the ray-class weight `η.toUnitaryIdealWeight` and the
zero infinity type. -/
def ofRayClassCharacter (η : RayClassCharacter 𝔪) : Grossencharacter K 𝔪 where
  toHeckeCharacter := HeckeCharacter.ofRayClassCharacter 𝔪 η
  unitaryWeight := η.toUnitaryIdealWeight
  infinityType := 0
  eq_one_of_mem y hy _ := HeckeCharacter.ofRayClassCharacter_apply_eq_one_of_mem_raySubgroup η
    (mem_raySubgroup_iff.mpr ⟨y, hy, rfl⟩)
  agreesOnIdentityComponent := by
    obtain ⟨ε, hε⟩ := HeckeCharacter.exists_finiteOrderInfinityType
      (HeckeCharacter.isFiniteOrder_ofRayClassCharacter η)
    rw [hε, map_zero,
      ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType]
    exact ⟨ε, (zero_add _).symm⟩
  realParity_eq w hw := by
    rw [map_zero, ContinuousInfinityType.zero_realParity, Pi.zero_apply,
      ← HeckeCharacter.infiniteComponent_eq_one_iff
        (HeckeCharacter.isFiniteOrder_ofRayClassCharacter η)]
    exact HeckeCharacter.infiniteComponent_eq_one_of_mem_range_ofRayClassCharacter ⟨η, rfl⟩
      fun w' hw' h ↦ hw (Subtype.ext h ▸ hw')
  unitaryWeight_eq_zero I hI := by
    rw [RayClassCharacter.val_toUnitaryIdealWeight,
      RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo η
        fun h ↦ hI (Modulus.isCoprimeTo_iff.mpr (Ideal.isPrimeTo_iff.mp h))]
  unitaryWeight_apply v hv u hu := by
    have hv' : v ∉ 𝔪.support := (𝔪.mem_support_iff v).not.mpr hv
    -- The character of `η` is its own unitary part, and its component at the uniformizer `u` is
    -- the value of `η` on the prime `v`, which is the ray-class weight at `v`.
    rw [(HeckeCharacter.unitaryPart_eq_self_iff _).mpr
        (HeckeCharacter.shift_ofRayClassCharacter η),
      HeckeCharacter.finiteComponent_ofRayClassCharacter_of_isUniformizer η hv'
        (v.isUniformizer_iff_valued_eq_exp_neg_one.mpr hu)]
    simp [Ideal.isPrimeTo_asIdeal_iff.mpr hv']

/-- The Hecke character presented by `ofRayClassCharacter η` is that of `η`. -/
@[simp]
theorem toHeckeCharacter_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).toHeckeCharacter = HeckeCharacter.ofRayClassCharacter 𝔪 η :=
  (rfl)

/-- The weight of `ofRayClassCharacter η` is the ray-class weight of `η`. -/
@[simp]
theorem unitaryWeight_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).unitaryWeight = η.toUnitaryIdealWeight :=
  (rfl)

/-- A ray class character has the zero infinity type. -/
@[simp]
theorem infinityType_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).infinityType = 0 :=
  (rfl)

/-- A ray class character has ideal-side shift `0`, as it has finite order. -/
@[simp]
theorem idealShift_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).idealShift = 0 := by
  rw [idealShift_def, toHeckeCharacter_ofRayClassCharacter,
    HeckeCharacter.shift_ofRayClassCharacter, neg_zero]

/-! ### The presented L-function -/

/-- **The presented L-function** of `χ`: the canonical meromorphic continuation from
`Re s > 1 + idealShift` of `∑_𝔞 χ_u(𝔞) N𝔞 ^ (idealShift - s)`, the norm-regrouped series of the
unitary weight at `s - idealShift`. It agrees with the series on that half-plane once a
continuation to the plane exists (`meromorphicContinuation_eqOn`), and is `0` otherwise. -/
def lFunctionC (χ : Grossencharacter K 𝔪) : ℂ → ℂ :=
  meromorphicContinuation (1 + χ.idealShift) fun s ↦
    LSeries (normCoeff K χ.unitaryWeight.toIdealArithmeticFunction) (s - χ.idealShift)

/-- The defining equation of the presented L-function, through which the general results on
`meromorphicContinuation` apply to it. -/
theorem lFunctionC_def (χ : Grossencharacter K 𝔪) :
    χ.lFunctionC = meromorphicContinuation (1 + χ.idealShift) fun s ↦
      LSeries (normCoeff K χ.unitaryWeight.toIdealArithmeticFunction) (s - χ.idealShift) :=
  (rfl)

/-- The presented L-function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_lFunctionC (χ : Grossencharacter K 𝔪) :
    MeromorphicNFOn χ.lFunctionC univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The presented L-function is holomorphic on `Re s > 1 + idealShift`. -/
theorem analyticOnNhd_lFunctionC (χ : Grossencharacter K 𝔪) :
    AnalyticOnNhd ℂ χ.lFunctionC {s | 1 + χ.idealShift < s.re} := by
  refine analyticOnNhd_meromorphicContinuation
    ((analyticOnNhd_LSeries_of_unitary χ.unitaryWeight).comp
      (analyticOnNhd_id.sub analyticOnNhd_const) fun s hs ↦ ?_)
  simp only [mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] at hs ⊢
  linarith

/-- **The presented L-function of a ray class character** is its presented Hecke L-function. -/
theorem lFunctionC_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).lFunctionC = heckeLFunctionC η := by
  simp [lFunctionC_def, heckeLFunctionC_def]

end Grossencharacter

end TauCeti.LFunctions
