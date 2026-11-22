/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Basic
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.UnitaryWeight
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Rat
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.RealParity
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# The presentation conductor, primitive reduction, and norm-power Grossencharacters

One algebraic Hecke character of a number field `K` can be presented (`Grossencharacter K 𝔪`) at
every modulus `𝔪` that clears both its finite ramification and the real sign mismatches between its
archimedean restriction and its algebraic infinity type. This file identifies the least such
modulus, constructs the primitive presentation there and the induced presentations at its
multiples, compares their L-functions by the deleted Euler factors, relates finite-order
presentations to ray class characters, and builds the integral norm-power presentations `N ^ m`.

## The presentation conductor

For a presentation `χ : Grossencharacter K 𝔪`, `χ.conductor` is the modulus whose finite part is
`χ.toHeckeCharacter.finiteConductor` (`∏_v v ^ a_v(χ)`) and whose infinite part consists of the
real places `w` at which the parity `χ.toHeckeCharacter.infinityType.realParity w` of the
archimedean restriction differs from
`(AlgebraicInfinityType.toContinuous χ.infinityType).realParity w`.

At a real place, this is the conductor of the **presentation**, not the ramification conductor of
the idele class character: the odd norm powers `N ^ m = ‖·‖ ^ (-m)` (`Grossencharacter.normPow`)
have archimedean component `x ↦ |x| ^ (-m)` trivial on `±1`, yet every real place divides their
presentation conductor (`Grossencharacter.conductor_normPow_of_odd`) because their algebraic
exponent `-m` is odd while `realParity_eq` forbids an unrecorded parity mismatch outside the
modulus. For a character of finite order the algebraic infinity type is `0`, the two notions agree,
and `Grossencharacter.conductor` equals `HeckeCharacter.conductor`
(`Grossencharacter.conductor_eq_heckeCharacter_conductor`).

A modulus `𝔫` presents `χ.toHeckeCharacter` if and only if `χ.conductor ∣ 𝔫`
(`Grossencharacter.conductor_dvd_iff`). In particular, `χ.primitive` is the canonical presentation
at `χ.conductor`, with unitary weight `χ.toHeckeCharacter.unitaryIdealWeight`, and every algebraic
Hecke character admits a presentation at some modulus
(`Grossencharacter.exists_grossencharacter_iff_isAlgebraic`).

## Imprimitive Euler factors

Presenting `χ` at a multiple `𝔫` of `𝔪` restricts its unitary weight away from `𝔫.support`,
multiplying its L-series on `Re s > 1 + χ.idealShift` and the punctured germs of `lFunctionC` at
every point of `ℂ` by the entire product
`Grossencharacter.eulerCorrection χ 𝔫 s = ∏_{𝔭 ∣ 𝔫, 𝔭 ∤ 𝔪} (1 - χ_u(𝔭) N𝔭 ^ (idealShift - s))`,
whose zeros lie on the vertical line `Re s = χ.idealShift`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.conductor`: the least modulus presenting `χ`.
* `TauCeti.LFunctions.Grossencharacter.changeModulus`: the presentation of `χ` at any multiple of
  `χ.conductor`.
* `TauCeti.LFunctions.Grossencharacter.primitive`: the canonical presentation at `χ.conductor`.
* `TauCeti.LFunctions.Grossencharacter.eulerCorrection`: the Euler factors deleted when passing to
  a larger modulus.
* `TauCeti.LFunctions.Grossencharacter.normPow`: the presentation at `narrowModulus K` of the
  integral norm power `‖·‖ ^ (-m)` (`m : ℤ`), with ideal-side shift `m` and L-function
  `dedekindZetaC K (s - m)` (`riemannZeta (s - m)` over `ℚ` away from `s = 1 + m`).

## Main results

* `TauCeti.LFunctions.Grossencharacter.conductor_dvd_iff`: `χ.conductor ∣ 𝔫` iff
  `χ.toHeckeCharacter` admits a presentation at `𝔫`.
* `TauCeti.LFunctions.Grossencharacter.exists_grossencharacter_iff_isAlgebraic`: a Hecke character
  admits a `Grossencharacter` presentation iff it is algebraic.
* `TauCeti.LFunctions.Grossencharacter.lFunctionC_eq_primitive` and
  `TauCeti.LFunctions.Grossencharacter.lFunctionC_eventuallyEq_primitive`: every presented
  L-function is the primitive L-function times the deleted Euler factors, on
  `Re s > 1 + χ.idealShift` and as punctured germs everywhere.
* `TauCeti.LFunctions.Grossencharacter.conductor_eq_heckeCharacter_conductor` and
  `TauCeti.LFunctions.Grossencharacter.isFiniteOrder_iff_mem_range_ofRayClassCharacter`:
  finite-order presentations and ray class characters.
* `TauCeti.LFunctions.Grossencharacter.conductor_normPow_of_even`,
  `TauCeti.LFunctions.Grossencharacter.conductor_normPow_of_odd`, and
  `TauCeti.LFunctions.Grossencharacter.not_exists_grossencharacter_one_normPow_of_odd`: parity
  dichotomy for `normPow K m` and non-presentability at the trivial modulus when `m` is odd and `K`
  has a real place.
* `TauCeti.LFunctions.Grossencharacter.lFunctionC_normPow` and
  `TauCeti.LFunctions.Grossencharacter.lFunctionC_normPow_rat`: the L-function of `normPow`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open Filter Set IsDedekindDomain NumberField
open scoped NumberField NNReal Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace Grossencharacter

variable {𝔪 𝔫 : Modulus K}

/-! ### The unitary weight of a presentation -/

/-- **The unitary weight of any presentation at `𝔪` is the primitive unitary ideal weight of its
Hecke character restricted away from `𝔪.support`.** -/
theorem unitaryWeight_eq_restrictAway (χ : Grossencharacter K 𝔪) :
    χ.unitaryWeight =
      χ.toHeckeCharacter.unitaryIdealWeight.restrictAway 𝔪.support 𝔪.support.finite_toSet := by
  classical
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  by_cases hv : v.asIdeal ∣ 𝔪.finitePart
  · have hmem : v ∈ 𝔪.support := (𝔪.mem_support_iff v).mpr hv
    have hbad : ¬ Ideal.IsPrimeTo v.asIdeal 𝔪.support :=
      fun hg ↦ (Ideal.isPrimeTo_asIdeal_iff.mp hg) (by simpa using hmem)
    rw [χ.unitaryWeight_apply_of_dvd hv, UnitaryIdealWeight.val_restrictAway,
      MultiplicativeIdealWeight.restrictAway_apply]
    simp [hbad]
  · have hnot : v ∉ 𝔪.support := (𝔪.mem_support_iff v).not.mpr hv
    have hgood : Ideal.IsPrimeTo v.asIdeal 𝔪.support := Ideal.isPrimeTo_asIdeal_iff.mpr hnot
    have hndvd : ¬ v.asIdeal ∣ χ.toHeckeCharacter.finiteConductor :=
      fun hdvd ↦ hv (hdvd.trans χ.finiteConductor_dvd_finitePart)
    obtain ⟨u, hu⟩ := v.exists_unit_valued_eq_exp K (-1)
    rw [χ.unitaryWeight_apply v hv u hu, UnitaryIdealWeight.val_restrictAway,
      MultiplicativeIdealWeight.restrictAway_apply,
      ite_eq_left_iff.mpr fun h ↦ (h hgood).elim,
      HeckeCharacter.unitaryIdealWeight_apply_prime _ v hndvd u hu]

/-! ### The presentation conductor and primitive reduction -/

open Classical in
/-- **The presentation conductor** of a Grossencharacter `χ`: the modulus whose finite part is
`χ.toHeckeCharacter.finiteConductor` and whose infinite part consists of the real places at which
the parity of `χ.toHeckeCharacter.infinityType` differs from the parity of `χ.infinityType`.

It is the least modulus at which `χ.toHeckeCharacter` admits a presentation
(`conductor_dvd_iff`). At real places this records sign-parity mismatch against the algebraic
infinity type rather than local ramification on `±1`; for finite-order characters the algebraic
infinity type vanishes and the two agree (`conductor_eq_heckeCharacter_conductor`). -/
def conductor (χ : Grossencharacter K 𝔪) : Modulus K where
  finitePart := χ.toHeckeCharacter.finiteConductor
  finitePart_ne_bot := χ.toHeckeCharacter.finiteConductor_ne_bot
  infinitePart := (narrowModulus K).infinitePart.filter fun w ↦
    χ.toHeckeCharacter.infinityType.realParity w ≠
      (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w

/-- The finite part of `χ.conductor` is the finite conductor of `χ.toHeckeCharacter`. -/
@[simp]
theorem finitePart_conductor (χ : Grossencharacter K 𝔪) :
    χ.conductor.finitePart = χ.toHeckeCharacter.finiteConductor :=
  (rfl)

/-- A real place divides `χ.conductor` exactly when the archimedean parity of
`χ.toHeckeCharacter` differs from that of `χ.infinityType` there. -/
@[simp]
theorem mem_conductor_infinitePart_iff (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ χ.conductor.infinitePart ↔
      χ.toHeckeCharacter.infinityType.realParity w ≠
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w := by
  simp [conductor]

/-- The `v`-adic exponent of `χ.conductor` is the conductor exponent of `χ.toHeckeCharacter` at
`v`. -/
@[simp]
theorem exponent_conductor (χ : Grossencharacter K 𝔪) (v : HeightOneSpectrum (𝓞 K)) :
    χ.conductor.exponent v = χ.toHeckeCharacter.conductorExponent v := by
  rw [Modulus.exponent_def, finitePart_conductor, HeckeCharacter.count_finiteConductor]

/-- A finite prime lies in the support of `χ.conductor` iff it divides the finite conductor of
`χ.toHeckeCharacter`. -/
theorem mem_support_conductor_iff (χ : Grossencharacter K 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ χ.conductor.support ↔ v.asIdeal ∣ χ.toHeckeCharacter.finiteConductor :=
  Modulus.mem_support_iff _ v

/-- **The presentation conductor divides the modulus of every presentation.** -/
theorem conductor_dvd (χ : Grossencharacter K 𝔪) : χ.conductor ∣ 𝔪 := by
  refine Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, fun w hw ↦ ?_⟩
  by_contra hnot
  exact (χ.mem_conductor_infinitePart_iff w).mp hw (χ.realParity_eq w hnot)

/-- **The presentation conductor depends only on the underlying Hecke character**, not on the
modulus at which it is presented. -/
theorem conductor_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.conductor = ψ.conductor := by
  refine Modulus.ext (by simp [h]) ?_
  ext w
  simp [h, infinityType_congr h]

/-- **Change of modulus**: presenting `χ` at any multiple `𝔫` of `χ.conductor`, with its unitary
weight restricted away from `𝔫.support`. -/
def changeModulus (χ : Grossencharacter K 𝔪) (h : χ.conductor ∣ 𝔫) :
    Grossencharacter K 𝔫 where
  toHeckeCharacter := χ.toHeckeCharacter
  unitaryWeight :=
    χ.toHeckeCharacter.unitaryIdealWeight.restrictAway 𝔫.support 𝔫.support.finite_toSet
  infinityType := χ.infinityType
  eq_one_of_mem _ hy hw :=
    χ.toHeckeCharacter.eq_one_of_finiteConductor_dvd_finitePart hy hw (Modulus.dvd_iff.mp h).1
  agreesOnIdentityComponent := χ.agreesOnIdentityComponent
  realParity_eq w hw := by
    by_contra hne
    exact hw ((Modulus.dvd_iff.mp h).2 ((χ.mem_conductor_infinitePart_iff w).mpr hne))
  unitaryWeight_eq_zero I hI := by
    classical
    rw [UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply,
      ite_eq_right_iff]
    intro hg
    exact (hI (Modulus.isCoprimeTo_iff.mpr (Ideal.isPrimeTo_iff.mp hg))).elim
  unitaryWeight_apply v hv u hu := by
    classical
    have hnot : v ∉ 𝔫.support := (𝔫.mem_support_iff v).not.mpr hv
    have hgood : Ideal.IsPrimeTo v.asIdeal 𝔫.support := Ideal.isPrimeTo_asIdeal_iff.mpr hnot
    have hndvd : ¬ v.asIdeal ∣ χ.toHeckeCharacter.finiteConductor :=
      fun hdvd ↦ hv (hdvd.trans (Modulus.dvd_iff.mp h).1)
    rw [UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply,
      ite_eq_left_iff.mpr fun hbad ↦ (hbad hgood).elim]
    exact χ.toHeckeCharacter.unitaryIdealWeight_apply_prime v hndvd u hu

/-- Changing modulus preserves the underlying Hecke character. -/
@[simp]
theorem toHeckeCharacter_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) :
    (χ.changeModulus h).toHeckeCharacter = χ.toHeckeCharacter :=
  (rfl)

/-- Changing modulus to `𝔫` restricts the primitive unitary ideal weight away from `𝔫.support`. -/
@[simp]
theorem unitaryWeight_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) :
    (χ.changeModulus h).unitaryWeight =
      χ.toHeckeCharacter.unitaryIdealWeight.restrictAway 𝔫.support 𝔫.support.finite_toSet :=
  (rfl)

/-- Changing modulus preserves the algebraic infinity type. -/
@[simp]
theorem infinityType_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) :
    (χ.changeModulus h).infinityType = χ.infinityType :=
  (rfl)

/-- Changing modulus preserves the ideal-side shift. -/
@[simp]
theorem idealShift_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) :
    (χ.changeModulus h).idealShift = χ.idealShift :=
  idealShift_congr (χ.toHeckeCharacter_changeModulus h)

/-- Changing modulus preserves the presentation conductor. -/
@[simp]
theorem conductor_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) :
    (χ.changeModulus h).conductor = χ.conductor :=
  conductor_congr (χ.toHeckeCharacter_changeModulus h)

/-- Changing modulus to the current modulus `𝔪` is the identity. -/
@[simp]
theorem changeModulus_self (χ : Grossencharacter K 𝔪) (h : χ.conductor ∣ 𝔪) :
    χ.changeModulus h = χ :=
  ext rfl

/-- Changing modulus twice in succession agrees with a single change of modulus. -/
theorem changeModulus_changeModulus {𝔨 : Modulus K} (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) (h' : (χ.changeModulus h).conductor ∣ 𝔨) :
    (χ.changeModulus h).changeModulus h' =
      χ.changeModulus ((χ.conductor_changeModulus h) ▸ h') :=
  ext rfl

/-- Construct a presentation carrying the primitive unitary ideal weight `φ.unitaryIdealWeight`
at any modulus whose finite part is `φ.finiteConductor` and whose infinite part clears all real
sign-parity mismatches against `n`. -/
private def mkOfFiniteConductor (φ : HeckeCharacter K) (n : AlgebraicInfinityType K)
    (hn : φ.infinityType.AgreesOnIdentityComponent n.toContinuous) {𝔪 : Modulus K}
    (hfin : 𝔪.finitePart = φ.finiteConductor)
    (hparity : ∀ w : {w : InfinitePlace K // w.IsReal}, w ∉ 𝔪.infinitePart →
      φ.infinityType.realParity w = n.toContinuous.realParity w) :
    Grossencharacter K 𝔪 where
  toHeckeCharacter := φ
  unitaryWeight := φ.unitaryIdealWeight
  infinityType := n
  eq_one_of_mem _ hy hw := φ.eq_one_of_finiteConductor_dvd_finitePart hy hw (by rw [hfin])
  agreesOnIdentityComponent := hn
  realParity_eq := hparity
  unitaryWeight_eq_zero I hI :=
    φ.unitaryIdealWeight_apply_of_not_isPrimeTo fun hg ↦ hI <| by
      obtain ⟨hne, hprime⟩ := Ideal.isPrimeTo_iff.mp hg
      exact Modulus.isCoprimeTo_iff.mpr ⟨hne, fun v hv ↦
        hprime v (hfin ▸ (𝔪.mem_support_iff v).mp hv)⟩
  unitaryWeight_apply v hv u hu :=
    φ.unitaryIdealWeight_apply_prime v (hfin ▸ hv) u hu

/-- **The primitive presentation** of `χ` at `χ.conductor`, carrying the canonical primitive
unitary ideal weight `χ.toHeckeCharacter.unitaryIdealWeight`. -/
def primitive (χ : Grossencharacter K 𝔪) : Grossencharacter K χ.conductor :=
  mkOfFiniteConductor χ.toHeckeCharacter χ.infinityType χ.agreesOnIdentityComponent
    χ.finitePart_conductor fun w hw ↦
      not_not.mp ((χ.mem_conductor_infinitePart_iff w).not.mp hw)

/-- The primitive presentation has the same underlying Hecke character as `χ`. -/
@[simp]
theorem toHeckeCharacter_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.toHeckeCharacter = χ.toHeckeCharacter :=
  (rfl)

/-- The unitary weight of `χ.primitive` is `χ.toHeckeCharacter.unitaryIdealWeight`. -/
@[simp]
theorem unitaryWeight_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.unitaryWeight = χ.toHeckeCharacter.unitaryIdealWeight :=
  (rfl)

/-- The primitive presentation has the same algebraic infinity type as `χ`. -/
@[simp]
theorem infinityType_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.infinityType = χ.infinityType :=
  (rfl)

/-- The primitive presentation has the same ideal-side shift as `χ`. -/
@[simp]
theorem idealShift_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.idealShift = χ.idealShift :=
  idealShift_congr χ.toHeckeCharacter_primitive

/-- The presentation conductor of `χ.primitive` is `χ.conductor`. -/
@[simp]
theorem conductor_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.conductor = χ.conductor :=
  conductor_congr χ.toHeckeCharacter_primitive

/-- Changing modulus to `χ.conductor` recovers `χ.primitive`. -/
@[simp]
theorem changeModulus_conductor (χ : Grossencharacter K 𝔪) :
    χ.changeModulus (Modulus.dvd_refl _) = χ.primitive :=
  ext rfl

/-- Two presentations of the same Hecke character have the same primitive L-function. -/
theorem lFunctionC_primitive_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.primitive.lFunctionC = ψ.primitive.lFunctionC := by
  rw [lFunctionC_def, lFunctionC_def, unitaryWeight_primitive, unitaryWeight_primitive,
    idealShift_primitive, idealShift_primitive, idealShift_congr h, h]

/-- Changing modulus does not alter the primitive L-function. -/
@[simp]
theorem lFunctionC_primitive_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.conductor ∣ 𝔫) :
    (χ.changeModulus h).primitive.lFunctionC = χ.primitive.lFunctionC :=
  lFunctionC_primitive_congr (χ.toHeckeCharacter_changeModulus h)

/-- Passing to `primitive` is idempotent on the presented L-function. -/
@[simp]
theorem lFunctionC_primitive_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.primitive.lFunctionC = χ.primitive.lFunctionC :=
  lFunctionC_primitive_congr χ.toHeckeCharacter_primitive

/-- **Universal property of the presentation conductor**: a modulus `𝔫` admits a presentation of
`χ.toHeckeCharacter` if and only if `χ.conductor ∣ 𝔫`. -/
theorem conductor_dvd_iff (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) :
    χ.conductor ∣ 𝔫 ↔
      ∃ ψ : Grossencharacter K 𝔫, ψ.toHeckeCharacter = χ.toHeckeCharacter :=
  ⟨fun h ↦ ⟨χ.changeModulus h, rfl⟩,
    fun ⟨ψ, hψ⟩ ↦ conductor_congr hψ.symm ▸ ψ.conductor_dvd⟩

/-- **A Hecke character admits a `Grossencharacter` presentation at some modulus if and only if it
is algebraic** (of Weil's type `A₀`). -/
theorem exists_grossencharacter_iff_isAlgebraic {φ : HeckeCharacter K} :
    (∃ (𝔪 : Modulus K) (χ : Grossencharacter K 𝔪), χ.toHeckeCharacter = φ) ↔ φ.IsAlgebraic := by
  refine ⟨fun ⟨_, χ, hχ⟩ ↦ hχ ▸ χ.isAlgebraic, fun hφ ↦ ?_⟩
  obtain ⟨n, hn⟩ := HeckeCharacter.isAlgebraic_iff_exists_agreesOnIdentityComponent.mp hφ
  exact ⟨⟨φ.finiteConductor, φ.finiteConductor_ne_bot, (narrowModulus K).infinitePart⟩,
    mkOfFiniteConductor φ n hn rfl fun w hw ↦ (hw (mem_narrowModulus_infinitePart w)).elim, rfl⟩

/-! ### Imprimitive Euler factors and comparison of L-functions -/

open Classical in
/-- **The Euler factors deleted by passing from `𝔪` to `𝔫`**:
`∏_{𝔭 ∣ 𝔫₀, 𝔭 ∤ 𝔪₀} (1 - χ_u(𝔭) N(𝔭) ^ (idealShift - s))`. Since `χ.unitaryWeight` vanishes on the
primes dividing `𝔪₀`, the product may equivalently be taken over all primes in `𝔫.support`
(`eulerCorrection_eq_prod_support`). -/
def eulerCorrection (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) (s : ℂ) : ℂ :=
  ∏ 𝔭 ∈ 𝔫.support \ 𝔪.support,
    (1 - χ.unitaryWeight.val 𝔭.asIdeal *
      (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ ((χ.idealShift : ℂ) - s))

/-- Since `χ.unitaryWeight` vanishes at every prime dividing `𝔪.finitePart`, the Euler correction
may be taken over the whole support of `𝔫`. -/
theorem eulerCorrection_eq_prod_support (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) (s : ℂ) :
    χ.eulerCorrection 𝔫 s = ∏ 𝔭 ∈ 𝔫.support,
      (1 - χ.unitaryWeight.val 𝔭.asIdeal *
        (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ ((χ.idealShift : ℂ) - s)) := by
  classical
  refine Finset.prod_subset Finset.sdiff_subset fun 𝔭 h𝔫 h𝔭 ↦ ?_
  have h𝔪 : 𝔭 ∈ 𝔪.support := by
    by_contra h
    exact h𝔭 (Finset.mem_sdiff.mpr ⟨h𝔫, h⟩)
  rw [χ.unitaryWeight_apply_of_dvd ((𝔪.mem_support_iff 𝔭).mp h𝔪), zero_mul, sub_zero]

/-- Presenting a Grossencharacter at its own modulus deletes no Euler factor. -/
@[simp]
theorem eulerCorrection_self (χ : Grossencharacter K 𝔪) (s : ℂ) : χ.eulerCorrection 𝔪 s = 1 := by
  classical
  rw [eulerCorrection, Finset.sdiff_self, Finset.prod_empty]

/-- No Euler factor is deleted when every prime dividing `𝔫` already divides `𝔪`. -/
theorem eulerCorrection_of_support_subset (χ : Grossencharacter K 𝔪)
    (h : 𝔫.support ⊆ 𝔪.support) (s : ℂ) : χ.eulerCorrection 𝔫 s = 1 := by
  classical
  rw [eulerCorrection, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.prod_empty]

/-- For a ray class character `η`, the Grossencharacter Euler correction reduces to
`RayClassCharacter.eulerCorrection`. -/
@[simp]
theorem eulerCorrection_ofRayClassCharacter (η : RayClassCharacter 𝔪) (𝔫 : Modulus K) (s : ℂ) :
    (ofRayClassCharacter η).eulerCorrection 𝔫 s = η.eulerCorrection 𝔫 s := by
  rw [eulerCorrection_eq_prod_support, RayClassCharacter.eulerCorrection_eq_prod_support]
  simp

/-- The Euler correction is an entire function of `s`. -/
theorem differentiable_eulerCorrection (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) :
    Differentiable ℂ (χ.eulerCorrection 𝔫) := by
  classical
  refine Differentiable.fun_finsetProd fun 𝔭 _ ↦ (differentiable_const 1).sub
    ((differentiable_const _).mul
      (((differentiable_const _).sub differentiable_id).const_cpow
        (.inl 𝔭.natCast_absNorm_ne_zero)))

/-- Every zero of `χ.eulerCorrection 𝔫` lies on the vertical line `Re s = χ.idealShift`. -/
theorem re_eq_idealShift_of_eulerCorrection_eq_zero (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K)
    {s : ℂ} (hs : χ.eulerCorrection 𝔫 s = 0) : s.re = χ.idealShift := by
  classical
  rw [eulerCorrection_eq_prod_support] at hs
  obtain ⟨P, _, hP⟩ := Finset.prod_eq_zero_iff.mp hs
  have hane : χ.unitaryWeight.val P.asIdeal ≠ 0 := by
    intro ha
    simp [ha] at hP
  have hgood : χ.unitaryWeight.val.IsGood P.asIdeal :=
    (MultiplicativeIdealWeight.apply_ne_zero_iff_isGood _ _).mp hane
  have hnorm : ‖χ.unitaryWeight.val P.asIdeal‖ = 1 := χ.unitaryWeight.norm_eq_one hgood
  have hz : 1 - χ.unitaryWeight.val P.asIdeal *
      ((Ideal.absNorm P.asIdeal : ℝ) : ℂ) ^ (-(s - (χ.idealShift : ℂ))) = 0 := by
    simpa [neg_sub] using hP
  have hre := Complex.re_eq_zero_of_one_sub_mul_ofReal_cpow_neg_eq_zero
    (one_lt_two.trans_le (TauCeti.two_le_absNorm_asIdeal_real P)) hnorm hz
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- The Euler correction does not vanish off the line `Re s = χ.idealShift`. -/
theorem eulerCorrection_ne_zero (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) {s : ℂ}
    (hs : s.re ≠ χ.idealShift) : χ.eulerCorrection 𝔫 s ≠ 0 :=
  fun hz ↦ hs (χ.re_eq_idealShift_of_eulerCorrection_eq_zero 𝔫 hz)

/-- When `𝔪 ∣ 𝔫` and `ψ` presents the same Hecke character at `𝔫` as `χ` at `𝔪`, the unitary
weight of `ψ` is obtained by restricting `χ.unitaryWeight` away from `𝔫.support`. -/
theorem unitaryWeight_eq_restrictAway_of_dvd {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) :
    ψ.unitaryWeight = χ.unitaryWeight.restrictAway 𝔫.support 𝔫.support.finite_toSet := by
  classical
  rw [ψ.unitaryWeight_eq_restrictAway, χ.unitaryWeight_eq_restrictAway, hψ]
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  simp only [UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply,
    Ideal.isPrimeTo_asIdeal_iff, Finset.mem_coe]
  by_cases hv : v ∈ 𝔫.support
  · simp [hv]
  · have hv𝔪 : v ∉ 𝔪.support := fun hm ↦ hv (Modulus.support_mono h hm)
    simp [hv, hv𝔪]

/-- **Passing to a multiple of the modulus deletes Euler factors on `Re s > 1 + χ.idealShift`**
at the level of the defining Dirichlet series. -/
theorem LSeries_eq_of_dvd {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) {s : ℂ}
    (hs : 1 + χ.idealShift < s.re) :
    LSeries (normCoeff K ψ.unitaryWeight.toIdealArithmeticFunction) (s - ψ.idealShift) =
      LSeries (normCoeff K χ.unitaryWeight.toIdealArithmeticFunction) (s - χ.idealShift) *
        χ.eulerCorrection 𝔫 s := by
  have hw : 1 < (s - (χ.idealShift : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hsum := summable_idealTerm_of_unitary_of_one_lt_re χ.unitaryWeight hw
  rw [idealShift_congr hψ, unitaryWeight_eq_restrictAway_of_dvd h hψ]
  simp only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.val_restrictAway] at hsum ⊢
  rw [χ.unitaryWeight.val.LSeries_restrictAway 𝔫.support hsum, eulerCorrection_eq_prod_support]
  congr 1
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_sub]

private theorem lFunctionC_eq_meromorphicContinuation_smul {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) :
    ψ.lFunctionC = meromorphicContinuation (1 + χ.idealShift)
      (χ.eulerCorrection 𝔫 • fun s ↦
        LSeries (normCoeff K χ.unitaryWeight.toIdealArithmeticFunction) (s - χ.idealShift)) := by
  simp only [ψ.lFunctionC_def, idealShift_congr hψ]
  refine meromorphicContinuation_congr fun s hs ↦ ?_
  have hL := LSeries_eq_of_dvd h hψ hs
  rw [idealShift_congr hψ] at hL
  rw [hL, Pi.smul_apply', smul_eq_mul, mul_comm]

/-- **Passing to a larger modulus multiplies `lFunctionC` by the deleted Euler factors as punctured
germs at every point of `ℂ`.** -/
theorem lFunctionC_eventuallyEq_of_dvd {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) (s : ℂ) :
    ψ.lFunctionC =ᶠ[𝓝[≠] s] fun z ↦ χ.lFunctionC z * χ.eulerCorrection 𝔫 z := by
  rw [lFunctionC_eq_meromorphicContinuation_smul h hψ]
  have hne : ∀ z : ℂ, 1 + χ.idealShift < z.re → χ.eulerCorrection 𝔫 z ≠ 0 :=
    fun z hz ↦ χ.eulerCorrection_ne_zero 𝔫 (by linarith)
  filter_upwards [meromorphicContinuation_smul_eventuallyEq
    (fun z ↦ ((χ.differentiable_eulerCorrection 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (χ.differentiable_eulerCorrection 𝔫).analyticAt z)
    hne χ.analyticOnNhd_LSeries_sub_idealShift s] with z hz
  rw [hz, Pi.smul_apply', smul_eq_mul, mul_comm, χ.lFunctionC_def]

/-- **Passing to a larger modulus multiplies `lFunctionC` by the deleted Euler factors on
`Re s > 1 + χ.idealShift`.** -/
theorem lFunctionC_eq_of_dvd {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) {s : ℂ}
    (hs : 1 + χ.idealShift < s.re) :
    ψ.lFunctionC s = χ.lFunctionC s * χ.eulerCorrection 𝔫 s := by
  have hψc : ContinuousAt ψ.lFunctionC s :=
    (ψ.analyticOnNhd_lFunctionC s (by rwa [idealShift_congr hψ])).continuousAt
  have hχc : ContinuousAt (fun z ↦ χ.lFunctionC z * χ.eulerCorrection 𝔫 z) s :=
    (χ.analyticOnNhd_lFunctionC s hs).continuousAt.mul
      (χ.differentiable_eulerCorrection 𝔫).continuous.continuousAt
  exact tendsto_nhds_unique hψc.continuousWithinAt
    (hχc.continuousWithinAt.congr' (lFunctionC_eventuallyEq_of_dvd h hψ s).symm)

/-- **Every presented L-function is the primitive L-function times the deleted Euler factors** on
`Re s > 1 + χ.idealShift`. -/
theorem lFunctionC_eq_primitive (χ : Grossencharacter K 𝔪) {s : ℂ}
    (hs : 1 + χ.idealShift < s.re) :
    χ.lFunctionC s = χ.primitive.lFunctionC s * χ.primitive.eulerCorrection 𝔪 s :=
  lFunctionC_eq_of_dvd χ.conductor_dvd rfl (by rwa [idealShift_primitive])

/-- **Every presented L-function is the primitive L-function times the deleted Euler factors** as
punctured germs at every point of `ℂ`. -/
theorem lFunctionC_eventuallyEq_primitive (χ : Grossencharacter K 𝔪) (s : ℂ) :
    χ.lFunctionC =ᶠ[𝓝[≠] s]
      fun z ↦ χ.primitive.lFunctionC z * χ.primitive.eulerCorrection 𝔪 z :=
  lFunctionC_eventuallyEq_of_dvd χ.conductor_dvd rfl s

/-! ### Finite-order Grossencharacters and ray class characters -/

/-- **For a finite-order Hecke character, the presentation conductor agrees with
`HeckeCharacter.conductor`.** -/
theorem conductor_eq_heckeCharacter_conductor (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.IsFiniteOrder) :
    χ.conductor = χ.toHeckeCharacter.conductor h := by
  refine Modulus.ext (HeckeCharacter.finitePart_conductor h).symm ?_
  ext w
  rw [mem_conductor_infinitePart_iff, χ.infinityType_eq_zero_of_isFiniteOrder h,
    map_zero, ContinuousInfinityType.zero_realParity, Pi.zero_apply]
  exact (HeckeCharacter.realParity_infinityType_eq_zero_iff h w).not.trans not_not

/-- The presentation conductor of `ofRayClassCharacter η` is `η.conductor`. -/
@[simp]
theorem conductor_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).conductor = η.conductor := by
  have heq := toHeckeCharacter_ofRayClassCharacter η
  have hfin : (ofRayClassCharacter η).toHeckeCharacter.IsFiniteOrder :=
    heq.symm ▸ HeckeCharacter.isFiniteOrder_ofRayClassCharacter η
  rw [conductor_eq_heckeCharacter_conductor _ hfin]
  generalize (ofRayClassCharacter η).toHeckeCharacter = φ at heq hfin
  subst heq
  exact HeckeCharacter.conductor_ofRayClassCharacter η hfin

/-- **Every finite-order presentation at `𝔪` comes from a ray class character of `𝔪`.** -/
theorem exists_rayClassCharacter_of_isFiniteOrder (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.IsFiniteOrder) :
    ∃ η : RayClassCharacter 𝔪, ofRayClassCharacter η = χ := by
  have hdvd : χ.toHeckeCharacter.conductor h ∣ 𝔪 :=
    χ.conductor_eq_heckeCharacter_conductor h ▸ χ.conductor_dvd
  obtain ⟨η, hη⟩ := (HeckeCharacter.conductor_dvd_iff h).mp hdvd
  exact ⟨η, ext ((toHeckeCharacter_ofRayClassCharacter η).trans hη)⟩

/-- **A presentation at `𝔪` has finite order if and only if it lies in the range of
`ofRayClassCharacter` at `𝔪`.** -/
theorem isFiniteOrder_iff_mem_range_ofRayClassCharacter (χ : Grossencharacter K 𝔪) :
    χ.toHeckeCharacter.IsFiniteOrder ↔ χ ∈ Set.range (ofRayClassCharacter (𝔪 := 𝔪)) := by
  refine ⟨χ.exists_rayClassCharacter_of_isFiniteOrder, ?_⟩
  rintro ⟨η, rfl⟩
  rw [toHeckeCharacter_ofRayClassCharacter]
  exact HeckeCharacter.isFiniteOrder_ofRayClassCharacter η

/-- The primitive L-function of `ofRayClassCharacter η` is the presented Hecke L-function of
`η.primitiveCharacter`. -/
@[simp]
theorem lFunctionC_primitive_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).primitive.lFunctionC = heckeLFunctionC η.primitiveCharacter := by
  have hη : HeckeCharacter.ofRayClassCharacter 𝔪 η =
      HeckeCharacter.ofRayClassCharacter η.conductor η.primitiveCharacter := by
    conv_lhs => rw [← η.induced_primitiveCharacter]
    exact HeckeCharacter.ofRayClassCharacter_induced η.conductor_dvd η.primitiveCharacter
  rw [lFunctionC_def, heckeLFunctionC_def, idealShift_primitive, idealShift_ofRayClassCharacter,
    unitaryWeight_primitive, toHeckeCharacter_ofRayClassCharacter, hη,
    HeckeCharacter.unitaryIdealWeight_ofRayClassCharacter_of_isPrimitive
      η.isPrimitive_primitiveCharacter]
  simp

/-! ### Integral norm-power presentations and real-parity separation -/

variable (K) in
/-- **The integral norm-power Grossencharacter `N ^ m`** (`m : ℤ`) of a number field `K`,
presented at `narrowModulus K`: the idele class character `HeckeCharacter.normPow K (-m)`, with
unitary weight `1`, constant algebraic infinity type `-m`, and ideal-side shift `m`. -/
def normPow (m : ℤ) : Grossencharacter K (narrowModulus K) where
  toHeckeCharacter := HeckeCharacter.normPow K (-m)
  unitaryWeight := 1
  infinityType := fun _ ↦ -m
  eq_one_of_mem _ hy hw :=
    (HeckeCharacter.normPow K (-m)).eq_one_of_finiteConductor_dvd_finitePart hy hw (by simp)
  agreesOnIdentityComponent := by
    rw [HeckeCharacter.infinityType_normPow, ContinuousInfinityType.agreesOnIdentityComponent_iff]
    refine ⟨funext fun _ ↦ by simp, funext fun _ ↦ ?_, funext fun _ ↦ by simp⟩
    simp only [AlgebraicInfinityType.toContinuous_complexExponent]
    push_cast
    ring
  realParity_eq w hw := (hw (mem_narrowModulus_infinitePart w)).elim
  unitaryWeight_eq_zero I hI := by
    have hbot : I = ⊥ := by
      by_contra hne
      exact hI (Modulus.isCoprimeTo_iff.mpr ⟨hne, fun v hv ↦ by simp at hv⟩)
    simp [hbot]
  unitaryWeight_apply v _ u _ := by
    have hunit : (HeckeCharacter.normPow K (-(m : ℂ))).unitaryPart = 1 := by
      simpa using HeckeCharacter.unitaryPart_normPow_ofReal (K := K) (-m)
    rw [hunit]
    simp [MultiplicativeIdealWeight.one_apply, v.ne_bot]

/-- The underlying Hecke character of `normPow K m` is `HeckeCharacter.normPow K (-m)`. -/
@[simp]
theorem toHeckeCharacter_normPow (m : ℤ) :
    (normPow K m).toHeckeCharacter = HeckeCharacter.normPow K (-m) :=
  (rfl)

/-- The unitary weight of `normPow K m` is `1`. -/
@[simp]
theorem unitaryWeight_normPow (m : ℤ) : (normPow K m).unitaryWeight = 1 :=
  (rfl)

/-- The algebraic infinity type of `normPow K m` is the constant exponent `-m`. -/
@[simp]
theorem infinityType_normPow (m : ℤ) : (normPow K m).infinityType = fun _ ↦ -m :=
  (rfl)

/-- **The ideal-side shift of `normPow K m` is `m`**, opposite to its idelic shift `-m`. -/
@[simp]
theorem idealShift_normPow (m : ℤ) : (normPow K m).idealShift = m := by
  simp [idealShift_def]

/-- **For even `m`, the presentation conductor of `normPow K m` is the trivial modulus.** -/
theorem conductor_normPow_of_even {m : ℤ} (hm : Even m) :
    (normPow K m).conductor = Modulus.one K := by
  refine Modulus.ext (by simp) ?_
  ext w
  simp [HeckeCharacter.infinityType_normPow, AlgebraicInfinityType.toContinuous_realParity,
    hm.neg.intCast_zmod_two]

/-- **For odd `m`, the presentation conductor of `normPow K m` is `narrowModulus K`**: every real
place divides it because `HeckeCharacter.normPow K (-m)` has even real parity while the algebraic
exponent `-m` is odd. -/
theorem conductor_normPow_of_odd {m : ℤ} (hm : Odd m) :
    (normPow K m).conductor = narrowModulus K := by
  refine Modulus.ext (by simp) ?_
  ext w
  simp [HeckeCharacter.infinityType_normPow, AlgebraicInfinityType.toContinuous_realParity,
    hm.neg.intCast_zmod_two]

/-- **Real-parity separation**: over any number field `K` with a real place, an odd norm power
`HeckeCharacter.normPow K (-m)` admits no presentation at `Modulus.one K`, even though it is
unramified at every finite place and trivial on `-1` at every real place. -/
theorem not_exists_grossencharacter_one_normPow_of_odd
    [hK : Nonempty {w : InfinitePlace K // w.IsReal}] {m : ℤ} (hm : Odd m) :
    ¬ ∃ ψ : Grossencharacter K (Modulus.one K),
      ψ.toHeckeCharacter = HeckeCharacter.normPow K (-m) := by
  intro h
  have hdvd : (normPow K m).conductor ∣ Modulus.one K :=
    ((normPow K m).conductor_dvd_iff (Modulus.one K)).mpr h
  rw [conductor_normPow_of_odd hm] at hdvd
  obtain ⟨w⟩ := hK
  have hw := (Modulus.dvd_iff.mp hdvd).2 (mem_narrowModulus_infinitePart w)
  rw [Modulus.one_infinitePart] at hw
  exact Finset.notMem_empty w hw

/-- **The presented L-function of `normPow K m` is the shifted continued Dedekind zeta function
`dedekindZetaC K (s - m)`** at every point of `ℂ`. -/
@[simp]
theorem lFunctionC_normPow (m : ℤ) (s : ℂ) :
    (normPow K m).lFunctionC s = dedekindZetaC K (s - m) := by
  have hfun : (fun z : ℂ ↦ LSeries (normCoeff K
      (normPow K m).unitaryWeight.toIdealArithmeticFunction) (z - (m : ℝ))) =
      fun z : ℂ ↦ NumberField.dedekindZeta K (z - (m : ℝ)) := by
    ext z
    rw [unitaryWeight_normPow, UnitaryIdealWeight.toIdealArithmeticFunction_one,
      ← dedekindZeta_eq_LSeries_normCoeff_one]
  rw [lFunctionC_def, idealShift_normPow, hfun,
    congrFun (meromorphicContinuation_comp_sub_ofReal 1 (NumberField.dedekindZeta K) m) s,
    dedekindZetaC_def, Complex.ofReal_intCast]

/-- Over `ℚ`, the presented L-function of `normPow ℚ m` has the punctured germ of `ζ(s - m)` at
every point of `ℂ`. -/
theorem lFunctionC_normPow_rat_eventuallyEq (m : ℤ) (s : ℂ) :
    (normPow ℚ m).lFunctionC =ᶠ[𝓝[≠] s] fun z ↦ riemannZeta (z - m) := by
  rw [funext (lFunctionC_normPow m)]
  exact (dedekindZetaC_rat_eventuallyEq_riemannZeta (s - m)).comp_tendsto
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_id.sub continuous_const).tendsto s).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hz ↦ sub_left_inj.not.mpr hz))

/-- **Over `ℚ`, the presented L-function of `normPow ℚ m` equals `riemannZeta (s - m)` at every
`s ≠ 1 + m`** (in particular on `1 + m < Re s`). -/
theorem lFunctionC_normPow_rat (m : ℤ) {s : ℂ} (hs : s ≠ 1 + m) :
    (normPow ℚ m).lFunctionC s = riemannZeta (s - m) := by
  rw [lFunctionC_normPow]
  exact dedekindZetaC_rat_eq_riemannZeta fun h ↦ hs (by linear_combination h)

end Grossencharacter

end TauCeti.LFunctions
