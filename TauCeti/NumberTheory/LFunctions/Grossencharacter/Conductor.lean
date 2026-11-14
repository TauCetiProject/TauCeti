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
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.RealParity
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The presentation conductor, primitive reduction, and norm-power Grossencharacters

One algebraic Hecke character of a number field `K` can be presented (`Grossencharacter K 𝔪`) at
every modulus `𝔪` that clears both its finite ramification and the real sign mismatches between its
archimedean restriction and its algebraic infinity type. This file identifies the least such
modulus, constructs the primitive presentation there and the induced presentations at its
multiples, compares their L-functions by the deleted Euler factors, relates finite-order
presentations to ray class characters, and builds the integral norm-power presentations `N ^ m`.

## The presentation conductor

For a presentation `χ : Grossencharacter K 𝔪`, `χ.primitiveConductor` is the modulus whose finite
part is `χ.toHeckeCharacter.finiteConductor` (`∏_v v ^ a_v(χ)`) and whose infinite part consists of
the real places `w` at which the parity `χ.toHeckeCharacter.infinityType.realParity w` of the
archimedean restriction differs from
`(AlgebraicInfinityType.toContinuous χ.infinityType).realParity w`.

At a real place, this is the conductor of the **presentation**, not the ramification conductor of
the idele class character: the odd norm powers `N ^ m = ‖·‖ ^ (-m)` (`Grossencharacter.normPow`)
have archimedean component `x ↦ |x| ^ (-m)` trivial on `±1`, yet every real place divides their
presentation conductor (`Grossencharacter.primitiveConductor_normPow_of_odd`) because their
algebraic exponent `-m` is odd while `realParity_eq` forbids an unrecorded parity mismatch outside
the modulus. For a character of finite order the algebraic infinity type is `0`, the two notions
agree, and `primitiveConductor` equals `HeckeCharacter.conductor`
(`Grossencharacter.primitiveConductor_eq_conductor`).

A modulus `𝔫` presents `χ.toHeckeCharacter` if and only if `χ.primitiveConductor ∣ 𝔫`
(`Grossencharacter.primitiveConductor_dvd_iff`). In particular, `χ.primitive` is the canonical
presentation at `χ.primitiveConductor`, with unitary weight `χ.toHeckeCharacter.unitaryIdealWeight`,
and every algebraic Hecke character admits a presentation at some modulus
(`Grossencharacter.exists_grossencharacter_iff_isAlgebraic`).

## Imprimitive Euler factors

Presenting `χ` at a multiple `𝔫` of `𝔪` restricts its unitary weight away from `𝔫.support`,
multiplying its L-series on `Re s > 1 + χ.idealShift` and the punctured germs of `lFunctionC` at
every point of `ℂ` by the entire product
`Grossencharacter.eulerCorrection χ 𝔫 s = ∏_{𝔭 ∣ 𝔫, 𝔭 ∤ 𝔪} (1 - χ_u(𝔭) N𝔭 ^ (idealShift - s))`,
whose zeros lie on the vertical line `Re s = χ.idealShift`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.primitiveConductor`: the least modulus presenting `χ`.
* `TauCeti.LFunctions.Grossencharacter.changeModulus`: the presentation of `χ` at any multiple of
  `χ.primitiveConductor`.
* `TauCeti.LFunctions.Grossencharacter.primitive`: the canonical presentation at
  `χ.primitiveConductor`.
* `TauCeti.LFunctions.Grossencharacter.eulerCorrection`: the Euler factors deleted when passing to
  a larger modulus.
* `TauCeti.LFunctions.Grossencharacter.normPow`: the presentation at `narrowModulus K` of the
  integral norm power `‖·‖ ^ (-m)` (`m : ℤ`), with ideal-side shift `m` and L-function
  `dedekindZetaC K (s - m)` (`riemannZeta (s - m)` over `ℚ` away from `s = 1 + m`).

## Main results

* `TauCeti.LFunctions.Grossencharacter.primitiveConductor_dvd_iff`: `χ.primitiveConductor ∣ 𝔫` iff
  `χ.toHeckeCharacter` admits a presentation at `𝔫`.
* `TauCeti.LFunctions.Grossencharacter.exists_grossencharacter_iff_isAlgebraic`: a Hecke character
  admits a `Grossencharacter` presentation iff it is algebraic.
* `TauCeti.LFunctions.Grossencharacter.lFunctionC_eq_primitive` and
  `TauCeti.LFunctions.Grossencharacter.lFunctionC_eventuallyEq_primitive`: every presented
  L-function is the primitive L-function times the deleted Euler factors, on
  `Re s > 1 + χ.idealShift` and as punctured germs everywhere.
* `TauCeti.LFunctions.Grossencharacter.primitiveConductor_eq_conductor` and
  `TauCeti.LFunctions.Grossencharacter.isFiniteOrder_iff_mem_range_ofRayClassCharacter`:
  finite-order presentations and ray class characters.
* `TauCeti.LFunctions.Grossencharacter.primitiveConductor_normPow_of_even`,
  `TauCeti.LFunctions.Grossencharacter.primitiveConductor_normPow_of_odd`, and
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

/-! ### Meromorphy and the unitary weight of a presentation -/

/-- The presented L-function is meromorphic on the whole complex plane. -/
theorem meromorphic_lFunctionC (χ : Grossencharacter K 𝔪) : Meromorphic χ.lFunctionC :=
  meromorphicOn_univ.mp χ.meromorphicNFOn_lFunctionC.meromorphicOn

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
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
    have hu' := v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu
    rw [χ.unitaryWeight_apply v hv u hu', UnitaryIdealWeight.val_restrictAway,
      MultiplicativeIdealWeight.restrictAway_apply,
      ite_eq_left_iff.mpr fun h ↦ (h hgood).elim,
      HeckeCharacter.unitaryIdealWeight_apply_prime _ v hndvd u hu']

/-- Two presentations of the same Hecke character, even at different moduli, have the same
algebraic infinity type. -/
theorem infinityType_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) : χ.infinityType = ψ.infinityType :=
  AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff.mp
    (χ.agreesOnIdentityComponent.symm.trans (h ▸ ψ.agreesOnIdentityComponent))

/-- Two presentations of the same Hecke character have the same ideal-side shift. -/
theorem idealShift_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) : χ.idealShift = ψ.idealShift := by
  rw [idealShift_def, idealShift_def, h]

/-! ### The presentation conductor and primitive reduction -/

/-- A Hecke character is trivial on the ideles of `ideleCongruenceSubgroup 𝔫` with trivial
archimedean coordinates whenever `φ.finiteConductor` divides `𝔫.finitePart`. -/
private theorem eq_one_of_finiteConductor_dvd_finitePart {φ : HeckeCharacter K} {𝔫 : Modulus K}
    {y : IdeleGroup (𝓞 K) K} (hy : y ∈ ideleCongruenceSubgroup 𝔫)
    (hw : ∀ w : InfinitePlace K, w.ideleInfiniteCoord y = 1)
    (hfin : φ.finiteConductor ∣ 𝔫.finitePart) :
    φ (y : IdeleClassGroup (𝓞 K) K) = 1 := by
  have hexp (v : HeightOneSpectrum (𝓞 K)) : φ.conductorExponent v ≤ 𝔫.exponent v := by
    rw [← Modulus.pow_dvd_finitePart_iff_le_exponent]
    exact ((φ.pow_dvd_finiteConductor_iff v _).mpr le_rfl).trans hfin
  have hfinite := φ.finitePart_eq_one_of_forall_mem_unitFiltration y fun v ↦
    TauCeti.unitFiltration_antitone (hexp v)
      (ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hy v)
  have hsplit := IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele y
  simp only [hw, map_one, Finset.prod_const_one, one_mul] at hsplit
  rwa [hsplit] at hfinite

open Classical in
/-- **The presentation conductor** of a Grossencharacter `χ`: the modulus whose finite part is
`χ.toHeckeCharacter.finiteConductor` and whose infinite part consists of the real places at which
the parity of `χ.toHeckeCharacter.infinityType` differs from the parity of `χ.infinityType`.

It is the least modulus at which `χ.toHeckeCharacter` admits a presentation
(`primitiveConductor_dvd_iff`). At real places this records sign-parity mismatch against the
algebraic infinity type rather than local ramification on `±1`; for finite-order characters the
algebraic infinity type vanishes and the two agree (`primitiveConductor_eq_conductor`). -/
def primitiveConductor (χ : Grossencharacter K 𝔪) : Modulus K where
  finitePart := χ.toHeckeCharacter.finiteConductor
  finitePart_ne_bot := χ.toHeckeCharacter.finiteConductor_ne_bot
  infinitePart := (narrowModulus K).infinitePart.filter fun w ↦
    χ.toHeckeCharacter.infinityType.realParity w ≠
      (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w

/-- The finite part of `χ.primitiveConductor` is the finite conductor of `χ.toHeckeCharacter`. -/
@[simp]
theorem finitePart_primitiveConductor (χ : Grossencharacter K 𝔪) :
    χ.primitiveConductor.finitePart = χ.toHeckeCharacter.finiteConductor :=
  (rfl)

/-- A real place divides `χ.primitiveConductor` exactly when the archimedean parity of
`χ.toHeckeCharacter` differs from that of `χ.infinityType` there. -/
@[simp]
theorem mem_primitiveConductor_infinitePart_iff (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ χ.primitiveConductor.infinitePart ↔
      χ.toHeckeCharacter.infinityType.realParity w ≠
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w := by
  simp [primitiveConductor]

/-- The `v`-adic exponent of `χ.primitiveConductor` is the conductor exponent of
`χ.toHeckeCharacter` at `v`. -/
@[simp]
theorem exponent_primitiveConductor (χ : Grossencharacter K 𝔪) (v : HeightOneSpectrum (𝓞 K)) :
    χ.primitiveConductor.exponent v = χ.toHeckeCharacter.conductorExponent v := by
  rw [Modulus.exponent_def, finitePart_primitiveConductor, HeckeCharacter.count_finiteConductor]

/-- A finite prime lies in the support of `χ.primitiveConductor` iff it divides the finite
conductor of `χ.toHeckeCharacter`. -/
theorem mem_support_primitiveConductor_iff (χ : Grossencharacter K 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ χ.primitiveConductor.support ↔ v.asIdeal ∣ χ.toHeckeCharacter.finiteConductor :=
  Modulus.mem_support_iff _ v

/-- **The presentation conductor divides the modulus of every presentation.** -/
theorem primitiveConductor_dvd (χ : Grossencharacter K 𝔪) : χ.primitiveConductor ∣ 𝔪 := by
  refine Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, fun w hw ↦ ?_⟩
  by_contra hnot
  exact (χ.mem_primitiveConductor_infinitePart_iff w).mp hw (χ.realParity_eq w hnot)

/-- **The presentation conductor depends only on the underlying Hecke character**, not on the
modulus at which it is presented. -/
theorem primitiveConductor_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.primitiveConductor = ψ.primitiveConductor := by
  refine Modulus.ext (by simp [h]) ?_
  ext w
  simp [h, infinityType_congr h]

/-- **Change of modulus**: presenting `χ` at any multiple `𝔫` of `χ.primitiveConductor`, with its
unitary weight restricted away from `𝔫.support`. -/
def changeModulus (χ : Grossencharacter K 𝔪) (h : χ.primitiveConductor ∣ 𝔫) :
    Grossencharacter K 𝔫 where
  toHeckeCharacter := χ.toHeckeCharacter
  unitaryWeight :=
    χ.toHeckeCharacter.unitaryIdealWeight.restrictAway 𝔫.support 𝔫.support.finite_toSet
  infinityType := χ.infinityType
  eq_one_of_mem _ hy hw :=
    eq_one_of_finiteConductor_dvd_finitePart hy hw (Modulus.dvd_iff.mp h).1
  agreesOnIdentityComponent := χ.agreesOnIdentityComponent
  realParity_eq w hw := by
    by_contra hne
    exact hw ((Modulus.dvd_iff.mp h).2 ((χ.mem_primitiveConductor_infinitePart_iff w).mpr hne))
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
    (h : χ.primitiveConductor ∣ 𝔫) :
    (χ.changeModulus h).toHeckeCharacter = χ.toHeckeCharacter :=
  (rfl)

/-- Changing modulus to `𝔫` restricts the primitive unitary ideal weight away from `𝔫.support`. -/
@[simp]
theorem unitaryWeight_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.primitiveConductor ∣ 𝔫) :
    (χ.changeModulus h).unitaryWeight =
      χ.toHeckeCharacter.unitaryIdealWeight.restrictAway 𝔫.support 𝔫.support.finite_toSet :=
  (rfl)

/-- Changing modulus preserves the algebraic infinity type. -/
@[simp]
theorem infinityType_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.primitiveConductor ∣ 𝔫) :
    (χ.changeModulus h).infinityType = χ.infinityType :=
  (rfl)

/-- Changing modulus preserves the ideal-side shift. -/
@[simp]
theorem idealShift_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.primitiveConductor ∣ 𝔫) :
    (χ.changeModulus h).idealShift = χ.idealShift :=
  idealShift_congr (χ.toHeckeCharacter_changeModulus h)

/-- Changing modulus preserves the presentation conductor. -/
@[simp]
theorem primitiveConductor_changeModulus (χ : Grossencharacter K 𝔪)
    (h : χ.primitiveConductor ∣ 𝔫) :
    (χ.changeModulus h).primitiveConductor = χ.primitiveConductor :=
  primitiveConductor_congr (χ.toHeckeCharacter_changeModulus h)

/-- Changing modulus to the current modulus `𝔪` is the identity. -/
@[simp]
theorem changeModulus_self (χ : Grossencharacter K 𝔪) (h : χ.primitiveConductor ∣ 𝔪) :
    χ.changeModulus h = χ :=
  ext rfl

/-- Changing modulus twice in succession agrees with a single change of modulus. -/
theorem changeModulus_changeModulus {𝔨 : Modulus K} (χ : Grossencharacter K 𝔪)
    (h : χ.primitiveConductor ∣ 𝔫) (h' : (χ.changeModulus h).primitiveConductor ∣ 𝔨) :
    (χ.changeModulus h).changeModulus h' =
      χ.changeModulus ((χ.primitiveConductor_changeModulus h) ▸ h') :=
  ext rfl

/-- **The primitive presentation** of `χ` at `χ.primitiveConductor`, carrying the canonical
primitive unitary ideal weight `χ.toHeckeCharacter.unitaryIdealWeight`. -/
def primitive (χ : Grossencharacter K 𝔪) : Grossencharacter K χ.primitiveConductor where
  toHeckeCharacter := χ.toHeckeCharacter
  unitaryWeight := χ.toHeckeCharacter.unitaryIdealWeight
  infinityType := χ.infinityType
  eq_one_of_mem _ hy hw :=
    eq_one_of_finiteConductor_dvd_finitePart hy hw (by rw [finitePart_primitiveConductor])
  agreesOnIdentityComponent := χ.agreesOnIdentityComponent
  realParity_eq w hw := not_not.mp ((χ.mem_primitiveConductor_infinitePart_iff w).not.mp hw)
  unitaryWeight_eq_zero I hI :=
    χ.toHeckeCharacter.unitaryIdealWeight_apply_of_not_isPrimeTo fun hg ↦ hI <| by
      obtain ⟨hne, hprime⟩ := Ideal.isPrimeTo_iff.mp hg
      exact Modulus.isCoprimeTo_iff.mpr ⟨hne, fun v hv ↦
        hprime v ((χ.mem_support_primitiveConductor_iff v).mp hv)⟩
  unitaryWeight_apply v hv u hu := χ.toHeckeCharacter.unitaryIdealWeight_apply_prime v hv u hu

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

/-- The presentation conductor of `χ.primitive` is `χ.primitiveConductor`. -/
@[simp]
theorem primitiveConductor_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.primitiveConductor = χ.primitiveConductor :=
  primitiveConductor_congr χ.toHeckeCharacter_primitive

/-- Changing modulus to `χ.primitiveConductor` recovers `χ.primitive`. -/
@[simp]
theorem changeModulus_primitiveConductor (χ : Grossencharacter K 𝔪) :
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
    (h : χ.primitiveConductor ∣ 𝔫) :
    (χ.changeModulus h).primitive.lFunctionC = χ.primitive.lFunctionC :=
  lFunctionC_primitive_congr (χ.toHeckeCharacter_changeModulus h)

/-- Passing to `primitive` is idempotent on the presented L-function. -/
@[simp]
theorem lFunctionC_primitive_primitive (χ : Grossencharacter K 𝔪) :
    χ.primitive.primitive.lFunctionC = χ.primitive.lFunctionC :=
  lFunctionC_primitive_congr χ.toHeckeCharacter_primitive

/-- **Universal property of the presentation conductor**: a modulus `𝔫` admits a presentation of
`χ.toHeckeCharacter` if and only if `χ.primitiveConductor ∣ 𝔫`. -/
theorem primitiveConductor_dvd_iff (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) :
    χ.primitiveConductor ∣ 𝔫 ↔
      ∃ ψ : Grossencharacter K 𝔫, ψ.toHeckeCharacter = χ.toHeckeCharacter :=
  ⟨fun h ↦ ⟨χ.changeModulus h, rfl⟩,
    fun ⟨ψ, hψ⟩ ↦ primitiveConductor_congr hψ.symm ▸ ψ.primitiveConductor_dvd⟩

/-- **A Hecke character admits a `Grossencharacter` presentation at some modulus if and only if it
is algebraic** (of Weil's type `A₀`). -/
theorem exists_grossencharacter_iff_isAlgebraic {φ : HeckeCharacter K} :
    (∃ (𝔪 : Modulus K) (χ : Grossencharacter K 𝔪), χ.toHeckeCharacter = φ) ↔ φ.IsAlgebraic := by
  refine ⟨fun ⟨_, χ, hχ⟩ ↦ hχ ▸ χ.isAlgebraic, fun hφ ↦ ?_⟩
  obtain ⟨n, hn⟩ := HeckeCharacter.isAlgebraic_iff_exists_agreesOnIdentityComponent.mp hφ
  refine ⟨⟨φ.finiteConductor, φ.finiteConductor_ne_bot, (narrowModulus K).infinitePart⟩, {
    toHeckeCharacter := φ
    unitaryWeight := φ.unitaryIdealWeight
    infinityType := n
    eq_one_of_mem := fun _ hy hw ↦ eq_one_of_finiteConductor_dvd_finitePart hy hw dvd_rfl
    agreesOnIdentityComponent := hn
    realParity_eq := fun w hw ↦ (hw (mem_narrowModulus_infinitePart w)).elim
    unitaryWeight_eq_zero := fun I hI ↦
      φ.unitaryIdealWeight_apply_of_not_isPrimeTo fun hg ↦ hI <| by
        obtain ⟨hne, hprime⟩ := Ideal.isPrimeTo_iff.mp hg
        exact Modulus.isCoprimeTo_iff.mpr ⟨hne, fun v hv ↦
          hprime v ((Modulus.mem_support_iff _ v).mp hv)⟩
    unitaryWeight_apply := fun v hv u hu ↦ φ.unitaryIdealWeight_apply_prime v hv u hu }, rfl⟩

/-! ### Imprimitive Euler factors and comparison of L-functions -/

open Classical in
/-- **The Euler factors deleted by passing from `𝔪` to `𝔫`**:
`∏_{𝔭 ∣ 𝔫₀, 𝔭 ∤ 𝔪₀} (1 - χ_u(𝔭) N(𝔭) ^ (idealShift - s))`. Since `χ.unitaryWeight` vanishes on the
primes dividing `𝔪₀`, the product may equivalently be taken over all primes in `𝔫.support`
(`eulerCorrection_eq_prod_support`). -/
def eulerCorrection (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) (s : ℂ) : ℂ :=
  ∏ 𝔭 ∈ 𝔫.support \ 𝔪.support,
    (1 - χ.unitaryWeight.1 𝔭.asIdeal *
      (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ ((χ.idealShift : ℂ) - s))

/-- Since `χ.unitaryWeight` vanishes at every prime dividing `𝔪.finitePart`, the Euler correction
may be taken over the whole support of `𝔫`. -/
theorem eulerCorrection_eq_prod_support (χ : Grossencharacter K 𝔪) (𝔫 : Modulus K) (s : ℂ) :
    χ.eulerCorrection 𝔫 s = ∏ 𝔭 ∈ 𝔫.support,
      (1 - χ.unitaryWeight.1 𝔭.asIdeal *
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
  have hane : χ.unitaryWeight.1 P.asIdeal ≠ 0 := by
    intro ha
    simp [ha] at hP
  have hgood : χ.unitaryWeight.1.IsGood P.asIdeal :=
    (MultiplicativeIdealWeight.apply_ne_zero_iff_isGood _ _).mp hane
  have hnorm : ‖χ.unitaryWeight.1 P.asIdeal‖ = 1 := χ.unitaryWeight.norm_eq_one hgood
  have hz : 1 - χ.unitaryWeight.1 P.asIdeal *
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
  rw [χ.unitaryWeight.1.LSeries_restrictAway 𝔫.support hsum, eulerCorrection_eq_prod_support]
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

/-- **Passing to a larger modulus multiplies `lFunctionC` by the deleted Euler factors on
`Re s > 1 + χ.idealShift`.** -/
theorem lFunctionC_eq_of_dvd {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) {s : ℂ}
    (hs : 1 + χ.idealShift < s.re) :
    ψ.lFunctionC s = χ.lFunctionC s * χ.eulerCorrection 𝔫 s := by
  have han : AnalyticOnNhd ℂ
      (fun z ↦ LSeries (normCoeff K χ.unitaryWeight.toIdealArithmeticFunction) (z - χ.idealShift))
      {z | 1 + χ.idealShift < z.re} := by
    refine (analyticOnNhd_LSeries_of_unitary χ.unitaryWeight).comp
      (analyticOnNhd_id.sub analyticOnNhd_const) fun z hz ↦ ?_
    simp only [mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] at hz ⊢
    linarith
  rw [lFunctionC_eq_meromorphicContinuation_smul h hψ, meromorphicContinuation_smul_apply
    (fun z ↦ ((χ.differentiable_eulerCorrection 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (χ.differentiable_eulerCorrection 𝔫).analyticAt z)
    (fun z hz ↦ χ.eulerCorrection_ne_zero 𝔫 (by linarith [show 1 + χ.idealShift < z.re from hz]))
    han hs, smul_eq_mul, mul_comm, χ.lFunctionC_def]

/-- **Passing to a larger modulus multiplies `lFunctionC` by the deleted Euler factors as punctured
germs at every point of `ℂ`.** -/
theorem lFunctionC_eventuallyEq_of_dvd {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : 𝔪 ∣ 𝔫) (hψ : ψ.toHeckeCharacter = χ.toHeckeCharacter) (s : ℂ) :
    ψ.lFunctionC =ᶠ[𝓝[≠] s] fun z ↦ χ.lFunctionC z * χ.eulerCorrection 𝔫 z := by
  have han : AnalyticOnNhd ℂ
      (fun z ↦ LSeries (normCoeff K χ.unitaryWeight.toIdealArithmeticFunction) (z - χ.idealShift))
      {z | 1 + χ.idealShift < z.re} := by
    refine (analyticOnNhd_LSeries_of_unitary χ.unitaryWeight).comp
      (analyticOnNhd_id.sub analyticOnNhd_const) fun z hz ↦ ?_
    simp only [mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] at hz ⊢
    linarith
  rw [lFunctionC_eq_meromorphicContinuation_smul h hψ]
  filter_upwards [meromorphicContinuation_smul_eventuallyEq
    (fun z ↦ ((χ.differentiable_eulerCorrection 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (χ.differentiable_eulerCorrection 𝔫).analyticAt z)
    (fun z hz ↦ χ.eulerCorrection_ne_zero 𝔫 (by linarith [show 1 + χ.idealShift < z.re from hz]))
    han s] with z hz
  rw [hz, Pi.smul_apply', smul_eq_mul, mul_comm, χ.lFunctionC_def]

/-- **Every presented L-function is the primitive L-function times the deleted Euler factors** on
`Re s > 1 + χ.idealShift`. -/
theorem lFunctionC_eq_primitive (χ : Grossencharacter K 𝔪) {s : ℂ}
    (hs : 1 + χ.idealShift < s.re) :
    χ.lFunctionC s = χ.primitive.lFunctionC s * χ.primitive.eulerCorrection 𝔪 s :=
  lFunctionC_eq_of_dvd χ.primitiveConductor_dvd rfl (by rwa [idealShift_primitive])

/-- **Every presented L-function is the primitive L-function times the deleted Euler factors** as
punctured germs at every point of `ℂ`. -/
theorem lFunctionC_eventuallyEq_primitive (χ : Grossencharacter K 𝔪) (s : ℂ) :
    χ.lFunctionC =ᶠ[𝓝[≠] s]
      fun z ↦ χ.primitive.lFunctionC z * χ.primitive.eulerCorrection 𝔪 z :=
  lFunctionC_eventuallyEq_of_dvd χ.primitiveConductor_dvd rfl s

/-! ### Finite-order Grossencharacters and ray class characters -/

/-- A presentation of a finite-order Hecke character has the zero algebraic infinity type. -/
theorem infinityType_eq_zero_of_isFiniteOrder (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.IsFiniteOrder) : χ.infinityType = 0 := by
  obtain ⟨ε, hε⟩ := HeckeCharacter.exists_finiteOrderInfinityType h
  have hagrees : χ.toHeckeCharacter.infinityType.AgreesOnIdentityComponent
      (AlgebraicInfinityType.toContinuous 0) := by
    rw [hε, map_zero,
      ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType]
    exact ⟨ε, (zero_add _).symm⟩
  exact AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff.mp
    (χ.agreesOnIdentityComponent.symm.trans hagrees)

/-- A presentation of a finite-order Hecke character has ideal-side shift `0`. -/
theorem idealShift_eq_zero_of_isFiniteOrder (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.IsFiniteOrder) : χ.idealShift = 0 := by
  rw [idealShift_def, HeckeCharacter.shift_eq_zero_of_isOfFinOrder h, neg_zero]

/-- **For a finite-order Hecke character, the presentation conductor agrees with
`HeckeCharacter.conductor`.** -/
theorem primitiveConductor_eq_conductor (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.IsFiniteOrder) :
    χ.primitiveConductor = χ.toHeckeCharacter.conductor h := by
  refine Modulus.ext (HeckeCharacter.finitePart_conductor h).symm ?_
  ext w
  rw [mem_primitiveConductor_infinitePart_iff, χ.infinityType_eq_zero_of_isFiniteOrder h,
    map_zero, ContinuousInfinityType.zero_realParity, Pi.zero_apply]
  exact (HeckeCharacter.realParity_infinityType_eq_zero_iff h w).not.trans not_not

/-- The presentation conductor of `ofRayClassCharacter η` is `η.conductor`. -/
@[simp]
theorem primitiveConductor_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).primitiveConductor = η.conductor := by
  have heq := toHeckeCharacter_ofRayClassCharacter η
  have hfin : (ofRayClassCharacter η).toHeckeCharacter.IsFiniteOrder :=
    heq.symm ▸ HeckeCharacter.isFiniteOrder_ofRayClassCharacter η
  rw [primitiveConductor_eq_conductor _ hfin]
  generalize (ofRayClassCharacter η).toHeckeCharacter = φ at heq hfin
  subst heq
  exact HeckeCharacter.conductor_ofRayClassCharacter η hfin

/-- **Every finite-order presentation at `𝔪` comes from a ray class character of `𝔪`.** -/
theorem exists_rayClassCharacter_of_isFiniteOrder (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.IsFiniteOrder) :
    ∃ η : RayClassCharacter 𝔪, ofRayClassCharacter η = χ := by
  have hdvd : χ.toHeckeCharacter.conductor h ∣ 𝔪 :=
    χ.primitiveConductor_eq_conductor h ▸ χ.primitiveConductor_dvd
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
  eq_one_of_mem _ hy hw := eq_one_of_finiteConductor_dvd_finitePart hy hw (by simp)
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

/-- Evaluating `(normPow K m).toHeckeCharacter` on the idele class of `y` gives `‖y‖ ^ (-m)`. -/
theorem toHeckeCharacter_normPow_apply (m : ℤ) (y : IdeleGroup (𝓞 K) K) :
    (((normPow K m).toHeckeCharacter (y : IdeleClassGroup (𝓞 K) K) : ℂˣ) : ℂ) =
      (((ideleNorm y : ℝ≥0) : ℝ) : ℂ) ^ (-(m : ℂ)) := by
  simp

/-- The idelic shift of `normPow K m` is `-m`. -/
theorem shift_toHeckeCharacter_normPow (m : ℤ) :
    (normPow K m).toHeckeCharacter.shift = -m := by
  simp

/-- **The ideal-side shift of `normPow K m` is `m`**, opposite to its idelic shift `-m`. -/
@[simp]
theorem idealShift_normPow (m : ℤ) : (normPow K m).idealShift = m := by
  simp [idealShift_def]

/-- `normPow K m` has finite order if and only if `m = 0`. -/
theorem isFiniteOrder_toHeckeCharacter_normPow_iff {m : ℤ} :
    (normPow K m).toHeckeCharacter.IsFiniteOrder ↔ m = 0 := by
  simp [HeckeCharacter.isFiniteOrder_normPow_iff]

/-- **For even `m`, the presentation conductor of `normPow K m` is the trivial modulus.** -/
theorem primitiveConductor_normPow_of_even {m : ℤ} (hm : Even m) :
    (normPow K m).primitiveConductor = Modulus.one K := by
  refine Modulus.ext (by simp) ?_
  ext w
  obtain ⟨k, rfl⟩ := hm
  simp only [mem_primitiveConductor_infinitePart_iff, toHeckeCharacter_normPow,
    infinityType_normPow, HeckeCharacter.infinityType_normPow, Pi.zero_apply,
    AlgebraicInfinityType.toContinuous_realParity, Modulus.one_infinitePart, Finset.notMem_empty,
    iff_false, not_not]
  rw [Int.cast_neg, Int.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul, neg_zero]

/-- **For odd `m`, the presentation conductor of `normPow K m` is `narrowModulus K`**: every real
place divides it because `HeckeCharacter.normPow K (-m)` has even real parity while the algebraic
exponent `-m` is odd. -/
theorem primitiveConductor_normPow_of_odd {m : ℤ} (hm : Odd m) :
    (normPow K m).primitiveConductor = narrowModulus K := by
  refine Modulus.ext (by simp) ?_
  ext w
  obtain ⟨k, rfl⟩ := hm
  simp only [mem_primitiveConductor_infinitePart_iff, toHeckeCharacter_normPow,
    infinityType_normPow, HeckeCharacter.infinityType_normPow, Pi.zero_apply,
    AlgebraicInfinityType.toContinuous_realParity, mem_narrowModulus_infinitePart, iff_true]
  rw [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_two, Int.cast_one,
    show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  decide

/-- **Real-parity separation**: over any number field `K` with a real place, an odd norm power
`HeckeCharacter.normPow K (-m)` admits no presentation at `Modulus.one K`, even though it is
unramified at every finite place and trivial on `-1` at every real place. -/
theorem not_exists_grossencharacter_one_normPow_of_odd
    [hK : Nonempty {w : InfinitePlace K // w.IsReal}] {m : ℤ} (hm : Odd m) :
    ¬ ∃ ψ : Grossencharacter K (Modulus.one K),
      ψ.toHeckeCharacter = HeckeCharacter.normPow K (-m) := by
  intro h
  have hdvd : (normPow K m).primitiveConductor ∣ Modulus.one K :=
    ((normPow K m).primitiveConductor_dvd_iff (Modulus.one K)).mpr h
  rw [primitiveConductor_normPow_of_odd hm] at hdvd
  obtain ⟨w⟩ := hK
  have hw := (Modulus.dvd_iff.mp hdvd).2 (mem_narrowModulus_infinitePart w)
  rw [Modulus.one_infinitePart] at hw
  exact Finset.notMem_empty w hw

/-- Over `ℚ`, an odd norm power `HeckeCharacter.normPow ℚ (-m)` admits no presentation at the
trivial modulus. -/
theorem not_exists_grossencharacter_one_normPow_rat_of_odd {m : ℤ} (hm : Odd m) :
    ¬ ∃ ψ : Grossencharacter ℚ (Modulus.one ℚ),
      ψ.toHeckeCharacter = HeckeCharacter.normPow ℚ (-m) := by
  have : Nonempty {w : InfinitePlace ℚ // w.IsReal} :=
    ⟨⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩⟩
  exact not_exists_grossencharacter_one_normPow_of_odd hm

/-- Canonical meromorphic continuation commutes with real horizontal translation. -/
private theorem meromorphicContinuation_comp_sub_ofReal (f : ℂ → ℂ) (τ : ℝ) :
    meromorphicContinuation (1 + τ) (fun z ↦ f (z - τ)) =
      fun z ↦ meromorphicContinuation 1 f (z - τ) := by
  by_cases h : ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧ EqOn g f {z | 1 < z.re}
  · refine meromorphicContinuation_eq (fun z _ ↦ ?_) fun z hz ↦ ?_
    · exact (meromorphicNFAt_fun_comp_sub_const_iff_meromorphicNFAt (c := (τ : ℂ))).mpr
        (meromorphicNFOn_meromorphicContinuation 1 f (mem_univ (z - τ)))
    · refine meromorphicContinuation_eqOn h ?_
      simp only [mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] at hz ⊢
      linarith
  · have h0 : (fun z : ℂ ↦ meromorphicContinuation 1 f (z - τ)) = 0 := by
      rw [meromorphicContinuation_of_not_exists h]
      rfl
    rw [h0]
    refine meromorphicContinuation_of_not_exists ?_
    rintro ⟨g, hg, hgf⟩
    refine h ⟨fun z ↦ g (z + τ), fun z _ ↦ ?_, fun z hz ↦ ?_⟩
    · exact (meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt (c := (τ : ℂ))).mpr
        (hg (mem_univ (z + τ)))
    · have hz' : 1 + τ < (z + (τ : ℂ)).re := by
        simp only [mem_ofPred_eq] at hz
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      simpa using hgf hz'

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
    congrFun (meromorphicContinuation_comp_sub_ofReal (NumberField.dedekindZeta K) m) s,
    dedekindZetaC_def, Complex.ofReal_intCast]

private theorem analyticOnNhd_riemannZeta_halfPlane :
    AnalyticOnNhd ℂ riemannZeta {s | 1 < s.re} := by
  intro s hs
  refine analyticOn_riemannZeta s fun h ↦ ?_
  rw [mem_ofPred_eq, Set.mem_singleton_iff.mp h, Complex.one_re] at hs
  exact lt_irrefl 1 hs

private theorem eqOn_riemannZeta_dedekindZeta_rat :
    EqOn riemannZeta (NumberField.dedekindZeta ℚ) {s | 1 < s.re} := by
  intro s hs
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  rw [ArithmeticFunction.zeta_apply, ite_eq_right hn, dedekindZetaCoeff_rat, Nat.cast_one]

/-- Over `ℚ`, the presented L-function of `normPow ℚ m` has the punctured germ of `ζ(s - m)` at
every point of `ℂ`. -/
theorem lFunctionC_normPow_rat_eventuallyEq (m : ℤ) (s : ℂ) :
    (normPow ℚ m).lFunctionC =ᶠ[𝓝[≠] s] fun z ↦ riemannZeta (z - m) := by
  rw [funext (lFunctionC_normPow m), dedekindZetaC_def]
  exact (meromorphicContinuation_eventuallyEq meromorphic_riemannZeta
    analyticOnNhd_riemannZeta_halfPlane eqOn_riemannZeta_dedekindZeta_rat (s - m)).comp_tendsto
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_id.sub continuous_const).tendsto s).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hz ↦ sub_left_inj.not.mpr hz))

/-- **Over `ℚ`, the presented L-function of `normPow ℚ m` equals `riemannZeta (s - m)` at every
`s ≠ 1 + m`** (in particular on `1 + m < Re s`). -/
theorem lFunctionC_normPow_rat (m : ℤ) {s : ℂ} (hs : s ≠ 1 + m) :
    (normPow ℚ m).lFunctionC s = riemannZeta (s - m) := by
  rw [lFunctionC_normPow, dedekindZetaC_def]
  refine meromorphicContinuation_apply meromorphic_riemannZeta
    analyticOnNhd_riemannZeta_halfPlane eqOn_riemannZeta_dedekindZeta_rat
    (analyticOn_riemannZeta _ fun h ↦ hs ?_)
  have h1 : s - (m : ℂ) = 1 := Set.mem_singleton_iff.mp h
  linear_combination h1

end Grossencharacter

end TauCeti.LFunctions
