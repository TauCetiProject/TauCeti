/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Henselian
public import TauCeti.Topology.Algebra.Valued.ResidueField
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.RingTheory.Henselian.Integral
import TauCeti.Topology.Algebra.Valued.Integer

/-!
# The residue field of the algebraic closure of `ℚ_p`

Let `O = 𝒪[PadicAlgCl p] = {x | ‖x‖ ≤ 1}` be the valuation ring of the algebraic closure
`PadicAlgCl p` of `ℚ_p` for its spectral norm, and `κ = 𝓀[PadicAlgCl p]` its residue field. This
file proves that `κ` is an algebraic closure of `𝔽_p = ZMod p`, hence non-canonically isomorphic to
`AlgebraicClosure (ZMod p)` through Mathlib's `IsAlgClosure.equiv`.

* `κ` is algebraically closed, as is the residue field of every algebraically closed valued
  field (`Valued.instIsAlgClosedResidueField`).
* `κ` is algebraic over `𝔽_p`: an element `x` of `O` has minimal polynomial over `ℚ_p` with
  coefficients of norm at most `1` (its spectral value is `‖x‖ ≤ 1`), so in `ℤ_p`, and the
  reduction of that polynomial to `𝔽_p` is a monic polynomial killing the residue of `x`.

## Main definitions

* `PadicAlgCl.instAlgebraZModResidueField`: the `𝔽_p`-algebra structure on `𝓀[PadicAlgCl p]`,
  which has characteristic `p`.

## Main results

* `TauCeti.PadicAlgCl.norm_coeff_minpoly_le_one`: an element of norm at most `1` has minimal
  polynomial over `ℚ_p` with coefficients of norm at most `1`.
* `TauCeti.PadicAlgCl.isIntegral_padicIntToInteger`: `𝒪[PadicAlgCl p]` is integral over `ℤ_p`.
* `PadicAlgCl.instHenselianLocalRingInteger`: `𝒪[PadicAlgCl p]` is a henselian local ring, being
  integral over the henselian ring `ℤ_p`.
* `PadicAlgCl.instIsAlgebraicZModResidueField`: `𝓀[PadicAlgCl p]` is algebraic over `ZMod p`.
* `PadicAlgCl.instIsAlgClosureZModResidueField`: `𝓀[PadicAlgCl p]` is an algebraic closure of
  `ZMod p`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section

open Polynomial Valued IsLocalRing

namespace TauCeti.PadicAlgCl

variable {p : ℕ} [Fact p.Prime]

/-- An element of `PadicAlgCl p` of norm at most `1` has minimal polynomial over `ℚ_p` with all
coefficients of norm at most `1`: the spectral norm is the spectral value of the minimal
polynomial. -/
theorem norm_coeff_minpoly_le_one {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 :=
  (spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))).1 hx n

/-- The integers `ℤ_p` sit inside the valuation ring of `PadicAlgCl p`. -/
noncomputable def padicIntToInteger (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* 𝒪[PadicAlgCl p] :=
  (TauCeti.padicIntAlgebraMap p (PadicAlgCl p)).codRestrict _
    fun x ↦ Valued.integer.mem_iff.2 (TauCeti.norm_padicIntAlgebraMap_le_one norm_one.le x)

/-- `TauCeti.PadicAlgCl.padicIntToInteger` is the inclusion `ℤ_p ⊆ ℚ_p ⊆ PadicAlgCl p`. -/
@[simp]
theorem coe_padicIntToInteger (x : ℤ_[p]) :
    (padicIntToInteger p x : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) x :=
  TauCeti.padicIntAlgebraMap_apply x

/-- The prime `p` lies in the maximal ideal of `𝒪[PadicAlgCl p]`. -/
theorem residue_natCast_p : residue 𝒪[PadicAlgCl p] (p : 𝒪[PadicAlgCl p]) = 0 :=
  Valued.integer.residue_eq_zero_iff_norm_lt_one.2 (by
    rw [Subring.coe_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
      PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one)

/-- The residue field of `PadicAlgCl p` has characteristic `p`. -/
instance _root_.PadicAlgCl.instCharPResidueField : CharP 𝓀[PadicAlgCl p] p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    simpa using residue_natCast_p (p := p))

/-- The residue field of `PadicAlgCl p` is an algebra over `𝔽_p = ZMod p`. -/
noncomputable instance _root_.PadicAlgCl.instAlgebraZModResidueField :
    Algebra (ZMod p) 𝓀[PadicAlgCl p] :=
  ZMod.algebra _ p

/-- Reduction from `ℤ_p` to the residue field of `PadicAlgCl p` factors through `ZMod p`. -/
@[simp]
theorem residue_padicIntToInteger (x : ℤ_[p]) :
    residue 𝒪[PadicAlgCl p] (padicIntToInteger p x) =
      algebraMap (ZMod p) 𝓀[PadicAlgCl p] (PadicInt.toZMod x) := by
  obtain ⟨y, hy⟩ : ∃ y, x - (ZMod.cast (PadicInt.toZMod x) : ℤ_[p]) = p * y := by
    have := PadicInt.toZMod_spec x
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  set z := PadicInt.toZMod x
  rw [sub_eq_iff_eq_add, ZMod.cast_eq_val] at hy
  conv_rhs => rw [← ZMod.natCast_zmod_val z, map_natCast]
  simp only [hy, map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, zero_add]

/-- The valuation ring `𝒪[PadicAlgCl p]` is integral over `ℤ_p`: the minimal polynomial over `ℚ_p`
of an element of norm at most `1` has coefficients in `ℤ_p`. -/
theorem isIntegral_padicIntToInteger : (padicIntToInteger p).IsIntegral := by
  intro x
  have hlifts : minpoly ℚ_[p] (x : PadicAlgCl p) ∈ lifts (PadicInt.Coe.ringHom (p := p)) :=
    lifts_iff_coeff_lifts _ |>.2 fun n ↦
      ⟨⟨_, norm_coeff_minpoly_le_one (Valued.integer.norm_le_one x) n⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hlifts
    (minpoly.monic (Algebra.IsIntegral.isIntegral _))
  have hcomp : (𝒪[PadicAlgCl p]).subtype.comp (padicIntToInteger p) =
      (algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom :=
    RingHom.ext coe_padicIntToInteger
  refine ⟨Q, hQm, Subring.subtype_injective _ ?_⟩
  rw [map_zero, hom_eval₂, hcomp, ← eval₂_map, hQ]
  exact minpoly.aeval ℚ_[p] _

/-- The valuation ring `𝒪[PadicAlgCl p]` is a henselian local ring: it is integral over the
henselian local ring `ℤ_p` (`TauCeti.PadicAlgCl.isIntegral_padicIntToInteger`). -/
instance _root_.PadicAlgCl.instHenselianLocalRingInteger : HenselianLocalRing 𝒪[PadicAlgCl p] :=
  letI := (padicIntToInteger p).toAlgebra
  haveI : Algebra.IsIntegral ℤ_[p] 𝒪[PadicAlgCl p] := ⟨isIntegral_padicIntToInteger⟩
  HenselianLocalRing.of_isIntegral ℤ_[p] 𝒪[PadicAlgCl p]

/-- **The residue field of `PadicAlgCl p` is algebraic over `𝔽_p`.** -/
instance _root_.PadicAlgCl.instIsAlgebraicZModResidueField :
    Algebra.IsAlgebraic (ZMod p) 𝓀[PadicAlgCl p] := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨Q, hQm, hQx⟩ := isIntegral_padicIntToInteger x
  have hcomp : (algebraMap (ZMod p) 𝓀[PadicAlgCl p]).comp PadicInt.toZMod =
      (residue 𝒪[PadicAlgCl p]).comp (padicIntToInteger p) :=
    RingHom.ext fun z ↦ (residue_padicIntToInteger z).symm
  refine ⟨Q.map PadicInt.toZMod, (hQm.map _).ne_zero, ?_⟩
  rw [aeval_def, eval₂_map, hcomp, ← hom_eval₂, hQx, map_zero]

/-- **The residue field of `PadicAlgCl p` is an algebraic closure of `𝔽_p`.** -/
instance _root_.PadicAlgCl.instIsAlgClosureZModResidueField :
    IsAlgClosure (ZMod p) 𝓀[PadicAlgCl p] :=
  ⟨inferInstance, inferInstance⟩

end TauCeti.PadicAlgCl
