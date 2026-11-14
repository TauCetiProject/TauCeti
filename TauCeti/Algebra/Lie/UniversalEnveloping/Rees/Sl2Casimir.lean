/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.PoissonBracket
import Mathlib.Tactic.NoncommRing

/-!
# The deformed `sl₂` Casimir element in the PBW Rees algebra and its Poisson-central symbol

Let `L` be a Lie algebra over a commutative ring `R`, and let `h, e, f : L` satisfy the `sl₂`
relations `⁅e, f⁆ = h`, `⁅h, e⁆ = (2 : R) • e`, and `⁅h, f⁆ = -((2 : R) • f)`. Inside
`reesAlgebra R L`, the **deformed Casimir element**

`reesSl2Casimir R L h e f = j(h)² + 2 * ħ * j(h) + 4 * j(f) * j(e)`

lifts the classical enveloping-algebra Casimir `ι(h)² + 2 ι(h) + 4 ι(f) ι(e)` into homogeneous
Rees degree `2`. Using `reesDividedCommutator`, we show that `reesSl2Casimir R L h e f` commutes
with `reesGenerator R L e`, `reesGenerator R L f`, and `reesGenerator R L h` over any commutative
ring `R` without characteristic or nontriviality assumptions.

For `L = LieAlgebra.SpecialLinear.sl (Fin 2) R`, the standard triple
`(slFinTwoBasis R 2, slFinTwoBasis R 0, slFinTwoBasis R 1)` spans `sl (Fin 2) R`, so
`reesSl2Casimir` belongs to `Subalgebra.center R (reesAlgebra R (SpecialLinear.sl (Fin 2) R))`.
Under `reesSpecializationZero`, the subleading `2 * ħ * j(h)` term vanishes while `j(f) * j(e)`
specializes to `ι(e) * ι(f)`, yielding the Poisson-central quadratic polynomial

`sl2CasimirSymbol R L h e f = ι(h)² + 4 * ι(e) * ι(f)`

in `lieInvariants R (SpecialLinear.sl (Fin 2) R) (SpecialLinear.sl (Fin 2) R)`. By contrast, when
`(2 : R) ≠ 0`, `{ι(h), ι(e)} = (2 : R) • ι(e) ≠ 0`, so `ι(e)` is not Poisson-central.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.reesSl2Casimir`: `j(h)² + 2 * ħ * j(h) + 4 * j(f) * j(e)` in
  `reesAlgebra R L`.
* `TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol`: `ι(h)² + 4 * ι(e) * ι(f)` in
  `SymmetricAlgebra R L`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.commute_reesSl2Casimir_reesGenerator_e`,
  `commute_reesSl2Casimir_reesGenerator_f`, `commute_reesSl2Casimir_reesGenerator_h`: commutation
  of `reesSl2Casimir` with the Rees generators of any `sl₂` triple.
* `TauCeti.UniversalEnvelopingAlgebra.reesSlFinTwoCasimir_mem_center`: centrality in
  `reesAlgebra R (SpecialLinear.sl (Fin 2) R)`.
* `TauCeti.UniversalEnvelopingAlgebra.reesSpecializationZero_reesSl2Casimir`,
  `TauCeti.UniversalEnvelopingAlgebra.slFinTwoCasimirSymbol_mem_lieInvariants`,
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_slFinTwoCasimirSymbol_left`: zero-fibre
  specialization and Poisson-centrality of `h² + 4ef`.
* `Module.Basis.symmetricGradient_sl2CasimirSymbol` and
  `TauCeti.UniversalEnvelopingAlgebra.reesZeroFiberBracket_slFinTwo_h_e_ne_zero`: explicit gradient
  formula `2ξ(h)h + 4ξ(f)e + 4ξ(e)f` and non-centrality of `ι(e)` when `(2 : R) ≠ 0`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.2 and §23.1
  (the Casimir element of `sl₂` and central invariants).
* J. Dixmier, *Enveloping Algebras*, Graduate Studies in Mathematics 11, AMS (1996), §2.4.
-/

public section

open LieAlgebra

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

section AbstractTriple

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The **deformed `sl₂` Casimir element** `j(h)² + 2 * ħ * j(h) + 4 * j(f) * j(e)` in
`reesAlgebra R L`. -/
noncomputable def reesSl2Casimir (h e f : L) : reesAlgebra R L :=
  reesGenerator R L h ^ 2 + 2 * reesParameter R L * reesGenerator R L h +
    4 * reesGenerator R L f * reesGenerator R L e

/-- The classical quadratic Casimir symbol `ι(h)² + 4 * ι(e) * ι(f)` in `SymmetricAlgebra R L`. -/
noncomputable def sl2CasimirSymbol (h e f : L) : SymmetricAlgebra R L :=
  SymmetricAlgebra.ι R L h ^ 2 + 4 * SymmetricAlgebra.ι R L e * SymmetricAlgebra.ι R L f

@[simp]
theorem evalOne_reesSl2Casimir (h e f : L) :
    coeffSubalgebra.evalOne (pbwFiltration R L) (reesSl2Casimir R L h e f) =
      _root_.UniversalEnvelopingAlgebra.ι R h ^ 2 +
        2 * _root_.UniversalEnvelopingAlgebra.ι R h +
        4 * _root_.UniversalEnvelopingAlgebra.ι R f *
          _root_.UniversalEnvelopingAlgebra.ι R e := by
  simp [reesSl2Casimir, map_ofNat]

@[simp]
theorem reesSpecializationZero_reesSl2Casimir [Module.Free R L] (h e f : L) :
    reesSpecializationZero R L (reesSl2Casimir R L h e f) = sl2CasimirSymbol R L h e f := by
  simp only [reesSl2Casimir, sl2CasimirSymbol, map_add, map_pow, map_mul, map_ofNat,
    reesSpecializationZero_reesGenerator, reesSpecializationZero_reesParameter]
  ring

/-- Negating `h` and swapping `e` and `f` leaves `reesSl2Casimir` unchanged whenever
`⁅e, f⁆ = h`. -/
theorem reesSl2Casimir_neg_swap {R : Type u} {L : Type v} [CommRing R] [LieRing L]
    [LieAlgebra R L] {h e f : L} (hef : ⁅e, f⁆ = h) :
    reesSl2Casimir R L (-h) f e = reesSl2Casimir R L h e f := by
  have hrel : reesGenerator R L e * reesGenerator R L f =
      reesGenerator R L f * reesGenerator R L e +
        reesParameter R L * reesGenerator R L h := by
    have hsub := reesGenerator_mul_sub_mul R L e f
    rw [hef] at hsub
    exact sub_eq_iff_eq_add'.mp hsub
  rw [reesSl2Casimir, reesSl2Casimir, map_neg, mul_assoc 4, hrel]
  noncomm_ring [neg_neg]

/-- `reesSl2Casimir R L h e f` commutes with `reesGenerator R L e` for any elements obeying
`⁅e, f⁆ = h` and `⁅h, e⁆ = (2 : R) • e`. -/
theorem commute_reesSl2Casimir_reesGenerator_e {R : Type u} {L : Type v} [CommRing R]
    [LieRing L] [LieAlgebra R L] {h e f : L}
    (hef : ⁅e, f⁆ = h) (hhe : ⁅h, e⁆ = (2 : R) • e) :
    Commute (reesSl2Casimir R L h e f) (reesGenerator R L e) := by
  have hd : reesDividedCommutator R L (reesSl2Casimir R L h e f) (reesGenerator R L e) = 0 := by
    have hfe : ⁅f, e⁆ = -h := by rw [← hef, lie_skew]
    have h2e : ((2 : R) • reesGenerator R L e : reesAlgebra R L) =
        2 * reesGenerator R L e := by
      rw [Algebra.smul_def, map_ofNat]
    have hcomm_he : reesGenerator R L e * reesGenerator R L h =
        reesGenerator R L h * reesGenerator R L e -
          reesParameter R L * (2 * reesGenerator R L e) := by
      have hsub := reesGenerator_mul_sub_mul R L h e
      rw [hhe, map_smul, h2e] at hsub
      exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp hsub).symm
    have h2 : reesDividedCommutator R L (2 : reesAlgebra R L) (reesGenerator R L e) = 0 :=
      reesDividedCommutator_of_commute R L (Commute.ofNat_left 2 _)
    have h4 : reesDividedCommutator R L (4 : reesAlgebra R L) (reesGenerator R L e) = 0 :=
      reesDividedCommutator_of_commute R L (Commute.ofNat_left 4 _)
    rw [reesSl2Casimir, sq, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply]
    repeat rw [reesDividedCommutator_mul_left]
    simp only [reesDividedCommutator_reesGenerator, reesDividedCommutator_reesParameter_left,
      h2, h4, hhe, hfe, lie_self, map_zero, map_smul, map_neg, h2e, mul_zero, zero_mul,
      add_zero, zero_add]
    rw [mul_assoc 2 (reesGenerator R L e) (reesGenerator R L h), hcomm_he]
    noncomm_ring [neg_neg]
  have hsub := reesParameter_mul_reesDividedCommutator R L (reesSl2Casimir R L h e f)
    (reesGenerator R L e)
  rw [hd, mul_zero] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- `reesSl2Casimir R L h e f` commutes with `reesGenerator R L f` for any elements obeying
`⁅e, f⁆ = h` and `⁅h, f⁆ = -((2 : R) • f)`. -/
theorem commute_reesSl2Casimir_reesGenerator_f {R : Type u} {L : Type v} [CommRing R]
    [LieRing L] [LieAlgebra R L] {h e f : L}
    (hef : ⁅e, f⁆ = h) (hhf : ⁅h, f⁆ = -((2 : R) • f)) :
    Commute (reesSl2Casimir R L h e f) (reesGenerator R L f) := by
  rw [← reesSl2Casimir_neg_swap hef]
  refine commute_reesSl2Casimir_reesGenerator_e
    (by rw [← hef, lie_skew])
    (by rw [neg_lie, hhf, neg_neg])

/-- `reesSl2Casimir R L h e f` commutes with `reesGenerator R L h` for any elements obeying
`⁅e, f⁆ = h`, `⁅h, e⁆ = (2 : R) • e`, and `⁅h, f⁆ = -((2 : R) • f)`. -/
theorem commute_reesSl2Casimir_reesGenerator_h {R : Type u} {L : Type v} [CommRing R]
    [LieRing L] [LieAlgebra R L] {h e f : L}
    (hef : ⁅e, f⁆ = h) (hhe : ⁅h, e⁆ = (2 : R) • e) (hhf : ⁅h, f⁆ = -((2 : R) • f)) :
    Commute (reesSl2Casimir R L h e f) (reesGenerator R L h) := by
  have hce := commute_reesSl2Casimir_reesGenerator_e hef hhe
  have hcf := commute_reesSl2Casimir_reesGenerator_f hef hhf
  have hXh : reesParameter R L * reesGenerator R L h =
      reesGenerator R L e * reesGenerator R L f -
        reesGenerator R L f * reesGenerator R L e := by
    rw [← hef, ← reesGenerator_mul_sub_mul]
  have hcomm_Xh : Commute (reesSl2Casimir R L h e f)
      (reesParameter R L * reesGenerator R L h) := by
    rw [hXh]
    exact (hce.mul_right hcf).sub_right (hcf.mul_right hce)
  have hX := coeffSubalgebra.commute_X (pbwFiltration R L) (one_mem_pbwFiltration R L 1)
  rw [Commute, SemiconjBy]
  apply coeffSubalgebra.X_mul_injective (pbwFiltration R L) (one_mem_pbwFiltration R L 1)
  calc
    reesParameter R L * (reesSl2Casimir R L h e f * reesGenerator R L h)
      = reesSl2Casimir R L h e f * (reesParameter R L * reesGenerator R L h) :=
        (hX _).left_comm _
    _ = (reesParameter R L * reesGenerator R L h) * reesSl2Casimir R L h e f := hcomm_Xh.eq
    _ = reesParameter R L * (reesGenerator R L h * reesSl2Casimir R L h e f) := mul_assoc _ _ _

end AbstractTriple

end TauCeti.UniversalEnvelopingAlgebra

namespace Module.Basis

/-- Gradient of `TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol R L h e f` at
`ξ : Module.Dual R L`: `(2 * ξ h) • h + (4 * ξ f) • e + (4 * ξ e) • f`. -/
theorem symmetricGradient_sl2CasimirSymbol {R L ι : Type*}
    [CommRing R] [LieRing L] [LieAlgebra R L] [Fintype ι]
    (b : Module.Basis ι R L) (h e f : L) (ξ : Module.Dual R L) :
    b.symmetricGradient (TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol R L h e f) ξ =
      (2 * ξ h) • h + (4 * ξ f) • e + (4 * ξ e) • f := by
  rw [TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol, sq, mul_assoc,
    b.symmetricGradient_add, b.symmetricGradient_mul, b.symmetricGradient_mul,
    b.symmetricGradient_mul, b.symmetricGradient_ι, b.symmetricGradient_ι,
    b.symmetricGradient_ι, b.symmetricGradient_ofNat]
  simp only [map_mul, SymmetricAlgebra.lift_ι_apply, map_ofNat, smul_zero, add_zero,
    smul_add, smul_smul]
  rw [← add_smul, ← two_mul]
  abel

end Module.Basis

namespace TauCeti.UniversalEnvelopingAlgebra

/-! ### Specialization to `sl (Fin 2) R` -/

section SlFinTwo

variable (R : Type u) [CommRing R]

/-- The deformed Casimir element of the standard triple `(h, e, f)` of `sl (Fin 2) R`. -/
noncomputable abbrev reesSlFinTwoCasimir :
    reesAlgebra R (SpecialLinear.sl (Fin 2) R) :=
  reesSl2Casimir R (SpecialLinear.sl (Fin 2) R)
    (TauCeti.slFinTwoBasis R 2) (TauCeti.slFinTwoBasis R 0) (TauCeti.slFinTwoBasis R 1)

/-- The quadratic Casimir symbol `h² + 4ef` in `SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`. -/
noncomputable abbrev slFinTwoCasimirSymbol :
    SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R) :=
  sl2CasimirSymbol R (SpecialLinear.sl (Fin 2) R)
    (TauCeti.slFinTwoBasis R 2) (TauCeti.slFinTwoBasis R 0) (TauCeti.slFinTwoBasis R 1)

/-- **Centrality of the deformed `sl₂` Casimir element** in
`reesAlgebra R (SpecialLinear.sl (Fin 2) R)`, over any commutative ring `R`. -/
theorem reesSlFinTwoCasimir_mem_center :
    reesSlFinTwoCasimir R ∈
      Subalgebra.center R (reesAlgebra R (SpecialLinear.sl (Fin 2) R)) := by
  rw [mem_center_reesAlgebra_iff]
  have hce := commute_reesSl2Casimir_reesGenerator_e
    (TauCeti.lie_slFinTwoBasis_zero_one R) (TauCeti.lie_slFinTwoBasis_two_zero R)
  have hcf := commute_reesSl2Casimir_reesGenerator_f
    (TauCeti.lie_slFinTwoBasis_zero_one R) (TauCeti.lie_slFinTwoBasis_two_one R)
  have hch := commute_reesSl2Casimir_reesGenerator_h
    (TauCeti.lie_slFinTwoBasis_zero_one R) (TauCeti.lie_slFinTwoBasis_two_zero R)
    (TauCeti.lie_slFinTwoBasis_two_one R)
  intro x
  rw [TauCeti.eq_smul_single_add_smul_single_add_smul_singleSubSingle x zero_ne_one,
    ← TauCeti.slFinTwoBasis_zero, ← TauCeti.slFinTwoBasis_one, ← TauCeti.slFinTwoBasis_two,
    map_add, map_add, map_smul, map_smul, map_smul]
  exact ((hce.smul_right _).add_right (hcf.smul_right _)).add_right (hch.smul_right _)

/-- **Poisson-centrality of `h² + 4ef`** in `SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`: its
zero-fibre symbol belongs to the Lie invariants. -/
theorem slFinTwoCasimirSymbol_mem_lieInvariants :
    slFinTwoCasimirSymbol R ∈
      TauCeti.SymmetricAlgebra.lieInvariants R
        (SpecialLinear.sl (Fin 2) R) (SpecialLinear.sl (Fin 2) R) := by
  rw [slFinTwoCasimirSymbol, ← reesSpecializationZero_reesSl2Casimir]
  exact reesSpecializationZero_mem_lieInvariants_of_mem_center _ _
    (reesSlFinTwoCasimir_mem_center R)

/-- `slFinTwoCasimirSymbol R` has vanishing zero-fibre Poisson bracket with every element of
`SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`. -/
@[simp]
theorem reesZeroFiberBracket_slFinTwoCasimirSymbol_left
    (q : SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)) :
    reesZeroFiberBracket R (SpecialLinear.sl (Fin 2) R) (slFinTwoCasimirSymbol R) q = 0 :=
  (forall_reesZeroFiberBracket_eq_zero_iff_mem_lieInvariants _ _).mpr
    (slFinTwoCasimirSymbol_mem_lieInvariants R) q

@[simp]
theorem reesZeroFiberBracket_slFinTwoCasimirSymbol_right
    (p : SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)) :
    reesZeroFiberBracket R (SpecialLinear.sl (Fin 2) R) p (slFinTwoCasimirSymbol R) = 0 := by
  rw [reesZeroFiberBracket_swap, reesZeroFiberBracket_slFinTwoCasimirSymbol_left, neg_zero]

/-- When `(2 : R) ≠ 0`, `{ι(h), ι(e)} = (2 : R) • ι(e) ≠ 0` in
`SymmetricAlgebra R (SpecialLinear.sl (Fin 2) R)`, so `ι(e)` is not Poisson-central. -/
theorem reesZeroFiberBracket_slFinTwo_h_e_ne_zero {R : Type u} [CommRing R] (h2 : (2 : R) ≠ 0) :
    reesZeroFiberBracket R (SpecialLinear.sl (Fin 2) R)
      (SymmetricAlgebra.ι R _ (TauCeti.slFinTwoBasis R 2))
      (SymmetricAlgebra.ι R _ (TauCeti.slFinTwoBasis R 0)) ≠ 0 := by
  rw [reesZeroFiberBracket_ι_ι, TauCeti.lie_slFinTwoBasis_two_zero, map_smul]
  intro hzero
  have heval := congrArg (SymmetricAlgebra.lift ((TauCeti.slFinTwoBasis R).coord 0)) hzero
  rw [map_smul, SymmetricAlgebra.lift_ι_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero] at heval
  exact h2 heval

end SlFinTwo

end TauCeti.UniversalEnvelopingAlgebra
