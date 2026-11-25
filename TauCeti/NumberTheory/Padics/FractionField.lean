/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Ring homomorphisms out of `ℤ_[p]` and its fraction field `ℚ_[p]`

`ℚ_[p]` is the fraction field of `ℤ_[p]`, and every nonzero `p`-adic integer is a unit times a
power of `p`. Hence a ring homomorphism `f : ℤ_[p] →+* A` to a commutative ring sends every
nonzero element to a unit as soon as `p` is a unit of `A`
(`PadicInt.isUnit_map_of_ne_zero`), and `IsLocalization.lift` then extends `f` uniquely to
`ℚ_[p]`. The ring `ℤ_[p]` is an open subring of `ℚ_[p]`, so an additive map out of `ℚ_[p]` is
continuous exactly when its restriction to `ℤ_[p]` is (`Padic.continuous_iff_continuous_comp_coe`);
in particular the extension of a continuous `f` is continuous (for instance when the target is
`J`-adic with `p ∈ J`, by `PadicInt.continuous_of_isAdic` in
`TauCeti.RingTheory.Huber.Padic.Basic`). Finally `ℤ` is dense in `ℤ_[p]` and `ℚ` is dense in
`ℚ_[p]`, so a Hausdorff ring receives at most one continuous ring homomorphism from each of them
(`PadicInt.ringHom_ext_of_continuous`, `Padic.ringHom_ext_of_continuous`).

Together these give a topological ring in which `p` is a unit, and which receives a continuous
ring homomorphism from `ℤ_p`, a `ℚ_p`-structure that is continuous and is the only continuous one.
The interval rings `B^I` of the period domain of the Fargues–Fontaine curve are of this kind.

## Main results

* `PadicInt.isUnit_map_of_ne_zero`: a ring homomorphism out of `ℤ_[p]` inverting `p` inverts
  every nonzero element.
* `Padic.continuous_iff_continuous_comp_coe`: an additive map out of `ℚ_[p]` is continuous exactly
  when its restriction to `ℤ_[p]` is.
* `PadicInt.ringHom_ext_of_continuous`, `Padic.ringHom_ext_of_continuous`: continuous ring
  homomorphisms out of `ℤ_[p]`, respectively `ℚ_[p]`, into a Hausdorff ring are equal.
-/

public section

variable {p : ℕ} [Fact p.Prime] {A : Type*}

namespace PadicInt

/-- A ring homomorphism out of `ℤ_[p]` for which `p` becomes a unit sends every nonzero `p`-adic
integer to a unit, since it is a unit times a power of `p`. -/
theorem isUnit_map_of_ne_zero [Semiring A] (f : ℤ_[p] →+* A) (hp : IsUnit (p : A)) {x : ℤ_[p]}
    (hx : x ≠ 0) : IsUnit (f x) := by
  rw [unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact ((unitCoeff hx).isUnit.map f).mul (hp.pow _)

/-- **Continuous ring homomorphisms out of `ℤ_[p]` are unique**: they agree on the dense subring
`ℤ`, so two continuous ring homomorphisms into a Hausdorff ring are equal. -/
theorem ringHom_ext_of_continuous [NonAssocSemiring A] [TopologicalSpace A] [T2Space A]
    {f g : ℤ_[p] →+* A} (hf : Continuous f) (hg : Continuous g) : f = g :=
  RingHom.ext <| congrFun <| denseRange_intCast.equalizer hf hg <|
    congrArg DFunLike.coe
      (RingHom.ext_int (f.comp (Int.castRingHom ℤ_[p])) (g.comp (Int.castRingHom _)))

end PadicInt

namespace Padic

/-- **An additive map out of `ℚ_[p]` is continuous exactly when its restriction to `ℤ_[p]` is**,
because `ℤ_[p]` is an open neighbourhood of `0` in `ℚ_[p]`. -/
theorem continuous_iff_continuous_comp_coe [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] {F : Type*} [FunLike F ℚ_[p] A] [AddMonoidHomClass F ℚ_[p] A]
    (g : F) : Continuous g ↔ Continuous (g ∘ ((↑) : ℤ_[p] → ℚ_[p])) := by
  refine ⟨fun h ↦ h.comp PadicInt.isOpenEmbedding_coe.continuous,
    fun h ↦ continuous_of_continuousAt_zero g ?_⟩
  simpa using PadicInt.isOpenEmbedding_coe.continuousAt_iff.mp (h.continuousAt (x := 0))

/-- **Continuous ring homomorphisms out of `ℚ_[p]` are unique**: they agree on the dense subfield
`ℚ`, so two continuous ring homomorphisms into a Hausdorff ring are equal. -/
theorem ringHom_ext_of_continuous [Semiring A] [TopologicalSpace A] [T2Space A]
    {f g : ℚ_[p] →+* A} (hf : Continuous f) (hg : Continuous g) : f = g :=
  RingHom.ext <| congrFun <| (denseRange_ratCast p).equalizer hf hg <|
    congrArg DFunLike.coe (RingHom.ext_rat (f.comp (Rat.castHom ℚ_[p])) (g.comp (Rat.castHom _)))

end Padic
