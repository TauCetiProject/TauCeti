/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Cuspidal

/-!
# Linear structure of cuspidal elements and Green's cuspidal functions

Let `k` be a finite field and `K` a field containing `k`. In `TauCeti.HallAlgebra`, cuspidal
elements (`TauCeti.HallAlgebra.IsCuspidal`) are those whose block averages vanish whenever both
blocks have positive size, and Green's cuspidal function `C_η = TauCeti.HallAlgebra.greenCuspidal`
is attached to any `η : K → ℂ`.

This file records the linear closure properties of `IsCuspidal` (bundling the cuspidal subspace
`TauCeti.HallAlgebra.cuspidalSubmodule`) together with the inversion identity
`C_η = -(β_η ∗ μ)` (immediate from `C_η ∗ 𝟙 = -β_η`).

## Main definitions

* `TauCeti.HallAlgebra.cuspidalSubmodule`: the `ℂ`-submodule of cuspidal elements in
  `HallAlgebra k`.

## Main results

* `TauCeti.HallAlgebra.isCuspidal_zero`, `TauCeti.HallAlgebra.IsCuspidal.add`,
  `TauCeti.HallAlgebra.IsCuspidal.smul`, `TauCeti.HallAlgebra.IsCuspidal.neg`,
  `TauCeti.HallAlgebra.IsCuspidal.sub`: linear closure of cuspidal elements.
* `TauCeti.HallAlgebra.greenCuspidal_eq_neg_eigenvalueSum_mul_moebius`:
  `C_η = -(eigenvalueSum K η * moebius)`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* Adapted from `src/Lib/LocalGL/Green/CuspidalFunctions.lean` and
  `src/Lib/LocalGL/Green/TauFunctions.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

namespace TauCeti.HallAlgebra

variable {k : Type*} [Field k]

section CuspidalLinear

variable [Fintype k]

/-- `0` is cuspidal. -/
theorem isCuspidal_zero : (0 : HallAlgebra k).IsCuspidal :=
  isCuspidal_iff.mpr fun a b _ _ ↦ by simp [blockAverage_zero]

/-- The sum of two cuspidal elements is cuspidal. -/
theorem IsCuspidal.add {F H : HallAlgebra k} (hF : F.IsCuspidal) (hH : H.IsCuspidal) :
    (F + H).IsCuspidal :=
  isCuspidal_iff.mpr fun a b ha hb ↦ by
    rw [blockAverage_add, add_apply, hF.blockAverage_eq_zero ha hb,
      hH.blockAverage_eq_zero ha hb, add_zero]

/-- A complex scalar multiple of a cuspidal element is cuspidal. -/
theorem IsCuspidal.smul {F : HallAlgebra k} (hF : F.IsCuspidal) (c : ℂ) :
    (c • F).IsCuspidal :=
  isCuspidal_iff.mpr fun a b ha hb ↦ by
    rw [blockAverage_smul, smul_apply, hF.blockAverage_eq_zero ha hb, mul_zero]

/-- The negation of a cuspidal element is cuspidal. -/
theorem IsCuspidal.neg {F : HallAlgebra k} (hF : F.IsCuspidal) : (-F).IsCuspidal := by
  simpa only [neg_one_smul] using hF.smul (-1)

/-- The difference of two cuspidal elements is cuspidal. -/
theorem IsCuspidal.sub {F H : HallAlgebra k} (hF : F.IsCuspidal) (hH : H.IsCuspidal) :
    (F - H).IsCuspidal := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg

/-- The `ℂ`-submodule of cuspidal elements in `HallAlgebra k`. -/
def cuspidalSubmodule : Submodule ℂ (HallAlgebra k) where
  carrier := {F | F.IsCuspidal}
  zero_mem' := isCuspidal_zero
  add_mem' hF hH := hF.add hH
  smul_mem' c _ hF := hF.smul c

/-- Membership in `cuspidalSubmodule` is `IsCuspidal`. -/
@[simp]
theorem mem_cuspidalSubmodule {F : HallAlgebra k} :
    F ∈ (cuspidalSubmodule : Submodule ℂ (HallAlgebra k)) ↔ F.IsCuspidal :=
  Iff.rfl

end CuspidalLinear

section GreenFormula

variable {K : Type*} [Field K] [Algebra k K] [Finite k]

/-- Green's cuspidal function satisfies `C_η = -(β_η ∗ μ)`, inverting `C_η ∗ 𝟙 = -β_η`. -/
theorem greenCuspidal_eq_neg_eigenvalueSum_mul_moebius (η : K → ℂ) :
    (greenCuspidal K η : HallAlgebra k) = -(eigenvalueSum K η * moebius) := by
  calc (greenCuspidal K η : HallAlgebra k)
      = greenCuspidal K η * 1 := (mul_one _).symm
    _ = greenCuspidal K η * (constOne * moebius) := by rw [constOne_mul_moebius]
    _ = (greenCuspidal K η * constOne) * moebius := (mul_assoc _ _ _).symm
    _ = -(eigenvalueSum K η) * moebius := by rw [greenCuspidal_mul_constOne]
    _ = -(eigenvalueSum K η * moebius) := neg_mul _ _

end GreenFormula

end TauCeti.HallAlgebra
