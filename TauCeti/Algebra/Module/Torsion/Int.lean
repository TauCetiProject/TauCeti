/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Torsion and reduction of abelian groups

For `n ≠ 0`, the `n`-torsion of a torsion-free abelian group `M`, such as `ℤ`, is zero, and the
reduction `M ⧸ nM = QuotSMulTop n M` of a finitely generated abelian group is finite. These are
recorded as instances, so that such groups meet the finiteness hypotheses of constructions that
take both the `n`-torsion and the reduction mod `n` of a `ℤ`-module.

## Main results

* `TauCeti.subsingleton_torsionBy_int`: the `n`-torsion of a torsion-free abelian group is zero for
  `n ≠ 0`.
* `TauCeti.finite_quotSMulTop_int`: `M ⧸ nM` is finite for `n ≠ 0` and `M` finitely generated.
* `TauCeti.subsingleton_quotSMulTop_of_surjective_zsmul`,
  `TauCeti.subsingleton_torsionBy_of_injective_zsmul`: if multiplication by `ℓ` on `V` is
  surjective, respectively injective, then `V ⧸ ℓV`, respectively `V[ℓ]`, is zero.
-/

public section

open Function
open scoped Pointwise

namespace TauCeti

variable (n : ℕ) [NeZero n] (M : Type*) [AddCommGroup M]

/-- A torsion-free abelian group, such as `ℤ`, has no nonzero `n`-torsion for `n ≠ 0`. -/
instance subsingleton_torsionBy_int [IsAddTorsionFree M] :
    Subsingleton (Submodule.torsionBy ℤ M (n : ℤ)) := by
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  have hx := (Submodule.mem_torsionBy_iff _ _).mp x.property
  have hy := (Submodule.mem_torsionBy_iff _ _).mp y.property
  simp only [smul_eq_zero, Int.natCast_eq_zero, NeZero.ne n, false_or] at hx hy
  rw [hx, hy]

/-- The reduction `M ⧸ nM` of a finitely generated abelian group, such as `ℤ ⧸ nℤ`, is finite for
`n ≠ 0`. -/
instance finite_quotSMulTop_int [Module.Finite ℤ M] : Finite (QuotSMulTop (n : ℤ) M) :=
  Module.finite_of_fg_torsion _ fun x ↦
    ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr (NeZero.ne n))⟩,
      Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M (n : ℤ)) x⟩

/-- If multiplication by `ℓ` is surjective on `V`, the reduction `V ⧸ ℓV` is zero. -/
theorem subsingleton_quotSMulTop_of_surjective_zsmul {V : Type*} [AddCommGroup V] (ℓ : ℕ)
    (hV : Surjective fun x : V => (ℓ : ℤ) • x) : Subsingleton (QuotSMulTop (ℓ : ℤ) V) :=
  Submodule.Quotient.subsingleton_iff.mpr <| top_unique fun x _ ↦
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨_, trivial, (hV x).choose_spec⟩

/-- If multiplication by `ℓ` is injective on `V`, the `ℓ`-torsion `V[ℓ]` is zero. -/
theorem subsingleton_torsionBy_of_injective_zsmul {V : Type*} [AddCommGroup V] (ℓ : ℕ)
    (hV : Injective fun x : V => (ℓ : ℤ) • x) :
    Subsingleton (Submodule.torsionBy ℤ V (ℓ : ℤ)) :=
  ⟨fun x y => Subtype.ext <| hV <|
    ((Submodule.mem_torsionBy_iff _ _).mp x.property).trans
      ((Submodule.mem_torsionBy_iff _ _).mp y.property).symm⟩

end TauCeti
