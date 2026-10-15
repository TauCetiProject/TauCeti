/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Finite
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Lattice
import TauCeti.NumberTheory.Padics.FreeModuleReduction

/-!
# The lattice defect of a `p`-adic permutation lattice

Let `G` be a group acting on a finite set `X`, and `k` a commutative ring of characteristic `p`.
The `p`-adic permutation lattice `ℤ_p[X] = X →₀ ℤ_[p]`, on which `G` acts by pushing the support
forward, has the lattice defect of the integral permutation lattice `ℤ[X]`, that is the
permutation class `[k[X]]` (`TauCeti.latticeDefect_finsupp_padicInt`).

The inclusion `ℤ[X] ⊆ ℤ_p[X]` is not of finite index, but its cokernel `(ℤ_p / ℤ)[X]` is uniquely
`p`-divisible: every `p`-adic integer is congruent to an integer modulo `p`, and a `p`-adic integer
whose `p`-fold is an integer is itself an integer
(`TauCeti.PadicInt.exists_finsupp_eq_mapRange_intCast_add`,
`TauCeti.PadicInt.mem_range_finsupp_mapRange_intCast_of_smul_mem`). So the defect does not change
(`TauCeti.latticeDefect_eq_of_bijective_zsmul_quotient`), and the defect of `ℤ[X]` is computed by
`TauCeti.latticeDefect_finsupp_int`.

Finite free `ℤ_p[G]`-modules arise as Galois-stable lattices in `p`-adic fields, through normal
bases; this is how their defects are computed.

## Main results

* `TauCeti.latticeDefect_finsupp_padicInt`: the defect of `ℤ_p[X]` is `[k[X]]`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 2.12.
-/

public section

open Function
open scoped Pointwise

namespace TauCeti

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction

variable (p : ℕ) [Fact p.Prime]

variable {X : Type}

/-- The inclusion `ℤ[X] → ℤ_p[X]` of finitely supported functions. -/
private noncomputable abbrev finsuppIntCast : (X →₀ ℤ) →+ (X →₀ ℤ_[p]) :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℤ_[p])

variable [Finite X]

/-- The reduction `ℤ_p[X] ⧸ p` of the `p`-adic permutation lattice is finite: it is the image of
`ℤ[X] ⧸ p`. -/
instance finite_quotSMulTop_finsupp_padicInt : Finite (QuotSMulTop (p : ℤ) (X →₀ ℤ_[p])) :=
  Finite.of_surjective (QuotSMulTop.map (p : ℤ) (finsuppIntCast p (X := X)).toIntLinearMap)
    fun v ↦ Submodule.Quotient.induction_on _ v fun v ↦ by
      obtain ⟨w, y, rfl⟩ := PadicInt.exists_finsupp_eq_mapRange_intCast_add v
      refine ⟨Submodule.Quotient.mk w, (Submodule.Quotient.eq _).mpr ?_⟩
      -- `QuotSMulTop.map` is `Submodule.mapQ`, which sends the class of `w` to that of its image
      change finsuppIntCast p w - (finsuppIntCast p w + (p : ℤ) • y) ∈ _
      rw [sub_add_cancel_left]
      exact neg_mem (Submodule.smul_mem_pointwise_smul _ _ _ trivial)

variable (k G : Type) [CommRing k] [CharP k p] [Group G] [MulAction G X]

/-- **The lattice defect of a `p`-adic permutation lattice** `ℤ_p[X] = X →₀ ℤ_[p]`, on which `G`
acts by pushing the support forward, is the permutation class `[k[X]]` in characteristic `p`: the
inclusion `ℤ[X] ⊆ ℤ_p[X]` has a uniquely `p`-divisible cokernel, so `ℤ_p[X]` has the defect of
`ℤ[X]`. -/
theorem latticeDefect_finsupp_padicInt : latticeDefect k G p (X →₀ ℤ_[p]) = permK0 k G X := by
  rw [← latticeDefect_finsupp_int k G p X]
  let f : (X →₀ ℤ) →+[G] (X →₀ ℤ_[p]) :=
    { finsuppIntCast p with map_smul' g f := by ext x; simp [Finsupp.comapSMul_apply] }
  refine (latticeDefect_eq_of_bijective_zsmul_quotient k G p f (fun a b h ↦ Finsupp.ext fun x ↦
    Int.cast_injective (DFunLike.congr_fun h x)) ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩).symm
  · induction x using QuotientAddGroup.induction_on with | H a => ?_
    induction y using QuotientAddGroup.induction_on with | H b => ?_
    dsimp only at hxy
    rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq] at hxy
    rw [QuotientAddGroup.eq]
    refine PadicInt.mem_range_finsupp_mapRange_intCast_of_smul_mem ?_
    rwa [smul_add, smul_neg]
  · induction x using QuotientAddGroup.induction_on with | H v => ?_
    obtain ⟨w, y, rfl⟩ := PadicInt.exists_finsupp_eq_mapRange_intCast_add v
    refine ⟨y, ?_⟩
    dsimp only
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq]
    refine ⟨w, ?_⟩
    -- `f` is `finsuppIntCast p` with its equivariance recorded
    change finsuppIntCast p w = -((p : ℤ) • y) + (finsuppIntCast p w + (p : ℤ) • y)
    abel

end TauCeti
