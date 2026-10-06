/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Finite
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Lattice

/-!
# The lattice defect of a `p`-adic permutation lattice

Let `G` be a group acting on a finite set `X`, and `k` a commutative ring of characteristic `p`.
The `p`-adic permutation lattice `ℤ_p[X] = X →₀ ℤ_[p]`, on which `G` acts by pushing the support
forward, has the lattice defect of the integral permutation lattice `ℤ[X]`, that is the
permutation class `[k[X]]` (`TauCeti.latticeDefect_finsupp_padicInt`).

The inclusion `ℤ[X] ⊆ ℤ_p[X]` is not of finite index, but its cokernel `(ℤ_p / ℤ)[X]` is uniquely
`p`-divisible: every `p`-adic integer is congruent to an integer modulo `p`, and a `p`-adic integer
whose `p`-fold is an integer is itself an integer. So the defect does not change
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

/-- Every element of `ℤ_p[X]` is in `ℤ[X]` modulo `p`. -/
private theorem exists_eq_finsuppIntCast_add (v : X →₀ ℤ_[p]) :
    ∃ w : X →₀ ℤ, ∃ y, v = finsuppIntCast p w + (p : ℤ) • y := by
  have h (a : ℤ_[p]) : ∃ n : ℤ, ∃ z, a = n + p * z := by
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range a
    rw [PadicInt.maximalIdeal_eq_span_p (p := p)] at hn
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hn
    exact ⟨n, z, by push_cast; linear_combination -hz⟩
  choose n z hz using fun x ↦ h (v x)
  refine ⟨Finsupp.equivFunOnFinite.symm n, Finsupp.equivFunOnFinite.symm z, Finsupp.ext fun x ↦ ?_⟩
  simp [hz x]

/-- An element of `ℤ_p[X]` whose `p`-fold is in `ℤ[X]` is itself in `ℤ[X]`. -/
private theorem mem_range_finsuppIntCast (v : X →₀ ℤ_[p])
    (h : (p : ℤ) • v ∈ (finsuppIntCast p).range) : v ∈ (finsuppIntCast p).range := by
  obtain ⟨w, hw⟩ := h
  -- coordinatewise: `p a = n ∈ ℤ` forces `p ∣ n`, as `‖n‖ < 1`, and then `a = n / p ∈ ℤ`
  have hcoord (x : X) : ∃ m : ℤ, v x = m := by
    have hx : (p : ℤ_[p]) * v x = w x := by
      have := DFunLike.congr_fun hw x
      simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
        Int.coe_castAddHom] at this
      rw [this, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast]
    obtain ⟨m, hm⟩ := (PadicInt.norm_int_lt_one_iff_dvd (w x)).mp <|
      (PadicInt.norm_lt_one_iff_dvd _).mpr ⟨v x, hx.symm⟩
    refine ⟨m, mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) ?_⟩
    rw [hx, hm]
    push_cast
    ring
  choose m hm using hcoord
  exact ⟨Finsupp.equivFunOnFinite.symm m, Finsupp.ext fun x ↦ (hm x).symm⟩

/-- The reduction `ℤ_p[X] ⧸ p` of the `p`-adic permutation lattice is finite: it is the image of
`ℤ[X] ⧸ p`. -/
instance finite_quotSMulTop_finsupp_padicInt : Finite (QuotSMulTop (p : ℤ) (X →₀ ℤ_[p])) :=
  Finite.of_surjective (QuotSMulTop.map (p : ℤ) (finsuppIntCast p (X := X)).toIntLinearMap)
    fun v ↦ Submodule.Quotient.induction_on _ v fun v ↦ by
      obtain ⟨w, y, rfl⟩ := exists_eq_finsuppIntCast_add p v
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
    refine mem_range_finsuppIntCast p _ ?_
    rwa [smul_add, smul_neg]
  · induction x using QuotientAddGroup.induction_on with | H v => ?_
    obtain ⟨w, y, rfl⟩ := exists_eq_finsuppIntCast_add p v
    refine ⟨y, ?_⟩
    dsimp only
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq]
    refine ⟨w, ?_⟩
    -- `f` is `finsuppIntCast p` with its equivariance recorded
    change finsuppIntCast p w = -((p : ℤ) • y) + (finsuppIntCast p w + (p : ℤ) • y)
    abel

end TauCeti
