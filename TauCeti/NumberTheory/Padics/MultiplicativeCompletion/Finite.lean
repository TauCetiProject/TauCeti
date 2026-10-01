/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Module

/-!
# Finite generation of the p-adic completion of units

For a prime `p` and a field `L`, the completed multiplicative module
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` is a finitely generated `ℤ_p`-module as soon as `Lˣ/(Lˣ)^p` is
finite. In particular, for a nonarchimedean local field `L` in which `p ≠ 0`, such as a finite
extension of `ℚ_p`, the module `A(L)` is finitely generated over `ℤ_p`, and hence over the group
algebra `ℤ_p[Gal(L/K)]` for any field `K` below `L`. This is the finiteness hypothesis under which
the integral cancellation theorems for `ℤ_p[G]`-modules apply to `A(L)`.

## Implementation notes

The generators are the classes in `A(L)` of representatives of `Lˣ/(Lˣ)^p`. Every unit is, in
`A(L)`, a `ℤ_p`-combination of them plus a `p^m`-multiple, so every element of `A(L)` is matched
at each level `m` by some combination. Since the level-`m` coordinate of a combination depends on
the coefficients only modulo `p^m`, the coefficient vectors matching a given element at level `m`
form a decreasing sequence of nonempty closed subsets of the compact space of coefficient vectors,
and a vector in their intersection represents the element exactly.

## Main results

* `TauCeti.module_finite_padicCompletionUnits_of_finiteIndex`: `A(L)` is a finitely generated
  `ℤ_p`-module when `(Lˣ)^p` has finite index in `Lˣ`.
* `TauCeti.span_range_padicCompletionUnitsOf_eq_top`: under the same hypothesis, the classes of
  the units of `L` span `A(L)` over `ℤ_p`.
* `TauCeti.padicCompletionUnits_add_pow_smul_apply`: adding a `p ^ m`-multiple does not change
  the level-`m` coordinate of an element of `A(L)`.
* `TauCeti.module_finite_padicCompletionUnits_padicInt`: `A(L)` is a finitely generated
  `ℤ_p`-module for a nonarchimedean local field `L` with `(p : L) ≠ 0`.
* `TauCeti.module_finite_padicCompletionUnits_monoidAlgebra_of_finiteIndex`: `A(L)` is a
  finitely generated `ℤ_p[Gal(L/K)]`-module when `(Lˣ)^p` has finite index in `Lˣ`.
* `TauCeti.padicCompletionUnits_module_finite`: for a nonarchimedean local field `L` with
  `(p : L) ≠ 0`, `A(L)` is a finitely generated `ℤ_p[Gal(L/K)]`-module.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.4.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L]

/-- Adding a `p ^ m`-multiple in `A(L)` does not change the level-`m` coordinate. -/
theorem padicCompletionUnits_add_pow_smul_apply (m : ℕ)
    (y z : Additive ↑(padicCompletionUnits p L)) :
    (y + (p : ℤ_[p]) ^ m • z).toMul.1 m = y.toMul.1 m := by
  have h : (y + (p : ℤ_[p]) ^ m • z).toMul.1 m =
      (y.toMul.1 m : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) * z.toMul.1 m ^ p ^ m := by
    simp only [← Nat.cast_pow, padicCompletionUnits_natCast_smul, toMul_add, toMul_nsmul,
      Subgroup.coe_mul, Subgroup.coe_pow, Pi.mul_apply, Pi.pow_apply]
  rw [h, QuotientGroup.pow_eq_one_quotient_range_powMonoidHom]
  -- `rw [mul_one]` fails here: the type of the coordinate is the beta-redex
  -- `(fun m ↦ Lˣ ⧸ _) m`, so `mul_one` needs its argument at the reduced type.
  exact mul_one (y.toMul.1 m : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range)

/-- Modulo `p ^ m`-multiples, the class in `A(L)` of every unit is a `ℤ_p`-combination of the
classes of representatives of `Lˣ/(Lˣ)^p`. -/
private theorem exists_mem_span_add_pow_smul (m : ℕ) (u : Lˣ) :
    ∃ y ∈ Submodule.span ℤ_[p] (Set.range fun c : Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range ↦
        Additive.ofMul (padicCompletionUnitsOf p L c.out)),
      ∃ w : Lˣ, Additive.ofMul (padicCompletionUnitsOf p L u) =
        y + (p : ℤ_[p]) ^ m • Additive.ofMul (padicCompletionUnitsOf p L w) := by
  induction m generalizing u with
  | zero => exact ⟨0, zero_mem _, u, by simp⟩
  | succ m ih =>
    obtain ⟨y, hy, w, hw⟩ := ih u
    -- Split `w` as the chosen representative of its class times a `p`-th power.
    obtain ⟨z, hz⟩ : (w : Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range).out⁻¹ * w ∈
        (powMonoidHom p : Lˣ →* Lˣ).range :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    set c : Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range := QuotientGroup.mk w
    refine ⟨y + (p : ℤ_[p]) ^ m • Additive.ofMul (padicCompletionUnitsOf p L c.out),
      add_mem hy (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)), z, ?_⟩
    have hwz : w = c.out * z ^ p := by
      rw [powMonoidHom_apply] at hz
      rw [hz, mul_inv_cancel_left]
    have hprod : Additive.ofMul (padicCompletionUnitsOf p L (c.out * z ^ p)) =
        Additive.ofMul (padicCompletionUnitsOf p L c.out) +
          (p : ℤ_[p]) • Additive.ofMul (padicCompletionUnitsOf p L z) := by
      simp only [map_mul, map_pow, ofMul_mul, ofMul_pow,
        padicCompletionUnits_natCast_smul]
    rw [hw, hwz, hprod]
    module

/-- The level-`m` coordinate of a `ℤ_p`-combination of a finite family in `A(L)` is a locally
constant function of the coefficients: it only depends on them modulo `p ^ m`. -/
private theorem isLocallyConstant_linearCombination_apply {ι : Type*} [Fintype ι]
    (x : ι → Additive ↑(padicCompletionUnits p L)) (m : ℕ) :
    IsLocallyConstant fun c : ι → ℤ_[p] ↦ (Fintype.linearCombination ℤ_[p] x c).toMul.1 m := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun c ↦ ?_
  have hnhds : ∀ᶠ c' in nhds c, ∀ i, c' i - c i ∈ Ideal.span {(p : ℤ_[p]) ^ m} := by
    refine Filter.eventually_all.2 fun i ↦ ((continuous_apply i).tendsto c).eventually
      (p := fun y ↦ y - c i ∈ Ideal.span {(p : ℤ_[p]) ^ m}) ?_
    filter_upwards [Metric.closedBall_mem_nhds (c i)
      (zpow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) (-m : ℤ))] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hy
  filter_upwards [hnhds] with c' hc'
  choose d hd using fun i ↦ Ideal.mem_span_singleton'.1 (hc' i)
  have hc'd : c' = c + (p : ℤ_[p]) ^ m • d := by
    ext i
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm, hd i, add_sub_cancel]
  rw [hc'd, map_add, map_smul]
  exact padicCompletionUnits_add_pow_smul_apply p L m _ _

/-- If `Lˣ/(Lˣ)^p` is finite, every element of `A(L)` is a `ℤ_p`-combination of the classes of
representatives of `Lˣ/(Lˣ)^p`. -/
private theorem surjective_linearCombination_padicCompletionUnitsOf_out
    [Fintype (Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range)] :
    Function.Surjective (Fintype.linearCombination ℤ_[p]
      fun c : Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range ↦
        Additive.ofMul (padicCompletionUnitsOf p L c.out)) := by
  let Q := Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range
  let x : Q → Additive ↑(padicCompletionUnits p L) := fun c ↦
    Additive.ofMul (padicCompletionUnitsOf p L c.out)
  let f := Fintype.linearCombination ℤ_[p] x
  intro a
  -- The coefficient vectors that represent `a` at level `m`.
  let C : ℕ → Set (Q → ℤ_[p]) := fun m ↦ {c | (f c).toMul.1 m = a.toMul.1 m}
  have hanti (m : ℕ) : C (m + 1) ⊆ C m := by
    intro c hc
    have hfc := (mem_padicCompletionUnits_iff p L _).1 (f c).toMul.2 m
    have ha := (mem_padicCompletionUnits_iff p L _).1 a.toMul.2 m
    simp only [C, Set.mem_ofPred_eq] at hc ⊢
    rw [← hfc, ← ha, hc]
  have hne (m : ℕ) : (C m).Nonempty := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (a.toMul.1 m)
    obtain ⟨y, hy, w, hw⟩ := exists_mem_span_add_pow_smul p L m u
    rw [← Fintype.range_linearCombination] at hy
    obtain ⟨c, rfl⟩ := hy
    refine ⟨c, ?_⟩
    have hwm := congrArg (fun z : Additive ↑(padicCompletionUnits p L) ↦ z.toMul.1 m) hw
    simp only [padicCompletionUnits_add_pow_smul_apply, toMul_ofMul,
      padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply] at hwm
    exact hwm.symm.trans hu
  have hclosed (m : ℕ) : IsClosed (C m) :=
    (isLocallyConstant_linearCombination_apply p L x m).isClosed_fiber _
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti
    hne (hclosed 0).isCompact hclosed
  refine ⟨c, Additive.toMul.injective (Subtype.ext (funext fun m ↦ ?_))⟩
  exact Set.mem_iInter.1 hc m

/-- **Finite generation of `A(L)`.** If the subgroup `(Lˣ)^p` of `p`-th powers has finite index
in `Lˣ`, then the `p`-adic completion `A(L) = lim_m Lˣ/(Lˣ)^(p^m)` is a finitely generated
`ℤ_p`-module. -/
theorem module_finite_padicCompletionUnits_of_finiteIndex
    [(powMonoidHom p : Lˣ →* Lˣ).range.FiniteIndex] :
    Module.Finite ℤ_[p] (Additive ↑(padicCompletionUnits p L)) :=
  let _ : Fintype (Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range) := Fintype.ofFinite _
  .of_surjective _ (surjective_linearCombination_padicCompletionUnitsOf_out p L)

/-- If `(Lˣ)^p` has finite index in `Lˣ`, the classes of the units of `L` span `A(L)` as a
`ℤ_p`-module. -/
theorem span_range_padicCompletionUnitsOf_eq_top
    [(powMonoidHom p : Lˣ →* Lˣ).range.FiniteIndex] :
    Submodule.span ℤ_[p] (Set.range fun u : Lˣ ↦ Additive.ofMul (padicCompletionUnitsOf p L u)) =
      ⊤ := by
  let _ : Fintype (Lˣ ⧸ (powMonoidHom p : Lˣ →* Lˣ).range) := Fintype.ofFinite _
  refine eq_top_iff.2 fun a _ ↦ ?_
  obtain ⟨c, rfl⟩ := surjective_linearCombination_padicCompletionUnitsOf_out p L a
  rw [Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun q _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.out, rfl⟩)

/-- When `(Lˣ)^p` has finite index, `A(L)` is finite over the group algebra of any field
automorphism group `Gal(L/K)`. -/
theorem module_finite_padicCompletionUnits_monoidAlgebra_of_finiteIndex
    [(powMonoidHom p : Lˣ →* Lˣ).range.FiniteIndex] (K : Type*) [Field K] [Algebra K L] :
    Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (Additive ↑(padicCompletionUnits p L)) :=
  have := module_finite_padicCompletionUnits_of_finiteIndex p L
  Module.Finite.of_restrictScalars_finite ℤ_[p] _ _

section LocalField

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- For a nonarchimedean local field `L` in which `p ≠ 0`, for instance a finite extension of
`ℚ_p`, the completed multiplicative module `A(L)` is a finitely generated `ℤ_p`-module. -/
theorem module_finite_padicCompletionUnits_padicInt (hpL : (p : L) ≠ 0) :
    Module.Finite ℤ_[p] (Additive ↑(padicCompletionUnits p L)) :=
  have := finiteIndex_range_powMonoidHom hpL
  module_finite_padicCompletionUnits_of_finiteIndex p L

/-- **`A(L)` is a finitely generated `ℤ_p[Gal(L/K)]`-module.** For a nonarchimedean local field
`L` in which `p ≠ 0` and any field `K` below `L`, the completed multiplicative module `A(L)` is
finitely generated over the integral group algebra `ℤ_p[Gal(L/K)]`. -/
theorem padicCompletionUnits_module_finite (hpL : (p : L) ≠ 0) (K : Type*) [Field K]
    [Algebra K L] :
    Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (Additive ↑(padicCompletionUnits p L)) :=
  have := finiteIndex_range_powMonoidHom hpL
  module_finite_padicCompletionUnits_monoidAlgebra_of_finiteIndex p L K

end LocalField

end TauCeti
