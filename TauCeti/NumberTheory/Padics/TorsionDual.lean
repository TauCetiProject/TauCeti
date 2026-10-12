/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.Padics.Module
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# `Ext¹(-, ℤ_p)` of a presented module is the dual of its `p`-power torsion

Let `0 → P₁ → P₀ → M → 0` be an exact sequence of `ℤ_p`-modules, with first map `f`. Applying
`Hom_{ℤ_p}(-, ℤ_p)` gives `Hom(P₀, ℤ_p) → Hom(P₁, ℤ_p)`, whose cokernel is `Ext¹_{ℤ_p}(M, ℤ_p)` when
`P₀` is projective. For `M` finitely generated this cokernel is the Pontryagin dual
`Hom_{ℤ_p}(M[p^∞], ℚ_p / ℤ_p)` of the `p`-power torsion `M[p^∞]` of `M`.

The comparison is the connecting map of the long exact sequence for
`0 → ℤ_p → ℚ_p → ℚ_p / ℤ_p → 0`, written out by hand: a torsion element `t` lifts to `x ∈ P₀` with
`p ^ n • x = f k` for some `k ∈ P₁`, and a functional `ψ` on `P₁` sends `t` to the class of
`ψ k / p ^ n`. Its kernel consists of the functionals extending along `f`, because `M[p^∞]` is a
direct summand of `M` over `ℤ_p`, and it is surjective because `P₀` is projective.

The modules may carry an action of a `ℤ_p`-algebra `A` for which the maps are `A`-linear; the
connecting map is then compatible with the contragredient actions of `A`: precomposing a functional
on `P₁` with the action of `a ∈ A` corresponds to precomposing a character of `M[p^∞]` with the
action of `a`. Applied to the group algebra `A = ℤ_p[G]` of a finite group,
this identifies `E¹(M) = Ext¹_{ℤ_p[G]}(M, ℤ_p[G])` of a module of projective dimension one with the
Pontryagin dual of its `p`-power torsion.

## Main definitions

* `TauCeti.torsionDualMap`: the connecting map `Hom(P₁, ℤ_p) → Hom(M[p^∞], ℚ_p / ℤ_p)`.
* `TauCeti.torsionDualEquiv`: the induced isomorphism of its cokernel with the dual of the torsion.

## Main results

* `TauCeti.torsionDualMap_apply`: the connecting map on representatives.
* `TauCeti.torsionDualMap_apply_of_extension`: the connecting map at a functional extending along
  `f` to a `ℚ_p`-valued functional `Φ` sends `π x` to the class of `Φ x`.
* `TauCeti.ker_torsionDualMap`: its kernel is the range of `Hom(P₀, ℤ_p) → Hom(P₁, ℤ_p)`.
* `TauCeti.torsionDualMap_surjective`: it is surjective when `P₀` is projective over `ℤ_p`.
* `TauCeti.torsionDualMap_comp_toLinearMap_apply`: it is compatible with the contragredient
  actions of `A` on functionals and on characters.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Springer (2008), (5.4.11) and (5.6.9).
-/

public section

noncomputable section

open Module

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {A : Type*} [Ring A] [Algebra ℤ_[p] A]
  {P₁ P₀ M : Type*} [AddCommGroup P₁] [Module A P₁] [Module ℤ_[p] P₁] [IsScalarTower ℤ_[p] A P₁]
  [AddCommGroup P₀] [Module A P₀] [Module ℤ_[p] P₀] [IsScalarTower ℤ_[p] A P₀]
  [AddCommGroup M] [Module A M] {f : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}

section Extension

omit [Fact p.Prime] [Algebra ℤ_[p] A] [Module ℤ_[p] P₁] [IsScalarTower ℤ_[p] A P₁] [Module ℤ_[p] P₀]
  [IsScalarTower ℤ_[p] A P₀] in
/-- Some power of `p` carries an element of the preimage of the `p`-power torsion into the range
of `f`. -/
private theorem exists_nsmul_eq (hf : Function.Exact f π) (y : (pPowerTorsion p A M).comap π) :
    ∃ nk : ℕ × P₁, p ^ nk.1 • (y : P₀) = f nk.2 := by
  obtain ⟨n, hn⟩ := mem_pPowerTorsion_iff.mp (Submodule.mem_comap.mp y.2)
  obtain ⟨k, hk⟩ := (hf _).mp (by rw [map_nsmul, hn])
  exact ⟨(n, k), hk.symm⟩

/-- The value at `y` of the `ℚ_p`-valued extension of `ψ`, through a chosen `p ^ n • y = f k`. -/
private def extendDualFun (hf : Function.Exact f π) (ψ : Dual ℤ_[p] P₁)
    (y : (pPowerTorsion p A M).comap π) : ℚ_[p] :=
  (ψ (exists_nsmul_eq hf y).choose.2 : ℚ_[p]) / (p : ℚ_[p]) ^ (exists_nsmul_eq hf y).choose.1

omit [Algebra ℤ_[p] A] [IsScalarTower ℤ_[p] A P₁] [Module ℤ_[p] P₀] [IsScalarTower ℤ_[p] A P₀] in
private theorem extendDualFun_eq (hf : Function.Exact f π) (hfi : Function.Injective f)
    (ψ : Dual ℤ_[p] P₁) (y : (pPowerTorsion p A M).comap π) {n : ℕ} {k : P₁}
    (h : p ^ n • (y : P₀) = f k) : extendDualFun hf ψ y = ψ k / (p : ℚ_[p]) ^ n := by
  have hspec := (exists_nsmul_eq hf y).choose_spec
  set nk := (exists_nsmul_eq hf y).choose
  -- The chosen representative `p ^ n' • y = f k'` satisfies `p ^ n • k' = p ^ n' • k`, since `f`
  -- is injective.
  have hkk : p ^ n • nk.2 = p ^ nk.1 • k := hfi <| by
    rw [map_nsmul, map_nsmul, ← hspec, ← h, smul_comm]
  have hcast := congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) (congrArg ψ hkk)
  push_cast [map_nsmul, nsmul_eq_mul] at hcast
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [extendDualFun, div_eq_div_iff (pow_ne_zero _ hp) (pow_ne_zero _ hp)]
  linear_combination hcast

variable (hf : Function.Exact f π) (hfi : Function.Injective f)

/-- The `ℚ_p`-valued extension of a functional on `P₁` to the preimage in `P₀` of the `p`-power
torsion, determined by `p ^ n • y = f k ↦ ψ k / p ^ n`. -/
private def extendDual :
    Dual ℤ_[p] P₁ →ₗ[ℤ_[p]] (pPowerTorsion p A M).comap π →ₗ[ℤ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℤ_[p] (extendDualFun hf)
    (fun ψ₁ ψ₂ y ↦ by
      obtain ⟨⟨n, k⟩, h⟩ := exists_nsmul_eq hf y
      simp only [extendDualFun_eq hf hfi _ y h, LinearMap.add_apply, PadicInt.coe_add, add_div])
    (fun c ψ y ↦ by
      obtain ⟨⟨n, k⟩, h⟩ := exists_nsmul_eq hf y
      simp only [extendDualFun_eq hf hfi _ y h, LinearMap.smul_apply, smul_eq_mul,
        PadicInt.coe_mul, Algebra.smul_def, PadicInt.algebraMap_apply, mul_div_assoc])
    (fun ψ y₁ y₂ ↦ by
      obtain ⟨⟨n₁, k₁⟩, h₁⟩ := exists_nsmul_eq hf y₁
      obtain ⟨⟨n₂, k₂⟩, h₂⟩ := exists_nsmul_eq hf y₂
      have h : p ^ (n₁ + n₂) • ((y₁ + y₂ : (pPowerTorsion p A M).comap π) : P₀) =
          f (p ^ n₂ • k₁ + p ^ n₁ • k₂) := by
        rw [Submodule.coe_add, smul_add, map_add, map_nsmul, map_nsmul, ← h₁, ← h₂, pow_add,
          mul_comm, mul_smul, mul_comm, mul_smul, smul_comm (p ^ n₁)]
      have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      rw [extendDualFun_eq hf hfi ψ _ h, extendDualFun_eq hf hfi ψ _ h₁,
        extendDualFun_eq hf hfi ψ _ h₂]
      -- Normalize the casts, then clear the powers of `p`.
      push_cast [map_add, map_nsmul, nsmul_eq_mul]
      field_simp
      ring)
    (fun c ψ y ↦ by
      obtain ⟨⟨n, k⟩, h⟩ := exists_nsmul_eq hf y
      have h' : p ^ n • ((c • y : (pPowerTorsion p A M).comap π) : P₀) = f (c • k) := by
        rw [Submodule.coe_smul_of_tower, smul_comm, h, LinearMap.map_smul_of_tower]
      rw [extendDualFun_eq hf hfi ψ _ h', extendDualFun_eq hf hfi ψ _ h, map_smul, smul_eq_mul,
        PadicInt.coe_mul, Algebra.smul_def, PadicInt.algebraMap_apply, mul_div_assoc])

private theorem extendDual_eq (ψ : Dual ℤ_[p] P₁) (y : (pPowerTorsion p A M).comap π) {n : ℕ}
    {k : P₁} (h : p ^ n • (y : P₀) = f k) :
    extendDual hf hfi ψ y = ψ k / (p : ℚ_[p]) ^ n :=
  extendDualFun_eq hf hfi ψ y h

/-- On the range of `f`, the extension of `ψ` takes the values of `ψ`. -/
private theorem extendDual_eq_of_eq (ψ : Dual ℤ_[p] P₁) (y : (pPowerTorsion p A M).comap π)
    {k : P₁} (h : (y : P₀) = f k) : extendDual hf hfi ψ y = ψ k := by
  rw [extendDual_eq hf hfi ψ y (n := 0) (by rw [pow_zero, one_smul, h]), pow_zero, div_one]

end Extension

section TorsionDual

variable (hf : Function.Exact f π) (hfi : Function.Injective f) (hπ : Function.Surjective π)

omit [Fact p.Prime] [Algebra ℤ_[p] A] [Module ℤ_[p] P₁] [IsScalarTower ℤ_[p] A P₁] [Module ℤ_[p] P₀]
  [IsScalarTower ℤ_[p] A P₀] in
private theorem exists_lift (hπ : Function.Surjective π) (t : pPowerTorsion p A M) :
    ∃ y : (pPowerTorsion p A M).comap π, ⟨π y, y.2⟩ = t := by
  obtain ⟨x, hx⟩ := hπ t
  exact ⟨⟨x, by simp [hx]⟩, Subtype.ext hx⟩

/-- The class in `ℚ_p / ℤ_p` of the extension of `ψ` at a chosen lift of `t`. -/
private def torsionDualFun (ψ : Dual ℤ_[p] P₁) (t : pPowerTorsion p A M) :
    ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  Submodule.Quotient.mk (extendDual hf hfi ψ (exists_lift hπ t).choose)

private theorem torsionDualFun_eq (ψ : Dual ℤ_[p] P₁) (y : (pPowerTorsion p A M).comap π) :
    torsionDualFun hf hfi hπ ψ ⟨π y, y.2⟩ = Submodule.Quotient.mk (extendDual hf hfi ψ y) := by
  have hy : π (exists_lift hπ ⟨π y, y.2⟩).choose = π y :=
    congrArg Subtype.val (exists_lift hπ ⟨π y, y.2⟩).choose_spec
  set y' := (exists_lift hπ ⟨π y, y.2⟩).choose
  -- Two lifts differ by an element of the range of `f`, on which the extension is integral.
  obtain ⟨j, hj⟩ := (hf ((y' : P₀) - y)).mp (by rw [map_sub, hy, sub_self])
  rw [torsionDualFun, Submodule.Quotient.eq, ← map_sub,
    extendDual_eq_of_eq hf hfi ψ (y' - y) (k := j) (by rw [Submodule.coe_sub, hj])]
  exact Submodule.mem_one.mpr ⟨ψ j, rfl⟩

variable [Module ℤ_[p] M] [IsScalarTower ℤ_[p] A M]

variable (p) in
/-- The **connecting map** `Hom(P₁, ℤ_p) → Hom(M[p^∞], ℚ_p / ℤ_p)` of a presentation
`0 → P₁ → P₀ → M → 0`: for `t` in the `p`-power torsion of `M`, choose `x ∈ P₀` over `t` and
`p ^ n • x = f k`; then `ψ` sends `t` to the class of `ψ k / p ^ n`. When `M` is finitely generated
over `ℤ_p`, its kernel consists of the functionals extending along `f`
(`TauCeti.ker_torsionDualMap`), and when moreover `P₀` is projective it is surjective
(`TauCeti.torsionDualMap_surjective`); so it identifies `Ext¹_{ℤ_p}(M, ℤ_p)` with the Pontryagin
dual of the `p`-power torsion of `M` (`TauCeti.torsionDualEquiv`). -/
def torsionDualMap :
    Dual ℤ_[p] P₁ →ₗ[ℤ_[p]] pPowerTorsion p A M →ₗ[ℤ_[p]] ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  LinearMap.mk₂ ℤ_[p] (torsionDualFun hf hfi hπ)
    (fun ψ₁ ψ₂ t ↦ by
      simp only [torsionDualFun, map_add, LinearMap.add_apply, Submodule.Quotient.mk_add])
    (fun c ψ t ↦ by
      simp only [torsionDualFun, map_smul, LinearMap.smul_apply, Submodule.Quotient.mk_smul])
    (fun ψ t₁ t₂ ↦ by
      obtain ⟨y₁, rfl⟩ := exists_lift hπ t₁
      obtain ⟨y₂, rfl⟩ := exists_lift hπ t₂
      have h := torsionDualFun_eq hf hfi hπ ψ (y₁ + y₂)
      rw [torsionDualFun_eq, torsionDualFun_eq, ← Submodule.Quotient.mk_add, ← map_add, ← h]
      exact congrArg _ (Subtype.ext (by simp)))
    (fun c ψ t ↦ by
      obtain ⟨y, rfl⟩ := exists_lift hπ t
      have h := torsionDualFun_eq hf hfi hπ ψ (c • y)
      rw [torsionDualFun_eq, ← Submodule.Quotient.mk_smul, ← map_smul, ← h]
      exact congrArg _ (Subtype.ext (by simp)))

private theorem torsionDualMap_eq (ψ : Dual ℤ_[p] P₁) (y : (pPowerTorsion p A M).comap π) :
    torsionDualMap p hf hfi hπ ψ ⟨π y, y.2⟩ = Submodule.Quotient.mk (extendDual hf hfi ψ y) :=
  torsionDualFun_eq hf hfi hπ ψ y

omit [Fact p.Prime] [Algebra ℤ_[p] A] [Module ℤ_[p] P₁] [IsScalarTower ℤ_[p] A P₁] [Module ℤ_[p] P₀]
  [IsScalarTower ℤ_[p] A P₀] in
/-- Every `p`-power torsion element of `M` has a lift `x ∈ P₀` with `p ^ n • x` in the range of
`f`. -/
private theorem exists_lift_nsmul_eq (hf : Function.Exact f π) (hπ : Function.Surjective π)
    (t : pPowerTorsion p A M) :
    ∃ x : P₀, ∃ n : ℕ, ∃ k : P₁, π x = t ∧ p ^ n • x = f k := by
  obtain ⟨y, rfl⟩ := exists_lift hπ t
  obtain ⟨⟨n, k⟩, h⟩ := exists_nsmul_eq hf y
  exact ⟨y, n, k, rfl, h⟩

/-- The connecting map on a `p`-power torsion element `t`: if `π x = t` and `p ^ n • x = f k`,
then `ψ` sends `t` to the class of `ψ k / p ^ n`. -/
theorem torsionDualMap_apply (ψ : Dual ℤ_[p] P₁) (t : pPowerTorsion p A M) {x : P₀} {n : ℕ}
    {k : P₁} (hx : π x = t) (hk : p ^ n • x = f k) :
    torsionDualMap p hf hfi hπ ψ t = Submodule.Quotient.mk ((ψ k : ℚ_[p]) / (p : ℚ_[p]) ^ n) := by
  have hy : x ∈ (pPowerTorsion p A M).comap π := by
    rw [Submodule.mem_comap, hx]
    exact t.2
  obtain rfl : (⟨π x, hy⟩ : pPowerTorsion p A M) = t := Subtype.ext hx
  rw [torsionDualMap_eq hf hfi hπ ψ ⟨x, hy⟩, extendDual_eq hf hfi ψ _ hk]

/-- The connecting map at a functional `ψ` that extends along `f` to a `ℚ_p`-valued functional `Φ`
on `P₀`: it sends `π x` to the class of `Φ x`. -/
theorem torsionDualMap_apply_of_extension (ψ : Dual ℤ_[p] P₁) (Φ : P₀ →ₗ[ℤ_[p]] ℚ_[p])
    (hΦ : ∀ k, (ψ k : ℚ_[p]) = Φ (f k)) (t : pPowerTorsion p A M) {x : P₀} (hx : π x = t) :
    torsionDualMap p hf hfi hπ ψ t = Submodule.Quotient.mk (Φ x) := by
  have hy : x ∈ (pPowerTorsion p A M).comap π := by
    rw [Submodule.mem_comap, hx]
    exact t.2
  obtain ⟨⟨n, k⟩, hk⟩ := exists_nsmul_eq hf ⟨x, hy⟩
  rw [torsionDualMap_apply hf hfi hπ ψ t hx hk, hΦ]
  -- `Φ (f k) / p ^ n = Φ (p ^ n • x) / p ^ n = Φ x`.
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp [← hk, hp]

/-- The connecting map is compatible with the contragredient actions of `A`: precomposing a
functional with the action of `a ∈ A` on `P₁` corresponds to evaluating its image at `a • t`. -/
@[simp]
theorem torsionDualMap_comp_toLinearMap_apply (ψ : Dual ℤ_[p] P₁) (a : A)
    (t : pPowerTorsion p A M) :
    torsionDualMap p hf hfi hπ (ψ ∘ₗ DistribSMul.toLinearMap ℤ_[p] P₁ a) t =
      torsionDualMap p hf hfi hπ ψ (a • t) := by
  obtain ⟨x, n, k, hx, hk⟩ := exists_lift_nsmul_eq hf hπ t
  rw [torsionDualMap_apply hf hfi hπ _ t hx hk,
    torsionDualMap_apply hf hfi hπ ψ (a • t) (x := a • x) (n := n) (k := a • k)
      (by rw [map_smul, hx, Submodule.coe_smul]) (by rw [smul_comm, hk, map_smul]),
    LinearMap.comp_apply, DistribSMul.toLinearMap_apply]

/-- The connecting map vanishes on the functionals that extend along `f`. -/
@[simp]
theorem torsionDualMap_dualMap (φ : Dual ℤ_[p] P₀) :
    torsionDualMap p hf hfi hπ ((f.restrictScalars ℤ_[p]).dualMap φ) = 0 := by
  ext t
  obtain ⟨x, hx⟩ := hπ t
  rw [torsionDualMap_apply_of_extension hf hfi hπ _ (Algebra.linearMap ℤ_[p] ℚ_[p] ∘ₗ φ)
    (fun _ ↦ rfl) t hx, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_one.mpr ⟨φ x, rfl⟩

end TorsionDual

section Bijective

variable [Module ℤ_[p] M] [IsScalarTower ℤ_[p] A M]

variable [Module.Finite ℤ_[p] M] (hf : Function.Exact f π) (hfi : Function.Injective f)
  (hπ : Function.Surjective π)

omit [Module ℤ_[p] P₁] [IsScalarTower ℤ_[p] A P₁] in
/-- Modulo its `p`-power torsion, a finitely generated `ℤ_p`-module is free, so `P₀ → M` has a
section over it. -/
private theorem exists_section (hπ : Function.Surjective π) :
    ∃ σ : (M ⧸ pPowerTorsion p A M) →ₗ[ℤ_[p]] P₀,
      ∀ z, Submodule.Quotient.mk (π (σ z)) = z := by
  have : Module.Finite ℤ_[p] (M ⧸ pPowerTorsion p A M) :=
    .of_surjective ((pPowerTorsion p A M).mkQ.restrictScalars ℤ_[p]) <| by
      rw [LinearMap.coe_restrictScalars]
      exact Submodule.mkQ_surjective _
  obtain ⟨σ, hσ⟩ := projective_lifting_property
    (((pPowerTorsion p A M).mkQ ∘ₗ π).restrictScalars ℤ_[p]) LinearMap.id
    ((Submodule.mkQ_surjective _).comp hπ)
  exact ⟨σ, fun z ↦ LinearMap.congr_fun hσ z⟩

/-- The kernel of the connecting map consists exactly of the functionals that extend along `f`. -/
theorem ker_torsionDualMap :
    LinearMap.ker (torsionDualMap p hf hfi hπ) =
      LinearMap.range (f.restrictScalars ℤ_[p]).dualMap := by
  refine le_antisymm (fun ψ hψ ↦ ?_)
    (LinearMap.range_le_ker_iff.mpr (LinearMap.ext (torsionDualMap_dualMap hf hfi hπ)))
  obtain ⟨σ, hσ⟩ := exists_section (p := p) (A := A) hπ
  -- Subtracting the section projects `P₀` onto the preimage of the torsion.
  have hpr (x : P₀) : x - σ (Submodule.Quotient.mk (π x)) ∈ (pPowerTorsion p A M).comap π := by
    rw [Submodule.mem_comap, ← Submodule.Quotient.mk_eq_zero, map_sub, Submodule.Quotient.mk_sub,
      hσ, sub_self]
  let pr : P₀ →ₗ[ℤ_[p]] (pPowerTorsion p A M).comap π :=
    { toFun x := ⟨_, hpr x⟩
      map_add' x y := Subtype.ext <| by
        simp only [map_add, Submodule.Quotient.mk_add, Submodule.coe_add]
        abel
      map_smul' c x := Subtype.ext <| by
        simp only [LinearMap.map_smul_of_tower, Submodule.Quotient.mk_smul, map_smul,
          Submodule.coe_smul_of_tower, RingHom.id_apply, smul_sub] }
  have hint (x : P₀) : extendDual hf hfi ψ (pr x) ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← torsionDualMap_eq hf hfi hπ, LinearMap.mem_ker.mp hψ,
      LinearMap.zero_apply]
  refine ⟨(extendDual hf hfi ψ ∘ₗ pr).padicIntCodRestrict hint,
    LinearMap.ext fun k ↦ Subtype.ext ?_⟩
  rw [LinearMap.dualMap_apply, LinearMap.restrictScalars_apply,
    LinearMap.coe_padicIntCodRestrict_apply, LinearMap.comp_apply]
  exact extendDual_eq_of_eq hf hfi ψ (pr (f k)) (k := k) (by
    simp [pr, hf.apply_apply_eq_zero])

/-- The connecting map is surjective when `P₀` is projective over `ℤ_p`: every character of the
`p`-power torsion of `M` comes from a functional on `P₁`. -/
theorem torsionDualMap_surjective [Module.Projective ℤ_[p] P₀] :
    Function.Surjective (torsionDualMap p hf hfi hπ) := by
  intro χ
  obtain ⟨σ, hσ⟩ := exists_section (p := p) (A := A) hπ
  -- Subtracting the section retracts `M` onto its `p`-power torsion.
  have hr (m : M) : m - π (σ (Submodule.Quotient.mk m)) ∈ pPowerTorsion p A M := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hσ, sub_self]
  let r : M →ₗ[ℤ_[p]] pPowerTorsion p A M :=
    { toFun m := ⟨_, hr m⟩
      map_add' x y := Subtype.ext <| by
        simp only [map_add, Submodule.Quotient.mk_add, Submodule.coe_add]
        abel
      map_smul' c x := Subtype.ext <| by
        simp only [Submodule.Quotient.mk_smul, map_smul, LinearMap.map_smul_of_tower,
          Submodule.coe_smul_of_tower, RingHom.id_apply, smul_sub] }
  have hrt (t : pPowerTorsion p A M) : r t = t := Subtype.ext (by
    simp [r, (Submodule.Quotient.mk_eq_zero _).mpr t.2])
  obtain ⟨Φ, hΦ⟩ := projective_lifting_property (1 : Submodule ℤ_[p] ℚ_[p]).mkQ
    (χ ∘ₗ r ∘ₗ π.restrictScalars ℤ_[p]) (Submodule.mkQ_surjective _)
  have hΦx (x : P₀) : Submodule.Quotient.mk (Φ x) = χ (r (π x)) := LinearMap.congr_fun hΦ x
  have hint (k : P₁) : (Φ ∘ₗ f.restrictScalars ℤ_[p]) k ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
    rw [← Submodule.Quotient.mk_eq_zero, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      hΦx, hf.apply_apply_eq_zero, map_zero, map_zero]
  refine ⟨LinearMap.padicIntCodRestrict _ hint, LinearMap.ext fun t ↦ ?_⟩
  obtain ⟨x, hx⟩ := hπ t
  rw [torsionDualMap_apply_of_extension hf hfi hπ _ Φ
    (LinearMap.coe_padicIntCodRestrict_apply _ hint) t hx, hΦx, ← hrt t]
  rw [hx]

variable (p) in
/-- **`Ext¹_{ℤ_p}(M, ℤ_p)` is the Pontryagin dual of the `p`-power torsion of `M`.** For an exact
sequence `0 → P₁ → P₀ → M → 0` with `P₀` projective over `ℤ_p` and `M` finitely generated over
`ℤ_p`, the cokernel of `Hom(P₀, ℤ_p) → Hom(P₁, ℤ_p)` is isomorphic to
`Hom_{ℤ_p}(M[p^∞], ℚ_p / ℤ_p)`, through the connecting map `TauCeti.torsionDualMap`. -/
def torsionDualEquiv [Module.Projective ℤ_[p] P₀] :
    (Dual ℤ_[p] P₁ ⧸ LinearMap.range (f.restrictScalars ℤ_[p]).dualMap) ≃ₗ[ℤ_[p]]
      (pPowerTorsion p A M →ₗ[ℤ_[p]] ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) :=
  (Submodule.quotEquivOfEq _ _ (ker_torsionDualMap hf hfi hπ).symm).trans
    ((torsionDualMap p hf hfi hπ).quotKerEquivOfSurjective (torsionDualMap_surjective hf hfi hπ))

/-- `TauCeti.torsionDualEquiv` sends the class of a functional to its image under the connecting
map. -/
@[simp]
theorem torsionDualEquiv_mk [Module.Projective ℤ_[p] P₀] (ψ : Dual ℤ_[p] P₁) :
    torsionDualEquiv p hf hfi hπ (Submodule.Quotient.mk ψ) = torsionDualMap p hf hfi hπ ψ := by
  simp [torsionDualEquiv]

end Bijective

end TauCeti
