/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The lattice defect of the trivial module `ℤ`

Let `G` be a finite group and `k` a field of characteristic `ℓ`. The group `ℤ` with the trivial
action of `G` has no `ℓ`-torsion, and its reduction `k ⊗_ℤ (ℤ ⧸ ℓℤ)` is the trivial line `k`. So
its lattice defect is the unit `1 = [k]` of the ring `G₀(k[G])`
(`TauCeti.latticeDefect_int_eq_one`).

This is the contribution of the value group whenever a `G`-module `V` is an extension of `ℤ` with
trivial action, `0 → V₀ → V → ℤ → 0`: by additivity, the defect of `V` is `1` plus that of `V₀`.
The main example is the valuation sequence `0 → 𝒪[L]ˣ → Lˣ → ℤ → 0` of a Galois extension of
local fields.

The action of `G` on `ℤ` is an arbitrary `DistribMulAction` together with the hypothesis that it
is trivial, since Mathlib has no trivial-action instance on `ℤ`. The finiteness of `ℤ ⧸ ℓℤ` and of
the `ℓ`-torsion of `ℤ`, which the definition of the defect asks for, are recorded as instances.

## Main results

* `TauCeti.subsingleton_torsionBy_int` and `TauCeti.finite_quotSMulTop_int`: for `n ≠ 0`, the
  `n`-torsion of `ℤ` is zero and `ℤ ⧸ nℤ` is finite.
* `TauCeti.latticeDefect_int_eq_one`: the lattice defect of `ℤ` with the trivial action is `1`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3) and the proof of (7.3.1).
-/

public section

namespace TauCeti

open scoped _root_.MonoidAlgebra TensorProduct Pointwise

/-- `ℤ` has no nonzero `n`-torsion for `n ≠ 0`. -/
instance subsingleton_torsionBy_int (n : ℕ) [NeZero n] :
    Subsingleton (Submodule.torsionBy ℤ ℤ (n : ℤ)) := by
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  have hx := (Submodule.mem_torsionBy_iff _ _).mp x.property
  have hy := (Submodule.mem_torsionBy_iff _ _).mp y.property
  simp only [smul_eq_mul, mul_eq_zero, Int.natCast_eq_zero, NeZero.ne n, false_or] at hx hy
  rw [hx, hy]

/-- `ℤ ⧸ nℤ` is finite for `n ≠ 0`. -/
instance finite_quotSMulTop_int (n : ℕ) [NeZero n] : Finite (QuotSMulTop (n : ℤ) ℤ) :=
  Module.finite_of_fg_torsion _ fun x ↦
    ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr (NeZero.ne n))⟩,
      Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator ℤ (n : ℤ)) x⟩

variable (k G : Type) [Field k] [Monoid G] [Finite G] (ℓ : ℕ)

/-- **The lattice defect of `ℤ` with the trivial action is the class of the trivial line**: in
`G₀(k[G])` with `k` of characteristic `ℓ`, `[k ⊗_ℤ (ℤ ⧸ ℓℤ)] - [k ⊗_ℤ ℤ[ℓ]] = [k] = 1`. -/
theorem latticeDefect_int_eq_one [NeZero ℓ] [CharP k ℓ] [DistribMulAction G ℤ]
    (h : ∀ (g : G) (n : ℤ), g • n = n) : latticeDefect k G ℓ ℤ = 1 := by
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) ℤ)
  have := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ ℤ (ℓ : ℤ))
  let ρ := Representation.ofDistribMulAction ℤ G ℤ
  -- the reduction of the trivial module is trivial
  have hρ (g : G) : Representation.baseChange k (ρ.quotSMulTop ℓ) g = LinearMap.id := by
    rw [Representation.baseChange_apply, Representation.quotSMulTop_apply,
      show ρ g = LinearMap.id from LinearMap.ext (h g), QuotSMulTop.map_id,
      LinearMap.baseChange_id]
  -- `k ⊗_ℤ (ℤ ⧸ ℓℤ) ≅ (k ⊗_ℤ ℤ) ⧸ ℓ = k ⊗_ℤ ℤ ≅ k`, as `ℓ` vanishes in `k`
  have h0 : (algebraMap ℤ k ℓ) • (⊤ : Submodule k (k ⊗[ℤ] ℤ)) = ⊥ := by
    rw [map_natCast, CharP.cast_eq_zero, zero_smul, Submodule.zero_eq_bot]
  let e : (Representation.baseChange k (ρ.quotSMulTop ℓ)).Equiv
      (Representation.trivial k G k) :=
    { toLinearEquiv :=
        (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop (ℓ : ℤ) ℤ k).symm ≪≫ₗ
          Submodule.quotEquivOfEqBot _ h0 ≪≫ₗ TensorProduct.AlgebraTensorModule.rid ℤ k k
      isIntertwining' g := by
        ext
        simp [hρ] }
  rw [latticeDefect_def, reductionK0_eq_zero_of_subsingleton k (ρ.torsionBy ℓ), sub_zero,
    reductionK0_def, exactK0_one_eq_of_trivial]
  have : Module.Finite k[G] (Representation.trivial k G k).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv e).toFGModuleCatIso

end TauCeti
