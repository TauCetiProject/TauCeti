/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The tautological action of the diffeomorphism group

The self-diffeomorphism group `M ≃ₘ^n⟮I, I⟯ M` acts on the underlying manifold by evaluation:
`φ • x = φ x`. This file records that action, its faithfulness, and continuity in the point.

The action formalization mirrors Mathlib's `Homeomorph.applyMulAction`
(`Mathlib.Topology.Algebra.ConstMulAction`, added in Kim Morrison's mathlib4#40135), which
generalizes `Equiv.Perm.applyMulAction`.

The evaluation action and the forgetful homomorphism `Diff(M) → Homeomorph(M)` are the basic
API relating the abstract group `Diff(M)` to the space it acts on: faithfulness identifies a
diffeomorphism with the permutation of `M` it induces, and continuity in the point records that
each diffeomorphism acts by a homeomorphism.

## Main definitions

* `Diffeomorph.applyMulAction`: the `MulAction (M ≃ₘ^n⟮I, I⟯ M) M` with
  `φ • x = φ x`.
* `Diffeomorph.applyFaithfulSMul`: the action is faithful.
* `Diffeomorph.applyContinuousConstSMul`: each diffeomorphism acts continuously.
* `Diffeomorph.applySubgroupContinuousConstSMul`: subgroups inherit continuity in the
  point.

## Main statements

* `Diffeomorph.isFixedPt_zpow_iff_minimalPeriod_dvd`: a point is fixed by `f ^ k` exactly when
  its minimal period under `f` divides `k`.
* `Diffeomorph.exists_zpow_apply_eq_iff`: the orbit of a periodic point under the integer powers
  of `f` consists of its iterates below the minimal period.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The tautological action of the self-diffeomorphism group on the manifold by evaluation. -/
instance applyMulAction : MulAction (M ≃ₘ^n⟮I, I⟯ M) M where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action of `M ≃ₘ^n⟮I, I⟯ M` on `M` is given by evaluation. -/
@[simp]
theorem smul_def (f : M ≃ₘ^n⟮I, I⟯ M) (x : M) : f • x = f x := rfl

/-- The action homomorphism of the tautological diffeomorphism action is the forgetful homomorphism
to permutations. -/
@[simp]
theorem toPermHom_eq_toPerm :
    MulAction.toPermHom (M ≃ₘ^n⟮I, I⟯ M) M = toPerm := by
  ext f x
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_def, toPerm_apply,
    coe_toEquiv]

/-- A point `x` is a fixed point of the power `f ^ k` of a self-diffeomorphism exactly when the
minimal period of `x` under `f` divides `k`. -/
theorem isFixedPt_zpow_iff_minimalPeriod_dvd (f : M ≃ₘ^n⟮I, I⟯ M) (x : M) (k : ℤ) :
    Function.IsFixedPt (f ^ k) x ↔ (Function.minimalPeriod f x : ℤ) ∣ k := by
  simpa [Function.IsFixedPt] using MulAction.zpow_smul_eq_iff_minimalPeriod_dvd (a := f) (b := x)
    (n := k)

/-- For a periodic point `x` of a self-diffeomorphism `f`, the points `(f ^ k) x` with `k ∈ ℤ` are
the iterates `f^[j] x` with `j` below the least period of `x`. -/
theorem exists_zpow_apply_eq_iff {f : M ≃ₘ^n⟮I, I⟯ M} {x : M} (hx : x ∈ Function.periodicPts f)
    {y : M} : (∃ k : ℤ, (f ^ k) x = y) ↔ ∃ j < Function.minimalPeriod f x, f^[j] x = y := by
  have hm := Function.minimalPeriod_pos_of_mem_periodicPts hx
  have hiter (j : ℕ) : (f ^ (j : ℤ)) x = f^[j] x := by rw [zpow_natCast, coe_pow]
  constructor
  · rintro ⟨k, rfl⟩
    -- Reduce the exponent modulo the least period.
    have hk := MulAction.zpow_smul_mod_minimalPeriod f x k
    simp only [smul_def] at hk
    have hnn : 0 ≤ k % (Function.minimalPeriod f x : ℤ) := Int.emod_nonneg _ (by omega)
    have hlt : k % (Function.minimalPeriod f x : ℤ) < Function.minimalPeriod f x :=
      Int.emod_lt_of_pos _ (by omega)
    refine ⟨(k % (Function.minimalPeriod f x : ℤ)).toNat, by omega, ?_⟩
    rw [← hiter, Int.toNat_of_nonneg hnn, hk]
  · rintro ⟨j, -, rfl⟩
    exact ⟨j, hiter j⟩

/-- The tautological action of `M ≃ₘ^n⟮I, I⟯ M` on `M` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨fun h => Diffeomorph.ext h⟩

/-- The action of each self-diffeomorphism on `M` is continuous. -/
instance applyContinuousConstSMul : ContinuousConstSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨fun f => f.continuous⟩

/-- A subgroup of the self-diffeomorphism group acts continuously on `M` in the point, by the
generic subgroup transfer for `ContinuousConstSMul`. -/
abbrev applySubgroupContinuousConstSMul (G : Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :
    ContinuousConstSMul G M :=
  inferInstance

end Diffeomorph
