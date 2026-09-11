/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Action

/-!
# The descent slash sum is `Γ₀(N / p)`-invariant

`Newforms/Descent/Action.lean` shows that, at a prime `p` with `p² ∣ N`, right multiplication by
`γ ∈ Γ₀(N / p)` permutes the family `descendMatrix p N` up to `Γ₀(N)`. This file draws the
consequence that the descent consumes: the sum of the slashes of `f` along the family is
`Γ₀(N / p)`-invariant whenever `f` is `Γ₀(N)`-invariant.

## Main definitions

* `TauCeti.descendSlash`: `∑ v, f ∣[k] descendMatrix p N v`, the descent slash sum.

## Main results

* `TauCeti.descendSlash_zero`, `TauCeti.descendSlash_add`, `TauCeti.descendSlash_smul`:
  `f ↦ descendSlash k p N f` is linear.
* `TauCeti.descendSlash_slash_mapGL_of_mem_Gamma0`: for `p² ∣ N`, if `f` is `Γ₀(N)`-invariant
  then `descendSlash k p N f` is `Γ₀(N / p)`-invariant.

## Scope

Only the `p² ∣ N` case, and only invariance: the factorisation in `Action.lean` records that
the witness lies in `Γ₀(N)` but not its lower-right entry, so the nebentypus transport that
`HeckeSlash/UpperTri/Invariance.lean` derives for the upper-triangular sum is not available here
yet. The behaviour at cusps is likewise not claimed.

Corresponds to the `Γ₀(N / p)`-slash step of `miyake_hecke_descend_char` in the AINTLIB
`LeanModularForms` project (`LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {p N : ℕ}

/-- **The descent slash sum**: `∑ v, f ∣[k] descendMatrix p N v`, over the whole family. -/
noncomputable def descendSlash (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ v : Fin (descendMatrixCount p N), f ∣[k] descendMatrix p N v

/-- The defining equation of `descendSlash`: the sum of the slashes of `f` along the family. -/
lemma descendSlash_def (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) :
    descendSlash k p N f = ∑ v : Fin (descendMatrixCount p N), f ∣[k] descendMatrix p N v :=
  (rfl)

/-- The value of the descent slash sum at a point: the sum of the slashed values. -/
lemma descendSlash_apply (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) (τ : ℍ) :
    descendSlash k p N f τ
      = ∑ v : Fin (descendMatrixCount p N), (f ∣[k] descendMatrix p N v) τ := by
  rw [descendSlash_def, Finset.sum_apply]

/-- The descent slash sum sends the zero function to zero. -/
@[simp] lemma descendSlash_zero (k : ℤ) (p N : ℕ) [NeZero p] : descendSlash k p N 0 = 0 := by
  rw [descendSlash_def]
  exact Finset.sum_eq_zero fun v _ ↦ SlashAction.zero_slash k (descendMatrix p N v)

/-- The descent slash sum is additive in `f`, since each slash is. -/
@[simp] lemma descendSlash_add (k : ℤ) (p N : ℕ) [NeZero p] (f g : ℍ → ℂ) :
    descendSlash k p N (f + g) = descendSlash k p N f + descendSlash k p N g := by
  rw [descendSlash_def, descendSlash_def, descendSlash_def, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ ↦ SlashAction.add_slash k (descendMatrix p N v) f g

/-- **Scalars pass through the descent slash sum.** With `descendSlash_add` and
`descendSlash_zero` this is the linearity of `f ↦ descendSlash k p N f`; the scalar generality
matches `ModularForm.smul_slash_of_det_pos`, which applies because every member of the family has
positive determinant (`descendMatrix_det_pos`). -/
@[simp] lemma descendSlash_smul (k : ℤ) (p N : ℕ) [NeZero p] {α : Type*} [DistribSMul α ℂ]
    [IsScalarTower α ℂ ℂ] (c : α) (f : ℍ → ℂ) :
    descendSlash k p N (c • f) = c • descendSlash k p N f := by
  rw [descendSlash_def, descendSlash_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun v _ ↦
    ModularForm.smul_slash_of_det_pos k (descendMatrix_det_pos p N v) f c

/-- **The descent slash sum is `Γ₀(N / p)`-invariant at `p² ∣ N`.** If `f` is invariant under
`Γ₀(N)`, then `descendSlash k p N f` is invariant under the larger group `Γ₀(N / p)`: the descent
lowers the level. -/
theorem descendSlash_slash_mapGL_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpsq : p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p)) {f : ℍ → ℂ}
    (hf : ∀ α ∈ Gamma0 N, f ∣[k] (mapGL ℝ α : GL (Fin 2) ℝ) = f) :
    descendSlash k p N f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = descendSlash k p N f := by
  rw [descendSlash_def, SlashAction.sum_slash]
  have key : ∀ v : Fin (descendMatrixCount p N),
      (f ∣[k] descendMatrix p N v) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)
        = f ∣[k] descendMatrix p N (descendShift p N hpsq γ v) := fun v ↦ by
    obtain ⟨α, hα, -, hmul⟩ := exists_mem_Gamma0_descendMatrix_mul p N hpsq hγ v
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf α hα]
  rw [Finset.sum_congr rfl fun v _ ↦ key v]
  exact Fintype.sum_bijective (descendShift p N hpsq γ)
    (descendShift_bijective hpsq
      (Gamma0_le_Gamma0_of_dvd (Nat.dvd_div_of_mul_dvd (by rwa [← pow_two])) hγ))
    (fun v ↦ f ∣[k] descendMatrix p N (descendShift p N hpsq γ v))
    (fun v ↦ f ∣[k] descendMatrix p N v) fun _ ↦ rfl

end TauCeti
