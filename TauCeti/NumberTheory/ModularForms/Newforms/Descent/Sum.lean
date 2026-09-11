/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Invariance
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Action

import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Units

/-!
# The descent slash sum is `Γ₀(N / p)`-invariant

`Newforms/Descent/Action.lean` shows that, at a prime `p` with `p² ∣ N`, right multiplication by
`γ ∈ Γ₀(N / p)` permutes the family `descendMatrix p N` up to `Γ₀(N)`. This file draws the
consequence that the descent consumes: if `f` transforms under `Γ₀(N)` by a scalar, the sum of
the slashes of `f` along the family transforms under `Γ₀(N / p)` by that scalar; in particular
the sum is `Γ₀(N / p)`-invariant whenever `f` is `Γ₀(N)`-invariant.

## Main definitions

* `TauCeti.descendSlash`: `∑ v, f ∣[k] descendMatrix p N v`, the descent slash sum.

## Main results

* `TauCeti.descendSlash_zero`, `TauCeti.descendSlash_add`, `TauCeti.descendSlash_smul`:
  `f ↦ descendSlash k p N f` is linear.
* `TauCeti.descendSlash_slash_mapGL_of_mem_Gamma0`: for `p² ∣ N` and `γ ∈ Γ₀(N / p)`, if
  `f ∣[k] δ = u • f` for every `δ ∈ Γ₀(N)` with the lower-right entry of `γ` modulo `N / p`, then
  `descendSlash k p N f ∣[k] γ = u • descendSlash k p N f`, for a scalar `u` from any `α` acting
  compatibly on `ℂ`.
* `TauCeti.descendSlash_slash_mapGL_eq_self_of_mem_Gamma0`: its case `u = 1` — the descent sum
  of a `Γ₀(N)`-invariant function is `Γ₀(N / p)`-invariant.
* `TauCeti.descendSlash_slash_mapGL_of_nebentypus`: if `f` transforms under `Γ₀(N)` by `χ`, and
  `χ` is the pull-back of `χ₀` modulo `N / p`, then `descendSlash k p N f` transforms under
  `Γ₀(N / p)` by `χ₀` — the descent lowers the level of the nebentypus.

## Scope

Only the `p² ∣ N` case. The behaviour at cusps is not claimed.

Corresponds to the `p² ∣ N` case of `miyake_hecke_descend_char` in the AINTLIB
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

/-- **The descent slash sum is `Γ₀(N / p)`-equivariant at `p² ∣ N`.** If `f ∣[k] δ = u • f` for
every `δ ∈ Γ₀(N)` with the same lower-right entry modulo `N / p` as `γ ∈ Γ₀(N / p)`, then
`descendSlash k p N f ∣[k] γ = u • descendSlash k p N f`. With `u = 1` this is the
`Γ₀(N / p)`-invariance of the descent sum of a `Γ₀(N)`-invariant function; with `u` a character
value it is the nebentypus transport `descendSlash_slash_mapGL_of_nebentypus`. The scalar may
come from any `α` acting compatibly on `ℂ`, as in `descendSlash_smul`. -/
theorem descendSlash_slash_mapGL_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpsq : p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p)) {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ]
    {f : ℍ → ℂ} {u : α}
    (hf : ∀ δ ∈ Gamma0 N, ((δ 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) →
      f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = u • f) :
    descendSlash k p N f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = u • descendSlash k p N f := by
  rw [descendSlash_def, SlashAction.sum_slash, Finset.smul_sum]
  have key : ∀ v : Fin (descendMatrixCount p N),
      (f ∣[k] descendMatrix p N v) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)
        = u • (f ∣[k] descendMatrix p N (descendShift p N hpsq γ v)) := fun v ↦ by
    obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_descendMatrix_mul p N hpsq hγ v
    have hα11 : ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) := by
      rw [hd]
      push_cast
      rw [Gamma0_mem.mp hγ]
      ring
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf α hα hα11,
      ModularForm.smul_slash_of_det_pos k (descendMatrix_det_pos p N _) f u]
  rw [Finset.sum_congr rfl fun v _ ↦ key v]
  exact Fintype.sum_bijective (descendShift p N hpsq γ)
    (descendShift_bijective hpsq
      (Gamma0_le_Gamma0_of_dvd (Nat.dvd_div_of_mul_dvd (by rwa [← pow_two])) hγ))
    (fun v ↦ u • (f ∣[k] descendMatrix p N (descendShift p N hpsq γ v)))
    (fun v ↦ u • (f ∣[k] descendMatrix p N v)) fun _ ↦ rfl

/-- **The descent slash sum is `Γ₀(N / p)`-invariant at `p² ∣ N`**: if `f` is invariant under
`Γ₀(N)`, then `descendSlash k p N f` is invariant under the larger group `Γ₀(N / p)` — the
descent lowers the level. The case `u = 1` of `descendSlash_slash_mapGL_of_mem_Gamma0`. -/
theorem descendSlash_slash_mapGL_eq_self_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpsq : p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p)) {f : ℍ → ℂ}
    (hf : ∀ δ ∈ Gamma0 N, f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = f) :
    descendSlash k p N f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = descendSlash k p N f := by
  simpa using descendSlash_slash_mapGL_of_mem_Gamma0 k hpsq hγ (u := (1 : ℂ))
    fun δ hδ _ ↦ by rw [hf δ hδ, one_smul]

/-- **The descent sum lowers the level of the nebentypus at `p² ∣ N`.** If `f` transforms under
`Γ₀(N)` by `χ`, and `χ` is the pull-back of a character `χ₀` modulo `N / p` (the hypothesis
`hcomp`, in the shape `cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace` takes), then
`descendSlash k p N f` transforms under `Γ₀(N / p)` by `χ₀`. -/
theorem descendSlash_slash_mapGL_of_nebentypus (k : ℤ) [NeZero p] (hpsq : p ^ 2 ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp
      (ZMod.unitsMap (Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hpsq))))
    (γ : ↥(Gamma0 (N / p))) {f : ℍ → ℂ}
    (hf : ∀ δ : ↥(Gamma0 N), f ∣[k] (mapGL ℝ (δ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (↑(χ ((Gamma0Map N).toHomUnits δ)) : ℂ) • f) :
    descendSlash k p N f ∣[k] (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (↑(χ₀ ((Gamma0Map (N / p)).toHomUnits γ)) : ℂ) • descendSlash k p N f := by
  apply descendSlash_slash_mapGL_of_mem_Gamma0 k hpsq γ.2
  intro δ hδ hd
  have hdvd : N / p ∣ N := Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hpsq)
  have hmap : ZMod.unitsMap hdvd ((Gamma0Map N).toHomUnits ⟨δ, hδ⟩) =
      (Gamma0Map (N / p)).toHomUnits γ := by
    rw [← Gamma0Map_toHomUnits_of_dvd hdvd ⟨δ, hδ⟩ (Gamma0_le_Gamma0_of_dvd hdvd hδ)]
    exact Units.ext hd
  rw [hf ⟨δ, hδ⟩, hcomp, MonoidHom.comp_apply, hmap]

end TauCeti
