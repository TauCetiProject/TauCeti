/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.LevelRaise
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum

/-!
# The descent of a level-raise

For a prime `p ∣ N` and `g` slash-invariant of level `Γ₁(N / p)`, every member of the descent
family `descendMatrix p N` slashes the level-raise `V_p g = p^(1-k) • (g ∣[k] scaleGL p)` (a form
of level `Γ₁(N)`) back to `p⁻¹ • g`: the upper-triangular members `!![1, b; 0, p]` because
`(V_p g) ((τ + b) / p) = g (τ + b) = g τ` (`smul_slash_scaleGL_slash_upperTriRep`), and the extra
member because its `Γ₀(N / p)` factor lies in `Γ(N / p)`. So the descent slash sum of `V_p g` is
the scalar multiple `(|family| / p) • g`, with `|family| = p` when `p² ∣ N` and `p + 1`
otherwise. This is the computation behind the coefficient formula of the descent in Miyake's
proof of Lemma 4.6.14.

## Main results

* `TauCeti.smul_slash_scaleGL_slash_descendMatrix`: every member of the family slashes
  `V_p g = p^(1-k) • (g ∣[k] scaleGL p)` to `p⁻¹ • g`, for `g` slash-invariant of level
  `Γ₁(N / p)`.
* `TauCeti.descendSlash_smul_slash_scaleGL`: hence
  `descendSlash k p N (p^(1-k) • (g ∣[k] scaleGL p)) = (|family| / p) • g`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`
(`V_p_slash_descendCoset`) and `StrongMultiplicityOne/DescentCharSpace.lean`
(`slash_sum_V_p_pointwise_eq_smul_g_low`). The source's `modularFormLevelRaise` is this
repository's `ModularForm.levelRaise`, and its `descendCosetList` the family `descendMatrix`;
the statements are re-proved on those.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {p N : ℕ} (k : ℤ)

/-- **Every member of the descent family slashes a level-raise back to the form.** For `p ∣ N`
prime and `g` slash-invariant of level `Γ₁(N / p)`, with `V_p g = p^(1-k) • (g ∣[k] scaleGL p)`,
`(V_p g) ∣[k] descendMatrix p N v = p⁻¹ • g` for every `v`. -/
theorem smul_slash_scaleGL_slash_descendMatrix (hp : p.Prime) (hpN : p ∣ N) {F : Type*}
    [FunLike F ℍ ℂ] [SlashInvariantFormClass F ((Gamma1 (N / p)).map (mapGL ℝ)) k] (g : F)
    (v : Fin (descendMatrixCount p N)) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ((p : ℂ) ^ (1 - k) • (⇑g ∣[k] scaleGL p)) ∣[k] descendMatrix p N v = (p : ℂ)⁻¹ • ⇑g := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases lt_or_ge v.val p with hv | hv
  · rw [descendMatrix_of_lt hv, ← ModularForm.rat_slash,
      smul_slash_scaleGL_slash_upperTriRep k (one_mem_strictPeriods_Gamma1_map _)]
  · have hpsq : ¬ p ^ 2 ∣ N := fun h ↦ by
      have h1 := descendMatrixCount_of_sq_dvd h
      have h2 := v.isLt
      omega
    have hmem : descendExtraGamma p N ∈ Gamma1 (N / p) :=
      Gamma_le_Gamma1 (N / p)
        (Gamma_mem'.mpr (descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq))
    rw [descendMatrix_of_le hv, SlashAction.slash_mul, ← ModularForm.rat_slash,
      smul_slash_scaleGL_slash_upperTriRep k (one_mem_strictPeriods_Gamma1_map _),
      _root_.ModularForm.smul_slash, σ_mapGL_real_eq_refl, ContinuousAlgEquiv.refl_apply,
      SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)]

/-- **The descent of a level-raise is a multiple of the form.** For `p ∣ N` prime and `g`
slash-invariant of level `Γ₁(N / p)`, with `V_p g = p^(1-k) • (g ∣[k] scaleGL p)`,
`descendSlash k p N (V_p g) = (|family| / p) • g`. This is the coefficient formula of the
descent on a level-raise, the input to Miyake's Lemma 4.6.14. -/
theorem descendSlash_smul_slash_scaleGL (hp : p.Prime) (hpN : p ∣ N) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 (N / p)).map (mapGL ℝ)) k] (g : F) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    descendSlash k p N ((p : ℂ) ^ (1 - k) • (⇑g ∣[k] scaleGL p)) =
      ((descendMatrixCount p N : ℂ) / p) • ⇑g := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [descendSlash_def, Finset.sum_congr rfl fun v _ ↦ smul_slash_scaleGL_slash_descendMatrix k hp
    hpN g v, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, div_eq_mul_inv]

end TauCeti
