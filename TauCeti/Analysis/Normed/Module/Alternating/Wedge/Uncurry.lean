/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.GroupTheory.Perm.Basic

/-!
# Alternatization of wedges with a linear family of forms

For a continuous linear family `f` of `k`-forms, a fixed `l`-form `ψ` and a fixed continuous
bilinear pairing `μ`, alternatizing the family `v ↦ f v ∧ ψ` gives `alternatizeUncurryFin f ∧ ψ`,
and alternatizing `v ↦ φ ∧ g v` for a fixed `k`-form `φ` gives
`(-1) ^ k • φ ∧ alternatizeUncurryFin g`. Applied to the derivatives of two families of forms,
these are the two terms of the Leibniz rule `d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ` for the
exterior derivative. The degrees `k + 1 + l` and `k + (l + 1)` are identified with `k + l + 1`
by `Fin.cast`.

Both sides are expanded as signed sums over permutations. The alternatization of `f` is itself
such a sum (`ContinuousAlternatingMap.factorial_smul_alternatizeUncurryFin_apply`), and the nested
alternatization is absorbed into the outer one
(`TauCeti.sum_sign_smul_sum_sign_smul_eq_card_nsmul`). The wedge normalization follows John M. Lee,
*Introduction to Smooth Manifolds*, second edition, Chapter 14.

## Main declarations

* `ContinuousAlternatingMap.alternatizeUncurryFin_pairedWedgeCLM_flip_comp_apply`: the identity
  for `v ↦ f v ∧ ψ`.
* `ContinuousAlternatingMap.alternatizeUncurryFin_pairedWedgeCLM_comp_apply`: the identity for
  `v ↦ φ ∧ g v`.
-/

public section

namespace ContinuousAlternatingMap

open Equiv TauCeti

variable {E F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ}

/-- The paired wedge of an alternatized linear family with a fixed form, as a single signed
permutation sum. -/
private theorem pairedWedge_alternatizeUncurryFin_left_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) (w : Fin (k + 1 + l) → E) :
    pairedWedge μ μ.continuous₂ (alternatizeUncurryFin f) ψ w =
      ((k.factorial : ℝ) * l.factorial)⁻¹ • ∑ σ : Perm (Fin (k + 1 + l)), Perm.sign σ •
        μ (f (w (σ (Fin.castAdd l 0))) (fun i => w (σ (Fin.castAdd l i.succ))))
          (ψ (fun j => w (σ (Fin.natAdd (k + 1) j)))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun ρ => finSumFinEquiv.permCongr (Perm.sumCongr ρ (1 : Perm (Fin l))))
    (fun ρ => by simp [Perm.sign_sumCongr])
    (fun σ : Perm (Fin (k + 1 + l)) =>
      μ (f (w (σ (Fin.castAdd l 0))) (fun i => w (σ (Fin.castAdd l i.succ))))
        (ψ (fun j => w (σ (Fin.natAdd (k + 1) j)))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [pairedWedge_apply, alternatizeUncurryFin_apply_eq_inv_factorial_smul_sum,
    map_smul, _root_.map_sum, _root_.smul_apply, FunLike.coe_sum,
    Finset.sum_apply, Units.smul_def, _root_.map_zsmul, FunLike.coe_smul,
    Pi.smul_apply]
  simp only [Units.smul_def] at key
  simp_rw [smul_comm _ (k.factorial : ℝ)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Alternatizing the linear family `v ↦ f v ∧ ψ` gives the wedge of the alternatization of `f`
with `ψ`. This is the algebraic identity behind the first term of the Leibniz rule
`d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ`. -/
theorem alternatizeUncurryFin_pairedWedgeCLM_flip_comp_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) (v : Fin (k + l + 1) → E) :
    alternatizeUncurryFin (((pairedWedgeCLM μ).flip ψ).comp f) v =
      pairedWedge μ μ.continuous₂ (alternatizeUncurryFin f) ψ
        (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) := by
  -- Both sides are `(k! l!)⁻¹` times a signed sum over all permutations: the left side is
  -- expanded along the entry fed to `f`, and the right side is reindexed along `Fin.cast`.
  have hcons := sum_sign_smul_comp_eq_sum_cons_removeNth
    (fun u : Fin (k + l + 1) → E => μ (f (u 0) (fun i => u (Fin.castAdd l i).succ))
      (ψ (fun j => u (Fin.natAdd k j).succ))) v
  simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ] at hcons
  rw [pairedWedge_alternatizeUncurryFin_left_apply, alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    pairedWedgeCLM_apply, pairedWedge_apply, Function.comp_apply]
  simp_rw [smul_comm _ ((k.factorial : ℝ) * l.factorial)⁻¹, ← Finset.smul_sum, ← hcons]
  congr 1
  refine Fintype.sum_equiv (finCongr (show k + l + 1 = k + 1 + l by omega)).permCongr _ _
    fun σ => ?_
  have h₀ : Fin.cast (show k + 1 + l = k + l + 1 by omega) (Fin.castAdd l 0) = 0 := Fin.ext rfl
  have h₁ (i : Fin k) : Fin.cast (show k + 1 + l = k + l + 1 by omega) (Fin.castAdd l i.succ) =
      (Fin.castAdd l i).succ := Fin.ext rfl
  have h₂ (j : Fin l) : Fin.cast (show k + 1 + l = k + l + 1 by omega) (Fin.natAdd (k + 1) j) =
      (Fin.natAdd k j).succ := Fin.ext (by simp; omega)
  simp [h₀, h₁, h₂, Perm.sign_permCongr]

/-- The paired wedge of a fixed form with an alternatized linear family, as a single signed
permutation sum. -/
private theorem pairedWedge_alternatizeUncurryFin_right_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (g : E →L[ℝ] E [⋀^Fin l]→L[ℝ] F₂) (w : Fin (k + (l + 1)) → E) :
    pairedWedge μ μ.continuous₂ φ (alternatizeUncurryFin g) w =
      ((k.factorial : ℝ) * l.factorial)⁻¹ • ∑ σ : Perm (Fin (k + (l + 1))), Perm.sign σ •
        μ (φ (fun i => w (σ (Fin.castAdd (l + 1) i))))
          (g (w (σ (Fin.natAdd k 0))) (fun j => w (σ (Fin.natAdd k j.succ)))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun ρ => finSumFinEquiv.permCongr (Perm.sumCongr (1 : Perm (Fin k)) ρ))
    (fun ρ => by simp [Perm.sign_sumCongr])
    (fun σ : Perm (Fin (k + (l + 1))) =>
      μ (φ (fun i => w (σ (Fin.castAdd (l + 1) i))))
        (g (w (σ (Fin.natAdd k 0))) (fun j => w (σ (Fin.natAdd k j.succ)))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [pairedWedge_apply, alternatizeUncurryFin_apply_eq_inv_factorial_smul_sum,
    map_smul, _root_.map_sum, Units.smul_def, _root_.map_zsmul]
  simp only [Units.smul_def] at key
  simp_rw [smul_comm _ (l.factorial : ℝ)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Alternatizing the linear family `v ↦ φ ∧ g v` gives `(-1) ^ k` times the wedge of `φ` with the
alternatization of `g`, for a `k`-form `φ`. This is the algebraic identity behind the second term
of the Leibniz rule `d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ`. -/
theorem alternatizeUncurryFin_pairedWedgeCLM_comp_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (g : E →L[ℝ] E [⋀^Fin l]→L[ℝ] F₂) (v : Fin (k + l + 1) → E) :
    alternatizeUncurryFin ((pairedWedgeCLM μ φ).comp g) v =
      (-1 : ℝ) ^ k • pairedWedge μ μ.continuous₂ φ (alternatizeUncurryFin g)
        (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  -- Both sides are `(k! l!)⁻¹` times a signed sum over all permutations. The entry fed to `g`
  -- sits at slot `k` on the right side, so expanding the left side along it costs `(-1) ^ k`.
  have hkl : k + (l + 1) = k + l + 1 := by omega
  set p : Fin (k + l + 1) := Fin.cast hkl (Fin.natAdd k 0) with hp
  have hcast₁ (i : Fin k) : Fin.cast hkl (Fin.castAdd (l + 1) i) = p.succAbove (Fin.castAdd l i) :=
    Fin.ext (by simp [hp])
  have hcast₂ (j : Fin l) : Fin.cast hkl (Fin.natAdd k j.succ) = p.succAbove (Fin.natAdd k j) :=
    Fin.ext (by simp [hp])
  have hins := sum_sign_smul_comp_eq_sum_insertNth_removeNth
    (fun u : Fin (k + l + 1) → E => μ (φ (fun i => u (Fin.cast hkl (Fin.castAdd (l + 1) i))))
      (g (u p) (fun j => u (Fin.cast hkl (Fin.natAdd k j.succ))))) v p
  simp only [Function.comp_apply, hcast₁, hcast₂, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove] at hins
  rw [pairedWedge_alternatizeUncurryFin_right_apply, alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.comp_apply, pairedWedgeCLM_apply, pairedWedge_apply,
    Function.comp_apply]
  have hpk : (p : ℕ) = k := by simp [hp]
  have hsum : ∑ j : Fin (k + l + 1), (-1 : ℤ) ^ (j : ℕ) • ∑ τ : Perm (Fin (k + l)), Perm.sign τ •
        μ (φ fun i => j.removeNth v (τ (Fin.castAdd l i)))
          (g (v j) fun j' => j.removeNth v (τ (Fin.natAdd k j'))) =
      (-1 : ℤ) ^ k • ∑ σ : Perm (Fin (k + l + 1)), Perm.sign σ •
        μ (φ fun i => v (σ (p.succAbove (Fin.castAdd l i))))
          (g (v (σ p)) fun j => v (σ (p.succAbove (Fin.natAdd k j)))) := by
    rw [hins, hpk, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  simp_rw [smul_comm _ ((k.factorial : ℝ) * l.factorial)⁻¹, ← Finset.smul_sum]
  rw [hsum, ← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  congr 2
  refine Fintype.sum_equiv (finCongr hkl.symm).permCongr _ _ fun σ => ?_
  simp only [permCongr_apply, Perm.sign_permCongr, finCongr_apply, finCongr_symm,
    Fin.cast_eq_self]
  -- The two sides agree slot by slot: `p.succAbove` realizes the two block inclusions.
  congr 4 <;> funext i <;> congr 2
  exacts [(hcast₁ i).symm, (hcast₂ i).symm]

end ContinuousAlternatingMap
