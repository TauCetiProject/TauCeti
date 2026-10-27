/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.GroupTheory.Perm.Basic

/-!
# Alternatization and interior products

For a continuous linear map `f : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F` and a vector `y`, the two ways
of combining the alternatization `ContinuousAlternatingMap.alternatizeUncurryFin` with the
interior product `ι_y = ContinuousAlternatingMap.curryLeft · y` add up to evaluation at `y`:

`alternatizeUncurryFin (ι_y ∘ f) + ι_y (alternatizeUncurryFin f) = f y`.

Applied to the derivative `f = Dω(x)` of a differential form, this is the pointwise form of
Cartan's formula `d ι_y + ι_y d = L_y` for the constant vector field `y`. It is the algebraic
identity behind the homotopy formula of the Poincaré lemma.

Up to the factor `n!`, `alternatizeUncurryFin f` is also the signed sum over all permutations of
the uncurried map `v ↦ f (v 0) (Fin.tail v)`. This expresses it as an alternatization and lets it
be combined with other permutation sums, such as those defining wedge products.

## Main declarations

* `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft`: the identity
  above.
* `ContinuousAlternatingMap.alternatizeUncurryFin_compContinuousLinearMap`: alternatization
  commutes with pullback along a continuous linear map.
* `ContinuousAlternatingMap.factorial_smul_alternatizeUncurryFin_apply`: the permutation-sum
  formula.
* `ContinuousAlternatingMap.alternatizeUncurryFin_apply_eq_inv_factorial_smul_sum`: the same
  formula normalized by `n!`, in characteristic zero.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- Alternatizing the interior product with `y` of a family of forms, plus the interior product
with `y` of its alternatization, is evaluation of the family at `y`. This is the pointwise
constant-coefficient case of Cartan's formula `d ι_y + ι_y d = L_y`. -/
theorem alternatizeUncurryFin_curryLeft_comp_add_curryLeft
    (f : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F) (y : E) :
    alternatizeUncurryFin ((curryLeftLI (𝕜 := 𝕜) (E := E) (F := F)).toContinuousLinearMap.flip y ∘L
      f) + (alternatizeUncurryFin f).curryLeft y = f y := by
  ext v
  have hremove (i : Fin (n + 1)) :
      Fin.removeNth i.succ (Matrix.vecCons y v) = Matrix.vecCons y (Fin.removeNth i v) := by
    funext j
    rw [Fin.removeNth_apply, Matrix.vecCons, Matrix.vecCons, ← Fin.cons_comp_succ_succAbove y v i,
      Function.comp_apply]
  rw [add_apply, curryLeft_apply_apply, alternatizeUncurryFin_apply, alternatizeUncurryFin_apply,
    Fin.sum_univ_succ (n := n + 1)]
  simp [hremove, pow_succ]

/-- Alternatization commutes with pullback along a continuous linear map `L`: pulling back the
alternatization of `f` is alternatizing `f` with its argument and its values pulled back. Applied
to the derivative of a differential form, this is the pointwise linear case of the naturality of
the exterior derivative. -/
theorem alternatizeUncurryFin_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (L : E' →L[𝕜] E) :
    (alternatizeUncurryFin f).compContinuousLinearMap L =
      alternatizeUncurryFin (compContinuousLinearMapCLM L ∘L f ∘L L) := by
  ext v
  simp +unfoldPartialApp [alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]

/-- Up to the factor `n!`, the alternatization of a linear family of `n`-forms is the signed sum
over all permutations of the uncurried map: the entry moved to the first slot is fed to `f`, and
the remaining entries to the resulting form. -/
theorem factorial_smul_alternatizeUncurryFin_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F)
    (v : Fin (n + 1) → E) :
    n.factorial • alternatizeUncurryFin f v =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        Equiv.Perm.sign σ • f (v (σ 0)) (fun i => v (σ i.succ)) := by
  -- Expand the signed sum along the entry moved to the first slot; each inner sum over
  -- rearrangements of the remaining entries contributes `n!` copies of the same term.
  have h := TauCeti.sum_sign_smul_comp_eq_sum_cons_removeNth
    (fun u => f (u 0) (fun i => u i.succ)) v
  have hperm (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
      f (v j) (fun i => j.removeNth v (τ i)) = Equiv.Perm.sign τ • f (v j) (j.removeNth v) := by
    simpa [Function.comp_def] using (f (v j)).toAlternatingMap.map_perm (j.removeNth v) τ
  simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ, hperm, smul_smul,
    Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin] at h
  rw [h, alternatizeUncurryFin_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm]

/-- In characteristic zero, the alternatization of a linear family of `n`-forms is the signed sum
over all permutations of the uncurried map, normalized by `n!`. -/
theorem alternatizeUncurryFin_apply_eq_inv_factorial_smul_sum [CharZero 𝕜]
    (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 1) → E) :
    alternatizeUncurryFin f v = (n.factorial : 𝕜)⁻¹ •
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        Equiv.Perm.sign σ • f (v (σ 0)) (fun i => v (σ i.succ)) := by
  rw [← factorial_smul_alternatizeUncurryFin_apply, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

end ContinuousAlternatingMap
