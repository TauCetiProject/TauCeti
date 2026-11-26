/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.RankOne
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Multilinear evaluation of iterated gradients

An iterated gradient `TauCeti.IteratedGradient E j` has `j` outer continuous-linear direction
slots above a vector in `E`. `TauCeti.IteratedGradient.toContinuousMultilinearMap` embeds
`IteratedGradient E j` linearly and isometrically into `E [×(j + 1)]→L[ℝ] ℝ` without assuming
completeness of `E`. Evaluating it via `TauCeti.IteratedGradient.evalTupleL` along a reversed tuple
`m ∘ Fin.rev` agrees with left-to-right multilinear evaluation
(`TauCeti.IteratedGradient.toContinuousMultilinearMap_apply`), and evaluating outer slots via
`TauCeti.IteratedGradient.applyL` appends those directions on the left
(`TauCeti.IteratedGradient.toContinuousMultilinearMap_applyL_apply`). When `E` is complete, Riesz
representation and left uncurrying assemble this evaluation into a linear isometric equivalence
`TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ` between `TauCeti.IteratedGradient E j` and
the space `E [×(j + 1)]→L[ℝ] ℝ` of scalar continuous multilinear maps, sending
`TauCeti.iteratedGradientChain f j x` to `iteratedFDeriv ℝ (j + 1) f x` without any
differentiability hypothesis. Consequently, `TauCeti.iteratedGradientChain f k x` and
`iteratedFDeriv ℝ (k + 1) f x` have the same norm (`TauCeti.norm_iteratedGradientChain`) and the
same difference norm
(`TauCeti.norm_iteratedGradientChain_sub_iteratedGradientChain_eq_norm_iteratedFDeriv_sub`).

Precomposing with a single outer contraction `TauCeti.IteratedGradient.contractL j 1 h` curries `h`
into the first argument of the corresponding continuous multilinear map
(`TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ_contractL_one`).

## Main declarations

* `TauCeti.IteratedGradient.toContinuousMultilinearMap`: linear isometric embedding of
  `IteratedGradient E j` into `E [×(j + 1)]→L[ℝ] ℝ`.
* `TauCeti.IteratedGradient.toContinuousMultilinearMap_apply`: compatibility between
  `toContinuousMultilinearMap` and `evalTupleL` along `Fin.rev`.
* `TauCeti.IteratedGradient.toContinuousMultilinearMap_applyL_apply`: evaluating
  `toContinuousMultilinearMap` after `applyL`.
* `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ`: the linear isometric equivalence
  `IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)` when `E` is complete.
* `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain`: under this
  equivalence, `iteratedGradientChain f j x` corresponds to `iteratedFDeriv ℝ (j + 1) f x`.
* `TauCeti.norm_iteratedFDeriv_iteratedGradientChain`, `TauCeti.norm_iteratedGradientChain`,
  `TauCeti.iteratedGradientChain_sub`, and
  `TauCeti.norm_iteratedGradientChain_sub_iteratedGradientChain_eq_norm_iteratedFDeriv_sub`:
  pointwise norm and difference comparisons between `iteratedGradientChain` and `iteratedFDeriv`.
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

open scoped InnerProductSpace

section InnerProductSpace

section
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Linear isometric embedding of `IteratedGradient E j` into `E [×(j + 1)]→L[ℝ] ℝ`, without
assuming completeness of `E`. -/
def toContinuousMultilinearMap :
    (j : ℕ) → IteratedGradient E j →ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)
  | 0 => (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearIsometry.comp
      (InnerProductSpace.toDualMap ℝ E)
  | j + 1 =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E)
        ℝ).symm.toLinearIsometry.comp ((toContinuousMultilinearMap j).postcomp (E := E))

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At index `0`, `toContinuousMultilinearMap` is the Riesz isometry composed with `Fin 1`
uncurrying. -/
theorem toContinuousMultilinearMap_zero :
    toContinuousMultilinearMap E 0 =
      (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearIsometry.comp
        (InnerProductSpace.toDualMap ℝ E) :=
  (rfl)

/-- Unfolding `toContinuousMultilinearMap` at a successor index curries `m 0` into `G` and
applies `toContinuousMultilinearMap E j` to the remaining directions `Fin.tail m`. -/
theorem toContinuousMultilinearMap_succ_apply (j : ℕ) (G : IteratedGradient E (j + 1))
    (m : Fin (j + 1 + 1) → E) :
    toContinuousMultilinearMap E (j + 1) G m =
      toContinuousMultilinearMap E j (G (m 0)) (Fin.tail m) := by
  simp [toContinuousMultilinearMap, continuousMultilinearCurryLeftEquiv_symm_apply,
    LinearIsometry.postcomp]

/-- Evaluating `toContinuousMultilinearMap E j G` at `m` agrees with
`evalTupleL j (m ∘ Fin.rev) G`. -/
@[simp]
theorem toContinuousMultilinearMap_apply :
    ∀ (j : ℕ) (G : IteratedGradient E j) (m : Fin (j + 1) → E),
      toContinuousMultilinearMap E j G m = evalTupleL j (m ∘ Fin.rev) G
  | 0, G, m => by
      rw [toContinuousMultilinearMap_zero]
      simp [evalTupleL_zero, real_inner_comm]
  | j + 1, G, m => by
      rw [toContinuousMultilinearMap_succ_apply, toContinuousMultilinearMap_apply j,
        evalTupleL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        Fin.init_comp_rev, Function.comp_apply, Fin.rev_last]

/-- Evaluating `toContinuousMultilinearMap E j (applyL j i m G)` at `n` agrees with evaluating
`toContinuousMultilinearMap E (j + i) G` at `Fin.append m n` (reindexed along
`j + i + 1 = i + (j + 1)`). -/
theorem toContinuousMultilinearMap_applyL_apply (j : ℕ) :
    ∀ (i : ℕ) (m : Fin i → E) (G : IteratedGradient E (j + i)) (n : Fin (j + 1) → E),
      toContinuousMultilinearMap E j (applyL j i m G) n =
        toContinuousMultilinearMap E (j + i) G (Fin.append m n ∘ Fin.cast (by omega))
  | 0, m, G, n => by
      simp only [applyL_zero, ContinuousLinearMap.id_apply, Nat.add_zero]
      congr 1
      ext r
      have h1 : Fin.cast (by omega : j + 1 = 0 + (j + 1)) r = Fin.natAdd 0 r :=
        Fin.ext (by simp)
      simp only [Function.comp_apply, h1, Fin.append_right]
  | i + 1, m, G, n => by
      have h0 :
          (Fin.append m n ∘ Fin.cast (by omega : j + (i + 1) + 1 = i + 1 + (j + 1))) 0 = m 0 := by
        have hc : Fin.cast (by omega : j + (i + 1) + 1 = i + 1 + (j + 1)) 0 =
            Fin.castAdd (j + 1) 0 := rfl
        simp only [Function.comp_apply, hc, Fin.append_left]
      have htail :
          Fin.tail (Fin.append m n ∘ Fin.cast (by omega : j + (i + 1) + 1 = i + 1 + (j + 1))) =
            Fin.append (Fin.tail m) n ∘ Fin.cast (by omega : j + i + 1 = i + (j + 1)) := by
        ext r
        rcases Nat.lt_or_ge (r : ℕ) i with hr | hr
        · have h1 : Fin.cast (by omega : j + i + 1 = i + (j + 1)) r =
              Fin.castAdd (j + 1) ⟨r, hr⟩ := rfl
          have h2 : Fin.cast (by omega : j + (i + 1) + 1 = i + 1 + (j + 1)) r.succ =
              Fin.castAdd (j + 1) ⟨r + 1, Nat.succ_lt_succ hr⟩ := rfl
          simp only [Function.comp_apply, Fin.tail, h1, h2, Fin.append_left]
          rfl
        · have h1 : Fin.cast (by omega : j + i + 1 = i + (j + 1)) r =
              Fin.natAdd i ⟨r - i, by omega⟩ := Fin.ext (by simp; omega)
          have h2 : Fin.cast (by omega : j + (i + 1) + 1 = i + 1 + (j + 1)) r.succ =
              Fin.natAdd (i + 1) ⟨r - i, by omega⟩ := Fin.ext (by simp; omega)
          simp only [Function.comp_apply, Fin.tail, h1, h2, Fin.append_right]
      refine Eq.trans ?_ (toContinuousMultilinearMap_succ_apply (j + i) G _).symm
      rw [applyL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        toContinuousMultilinearMap_applyL_apply j i (Fin.tail m) (G (m 0)) n, h0, htail]

end InnerProductSpace

section CompleteSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On a complete real inner product space, `toContinuousMultilinearMap E j` is surjective. -/
theorem toContinuousMultilinearMap_surjective :
    (j : ℕ) → Function.Surjective (toContinuousMultilinearMap E j)
  | 0 => by
      rw [toContinuousMultilinearMap_zero, LinearIsometry.coe_comp,
        ← InnerProductSpace.toLinearIsometry_toDual,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toLinearIsometry]
      exact (continuousMultilinearCurryFin1 ℝ E ℝ).symm.surjective.comp
        (InnerProductSpace.toDual ℝ E).surjective
  | j + 1 => by
      let e : IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ) :=
        LinearIsometryEquiv.ofSurjective (toContinuousMultilinearMap E j)
          (toContinuousMultilinearMap_surjective j)
      have h : ⇑(toContinuousMultilinearMap E (j + 1)) =
          ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E) ℝ).symm ∘
            ⇑((ContinuousLinearEquiv.refl ℝ E).arrowCongr e.toContinuousLinearEquiv) := by
        ext G m
        rw [Function.comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply,
          ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_symm,
          ContinuousLinearEquiv.refl_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.coe_ofSurjective, toContinuousMultilinearMap_succ_apply]
      rw [h]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E)
        ℝ).symm.surjective.comp
        ((ContinuousLinearEquiv.refl ℝ E).arrowCongr e.toContinuousLinearEquiv).surjective

/-- On a complete real inner product space, `IteratedGradient E j` is linearly isometric to the
space `E [×(j + 1)]→L[ℝ] ℝ` of scalar continuous multilinear maps in `j + 1` arguments. -/
def toContinuousMultilinearMapₗᵢ (j : ℕ) :
    IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ) :=
  LinearIsometryEquiv.ofSurjective (toContinuousMultilinearMap E j)
    (toContinuousMultilinearMap_surjective E j)

variable {E}

/-- As a function, `toContinuousMultilinearMapₗᵢ E j` agrees with
`toContinuousMultilinearMap E j`. -/
@[simp]
theorem coe_toContinuousMultilinearMapₗᵢ (j : ℕ) :
    ⇑(toContinuousMultilinearMapₗᵢ E j) = toContinuousMultilinearMap E j :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- The underlying linear isometry of `toContinuousMultilinearMapₗᵢ E j` is
`toContinuousMultilinearMap E j`. -/
@[simp]
theorem toLinearIsometry_toContinuousMultilinearMapₗᵢ (j : ℕ) :
    (toContinuousMultilinearMapₗᵢ E j).toLinearIsometry = toContinuousMultilinearMap E j :=
  LinearIsometry.ext fun G => congrFun (coe_toContinuousMultilinearMapₗᵢ j) G

/-- Evaluating `toContinuousMultilinearMapₗᵢ E j G` at `m` agrees with
`evalTupleL j (m ∘ Fin.rev) G`. -/
theorem toContinuousMultilinearMapₗᵢ_apply (j : ℕ) (G : IteratedGradient E j)
    (m : Fin (j + 1) → E) :
    toContinuousMultilinearMapₗᵢ E j G m = evalTupleL j (m ∘ Fin.rev) G := by
  rw [coe_toContinuousMultilinearMapₗᵢ, toContinuousMultilinearMap_apply]

/-- Evaluating `(toContinuousMultilinearMapₗᵢ E j).symm M` along `m` recovers
`M (m ∘ Fin.rev)`. -/
@[simp]
theorem evalTupleL_toContinuousMultilinearMapₗᵢ_symm (j : ℕ) (m : Fin (j + 1) → E)
    (M : E [×(j + 1)]→L[ℝ] ℝ) :
    evalTupleL j m ((toContinuousMultilinearMapₗᵢ E j).symm M) = M (m ∘ Fin.rev) := by
  have h : m = (m ∘ Fin.rev) ∘ Fin.rev := funext fun i => by simp
  conv_lhs => rw [h, ← toContinuousMultilinearMapₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Contracting one outer slot of `G` at `h` curries `h` into the first argument of the
corresponding continuous multilinear map. -/
theorem toContinuousMultilinearMapₗᵢ_contractL_one (j : ℕ) (h : E)
    (G : IteratedGradient E (j + 1)) :
    toContinuousMultilinearMapₗᵢ E j (contractL j 1 h G) =
      (toContinuousMultilinearMapₗᵢ E (j + 1) G).curryLeft h := by
  ext m
  rw [coe_toContinuousMultilinearMapₗᵢ, ContinuousMultilinearMap.curryLeft_apply,
    coe_toContinuousMultilinearMapₗᵢ, ← applyL_const, toContinuousMultilinearMap_applyL_apply]
  congr 1
  ext r
  cases r using Fin.cases with
  | zero =>
      have h1 : Fin.cast (by omega : j + 1 + 1 = 1 + (j + 1)) 0 = Fin.castAdd (j + 1) 0 := rfl
      simp only [Function.comp_apply, h1, Fin.append_left, Fin.cons_zero]
  | succ r =>
      have h1 : Fin.cast (by omega : j + 1 + 1 = 1 + (j + 1)) r.succ = Fin.natAdd 1 r :=
        Fin.ext (by simp; omega)
      simp only [Function.comp_apply, h1, Fin.append_right, Fin.cons_succ]

/-- Under `toContinuousMultilinearMapₗᵢ`, the classical `j`th iterated-gradient field of any
scalar function `f` at `x` is `iteratedFDeriv ℝ (j + 1) f x`. No differentiability assumption is
needed: both sides use the `fderiv` junk-value convention at each step, vanishing whenever the
preceding stage fails to be differentiable at `x`. -/
theorem toContinuousMultilinearMapₗᵢ_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x : E) :
    toContinuousMultilinearMapₗᵢ E j (iteratedGradientChain f j x) =
      iteratedFDeriv ℝ (j + 1) f x := by
  induction j generalizing x with
  | zero =>
      ext m
      rw [coe_toContinuousMultilinearMapₗᵢ, toContinuousMultilinearMap_zero,
        LinearIsometry.coe_comp, Function.comp_apply,
        ← InnerProductSpace.toLinearIsometry_toDual, LinearIsometryEquiv.coe_toLinearIsometry,
        LinearIsometryEquiv.coe_toLinearIsometry, continuousMultilinearCurryFin1_symm_apply,
        iteratedGradientChain_zero, iteratedFDeriv_one_apply, gradient,
        InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_symm_apply]
  | succ j ih =>
      have hfun : (toContinuousMultilinearMapₗᵢ E j ∘ iteratedGradientChain f j) =
          iteratedFDeriv ℝ (j + 1) f := funext ih
      ext m
      have hfd := congrArg
        (fun g : E → E [×(j + 1)]→L[ℝ] ℝ => fderiv ℝ g x (m 0) (Fin.tail m)) hfun
      rw [LinearIsometryEquiv.comp_fderiv] at hfd
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, coe_toContinuousMultilinearMapₗᵢ] at hfd
      rw [coe_toContinuousMultilinearMapₗᵢ, toContinuousMultilinearMap_succ_apply,
        iteratedGradientChain_succ, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        continuousMultilinearCurryLeftEquiv_symm_apply]
      exact hfd

/-- Evaluating `iteratedGradientChain f j x` along `m ∘ Fin.rev` gives
`iteratedFDeriv ℝ (j + 1) f x m`. -/
theorem evalTupleL_comp_rev_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x : E)
    (m : Fin (j + 1) → E) :
    evalTupleL j (m ∘ Fin.rev) (iteratedGradientChain f j x) =
      iteratedFDeriv ℝ (j + 1) f x m := by
  rw [← toContinuousMultilinearMapₗᵢ_apply, toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

end CompleteSpace

end TauCeti.IteratedGradient

namespace TauCeti

section Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking `i` further derivatives of the `k`th iterated-gradient field has the same norm as
taking `i + k + 1` derivatives of the original scalar function. No smoothness is needed. -/
theorem norm_iteratedFDeriv_iteratedGradientChain (f : E → ℝ) (i k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (iteratedGradientChain f k) x‖ =
      ‖iteratedFDeriv ℝ (i + k + 1) f x‖ := by
  induction k generalizing i with
  | zero =>
      rw [iteratedGradientChain_zero]
      -- The gradient is the inverse Riesz isometry applied to the Fréchet derivative.
      exact ((InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left
        (fderiv ℝ f) x i).trans norm_iteratedFDeriv_fderiv
  | succ k ih =>
      rw [iteratedGradientChain_succ, norm_iteratedFDeriv_fderiv]
      exact (ih (i + 1)).trans (congrArg
        (fun j => ‖iteratedFDeriv ℝ (j + 1) f x‖) (by omega))

/-- The nested iterated-gradient field has the same norm as the corresponding multilinear
derivative of the scalar function. -/
@[simp]
theorem norm_iteratedGradientChain (f : E → ℝ) (k : ℕ) (x : E) :
    ‖iteratedGradientChain f k x‖ = ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
  rw [← (IteratedGradient.toContinuousMultilinearMapₗᵢ E k).norm_map,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

/-- Iterated-gradient fields through order `k + 1` preserve subtraction of scalar functions
that are `C^{k+1}` at the point of evaluation. -/
@[simp]
theorem iteratedGradientChain_sub {f g : E → ℝ} {x : E}
    (k : ℕ) (hf : ContDiffAt ℝ (k + 1) f x) (hg : ContDiffAt ℝ (k + 1) g x) :
    iteratedGradientChain (f - g) k x =
      iteratedGradientChain f k x - iteratedGradientChain g k x := by
  refine (IteratedGradient.toContinuousMultilinearMapₗᵢ E k).injective ?_
  rw [map_sub, IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain]
  exact fun_iteratedFDeriv_sub_apply (hf.of_le (by simp)) (hg.of_le (by simp))

/-- The order-`k + 1` iterated-gradient fields of two scalar functions have the same difference
norm at any point as their multilinear derivatives. This identifies the error seminorms in smooth
approximation. -/
theorem norm_iteratedGradientChain_sub_iteratedGradientChain_eq_norm_iteratedFDeriv_sub
    {f g : E → ℝ} {x : E} (k : ℕ) :
    ‖iteratedGradientChain f k x - iteratedGradientChain g k x‖ =
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) g x‖ := by
  rw [← (IteratedGradient.toContinuousMultilinearMapₗᵢ E k).norm_map, map_sub,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

end Classical

end TauCeti
