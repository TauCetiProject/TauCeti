/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Comul
public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic

/-!
# Translation on analytic stages and locally analytic functions

Evaluating the outer stage of the curried stage comultiplication
`TauCeti.AnalyticStage.comulCurried` at a fixed `x : ℤ_p` gives the isometric translation
`TauCeti.AnalyticStage.translate S x : LA_h(E) ≃ₗᵢ[S] LA_h(E)` satisfying
`eval S (translate S x c) y = eval S c (x + y)` (`AnalyticStage.eval_translate`). By
cocommutativity (`AnalyticStage.congrLeft_prodComm_comul`), evaluating the inner stage slice at `x`
recovers the coordinates of `translate S x` (`AnalyticStage.eval_comulCurried_apply`). Translation
commutes with bounded coefficient maps (`AnalyticStage.translate_compLeft`) and with stage
transitions (`AnalyticStage.transition_translate`, `AnalyticStage.transitionLE_translate`), and
descends via `Module.DirectLimit.congr` to the linear equivalence
`TauCeti.LocallyAnalytic.translate S x : LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)`.

Structural identities for `translate` (`translate_zero`, `translate_add`) follow directly from the
counit (`eval_apply_zero`, `comulCurried_apply_zero`) and coassociativity
(`comulCurried_comulCurried`) for arbitrary complete ultrametric `ℤ_p`-modules `E` (including
torsion and positive-characteristic coefficients).

## Main definitions

* `TauCeti.AnalyticStage.translate S x`: isometric translation `LA_h(E) ≃ₗᵢ[S] LA_h(E)` by `x`.
* `TauCeti.LocallyAnalytic.translate S x`: translation `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` by `x`.

## Main results

* `TauCeti.AnalyticStage.translate_eq_eval_comulCurried`,
  `TauCeti.AnalyticStage.eval_comulCurried_apply`: relation with `comulCurried`.
* `TauCeti.AnalyticStage.eval_translate`, `TauCeti.AnalyticStage.translate_zero`,
  `TauCeti.AnalyticStage.translate_add`, `TauCeti.AnalyticStage.translate_symm`,
  `TauCeti.AnalyticStage.translate_eq_translate_padicInt`,
  `TauCeti.AnalyticStage.translate_compLeft`, `TauCeti.AnalyticStage.transition_translate`,
  `TauCeti.AnalyticStage.transitionLE_translate`: evaluation, group law, scalar independence,
  naturality, and transition compatibility of stage translation.
* `TauCeti.LocallyAnalytic.translate_ofStage`, `TauCeti.LocallyAnalytic.eval_translate`,
  `TauCeti.LocallyAnalytic.translate_zero`, `TauCeti.LocallyAnalytic.translate_add`,
  `TauCeti.LocallyAnalytic.translate_symm`: corresponding properties on `LA(ℤ_p, E)`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Translation on analytic stages -/

namespace AnalyticStage

section Translate

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private noncomputable def translateCLM (x : ℤ_[p]) :
    AnalyticStage p h E →L[S] AnalyticStage p h E :=
  (ContinuousMap.evalCLM S x).comp ((eval S).comp (comulCurried S))

private theorem translateCLM_apply (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S x c = eval S (comulCurried S c) x :=
  (rfl)

private theorem translateCLM_eq_translateCLM_padicInt (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S x c = translateCLM ℤ_[p] x c := by
  simp only [translateCLM_apply, comulCurried_eq_comulCurried_padicInt S c,
    eval_eq_eval_padicInt S]

private theorem eval_translateCLM (x : ℤ_[p]) (c : AnalyticStage p h E) (y : ℤ_[p]) :
    eval S (translateCLM S x c) y = eval S c (x + y) := by
  rw [translateCLM_apply, eval_eval_comulCurried]

private theorem norm_translateCLM_le (x : ℤ_[p]) (c : AnalyticStage p h E) :
    ‖translateCLM S x c‖ ≤ ‖c‖ := by
  rw [translateCLM_apply]
  calc
    ‖eval S (comulCurried S c) x‖ ≤ ‖eval S (comulCurried S c)‖ :=
      ContinuousMap.norm_coe_le_norm _ x
    _ ≤ ‖comulCurried S c‖ := norm_eval_le S (comulCurried S c)
    _ = ‖c‖ := norm_comulCurried S c

private theorem translateCLM_compLeft {F R : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F] [ContinuousConstSMul R F]
    [LinearMap.CompatibleSMul E F ℤ_[p] R]
    (u : E →L[R] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S' x (compLeft u hu c) = compLeft u hu (translateCLM S x c) := by
  let u' : E →L[ℤ_[p]] F := u.restrictScalars ℤ_[p]
  have hu' : ∃ C, ∀ e, ‖u' e‖ ≤ C * ‖e‖ := hu
  have hcomp : ∀ d : AnalyticStage p h E, compLeft u hu d = compLeft u' hu' d := fun d ↦ by
    ext i
    simp only [compLeft_apply]
    rfl
  rw [hcomp, hcomp, translateCLM_eq_translateCLM_padicInt S',
    translateCLM_eq_translateCLM_padicInt S, translateCLM_apply, translateCLM_apply,
    comulCurried_compLeft ℤ_[p] u' hu', eval_compLeft ℤ_[p]]

private theorem translateCLM_zero (c : AnalyticStage p h E) : translateCLM S 0 c = c := by
  rw [translateCLM_apply, eval_apply_zero, comulCurried_apply_zero]

private theorem translateCLM_add (x y : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S (x + y) c = translateCLM S x (translateCLM S y c) := by
  simp only [translateCLM_eq_translateCLM_padicInt S]
  rw [add_comm x y, translateCLM_apply, ← eval_eval_comulCurried ℤ_[p] (comulCurried ℤ_[p] c) y x,
    comulCurried_comulCurried ℤ_[p] c,
    eval_compLeft ℤ_[p] (comulCurried (p := p) (h := h) (E := E) ℤ_[p])
      (exists_norm_comulCurried_le ℤ_[p]) (comulCurried ℤ_[p] c) y]
  rfl

/-- **Translation on an analytic stage.** Translating the argument by `x : ℤ_p` defines a linear
isometry equivalence `LA_h(E) ≃ₗᵢ[S] LA_h(E)` with `eval (translate S x c) y = eval c (x + y)`. -/
noncomputable def translate (x : ℤ_[p]) : AnalyticStage p h E ≃ₗᵢ[S] AnalyticStage p h E :=
  LinearIsometryEquiv.ofBounds
    { toFun := translateCLM S x
      map_add' := map_add (translateCLM S x)
      map_smul' := map_smul (translateCLM S x)
      invFun := translateCLM S (-x)
      left_inv c := by rw [← translateCLM_add, neg_add_cancel, translateCLM_zero]
      right_inv c := by rw [← translateCLM_add, add_neg_cancel, translateCLM_zero] }
    (norm_translateCLM_le S x) (norm_translateCLM_le S (-x))

private theorem translate_apply_eq_translateCLM (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S x c = translateCLM S x c :=
  (rfl)

/-- Translation of `c` by `x` is the evaluation of `comulCurried S c` at `x`. -/
theorem translate_eq_eval_comulCurried (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S x c = eval S (comulCurried S c) x := by
  rw [translate_apply_eq_translateCLM, translateCLM_apply]

/-- Evaluating the `i`-th inner slice `comulCurried S c i` at `x` gives the `i`-th coordinate of
`translate S x c`. -/
@[simp]
theorem eval_comulCurried_apply (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) (x : ℤ_[p]) :
    eval S (comulCurried S c i) x = translate S x c i := by
  rw [eval_eq_eval_padicInt S, comulCurried_eq_comulCurried_padicInt S,
    translate_apply_eq_translateCLM, translateCLM_eq_translateCLM_padicInt S, translateCLM_apply]
  have hrow : compLeft (ZeroAtInftyContinuousMap.evalCLM ℤ_[p] i)
        ⟨1, fun d ↦ by simpa only [evalCLM_apply, one_mul] using d.norm_coe_le_norm i⟩
        (comulCurried ℤ_[p] c) =
      comulCurried ℤ_[p] c i := by
    ext j
    simp only [compLeft_apply, evalCLM_apply, comulCurried_apply_apply]
    rw [← DFunLike.congr_fun (congrLeft_prodComm_comul ℤ_[p] c) (j, i), congrLeft_apply]
    rfl
  rw [← hrow, eval_compLeft ℤ_[p], evalCLM_apply]

/-- Evaluating the translate of `c` by `x` at `y` gives `eval S c (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (c : AnalyticStage p h E) (y : ℤ_[p]) :
    eval S (translate S x c) y = eval S c (x + y) := by
  rw [translate_apply_eq_translateCLM, eval_translateCLM]

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (c : AnalyticStage p h E) : translate S 0 c = c :=
  translateCLM_zero S c

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S (x + y) c = translate S x (translate S y c) :=
  translateCLM_add S x y c

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (h := h) (E := E) S x).symm = translate S (-x) := by
  ext c
  rfl

/-- Stage translation does not depend on the choice of auxiliary scalar ring `S`. -/
theorem translate_eq_translate_padicInt (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S x c = translate ℤ_[p] x c :=
  translateCLM_eq_translateCLM_padicInt S x c

/-- Translation commutes with the coordinatewise action of a bounded continuous linear map
compatible with the `ℤ_p`-action. -/
theorem translate_compLeft {F R : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F] [ContinuousConstSMul R F]
    [LinearMap.CompatibleSMul E F ℤ_[p] R]
    (u : E →L[R] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S' x (compLeft u hu c) = compLeft u hu (translate S x c) :=
  translateCLM_compLeft S S' u hu x c

/-- Translation commutes with adjacent stage transitions. -/
theorem transition_translate (x : ℤ_[p]) (c : AnalyticStage p h E) :
    transition S (translate S x c) = translate S x (transition S c) := by
  rw [transition_eq_transition_padicInt S, translate_eq_translate_padicInt S,
    translate_eq_translate_padicInt S, transition_eq_transition_padicInt S,
    translate_eq_eval_comulCurried, translate_eq_eval_comulCurried,
    ← transition_compLeft_transition_comulCurried ℤ_[p] c, eval_transition,
    eval_compLeft ℤ_[p] (transition ℤ_[p]) (exists_norm_transition_le ℤ_[p])]

/-- Translation commutes with multi-level stage transitions. -/
theorem transitionLE_translate {k : ℕ} (hhk : h ≤ k) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    transitionLE S hhk (translate S x c) = translate S x (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ih, transition_translate]

end Translate

end AnalyticStage

/-! ### Translation on locally analytic functions -/

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Translation on locally analytic functions.** Translating the argument by `x : ℤ_p` defines a
linear equivalence `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` agreeing with `AnalyticStage.translate S x` on
every stage. -/
noncomputable def translate (x : ℤ_[p]) : LocallyAnalytic p S E ≃ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.congr (fun _ ↦ (AnalyticStage.translate S x).toLinearEquiv)
    (fun _ _ hhk ↦ LinearMap.ext fun c ↦ (transitionLE_translate S hhk x c).symm)

/-- Translation restricts to `AnalyticStage.translate` on every analytic stage. -/
@[simp]
theorem translate_ofStage (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h E) :
    translate S x (ofStage S h c) = ofStage S h (AnalyticStage.translate S x c) := by
  rw [translate, ofStage_def, Module.DirectLimit.congr_apply_of,
    LinearIsometryEquiv.coe_toLinearEquiv]

/-- Evaluating the translate of `f` by `x` at `y` gives `eval S f (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (f : LocallyAnalytic p S E) (y : ℤ_[p]) :
    eval S (translate S x f) y = eval S f (x + y) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, eval_ofStage, eval_ofStage, AnalyticStage.eval_translate]

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (f : LocallyAnalytic p S E) : translate S 0 f = f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, AnalyticStage.translate_zero]

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (f : LocallyAnalytic p S E) :
    translate S (x + y) f = translate S x (translate S y f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, translate_ofStage, translate_ofStage,
    AnalyticStage.translate_add]

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (E := E) S x).symm = translate S (-x) := by
  ext f
  apply (translate S x).injective
  rw [LinearEquiv.apply_symm_apply, ← translate_add, add_neg_cancel, translate_zero]

end LocallyAnalytic

end TauCeti
