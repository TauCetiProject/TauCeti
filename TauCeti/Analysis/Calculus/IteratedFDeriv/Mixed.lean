/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.InnerProductSpace.Projection.NormalDilation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Nat.Choose.Sum
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite
import TauCeti.GroupTheory.Perm.Fin

/-!
# Mixed iterated derivatives along a subspace and its orthogonal complement

Let `E` be a real inner product space and `V` a subspace of `E` with an orthogonal projection.
Near a submanifold, after choosing a tube, `V` plays the role of the normal directions and its
orthogonal complement `Vᗮ` that of the tangent, or horizontal, directions. This file contains the
pointwise calculus of derivatives split along this decomposition; the mixed semiclassical Sobolev
norms built from it are in `TauCeti.Analysis.Sobolev.Semiclassical.Mixed`.

**Mixed derivatives.** For `a ≤ n`, the mixed derivative of order `(a, n - a)` of `f` at `x` is
the `n`-th derivative `Dⁿ f x` restricted to horizontal vectors in its first `a` slots and to
normal vectors in the remaining `n - a`:

`∂^{a, n - a} f x (m) = Dⁿ f x (P_{Vᗮ} m₀, …, P_{Vᗮ} m_{a-1}, P_V m_a, …, P_V m_{n-1})`

(`Submodule.mixedIteratedFDeriv`). It is bounded by the full derivative
(`Submodule.norm_mixedIteratedFDeriv_le`). Conversely, by the symmetry of iterated derivatives and
the expansion of each argument into its horizontal and normal parts, the full derivative of a
`Cⁿ` function is bounded by its mixed derivatives,
`‖Dⁿ f x‖ ≤ ∑_{a ≤ n} (n choose a) ‖∂^{a, n - a} f x‖`
(`Submodule.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv`).

**The normal dilation.** Under the normal dilation `Submodule.normalDilation V t`, which fixes
`Vᗮ` and multiplies `V` by `t` (`TauCeti.Analysis.InnerProductSpace.Projection.NormalDilation`),
the mixed derivative of order `(a, n - a)` gains the factor `t ^ (n - a)`: each normal derivative
contributes a factor `t`, each horizontal one none
(`Submodule.mixedIteratedFDeriv_comp_normalDilation`, and
`Submodule.mixedIteratedFDeriv_comp_normalDilation_of_ne_zero`, which needs no smoothness). So
bounds `h ^ (i - a) ‖∂^{a, i - a} g‖ ≤ B` at the scale `h` become, after the normal dilation by
`h`, unscaled bounds `‖Dⁱ (g ∘ normalDilation V h)‖ ≤ 2ⁱ B`
(`Submodule.norm_iteratedFDeriv_comp_normalDilation_le`).

**Linearity.** Mixed derivatives commute with negation and scalar multiplication, and with sums
of functions of class `Cⁿ` (`Submodule.mixedIteratedFDeriv_neg`,
`Submodule.mixedIteratedFDeriv_const_smul`, `Submodule.mixedIteratedFDeriv_add`,
`Submodule.mixedIteratedFDeriv_sum`). Left composition with a linear isometry equivalence, such as
complex conjugation, preserves their norms (`Submodule.norm_mixedIteratedFDeriv_comp_left`).

**Derivatives.** A normal derivative `∂_v f`, `v ∈ V`, raises the normal order of a mixed
derivative by one (`Submodule.mixedIteratedFDeriv_fderiv_apply_of_mem`), and a horizontal
derivative `∂_e f`, `e ∈ Vᗮ`, raises the horizontal order by one
(`Submodule.mixedIteratedFDeriv_fderiv_apply_of_mem_orthogonal`).

## Main definitions

* `Submodule.mixedIteratedFDeriv V n a f x`: the mixed derivative of order `(a, n - a)`.

## Main results

* `Submodule.mixedIteratedFDeriv_comp_normalDilation`: the mixed derivative of order
  `(a, n - a)` of `f ∘ normalDilation V t` is `t ^ (n - a)` times that of `f`.
* `Submodule.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv`: the full derivative is
  bounded by the mixed ones.
* `Submodule.norm_iteratedFDeriv_comp_normalDilation_le`: bounds on the mixed derivatives, with a
  factor `t` for each normal derivative, bound the derivatives of `f ∘ normalDilation V t`.
* `Submodule.mixedIteratedFDeriv_fderiv_apply_of_mem`,
  `Submodule.mixedIteratedFDeriv_fderiv_apply_of_mem_orthogonal`: normal and horizontal
  derivatives raise the normal and horizontal orders.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Finset Module

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (V : Submodule ℝ E)
  [V.HasOrthogonalProjection]

/-! ### Mixed derivatives -/

/-- The **mixed derivative** of order `(a, n - a)` of `f` at `x`: the `n`-th derivative of `f` at
`x` with its first `a` arguments projected to the horizontal subspace `Vᗮ` and its remaining
`n - a` arguments projected to the normal subspace `V`. For `a ≥ n` every argument is horizontal.
Its norm is the norm of `Dⁿ f x` on `a` horizontal and `n - a` normal vectors. -/
def mixedIteratedFDeriv (n a : ℕ) (f : E → F) (x : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F :=
  (iteratedFDeriv ℝ n f x).compContinuousLinearMap fun i ↦
    if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection

/-- The defining formula of the mixed derivative. -/
theorem mixedIteratedFDeriv_def (n a : ℕ) (f : E → F) (x : E) :
    V.mixedIteratedFDeriv n a f x = (iteratedFDeriv ℝ n f x).compContinuousLinearMap fun i ↦
      if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection :=
  (rfl)

@[simp]
theorem mixedIteratedFDeriv_apply (n a : ℕ) (f : E → F) (x : E) (m : Fin n → E) :
    V.mixedIteratedFDeriv n a f x m = iteratedFDeriv ℝ n f x fun i ↦
      if (i : ℕ) < a then Vᗮ.starProjection (m i) else V.starProjection (m i) := by
  rw [mixedIteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  exact apply_ite (fun L : E →L[ℝ] E ↦ L (m i)) _ _ _

/-- A mixed derivative is bounded by the full derivative of the same order. -/
theorem norm_mixedIteratedFDeriv_le (n a : ℕ) (f : E → F) (x : E) :
    ‖V.mixedIteratedFDeriv n a f x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) (prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    fun i _ ↦ ?_)
  split_ifs
  · exact Vᗮ.starProjection_norm_le
  · exact V.starProjection_norm_le

/-- The mixed derivatives of a function of class `Cⁿ` depend continuously on the point. -/
theorem continuous_mixedIteratedFDeriv {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) (a : ℕ) :
    Continuous (V.mixedIteratedFDeriv n a f) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL fun i : Fin n ↦
    if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection).continuous.comp
    (hf.continuous_iteratedFDeriv le_rfl)

@[simp]
theorem mixedIteratedFDeriv_zero_fun (n a : ℕ) :
    V.mixedIteratedFDeriv n a (0 : E → F) = 0 := by
  ext x m
  simp [mixedIteratedFDeriv_apply, iteratedFDeriv_zero]

@[simp]
theorem mixedIteratedFDeriv_neg (n a : ℕ) (f : E → F) :
    V.mixedIteratedFDeriv n a (-f) = -V.mixedIteratedFDeriv n a f := by
  ext x m
  simp [iteratedFDeriv_neg_apply]

/-- Mixed derivatives are homogeneous: `∂^{a, n - a} (c • f) = c • ∂^{a, n - a} f`, with no
smoothness assumption on `f`. -/
theorem mixedIteratedFDeriv_const_smul (n a : ℕ) (c : ℝ) (f : E → F) :
    V.mixedIteratedFDeriv n a (c • f) = c • V.mixedIteratedFDeriv n a f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  ext x m
  have hD : iteratedFDeriv ℝ n (c • f) x = c • iteratedFDeriv ℝ n f x :=
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc)).iteratedFDeriv_comp_left
  simp [hD]

/-- Mixed derivatives are additive on functions of class `Cⁿ`. -/
theorem mixedIteratedFDeriv_add {n : ℕ} {f g : E → F} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) (a : ℕ) :
    V.mixedIteratedFDeriv n a (f + g) =
      V.mixedIteratedFDeriv n a f + V.mixedIteratedFDeriv n a g := by
  ext x m
  simp [iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]

/-- Mixed derivatives commute with finite sums of functions of class `Cⁿ`. -/
theorem mixedIteratedFDeriv_sum {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → E → F}
    (hf : ∀ i ∈ s, ContDiff ℝ n (f i)) (a : ℕ) :
    V.mixedIteratedFDeriv n a (fun x ↦ ∑ i ∈ s, f i x) =
      ∑ i ∈ s, V.mixedIteratedFDeriv n a (f i) := by
  ext x m
  simp [iteratedFDeriv_sum hf]

/-- Mixed derivatives commute with translations. -/
theorem mixedIteratedFDeriv_comp_sub (n a : ℕ) (f : E → F) (c : E) :
    V.mixedIteratedFDeriv n a (fun y ↦ f (y - c)) =
      fun x ↦ V.mixedIteratedFDeriv n a f (x - c) := by
  ext x : 1
  rw [mixedIteratedFDeriv, mixedIteratedFDeriv, iteratedFDeriv_comp_sub]

/-- Composition on the left with a linear isometry equivalence, such as complex conjugation,
preserves the norms of the mixed derivatives. -/
theorem norm_mixedIteratedFDeriv_comp_left {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : F ≃ₗᵢ[ℝ] G) (n a : ℕ) (f : E → F) (x : E) :
    ‖V.mixedIteratedFDeriv n a (g ∘ f) x‖ = ‖V.mixedIteratedFDeriv n a f x‖ := by
  have hcomp : V.mixedIteratedFDeriv n a (g ∘ f) x =
      (g : F →L[ℝ] G).compContinuousMultilinearMap (V.mixedIteratedFDeriv n a f x) := by
    ext m
    simp only [mixedIteratedFDeriv_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply]
    rw [← g.coe_toContinuousLinearEquiv, g.toContinuousLinearEquiv.iteratedFDeriv_comp_left,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [hcomp]
  exact LinearIsometry.norm_compContinuousMultilinearMap g.toLinearIsometry _

/-- Dilating the arguments of a multilinear map in the slots of a mixed derivative of order
`(a, n - a)` gives the factor `t ^ (n - a)`: the `n - a` normal slots each contribute `t`. -/
private theorem map_normalDilation_mixed {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F) (a : ℕ) (t : ℝ) (m : Fin n → E) :
    M (fun i ↦ V.normalDilation t
        (if (i : ℕ) < a then Vᗮ.starProjection (m i) else V.starProjection (m i))) =
      t ^ (n - a) • M fun i ↦
        if (i : ℕ) < a then Vᗮ.starProjection (m i) else V.starProjection (m i) := by
  have hcard : #{i : Fin n | ¬(i : ℕ) < a} = n - a := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ (i : ℕ) < a)
    rw [Fin.card_filter_val_lt, card_univ, Fintype.card_fin] at h
    omega
  have hc : ∏ i : Fin n, (if (i : ℕ) < a then (1 : ℝ) else t) = t ^ (n - a) := by
    rw [prod_ite, prod_const_one, one_mul, prod_const, hcard]
  rw [← hc, ← ContinuousMultilinearMap.map_smul_univ]
  congr 1
  ext i
  split_ifs <;> simp only [one_smul, normalDilation_starProjection_orthogonal,
    normalDilation_starProjection]

/-- **Mixed derivatives under the normal dilation.** For `f` of class `Cⁿ`, the mixed derivative
of order `(a, n - a)` of `f ∘ normalDilation V t` is `t ^ (n - a)` times that of `f` at the
dilated point: each normal derivative contributes a factor `t`, each horizontal one none. -/
theorem mixedIteratedFDeriv_comp_normalDilation {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f)
    (a : ℕ) (t : ℝ) (x : E) :
    V.mixedIteratedFDeriv n a (f ∘ V.normalDilation t) x =
      t ^ (n - a) • V.mixedIteratedFDeriv n a f (V.normalDilation t x) := by
  ext m
  rw [mixedIteratedFDeriv_apply, (V.normalDilation t).iteratedFDeriv_comp_right hf x le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    mixedIteratedFDeriv_apply, map_normalDilation_mixed]

/-- **Mixed derivatives under an invertible normal dilation.** For `t ≠ 0` and any `f`, with no
smoothness assumption, the mixed derivative of order `(a, n - a)` of `f ∘ normalDilation V t` is
`t ^ (n - a)` times that of `f` composed with the dilation. -/
theorem mixedIteratedFDeriv_comp_normalDilation_of_ne_zero (n a : ℕ) (f : E → F) {t : ℝ}
    (ht : t ≠ 0) :
    V.mixedIteratedFDeriv n a (f ∘ V.normalDilation t) =
      t ^ (n - a) • (V.mixedIteratedFDeriv n a f ∘ V.normalDilation t) := by
  have hcomp : f ∘ V.normalDilation t = f ∘ V.normalDilationEquiv ht := by
    rw [coeFn_normalDilationEquiv]
  ext x m
  rw [mixedIteratedFDeriv_apply, hcomp, ContinuousLinearEquiv.iteratedFDeriv_comp_right,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, coe_normalDilationEquiv,
    normalDilationEquiv_apply, Pi.smul_apply, Function.comp_apply, smul_apply,
    mixedIteratedFDeriv_apply, map_normalDilation_mixed]

/-- **The full derivative is bounded by the mixed derivatives.** For `f` of class `Cⁿ` at `x`,
`‖Dⁿ f x‖ ≤ ∑_{a ≤ n} (n choose a) ‖∂^{a, n - a} f x‖`. Splitting every argument into its horizontal
and normal parts expands `Dⁿ f x` into `2ⁿ` terms; by the symmetry of `Dⁿ f x`, the term whose
arguments indexed by a set `S` are horizontal is a value of the mixed derivative of order
`(#S, n - #S)`. -/
theorem norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv {n : ℕ} {f : E → F}
    {x : E} (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      ∑ a ∈ range (n + 1), (n.choose a : ℝ) * ‖V.mixedIteratedFDeriv n a f x‖ := by
  classical
  -- The term of the expansion in which the arguments indexed by `S` are horizontal.
  have hterm (S : Finset (Fin n)) (m : Fin n → E) :
      ‖iteratedFDeriv ℝ n f x (S.piecewise (fun i ↦ Vᗮ.starProjection (m i))
          fun i ↦ V.starProjection (m i))‖ ≤ ‖V.mixedIteratedFDeriv n #S f x‖ * ∏ i, ‖m i‖ := by
    -- A permutation of the slots carrying the first `#S` slots onto `S`.
    obtain ⟨σ, hσ⟩ := Fin.exists_perm_mem_iff_val_lt_card S
    rw [← hf.iteratedFDeriv_comp_perm_of_le (by simp) _ σ, ← Equiv.prod_comp σ fun i ↦ ‖m i‖]
    have hperm : (S.piecewise (fun i ↦ Vᗮ.starProjection (m i))
        fun i ↦ V.starProjection (m i)) ∘ σ = fun i : Fin n ↦
          if (i : ℕ) < #S then Vᗮ.starProjection (m (σ i)) else V.starProjection (m (σ i)) := by
      ext i
      simp only [Function.comp_apply, piecewise, hσ]
    rw [hperm, ← mixedIteratedFDeriv_apply]
    exact ContinuousMultilinearMap.le_opNorm _ _
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : (fun i ↦ Vᗮ.starProjection (m i)) + (fun i ↦ V.starProjection (m i)) = m := by
    ext i
    simp only [Pi.add_apply, add_comm, starProjection_add_starProjection_orthogonal]
  have hexp := (iteratedFDeriv ℝ n f x).map_add_univ (fun i ↦ Vᗮ.starProjection (m i))
    fun i ↦ V.starProjection (m i)
  rw [hm] at hexp
  rw [hexp]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun S _ ↦ hterm S m).trans_eq ?_)
  rw [← sum_mul, ← powerset_univ,
    sum_powerset_apply_card fun k ↦ ‖V.mixedIteratedFDeriv n k f x‖, card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]

/-- **Derivatives of a normally dilated field from its mixed derivatives.** For `f` of class `Cⁿ`
and `t ≥ 0`, if `t ^ (n - a) ‖∂^{a, n - a} f (normalDilation V t x)‖ ≤ B` for every `a ≤ n`, then
`‖Dⁿ (f ∘ normalDilation V t) x‖ ≤ 2ⁿ B`: bounds on the mixed derivatives in which each normal
derivative costs a factor `t` bound the derivatives of the field read in the normal coordinate
rescaled by `t`. -/
theorem norm_iteratedFDeriv_comp_normalDilation_le {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f)
    {t B : ℝ} (ht : 0 ≤ t) {x : E}
    (hB : ∀ a ≤ n, t ^ (n - a) * ‖V.mixedIteratedFDeriv n a f (V.normalDilation t x)‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (f ∘ V.normalDilation t) x‖ ≤ 2 ^ n * B := by
  refine (V.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv
    (hf.comp (V.normalDilation t).contDiff).contDiffAt).trans ?_
  calc ∑ a ∈ range (n + 1),
        (n.choose a : ℝ) * ‖V.mixedIteratedFDeriv n a (f ∘ V.normalDilation t) x‖
      ≤ ∑ a ∈ range (n + 1), (n.choose a : ℝ) * B := by
        refine sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [V.mixedIteratedFDeriv_comp_normalDilation hf a t x, norm_smul, norm_pow,
          Real.norm_of_nonneg ht]
        exact hB a (Nat.lt_succ_iff.1 (mem_range.1 ha))
    _ = 2 ^ n * B := by
        rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

/-- **A normal derivative raises the normal order.** For `a ≤ n`, `f` of class `Cⁿ⁺¹` at `x` and a
normal vector `v ∈ V`, the mixed derivative of order `(a, n - a)` of the derivative of `f` along
`v` is the mixed derivative of order `(a, n + 1 - a)` of `f` with `v` in its last slot. -/
theorem mixedIteratedFDeriv_fderiv_apply_of_mem {n a : ℕ} (ha : a ≤ n) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n + 1) f x) {v : E} (hv : v ∈ V) (m : Fin n → E) :
    V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v) x m =
      V.mixedIteratedFDeriv (n + 1) a f x (Fin.snoc m v) := by
  rw [mixedIteratedFDeriv_apply, hf.iteratedFDeriv_fderiv_apply_eq_iteratedFDeriv_snoc,
    mixedIteratedFDeriv_apply]
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp [show ¬n < a by omega, starProjection_eq_self_iff.2 hv]
  · simp

/-- **A horizontal derivative raises the horizontal order.** For `a ≤ n`, `f` of class `Cⁿ⁺¹` at
`x` and a horizontal vector `e ∈ Vᗮ`, the mixed derivative of order `(a, n - a)` of the derivative
of `f` along `e` is the mixed derivative of order `(a + 1, n - a)` of `f` with `e` inserted in
slot `a`, the last horizontal slot. -/
theorem mixedIteratedFDeriv_fderiv_apply_of_mem_orthogonal {n a : ℕ} (ha : a ≤ n) {f : E → F}
    {x : E} (hf : ContDiffAt ℝ (n + 1) f x) {e : E} (he : e ∈ Vᗮ) (m : Fin n → E) :
    V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e) x m =
      V.mixedIteratedFDeriv (n + 1) (a + 1) f x (Fin.insertNth ⟨a, by omega⟩ e m) := by
  set p : Fin (n + 1) := ⟨a, by omega⟩
  set w : Fin n → E := fun i ↦
    if (i : ℕ) < a then Vᗮ.starProjection (m i) else V.starProjection (m i)
  -- By symmetry, the slot of the new horizontal argument may be moved from the last one to `a`.
  have hsymm : iteratedFDeriv ℝ (n + 1) f x (Fin.snoc w e) =
      iteratedFDeriv ℝ (n + 1) f x (p.insertNth e w) := by
    rw [← Fin.insertNth_last', ← Fin.cons_comp_cycleRange, ← Fin.cons_comp_cycleRange,
      hf.iteratedFDeriv_comp_perm_of_le (by simp), hf.iteratedFDeriv_comp_perm_of_le (by simp)]
  rw [mixedIteratedFDeriv_apply, hf.iteratedFDeriv_fderiv_apply_eq_iteratedFDeriv_snoc, hsymm,
    mixedIteratedFDeriv_apply]
  congr 1
  ext i
  refine p.succAboveCases ?_ (fun k ↦ ?_) i
  · simp [p, starProjection_eq_self_iff.2 he]
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    by_cases hk : (k : ℕ) < a
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [p, Fin.lt_def] using hk)]
      simp [w, hk, show (k : ℕ) < a + 1 by omega]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [p, Fin.le_def] using hk)]
      simp [w, hk]

/-- The mixed derivatives of a normal derivative:
`‖∂^{a, n - a} (∂_v f) x‖ ≤ ‖v‖ ‖∂^{a, n + 1 - a} f x‖` for `a ≤ n` and `v ∈ V`. -/
theorem norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem {n a : ℕ} (ha : a ≤ n) {f : E → F}
    {x : E} (hf : ContDiffAt ℝ (n + 1) f x) {v : E} (hv : v ∈ V) :
    ‖V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖V.mixedIteratedFDeriv (n + 1) a f x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [V.mixedIteratedFDeriv_fderiv_apply_of_mem ha hf hv]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The mixed derivatives of a horizontal derivative:
`‖∂^{a, n - a} (∂_e f) x‖ ≤ ‖e‖ ‖∂^{a + 1, n - a} f x‖` for `a ≤ n` and `e ∈ Vᗮ`. -/
theorem norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal {n a : ℕ} (ha : a ≤ n)
    {f : E → F} {x : E} (hf : ContDiffAt ℝ (n + 1) f x) {e : E} (he : e ∈ Vᗮ) :
    ‖V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e) x‖ ≤
      ‖e‖ * ‖V.mixedIteratedFDeriv (n + 1) (a + 1) f x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [V.mixedIteratedFDeriv_fderiv_apply_of_mem_orthogonal ha hf he]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Fin.prod_univ_succAbove _ ⟨a, by omega⟩]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

end Submodule
