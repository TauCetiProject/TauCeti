/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.Analysis.Normed.Module.Alternating.Curry

/-!
# Comass of wedges with a one-form and of powers of a two-form

On a real inner product space the norm of a continuous alternating form is its comass, the
supremum of its absolute values on orthonormal frames. The general wedge bound
`ContinuousAlternatingMap.norm_wedge_le` carries the binomial factor `(k + l).choose k`. When
one factor is a one-form `α` this factor disappears:

`‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`.

On the span of an orthonormal frame, `α` is the inner product with one vector, so some
orthonormal basis of the span has `α` vanishing on all but its first vector
(`TauCeti.exists_linearIsometryEquiv_inner_eq_norm_mul_eval`), and only one term of the wedge
survives.

Inserting a vector `v` into the power `ω ^ (m + 1)` of a two-form gives
`(m + 1) • (ι_v ω ∧ ω ^ m)`, and `ι_v ω` is a one-form of norm at most `‖ω‖ ‖v‖`. Induction
gives the bound

`‖ω ^ m‖ ≤ m! ‖ω‖ ^ m`,

so the normalized power `ω ^ m / m!` has comass at most `‖ω‖ ^ m`. Applied to the Kähler form,
whose comass is one, this is the Wirtinger inequality in every degree. The bound is sharp: a
two-form takes the value `m!` on `m` standard pairs
(`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`).

## Main results

* `ContinuousAlternatingMap.norm_wedge_le_norm_mul_norm`: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖` for a one-form
  `α`.
* `ContinuousAlternatingMap.norm_wedgePow_le`: `‖ω ^ m‖ ≤ m! ‖ω‖ ^ m` for a two-form `ω`.

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969, §1.8.1 (comass of a wedge with a
  simple factor).
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.4.
-/

public section

open Module Set
open scoped RealInnerProductSpace Nat

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {l : ℕ}

/-- **The comass of a wedge with a one-form** is at most the product of the comasses:
`‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`, without the binomial factor of the general bound
`ContinuousAlternatingMap.norm_wedge_le`. -/
theorem norm_wedge_le_norm_mul_norm (α : E [⋀^Fin 1]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    ‖wedge α ψ‖ ≤ ‖α‖ * ‖ψ‖ := by
  classical
  refine (opNorm_le_iff_le_orthonormal (by positivity)).2 fun v hv ↦ ?_
  -- Restrict to the span `W` of the frame, where the wedge has top degree.
  let W := Submodule.span ℝ (range v)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_range v)
  have hW : finrank ℝ W = l + 1 := by
    rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin, Nat.add_comm]
  let w : Fin (1 + l) → W := fun i ↦ ⟨v i, Submodule.subset_span (mem_range_self i)⟩
  let η := (wedge α ψ).compContinuousLinearMap W.subtypeL
  -- An orthonormal basis `b` of `W` on whose last `l` vectors `α` vanishes: in suitable
  -- coordinates, the Riesz representative `a` of `α` on `W` is a multiple of the first one.
  set a := (InnerProductSpace.toDual ℝ W).symm (toDual α ∘L W.subtypeL)
  obtain ⟨g, hg⟩ := TauCeti.exists_linearIsometryEquiv_inner_eq_norm_mul_eval a ⟨0, by omega⟩
  let b := (OrthonormalBasis.ofRepr g).reindex (finCongr hW)
  have hb' (j : Fin l) : α ![(b j.succ : E)] = 0 := by
    have h := hg (b j.succ)
    rw [InnerProductSpace.toDual_symm_apply] at h
    simpa [b, PiLp.single_apply, Fin.ext_iff] using h
  have hηb : η (b.reindex (finCongr (Nat.add_comm l 1))) =
      α ![(b 0 : E)] * ψ fun j ↦ (b j.succ : E) := by
    have hframe : W.subtypeL ∘ b.reindex (finCongr (Nat.add_comm l 1)) =
        Matrix.vecCons (b 0 : E) (fun j ↦ (b j.succ : E)) ∘ Fin.cast (Nat.add_comm 1 l) := by
      funext i
      rw [Function.comp_apply, Function.comp_apply, OrthonormalBasis.reindex_apply, finCongr_symm,
        finCongr_apply]
      -- `Matrix.vecCons` reduces at `0` and at successors.
      exact Fin.cases rfl (fun j ↦ rfl) (Fin.cast (Nat.add_comm 1 l) i)
    rw [compContinuousLinearMap_apply, hframe, wedge_def,
      pairedWedge_apply_vecCons_of_forall _ _ _ _ _ _ hb', ContinuousLinearMap.mul_apply']
  have hα : |α ![(b 0 : E)]| ≤ ‖α‖ := by
    simpa [Submodule.norm_coe, b.norm_eq_one] using α.le_opNorm ![(b 0 : E)]
  have hψ : |ψ fun j ↦ (b j.succ : E)| ≤ ‖ψ‖ := by
    simpa [Submodule.norm_coe, b.norm_eq_one] using ψ.le_opNorm fun j ↦ (b j.succ : E)
  -- The frame `w` is `v` with its vectors viewed in `W`.
  calc ‖wedge α ψ v‖ = ‖η w‖ := rfl
    _ ≤ ‖η‖ := by
      simpa [w, hv.norm_eq_one] using η.le_opNorm w
    _ = |α ![(b 0 : E)]| * |ψ fun j ↦ (b j.succ : E)| := by
      rw [η.norm_eq_norm_apply_orthonormalBasis (b.reindex (finCongr (Nat.add_comm l 1))), hηb,
        Real.norm_eq_abs, abs_mul]
    _ ≤ ‖α‖ * ‖ψ‖ := mul_le_mul hα hψ (abs_nonneg _) (norm_nonneg _)

/-- **The comass of a power of a two-form**: `‖ω ^ m‖ ≤ m! ‖ω‖ ^ m`, so the normalized power
`ω ^ m / m!` has comass at most `‖ω‖ ^ m`. The bound is attained, for `2 m` at most the dimension,
by the Kähler form of an orthogonal complex structure. -/
theorem norm_wedgePow_le (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) :
    ‖wedgePow ω m‖ ≤ m ! * ‖ω‖ ^ m := by
  induction m with
  | zero =>
    refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
    -- `wedgePow_zero_apply` is stated in degree `0`, which `2 * 0` is only up to defeq.
    rw [show wedgePow ω 0 v = 1 from wedgePow_zero_apply ω v]
    simp
  | succ m ih =>
    refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
    obtain ⟨x, w, rfl⟩ : ∃ (x : E) (w : Fin (2 * m + 1) → E), v = Matrix.vecCons x w :=
      ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
    have hα : ‖curryLeftTopological (n := 1) ω x‖ ≤ ‖ω‖ * ‖x‖ := by
      rw [← curryLeft_eq_curryLeftTopological, ← norm_curryLeft ω]
      exact ω.curryLeft.le_opNorm x
    have hprod : ∏ i, ‖(w ∘ Fin.cast (Nat.add_comm 1 (2 * m))) i‖ = ∏ i, ‖w i‖ :=
      Fintype.prod_equiv (finCongr (Nat.add_comm 1 (2 * m))) _ _ fun _ ↦ rfl
    have hv : ∏ i : Fin (2 * (m + 1)), ‖Matrix.vecCons x w i‖ = ‖x‖ * ∏ i, ‖w i‖ :=
      Fin.prod_univ_succ (n := 2 * m + 1) _
    rw [wedgePow_succ_apply_vecCons, ← wedge_def, norm_mul, hv]
    calc ‖((m : ℝ) + 1)‖ * ‖wedge (curryLeftTopological (n := 1) ω x) (wedgePow ω m)
          (w ∘ Fin.cast (Nat.add_comm 1 (2 * m)))‖
        ≤ (m + 1) * (‖curryLeftTopological (n := 1) ω x‖ * ‖wedgePow ω m‖ * ∏ i, ‖w i‖) := by
          rw [Real.norm_of_nonneg (by positivity), ← hprod]
          gcongr
          exact (le_opNorm _ _).trans (by gcongr; exact norm_wedge_le_norm_mul_norm _ _)
      _ ≤ (m + 1) * (‖ω‖ * ‖x‖ * (m ! * ‖ω‖ ^ m) * ∏ i, ‖w i‖) := by gcongr
      _ = (m + 1)! * ‖ω‖ ^ (m + 1) * (‖x‖ * ∏ i, ‖w i‖) := by
          push_cast [Nat.factorial_succ]
          ring

end ContinuousAlternatingMap
