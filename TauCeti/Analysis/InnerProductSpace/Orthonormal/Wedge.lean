/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Reflection

/-!
# Comass of wedge products with a one-form

On a real inner product space the operator norm of a real alternating form is its comass, the
supremum of its absolute values on orthonormal frames
(`ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal`). For forms of arbitrary degrees the
comass of a wedge product is only bounded by a binomial multiple of the product of the comasses
(`ContinuousAlternatingMap.norm_wedge_le`). When the first factor is a one-form `α` the binomial
coefficient is not needed: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`.

To see this on an orthonormal frame `w`, reflect the frame within its span so that `α` vanishes
on all of its vectors but the first. A Householder reflection of the coefficient vector
`(α(w₀), …, α(wₗ))` onto a multiple of the first basis vector does this
(`TauCeti.exists_mem_orthogonalGroup_mulVec_eq_smul_single`). The change of frame multiplies the
value of an alternating form by the determinant `±1` of the reflection, and on the new frame the
determinant expansion of `α ∧ ψ` along `α` has the single term `α(w₀) ψ(w₁, …, wₗ)`. The same
rotation argument in an orthonormal basis of the span also yields the sharp comass bound
`‖alternatizeUncurryFin (α.smulRight ω)‖ ≤ ‖α‖ * ‖ω‖` for any normed codomain `F`, without the
`(k + 1)` factor of general normed spaces.

With the power rule `ι_v (ω ^ (m + 1)) = (m + 1) • (ι_v ω ∧ ω ^ m)` for a two-form `ω`, this
bounds the comass of the wedge powers of every real two-form: `‖ω ^ m‖ ≤ m! ‖ω‖ ^ m`. For a
two-form of comass at most one, such as the Kähler form of an orthogonal complex structure, the
normalized power `ω ^ m / m!` therefore has comass at most one; this is the Wirtinger inequality.

## Main results

* `ContinuousAlternatingMap.norm_wedge_le_norm_mul_norm`: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖` for a one-form `α`.
* `ContinuousAlternatingMap.norm_alternatizeUncurryFin_smulRight_le`,
  `ContinuousAlternatingMap.enorm_alternatizeUncurryFin_smulRight_le`: sharp comass bounds
  `‖alternatizeUncurryFin (α.smulRight ω)‖ ≤ ‖α‖ * ‖ω‖` (and extended-norm form) for a
  covector `α` and a vector-valued alternating form `ω`.
* `ContinuousAlternatingMap.norm_wedgePow_succ_le`: `‖ω ^ (m + 1)‖ ≤ (m + 1) ‖ω‖ ‖ω ^ m‖` for a
  two-form `ω`.
* `ContinuousAlternatingMap.norm_wedgePow_le`: `‖ω ^ m‖ ≤ m! ‖ω‖ ^ m` for a two-form `ω`.

## References

* H. Federer, *Geometric Measure Theory*, §1.8.1 (comass of products with a covector) and §1.8.2
  (the Wirtinger inequality).
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  §II.6.
-/

public section

namespace ContinuousAlternatingMap

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {l : ℕ}

/-- **The comass of a wedge with a one-form**: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`, with no binomial factor. -/
theorem norm_wedge_le_norm_mul_norm (α : E [⋀^Fin 1]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    ‖α.wedge ψ‖ ≤ ‖α‖ * ‖ψ‖ := by
  classical
  refine (opNorm_le_iff_le_orthonormal (by positivity)).2 fun v hv ↦ ?_
  -- Reindex the frame by `Fin (l + 1)` and reflect it so that `α` vanishes on `w 1, …, w l`.
  set f := (α.wedge ψ).toAlternatingMap.domDomCongr (finCongr (Nat.add_comm 1 l))
  set x : Fin (l + 1) → E := v ∘ Fin.cast (Nat.add_comm l 1)
  have hx : Orthonormal ℝ x := hv.comp _ (Fin.cast_injective _)
  obtain ⟨A, hA, hAc⟩ := TauCeti.exists_mem_orthogonalGroup_mulVec_eq_smul_single
    (Real.mul_self_sqrt (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (α ![x i]))) 0
  set w : Fin (l + 1) → E := fun j ↦ ∑ i, A j i • x i
  have hw : Orthonormal ℝ w := (hx.orthonormal_sum_smul_iff_mem_unitaryGroup A).2 hA
  have hαw (j : Fin (l + 1)) : α ![w j] = (A *ᵥ fun i ↦ α ![x i]) j := by
    -- A one-form at `![y]` is the linear map `curryLeft α` at `y`, evaluated at `![]`.
    rw [← curryLeft_apply_apply]
    simp [w, mulVec, dotProduct]
  -- The reflection changes the value by `det A = ±1`.
  have hdet : |A.det| = 1 := by
    rcases TauCeti.det_eq_one_or_neg_one_of_mem_orthogonalGroup hA with h | h <;> simp [h]
  have hfv : f x = α.wedge ψ v := by simp [f, x, Function.comp_def]
  have hfw : f w = A.det • f x := f.map_sum_smul A x
  -- On the reflected frame the wedge is `α (w 0) * ψ (w 1, …, w l)`.
  have hval : f w = α ![w 0] * ψ (Fin.tail w) := by
    have h := pairedWedge_apply_vecCons_of_forall (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ α ψ (w 0) (Fin.tail w) fun i ↦ by
        rw [Fin.tail, hαw, hAc]
        simp
    have hcons : Matrix.vecCons (w 0) (Fin.tail w) = w := by
      funext i
      cases i using Fin.cases <;> simp [Fin.tail]
    rw [← wedge_def, hcons] at h
    simpa [f, Function.comp_def] using h
  have hα : ‖α ![w 0]‖ ≤ ‖α‖ := by simpa [hw.norm_eq_one] using α.le_opNorm ![w 0]
  have hψ : ‖ψ (Fin.tail w)‖ ≤ ‖ψ‖ := by
    simpa [Fin.tail, hw.norm_eq_one] using ψ.le_opNorm (Fin.tail w)
  calc ‖α.wedge ψ v‖ = ‖f w‖ := by rw [hfw, ← hfv, norm_smul, Real.norm_eq_abs A.det, hdet, one_mul]
    _ = ‖α ![w 0]‖ * ‖ψ (Fin.tail w)‖ := by rw [hval, norm_mul]
    _ ≤ ‖α‖ * ‖ψ‖ := mul_le_mul hα hψ (norm_nonneg _) (norm_nonneg _)

/-- **One step of the Wirtinger bound**: `‖ω ^ (m + 1)‖ ≤ (m + 1) ‖ω‖ ‖ω ^ m‖` for a real
two-form `ω`. -/
theorem norm_wedgePow_succ_le (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) :
    ‖ω.wedgePow (m + 1)‖ ≤ (m + 1) * ‖ω‖ * ‖ω.wedgePow m‖ := by
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  obtain ⟨u, w, rfl⟩ : ∃ (u : E) (w : Fin (2 * m + 1) → E), v = Matrix.vecCons u w :=
    ⟨vecHead v, vecTail v, (Matrix.cons_head_tail v).symm⟩
  have hprod : ∏ i, ‖(w ∘ Fin.cast (Nat.add_comm 1 (2 * m))) i‖ = ∏ i, ‖w i‖ :=
    Fintype.prod_equiv (finCongr (Nat.add_comm 1 (2 * m))) _ _ fun i ↦ rfl
  have hprod' : ∏ i : Fin (2 * (m + 1)), ‖Matrix.vecCons u w i‖ = ‖u‖ * ∏ i, ‖w i‖ :=
    (Fin.prod_univ_succ (fun i : Fin (2 * m + 1 + 1) ↦ ‖Matrix.vecCons u w i‖)).trans (by simp)
  rw [wedgePow_succ_apply_vecCons, ← wedge_def, hprod']
  calc ‖((m : ℝ) + 1) * (curryLeftTopological (n := 1) ω u).wedge (ω.wedgePow m)
          (w ∘ Fin.cast (Nat.add_comm 1 (2 * m)))‖
      ≤ (m + 1) * (‖curryLeftTopological (n := 1) ω u‖ * ‖ω.wedgePow m‖ * ∏ i, ‖w i‖) := by
        rw [norm_mul, Real.norm_of_nonneg (by positivity), ← hprod]
        gcongr
        exact ((curryLeftTopological ω u).wedge (ω.wedgePow m)).le_opNorm _ |>.trans
          (by gcongr; exact norm_wedge_le_norm_mul_norm _ _)
    _ ≤ (m + 1) * (‖ω‖ * ‖u‖ * ‖ω.wedgePow m‖ * ∏ i, ‖w i‖) := by
        gcongr
        -- Inserting `u` is Mathlib's normed `curryLeft`, of norm `‖ω‖`.
        rw [← curryLeft_eq_curryLeftTopological, ← norm_curryLeft ω]
        exact (curryLeft ω).le_opNorm u
    _ = (m + 1) * ‖ω‖ * ‖ω.wedgePow m‖ * (‖u‖ * ∏ i, ‖w i‖) := by ring

/-- **The Wirtinger bound for two-forms**: the `m`-th wedge power of a real two-form `ω` on a real
inner product space has comass `‖ω ^ m‖ ≤ m! ‖ω‖ ^ m`. -/
theorem norm_wedgePow_le (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) :
    ‖ω.wedgePow m‖ ≤ m.factorial * ‖ω‖ ^ m := by
  induction m with
  | zero =>
    have h : ω.wedgePow 0 = constOfIsEmpty ℝ E (Fin 0) 1 := by ext v; simp
    simp [h]
  | succ m ih =>
    calc ‖ω.wedgePow (m + 1)‖ ≤ (m + 1) * ‖ω‖ * ‖ω.wedgePow m‖ := norm_wedgePow_succ_le ω m
      _ ≤ (m + 1) * ‖ω‖ * (m.factorial * ‖ω‖ ^ m) := by gcongr
      _ = (m + 1).factorial * ‖ω‖ ^ (m + 1) := by push_cast [Nat.factorial_succ]; ring

section Alternatize

open Module Set
open scoped ENNReal RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Sharp comass bound for wedging with a one-form.** On a real inner product space,
`‖α ∧ ω‖ ≤ ‖α‖ * ‖ω‖` without a degree factor `(k + 1)`. -/
theorem norm_alternatizeUncurryFin_smulRight_le (α : E →L[ℝ] ℝ) (ω : E [⋀^Fin k]→L[ℝ] F) :
    ‖alternatizeUncurryFin (α.smulRight ω)‖ ≤ ‖α‖ * ‖ω‖ := by
  refine (opNorm_le_iff_le_orthonormal (by positivity)).2 fun v hv ↦ ?_
  let W := Submodule.span ℝ (range v)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_range v)
  let w : Fin (k + 1) → W := fun i ↦ ⟨v i, Submodule.subset_span (mem_range_self i)⟩
  let αW : W →L[ℝ] ℝ := α.comp W.subtypeL
  by_cases hαW : αW = 0
  · have hv0 (i : Fin (k + 1)) : α (v i) = 0 := by
      simpa [αW, w] using DFunLike.congr_fun hαW (w i)
    have hzero : alternatizeUncurryFin (α.smulRight ω) v = 0 := by
      simp [alternatizeUncurryFin_apply, hv0]
    rw [hzero, norm_zero]
    positivity
  · -- Extend the unit Riesz vector of `α|_W` to an orthonormal basis `b` of `W`; `α` vanishes on
    -- `b j.succ`, so only the `0`-th term survives in the alternating sum.
    let u : W := (InnerProductSpace.toDual ℝ W).symm αW
    have hu_norm : ‖(u : E)‖ ≠ 0 := by simpa [u] using hαW
    let u₀ : W := ‖u‖⁻¹ • u
    have hu₀_norm : ‖u₀‖ = 1 := by simp [u₀, norm_smul, inv_mul_cancel₀ hu_norm]
    have horth : Orthonormal ℝ (({0} : Set (Fin (k + 1))).domRestrict fun _ ↦ u₀) :=
      ⟨fun _ ↦ hu₀_norm, fun i j hij ↦ False.elim (hij (Subsingleton.elim i j))⟩
    obtain ⟨b, hb0⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
      (by simpa using finrank_span_eq_card hv.linearIndependent)
    have hb_succ (j : Fin k) : α (b j.succ : E) = 0 := by
      have h0 : ⟪u₀, b j.succ⟫ = 0 :=
        hb0 0 (mem_singleton 0) ▸ b.orthonormal.2 (Fin.succ_ne_zero j).symm
      have hinner : ⟪u, b j.succ⟫ = 0 := by
        simpa [u₀, real_inner_smul_left, inv_eq_zero, hu_norm] using h0
      simpa [u, αW] using (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := W)).symm.trans hinner
    -- Restrict to `W` (dimension `k + 1`), where the operator norm equals `‖ψ b‖`.
    let ψ := (alternatizeUncurryFin (α.smulRight ω)).compContinuousLinearMap W.subtypeL
    have hle : ‖alternatizeUncurryFin (α.smulRight ω) v‖ ≤ ‖ψ‖ := by
      simpa [ψ, w, Function.comp_def, fun i ↦ hv.norm_eq_one i] using ψ.le_opNorm w
    refine hle.trans ?_
    rw [ψ.norm_eq_norm_apply_orthonormalBasis b]
    have hψb : ψ b = α (b 0 : E) • ω (fun j ↦ (b j.succ : E)) := by
      have hrem : Fin.removeNth 0 (fun i : Fin (k + 1) ↦ (b i : E)) =
          fun j : Fin k ↦ (b j.succ : E) := by
        ext j
        simp [Fin.removeNth_zero, Fin.tail]
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, alternatizeUncurryFin_apply,
        Fin.sum_univ_succ]
      simp [Function.comp_def, hb_succ, hrem]
    rw [hψb, norm_smul, Real.norm_eq_abs]
    have hbnorm (i : Fin (k + 1)) : ‖(b i : E)‖ = 1 := by
      rw [Submodule.norm_coe]
      exact b.orthonormal.norm_eq_one i
    calc |α (b 0 : E)| * ‖ω (fun j ↦ (b j.succ : E))‖
        ≤ (‖α‖ * ‖(b 0 : E)‖) * (‖ω‖ * ∏ j : Fin k, ‖(b j.succ : E)‖) := by
          gcongr
          · exact α.le_opNorm (b 0 : E)
          · exact ω.le_opNorm _
      _ = ‖α‖ * ‖ω‖ := by simp [hbnorm]

/-- Extended-norm form of `ContinuousAlternatingMap.norm_alternatizeUncurryFin_smulRight_le`. -/
theorem enorm_alternatizeUncurryFin_smulRight_le (α : E →L[ℝ] ℝ) (ω : E [⋀^Fin k]→L[ℝ] F) :
    ‖alternatizeUncurryFin (α.smulRight ω)‖ₑ ≤ ‖α‖ₑ * ‖ω‖ₑ := by
  simp only [eNorm_eq_nnNorm]
  exact_mod_cast norm_alternatizeUncurryFin_smulRight_le α ω

end Alternatize

end ContinuousAlternatingMap
