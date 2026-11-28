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
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Uncurry

/-!
# Comass of wedge products with a one-form

On a real inner product space the operator norm of a real alternating form is its comass, the
supremum of its absolute values on orthonormal frames
(`ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal`). For forms of arbitrary degrees the
comass of a wedge product is only bounded by a binomial multiple of the product of the comasses
(`ContinuousAlternatingMap.norm_wedge_le`). When the first factor is a one-form `α` the binomial
coefficient is not needed: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`.

To see this more generally for `alternatizeUncurryFin (α.smulRight ω)` with covector `α` and
vector-valued alternating form `ω`, evaluate on an orthonormal frame `v` and take the Riesz vector
of `α` restricted to `span (range v)`. Extending its unit vector to an orthonormal basis `b` of the
span makes `α` vanish on `b j.succ`, so only the `0`-th term survives in the alternating sum and
`‖alternatizeUncurryFin (α.smulRight ω)‖ ≤ ‖α‖ * ‖ω‖` with no `(k + 1)` degree factor. Identifying a
real one-form with a covector via `ContinuousAlternatingMap.ofSubsingletonLIE` gives
`‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`.

With the power rule `ι_v (ω ^ (m + 1)) = (m + 1) • (ι_v ω ∧ ω ^ m)` for a two-form `ω`, this
bounds the comass of the wedge powers of every real two-form: `‖ω ^ m‖ ≤ m! ‖ω‖ ^ m`. For a
two-form of comass at most one, such as the Kähler form of an orthogonal complex structure, the
normalized power `ω ^ m / m!` therefore has comass at most one; this is the Wirtinger inequality.

## Main results

* `ContinuousAlternatingMap.norm_alternatizeUncurryFin_smulRight_le`,
  `ContinuousAlternatingMap.enorm_alternatizeUncurryFin_smulRight_le`: sharp comass bounds
  `‖alternatizeUncurryFin (α.smulRight ω)‖ ≤ ‖α‖ * ‖ω‖` (and extended-norm form) for a
  covector `α` and a vector-valued alternating form `ω`.
* `ContinuousAlternatingMap.norm_wedge_le_norm_mul_norm`: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖` for a one-form `α`.
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

open Module Set
open scoped ENNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k l : ℕ}

section Alternatize

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

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

/-- **The comass of a wedge with a one-form**: `‖α ∧ ψ‖ ≤ ‖α‖ ‖ψ‖`, with no binomial factor. -/
theorem norm_wedge_le_norm_mul_norm (α : E [⋀^Fin 1]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    ‖α.wedge ψ‖ ≤ ‖α‖ * ‖ψ‖ := by
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  let a : E →L[ℝ] ℝ := (ofSubsingletonLIE (0 : Fin 1)).symm α
  have ha_eq : ofSubsingleton ℝ E ℝ (0 : Fin 1) a = α :=
    (ofSubsingletonLIE (0 : Fin 1)).apply_symm_apply α
  let w : Fin (l + 1) → E := v ∘ Fin.cast (Nat.add_comm l 1)
  have hval : α.wedge ψ v = alternatizeUncurryFin (a.smulRight ψ) w := by
    simpa [w, ha_eq, Function.comp_def] using
      (alternatizeUncurryFin_smulRight_apply_eq_wedge a ψ w).symm
  have hprod : ∏ i, ‖w i‖ = ∏ i, ‖v i‖ :=
    Fintype.prod_equiv (finCongr (Nat.add_comm l 1)) _ _ fun _ ↦ rfl
  rw [hval]
  refine (alternatizeUncurryFin (a.smulRight ψ)).le_opNorm w |>.trans ?_
  rw [hprod, ← (ofSubsingletonLIE (0 : Fin 1)).symm.norm_map α]
  gcongr
  exact norm_alternatizeUncurryFin_smulRight_le a ψ

/-- **One step of the Wirtinger bound**: `‖ω ^ (m + 1)‖ ≤ (m + 1) ‖ω‖ ‖ω ^ m‖` for a real
two-form `ω`. -/
theorem norm_wedgePow_succ_le (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) :
    ‖ω.wedgePow (m + 1)‖ ≤ (m + 1) * ‖ω‖ * ‖ω.wedgePow m‖ := by
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  obtain ⟨u, w, rfl⟩ : ∃ (u : E) (w : Fin (2 * m + 1) → E), v = Matrix.vecCons u w :=
    ⟨Matrix.vecHead v, Matrix.vecTail v, (Matrix.cons_head_tail v).symm⟩
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

end ContinuousAlternatingMap
