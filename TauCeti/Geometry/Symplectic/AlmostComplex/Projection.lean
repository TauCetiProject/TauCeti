/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Taming forms for complex structures with a complex-linear projection

Let `π : V → E` be a linear map of finite-dimensional real vector spaces, and let `J` and `J_E`
be linear complex structures on `V` and `E` for which `π` is complex linear,
`π (J v) = J_E (π v)`. The kernel of `π`, the vertical subspace, is then `J`-invariant. If a
symplectic form `ω` on `E` tames `J_E`, the pullback `π^* ω` is nonnegative on the complex lines
of `J`: `ω (π v) (π (J v)) ≥ 0`, with equality exactly on the vertical vectors. If moreover an
alternating form `σ` on `V` tames `J` on the vertical subspace, then for every sufficiently large
`t` the form

`Ω_t = t π^* ω + σ`

tames `J` on all of `V`, and so is a symplectic form taming `J`.

This is the pointwise linear algebra of Thurston's construction of symplectic forms on symplectic
fibrations, and of taming forms on disc bundles. On the normal bundle of a pseudoholomorphic
curve `C`, with projection `π` to `C`, consider an almost complex structure for which the fibres
are complex and `π` is complex linear, such as the normal linearization of an ambient structure
along `C`. Let `ω_C` tame the complex structure of `C`, and let `dλ` restrict on each fibre to an
area form taming the complex structure of that fibre. At each point of the disc bundle of a fixed
radius, the results below then make `t π^* ω_C + dλ` tame the structure for all large `t`. The
constant `t` must be uniform over the points of the disc bundle, which form a compact family once
the radius is fixed. The results are therefore stated for families of data that are continuous on
a compact parameter set `S`; a single structure is the case of a one-point set.

The proof is the case of Finsler's lemma where the first form is positive semidefinite, for
compact families of bilinear forms
(`IsCompact.eventually_exists_pos_forall_mul_norm_sq_le_mul_add`), applied to
`a_x(v, w) = ω_x (π v) (π (J_x w))` and `b_x(v, w) = σ_x v (J_x w)`.

## Main results

* `TauCeti.SymplecticForm.eventually_exists_pos_forall_mul_norm_sq_le_mul_apply_add_apply`: over
  a compact family, for every large `t` one constant `c > 0` gives
  `c ‖v‖² ≤ t ω_x (π v) (π (J_x v)) + σ_x v (J_x v)`.
* `TauCeti.SymplecticForm.eventually_forall_exists_tames`: over a compact family with alternating
  `σ_x`, for every large `t` each form `t π^* ω_x + σ_x` is a symplectic form taming `J_x`.

## References

* W. P. Thurston, *Some simple examples of symplectic manifolds*, Proc. Amer. Math. Soc. 55
  (1976), 467–468.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Oxford University Press,
  Chapter 6 (symplectic fibrations and Thurston's construction).
* P. Finsler, *Über das Vorkommen definiter und semidefiniter Formen in Scharen quadratischer
  Formen*, Comment. Math. Helv. 9 (1937), 188–192.
-/

public section

open Filter

namespace TauCeti

namespace SymplecticForm

section Projection

variable {V E X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace X]
  {S : Set X} {π : V →L[ℝ] E} {J : X → AlmostComplexStructure V}
  {JE : X → AlmostComplexStructure E} {σ : X → V →L[ℝ] V →L[ℝ] ℝ}

/-- **Uniform taming by a large multiple of a pulled-back form.** Let `π : V → E` be complex
linear from `J_x` to `J_E x`, let `ω_x` tame `J_E x`, and let `σ_x` satisfy `σ_x v (J_x v) > 0`
for every nonzero vertical vector `v`, `π v = 0`, for every `x` in a compact set `S` on which the
data depend continuously. Then for every sufficiently large `t` one constant `c > 0` gives

`c ‖v‖² ≤ t ω_x (π v) (π (J_x v)) + σ_x v (J_x v)`

for every `x ∈ S` and every `v`. -/
theorem eventually_exists_pos_forall_mul_norm_sq_le_mul_apply_add_apply
    (ω : X → SymplecticForm E) (hS : IsCompact S)
    (hJ : ContinuousOn (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) S)
    (hω : ContinuousOn (fun x ↦ (ω x).toBilinForm.toContinuousBilinearMap) S)
    (hσ : ContinuousOn σ S) (hπ : ∀ x ∈ S, ∀ v, π (J x v) = JE x (π v))
    (hωJ : ∀ x ∈ S, (ω x).Tames (JE x))
    (hσJ : ∀ x ∈ S, ∀ v, v ≠ 0 → π v = 0 → 0 < σ x v (J x v)) :
    ∀ᶠ t in atTop, ∃ c > 0, ∀ x ∈ S, ∀ v,
      c * ‖v‖ ^ 2 ≤ t * ω x (π v) (π (J x v)) + σ x v (J x v) := by
  set Jc : X → V →L[ℝ] V := fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap
  set ωc : X → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ (ω x).toBilinForm.toContinuousBilinearMap
  -- The forms `a_x(v, w) = ω_x (π v) (π (J_x w))` and `b_x(v, w) = σ_x v (J_x w)`.
  set a : X → V →L[ℝ] V →L[ℝ] ℝ := fun x ↦ ((ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc x)).comp
    (((ContinuousLinearMap.compL ℝ V E ℝ).flip π).comp ((ωc x).comp π))
  set b : X → V →L[ℝ] V →L[ℝ] ℝ := fun x ↦
    ((ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc x)).comp (σ x)
  have ha_apply (x : X) (v : V) : a x v v = ω x (π v) (π (J x v)) := by simp [a, Jc, ωc]
  have hb_apply (x : X) (v : V) : b x v v = σ x v (J x v) := by simp [b, Jc]
  -- `π^* ω_x` is nonnegative on complex lines, and vanishes there only on vertical vectors.
  have hpos (x : X) (hx : x ∈ S) (v : V) (hv : π v ≠ 0) : 0 < ω x (π v) (π (J x v)) := by
    simpa [hπ x hx v] using hωJ x hx (π v) hv
  have ha₀ (x : X) (hx : x ∈ S) (v : V) : 0 ≤ a x v v := by
    rw [ha_apply]
    by_cases hv : π v = 0
    · simp [hv]
    · exact (hpos x hx v hv).le
  have hcont : ContinuousOn a S ∧ ContinuousOn b S := by
    have hJ' : ContinuousOn (fun x ↦ (ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc x)) S :=
      (ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.comp_continuousOn hJ
    exact ⟨hJ'.clm_comp (continuousOn_const.clm_comp (hω.clm_comp continuousOn_const)),
      hJ'.clm_comp hσ⟩
  filter_upwards [hS.eventually_exists_pos_forall_mul_norm_sq_le_mul_add hcont.1 hcont.2 ha₀
    fun x hx v hv h0 ↦ by
      rw [ha_apply] at h0
      have hπv : π v = 0 := by
        by_contra hπv
        exact (hpos x hx v hπv).ne' h0
      simpa [hb_apply] using hσJ x hx v hv hπv] with t ⟨c, hc, h⟩
  exact ⟨c, hc, fun x hx v ↦ by simpa [ha_apply, hb_apply] using h x hx v⟩

/-- **Taming forms `t π^* ω + σ` over a compact family.** Under the hypotheses of
`TauCeti.SymplecticForm.eventually_exists_pos_forall_mul_norm_sq_le_mul_apply_add_apply`, if
moreover each `σ_x` is alternating, then for every sufficiently large `t` and every `x ∈ S` the
form `t π^* ω_x + σ_x` is a symplectic form taming `J_x`. -/
theorem eventually_forall_exists_tames
    (ω : X → SymplecticForm E) (hS : IsCompact S)
    (hJ : ContinuousOn (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) S)
    (hω : ContinuousOn (fun x ↦ (ω x).toBilinForm.toContinuousBilinearMap) S)
    (hσ : ContinuousOn σ S) (hσa : ∀ x ∈ S, ∀ v, σ x v v = 0)
    (hπ : ∀ x ∈ S, ∀ v, π (J x v) = JE x (π v)) (hωJ : ∀ x ∈ S, (ω x).Tames (JE x))
    (hσJ : ∀ x ∈ S, ∀ v, v ≠ 0 → π v = 0 → 0 < σ x v (J x v)) :
    ∀ᶠ t in atTop, ∀ x ∈ S, ∃ Ω : SymplecticForm V,
      (∀ v w, Ω v w = t * ω x (π v) (π w) + σ x v w) ∧ Ω.Tames (J x) := by
  filter_upwards [eventually_exists_pos_forall_mul_norm_sq_le_mul_apply_add_apply ω hS hJ hω hσ
    hπ hωJ hσJ] with t ⟨c, hc, h⟩ x hx
  set B : LinearMap.BilinForm ℝ V :=
    t • (ω x).toBilinForm.compl₁₂ (π : V →ₗ[ℝ] E) π + (σ x).toBilinForm
  have hB (v w : V) : B v w = t * ω x (π v) (π w) + σ x v w := by simp [B]
  have hJB : ∀ v, v ≠ 0 → 0 < B v (J x v) := fun v hv ↦ by
    rw [hB]
    exact (mul_pos hc (by positivity)).trans_le (h x hx v)
  have hBa : B.IsAlt := fun v ↦ by simp [hB, hσa x hx v]
  exact ⟨ofTames B hBa hJB, fun v w ↦ by simp only [ofTames_apply, hB], tames_ofTames hBa hJB⟩

end Projection

end SymplecticForm

end TauCeti
