/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Vector fields transverse to a map

A vector field `Z` on a manifold `M` is **transverse along** a map `ι : S → M`
(`TauCeti.IsTransverseAlong`) when at every point `s` of `S` the vector `Z (ι s)` is not tangent
to `ι`: it does not lie in the range of the differential `dι_s`. When `ι` is an embedded
hypersurface, so that this range has codimension one, this is transversality of `Z` to the
hypersurface in the usual sense: `Z (ι s)` and the tangent space of the hypersurface at `s` span
the tangent space of `M` at `ι s`. A transverse vector field does not vanish along `ι`
(`TauCeti.IsTransverseAlong.ne_zero`). If moreover `S` has one dimension less than `M`, a function
vanishing on the image of `ι` near `s` whose derivative along `Z` vanishes at `ι s` has zero
differential there (`TauCeti.mvfderiv_eq_zero_of_comp_eventuallyEq_zero`).

For a regular level `f⁻¹(c)` of a scalar function, with its preferred atlas
`TauCeti.regularLevelChartedSpace`, the tangent space at `x` is the kernel of `df_x`
(`TauCeti.range_mfderiv_coe_regularLevel`). So a vector field is transverse along the
inclusion of the level exactly when `df(Z) ≠ 0` at every point of the level
(`TauCeti.isTransverseAlong_coe_scalarRegularLevel_iff`). This is how transversality to the
hypersurfaces of symplectic geometry (energy levels, boundaries of domains, cosphere bundles) is
checked in practice.

A vector field crossing a level of `f` in the direction of increasing `f`, `df(Z) > 0`, leaves the
sublevel set there: a point where `df` does not vanish is not a local maximum, by Fermat's theorem,
so every point of the level is a limit of points where `f` is larger
(`TauCeti.mem_closure_setOf_lt_of_mvfderiv_pos`). Hence the frontier of the sublevel set `{f ≤ c}`
is exactly the level `f⁻¹(c)` when `df(Z) > 0` along it
(`TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`). This identifies the boundary of a domain whose
boundary is crossed outwards by a vector field, as for Liouville domains.

## Main definitions

* `TauCeti.IsTransverseAlong`: `Z (ι s)` is outside the range of `dι_s` for every `s`.

## Main results

* `TauCeti.mvfderiv_eq_zero_of_comp_eventuallyEq_zero`: on a transverse slice of codimension one,
  a function vanishing on the slice and killed by `Z` has zero differential.
* `TauCeti.isTransverseAlong_coe_scalarRegularLevel_iff`: transversality along a regular level is
  the nonvanishing of `df(Z)` on the level.
* `TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`: the frontier of a sublevel set whose level is
  crossed outwards by a vector field is the level.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 5
  (vector fields transverse to a hypersurface).
-/

public section

open Filter Module Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

variable (J) in
/-- A vector field `Z` on `M` is **transverse along** a map `ι : S → M` when at every point `s`
the vector `Z (ι s)` is not tangent to `ι`, that is, not in the range of the differential `dι_s`.
For an embedded hypersurface this is transversality of `Z` to the hypersurface. -/
def IsTransverseAlong (Z : (x : M) → TangentSpace I x) (ι : S → M) : Prop :=
  ∀ s, Z (ι s) ∉ (mfderiv J I ι s).range

/-- The defining characterization of a vector field transverse along a map. -/
theorem isTransverseAlong_iff {Z : (x : M) → TangentSpace I x} {ι : S → M} :
    IsTransverseAlong J Z ι ↔ ∀ s, Z (ι s) ∉ (mfderiv J I ι s).range :=
  Iff.rfl

/-- A vector field transverse along `ι` does not vanish at the points of the image of `ι`. -/
theorem IsTransverseAlong.ne_zero {Z : (x : M) → TangentSpace I x} {ι : S → M}
    (h : IsTransverseAlong J Z ι) (s : S) : Z (ι s) ≠ 0 :=
  fun h0 ↦ h s (h0 ▸ Submodule.zero_mem _)

/-- If `Z` is transverse along `ι` and the differential `dι_s` is injective, then
`(a, w) ↦ a Z (ι s) + dι_s w` is injective. This is the differential of a flow-out at time zero. -/
theorem IsTransverseAlong.injective_smul_add {Z : (x : M) → TangentSpace I x} {ι : S → M}
    (h : IsTransverseAlong J Z ι) {s : S} (himm : Function.Injective (mfderiv J I ι s)) :
    Function.Injective fun v : ℝ × E' ↦ v.1 • Z (ι s) + mfderiv J I ι s v.2 := by
  rintro ⟨a, w⟩ ⟨b, u⟩ hv
  -- `w` and `u` are tangent vectors at `s`, that is vectors of the model space `E'`.
  set d : TangentSpace J s := w - u
  have h0 : (a - b) • Z (ι s) + mfderiv J I ι s d = 0 := by
    have hd : mfderiv J I ι s d = mfderiv J I ι s w - mfderiv J I ι s u := map_sub _ _ _
    simp only at hv
    rw [sub_smul, hd, ← sub_eq_zero.2 hv]
    abel
  obtain hab : a - b = 0 := by
    by_contra hab
    refine h s (LinearMap.mem_range.2 ⟨-(a - b)⁻¹ • d, ((mfderiv J I ι s).map_smul _ _).trans ?_⟩)
    rw [eq_neg_of_add_eq_zero_right h0, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hab,
      neg_smul, one_smul, neg_neg]
  rw [hab, zero_smul, zero_add, ← map_zero (mfderiv J I ι s)] at h0
  exact Prod.ext (sub_eq_zero.1 hab) (sub_eq_zero.1 (himm h0))

/-- If `Z` is transverse along `ι` and the differential `dι_s` is injective, then
`a Z (ι s) + dι_s w = 0` only for `a = 0` and `w = 0`. -/
theorem IsTransverseAlong.eq_zero_of_smul_add_eq_zero {Z : (x : M) → TangentSpace I x}
    {ι : S → M} (h : IsTransverseAlong J Z ι) {s : S}
    (himm : Function.Injective (mfderiv J I ι s)) {a : ℝ} {w : TangentSpace J s}
    (hw : a • Z (ι s) + mfderiv J I ι s w = 0) : a = 0 ∧ w = 0 :=
  Prod.ext_iff.1 <| h.injective_smul_add himm (a₁ := (a, w)) (a₂ := (0, 0)) <|
    hw.trans (by simp only [zero_smul, zero_add]; exact (map_zero _).symm)

/-- **Vanishing of the differential on a transverse slice.** Let `ι : S → M` have injective
differential at `s`, with `Z (ι s)` outside its range, where `S` has one dimension less than `M`.
If a function `h` vanishes on the slice near `s` and its derivative along `Z` vanishes at `ι s`,
then its differential at `ι s` is zero. -/
theorem mvfderiv_eq_zero_of_comp_eventuallyEq_zero
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {Z : (x : M) → TangentSpace I x} {ι : S → M}
    {h : M → ℝ} {s : S}
    (h0 : h ∘ ι =ᶠ[𝓝 s] 0) (himm : Function.Injective (mfderiv J I ι s))
    (htr : Z (ι s) ∉ (mfderiv J I ι s).range) (hZ : mvfderiv I h (ι s) (Z (ι s)) = 0) :
    mvfderiv I h (ι s) = 0 := by
  -- A function that is not differentiable at `ι s` has zero differential there by convention.
  by_cases hh : MDifferentiableAt I 𝓘(ℝ) h (ι s)
  swap
  · simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hh]
  set L := (mfderiv J I ι s).toLinearMap
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hdim ▸ Nat.succ_pos _)
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv himm
  -- The differential of `h` kills the tangent space of the slice, since `h ∘ ι` vanishes near `s`
  -- (trivially when `ι` is not differentiable at `s`, as then `L = 0`).
  have hL (w : TangentSpace J s) : mvfderiv I h (ι s) (L w) = 0 := by
    by_cases hιs : MDifferentiableAt J I ι s
    · have hc := mvfderiv_comp_apply s hh hιs w
      rw [h0.mvfderiv_eq, mvfderiv_zero] at hc
      exact hc.symm
    · rw [show L w = 0 by simp [L, mfderiv_zero_of_not_mdifferentiableAt hιs], map_zero]
  -- The tangent space of the slice and the line through `Z (ι s)` span the tangent space of `M`.
  have htop : LinearMap.range L ⊔ ℝ ∙ Z (ι s) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Submodule.finrank_sup_span_singleton htr, LinearMap.finrank_range_of_inj himm]
    exact hdim
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : v ∈ LinearMap.range L ⊔ ℝ ∙ Z (ι s) := htop ▸ Submodule.mem_top
  obtain ⟨_, ⟨w, rfl⟩, _, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [map_add, map_smul, hL, hZ]
  simp

/-! ### Vector fields crossing a level outwards -/

section Crossing

variable [I.Boundaryless]

/-- **A direction increasing a function leaves its sublevel set.** If a tangent vector `v` at a
point `x` of a boundaryless manifold satisfies `df_x(v) > 0`, then `x` lies in the closure of the
set `{y | f x < f y}`: otherwise `x` would be a local maximum of `f`, hence a critical point by
Fermat's theorem (`IsLocalMax.mem_criticalPoints`), and `df_x` would vanish. -/
theorem mem_closure_setOf_lt_of_mvfderiv_pos {f : M → ℝ} {x : M} {v : TangentSpace I x}
    (hpos : 0 < mvfderiv I f x v) : x ∈ closure {y | f x < f y} := by
  by_contra h
  rw [mem_closure_iff_frequently, not_frequently] at h
  have hmax : IsLocalMax f x := h.mono fun y hy ↦ not_lt.1 hy
  simp [mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))] at hpos

/-- **The frontier of a sublevel set crossed outwards by a vector field.** Let `f` be continuous,
and let `Z` be a vector field with `df(Z) > 0` along the level `f⁻¹(c)`. Then the frontier of the
sublevel set `{f ≤ c}` is exactly the level `f⁻¹(c)`. -/
theorem frontier_setOf_le_eq_of_mvfderiv_pos {Z : (x : M) → TangentSpace I x} {f : M → ℝ}
    {c : ℝ} (hfc : Continuous f) (hpos : ∀ x, f x = c → 0 < mvfderiv I f x (Z x)) :
    frontier {x | f x ≤ c} = {x | f x = c} := by
  refine (frontier_le_subset_eq hfc continuous_const).antisymm fun x (hx : f x = c) ↦ ?_
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hx.le, closure_mono (fun y hy ↦ by simpa [← hx] using hy)
    (mem_closure_setOf_lt_of_mvfderiv_pos (hpos x hx))⟩

end Crossing

variable {f : M → ℝ} {c : ℝ} [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x) (hreg : IsRegularValue I 𝓘(ℝ) f c)

/-- **Transversality to a regular level.** A vector field `Z` is transverse along the inclusion of
a regular level `f⁻¹(c)`, with its preferred atlas `TauCeti.regularLevelChartedSpace`,
exactly when `df(Z) ≠ 0` at every point of the level. -/
theorem isTransverseAlong_coe_scalarRegularLevel_iff {Z : (x : M) → TangentSpace I x} :
    letI := regularLevelChartedSpace (n := finrank ℝ E - 1) hf hreg (by rw [finrank_self])
    IsTransverseAlong 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) Z (Subtype.val : {x : M // f x = c} → M) ↔
      ∀ x, f x = c → mfderiv I 𝓘(ℝ) f x (Z x) ≠ 0 := by
  let := regularLevelChartedSpace (n := finrank ℝ E - 1) hf hreg (by rw [finrank_self])
  simp only [isTransverseAlong_iff, range_mfderiv_coe_regularLevel hf hreg (by rw [finrank_self]),
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Subtype.forall]

end TauCeti
