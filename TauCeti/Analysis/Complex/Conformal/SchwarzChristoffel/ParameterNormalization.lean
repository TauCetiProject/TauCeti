/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.AffineCovariance
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.JordanPolygon

/-!
# Normalized Schwarz--Christoffel parameters

Positive affine changes of the real line do not change the polygonal domain represented by a
Schwarz--Christoffel map.  This file uses that covariance to remove the two real affine degrees of
freedom from the prevertices: one chosen prevertex is placed at `0`, and the distance to a second
chosen prevertex is normalized to `1`.  Its sign records their boundary order, which a
holomorphic change of upper-half-plane coordinate cannot reverse.

The main theorem gives this normalization for the Schwarz--Christoffel representation of a
bounded polygonal Jordan domain.  Thus the remaining parameters live in a finite-dimensional
slice rather than carrying a redundant translation and positive scaling.

## Main results

* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_affine_prevertices` -- a positive
  affine change of all prevertices preserves the represented domain, after adjusting the two
  complex affine constants.
* `TauCeti.exists_bijOn_normalized_schwarzChristoffelPrimitive_of_isJordanCurve_frontier` -- the
  Schwarz--Christoffel representation of a polygonal Jordan domain can be chosen with one
  prevertex equal to `0` and a second at distance `1`.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

noncomputable section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A positive affine change of the prevertices scales their Schwarz--Christoffel boundary values
by the same factor as the primitive.  Keeping the original base point introduces the displayed
translation, independent of the chosen prevertex. -/
theorem schwarzChristoffelVertex_affine_prevertices (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) (j : ι)
    (hj : -1 < ∑ i with a i = a j, e i) :
    schwarzChristoffelVertex (fun i ↦ c * a i + d) e z₀ j =
      (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ) *
        schwarzChristoffelVertex a e z₀ j -
      schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)) z₀ := by
  let a' : ι → ℝ := fun i ↦ c * a i + d
  let z₀' : UpperHalfPlane := d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  let φ : ℂ → ℂ := fun z ↦ (c : ℂ) * z + (d : ℂ)
  have hc0 : c ≠ 0 := hc.ne'
  have hj' : -1 < ∑ i with a' i = a' j, e i := by
    have hfiber (i : ι) : a' i = a' j ↔ a i = a j := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc0
        exact add_right_cancel h
      · exact fun h ↦ congrArg (fun x ↦ c * x + d) h
    simpa only [hfiber] using hj
  have hφ_maps : MapsTo φ upperHalfPlaneSet upperHalfPlaneSet := by
    intro z hz
    simpa [upperHalfPlaneSet, φ, mul_im] using mul_pos hc hz
  have hφ_tendsto : Tendsto φ (𝓝[upperHalfPlaneSet] (a j : ℂ))
      (𝓝[upperHalfPlaneSet] (a' j : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt φ (a j : ℂ) := by fun_prop
      have ht := hcont.tendsto.mono_left
        (@inf_le_left (Filter ℂ) _ (𝓝 (a j : ℂ)) (𝓟 upperHalfPlaneSet))
      have hcenter : ((a' j : ℝ) : ℂ) = φ (a j : ℂ) := by
        dsimp only [a', φ]
        push_cast
        rfl
      rw [hcenter]
      exact ht
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hφ_maps hz
  have hleft :=
    (tendsto_schwarzChristoffelPrimitive a' e z₀' j hj').comp hφ_tendsto
  have hright : Tendsto (fun z ↦ C * schwarzChristoffelPrimitive a e z₀ z)
      (𝓝[upperHalfPlaneSet] (a j : ℂ))
      (𝓝 (C * schwarzChristoffelVertex a e z₀ j)) :=
    tendsto_const_nhds.mul (tendsto_schwarzChristoffelPrimitive a e z₀ j hj)
  have heq : (fun z ↦ schwarzChristoffelPrimitive a' e z₀' (φ z)) =ᶠ[
      𝓝[upperHalfPlaneSet] (a j : ℂ)]
      (fun z ↦ C * schwarzChristoffelPrimitive a e z₀ z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot (a j)
  have hvertex : schwarzChristoffelVertex a' e z₀' j =
      C * schwarzChristoffelVertex a e z₀ j :=
    tendsto_nhds_unique hleft (hright.congr' heq.symm)
  rw [schwarzChristoffelVertex_change_base a' e z₀ z₀' j hj', hvertex]

/-- A positive affine change of all real prevertices preserves the domain represented by an
affine image of the Schwarz--Christoffel primitive.  The normalization point of the primitive is
kept fixed; its change under reparametrization is absorbed into the additive constant.  At every
integrable prevertex, the adjusted affine images of the old and new boundary values agree. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_affine_prevertices
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ)
    {A B : ℂ} {U : Set ℂ}
    (hbij : BijOn (fun z ↦ A * schwarzChristoffelPrimitive a e z₀ z + B)
      upperHalfPlaneSet U) (hA : A ≠ 0) :
    ∃ A' : ℂ, A' ≠ 0 ∧ ∃ B' : ℂ,
      BijOn (fun z ↦ A' *
        schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e z₀ z + B')
        upperHalfPlaneSet U ∧
      ∀ j, -1 < ∑ i with a i = a j, e i →
        A' * schwarzChristoffelVertex (fun i ↦ c * a i + d) e z₀ j + B' =
          A * schwarzChristoffelVertex a e z₀ j + B := by
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  let z₀' : UpperHalfPlane := d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)
  let A' : ℂ := A * C⁻¹
  let B' : ℂ := B + A' *
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e z₀' z₀
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hC : C ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc0)
  have hA' : A' ≠ 0 := mul_ne_zero hA (inv_ne_zero hC)
  let φ : ℂ → ℂ := fun z ↦ (c : ℂ) * z + (d : ℂ)
  have hφ : BijOn φ upperHalfPlaneSet upperHalfPlaneSet := by
    refine ⟨fun z hz ↦ ?_, fun x hx y hy hxy ↦ ?_, fun w hw ↦ ?_⟩
    · simpa [upperHalfPlaneSet, φ, mul_im] using mul_pos hc hz
    · exact mul_left_cancel₀ hc0 (add_right_cancel hxy)
    · let w' : UpperHalfPlane := ⟨w, hw⟩
      let z : UpperHalfPlane :=
        (⟨c⁻¹, inv_pos.mpr hc⟩ : {x : ℝ // 0 < x}) • (-d +ᵥ w')
      refine ⟨(z : ℂ), z.im_pos, ?_⟩
      · dsimp only [φ]
        have hcoe : (z : ℂ) = (c⁻¹ : ℝ) • ((-d : ℝ) + w) := by
          rw [UpperHalfPlane.coe_pos_real_smul, UpperHalfPlane.coe_vadd]
        rw [hcoe]
        simp only [Complex.real_smul]
        push_cast
        field_simp
        ring
  have heq : Set.EqOn
      ((fun w ↦ A' *
        schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e z₀ w + B') ∘ φ)
      (fun z ↦ A * schwarzChristoffelPrimitive a e z₀ z + B)
      upperHalfPlaneSet := by
    intro z hz
    rw [Function.comp_apply,
      schwarzChristoffelPrimitive_change_base (fun i ↦ c * a i + d) e z₀ z₀'
        (hφ.mapsTo hz),
      schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz]
    dsimp only [A', B']
    field_simp
    ring
  refine ⟨A', hA', B', ?_, fun j hj ↦ ?_⟩
  · rw [← hφ.image_eq]
    exact (bijOn_comp_iff hφ.injOn).mp (hbij.congr heq.symm)
  · rw [schwarzChristoffelVertex_affine_prevertices a e z₀ hc d j hj]
    dsimp only [A', B']
    field_simp
    ring

/-- **Normalized Schwarz--Christoffel parameters for a polygonal Jordan domain.**

Under the polygonal boundary hypotheses, choose two distinct labelled vertices `i` and `j`.
There is a Schwarz--Christoffel representation of the domain whose `i`-th prevertex is `0` and
whose `j`-th prevertex has absolute value `1`.  The sign of that prevertex records whether `j`
comes before or after `i` in the boundary orientation. -/
theorem exists_bijOn_normalized_schwarzChristoffelPrimitive_of_isJordanCurve_frontier
    (e : ι → ℝ) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ} (hv : Function.Injective v)
    (hside : ∀ w ∈ frontier U, (∀ k, w ≠ v k) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ Metric.ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ k, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧
      ∀ z ∈ Metric.ball (v k) ρ, z ≠ v k →
        (z ∈ U ↔ |((z - v k) / b).arg| < (e k + 1) * Real.pi / 2))
    (i j : ι) (hij : i ≠ j) :
    ∃ a : ι → ℝ, Function.Injective a ∧ a i = 0 ∧ |a j| = 1 ∧
      ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
        BijOn (fun z ↦ A * schwarzChristoffelPrimitive a e z₀ z + B)
          upperHalfPlaneSet U ∧
        ∀ k, A * schwarzChristoffelVertex a e z₀ k + B = v k := by
  obtain ⟨a, ha, A, hA, B, hbij, hvertex⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier
      e he z₀ hUo hUc hUb hUJ hv hside hcorner
  have hgap : a j - a i ≠ 0 := sub_ne_zero.mpr (ha.ne hij.symm)
  let c : ℝ := |a j - a i|⁻¹
  let d : ℝ := -c * a i
  have hc : 0 < c := inv_pos.mpr (abs_pos.mpr hgap)
  let a' : ι → ℝ := fun k ↦ c * a k + d
  have ha' : Function.Injective a' := fun k l hkl ↦ by
    dsimp only [a'] at hkl
    exact ha (mul_left_cancel₀ hc.ne' (add_right_cancel hkl))
  have hai : a' i = 0 := by
    dsimp only [a', d]
    ring
  have haj : |a' j| = 1 := by
    dsimp only [a', d]
    have habs : |c * a j + -c * a i| = c * |a j - a i| := by
      have h : c * a j + -c * a i = c * (a j - a i) := by ring
      rw [h, abs_mul, abs_of_pos hc]
    rw [habs]
    exact inv_mul_cancel₀ (abs_ne_zero.mpr hgap)
  obtain ⟨A', hA', B', hbij', hvertex'⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_affine_prevertices
      a e z₀ hc d hbij hA
  refine ⟨a', ha', hai, haj, A', hA', B', hbij', fun k ↦ ?_⟩
  have hsum : ∑ l with a l = a k, e l = e k := by
    classical
    have hf : Finset.univ.filter (fun l ↦ a l = a k) = {k} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ha.eq_iff
    rw [hf, Finset.sum_singleton]
  rw [hvertex' k (by rw [hsum]; exact (he k).1), hvertex k]

end TauCeti

end
