/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Algebra.Field.LinearFractional
public import Mathlib.Analysis.Complex.UnitDisc.Basic
import TauCeti.Analysis.Complex.Conformal.Caratheodory
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Uniqueness
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Boundary correspondence of two conformal maps onto a Jordan domain

Let `f` and `g` be holomorphic bijections of the upper half-plane onto the same bounded domain `U`
whose frontier is a Jordan curve. Pair a real point `x` with a real point `y` when `f` at `x` and
`g` at `y` have the same boundary limit. Then `g⁻¹ ∘ f` is an automorphism of the upper
half-plane. Its boundary action is naturally defined on the extended real line, where a real
Möbius transformation may send a finite point to infinity. In the Cayley coordinate
`z ↦ (z - i) / (z + i)` it is a standard disc automorphism `w ↦ u * (w - c) / (1 - conj c * w)`.

Two consequences are recorded. Paired points have equal cross-ratios
`(x₁ - x₃) * (x₂ - x₄) / ((x₁ - x₄) * (x₂ - x₃))`. Three pairs `x ↦ x` force the Möbius map
to be the identity, so if `f` and `g` have the same boundary limits at three distinct real points
then `f = g`. This is the three-point normalization of conformal maps onto a Jordan domain.
Distinct real points also have distinct boundary limits. For Schwarz--Christoffel maps these
facts say that the prevertices of a polygon are determined up to a real Möbius transformation.

## Main results

* `TauCeti.exists_sub_I_div_add_I_eq_unitDiscStandardAutomorphismFormula_of_tendsto` -- in Cayley
  coordinates, the boundary correspondence is a disc automorphism.
* `TauCeti.crossRatio_eq_of_tendsto_of_bijOn_upperHalfPlaneSet` -- the boundary correspondence
  preserves cross-ratios.
* `TauCeti.eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn` -- two conformal maps onto a Jordan domain
  with the same boundary limits at three distinct real points coincide.
* `TauCeti.eq_of_tendsto_of_bijOn_upperHalfPlaneSet` -- a conformal map onto a Jordan domain has
  distinct boundary limits at distinct real points.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Sections 1--2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
-/

public section

open Bornology Complex Filter Function Metric Set Topology
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)

namespace TauCeti

/-! ### Transport to the disc -/

/-- **The two maps in a common disc picture.** Let `f` and `g` be holomorphic bijections of the
upper half-plane onto a bounded Jordan domain `U`. Then `g` is `G` after the Cayley transform `C`,
for some `G` continuous and injective on the closed unit disc, and `f` is `G ∘ M ∘ C` for a standard
disc automorphism `M`. -/
private theorem exists_disc_factorization {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hfU : BijOn f upperHalfPlaneSet U) (hgU : BijOn g upperHalfPlaneSet U) :
    ∃ (u : Circle) (c : Complex.UnitDisc) (G : ℂ → ℂ), ContinuousOn G (closedBall 0 1) ∧
      InjOn G (closedBall 0 1) ∧ (∀ z ∈ upperHalfPlaneSet, g z = G ((z - I) / (z + I))) ∧
      ∀ z ∈ upperHalfPlaneSet,
        (u : ℂ) * (((z - I) / (z + I) - c) / (1 - (starRingEnd ℂ) (c : ℂ) * ((z - I) / (z + I))))
          ∈ ball (0 : ℂ) 1 ∧
        f z = G ((u : ℂ) *
          (((z - I) / (z + I) - c) / (1 - (starRingEnd ℂ) (c : ℂ) * ((z - I) / (z + I))))) := by
  -- the inverse `K` of the Cayley transform `C`, from the disc onto the upper half-plane
  set C : ℂ → ℂ := fun z => (z - I) / (z + I) with hC
  have hCH : BijOn C upperHalfPlaneSet (ball 0 1) := bijOn_sub_I_div_add_I_upperHalfPlaneSet
  set K := invFunOn C upperHalfPlaneSet
  have hKmaps : MapsTo K (ball 0 1) upperHalfPlaneSet := hCH.surjOn.mapsTo_invFunOn
  have hCK : ∀ w ∈ ball (0 : ℂ) 1, C (K w) = w := hCH.surjOn.rightInvOn_invFunOn
  have hKC : ∀ z ∈ upperHalfPlaneSet, K (C z) = z := hCH.injOn.leftInvOn_invFunOn
  have hKi : InjOn K (ball 0 1) := fun w hw w' hw' h => by rw [← hCK w hw, ← hCK w' hw', h]
  have hKd : DifferentiableOn ℂ K (ball 0 1) := by
    have hCd : DifferentiableOn ℂ C upperHalfPlaneSet :=
      differentiableOn_sub_I_div_add_I.mono fun z (hz : 0 < z.im) =>
        add_I_ne_zero_of_im_nonneg hz.le
    have h := hCd.invFunOn isOpen_upperHalfPlaneSet hCH.injOn
    rwa [hCH.image_eq] at h
  have hKimg : K '' ball 0 1 = upperHalfPlaneSet := by
    rw [← hCH.image_eq]
    exact hCH.injOn.invFunOn_image subset_rfl
  -- both maps transported to the disc
  have htrans {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h upperHalfPlaneSet)
      (hb : BijOn h upperHalfPlaneSet U) :
      DifferentiableOn ℂ (h ∘ K) (ball 0 1) ∧ InjOn (h ∘ K) (ball 0 1) ∧
        (h ∘ K) '' ball 0 1 = U :=
    ⟨hd.comp hKd hKmaps, hb.injOn.comp hKi hKmaps, by rw [image_comp, hKimg, hb.image_eq]⟩
  obtain ⟨hFd, hFi, hFim⟩ := htrans hf hfU
  obtain ⟨hF'd, hF'i, hF'im⟩ := htrans hg hgU
  have hUo : IsOpen U := hFim ▸ isOpen_image_of_differentiableOn_of_injOn isOpen_ball hFd hFi
  -- Carathéodory's extension of `g ∘ K` to the closed disc
  obtain ⟨G, hGc, hGF⟩ := exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier one_pos
    hF'd hF'i (by rwa [hF'im]) (by rwa [hF'im])
  have hGi : InjOn G (closedBall 0 1) := injOn_closedBall_of_isJordanCurve_frontier one_pos hF'd
    hF'i (by rwa [hF'im]) (by rwa [hF'im]) hGc hGF
  -- the inverses of `f ∘ K` and `g ∘ K` differ by a disc automorphism
  have hinv {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1)) (hi : InjOn F (ball 0 1))
      (him : F '' ball 0 1 = U) :
      DifferentiableOn ℂ (invFunOn F (ball 0 1)) U ∧ InjOn (invFunOn F (ball 0 1)) U ∧
        invFunOn F (ball 0 1) '' U = ball 0 1 :=
    ⟨him ▸ hd.invFunOn isOpen_ball hi, him ▸ invFunOn_injOn_image F _,
      him ▸ hi.invFunOn_image subset_rfl⟩
  obtain ⟨hψd, hψi, hψim⟩ := hinv hFd hFi hFim
  obtain ⟨hψ'd, hψ'i, hψ'im⟩ := hinv hF'd hF'i hF'im
  obtain ⟨u, c, hM⟩ :=
    exists_eqOn_unitDiscStandardAutomorphismFormula_comp hUo hψd hψ'd hψi hψ'i hψim hψ'im
  refine ⟨u, c, G, hGc, hGi, fun z hz => ?_, fun z hz => ?_⟩
  · rw [hGF (hCH.mapsTo hz)]
    simp only [comp_apply, hKC z hz]
  · -- `y = f z` has preimage `C z` under `f ∘ K` and preimage `M (C z)` under `g ∘ K`
    have hy : (f ∘ K) (C z) ∈ U := hFim ▸ mem_image_of_mem _ (hCH.mapsTo hz)
    have hy' : ∃ w ∈ ball (0 : ℂ) 1, (g ∘ K) w = (f ∘ K) (C z) := by
      rw [← mem_image, hF'im]
      exact hy
    have hMz := hM hy
    simp only [hFi.leftInvOn_invFunOn (hCH.mapsTo hz)] at hMz
    rw [← hMz]
    refine ⟨invFunOn_mem hy', ?_⟩
    rw [hGF (invFunOn_mem hy'), invFunOn_eq hy']
    simp only [comp_apply, hKC z hz]

/-- In the disc picture of `exists_disc_factorization`, if `f` at `x` and `g` at `y` have the same
limit along the upper half-plane, then the disc automorphism carries the Cayley transform of `x` to
that of `y`. -/
private theorem sub_I_div_add_I_eq_of_factorization {u : Circle} {c : Complex.UnitDisc}
    {G f g : ℂ → ℂ} (hGc : ContinuousOn G (closedBall 0 1)) (hGi : InjOn G (closedBall 0 1))
    (hg' : ∀ z ∈ upperHalfPlaneSet, g z = G ((z - I) / (z + I)))
    (hf' : ∀ z ∈ upperHalfPlaneSet,
      (u : ℂ) * (((z - I) / (z + I) - c) / (1 - (starRingEnd ℂ) (c : ℂ) * ((z - I) / (z + I))))
        ∈ ball (0 : ℂ) 1 ∧
      f z = G ((u : ℂ) *
        (((z - I) / (z + I) - c) / (1 - (starRingEnd ℂ) (c : ℂ) * ((z - I) / (z + I))))))
    {x y : ℝ} {w : ℂ} (hx : Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w))
    (hy : Tendsto g (𝓝[upperHalfPlaneSet] (y : ℂ)) (𝓝 w)) :
    ((y : ℂ) - I) / ((y : ℂ) + I) =
      (u : ℂ) * ((((x : ℂ) - I) / ((x : ℂ) + I) - c) /
        (1 - (starRingEnd ℂ) (c : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)))) := by
  have hMc : ContinuousAt (fun z : ℂ => (u : ℂ) *
      (((z - I) / (z + I) - c) / (1 - (starRingEnd ℂ) (c : ℂ) * ((z - I) / (z + I))))) (x : ℂ) :=
    continuousAt_const.mul (((continuousAt_sub_I_div_add_I x).sub continuousAt_const).div
      (continuousAt_const.sub (continuousAt_const.mul (continuousAt_sub_I_div_add_I x)))
      (one_sub_conj_mul_sub_I_div_add_I_ne_zero c x))
  obtain ⟨hxm, hxw⟩ := mem_closedBall_and_eq_of_tendsto hGc hMc (fun z hz => (hf' z hz).1)
    (fun z hz => (hf' z hz).2) hx
  obtain ⟨hym, hyw⟩ := mem_closedBall_and_eq_of_tendsto hGc (continuousAt_sub_I_div_add_I y)
    (fun z hz => bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo hz) hg' hy
  exact hGi hym hxm (hyw.trans hxw.symm)

/-! ### The boundary correspondence -/

/-- **The boundary correspondence of two conformal maps is a Möbius transformation.** Let `f` and
`g` be holomorphic bijections of the upper half-plane onto a bounded domain `U` whose frontier is a
Jordan curve. There are `u` on the unit circle and `c` in the unit disc such that whenever `f` at
the real point `x` and `g` at the real point `y` have the same limit along the upper half-plane,
the Cayley transforms of `x` and `y` are related by the standard disc automorphism
`w ↦ u * (w - c) / (1 - conj c * w)`. -/
theorem exists_sub_I_div_add_I_eq_unitDiscStandardAutomorphismFormula_of_tendsto {U : Set ℂ}
    (hUb : IsBounded U) (hUJ : IsJordanCurve (frontier U)) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hfU : BijOn f upperHalfPlaneSet U) (hgU : BijOn g upperHalfPlaneSet U) :
    ∃ (u : Circle) (c : Complex.UnitDisc), ∀ (x y : ℝ) (w : ℂ),
      Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w) →
      Tendsto g (𝓝[upperHalfPlaneSet] (y : ℂ)) (𝓝 w) →
        ((y : ℂ) - I) / ((y : ℂ) + I) =
          (u : ℂ) * ((((x : ℂ) - I) / ((x : ℂ) + I) - c) /
            (1 - (starRingEnd ℂ) (c : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)))) := by
  obtain ⟨u, c, G, hGc, hGi, hg', hf'⟩ := exists_disc_factorization hUb hUJ hf hg hfU hgU
  exact ⟨u, c, fun x y w hx hy => sub_I_div_add_I_eq_of_factorization hGc hGi hg' hf' hx hy⟩

/-- **The boundary correspondence of two conformal maps preserves cross-ratios.** Let `f` and `g`
be holomorphic bijections of the upper half-plane onto a bounded domain `U` whose frontier is a
Jordan curve. If `f` at `x i` and `g` at `y i` have the same limit `w i` along the upper
half-plane for every index `i`, then the families `x` and `y` of real points have the same
cross-ratios. -/
theorem crossRatio_eq_of_tendsto_of_bijOn_upperHalfPlaneSet {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hfU : BijOn f upperHalfPlaneSet U) (hgU : BijOn g upperHalfPlaneSet U) {ι : Type*}
    {x y : ι → ℝ} {w : ι → ℂ}
    (hfx : ∀ i, Tendsto f (𝓝[upperHalfPlaneSet] (x i : ℂ)) (𝓝 (w i)))
    (hgy : ∀ i, Tendsto g (𝓝[upperHalfPlaneSet] (y i : ℂ)) (𝓝 (w i))) (i j k l : ι) :
    (y i - y k) * (y j - y l) / ((y i - y l) * (y j - y k)) =
      (x i - x k) * (x j - x l) / ((x i - x l) * (x j - x k)) := by
  obtain ⟨u, c, h⟩ :=
    exists_sub_I_div_add_I_eq_unitDiscStandardAutomorphismFormula_of_tendsto hUb hUJ hf hg hfU hgU
  have hm (m : ι) := h (x m) (y m) (w m) (hfx m) (hgy m)
  -- cross-ratios are preserved by the Cayley transform and by the disc automorphism
  have hre (x : ℝ) : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hC (p q r s : ℝ) := crossRatio_comp_eq_of_sub_eq_div
    (φ := fun z : ℂ => (z - I) / (z + I)) (d := fun z => z + I) (S := {z : ℂ | z + I ≠ 0})
    (mul_ne_zero two_ne_zero I_ne_zero) (fun _ ht => ht)
    (fun _ hs _ ht => sub_I_div_add_I_sub_sub_I_div_add_I hs ht) (hre p) (hre q) (hre r) (hre s)
  have hd (t : ℂ) (ht : t ∈ sphere (0 : ℂ) 1) : 1 - (starRingEnd ℂ) (c : ℂ) * t ≠ 0 :=
    (sub_ne_zero_and_one_sub_conj_mul_ne_zero_of_norm_lt_one_of_norm_eq_one c.norm_lt_one
      (mem_sphere_zero_iff_norm.mp ht)).2
  have hS (x : ℝ) : ((x : ℂ) - I) / ((x : ℂ) + I) ∈ sphere (0 : ℂ) 1 :=
    mem_sphere_zero_iff_norm.mpr (by simpa only [norm_div] using norm_sub_I_div_add_I_ofReal x)
  have hM := crossRatio_comp_eq_of_sub_eq_div
    (φ := fun w : ℂ => (u : ℂ) * ((w - c) / (1 - (starRingEnd ℂ) (c : ℂ) * w)))
    (d := fun w => 1 - (starRingEnd ℂ) (c : ℂ) * w) (S := sphere 0 1)
    (mul_ne_zero (Circle.coe_ne_zero u) (one_sub_conj_mul_ne_zero_unitDisc c c)) hd
    (fun s hs t ht => by
      rw [← mul_sub, unitDiscMoebiusFormula_sub_unitDiscMoebiusFormula _ (hd s hs) (hd t ht)]
      ring)
    (hS (x i)) (hS (x j)) (hS (x k)) (hS (x l))
  apply Complex.ofReal_injective
  push_cast
  rw [← hC, ← hC, hm i, hm j, hm k, hm l]
  exact hM

/-- **Three-point normalization of conformal maps onto a Jordan domain.** Two holomorphic
bijections `f` and `g` of the upper half-plane onto a bounded domain whose frontier is a Jordan
curve coincide on the upper half-plane as soon as, at each of three distinct real points, they have
the same limit along the upper half-plane. -/
theorem eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hfU : BijOn f upperHalfPlaneSet U) (hgU : BijOn g upperHalfPlaneSet U) {x₁ x₂ x₃ : ℝ}
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) {w₁ w₂ w₃ : ℂ}
    (hf₁ : Tendsto f (𝓝[upperHalfPlaneSet] (x₁ : ℂ)) (𝓝 w₁))
    (hf₂ : Tendsto f (𝓝[upperHalfPlaneSet] (x₂ : ℂ)) (𝓝 w₂))
    (hf₃ : Tendsto f (𝓝[upperHalfPlaneSet] (x₃ : ℂ)) (𝓝 w₃))
    (hg₁ : Tendsto g (𝓝[upperHalfPlaneSet] (x₁ : ℂ)) (𝓝 w₁))
    (hg₂ : Tendsto g (𝓝[upperHalfPlaneSet] (x₂ : ℂ)) (𝓝 w₂))
    (hg₃ : Tendsto g (𝓝[upperHalfPlaneSet] (x₃ : ℂ)) (𝓝 w₃)) :
    EqOn f g upperHalfPlaneSet := by
  obtain ⟨u, c, G, hGc, hGi, hg', hf'⟩ := exists_disc_factorization hUb hUJ hf hg hfU hgU
  -- the disc automorphism fixes the Cayley transforms of the three points, so it is the identity
  have hfix (x : ℝ) {w : ℂ} (hx : Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w))
      (hy : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w)) :=
    (sub_I_div_add_I_eq_of_factorization hGc hGi hg' hf' hx hy).symm
  have hne {x y : ℝ} (hxy : x ≠ y) :
      ((x : ℂ) - I) / ((x : ℂ) + I) ≠ ((y : ℂ) - I) / ((y : ℂ) + I) := fun h => hxy <| by
    have := injOn_sub_I_div_add_I (add_I_ne_zero_of_im_nonneg (by simp))
      (add_I_ne_zero_of_im_nonneg (by simp)) h
    exact_mod_cast this
  obtain ⟨hc, hu⟩ := eq_zero_and_eq_one_of_unitDiscStandardAutomorphismFormula_eq_self
    (hne h₁₂) (hne h₁₃) (hne h₂₃) (one_sub_conj_mul_sub_I_div_add_I_ne_zero c x₁)
    (one_sub_conj_mul_sub_I_div_add_I_ne_zero c x₂) (one_sub_conj_mul_sub_I_div_add_I_ne_zero c x₃)
    (hfix x₁ hf₁ hg₁) (hfix x₂ hf₂ hg₂) (hfix x₃ hf₃ hg₃)
  intro z hz
  rw [(hf' z hz).2, hg' z hz, hc, hu]
  simp

/-- **Distinct real points have distinct boundary limits.** If a holomorphic bijection of the upper
half-plane onto a bounded domain whose frontier is a Jordan curve has the same limit along the
upper half-plane at two real points, then these points are equal. -/
theorem eq_of_tendsto_of_bijOn_upperHalfPlaneSet {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgU : BijOn g upperHalfPlaneSet U) {x y : ℝ} {w : ℂ}
    (hx : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w))
    (hy : Tendsto g (𝓝[upperHalfPlaneSet] (y : ℂ)) (𝓝 w)) : x = y := by
  obtain ⟨-, -, G, hGc, hGi, hg', -⟩ := exists_disc_factorization hUb hUJ hg hg hgU hgU
  have hmaps := fun z (hz : z ∈ upperHalfPlaneSet) =>
    bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo hz
  obtain ⟨hxm, hxw⟩ :=
    mem_closedBall_and_eq_of_tendsto hGc (continuousAt_sub_I_div_add_I x) hmaps hg' hx
  obtain ⟨hym, hyw⟩ :=
    mem_closedBall_and_eq_of_tendsto hGc (continuousAt_sub_I_div_add_I y) hmaps hg' hy
  have hxy := injOn_sub_I_div_add_I (add_I_ne_zero_of_im_nonneg (by simp))
    (add_I_ne_zero_of_im_nonneg (by simp)) (hGi hxm hym (hxw.trans hyw.symm))
  exact_mod_cast hxy

end TauCeti

end
