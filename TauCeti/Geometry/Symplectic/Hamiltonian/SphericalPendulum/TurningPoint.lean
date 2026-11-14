/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum

/-!
# The turning points of the spherical pendulum

On the fibre `F⁻¹(h, j)` of the energy–momentum map `F = (H, J)` of the spherical pendulum the
height `z = q₃` and the vertical momentum satisfy `p₃² = 2 (h - z) (1 - z²) - j²`
(`TauCeti.sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace`). The heights occurring in the fibre
are therefore those `z ∈ [-1, 1]` with `z ≤ h` where this cubic radicand is nonnegative
(`TauCeti.image_apply_two_preimage_sphericalPendulumEnergyMomentum`), and the motion of the height
turns around at its lowest and highest values `z₋` and `z₊`, the **turning points**
(`TauCeti.sphericalPendulumLowerTurningPoint`, `TauCeti.sphericalPendulumUpperTurningPoint`),
defined as the infimum and the supremum of the heights of the fibre.

This file studies them at the values `(h, j)` with `j ≠ 0` lying strictly above the curve of
relative equilibria, that is, with `V_j(z) < h` for some height `z ∈ (-1, 1)`, where `V_j` is the
effective potential (`TauCeti.sphericalPendulumEffectivePotential`). There the turning points
satisfy `-1 < z₋ < z₊ < 1`, the heights of the fibre form the interval `[z₋, z₊]`, and the
radicand factors as

`2 (h - z) (1 - z²) - j² = 2 (z - z₋) (z₊ - z) (z₃ - z)`,  `z₃ = h - z₋ - z₊ > 1`.

So `z₋` and `z₊` are simple roots of the radicand, and its third root `z₃` lies above the north
pole. Simple roots move continuously with the coefficients: both turning points are continuous
functions of `(h, j)` on this set of values. These are the inputs for writing the quadratures of
the pendulum, such as its rotation angle, as integrals with continuous integrands in the angle
`θ` of the substitution `z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ`.

## Main declarations

* `TauCeti.sphericalPendulumLowerTurningPoint`, `TauCeti.sphericalPendulumUpperTurningPoint`: the
  lowest and the highest height on the fibre `F⁻¹(h, j)`.
* `TauCeti.image_apply_two_preimage_sphericalPendulumEnergyMomentum_eq_Icc`: the heights of the
  fibre form the interval `[z₋, z₊]`.
* `TauCeti.two_mul_sub_mul_one_sub_sq_sub_sq_eq`: the factorization of the radicand.
* `TauCeti.continuousOn_sphericalPendulumLowerTurningPoint`,
  `TauCeti.continuousOn_sphericalPendulumUpperTurningPoint`: continuity of the turning points.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

/-- The energy–momentum values with nonzero vertical angular momentum strictly above the curve of
relative equilibria: the domain where the two turning points are distinct and avoid the poles. -/
def sphericalPendulumTurningPointDomain : Set (ℝ × ℝ) :=
  {c | c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1, sphericalPendulumEffectivePotential c.2 z < c.1}

/-- Membership in the domain of distinct nonpolar turning points. -/
@[simp]
theorem mem_sphericalPendulumTurningPointDomain_iff {c : ℝ × ℝ} :
    c ∈ sphericalPendulumTurningPointDomain ↔
      c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1, sphericalPendulumEffectivePotential c.2 z < c.1 := (Iff.rfl)

/-- The **lower turning point** `z₋` of the spherical pendulum at energy `h` and vertical angular
momentum `j`: the infimum of the heights `q₃` of the points of the fibre `F⁻¹(h, j)` of the
energy–momentum map. -/
noncomputable def sphericalPendulumLowerTurningPoint (h j : ℝ) : ℝ :=
  sInf ((fun x ↦ x.1 2) ''
    (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}))

/-- The **upper turning point** `z₊` of the spherical pendulum at energy `h` and vertical angular
momentum `j`: the supremum of the heights `q₃` of the points of the fibre `F⁻¹(h, j)` of the
energy–momentum map. -/
noncomputable def sphericalPendulumUpperTurningPoint (h j : ℝ) : ℝ :=
  sSup ((fun x ↦ x.1 2) ''
    (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}))

/-- The heights `z ∈ [-1, 1]` with `z ≤ h` and `j² ≤ 2 (h - z) (1 - z²)`, which are the heights
of the fibre over `(h, j)`. -/
private def fibreHeights (h j : ℝ) : Set ℝ :=
  {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)}

/-- The lower turning point is the infimum of the heights `z ∈ [-1, 1]` with `z ≤ h` and
`j² ≤ 2 (h - z) (1 - z²)`. -/
theorem sphericalPendulumLowerTurningPoint_eq_sInf (h j : ℝ) :
    sphericalPendulumLowerTurningPoint h j =
      sInf {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} := by
  rw [sphericalPendulumLowerTurningPoint, image_apply_two_preimage_sphericalPendulumEnergyMomentum]

/-- The upper turning point is the supremum of the heights `z ∈ [-1, 1]` with `z ≤ h` and
`j² ≤ 2 (h - z) (1 - z²)`. -/
theorem sphericalPendulumUpperTurningPoint_eq_sSup (h j : ℝ) :
    sphericalPendulumUpperTurningPoint h j =
      sSup {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} := by
  rw [sphericalPendulumUpperTurningPoint, image_apply_two_preimage_sphericalPendulumEnergyMomentum]

/-! ### The heights of a fibre -/

private theorem isClosed_fibreHeights (h j : ℝ) : IsClosed (fibreHeights h j) := by
  simp only [fibreHeights, ofPred_and, ofPred_mem_eq]
  exact isClosed_Icc.inter ((isClosed_le continuous_id continuous_const).inter
    (isClosed_le continuous_const (by fun_prop)))

private theorem bddBelow_fibreHeights (h j : ℝ) : BddBelow (fibreHeights h j) :=
  ⟨-1, fun _ hz ↦ hz.1.1⟩

private theorem bddAbove_fibreHeights (h j : ℝ) : BddAbove (fibreHeights h j) :=
  ⟨1, fun _ hz ↦ hz.1.2⟩

/-- A height `z ∈ (-1, 1)` where the radicand is positive belongs to the fibre. -/
private theorem mem_fibreHeights_of_lt {h j z : ℝ} (hz : z ∈ Ioo (-1) 1)
    (hlt : j ^ 2 < 2 * (h - z) * (1 - z ^ 2)) : z ∈ fibreHeights h j := by
  have h₁ : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  refine ⟨Ioo_subset_Icc_self hz, ?_, hlt.le⟩
  by_contra hzh
  nlinarith [mul_pos (sub_pos.2 (not_le.1 hzh)) h₁, sq_nonneg j]

/-- For `j ≠ 0` the fibre contains neither pole. -/
private theorem mem_Ioo_of_mem_fibreHeights {h j z : ℝ} (hj : j ≠ 0)
    (hz : z ∈ fibreHeights h j) : z ∈ Ioo (-1) 1 := by
  obtain ⟨⟨h₁, h₂⟩, -, hjz⟩ := hz
  have hj2 : 0 < j ^ 2 := by positivity
  refine ⟨lt_of_le_of_ne h₁ ?_, lt_of_le_of_ne h₂ ?_⟩ <;> rintro rfl <;> nlinarith

/-- Above the curve of relative equilibria the fibre contains a height of positive radicand. -/
private theorem exists_mem_fibreHeights {h j z₀ : ℝ} (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    z₀ ∈ fibreHeights h j ∧ j ^ 2 < 2 * (h - z₀) * (1 - z₀ ^ 2) := by
  have hlt := (sphericalPendulumEffectivePotential_lt_iff
    ((sq_lt_one_iff_abs_lt_one _).2 (abs_lt.2 hz₀))).1 hV
  exact ⟨mem_fibreHeights_of_lt hz₀ hlt, hlt⟩

/-- Strict positivity of the radicand away from the poles gives an interior fibre height. -/
private theorem mem_interior_fibreHeights_of_lt {h j z : ℝ} (hz : z ∈ Ioo (-1) 1)
    (hlt : j ^ 2 < 2 * (h - z) * (1 - z ^ 2)) : z ∈ interior (fibreHeights h j) := by
  have hcont : Continuous fun z : ℝ ↦ 2 * (h - z) * (1 - z ^ 2) := by fun_prop
  exact mem_interior_iff_mem_nhds.2
    ((((hcont.tendsto z).eventually_const_lt hlt).and (isOpen_Ioo.mem_nhds hz)).mono
      fun _ hx ↦ mem_fibreHeights_of_lt hx.2 hx.1)

/-- At the infimum of the heights of a nonempty fibre with `j ≠ 0` the radicand vanishes: a
height of positive radicand has lower heights of the fibre next to it. -/
private theorem radicand_sInf_eq_zero {h j : ℝ} (hj : j ≠ 0) (hne : (fibreHeights h j).Nonempty) :
    2 * (h - sInf (fibreHeights h j)) * (1 - sInf (fibreHeights h j) ^ 2) - j ^ 2 = 0 := by
  set a := sInf (fibreHeights h j)
  have ha : a ∈ fibreHeights h j :=
    (isClosed_fibreHeights h j).csInf_mem hne (bddBelow_fibreHeights h j)
  refine le_antisymm ?_ (sub_nonneg.2 ha.2.2)
  by_contra hpos
  have hmem := mem_interior_fibreHeights_of_lt (mem_Ioo_of_mem_fibreHeights hj ha)
    (by linarith : j ^ 2 < 2 * (h - a) * (1 - a ^ 2))
  have hsub : fibreHeights h j ⊆ Ici a := fun _ hz ↦ csInf_le (bddBelow_fibreHeights h j) hz
  have := interior_mono hsub hmem
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at this

/-- At the supremum of the heights of a nonempty fibre with `j ≠ 0` the radicand vanishes. -/
private theorem radicand_sSup_eq_zero {h j : ℝ} (hj : j ≠ 0) (hne : (fibreHeights h j).Nonempty) :
    2 * (h - sSup (fibreHeights h j)) * (1 - sSup (fibreHeights h j) ^ 2) - j ^ 2 = 0 := by
  set b := sSup (fibreHeights h j)
  have hb : b ∈ fibreHeights h j :=
    (isClosed_fibreHeights h j).csSup_mem hne (bddAbove_fibreHeights h j)
  refine le_antisymm ?_ (sub_nonneg.2 hb.2.2)
  by_contra hpos
  have hmem := mem_interior_fibreHeights_of_lt (mem_Ioo_of_mem_fibreHeights hj hb)
    (by linarith : j ^ 2 < 2 * (h - b) * (1 - b ^ 2))
  have hsub : fibreHeights h j ⊆ Iic b := fun _ hz ↦ le_csSup (bddAbove_fibreHeights h j) hz
  have := interior_mono hsub hmem
  simp only [interior_Iic, mem_Iio, lt_self_iff_false] at this

/-- **Vieta.** If the radicand `2 (h - z) (1 - z²) - j²`, a cubic in `z` with leading coefficient
`2` and sum of roots `h`, vanishes at two distinct heights `a` and `b`, then its third root is
`h - a - b`. -/
private theorem radicand_eq_of_ne {h j a b : ℝ} (hab : a ≠ b)
    (ha : 2 * (h - a) * (1 - a ^ 2) - j ^ 2 = 0) (hb : 2 * (h - b) * (1 - b ^ 2) - j ^ 2 = 0)
    (z : ℝ) :
    2 * (h - z) * (1 - z ^ 2) - j ^ 2 = 2 * (z - a) * (b - z) * (h - a - b - z) := by
  have hK : a ^ 2 + a * b + b ^ 2 - h * (a + b) - 1 = 0 := by
    have : (a - b) * (a ^ 2 + a * b + b ^ 2 - h * (a + b) - 1) = 0 := by
      linear_combination (ha - hb) / 2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab)
  linear_combination ha + 2 * (z - a) * hK

/-! ### The turning points above the curve of relative equilibria -/

section Regular

variable {h j z₀ : ℝ}

/-- The turning points lie in the fibre, the radicand vanishes there, and they are distinct. -/
private theorem turningPoint_spec (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumLowerTurningPoint h j ∈ fibreHeights h j ∧
      sphericalPendulumUpperTurningPoint h j ∈ fibreHeights h j ∧
      sphericalPendulumLowerTurningPoint h j < sphericalPendulumUpperTurningPoint h j ∧
      ∀ z, 2 * (h - z) * (1 - z ^ 2) - j ^ 2 =
        2 * (z - sphericalPendulumLowerTurningPoint h j) *
          (sphericalPendulumUpperTurningPoint h j - z) *
          (h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j -
            z) := by
  obtain ⟨hmem₀, hlt₀⟩ := exists_mem_fibreHeights hz₀ hV
  rw [sphericalPendulumLowerTurningPoint_eq_sInf, sphericalPendulumUpperTurningPoint_eq_sSup]
  have ha := (isClosed_fibreHeights h j).csInf_mem ⟨z₀, hmem₀⟩ (bddBelow_fibreHeights h j)
  have hb := (isClosed_fibreHeights h j).csSup_mem ⟨z₀, hmem₀⟩ (bddAbove_fibreHeights h j)
  have ha₀ := radicand_sInf_eq_zero hj ⟨z₀, hmem₀⟩
  have hb₀ := radicand_sSup_eq_zero hj ⟨z₀, hmem₀⟩
  have hlt : sInf (fibreHeights h j) < sSup (fibreHeights h j) := by
    refine (csInf_le (bddBelow_fibreHeights h j) hmem₀).lt_of_ne ?_ |>.trans_le
      (le_csSup (bddAbove_fibreHeights h j) hmem₀)
    rintro hEq
    rw [hEq] at ha₀
    linarith
  exact ⟨ha, hb, hlt, radicand_eq_of_ne hlt.ne ha₀ hb₀⟩

/-- Above the curve of relative equilibria, the lower turning point lies above the south pole. -/
theorem neg_one_lt_sphericalPendulumLowerTurningPoint (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    -1 < sphericalPendulumLowerTurningPoint h j :=
  (mem_Ioo_of_mem_fibreHeights hj (turningPoint_spec hj hz₀ hV).1).1

/-- Above the curve of relative equilibria, the upper turning point lies below the north pole. -/
theorem sphericalPendulumUpperTurningPoint_lt_one (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumUpperTurningPoint h j < 1 :=
  (mem_Ioo_of_mem_fibreHeights hj (turningPoint_spec hj hz₀ hV).2.1).2

/-- Above the curve of relative equilibria, the two turning points are distinct. -/
theorem sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumLowerTurningPoint h j < sphericalPendulumUpperTurningPoint h j :=
  (turningPoint_spec hj hz₀ hV).2.2.1

/-- **The factorization of the radicand.** Above the curve of relative equilibria, the radicand
`p₃² = 2 (h - z) (1 - z²) - j²` of the fibre over `(h, j)` has the turning points `z₋`, `z₊` as
roots, and its third root is `z₃ = h - z₋ - z₊`:
`2 (h - z) (1 - z²) - j² = 2 (z - z₋) (z₊ - z) (z₃ - z)`. -/
theorem two_mul_sub_mul_one_sub_sq_sub_sq_eq (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) (z : ℝ) :
    2 * (h - z) * (1 - z ^ 2) - j ^ 2 =
      2 * (z - sphericalPendulumLowerTurningPoint h j) *
        (sphericalPendulumUpperTurningPoint h j - z) *
        (h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j - z) :=
  (turningPoint_spec hj hz₀ hV).2.2.2 z

/-- Above the curve of relative equilibria, the third root `h - z₋ - z₊` of the radicand lies
above the north pole: at `z = 1` the radicand is `-j² < 0`. -/
theorem one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    1 < h - sphericalPendulumLowerTurningPoint h j - sphericalPendulumUpperTurningPoint h j := by
  have h₁ := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV 1
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hj2 : 0 < j ^ 2 := by positivity
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  by_contra hc
  have : 0 ≤ (1 - a) * (1 - b) * (1 - (h - a - b)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

/-- **The heights of a fibre.** Above the curve of relative equilibria, the heights `q₃` of the
points of the fibre `F⁻¹(h, j)` of the energy–momentum map form the interval `[z₋, z₊]` between
the turning points. -/
theorem image_apply_two_preimage_sphericalPendulumEnergyMomentum_eq_Icc (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    (fun x ↦ x.1 2) ''
        (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}) =
      Icc (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j) := by
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  have ha := neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  rw [image_apply_two_preimage_sphericalPendulumEnergyMomentum (h, j)]
  refine Subset.antisymm (fun z hz ↦ ⟨?_, ?_⟩) fun z hz ↦ ?_
  · rw [sphericalPendulumLowerTurningPoint_eq_sInf]
    exact csInf_le (bddBelow_fibreHeights h j) hz
  · rw [sphericalPendulumUpperTurningPoint_eq_sSup]
    exact le_csSup (bddAbove_fibreHeights h j) hz
  · set a := sphericalPendulumLowerTurningPoint h j
    set b := sphericalPendulumUpperTurningPoint h j
    have hzI : z ∈ Ioo (-1) 1 := ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
    have hnn : 0 ≤ 2 * (h - z) * (1 - z ^ 2) - j ^ 2 := by
      rw [hfac z]
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hz.1) (sub_nonneg.2 hz.2))
        (by linarith [hz.2, hzI.2] : (0 : ℝ) ≤ h - a - b - z)
      linarith
    have h₁ : 0 < 1 - z ^ 2 := by nlinarith [hzI.1, hzI.2]
    refine ⟨Ioo_subset_Icc_self hzI, ?_, by linarith⟩
    by_contra hzh
    nlinarith [mul_pos (sub_pos.2 (not_le.1 hzh)) h₁, sq_pos_of_ne_zero hj]

end Regular

/-! ### Continuity of the turning points -/

/-- If the radicand is positive at a height `y` for the value `(h₀, j₀)`, it stays positive there
for all nearby values. -/
private theorem eventually_radicand_pos {h₀ j₀ y : ℝ}
    (hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - j₀ ^ 2) :
    ∀ᶠ c : ℝ × ℝ in 𝓝 (h₀, j₀), 0 < 2 * (c.1 - y) * (1 - y ^ 2) - c.2 ^ 2 :=
  ((by fun_prop : Continuous fun c : ℝ × ℝ ↦ 2 * (c.1 - y) * (1 - y ^ 2) - c.2 ^ 2).tendsto
    (h₀, j₀)).eventually_const_lt hpos

/-- If the radicand is negative on a compact set of heights for the value `(h₀, j₀)`, it stays
negative there for all nearby values. -/
private theorem eventually_forall_radicand_neg {h₀ j₀ : ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hneg : ∀ z ∈ K, 2 * (h₀ - z) * (1 - z ^ 2) - j₀ ^ 2 < 0) :
    ∀ᶠ c : ℝ × ℝ in 𝓝 (h₀, j₀), ∀ z ∈ K, 2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2 < 0 :=
  hK.eventually_forall_of_forall_eventually fun z hz ↦
    ((by fun_prop : Continuous fun p : (ℝ × ℝ) × ℝ ↦
      2 * (p.1.1 - p.2) * (1 - p.2 ^ 2) - p.1.2 ^ 2).tendsto ((h₀, j₀), z)).eventually_lt_const
      (hneg z hz)

/-- **Continuity of the lower turning point** on the values `(h, j)` with `j ≠ 0` lying strictly
above the curve of relative equilibria. -/
theorem continuousOn_sphericalPendulumLowerTurningPoint :
    ContinuousOn (fun c : ℝ × ℝ ↦ sphericalPendulumLowerTurningPoint c.1 c.2)
      sphericalPendulumTurningPointDomain := by
  rintro ⟨h₀, j₀⟩ ⟨hj₀, z₀, hz₀, hV₀⟩
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj₀ hz₀ hV₀
  have ha₀ := neg_one_lt_sphericalPendulumLowerTurningPoint hj₀ hz₀ hV₀
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj₀ hz₀ hV₀
  have hb₀ := sphericalPendulumUpperTurningPoint_lt_one hj₀ hz₀ hV₀
  have hc₀ := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj₀ hz₀ hV₀
  set a := sphericalPendulumLowerTurningPoint h₀ j₀
  set b := sphericalPendulumUpperTurningPoint h₀ j₀
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · -- Below `l < z₋` the radicand stays negative, so the fibre has no heights there.
    have hK := eventually_forall_radicand_neg (h₀ := h₀) (j₀ := j₀)
      (isCompact_Icc (a := -1) (b := l))
      fun z hz ↦ by
        rw [hfac z]
        have : 0 < (a - z) * (b - z) * (h₀ - a - b - z) :=
          mul_pos (mul_pos (by linarith [hz.2]) (by linarith [hz.2])) (by linarith [hz.2])
        nlinarith
    filter_upwards [nhdsWithin_le_nhds hK, self_mem_nhdsWithin] with c hc ⟨hj, z, hz, hV⟩
    have hmem := (turningPoint_spec hj hz hV).1
    by_contra hle
    exact (hc _ ⟨hmem.1.1, not_lt.1 hle⟩).not_ge (sub_nonneg.2 hmem.2.2)
  · -- Just above `z₋` the radicand stays positive, so this height stays in the fibre.
    set y := (a + min u b) / 2
    have hy₁ : a < y := by simp only [y]; linarith [lt_min hu hab]
    have hy₂ : y < min u b := by simp only [y]; linarith [lt_min hu hab]
    have hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - j₀ ^ 2 := by
      rw [hfac y]
      have := min_le_right u b
      have : 0 < (y - a) * (b - y) * (h₀ - a - b - y) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      linarith
    filter_upwards [nhdsWithin_le_nhds (eventually_radicand_pos hpos)] with c hc
    rw [sphericalPendulumLowerTurningPoint_eq_sInf]
    have hyI : y ∈ Ioo (-1) 1 := ⟨by linarith, by linarith [min_le_right u b]⟩
    exact (csInf_le (bddBelow_fibreHeights c.1 c.2)
      (mem_fibreHeights_of_lt hyI (by linarith))).trans_lt (hy₂.trans_le (min_le_left u b))

/-- **Continuity of the upper turning point** on the values `(h, j)` with `j ≠ 0` lying strictly
above the curve of relative equilibria. -/
theorem continuousOn_sphericalPendulumUpperTurningPoint :
    ContinuousOn (fun c : ℝ × ℝ ↦ sphericalPendulumUpperTurningPoint c.1 c.2)
      sphericalPendulumTurningPointDomain := by
  rintro ⟨h₀, j₀⟩ ⟨hj₀, z₀, hz₀, hV₀⟩
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj₀ hz₀ hV₀
  have ha₀ := neg_one_lt_sphericalPendulumLowerTurningPoint hj₀ hz₀ hV₀
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj₀ hz₀ hV₀
  have hb₀ := sphericalPendulumUpperTurningPoint_lt_one hj₀ hz₀ hV₀
  have hc₀ := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj₀ hz₀ hV₀
  set a := sphericalPendulumLowerTurningPoint h₀ j₀
  set b := sphericalPendulumUpperTurningPoint h₀ j₀
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · -- Just below `z₊` the radicand stays positive, so this height stays in the fibre.
    set y := (max l a + b) / 2
    have hy₁ : max l a < y := by simp only [y]; linarith [max_lt hl hab]
    have hy₂ : y < b := by simp only [y]; linarith [max_lt hl hab]
    have hpos : 0 < 2 * (h₀ - y) * (1 - y ^ 2) - j₀ ^ 2 := by
      rw [hfac y]
      have := le_max_right l a
      have : 0 < (y - a) * (b - y) * (h₀ - a - b - y) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      linarith
    filter_upwards [nhdsWithin_le_nhds (eventually_radicand_pos hpos)] with c hc
    rw [sphericalPendulumUpperTurningPoint_eq_sSup]
    have hyI : y ∈ Ioo (-1) 1 := ⟨by linarith [le_max_right l a], by linarith⟩
    exact ((le_max_left l a).trans_lt hy₁).trans_le (le_csSup (bddAbove_fibreHeights c.1 c.2)
      (mem_fibreHeights_of_lt hyI (by linarith)))
  · -- Above `u > z₊` the radicand stays negative, so the fibre has no heights there.
    have hK := eventually_forall_radicand_neg (h₀ := h₀) (j₀ := j₀)
      (isCompact_Icc (a := u) (b := 1))
      fun z hz ↦ by
        rw [hfac z]
        have : 0 < (z - a) * (z - b) * (h₀ - a - b - z) :=
          mul_pos (mul_pos (by linarith [hz.1]) (by linarith [hz.1])) (by linarith [hz.2])
        nlinarith
    filter_upwards [nhdsWithin_le_nhds hK, self_mem_nhdsWithin] with c hc ⟨hj, z, hz, hV⟩
    have hmem := (turningPoint_spec hj hz hV).2.1
    by_contra hle
    exact (hc _ ⟨not_lt.1 hle, hmem.1.2⟩).not_ge (sub_nonneg.2 hmem.2.2)

end TauCeti
