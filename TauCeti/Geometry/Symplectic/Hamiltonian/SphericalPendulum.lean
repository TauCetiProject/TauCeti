/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The spherical pendulum: energy, angular momentum and their joint values

The spherical pendulum, with mass, length and gravitational acceleration normalized to one, is a
particle on the unit sphere `S² ⊆ ℝ³` subject to the potential `q₃`. Its phase space is the
cotangent bundle of the sphere, realized inside `ℝ³ × ℝ³` as
`T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` (`TauCeti.sphericalPendulumPhaseSpace`). The energy is
`H(q, p) = ‖p‖² / 2 + q₃` and the vertical component of the angular momentum is
`J(q, p) = q₁ p₂ - q₂ p₁`; together they form the energy–momentum map
`F = (H, J)` (`TauCeti.sphericalPendulumEnergyMomentum`). Lean indexes the coordinates of
`EuclideanSpace ℝ (Fin 3)` by `0, 1, 2`, so `q₃` is `q 2`.

The basic identity is that on `T*S²` the square of the vertical momentum is determined by the
height and the values of `F`:
`p₃² = 2 (H - q₃) (1 - q₃²) - J²`.
Away from the poles this says `H = V_J(q₃) + p₃² / (2 (1 - q₃²))`, where
`V_j(z) = j² / (2 (1 - z²)) + z` is the effective potential of the reduced one-degree-of-freedom
system (`TauCeti.sphericalPendulumEffectivePotential`). Consequently the heights occurring in a
fibre `F⁻¹(h, j)` are exactly the `z ∈ [-1, 1]` with `z ≤ h` and `j² ≤ 2 (h - z) (1 - z²)`, and
the image of `F` is the set of `(h, j)` for which such a height exists.

For `j ≠ 0` the effective potential has a unique minimum on `(-1, 1)`, at the unique root
`z_j ∈ (-1, 0)` of `j² z + (1 - z²)² = 0`, with minimum value `(3 z_j² - 1) / (2 z_j)`. The
image of `F` is therefore bounded below by the curve of relative equilibria: for `j ≠ 0`, `(h, j)`
is a value of `F` exactly when `h ≥ V_j(z_j)`, and the fibre over `(V_j(z_j), j)` consists of the
horizontal circular motions at height `z_j`. For `j = 0` the values are `h ≥ -1`, the bottom value
`(-1, 0)` being attained only at the equilibrium at rest at the south pole.

The energy is a proper function on the phase space
(`TauCeti.isProperMap_sphericalPendulumHamiltonian_comp_subtypeVal`), so every energy level is
compact, and so is every fibre of `F`.

Finally, every fibre of `F` is connected
(`TauCeti.isPreconnected_sphericalPendulumPhaseSpace_inter_preimage_singleton`). Up to rotation
about the vertical axis, a point of the fibre over `(h, j)` is determined by its height `z` and
its vertical momentum `p₃ = ±√(2 (h - z) (1 - z²) - j²)`, so the fibre is swept out by two sheets,
one for each sign of `p₃`. For `j ≠ 0` the heights are those with `V_j(z) ≤ h`, an interval
because `V_j` is convex (`TauCeti.convexOn_sphericalPendulumEffectivePotential`), and for `j = 0`
they are the `z ∈ [-1, 1]` with `z ≤ h`. The two sheets meet where `p₃` vanishes. This holds for
every value, regular or not, including the value `(1, 0)` of the unstable equilibrium at the north
pole.

## Main results

* `TauCeti.sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace`: `p₃² = 2 (H - q₃) (1 - q₃²) - J²`.
* `TauCeti.fst_sphericalPendulumEnergyMomentum_eq`: `H = V_J(q₃) + p₃² / (2 (1 - q₃²))` away
  from the poles.
* `TauCeti.image_apply_two_preimage_sphericalPendulumEnergyMomentum`: the heights occurring in a
  fibre of `F`.
* `TauCeti.image_sphericalPendulumEnergyMomentum`: the image of the energy–momentum map.
* `TauCeti.fst_sphericalPendulumEnergyMomentum_eq_neg_one_iff`: the energy `-1` is attained only
  at the south pole at rest.
* `TauCeti.isMinOn_sphericalPendulumEffectivePotential_iff` and
  `TauCeti.existsUnique_isMinOn_sphericalPendulumEffectivePotential`: the minimum of `V_j`.
* `TauCeti.mk_mem_image_sphericalPendulumEnergyMomentum_iff_of_isMinOn`: for `j ≠ 0`, the values
  of `F` with second coordinate `j` are the `h ≥ min V_j`.
* `TauCeti.sphericalPendulumEnergyMomentum_eq_iff_of_isMinOn`: the fibre over the boundary
  point `(min V_j, j)` is the relative equilibrium at height `z_j`.
* `TauCeti.isProperMap_sphericalPendulumHamiltonian_comp_subtypeVal`: the energy is proper.
* `TauCeti.convexOn_sphericalPendulumEffectivePotential`: the effective potential is convex.
* `TauCeti.isCompact_sphericalPendulumPhaseSpace_inter_preimage_singleton`: the fibres of `F` are
  compact.
* `TauCeti.isPreconnected_sphericalPendulumPhaseSpace_inter_preimage_singleton` and
  `TauCeti.isConnected_sphericalPendulumPhaseSpace_inter_preimage_singleton`: the fibres of `F`
  are connected.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 15.
-/

public section

namespace TauCeti

open Set
open scoped InnerProductSpace

/-- The phase space `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` of the spherical pendulum: positions
on the unit sphere and momenta tangent to it, as a subset of `ℝ³ × ℝ³`. -/
def sphericalPendulumPhaseSpace : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {x | ‖x.1‖ = 1 ∧ ⟪x.1, x.2⟫_ℝ = 0}

@[simp]
theorem mem_sphericalPendulumPhaseSpace {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} :
    x ∈ sphericalPendulumPhaseSpace ↔ ‖x.1‖ = 1 ∧ ⟪x.1, x.2⟫_ℝ = 0 :=
  Iff.rfl

theorem isClosed_sphericalPendulumPhaseSpace : IsClosed sphericalPendulumPhaseSpace :=
  (isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq (continuous_fst.inner continuous_snd) continuous_const)

/-- The energy `H(q, p) = ‖p‖² / 2 + q₃` of the spherical pendulum, with mass, length and
gravitational acceleration normalized to one. -/
noncomputable def sphericalPendulumHamiltonian
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖x.2‖ ^ 2 / 2 + x.1 2

@[simp]
theorem sphericalPendulumHamiltonian_apply (q p : EuclideanSpace ℝ (Fin 3)) :
    sphericalPendulumHamiltonian (q, p) = ‖p‖ ^ 2 / 2 + q 2 :=
  (rfl)

@[fun_prop]
theorem continuous_sphericalPendulumHamiltonian : Continuous sphericalPendulumHamiltonian := by
  unfold sphericalPendulumHamiltonian
  fun_prop

/-- The energy–momentum map `F = (H, J)` of the spherical pendulum: the energy
`H(q, p) = ‖p‖² / 2 + q₃` together with the vertical angular momentum `J(q, p) = q₁ p₂ - q₂ p₁`,
the angular momentum `TauCeti.angularMomentum` in the horizontal coordinate plane. -/
noncomputable def sphericalPendulumEnergyMomentum
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ℝ × ℝ :=
  (sphericalPendulumHamiltonian x,
    angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) x)

@[simp]
theorem sphericalPendulumEnergyMomentum_apply (q p : EuclideanSpace ℝ (Fin 3)) :
    sphericalPendulumEnergyMomentum (q, p) = (‖p‖ ^ 2 / 2 + q 2, q 0 * p 1 - q 1 * p 0) := by
  simp [sphericalPendulumEnergyMomentum, EuclideanSpace.inner_single_right]

@[simp]
theorem fst_sphericalPendulumEnergyMomentum
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (sphericalPendulumEnergyMomentum x).1 = sphericalPendulumHamiltonian x :=
  (rfl)

@[simp]
theorem snd_sphericalPendulumEnergyMomentum
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (sphericalPendulumEnergyMomentum x).2 =
      angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) x :=
  (rfl)

@[fun_prop]
theorem continuous_sphericalPendulumEnergyMomentum :
    Continuous sphericalPendulumEnergyMomentum :=
  continuous_sphericalPendulumHamiltonian.prodMk <|
    continuous_iff_continuousAt.2 fun x ↦ (hasFDerivAt_angularMomentum _ _ x).continuousAt

/-- The effective potential `V_j(z) = j² / (2 (1 - z²)) + z` of the spherical pendulum at vertical
angular momentum `j`, as a function of the height `z ∈ (-1, 1)`. On the phase space the energy is
`V_J(q₃)` plus the nonnegative kinetic energy `p₃² / (2 (1 - q₃²))` of the vertical motion. -/
noncomputable def sphericalPendulumEffectivePotential (j z : ℝ) : ℝ :=
  j ^ 2 / (2 * (1 - z ^ 2)) + z

theorem sphericalPendulumEffectivePotential_def (j z : ℝ) :
    sphericalPendulumEffectivePotential j z = j ^ 2 / (2 * (1 - z ^ 2)) + z :=
  (rfl)

/-! ### The phase space in coordinates -/

/-- At a pole `z² = 1`, the condition `j² ≤ 2 (h - z) (1 - z²)` forces `j = 0`. -/
private theorem eq_zero_of_sq_le_of_sq_eq_one {j z h : ℝ} (hz : z ^ 2 = 1)
    (hj : j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)) : j = 0 := by
  rw [hz, sub_self, mul_zero] at hj
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hj (sq_nonneg j))

private theorem coords_of_mem {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 ∧
      x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2 = 0 := by
  obtain ⟨hq, hqp⟩ := hx
  have hq2 := EuclideanSpace.real_norm_sq_eq x.1
  rw [hq, one_pow, Fin.sum_univ_three] at hq2
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hqp
  exact ⟨hq2.symm, by linear_combination hqp⟩

/-- **The reduced energy identity.** On the phase space of the spherical pendulum the square of
the vertical momentum is determined by the height and the values `(h, j)` of the energy–momentum
map:
`p₃² = 2 (h - q₃) (1 - q₃²) - j²`. -/
theorem sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    x.2 2 ^ 2 = 2 * ((sphericalPendulumEnergyMomentum x).1 - x.1 2) * (1 - x.1 2 ^ 2) -
      (sphericalPendulumEnergyMomentum x).2 ^ 2 := by
  obtain ⟨hq, hqp⟩ := coords_of_mem hx
  obtain ⟨q, p⟩ := x
  simp only [sphericalPendulumEnergyMomentum_apply, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three] at hq hqp ⊢
  -- Lagrange's identity in the horizontal plane, together with the two constraints.
  linear_combination (p 0 ^ 2 + p 1 ^ 2) * hq - (q 0 * p 0 + q 1 * p 1 - q 2 * p 2) * hqp

/-- On the phase space the height `q₃` lies in `[-1, 1]`. -/
theorem apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    x.1 2 ∈ Icc (-1) 1 := by
  obtain ⟨hq, -⟩ := coords_of_mem hx
  exact ⟨by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)],
    by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]⟩

/-- The height `q₃` does not exceed the energy. -/
theorem apply_two_le_sphericalPendulumHamiltonian
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    x.1 2 ≤ sphericalPendulumHamiltonian x := by
  have : 0 ≤ ‖x.2‖ ^ 2 / 2 := by positivity
  rw [sphericalPendulumHamiltonian]
  linarith

/-- At the poles `q₃ = ±1` of the phase space the vertical angular momentum vanishes. -/
theorem snd_sphericalPendulumEnergyMomentum_eq_zero_of_sq_eq_one
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hz : x.1 2 ^ 2 = 1) :
    (sphericalPendulumEnergyMomentum x).2 = 0 := by
  have h := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
  rw [hz, sub_self, mul_zero, zero_sub] at h
  nlinarith [sq_nonneg (x.2 2), sq_nonneg (sphericalPendulumEnergyMomentum x).2]

/-- At the poles `q₃ = ±1` of the phase space the vertical momentum vanishes. -/
theorem snd_two_eq_zero_of_mem_sphericalPendulumPhaseSpace_of_sq_eq_one
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hz : x.1 2 ^ 2 = 1) :
    x.2 2 = 0 := by
  have h := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
  rw [hz, sub_self, mul_zero, zero_sub] at h
  nlinarith [sq_nonneg (x.2 2), sq_nonneg (sphericalPendulumEnergyMomentum x).2]

/-- Away from the poles the energy of the spherical pendulum is the effective potential at the
height `q₃` plus the kinetic energy of the vertical motion:
`H = V_J(q₃) + p₃² / (2 (1 - q₃²))`. -/
theorem fst_sphericalPendulumEnergyMomentum_eq
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hz : x.1 2 ^ 2 < 1) :
    (sphericalPendulumEnergyMomentum x).1 =
      sphericalPendulumEffectivePotential (sphericalPendulumEnergyMomentum x).2 (x.1 2) +
        x.2 2 ^ 2 / (2 * (1 - x.1 2 ^ 2)) := by
  have h := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
  have hz' : 1 - x.1 2 ^ 2 ≠ 0 := (sub_pos.2 hz).ne'
  rw [sphericalPendulumEffectivePotential_def, h]
  field_simp
  ring

/-- Away from the poles the energy is at least the effective potential at the height `q₃`. -/
theorem sphericalPendulumEffectivePotential_le
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hz : x.1 2 ^ 2 < 1) :
    sphericalPendulumEffectivePotential (sphericalPendulumEnergyMomentum x).2 (x.1 2) ≤
      (sphericalPendulumEnergyMomentum x).1 := by
  rw [fst_sphericalPendulumEnergyMomentum_eq hx hz]
  have : 0 < 1 - x.1 2 ^ 2 := sub_pos.2 hz
  have : 0 ≤ x.2 2 ^ 2 / (2 * (1 - x.1 2 ^ 2)) := by positivity
  linarith

/-! ### Fibres and the image of the energy–momentum map -/

/-- **The heights in a fibre of the energy–momentum map.** The heights `q₃` of the points of the
spherical pendulum with energy `h` and vertical angular momentum `j` are exactly the
`z ∈ [-1, 1]` with `z ≤ h` and `j² ≤ 2 (h - z) (1 - z²)`. -/
theorem image_apply_two_preimage_sphericalPendulumEnergyMomentum (c : ℝ × ℝ) :
    (fun x ↦ x.1 2) '' (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {c}) =
      {z | z ∈ Icc (-1) 1 ∧ z ≤ c.1 ∧ c.2 ^ 2 ≤ 2 * (c.1 - z) * (1 - z ^ 2)} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩, rfl⟩
    refine ⟨apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace hx,
      apply_two_le_sphericalPendulumHamiltonian x, ?_⟩
    have := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
    nlinarith [sq_nonneg (x.2 2)]
  rintro ⟨⟨hz₁, hz₂⟩, hzh, hj⟩
  obtain ⟨h, j⟩ := c
  dsimp only at hzh hj ⊢
  rcases (sq_le_one_iff_abs_le_one z |>.2 (abs_le.2 ⟨hz₁, hz₂⟩)).lt_or_eq with hz | hz
  · -- Away from the poles: the position `(s, 0, z)` with `s = √(1 - z²)`, and the momentum
    -- `(-w z / s, j / s, w)` with vertical part `w = √(2 (h - z) (1 - z²) - j²)`.
    set s := √(1 - z ^ 2)
    set w := √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    have hs : 0 < s := Real.sqrt_pos.2 (sub_pos.2 hz)
    have hs2 : s ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (sub_pos.2 hz).le
    have hw2 : w ^ 2 = 2 * (h - z) * (1 - z ^ 2) - j ^ 2 := Real.sq_sqrt (by linarith)
    refine ⟨(!₂[s, 0, z], !₂[-(w * z / s), j / s, w]), ⟨⟨?_, ?_⟩, ?_⟩, by simp⟩
    · rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, EuclideanSpace.real_norm_sq_eq,
        Fin.sum_univ_three]
      simp [hs2]
    · simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      field_simp
      ring
    · simp only [mem_preimage, sphericalPendulumEnergyMomentum_apply,
        EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, mem_singleton_iff, Prod.mk.injEq,
        Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      constructor
      · field_simp
        rw [hw2, hs2]
        ring
      · field_simp
        ring
  · -- At a pole: the position `(0, 0, z)` and the horizontal momentum `(√(2 (h - z)), 0, 0)`.
    have hj0 : j = 0 := eq_zero_of_sq_le_of_sq_eq_one hz hj
    have hu : √(2 * (h - z)) ^ 2 = 2 * (h - z) := Real.sq_sqrt (by linarith)
    refine ⟨(!₂[0, 0, z], !₂[√(2 * (h - z)), 0, 0]), ⟨⟨?_, ?_⟩, ?_⟩, by simp⟩
    · rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, EuclideanSpace.real_norm_sq_eq,
        Fin.sum_univ_three]
      simp [hz]
    · simp [PiLp.inner_apply, Fin.sum_univ_three]
    · simp only [mem_preimage, sphericalPendulumEnergyMomentum_apply,
        EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, mem_singleton_iff, Prod.mk.injEq,
        Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hu, hj0]
      constructor <;> ring

/-- **The image of the energy–momentum map** of the spherical pendulum: `(h, j)` is a value of
`F = (H, J)` on the phase space exactly when some height `z ∈ [-1, 1]` has `z ≤ h` and
`j² ≤ 2 (h - z) (1 - z²)`. -/
theorem image_sphericalPendulumEnergyMomentum :
    sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace =
      {c | ∃ z ∈ Icc (-1) 1, z ≤ c.1 ∧ c.2 ^ 2 ≤ 2 * (c.1 - z) * (1 - z ^ 2)} := by
  ext c
  have h := congrArg Set.Nonempty (image_apply_two_preimage_sphericalPendulumEnergyMomentum c)
  simp only [image_nonempty, eq_iff_iff] at h
  rw [mem_ofPred_eq]
  -- Both sides only repackage the existentials of `h`.
  refine (?_ : _ ↔ _).trans (h.trans ?_)
  · exact ⟨fun ⟨x, hx, hxc⟩ ↦ ⟨x, hx, hxc⟩, fun ⟨x, hx, hxc⟩ ↦ ⟨x, hx, hxc⟩⟩
  · exact ⟨fun ⟨z, hz, hzh, hj⟩ ↦ ⟨z, hz, hzh, hj⟩, fun ⟨z, hz, hzh, hj⟩ ↦ ⟨z, hz, hzh, hj⟩⟩

/-- With vertical angular momentum zero, the values of the energy are the `h ≥ -1`. The bottom
value is described by `TauCeti.fst_sphericalPendulumEnergyMomentum_eq_neg_one_iff`. -/
theorem mk_zero_mem_image_sphericalPendulumEnergyMomentum_iff (h : ℝ) :
    (h, 0) ∈ sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace ↔ -1 ≤ h := by
  rw [image_sphericalPendulumEnergyMomentum]
  refine ⟨fun ⟨z, hz, hzh, _⟩ ↦ hz.1.trans hzh, fun hh ↦ ⟨-1, by norm_num, hh, by norm_num⟩⟩

/-- **The bottom of the energy.** The energy of the spherical pendulum is `-1` exactly at the
equilibrium at rest at the south pole, `q = (0, 0, -1)` and `p = 0`. -/
theorem fst_sphericalPendulumEnergyMomentum_eq_neg_one_iff
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    (sphericalPendulumEnergyMomentum x).1 = -1 ↔ x = (!₂[0, 0, -1], 0) := by
  obtain ⟨hq, -⟩ := coords_of_mem hx
  obtain ⟨q, p⟩ := x
  simp only [sphericalPendulumEnergyMomentum_apply] at hq ⊢
  constructor
  · intro hH
    -- Both `‖p‖² / 2` and `q₃ + 1` are nonnegative and they add up to zero.
    have hp : ‖p‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq2 : q 2 = -1 := by nlinarith [sq_nonneg ‖p‖]
    have hq01 : q 0 ^ 2 + q 1 ^ 2 = 0 := by rw [hq2] at hq; linarith
    have hq0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    refine Prod.ext ?_ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hp))
    ext i
    fin_cases i <;> simp [hq0, hq1, hq2]
  · rintro ⟨rfl, rfl⟩
    norm_num

/-! ### The effective potential and the relative equilibria -/

/-- Away from the poles, the condition `j² ≤ 2 (h - z) (1 - z²)` describing the heights in the
fibre over `(h, j)` says that the effective potential at `z` is at most `h`. -/
theorem sphericalPendulumEffectivePotential_le_iff {j z h : ℝ} (hz : z ^ 2 < 1) :
    sphericalPendulumEffectivePotential j z ≤ h ↔ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2) := by
  have hz' : 0 < 2 * (1 - z ^ 2) := by linarith
  rw [sphericalPendulumEffectivePotential_def, ← le_sub_iff_add_le, div_le_iff₀ hz']
  constructor <;> intro h <;> linarith

/-- **The effective potential is convex** on `(-1, 1)`: it is `z` plus the nonnegative multiple
`j² / 4` of `2 / (1 - z²) = (1 - z)⁻¹ + (1 + z)⁻¹`. -/
theorem convexOn_sphericalPendulumEffectivePotential (j : ℝ) :
    ConvexOn ℝ (Ioo (-1) 1) (sphericalPendulumEffectivePotential j) := by
  have hinv : ConvexOn ℝ (Ioi 0) fun x : ℝ ↦ x⁻¹ := by
    simpa only [zpow_neg, zpow_one] using convexOn_zpow (𝕜 := ℝ) (-1)
  have h₁ : ConvexOn ℝ (Ioo (-1) 1) fun z : ℝ ↦ (1 + z)⁻¹ :=
    (hinv.translate_right 1).subset (fun z hz ↦ by
      simp only [mem_preimage, mem_Ioi]
      linarith [hz.1]) (convex_Ioo _ _)
  have h₂ : ConvexOn ℝ (Ioo (-1) 1) fun z : ℝ ↦ (1 - z)⁻¹ :=
    ((hinv.translate_right 1).comp_linearMap (-LinearMap.id)).subset (fun z hz ↦ by
      simp only [mem_preimage, mem_Ioi, LinearMap.neg_apply, LinearMap.id_apply]
      linarith [hz.2]) (convex_Ioo _ _) |>.congr fun z _ ↦ by simp [sub_eq_add_neg]
  refine (((h₁.add h₂).smul (c := j ^ 2 / 4) (by positivity)).add
    (convexOn_id (convex_Ioo (-1 : ℝ) 1))).congr fun z hz ↦ ?_
  have h1 : 1 + z ≠ 0 := by linarith [hz.1]
  have h2 : 1 - z ≠ 0 := by linarith [hz.2]
  have h3 : 1 - z ^ 2 ≠ 0 := by
    rw [show 1 - z ^ 2 = (1 + z) * (1 - z) by ring]
    exact mul_ne_zero h1 h2
  simp only [Pi.add_apply, smul_eq_mul, id, sphericalPendulumEffectivePotential_def]
  field_simp
  ring

/-- The heights `z ∈ (-1, 1)` with `j² ≤ 2 (h - z) (1 - z²)`, at which the effective potential
is at most `h`, form an interval. -/
private theorem convex_heights (j h : ℝ) :
    Convex ℝ {z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} := by
  convert (convexOn_sphericalPendulumEffectivePotential j).convex_le h using 1
  ext z
  simp only [mem_ofPred_eq, and_congr_right_iff]
  exact fun hz ↦ (sphericalPendulumEffectivePotential_le_iff
    (((sq_lt_one_iff_abs_lt_one _).trans abs_lt).2 hz)).symm

/-- If `z₀ ∈ (-1, 0)` solves `j² z₀ + (1 - z₀²)² = 0`, then
`V_j(z) - V_j(z₀) = (z - z₀)² (1 + z₀² + 2 z₀ z) / (-2 z₀ (1 - z²))`, which is positive for
`z ≠ z₀` in `(-1, 1)`. -/
private theorem sphericalPendulumEffectivePotential_sub_eq {j z₀ z : ℝ} (hz₀ : z₀ ≠ 0)
    (hz : 1 - z ^ 2 ≠ 0) (hcrit : j ^ 2 * z₀ + (1 - z₀ ^ 2) ^ 2 = 0) :
    sphericalPendulumEffectivePotential j z - sphericalPendulumEffectivePotential j z₀ =
      (z - z₀) ^ 2 * (1 + z₀ ^ 2 + 2 * z₀ * z) / (-2 * z₀ * (1 - z ^ 2)) := by
  have hj : j ^ 2 = -(1 - z₀ ^ 2) ^ 2 / z₀ := by
    field_simp
    linarith
  rw [sphericalPendulumEffectivePotential_def, sphericalPendulumEffectivePotential_def, hj]
  field_simp
  ring

/-- A root `z₀ ∈ (-1, 0)` of `j² z + (1 - z²)²` is the strict minimum of the effective potential
`V_j` on `(-1, 1)`. -/
theorem sphericalPendulumEffectivePotential_lt_of_eq_zero {j z₀ z : ℝ} (hz₀ : z₀ ∈ Ioo (-1) 0)
    (hcrit : j ^ 2 * z₀ + (1 - z₀ ^ 2) ^ 2 = 0) (hz : z ∈ Ioo (-1) 1) (hne : z ≠ z₀) :
    sphericalPendulumEffectivePotential j z₀ < sphericalPendulumEffectivePotential j z := by
  have h1z : 0 < 1 - z ^ 2 := sub_pos.2 (((sq_lt_one_iff_abs_lt_one _).trans abs_lt).2 hz)
  obtain ⟨hz₀₁, hz₀₂⟩ := hz₀
  rw [← sub_pos, sphericalPendulumEffectivePotential_sub_eq hz₀₂.ne h1z.ne' hcrit]
  have hnum : 0 < 1 + z₀ ^ 2 + 2 * z₀ * z := by
    -- `1 + z₀² + 2 z₀ z = (1 + z₀ z)² + z₀² (1 - z²)`.
    nlinarith [sq_nonneg (1 + z₀ * z), mul_pos (pow_pos (neg_pos.2 hz₀₂) 2) h1z]
  have hsq : 0 < (z - z₀) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
  exact div_pos (mul_pos hsq hnum) (by nlinarith)

/-- A root `z ∈ (-1, 1)` of `j² z + (1 - z²)²` is negative, since `j² z = -(1 - z²)² < 0`. -/
private theorem neg_of_sq_mul_add_sq_eq_zero {j z : ℝ} (hz : z ∈ Ioo (-1) 1)
    (hcrit : j ^ 2 * z + (1 - z ^ 2) ^ 2 = 0) : z < 0 := by
  have : 0 < (1 - z ^ 2) ^ 2 :=
    pow_pos (sub_pos.2 (((sq_lt_one_iff_abs_lt_one _).trans abs_lt).2 hz)) 2
  nlinarith [sq_nonneg j]

/-- For `j ≠ 0` the polynomial `j² z + (1 - z²)²` has a root in `(-1, 0)`: it is `-j² < 0` at
`z = -1` and `1 > 0` at `z = 0`. -/
theorem exists_mem_Ioo_sq_mul_add_sq_eq_zero {j : ℝ} (hj : j ≠ 0) :
    ∃ z ∈ Ioo (-1 : ℝ) 0, j ^ 2 * z + (1 - z ^ 2) ^ 2 = 0 := by
  have hcont : ContinuousOn (fun z : ℝ ↦ j ^ 2 * z + (1 - z ^ 2) ^ 2) (Icc (-1) 0) := by
    fun_prop
  have hmem : (0 : ℝ) ∈ Ioo (j ^ 2 * (-1) + (1 - (-1) ^ 2) ^ 2) (j ^ 2 * 0 + (1 - 0 ^ 2) ^ 2) := by
    norm_num
    positivity
  exact intermediate_value_Ioo (by norm_num) hcont hmem

/-- **The minimum of the effective potential.** For `j ≠ 0`, a height `z ∈ (-1, 1)` minimizes the
effective potential `V_j` on `(-1, 1)` exactly when `j² z + (1 - z²)² = 0`. -/
theorem isMinOn_sphericalPendulumEffectivePotential_iff {j z : ℝ} (hj : j ≠ 0)
    (hz : z ∈ Ioo (-1) 1) :
    IsMinOn (sphericalPendulumEffectivePotential j) (Ioo (-1) 1) z ↔
      j ^ 2 * z + (1 - z ^ 2) ^ 2 = 0 := by
  obtain ⟨z₁, hz₁, hcrit₁⟩ := exists_mem_Ioo_sq_mul_add_sq_eq_zero hj
  have hz₁' : z₁ ∈ Ioo (-1 : ℝ) 1 := ⟨hz₁.1, hz₁.2.trans one_pos⟩
  constructor
  · intro hmin
    by_contra hne
    have hne' : z ≠ z₁ := by rintro rfl; exact hne hcrit₁
    exact (sphericalPendulumEffectivePotential_lt_of_eq_zero hz₁ hcrit₁ hz hne').not_ge
      (hmin hz₁')
  · intro hcrit
    have hneg : z < 0 := neg_of_sq_mul_add_sq_eq_zero hz hcrit
    intro y hy
    rcases eq_or_ne y z with rfl | hyz
    · exact le_rfl
    · exact (sphericalPendulumEffectivePotential_lt_of_eq_zero ⟨hz.1, hneg⟩ hcrit hy hyz).le

/-- For `j ≠ 0` the effective potential `V_j` has exactly one minimum on `(-1, 1)`. -/
theorem existsUnique_isMinOn_sphericalPendulumEffectivePotential {j : ℝ} (hj : j ≠ 0) :
    ∃! z, z ∈ Ioo (-1) 1 ∧ IsMinOn (sphericalPendulumEffectivePotential j) (Ioo (-1) 1) z := by
  obtain ⟨z₁, hz₁, hcrit₁⟩ := exists_mem_Ioo_sq_mul_add_sq_eq_zero hj
  have hz₁' : z₁ ∈ Ioo (-1 : ℝ) 1 := ⟨hz₁.1, hz₁.2.trans one_pos⟩
  refine ⟨z₁, ⟨hz₁', (isMinOn_sphericalPendulumEffectivePotential_iff hj hz₁').2 hcrit₁⟩, ?_⟩
  rintro z ⟨hz, hmin⟩
  by_contra hne
  exact (sphericalPendulumEffectivePotential_lt_of_eq_zero hz₁ hcrit₁ hz hne).not_ge
    (hmin hz₁')

/-- For `j ≠ 0` the minimum of the effective potential lies in the southern hemisphere. -/
theorem neg_of_isMinOn_sphericalPendulumEffectivePotential {j z : ℝ} (hj : j ≠ 0)
    (hz : z ∈ Ioo (-1) 1)
    (hmin : IsMinOn (sphericalPendulumEffectivePotential j) (Ioo (-1) 1) z) : z < 0 :=
  neg_of_sq_mul_add_sq_eq_zero hz ((isMinOn_sphericalPendulumEffectivePotential_iff hj hz).1 hmin)

/-- At a root `z ≠ 0` of `j² z + (1 - z²)²`, the effective potential takes the value
`(3 z² - 1) / (2 z)`. Together with `j² = -(1 - z²)² / z` this parametrizes the curve of minimum
values by the height `z ∈ (-1, 0)`. -/
theorem sphericalPendulumEffectivePotential_eq_of_eq_zero {j z : ℝ} (hz : z ≠ 0)
    (hcrit : j ^ 2 * z + (1 - z ^ 2) ^ 2 = 0) :
    sphericalPendulumEffectivePotential j z = (3 * z ^ 2 - 1) / (2 * z) := by
  have hj : j ^ 2 = -(1 - z ^ 2) ^ 2 / z := by
    field_simp
    linarith
  rw [sphericalPendulumEffectivePotential_def, hj]
  field_simp
  ring

/-- **The boundary of the energy–momentum image.** For `j ≠ 0`, let `z₀` be the minimum of the
effective potential `V_j` on `(-1, 1)`. Then `(h, j)` is a value of the energy–momentum map of
the spherical pendulum exactly when `h ≥ V_j(z₀)`. -/
theorem mk_mem_image_sphericalPendulumEnergyMomentum_iff_of_isMinOn {j z₀ : ℝ} (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hmin : IsMinOn (sphericalPendulumEffectivePotential j) (Ioo (-1) 1) z₀) (h : ℝ) :
    (h, j) ∈ sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace ↔
      sphericalPendulumEffectivePotential j z₀ ≤ h := by
  rw [image_sphericalPendulumEnergyMomentum, mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz₁, hz₂⟩, -, hjz⟩
    -- The endpoints `z = ±1` would force `j = 0`.
    have hz : z ^ 2 < 1 := lt_of_le_of_ne (by nlinarith) fun hz ↦
      hj (eq_zero_of_sq_le_of_sq_eq_one hz hjz)
    have hzI : z ∈ Ioo (-1) 1 := ((sq_lt_one_iff_abs_lt_one _).trans abs_lt).1 hz
    exact (hmin hzI).trans ((sphericalPendulumEffectivePotential_le_iff hz).2 hjz)
  · intro hh
    have hz : z₀ ^ 2 < 1 := ((sq_lt_one_iff_abs_lt_one _).trans abs_lt).2 hz₀
    have hjz := (sphericalPendulumEffectivePotential_le_iff hz).1 hh
    refine ⟨z₀, ⟨hz₀.1.le, hz₀.2.le⟩, ?_, hjz⟩
    nlinarith [sq_nonneg j]

/-- **The relative equilibria.** For `j ≠ 0`, let `z₀` be the minimum of the effective potential
`V_j` on `(-1, 1)`. A point of the phase space lies in the fibre of the energy–momentum map over
the boundary value `(V_j(z₀), j)` exactly when it has vertical angular momentum `j`, height `z₀`
and vanishing vertical momentum: these are the horizontal circular motions at height `z₀`. -/
theorem sphericalPendulumEnergyMomentum_eq_iff_of_isMinOn {j z₀ : ℝ} (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hmin : IsMinOn (sphericalPendulumEffectivePotential j) (Ioo (-1) 1) z₀)
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    sphericalPendulumEnergyMomentum x = (sphericalPendulumEffectivePotential j z₀, j) ↔
      (sphericalPendulumEnergyMomentum x).2 = j ∧ x.1 2 = z₀ ∧ x.2 2 = 0 := by
  -- Points with `J = j ≠ 0` are away from the poles.
  have hpole : (sphericalPendulumEnergyMomentum x).2 = j → x.1 2 ^ 2 < 1 := fun hJ ↦
    lt_of_le_of_ne (by nlinarith [(apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace hx).1,
      (apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace hx).2])
      fun h1 ↦ hj (hJ ▸ snd_sphericalPendulumEnergyMomentum_eq_zero_of_sq_eq_one hx h1)
  constructor
  · intro hF
    have hJ : (sphericalPendulumEnergyMomentum x).2 = j := congrArg Prod.snd hF
    have hH : (sphericalPendulumEnergyMomentum x).1 = sphericalPendulumEffectivePotential j z₀ :=
      congrArg Prod.fst hF
    have hz := hpole hJ
    have hzI : x.1 2 ∈ Ioo (-1) 1 := ((sq_lt_one_iff_abs_lt_one _).trans abs_lt).1 hz
    have hE := fst_sphericalPendulumEnergyMomentum_eq hx hz
    rw [hJ, hH] at hE
    have hd : 0 < 2 * (1 - x.1 2 ^ 2) := by linarith
    have hkin : 0 ≤ x.2 2 ^ 2 / (2 * (1 - x.1 2 ^ 2)) := by positivity
    have hle := hmin hzI
    -- The kinetic term vanishes and the height is a minimum of `V_j`.
    have hkin0 : x.2 2 ^ 2 / (2 * (1 - x.1 2 ^ 2)) = 0 := by
      simp only [mem_ofPred_eq] at hle
      linarith
    have hp : x.2 2 = 0 := by
      rw [div_eq_zero_iff, or_iff_left hd.ne'] at hkin0
      exact pow_eq_zero_iff two_ne_zero |>.1 hkin0
    refine ⟨hJ, ?_, hp⟩
    by_contra hne
    have hlt := sphericalPendulumEffectivePotential_lt_of_eq_zero
      ⟨hz₀.1, neg_of_isMinOn_sphericalPendulumEffectivePotential hj hz₀ hmin⟩
      ((isMinOn_sphericalPendulumEffectivePotential_iff hj hz₀).1 hmin) hzI hne
    linarith
  · rintro ⟨hJ, hz, hp⟩
    have hE := fst_sphericalPendulumEnergyMomentum_eq hx (hpole hJ)
    rw [hJ, hz, hp] at hE
    rw [zero_pow two_ne_zero, zero_div, add_zero] at hE
    exact Prod.ext hE hJ

/-! ### Properness of the energy -/

/-- The energy of the spherical pendulum has compact sublevel sets on the phase space. -/
theorem isCompact_sphericalPendulumPhaseSpace_inter_preimage_Iic (b : ℝ) :
    IsCompact (sphericalPendulumPhaseSpace ∩ sphericalPendulumHamiltonian ⁻¹' Iic b) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_sphericalPendulumPhaseSpace.inter (isClosed_Iic.preimage (by fun_prop))) ?_
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3) ×
    EuclideanSpace ℝ (Fin 3))) (r := max 1 √(2 * (b + 1)))).subset ?_
  rintro ⟨q, p⟩ ⟨hx, hb⟩
  have hz := (apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace hx).1
  rw [mem_preimage, mem_Iic, sphericalPendulumHamiltonian_apply] at hb
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  refine max_le_max (le_of_eq hx.1) (Real.le_sqrt_of_sq_le ?_)
  dsimp only at hz
  linarith

/-- **The energy of the spherical pendulum is proper** as a function on the phase space. -/
theorem isProperMap_sphericalPendulumHamiltonian_comp_subtypeVal :
    IsProperMap fun x : sphericalPendulumPhaseSpace ↦ sphericalPendulumHamiltonian x := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨by fun_prop, fun K hK ↦ ?_⟩
  obtain ⟨b, hb⟩ := hK.isBounded.bddAbove
  have hc : IsCompact (sphericalPendulumPhaseSpace ∩ sphericalPendulumHamiltonian ⁻¹' K) :=
    (isCompact_sphericalPendulumPhaseSpace_inter_preimage_Iic b).of_isClosed_subset
      (isClosed_sphericalPendulumPhaseSpace.inter (hK.isClosed.preimage (by fun_prop)))
      (inter_subset_inter_right _ fun x hx ↦ hb hx)
  convert isClosed_sphericalPendulumPhaseSpace.isClosedEmbedding_subtypeVal.isCompact_preimage hc
    using 1
  ext x
  simp

/-! ### Compactness and connectedness of the fibres -/

/-- The point of `ℝ³ × ℝ³` whose position has cylindrical coordinates `(r, φ, z)` and whose
momentum has radial, angular and vertical components `a`, `b` and `w`. -/
private noncomputable def cylindricalPoint (φ r z a b w : ℝ) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (!₂[r * Real.cos φ, r * Real.sin φ, z],
    !₂[a * Real.cos φ - b * Real.sin φ, a * Real.sin φ + b * Real.cos φ, w])

/-- In cylindrical coordinates the phase space is `r² + z² = 1`, `r a + z w = 0`. -/
private theorem mem_sphericalPendulumPhaseSpace_cylindricalPoint_iff {φ r z a b w : ℝ} :
    cylindricalPoint φ r z a b w ∈ sphericalPendulumPhaseSpace ↔
      r ^ 2 + z ^ 2 = 1 ∧ r * a + z * w = 0 := by
  rw [mem_sphericalPendulumPhaseSpace, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [cylindricalPoint, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hsc := Real.sin_sq_add_cos_sq φ
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1 - r ^ 2 * hsc, by linear_combination h2 - r * a * hsc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1 + r ^ 2 * hsc, by linear_combination h2 + r * a * hsc⟩

/-- In cylindrical coordinates the energy is `(a² + b² + w²) / 2 + z` and the vertical angular
momentum is `r b`. -/
private theorem sphericalPendulumEnergyMomentum_cylindricalPoint (φ r z a b w : ℝ) :
    sphericalPendulumEnergyMomentum (cylindricalPoint φ r z a b w) =
      ((a ^ 2 + b ^ 2 + w ^ 2) / 2 + z, r * b) := by
  simp only [cylindricalPoint, sphericalPendulumEnergyMomentum_apply,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq]
  have hsc := Real.sin_sq_add_cos_sq φ
  constructor
  · linear_combination (a ^ 2 + b ^ 2) / 2 * hsc
  · linear_combination r * b * hsc

/-- Every point of `ℝ³ × ℝ³` has cylindrical coordinates with `r ≥ 0`. On the vertical axis
`r = 0` the angle `φ` is free, and it can be chosen to make the momentum purely radial with
nonnegative radial component. -/
private theorem exists_eq_cylindricalPoint
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ∃ φ r z a b w, 0 ≤ r ∧ x = cylindricalPoint φ r z a b w ∧ (r = 0 → b = 0 ∧ 0 ≤ a) := by
  obtain ⟨q, p⟩ := x
  have hsc (φ : ℝ) := Real.sin_sq_add_cos_sq φ
  by_cases hq : q 0 = 0 ∧ q 1 = 0
  · -- On the axis, take `φ` to be the argument of the horizontal momentum.
    set c : ℂ := ⟨p 0, p 1⟩
    refine ⟨Complex.arg c, 0, q 2, ‖c‖, 0, p 2, le_rfl, ?_, fun _ ↦ ⟨rfl, norm_nonneg _⟩⟩
    have h0 := Complex.norm_mul_cos_arg c
    have h1 := Complex.norm_mul_sin_arg c
    simp only [cylindricalPoint, Prod.mk.injEq]
    constructor <;> ext i <;> fin_cases i <;> simp [c, hq.1, hq.2] at h0 h1 ⊢
  · -- Off the axis, take `φ` to be the argument of the horizontal position.
    set c : ℂ := ⟨q 0, q 1⟩
    have h0 := Complex.norm_mul_cos_arg c
    have h1 := Complex.norm_mul_sin_arg c
    set φ := Complex.arg c
    refine ⟨φ, ‖c‖, q 2, p 0 * Real.cos φ + p 1 * Real.sin φ,
      p 1 * Real.cos φ - p 0 * Real.sin φ, p 2, norm_nonneg _, ?_, fun hc ↦ ?_⟩
    · simp only [cylindricalPoint, Prod.mk.injEq]
      constructor <;> ext i <;> fin_cases i <;> simp [c] at h0 h1 ⊢
      · linarith
      · linarith
      · linear_combination (-p 0) * hsc φ
      · linear_combination (-p 1) * hsc φ
    · rw [norm_eq_zero] at hc
      exact absurd ⟨congrArg Complex.re hc, congrArg Complex.im hc⟩ hq

/-- The sheet `s = ±1` of the fibre over `(h, 0)`: the point at height `z ∈ [-1, h]` and angle `φ`
moving in the vertical plane through the axis, with vertical momentum of sign `s`. At the poles
`z = ±1` its momentum is horizontal and points along the angle `φ`, up to the sign `-s z`. -/
private noncomputable def zeroFibreSheet (h s : ℝ) (v : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  cylindricalPoint v.2 √(1 - v.1 ^ 2) v.1 (-(v.1 * (s * √(2 * (h - v.1))))) 0
    (s * √(2 * (h - v.1)) * √(1 - v.1 ^ 2))

/-- The sheet `s = ±1` of the fibre over `(h, j)` away from the poles: the point at height `z`
and angle `φ` with vertical momentum `s √(2 (h - z) (1 - z²) - j²)` and angular momentum `j`. -/
private noncomputable def fibreSheet (h j s : ℝ) (v : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  cylindricalPoint v.2 √(1 - v.1 ^ 2) v.1
    (-(s * √(2 * (h - v.1) * (1 - v.1 ^ 2) - j ^ 2) * v.1 / √(1 - v.1 ^ 2)))
    (j / √(1 - v.1 ^ 2)) (s * √(2 * (h - v.1) * (1 - v.1 ^ 2) - j ^ 2))

private theorem continuous_zeroFibreSheet (h s : ℝ) : Continuous (zeroFibreSheet h s) := by
  unfold zeroFibreSheet cylindricalPoint
  refine .prodMk (PiLp.continuous_toLp _ _ |>.comp ?_) (PiLp.continuous_toLp _ _ |>.comp ?_) <;>
    refine continuous_pi fun i ↦ ?_ <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop

private theorem continuousOn_fibreSheet (h j s : ℝ) :
    ContinuousOn (fibreSheet h j s)
      ({z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} ×ˢ univ) := by
  have hne : ∀ v ∈ {z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} ×ˢ (univ : Set ℝ),
      √(1 - v.1 ^ 2) ≠ 0 := fun v hv ↦
    (Real.sqrt_pos.2 (by nlinarith [hv.1.1.1, hv.1.1.2])).ne'
  have hr : Continuous fun v : ℝ × ℝ ↦ √(1 - v.1 ^ 2) := by fun_prop
  have ha : ContinuousOn (fun v : ℝ × ℝ ↦
      -(s * √(2 * (h - v.1) * (1 - v.1 ^ 2) - j ^ 2) * v.1 / √(1 - v.1 ^ 2))) _ :=
    (ContinuousOn.div (by fun_prop) hr.continuousOn hne).neg
  have hb : ContinuousOn (fun v : ℝ × ℝ ↦ j / √(1 - v.1 ^ 2)) _ :=
    ContinuousOn.div continuousOn_const hr.continuousOn hne
  unfold fibreSheet cylindricalPoint
  refine .prodMk ((PiLp.continuous_toLp _ _).comp_continuousOn ?_)
    ((PiLp.continuous_toLp _ _).comp_continuousOn ?_) <;>
    refine continuousOn_pi.2 fun i ↦ ?_ <;> fin_cases i
  all_goals simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  · exact Continuous.continuousOn (by fun_prop)
  · exact Continuous.continuousOn (by fun_prop)
  · exact Continuous.continuousOn (by fun_prop)
  · exact (ha.mul (by fun_prop)).sub (hb.mul (by fun_prop))
  · exact (ha.mul (by fun_prop)).add (hb.mul (by fun_prop))
  · exact Continuous.continuousOn (by fun_prop)

/-- The sheets of the fibre over `(h, 0)` lie in that fibre. -/
private theorem zeroFibreSheet_mem {h s z : ℝ} (hs : s = 1 ∨ s = -1) (hz : z ∈ Icc (-1 : ℝ) 1)
    (hzh : z ≤ h) (φ : ℝ) :
    zeroFibreSheet h s (z, φ) ∈
      sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, 0)} := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hr : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by nlinarith [hz.1, hz.2])
  have hu : √(2 * (h - z)) ^ 2 = 2 * (h - z) := Real.sq_sqrt (by linarith)
  rw [mem_inter_iff, mem_preimage, mem_singleton_iff, zeroFibreSheet,
    mem_sphericalPendulumPhaseSpace_cylindricalPoint_iff,
    sphericalPendulumEnergyMomentum_cylindricalPoint]
  refine ⟨⟨by linear_combination hr, by ring⟩, Prod.ext ?_ (by simp)⟩
  linear_combination (s ^ 2 * √(2 * (h - z)) ^ 2 / 2) * hr + (s ^ 2 / 2) * hu + (h - z) * hs2

/-- Every point of the fibre over `(h, 0)` lies on one of its two sheets. -/
private theorem exists_zeroFibreSheet_eq {h : ℝ}
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, 0)}) :
    ∃ s, (s = 1 ∨ s = -1) ∧ ∃ z ∈ Icc (-1 : ℝ) 1, z ≤ h ∧ ∃ φ, zeroFibreSheet h s (z, φ) = x := by
  obtain ⟨hx, hF⟩ := hx
  rw [mem_preimage, mem_singleton_iff] at hF
  have hw := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
  rw [hF] at hw
  obtain ⟨φ, r, z, a, b, w, hr, rfl, hpole⟩ := exists_eq_cylindricalPoint x
  change w ^ 2 = 2 * (h - z) * (1 - z ^ 2) - 0 ^ 2 at hw
  obtain ⟨hx1, hx2⟩ := mem_sphericalPendulumPhaseSpace_cylindricalPoint_iff.1 hx
  rw [sphericalPendulumEnergyMomentum_cylindricalPoint, Prod.mk.injEq] at hF
  obtain ⟨hF1, hF2⟩ := hF
  have hz : z ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hrz : √(1 - z ^ 2) = r := by
    rw [← Real.sqrt_sq hr]
    congr 1
    linarith
  rcases hr.eq_or_lt with rfl | hr0
  · -- At a pole `z = ±1` the momentum is horizontal, of length `√(2 (h - z))`; use `s = -z`.
    obtain ⟨rfl, ha⟩ := hpole rfl
    have hz2 : z ^ 2 = 1 := by linarith
    obtain rfl : w = 0 := (mul_eq_zero.1 (show z * w = 0 by linarith)).resolve_left
      fun h0 ↦ by simp [h0] at hz2
    have ha2 : a ^ 2 = 2 * (h - z) := by linarith
    have hsa : √(2 * (h - z)) = a := by rw [← ha2, Real.sqrt_sq ha]
    refine ⟨-z, ?_, z, hz, by nlinarith, φ, ?_⟩
    · rcases sq_eq_sq_iff_eq_or_eq_neg.1 (show z ^ 2 = 1 ^ 2 by rw [hz2, one_pow]) with h0 | h0 <;>
        simp [h0]
    · simp only [zeroFibreSheet, hrz, hsa, mul_zero]
      congr 1
      linear_combination a * hz2
  · -- Away from the poles `b = 0`, and `w / r` is a square root of `2 (h - z)`.
    obtain rfl : b = 0 := (mul_eq_zero.1 hF2).resolve_left hr0.ne'
    have hw2 : w ^ 2 = 2 * (h - z) * r ^ 2 := by
      linear_combination hw - 2 * (h - z) * hx1
    have hu2 : (w / r) ^ 2 = 2 * (h - z) := by
      rw [div_pow, hw2]
      field_simp
    have hzh : z ≤ h := by nlinarith [sq_nonneg (w / r)]
    have hsq : √(2 * (h - z)) ^ 2 = 2 * (h - z) := Real.sq_sqrt (by linarith)
    have hgoal (s : ℝ) (hs : s * √(2 * (h - z)) = w / r) :
        zeroFibreSheet h s (z, φ) = cylindricalPoint φ r z a 0 w := by
      simp only [zeroFibreSheet, hrz, hs]
      congr 1
      · field_simp
        linarith
      · field_simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hu2.trans hsq.symm) with h1 | h1
    · exact ⟨1, .inl rfl, z, hz, hzh, φ, hgoal 1 (by rw [h1, one_mul])⟩
    · exact ⟨-1, .inr rfl, z, hz, hzh, φ, hgoal (-1) (by rw [h1, neg_one_mul])⟩

/-- The sheets of the fibre over `(h, j)` lie in that fibre. -/
private theorem fibreSheet_mem {h j s z : ℝ} (hs : s = 1 ∨ s = -1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hzj : j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)) (φ : ℝ) :
    fibreSheet h j s (z, φ) ∈
      sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)} := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hz2 : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hr : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hz2.le
  have hr0 : √(1 - z ^ 2) ≠ 0 := (Real.sqrt_pos.2 hz2).ne'
  have hW : √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) ^ 2 = 2 * (h - z) * (1 - z ^ 2) - j ^ 2 :=
    Real.sq_sqrt (by linarith)
  rw [mem_inter_iff, mem_preimage, mem_singleton_iff, fibreSheet,
    mem_sphericalPendulumPhaseSpace_cylindricalPoint_iff,
    sphericalPendulumEnergyMomentum_cylindricalPoint]
  refine ⟨⟨by linear_combination hr, by field_simp; ring⟩, Prod.ext ?_ (by field_simp)⟩
  field_simp
  rw [hW, hr, hs2]
  ring

/-- For `j ≠ 0`, every point of the fibre over `(h, j)` lies on one of its two sheets. -/
private theorem exists_fibreSheet_eq {h j : ℝ} (hj : j ≠ 0)
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)}) :
    ∃ s, (s = 1 ∨ s = -1) ∧ ∃ z ∈ Ioo (-1 : ℝ) 1, j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2) ∧
      ∃ φ, fibreSheet h j s (z, φ) = x := by
  obtain ⟨hx, hF⟩ := hx
  rw [mem_preimage, mem_singleton_iff] at hF
  have hw2 := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hx
  rw [hF] at hw2
  obtain ⟨φ, r, z, a, b, w, hr, rfl, -⟩ := exists_eq_cylindricalPoint x
  change w ^ 2 = 2 * (h - z) * (1 - z ^ 2) - j ^ 2 at hw2
  obtain ⟨hx1, hx2⟩ := mem_sphericalPendulumPhaseSpace_cylindricalPoint_iff.1 hx
  rw [sphericalPendulumEnergyMomentum_cylindricalPoint, Prod.mk.injEq] at hF
  obtain ⟨hF1, hF2⟩ := hF
  -- Since `r b = j ≠ 0`, the point is off the axis.
  have hr0 : 0 < r := hr.lt_of_ne fun h0 ↦ hj (by rw [← hF2, ← h0, zero_mul])
  have hz : z ∈ Ioo (-1 : ℝ) 1 := ((sq_lt_one_iff_abs_lt_one _).trans abs_lt).1 (by nlinarith)
  have hrz : √(1 - z ^ 2) = r := by
    rw [← Real.sqrt_sq hr]
    congr 1
    linarith
  have hzj : j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2) := by nlinarith [sq_nonneg w]
  have hW : √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) ^ 2 = 2 * (h - z) * (1 - z ^ 2) - j ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hgoal (s : ℝ) (hs : s * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) = w) :
      fibreSheet h j s (z, φ) = cylindricalPoint φ r z a b w := by
    simp only [fibreSheet, hrz, hs]
    congr 1
    · field_simp
      linarith
    · field_simp
      linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hw2.trans hW.symm) with h1 | h1
  · exact ⟨1, .inl rfl, z, hz, hzj, φ, hgoal 1 (by rw [h1, one_mul])⟩
  · exact ⟨-1, .inr rfl, z, hz, hzj, φ, hgoal (-1) (by rw [h1, neg_one_mul])⟩

/-- The fibre over `(h, 0)` is the union of its two sheets, parametrized by the heights in
`[-1, 1]` below `h` and all angles. -/
private theorem fibre_zero_eq_union (h : ℝ) :
    sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, 0)} =
      zeroFibreSheet h 1 '' ({z ∈ Icc (-1 : ℝ) 1 | z ≤ h} ×ˢ univ) ∪
        zeroFibreSheet h (-1) '' ({z ∈ Icc (-1 : ℝ) 1 | z ≤ h} ×ˢ univ) := by
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨s, hs, z, hz, hzh, φ, rfl⟩ := exists_zeroFibreSheet_eq hx
    rcases hs with rfl | rfl
    · exact .inl ⟨(z, φ), ⟨⟨hz, hzh⟩, trivial⟩, rfl⟩
    · exact .inr ⟨(z, φ), ⟨⟨hz, hzh⟩, trivial⟩, rfl⟩
  · rintro x (⟨⟨z, φ⟩, ⟨⟨hz, hzh⟩, -⟩, rfl⟩ | ⟨⟨z, φ⟩, ⟨⟨hz, hzh⟩, -⟩, rfl⟩)
    · exact zeroFibreSheet_mem (.inl rfl) hz hzh φ
    · exact zeroFibreSheet_mem (.inr rfl) hz hzh φ

/-- For `j ≠ 0` the fibre over `(h, j)` is the union of its two sheets, parametrized by the
heights `z ∈ (-1, 1)` with `j² ≤ 2 (h - z) (1 - z²)` and all angles. -/
private theorem fibre_eq_union_of_ne_zero {h j : ℝ} (hj : j ≠ 0) :
    sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {(h, j)} =
      fibreSheet h j 1 '' ({z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} ×ˢ univ) ∪
        fibreSheet h j (-1) ''
          ({z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} ×ˢ univ) := by
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨s, hs, z, hz, hzj, φ, rfl⟩ := exists_fibreSheet_eq hj hx
    rcases hs with rfl | rfl
    · exact .inl ⟨(z, φ), ⟨⟨hz, hzj⟩, trivial⟩, rfl⟩
    · exact .inr ⟨(z, φ), ⟨⟨hz, hzj⟩, trivial⟩, rfl⟩
  · rintro x (⟨⟨z, φ⟩, ⟨⟨hz, hzj⟩, -⟩, rfl⟩ | ⟨⟨z, φ⟩, ⟨⟨hz, hzj⟩, -⟩, rfl⟩)
    · exact fibreSheet_mem (.inl rfl) hz hzj φ
    · exact fibreSheet_mem (.inr rfl) hz hzj φ

/-- **The fibres of the energy–momentum map are connected.** For every `c = (h, j)`, the set of
points of the spherical pendulum with energy `h` and vertical angular momentum `j` is
preconnected; it is empty exactly when `c` is not a value of the energy–momentum map.

Rotating about the vertical axis, each fibre is swept out by two sheets, one for each sign of the
vertical momentum `p₃`, over an interval of heights: for `j ≠ 0` the heights where the effective
potential is at most `h`, which form an interval by its convexity, and for `j = 0` the heights in
`[-1, 1]` below `h`. The sheets meet where `p₃ = 0`: for `j ≠ 0` at the top height of the fibre,
and for `j = 0` at the south pole. -/
theorem isPreconnected_sphericalPendulumPhaseSpace_inter_preimage_singleton (c : ℝ × ℝ) :
    IsPreconnected (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {c}) := by
  obtain ⟨h, j⟩ := c
  rcases eq_or_ne j 0 with rfl | hj
  · rw [fibre_zero_eq_union]
    have hS : IsPreconnected ({z ∈ Icc (-1 : ℝ) 1 | z ≤ h} ×ˢ (univ : Set ℝ)) :=
      ((convex_Icc (-1) 1).inter (convex_Iic h)).isPreconnected.prod isPreconnected_univ
    rcases eq_empty_or_nonempty {z ∈ Icc (-1 : ℝ) 1 | z ≤ h} with hSe | ⟨z₀, hz₀⟩
    · rw [hSe, empty_prod, image_empty, image_empty, union_self]
      exact isPreconnected_empty
    -- The two sheets meet at the south pole, with opposite angles.
    have hm : (-1 : ℝ) ∈ {z ∈ Icc (-1 : ℝ) 1 | z ≤ h} :=
      ⟨⟨le_rfl, by norm_num⟩, hz₀.1.1.trans hz₀.2⟩
    refine IsPreconnected.union' ⟨zeroFibreSheet h 1 (-1, 0), mem_image_of_mem _ ⟨hm, trivial⟩,
      ⟨(-1, Real.pi), ⟨hm, trivial⟩, ?_⟩⟩
      (hS.image _ (continuous_zeroFibreSheet h 1).continuousOn)
      (hS.image _ (continuous_zeroFibreSheet h (-1)).continuousOn)
    simp [zeroFibreSheet, cylindricalPoint]
  · rw [fibre_eq_union_of_ne_zero hj]
    have hD : IsPreconnected
        ({z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} ×ˢ (univ : Set ℝ)) :=
      (convex_heights j h).isPreconnected.prod isPreconnected_univ
    rcases eq_empty_or_nonempty {z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)}
      with hDe | ⟨z₀, hz₀⟩
    · rw [hDe, empty_prod, image_empty, image_empty, union_self]
      exact isPreconnected_empty
    -- The vertical momentum vanishes at the top height of the fibre, where the sheets meet.
    obtain ⟨z₁, ⟨hz₁a, hz₁b⟩, hP⟩ := intermediate_value_Icc' hz₀.1.2.le
      (f := fun z : ℝ ↦ 2 * (h - z) * (1 - z ^ 2) - j ^ 2) (by fun_prop)
      ⟨by norm_num; positivity, sub_nonneg.2 hz₀.2⟩
    simp only at hP
    have hz₁1 : z₁ < 1 := hz₁b.lt_of_ne <| by
      rintro rfl
      exact hj (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
    have hz₁ : z₁ ∈ {z ∈ Ioo (-1 : ℝ) 1 | j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)} :=
      ⟨⟨hz₀.1.1.trans_le hz₁a, hz₁1⟩, by linarith⟩
    refine IsPreconnected.union' ⟨fibreSheet h j 1 (z₁, 0), mem_image_of_mem _ ⟨hz₁, trivial⟩,
      ⟨(z₁, 0), ⟨hz₁, trivial⟩, ?_⟩⟩ (hD.image _ (continuousOn_fibreSheet h j 1))
      (hD.image _ (continuousOn_fibreSheet h j (-1)))
    simp [fibreSheet, hP]

/-- Every value `c` of the energy–momentum map of the spherical pendulum has a connected fibre. -/
theorem isConnected_sphericalPendulumPhaseSpace_inter_preimage_singleton {c : ℝ × ℝ}
    (hc : c ∈ sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace) :
    IsConnected (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {c}) := by
  obtain ⟨x, hx, rfl⟩ := hc
  exact ⟨⟨x, hx, rfl⟩, isPreconnected_sphericalPendulumPhaseSpace_inter_preimage_singleton _⟩

/-- Every fibre of the energy–momentum map of the spherical pendulum is compact, as a closed
subset of a compact energy sublevel set. -/
theorem isCompact_sphericalPendulumPhaseSpace_inter_preimage_singleton (c : ℝ × ℝ) :
    IsCompact (sphericalPendulumPhaseSpace ∩ sphericalPendulumEnergyMomentum ⁻¹' {c}) :=
  (isCompact_sphericalPendulumPhaseSpace_inter_preimage_Iic c.1).of_isClosed_subset
    (isClosed_sphericalPendulumPhaseSpace.inter
      (isClosed_singleton.preimage continuous_sphericalPendulumEnergyMomentum))
    fun _ ⟨hx, hF⟩ ↦ ⟨hx, le_of_eq (congrArg Prod.fst hF)⟩

end TauCeti
