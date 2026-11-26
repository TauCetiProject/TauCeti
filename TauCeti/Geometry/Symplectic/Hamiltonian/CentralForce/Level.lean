/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar

/-!
# Connected levels of planar central forces

Let `V` be a plane with an orthonormal basis `b`, and let `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` be a
central-force Hamiltonian with angular momentum `L = q₁p₂ - q₂p₁`. Fixing `L = ℓ` reduces the
motion to the half-line `r > 0`, with the radial Hamiltonian `p_r² / (2m) + U_ℓ(r)` and the
effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`. This file compares the connectedness of the
common level `{q ≠ 0, H = E, L = ℓ}` of the planar problem with that of the radial level
`{r > 0, p_r² / (2m) + U_ℓ(r) = E}`.

* The common level is connected exactly when the radial level is
  (`TauCeti.isConnected_setOf_centralForceHamiltonian_eq_iff`). The polar canonical
  parametrization `TauCeti.polarCanonical` carries the product of the radial level with the line
  of angles onto the common level, and the radial projection `(q, p) ↦ (‖q‖, ⟪q, p⟫ / ‖q‖)`
  carries the common level back onto the radial level.
* A radial level over a potential well is connected
  (`TauCeti.isConnected_setOf_sq_div_add_eq`): if, for `r > 0`, a potential `f` lies below `E`
  exactly on an interval `[a, b]` with `0 < a` and `f(a) = E`, then the level
  `{r > 0, p² / (2m) + f(r) = E}` is the union of the two graphs `p = ±√(2m (E - f(r)))` over
  `[a, b]`, which meet at the turning point `(a, 0)`.

For the Kepler problem these combine into the connectedness of its bound levels,
`TauCeti.isConnected_setOf_centralForceHamiltonian_kepler_eq`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 4 and 8.
-/

public section

open Set
open scoped InnerProductSpace

namespace TauCeti

/-- **The level of a potential well is connected.** Let `m > 0`, and let `f` be a potential which,
on the half-line `r > 0`, lies below the energy `E` exactly on an interval `[a, b]` with `0 < a`,
is continuous there and has a turning point `f(a) = E`. Then the energy level
`{(r, p) | r > 0, p² / (2m) + f(r) = E}` is connected: it is the union of the two graphs
`p = ±√(2m (E - f(r)))` over `[a, b]`, which meet at `(a, 0)`. -/
theorem isConnected_setOf_sq_div_add_eq {m : ℝ} (hm : 0 < m) {f : ℝ → ℝ} {a b E : ℝ}
    (ha : 0 < a) (hf : ContinuousOn f (Icc a b)) (hfa : f a = E)
    (hle : ∀ r, 0 < r → (f r ≤ E ↔ r ∈ Icc a b)) :
    IsConnected {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ^ 2 / (2 * m) + f y.1 = E} := by
  have hab : a ≤ b := ((hle a ha).1 hfa.le).2
  set g : ℝ → ℝ := fun r ↦ √(2 * m * (E - f r))
  have hg : ContinuousOn g (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul (continuousOn_const.sub hf))
  -- The square of `g r` is `2 m (E - f r)` on `[a, b]`, where `f ≤ E`.
  have hg_sq (r : ℝ) (hr : r ∈ Icc a b) : g r ^ 2 = 2 * m * (E - f r) :=
    Real.sq_sqrt (mul_nonneg (by positivity)
      (sub_nonneg.2 ((hle r (ha.trans_le hr.1)).2 hr)))
  have heq : {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ^ 2 / (2 * m) + f y.1 = E} =
      (fun r ↦ (r, g r)) '' Icc a b ∪ (fun r ↦ (r, -g r)) '' Icc a b := by
    ext ⟨r, p⟩
    simp only [mem_ofPred_eq, mem_union, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨hr, hE⟩
      have hp : p ^ 2 = 2 * m * (E - f r) := by
        rw [← hE]
        field_simp
        ring
      have hr' : r ∈ Icc a b := (hle r hr).1 (by nlinarith [sq_nonneg p])
      have habs : g r = |p| := by
        simp only [g, ← hp, Real.sqrt_sq_eq_abs]
      rcases abs_choice p with h | h
      · exact Or.inl ⟨r, hr', rfl, by rw [habs, h]⟩
      · exact Or.inr ⟨r, hr', rfl, by rw [habs, h, neg_neg]⟩
    · rintro (⟨r, hr, rfl, rfl⟩ | ⟨r, hr, rfl, rfl⟩) <;> refine ⟨ha.trans_le hr.1, ?_⟩
      · rw [hg_sq r hr]
        field_simp
        ring
      · rw [neg_sq, hg_sq r hr]
        field_simp
        ring
  rw [heq]
  have ha' : a ∈ Icc a b := left_mem_Icc.2 hab
  refine IsConnected.union ⟨(a, g a), mem_image_of_mem _ ha', ⟨a, ha', ?_⟩⟩
    ((isConnected_Icc hab).image _ (continuousOn_id.prodMk hg))
    ((isConnected_Icc hab).image _ (continuousOn_id.prodMk hg.neg))
  simp [g, hfa]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)

/-- The point with polar coordinates `(r, p_r, θ, ℓ)`, `r > 0`, lies in the common level
`{q ≠ 0, H = E, L = ℓ}` exactly when `(r, p_r)` lies in the radial level
`{r > 0, p_r² / (2m) + U_ℓ(r) = E}`. -/
private theorem polarCanonical_mem_level_iff (m : ℝ) (U : ℝ → ℝ) {E ℓ : ℝ} {y : ℝ × ℝ}
    (hy : 0 < y.1) (θ : ℝ) :
    polarCanonical (b 0) (b 1) (y, (θ, ℓ)) ∈ {x : V × V | x.1 ≠ 0 ∧
        centralForceHamiltonian m U x = E ∧ angularMomentum (b 0) (b 1) x = ℓ} ↔
      y ∈ {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ^ 2 / (2 * m) + effectivePotential m ℓ U y.1 = E} := by
  have h0 := b.norm_eq_one 0
  have h1 := b.norm_eq_one 1
  have h01 : ⟪b 0, b 1⟫_ℝ = 0 := b.inner_eq_zero (by decide)
  have hq : (polarCanonical (b 0) (b 1) (y, (θ, ℓ))).1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_fst_polarCanonical h0 h1 h01]
    exact abs_ne_zero.2 hy.ne'
  simp only [mem_ofPred_eq,
    centralForceHamiltonian_polarCanonical h0 h1 h01 m U (x := (y, (θ, ℓ))) hy,
    angularMomentum_polarCanonical h0 h1 h01 (x := (y, (θ, ℓ))) hy.ne', hq, hy, ne_eq,
    not_false_eq_true, and_true, true_and]

/-- The radial projection carries the common level `{q ≠ 0, H = E, L = ℓ}` onto the radial level
`{r > 0, p_r² / (2m) + U_ℓ(r) = E}`. -/
private theorem image_radialProjection_level (m : ℝ) (U : ℝ → ℝ) (E ℓ : ℝ) :
    radialProjection '' {x : V × V | x.1 ≠ 0 ∧ centralForceHamiltonian m U x = E ∧
        angularMomentum (b 0) (b 1) x = ℓ} =
      {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ^ 2 / (2 * m) + effectivePotential m ℓ U y.1 = E} := by
  have h0 := b.norm_eq_one 0
  have h1 := b.norm_eq_one 1
  have h01 : ⟪b 0, b 1⟫_ℝ = 0 := b.inner_eq_zero (by decide)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hr : 0 < (radialProjection x).1 := by
      rw [radialProjection_fst]
      exact norm_pos_iff.2 hx.1
    have hx' := polarCanonical_radialProjection b hx.1
    rw [hx.2.2] at hx'
    rw [← polarCanonical_mem_level_iff b m U hr, hx']
    exact hx
  · intro hy
    refine ⟨polarCanonical (b 0) (b 1) (y, (0, ℓ)),
      (polarCanonical_mem_level_iff b m U hy.1 0).2 hy, Prod.ext ?_ ?_⟩
    · rw [radialProjection_fst, norm_fst_polarCanonical h0 h1 h01, abs_of_pos hy.1]
    · exact (radialProjection_snd _).trans
        (radialMomentum_polarCanonical h0 h1 h01 (x := (y, (0, ℓ))) hy.1)

/-- The polar canonical parametrization carries the product of the radial level
`{r > 0, p_r² / (2m) + U_ℓ(r) = E}` with the line of angles onto the common level
`{q ≠ 0, H = E, L = ℓ}`. -/
private theorem image_polarCanonical_level (m : ℝ) (U : ℝ → ℝ) (E ℓ : ℝ) :
    (fun z : (ℝ × ℝ) × ℝ ↦ polarCanonical (b 0) (b 1) (z.1, (z.2, ℓ))) ''
        ({y : ℝ × ℝ | 0 < y.1 ∧ y.2 ^ 2 / (2 * m) + effectivePotential m ℓ U y.1 = E} ×ˢ univ) =
      {x : V × V | x.1 ≠ 0 ∧ centralForceHamiltonian m U x = E ∧
        angularMomentum (b 0) (b 1) x = ℓ} := by
  ext x
  constructor
  · rintro ⟨z, ⟨hz, -⟩, rfl⟩
    exact (polarCanonical_mem_level_iff b m U hz.1 z.2).2 hz
  · intro hx
    have hx' := polarCanonical_radialProjection b hx.1
    rw [hx.2.2] at hx'
    refine ⟨(radialProjection x, (polarAngle (b 0) (b 1) x.1).toReal), ⟨?_, mem_univ _⟩, hx'⟩
    rw [← image_radialProjection_level b m U E ℓ]
    exact mem_image_of_mem _ hx

/-- **Central-force levels are connected exactly when their radial levels are.** For a central
force with potential `U`, the common level `{q ≠ 0, H = E, L = ℓ}` of the energy and the angular
momentum in the plane is connected if and only if the radial level
`{r > 0, p_r² / (2m) + U_ℓ(r) = E}` of the effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)` is
connected. -/
theorem isConnected_setOf_centralForceHamiltonian_eq_iff (m : ℝ) (U : ℝ → ℝ) (E ℓ : ℝ) :
    IsConnected {x : V × V | x.1 ≠ 0 ∧ centralForceHamiltonian m U x = E ∧
        angularMomentum (b 0) (b 1) x = ℓ} ↔
      IsConnected {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ^ 2 / (2 * m) + effectivePotential m ℓ U y.1 = E} := by
  constructor
  · -- The radial projection is continuous off the collision set.
    intro hS
    rw [← image_radialProjection_level b m U E ℓ]
    exact hS.image _ fun x hx ↦ (continuousAt_radialProjection hx.1).continuousWithinAt
  · -- The polar canonical parametrization is continuous where `r > 0`.
    intro hR
    rw [← image_polarCanonical_level b m U E ℓ]
    refine (hR.prod isConnected_univ).image _ fun z hz ↦ ContinuousAt.continuousWithinAt ?_
    exact (contDiffAt_polarCanonical (n := 0) (b 0) (b 1) (x := (z.1, (z.2, ℓ)))
      hz.1.1.ne').continuousAt.comp (x := z)
        (by fun_prop : ContinuousAt (fun z : (ℝ × ℝ) × ℝ ↦ (z.1, (z.2, ℓ))) z)

end TauCeti
