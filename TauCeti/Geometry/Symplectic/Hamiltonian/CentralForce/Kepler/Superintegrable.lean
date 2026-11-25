/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RungeLenz
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Torus

/-!
# Superintegrability of the planar Kepler problem

A particle of mass `m` in the plane `V`, moving in the Kepler potential `-κ / r`, has four first
integrals off the collision set `q = 0`: the energy `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖`, the angular
momentum `L = q₁p₂ - q₂p₁` and the two components `A₁, A₂` of the Runge–Lenz vector `A`, written
in an orthonormal basis `b` of `V`. Together they form the map

`(H, L, A₁, A₂) : V × V → ℝ⁴` (`TauCeti.keplerFirstIntegrals`).

Each of them Poisson-commutes with `H`
(`TauCeti.stdSymplecticForm_poissonBracket_keplerFirstIntegrals`). On the four-dimensional phase
space they cannot all be independent: they satisfy the length identity

`A₁² + A₂² = (m κ)² + 2 m H L²`

(`TauCeti.keplerFirstIntegrals_two_sq_add_three_sq`), and differentiating it gives the linear
relation `A₁ dA₁ + A₂ dA₂ = m L² dH + 2 m H L dL` between their differentials
(`TauCeti.keplerFirstIntegrals_two_mul_fderiv_add_three_mul_fderiv`). This is the only relation:

* for `m, κ ≠ 0`, the differential of `(H, L, A₁, A₂)` has rank at most three at every
  noncollision point, since the coefficients `(-m L², -2 m H L, A₁, A₂)` of the relation never all
  vanish there (`TauCeti.finrank_range_fderiv_keplerFirstIntegrals_le_three`);
* its rank is exactly three wherever the Runge–Lenz vector is nonzero
  (`TauCeti.finrank_range_fderiv_keplerFirstIntegrals_eq_three`).

For `m > 0` and nonzero angular momentum, the Runge–Lenz vector is nonzero exactly when the energy
exceeds `-m κ² / (2 L²)` (`TauCeti.rungeLenz_ne_zero_iff_lt_centralForceHamiltonian`); for `κ > 0`
this is the energy of the circular orbit with angular momentum `L`. The states of the bound phase
space `{q ≠ 0, H < 0, L ≠ 0}` (`TauCeti.keplerBoundPhaseSpace`) with nonzero Runge–Lenz vector form
a dense open subset of it, on which `(H, L, A₁, A₂)` has rank exactly three
(`TauCeti.exists_isOpen_finrank_range_fderiv_keplerFirstIntegrals_eq_three`): the
bound Kepler problem is superintegrable.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 49.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Section 3.9.
-/

public noncomputable section

open Function Set Module
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V) {m κ : ℝ}

/-- The four first integrals `(H, L, A₁, A₂)` of the planar Kepler problem with mass `m` and
potential `-κ / r`: the energy, the angular momentum and the two components of the Runge–Lenz
vector in the orthonormal basis `b`. -/
def keplerFirstIntegrals (m κ : ℝ) (x : V × V) : Fin 4 → ℝ :=
  ![centralForceHamiltonian m (fun r ↦ -κ / r) x, angularMomentum (b 0) (b 1) x,
    ⟪rungeLenz m κ x, b 0⟫_ℝ, ⟪rungeLenz m κ x, b 1⟫_ℝ]

@[simp]
theorem keplerFirstIntegrals_zero (m κ : ℝ) (x : V × V) :
    keplerFirstIntegrals b m κ x 0 = centralForceHamiltonian m (fun r ↦ -κ / r) x :=
  (rfl)

@[simp]
theorem keplerFirstIntegrals_one (m κ : ℝ) (x : V × V) :
    keplerFirstIntegrals b m κ x 1 = angularMomentum (b 0) (b 1) x :=
  (rfl)

@[simp]
theorem keplerFirstIntegrals_two (m κ : ℝ) (x : V × V) :
    keplerFirstIntegrals b m κ x 2 = ⟪rungeLenz m κ x, b 0⟫_ℝ :=
  (rfl)

@[simp]
theorem keplerFirstIntegrals_three (m κ : ℝ) (x : V × V) :
    keplerFirstIntegrals b m κ x 3 = ⟪rungeLenz m κ x, b 1⟫_ℝ :=
  (rfl)

/-- **The length identity.** Off the collision set, the four first integrals of the planar Kepler
problem satisfy `A₁² + A₂² = (m κ)² + 2 m H L²`. -/
theorem keplerFirstIntegrals_two_sq_add_three_sq (hm : m ≠ 0) {x : V × V} (hq : x.1 ≠ 0) :
    keplerFirstIntegrals b m κ x 2 ^ 2 + keplerFirstIntegrals b m κ x 3 ^ 2 =
      (m * κ) ^ 2 +
        2 * m * keplerFirstIntegrals b m κ x 0 * keplerFirstIntegrals b m κ x 1 ^ 2 := by
  rw [keplerFirstIntegrals_two, keplerFirstIntegrals_three,
    ← Fin.sum_univ_two (fun i ↦ ⟪rungeLenz m κ x, b i⟫_ℝ ^ 2), b.sum_sq_inner_left,
    norm_rungeLenz_sq_of_orthonormalBasis b hm κ hq, keplerFirstIntegrals_zero,
    keplerFirstIntegrals_one]

/-- The four first integrals of the planar Kepler problem are differentiable off the collision
set. -/
theorem differentiableAt_keplerFirstIntegrals {x : V × V} (hq : x.1 ≠ 0) :
    DifferentiableAt ℝ (keplerFirstIntegrals b m κ) x := by
  refine differentiableAt_pi.2 fun i ↦ ?_
  fin_cases i
  · exact (hasFDerivAt_centralForceHamiltonian
      (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq)) hq).differentiableAt
  · exact (hasFDerivAt_angularMomentum (b 0) (b 1) x).differentiableAt
  · exact (hasFDerivAt_inner_rungeLenz m κ (b 0) hq).differentiableAt
  · exact (hasFDerivAt_inner_rungeLenz m κ (b 1) hq).differentiableAt

/-- **The relation between the differentials.** Off the collision set, differentiating the length
identity gives `A₁ dA₁ + A₂ dA₂ = m L² dH + 2 m H L dL` for the differential of the four first
integrals `(H, L, A₁, A₂)` of the planar Kepler problem. -/
theorem keplerFirstIntegrals_two_mul_fderiv_add_three_mul_fderiv (hm : m ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) (v : V × V) :
    keplerFirstIntegrals b m κ x 2 * fderiv ℝ (keplerFirstIntegrals b m κ) x v 2 +
        keplerFirstIntegrals b m κ x 3 * fderiv ℝ (keplerFirstIntegrals b m κ) x v 3 =
      m * keplerFirstIntegrals b m κ x 1 ^ 2 * fderiv ℝ (keplerFirstIntegrals b m κ) x v 0 +
        2 * m * keplerFirstIntegrals b m κ x 0 * keplerFirstIntegrals b m κ x 1 *
          fderiv ℝ (keplerFirstIntegrals b m κ) x v 1 := by
  set F := keplerFirstIntegrals b m κ
  have hc (i : Fin 4) : HasFDerivAt (fun y ↦ F y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ F x)) x :=
    hasFDerivAt_pi'.1 (differentiableAt_keplerFirstIntegrals b hq).hasFDerivAt i
  -- The function `A₁² + A₂² - 2 m H L²` is constant on the open set `q ≠ 0`.
  let g : V × V → ℝ := fun y ↦ F y 2 ^ 2 + F y 3 ^ 2 - 2 * m * F y 0 * F y 1 ^ 2
  have hconst : HasFDerivAt g (0 : V × V →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const ((m * κ) ^ 2) x).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_const).mem_nhds hq] with y hy
    simp only [g]
    rw [keplerFirstIntegrals_two_sq_add_three_sq b hm hy]
    ring
  have hg : HasFDerivAt g _ x :=
    (((hc 2).pow 2).add ((hc 3).pow 2)).sub (((hc 0).const_mul (2 * m)).mul ((hc 1).pow 2))
  have h := congrArg (fun φ : V × V →L[ℝ] ℝ ↦ φ v) (hg.unique hconst)
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.proj_apply, zero_apply, smul_eq_mul] at h
  linear_combination h / 2

/-- A nonzero coefficient vector `(-m L², -2 m H L, A₁, A₂)` of the relation between the
differentials forces the differential of the first integrals to be nonsurjective, of rank at most
three. -/
private theorem finrank_range_fderiv_keplerFirstIntegrals_le_three_of_ne_zero (hm : m ≠ 0)
    {x : V × V} (hq : x.1 ≠ 0)
    (h : keplerFirstIntegrals b m κ x 1 ≠ 0 ∨ keplerFirstIntegrals b m κ x 2 ≠ 0 ∨
      keplerFirstIntegrals b m κ x 3 ≠ 0) :
    finrank ℝ (LinearMap.range (fderiv ℝ (keplerFirstIntegrals b m κ) x).toLinearMap) ≤ 3 := by
  set F := keplerFirstIntegrals b m κ
  -- If the differential were onto, the relation would hold for every vector of `ℝ⁴`.
  have hne : LinearMap.range (fderiv ℝ F x).toLinearMap ≠ ⊤ := by
    intro htop
    have hall (w : Fin 4 → ℝ) :
        F x 2 * w 2 + F x 3 * w 3 = m * F x 1 ^ 2 * w 0 + 2 * m * F x 0 * F x 1 * w 1 := by
      obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop w
      have hrel := keplerFirstIntegrals_two_mul_fderiv_add_three_mul_fderiv b (κ := κ) hm hq v
      simp only [ContinuousLinearMap.coe_coe] at hv
      rwa [hv] at hrel
    have h0 : m * F x 1 ^ 2 = 0 := by simpa using (hall (Pi.single 0 1)).symm
    have h2 : F x 2 = 0 := by simpa using hall (Pi.single 2 1)
    have h3 : F x 3 = 0 := by simpa using hall (Pi.single 3 1)
    rcases h with h | h | h
    · exact h (pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h0).resolve_left hm))
    · exact h h2
    · exact h h3
  have hlt := Submodule.finrank_lt hne
  rw [finrank_fin_fun] at hlt
  omega

/-- **At most three of the four Kepler integrals are independent.** For nonzero mass and coupling,
the differential of `(H, L, A₁, A₂)` has rank at most three at every noncollision point. -/
theorem finrank_range_fderiv_keplerFirstIntegrals_le_three (hm : m ≠ 0) (hκ : κ ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) :
    finrank ℝ (LinearMap.range (fderiv ℝ (keplerFirstIntegrals b m κ) x).toLinearMap) ≤ 3 := by
  refine finrank_range_fderiv_keplerFirstIntegrals_le_three_of_ne_zero b hm hq ?_
  by_contra! h
  -- If `L = A₁ = A₂ = 0`, the length identity reads `0 = (m κ)²`.
  have hrel := keplerFirstIntegrals_two_sq_add_three_sq b hm (κ := κ) hq
  rw [h.1, h.2.1, h.2.2] at hrel
  exact mul_ne_zero hm hκ (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination -hrel))

/-- **Three of the four Kepler integrals are independent where the Runge–Lenz vector is nonzero.**
At every noncollision point with nonzero Runge–Lenz vector, the differential of `(H, L, A₁, A₂)`
has rank exactly three. -/
theorem finrank_range_fderiv_keplerFirstIntegrals_eq_three (hm : m ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) (hA : rungeLenz m κ x ≠ 0) :
    finrank ℝ (LinearMap.range (fderiv ℝ (keplerFirstIntegrals b m κ) x).toLinearMap) = 3 := by
  set F := keplerFirstIntegrals b m κ
  have hA' : F x 2 ≠ 0 ∨ F x 3 ≠ 0 := by
    by_contra! h
    have hn := b.sum_sq_inner_left (rungeLenz m κ x)
    simp only [F, keplerFirstIntegrals_two, keplerFirstIntegrals_three] at h
    rw [Fin.sum_univ_two, h.1, h.2] at hn
    exact hA (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by simpa using hn.symm)))
  refine le_antisymm
    (finrank_range_fderiv_keplerFirstIntegrals_le_three_of_ne_zero b hm hq (Or.inr hA')) ?_
  -- Every function factoring linearly through `F` has its differential in the range of the dual
  -- map of `dF`.
  have hF := differentiableAt_keplerFirstIntegrals b (m := m) (κ := κ) hq
  have hmem (c : (Fin 4 → ℝ) →L[ℝ] ℝ) {f : V × V → ℝ} (hf : f = c ∘ F) :
      (fderiv ℝ f x : V × V →ₗ[ℝ] ℝ) ∈
        LinearMap.range (fderiv ℝ F x).toLinearMap.dualMap := by
    rw [hf, (c.hasFDerivAt.comp x hF.hasFDerivAt).fderiv]
    exact ⟨c, by rw [LinearMap.dualMap_apply', ContinuousLinearMap.toLinearMap_comp]⟩
  -- Energy, angular momentum and a Runge–Lenz component have independent differentials.
  obtain ⟨e, hli⟩ := exists_linearIndependent_fderiv_kepler_of_rungeLenz_ne_zero b hm hq hA
  have hli' := hli.map' (ContinuousLinearMap.coeLM ℝ)
    (LinearMap.ker_eq_bot.2 ContinuousLinearMap.coe_injective)
  set S := Submodule.span ℝ (range ((ContinuousLinearMap.coeLM ℝ) ∘ ![
    fderiv ℝ (centralForceHamiltonian m (fun r ↦ -κ / r)) x,
    fderiv ℝ (angularMomentum (b 0) (b 1)) x,
    fderiv ℝ (fun y ↦ ⟪rungeLenz m κ y, e⟫_ℝ) x])) with hS
  have hsub : S ≤ LinearMap.range (fderiv ℝ F x).toLinearMap.dualMap := by
    rw [Submodule.span_le, range_subset_iff]
    intro i
    fin_cases i
    · exact hmem (ContinuousLinearMap.proj 0)
        (funext fun y ↦ (keplerFirstIntegrals_zero b m κ y).symm)
    · exact hmem (ContinuousLinearMap.proj 1)
        (funext fun y ↦ (keplerFirstIntegrals_one b m κ y).symm)
    · -- `⟪A, e⟫ = ⟪b 0, e⟫ A₁ + ⟪b 1, e⟫ A₂`.
      refine hmem (⟪b 0, e⟫_ℝ • ContinuousLinearMap.proj 2 +
        ⟪b 1, e⟫_ℝ • ContinuousLinearMap.proj 3) (funext fun y ↦ ?_)
      simp only [comp_apply, add_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, F, keplerFirstIntegrals_two,
        keplerFirstIntegrals_three]
      rw [← b.sum_inner_mul_inner, Fin.sum_univ_two]
      ring
  calc 3 = finrank ℝ S := by rw [hS, finrank_span_eq_card hli', Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono hsub
    _ = _ := LinearMap.finrank_range_dualMap_eq_finrank_range _

/-- The states of the bound phase space of the Kepler problem with nonzero Runge–Lenz vector form
an open set. -/
theorem isOpen_setOf_mem_keplerBoundPhaseSpace_and_rungeLenz_ne_zero :
    IsOpen {x : V × V | x ∈ keplerBoundPhaseSpace b m κ ∧ rungeLenz m κ x ≠ 0} :=
  ContinuousOn.isOpen_inter_preimage (t := {0}ᶜ)
    (fun _ hx ↦ (contDiffAt_rungeLenz m κ (n := 0)
      ((mem_keplerBoundPhaseSpace b).1 hx).1).continuousAt.continuousWithinAt)
    (keplerBoundPhaseSpace b m κ).isOpen isOpen_compl_singleton

/-- For nonzero mass and coupling, the states of the bound phase space of the Kepler problem with
nonzero Runge–Lenz vector are dense in it. -/
theorem keplerBoundPhaseSpace_subset_closure_setOf_rungeLenz_ne_zero (hm : m ≠ 0) (hκ : κ ≠ 0) :
    (keplerBoundPhaseSpace b m κ : Set (V × V)) ⊆
      closure {x | x ∈ keplerBoundPhaseSpace b m κ ∧ rungeLenz m κ x ≠ 0} := by
  intro x hx
  -- Transfer the density of `A ≠ 0` in the punctured phase space to its open subset.
  have ht : IsOpen (Subtype.val ⁻¹' (keplerBoundPhaseSpace b m κ : Set (V × V)) :
      Set (puncturedPhaseSpace V)) :=
    (keplerBoundPhaseSpace b m κ).isOpen.preimage continuous_subtypeVal
  have hx' := (dense_setOf_rungeLenz_ne_zero hm hκ).open_subset_closure_inter ht
    (a := ⟨x, mem_puncturedPhaseSpace.2 ((mem_keplerBoundPhaseSpace b).1 hx).1⟩)
    (mem_preimage.2 hx)
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_subtypeVal ⟨_, hx', rfl⟩)
  rintro _ ⟨y, ⟨hy, hyA⟩, rfl⟩
  exact ⟨hy, hyA⟩

/-- **Superintegrability of the bound Kepler problem.** For nonzero mass and coupling, the four
first integrals `(H, L, A₁, A₂)` have rank exactly three on a dense open subset of the bound phase
space `{q ≠ 0, H < 0, L ≠ 0}`: the noncircular bound states. -/
theorem exists_isOpen_finrank_range_fderiv_keplerFirstIntegrals_eq_three (hm : m ≠ 0)
    (hκ : κ ≠ 0) :
    ∃ U : Set (V × V), IsOpen U ∧ U ⊆ keplerBoundPhaseSpace b m κ ∧
      (keplerBoundPhaseSpace b m κ : Set (V × V)) ⊆ closure U ∧ ∀ x ∈ U,
        finrank ℝ (LinearMap.range (fderiv ℝ (keplerFirstIntegrals b m κ) x).toLinearMap) = 3 :=
  ⟨_, isOpen_setOf_mem_keplerBoundPhaseSpace_and_rungeLenz_ne_zero b, fun _ hx ↦ hx.1,
    keplerBoundPhaseSpace_subset_closure_setOf_rungeLenz_ne_zero b hm hκ, fun _ hx ↦
      finrank_range_fderiv_keplerFirstIntegrals_eq_three b hm
        ((mem_keplerBoundPhaseSpace b).1 hx.1).1 hx.2⟩

variable [FiniteDimensional ℝ V]

/-- **The four Kepler integrals are first integrals.** Off the collision set, each component of
`(H, L, A₁, A₂)` Poisson-commutes with the Kepler Hamiltonian `H`. -/
theorem stdSymplecticForm_poissonBracket_keplerFirstIntegrals (hm : m ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) (i : Fin 4) :
    (stdSymplecticForm (V := V)).poissonBracket (fun y ↦ keplerFirstIntegrals b m κ y i)
      (centralForceHamiltonian m fun r ↦ -κ / r) x = 0 := by
  match i with
  | 0 =>
    simp only [keplerFirstIntegrals_zero]
    exact SymplecticForm.poissonBracket_self _ _ _
  | 1 =>
    simp only [keplerFirstIntegrals_one]
    have h := stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum
      (m := m) (U := fun r ↦ -κ / r) (x := x) (b 0) (b 1)
    rw [← SymplecticForm.neg_poissonBracket] at h
    exact neg_eq_zero.1 h
  | 2 =>
    simp only [keplerFirstIntegrals_two]
    exact stdSymplecticForm_poissonBracket_inner_rungeLenz hm κ (b 0) hq
  | 3 =>
    simp only [keplerFirstIntegrals_three]
    exact stdSymplecticForm_poissonBracket_inner_rungeLenz hm κ (b 1) hq

end TauCeti
