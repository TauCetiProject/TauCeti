/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity

/-!
# Asymptotic orbits at the ends of a finite-energy Floer pair of pants

Let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in a
symplectic vector space `(V, ω)`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q`,
for period-one Hamiltonians `H_q`, and let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on
`S` for uniformly tame almost complex structures `J(z)`. Suppose that `u` has image in a compact
set and finite energy. This file shows that `u` breaks off a one-periodic orbit of `H_q` at each
end `q`, and that the energy identity of the pair of pants holds with the actions of these orbits.

**Positive end charts.** On the input ends `0` and `1` of `S` the end coordinate `s` of the end
chart `φ_q` (`TauCeti.Floer.endChart`) tends to `+∞`, on the output end `∞` to `-∞`. The positive
end chart `φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`), with the sign of the end,
is again holomorphic, and in it the perturbation `K` becomes `H'_q(t) dt` far out, for the
Hamiltonian `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`): `H'_q = H_q` on
the inputs and `H'_∞(t, x) = -H_∞(-t, x)` on the output. Since holomorphic changes of coordinates
preserve the Floer equation and the energy, `u ∘ φ'_q` solves the Floer equation of a half-cylinder
for `H'_q` beyond `T₀`
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart`), and its
energy over a half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u`
over `S` (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). So
the results of `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` about finite-energy Floer
half-cylinders apply at each end of the pair of pants.

**Orbits at the ends.** Reversing the time of an orbit of `H'_∞` gives an orbit of `H_∞`, and
reversing the time of a loop negates its action for the reversed Hamiltonian
(`TauCeti.SymplecticForm.hamiltonianAction_comp_neg`). Read back in the end chart `φ_q`, this
gives, for each end `q`:

* a one-periodic orbit `y_q` of `X_{H_q}` and `s_n → ∞` such that the loops
  `t ↦ u(φ_q(±s_n, t))` converge uniformly to `y_q`
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_endChart_of_floer`);
* if `u` is `C²`, such an orbit for which, moreover, the actions `A_{H_q}(u(φ_q(±s, ·)))` tend to
  `A_{H_q}(y_q)` as `s → ∞`
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_endChart_of_floer`).

**The energy identity.** Consequently, the energy of such a solution is

`E(u) = A_{H_0}(y_0) + A_{H_1}(y_1) - A_{H_∞}(y_∞) - ∫_S R_K(u)`

for one-periodic orbits `y_q` of the end Hamiltonians
(`TauCeti.SymplecticForm.exists_lintegral_floerEnergyDensity_eq_sum_hamiltonianAction`, and
`TauCeti.SymplecticForm.exists_lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq` for the
pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation`). The identities
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm` and
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq` assume that the
actions of the end loops converge; here this convergence follows from finite energy and
compactness.

Without nondegeneracy the orbit `y_q` is obtained along a sequence `s_n`, while the convergence of
the actions holds along the whole end. Convergence of the whole end to a single orbit, which needs
nondegenerate orbits and a bound on the derivative, is proved in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ω : SymplecticForm V}
  {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {T₀ : ℝ}

variable [FiniteDimensional ℝ V]

/-! ### Orbits and actions in positive end charts -/

/-- Reading an orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the end gives
an orbit of `H_q`. -/
theorem hasDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (t : ℝ) :
    HasDerivAt (fun t ↦ x (q.endSign * t))
      (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) t := by
  have h := (hx (q.endSign * t)).scomp t ((hasDerivAt_id' t).const_mul q.endSign)
  have hX : ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) =
      fun y ↦ q.endSign • ω.hamiltonianVectorField (H q t) y := by
    funext y
    rw [show positiveEndHamiltonian H q (q.endSign * t) = fun y ↦ q.endSign * H q t y by
      funext y; rw [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul],
      hamiltonianVectorField_const_mul]
  rw [hX, mul_one, smul_smul, endSign_mul_self, one_smul] at h
  exact h

omit [FiniteDimensional ℝ V] in
/-- The action of a loop for the positive end Hamiltonian `H'_q` is `±` the action, for `H_q`,
of the loop read with the time `±t` of the end. -/
theorem hamiltonianAction_positiveEndHamiltonian {q : Puncture} (hH : Periodic (H q) 1)
    {x : ℝ → V} (hx : Periodic x 1) :
    ω.hamiltonianAction (positiveEndHamiltonian H q) x =
      q.endSign * ω.hamiltonianAction (H q) (fun t ↦ x (q.endSign * t)) := by
  rcases q.endSign_eq_one_or_eq_neg_one with h | h
  · have hH' : positiveEndHamiltonian H q = H q := by
      funext t y
      simp [positiveEndHamiltonian_apply, h]
    simp [hH', h]
  · have hH' : positiveEndHamiltonian H q = fun t y ↦ -H q (-t) y := by
      funext t y
      simp [positiveEndHamiltonian_apply, h]
    have hx' : Periodic (fun t ↦ x (-t)) 1 := by
      simpa only [h, neg_one_mul] using periodic_comp_endSign_mul (q := q) hx
    have h' := ω.hamiltonianAction_comp_neg hH hx'
    simp only [neg_neg] at h'
    rw [hH', h]
    simpa using h'

/-! ### The ends of a Floer pair of pants as Floer half-cylinders -/

/-- For the constant two-form of `ω`, the intrinsic perturbed derivative is the vector-space
perturbed derivative. -/
private theorem perturbedMFDeriv_constSmooth_eq (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    (ω.constSmooth.perturbedMFDeriv Ks Kt u z : ℝ × ℝ →L[ℝ] V) = ω.perturbedFDeriv Ks Kt u z :=
  ContinuousLinearMap.ext fun v ↦ by
    have h := ω.fromTangentSpace_perturbedMFDeriv_constSmooth_apply Ks Kt u z v
    rw [NormedSpace.fromTangentSpace_apply] at h
    exact h

/-- **The ends of a Floer pair of pants solve the Floer equation of a half-cylinder.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve the Floer equation
`(du - X_K)^{0,1} = 0` for the almost complex structure `J` at the image `φ'_q(ζ)` of a point `ζ`
with `s ≥ T₀` of the positive end chart. Then the map `u ∘ φ'_q` solves the Floer equation
`∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` of a half-cylinder at `ζ`, for the end Hamiltonian `H'_q` of
the positive end. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    {J : AlmostComplexStructure V} {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) :
          ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ : ℝ × ℝ →ₗ[ℝ] V) := by
  have h := ω.constSmooth.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart (hKH q)
    (hH q) (fun t ↦ (hHd q t).mdifferentiable) (J := J) hζ hu.mdifferentiableAt
    (by rwa [perturbedMFDeriv_constSmooth_eq])
  rwa [perturbedMFDeriv_constSmooth_eq] at h

/-- **The energy of an end of a Floer pair of pants.** Under the hypotheses of
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart`, the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]`, for
`a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a)
    (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  simpa only [floerEnergyDensity_constSmooth] using
    ω.constSmooth.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le (hKH q) (hH q)
      (fun t ↦ (hHd q t).mdifferentiable) hu.mdifferentiableOn ha₀ haT

/-! ### Asymptotic orbits at the ends -/

variable {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {c M : ℝ}

omit [FiniteDimensional ℝ V] in
/-- Uniform tameness `c ‖v‖² ≤ ω(v, J z v)` makes `ω(v, J z v)` positive for `v ≠ 0`. -/
private theorem apply_pos_of_tame (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) {v : V} (hv : v ≠ 0) : 0 < ω v (J z v) :=
  (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)

/-- The positive end chart maps the half-cylinder `(max T₀ 0, ∞) × ℝ` into `S`. -/
private theorem mapsTo_positiveEndChart (q : Puncture) :
    MapsTo (positiveEndChart q) (Ioi (max T₀ 0) ×ˢ univ) thricePuncturedSphereReal :=
  fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz.1)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Reading the end loop of `u ∘ φ'_q` with the time `±t` of the end gives the end loop of `u`. -/
private theorem comp_endChart_eq_comp_positiveEndChart (q : Puncture) (s : ℝ) :
    (fun t ↦ u (endChart q (q.endSign * s, t))) =
      (fun t ↦ (u ∘ positiveEndChart q) (s, t)) ∘ fun t ↦ q.endSign * t := by
  funext t
  simp only [comp_apply, endChart_eq_positiveEndChart]

/-- The hypotheses on `u` over `S` give the hypotheses of a finite-energy Floer half-cylinder for
`u ∘ φ'_q` over `(max T₀ 0, ∞) × [0, 1]`. -/
private theorem floer_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ thricePuncturedSphereReal, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    (∀ s, max T₀ 0 < s → ∀ t, (u ∘ positiveEndChart q) (s, t) ∈ B) ∧
      (∀ z ∈ Ioi (max T₀ 0) ×ˢ Icc 0 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ ω v ((J ∘ positiveEndChart q) z v)) ∧
      (∀ z ∈ Ioi (max T₀ 0) ×ˢ Icc 0 1, ∀ v, ‖(J ∘ positiveEndChart q) z v‖ ≤ M * ‖v‖) ∧
      (∀ z ∈ Ioi (max T₀ 0) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) ((J ∘ positiveEndChart q) z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
            (u ∘ positiveEndChart q) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi (max T₀ 0) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≠ ⊤ := by
  have hHd : ∀ q t, Differentiable ℝ (H q t) := fun q t ↦
    ((hHs q).differentiable one_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  have hud := hu.differentiableOn one_ne_zero
  have hmem (z : ℝ × ℝ) (hz : z ∈ Ioi (max T₀ 0) ×ˢ Icc 0 1) :
      positiveEndChart q z ∈ thricePuncturedSphereReal :=
    mapsTo_positiveEndChart q ⟨hz.1, mem_univ _⟩
  refine ⟨fun s hs t ↦ huB _ (mapsTo_positiveEndChart q ⟨hs, mem_univ _⟩),
    fun z hz v ↦ hJc _ (hmem z hz) v, fun z hz v ↦ hJM _ (hmem z hz) v, fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      hud q (le_max_right _ _) (le_max_left _ _))⟩
  exact isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart hKH hH hHd
    ((le_max_left _ _).trans hz.1.le)
    ((hud _ (hmem z hz)).differentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds (hmem z hz)))
    (hfloer _ (hmem z hz))

/-- **A finite-energy Floer pair of pants breaks off an orbit at each end.** Let `K` be equal to
`H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be
`C¹` on `S`, with image in a compact set, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`
for uniformly tame almost complex structures, `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖`. If the
energy of `u` over `S` is finite, then at each end `q` there are a `1`-periodic orbit `y` of the
Hamiltonian vector field of `H_q` and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with the
sign of the end, converge uniformly to `y`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_endChart_of_floer
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ thricePuncturedSphereReal, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (endChart q (q.endSign * σ n, t))) y atTop := by
  obtain ⟨huB', hJc', hJM', hfloer', hE'⟩ :=
    floer_comp_positiveEndChart hKH hH hHs hu huB hJc hJM hfloer hE q
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder.
  obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ := exists_periodic_hasDerivAt_tendstoUniformly_of_floer
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
    (hu.comp (contDiff_positiveEndChart q 1).contDiffOn (mapsTo_positiveEndChart q))
    (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one]) hB huB' hc hJc' hJM' hfloer'
    hE'
  refine ⟨fun t ↦ x (q.endSign * t), periodic_comp_endSign_mul hxper,
    hasDerivAt_comp_endSign_mul hx, φ, hφ, ?_⟩
  rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart (u := u) q (φ n)]
  exact hux.comp _

/-- **The actions at the ends of a finite-energy Floer pair of pants.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_endChart_of_floer`, suppose
moreover that `u` is `C²` on `S`. Then at each end `q` there is a `1`-periodic orbit `y` of the
Hamiltonian vector field of `H_q` such that the loops `t ↦ u(φ_q(±s_n, t))` converge uniformly to
`y` along some `s_n → ∞`, and the actions `A_{H_q}(u(φ_q(±s, ·)))` of the end loops tend to the
action `A_{H_q}(y)` as `s → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_endChart_of_floer
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ thricePuncturedSphereReal, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) ∧
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (endChart q (q.endSign * σ n, t))) y atTop) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (q.endSign * s, t))))
        atTop (𝓝 (ω.hamiltonianAction (H q) y)) := by
  obtain ⟨huB', hJc', hJM', hfloer', hE'⟩ :=
    floer_comp_positiveEndChart hKH hH hHs (hu.of_le one_le_two) huB hJc hJM hfloer hE q
  have hper (s : ℝ) : Periodic (fun t ↦ (u ∘ positiveEndChart q) (s, t)) 1 := fun t ↦ by
    simp only [comp_apply, positiveEndChart_add_one]
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder.
  obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer
      (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      (hu.comp (contDiff_positiveEndChart q 2).contDiffOn (mapsTo_positiveEndChart q))
      (fun s _ ↦ hper s) hB huB' hc hJc' hJM' hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), periodic_comp_endSign_mul hxper,
    hasDerivAt_comp_endSign_mul hx, ⟨φ, hφ, ?_⟩, ?_⟩
  · rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart (u := u) q (φ n)]
    exact hux.comp _
  -- Reading the loops with the time `±t` of the end multiplies their actions by `±1`.
  have hAq (y : ℝ → V) (hy : Periodic y 1) :
      ω.hamiltonianAction (H q) (fun t ↦ y (q.endSign * t)) =
        q.endSign * ω.hamiltonianAction (positiveEndHamiltonian H q) y := by
    rw [hamiltonianAction_positiveEndHamiltonian (hH q) hy, ← mul_assoc, endSign_mul_self,
      one_mul]
  have hAs : (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (q.endSign * s, t)))) =
      fun s ↦ q.endSign * ω.hamiltonianAction (positiveEndHamiltonian H q)
        (fun t ↦ (u ∘ positiveEndChart q) (s, t)) :=
    funext fun s ↦ by
      rw [comp_endChart_eq_comp_positiveEndChart q s]
      exact hAq _ (hper s)
  rw [hAs, hAq _ hxper]
  exact hA.const_mul _

/-- **The energy identity with asymptotic orbits.** Let `K` be `C¹` on `S` and equal to
`H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be
`C²` on `S`, with image in a compact set, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`
for uniformly tame almost complex structures, with integrable curvature term `R_K(u)` and finite
energy over `S`. Then there are `1`-periodic orbits `y_q` of the Hamiltonian vector fields of the
`H_q` such that

`E(u) = A_{H_0}(y_0) + A_{H_1}(y_1) - A_{H_∞}(y_∞) - ∫ R_K(u)`.

The orbits are asymptotic orbits of `u` at the ends, as in
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_endChart_of_floer`:
the loops `t ↦ u(φ_q(±s_n, t))` converge uniformly to `y_q` along some `s_n → ∞`, and the actions
`A_{H_q}(u(φ_q(±s, ·)))` tend to `A_{H_q}(y_q)` as `s → ∞`. -/
theorem exists_lintegral_floerEnergyDensity_eq_sum_hamiltonianAction
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ thricePuncturedSphereReal, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y : Puncture → ℝ → V, (∀ q, Periodic (y q) 1 ∧
        (∀ t, HasDerivAt (y q) (ω.hamiltonianVectorField (H q t) (y q t)) t) ∧
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ u (endChart q (q.endSign * σ n, t))) (y q) atTop) ∧
        Tendsto (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (ω.hamiltonianAction (H q) (y q)))) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (∑ q, q.endSign * ω.hamiltonianAction (H q) (y q) -
          ∫ z, ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  choose y hy using fun q ↦
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_endChart_of_floer hKH hH hHs hu hB huB
      hc hJc hJM hfloer hE q
  refine ⟨y, hy, ?_⟩
  exact ω.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm hK hKH hH
    (fun q ↦ (hHs q).continuous) hu
    (fun z hz ↦ ω.floerEnergyDensity_nonneg (fun _ hv ↦ apply_pos_of_tame hc hJc hz hv)
      (hfloer z hz)) hR fun q ↦ (hy q).2.2.2

/-- **The energy identity of the pair-of-pants perturbation with asymptotic orbits.** Let `K` be
the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of `1`-periodic `C¹`
Hamiltonians `H_q`, and let `u` be `C²` on `S`, with image in a compact set, solving the Floer
equation `(du - X_K)^{0,1} = 0` on `S` for uniformly tame almost complex structures, with finite
energy. Then there are `1`-periodic orbits `y_q` of the Hamiltonian vector fields of the `H_q`
such that

`E(u) = A_{H_0}(y_0) + A_{H_1}(y_1) - A_{H_∞}(y_∞) - ∫_S R_K(u)`.

The orbits are asymptotic orbits of `u` at the ends: the loops `t ↦ u(φ_q(±s_n, t))` converge
uniformly to `y_q` along some `s_n → ∞`, and the actions `A_{H_q}(u(φ_q(±s, ·)))` tend to
`A_{H_q}(y_q)` as `s → ∞`. -/
theorem exists_lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ thricePuncturedSphereReal, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤) :
    ∃ y : Puncture → ℝ → V, (∀ q, Periodic (y q) 1 ∧
        (∀ t, HasDerivAt (y q) (ω.hamiltonianVectorField (H q t) (y q t)) t) ∧
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ u (endChart q (q.endSign * σ n, t))) (y q) atTop) ∧
        Tendsto (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (ω.hamiltonianAction (H q) (y q)))) ∧
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
        ENNReal.ofReal (∑ q, q.endSign * ω.hamiltonianAction (H q) (y q) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z)) := by
  choose y hy using fun q ↦
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_endChart_of_floer
      (K := pairOfPantsPerturbation H) (T₀ := 2)
      (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs hu hB huB hc
      hJc hJM hfloer hE q
  refine ⟨y, hy, ?_⟩
  exact lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq ω hH hHs hu
    (fun _ hz _ hv ↦ apply_pos_of_tame hc hJc hz hv) hfloer
    (by simpa only [endChart_mk] using fun q ↦ (hy q).2.2.2)

end SymplecticForm

end TauCeti
