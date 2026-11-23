/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.PeriodicOrbit
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation

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
over `S` (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`).
Its energy over any measurable part `s` of a band `(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width
one is the energy of `u` over `φ'_q(s)`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_eq_of_subset`),
so it is at most the energy of `u` over `S`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset`).
The same holds for the translated ends `z ↦ u(φ'_q(z + (R, 0)))` at every height `R`: they solve
the Floer equation of the half-cylinder where `z.1 + R > max T₀ 0`
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add`), and
their energy over a set `s` whose translate lies in such a band is the energy of `u` over the
image of `s` under `z ↦ φ'_q(z + (R, 0))`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq`), so it is
at most the energy of `u` over `S`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le`).
If the almost complex structure is cylindrical on the end, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`,
then in the positive end chart it is `J'_q(t, x) = J_q(±t, x)`
(`TauCeti.Floer.eq_comp_positiveEndChart`,
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_of_cylindrical`),
and `u ∘ φ'_q` is a finite-energy Floer half-cylinder for `H'_q` and `J'_q`
(`TauCeti.SymplecticForm.floer_comp_positiveEndChart_of_cylindrical`). So the results of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` about finite-energy Floer half-cylinders
apply at each end of the pair of pants.

**Orbits at the ends.** Reversing the time of an orbit of `H'_∞` gives an orbit of `H_∞`
(`TauCeti.SymplecticForm.hasDerivAt_comp_endSign_mul`, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.PeriodicOrbit`), and reversing the time of a
loop negates its action for the reversed Hamiltonian
(`TauCeti.SymplecticForm.hamiltonianAction_positiveEndHamiltonian`, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action`). Read back in the end chart `φ_q`, this
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
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`. The orbits at the ends of a
pair of pants with values in a manifold are obtained in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold`. The statements about positive end
charts here are the case of a constant form of those in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback`.

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

/-! ### The ends of a Floer pair of pants as Floer half-cylinders -/

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
  -- This is the manifold statement for the constant form.
  rw [← toLinearMap_perturbedMFDeriv_constSmooth] at hfloer ⊢
  exact SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (ω := ω.constSmooth) (hKH q) (hH q) (fun t ↦ (hHd q t).mdifferentiable) hζ
    hu.mdifferentiableAt hfloer

/-- **A cylindrical end of a Floer pair of pants is a Floer half-cylinder.** Let `K` be equal to
`H_q(t) dt` beyond `T₀` on each end `q`, and let `u` be differentiable on `S` and solve the Floer
equation `(du - X_K)^{0,1} = 0` there. Suppose that on the end `q` beyond `T₀` the almost complex
structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`. Then at every point `ζ` of the
positive end chart `φ'_q` with `s > max T₀ 0`, the map `u ∘ φ'_q` solves the Floer equation
`∂_s v + J'_q(t, v) (∂_t v - X_{H'_q(t)}(v)) = 0` of a half-cylinder, for the end Hamiltonian
`H'_q` and the structure `J'_q(t, x) = J_q(±t, x)` of the positive end. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_of_cylindrical
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {q : Puncture} {Jq : ℝ → V → AlmostComplexStructure V}
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {ζ : ℝ × ℝ} (hζ : max T₀ 0 < ζ.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (Jq (q.endSign * ζ.2) ((u ∘ positiveEndChart q) ζ))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ : ℝ × ℝ →ₗ[ℝ] V) := by
  have hmem : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hζ)
  rw [← eq_comp_positiveEndChart hJ ((le_max_left _ _).trans hζ.le)]
  exact isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart hKH hH hHd
    ((le_max_left _ _).trans hζ.le)
    ((hu _ hmem).differentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hmem))
    (hfloer _ hmem)

/-- **The energy of a part of an end of a Floer pair of pants is the energy of its image.** Under
the hypotheses of
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart`, the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over a measurable subset `s` of a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width one is the energy of `u` over `φ'_q(s)`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_eq_of_subset
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) (q : Puncture) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) {t₀ : ℝ} (hst : s ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) =
      ∫⁻ z in positiveEndChart q '' s, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- This is the manifold statement for the constant form.
  simpa only [floerEnergyDensity_constSmooth] using
    SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_eq_of_subset
      (ω := ω.constSmooth) q (hKH q) (hH q) (fun t ↦ (hHd q t).mdifferentiable)
      hu.mdifferentiableOn hs hst

/-- **The energy of a part of an end of a Floer pair of pants.** Under the hypotheses of
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart`, the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over a measurable subset `s` of a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width one is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) (q : Puncture) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) {t₀ : ℝ} (hst : s ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- This is the manifold statement for the constant form.
  simpa only [floerEnergyDensity_constSmooth] using
    SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset
      (ω := ω.constSmooth) q (hKH q) (hH q) (fun t ↦ (hHd q t).mdifferentiable)
      hu.mdifferentiableOn hs hst

/-- **The translated ends of a Floer pair of pants solve one cylindrical Floer equation.** Let
`K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` be differentiable on `S` and
solve the Floer equation `(du - X_K)^{0,1} = 0` there, for a structure `J` which on the end `q`
beyond `T₀` is `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`. Then for every height `R`, the translated
end `v(z) = u(φ'_q(z + (R, 0)))` solves `∂_s v + J'_q(t, v) (∂_t v - X_{H'_q(t)}(v)) = 0` at every
point `z` with `max T₀ 0 < z.1 + R`, for the datum `H'_q` and the structure
`J'_q(t, x) = J_q(±t, x)` of the positive end, which do not depend on `R`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {q : Puncture} {Jq : ℝ → V → AlmostComplexStructure V}
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    (R : ℝ) {z : ℝ × ℝ} (hz : max T₀ 0 < z.1 + R) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (Jq (q.endSign * z.2) (u (positiveEndChart q (z + (R, 0)))))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z : ℝ × ℝ →ₗ[ℝ] V) := by
  -- This is the manifold statement for the constant form.
  have hz' : max T₀ 0 < (z + (R, 0)).1 := by simpa using hz
  have hmem : positiveEndChart q (z + (R, 0)) ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz')
  have hJz := eq_comp_positiveEndChart hJ ((le_max_left _ _).trans hz'.le)
  simp only [Prod.snd_add, add_zero, comp_apply] at hJz
  rw [← hJz, ← toLinearMap_perturbedMFDeriv_constSmooth]
  exact SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_add
    (ω := ω.constSmooth) (hKH q) (hH q) (fun t ↦ (hHd q t).mdifferentiable) R
    ((le_max_left _ _).trans hz'.le)
    ((hu _ hmem).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds hmem)).mdifferentiableAt
    (by rw [toLinearMap_perturbedMFDeriv_constSmooth]; exact hfloer _ hmem)

/-- **The energy of a translated end of a Floer pair of pants is the energy of its image.** Under
the hypotheses of
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart`, let `R` be a
height and `s` a measurable set whose translate `s + (R, 0)` lies in a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width one. Then the energy of the translated end
`z ↦ u(φ'_q(z + (R, 0)))` for the end Hamiltonian `H'_q` over `s` is the energy of `u` over the
image of `s` under `z ↦ φ'_q(z + (R, 0))`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) (q : Puncture) (R : ℝ)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {t₀ : ℝ}
    (hst : ∀ z ∈ s, z + (R, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z) =
      ∫⁻ z in (fun z ↦ positiveEndChart q (z + (R, 0))) '' s, ENNReal.ofReal
        (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  have h := ω.constSmooth.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) (R, 0)
    ((· + ((R, 0) : ℝ × ℝ)) '' s)
  rw [preimage_image_eq _ (add_left_injective _)] at h
  simp only [floerEnergyDensity_constSmooth, Prod.snd_add, add_zero, comp_apply] at h
  rw [h, setLIntegral_floerEnergyDensity_comp_positiveEndChart_eq_of_subset hKH hH hHd hu q
    ((measurableEmbedding_addRight _).measurableSet_image' hs)
    (by rintro _ ⟨z, hz, rfl⟩; exact hst z hz), image_image]

/-- **The energy of a translated end of a Floer pair of pants.** Under the hypotheses of
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart`, let `R` be a
height and `s` a measurable set whose translate `s + (R, 0)` lies in a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width one. Then the energy of the translated end
`z ↦ u(φ'_q(z + (R, 0)))` for the end Hamiltonian `H'_q` over `s` is at most the energy of `u`
over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) (q : Puncture) (R : ℝ)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {t₀ : ℝ}
    (hst : ∀ z ∈ s, z + (R, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- This is the manifold statement for the constant form.
  simpa only [floerEnergyDensity_constSmooth] using
    SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le
      (ω := ω.constSmooth) q (hKH q) (hH q) (fun t ↦ (hHd q t).mdifferentiable)
      hu.mdifferentiableOn R hs hst

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
  -- This is the manifold statement for the constant form.
  simpa only [floerEnergyDensity_constSmooth] using
    SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le (ω := ω.constSmooth)
      q (hKH q) (hH q) (fun t ↦ (hHd q t).mdifferentiable) hu.mdifferentiableOn ha₀ haT

/-- **A cylindrical end of a finite-energy Floer pair of pants is a finite-energy Floer
half-cylinder.** Let `K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` be `Cⁿ`
on `S` for some `n ≠ 0`, with image in `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on
`S` with finite energy. Suppose that on the end `q` beyond `T₀` the almost complex structure is
cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a `1`-periodic family `J_q(t, x)` which
is `Cᵐ` on an open set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`. Then:

* the structure `J'_q(t, x) = J_q(±t, x)` of the positive end is `Cᵐ` on the open set
  `{(t, x) | (±t, x) ∈ W} ⊇ ℝ × B`, `1`-periodic and tamed by `ω` on `ℝ × B`;
* on the half-cylinder `s > max T₀ 0` of the positive end chart, `u ∘ φ'_q` is `Cⁿ`, has
  `1`-periodic loops with image in `B`, solves the Floer equation for the end Hamiltonian `H'_q`
  and `J'_q`, and has finite energy.

These are the hypotheses on `J'_q` and `u ∘ φ'_q` of the results about finite-energy Floer
half-cylinders, such as `TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`. -/
theorem floer_comp_positiveEndChart_of_cylindrical
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t)) {u : ℝ × ℝ → V}
    {n : WithTop ℕ∞} (hu : ContDiffOn ℝ n u thricePuncturedSphereReal) (hn : n ≠ 0) {B : Set V}
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {q : Puncture} {W : Set (ℝ × V)} (hW : IsOpen W) {Jq : ℝ → V → AlmostComplexStructure V}
    {m : WithTop ℕ∞}
    (hJq : ContDiffOn ℝ m (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hBW : univ ×ˢ B ⊆ W) (hJqt : ∀ t, ∀ x ∈ B, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t)))) :
    IsOpen ((fun p : ℝ × V ↦ (q.endSign * p.1, p.2)) ⁻¹' W) ∧
      ContDiffOn ℝ m
        (fun p : ℝ × V ↦ (Jq (q.endSign * p.1) p.2).toLinearMap.toContinuousLinearMap)
        ((fun p : ℝ × V ↦ (q.endSign * p.1, p.2)) ⁻¹' W) ∧
      Periodic (fun t ↦ Jq (q.endSign * t)) 1 ∧
      univ ×ˢ B ⊆ (fun p : ℝ × V ↦ (q.endSign * p.1, p.2)) ⁻¹' W ∧
      (∀ t, ∀ x ∈ B, ω.Tames (Jq (q.endSign * t) x)) ∧
      ContDiffOn ℝ n (u ∘ positiveEndChart q) (Ioi (max T₀ 0) ×ˢ univ) ∧
      (∀ s, max T₀ 0 < s → Periodic (fun t ↦ (u ∘ positiveEndChart q) (s, t)) 1) ∧
      (∀ s, max T₀ 0 < s → ∀ t, (u ∘ positiveEndChart q) (s, t) ∈ B) ∧
      (∀ z ∈ Ioi (max T₀ 0) ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (q.endSign * z.2) ((u ∘ positiveEndChart q) z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (u ∘ positiveEndChart q) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi (max T₀ 0) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≠ ⊤ := by
  have hmem (z : ℝ × ℝ) (hz : max T₀ 0 < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
  -- In the positive end chart the structure is `J'(t, x) = J_q(±t, x)`.
  set g : ℝ × V → ℝ × V := fun p ↦ (q.endSign * p.1, p.2)
  have hg : ContDiff ℝ m g := (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  exact ⟨hW.preimage hg.continuous, hJq.comp hg.contDiffOn (mapsTo_preimage g W),
    periodic_comp_endSign_mul hJqper, fun p hp ↦ hBW ⟨mem_univ _, hp.2⟩, fun t ↦ hJqt _,
    hu.comp (contDiff_positiveEndChart q n).contDiffOn fun z hz ↦ hmem z hz.1,
    fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one],
    fun s hs t ↦ huB _ (hmem (s, t) hs),
    fun z hz ↦ isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_of_cylindrical hKH hH hHd
      (hu.differentiableOn hn) hfloer hJ hz.1,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      (hu.differentiableOn hn) q (le_max_right _ _) (le_max_left _ _))⟩

/-! ### Asymptotic orbits at the ends -/

variable {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {c M : ℝ}

/-- The positive end chart maps the half-cylinder `(max T₀ 0, ∞) × ℝ` into `S`. -/
private theorem mapsTo_positiveEndChart (q : Puncture) :
    MapsTo (positiveEndChart q) (Ioi (max T₀ 0) ×ˢ univ) thricePuncturedSphereReal :=
  fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz.1)

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
  rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart u q (φ n)]
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
  · rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart u q (φ n)]
    exact hux.comp _
  -- Reading the loops with the time `±t` of the end multiplies their actions by `±1`.
  have hAq (y : ℝ → V) (hy : Periodic y 1) :
      ω.hamiltonianAction (H q) (fun t ↦ y (q.endSign * t)) =
        q.endSign * ω.hamiltonianAction (positiveEndHamiltonian H q) y := by
    rw [ω.hamiltonianAction_positiveEndHamiltonian (hH q) hy, ← mul_assoc, endSign_mul_self,
      one_mul]
  have hAs : (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (q.endSign * s, t)))) =
      fun s ↦ q.endSign * ω.hamiltonianAction (positiveEndHamiltonian H q)
        (fun t ↦ (u ∘ positiveEndChart q) (s, t)) :=
    funext fun s ↦ by
      rw [comp_endChart_eq_comp_positiveEndChart u q s]
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
    (fun z hz ↦ ω.floerEnergyDensity_nonneg (tames_of_mul_norm_sq_le hc (hJc z hz))
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
    (fun z hz ↦ tames_of_mul_norm_sq_le hc (hJc z hz)) hfloer
    (by simpa only [endChart_mk] using fun q ↦ (hy q).2.2.2)

end SymplecticForm

end TauCeti
