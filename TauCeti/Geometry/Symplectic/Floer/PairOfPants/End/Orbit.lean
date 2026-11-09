/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart

/-!
# Asymptotic orbits at the ends of a finite-energy pair of pants

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
`C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with values in a symplectic vector
space `(V, ω)`, and let `u` be a `C²` solution of the Floer equation `(du - X_K)^{0,1} = 0` on `S`
with finite energy, values in a compact set, and uniformly tame almost complex structures `J(z)`:
`c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖` with `c > 0`. This file shows that every end of
`u` is asymptotic to a `1`-periodic orbit of the Hamiltonian of that end, and rewrites the energy
identity of the pair of pants through the actions of these orbits:

`E(u) = A_{H_0}(x_0) + A_{H_1}(x_1) - A_{H_∞}(x_∞) - ∫_S R_K(u)`.

The two inputs `0`, `1` and the output `∞` enter with the signs `±1` of their ends. These orbits are
the generators of the Floer complexes at the ends of a pair-of-pants solution, and this is the form
of the energy identity which bounds the product coefficients.

The proof reads each end in the *signed end chart* `(s, t) ↦ φ_q(±s ± i t)`
(`TauCeti.Floer.signedEndChart`), the end chart `TauCeti.Floer.endChart` precomposed with
multiplication by the sign of the end. It is holomorphic
(`TauCeti.Floer.isComplexLinearMap_fderiv_signedEndChart`), injective on half-open strips of angular
width one (`TauCeti.Floer.injOn_signedEndChart`), and its longitudinal coordinate tends to `+∞`
towards the puncture on the output end as well as on the inputs. On its half-cylinder `s > 2` the
pair-of-pants datum pulls back to the cylindrical datum `±H_q(±t) dt`, so `u` read in this chart is
a finite-energy Floer half-cylinder, and the asymptotic analysis of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder` applies. On the output end the loops are run
backwards and the Hamiltonian is `t ↦ -H_∞(-t)`; reversing them back negates the action
(`TauCeti.SymplecticForm.hamiltonianAction_comp_neg`).

As in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder`, no nondegeneracy of the orbits is assumed,
so the end loops converge to the orbit along a sequence `R_n → ∞`, while their actions converge as
`R → ∞`.

## Main results

* `SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pairOfPantsPerturbation`:
  at each end `q`, there is a `1`-periodic orbit `x` of `X_{H_q}` such that the end loops converge
  uniformly to `x` along a sequence and their actions converge to `A_{H_q}(x)`.
* `SymplecticForm.exists_periodic_lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`:
  asymptotic orbits at all three ends, and the energy identity in terms of their actions.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology ENNReal

namespace TauCeti

namespace Floer

/-- Precomposing a `1`-periodic function with `t ↦ ±t` keeps it `1`-periodic. -/
private theorem periodic_comp_endSign_mul {α : Type*} {f : ℝ → α} (hf : Periodic f 1)
    (q : Puncture) : Periodic (fun t ↦ f (q.endSign * t)) 1 := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h]
  · simpa using hf
  · simpa using (hf.const_mul (-1)).neg

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- On the part `s ≥ 2` of the signed end chart, the perturbed derivative of a map for the
pulled-back pair-of-pants datum is its perturbed derivative for the cylindrical datum
`±H_q(±t) dt`. -/
private theorem perturbedFDeriv_signedEndChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (v : ℝ × ℝ → V) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w x ↦ q.endSign * H q (q.endSign * w.2) x) v ζ =
      ω.perturbedFDeriv
        (perturbationPullback (signedEndChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (signedEndChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) v ζ := by
  obtain ⟨h₁, hI⟩ := perturbationPullback_signedEndChart hH (q := q) hζ
  refine ContinuousLinearMap.ext fun a ↦ ?_
  simp only [perturbedFDeriv_apply, h₁, hI]

/-- **The ends of a Floer pair of pants are Floer half-cylinders.** On the part `s ≥ 2` of the
signed end chart, a solution of the pair-of-pants Floer equation solves the Floer equation of the
cylindrical datum `±H_q(±t) dt`, with the almost complex structures read along the chart. -/
private theorem isComplexLinearMap_signedEndChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {q : Puncture} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1)
    {J : AlmostComplexStructure V}
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u (signedEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv (fun _ _ ↦ 0)
      (fun w x ↦ q.endSign * H q (q.endSign * w.2) x) (u ∘ signedEndChart q) ζ :
        ℝ × ℝ →ₗ[ℝ] V) := by
  have hS := signedEndChart_mem_thricePuncturedSphereReal (q := q) (by linarith : 0 < ζ.1)
  rw [ω.perturbedFDeriv_signedEndChart hH hζ]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    ((contDiff_signedEndChart q 1).differentiable one_ne_zero ζ)
    ((hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).differentiableAt two_ne_zero)
    (differentiableAt_pairOfPantsPerturbation hH hHs hS _ 1)
    (differentiableAt_pairOfPantsPerturbation hH hHs hS _ Complex.I)
    (isComplexLinearMap_fderiv_signedEndChart q ζ) hfloer

/-- On the part `s ≥ 2` of the signed end chart, the energy density of the end half-cylinder is
the Jacobian of the chart times the energy density of the pair of pants. -/
private theorem floerEnergyDensity_signedEndChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {q : Puncture} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w x ↦ q.endSign * H q (q.endSign * w.2) x)
        (u ∘ signedEndChart q) ζ =
      (fderiv ℝ (signedEndChart q) ζ).det * ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (signedEndChart q ζ) := by
  have hS := signedEndChart_mem_thricePuncturedSphereReal (q := q) (by linarith : 0 < ζ.1)
  rw [floerEnergyDensity_def, ω.perturbedFDeriv_signedEndChart hH hζ, ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_signedEndChart q 1).differentiable one_ne_zero ζ)
    ((hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).differentiableAt two_ne_zero)
    (differentiableAt_pairOfPantsPerturbation hH hHs hS _ 1)
    (differentiableAt_pairOfPantsPerturbation hH hHs hS _ Complex.I)

/-- A finite-energy pair of pants has finite energy on the end half-cylinder `s > 2` of each
signed end chart. -/
private theorem lintegral_floerEnergyDensity_signedEndChart_ne_top (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) (q : Puncture)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∫⁻ ζ in Ioi 2 ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w x ↦ q.endSign * H q (q.endSign * w.2) x) (u ∘ signedEndChart q) ζ) ≠ ⊤ := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
  have hs : MeasurableSet (Ioi (2 : ℝ) ×ˢ Ico (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Ico
  -- The segment `t = 1` of the closed strip is a null set.
  have hnull : volume (Ioi (2 : ℝ) ×ˢ ({1} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  have hsub : Ioi (2 : ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi 2 ×ˢ Ico 0 1 ∪ Ioi 2 ×ˢ {1} := by
    rintro ⟨s, t⟩ ⟨hs, ht₀, ht₁⟩
    rcases ht₁.lt_or_eq with ht | ht
    · exact Or.inl ⟨hs, ht₀, ht⟩
    · exact Or.inr ⟨hs, ht⟩
  -- On the half-open strip, change variables along the injective signed end chart.
  have hchange : ∫⁻ ζ in Ioi 2 ×ˢ Ico 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w x ↦ q.endSign * H q (q.endSign * w.2) x) (u ∘ signedEndChart q) ζ) =
        ∫⁻ z in signedEndChart q '' (Ioi 2 ×ˢ Ico 0 1), ENNReal.ofReal (e z) := by
    -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
    have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
      (fun ζ _ ↦ ((contDiff_signedEndChart q 1).differentiable one_ne_zero ζ).hasFDerivAt
        |>.hasFDerivWithinAt)
      ((injOn_signedEndChart q 0).mono (prod_mono (subset_univ _) (by norm_num)))]
    refine setLIntegral_congr_fun hs fun ζ hζ ↦ ?_
    rw [ω.floerEnergyDensity_signedEndChart hH hHs hu hζ.1.le,
      abs_of_nonneg (det_fderiv_signedEndChart_nonneg q ζ),
      ENNReal.ofReal_mul (det_fderiv_signedEndChart_nonneg q ζ)]
  have himage : signedEndChart q '' (Ioi 2 ×ˢ Ico 0 1) ⊆ thricePuncturedSphereReal := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact signedEndChart_mem_thricePuncturedSphereReal (lt_trans two_pos hζ.1)
  refine ne_top_of_le_ne_top hE ?_
  calc _ ≤ ∫⁻ ζ in Ioi 2 ×ˢ Ico 0 1 ∪ Ioi 2 ×ˢ {1}, ENNReal.ofReal
          (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w x ↦ q.endSign * H q (q.endSign * w.2) x)
            (u ∘ signedEndChart q) ζ) := lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ = ∫⁻ z in signedEndChart q '' (Ioi 2 ×ˢ Ico 0 1), ENNReal.ofReal (e z) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero, hchange]
    _ ≤ _ := lintegral_mono_set himage

omit [FiniteDimensional ℝ V] in
/-- The action of the loops of an end read in the signed end chart: replacing `H` by `±H(±t)` and
the loop `x` by `t ↦ x(±t)` multiplies the action by the sign of the end. -/
private theorem hamiltonianAction_endSign (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : Periodic H 1) {x : ℝ → V} (hx : Periodic x 1) (q : Puncture) :
    ω.hamiltonianAction (fun t y ↦ q.endSign * H (q.endSign * t) y) (fun t ↦ x (q.endSign * t)) =
      q.endSign * ω.hamiltonianAction H x := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h <;> simp only [h, one_mul, neg_one_mul]
  exact ω.hamiltonianAction_comp_neg hH hx

/-- **The ends of a finite-energy pair of pants, read in the signed end chart.** Under the
hypotheses of
`SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pairOfPantsPerturbation`, the
map `u` read in the signed end chart is a finite-energy Floer half-cylinder `s > 2` for the datum
`±H_q(±t) dt`, so it has an asymptotic orbit of that datum, with converging actions. -/
private theorem exists_periodic_signedEndChart
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {C : Set V} (hC : IsCompact C) {q : Puncture}
    (huK : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 → u (endChart q ζ) ∈ C) {c M : ℝ} (hc : 0 < c)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJc : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (endChart q ζ) v))
    (hJM : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 → ∀ v, ‖J (endChart q ζ) v‖ ≤ M * ‖v‖)
    (hfloer : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (endChart q ζ)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ y : ℝ → V, Periodic y 1 ∧
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField
        (fun x ↦ q.endSign * H q (q.endSign * t) x) (y t)) t) ∧
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (signedEndChart q (φ n, t))) y atTop) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction (fun t x ↦ q.endSign * H q (q.endSign * t) x)
          (fun t ↦ u (signedEndChart q (s, t)))) atTop
        (𝓝 (ω.hamiltonianAction (fun t x ↦ q.endSign * H q (q.endSign * t) x) y)) := by
  -- Points `ζ` of the half-cylinder `s > 2` of the signed end chart lie on the part `±s > 2`.
  have hend {ζ : ℝ × ℝ} (hζ : 2 < ζ.1) : 2 < q.endSign * (q.endSign • ζ).1 := by
    simpa using hζ
  have hH' : ContDiff ℝ 1 (uncurry fun t x ↦ q.endSign * H q (q.endSign * t) x) :=
    contDiff_const.mul ((hHs q).comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))
  have hH'per : Periodic (fun t x ↦ q.endSign * H q (q.endSign * t) x) 1 := fun t ↦ by
    simp only [periodic_comp_endSign_mul (hH q) q t]
  have hv : ContDiffOn ℝ 2 (u ∘ signedEndChart q) (Ioi 2 ×ˢ univ) :=
    hu.comp (contDiff_signedEndChart q 2).contDiffOn fun ζ hζ ↦
      signedEndChart_mem_thricePuncturedSphereReal (lt_trans two_pos hζ.1)
  have hper (s : ℝ) : Periodic (fun t ↦ u (signedEndChart q (s, t))) 1 := by
    simpa only [signedEndChart_mk, endChart_mk] using
      periodic_comp_endSign_mul (periodic_endLoop u q (q.endSign * s)) q
  obtain ⟨y, hyper, hy, ⟨φ, -, hφ, hφy⟩, hA⟩ :=
    ω.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (J := fun ζ ↦
      J (signedEndChart q ζ)) hH' hH'per hv (fun s _ ↦ hper s) hC
      (fun s hs t ↦ by
        rw [comp_apply, signedEndChart_apply]
        exact huK _ (hend (ζ := (s, t)) hs)) hc
      (fun ζ hζ v ↦ signedEndChart_apply q ζ ▸ hJc _ (hend hζ.1) v)
      (fun ζ hζ v ↦ signedEndChart_apply q ζ ▸ hJM _ (hend hζ.1) v)
      (fun ζ hζ ↦ ω.isComplexLinearMap_signedEndChart hH hHs hu hζ.1.le
        (signedEndChart_apply q ζ ▸ hfloer _ (hend hζ.1)))
      (ω.lintegral_floerEnergyDensity_signedEndChart_ne_top hH hHs hu q hE)
  exact ⟨y, hyper, hy, ⟨φ, hφ, hφy⟩, hA⟩

/-- **Asymptotic orbits at an end of a finite-energy pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the ends of `S = ℂ ∖ {0, 1}`, and let `u`
be a map which is `C²` on `S`, has finite energy, and on the part `±s > 2` of the end `q` takes
values in a compact set and solves the Floer equation `(du - X_K)^{0,1} = 0` for uniformly tame
almost complex structures `J(z)`: `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, with `c > 0`.
Then there is a `1`-periodic orbit `x` of the Hamiltonian vector field of `H_q`,
`x'(t) = X_{H_q(t)}(x(t))`, such that the end loops `ℓ_q(R)(t) = u(φ_q(±R + i t))` converge
uniformly to `x` along some sequence `R_n → ∞`, and their actions `A_{H_q}(ℓ_q(R))` tend to the
action `A_{H_q}(x)` as `R → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pairOfPantsPerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {C : Set V} (hC : IsCompact C) {q : Puncture}
    (huK : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 → u (endChart q ζ) ∈ C) {c M : ℝ} (hc : 0 < c)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJc : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (endChart q ζ) v))
    (hJM : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 → ∀ v, ‖J (endChart q ζ) v‖ ≤ M * ‖v‖)
    (hfloer : ∀ ζ : ℝ × ℝ, 2 < q.endSign * ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (endChart q ζ)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H q t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction (H q) x)) := by
  -- The loops of the signed end chart are the end loops, run backwards on the output end.
  have hℓ (R t : ℝ) : u (signedEndChart q (R, t)) = u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑(q.endSign * t) * Complex.I))) := by
    rw [signedEndChart_mk, endChart_mk]
  obtain ⟨y, hyper, hy, ⟨φ, hφ, hφy⟩, hA⟩ :=
    ω.exists_periodic_signedEndChart hH hHs hu hC huK hc hJc hJM hfloer hE
  refine ⟨fun t ↦ y (q.endSign * t), periodic_comp_endSign_mul hyper q, fun t ↦ ?_,
    ⟨φ, hφ, ?_⟩, ?_⟩
  · -- The orbit of `±H_q(±t)` read backwards on the output end is an orbit of `H_q`.
    have h := (hy (q.endSign * t)).scomp t ((hasDerivAt_id t).const_mul q.endSign)
    simp only [hamiltonianVectorField_const_mul, endSign_mul_endSign_mul, smul_smul, mul_one,
      endSign_mul_self, one_smul] at h
    exact h
  · have hfun : (fun n (t : ℝ) ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * φ n) + ↑t * Complex.I)))) =
        fun n ↦ (fun t ↦ u (signedEndChart q (φ n, t))) ∘ fun t ↦ q.endSign * t := by
      funext n t
      simp only [comp_apply, hℓ, endSign_mul_endSign_mul]
    rw [hfun]
    exact hφy.comp _
  · -- Both actions are multiplied by the sign of the end in the signed end chart.
    have hy' : y = fun t ↦ y (q.endSign * (q.endSign * t)) := by
      simp only [endSign_mul_endSign_mul]
    rw [hy', hamiltonianAction_endSign ω (hH q) (periodic_comp_endSign_mul hyper q)] at hA
    have h := hA.const_mul q.endSign
    rw [← mul_assoc, endSign_mul_self, one_mul] at h
    refine h.congr fun R ↦ ?_
    have hR := hamiltonianAction_endSign ω (hH q) (periodic_endLoop u q (q.endSign * R)) q
    simp only [← hℓ] at hR
    rw [hR, ← mul_assoc, endSign_mul_self, one_mul]

/-- **The energy of a pair of pants in terms of its asymptotic orbits.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on the ends of
`S = ℂ ∖ {0, 1}`, and let `u` be a finite-energy map which is `C²` on `S`, takes values in a
compact set, and solves the Floer equation `(du - X_K)^{0,1} = 0` for uniformly tame almost
complex structures `J(z)`. Then at every end `q` there is a `1`-periodic orbit `x_q` of the
Hamiltonian vector field of `H_q` to which the end loops `ℓ_q(R)(t) = u(φ_q(±R + i t))` converge
uniformly along some sequence `R_n → ∞`, and the energy of `u` is

`E(u) = A_{H_0}(x_0) + A_{H_1}(x_1) - A_{H_∞}(x_∞) - ∫_S R_K(u)`. -/
theorem exists_periodic_lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {C : Set V} (hC : IsCompact C) (huK : ∀ z ∈ thricePuncturedSphereReal, u z ∈ C) {c M : ℝ}
    (hc : 0 < c) {J : ℝ × ℝ → AlmostComplexStructure V}
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
    ∃ x : Puncture → ℝ → V, (∀ q, Periodic (x q) 1 ∧
        (∀ t, HasDerivAt (x q) (ω.hamiltonianVectorField (H q t) (x q t)) t) ∧
        ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
          TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R n) + ↑t * Complex.I)))) (x q) atTop) ∧
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
        ENNReal.ofReal ((∑ q, q.endSign * ω.hamiltonianAction (H q) (x q)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z)) := by
  -- Every point of the part `±s > 2` of an end lies in `S`.
  have hS {q : Puncture} {ζ : ℝ × ℝ} (hζ : 2 < q.endSign * ζ.1) :
      endChart q ζ ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by linarith)
  choose x hx using fun q ↦
    ω.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pairOfPantsPerturbation hH hHs hu hC
      (q := q) (fun _ hζ ↦ huK _ (hS hζ)) hc (fun _ hζ ↦ hJc _ (hS hζ))
      (fun _ hζ ↦ hJM _ (hS hζ)) (fun _ hζ ↦ hfloer _ (hS hζ)) hE
  have hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  exact ⟨x, fun q ↦ ⟨(hx q).1, (hx q).2.1, (hx q).2.2.1⟩,
    ω.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq hH hHs hu hJ hfloer
      fun q ↦ (hx q).2.2.2⟩

end SymplecticForm

end TauCeti
