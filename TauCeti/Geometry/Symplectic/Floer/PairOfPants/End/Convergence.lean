/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit
import TauCeti.Dynamics.Flow.Periodic.Basic

/-!
# Convergence of the ends of a Floer pair of pants to nondegenerate orbits

Let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in a
symplectic vector space `(V, ω)`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q`,
and let `u` be a finite-energy solution of the Floer equation `(du - X_K)^{0,1} = 0` on `S` with
image in a compact set `B`. By `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit`, the end
loops `t ↦ u(φ_q(±s, t))` converge to a one-periodic orbit of `H_q` along some sequence `s_n → ∞`.
This file shows that they converge as `s → ∞`, uniformly in `t`, to a single orbit when every
one-periodic orbit of `H_q` in `B` is nondegenerate. This is the asymptotic condition
`u(φ_q(±s, ·)) → y_q` under which the pairs of pants with ends at the orbits `y_q` are counted in
the pair-of-pants product.

**Convergence at nondegenerate ends.** Let `φ'_q` be the positive end chart
`TauCeti.Floer.positiveEndChart`, in which `s → ∞` along every end. Suppose that the derivative of
`u ∘ φ'_q` is bounded and the almost complex structures are uniformly tame on some half-cylinder
`s > b`, and that every one-periodic orbit `y` of `H_q` in `B` is nondegenerate, that is, `y(0)` is
a nondegenerate fixed point of the time-one map of the evolution of `H_q`. Then the loops
`t ↦ u(φ_q(±s, t))` converge uniformly to a single one-periodic orbit of `H_q` as `s → ∞`
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer`).
In the positive end chart the end is a finite-energy Floer half-cylinder for the Hamiltonian
`H'_q(t, x) = ±H_q(±t, x)`. On the output end the orbits of `H'_∞` are the orbits of `H_∞` run
backwards in time. Time reversal preserves isolation among periodic orbits, and isolation is what
the convergence theorem `TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop` for loops with
square-integrable defect uses.

**Cylindrical ends.** Suppose that on the end `q` beyond `T₀` the almost complex structure is
cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a `C²` period-one family `J_q(t, x)`
tamed by `ω` on `B`, and that `H_q` and `u` are `C³`. Then `u ∘ φ'_q` has bounded derivative on
every half-cylinder `s ≥ b` with `b > max T₀ 0`
(`TauCeti.SymplecticForm.exists_forall_norm_fderiv_comp_positiveEndChart_le`): in the positive end
chart the structure is `J'_q(t, x) = J_q(±t, x)`, and bubbling cannot occur along a finite-energy
cylindrical end (`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`). The structures
are then also uniformly tame on the end, so neither a derivative bound nor taming constants have
to be assumed for the convergence
(`exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer_of_cylindrical`).

**The energy identity.** Consequently the orbits in the energy identity

`E(u) = A_{H_0}(y_0) + A_{H_1}(y_1) - A_{H_∞}(y_∞) - ∫_S R_K(u)`

of `TauCeti.SymplecticForm.exists_lintegral_floerEnergyDensity_eq_sum_hamiltonianAction` are the
limits of the ends of `u`, not merely limits along sequences
(`exists_lintegral_floerEnergyDensity_eq_sum_hamiltonianAction_of_isNondegenerateFixedPt`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {c M : ℝ}

/-- An orbit of the positive end Hamiltonian `H'_q` which, read with the time `±t` of the end,
starts at a nondegenerate fixed point of the time-one map of `H_q`, is isolated among the
`1`-periodic orbits of `H'_q`. -/
private theorem exists_pos_forall_eq_of_isNondegenerateFixedPt {q : Puncture} {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q))) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (x 0)) :
    ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (y t)) t) →
      dist (y 0) (x 0) < ε → y = x := by
  have hiso := hnd.eventually_not_isFixedPt
  rw [timeDependentHamiltonianFlow_eq, ← zero_add (1 : ℝ)] at hiso
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_periodic_eq_of_eventually_not_isFixedPt _
    (hasDerivAt_comp_endSign_mul hx) (s := 0) (by simpa only [mul_zero] using hiso)
  refine ⟨ε, hε, fun y hyper hy hyx ↦ funext fun t ↦ ?_⟩
  have hxy := congrFun (h _ (hasDerivAt_comp_endSign_mul hy) (periodic_comp_endSign_mul hyper)
    (by simpa only [mul_zero] using hyx)) (q.endSign * t)
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using hxy

/-- **The ends of a Floer pair of pants converge to nondegenerate orbits.** Let `K` be equal to
`H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be
`C¹` on `S`, with image in a compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on
`S` with finite energy. Fix an end `q`, and suppose that on some half-cylinder `s > b` of the
positive end chart `φ'_q` the derivative of `u ∘ φ'_q` is bounded and the almost complex structures
are uniformly tame, `c ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖`. Suppose moreover that the suspension
of the Hamiltonian vector field of `H_q` is globally Lipschitz, so that its evolution is defined,
and that every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate: `y(0)` is a nondegenerate
fixed point of the time-one map. Then the loops `t ↦ u(φ_q(±s, t))` converge uniformly, as
`s → ∞`, to a single `1`-periodic orbit of `H_q`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positiveEndChart q z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positiveEndChart q z) v‖ ≤ M * ‖v‖) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) ∧
      TendstoUniformly (fun s t ↦ u (endChart q (q.endSign * s, t))) y atTop := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  have hHd : ∀ q t, Differentiable ℝ (H q t) := fun q t ↦
    ((hHs q).differentiable one_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  set H' := positiveEndHamiltonian H q
  have hH' : ContDiff ℝ 1 (uncurry H') := contDiff_uncurry_positiveEndHamiltonian (hHs q)
  have hH'per : Periodic H' 1 := periodic_positiveEndHamiltonian (hH q)
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder for `H'_q`.
  have hfloer' (z : ℝ × ℝ) (hz : z ∈ Ioi a ×ˢ Icc 0 1) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) ((J ∘ positiveEndChart q) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H' w.2) (u ∘ positiveEndChart q) z :
          ℝ × ℝ →ₗ[ℝ] V) :=
    isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart hKH hH hHd (haT.trans hz.1.le)
      (((hu.differentiableOn one_ne_zero) _ (hmem z hz.1)).differentiableAt
        (isOpen_thricePuncturedSphereReal.mem_nhds (hmem z hz.1)))
      (hfloer _ (hmem z hz.1))
  have hfin := lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc
    (fun z hz v ↦ hJc z (hab z hz.1) v) (fun z hz v ↦ hJM z (hab z hz.1) v) hfloer'
    (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      (hu.differentiableOn one_ne_zero) q ha₀ haT))
  obtain ⟨x, hxper, hx, hux⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop
    (hu.comp (contDiff_positiveEndChart q 1).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one]) hB
    (fun s hs t ↦ huB _ (hmem (s, t) hs))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH')).continuous
    (fun v t ↦ by simp only [hH'per t]) hfin (fun z hz ↦ hC z (hab z hz.1))
    fun x hxper hx hxB ↦ by
      -- Isolation of the orbits of `H'_q` comes from nondegeneracy of the orbits of `H_q`.
      have hnd₀ := hnd _ (periodic_comp_endSign_mul hxper) (hasDerivAt_comp_endSign_mul hx)
        fun t ↦ hxB _
      rw [mul_zero] at hnd₀
      obtain ⟨ε, hε, h⟩ := exists_pos_forall_eq_of_isNondegenerateFixedPt hL hx hnd₀
      exact ⟨ε, hε, fun y hyper hy _ hyx ↦ h y hyper hy (hyx 0)⟩
  refine ⟨fun t ↦ x (q.endSign * t), periodic_comp_endSign_mul hxper,
    hasDerivAt_comp_endSign_mul hx, ?_⟩
  -- The end loop at the height `±s` is the loop of `u ∘ φ'_q` at the height `s`, read with the
  -- time `±t` of the end.
  have hloop (s : ℝ) : (fun t ↦ u (endChart q (q.endSign * s, t))) =
      (fun t ↦ (u ∘ positiveEndChart q) (s, t)) ∘ fun t ↦ q.endSign * t := by
    funext t
    simp only [comp_apply, endChart_eq_positiveEndChart]
  rw [funext hloop]
  exact hux.comp _

/-- **The energy identity with the limits of the ends.** Let `K` be `C¹` on `S` and equal to
`H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q` whose suspended
Hamiltonian vector fields are globally Lipschitz and whose `1`-periodic orbits in a compact set
`B` are nondegenerate. Let `u` be `C²` on `S`, with image in `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` on `S` for uniformly tame almost complex structures, with integrable
curvature term `R_K(u)` and finite energy over `S`, and suppose that on each end the derivative
of `u ∘ φ'_q` is bounded on some half-cylinder. Then the end loops `t ↦ u(φ_q(±s, t))` converge
uniformly, as `s → ∞`, to `1`-periodic orbits `y_q` of the `H_q`, their actions converge to the
actions of the `y_q`, and

`E(u) = A_{H_0}(y_0) + A_{H_1}(y_1) - A_{H_∞}(y_∞) - ∫ R_K(u)`. -/
theorem exists_lintegral_floerEnergyDensity_eq_sum_hamiltonianAction_of_isNondegenerateFixedPt
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : Puncture → ℝ≥0}
    (hL : ∀ q, LipschitzWith (L q) (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ q (y : ℝ → V), Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) (hL q) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → V, (∀ q, Periodic (y q) 1 ∧
        (∀ t, HasDerivAt (y q) (ω.hamiltonianVectorField (H q t) (y q t)) t) ∧
        TendstoUniformly (fun s t ↦ u (endChart q (q.endSign * s, t))) (y q) atTop ∧
        Tendsto (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (ω.hamiltonianAction (H q) (y q)))) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (∑ q, q.endSign * ω.hamiltonianAction (H q) (y q) -
          ∫ z, ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨y, hy, hEy⟩ := exists_lintegral_floerEnergyDensity_eq_sum_hamiltonianAction hK hKH hH
    hHs hu hB huB hc hJc hJM hfloer hR hE
  refine ⟨y, fun q ↦ ?_, hEy⟩
  obtain ⟨hyper, hyX, ⟨σ, hσ, hσy⟩, hA⟩ := hy q
  obtain ⟨b, C, hbC⟩ := hC q
  -- On the half-cylinder `s > max b 0` the positive end chart stays in `S`.
  have hmem (z : ℝ × ℝ) (hz : max b 0 < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
  obtain ⟨y', -, -, hy'⟩ := exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer hKH
    hH hHs (hu.of_le one_le_two) hB huB hfloer hE q (hL q) (hnd q)
    (fun z hz ↦ hbC z ((le_max_left _ _).trans_lt hz)) hc
    (fun z hz v ↦ hJc _ (hmem z hz) v) fun z hz v ↦ hJM _ (hmem z hz) v
  -- The limit along the whole end is also the limit along the sequence `σ`.
  have hyy' : y q = y' := funext fun t ↦
    tendsto_nhds_unique (hσy.tendsto_at t) ((hy'.tendsto_at t).comp hσ)
  exact ⟨hyper, hyX, hyy' ▸ hy', hA⟩

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {W : Set (ℝ × V)}
  {Jq : ℝ → V → AlmostComplexStructure V}

omit [FiniteDimensional ℝ V] in
/-- A structure which is `J_q(t)` along the end `q` beyond `T₀` is `J_q(±t)` in the positive end
chart. -/
private theorem eq_comp_positiveEndChart {q : Puncture}
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {z : ℝ × ℝ} (hz : T₀ ≤ z.1) :
    J (positiveEndChart q z) = Jq (q.endSign * z.2) ((u ∘ positiveEndChart q) z) := by
  obtain ⟨s, t⟩ := z
  simp only [comp_apply, positiveEndChart_mk]
  exact hJ s _ hz

/-- **The ends of a finite-energy Floer pair of pants have bounded derivatives.** Let `K` be equal
to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C³` Hamiltonians `H_q`, and let `u`
be `C³` on `S`, with image in a compact set `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix an end `q`, and suppose that on it beyond `T₀`
the almost complex structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a
`1`-periodic family `J_q(t, x)` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`. Then for every `b > max T₀ 0` the derivative of `u ∘ φ'_q` is bounded on the
half-cylinder `s ≥ b`, where `φ'_q` is the positive end chart. -/
theorem exists_forall_norm_fderiv_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hBW : univ ×ˢ B ⊆ W) (hJqt : ∀ t, ∀ x ∈ B, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {b : ℝ} (hb : max T₀ 0 < b) :
    ∃ C, ∀ z : ℝ × ℝ, b ≤ z.1 → ‖fderiv ℝ (u ∘ positiveEndChart q) z‖ ≤ C := by
  set a := max T₀ 0
  have hHd : ∀ q t, Differentiable ℝ (H q t) := fun q t ↦
    ((hHs q).differentiable (by norm_num)).comp (differentiable_const t |>.prodMk differentiable_id)
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
  -- In the positive end chart the structure is `J'(t, x) = J_q(±t, x)`.
  set g : ℝ × V → ℝ × V := fun p ↦ (q.endSign * p.1, p.2)
  have hg : ContDiff ℝ 2 g := (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  exact exists_forall_norm_fderiv_le_of_floer (u := u ∘ positiveEndChart q)
    (J := fun t x ↦ Jq (q.endSign * t) x) (W := g ⁻¹' W)
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
    (hW.preimage hg.continuous) (hJq.comp hg.contDiffOn (mapsTo_preimage g W))
    (periodic_comp_endSign_mul hJqper) hB
    (fun p hp ↦ hBW ⟨mem_univ _, hp.2⟩) (fun t x hx ↦ hJqt _ x hx)
    (hu.comp (contDiff_positiveEndChart q 3).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
    (fun s hs t ↦ huB _ (hmem (s, t) hs))
    (fun z hz ↦ by
      rw [← eq_comp_positiveEndChart hJ ((le_max_left _ _).trans hz.1.le)]
      exact isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart hKH hH hHd
        ((le_max_left _ _).trans hz.1.le)
        (((hu.differentiableOn (by norm_num)) _ (hmem z hz.1)).differentiableAt
          (isOpen_thricePuncturedSphereReal.mem_nhds (hmem z hz.1)))
        (hfloer _ (hmem z hz.1)))
    (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      (hu.differentiableOn (by norm_num)) q (le_max_right _ _) (le_max_left _ _))) hb

/-- **The ends of a Floer pair of pants with cylindrical ends converge to nondegenerate orbits.**
Let `K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C³` Hamiltonians
`H_q`, and let `u` be `C³` on `S`, with image in a compact set `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix an end `q`, and suppose that on it beyond `T₀`
the almost complex structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a
`1`-periodic family `J_q(t, x)` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`. Suppose moreover that the suspension of the Hamiltonian vector field of `H_q` is globally
Lipschitz and that every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate: `y(0)` is a
nondegenerate fixed point of the time-one map. Then the loops `t ↦ u(φ_q(±s, t))` converge
uniformly, as `s → ∞`, to a single `1`-periodic orbit of `H_q`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer_of_cylindrical
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hBW : univ ×ˢ B ⊆ W) (hJqt : ∀ t, ∀ x ∈ B, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0)) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) ∧
      TendstoUniformly (fun s t ↦ u (endChart q (q.endSign * s, t))) y atTop := by
  set b := max T₀ 0 + 1
  have hb : max T₀ 0 < b := lt_add_one _
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_positiveEndChart_le hKH hH hHs hu hB huB
    hfloer hE q hW hJq hJqper hBW hJqt hJ hb
  -- The end structures `J_q` have uniform taming constants on `ℝ × B`.
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hB
    (hJq.continuousOn.mono hBW) hJqper hJqt
  have hbT (z : ℝ × ℝ) (hz : b < z.1) : T₀ ≤ z.1 :=
    (le_max_left _ _).trans ((lt_add_one _).trans hz).le
  have huB' (z : ℝ × ℝ) (hz : b < z.1) : (u ∘ positiveEndChart q) z ∈ B :=
    huB _ (positiveEndChart_mem_thricePuncturedSphereReal
      ((le_max_right _ _).trans_lt ((lt_add_one _).trans hz)))
  exact exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer hKH hH
    (fun q ↦ (hHs q).of_le (by norm_num)) (hu.of_le (by norm_num)) hB huB hfloer hE q hL hnd
    (fun z hz ↦ hC z hz.le) hc
    (fun z hz v ↦ by
      rw [eq_comp_positiveEndChart hJ (hbT z hz)]
      exact (hcM _ _ (huB' z hz) v).1)
    fun z hz v ↦ by
      rw [eq_comp_positiveEndChart hJ (hbT z hz)]
      exact (hcM _ _ (huB' z hz) v).2

end InnerProductSpace

end TauCeti.SymplecticForm
