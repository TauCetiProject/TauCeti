/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold.Orbit
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

/-!
# End convergence and energy identity for a Floer pair of pants in a manifold

Building on `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold.Orbit`, this file adapts
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` to a Hausdorff boundaryless
finite-dimensional manifold `M` with nondegenerate two-form `ω`:

* **Whole-end convergence.** For jointly `C²` `H_q`, bounded `fderiv (e ∘ u ∘ φ'_q)`, and
  nondegenerate full or contractible `1`-periodic orbits in `B`, `t ↦ u(φ_q(±s, t))` converges as
  `s → ∞` to a single orbit `y_q` in `B`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer`,
  `_of_isCompact`).
* **Energy identity at asymptotic orbits.** With integrable area and curvature and uniform tameness
  on `S`, `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)` holds at `y_q`
  (`exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm`,
  `exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm`, and their
  `pairOfPantsPerturbation` specializations).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis, ETH Zürich
  (1995).
-/

public section

open Set Filter Topology MeasureTheory Function Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ b C c : ℝ}
  {e : M → F} {B : Set M} {u : ℝ × ℝ → M} {q : Puncture}

/-! ### Whole-end convergence at nondegenerate ends -/

section NondegenerateEnds

omit [FiniteDimensional ℝ F] in
/-- An orbit of `H'_q` starting in `B` at a nondegenerate fixed point of `H_q` is isolated. -/
private theorem exists_pos_forall_mem_periodicSolutions_positiveEndHamiltonian_eq
    (hω : ω.IsNondegenerate) (hHq2 : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B) {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) (hxB : x 0 ∈ B)
    (hnd : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (x 0)) :
    ∃ ε > 0, ∀ y ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      y 0 ∈ B → dist (e (y 0)) (e (x 0)) < ε → y = x := by
  obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_mem_periodicSolutions_eq_of_isNondegenerateFixedPt
    (s := 0)
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hHq2.of_le (by norm_num))) hB
    he.continuous.continuousOn he_inj (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx)
    (by simpa only [mul_zero] using hxB) (by simpa only [mul_zero, zero_add] using hnd)
  refine ⟨ε, hε, fun y hy hyB hyx ↦ funext fun t ↦ ?_⟩
  simpa only [endSign_mul_endSign_mul] using congrFun
    (hiso _ (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hy)
      (by simpa only [mul_zero] using hyB) (by simpa only [mul_zero] using hyx)) (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate orbit.** Under
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, if `H_q` is jointly
`C²`, `e ∘ u ∘ φ'_q` has bounded derivative on `s > b`, and `1`-periodic orbits of `X_{H_q}` in `B`
are nondegenerate, `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a `1`-periodic orbit in `B`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hc : 0 < c) (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) := fun _ ↦ ((hHq2.of_le one_le_two).comp
    (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  have humd (z) (hz : z ∈ thricePuncturedSphereReal) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :=
    positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hz)
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHq2.of_le one_le_two))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun _ hz ↦ hmem hz.1)
      (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun _ hs _ ↦ huB _ (hmem hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v)
      (fun _ hz ↦ mfderiv_comp_positiveEndChart_add_eq_zero hKH hH hHd (haT.trans hz.1.le)
        (humd _ (hmem hz.1)) (hfloer _ (hmem hz.1)))
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
        humd ha₀ haT))
      (fun z hz ↦ hC z ((le_max_right _ _).trans_lt hz.1)) fun x hx hxB ↦
        let ⟨ε, hε, hiso⟩ := exists_pos_forall_mem_periodicSolutions_positiveEndHamiltonian_eq hω
          hHq2 he hB he_inj hx (hxB 0) <| by
            simpa only [mul_zero] using
              hnd _ (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx) fun _ ↦ hxB _
        ⟨ε, hε, fun y hy hyB hyx ↦ hiso y hy (hyB 0) (hyx 0)⟩
  exact ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun _ ↦ hxB _,
    by simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp (q.endSign * ·),
    fun t ↦ by simpa only [comp_apply, ← endChart_eq_positiveEndChart] using hpt (q.endSign * t)⟩

/-- **Convergence of an end on a closed manifold to a nondegenerate orbit.** `[CompactSpace M]` case
of `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hc : 0 < c) (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH hHq2
    he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE
    (fun y hy _ ↦ hnd y hy) hc hC hJc).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

/-- **Convergence of a contractible end of a Floer pair of pants in a manifold to a nondegenerate
contractible orbit.** Under
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, if some end
loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic on `AddCircle 1` and contractible orbits of
`X_{H_q}` in `B` are nondegenerate, `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a contractible
orbit in `B`. -/
theorem
  exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hc : 0 < c) (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) := fun _ ↦ ((hHq2.of_le one_le_two).comp
    (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  have humd (z) (hz : z ∈ thricePuncturedSphereReal) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :=
    positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hz)
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHq2.of_le one_le_two))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun _ hz ↦ hmem hz.1)
      (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun _ hs _ ↦ huB _ (hmem hs))
      ⟨a + 1, lt_add_one a, exists_nullhomotopic_positiveEndChart I hu.continuousOn hs₀
        (add_pos_of_nonneg_of_pos ha₀ zero_lt_one) hnull₀⟩
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v)
      (fun _ hz ↦ mfderiv_comp_positiveEndChart_add_eq_zero hKH hH hHd (haT.trans hz.1.le)
        (humd _ (hmem hz.1)) (hfloer _ (hmem hz.1)))
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
        humd ha₀ haT))
      (fun z hz ↦ hC z ((le_max_right _ _).trans_lt hz.1)) fun x hx hxB ↦
        let ⟨ε, hε, hiso⟩ := exists_pos_forall_mem_periodicSolutions_positiveEndHamiltonian_eq hω
          hHq2 he hB he_inj (mem_contractiblePeriodicSolutions.1 hx).1 (hxB 0) <| by
            simpa only [mul_zero] using hnd _
              (mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx) fun _ ↦ hxB _
        ⟨ε, hε, fun y hy hyB hyx ↦
          hiso y (mem_contractiblePeriodicSolutions.1 hy).1 (hyB 0) (hyx 0)⟩
  exact ⟨(x <| q.endSign * ·), mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun _ ↦ hxB _,
    by simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp (q.endSign * ·),
    fun t ↦ by simpa only [comp_apply, ← endChart_eq_positiveEndChart] using hpt (q.endSign * t)⟩

/-- **Convergence of a contractible end on a closed manifold to a nondegenerate contractible
orbit.** `[CompactSpace M]` case of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hc : 0 < c) (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  (exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hω
    hKH hH hHq2 he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J
    hfloer hE (fun y hy _ ↦ hnd y hy) hc hC hJc).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

end NondegenerateEnds

/-! ### The energy identity on the pair of pants with asymptotic periodic orbits -/

section AsymptoticPeriodicOrbits

private noncomputable abbrev pertReal (K : ℂ → M → ℂ →L[ℝ] ℝ) (z : ℝ × ℝ) (x : M) : ℝ :=
  K (Complex.equivRealProdCLM.symm z) x 1

private noncomputable abbrev pertImag (K : ℂ → M → ℂ →L[ℝ] ℝ) (z : ℝ × ℝ) (x : M) : ℝ :=
  K (Complex.equivRealProdCLM.symm z) x Complex.I

private noncomputable abbrev areaDensity (ω : SmoothTwoForm I M) (u : ℝ × ℝ → M) (z : ℝ × ℝ) : ℝ :=
  SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)

omit [FiniteDimensional ℝ F] [T2Space M] [BoundarylessManifold I M] in
/-- For a tamed `C¹` Floer solution `u` in `B` with integrable area and curvature, energy over `S`
is finite; given end convergence under finite energy, the Bochner energy identity holds at `y`. -/
private theorem exists_forall_integral_of_eq_smul_endAngularForm (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x,
      ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (hB : IsCompact B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (pertReal K) (pertImag K) u z).toLinearMap)
    (hA : IntegrableOn (areaDensity ω u) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (pertReal K) (pertImag K) z (u z))
      thricePuncturedSphereReal) {P : Puncture → (ℝ → M) → Prop}
    (hend : ∫⁻ z in thricePuncturedSphereReal,
        ENNReal.ofReal (ω.floerEnergyDensity (pertReal K) (pertImag K) u z) ≠ ⊤ →
      ∀ q, ∃ y, P q y ∧ (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t))) :
    ∃ y : Puncture → ℝ → M, (∀ q, P q (y q) ∧ (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity (pertReal K) (pertImag K) u) thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity (pertReal K) (pertImag K) u z =
        (∫ z in thricePuncturedSphereReal, areaDensity ω u z) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal,
            ω.hamiltonianCurvature (pertReal K) (pertImag K) z (u z) := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hnonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (pertReal K) (pertImag K) u z :=
    floerEnergyDensity_nonneg hω (fun v hv ↦ (mul_pos hc (pow_pos (norm_pos_iff.2 fun h0 ↦
      hv (hde (u z) (huB z hz) (h0.trans (map_zero _).symm))) 2)).trans_le (hJc z hz v))
      (hfloer z hz)
  choose M₀ hM₀ using fun q ↦
    (isCompact_Icc.prod hB).exists_bound_of_continuousOn (hHs q).continuous.continuousOn
  have hM (q : Puncture) : ∀ᶠ σ in atTop,
      |∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t)))| ≤ M₀ q := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1) (C := M₀ q) (f := fun t ↦ H q t (u (endChart q (q.endSign * σ, t))))
      fun t ht ↦ hM₀ q (t, _) ⟨Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht),
        huB _ (endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hσ))⟩
  rw [IntegrableOn, hS] at hA hR
  choose y hy using hend (by
    rw [hS]
    exact ((hω.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm hK hKH hH hu hnonneg hA hR
      hM).trans_lt ENNReal.ofReal_lt_top).ne)
  have hh (q : Puncture) := tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hB
    hu.continuousOn ((eventually_gt_atTop (0 : ℝ)).mono fun _ hs _ _ ↦
      huB _ (endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hs)))
    (hy q).2.2.2
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hnonneg hA
    hR hh
  refine ⟨y, hy, by rwa [IntegrableOn, hS], ?_⟩
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA hR hh

/-- **The pair-of-pants energy identity in a manifold with asymptotic `1`-periodic orbits.** For `K`
`C¹` on `S × M` equal to `H_q(t) dt` beyond `T₀` for `1`-periodic `C²` Hamiltonians `H_q` with
nondegenerate `1`-periodic orbits in `B`, any `C¹` Floer solution `u` in `B` with uniformly tame
`J`, bounded end derivatives, and integrable area and curvature has integrable energy
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)` at its asymptotic orbits `y_q`. -/
theorem exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate) (hK : ∀ (w : ThricePuncturedSphere) x,
      ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M, (∀ q,
        y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧ (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  choose b C hbC using hC
  exact exists_forall_integral_of_eq_smul_endAngularForm hω hK hKH hH
    (fun q ↦ (hHs q).of_le one_le_two) hB hde hu huB hc hJc hfloer hA hR fun hE q ↦
      hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
        (hHs q) he hB he_inj hde hu huB J hfloer hE (hnd q) (b := max (b q) 0) hc
        (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) fun _ hz v ↦
        hJc _ (positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)) v

/-- **The pair-of-pants energy identity in a manifold with contractible asymptotic orbits.**
Contractible-sector counterpart of
`exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm`, assuming null-homotopic
end loops and nondegeneracy only for contractible `1`-periodic orbits in `B`. -/
theorem exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate) (hK : ∀ (w : ThricePuncturedSphere) x,
      ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M, (∀ q,
        y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  choose b C hbC using hC
  exact exists_forall_integral_of_eq_smul_endAngularForm hω hK hKH hH
    (fun q ↦ (hHs q).of_le one_le_two) hB hde hu huB hc hJc hfloer hA hR fun hE q ↦
      exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
        hω hKH hH (hHs q) he hB he_inj hde hu huB (hnull q) J hfloer hE (hnd q)
        (b := max (b q) 0) hc (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) fun _ hz v ↦
        hJc _ (positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)) v

/-- `pairOfPantsPerturbation` specialization of
`exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm` in `B`. -/
theorem exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q))) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    (hB : IsCompact B) (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M, (∀ q,
        y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧ (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  let hHs1 (q : Puncture) := (hHs q).of_le one_le_two
  exact hω.exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- `[CompactSpace M]` case of
`exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation_of_isCompact`. -/
theorem exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q))) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M, (∀ q,
        y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  (hω.exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation_of_isCompact hH hHs he
    isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hA
    (fun q y hy _ ↦ hnd q y hy) hC).imp fun _ ⟨hy, h⟩ ↦ ⟨fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, h⟩

/-- `pairOfPantsPerturbation` specialization of
`exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm` in `B`. -/
theorem
  exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q))) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    (hB : IsCompact B) (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M, (∀ q,
        y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  let hHs1 (q : Puncture) := (hHs q).of_le one_le_two
  exact hω.exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hnull J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- `[CompactSpace M]` case of
`exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact`. -/
theorem exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation
    [CompactSpace M] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q))) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M, (∀ q,
        y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  (hω.exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J hc hJc
    hfloer hA (fun q y hy _ ↦ hnd q y hy) hC).imp fun _ ⟨hy, h⟩ ↦
      ⟨fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, h⟩

end AsymptoticPeriodicOrbits

end TauCeti.SmoothTwoForm.IsNondegenerate
