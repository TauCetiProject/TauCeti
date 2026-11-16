/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

/-!
# Asymptotic periodic orbits at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, `K` a Hamiltonian
perturbation on the thrice-punctured sphere `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond some
height `T₀` on each end `q` for `1`-periodic Hamiltonians `H_q`, and `u` a finite-energy `C¹`
solution of the Floer equation `(du - X_K)^{0,1} = 0` on `S` with image in a compact set `B ⊆ M`.
We assume that the almost complex structures `J z` on `T_{u z} M` are uniformly tame on each end
with respect to a `C¹` map `e : M → F` injective on `B` with injective differential on `B`, in the
sense that `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. This file adapts the vector-space end-breaking
and end-convergence formalizations in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` to manifold targets, including the
contractible-orbit sector and the whole-surface energy identity.

**Positive end charts on a manifold target.** In the holomorphic positive end chart `φ'_q(s, t) =
φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`), the perturbation `K` pulls back beyond `T₀` to
`H'_q(t) dt` for `H'_q(t, p) = ±H_q(±t, p)` (`TauCeti.Floer.positiveEndHamiltonian`). By domain
naturality of the intrinsic perturbed differential (`SmoothTwoForm.perturbedMFDeriv`), `u ∘ φ'_q`
solves the Floer equation of a positive half-cylinder for `H'_q` beyond `T₀`
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), with half-cylinder
energy bounded by the energy of `u` over `S`
(`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`).

**Time reversal and contractible orbits.** Reparametrizing time by `t ↦ ±t` identifies the
`1`-periodic orbits of `H'_q` with those of `H_q`
(`SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`), and preserves null-homotopy on
`AddCircle 1`, hence identifies the contractible `1`-periodic orbits as well
(`SmoothTwoForm.mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff`). Because this
bijection fixes evaluation at `t = 0`, isolation of nondegenerate orbits of `H_q` in `B` transfers
directly to `H'_q` on both input and output ends.

**Breaking, whole-end convergence, and energy identity.** At each end `q` of `S`:

* under uniform tameness of `J` on the end, without orbit nondegeneracy or derivative bounds, the
  end loops `t ↦ u(φ_q(±s_n, t))` converge along some sequence `s_n → ∞` to a `1`-periodic (or
  contractible `1`-periodic, when an end loop is null-homotopic) orbit of `X_{H_q}` in `B`,
  uniformly in `e` and pointwise on `M`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, and
  their `[CompactSpace M]` specializations
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer`);
* when `M` is Hausdorff and boundaryless, `H_q` is jointly `C²`, `e ∘ u ∘ φ'_q` has bounded
  derivative on a half-cylinder, and the `1`-periodic (or contractible `1`-periodic) orbits of
  `H_q` in `B` are nondegenerate, the whole end `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a
  single `1`-periodic (resp. contractible `1`-periodic) orbit `y_q` of `X_{H_q}` in `B`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`,
  and their `[CompactSpace M]` specializations
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer`);
* when `u` has integrable symplectic area and curvature on `S` and uniform tameness holds on `S`,
  its energy over `S` is automatically finite, integrable, and given by
  `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)` at the asymptotic orbits `y_q`
  (`exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm`,
  `exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm`, and their
  `pairOfPantsPerturbation` specializations `_of_isCompact` and on `[CompactSpace M]`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

open Set Filter Topology MeasureTheory Function Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

section PositiveEnd

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-- The Hamiltonian vector field of `H'_q(t)` is `±` that of `H_q(±t)`. -/
@[simp]
theorem hamiltonianVectorField_positiveEndHamiltonian (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (q : Puncture) (t : ℝ) (p : M) :
    ω.hamiltonianVectorField (positiveEndHamiltonian H q t) p =
      q.endSign • ω.hamiltonianVectorField (H q (q.endSign * t)) p := by
  have h : positiveEndHamiltonian H q t = q.endSign • H q (q.endSign * t) := by
    funext y
    simp [positiveEndHamiltonian_apply]
  rw [h, hamiltonianVectorField_const_smul]

/-- Reading a curve with the time `±t` of an end `q` carries `1`-periodic solutions of `X_{H'_q}`
onto `1`-periodic solutions of `X_{H_q}`. -/
private theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
  refine mem_periodicSolutions.2 ⟨fun t ↦ ?_, periodic_comp_endSign_mul hxper⟩
  have hφ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) := by
    simpa only [Pi.smul_def, id_eq, smul_eq_mul] using hasMFDerivAt_iff_hasFDerivAt.2
      ((hasFDerivAt_id t).const_smul q.endSign)
  have hd := hxd (q.endSign * t)
  simp only [hamiltonianVectorField_positiveEndHamiltonian, endSign_mul_endSign_mul] at hd
  have heq (r : ℝ) :
      (((1 : ℝ →L[ℝ] ℝ).smulRight
          (q.endSign • ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))).comp
          (q.endSign • ContinuousLinearMap.id ℝ ℝ)) r =
        (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) r := by
    rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> simp [h]
  exact (hd.comp t hφ).congr_mfderiv (ContinuousLinearMap.ext heq)

/-- **Orbits in positive end charts.** A curve `x : ℝ → M` is a `1`-periodic solution of the
Hamiltonian vector field of `H'_q` if and only if `t ↦ x(±t)` is a `1`-periodic solution of that of
`H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  have hx' : x = fun t ↦ (fun s ↦ x (q.endSign * s)) (q.endSign * t) := by
    funext t
    simp only [endSign_mul_endSign_mul]
  rw [hx']
  exact mem_periodicSolutions_comp_endSign_mul (H := positiveEndHamiltonian H)
    ((positiveEndHamiltonian_positiveEndHamiltonian H q).symm ▸ hx)

/-- Null-homotopy of a `1`-periodic loop in `M` is preserved under `t ↦ ±t`. -/
private theorem exists_nullhomotopic_comp_endSign_mul {X : Type*} [TopologicalSpace X]
    (q : Puncture) {x : ℝ → X}
    (hx : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = x t) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = x (q.endSign * t) := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨g', hg', hg'x⟩ := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
  have habs : (1 : ℝ) / |q.endSign| = 1 := by rw [q.abs_endSign, div_one]
  refine habs ▸ ⟨g', hg', fun t ↦ ?_⟩
  rw [hg'x t, hgx, mul_comm]

/-- **Contractible orbits in positive end charts.** A curve `x : ℝ → M` is a contractible
`1`-periodic solution of `X_{H'_q}` if and only if `t ↦ x(±t)` is a contractible `1`-periodic
solution of `X_{H_q}`. -/
theorem mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions, mem_contractiblePeriodicSolutions,
    mem_periodicSolutions_positiveEndHamiltonian_iff]
  refine and_congr_right fun _ ↦ ⟨exists_nullhomotopic_comp_endSign_mul q, fun h ↦ ?_⟩
  simpa only [endSign_mul_endSign_mul] using exists_nullhomotopic_comp_endSign_mul q h

omit [IsManifold I ⊤ M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the global coordinates of `S` are
differentiable in the target point when `H_q(t)` is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) =
      (q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v) •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im := by
    funext x
    simpa [hKH q _ x hre] using mul_comm _ _
  rw [h]
  exact (hHd _ y).const_smul _

/-- Beyond `T₀` on the positive end `q`, the pulled-back perturbation is `H'_q(t) dt`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      ω.perturbedMFDeriv
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        (u ∘ positiveEndChart q) ζ :=
  ω.perturbedMFDeriv_congr (u ∘ positiveEndChart q)
    (funext fun x ↦ (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x).symm)
    (funext fun x ↦
      (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x).symm)

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** Let
`K` agree with `H_q(t) dt` beyond `T₀` on each end `q`, and let `u : ℝ × ℝ → M` solve
`(du - X_K)^{0,1} = 0` at `φ'_q(ζ)` for `ζ.1 ≥ T₀`. Then `u ∘ φ'_q` solves the half-cylinder Floer
equation `(dv - X_{H'_q} dt)^{0,1} = 0` at `ζ`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))}
    (hζ : T₀ ≤ ζ.1) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **The energy of an end of a Floer pair of pants in a manifold.** When `K` agrees with
`H_q(t) dt` beyond `T₀` on each end `q`, the lower Lebesgue energy of `u ∘ φ'_q` for `H'_q` over
`(a, ∞) × [0, 1]`, with `a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : ∀ z ∈ thricePuncturedSphereReal, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * e (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζ₀ : 0 < ζ.1 := ha₀.trans_lt hζ.1
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ₀
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) (hu _ hS)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

end PositiveEnd

namespace IsNondegenerate

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → M} {q : Puncture}

/-! ### Breaking along a sequence at each end -/

/-- Beyond `a ≥ max T₀ 0`, `u ∘ φ'_q` satisfies the smoothness, periodicity, Floer-equation, and
finite-energy hypotheses of a positive Floer half-cylinder. -/
private theorem floer_halfCylinder_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun z ↦ u (positiveEndChart q z)) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ u (positiveEndChart q (s, t))) 1) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z) ≠ ⊤ := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t x ↦
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  have humd : ∀ z ∈ thricePuncturedSphereReal, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn (fun z hz ↦ hmem z hz.1),
    fun s _ t ↦ by simp only [positiveEndChart_add_one], fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      humd ha₀ haT)⟩
  have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le) (humd _ (hmem z hz.1)) (hfloer _ (hmem z hz.1))
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 hcl
  simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using hiff

omit [IsManifold I ⊤ M] in
/-- A null-homotopic end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) yields a null-homotopic positive-end
loop `t ↦ u(φ'_q(s₁, t))` at height `s₁ > a` for any `a ≥ 0`. -/
private theorem exists_gt_exists_nullhomotopic_positiveEndChart (I : ModelWithCorners ℝ E G)
    (hu : ContinuousOn u thricePuncturedSphereReal) {a : ℝ} (ha₀ : 0 ≤ a)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ s₁ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s₁, t)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  have hnull₀' : ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s₀, t)) := by
    simpa only [positiveEndChart_mk] using exists_nullhomotopic_comp_endSign_mul q hnull₀
  have hu0c : ContinuousOn (fun z ↦ u (positiveEndChart q z)) (Ioi (0 : ℝ) ×ˢ univ) :=
    hu.comp (contDiff_positiveEndChart q 0).continuous.continuousOn fun z hz ↦
      positiveEndChart_mem_thricePuncturedSphereReal hz.1
  exact ⟨a + 1, lt_add_one a, (exists_nullhomotopic_slice_iff_of_isPreconnected isPreconnected_Ioi
    hu0c one_pos (fun s _ t ↦ by simp only [positiveEndChart_add_one]) hs₀
    (add_pos_of_nonneg_of_pos ha₀ zero_lt_one)).1 hnull₀'⟩

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F} {B : Set M}

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `K` equal `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic Hamiltonians `H_q` with `H_q`
jointly `C¹` at a fixed puncture `q`, and let `u` be `C¹` on `S = ℂ ∖ {0, 1}`, with image in a
compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy, where the almost
complex structures on the end `q` are uniformly tame with respect to a `C¹` map `e : M → F`
injective on `B` with injective differential on `B`. Then there are a `1`-periodic orbit `y` of
`X_{H_q}` in `B` and `σ_n → ∞` such that `t ↦ u(φ_q(±σ_n, t))` converges to `y`, uniformly in `e`
and pointwise on `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHq hu hfloer hE ha₀ haT
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp fun t ↦ q.endSign * t
  · simpa only [← endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants on a closed manifold breaks off a periodic orbit at each
end.** The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to a compact
manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHq he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE hc hJc
  exact ⟨y, hy, h⟩

/-- **A contractible end of a finite-energy Floer pair of pants breaks off a contractible periodic
orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, if some end loop
`t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic as a map `AddCircle 1 → M`, then the sequential
limit orbit `y` is contractible (`y ∈ contractiblePeriodicSolutions _ 1`). -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧ ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHq hu hfloer hE ha₀ haT
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (exists_gt_exists_nullhomotopic_positiveEndChart I hu.continuousOn ha₀ hnull)
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t),
    mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx, fun t ↦ hxB _, σ, hσ, ?_,
    fun t ↦ ?_⟩
  · simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp fun t ↦ q.endSign * t
  · simpa only [← endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A contractible end of a finite-energy Floer pair of pants on a closed manifold breaks off a
contractible periodic orbit.** The specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`
to a compact manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
      hKH hH hHq he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J
      hfloer hE hc hJc
  exact ⟨y, hy, h⟩

/-! ### Whole-end convergence at nondegenerate ends -/

section NondegenerateEnds

variable [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ F] in
/-- An orbit of `H'_q` starting in `B` at a nondegenerate fixed point of the time-one map of `H_q`
is isolated in `e` among `1`-periodic orbits of `H'_q` starting in `B`. -/
private theorem exists_pos_forall_mem_periodicSolutions_positiveEndHamiltonian_eq
    (hω : ω.IsNondegenerate) (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B) {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
    (hxB : x 0 ∈ B)
    (hnd : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (x 0)) :
    ∃ ε > 0, ∀ y ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      y 0 ∈ B → dist (e (y 0)) (e (x 0)) < ε → y = x := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq2.of_le (by norm_num))
  obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_mem_periodicSolutions_eq_of_isNondegenerateFixedPt
    (s := 0) hX hB he.continuous.continuousOn he_inj
    (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx) (by simpa only [mul_zero] using hxB)
    (by simpa only [mul_zero, zero_add] using hnd)
  refine ⟨ε, hε, fun y hy hyB hyx ↦ funext fun t ↦ ?_⟩
  have hxy := congrFun (hiso _ (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hy)
    (by simpa only [mul_zero] using hyB) (by simpa only [mul_zero] using hyx)) (q.endSign * t)
  simpa only [endSign_mul_endSign_mul] using hxy

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate orbit.** Under
the hypotheses of `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
suppose that `M` is Hausdorff and boundaryless, `H_q` is jointly `C²`, `e ∘ u ∘ φ'_q` has bounded
derivative on `s > b`, and every `1`-periodic orbit `y` of `X_{H_q}` in `B` is nondegenerate (`y 0`
is a nondegenerate fixed point of `timeDependentFlowOf X_{H_q} 0 1`). Then `t ↦ u(φ_q(±s, t))`
converges as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`, uniformly in `e` and
pointwise on `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) := hHq2.of_le one_le_two
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHq hu hfloer hE ha₀ haT
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
      (fun z hz ↦ hC z (hab z hz.1)) fun x hx hxB ↦ by
        obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_mem_periodicSolutions_positiveEndHamiltonian_eq
          hω hHq2 he hB he_inj hx (hxB 0) (by
            simpa only [mul_zero] using
              hnd _ (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx) fun t ↦ hxB _)
        exact ⟨ε, hε, fun y hy hyB hyx ↦ hiso y hy (hyB 0) (hyx 0)⟩
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp fun t ↦ q.endSign * t
  · simpa only [← endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants on a closed manifold to a nondegenerate
orbit.** The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` to a compact
manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      hHq2 he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE
      (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, hux, hpt⟩

/-- **Convergence of a contractible end of a Floer pair of pants in a manifold to a nondegenerate
contractible orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, suppose that
some end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic as a map `AddCircle 1 → M`, and
assume nondegeneracy only for the *contractible* `1`-periodic orbits of `X_{H_q}` in `B`. Then
`t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single contractible `1`-periodic orbit `y` of
`X_{H_q}` in `B`. -/
theorem
  exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) := hHq2.of_le one_le_two
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHq hu hfloer hE ha₀ haT
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (exists_gt_exists_nullhomotopic_positiveEndChart I hu.continuousOn ha₀ hnull)
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
      (fun z hz ↦ hC z (hab z hz.1)) fun x hx hxB ↦ by
        obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_mem_periodicSolutions_positiveEndHamiltonian_eq
          hω hHq2 he hB he_inj (mem_contractiblePeriodicSolutions.1 hx).1 (hxB 0) (by
            simpa only [mul_zero] using hnd _
              (mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx) fun t ↦ hxB _)
        exact ⟨ε, hε, fun y hy hyB hyx ↦
          hiso y (mem_contractiblePeriodicSolutions.1 hy).1 (hyB 0) (hyx 0)⟩
  refine ⟨fun t ↦ x (q.endSign * t),
    mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx, fun t ↦ hxB _, ?_,
    fun t ↦ ?_⟩
  · simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp fun t ↦ q.endSign * t
  · simpa only [← endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of a contractible end on a closed manifold to a nondegenerate contractible
orbit.** The specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
to a compact manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, hux, hpt⟩ :=
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hω hKH hH hHq2 he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _)
      hnull J hfloer hE (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, hux, hpt⟩

/-! ### The energy identity on the pair of pants with asymptotic periodic orbits -/

section AsymptoticPeriodicOrbits

omit [FiniteDimensional ℝ F] [T2Space M] [BoundarylessManifold I M] in
/-- For a tamed Floer solution `u` with image in a compact set `B` and integrable symplectic area
and curvature, the Floer energy density is nonnegative on `S` and has finite lower Lebesgue
integral over `S`. -/
private theorem floerEnergyDensity_nonneg_and_lintegral_ne_top_of_isCompact (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : IsCompact B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal) :
    (∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ∧
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have htame (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      (hω.symplecticFormAt (u z)).Tames (J z) := fun v hv ↦ by
    have hdv : mvfderiv I e (u z) v ≠ 0 := fun h0 ↦
      hv (hde (u z) (huB z hz) (h0.trans (map_zero _).symm))
    exact (mul_pos hc (pow_pos (norm_pos_iff.2 hdv) 2)).trans_le (hJc z hz v)
  have hnonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    floerEnergyDensity_nonneg hω (htame z hz) (hfloer z hz)
  choose M₀ hM₀ using fun q ↦
    (isCompact_Icc.prod hB).exists_bound_of_continuousOn (hHs q).continuous.continuousOn
  have hM (q : Puncture) : ∀ᶠ σ in atTop,
      |∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t)))| ≤ M₀ q := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M₀ q)
      (f := fun t ↦ H q t (u (endChart q (q.endSign * σ, t)))) fun t ht ↦
        hM₀ q (t, _) ⟨Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht),
          huB _ (endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hσ))⟩
    simpa [Real.norm_eq_abs] using hb
  rw [IntegrableOn, hS] at hA hR
  refine ⟨hnonneg, ?_⟩
  rw [hS]
  exact hω.lintegral_floerEnergyDensity_ne_top_of_eq_smul_endAngularForm hK hKH hH hu hnonneg hA hR
    hM

omit [FiniteDimensional ℝ F] [T2Space M] [BoundarylessManifold I M] in
/-- Given pointwise end limits `y q` for a nonnegative-energy `C¹` map `u` with image in a compact
set `B`, the energy density is integrable on `S` and satisfies the Bochner energy identity. -/
private theorem integrableOn_and_integral_floerEnergyDensity_of_tendsto (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : IsCompact B) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnonneg : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    {y : Puncture → ℝ → M}
    (hy : ∀ q t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hh (q : Puncture) := tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hB
    hu.continuousOn ((eventually_gt_atTop (0 : ℝ)).mono fun s hs t _ ↦
      huB _ (endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hs))) (hy q)
  rw [IntegrableOn, hS] at hA hR
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hnonneg hA
    hR hh
  refine ⟨by rwa [IntegrableOn, hS], ?_⟩
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA hR hh

/-- **The pair-of-pants energy identity in a manifold with asymptotic `1`-periodic orbits.** Let `K`
be `C¹` on `S × M` and equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C²`
Hamiltonians `H_q` whose `1`-periodic orbits in a compact set `B ⊆ M` are nondegenerate. Let `u` be
a `C¹` solution of `(du - X_K)^{0,1} = 0` on `S` with image in `B`, uniformly tame almost complex
structures via `e : M → F`, bounded end derivatives `‖d(e ∘ u ∘ φ'_q)‖ ≤ C_q` on `s > b_q`, and
integrable symplectic area and curvature on `S`. Then the energy of `u` over `S` is automatically
finite and integrable, the ends of `u` converge as `s → ∞` to `1`-periodic orbits `y_q` of `X_{H_q}`
in `B`, and `∫_S E = ∫_S u^*ω + ∑ q, q.endSign * ∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
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
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  obtain ⟨hnonneg, hE⟩ := floerEnergyDensity_nonneg_and_lintegral_ne_top_of_isCompact hω hK hKH hH
    hHs1 hB hde hu huB hc hJc hfloer hA hR
  choose b C hbC using hC
  choose y hy using fun q ↦
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hKH hH (hHs q) he hB he_inj hde hu huB J hfloer hE (hnd q)
      (b := max (b q) 0) (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) hc
      fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt hz)) v
  exact ⟨y, hy, integrableOn_and_integral_floerEnergyDensity_of_tendsto hω hK hKH hH hHs1 hB hu huB
    hnonneg hA hR fun q ↦ (hy q).2.2.2⟩

/-- **The pair-of-pants energy identity in a manifold with contractible asymptotic orbits.** The
contractible-sector counterpart of
`exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm`, assuming null-homotopic
end loops and nondegeneracy only for contractible `1`-periodic orbits in `B`. -/
theorem exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  obtain ⟨hnonneg, hE⟩ := floerEnergyDensity_nonneg_and_lintegral_ne_top_of_isCompact hω hK hKH hH
    hHs1 hB hde hu huB hc hJc hfloer hA hR
  choose b C hbC using hC
  choose y hy using fun q ↦
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hω hKH hH (hHs q) he hB he_inj hde hu huB (hnull q) J hfloer hE (hnd q)
      (b := max (b q) 0) (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) hc
      fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt hz)) v
  exact ⟨y, hy, integrableOn_and_integral_floerEnergyDensity_of_tendsto hω hK hKH hH hHs1 hB hu huB
    hnonneg hA hR fun q ↦ (hy q).2.2.2⟩

/-- **The energy identity of `pairOfPantsPerturbation` in a compact subset of a manifold.** The
specialization of `exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm` to
`TauCeti.Floer.pairOfPantsPerturbation` for a map `u` with image in a compact set `B ⊆ M`; the
cutoff regularity, cylindrical-end condition beyond height `2`, and curvature integrability hold
automatically. -/
theorem exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
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
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact hω.exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- **The energy identity of `pairOfPantsPerturbation` on a closed manifold with asymptotic
`1`-periodic orbits.** The specialization of
`exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation_of_isCompact` (and hence of
`exists_forall_mem_periodicSolutions_integral_of_eq_smul_endAngularForm`) to a compact Hausdorff
boundaryless manifold `M`: for a `C¹` Floer solution `u` with uniformly tame `J`, bounded end
derivatives, integrable symplectic area, and nondegenerate `1`-periodic orbits, the ends converge to
`1`-periodic orbits `y_q` and `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation
    [CompactSpace M] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
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
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hEid⟩ :=
    hω.exists_forall_mem_periodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc
      hfloer hA (fun q y hy _ ↦ hnd q y hy) hC
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hEid⟩

/-- **The energy identity of `pairOfPantsPerturbation` in a compact subset with contractible
asymptotic orbits.** The specialization of
`exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm` to
`TauCeti.Floer.pairOfPantsPerturbation` for a map `u` with image in a compact set `B ⊆ M`, assuming
null-homotopic end loops and nondegeneracy only for contractible `1`-periodic orbits in `B`. -/
theorem
  exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact hω.exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hnull J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- **The energy identity of `pairOfPantsPerturbation` on a closed manifold with contractible
asymptotic `1`-periodic orbits.** The specialization of
`exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact`
(and hence of `exists_forall_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm`)
to a compact Hausdorff boundaryless manifold `M`, assuming null-homotopic end loops and
nondegeneracy only for contractible `1`-periodic orbits. -/
theorem exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation
    [CompactSpace M] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hEid⟩ :=
    hω.exists_forall_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J hc
      hJc hfloer hA (fun q y hy _ ↦ hnd q y hy) hC
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hEid⟩

end AsymptoticPeriodicOrbits

end NondegenerateEnds

end IsNondegenerate

end SmoothTwoForm

end TauCeti
