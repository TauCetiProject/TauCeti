/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Asymptotic periodic orbits at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, `K` a Hamiltonian
perturbation on the thrice-punctured sphere `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond some
height `T₀` on each end `q` for `1`-periodic Hamiltonians `H_q`, and `u` a finite-energy `C¹`
solution of the Floer equation `(du - X_K)^{0,1} = 0` on `S` with image in a compact set `B ⊆ M`,
measured through a `C¹` map `e : M → F` injective on `B` with injective differential on `B`.

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

**Breaking and whole-end convergence.** Consequently, at each end `q`:

* without orbit nondegeneracy or derivative bounds, the end loops `t ↦ u(φ_q(±s_n, t))` converge
  along some sequence `s_n → ∞` to a `1`-periodic (or contractible `1`-periodic, when an end loop
  is null-homotopic) orbit of `X_{H_q}` in `B`, uniformly in `e` and pointwise on `M`
  (`SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer`);
* when `M` is Hausdorff and boundaryless, `H_q` is jointly `C²`, `e ∘ u ∘ φ'_q` has bounded
  derivative on a half-cylinder, and the `1`-periodic (or contractible `1`-periodic) orbits of
  `H_q` in `B` are nondegenerate, the whole end `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a
  single `1`-periodic (resp. contractible `1`-periodic) orbit `y_q` of `X_{H_q}`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop` and
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop`).

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

namespace Floer

/-- On a manifold target, the positive end Hamiltonian `H'_q(t, p) = ±H_q(±t, p)` inherits joint
`C^n` regularity from `H_q`. -/
theorem contMDiff_uncurry_positiveEndHamiltonian {E G M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M]
    [ChartedSpace G M] {H : Puncture → ℝ → M → ℝ} {q : Puncture} {n : WithTop ℕ∞}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (positiveEndHamiltonian H q)) := by
  have h : uncurry (positiveEndHamiltonian H q) =
      fun p : ℝ × M ↦ q.endSign * uncurry (H q) (q.endSign * p.1, p.2) := by
    ext ⟨t, x⟩
    exact positiveEndHamiltonian_apply H q t x
  rw [h]
  exact (contMDiff_const (c := q.endSign)).mul
    (hH.comp (((contMDiff_const (c := q.endSign)).mul contMDiff_fst).prodMk contMDiff_snd))

end Floer

namespace SmoothTwoForm

open Floer

section PositiveEnd

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-- At the reflected time `±t`, the Hamiltonian vector field of `H'_q` is `±` that of `H_q`. -/
theorem hamiltonianVectorField_positiveEndHamiltonian (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (q : Puncture) (t : ℝ) (p : M) :
    ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) p =
      q.endSign • ω.hamiltonianVectorField (H q t) p := by
  have h : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t := by
    funext y
    rw [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul, Pi.smul_apply,
      smul_eq_mul]
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
  rw [hamiltonianVectorField_positiveEndHamiltonian] at hd
  have heq (r : ℝ) :
      (((1 : ℝ →L[ℝ] ℝ).smulRight
          (q.endSign • ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))).comp
          (q.endSign • ContinuousLinearMap.id ℝ ℝ)) r =
        (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) r := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.id_apply,
      one_apply_eq_self, one_apply_eq_self, smul_eq_mul, smul_smul, mul_assoc,
      mul_comm r q.endSign, ← mul_assoc, endSign_mul_self, one_mul]
  exact (hd.comp t hφ).congr_mfderiv (ContinuousLinearMap.ext heq)

/-- **Orbits in positive end charts.** A curve `x : ℝ → M` is a `1`-periodic solution of the
Hamiltonian vector field of `H'_q` if and only if `t ↦ x(±t)` is a `1`-periodic solution of that of
`H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  have hH' : positiveEndHamiltonian (positiveEndHamiltonian H) q = H q := by
    funext t p
    simp only [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul]
  have hx' : x = fun t ↦ (fun s ↦ x (q.endSign * s)) (q.endSign * t) := by
    funext t
    simp only [← mul_assoc, endSign_mul_self, one_mul]
  rw [hx']
  exact mem_periodicSolutions_comp_endSign_mul (H := positiveEndHamiltonian H) (hH'.symm ▸ hx)

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
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using
    exists_nullhomotopic_comp_endSign_mul q h

omit [IsManifold I ⊤ M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the global coordinates of `S` are
differentiable in the target point when `H_q(t)` is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
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
    rw [hKH q _ x hre, smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact ((hHd q _) y).const_smul _

/-- Pointwise congruence of `perturbedMFDeriv` in the perturbation components at `z`. -/
private theorem perturbedMFDeriv_congr {Ks Kt Ks' Kt' : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M}
    {z : ℝ × ℝ} (hs : Ks z = Ks' z) (ht : Kt z = Kt' z) :
    ω.perturbedMFDeriv Ks Kt u z = ω.perturbedMFDeriv Ks' Kt' u z := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hs, ht]

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
  perturbedMFDeriv_congr
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
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    {q : Puncture} {ζ : ℝ × ℝ}
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
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    (hu : ∀ z ∈ thricePuncturedSphereReal, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (q : Puncture)
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
  {u : ℝ × ℝ → M}

/-! ### Breaking along a sequence at each end -/

/-- Beyond `a ≥ max T₀ 0`, `u ∘ φ'_q` satisfies the smoothness, periodicity, Floer-equation, and
finite-energy hypotheses of a positive Floer half-cylinder. -/
private theorem floer_halfCylinder_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
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
  have hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t) := fun q t x ↦
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  have humd : ∀ z ∈ thricePuncturedSphereReal, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn (fun z hz ↦ hmem z hz.1),
    fun s _ t ↦ by simp only [positiveEndChart_add_one], fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      humd q ha₀ haT)⟩
  have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le) (humd _ (hmem z hz.1)) (hfloer _ (hmem z hz.1))
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 hcl
  simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using hiff

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F} {B : Set M}

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `K` equal `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and
let `u` be `C¹` on `S = ℂ ∖ {0, 1}`, with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with finite energy, where the almost complex structures on the end
`q` are uniformly tame with respect to a `C¹` map `e : M → F` injective on `B` with injective
differential on `B`. Then there are a `1`-periodic orbit `y` of `X_{H_q}` in `B` and `σ_n → ∞` such
that `t ↦ u(φ_q(±σ_n, t))` converges to `y`, uniformly in `e` and pointwise on `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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
    (q : Puncture) {b c : ℝ} (hc : 0 < c)
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
    floer_halfCylinder_comp_positiveEndChart hKH hH hHs hu hfloer hE q ha₀ haT
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
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
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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
    (q : Puncture) {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE q hc hJc
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
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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
  obtain ⟨y, hy, hyB, σ, hσ, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      hB he_inj hde hu huB J hfloer hE q hc hJc
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  have hmemS {s : ℝ} (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hs)
  have huend : ContinuousOn (fun z : ℝ × ℝ ↦ u (endChart q (q.endSign * z.1, z.2)))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    hu.continuousOn.comp ((contDiff_endChart q 0).continuous.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)).continuousOn fun z hz ↦
      hmemS hz.1 z.2
  have hσ0 := hσ.eventually_gt_atTop 0
  have hyc : y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
    (mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp (I := I) hB
      he.continuous.continuousOn he_inj one_pos hy hyB
      (hσ0.mono fun n hn ↦ hu.continuousOn.comp_continuous
        ((contDiff_endChart q 0).continuous.comp (continuous_const.prodMk continuous_id))
        (hmemS hn))
      (Eventually.of_forall fun n t ↦ by simp only [comp_apply, id_eq, endChart_add_one])
      (hσ0.mono fun n hn t ↦ huB _ (hmemS hn t)) hux).2 <|
      hσ0.mono fun n hn ↦ (exists_nullhomotopic_slice_iff_of_isPreconnected I isPreconnected_Ioi
        huend one_pos (fun s _ t ↦ by simp only [endChart_add_one]) hs₀ hn).1 hnull₀
  exact ⟨y, hyc, hyB, σ, hσ, hux, hpt⟩

/-- **A contractible end of a finite-energy Floer pair of pants on a closed manifold breaks off a
contractible periodic orbit.** The specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`
to a compact manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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
      hKH hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J
      hfloer hE hc hJc
  exact ⟨y, hy, h⟩

/-! ### Whole-end convergence at nondegenerate ends -/

section NondegenerateEnds

variable [T2Space M] [BoundarylessManifold I M]

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate orbit.** Under
the hypotheses of `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
suppose that `M` is Hausdorff and boundaryless, `H_q` is jointly `C²`, `e ∘ u ∘ φ'_q` has bounded
derivative on `s > b`, and every `1`-periodic orbit `y` of `X_{H_q}` in `B` is nondegenerate (`y 0`
is a nondegenerate fixed point of `timeDependentFlowOf X_{H_q} 0 1`). Then `t ↦ u(φ_q(±s, t))`
converges as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`, uniformly in `e` and
pointwise on `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
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
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHs hu hfloer hE q ha₀ haT
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq2.of_le (by norm_num))
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
      (fun z hz ↦ hC z (hab z hz.1)) fun x hx hxB ↦ by
        have hx' := mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx
        have hnd₀ := hnd _ hx' (fun t ↦ hxB _)
        obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_eq_of_isNondegenerateFixedPt (s := 0) hX
          (fun t ↦ by rw [hH q t]) one_ne_zero hB he.continuous.continuousOn he_inj hx'
          (fun t ↦ hxB _) (by simpa only [zero_add] using hnd₀)
        refine ⟨ε, hε, fun y hy hyB hyx ↦ funext fun t ↦ ?_⟩
        have hxy := congrFun (hiso _ (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hy)
          (fun s ↦ hyB _) (by simpa only [mul_zero] using hyx 0)) (q.endSign * t)
        simpa only [← mul_assoc, endSign_mul_self, one_mul] using hxy
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp fun t ↦ q.endSign * t
  · simpa only [← endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants on a closed manifold to a nondegenerate
orbit.** The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_isCompact` to a compact manifold
`M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
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
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_isCompact hKH hH hHs hHq2 he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE
      (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, hux, hpt⟩

/-- **Convergence of a contractible end of a Floer pair of pants in a manifold to a nondegenerate
contractible orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_isCompact`, suppose that some end
loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic as a map `AddCircle 1 → M`, and assume
nondegeneracy only for the *contractible* `1`-periodic orbits of `X_{H_q}` in `B`. Then
`t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single contractible `1`-periodic orbit `y` of
`X_{H_q}` in `B`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
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
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHs hu hfloer hE q ha₀ haT
  -- Transfer null-homotopy from `s₀ > 0` to `a + 1 > a` across the preconnected half-line `(0, ∞)`.
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  have hnull₀' : ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s₀, t)) := by
    simpa only [positiveEndChart_mk] using exists_nullhomotopic_comp_endSign_mul q hnull₀
  have hu0c : ContinuousOn (fun z ↦ u (positiveEndChart q z)) (Ioi (0 : ℝ) ×ˢ univ) :=
    hu.continuousOn.comp (contDiff_positiveEndChart q 0).continuous.continuousOn fun z hz ↦
      positiveEndChart_mem_thricePuncturedSphereReal hz.1
  have hnulla : ∃ s₁ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s₁, t)) :=
    ⟨a + 1, lt_add_one a, (exists_nullhomotopic_slice_iff_of_isPreconnected I isPreconnected_Ioi
      hu0c one_pos (fun s _ t ↦ by simp only [positiveEndChart_add_one]) hs₀
      (add_pos_of_nonneg_of_pos ha₀ zero_lt_one)).1 hnull₀'⟩
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq2.of_le (by norm_num))
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      hnulla (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
      (fun z hz ↦ hC z (hab z hz.1)) fun x hx hxB ↦ by
        have hx' := mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx
        have hnd₀ := hnd _ hx' (fun t ↦ hxB _)
        obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_eq_of_isNondegenerateFixedPt (s := 0) hX
          (fun t ↦ by rw [hH q t]) one_ne_zero hB he.continuous.continuousOn he_inj
          (mem_contractiblePeriodicSolutions.1 hx').1 (fun t ↦ hxB _)
          (by simpa only [zero_add] using hnd₀)
        refine ⟨ε, hε, fun y hy hyB hyx ↦ funext fun t ↦ ?_⟩
        have hy' := mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hy
        have hxy := congrFun (hiso _ (mem_contractiblePeriodicSolutions.1 hy').1
          (fun s ↦ hyB _) (by simpa only [mul_zero] using hyx 0)) (q.endSign * t)
        simpa only [← mul_assoc, endSign_mul_self, one_mul] using hxy
  refine ⟨fun t ↦ x (q.endSign * t),
    mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx, fun t ↦ hxB _, ?_,
    fun t ↦ ?_⟩
  · simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp fun t ↦ q.endSign * t
  · simpa only [← endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of a contractible end on a closed manifold to a nondegenerate contractible
orbit.** The specialization to `[CompactSpace M]`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hHq2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
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
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_isCompact
      hKH hH hHs hHq2 he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _)
      hnull J hfloer hE (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, hux, hpt⟩

end NondegenerateEnds

end IsNondegenerate

end SmoothTwoForm

end TauCeti
