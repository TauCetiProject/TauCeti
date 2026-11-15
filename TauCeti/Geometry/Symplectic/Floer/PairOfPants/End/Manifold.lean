/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Asymptotic orbits at the ends of a finite-energy Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `K` be a Hamiltonian perturbation on the pair of pants
`S = ℂ ∖ {0, 1}` with values in functions on `M`, equal to `H_q(t) dt` beyond some height `T₀` on
each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`. Let `u : S → M` be `C¹`, with image in a
compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` for almost complex structures
`J z` on the tangent spaces `T_{u z} M`, uniformly tame with respect to a `C¹` map `e : M → F` into
a finite-dimensional normed space which is injective with injective differential on `B`. This file
shows that if `u` has finite energy, then `u` breaks off a `1`-periodic orbit of `H_q` at each end
`q` (`IsNondegenerate.exists_mem_periodicSolutions_tendsto_endChart_of_floer_of_isCompact`, in the
namespace `TauCeti.SmoothTwoForm`): there are `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`
along the circles of the end, with the sign of the end, converge to the orbit, pointwise in `M` and
uniformly after applying `e`. On a compact manifold `B` can be the whole manifold
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendsto_endChart_of_floer`).
This is Floer breaking at the ends of a pair of pants for a manifold target, the first step of the
Gromov–Floer compactness of the moduli spaces defining the pair-of-pants product.
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` proves it for a symplectic vector space.

The proof reads each end as a Floer half-cylinder and applies
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`.

* In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`), the
  perturbation `K` becomes `H'_q(t) dt` beyond `T₀`, for the end Hamiltonian
  `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). Since `φ'_q` is holomorphic,
  `u ∘ φ'_q` solves the Floer equation `∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` of a half-cylinder
  there (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`).
* Since `φ'_q` preserves orientation and is injective on the band `ℝ × (0, 1)`, the energy of
  `u ∘ φ'_q` over a half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of
  `u` over `S` (`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`).
* Reading an orbit of `H'_q` with the time `±t` of the end gives an orbit of `H_q`
  (`SmoothTwoForm.comp_endSign_mul_mem_periodicSolutions`), because `X_{c H} = c X_H`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-- **Orbits in positive end charts.** Reading a `1`-periodic orbit of the end Hamiltonian `H'_q`
of the positive end chart with the time `±t` of the end gives a `1`-periodic orbit of `H_q`. -/
theorem comp_endSign_mul_mem_periodicSolutions {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
  refine mem_periodicSolutions.2 ⟨fun t ↦ ?_, periodic_comp_endSign_mul (q := q) hxper⟩
  -- `H'_q(±t) = ±H_q(t)`, and Hamiltonian vector fields are linear in the Hamiltonian.
  have hX : ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t))
      (x (q.endSign * t)) = q.endSign • ω.hamiltonianVectorField (H q t) (x (q.endSign * t)) := by
    rw [show positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t by
      funext y
      rw [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul, Pi.smul_apply,
        smul_eq_mul], hamiltonianVectorField_const_smul]
  have hmul : HasDerivAt (fun t : ℝ ↦ q.endSign * t) q.endSign t := by
    simpa using (hasDerivAt_id t).const_mul q.endSign
  have heq : ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField
      (positiveEndHamiltonian H q (q.endSign * t)) (x (q.endSign * t)))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ q.endSign) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) := by
    ext
    simp [hX, smul_smul]
  exact ((hxd (q.endSign * t)).comp t
    (hasMFDerivAt_iff_hasFDerivAt.2 hmul.hasFDerivAt)).congr_mfderiv heq

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the positive end chart are differentiable
in the target point when the end Hamiltonian is. -/
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
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x := by
    funext x
    rw [hKH q _ x hre, smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact (hHd q _ y).const_smul _

/-- On the positive end beyond `T₀`, the pulled-back perturbation is `H'_q(t) dt`. -/
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
        (u ∘ positiveEndChart q) ζ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply,
    funext (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ),
    funext (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ)]

/-- **The ends of a Floer pair of pants in a manifold solve the Floer equation of a
half-cylinder.** Let `K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve the
Floer equation `(du - X_K)^{0,1} = 0` for the almost complex structure `J` on `T_{u(φ'_q ζ)} M` at
the image `φ'_q(ζ)` of a point `ζ` with `s ≥ T₀` of the positive end chart. Then the map `u ∘ φ'_q`
solves the Floer equation `∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` of a half-cylinder at `ζ`, for the
end Hamiltonian `H'_q` of the positive end. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {q : Puncture} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
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

/-- **The energy of an end of a Floer pair of pants in a manifold.** Let `K` be equal to
`H_q(t) dt` beyond `T₀` on each end `q`, and let `u` be differentiable on `S`. Then the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]`, for
`a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  -- The closed band differs from the open one by a null set.
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  -- On the open band the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * e (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hζ.1)
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      ((hu _ hS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `ω`
be a nondegenerate two-form on `M`, let `K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for
`1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be `C¹` on `S`, with image in a compact set `B`,
solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a `C¹` map into a
finite-dimensional normed space, injective on `B` and with injective differential at the points of
`B`, and suppose that the almost complex structures are uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `S` is finite, then at each end
`q` there are a `1`-periodic orbit `y` of the Hamiltonian vector field of `H_q` in `B` and
`s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`,
pointwise in `M` and uniformly after applying `e`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendsto_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  have hHd (q : Puncture) (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : max T₀ 0 < z.1) :
      positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
  have hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal :=
    hu.mdifferentiableOn one_ne_zero
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder.
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  have hfloer' (z : ℝ × ℝ) (hz : z ∈ Ioi (max T₀ 0) ×ˢ Icc 0 1) :
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineReal +
        J' z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z
          stdComplexLineImag - ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
            ((u ∘ positiveEndChart q) z)) = 0 := by
    have h := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ _ _ _).1
      (isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
        ((le_max_left _ _).trans hz.1.le)
        ((hud _ (hmem hz.1)).mdifferentiableAt
          (isOpen_thricePuncturedSphereReal.mem_nhds (hmem hz.1)))
        (hfloer _ (hmem hz.1)))
    simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using h
  obtain ⟨x, hx, hxB, φ, -, hφ, hux, hconv, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦ hmem hz.1)
      (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem hs)) J' hc
      (fun z hz v ↦ hJc _ (hmem hz.1) v) hfloer'
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH
        hHd hud q (le_max_right _ _) (le_max_left _ _)))
  -- Read the orbit and the loops back in the end chart, with the time `±t` of the end.
  refine ⟨fun t ↦ x (q.endSign * t), comp_endSign_mul_mem_periodicSolutions hx,
    fun t ↦ hxB _, φ, hφ, ?_, fun t ↦ ?_⟩
  · have h := hux.comp fun t ↦ q.endSign * t
    simpa only [comp_def, endChart_eq_positiveEndChart] using h
  · simpa only [endChart_eq_positiveEndChart, comp_apply] using hconv (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
Let `ω` be a nondegenerate two-form on a compact manifold `M`, let `K` be equal to `H_q(t) dt`
beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be `C¹` on `S`,
solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a `C¹` injective map
with injective differential into a finite-dimensional normed space, and suppose that the almost
complex structures are uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`.
If the energy of `u` over `S` is finite, then at each end `q` there are a `1`-periodic orbit `y` of
the Hamiltonian vector field of `H_q` and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with
the sign of the end, converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendsto_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendsto_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE q
  exact ⟨y, hy, h⟩

end SmoothTwoForm

end TauCeti
