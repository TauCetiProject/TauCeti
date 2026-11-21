/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.CauchyRiemann
import TauCeti.Topology.Constructions.SumProd

/-!
# The semi-Fredholm estimate of the linearized Floer operator on a cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `D_u` be the linearized Floer
operator (`TauCeti.SymplecticForm.floerLinearization`) along a map `u : ℝ × ℝ → V` of period one
in `t`. The Fredholm property of `D_u` on the cylinder `ℝ × S¹` rests on the estimate

`‖ξ‖²_{W^{1,2}} ≤ C (‖D_u ξ‖²_{L²} + ‖ξ‖²_{L²([-T, T] × S¹)})`

for sections `ξ` of compact support, with `C` and `T` independent of `ξ`. Since restriction to
the compact cylinder `[-T, T] × S¹` is compact from `W^{1,2}` to `L²`, Peetre's compact-error
estimate (`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`) turns such an estimate
into finite dimensional kernel and closed range of the extension of `D_u` to `W^{1,2}`.

The operator `D_u` is the real Cauchy–Riemann operator `∂s + J(z, u z) ∂t + A(z)` with zeroth-order
part `A = floerLinearizationCoeff` (`TauCeti.SymplecticForm.floerLinearization_eq_add`), so the
estimate follows by patching estimates on the two ends with the interior estimate on a compact
cylinder, as for every such operator
(`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_ends`,
in `TauCeti.Geometry.Symplectic.Floer.SemiFredholm.CauchyRiemann`). On the far parts of the ends,
where `u` is close to a nondegenerate orbit, `D_u` controls the whole `W^{1,2}` norm
(`TauCeti.SymplecticForm.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization`).

* `exists_setIntegral_norm_fderiv_sq_le_floerLinearization` is the interior estimate on any
  compact set `K`: for `J` compatible along `u`, `D_u` controls the `L²` norm of the derivatives of
  sections supported in `K`, up to their `L²` norm on `K`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_ends` is the patching
  argument for `D_u`: for any data `J`, `K_s`, `K_t` that are regular along `u`, with `J`
  compatible along `u`, estimates of `D_u` on the two ends imply the semi-Fredholm estimate.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical` is the
  semi-Fredholm estimate for Floer data that are cylindrical near the ends
  (`TauCeti.Floer.IsCylindricalNearEnds`): the data are
  `(J₋_t, 0, H₋_t)` for `s ≤ -R` and `(J₊_t, 0, H₊_t)` for `s ≥ R`, possibly with different
  Hamiltonians and almost complex structures at the two ends, as for a continuation cylinder, and
  `u` is asymptotic at `±∞` to nondegenerate one-periodic orbits of `H±`. Beyond `±R` the operator
  `D_u` is the operator of the end data
  (`TauCeti.SymplecticForm.floerLinearization_congr_data`), so its end estimates are those of
  `exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq`, in the norm of
  `V`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add` is the case of a Floer
  trajectory: `K = H_t dt` with `J_t` independent of `s`, which is cylindrical with `R = 0`
  (`TauCeti.Floer.isCylindricalNearEnds_comp_snd`).

Sections are `C²` maps `ξ : ℝ × ℝ → V` of period one in `t` that vanish outside a strip
`(a, b) × ℝ`, and the integrals are over the fundamental domain `[a, b] × [0, 1]`. The Sobolev
completion and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` along a Floer
  trajectory.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate.
-/

public section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open scoped NNReal Manifold

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Floer data `(J, K_s, K_t)` on the cylinder are **cylindrical near the ends along `u`**, with end
data `(J₋, H₋)`, `(J₊, H₊)` and radius `R`, when they agree with the cylindrical data
`(J₋_t, 0, H₋_t)` for `s ≤ -R` and with `(J₊_t, 0, H₊_t)` for `s ≥ R`, and when `J` is `C¹` and
`K_s`, `K_t` are `C²` at the points `(z, u z)` of the graph of `u`. Floer trajectories are the
case `R = 0` (`TauCeti.Floer.isCylindricalNearEnds_comp_snd`), and continuation cylinders the case
`R = 1`. -/
structure IsCylindricalNearEnds (J : ℝ × ℝ → V → AlmostComplexStructure V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (Jm Jp : ℝ → V → AlmostComplexStructure V) (Hm Hp : ℝ → V → ℝ)
    (R : ℝ) (u : ℝ × ℝ → V) : Prop where
  /-- For `s ≤ -R` the almost complex structures are those of the negative end. -/
  almostComplex_eq_of_le_neg : ∀ z : ℝ × ℝ, z.1 ≤ -R → J z = Jm z.2
  /-- For `s ≥ R` the almost complex structures are those of the positive end. -/
  almostComplex_eq_of_le : ∀ z : ℝ × ℝ, R ≤ z.1 → J z = Jp z.2
  /-- Outside `(-R, R)` the `ds` part of the datum vanishes. -/
  hamiltonianS_eq_zero : ∀ z : ℝ × ℝ, z.1 ∉ Ioo (-R) R → Ks z = 0
  /-- For `s ≤ -R` the `dt` part of the datum is the Hamiltonian of the negative end. -/
  hamiltonianT_eq_of_le_neg : ∀ z : ℝ × ℝ, z.1 ≤ -R → Kt z = Hm z.2
  /-- For `s ≥ R` the `dt` part of the datum is the Hamiltonian of the positive end. -/
  hamiltonianT_eq_of_le : ∀ z : ℝ × ℝ, R ≤ z.1 → Kt z = Hp z.2
  /-- The almost complex structures are `C¹` along the graph of `u`. -/
  contDiffAt_almostComplex : ∀ z, ContDiffAt ℝ 1
    (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z)
  /-- The `ds` part of the datum is `C²` along the graph of `u`. -/
  contDiffAt_hamiltonianS : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z)
  /-- The `dt` part of the datum is `C²` along the graph of `u`. -/
  contDiffAt_hamiltonianT : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)

/-- The data `(J_t, 0, H_t)` of a Floer trajectory, for a `C¹` family `J_t(y)` of almost complex
structures and a jointly `C²` Hamiltonian `H`, are cylindrical near the ends with radius `0` and
end data `(J, H)` at both ends, along any map `u`. -/
theorem isCylindricalNearEnds_comp_snd {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (u : ℝ × ℝ → V) :
    IsCylindricalNearEnds (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2) J J H H 0 u where
  almostComplex_eq_of_le_neg _ _ := rfl
  almostComplex_eq_of_le _ _ := rfl
  hamiltonianS_eq_zero _ _ := rfl
  hamiltonianT_eq_of_le_neg _ _ := rfl
  hamiltonianT_eq_of_le _ _ := rfl
  contDiffAt_almostComplex _ := (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
  contDiffAt_hamiltonianS _ := contDiffAt_const
  contDiffAt_hamiltonianT _ := (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt

end TauCeti.Floer

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `L²` estimate on a compact set.** If `J` is compatible along `u`, then on sections
supported in a compact set `K` the operator `D_u` controls the derivatives in `L²`, up to the `L²`
norm on `K`: `∫_K (‖∂s η‖² + ‖∂t η‖²) ≤ C (∫ ‖D_u η‖² + ∫_K ‖η‖²)`. This is the `L²` estimate of a
Cauchy–Riemann operator with domain-dependent compatible structure, for `D_u = ∂s + J ∂t + A`. -/
theorem exists_setIntegral_norm_fderiv_sq_le_floerLinearization (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → tsupport η ⊆ K →
      ∫ z in K, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u η z‖ ^ 2) + ∫ z in K, ‖η z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨C, hC, hcore⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_tsupport_subset
    (μ := volume) (J := fun z ↦ J z (u z)) hK (fun z _ ↦ hc z)
    (continuous_comp_prodMk_of_continuousAt (fun z ↦ (hJ z).continuousAt)
      hu.continuous).continuousOn
    (ω.continuousOn_floerLinearizationCoeff (J := J') (fun z _ ↦ hJ z) (fun z _ ↦ hKs z)
      (fun z _ ↦ hKt z) fun z _ ↦ hu.contDiffAt)
  refine ⟨C, hC, fun η hη hηK ↦ ?_⟩
  have hD : Continuous fun z ↦ ‖ω.floerLinearization J' Ks Kt u η z‖ ^ 2 :=
    ((ω.continuous_floerLinearization (J := J') hJ hKs hKt hu (hη.of_le one_le_two)).norm.pow 2)
  have hη2 : Continuous fun z ↦ ‖η z‖ ^ 2 := hη.continuous.norm.pow 2
  -- `∂s η + J ∂t η + A η` is `D η`, and `∫_K ‖D η‖² ≤ ∫ ‖D η‖²`.
  have hDeq (z : ℝ × ℝ) : fderiv ℝ η z stdComplexLineReal +
      J z (u z) (fderiv ℝ η z stdComplexLineImag) +
        ω.floerLinearizationCoeff J' Ks Kt u z (η z) =
      ω.floerLinearization J' Ks Kt u η z := by
    simp only [floerLinearization_eq_add, J', LinearMap.coe_toContinuousLinearMap']
  have h := hcore hη hηK
  simp only [hDeq] at h
  rw [integral_add (hD.continuousOn.integrableOn_compact hK)
    (hη2.continuousOn.integrableOn_compact hK)] at h
  have hηc : HasCompactSupport η := hK.of_isClosed_subset (isClosed_tsupport η) hηK
  refine h.trans (mul_le_mul_of_nonneg_left (add_le_add_left (setIntegral_le_integral
    (ω.integrable_norm_floerLinearization_sq (J := J') hJ hKs hKt hu (hη.of_le one_le_two) hηc)
    (Eventually.of_forall fun _ ↦ by positivity)) _) hC)

/-- **Patching end estimates into the semi-Fredholm estimate.** Let `J(z)` be compatible along
`u`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹`. Suppose that the
linearized Floer operator `D_u` controls the `W^{1,2}` norm on the two ends: there are constants
`Cp`, `Cm` such that every `C²` map `ξ` of period one in `t`, vanishing on two slices `s = a ≤ b`
with `Rp ≤ a`, respectively with `b ≤ Rm`, satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ Cp ∫ ‖D_u ξ‖²`, respectively `≤ Cm ∫ ‖D_u ξ‖²`, over
`[a, b] × [0, 1]`. Then there are `C ≥ 0` and
`T` such that every `C²` map `ξ` of period one in `t` vanishing for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {Cp Cm Rp Rm : ℝ}
    (hp : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, Rp ≤ a → a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cp * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2)
    (hm : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → b ≤ Rm → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cm * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  -- `D_u` is the real Cauchy–Riemann operator with coefficients `J(z, u z)` and its zeroth-order
  -- part.
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  have hJc : Continuous fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap :=
    continuous_comp_prodMk_of_continuousAt (fun z ↦ (hJ z).continuousAt) hu.continuous
  have hAc : Continuous (ω.floerLinearizationCoeff J' Ks Kt u) :=
    continuousOn_univ.1 (ω.continuousOn_floerLinearizationCoeff (fun z _ ↦ hJ z)
      (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) fun z _ ↦ hu.contDiffAt)
  have hD (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : ω.floerLinearization J' Ks Kt u ξ z =
      fderiv ℝ ξ z stdComplexLineReal + J z (u z) (fderiv ℝ ξ z stdComplexLineImag) +
        ω.floerLinearizationCoeff J' Ks Kt u z (ξ z) := by
    simp only [floerLinearization_eq_add, J', LinearMap.coe_toContinuousLinearMap']
  simp only [hD] at hp hm ⊢
  exact ω.exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_ends
    (J := fun z ↦ J z (u z)) hc hJc hAc hp hm

/-- **The semi-Fredholm estimate for Floer data that are cylindrical near the ends.** Let
`J(z)`, `K_s`, `K_t` be Floer data on the cylinder that agree with the cylindrical data
`(J₋_t, 0, H₋_t)` for `s ≤ -R` and with `(J₊_t, 0, H₊_t)` for `s ≥ R`, as for a continuation
cylinder from `H₋` to `H₊`. Suppose that `J` is `C¹` and `K_s`, `K_t` are `C²` at the points
`(z, u z)`, where `u` is a `C¹` map along which `J` is `ω`-compatible. Let the end Hamiltonians
`H±` be jointly `C²` with globally Lipschitz suspended vector fields, the end structures `J±_t(y)`
be `C¹` families compatible along orbits `x±` of `H±` that start at nondegenerate fixed points of
the time-one maps, and let the loops of `u` converge uniformly to `xm` at `-∞` and to `xp` at
`+∞` while the slice defects `∂t u - X_{H±_t}(u)` tend uniformly to zero there. Then there are
`C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)`
satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (J z (u z))) {Km : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 2 (Function.uncurry Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1)) {Kp : ℝ≥0}
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxp : ∀ t, ω.Compatible (Jp t (xp t)))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  have hu' (l : Filter ℝ) : ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 u (s, t) :=
    Eventually.of_forall fun _ _ _ ↦ hu.contDiffAt
  obtain ⟨Cp, -, Up, hUp, hp⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq hXp hHp hxp hndp
      hJp hJxp (hu' atTop) huxp hδp
  obtain ⟨Cm, -, Um, hUm, hm⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq hXm hHm hxm hndm
      hJm hJxm (hu' atBot) huxm hδm
  obtain ⟨Rp, hRp⟩ := mem_atTop_sets.1 hUp
  obtain ⟨Rm, hRm⟩ := mem_atBot_sets.1 hUm
  -- Beyond `R` the operator of `(J, K_s, K_t)` is the operator of the cylindrical end data.
  have hD {J' : ℝ → V → AlmostComplexStructure V} {H : ℝ → V → ℝ} {ξ : ℝ × ℝ → V} {S : Set ℝ}
      (hS : ∀ s ∈ S, s ∉ Ioo (-R) R) (hJS : ∀ z : ℝ × ℝ, z.1 ∈ S → J z = J' z.2)
      (hKtS : ∀ z : ℝ × ℝ, z.1 ∈ S → Kt z = H z.2) :
      EqOn (fun z ↦ ‖ω.floerLinearization (fun w y ↦ (J' w.2 y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z‖ ^ 2)
        (fun z ↦ ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) (S ×ˢ Icc (0 : ℝ) 1) := fun z hz ↦ by
    beta_reduce
    rw [ω.floerLinearization_congr_data (Ks' := Ks) (Kt' := Kt)
      (J' := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u ξ ?_
      (hcyl.hamiltonianS_eq_zero z (hS z.1 hz.1)).symm (hKtS z hz.1).symm]
    simp only [hJS z hz.1]
  refine ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_ends
    hcyl.contDiffAt_almostComplex hcyl.contDiffAt_hamiltonianS hcyl.contDiffAt_hamiltonianT hu hJu
    (Cp := Cp) (Cm := Cm) (Rp := max Rp R) (Rm := min Rm (-R))
    (fun ξ hξ hper a b ha hab hsa hsb ↦ ?_) (fun ξ hξ hper a b hab hb hsa hsb ↦ ?_)
  · have hR : ∀ s ∈ Icc a b, R ≤ s := fun s hs ↦ (le_max_right Rp R).trans (ha.trans hs.1)
    refine (hp hξ hper hab (fun s hs ↦ hRp s ((le_max_left Rp R).trans (ha.trans hs.1))) hsa
      hsb).trans_eq ?_
    rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      (hD (fun s hs h ↦ (hR s hs).not_gt h.2)
        (fun z hz ↦ hcyl.almostComplex_eq_of_le z (hR _ hz))
        (fun z hz ↦ hcyl.hamiltonianT_eq_of_le z (hR _ hz)))]
  · have hR : ∀ s ∈ Icc a b, s ≤ -R := fun s hs ↦ hs.2.trans (hb.trans (min_le_right Rm _))
    refine (hm hξ hper hab (fun s hs ↦ hRm s (hs.2.trans (hb.trans (min_le_left Rm _)))) hsa
      hsb).trans_eq ?_
    rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      (hD (fun s hs h ↦ (hR s hs).not_gt h.1)
        (fun z hz ↦ hcyl.almostComplex_eq_of_le_neg z (hR _ hz))
        (fun z hz ↦ hcyl.hamiltonianT_eq_of_le_neg z (hR _ hz)))]

/-- **The semi-Fredholm estimate along a Floer trajectory.** Let `H` be a jointly `C²`
Hamiltonian whose suspended vector field is globally Lipschitz, and let `J_t(y)` be a `C¹` family
of almost complex structures. Let `u : ℝ × ℝ → V` be a `C¹` map along which `J_t` is
`ω`-compatible, whose loops converge uniformly to orbits `xm` at `-∞` and `xp` at `+∞` starting at
nondegenerate fixed points of the time-one map, as for nondegenerate one-periodic orbits of a
one-periodic Hamiltonian, with `J_t` compatible along them, while its slice defect
`∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as for a Floer trajectory from `xm` to
`xp`. Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that
vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z‖ ^ 2) + ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (Floer.isCylindricalNearEnds_comp_snd hJ hH u) hu hJu hX hH hxm hndm hJ hJxm huxm hδm hX hH hxp
    hndp hJ hJxp huxp hδp

end TauCeti.SymplecticForm
