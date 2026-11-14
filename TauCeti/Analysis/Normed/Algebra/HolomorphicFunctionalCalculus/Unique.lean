/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Cauchy
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Spectrum
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniqueness of the holomorphic functional calculus

Any unital complex-algebra homomorphism `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` into a complex
Banach algebra `A` that sends the coordinate germ to `a` and whose restriction `Φ ∘ toGerm haV` to
every open neighbourhood `V` of `spectrum ℂ a` is continuous for the compact-open topology coincides
with `holomorphicCalculus a`.

The proof avoids Runge's theorem by working directly in the inductive system of open neighbourhoods
of `spectrum ℂ a`: given a representative `f : holomorphicFunctions U` on `spectrum ℂ a ⊆ U`,
`IsCompact.exists_open_segments_cycle_windingNumber_eq_one` produces a smaller open neighbourhood
`V` of `spectrum ℂ a` with `V ≤ U` and a polygonal cycle `Γ` carried on a finite segment family `E`
in `U \ V`. In `holomorphicFunctions V`, the rational Cauchy Riemann sums
`cauchyRiemannSum V (extend f) E hEV N` converge to `restrict hVU f`; applying `Φ ∘ toGerm haV`
turns each Cauchy kernel into a resolvent of `a`, and the resulting Banach-algebra Riemann sums
converge to the contour integral defining `holomorphicCalculusOn a U ha f`.

## Main results

* `TauCeti.algHom_toGerm_cauchyKernel` and `TauCeti.algHom_toGerm_cauchyRiemannSum`: any unital
  algebra homomorphism sending the coordinate germ to `a` maps Cauchy kernels outside `V` to
  resolvents of `a` and Cauchy Riemann sums on `V` to resolvent Riemann sums.
* `TauCeti.tendsto_algHom_toGerm_cauchyRiemannSum`: those resolvent Riemann sums converge in `A` to
  `holomorphicCalculusOn a U ha f`.
* `TauCeti.eq_holomorphicCalculus_of_forall_continuous` and
  `TauCeti.existsUnique_holomorphicCalculus`: uniqueness of `holomorphicCalculus a`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.4.
* N. Bourbaki, *Théories spectrales*, Ch. I, §4, No. 3, Théorème 1.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped Real

namespace TauCeti

open Contour HolomorphicFunctions

section Algebraic

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` maps the germ of `cauchyKernel V w hw` (on `spectrum ℂ a ⊆ V`) to
`resolvent a w`. -/
theorem algHom_toGerm_cauchyKernel {A : Type*} [Ring A] [Algebra ℂ A] {a : A}
    (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hid : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {V : Opens ℂ} (haV : spectrum ℂ a ⊆ V) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    Φ (toGerm haV (cauchyKernel V w hw)) = resolvent a w := by
  have hw_res : w ∈ resolventSet ℂ a := spectrum.notMem_iff.mp fun hwσ ↦ hw (haV hwσ)
  rw [cauchyKernel_def, toGerm_of,
    (holomorphicGerms.ofFun_eq_iff _ (analyticOnNhd_sub_inv hw_res)).mpr EventuallyEq.rfl]
  exact algHom_ofFun_sub_inv_eq_resolvent Φ hid hw_res

/-- Image of `cauchyRiemannSum` under `Φ ∘ toGerm haV` for any unital complex-algebra homomorphism
`Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ to `a`: every Cauchy
kernel term evaluates to the corresponding resolvent of `a`. -/
theorem algHom_toGerm_cauchyRiemannSum {A : Type*} [Ring A] [Algebra ℂ A] {a : A}
    (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hid : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {V : Opens ℂ} (haV : spectrum ℂ a ⊆ V) (g : ℂ → ℂ) (E : Finset (ℂ × ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (N : ℕ) :
    Φ (toGerm haV (cauchyRiemannSum V g E hEV N)) =
      (2 * π * I)⁻¹ • ∑ e ∈ E, ((e.2 - e.1) / (N + 1 : ℂ)) •
        ∑ k ∈ Finset.range (N + 1),
          g (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ))) •
            resolvent a (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ))) :=
  map_cauchyRiemannSum (Φ.comp (toGerm haV)) g E hEV (resolvent a)
    (fun _ hw ↦ algHom_toGerm_cauchyKernel Φ hid haV (hEV.notMem_of_mem_left hw)) N

end Algebraic

section BanachAlgebra

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Deduce the scalar `ℂ` segment-sum integral formula from a universe-`u` segment-sum integral
formula by embedding `ℂ` into `PUnit.{u + 1} → ℂ`. -/
private theorem integral_eq_sum_segments_complex {E : Finset (ℂ × ℂ)} {Γ : Cycle}
    (hΓ : Γ.IsIn (⋃ e ∈ E, segment ℝ e.1 e.2))
    (hint : ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] {g : ℂ → F},
      ContinuousOn g (⋃ e ∈ E, segment ℝ e.1 e.2) → Cycle.integral g Γ =
        ∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t))
    {g : ℂ → ℂ} (hg : ContinuousOn g (⋃ e ∈ E, segment ℝ e.1 e.2)) :
    Cycle.integral g Γ =
      ∑ e ∈ E, (e.2 - e.1) * ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t) := by
  let L : (PUnit.{u + 1} → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique PUnit.{u + 1} ℂ ℂ
  have hgL : ContinuousOn (fun z ↦ L.symm (g z)) (⋃ e ∈ E, segment ℝ e.1 e.2) :=
    L.symm.continuous.comp_continuousOn hg
  calc Cycle.integral g Γ
      = Cycle.integral (fun z ↦ L.toContinuousLinearMap (L.symm (g z))) Γ :=
          Cycle.integral_congr fun z _ ↦ (L.apply_symm_apply (g z)).symm
    _ = L (Cycle.integral (fun z ↦ L.symm (g z)) Γ) :=
          Cycle.integral_comp_comm
            (fun _ ↦ Cycle.intervalIntegrable_of_mem_support (hgL.mono (Cycle.isIn_iff.mp hΓ)))
            L.toContinuousLinearMap
    _ = L (∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, L.symm (g (AffineMap.lineMap e.1 e.2 t))) :=
          congrArg L (hint hgL)
    _ = ∑ e ∈ E, (e.2 - e.1) * ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun e _ ↦ ?_
          rw [map_smul, smul_eq_mul, ← L.intervalIntegral_comp_comm]
          simp only [L.apply_symm_apply]

/-- For any unital complex-algebra homomorphism `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A`
sending the coordinate germ to `a` (with no continuity assumption on `Φ`), the images of the Cauchy
Riemann sums of `f : holomorphicFunctions U` on `V ≤ U` converge in `A` to
`holomorphicCalculusOn a U (haV.trans hVU) f`. -/
theorem tendsto_algHom_toGerm_cauchyRiemannSum {a : A}
    (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hid : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {U V : Opens ℂ} (haV : spectrum ℂ a ⊆ V) (hVU : V ≤ U) (f : holomorphicFunctions U)
    (E : Finset (ℂ × ℂ)) (hEU : (⋃ e ∈ E, segment ℝ e.1 e.2) ⊆ (U : Set ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (Γ : Cycle)
    (hΓ : Γ.IsIn (⋃ e ∈ E, segment ℝ e.1 e.2)) (hn : Γ.IsNullHomologous U)
    (hw : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ = 1)
    (hint : ∀ {g : ℂ → A}, ContinuousOn g (⋃ e ∈ E, segment ℝ e.1 e.2) →
      Cycle.integral g Γ =
        ∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t)) :
    Tendsto (fun N ↦ Φ (toGerm haV (cauchyRiemannSum V (extend f) E hEV N))) atTop
      (𝓝 (holomorphicCalculusOn a U (haV.trans hVU) f)) := by
  let G : ℂ → A := fun z ↦ extend f z • resolvent a z
  have hG_cont : ContinuousOn G (⋃ e ∈ E, segment ℝ e.1 e.2) :=
    ((differentiableOn_extend f).continuousOn.mono hEU).smul
      ((spectrum.differentiableOn_resolvent a).continuousOn.mono fun _ hz ↦
        spectrum.notMem_iff.mp fun hσ ↦ hEV.notMem_of_mem_left hz (haV hσ))
  have hseg : ∀ e ∈ E, Tendsto
      (fun N : ℕ ↦ ((e.2 - e.1) / (N + 1 : ℂ)) •
        ∑ k ∈ Finset.range (N + 1),
          G (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ))))
      atTop (𝓝 ((e.2 - e.1) • ∫ t in (0 : ℝ)..1, G (AffineMap.lineMap e.1 e.2 t))) := fun e he ↦ by
    have hcont_e : ContinuousOn (fun t : ℝ ↦ G (AffineMap.lineMap (k := ℝ) e.1 e.2 t)) (Icc 0 1) :=
      hG_cont.comp (AffineMap.lineMap_continuous (R := ℝ) (p := e.1) (q := e.2)).continuousOn
        fun t ht ↦ mem_biUnion he (segment_eq_image_lineMap ℝ e.1 e.2 ▸ mem_image_of_mem _ ht)
    refine ((TauCeti.intervalIntegral.tendsto_riemannSum_zero_one hcont_e).const_smul
      (e.2 - e.1)).congr fun N ↦ ?_
    rw [← one_smul ℂ (∑ k ∈ _, _), ← smul_assoc (N + 1 : ℝ)⁻¹ (1 : ℂ), Complex.real_smul, mul_one,
      Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      smul_smul, ← div_eq_mul_inv, one_smul]
  have hΓ_in : Γ.IsIn ((U : Set ℂ) \ spectrum ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz ↦
      have hzE := Cycle.isIn_iff.mp hΓ hz
      ⟨hEU hzE, fun hσ ↦ hEV.notMem_of_mem_left hzE (haV hσ)⟩
  have hlim : holomorphicCalculusOn a U (haV.trans hVU) f =
      (2 * π * I)⁻¹ •
        ∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, G (AffineMap.lineMap e.1 e.2 t) := by
    rw [holomorphicCalculusOn_eq_integral a U (haV.trans hVU) f Γ hΓ_in hn hw, hint hG_cont]
  rw [hlim]
  exact ((tendsto_finsetSum E hseg).const_smul (2 * π * I)⁻¹).congr fun N ↦
    (algHom_toGerm_cauchyRiemannSum Φ hid haV (extend f) E hEV N).symm

/-- **Uniqueness of the holomorphic functional calculus.** Any unital complex-algebra homomorphism
`Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` that sends the coordinate germ to `a` and whose
restriction `Φ ∘ toGerm haV` to every open neighbourhood `V` of `spectrum ℂ a` is continuous for the
compact-open topology equals `holomorphicCalculus a`. -/
theorem eq_holomorphicCalculus_of_forall_continuous {a : A}
    (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hid : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hcont : ∀ (V : Opens ℂ) (haV : spectrum ℂ a ⊆ V), Continuous (Φ ∘ toGerm haV)) :
    Φ = holomorphicCalculus a := by
  apply holomorphicGerms.algHom_ext
  intro U haU f
  obtain ⟨V, haV, hVU, E, Γ, hEU, hEV, hΓ, hn, hw, hint⟩ :=
    (spectrum.isCompact a).exists_open_segments_cycle_windingNumber_eq_one.{u} U haU
  have h1 : Tendsto (fun N ↦ Φ (toGerm haV (cauchyRiemannSum V (extend f) E hEV N))) atTop
      (𝓝 (Φ (toGerm haU f))) := by
    have hlim := ((hcont V haV).tendsto (restrict hVU f)).comp
      (tendsto_cauchyRiemannSum hVU f E hEU hEV Γ hΓ hn hw
        (integral_eq_sum_segments_complex hΓ hint))
    rw [Function.comp_apply, toGerm_restrict haV hVU f] at hlim
    exact hlim
  have h2 := tendsto_algHom_toGerm_cauchyRiemannSum Φ hid haV hVU f E hEU hEV Γ hΓ hn
    (fun z hz ↦ hw z (haV hz)) hint
  simpa only [holomorphicCalculus_toGerm] using tendsto_nhds_unique h1 h2

/-- **Existence and uniqueness of the holomorphic functional calculus.** For every element `a` of a
complex Banach algebra `A`, `holomorphicCalculus a` is the unique unital complex-algebra
homomorphism `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ to `a` whose
restriction `Φ ∘ toGerm haV` to every open neighbourhood `V` of `spectrum ℂ a` is continuous for the
compact-open topology. -/
theorem existsUnique_holomorphicCalculus (a : A) :
    ∃! Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A,
      Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a ∧
        ∀ (V : Opens ℂ) (haV : spectrum ℂ a ⊆ V), Continuous (Φ ∘ toGerm haV) :=
  ⟨holomorphicCalculus a,
    ⟨holomorphicCalculus_id a, fun V haV ↦ by
      have heq : holomorphicCalculus a ∘ toGerm haV = holomorphicCalculusOn a V haV :=
        funext (holomorphicCalculus_toGerm a V haV)
      exact heq ▸ continuous_holomorphicCalculusOn a V haV⟩,
    fun Φ ⟨hid, hcont⟩ ↦ eq_holomorphicCalculus_of_forall_continuous Φ hid hcont⟩

end BanachAlgebra

end TauCeti
