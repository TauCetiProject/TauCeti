/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Manifold
import TauCeti.Order.Interval.Set.Prod

/-!
# Compactness along the end of PSS planes

The Piunikhin–Salamon–Schwarz maps count solutions `u : ℂ → X` of the perturbed Cauchy–Riemann
equation `(du - X_K)^{0,1} = 0` for the perturbation `K` of a PSS plane `p`
(`TauCeti.Floer.PSSPlane.perturbation`), built from a period-one Hamiltonian `H`. The compactness
theorems of `TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.Basic` apply on a fixed compact
window of the plane. Breaking along the end concerns windows that move off to `∞` instead: a
sequence of solutions `uₖ` is read along the end at heights `Rₖ`, through the translated ends

`vₖ(s, t) = uₖ(φ(s + Rₖ, t))`,

where `φ(s, t) = exp (2π (s + i t))` is the end lift of the positive plane in real coordinates.
These windows are where Floer cylinders break off when `Rₖ → ∞`.

Both planes are read in the coordinates of the positive plane: the perturbation of a plane `p`
with end sign `ε` given by `H` is the perturbation of the positive plane given by the Hamiltonian
`H'(t) = ε H(ε t)` (`TauCeti.Floer.PSSPlane.perturbation_eq_positive`), which is `H` for the
positive plane and `-H(-t)` for the negative plane. This file proves that the `vₖ` converge off
finitely many bubbling points, uniformly in the heights, from two facts.

* **One equation for all heights.** Beyond `s = 2` the perturbation of the positive plane pulls
  back to the cylindrical datum `H'(t) dt` along `φ`
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive`). It does
  not depend on `s`, so if the almost complex structures `J` are cylindrical far out on the end,
  `J(φ(s, t), x) = J_∞(t, x)` for `s ≥ T₀`, every translated end `vₖ` solves the same Floer
  equation for `H'(t) dt` and `J_∞`, whatever the height.
* **Energy.** The energy of a translated end over a window of angular width one is the energy of
  `uₖ ∘ φ` over the translated window, so it is at most the energy of `uₖ` over the plane
  (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_add_le`).

The compactness theorem for Floer solutions of bounded energy therefore applies to the `vₖ` on a
fixed window, with a threshold `δ` that does not depend on the heights.

The results are stated for a fixed compact window `D ⊆ (max T₀ 2, ∞) × (t₀, t₀ + 1)`, of angular
width less than one so that `φ` is injective on it; two such windows cover any compact part of the
half-cylinder.

* **Vector-space targets.** For a symplectic vector space `(V, ω)` and a compact set `B ⊆ V` there
  is `δ > 0` such that for all heights `Rₖ ≥ 0` and every sequence of solutions with energy at
  most `E` and `vₖ(Ω) ⊆ B`, a subsequence of the `vₖ` converges locally uniformly on `Ω` off a
  finite set `Z` with `#Z * δ ≤ E`
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_realChart_positive_add` in
  the namespace `TauCeti.SymplecticForm`).
* **Symplectic charts of a manifold.** The same holds for solutions in a manifold `M` whose
  translated ends map `Ω` into a compact subset `C` of the source of a symplectic chart; the
  coordinate maps converge locally uniformly off `Z`, and the maps converge pointwise in `M`
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_realChart_positive_add` in
  the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`).

For smooth solutions the limit is a Floer cylinder: the convergence holds in `C¹` off `Z`, and the
limit `v` is a `C¹` solution on `Ω \ Z` of the Floer equation for the cylindrical datum
`ε H(ε t) dt` and the structures `J_∞(t)`, with energy over `Ω \ Z` at most `E`. In a symplectic
chart the coordinate maps and their derivatives converge. These are
`exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_realChart_positive_add`
in the namespaces `TauCeti.SymplecticForm` and `TauCeti.SmoothTwoForm.IsNondegenerate`. They follow
from the `C¹` compactness theorems for fixed data,
`exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset` in the same two namespaces,
applied to the translated ends.

For solutions whose end loops have actions converging to `aₖ` with `ε aₖ ≤ A`, and `|H| ≤ b`, the
energy is at most `A + b`
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_le` and
`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_le`).
The bubbles at the points of `Z`, and the assembly of the levels into a broken configuration, are
not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on Floer breaking at the ends.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Chapter 12 (the PSS isomorphism).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.Complex (realChart contDiff_realChart)
open scoped Manifold

namespace TauCeti

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : ℝ → V → ℝ}

/-- **A translated end of the positive plane.** Let `u` be a `C³` solution on the plane of the
Floer equation for the perturbation of the positive plane given by `H`, with energy at most `E`,
for structures `J` with `J(φ(s, t), x) = J_∞(t, x)` for `s ≥ T₀`. If the translate by `(R, 0)` of
an open set `Ω` lies in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` and `v(z) = u(φ(z + (R, 0)))` maps
`Ω` into a set on which `J_∞(t)` is tamed by `ω` for `(s, t) ∈ Ω`, then `v` is `C³`, solves the
Floer equation for `H(t) dt` and `J_∞` on `Ω`, and its energy density is integrable on `Ω` with
integral at most `E`. -/
private theorem contDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {T₀ : ℝ} {Jend : ℝ → V → AlmostComplexStructure V}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    {B : Set V} {Ω : Set (ℝ × ℝ)} (hJt : ∀ z ∈ Ω, ∀ x ∈ B, ω.Tames (Jend z.2 x)) (hΩ : IsOpen Ω)
    {u : ℝ × ℝ → V} {R E t₀ : ℝ}
    (hΩT : ∀ z ∈ Ω, z + (R, 0) ∈ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1)) (hu : ContDiff ℝ 3 u)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedFDeriv (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE0 : 0 ≤ E)
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x I) u z) ≤ ENNReal.ofReal E)
    (huB : MapsTo (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) Ω B) :
    ContDiff ℝ 3 (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) ∧
      (∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jend z.2 (u (realChart positive.cylindricalEndLift (z + (R, 0)))))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0))))) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) z ≤ E := by
  set e := realChart positive.cylindricalEndLift
  set v : ℝ × ℝ → V := fun z ↦ u (e (z + (R, 0)))
  have hvC : ContDiff ℝ 3 v :=
    hu.comp ((contDiff_realChart positive.contDiff_cylindricalEndLift).comp
      (contDiff_id.add contDiff_const))
  -- Beyond `T₀` the structure is `J_∞(t)` and beyond `2` the datum is `H(t) dt`, so `v` solves the
  -- cylindrical equation.
  have hvfl (z : ℝ × ℝ) (hz : z ∈ Ω) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (Jend z.2 (v z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z : ℝ × ℝ →ₗ[ℝ] V) := by
    obtain ⟨h₁, -⟩ := hΩT z hz
    have h := ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive hH
      (hHs.of_le (by norm_num)) ((le_max_right _ _).trans (mem_Ioi.1 h₁).le)
      (hu.differentiable (by norm_num) _) (hfl (e (z + (R, 0))))
    rw [hJ _ _ _ ((le_max_left _ _).trans (mem_Ioi.1 h₁).le)] at h
    have heq := ω.perturbedFDeriv_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ e) (R, 0) z
    simp only [Prod.snd_add, add_zero, comp_apply] at heq
    rw [heq]
    simpa using h
  -- The energy of `v` over `Ω` is at most the energy of `u` over the plane.
  have hlin : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) ≤
      ENNReal.ofReal E :=
    (ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_add_le hH (hHs.of_le (by norm_num))
      (t₀ := t₀) le_rfl (hu.differentiable (by norm_num)).differentiableOn R
      hΩ.measurableSet fun z hz ↦ ⟨(le_max_right _ _).trans_lt (hΩT z hz).1,
        Ioo_subset_Ico_self (hΩT z hz).2⟩).trans ((setLIntegral_le_lintegral _ _).trans hE)
  have hKt : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ H w.2) :=
    (hHs.of_le (by norm_num)).comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  exact ⟨hvC, hvfl, ω.integrableOn_and_setIntegral_floerEnergyDensity_le hΩ hΩ.measurableSet
    subset_rfl (hvC.of_le (by norm_num)).contDiffOn contDiffOn_const hKt.contDiffOn
    (fun z hz ↦ ω.floerEnergyDensity_nonneg (hJt z hz _ (huB hz)) (hvfl z hz)) hE0 hlin⟩

/-- **The translated ends of PSS planes converge off finitely many bubbling points.** Let `p` be a
PSS plane with end sign `ε`, `H` a period-one `C³` Hamiltonian on `V`, and `J(z, x)` structures on
`V` which are cylindrical far out on the end, `J(φ(s, t), x) = J_∞(t, x)` for `s ≥ T₀`, where `φ`
is the end lift of the positive plane in real coordinates. Fix compact sets
`D ⊆ (max T₀ 2, ∞) × (t₀, t₀ + 1)` and `B ⊆ V`, and let `J_∞(t, x)` be tamed by `ω` for
`(s, t) ∈ D` and `x ∈ B`, with `((s, t), x) ↦ J_∞(t, x)` `C²` on an open set containing `D × B`.
There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions on the plane
of the Floer equation for `J(z, u)` and the perturbation of `p` given by `H`, with energy at most
`E ≥ 0`, let `Rₖ ≥ 0` be heights, and let the translated ends `vₖ(z) = uₖ(φ(z + (Rₖ, 0)))` map an
open `Ω ⊆ D` into `B`. Then there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`,
and a continuous `v : Ω \ Z → B` such that along `ψ` every disc about a point of `Z` eventually
carries energy at least `δ` for the cylindrical datum `ε H(ε t) dt`, the differentials of the `vₖ`
are uniformly bounded on every compact subset of `Ω \ Z`, and `v_{ψ n} → v` locally uniformly on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_realChart_positive_add
    (ω : SymplecticForm V) (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {T₀ : ℝ} {Jend : ℝ → V → AlmostComplexStructure V}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {B : Set V} {t₀ : ℝ}
    (hJt : ∀ z ∈ D, ∀ x ∈ B, ω.Tames (Jend z.2 x)) (hW : IsOpen W)
    (hJend : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (Jend q.1.2 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hDT : D ⊆ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1)) (hB : IsCompact B)
    (hDBW : D ×ˢ B ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u k) z
          : ℝ × ℝ →ₗ[ℝ] V)) →
      0 ≤ E →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u k) z) ≤
          ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (realChart positive.cylindricalEndLift (z + (R k, 0)))) Ω B) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
          (fun z ↦ u (ψ n) (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ L, ∀ n, ∀ y ∈ C,
          ‖fderiv ℝ (fun z ↦ u (ψ n) (realChart positive.cylindricalEndLift
            (z + (R (ψ n), 0)))) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) B ∧
        TendstoLocallyUniformlyOn (fun n z ↦ u (ψ n) (realChart positive.cylindricalEndLift
          (z + (R (ψ n), 0)))) v atTop (Ω \ ↑Z) := by
  -- The plane `p` is the positive plane for the Hamiltonian `ε H(ε t)`.
  have hHs' : ContDiff ℝ 3 (uncurry fun t x ↦ p.endSign * H (p.endSign * t) x) :=
    contDiff_const.mul (hHs.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))
  -- The cylindrical datum `ε H(ε t) dt` and the structures `J_∞(t)` of the end are smooth.
  have hKt : ContDiff ℝ 3 (uncurry fun (w : ℝ × ℝ) x ↦ p.endSign * H (p.endSign * w.2) x) :=
    hHs'.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (J := fun z ↦ Jend z.2) hW contDiffOn_const hKt.contDiffOn hJend hD hB
    hDBW hJt
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huB ↦ ?_⟩
  rw [perturbation_eq_positive p H] at hfl hE
  -- The translated windows lie in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` of the end.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have h (k : ℕ) :=
    contDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add ω
      (p.periodic_endSign_mul hH) hHs' hJ (fun z hz ↦ hJt z (hΩD hz)) hΩ (hΩT k) (hu k) (hfl k) hE0
      (hE k) (huB k)
  exact hconv hΩ hΩD (fun k ↦ (h k).1.contDiffOn) (fun k ↦ (h k).2.1) huB (fun k ↦ (h k).2.2.1)
    fun k ↦ (h k).2.2.2

/-- **The translated ends of smooth PSS planes converge in `C¹` off finitely many bubbling points to
a Floer cylinder.** Under the hypotheses of
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_realChart_positive_add`, there
is a threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions on the plane of
the Floer equation for `J(z, u)` and the perturbation of `p` given by `H`, with energy at most
`E ≥ 0`, let `Rₖ ≥ 0` be heights, and let the translated ends `vₖ(z) = uₖ(φ(z + (Rₖ, 0)))` map an
open `Ω ⊆ D` into `B`. Then there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`,
and a map `v : Ω \ Z → B` such that along `ψ` every disc about a point of `Z` eventually carries
energy at least `δ` for the cylindrical datum `ε H(ε t) dt`, `v_{ψ n} → v` and `dv_{ψ n} → dv`
locally uniformly on `Ω \ Z`, `v` is a `C¹` solution on `Ω \ Z` of the Floer equation for the datum
`ε H(ε t) dt` and the structures `J_∞(t)`, and the energy of `v` over `Ω \ Z` is finite and at most
`E`. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_realChart_positive_add
    (ω : SymplecticForm V) (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {T₀ : ℝ} {Jend : ℝ → V → AlmostComplexStructure V}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {B : Set V} {t₀ : ℝ}
    (hJt : ∀ z ∈ D, ∀ x ∈ B, ω.Tames (Jend z.2 x)) (hW : IsOpen W)
    (hJend : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (Jend q.1.2 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hDT : D ⊆ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1)) (hB : IsCompact B)
    (hDBW : D ×ˢ B ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) → (∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u k) z
          : ℝ × ℝ →ₗ[ℝ] V)) →
      0 ≤ E →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u k) z) ≤
          ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (realChart positive.cylindricalEndLift (z + (R k, 0)))) Ω B) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
          (fun z ↦ u (ψ n) (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) y) ∧
        ContDiffOn ℝ 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) B ∧
        TendstoLocallyUniformlyOn (fun n z ↦ u (ψ n) (realChart positive.cylindricalEndLift
          (z + (R (ψ n), 0)))) v atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ fun z ↦ u (ψ n)
          (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) (fderiv ℝ v) atTop
          (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jend z.2 (v z))
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x) v z
            : ℝ × ℝ →ₗ[ℝ] V)) ∧
        IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w x ↦ p.endSign * H (p.endSign * w.2) x) v) (Ω \ ↑Z) ∧
        ∫ z in Ω \ ↑Z, ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w x ↦ p.endSign * H (p.endSign * w.2) x) v z ≤ E := by
  -- The plane `p` is the positive plane for the Hamiltonian `ε H(ε t)`.
  have hHs' : ContDiff ℝ 3 (uncurry fun t x ↦ p.endSign * H (p.endSign * t) x) :=
    contDiff_const.mul (hHs.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))
  -- The cylindrical datum `ε H(ε t) dt` and the structures `J_∞(t)` of the end are smooth.
  have hKt : ContDiff ℝ 3 (uncurry fun (w : ℝ × ℝ) x ↦ p.endSign * H (p.endSign * w.2) x) :=
    hHs'.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (J := fun z ↦ Jend z.2) hW contDiffOn_const hKt.contDiffOn hJend hD hB
    hDBW hJt
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huB ↦ ?_⟩
  rw [perturbation_eq_positive p H] at hfl hE
  -- The translated windows lie in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` of the end.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have h (k : ℕ) :=
    contDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add ω
      (p.periodic_endSign_mul hH) hHs' hJ (fun z hz ↦ hJt z (hΩD hz)) hΩ (hΩT k)
      ((hu k).of_le (WithTop.coe_le_coe.2 le_top)) (hfl k) hE0 (hE k) (huB k)
  exact hconv hΩ hΩD (fun k ↦ ((hu k).comp ((contDiff_realChart
    positive.contDiff_cylindricalEndLift).comp (contDiff_id.add contDiff_const))).contDiffOn)
    (fun k ↦ (h k).2.1) huB (fun k ↦ (h k).2.2.1) fun k ↦ (h k).2.2.2

end SymplecticForm

section Manifold

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  {H : ℝ → M → ℝ}

namespace SmoothTwoForm.IsNondegenerate

open Floer Floer.PSSPlane

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **A translated end of the positive plane in a manifold.** Let `u` be a `C³` solution on the
plane of the Floer equation for the perturbation of the positive plane given by `H`, with energy at
most `E`, for structures `J` with `J(φ(s, t), x) = J_∞(t, x)` for `s ≥ T₀`. If the translate by
`(R, 0)` of an open set `Ω` lies in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` and
`v(z) = u(φ(z + (R, 0)))` maps `Ω` into a set on which `J_∞(t)` is tamed by `ω` for `(s, t) ∈ Ω`,
then `v` is `C³`, solves the Floer equation for `H(t) dt` and `J_∞` on `Ω`, and its energy density
is integrable on `Ω` with integral at most `E`. -/
private theorem contMDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    {C : Set M} {Ω : Set (ℝ × ℝ)}
    (hJt : ∀ z ∈ Ω, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (Jend z.2 x)) (hΩ : IsOpen Ω)
    {u : ℝ × ℝ → M} {R E t₀ : ℝ}
    (hΩT : ∀ z ∈ Ω, z + (R, 0) ∈ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 u)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x Complex.I) u
        z).toLinearMap)
    (hE0 : 0 ≤ E)
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal E)
    (huC : MapsTo (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) Ω C) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) ∧
      (∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jend z.2 (u (realChart positive.cylindricalEndLift (z + (R, 0)))))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) z).toLinearMap) ∧
      IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0))))) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) z ≤ E := by
  set e := realChart positive.cylindricalEndLift
  set v : ℝ × ℝ → M := fun z ↦ u (e (z + (R, 0)))
  have hHs₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H) := hHs.of_le (by norm_num)
  have hvC : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 v :=
    hu.comp ((contDiff_realChart positive.contDiff_cylindricalEndLift).comp
      (contDiff_id.add contDiff_const)).contMDiff
  -- Beyond `T₀` the structure is `J_∞(t)` and beyond `2` the datum is `H(t) dt`, so `v` solves the
  -- cylindrical equation.
  have hvfl (z : ℝ × ℝ) (hz : z ∈ Ω) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (Jend z.2 (v z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z).toLinearMap := by
    obtain ⟨h₁, -⟩ := hΩT z hz
    have h := ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive hH hHs₁
      ((le_max_right _ _).trans (mem_Ioi.1 h₁).le) (hu.mdifferentiable (by norm_num) _)
      (hfl (e (z + (R, 0))))
    rw [hJ _ _ _ ((le_max_left _ _).trans (mem_Ioi.1 h₁).le)] at h
    have heq := ω.perturbedMFDeriv_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ e) (R, 0) z
    simp only [Prod.snd_add, add_zero, comp_apply] at heq
    rw [heq]
    simpa using h
  -- The energy of `v` over `Ω` is at most the energy of `u` over the plane.
  have hlin : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) ≤
      ENNReal.ofReal E :=
    (ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_add_le hH hHs₁ (t₀ := t₀) le_rfl
      (hu.mdifferentiable (by norm_num)).mdifferentiableOn R
      hΩ.measurableSet fun z hz ↦ ⟨(le_max_right _ _).trans_lt (hΩT z hz).1,
        Ioo_subset_Ico_self (hΩT z hz).2⟩).trans ((setLIntegral_le_lintegral _ _).trans hE)
  -- The density is continuous on `Ω`, since the Hamiltonian vector fields of `0` and of `H(t)`
  -- are.
  have hX {F : ℝ × ℝ → M → ℝ} (hF : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 2 (uncurry F)) :
      ContinuousOn (fun p : (ℝ × ℝ) × M ↦
        (⟨p.2, ω.hamiltonianVectorField (F p.1) p.2⟩ : TangentBundle I M)) (Ω ×ˢ univ) :=
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) hF).continuous.continuousOn
  have hH₂ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 2 (uncurry fun (w : ℝ × ℝ) x ↦ H w.2 x) :=
    (hHs.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)).of_le
      (by norm_num)
  exact ⟨hvC, hvfl, ω.integrableOn_and_setIntegral_floerEnergyDensity_le hΩ hΩ.measurableSet
    subset_rfl (hvC.of_le (by norm_num)).contMDiffOn (hX contMDiff_const) (hX hH₂)
    (fun z hz ↦ floerEnergyDensity_nonneg (u := v) hω (hJt z hz _ (huC hz)) (hvfl z hz)) hE0 hlin⟩

omit [FiniteDimensional ℝ E] [IsManifold I ⊤ M] in
/-- **The end datum of a PSS plane read in a chart.** The Hamiltonian `ε H(ε t)` of the end of
`p`, for which `p` is the positive plane, is `C³`; read in a chart `φ`, its cylindrical datum
`ε H(ε t) dt` is `C³` on an open set containing `D × φ(C)` on which the structures `J'` are `C²`. -/
private theorem contMDiff_and_exists_isOpen_and_contDiffOn_comp_symm (p : PSSPlane)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {W : Set ((ℝ × ℝ) × V)}
    {D : Set (ℝ × ℝ)} {C : Set M} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry fun t x ↦ p.endSign * H (p.endSign * t) x) ∧
      ∃ W' : Set ((ℝ × ℝ) × V), IsOpen W' ∧ D ×ˢ (φ '' C) ⊆ W' ∧
        ContDiffOn ℝ 3 (fun q : (ℝ × ℝ) × V ↦ p.endSign * H (p.endSign * q.1.2) (φ.symm q.2)) W' ∧
        ContDiffOn ℝ 2
          (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W' := by
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3
      (uncurry fun t x ↦ p.endSign * H (p.endSign * t) x) :=
    (contDiff_const.mul contDiff_id).contMDiff.comp (hHs.comp
      (((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
  -- The datum is `C³` on `ℝ² × φ(U)`, which contains `D × φ(C)`.
  refine ⟨hHs', W ∩ univ ×ˢ φ.target, hW.inter (isOpen_univ.prod φ.open_target), ?_,
    (φ.contDiffOn_comp_symm_of_contMDiffOn
      (K := fun (w : ℝ × ℝ) x ↦ p.endSign * H (p.endSign * w.2) x)
      isOpen_univ (hHs'.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk
        contMDiff_snd)).contMDiffOn (WithTop.coe_le_coe.2 le_top)).mono inter_subset_right,
    hJ'.mono inter_subset_left⟩
  refine subset_inter hDCW (prod_mono (subset_univ D) ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact φ.toPartialEquiv.map_source (hCφ hx)

/-- **The translated ends of PSS planes in a symplectic chart of a manifold converge off finitely
many bubbling points.** Let `p` be a PSS plane with end sign `ε`, `H` a period-one `C³`
Hamiltonian on `M`, and `J(z, x)` structures on the tangent spaces of `M` which are cylindrical far
out on the end, `J(e(s, t), x) = J_∞(t, x)` for `s ≥ T₀`, where `e` is the end lift of the positive
plane in real coordinates. Let `φ` be a smooth partial diffeomorphism from `M` onto an open subset
of `V`, and `D ⊆ (max T₀ 2, ∞) × (t₀, t₀ + 1)` and `C ⊆ φ.source` compact, with `J_∞(t, x)` tamed
by `ω` for `(s, t) ∈ D` and `x ∈ C`. Let `φ` pull the symplectic form `ω₀` back to `ω` at the
points of `C`, and let `J'` be the family `J_∞` read in the chart,
`dφ_x ∘ J_∞(t, x) = J'((s, t), φ x) ∘ dφ_x` for `(s, t) ∈ D` and `x ∈ C`, and `C²` on an open set
containing `D × φ(C)`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
solutions on the plane of the Floer equation for `J(z, u)` and the perturbation of `p` given by
`H`, with energy at most `E ≥ 0`, let `Rₖ ≥ 0` be heights, and let the translated ends
`vₖ(z) = uₖ(e(z + (Rₖ, 0)))` map an open `Ω ⊆ D` into `C`. Then there are a subsequence `ψ`, a
finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a map `v`, continuous on `Ω \ Z` with values in `C`, such
that along `ψ` every disc about a point of `Z` eventually carries energy at least `δ` for the
cylindrical datum `ε H(ε t) dt`, the differentials of the coordinate maps `φ ∘ v_{ψ n}` are
uniformly bounded on every compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v`
locally uniformly on `Ω \ Z`, and `v_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_realChart_positive_add
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M} {t₀ : ℝ}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (Jend z.2 x))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (Jend z.2 x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hDT : D ⊆ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1)) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤
          ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (realChart positive.cylindricalEndLift (z + (R k, 0)))) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
          (fun z ↦ u (ψ n) (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) y) ∧
        (∀ K, IsCompact K → K ⊆ Ω \ ↑Z → ∃ L, ∀ n, ∀ y ∈ K,
          ‖fderiv ℝ (φ ∘ fun z ↦ u (ψ n) (realChart positive.cylindricalEndLift
            (z + (R (ψ n), 0)))) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ fun z ↦ u (ψ n)
          (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n)
          (realChart positive.cylindricalEndLift (y + (R (ψ n), 0)))) atTop (𝓝 (v y)) := by
  obtain ⟨hHs', W', hW', hDCW', hKt, hJ''⟩ :=
    contMDiff_and_exists_isOpen_and_contDiffOn_comp_symm p hHs φ hW hJ' hCφ hDCW
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset φ
    (Ks := fun _ _ ↦ 0) (Kt := fun w x ↦ p.endSign * H (p.endSign * w.2) x)
    (J := fun z ↦ Jend z.2) hφ hJJ' hW' contDiffOn_const hKt hJ'' hD hC hCφ hDCW' hJt
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huC ↦ ?_⟩
  rw [perturbation_eq_positive p H] at hfl hE
  -- The translated windows lie in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` of the end.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have h (k : ℕ) :=
    contMDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add hω
      (p.periodic_endSign_mul hH) hHs' hJ (fun z hz ↦ hJt z (hΩD hz)) hΩ (hΩT k) (hu k) (hfl k) hE0
      (hE k) (huC k)
  exact hconv hΩ hΩD (fun k ↦ (h k).1.contMDiffOn) (fun k ↦ (h k).2.1) huC
    (fun k ↦ (h k).2.2.1) fun k ↦ (h k).2.2.2

/-- **The translated ends of smooth PSS planes in a symplectic chart of a manifold converge in `C¹`
off finitely many bubbling points to a Floer cylinder.** Under the hypotheses of
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_realChart_positive_add`, there
is a threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions on the plane of
the Floer equation for `J(z, u)` and the perturbation of `p` given by `H`, with energy at most
`E ≥ 0`, let `Rₖ ≥ 0` be heights, and let the translated ends `vₖ(z) = uₖ(e(z + (Rₖ, 0)))` map an
open `Ω ⊆ D` into `C`. Then there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`,
and a map `v` with values in `C` on `Ω \ Z` such that along `ψ` every disc about a point of `Z`
eventually carries energy at least `δ` for the cylindrical datum `ε H(ε t) dt`, the coordinate maps
`φ ∘ v_{ψ n}` and their derivatives converge to `φ ∘ v` and its derivative locally uniformly on
`Ω \ Z`, `v` is a `C¹` solution on `Ω \ Z` of the Floer equation for the datum `ε H(ε t) dt` and the
structures `J_∞(t)`, and the energy of `v` over `Ω \ Z` is finite and at most `E`. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_realChart_positive_add
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M} {t₀ : ℝ}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (Jend z.2 x))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (Jend z.2 x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hDT : D ⊆ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1)) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤
          ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (realChart positive.cylindricalEndLift (z + (R k, 0)))) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
          (fun z ↦ u (ψ n) (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ fun z ↦ u (ψ n)
          (realChart positive.cylindricalEndLift (z + (R (ψ n), 0)))) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (φ ∘ fun z ↦ u (ψ n)
          (realChart positive.cylindricalEndLift (z + (R (ψ n), 0))))) (fderiv ℝ (φ ∘ v)) atTop
          (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jend z.2 (v z))
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x) v
            z).toLinearMap) ∧
        IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w x ↦ p.endSign * H (p.endSign * w.2) x) v) (Ω \ ↑Z) ∧
        ∫ z in Ω \ ↑Z, ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w x ↦ p.endSign * H (p.endSign * w.2) x) v z ≤ E := by
  obtain ⟨hHs', W', hW', hDCW', hKt, hJ''⟩ :=
    contMDiff_and_exists_isOpen_and_contDiffOn_comp_symm p hHs φ hW hJ' hCφ hDCW
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset
    φ (Ks := fun _ _ ↦ 0) (Kt := fun w x ↦ p.endSign * H (p.endSign * w.2) x)
    (J := fun z ↦ Jend z.2) hφ hJJ' hW' contDiffOn_const hKt hJ'' hD hC hCφ hDCW' hJt
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huC ↦ ?_⟩
  rw [perturbation_eq_positive p H] at hfl hE
  -- The translated windows lie in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` of the end.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have h (k : ℕ) :=
    contMDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add hω
      (p.periodic_endSign_mul hH) hHs' hJ (fun z hz ↦ hJt z (hΩD hz)) hΩ (hΩT k)
      ((hu k).of_le (WithTop.coe_le_coe.2 le_top)) (hfl k) hE0 (hE k) (huC k)
  exact hconv hΩ hΩD (fun k ↦ ((hu k).comp ((contDiff_realChart
      positive.contDiff_cylindricalEndLift).comp
        (contDiff_id.add contDiff_const)).contMDiff).contMDiffOn)
    (fun k ↦ (h k).2.1) huC (fun k ↦ (h k).2.2.1) fun k ↦ (h k).2.2.2

end SmoothTwoForm.IsNondegenerate

end Manifold

end TauCeti
