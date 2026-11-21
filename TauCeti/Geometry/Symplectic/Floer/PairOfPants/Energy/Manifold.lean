/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

/-!
# The energy identity and topological energy bound for a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `K` be a Hamiltonian
perturbation on the pair of pants `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond `T₀` on each end `q`
for `1`-periodic Hamiltonians `H_q`, and let `u : ℝ × ℝ → M` solve `(du - X_K)^{0,1} = 0` on `S`
with image in a compact set `B ⊆ M` and integrable symplectic area density and curvature along `u`.

Because `[0, 1] × B` is compact, each continuous `H_q` is automatically bounded along the end loops
of `u`, giving integrable (hence finite) Floer energy density on `S` before proving end convergence
(`integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`,
`lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact`). Combined with
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold` and
`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`, this yields:

* **Energy identity (`C¹` with isolated subsequential-limit orbits):** without `[T2Space M]`,
  `[BoundarylessManifold I M]`, or finite energy a priori, `u` converges along each end `q` to an
  orbit `y_q` in `B` and satisfies `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`
  (`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually`,
  specialized to `pairOfPantsPerturbation H`).
* **Topological energy lower bound on `B`:** if `|H_q(t, x)| ≤ M_H q` on `B`, then
  `-(M_H 0 + M_H 1 + M_H ∞) ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt`.
* **Corollaries:** nondegeneracy supplies isolation for `C²` `H_q` on a Hausdorff boundaryless
  manifold (including closed-manifold specializations); when one end loop per end is
  null-homotopic, parallel `_of_nullhomotopic` theorems require isolation or nondegeneracy only on
  `contractiblePeriodicSolutions` and yield contractible `y_q`.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis (1995).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti.SmoothTwoForm

open Floer

-- File-local syntactic macros expanding directly to the unfolded statement terms
-- (all generated auxiliary declarations are module-private; no extra public API is added).
local notation "Sℝ" => thricePuncturedSphereReal
local macro "PoP(" H:term ")" : term => `(pairOfPantsPerturbation $H)
local macro "pertS(" K:term ")" : term => `(fun z x ↦ ($K) (Complex.equivRealProdCLM.symm z) x 1)
local macro "pertT(" K:term ")" : term =>
  `(fun z x ↦ ($K) (Complex.equivRealProdCLM.symm z) x Complex.I)
local macro "Dens(" ω:term ", " K:term ", " u:term ")" : term =>
  `(($ω).floerEnergyDensity pertS($K) pertT($K) $u)
local macro "FloerS(" ω:term ", " K:term ", " u:term ", " J:term ")" : term =>
  `(∀ z ∈ Sℝ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) ($J z)
    (($ω).perturbedMFDeriv pertS($K) pertT($K) $u z).toLinearMap)
local macro "ωAreaAt(" I:term ", " ω:term ", " u:term ", " z:term ")" : term =>
  `((SmoothBundleForm.eval₂ $ω ($u $z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) $I $u $z stdComplexLineReal)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) $I $u $z stdComplexLineImag) : ℝ))
local macro "ωArea(" I:term ", " ω:term ", " u:term ")" : term =>
  `(fun z ↦ ωAreaAt($I, $ω, $u, z))
local macro "Orb(" S:ident ", " ω:term ", " H:term ", " q:term ")" : term =>
  `($S (fun t ↦ ($ω).hamiltonianVectorField ($H $q t)) 1)
local macro "EndConv(" e:term ", " u:term ", " q:term ", " y:term ")" : term =>
  `(TendstoUniformly (fun s t ↦ $e ($u (endChart $q (($q).endSign * s, t)))) ($e ∘ $y) atTop ∧
    ∀ t, Tendsto (fun s ↦ $u (endChart $q (($q).endSign * s, t))) atTop (𝓝 ($y t)))
local macro "SubseqLim(" e:term ", " u:term ", " q:term ", " y:term ")" : term =>
  `(∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
    TendstoUniformly (fun n t ↦ $e ($u (endChart $q (($q).endSign * σ n, t)))) ($e ∘ $y) atTop)
local macro "IsoEnds(" S:ident ", " ω:term ", " H:term ", " B:term ", "
    e:term ", " u:term ")" : term =>
  `(∀ q, ∀ y ∈ Orb($S, $ω, $H, q), (∀ t, y t ∈ $B) → SubseqLim($e, $u, q, y) →
    ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ Orb($S, $ω, $H, q), (∀ t, y' t ∈ $B) → SubseqLim($e, $u, q, y') →
      y' 0 = p → y' = y)
local macro "EnergyEq(" I:term ", " ω:term ", " K:term ", " H:term ", " u:term ", " y:term ")" :
    term =>
  `(∫ z in Sℝ, Dens($ω, $K, $u) z = (∫ z in Sℝ, ωAreaAt($I, $ω, $u, z)) +
      (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, $H q t ($y q t)) -
      ∫ z in Sℝ, ($ω).hamiltonianCurvature pertS($K) pertT($K) z ($u z))
local macro "TopoBound(" I:term ", " ω:term ", " H:term ", " u:term ", " M_H:term ", " y:term ")" :
    term =>
  `(-∑ q, $M_H q ≤ (∫ z in Sℝ, ωAreaAt($I, $ω, $u, z)) +
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, $H q t ($y q t))
local macro "NullEnds(" u:term ")" : term =>
  `(∀ q, ∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), _),
    g.Nullhomotopic ∧ ∀ t : ℝ, g t = $u (endChart q (q.endSign * s, t)))
local macro "NondegenAt(" I:term ", " ω:term ", " H:term ", " q:term ", " y:term ")" : term =>
  `(IsNondegenerateFixedPt $I
    (timeDependentFlowOf (fun t ↦ ($ω).hamiltonianVectorField ($H $q t)) 0 1) ($y 0))
local macro "CompactOut(" S:ident ", " I:term ", " ω:term ", " K:term ", " H:term ", "
    B:term ", " e:term ", " u:term ")" : term =>
  `(∃ y : Puncture → ℝ → _,
    (∀ q, y q ∈ Orb($S, $ω, $H, q) ∧ (∀ t, y q t ∈ $B) ∧ EndConv($e, $u, q, y q)) ∧
    IntegrableOn Dens($ω, $K, $u) Sℝ ∧ EnergyEq($I, $ω, $K, $H, $u, y))
local macro "BoundOut(" S:ident ", " I:term ", " ω:term ", " H:term ", "
    B:term ", " e:term ", " u:term ", " M_H:term ")" : term =>
  `(∃ y : Puncture → ℝ → _,
    (∀ q, y q ∈ Orb($S, $ω, $H, q) ∧ (∀ t, y q t ∈ $B) ∧ EndConv($e, $u, q, y q)) ∧
    TopoBound($I, $ω, $H, $u, $M_H, y))
local macro "ClosedOut(" S:ident ", " I:term ", " ω:term ", " H:term ", "
    e:term ", " u:term ")" : term =>
  `(∃ y : Puncture → ℝ → _, (∀ q, y q ∈ Orb($S, $ω, $H, q) ∧ EndConv($e, $u, q, y q)) ∧
    IntegrableOn Dens($ω, PoP($H), $u) Sℝ ∧ EnergyEq($I, $ω, PoP($H), $H, $u, y))
local macro "ClosedBound(" S:ident ", " I:term ", " ω:term ", " H:term ", "
    e:term ", " u:term ", " M_H:term ")" : term =>
  `(∃ y : Puncture → ℝ → _, (∀ q, y q ∈ Orb($S, $ω, $H, q) ∧ EndConv($e, $u, q, y q)) ∧
    TopoBound($I, $ω, $H, $u, $M_H, y))

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ} {B : Set M} {u : ℝ × ℝ → M}

namespace IsNondegenerate

/-! ### Automatic finite energy and energy identity on a compact target set -/

section CompactEnergy

variable (hω : ω.IsNondegenerate)
  (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
    (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
  (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
    K w x = H q (q.endCoord w).im x • q.endAngularForm w)
  (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q))) (hB : IsCompact B)
  (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Sℝ) (huB : ∀ z ∈ Sℝ, u z ∈ B)
  (he : ∀ z ∈ Sℝ, 0 ≤ Dens(ω, K, u) z) (hA : IntegrableOn ωArea(I, ω, u) Sℝ)
  (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature pertS(K) pertT(K) z (u z)) Sℝ)

include hω hK hKH hH hHc hB hu huB he hA hR

/-- **Automatic integrability of a nonnegative Floer energy density on a compact set.** Compactness
of `[0, 1] × B` uniformly bounds `∫₀¹ H_q(t, u(φ_q(±σ, t))) dt` for `σ > 0`, making the Floer energy
density integrable over `S` without global bounds on `H_q` or end convergence. -/
theorem integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact :
    IntegrableOn Dens(ω, K, u) Sℝ := by
  have hS : volume.restrict Sℝ = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hA hR ⊢
  have hbound : ∀ q, ∃ C : ℝ, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ B, ‖uncurry (H q) p‖ ≤ C := fun q ↦
    (isCompact_Icc.prod hB).exists_bound_of_continuousOn (hHc q).continuousOn
  choose C hC using hbound
  refine hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he hA hR
    (C := C) fun q ↦ ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
  have hmem (t : ℝ) : endChart q (q.endSign * σ, t) ∈ Sℝ :=
    endChart_mem_thricePuncturedSphereReal
      (by simpa only [← mul_assoc, endSign_mul_self, one_mul] using hσ)
  simpa only [Real.norm_eq_abs, uncurry_apply_pair, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦
      hC q (t, u (endChart q (q.endSign * σ, t)))
        ⟨Ioc_subset_Icc_self (uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ ht), huB _ (hmem t)⟩

/-- **Automatic finiteness of the Lebesgue Floer energy on a compact set.** -/
theorem lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact :
    ∫⁻ z in Sℝ, ENNReal.ofReal (Dens(ω, K, u) z) ≠ ⊤ := by
  have hS : volume.restrict Sℝ = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hEint := hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    hK hKH hH hHc hB hu huB he hA hR
  rw [IntegrableOn, hS] at hEint
  rw [hS, ← ofReal_integral_eq_lintegral_ofReal hEint (ae_mem_thricePuncturedSphereReal.mono he)]
  exact ENNReal.ofReal_ne_top

/-- **The manifold pair-of-pants energy identity on a compact target set.** If `t ↦ u(φ_q(±s, t))`
converges pointwise to `y_q` as `s → ∞` on each end `q`, then
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)` without finite energy a priori. -/
theorem integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    {y : Puncture → ℝ → M}
    (hy : ∀ q t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) :
    EnergyEq(I, ω, K, H, u, y) := by
  have hS : volume.restrict Sℝ = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hEint := hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    hK hKH hH hHc hB hu huB he hA hR
  rw [IntegrableOn, hS] at hEint hA hR
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA hR
    fun q ↦ tendsto_intervalIntegral_endChart_of_isCompact (hHc q) hB hu.continuousOn huB (hy q)

end CompactEnergy

/-! ### Energy identity and topological energy bound at asymptotic periodic orbits -/

section AsymptoticEnergy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {e : M → F} {c : ℝ}

/-- Nondegeneracy of a `C²` Hamiltonian vector field isolates orbits at time `0` in any subset
`P ⊆ periodicSolutions`. -/
private theorem eventually_eq_of_isNondegenerateFixedPt [T2Space M] [BoundarylessManifold I M]
    (hω : ω.IsNondegenerate) {h : ℝ → M → ℝ} (hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry h))
    {P : Set (ℝ → M)} (hP : P ⊆ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (h t)) 1)
    {y : ℝ → M} (hy : y ∈ P)
    (hnd : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (h t)) 0 1) (y 0)) :
    ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ P, y' 0 = p → y' = y := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hh.of_le (by norm_num))
  exact (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt hX
    (hP hy) (s := 0) (T := 1)
    (by simpa only [zero_add] using hnd.eventually_not_isFixedPt)).mono
    fun _ hp y' hy' hy'p ↦ hp y' (hP hy') hy'p

section Compact

variable (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
  (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
  (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
  (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Sℝ) (huB : ∀ z ∈ Sℝ, u z ∈ B)
  (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
  (hJc : ∀ z ∈ Sℝ, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
  (hA : IntegrableOn ωArea(I, ω, u) Sℝ)
  (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)

section General

variable
  (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
    (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
  (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
    K w x = H q (q.endCoord w).im x • q.endAngularForm w)
  (hfloer : FloerS(ω, K, u, J))
  (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature pertS(K) pertT(K) z (u z)) Sℝ)

include hω hK hKH hH he hB he_inj hde hu huB J hc hJc hfloer hA hR hC

omit [FiniteDimensional ℝ F] he he_inj hC in
/-- Shared derivation of integrability and the energy identity from an end-by-end convergence
package returning orbits in `P q`. -/
private theorem exists_energy_of_endConvergence {P : Puncture → Set (ℝ → M)}
    (hHc : ∀ q, Continuous (uncurry (H q)))
    (hex : (∫⁻ z in Sℝ, ENNReal.ofReal (Dens(ω, K, u) z) ≠ ⊤) →
      ∀ q, ∃ y ∈ P q, (∀ t, y t ∈ B) ∧ EndConv(e, u, q, y)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ P q ∧ (∀ t, y q t ∈ B) ∧ EndConv(e, u, q, y q)) ∧
      IntegrableOn Dens(ω, K, u) Sℝ ∧ EnergyEq(I, ω, K, H, u, y) := by
  have he₀ : ∀ z ∈ Sℝ, 0 ≤ Dens(ω, K, u) z := fun z hz ↦
    floerEnergyDensity_nonneg hω
      (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hE := hω.lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact
    hK hKH hH hHc hB hu huB he₀ hA hR
  choose y hy using hex hE
  exact ⟨y, hy,
    hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
      hK hKH hH hHc hB hu huB he₀ hA hR,
    hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
      hK hKH hH hHc hB hu huB he₀ hA hR fun q ↦ (hy q).2.2.2⟩

/-- **The manifold pair-of-pants energy identity at isolated asymptotic periodic orbits.** Under
compact image `B`, uniform tameness through `e`, bounded derivative of `e ∘ u ∘ φ'_q` on each end,
and isolation at time `0` of subsequential uniform-limit orbits in `B`, `u` has integrable Floer
energy density, converges along each end to an orbit `y_q` in `B`, and satisfies the energy
identity. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hiso : IsoEnds(periodicSolutions, ω, H, B, e, u)) :
    CompactOut(periodicSolutions, I, ω, K, H, B, e, u) := by
  choose b C hbC using hC
  refine exists_energy_of_endConvergence hω hH hB hde hu huB J hc hJc hA hK hKH hfloer
    hR (fun q ↦ (hHs q).continuous) fun hE q ↦ ?_
  exact
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
      hω hKH hH he hB he_inj hde hu huB J hfloer hE q (b := max (b q) 0)
      (fun z hz ↦ hbC q z ((le_max_left (b q) 0).trans_lt hz)) hc
      (fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right (b q) 0).trans_lt hz)) v) (hHs q) (hiso q)

/-- **The manifold pair-of-pants energy identity at isolated contractible asymptotic periodic
orbits.** Variant requiring isolation only among `contractiblePeriodicSolutions` when one end loop
per end is null-homotopic in `M`. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hnull : NullEnds(u)) (hiso : IsoEnds(contractiblePeriodicSolutions, ω, H, B, e, u)) :
    CompactOut(contractiblePeriodicSolutions, I, ω, K, H, B, e, u) := by
  choose b C hbC using hC
  exact exists_energy_of_endConvergence hω hH hB hde hu huB J hc hJc hA hK hKH hfloer
    hR (fun q ↦ (hHs q).continuous) fun hE q ↦
      exists_mem_contractiblePeriodicSolutions_endChart_atTop_of_floer_of_isCompact_of_eventually
        hω hKH hH he hB he_inj hde hu huB J hfloer hE q (b := max (b q) 0)
        (fun z hz ↦ hbC q z ((le_max_left (b q) 0).trans_lt hz)) hc
        (fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
          ((le_max_right (b q) 0).trans_lt hz)) v) (hHs q) (hnull q) (hiso q)

section Nondegenerate

variable [T2Space M] [BoundarylessManifold I M]
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))

include hHs

/-- **The manifold pair-of-pants energy identity at nondegenerate asymptotic periodic orbits.**
Corollary for `C²` Hamiltonians `H_q` on a Hausdorff boundaryless manifold without finite energy a
priori. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    (hnd : ∀ q, ∀ y ∈ Orb(periodicSolutions, ω, H, q), (∀ t, y t ∈ B) →
      NondegenAt(I, ω, H, q, y)) :
    CompactOut(periodicSolutions, I, ω, K, H, B, e, u) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually
    hω hH he hB he_inj hde hu huB J hc hJc hA hC hK hKH hfloer hR
    (fun q ↦ (hHs q).of_le one_le_two) fun q y hy hyB _ ↦
      (eventually_eq_of_isNondegenerateFixedPt hω (hHs q) Subset.rfl hy (hnd q y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- **The manifold pair-of-pants energy identity at nondegenerate contractible asymptotic orbits.**
Corollary for `C²` `H_q` assuming nondegeneracy only on `contractiblePeriodicSolutions`. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_nullhomotopic
    (hnull : NullEnds(u))
    (hnd : ∀ q, ∀ y ∈ Orb(contractiblePeriodicSolutions, ω, H, q), (∀ t, y t ∈ B) →
      NondegenAt(I, ω, H, q, y)) :
    CompactOut(contractiblePeriodicSolutions, I, ω, K, H, B, e, u) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually
    hω hH he hB he_inj hde hu huB J hc hJc hA hC hK hKH hfloer hR
    (fun q ↦ (hHs q).of_le one_le_two) hnull fun q y hy hyB _ ↦
      (eventually_eq_of_isNondegenerateFixedPt hω (hHs q)
        contractiblePeriodicSolutions_subset hy (hnd q y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

end Nondegenerate

end General

section PairOfPants

variable (hfloer : FloerS(ω, PoP(H), u, J))

include hω hH he hB he_inj hde hu huB J hc hJc hfloer hA hC

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] he hB he_inj hu hA hC in
/-- Deduce the topological energy lower bound `-∑ q, M_H q ≤ ∫ u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t))`
from the energy identity and pointwise bounds `|H_q(t, x)| ≤ M_H q` on `B`. -/
private theorem neg_sum_le_of_energyIdentity
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) {y : Puncture → ℝ → M}
    (hid : EnergyEq(I, ω, PoP(H), H, u, y)) :
    TopoBound(I, ω, H, u, M_H, y) := by
  have hpos : 0 ≤ ∫ z in Sℝ, Dens(ω, PoP(H), u) z :=
    setIntegral_nonneg isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
      floerEnergyDensity_nonneg hω
        (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hcurv := abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le_of_mapsTo ω hH hHs
    hMH huB Sℝ
  linarith [(abs_le.1 hcurv).1]

section PeriodicC1
variable (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
  (hiso : IsoEnds(periodicSolutions, ω, H, B, e, u))
include hHs hiso

/-- Specialization of the general `C¹` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually :
    CompactOut(periodicSolutions, I, ω, PoP(H), H, B, e, u) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually
    (K := PoP(H)) (T₀ := 2) hω hH he hB he_inj hde hu huB J hc hJc hA hC
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hfloer
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hHs hiso

/-- Lower bound on topological energy at isolated asymptotic periodic orbits for `|H_q| ≤ M_H q`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_eventually
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    BoundOut(periodicSolutions, I, ω, H, B, e, u, M_H) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually
      hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer hHs hiso
  ⟨y, hy, neg_sum_le_of_energyIdentity hω hH hde huB J hc hJc hfloer hHs hMH hid⟩
end PeriodicC1

section PeriodicC2
variable [T2Space M] [BoundarylessManifold I M]
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
  (hnd : ∀ q, ∀ y ∈ Orb(periodicSolutions, ω, H, q), (∀ t, y t ∈ B) → NondegenAt(I, ω, H, q, y))
include hHs hnd

/-- Specialization of the general `C²` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact :
    CompactOut(periodicSolutions, I, ω, PoP(H), H, B, e, u) :=
  exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually
    hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer (fun q ↦ (hHs q).of_le one_le_two)
    fun q y hy hyB _ ↦
      (eventually_eq_of_isNondegenerateFixedPt hω (hHs q) Subset.rfl hy (hnd q y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- Lower bound on topological energy at nondegenerate asymptotic orbits for `|H_q| ≤ M_H q`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    BoundOut(periodicSolutions, I, ω, H, B, e, u, M_H) :=
  let ⟨y, hy, _, hid⟩ := exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer hHs hnd
  ⟨y, hy, neg_sum_le_of_energyIdentity hω hH hde huB J hc hJc hfloer
    (fun q ↦ (hHs q).of_le one_le_two) hMH hid⟩
end PeriodicC2

section ContractibleC1
variable (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
  (hnull : NullEnds(u)) (hiso : IsoEnds(contractiblePeriodicSolutions, ω, H, B, e, u))
include hHs hnull hiso

/-- Specialization of the contractible `C¹` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic_of_eventually :
    CompactOut(contractiblePeriodicSolutions, I, ω, PoP(H), H, B, e, u) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually
    (K := PoP(H)) (T₀ := 2) hω hH he hB he_inj hde hu huB J hc hJc hA hC
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hfloer
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn)
    hHs hnull hiso

/-- Lower bound on topological energy at isolated contractible asymptotic orbits. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    BoundOut(contractiblePeriodicSolutions, I, ω, H, B, e, u, M_H) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
      hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer hHs hnull hiso
  ⟨y, hy, neg_sum_le_of_energyIdentity hω hH hde huB J hc hJc hfloer hHs hMH hid⟩
end ContractibleC1

section ContractibleC2
variable [T2Space M] [BoundarylessManifold I M]
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
  (hnull : NullEnds(u))
  (hnd : ∀ q, ∀ y ∈ Orb(contractiblePeriodicSolutions, ω, H, q), (∀ t, y t ∈ B) →
    NondegenAt(I, ω, H, q, y))
include hHs hnull hnd

/-- Specialization of the contractible `C²` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic :
    CompactOut(contractiblePeriodicSolutions, I, ω, PoP(H), H, B, e, u) :=
  exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
    hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer (fun q ↦ (hHs q).of_le one_le_two)
    hnull fun q y hy hyB _ ↦
      (eventually_eq_of_isNondegenerateFixedPt hω (hHs q)
        contractiblePeriodicSolutions_subset hy (hnd q y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- Lower bound on topological energy at nondegenerate contractible asymptotic orbits. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    BoundOut(contractiblePeriodicSolutions, I, ω, H, B, e, u, M_H) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
      hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer hHs hnull hnd
  ⟨y, hy, neg_sum_le_of_energyIdentity hω hH hde huB J hc hJc hfloer
    (fun q ↦ (hHs q).of_le one_le_two) hMH hid⟩
end ContractibleC2

end PairOfPants
end Compact

section Closed
variable [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
  (hH : ∀ q, Periodic (H q) 1)
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
  (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
  (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Sℝ)
  (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
  (hJc : ∀ z ∈ Sℝ, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
  (hfloer : FloerS(ω, PoP(H), u, J)) (hA : IntegrableOn ωArea(I, ω, u) Sℝ)
  (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
include hω hH hHs he he_inj hde hu J hc hJc hfloer hA hC

section Periodic
variable (hnd : ∀ q, ∀ y ∈ Orb(periodicSolutions, ω, H, q), NondegenAt(I, ω, H, q, y))
include hnd

/-- Closed-manifold specialization of the `pairOfPantsPerturbation H` energy identity. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation :
    ClosedOut(periodicSolutions, I, ω, H, e, u) :=
  let ⟨y, hy, hEint, hid⟩ :=
    hω.exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact hH he isCompact_univ
      he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hA hC hfloer hHs
      fun q y hy _ ↦ hnd q y hy
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- Closed-manifold specialization of the topological energy lower bound. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q) :
    ClosedBound(periodicSolutions, I, ω, H, e, u, M_H) :=
  let ⟨y, hy, hle⟩ :=
    hω.exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact hH he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hA hC hfloer
      hHs (fun q y hy _ ↦ hnd q y hy) (fun q t x _ ↦ hMH q t x)
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩
end Periodic

section Contractible
variable (hnull : NullEnds(u))
  (hnd : ∀ q, ∀ y ∈ Orb(contractiblePeriodicSolutions, ω, H, q), NondegenAt(I, ω, H, q, y))
include hnull hnd

/-- Closed-manifold specialization of the contractible `pairOfPantsPerturbation H` identity. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic :
    ClosedOut(contractiblePeriodicSolutions, I, ω, H, e, u) :=
  let ⟨y, hy, hEint, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic hω hH
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hA hC
      hfloer hHs hnull fun q y hy _ ↦ hnd q y hy
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- Closed-manifold specialization of the contractible topological energy lower bound. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q) :
    ClosedBound(contractiblePeriodicSolutions, I, ω, H, e, u, M_H) :=
  let ⟨y, hy, hle⟩ :=
    exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic hω
      hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hA hC
      hfloer hHs hnull (fun q y hy _ ↦ hnd q y hy) (fun q t x _ ↦ hMH q t x)
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩
end Contractible
end Closed
end AsymptoticEnergy
end IsNondegenerate
end TauCeti.SmoothTwoForm
