/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Integrable
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit

/-!
# The energy identity and topological energy bound for a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `K` be a Hamiltonian
perturbation on the pair of pants `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond `T₀` on each end `q`
for `1`-periodic Hamiltonians `H_q`, and let `u : ℝ × ℝ → M` solve `(du - X_K)^{0,1} = 0` on `S`
with image in a compact set `B ⊆ M` and integrable symplectic area density and curvature along `u`.

In `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Integrable` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic`, compactness of `[0, 1] × B`
bounds `H_q` along end loops, giving automatic finite energy
(`integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`,
`lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact`) and the energy
identity from pointwise end limits
(`integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`). Combined with
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold`, this yields:

* **Energy identity assuming finite energy a priori:**
  `exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated`
  and `..._of_eq_smul_endAngularForm`, specialized to `pairOfPantsPerturbation H`.
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

/-! ### Energy identity and topological energy bound at asymptotic periodic orbits -/

section AsymptoticEnergy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {e : M → F} {c : ℝ}

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
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq (hHs q) hy
        (hnd q y hy hyB)).mono fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

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
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq (hHs q)
        (contractiblePeriodicSolutions_subset hy) (hnd q y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' (contractiblePeriodicSolutions_subset hy') hy'p

end Nondegenerate

end General

section PairOfPants

variable (hfloer : FloerS(ω, PoP(H), u, J))

include hω hH he hB he_inj hde hu huB J hc hJc hfloer hA hC

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] hH he hB he_inj hu hA hC in
/-- Nonnegativity of the integrated Floer energy density under uniform tameness through `e`. -/
private theorem setIntegral_floerEnergyDensity_nonneg :
    0 ≤ ∫ z in Sℝ, Dens(ω, PoP(H), u) z :=
  setIntegral_nonneg isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
    floerEnergyDensity_nonneg hω
      (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)

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
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH hHs hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω hde huB J hc hJc hfloer) hid⟩
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
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq (hHs q) hy
        (hnd q y hy hyB)).mono fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- Lower bound on topological energy at nondegenerate asymptotic orbits for `|H_q| ≤ M_H q`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    BoundOut(periodicSolutions, I, ω, H, B, e, u, M_H) :=
  let ⟨y, hy, _, hid⟩ := exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer hHs hnd
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH
    (fun q ↦ (hHs q).of_le one_le_two) hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω hde huB J hc hJc hfloer) hid⟩
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
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH hHs hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω hde huB J hc hJc hfloer) hid⟩
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
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq (hHs q)
        (contractiblePeriodicSolutions_subset hy) (hnd q y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' (contractiblePeriodicSolutions_subset hy') hy'p

/-- Lower bound on topological energy at nondegenerate contractible asymptotic orbits. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    BoundOut(contractiblePeriodicSolutions, I, ω, H, B, e, u, M_H) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
      hω hH he hB he_inj hde hu huB J hc hJc hA hC hfloer hHs hnull hnd
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH
    (fun q ↦ (hHs q).of_le one_le_two) hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω hde huB J hc hJc hfloer) hid⟩
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

/-! ### Pair-of-pants energy identity assuming finite energy a priori -/

section FiniteEnergy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {e : M → F}

/-- **The pair-of-pants energy identity with isolated asymptotic orbits, for a manifold target.**
Let `ω` be a nondegenerate two-form on a manifold `M`, `K` a `C¹` perturbation on `S × M` equal to
`H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and `u` a `C¹` map
on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy
and integrable symplectic area and curvature. Let `e : M → F` be `C¹`, injective on `B` with
injective differential at the points of `B`, suppose that `c ‖d e v‖² ≤ ω(v, J z v)` on `S` with
`c > 0`, that `(e ∘ u) ∘ φ'_q` has bounded derivative on some strip `(b, ∞) × [0, 1]` at each end
`q`, and that every `1`-periodic orbit of `H_q` in `B` is isolated at `t = 0` among `1`-periodic
orbits of `H_q` in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic
orbits `y_q` of `H_q` in `B`, the Floer energy density of `u` is integrable on `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
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
  have hy_ex : ∀ q, ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := fun q ↦ by
    obtain ⟨b, C, hbC⟩ := hC q
    have hmem (z : ℝ × ℝ) (hz : max b 0 < z.1) :
        positiveEndChart q z ∈ thricePuncturedSphereReal :=
      positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
      hKH hH hHs he hB he_inj hde hu huB J hfloer hE q
      (b := max b 0) (fun z hz ↦ hbC z ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩) hc
      (fun z hz v ↦ hJc _ (hmem z hz.1) v) (hiso q)
  choose y hy hyB hyu hyp using hy_ex
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
        atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hB hu.continuousOn huB
      (hyp q)
  -- Uniform tameness relative to `e` with injective `d e` on `B` tames `J z`, so `E ≥ 0` on `S`.
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := by
    refine floerEnergyDensity_nonneg hω (fun v hv ↦ ?_) (hfloer z hz)
    have hdv : mvfderiv I e (u z) v ≠ 0 := fun h0 ↦
      hv (hde _ (huB z hz) (h0.trans (map_zero _).symm))
    exact (mul_pos hc (pow_pos (norm_pos_iff.2 hdv) 2)).trans_le (hJc z hz v)
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by rwa [IntegrableOn, hS] at hA
  have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rwa [IntegrableOn, hS] at hR
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA' hR' (C := fun q ↦ |∫ t in (0 : ℝ)..1, H q t (y q t)| + 1) fun q ↦
      ((hh q).abs.eventually (Iio_mem_nhds (lt_add_one _))).mono fun _ ↦ le_of_lt
  refine ⟨y, fun q ↦ ⟨hy q, hyB q, hyu q, hyp q, hh q⟩, ?_, ?_⟩
  · rwa [IntegrableOn, hS]
  · simp only [hS]
    exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA' hR' hh

/-- **The pair-of-pants energy identity with nondegenerate asymptotic orbits, for a manifold
target.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` a `C¹`
perturbation on `S × M` equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C²`
Hamiltonians `H_q`, and `u` a `C¹` map on `S` with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with finite energy and integrable symplectic area and curvature. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`, suppose that
`c ‖d e v‖² ≤ ω(v, J z v)` on `S` with `c > 0`, that `(e ∘ u) ∘ φ'_q` has bounded derivative on
some strip `(b, ∞) × [0, 1]` at each end `q`, and that every `1`-periodic orbit of `H_q` in `B` is
nondegenerate. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic orbits
`y_q` of `H_q` in `B`, the Floer energy density of `u` is integrable on `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
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
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) :=
  hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated
    hK hKH hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB J hc hJc hfloer hE hA hR
    hC fun q ↦ hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq (hHs q)
      (hnd q)

/-- **The energy identity for `pairOfPantsPerturbation` with isolated asymptotic orbits in a
compact set.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated` to
`TauCeti.Floer.pairOfPantsPerturbation H`, whose curvature is automatically integrable along `u`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isolated
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
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
            z (u z) :=
  hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hE hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hC hiso

/-- **The energy identity for `pairOfPantsPerturbation` with nondegenerate asymptotic orbits in a
compact set.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm` to
`TauCeti.Floer.pairOfPantsPerturbation H`, whose curvature is automatically integrable along `u`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
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
            z (u z) :=
  hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isolated
    hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB J hc hJc hfloer hE hA hC fun q ↦
      hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq (hHs q) (hnd q)

/-- **The energy identity for `pairOfPantsPerturbation` on a closed manifold.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` when
`M` is compact and `B = univ`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
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
  obtain ⟨y, hy, hEint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc
      hfloer hE hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

end FiniteEnergy
end IsNondegenerate
end TauCeti.SmoothTwoForm
