/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sard.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Topology.Order.IntermediateValue

/-!
# The contractible action spectrum

Let `σ` be a two-form on a manifold `M` and `H : ℝ → M → ℝ` a time-dependent Hamiltonian. The
**contractible action spectrum** of `H` (`TauCeti.SmoothTwoForm.contractibleActionSpectrum`) is
the set of capped actions `A_H(γ, u) = ∫ u^* σ - ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cylinderAction`) of
the contractible `1`-periodic orbits `γ` of the Hamiltonian vector field `X_H`, over all `C²` caps
`u` of `γ`. For a continuous weakly exact form the action does not depend on the cap, so the
spectrum is the set of actions `TauCeti.contractibleLoopAction` of these orbits
(`TauCeti.SmoothTwoForm.contractibleActionSpectrum_eq_image`), the critical values of the action
functional on contractible loops. Spectral invariants of Floer homology take their values in this
set.

On a closed manifold with a weakly exact form, a Hamiltonian whose contractible `1`-periodic
orbits are all nondegenerate has a finite spectrum
(`TauCeti.SmoothTwoForm.IsNondegenerate.finite_contractibleActionSpectrum`). Without weak
exactness, recapping an orbit by spheres of nonzero area makes the spectrum infinite.

**Autonomous Hamiltonians without fast orbits.** Let `F : M → ℝ` be autonomous and `s > 0`. The
`1`-periodic orbits of `s F` are the orbits of `X_F` of period `s`, run at speed `s`. Suppose that
no level of `F` carries a closed characteristic contractible in `M` of period at most `s`
(`TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristicOfPeriodLE`), that is, `X_F` has no
nonconstant contractible periodic orbit of period at most `s`. Then the contractible
`1`-periodic orbits of `s F` are the constant loops at the critical points of `F`, and for a
nondegenerate weakly exact form

`spec(s F) = {-s F(x) | x a critical point of F}`

(`TauCeti.SmoothTwoForm.IsNondegenerate.contractibleActionSpectrum_smul_eq`). The critical values
of a smooth function on a second countable manifold form a null set, by Sard's theorem, so this
spectrum has empty interior. Consequently, a continuous function `ρ` on a preconnected set `S` of
positive numbers with `ρ(s) ∈ spec(s F)` for every `s ∈ S` is of the form `ρ(s) = -s F(x)` for a
single critical point `x`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_criticalPoints_forall_eq_neg_mul`). This is how
the spectrality and continuity of a spectral invariant along the family `s F` pin its values down
to a single critical value of `F`, in Irie's proof that a homological spectral invariant bounds
the `π₁`-sensitive Hofer–Zehnder capacity.

## Main definitions

* `TauCeti.SmoothTwoForm.contractibleActionSpectrum σ H`: the contractible action spectrum.

## Main results

* `TauCeti.SmoothTwoForm.contractibleActionSpectrum_eq_image`: for a weakly exact form, the
  spectrum is the set of actions of the capped contractible `1`-periodic orbits.
* `TauCeti.SmoothTwoForm.IsNondegenerate.finite_contractibleActionSpectrum`: the spectrum of a
  Hamiltonian with nondegenerate contractible orbits on a closed weakly exact manifold is finite.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleActionSpectrum_smul_eq`: the spectrum of
  `s F` for an autonomous `F` without fast contractible orbits.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_criticalPoints_forall_eq_neg_mul`: a
  continuous selection of the spectra of `s F` is `s ↦ -s F(x)` for one critical point `x`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1 (Proposition 5.8 and Step 2 of the
  proof of Lemma 5.7).
* K. Irie, *Hofer–Zehnder capacity of unit disk cotangent bundles and the loop product*, J. Eur.
  Math. Soc. 16 (2014), 2477–2497.
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (the action spectrum).
-/

public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

variable (σ) in
/-- The **contractible action spectrum** of a time-dependent Hamiltonian `H` for a two-form `σ`:
the capped actions `A_H(γ, u)` (`TauCeti.cylinderAction`) of the contractible `1`-periodic orbits
`γ` of the Hamiltonian vector field of `H`, over all `C²` caps `u` of `γ`. -/
def contractibleActionSpectrum (Ham : ℝ → M → ℝ) : Set ℝ :=
  {a | ∃ γ ∈ contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham t)) 1,
    ∃ u, IsCap I u γ ∧ cylinderAction σ.1 Ham u = a}

/-- A value lies in the contractible action spectrum exactly when it is the action of a contractible
`1`-periodic orbit capped by one of its caps. -/
@[simp]
theorem mem_contractibleActionSpectrum {Ham : ℝ → M → ℝ} {a : ℝ} :
    a ∈ σ.contractibleActionSpectrum Ham ↔
      ∃ γ ∈ contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham t)) 1,
        ∃ u, IsCap I u γ ∧ cylinderAction σ.1 Ham u = a :=
  Iff.rfl

/-- For a weakly exact form the capped action does not depend on the cap, so the contractible
action spectrum is the set of actions `A_H(γ)` (`TauCeti.contractibleLoopAction`) of the
contractible `1`-periodic orbits `γ` that bound a cap. -/
theorem contractibleActionSpectrum_eq_image (hω : IsWeaklyExact σ.1) (Ham : ℝ → M → ℝ) :
    σ.contractibleActionSpectrum Ham = contractibleLoopAction σ.1 Ham ''
      {γ ∈ contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham t)) 1 |
        ∃ u, IsCap I u γ} := by
  have hω₀ : IsSmoothForm I 0 σ.1 := σ.isSmoothForm.of_le (by simp)
  ext a
  constructor
  · rintro ⟨γ, hγ, u, hu, rfl⟩
    exact ⟨γ, ⟨hγ, u, hu⟩, hω.contractibleLoopAction_eq hω₀ Ham hu⟩
  · rintro ⟨γ, ⟨hγ, u, hu⟩, rfl⟩
    exact ⟨γ, hγ, u, hu, (hω.contractibleLoopAction_eq hω₀ Ham hu).symm⟩

namespace IsNondegenerate

variable [FiniteDimensional ℝ E]

/-- **The spectrum of a nondegenerate Hamiltonian is finite.** Let `σ` be a nondegenerate weakly
exact two-form on a compact boundaryless manifold modelled on a finite-dimensional space, and `H`
a time-dependent Hamiltonian, jointly `C²` and `1`-periodic in time, whose contractible
`1`-periodic orbits are all nondegenerate. Then the contractible action spectrum of `H` is
finite. -/
theorem finite_contractibleActionSpectrum [CompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (h : σ.IsNondegenerate) (hω : IsWeaklyExact σ.1) {Ham : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 (uncurry Ham)) (hP : Periodic Ham 1)
    (hnd : ∀ γ ∈ contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (Ham t)) 0 1) (γ 0)) :
    (σ.contractibleActionSpectrum Ham).Finite :=
  contractibleActionSpectrum_eq_image hω Ham ▸
    ((h.finite_contractiblePeriodicSolutions_hamiltonianVectorField hH hP hnd).subset
      (sep_subset _ _)).image _

variable {F : M → ℝ} {s : ℝ}

/-- For `s ≠ 0`, the constant loop at `x` is a `1`-periodic orbit of `s F` exactly when `x` is a
critical point of `F`. -/
private theorem isMIntegralCurve_const_smul_iff (h : σ.IsNondegenerate) (hs : s ≠ 0) {x : M} :
    IsMIntegralCurve (fun _ : ℝ ↦ x) (σ.hamiltonianVectorField (s • F)) ↔
      x ∈ criticalPoints I F := by
  rw [isMIntegralCurve_const_iff, hamiltonianVectorField_const_smul, smul_eq_zero,
    or_iff_right hs, h.hamiltonianVectorField_eq_zero_iff, mem_criticalPoints]

/-- **Orbits of `s F` without fast orbits of `F`.** If no level of `F` carries a closed
characteristic contractible in `M` of period at most `s`, `s > 0`, then every contractible
`1`-periodic orbit of `s F` is constant. -/
private theorem eq_const_of_mem_contractiblePeriodicSolutions (h : σ.IsNondegenerate)
    (hF : MDifferentiable I 𝓘(ℝ) F) (hs : 0 < s)
    (hno : ∀ c, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c s) {γ : ℝ → M}
    (hγ : γ ∈ contractiblePeriodicSolutions (fun _ ↦ σ.hamiltonianVectorField (s • F)) 1) :
    γ = fun _ ↦ γ 0 := by
  obtain ⟨hint, g, hg, hgγ⟩ := mem_contractiblePeriodicSolutions.1 hγ
  have hint := (mem_periodicSolutions_const_iff.1 hint).1
  -- `F` is constant along `γ`, since `dF(X_{s F}) = s dF(X_F) = 0`.
  have hlev (t : ℝ) : F (γ t) = F (γ 0) :=
    (hint.isMIntegralCurveOn univ).apply_eq_of_mvfderiv_apply_eq_zero isPreconnected_univ
      (fun _ _ ↦ hF _) (fun u _ ↦ by
        rw [hamiltonianVectorField_const_smul, map_smul,
          (h.isHamiltonianVectorField_hamiltonianVectorField F).mvfderiv_apply_self, smul_zero])
      (mem_univ 0) (mem_univ t)
  -- Otherwise `t ↦ γ (t / s)` is a closed characteristic of period `s`, which is excluded.
  by_contra hne
  have hγs : IsMIntegralCurve γ (s⁻¹⁻¹ • σ.hamiltonianVectorField F) := fun t ↦ by
    rw [inv_inv, Pi.smul_apply, ← hamiltonianVectorField_const_smul]
    exact hint t
  have hc := hasContractibleClosedCharacteristicOfPeriodLE_of_isMIntegralCurve_smul one_pos
    (inv_ne_zero hs.ne') hγs (not_forall.1 fun hall ↦ hne (funext hall)) hlev
    ⟨(⟨fun x ↦ ⟨x, mem_univ x⟩, by fun_prop⟩ : C(M, (univ : Set M))).comp g, hg.comp_right _,
      hgγ⟩
  rw [abs_inv, abs_of_pos hs, div_inv_eq_mul, one_mul] at hc
  exact hno _ hc

/-- **The spectrum of an autonomous Hamiltonian without fast orbits.** Let `σ` be a nondegenerate
weakly exact two-form on a manifold modelled on a finite-dimensional space, `F` a differentiable
function and `s > 0`. If no level of `F` carries a closed characteristic contractible in `M` of
period at most `s`, then the contractible action spectrum of the autonomous Hamiltonian `s F`
consists of the values `-s F(x)` at the critical points `x` of `F`: its contractible `1`-periodic
orbits are the constant loops at these points. -/
theorem contractibleActionSpectrum_smul_eq (h : σ.IsNondegenerate) (hω : IsWeaklyExact σ.1)
    (hF : MDifferentiable I 𝓘(ℝ) F) (hs : 0 < s)
    (hno : ∀ c, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c s) :
    σ.contractibleActionSpectrum (fun _ ↦ s • F) = (fun x ↦ -(s * F x)) '' criticalPoints I F := by
  have haction (x : M) :
      contractibleLoopAction σ.1 (fun _ ↦ s • F) (fun _ ↦ x) = -(s * F x) := by
    simp [hω.contractibleLoopAction_const]
  rw [contractibleActionSpectrum_eq_image hω]
  ext a
  constructor
  · rintro ⟨γ, ⟨hγ, -⟩, rfl⟩
    have hconst := eq_const_of_mem_contractiblePeriodicSolutions h hF hs hno hγ
    have hint := (mem_periodicSolutions_const_iff.1 (contractiblePeriodicSolutions_subset hγ)).1
    rw [hconst] at hint
    exact ⟨γ 0, (isMIntegralCurve_const_smul_iff h hs.ne').1 hint, by rw [hconst, haction]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun _ ↦ x, ⟨mem_contractiblePeriodicSolutions.2 ⟨mem_periodicSolutions_const_iff.2
      ⟨(isMIntegralCurve_const_smul_iff h hs.ne').2 hx, fun _ ↦ rfl⟩,
      ContinuousMap.const _ x, ⟨x, ContinuousMap.Homotopic.refl _⟩, fun _ ↦ rfl⟩,
      _, (isLoopCylinder_const x).isCap⟩, haction x⟩

/-- **Continuous selections of the spectra of `s F`.** Let `σ` be a nondegenerate weakly exact
two-form on a boundaryless second countable manifold modelled on a finite-dimensional space, and
`F` a smooth function. Let `S` be a nonempty preconnected set of positive numbers such that, for
every `s ∈ S`, no level of `F` carries a closed characteristic contractible in `M` of period at
most `s`. If `ρ` is continuous on `S` and `ρ(s)` lies in the contractible action spectrum of `s F`
for every `s ∈ S`, then there is a single critical point `x` of `F` with `ρ(s) = -s F(x)` for all
`s ∈ S`. Indeed `-ρ(s) / s` is continuous on `S` with values in the critical values of `F`, which
have empty interior by Sard's theorem. -/
theorem exists_mem_criticalPoints_forall_eq_neg_mul [I.Boundaryless] [LindelofSpace M]
    (h : σ.IsNondegenerate) (hω : IsWeaklyExact σ.1) (hF : ContMDiff I 𝓘(ℝ) ∞ F) {S : Set ℝ}
    (hS : IsPreconnected S) (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hno : ∀ s ∈ S, ∀ c, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c s)
    {ρ : ℝ → ℝ} (hρ : ContinuousOn ρ S)
    (hρS : ∀ s ∈ S, ρ s ∈ σ.contractibleActionSpectrum fun _ ↦ s • F) :
    ∃ x ∈ criticalPoints I F, ∀ s ∈ S, ρ s = -(s * F x) := by
  -- The critical values of `F` have empty interior, by Sard's theorem.
  have hnull : interior (F '' criticalPoints I F) = ∅ := by
    refine ((hF.isNullSet_image_criticalPoints (by simp)).mono
      (image_mono fun x hx ↦ ?_)).interior_eq_empty
    exact isRegularPoint_iff_notMem_criticalPoints.not_left.2 hx
  -- `-ρ(s) / s` takes its values in the critical values of `F`.
  have hval (s : ℝ) (hs : s ∈ S) : ∃ x ∈ criticalPoints I F, ρ s = -(s * F x) := by
    have := hρS s hs
    rw [contractibleActionSpectrum_smul_eq h hω (hF.mdifferentiable (by simp)) (hSpos s hs)
      (hno s hs)] at this
    obtain ⟨x, hx, hρx⟩ := this
    exact ⟨x, hx, hρx.symm⟩
  have hmaps : MapsTo (fun s ↦ -(ρ s / s)) S (F '' criticalPoints I F) := fun s hs ↦ by
    obtain ⟨x, hx, hρx⟩ := hval s hs
    refine ⟨x, hx, ?_⟩
    dsimp only
    rw [hρx, neg_div, neg_neg, mul_div_cancel_left₀ _ (hSpos s hs).ne']
  have hcont : ContinuousOn (fun s ↦ -(ρ s / s)) S :=
    (hρ.div continuousOn_id fun s hs ↦ (hSpos s hs).ne').neg
  have hsub := hS.subsingleton_image_of_interior_eq_empty hcont hmaps hnull
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨x, hx, hρx⟩ := hval s₀ hs₀
  refine ⟨x, hx, fun s hs ↦ ?_⟩
  have heq := hsub (mem_image_of_mem _ hs) (mem_image_of_mem _ hs₀)
  have hs0 := (hSpos s hs).ne'
  simp only [hρx, neg_div, neg_neg, mul_div_cancel_left₀ _ (hSpos s₀ hs₀).ne'] at heq
  rw [← heq]
  field_simp

end IsNondegenerate

end SmoothTwoForm

end TauCeti
