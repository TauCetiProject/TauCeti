/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Geometry.Manifold.Sard.Basic
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

**Autonomous Hamiltonians without fast orbits.** Let `F : M → ℝ` be autonomous and `s ≠ 0`. The
`1`-periodic orbits of `s F` are the orbits of `X_F` of period `|s|`, run at speed `s` (backwards
when `s < 0`). Suppose that no level of `F` carries a closed characteristic contractible in `M` of
period at most `|s|` (`TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristicOfPeriodLE`), that
is, `X_F` has no nonconstant contractible periodic orbit of period at most `|s|`. Then the
contractible `1`-periodic orbits of `s F` are the constant loops at the critical points of `F`
(`contractiblePeriodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`), and for a nondegenerate weakly exact form

`spec(s F) = {-s F(x) | x a critical point of F}`

(`TauCeti.SmoothTwoForm.IsNondegenerate.contractibleActionSpectrum_smul_eq`). The critical values
of a `C^n` function on a boundaryless Lindelöf manifold of dimension `m`, with `n ≥ max m 1`, form a
null set, by Sard's theorem, so this spectrum has empty interior. Consequently, a continuous
function `ρ` on a preconnected set `S` of nonzero numbers with `ρ(s) ∈ spec(s F)` for every
`s ∈ S` is of the form `ρ(s) = -s F(x)` for a single critical point `x`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_criticalPoints_forall_eq_neg_mul`). This is how
the spectrality and continuity of a spectral invariant along the family `s F` pin its values down
to a single critical value of `F`, in Irie's proof that a homological spectral invariant bounds
the `π₁`-sensitive Hofer–Zehnder capacity.

## Main definitions

* `TauCeti.SmoothTwoForm.contractibleActionSpectrum σ H`: the contractible action spectrum.

## Main results

* `TauCeti.SmoothTwoForm.cylinderAction_mem_contractibleActionSpectrum`,
  `TauCeti.IsWeaklyExact.contractibleLoopAction_mem_contractibleActionSpectrum`: the actions of
  capped contractible `1`-periodic orbits lie in the spectrum.
* `TauCeti.SmoothTwoForm.contractibleActionSpectrum_eq_image`: for a weakly exact form, the
  spectrum is the set of actions of the capped contractible `1`-periodic orbits.
* `TauCeti.SmoothTwoForm.IsNondegenerate.finite_contractibleActionSpectrum`: the spectrum of a
  Hamiltonian with nondegenerate contractible orbits on a closed weakly exact manifold is finite.
* `contractiblePeriodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints` (in
  `TauCeti.SmoothTwoForm.IsNondegenerate`): the contractible `1`-periodic orbits of `s F` for an
  autonomous `F` without fast contractible orbits are the constant loops at its critical points.
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

/-- The action of a contractible `1`-periodic orbit capped by one of its caps lies in the
contractible action spectrum. -/
theorem cylinderAction_mem_contractibleActionSpectrum {Ham : ℝ → M → ℝ} {γ : ℝ → M}
    (hγ : γ ∈ contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham t)) 1)
    {u : ℝ × ℝ → M} (hu : IsCap I u γ) :
    cylinderAction σ.1 Ham u ∈ σ.contractibleActionSpectrum Ham :=
  ⟨γ, hγ, u, hu, rfl⟩

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

/-- For a weakly exact form, the action `A_H(γ)` (`TauCeti.contractibleLoopAction`) of a
contractible `1`-periodic orbit `γ` that bounds a cap lies in the contractible action spectrum. -/
theorem _root_.TauCeti.IsWeaklyExact.contractibleLoopAction_mem_contractibleActionSpectrum
    (hω : IsWeaklyExact σ.1) {Ham : ℝ → M → ℝ} {γ : ℝ → M}
    (hγ : γ ∈ contractiblePeriodicSolutions (fun t ↦ σ.hamiltonianVectorField (Ham t)) 1)
    {u : ℝ × ℝ → M} (hu : IsCap I u γ) :
    contractibleLoopAction σ.1 Ham γ ∈ σ.contractibleActionSpectrum Ham :=
  contractibleActionSpectrum_eq_image hω Ham ▸ mem_image_of_mem _ ⟨hγ, u, hu⟩

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

/-- **Orbits of `s F` without fast orbits of `F`.** Let `σ` be a nondegenerate two-form on a
manifold modelled on a finite-dimensional space, `F` a differentiable function and `s ≠ 0`. If no
level of `F` carries a closed characteristic contractible in `M` of period at most `|s|`, then the
contractible `1`-periodic orbits of the autonomous Hamiltonian `s F` are the constant loops at the
critical points of `F`. -/
theorem contractiblePeriodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints
    (h : σ.IsNondegenerate) (hF : MDifferentiable I 𝓘(ℝ) F) (hs : s ≠ 0)
    (hno : ∀ c, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c |s|) :
    contractiblePeriodicSolutions (fun _ ↦ σ.hamiltonianVectorField (s • F)) 1 =
      (fun x _ ↦ x) '' criticalPoints I F := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨hper, g, hg, hgγ⟩ := mem_contractiblePeriodicSolutions.1 hγ
    have hint := (mem_periodicSolutions_const_iff.1 hper).1
    -- `s F = (s * ·) ∘ F`, and the level of `γ 0` carries no closed characteristic of period
    -- at most `|s|`, so `γ` is constant.
    have hconst := h.eq_of_isMIntegralCurve_comp hF (differentiable_id.const_mul s) one_pos
      (φ := (s * ·)) hint (g := (⟨fun x ↦ ⟨x, mem_univ x⟩, by fun_prop⟩ :
        C(M, (univ : Set M))).comp g) (hg.comp_right _) hgγ fun _ ↦ by simpa using hno _
    have hγc : γ = fun _ ↦ γ 0 := funext hconst
    rw [hγc] at hint
    exact ⟨γ 0, (h.isMIntegralCurve_const_hamiltonianVectorField_smul_iff hs).1 hint, hγc.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_contractiblePeriodicSolutions.2 ⟨mem_periodicSolutions_const_iff.2
      ⟨(h.isMIntegralCurve_const_hamiltonianVectorField_smul_iff hs).2 hx, fun _ ↦ rfl⟩,
      ContinuousMap.const _ x, ⟨x, ContinuousMap.Homotopic.refl _⟩, fun _ ↦ rfl⟩

/-- **The spectrum of an autonomous Hamiltonian without fast orbits.** Let `σ` be a nondegenerate
weakly exact two-form on a manifold modelled on a finite-dimensional space, `F` a differentiable
function and `s ≠ 0`. If no level of `F` carries a closed characteristic contractible in `M` of
period at most `|s|`, then the contractible action spectrum of the autonomous Hamiltonian `s F`
consists of the values `-s F(x)` at the critical points `x` of `F`. -/
theorem contractibleActionSpectrum_smul_eq (h : σ.IsNondegenerate) (hω : IsWeaklyExact σ.1)
    (hF : MDifferentiable I 𝓘(ℝ) F) (hs : s ≠ 0)
    (hno : ∀ c, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c |s|) :
    σ.contractibleActionSpectrum (fun _ ↦ s • F) = (fun x ↦ -(s * F x)) '' criticalPoints I F := by
  have haction (x : M) :
      contractibleLoopAction σ.1 (fun _ ↦ s • F) (fun _ ↦ x) = -(s * F x) := by
    simp [hω.contractibleLoopAction_const]
  rw [contractibleActionSpectrum_eq_image hω,
    contractiblePeriodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints h hF hs hno]
  ext a
  constructor
  · rintro ⟨-, ⟨⟨x, hx, rfl⟩, -⟩, rfl⟩
    exact ⟨x, hx, (haction x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun _ ↦ x, ⟨⟨x, hx, rfl⟩, _, (isLoopCylinder_const x).isCap⟩, haction x⟩

/-- **Continuous selections of the spectra of `s F`.** Let `σ` be a nondegenerate weakly exact
two-form on a boundaryless Lindelöf manifold modelled on a space of finite dimension `m`, and `F` a
`C^n` function with `n ≥ max m 1`, the regularity of Sard's theorem. Let `S` be a nonempty
preconnected set of nonzero numbers such that, for every `s ∈ S`, no level of `F` carries a closed
characteristic contractible in `M` of period at most `|s|`. If `ρ` is continuous on `S` and `ρ(s)`
lies in the contractible action spectrum of `s F` for every `s ∈ S`, then there is a single
critical point `x` of `F` with `ρ(s) = -s F(x)` for all `s ∈ S`. -/
theorem exists_mem_criticalPoints_forall_eq_neg_mul [I.Boundaryless] [LindelofSpace M]
    (h : σ.IsNondegenerate) (hω : IsWeaklyExact σ.1) {n : ℕ} (hF : ContMDiff I 𝓘(ℝ) n F)
    (hn : max (Module.finrank ℝ E) 1 ≤ n) {S : Set ℝ} (hS : IsPreconnected S)
    (hSne : S.Nonempty) (hS0 : ∀ s ∈ S, s ≠ 0)
    (hno : ∀ s ∈ S, ∀ c, ¬σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c |s|)
    {ρ : ℝ → ℝ} (hρ : ContinuousOn ρ S)
    (hρS : ∀ s ∈ S, ρ s ∈ σ.contractibleActionSpectrum fun _ ↦ s • F) :
    ∃ x ∈ criticalPoints I F, ∀ s ∈ S, ρ s = -(s * F x) := by
  have : IsManifold I n M := IsManifold.of_le (n := ∞) (by simp)
  -- The critical values of `F` have empty interior, by Sard's theorem.
  have hnull : interior (F '' criticalPoints I F) = ∅ := by
    have hk : ((Module.finrank ℝ E - Module.finrank ℝ ℝ + 1 : ℕ) : ℕ∞ω) ≤ n := by
      rw [Module.finrank_self]
      exact_mod_cast (by omega : Module.finrank ℝ E - 1 + 1 ≤ n)
    refine ((hF.isNullSet_image_criticalPoints hk).mono
      (image_mono fun x hx ↦ ?_)).interior_eq_empty
    exact isRegularPoint_iff_notMem_criticalPoints.not_left.2 hx
  have hval (s : ℝ) (hs : s ∈ S) : ∃ x ∈ criticalPoints I F, ρ s = -(s * F x) := by
    have := hρS s hs
    rw [contractibleActionSpectrum_smul_eq h hω
      (hF.mdifferentiable (by norm_cast; omega)) (hS0 s hs) (hno s hs)] at this
    obtain ⟨x, hx, hρx⟩ := this
    exact ⟨x, hx, hρx.symm⟩
  -- `-ρ(s) / s` takes its values in the critical values of `F`, and is continuous on `S`, so it is
  -- constant there.
  have hmaps : MapsTo (fun s ↦ -(ρ s / s)) S (F '' criticalPoints I F) := fun s hs ↦ by
    obtain ⟨x, hx, hρx⟩ := hval s hs
    refine ⟨x, hx, ?_⟩
    dsimp only
    rw [hρx, neg_div, neg_neg, mul_div_cancel_left₀ _ (hS0 s hs)]
  have hcont : ContinuousOn (fun s ↦ -(ρ s / s)) S :=
    (hρ.div continuousOn_id hS0).neg
  have hsub := hS.subsingleton_image_of_interior_eq_empty hcont hmaps hnull
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨x, hx, hρx⟩ := hval s₀ hs₀
  refine ⟨x, hx, fun s hs ↦ ?_⟩
  have heq := hsub (mem_image_of_mem _ hs) (mem_image_of_mem _ hs₀)
  have hs0 := hS0 s hs
  simp only [hρx, neg_div, neg_neg, mul_div_cancel_left₀ _ (hS0 s₀ hs₀)] at heq
  rw [← heq]
  field_simp

end IsNondegenerate

end SmoothTwoForm

end TauCeti
