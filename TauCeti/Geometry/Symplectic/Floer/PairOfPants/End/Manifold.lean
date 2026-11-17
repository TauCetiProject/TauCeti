/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback

/-!
# Asymptotic orbits at the ends of a finite-energy Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a closed symplectic manifold, and
let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in
functions on `M`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for period-one
`C¹` Hamiltonians `H_q`. Let `u : S → M` be a `C¹` solution of the Floer equation
`(du - X_K)^{0,1} = 0` for almost complex structures `J(z)` on the tangent spaces `T_{u z} M`,
with image in a compact set `B` and finite energy. This file shows that `u` breaks off a
one-periodic orbit of `H_q` at each end `q`: there are an orbit `y` in `B` and `s_n → ∞` such that
the loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
in the namespace `TauCeti.SmoothTwoForm`). On a compact manifold `B` can be the whole manifold
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`, in the same
namespace).
This is the first step of Floer breaking at the ends of a pair of pants in a closed symplectic
manifold; `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` proves it for a symplectic
vector space.

As in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`, convergence and uniform tameness
are measured through a `C¹` map `e : M → F` into a finite-dimensional normed space, injective on
`B` and with injective differential at the points of `B`: the loops converge pointwise in `M` and
uniformly after applying `e`, and the almost complex structures satisfy
`c ‖d e v‖² ≤ ω(v, J z v)` for a constant `c > 0`. On a compact Hausdorff manifold such a map
exists by Mathlib's `exists_embedding_euclidean_of_compact`.

The proof reduces each end to a finite-energy Floer half-cylinder.

* **Positive end charts.** On the end `q`, the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
  (`TauCeti.Floer.positiveEndChart`) is holomorphic, and beyond `T₀` it pulls `K` back to
  `H'_q(t) dt` for the positive end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
  (`TauCeti.Floer.positiveEndHamiltonian`). Since the perturbed derivative is natural under
  changes of domain coordinates (`TauCeti.SmoothTwoForm.perturbedMFDeriv_perturbationPullback`),
  `u ∘ φ'_q` solves the Floer equation of a half-cylinder for `H'_q`
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), and its
  energy over a half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u`
  over `S` (`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`).
  These statements are in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback`.
* **Orbits at the ends.** The half-cylinder theorem
  `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, in the
  namespace `TauCeti.SmoothTwoForm`, gives an orbit `x` of `H'_q` at the end of `u ∘ φ'_q`.
  Reading it with the time `±t` of the end gives an orbit of `H_q`, since
  `X_{H'_q(±t)} = ±X_{H_q(t)}` (`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul`).

With bounded derivative of `e ∘ u ∘ φ'_q` on a half-cylinder `s > b` and isolated (or nondegenerate
for `C²` `H_q` on a Hausdorff boundaryless manifold) subsequential-limit orbits, `t ↦ u(φ_q(±s, t))`
converges as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`
(`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually`,
`..._of_isCompact`). Null-homotopic ends admit parallel `contractiblePeriodicSolutions` theorems;
see `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Manifold` for the energy identity.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace Floer

/-- Reparametrizing a curve by `t ↦ ±t`, with the sign of the end `q`, preserves descending to a
null-homotopic map `AddCircle 1 → X`. -/
theorem exists_nullhomotopic_comp_endSign_mul_iff {X : Type*} [TopologicalSpace X]
    {q : Puncture} {γ : ℝ → X} :
    (∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ (q.endSign * t)) ↔
      ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  have fwd {δ : ℝ → X}
      (h : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ t) :
      ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ (q.endSign * t) := by
    obtain ⟨g, hg, hgδ⟩ := h
    have hex := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
    rw [abs_endSign, div_one] at hex
    obtain ⟨g', hg', hg'g⟩ := hex
    exact ⟨g', hg', fun t ↦ (hg'g t).trans (by rw [mul_comm, hgδ])⟩
  refine ⟨fun h ↦ ?_, fwd⟩
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using fwd h

/-- If `u` is continuous on `S = ℂ ∖ {0, 1}` and one end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is
null-homotopic in a locally path-connected, semilocally simply connected space `X`, then every
positive-end loop `t ↦ (u ∘ φ'_q)(s, t)` (`s > 0`) is null-homotopic in `X`. -/
theorem forall_exists_nullhomotopic_positiveEndChart {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X] {u : ℝ × ℝ → X}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture}
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t))) :
    ∀ s > 0, ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = (u ∘ positiveEndChart q) (s, t) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨s₀, hs₀, hg₀⟩ := hnull
  have hg₀' : ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = (u ∘ positiveEndChart q) (s₀, t) := by
    simpa only [comp_apply, positiveEndChart_mk] using
      exists_nullhomotopic_comp_endSign_mul_iff.2 hg₀
  exact TauCeti.forall_exists_nullhomotopic_of_isPreconnected isPreconnected_Ioi
    (u := fun s t ↦ (u ∘ positiveEndChart q) (s, t))
    (hu.comp (contDiff_positiveEndChart q 0).continuous.continuousOn
      fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal (mem_Ioi.1 hz.1))
    (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one]) hs₀ hg₀'

/-- Uniform convergence of `(u ∘ φ'_q)(r i, ·)` after `e` to `e ∘ x` transports to uniform
convergence of `t ↦ u(φ_q(±r i, t))` after `e` to `e ∘ (t ↦ x(±t))`. -/
theorem tendstoUniformly_endChart_of_positiveEndChart {X Y ι : Type*} [UniformSpace Y]
    {l : Filter ι} {u : ℝ × ℝ → X} {e : X → Y} {q : Puncture} {r : ι → ℝ} {x : ℝ → X}
    (h : TendstoUniformly (fun i t ↦ e ((u ∘ positiveEndChart q) (r i, t))) (e ∘ x) l) :
    TendstoUniformly (fun i t ↦ e (u (endChart q (q.endSign * r i, t))))
      (e ∘ fun t ↦ x (q.endSign * t)) l := by
  have hloop : (fun i t ↦ e (u (endChart q (q.endSign * r i, t)))) =
      fun i ↦ (fun t ↦ e ((u ∘ positiveEndChart q) (r i, t))) ∘ fun t ↦ q.endSign * t := by
    funext i t; simp only [comp_apply, endChart_eq_positiveEndChart]
  exact hloop ▸ h.comp fun t ↦ q.endSign * t

end Floer

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Orbits in positive end charts -/

/-- Reading a solution curve of the positive end Hamiltonian `H'_q` with the time `±t` of the end
gives a solution curve of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ) I (fun s ↦ x (q.endSign * s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  -- The velocity `±X_{H'_q(±t)}` of `x` at `±t`, rescaled by the sign of the end, is `X_{H_q(t)}`.
  have h : (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t))
            (x (q.endSign * t))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight q.endSign := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight,
      hamiltonianVectorField_positiveEndHamiltonian_endSign_mul, smul_smul]
  rw [h]
  refine (hx (q.endSign * t)).comp t (hasMFDerivAt_iff_hasFDerivAt.2 ?_)
  exact ((hasDerivAt_id' t).const_mul q.endSign).hasFDerivAt.congr_fderiv
    (ContinuousLinearMap.ext_ring (by simp))

/-- Reading a one-periodic orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the
end gives a one-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
      1) :
    (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
  mem_periodicSolutions.2
    ⟨hasMFDerivAt_comp_endSign_mul (mem_periodicSolutions.1 hx).1,
      periodic_comp_endSign_mul (mem_periodicSolutions.1 hx).2⟩

/-- A curve `x` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only if
`t ↦ x(±t)`, with the sign of the end `q`, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  have hx' : (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField
        (positiveEndHamiltonian (positiveEndHamiltonian H) q t)) 1 := by
    simpa only [positiveEndHamiltonian_positiveEndHamiltonian] using hx
  simpa only [endSign_mul_endSign_mul] using
    mem_periodicSolutions_comp_endSign_mul (H := positiveEndHamiltonian H) hx'

/-- A curve `x` is a contractible `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and
only if `t ↦ x(±t)`, with the sign of the end `q`, is a contractible `1`-periodic orbit of `H_q`. -/
theorem mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions, mem_contractiblePeriodicSolutions,
    mem_periodicSolutions_positiveEndHamiltonian_iff,
    ← exists_nullhomotopic_comp_endSign_mul_iff]

/-! ### Asymptotic orbits at the ends -/

/-- Beyond `max T₀ 0`, the positive end chart maps into `S` and transports the pair-of-pants Floer
equation to the coordinate half-cylinder Floer equation for `H'_q`. -/
private theorem floer_halfCylinder_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a)
    {J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z))}
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (positiveEndChart q z)).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ positiveEndChart q) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineReal +
          J' z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineImag -
            ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
              ((u ∘ positiveEndChart q) z)) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≠ ⊤ := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hmaps : MapsTo (positiveEndChart q) (Ioi a ×ˢ univ) thricePuncturedSphereReal :=
    fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn hmaps, fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH
      (hu.mdifferentiableOn one_ne_zero) q hHd ha₀ haT)⟩
  have hS : positiveEndChart q z ∈ thricePuncturedSphereReal := hmaps ⟨hz.1, mem_univ _⟩
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt one_ne_zero)
    (hfloer z hz)
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z (J' z)).1 hcl
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at hiff

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `ω`
be a nondegenerate two-form on a manifold `M`, let `K` be equal to `H_r(t) dt` beyond `T₀` on each
end `r`, for `1`-periodic Hamiltonians `H_r`, and let `u` be `C¹` on `S`, with image in a
compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a
`C¹` map into a finite-dimensional normed space, injective on `B` and with injective differential
at the points of `B`, and suppose that the almost complex structures are uniformly tame with
respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `S` is finite
and `H_q` is `C¹`, then at the end `q` there are a `1`-periodic orbit `y` of the Hamiltonian
vector field of `H_q` in `B` and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with the
sign of the end, converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max T₀ 0
  have ha₀ : 0 ≤ a := le_max_right T₀ 0
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀
    (le_max_left T₀ 0) (J' := J')
    (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, φ, -, hφ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc
      (fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)) v)
      hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, φ, hφ, tendstoUniformly_endChart_of_positiveEndChart hconv, fun t ↦ ?_⟩
  simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
Specialization of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to a
compact manifold `M`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE q
      hHq
  exact ⟨y, hy, h⟩

namespace IsNondegenerate

local notation "Sℝ" => thricePuncturedSphereReal
local macro "pertS(" K:term ")" : term => `(fun z x ↦ ($K) (Complex.equivRealProdCLM.symm z) x 1)
local macro "pertT(" K:term ")" : term =>
  `(fun z x ↦ ($K) (Complex.equivRealProdCLM.symm z) x Complex.I)
local macro "Orbits(" ω:term ", " H:term ", " q:term ")" : term =>
  `(periodicSolutions (fun t ↦ ($ω).hamiltonianVectorField ($H $q t)) 1)
local macro "ContrOrbits(" ω:term ", " H:term ", " q:term ")" : term =>
  `(contractiblePeriodicSolutions (fun t ↦ ($ω).hamiltonianVectorField ($H $q t)) 1)
local macro "EndLim(" e:term ", " u:term ", " q:term ", " y:term ")" : term =>
  `(TendstoUniformly (fun s t ↦ $e ($u (endChart $q (($q).endSign * s, t)))) ($e ∘ $y) atTop ∧
    ∀ t, Tendsto (fun s ↦ $u (endChart $q (($q).endSign * s, t))) atTop (𝓝 ($y t)))
local macro "SubseqEnd(" e:term ", " u:term ", " q:term ", " y:term ")" : term =>
  `(∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
    TendstoUniformly (fun n t ↦ $e ($u (endChart $q (($q).endSign * σ n, t)))) ($e ∘ $y) atTop)
local macro "SeqEndLim(" e:term ", " u:term ", " q:term ", " y:term ")" : term =>
  `(∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
    TendstoUniformly (fun n t ↦ $e ($u (endChart $q (($q).endSign * σ n, t)))) ($e ∘ $y) atTop ∧
    ∀ t, Tendsto (fun n ↦ $u (endChart $q (($q).endSign * σ n, t))) atTop (𝓝 ($y t)))
local macro "IsoEnd(" P:term ", " B:term ", " e:term ", " u:term ", " q:term ")" : term =>
  `(∀ y ∈ $P, (∀ t, y t ∈ $B) → SubseqEnd($e, $u, $q, y) →
    ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ $P, (∀ t, y' t ∈ $B) → SubseqEnd($e, $u, $q, y') → y' 0 = p → y' = y)
local macro "NullEnd(" u:term ", " q:term ")" : term =>
  `(∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), _),
    g.Nullhomotopic ∧ ∀ t : ℝ, g t = $u (endChart $q (($q).endSign * s, t)))
local macro "NondegenAt(" I:term ", " ω:term ", " H:term ", " q:term ", " y:term ")" : term =>
  `(IsNondegenerateFixedPt $I
    (timeDependentFlowOf (fun t ↦ ($ω).hamiltonianVectorField ($H $q t)) 0 1) ($y 0))
local macro "FloerS(" ω:term ", " K:term ", " u:term ", " J:term ")" : term =>
  `(∀ z ∈ Sℝ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) ($J z)
    (($ω).perturbedMFDeriv pertS($K) pertT($K) $u z).toLinearMap)
local macro "FinEnergy(" ω:term ", " K:term ", " u:term ")" : term =>
  `(∫⁻ z in Sℝ, ENNReal.ofReal (($ω).floerEnergyDensity pertS($K) pertT($K) $u z) ≠ ⊤)

variable {B : Set M} {u : ℝ × ℝ → M} {c : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [NormedSpace ℝ F] in
/-- Transport an orbit-isolation hypothesis from `endChart q` to `positiveEndChart q` via
reparametrizing time by `t ↦ q.endSign * t`. -/
private theorem eventually_eq_positiveEndChart_of_endChart {q : Puncture}
    {P Q : Set (ℝ → M)} (hPQ : ∀ x ∈ P, (fun t ↦ x (q.endSign * t)) ∈ Q) {a : ℝ}
    (hiso : IsoEnd(Q, B, e, u, q)) {x : ℝ → M} (hx : x ∈ P) (hxB : ∀ t, x t ∈ B)
    (hlim : ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
      TendstoUniformly (fun n t ↦ e ((u ∘ positiveEndChart q) (φ n, t))) (e ∘ x) atTop) :
    ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ P, (∀ t, x' t ∈ B) →
      (∃ ψ : ℕ → ℝ, (∀ n, a < ψ n) ∧ Tendsto ψ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e ((u ∘ positiveEndChart q) (ψ n, t))) (e ∘ x') atTop) →
      x' 0 = p → x' = x := by
  obtain ⟨φ, -, hφtop, hφx⟩ := hlim
  have hev := hiso (fun t ↦ x (q.endSign * t)) (hPQ x hx) (fun t ↦ hxB _)
    ⟨φ, hφtop, tendstoUniformly_endChart_of_positiveEndChart hφx⟩
  rw [mul_zero] at hev
  refine hev.mono fun p hp x' hx' hx'B ⟨ψ, _, hψtop, hψx'⟩ hx'p ↦ funext fun t ↦ ?_
  have h := congrFun (hp (fun s ↦ x' (q.endSign * s)) (hPQ x' hx') (fun s ↦ hx'B _)
    ⟨ψ, hψtop, tendstoUniformly_endChart_of_positiveEndChart hψx'⟩
    (by simpa only [mul_zero] using hx'p)) (q.endSign * t)
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using h

omit [FiniteDimensional ℝ F] [NormedSpace ℝ F] in
/-- Nondegeneracy of a `C²` end Hamiltonian isolates orbits at time `0` in `P`. -/
private theorem iso_of_nondegenerate [T2Space M] [BoundarylessManifold I M]
    (hω : ω.IsNondegenerate) {q : Puncture}
    (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    {P : Set (ℝ → M)} (hP : P ⊆ Orbits(ω, H, q)) {y : ℝ → M} (hy : y ∈ P)
    (hnd : NondegenAt(I, ω, H, q, y)) :
    ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ P, y' 0 = p → y' = y := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq.of_le (by norm_num))
  exact (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt hX
    (mem_periodicSolutions.1 (hP hy)).1 (s := 0) (T := 1)
    (by simpa only [zero_add] using hnd.eventually_not_isFixedPt)).mono
    fun _ hp y' hy' hy'p ↦ hp y' (hP hy') hy'p

section Compact

variable (hω : ω.IsNondegenerate)
  (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
    K w x = H q (q.endCoord w).im x • q.endAngularForm w)
  (hH : ∀ q, Periodic (H q) 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B)
  (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
  (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Sℝ) (huB : ∀ z ∈ Sℝ, u z ∈ B)
  (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
  (hfloer : FloerS(ω, K, u, J)) (hE : FinEnergy(ω, K, u)) (q : Puncture)

include he hB he_inj hu huB in
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- If one end loop `t ↦ u(φ_q(±s, t))` (`s > 0`) is null-homotopic, any uniform limit along `e`
of end loops as the radial parameter tends to `∞` solving the Hamiltonian ODE is contractible. -/
private theorem mem_contractible_endChart {ι : Type*} {l : Filter ι} [NeBot l]
    {r : ι → ℝ} (hr : Tendsto r l atTop) (hnull : NullEnd(u, q))
    {y : ℝ → M} (hy : y ∈ Orbits(ω, H, q)) (hyB : ∀ t, y t ∈ B)
    (hconv : TendstoUniformly (fun i t ↦ e (u (endChart q (q.endSign * r i, t)))) (e ∘ y) l) :
    y ∈ ContrOrbits(ω, H, q) := by
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have := isCompact_iff_compactSpace.1 hB
  have hind : IsInducing fun p : B ↦ e p :=
    ((he.continuous.comp continuous_subtype_val).isClosedEmbedding fun p r h ↦
      Subtype.ext (he_inj p.2 r.2 h)).isInducing
  have hpos := hr.eventually (eventually_gt_atTop (0 : ℝ))
  have hall : ∀ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)) := fun s hs ↦ by
    simpa only [comp_apply, endChart_eq_positiveEndChart] using
      exists_nullhomotopic_comp_endSign_mul_iff.2
        (forall_exists_nullhomotopic_positiveEndChart hu.continuousOn hnull s hs)
  exact mem_contractiblePeriodicSolutions_of_tendstoUniformly hy zero_lt_one hyB hind
    (hpos.mono fun _ hi t ↦ huB _ (endChart_mem_thricePuncturedSphereReal
      (by simpa only [← mul_assoc, endSign_mul_self, one_mul] using hi)))
    hconv (hpos.mono fun _ hi ↦ hall _ hi).frequently

include hω hKH hH he hB he_inj hde hu huB J hfloer hE q

/-- **Breaking off a contractible periodic orbit at a contractible end of a Floer pair of pants.**
Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, if one end loop
`t ↦ u(φ_q(±s, t))` (`s > 0`) is null-homotopic, then the subsequential limit orbit is contractible.
-/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hc : 0 < c)
    (hJc : ∀ z ∈ Sℝ, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) (hnull : NullEnd(u, q)) :
    ∃ y ∈ ContrOrbits(ω, H, q), (∀ t, y t ∈ B) ∧ SeqEndLim(e, u, q, y) := by
  obtain ⟨y, hy, hyB, σ, hσ, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH he hB
      he_inj hde hu huB J hc hJc hfloer hE q hHq
  exact ⟨y, mem_contractible_endChart he hB he_inj hu huB q hσ hnull hy hyB hconv, hyB,
    σ, hσ, hconv, hpt⟩

section AtTop

variable {b C : ℝ}
  (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
  (hc : 0 < c)
  (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
    c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))

include hC hc hJc

/-- **Convergence of an end of a Floer pair of pants to an isolated periodic orbit.** Fix an end `q`
with `H_q` `C¹`, uniformly tame `J`, and bounded derivative of `e ∘ u ∘ φ'_q` on `s > b`. If every
subsequential uniform-limit `1`-periodic orbit in `B` is isolated at time `0`, then `t ↦ u(φ_q(±s,
t))` converges as `s → ∞` to a single orbit in `B`, pointwise in `M` and uniformly after `e`. -/
theorem
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
    (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (hiso : IsoEnd(Orbits(ω, H, q), B, e, u, q)) :
    ∃ y ∈ Orbits(ω, H, q), (∀ t, y t ∈ B) ∧ EndLim(e, u, q, y) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right T₀ 0).trans (le_max_left _ b)
  have hab : ∀ z : ℝ × ℝ, a < z.1 → b < z.1 := fun _ hz ↦ (le_max_right _ b).trans_lt hz
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀
    ((le_max_left T₀ 0).trans (le_max_left _ b)) (J' := J')
    (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact_of_eventually
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde hu'
      (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (fun z hz ↦ hC z (hab z hz.1))
      fun x hx hxB hlim ↦ eventually_eq_positiveEndChart_of_endChart
        (fun _ ↦ mem_periodicSolutions_positiveEndHamiltonian_iff.1) hiso hx hxB hlim
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, tendstoUniformly_endChart_of_positiveEndChart hux, fun t ↦ ?_⟩
  simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of a contractible end of a pair of pants to an isolated contractible orbit.**
Variant of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually`
requiring isolation only on `contractiblePeriodicSolutions` when an end loop is null-homotopic. -/
theorem exists_mem_contractiblePeriodicSolutions_endChart_atTop_of_floer_of_isCompact_of_eventually
    (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) (hnull : NullEnd(u, q))
    (hiso : IsoEnd(ContrOrbits(ω, H, q), B, e, u, q)) :
    ∃ y ∈ ContrOrbits(ω, H, q), (∀ t, y t ∈ B) ∧ EndLim(e, u, q, y) := by
  obtain ⟨y, hy, hyB, hconv, hpt⟩ :=
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
      hω hKH hH he hB he_inj hde hu huB J hfloer hE q hC hc hJc hHq
      fun y hy hyB ⟨σ, hσ, hσy⟩ ↦
        (hiso y (mem_contractible_endChart he hB he_inj hu huB q hσ hnull hy hyB hσy) hyB
            ⟨σ, hσ, hσy⟩).mono
          fun _ hp y' hy' hy'B ⟨τ, hτ, hτy'⟩ hy'p ↦
            hp y' (mem_contractible_endChart he hB he_inj hu huB q hτ hnull hy' hy'B hτy') hy'B
              ⟨τ, hτ, hτy'⟩ hy'p
  exact ⟨y, mem_contractible_endChart he hB he_inj hu huB q tendsto_id hnull hy hyB hconv, hyB,
    hconv, hpt⟩

section Nondegenerate

variable [T2Space M] [BoundarylessManifold I M]
  (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))

include hHq

/-- **Convergence of an end of a Floer pair of pants to a nondegenerate periodic orbit.** Corollary
for a `C²` Hamiltonian `H_q` on a Hausdorff boundaryless manifold whose `1`-periodic orbits in `B`
are nondegenerate fixed points of `timeDependentFlowOf X_{H_q} 0 1`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    (hnd : ∀ y ∈ Orbits(ω, H, q), (∀ t, y t ∈ B) → NondegenAt(I, ω, H, q, y)) :
    ∃ y ∈ Orbits(ω, H, q), (∀ t, y t ∈ B) ∧ EndLim(e, u, q, y) :=
  exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
    hω hKH hH he hB he_inj hde hu huB J hfloer hE q hC hc hJc (hHq.of_le one_le_two)
    fun y hy hyB _ ↦ (iso_of_nondegenerate hω hHq Subset.rfl hy (hnd y hy hyB)).mono
      fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- **Convergence of a contractible end of a Floer pair of pants to a nondegenerate contractible
orbit.** Corollary for a `C²` `H_q` assuming nondegeneracy only on `contractiblePeriodicSolutions`.
-/
theorem
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    (hnull : NullEnd(u, q))
    (hnd : ∀ y ∈ ContrOrbits(ω, H, q), (∀ t, y t ∈ B) → NondegenAt(I, ω, H, q, y)) :
    ∃ y ∈ ContrOrbits(ω, H, q), (∀ t, y t ∈ B) ∧ EndLim(e, u, q, y) :=
  hω.exists_mem_contractiblePeriodicSolutions_endChart_atTop_of_floer_of_isCompact_of_eventually
    hKH hH he hB he_inj hde hu huB J hfloer hE q hC hc hJc (hHq.of_le one_le_two) hnull
    fun y hy hyB _ ↦ (iso_of_nondegenerate hω hHq contractiblePeriodicSolutions_subset hy
      (hnd y hy hyB)).mono fun _ hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

end Nondegenerate

end AtTop

end Compact

section Closed

variable [CompactSpace M] (hω : ω.IsNondegenerate)
  (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
    K w x = H q (q.endCoord w).im x • q.endAngularForm w)
  (hH : ∀ q, Periodic (H q) 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
  (hde : ∀ p, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Sℝ)
  (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
  (hfloer : FloerS(ω, K, u, J)) (hE : FinEnergy(ω, K, u)) (q : Puncture)

include hω hKH hH he he_inj hde hu J hfloer hE q

/-- Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to a
compact manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer
    (hc : 0 < c)
    (hJc : ∀ z ∈ Sℝ, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) (hnull : NullEnd(u, q)) :
    ∃ y ∈ ContrOrbits(ω, H, q), SeqEndLim(e, u, q, y) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
      hKH hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer
      hE q hc hJc hHq hnull
  exact ⟨y, hy, h⟩

section Nondegenerate

variable [T2Space M] [BoundarylessManifold I M]
  (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
  {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
  (hc : 0 < c)
  (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
    c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))

include hHq hC hc hJc

/-- Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` to a compact
Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    (hnd : ∀ y ∈ Orbits(ω, H, q), NondegenAt(I, ω, H, q, y)) :
    ∃ y ∈ Orbits(ω, H, q), EndLim(e, u, q, y) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE
      q hC hc hJc hHq fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

/-- Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` to
a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    (hnull : NullEnd(u, q)) (hnd : ∀ y ∈ ContrOrbits(ω, H, q), NondegenAt(I, ω, H, q, y)) :
    ∃ y ∈ ContrOrbits(ω, H, q), EndLim(e, u, q, y) := by
  obtain ⟨y, hy, -, h⟩ :=
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hω hKH hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J
      hfloer hE q hC hc hJc hHq hnull fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

end Nondegenerate

end Closed

end IsNondegenerate

end SmoothTwoForm

end TauCeti
