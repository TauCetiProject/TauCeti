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
# Asymptotic periodic orbits at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a symplectic
manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`, equal to
`H_q(t) dt` beyond some height `T₀` on each end `q` for `1`-periodic Hamiltonians `H_q`, and let
`u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` with image in a compact set
`B ⊆ M` and finite energy. This file proves that `u` breaks off a `1`-periodic orbit of `X_{H_q}`
along each end `q`, and converges along the whole end `s → ∞` when the `1`-periodic orbits of `H_q`
in `B` arising as subsequential uniform limits (or the contractible `1`-periodic orbits when an end
loop is null-homotopic) are isolated or nondegenerate. The manifold pair-of-pants energy identity
and topological energy lower bound at these asymptotic periodic orbits are derived in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Manifold`; the vector-space counterparts are
in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`.

**Positive end charts.** In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), with the sign `+1` on the input ends `0`, `1` and `-1` on the
output end `∞`, every end has `s → +∞`, and beyond `T₀` the pulled-back perturbation is
`H'_q(t) dt` for `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). By the
conformal naturality of `SmoothTwoForm.perturbedMFDeriv` and `SmoothTwoForm.floerEnergyDensity`:

* `u ∘ φ'_q` has perturbed derivative `(du - X_K) ∘ dφ'_q`
  (`SmoothTwoForm.perturbedMFDeriv_comp_positiveEndChart`) and solves the half-cylinder Floer
  equation for `H'_q` beyond `T₀`
  (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`);
* its energy density is multiplied by `det dφ'_q > 0`
  (`SmoothTwoForm.floerEnergyDensity_comp_positiveEndChart`), so its energy over `(a, ∞) × [0, 1]`
  for `a ≥ max T₀ 0` is at most the energy of `u` over `S`
  (`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`).

**Asymptotic periodic orbits.** Reading a `1`-periodic orbit of `H'_q` with the time `±t` of the
end gives a `1`-periodic orbit of `H_q`, and vice versa, preserving contractibility
(`SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`,
`SmoothTwoForm.mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff`). Measuring uniform
convergence and uniform tameness near `B` through a `C¹` map `e : M → F` injective on `B` with
injective differential on `B`, the manifold half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` apply to `u ∘ φ'_q`:

* without nondegeneracy or derivative bounds, for `C¹` Hamiltonians `H_q`, there are a `1`-periodic
  orbit `y_q` of `X_{H_q}` in `B` and `s_n → ∞` such that the end loops `t ↦ u(φ_q(±s_n, t))`
  converge to `y_q` pointwise in `M` and uniformly after `e`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`),
  and `y_q` is contractible when an end loop is null-homotopic in `M`
  (`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`);
* when `e ∘ u ∘ φ'_q` has bounded derivative on some half-cylinder `s > b` and the `1`-periodic
  orbits of `H_q` in `B` arising as subsequential uniform limits along `endChart q` are isolated
  (or nondegenerate for `C²` Hamiltonians on a Hausdorff boundaryless manifold), the end loops
  `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y_q` of `X_{H_q}` in `B`
  (see
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually`
  and `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, along
  with their `contractiblePeriodicSolutions` counterparts requiring isolation or nondegeneracy only
  on contractible `1`-periodic orbits when an end loop is null-homotopic).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti.Floer

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

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

section Smooth

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}

/-! ### Orbits in positive end charts -/

/-- Reading a solution curve of the positive end Hamiltonian `H'_q` with the time `±t` of the end
gives a solution curve of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ x (q.endSign * s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  have hmul : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id t).const_mul q.endSign)
  have hH : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, positiveEndHamiltonian_apply, ← mul_assoc,
      endSign_mul_self, one_mul]
  set v := ω.hamiltonianVectorField (H q t) (x (q.endSign * t))
  have hlin : (((1 : ℝ →L[ℝ] ℝ).smulRight (q.endSign • v)).comp
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :
        ℝ →L[ℝ] TangentSpace I (x (q.endSign * t))) = (1 : ℝ →L[ℝ] ℝ).smulRight v := by
    refine ContinuousLinearMap.ext fun r : ℝ ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul, smul_smul]
    exact congrArg (· • v) (by linear_combination r * q.endSign_mul_self)
  refine ((hx (q.endSign * t)).comp t hmul).congr_mfderiv ?_
  rw [hH, hamiltonianVectorField_const_smul]
  exact hlin

/-- A curve `x` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only if
`t ↦ x(±t)`, with the sign of the end `q`, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨fun hx ↦ mem_periodicSolutions.2
    ⟨hasMFDerivAt_comp_endSign_mul (mem_periodicSolutions.1 hx).1,
      periodic_comp_endSign_mul (mem_periodicSolutions.1 hx).2⟩, fun hx ↦ ?_⟩
  -- Passing to the positive end Hamiltonian a second time recovers `H_q` and `x`.
  have hH : positiveEndHamiltonian (positiveEndHamiltonian H) q = H q := by
    funext t y
    simp only [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul]
  have hx' : (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField
        (positiveEndHamiltonian (positiveEndHamiltonian H) q t)) 1 := by
    rwa [hH]
  have hxx : (fun t ↦ x (q.endSign * (q.endSign * t))) = x := by
    funext t
    rw [← mul_assoc, endSign_mul_self, one_mul]
  rw [← hxx]
  exact mem_periodicSolutions.2
    ⟨hasMFDerivAt_comp_endSign_mul (H := positiveEndHamiltonian H) (mem_periodicSolutions.1 hx').1,
      periodic_comp_endSign_mul (x := fun t ↦ x (q.endSign * t)) (mem_periodicSolutions.1 hx').2⟩

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

/-! ### The ends of a Floer pair of pants as Floer half-cylinders -/

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the global coordinate are differentiable
in the target point whenever `H_q` is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) =
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im := by
    funext x
    rw [hKH q _ x hre, smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact (hHd _ y).const_smul _

/-- Beyond `T₀` on the positive end `q`, the half-cylinder perturbed derivative of `u ∘ φ'_q` for
`H'_q` coincides with the perturbed derivative for the pulled-back datum `(φ'_q)^*K`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq_perturbationPullback
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
  have hs : (fun _ : M ↦ (0 : ℝ)) = perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ :=
    funext fun x ↦ (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x).symm
  have ht : positiveEndHamiltonian H q ζ.2 = perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ :=
    funext fun x ↦
      (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x).symm
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hs, ht]

/-- **The perturbed derivative in a positive end chart.** Where `K = H_q(t) dt` beyond `T₀` on each
end `q`, the half-cylinder perturbed derivative of `u ∘ φ'_q` for `H'_q` at a point `ζ` with
`ζ.1 ≥ T₀` is `(du - X_K) ∘ dφ'_q`. No nondegeneracy of `ω` is needed. -/
theorem perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ)) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      (ω.perturbedMFDeriv
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).comp (fderiv ℝ (positiveEndChart q) ζ) := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq_perturbationPullback hKH hH hζ]
  exact ω.perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** Let
`K = H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve `(du - X_K)^{0,1} = 0` at `φ'_q(ζ)`
with `ζ.1 ≥ T₀` for an almost complex structure `J` on `T_{u(φ'_q(ζ))} M`. Then `u ∘ φ'_q` solves
the half-cylinder Floer equation for `H'_q` at `ζ`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [ω.perturbedMFDeriv_comp_positiveEndChart hKH hH hHd hζ hu,
    ContinuousLinearMap.toLinearMap_comp]
  exact hfloer.comp (isComplexLinearMap_fderiv_positiveEndChart q ζ)

/-- **The energy density in a positive end chart.** Beyond `T₀` on each end `q`, the half-cylinder
Floer energy density of `u ∘ φ'_q` for `H'_q` at `ζ` is `det dφ'_q(ζ)` times the energy density of
`u` at `φ'_q(ζ)`. No nondegeneracy of `ω` is needed. -/
theorem floerEnergyDensity_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      (fderiv ℝ (positiveEndChart q) ζ).det * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
  rw [floerEnergyDensity_def,
    perturbedMFDeriv_comp_positiveEndChart_eq_perturbationPullback hKH hH hζ,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)

/-- **The energy of an end of a Floer pair of pants in a manifold.** Where `K = H_q(t) dt` beyond
`T₀` on each end `q`, the energy of `u ∘ φ'_q` for `H'_q` over `(a, ∞) × [0, 1]` with
`a ≥ max T₀ 0` is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    (q : Puncture) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t)) {a : ℝ} (ha₀ : 0 ≤ a)
    (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
    intro ζ hζ
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hζ.1)
    rw [abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_comp_positiveEndChart hKH hH hHd (haT.trans hζ.1.le)
      ((hu _ hS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

/-! ### Asymptotic periodic orbits at the ends -/

section Asymptotics

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {e : M → F} {B : Set M} {u : ℝ × ℝ → M} {c : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Beyond `max T₀ 0`, the positive end chart maps into `S` and transports the pair-of-pants Floer
equation to the coordinate half-cylinder Floer equation for `H'_q`. -/
private theorem floer_halfCylinder_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t) := fun t ↦
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

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `ω` be a nondegenerate two-form on `M`, let `K = H_r(t) dt` beyond `T₀` on each end `r` for
`1`-periodic Hamiltonians `H_r`, and let `u` be `C¹` on `S`, with image in a compact set `B ⊆ M`,
solving `(du - X_K)^{0,1} = 0` on `S` with finite energy for almost complex structures uniformly
tame through a `C¹` map `e : M → F` injective on `B` with injective differential on `B`. If `H_q`
is `C¹` on a given end `q`, there are a `1`-periodic orbit `y` of `X_{H_q}` in `B` and `s_n → ∞`
such that the loops `t ↦ u(φ_q(±s_n, t))` converge to `y` pointwise in `M` and uniformly after
applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max T₀ 0
  have ha₀ : 0 ≤ a := le_max_right T₀ 0
  have haT : T₀ ≤ a := le_max_left T₀ 0
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀ haT
    (J' := J') (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal
      (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc
      (fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)) v)
      hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · have hloop : (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) =
        fun n ↦ (fun t ↦ e ((u ∘ positiveEndChart q) (σ n, t))) ∘ fun t ↦ q.endSign * t := by
      funext n t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [hloop]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off a periodic orbit at each
end.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to a compact
manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE q
      hHq
  exact ⟨y, hy, h⟩

/-- **Convergence of an end of a Floer pair of pants in a manifold to an isolated periodic orbit.**
Let `K = H_r(t) dt` beyond `T₀` on each end `r` for `1`-periodic Hamiltonians `H_r`, and let `u` be
`C¹` on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite
energy. Fix an end `q` with `H_q` `C¹`, and suppose that on some half-cylinder `s > b` of the
positive end chart `φ'_q` the almost complex structures are uniformly tame and `e ∘ u ∘ φ'_q` has
bounded derivative, and that every `1`-periodic orbit of `X_{H_q}` in `B` arising as a
subsequential uniform limit along `endChart q` is isolated at time `0` among such `1`-periodic
orbits in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic
orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly after applying `e`. -/
theorem
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
        y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right T₀ 0).trans (le_max_left _ b)
  have haT : T₀ ≤ a := (le_max_left T₀ 0).trans (le_max_left _ b)
  have hab : ∀ z : ℝ × ℝ, a < z.1 → b < z.1 := fun _ hz ↦ (le_max_right _ b).trans_lt hz
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀ haT
    (J' := J') (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal
      (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact_of_eventually
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE' (fun z hz ↦ hC z (hab z hz.1))
      fun x hx hxB ⟨φ, _, hφtop, hφx⟩ ↦ by
        have hev := hiso (fun t ↦ x (q.endSign * t))
          (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx) (fun t ↦ hxB _)
          ⟨φ, hφtop, tendstoUniformly_endChart_of_positiveEndChart hφx⟩
        rw [mul_zero] at hev
        refine hev.mono fun p hp x' hx' hx'B ⟨ψ, _, hψtop, hψx'⟩ hx'p ↦ funext fun t ↦ ?_
        have h := congrFun (hp (fun s ↦ x' (q.endSign * s))
          (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx') (fun s ↦ hx'B _)
          ⟨ψ, hψtop, tendstoUniformly_endChart_of_positiveEndChart hψx'⟩
          (by simpa only [mul_zero] using hx'p)) (q.endSign * t)
        simpa only [← mul_assoc, endSign_mul_self, one_mul] using h
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, tendstoUniformly_endChart_of_positiveEndChart hux, fun t ↦ ?_⟩
  simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate periodic
orbit.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, let
`K = H_r(t) dt` beyond `T₀` on each end `r` for `1`-periodic Hamiltonians `H_r`, and let `u` be `C¹`
on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite
energy. Fix an end `q` with `H_q` `C²`; if on some half-cylinder `s > b` of `φ'_q` the almost
complex structures are uniformly tame and `e ∘ u ∘ φ'_q` has bounded derivative, and every
`1`-periodic orbit `y` of `X_{H_q}` in `B` has `y 0` a nondegenerate fixed point of
`timeDependentFlowOf X_{H_q} 0 1`, then `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single
`1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly after `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq.of_le (by norm_num))
  exact
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
      hω hKH hH he hB he_inj hde hu huB J hfloer hE q (hHq.of_le one_le_two) hC hc hJc
      fun y hy hyB _ ↦
        (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt hX
          (mem_periodicSolutions.1 hy).1 (s := 0) (T := 1)
          (by simpa only [zero_add] using (hnd y hy hyB).eventually_not_isFixedPt)).mono
          fun p hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- **Convergence of an end of a Floer pair of pants in a closed manifold to a nondegenerate
periodic orbit.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` to a compact
Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE
      q hHq hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

/-- **Breaking off a contractible periodic orbit at a contractible end of a Floer pair of pants.**
Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, if one end loop
`t ↦ u(φ_q(±s, t))` (`s > 0`) on the end `q` is null-homotopic in `M`, then there are a
contractible `1`-periodic orbit `y` of `X_{H_q}` in `B` and `s_n → ∞` along which the end loops
converge to `y` pointwise in `M` and uniformly after `e`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t))) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  set a := max T₀ 0
  have ha₀ : 0 ≤ a := le_max_right T₀ 0
  have haT : T₀ ≤ a := le_max_left T₀ 0
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀ haT
    (J' := J') (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal
      (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      ⟨a + 1, lt_add_one a, forall_exists_nullhomotopic_positiveEndChart hu.continuousOn hnull
        (a + 1) (by linarith)⟩
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc
      (fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)) v)
      hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t),
    mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx, fun t ↦ hxB _, σ, hσ,
    tendstoUniformly_endChart_of_positiveEndChart hux, fun t ↦ ?_⟩
  simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Breaking off a contractible periodic orbit at a contractible end in a closed manifold.**
Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to a
compact manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t))) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
      hKH hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc
      hfloer hE q hHq hnull
  exact ⟨y, hy, h⟩

/-- **Convergence of a contractible end of a Floer pair of pants in a manifold to an isolated
contractible periodic orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually`,
if one end loop `t ↦ u(φ_q(±s, t))` (`s > 0`) is null-homotopic in `M` and isolation at time `0` is
assumed only for contractible `1`-periodic orbits of `X_{H_q}` in `B` arising as subsequential
uniform limits along `endChart q`, then the end loops converge as `s → ∞` to a single contractible
`1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly after `e`. -/
theorem exists_mem_contractiblePeriodicSolutions_endChart_atTop_of_floer_of_isCompact_of_eventually
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) →
          (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
            TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
          y' 0 = p → y' = y) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right T₀ 0).trans (le_max_left _ b)
  have haT : T₀ ≤ a := (le_max_left T₀ 0).trans (le_max_left _ b)
  have hab : ∀ z : ℝ × ℝ, a < z.1 → b < z.1 := fun _ hz ↦ (le_max_right _ b).trans_lt hz
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀ haT
    (J' := J') (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal
      (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isCompact_of_eventually
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      ⟨a + 1, lt_add_one a, forall_exists_nullhomotopic_positiveEndChart hu.continuousOn hnull
        (a + 1) (by linarith)⟩
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE' (fun z hz ↦ hC z (hab z hz.1))
      fun x hx hxB ⟨φ, _, hφtop, hφx⟩ ↦ by
        have hev := hiso (fun t ↦ x (q.endSign * t))
          (mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx) (fun t ↦ hxB _)
          ⟨φ, hφtop, tendstoUniformly_endChart_of_positiveEndChart hφx⟩
        rw [mul_zero] at hev
        refine hev.mono fun p hp x' hx' hx'B ⟨ψ, _, hψtop, hψx'⟩ hx'p ↦ funext fun t ↦ ?_
        have h := congrFun (hp (fun s ↦ x' (q.endSign * s))
          (mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx') (fun s ↦ hx'B _)
          ⟨ψ, hψtop, tendstoUniformly_endChart_of_positiveEndChart hψx'⟩
          (by simpa only [mul_zero] using hx'p)) (q.endSign * t)
        simpa only [← mul_assoc, endSign_mul_self, one_mul] using h
  refine ⟨fun t ↦ x (q.endSign * t),
    mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff.1 hx, fun t ↦ hxB _,
    tendstoUniformly_endChart_of_positiveEndChart hux, fun t ↦ ?_⟩
  simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of a contractible end of a Floer pair of pants in a manifold to a nondegenerate
contractible periodic orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, if one end
loop `t ↦ u(φ_q(±s, t))` (`s > 0`) is null-homotopic in `M` and nondegeneracy at time `0` is assumed
only on `contractiblePeriodicSolutions`, then `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single
contractible `1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly after
`e`. -/
theorem
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq.of_le (by norm_num))
  exact
    hω.exists_mem_contractiblePeriodicSolutions_endChart_atTop_of_floer_of_isCompact_of_eventually
      hKH hH he hB he_inj hde hu huB J hfloer hE q (hHq.of_le one_le_two) hnull hC hc hJc
      fun y hy hyB _ ↦
        (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt hX
          (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset hy)).1 (s := 0) (T := 1)
          (by simpa only [zero_add] using (hnd y hy hyB).eventually_not_isFixedPt)).mono
          fun p hp y' hy' _ _ hy'p ↦ hp y' (contractiblePeriodicSolutions_subset hy') hy'p

/-- **Convergence of a contractible end of a Floer pair of pants in a closed manifold to a
nondegenerate contractible periodic orbit.** Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` to
a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hω hKH hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer
      hE q hHq hnull hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

end IsNondegenerate

end Asymptotics

end Smooth

end TauCeti.SmoothTwoForm
