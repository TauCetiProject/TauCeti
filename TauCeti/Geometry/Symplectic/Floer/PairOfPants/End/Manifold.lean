/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Homotopy
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.PeriodicOrbit
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Topology.Compactness.Compact

/-!
# Asymptotic orbits at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`
equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for period-one Hamiltonians `H_q` on
`M`, and let `u : S → M` solve the Floer equation `(du - X_K)^{0,1} = 0` with finite energy and
image in a compact set `B ⊆ M`. This file proves that `u` breaks off a `1`-periodic orbit of `H_q`
at each end `q`, and converges along the whole end when `(e ∘ u) ∘ φ'_q` has bounded derivative on a
half-cylinder and the `1`-periodic orbits of `H_q` in `B` are isolated or nondegenerate.

The vector-space counterparts are `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`. On a manifold target, uniform
convergence and uniform tameness near `B` are measured through a `C¹` map `e : M → F` into a
finite-dimensional normed space, injective on `B` and with injective differential at the points of
`B`. On a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`.

**Positive end charts.** On the end `q`, the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), with the sign `+1` on the input ends `0`, `1` and `-1` on the
output end `∞`, is holomorphic, and beyond `T₀` it pulls `K` back to `H'_q(t) dt` for the positive
end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). By
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback`, `u ∘ φ'_q` solves the half-cylinder
Floer equation for `H'_q`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`,
`TauCeti.SmoothTwoForm.floer_halfCylinder_comp_positiveEndChart`), and its energy over
`(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). By
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.PeriodicOrbit`, reading a `1`-periodic orbit of
`H'_q` with the time `±t` of the end gives a `1`-periodic orbit of `H_q`, and vice versa
(`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul` and
`TauCeti.SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`).

**Orbits and convergence at the ends.** Applying the manifold half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` to `u ∘ φ'_q` gives, at each end `q`:

* along a sequence `s_n → ∞`, uniform convergence (after `e`) and pointwise convergence in `M` of
  the end loops `t ↦ u(φ_q(±s_n, t))` to a `1`-periodic orbit of `H_q` in `B`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`). Only the part of the domain along the end matters:
  the same holds for a map defined only on an open set containing the part `±s > a` of one end
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen`), which applies to
  the ends of other punctured spheres built from `S`;
* along the whole end `s → ∞`, when `(e ∘ u) ∘ φ'_q` has bounded derivative on a half-cylinder and
  the `1`-periodic orbits of `H_q` in `B` are isolated — in particular when `H_q` is `C²` on a
  Hausdorff boundaryless manifold and each `1`-periodic orbit in `B` starts at a nondegenerate
  fixed point of `timeDependentFlowOf X_{H_q} 0 1` — uniform and pointwise convergence of
  `t ↦ u(φ_q(±s, t))` to a single `1`-periodic orbit `y_q` of `H_q`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer`). Since time reversal
  fixes `t = 0`, isolation of `1`-periodic orbits at `t = 0` transfers directly between `H_q` and
  `H'_q`.

With bounded derivative of `e ∘ u ∘ φ'_q` on a half-cylinder `s > b` and isolated (or nondegenerate
for `C²` `H_q` on a Hausdorff boundaryless manifold) subsequential-limit orbits, `t ↦ u(φ_q(±s, t))`
converges as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`
(`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually`,
`..._of_isCompact`). Null-homotopic ends admit parallel `contractiblePeriodicSolutions` theorems;
see `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Manifold` for the energy identity.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy identity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations on punctured surfaces and their energy identities.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Asymptotic orbits at the ends -/

/-- Transfer a `1`-periodic orbit `x` of `H'_q` in `B` and uniform/pointwise convergence of
`u(φ'_q(σ i, ·))` to `x` into a `1`-periodic orbit `t ↦ x(±t)` of `H_q` in `B` and convergence of
the end loops `u(φ_q(±σ i, ·))`. -/
private theorem mem_periodicSolutions_and_tendstoUniformly_endChart_of_positiveEndChart
    {ι α : Type*} [UniformSpace α] {f : M → α} {l : Filter ι} {σ : ι → ℝ} {B : Set M}
    {u : ℝ × ℝ → M} {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
    (hxB : ∀ t, x t ∈ B)
    (hconv : TendstoUniformly (fun i t ↦ f (u (positiveEndChart q (σ i, t)))) (f ∘ x) l)
    (hpt : ∀ t, Tendsto (fun i ↦ u (positiveEndChart q (σ i, t))) l (𝓝 (x t))) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
      (∀ t, x (q.endSign * t) ∈ B) ∧
      TendstoUniformly (fun i t ↦ f (u (endChart q (q.endSign * σ i, t))))
        (f ∘ fun t ↦ x (q.endSign * t)) l ∧
      ∀ t, Tendsto (fun i ↦ u (endChart q (q.endSign * σ i, t))) l
        (𝓝 (x (q.endSign * t))) := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul hx, fun _ ↦ hxB _, ?_, fun t ↦ ?_⟩
  · rw [funext fun i ↦ comp_endChart_eq_comp_positiveEndChart (fun z ↦ f (u z)) q (σ i)]
    exact hconv.comp _
  · simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

namespace IsNondegenerate

/-! #### Breaking off periodic orbits along sequences -/

/-- **A finite-energy Floer solution breaks off an orbit along an end of the pair of pants.** Let
`ω` be a nondegenerate two-form on a manifold `M`, let `K` be equal to `H_q(t) dt` beyond `T₀` on
an end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let `u` be `C¹` on an open set `U`,
with image in a compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `U`. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `B` and with
injective differential at the points of `B`, and suppose that the almost complex structures are
uniformly tame with respect to `e` on `U`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy
of `u` over `U` is finite and `U` contains the part `±s > a` of the end `q`, then there are a
`1`-periodic orbit `y` of the Hamiltonian vector field of `H_q` in `B` and `s_n → ∞` such that the
loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`, pointwise in `M` and
uniformly after applying `e`.

Only the part of `U` along the end matters, so `u` need not be defined on the whole pair of pants:
this applies to the ends of domains that contain an end of `S`, such as the ends of a plumbed
four-punctured sphere. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (huB : ∀ z ∈ U, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    (hHs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  obtain ⟨hu', hfloer', hE'⟩ :=
    ω.floer_halfCylinder_comp_positiveEndChart_of_isOpen q hKH hH hHd hU hu one_ne_zero
      (le_max_left T₀ a) (fun ζ hζ ↦ haU ζ ((le_max_right T₀ a).trans_lt hζ))
      (J' := fun z ↦ J (positiveEndChart q z))
      (fun z hz ↦ hfloer _ (haU _ ((le_max_right T₀ a).trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, σ, -, hσ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHs)
      (periodic_positiveEndHamiltonian hH) he hB he_inj hde hu'
      (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (haU (s, t) ((le_max_right T₀ a).trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc _ (haU _ ((le_max_right T₀ a).trans_lt hz.1)) v) hfloer' hE'
  obtain ⟨hy, hyB, hconv', hpt'⟩ :=
    mem_periodicSolutions_and_tendstoUniformly_endChart_of_positiveEndChart hx hxB hconv hpt
  exact ⟨_, hy, hyB, σ, hσ, hconv', hpt'⟩

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `ω`
be a nondegenerate two-form on a manifold `M`, let `K` be equal to `H_q(t) dt` beyond `T₀` on an
end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let `u` be `C¹` on `S`, with image in a
compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a
`C¹` map into a finite-dimensional normed space, injective on `B` and with injective differential
at the points of `B`, and suppose that the almost complex structures are uniformly tame with
respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `S` is finite,
then at the end `q` there are a `1`-periodic orbit `y` of the Hamiltonian vector field of `H_q`
in `B` and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end,
converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen q hKH hH hHs he hB
    he_inj hde isOpen_thricePuncturedSphereReal hu huB J hc hJc hfloer hE (a := 0)
    fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal hζ

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
Let `ω` be a nondegenerate two-form on a compact manifold `M`, let `K` be equal to `H_q(t) dt`
beyond `T₀` on an end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let `u` be `C¹` on `S`,
solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a `C¹` injective map
with injective differential into a finite-dimensional normed space, and suppose that the almost
complex structures are uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with
`c > 0`. If the energy of `u` over `S` is finite, then at the end `q` there are a `1`-periodic
orbit `y` of the Hamiltonian vector field of `H_q` and `s_n → ∞` such that the loops
`t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`, pointwise in `M` and uniformly
after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
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
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact q hKH hH hHs
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE
  exact ⟨y, hy, h⟩

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
    ⟨φ, hφtop, tendstoUniformly_endChart_of_positiveEndChart (u := e ∘ u) hφx⟩
  rw [mul_zero] at hev
  refine hev.mono fun p hp x' hx' hx'B ⟨ψ, _, hψtop, hψx'⟩ hx'p ↦ funext fun t ↦ ?_
  have h := congrFun (hp (fun s ↦ x' (q.endSign * s)) (hPQ x' hx') (fun s ↦ hx'B _)
    ⟨ψ, hψtop, tendstoUniformly_endChart_of_positiveEndChart (u := e ∘ u) hψx'⟩
    (by simpa only [mul_zero] using hx'p)) (q.endSign * t)
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using h

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
  have hind : IsInducing fun p : B ↦ e p :=
    (hB.isClosedEmbedding_domRestrict he.continuous.continuousOn he_inj).isInducing
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
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact q (hKH q) (hH q)
      hHq he hB he_inj hde hu huB J hc hJc hfloer hE
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
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  obtain ⟨hu', hfloer', hE'⟩ :=
    ω.floer_halfCylinder_comp_positiveEndChart q (hKH q) (hH q) hHd hu one_ne_zero ha₀
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
    fun t ↦ hxB _, tendstoUniformly_endChart_of_positiveEndChart (u := e ∘ u) hux, fun t ↦ ?_⟩
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
    fun y hy hyB _ ↦
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq hHq
        (contractiblePeriodicSolutions_subset hy) (hnd y hy hyB)).mono
        fun _ hp y' hy' _ _ hy'p ↦ hp y' (contractiblePeriodicSolutions_subset hy') hy'p

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

/-! #### Convergence of the ends to isolated and nondegenerate orbits -/

/-- **Convergence of an end of a Floer pair of pants in a manifold to an isolated orbit.** Let `ω`
be a nondegenerate two-form on a finite-dimensional manifold `M`, `K` equal to `H_q(t) dt` beyond
`T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and `u` a `C¹` map on `S` with
image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`. Fix an end
`q`, suppose that on `(b, ∞) × [0, 1]` in the positive end chart `φ'_q` the derivative of
`(e ∘ u) ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` with `c > 0`, and suppose that
each `1`-periodic orbit `y` of `H_q` in `B` is isolated at `t = 0` among the `1`-periodic orbits
of `H_q` in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single
`1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab {z : ℝ × ℝ} (hz : z ∈ Ioi a ×ˢ Icc 0 1) : z ∈ Ioi b ×ˢ Icc 0 1 :=
    ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  obtain ⟨hu', hfloer', hE'⟩ :=
    ω.floer_halfCylinder_comp_positiveEndChart q (hKH q) (hH q) hHd hu one_ne_zero ha₀ haT
      (J' := fun z ↦ J (positiveEndChart q z))
      (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1))) hE
  -- Time reversal fixes `t = 0`, so isolation at `0` transfers from `H_q` to `H'_q`.
  have hiso' : ∀ x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1, (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    intro x hx hxB
    have h0 := hiso (fun t ↦ x (q.endSign * t)) (mem_periodicSolutions_comp_endSign_mul hx)
      (fun t ↦ hxB _)
    rw [mul_zero] at h0
    refine h0.mono fun p hp x' hx' hx'B hx'0 ↦ funext fun t ↦ ?_
    have heq := congrFun (hp (fun r ↦ x' (q.endSign * r))
      (mem_periodicSolutions_comp_endSign_mul hx') (fun r ↦ hx'B _)
      (by simpa only [mul_zero] using hx'0)) (q.endSign * t)
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using heq
  obtain ⟨x, hx, hxB, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde hu'
      (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab hz) v) hfloer' hE'
      (fun z hz ↦ hC z (hab hz)) hiso'
  exact ⟨_, mem_periodicSolutions_and_tendstoUniformly_endChart_of_positiveEndChart
    (σ := id) hx hxB hconv hpt⟩

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate orbit.** Let
`ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` equal to `H_q(t) dt`
beyond `T₀` on each end `q` for `1`-periodic `C²` Hamiltonians `H_q`, and `u` a `C¹` map on `S`
with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`. Fix an end
`q`, suppose that on `(b, ∞) × [0, 1]` in the positive end chart `φ'_q` the derivative of
`(e ∘ u) ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` with `c > 0`, and suppose that
every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate: `y 0` is a nondegenerate fixed point
of `timeDependentFlowOf X_{H_q} 0 1`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞`
to a single `1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated hKH hH
    (fun r ↦ (hHs r).of_le one_le_two) he hB he_inj hde hu huB J hfloer hE q hC hc hJc
    (hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq (hHs q) hnd)

/-- **Convergence of an end of a Floer pair of pants in a closed manifold to a nondegenerate
orbit.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` when `M` is
compact and `B = univ`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
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
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE q
      hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
