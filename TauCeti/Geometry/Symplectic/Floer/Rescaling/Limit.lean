/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Quantization
import TauCeti.Geometry.Manifold.ExtChartAt.ClosedBall
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic.Regularity
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The limit of rescaled Floer solutions in a manifold

At a point `z₀` where the energy densities of a sequence of Floer solutions `uᵢ` in a manifold `M`
blow up, bubbling analysis rescales the solutions at centres `cᵢ → z₀` by scales `εᵢ → 0` to maps
`w ↦ uᵢ(cᵢ + εᵢ w)`, which solve the Floer equation for the rescaled perturbation
`εᵢ K(cᵢ + εᵢ w)` and have energy density one at the origin and at most four on discs of radii
`Rᵢ → ∞` (`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv`). This file
shows that a subsequence of the rescaled maps converges to a map `v : ℝ × ℝ → M`, and that `v` is
the bubble at `z₀`: a nonconstant `C¹` plane, holomorphic for the structure `J(z₀, ·)` frozen at
the bubbling point, whose area is at most the energy concentrating at `z₀`.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity`, convergence in `M` is
measured through a map `e : M → F` into a normed space, differentiable at the points of a compact
set `K` containing the images of the solutions and injective on `K`, with the structures
uniformly tame with respect to `e`. Since the energy densities of the rescaled maps are bounded
on the discs of radii `Rᵢ → ∞`, and the Hamiltonian terms of the rescaled perturbation carry the
factor `εᵢ → 0`, the maps `w ↦ e(uᵢ(cᵢ + εᵢ w))` are uniformly Lipschitz on these discs, and the
exhausting-disc compactness theorem
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_strictMono_tendstoLocallyUniformly_comp` applies:

* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_strictMono_tendstoLocallyUniformly_comp_rescale`:
  rescaled solutions with bounded energy density on exhausting discs converge, locally uniformly
  on `ℝ × ℝ` after applying `e` and pointwise in `M`;
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_rescale_tendstoLocallyUniformly_comp`: at a point
  where the energy densities blow up, there are centres and scales as above along which a
  subsequence of the rescaled solutions converges to a continuous map `v : ℝ × ℝ → M`.

**The bubble** (in the namespace `TauCeti.SmoothTwoForm`,
`IsNondegenerate.exists_rescale_tendstoLocallyUniformly_fderiv_extChartAt_comp`). When the
structures and the Hamiltonian vector fields, read in the charts at the points of `K`, are `C¹`,
the convergence holds in `C¹` in these charts. Near a point where `v` lies in the chart
at `α`, the rescaled maps eventually lie in a compact coordinate ball of the chart
(`IsCompact.exists_closedBall_forall_mem_extChartAt_source`), where their coordinate expressions
solve the coordinate Floer equation for `J(cᵢ + εᵢ w, x)` and `εᵢ X_K(cᵢ + εᵢ w, x)` read in the
chart. These data depend on the parameter `(cᵢ, εᵢ) → (z₀, 0)`, jointly `C¹` in the parameter and
the point, and the bounded energy densities bound the derivatives in the chart
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_le_parametric`),
so the derivatives converge
(`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub_parametric`). At the
parameter `(z₀, 0)` the equation is that of `J(z₀, ·)`-holomorphic maps, and the derivatives
converge in the tangent bundle
(`TauCeti.tendsto_tangentBundle_mfderiv_of_tendsto_fderiv_extChartAt_comp`), which identifies the
area density of `v` with the limit of the energy densities of the rescaled maps
(`TauCeti.SmoothTwoForm.tendsto_floerEnergyDensity_rescale`) and bounds its area by Fatou's lemma
(`TauCeti.SmoothTwoForm.lintegral_eval₂_le_liminf_of_tendsto_rescale`). The vector-space form of
this statement is
`TauCeti.SymplecticForm.exists_tendstoLocallyUniformly_rescale_of_tendsto_norm_fderiv`.

**The smooth bubble and its quantum of area** (in the namespace `TauCeti.SmoothTwoForm`,
`IsNondegenerate.exists_pos_forall_exists_rescale_ofReal_le_lintegral_eval₂`). When the frozen
structure `J(z₀, ·)` is a smooth almost complex structure `J₀` (tamed by `ω`, as every `J(z, ·)`
is), the `C¹` bubble is smooth, since `C¹` pseudoholomorphic planes are
(`TauCeti.contMDiff_of_mfderiv_stdComplexLineImag_eq`), and energy quantization
(`TauCeti.SmoothTwoForm.Tames.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne`) bounds its area
below by an energy `κ > 0` depending only on `ω`, `J₀` and `K`. So every bubbling point absorbs at
least `κ`.

The bubble is a plane. That it extends to a sphere needs removal of the singularity at infinity,
which is in `TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity.Smooth`:
`TauCeti.SymplecticForm.exists_contMDiff_onePoint_elim_of_finite_energy` extends a solution
`u : ℂ → V` of `∂ₜu = J(u) ∂ₛu`, for `V` a finite-dimensional real inner product space, to the
sphere. It needs `J` of class `C^ℓ` with `ℓ ≥ 2` on an open set `W`, `u` of class `C³` with
image in a compact set `K ⊆ W` on which `J² = -1`, `J(u)` uniformly tamed by a symplectic form
compatible with the inner product through a linear complex structure, and finite energy. The
bubble is a map `ℝ × ℝ → M` rather than `ℂ → V` and has to be transported to that setting before
the theorem applies; this is not done here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.2
  (rescaling at a point where the derivatives blow up), Section 4.6 (bubbling off) and Section 8.1
  (inhomogeneous equations and bubbles for the frozen structure).
-/

public section

open Filter Function Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {e : M → F}

/-- **Rescaled Floer solutions in a manifold converge.** Let the maps `uᵢ` be differentiable on a
set `U` of the domain, with values there in a compact set `K ⊆ M`, and let `J(z, x)` be
domain-dependent structures on `T_x M`. Let `e : M → F` be a map into a normed space,
differentiable at the points of `K` and injective on `K`, with `J` uniformly tame with respect to
`e`, `c ‖d e v‖² ≤ ω(v, J(z, x) v)` with `c > 0`, and the pushforwards `d e (X_{K_s})`,
`d e (X_{K_t})` at most `B`, on `U × K`. Rescale at centres `cᵢ` by scales `εᵢ → 0` to the
maps `w ↦ uᵢ(cᵢ + εᵢ w)`, and suppose that for radii `Rᵢ → ∞`, eventually, for `‖w‖ ≤ Rᵢ`, the
point `cᵢ + εᵢ w` lies in `U` and the rescaled maps solve the rescaled Floer equation, for the
perturbation `εᵢ K(cᵢ + εᵢ w)` and the structure `J(cᵢ + εᵢ w, ·)`, with energy density at most `A`.
This is the output of the choice of centres and scales at a bubbling point,
`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv`, with `A = 4`. Then a
subsequence of the rescaled maps converges, locally uniformly on `ℝ × ℝ` after applying `e` and
pointwise in `M`, to a continuous map `v : ℝ × ℝ → M` with values in `K`. This statement gives
only the continuity of the limit. Under `C¹` hypotheses on the chart readings of `J` and of the
Hamiltonian vector fields of `Ks`, `Kt`,
`IsNondegenerate.exists_rescale_tendstoLocallyUniformly_fderiv_extChartAt_comp` gives a subsequence
along which the rescaled maps converge in `C¹` to a holomorphic, nonconstant bubble. -/
theorem IsNondegenerate.exists_strictMono_tendstoLocallyUniformly_comp_rescale
    (hω : ω.IsNondegenerate) {K : Set M} (hK : IsCompact K)
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {U : Set (ℝ × ℝ)} {u : ℕ → ℝ × ℝ → M} {c' : ℕ → ℝ × ℝ} {ε R : ℕ → ℝ} {c A B : ℝ}
    (hc : 0 < c) (hu : ∀ i, ∀ y ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u i) y)
    (huK : ∀ i, MapsTo (u i) U K)
    (hJc : ∀ y ∈ U, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J y x v))
    (hBs : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks y) x)‖ ≤ B)
    (hBt : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt y) x)‖ ≤ B)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop)
    (hres : ∀ᶠ i in atTop, ∀ w, ‖w‖ ≤ R i → c' i + ε i • w ∈ U ∧
      ω.floerEnergyDensity (fun w x ↦ ε i * Ks (c' i + ε i • w) x)
        (fun w x ↦ ε i * Kt (c' i + ε i • w) x) (fun w ↦ u i (c' i + ε i • w)) w ≤ A ∧
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (c' i + ε i • w) (u i (c' i + ε i • w)))
        (ω.perturbedMFDeriv (fun w x ↦ ε i * Ks (c' i + ε i • w) x)
          (fun w x ↦ ε i * Kt (c' i + ε i • w) x) (fun w ↦ u i (c' i + ε i • w)) w).toLinearMap) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ × ℝ → M, Continuous v ∧ (∀ w, v w ∈ K) ∧
      TendstoLocallyUniformly (fun n w ↦ e (u (φ n) (c' (φ n) + ε (φ n) • w))) (e ∘ v) atTop ∧
      ∀ w, Tendsto (fun n ↦ u (φ n) (c' (φ n) + ε (φ n) • w)) atTop (𝓝 (v w)) := by
  -- From some index `N` on, the rescaling data hold and `|εᵢ| ≤ 1`.
  have hε1 : Tendsto (fun i ↦ ‖ε i‖) atTop (𝓝 0) := by simpa using hε0.norm
  obtain ⟨N, hN⟩ :=
    (hres.and (hε1.eventually (ge_mem_nhds zero_lt_one))).exists_forall_of_atTop
  -- The Hamiltonian terms of the rescaled perturbation are `εᵢ` times those of `K`.
  have hX (i : ℕ) (K' : ℝ × ℝ → M → ℝ) (w : ℝ × ℝ) :
      ω.hamiltonianVectorField (fun x ↦ ε i * K' (c' i + ε i • w) x) =
        ε i • ω.hamiltonianVectorField (K' (c' i + ε i • w)) := by
    funext x
    exact ω.hamiltonianVectorField_const_smul (f := K' (c' i + ε i • w)) (ε i) x
  have hB (i : ℕ) (hi : N ≤ i) (K' : ℝ × ℝ → M → ℝ)
      (hK' : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (K' y) x)‖ ≤ B)
      (w : ℝ × ℝ) (hw : c' i + ε i • w ∈ U) :
      ‖mvfderiv I e (u i (c' i + ε i • w))
        (ω.hamiltonianVectorField (fun x ↦ ε i * K' (c' i + ε i • w) x)
          (u i (c' i + ε i • w)))‖ ≤ |B| := by
    rw [hX, Pi.smul_apply, map_smul, norm_smul]
    calc ‖ε i‖ * _ ≤ 1 * |B| := mul_le_mul (hN i hi).2
          ((hK' _ hw _ (huK i hw)).trans (le_abs_self B)) (norm_nonneg _) zero_le_one
      _ = |B| := one_mul _
  have hres' (n : ℕ) {w : ℝ × ℝ} (hw : w ∈ Metric.closedBall 0 (R (n + N))) :=
    (hN _ (Nat.le_add_left N n)).1 w (mem_closedBall_zero_iff.1 hw)
  obtain ⟨φ, hφ, v, hv, hvK, hconv, hpt⟩ :=
    hω.exists_strictMono_tendstoLocallyUniformly_comp hK he he_inj
      (u := fun n w ↦ u (n + N) (c' (n + N) + ε (n + N) • w))
      (Ks := fun n w x ↦ ε (n + N) * Ks (c' (n + N) + ε (n + N) • w) x)
      (Kt := fun n w x ↦ ε (n + N) * Kt (c' (n + N) + ε (n + N) • w) x)
      (fun n w ↦ J (c' (n + N) + ε (n + N) • w) (u (n + N) (c' (n + N) + ε (n + N) • w)))
      (R := fun n ↦ R (n + N))
      (hR.comp (tendsto_add_atTop_nat N)) (A := A) (B := |B|) hc
      (fun n w hw ↦ (hu _ _ (hres' n hw).1).comp w (mdifferentiableAt_iff_differentiableAt.2
        (by fun_prop : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ c' (n + N) + ε (n + N) • w) w)))
      (fun n w hw ↦ huK _ (hres' n hw).1)
      (fun n w hw ↦ hJc _ (hres' n hw).1 _ (huK _ (hres' n hw).1))
      (fun n w hw ↦ hB _ (Nat.le_add_left N n) Ks hBs w (hres' n hw).1)
      (fun n w hw ↦ hB _ (Nat.le_add_left N n) Kt hBt w (hres' n hw).1)
      (fun n w hw ↦ (hres' n hw).2.2) (fun n w hw ↦ (hres' n hw).2.1)
  exact ⟨fun n ↦ φ n + N, fun m n hmn ↦ Nat.add_lt_add_right (hφ hmn) N, v, hv, hvK, hconv, hpt⟩

/-- **Limits of rescaled Floer solutions in a manifold.** Let `uᵢ` solve the Floer equation
`(du - X_K)^{0,1} = 0` on an open set `U` of the domain, with values in a compact set `K ⊆ M` and
continuous Floer energy densities, for domain-dependent structures `J(z, x)` on `T_x M`. Let
`e : M → F` be a map into a normed space, differentiable at the points of `K` and injective on
`K`, with `J` uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J(z, x) v)` with `c > 0`, and
the pushforwards `d e (X_{K_s})`, `d e (X_{K_t})` at most `B`, on `U × K`. If the energy densities
of the `uᵢ` at points `zᵢ → z₀ ∈ U` tend to `∞`, there are centres `cᵢ → z₀`, scales `εᵢ > 0`
with `εᵢ → 0` and radii `Rᵢ → ∞` with `εᵢ Rᵢ → 0`, such that the rescaled maps
`w ↦ uᵢ(cᵢ + εᵢ w)` eventually have energy density one at the origin for the rescaled perturbation
`εᵢ K(cᵢ + εᵢ w)`, and a subsequence of them converges, locally uniformly on `ℝ × ℝ` after applying
`e` and pointwise in `M`, to a continuous map `v : ℝ × ℝ → M` with values in `K`. Under `C¹`
hypotheses on the chart readings of `J` and of the Hamiltonian vector fields of `Ks`, `Kt`,
`IsNondegenerate.exists_rescale_tendstoLocallyUniformly_fderiv_extChartAt_comp` gives a subsequence
along which the rescaled maps converge in `C¹` to a bubble that is holomorphic for the frozen
`J(z₀, ·)` and nonconstant. -/
theorem IsNondegenerate.exists_rescale_tendstoLocallyUniformly_comp (hω : ω.IsNondegenerate)
    {K : Set M} (hK : IsCompact K) (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : InjOn e K)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U) {u : ℕ → ℝ × ℝ → M} {z : ℕ → ℝ × ℝ}
    {c B : ℝ} (hc : 0 < c) (hu : ∀ i, ∀ y ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u i) y)
    (huK : ∀ i, MapsTo (u i) U K)
    (hJc : ∀ y ∈ U, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J y x v))
    (hBs : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks y) x)‖ ≤ B)
    (hBt : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt y) x)‖ ≤ B)
    (hρ : ∀ i, ContinuousOn (ω.floerEnergyDensity Ks Kt (u i)) U)
    (hsol : ∀ i, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u i y))
      (ω.perturbedMFDeriv Ks Kt (u i) y).toLinearMap)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hblow : Tendsto (fun i ↦ ω.floerEnergyDensity Ks Kt (u i) (z i)) atTop atTop) :
    ∃ (c' : ℕ → ℝ × ℝ) (ε R : ℕ → ℝ), (∀ i, 0 < ε i) ∧ Tendsto c' atTop (𝓝 z₀) ∧
      Tendsto ε atTop (𝓝 0) ∧ Tendsto R atTop atTop ∧ Tendsto (fun i ↦ ε i * R i) atTop (𝓝 0) ∧
      (∀ᶠ i in atTop, ω.floerEnergyDensity (fun w x ↦ ε i * Ks (c' i + ε i • w) x)
        (fun w x ↦ ε i * Kt (c' i + ε i • w) x) (fun w ↦ u i (c' i + ε i • w)) 0 = 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ × ℝ → M, Continuous v ∧ (∀ w, v w ∈ K) ∧
        TendstoLocallyUniformly (fun n w ↦ e (u (φ n) (c' (φ n) + ε (φ n) • w))) (e ∘ v)
          atTop ∧
        ∀ w, Tendsto (fun n ↦ u (φ n) (c' (φ n) + ε (φ n) • w)) atTop (𝓝 (v w)) := by
  obtain ⟨c', ε, R, hε, hc', hε0, hR, hεR, hres⟩ :=
    ω.exists_rescale_isComplexLinearMap_perturbedMFDeriv hU hz₀ hρ
      (Eventually.of_forall hsol) hz hblow
  refine ⟨c', ε, R, hε, hc', hε0, hR, hεR, hres.mono fun i hi ↦ hi.1, ?_⟩
  exact hω.exists_strictMono_tendstoLocallyUniformly_comp_rescale hK he he_inj hc hu huK hJc
    hBs hBt hε0 hR (hres.mono fun i hi ↦ hi.2)

/-! ### The bubble in a manifold

The derivatives of the rescaled solutions converge in the charts of `M`. Near a point `y` where the
candidate bubble `v` lies in the chart at `α`, the rescaled maps `w ↦ uₙ(cₙ + εₙ w)` eventually
lie in a compact coordinate ball of that chart, and their coordinate expressions solve the
coordinate Floer equation for the data `J(cₙ + εₙ w, x)` and `εₙ X_K(cₙ + εₙ w, x)` read in the
chart. These data depend on the parameter `(cₙ, εₙ) → (z₀, 0)`, jointly `C¹` in the parameter and
the point, so the convergence theorem over converging parameters applies once the derivatives are
bounded, and they are, because the energy densities of the rescaled maps are. -/

section Bubble

open Metric

variable [FiniteDimensional ℝ E] [I.Boundaryless]

omit [I.Boundaryless] in
/-- **Rescaled solutions in a chart.** If `u` is smooth on an open set `U` of the domain and the
rescaled map `w ↦ u(c + ε w)` solves the rescaled Floer equation on an open set `S` with
`c + ε • S ⊆ U` and values in the source of the chart at `α`, then its coordinate expression is
smooth on `S`, the rescaled map is differentiable there, and its coordinate expression solves the
coordinate Floer equation for `J(c + ε w, ·)` and `ε X_K(c + ε w, ·)` read in the chart. -/
private theorem contDiffOn_extChartAt_comp_rescale_and_fderiv_stdComplexLineImag_sub
    (ω : SmoothTwoForm I M) {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {U : Set (ℝ × ℝ)} {α : M} {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) u U) {c : ℝ × ℝ} {ε : ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hSU : ∀ w ∈ S, c + ε • w ∈ U)
    (hsrc : ∀ w ∈ S, u (c + ε • w) ∈ (extChartAt I α).source)
    (hsol : ∀ w ∈ S, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (c + ε • w) (u (c + ε • w)))
      (ω.perturbedMFDeriv (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
        (fun w ↦ u (c + ε • w)) w).toLinearMap) :
    ContDiffOn ℝ (⊤ : ℕ∞) (extChartAt I α ∘ fun w ↦ u (c + ε • w)) S ∧
      (∀ w ∈ S, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (c + ε • w)) w) ∧
      ∀ w ∈ S, fderiv ℝ (extChartAt I α ∘ fun w ↦ u (c + ε • w)) w stdComplexLineImag -
          ε • ω.hamiltonianVectorFieldInChartAt α Kt (c + ε • w, extChartAt I α (u (c + ε • w))) =
        Floer.almostComplexInChartAt I α J (c + ε • w, extChartAt I α (u (c + ε • w)))
          (fderiv ℝ (extChartAt I α ∘ fun w ↦ u (c + ε • w)) w stdComplexLineReal -
            ε • ω.hamiltonianVectorFieldInChartAt α Ks
              (c + ε • w, extChartAt I α (u (c + ε • w)))) := by
  have hur : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (fun w ↦ u (c + ε • w)) S :=
    hu.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ ↦ c + ε • w)).contMDiff.contMDiffOn
      hSU
  refine ⟨contMDiffOn_iff_contDiffOn.1 <| contMDiffOn_extChartAt.comp hur fun w hw ↦ by
    rw [mem_preimage, ← extChartAt_source I]
    exact hsrc w hw, fun w hw ↦ (hur.mdifferentiableOn (by simp)).mdifferentiableAt
      (hS.mem_nhds hw), fun w hw ↦ ?_⟩
  -- The coordinate Floer equation for the rescaled data, with the data read back at `c + ε w`.
  simpa only [Function.comp_apply, hamiltonianOneFormInChartAt_stdComplexLineReal,
    hamiltonianOneFormInChartAt_stdComplexLineImag, hamiltonianVectorFieldInChartAt_rescale,
    Floer.almostComplexInChartAt_comp] using
    (ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub (J := fun w ↦ J (c + ε • w))
      (n := 3) hS (hur.of_le (by norm_cast)) (by norm_num) hsrc hsol).2 w hw

omit [I.Boundaryless] in
/-- **A bound on the energy density bounds the derivatives of rescaled solutions in a chart.** For
an open set `U ∋ z₀` of the domain, a compact set `D`, a compact set `K` of coordinates of the
chart at `α` and a bound `A`, there are a neighbourhood `C` of `(z₀, 0)` and a constant `L`
bounding, for every parameter `(c, ε) ∈ C`, the derivative at `w ∈ D` of the coordinate
expression of every rescaled map `w ↦ u(c + ε w)` that solves the rescaled Floer equation at `w`,
with value there in the chart source, coordinate in `K` and energy density at most `A`. -/
private theorem IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_rescale_le
    (hω : ω.IsNondegenerate) {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U) {α : M}
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) (U ×ˢ (extChartAt I α).target))
    (hXs : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Ks) (U ×ˢ (extChartAt I α).target))
    (hXt : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Kt) (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ U, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) {K : Set E} (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (A : ℝ) :
    ∃ C ∈ 𝓝 (z₀, (0 : ℝ)), ∃ L, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃ε : ℝ⦄ ⦃w : ℝ × ℝ⦄,
      (c, ε) ∈ C → w ∈ D →
      u (c + ε • w) ∈ (extChartAt I α).source → extChartAt I α (u (c + ε • w)) ∈ K →
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (c + ε • w)) w →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c + ε • w) (u (c + ε • w)))
        (ω.perturbedMFDeriv (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
          (fun w ↦ u (c + ε • w)) w).toLinearMap →
      ω.floerEnergyDensity (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
        (fun w ↦ u (c + ε • w)) w ≤ A →
      ‖fderiv ℝ (extChartAt I α ∘ fun w ↦ u (c + ε • w)) w‖ ≤ L := by
  -- A compact window `C` of parameters `(c, ε)` about `(z₀, 0)` with `c + ε • D ⊆ U`.
  obtain ⟨δ, hδ, hCD⟩ := nhds_basis_closedBall.eventually_iff.1 <|
    hD.eventually_forall_of_forall_eventually (x₀ := (z₀, (0 : ℝ)))
      (P := fun p w ↦ p.1 + p.2 • w ∈ U) fun w _ ↦
      (by fun_prop : Continuous fun q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ) ↦
        q.1.1 + q.1.2 • q.2).continuousAt (x := ((z₀, 0), w)) |>.eventually_mem
          (hU.mem_nhds (by simpa using hz₀))
  set C := closedBall (z₀, (0 : ℝ)) δ
  -- The rescaled data form one family over the parameters `(c, ε)`, read in the chart through
  -- the point `(c + ε • w, x)`.
  set g : (((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) × E → (ℝ × ℝ) × E :=
    fun q ↦ (q.1.1.1 + q.1.1.2 • q.1.2, q.2)
  have hg : Continuous g := by fun_prop
  have hgC : MapsTo g ((C ×ˢ D) ×ˢ K) (U ×ˢ (extChartAt I α).target) :=
    fun q hq ↦ ⟨hCD hq.1.1 _ hq.1.2, hKα hq.2⟩
  obtain ⟨L, hL⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_le_parametric
    (J := fun (p : (ℝ × ℝ) × ℝ) w ↦ J (p.1 + p.2 • w))
    (Ks := fun p w x ↦ p.2 * Ks (p.1 + p.2 • w) x) (Kt := fun p w x ↦ p.2 * Kt (p.1 + p.2 • w) x)
    α (isCompact_closedBall _ δ) hD hK hKα
    ((hJ.comp hg.continuousOn hgC).congr fun ⟨⟨p, w⟩, x⟩ _ ↦ by
      rw [Floer.almostComplexInChartAt_uncurry, Floer.almostComplexInChartAt_comp]
      rfl)
    (((continuous_fst.fst.snd.continuousOn).smul (hXs.comp hg.continuousOn hgC)).congr
      fun ⟨⟨p, w⟩, x⟩ _ ↦ by
        rw [hamiltonianVectorFieldInChartAt_uncurry, hamiltonianVectorFieldInChartAt_rescale]
        rfl)
    (((continuous_fst.fst.snd.continuousOn).smul (hXt.comp hg.continuousOn hgC)).congr
      fun ⟨⟨p, w⟩, x⟩ _ ↦ by
        rw [hamiltonianVectorFieldInChartAt_uncurry, hamiltonianVectorFieldInChartAt_rescale]
        rfl)
    (fun p hp w hw _ _ ↦ hJt _ (hCD hp w hw) _) A
  exact ⟨C, closedBall_mem_nhds _ hδ, L, fun u c ε w hp hw ↦
    hL (p := (c, ε)) (u := fun w ↦ u (c + ε • w)) hp hw⟩

omit [NormedSpace ℝ F] in
/-- **The derivatives of rescaled solutions converge in a chart.** Let `uₙ` be smooth on an open
set `U` of the domain, and let the rescaled maps `w ↦ uₙ(cₙ + εₙ w)`, with `cₙ → z₀ ∈ U` and
`εₙ → 0`, solve the rescaled Floer equation on an open set `S` with values in a compact set `K`
and energy densities at most `A`, and converge on `S` to `v`, locally uniformly through a map `e`
continuous and injective on `K`, and pointwise. If `v y` lies in the source of the chart at `α`,
where the data are `C¹`, then on a disc about `y` the coordinate expression of `v` is `C¹` and
`J(z₀, ·)`-holomorphic, and the derivatives of the coordinate expressions of the rescaled maps
converge to its derivative locally uniformly. -/
private theorem IsNondegenerate.exists_ball_tendstoLocallyUniformlyOn_fderiv_rescale
    (hω : ω.IsNondegenerate) {K : Set M} (hK : IsCompact K) (he : ContinuousOn e K)
    (he_inj : InjOn e K) {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U) {α : M}
    (hJ : ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I α J) (U ×ˢ (extChartAt I α).target))
    (hXs : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Ks) (U ×ˢ (extChartAt I α).target))
    (hXt : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Kt) (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ U, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) U)
    {c : ℕ → ℝ × ℝ} {ε : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 z₀)) (hε : Tendsto ε atTop (𝓝 0))
    {S : Set (ℝ × ℝ)} (hS : IsOpen S) {A : ℝ}
    (hres : ∀ n, ∀ w ∈ S, c n + ε n • w ∈ U ∧ u n (c n + ε n • w) ∈ K ∧
      ω.floerEnergyDensity (fun w x ↦ ε n * Ks (c n + ε n • w) x)
        (fun w x ↦ ε n * Kt (c n + ε n • w) x) (fun w ↦ u n (c n + ε n • w)) w ≤ A ∧
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (c n + ε n • w) (u n (c n + ε n • w)))
        (ω.perturbedMFDeriv (fun w x ↦ ε n * Ks (c n + ε n • w) x)
          (fun w x ↦ ε n * Kt (c n + ε n • w) x) (fun w ↦ u n (c n + ε n • w)) w).toLinearMap)
    {v : ℝ × ℝ → M} (hv : ContinuousOn v S) (hvK : MapsTo v S K)
    (hconv : TendstoLocallyUniformlyOn (fun n ↦ e ∘ fun w ↦ u n (c n + ε n • w)) (e ∘ v) atTop S)
    (hpt : ∀ w ∈ S, Tendsto (fun n ↦ u n (c n + ε n • w)) atTop (𝓝 (v w)))
    {y : ℝ × ℝ} (hy : y ∈ S) (hyα : v y ∈ (extChartAt I α).source) :
    ∃ r > 0, ball y r ⊆ S ∧ MapsTo v (ball y r) (extChartAt I α).source ∧
      ContDiffOn ℝ 1 (extChartAt I α ∘ v) (ball y r) ∧
      TendstoLocallyUniformlyOn
        (fun n ↦ fderiv ℝ (extChartAt I α ∘ fun w ↦ u n (c n + ε n • w)))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (ball y r) ∧
      ∀ w ∈ ball y r, fderiv ℝ (extChartAt I α ∘ v) w stdComplexLineImag =
        Floer.almostComplexInChartAt I α J (z₀, extChartAt I α (v w))
          (fderiv ℝ (extChartAt I α ∘ v) w stdComplexLineReal) := by
  set χ := extChartAt I α
  -- A closed coordinate ball of the chart and a closed disc about `y` on which `v` and the tail
  -- of the rescaled maps take values in the chart source with coordinates in that ball.
  obtain ⟨κ, -, hKcT, r, hr, hcl, N, hN⟩ := hK.exists_closedBall_forall_mem_extChartAt_source he
    he_inj hS (u := fun n w ↦ u n (c n + ε n • w)) (fun n w hw ↦ (hres n w hw).2.1) hv hvK hconv
    hy hyα
  have hBS : ball y r ⊆ S := ball_subset_closedBall.trans hcl
  -- The energy densities bound the derivatives in the chart, for parameters `(c, ε)` in a
  -- neighbourhood `C` of `(z₀, 0)`, which contains `(cₙ, εₙ)` for large `n`.
  obtain ⟨C, hC, L, hL⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_rescale_le hU hz₀
    hJ.continuousOn hXs.continuousOn hXt.continuousOn hJt (isCompact_closedBall y r)
    (isCompact_closedBall _ κ) hKcT A
  obtain ⟨N', hN'⟩ := eventually_atTop.1 ((hc.prodMk_nhds hε).eventually hC)
  -- From the index `N₀` on, the rescaled maps are read in the chart on the open disc.
  set N₀ := max N N'
  have hsrc (n : ℕ) {w : ℝ × ℝ} (hw : w ∈ ball y r) :=
    (hN w (ball_subset_closedBall hw)).2 (n + N₀) ((le_max_left N N').trans (Nat.le_add_left _ n))
  have hchart (n : ℕ) := contDiffOn_extChartAt_comp_rescale_and_fderiv_stdComplexLineImag_sub ω
    (hu (n + N₀)) isOpen_ball (fun w hw ↦ (hres _ w (hBS hw)).1) (fun w hw ↦ (hsrc n hw).1)
    fun w hw ↦ (hres _ w (hBS hw)).2.2.2
  -- The data at the parameter `(c, ε)` and the point `(w, x)`, read in the chart.
  set g : (((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) × E → (ℝ × ℝ) × E :=
    fun q ↦ (q.1.1.1 + q.1.1.2 • q.1.2, q.2)
  have hg : ContDiff ℝ 1 g := by fun_prop
  obtain ⟨hv1, hdconv, heq⟩ :=
    Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub_parametric
      (J := fun q ↦ Floer.almostComplexInChartAt I α J (g q))
      (X := fun q ↦ q.1.1.2 • ω.hamiltonianOneFormInChartAt α Ks Kt (g q))
      ((hU.prod (isOpen_extChartAt_target α)).preimage hg.continuous)
      (hJ.comp hg.contDiffOn (mapsTo_preimage _ _))
      (contDiff_fst.fst.snd.contDiffOn.smul ((contDiffOn_hamiltonianOneFormInChartAt hXs
        hXt).comp hg.contDiffOn (mapsTo_preimage _ _)))
      isOpen_ball (p := fun n ↦ (c (n + N₀), ε (n + N₀))) (p₀ := (z₀, 0))
      (u := fun n ↦ χ ∘ fun w ↦ u (n + N₀) (c (n + N₀) + ε (n + N₀) • w)) (v := χ ∘ v)
      ((hc.prodMk_nhds hε).comp (tendsto_add_atTop_nat N₀))
      (fun w hw ↦ ⟨by simpa [g] using hz₀, χ.map_source (hN w (ball_subset_closedBall hw)).1.1⟩)
      (fun n ↦ (hchart n).1)
      (fun n w hw ζ ↦ Floer.almostComplexInChartAt_apply_apply (χ.map_source (hsrc n hw).1) _ ζ)
      (fun n w hw ↦ by
        simpa only [g, smul_apply, Function.comp_apply,
          hamiltonianOneFormInChartAt_stdComplexLineImag,
          hamiltonianOneFormInChartAt_stdComplexLineReal] using (hchart n).2.2 w hw)
      (fun C' _ hC' ↦ ⟨L, fun n w hw ↦ hL
        (hN' _ ((le_max_right N N').trans (Nat.le_add_left _ n)))
        (ball_subset_closedBall (hC' hw)) (hsrc n (hC' hw)).1 (hsrc n (hC' hw)).2
        ((hchart n).2.1 w (hC' hw))
        (hres _ w (hBS (hC' hw))).2.2.2 (hres _ w (hBS (hC' hw))).2.2.1⟩)
      (fun w hw ↦ (continuousAt_extChartAt' (hN w (ball_subset_closedBall hw)).1.1).tendsto.comp
        ((hpt w (hBS hw)).comp (tendsto_add_atTop_nat N₀)))
  -- Convergence of the tail is convergence of the sequence.
  refine ⟨r, hr, hBS, fun w hw ↦ (hN w (ball_subset_closedBall hw)).1.1, hv1,
    by rw [← map_add_atTop_eq_nat N₀]; exact tendstoLocallyUniformlyOn_map_iff.2 hdconv,
    fun w hw ↦ by simpa [g] using heq w hw⟩

omit [NormedSpace ℝ F] in
/-- The chart statement of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_ball_tendstoLocallyUniformlyOn_fderiv_rescale` near
every point of the plane, for rescaled maps that eventually solve the rescaled equation, with
energy density at most `A`, on discs of radii `Rₙ → ∞`, and converge on the whole plane. -/
private theorem IsNondegenerate.exists_ball_tendstoLocallyUniformlyOn_fderiv_rescale_of_tendsto
    (hω : ω.IsNondegenerate) {K : Set M} (hK : IsCompact K) (he : ContinuousOn e K)
    (he_inj : InjOn e K) {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U) {α : M}
    (hJ : ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I α J) (U ×ˢ (extChartAt I α).target))
    (hXs : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Ks) (U ×ˢ (extChartAt I α).target))
    (hXt : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Kt) (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ U, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) U)
    (huK : ∀ n, MapsTo (u n) U K) {c : ℕ → ℝ × ℝ} {ε R : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 z₀))
    (hε : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop) {A : ℝ}
    (hres : ∀ᶠ n in atTop, ∀ w, ‖w‖ ≤ R n → c n + ε n • w ∈ U ∧
      ω.floerEnergyDensity (fun w x ↦ ε n * Ks (c n + ε n • w) x)
        (fun w x ↦ ε n * Kt (c n + ε n • w) x) (fun w ↦ u n (c n + ε n • w)) w ≤ A ∧
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (c n + ε n • w) (u n (c n + ε n • w)))
        (ω.perturbedMFDeriv (fun w x ↦ ε n * Ks (c n + ε n • w) x)
          (fun w x ↦ ε n * Kt (c n + ε n • w) x) (fun w ↦ u n (c n + ε n • w)) w).toLinearMap)
    {v : ℝ × ℝ → M} (hv : Continuous v) (hvK : ∀ w, v w ∈ K)
    (hconv : TendstoLocallyUniformly (fun n w ↦ e (u n (c n + ε n • w))) (e ∘ v) atTop)
    (hpt : ∀ w, Tendsto (fun n ↦ u n (c n + ε n • w)) atTop (𝓝 (v w)))
    {y : ℝ × ℝ} (hyα : v y ∈ (extChartAt I α).source) :
    ∃ r > 0, MapsTo v (ball y r) (extChartAt I α).source ∧
      ContDiffOn ℝ 1 (extChartAt I α ∘ v) (ball y r) ∧
      TendstoLocallyUniformlyOn
        (fun n ↦ fderiv ℝ (extChartAt I α ∘ fun w ↦ u n (c n + ε n • w)))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (ball y r) ∧
      ∀ w ∈ ball y r, fderiv ℝ (extChartAt I α ∘ v) w stdComplexLineImag =
        Floer.almostComplexInChartAt I α J (z₀, extChartAt I α (v w))
          (fderiv ℝ (extChartAt I α ∘ v) w stdComplexLineReal) := by
  -- From an index `k` on, the rescaled maps solve the equation on the disc of radius `m > ‖y‖`.
  obtain ⟨m, hm⟩ := exists_nat_gt ‖y‖
  obtain ⟨k, hk⟩ := eventually_atTop.1 (hres.and (hR.eventually_ge_atTop m))
  have hk' (n : ℕ) {w : ℝ × ℝ} (hw : w ∈ ball (0 : ℝ × ℝ) m) :=
    (hk (n + k) (Nat.le_add_left k n)).1 w
      ((mem_ball_zero_iff.1 hw).le.trans (hk (n + k) (Nat.le_add_left k n)).2)
  have hsh := tendsto_add_atTop_nat k
  obtain ⟨r, hr, -, hvα, hv1, hconv', heq⟩ :=
    hω.exists_ball_tendstoLocallyUniformlyOn_fderiv_rescale hK he he_inj hU hz₀ hJ hXs hXt hJt
      (u := fun n ↦ u (n + k)) (fun n ↦ hu _) (hc.comp hsh) (hε.comp hsh) isOpen_ball (A := A)
      (fun n w hw ↦ ⟨(hk' n hw).1, huK _ (hk' n hw).1, (hk' n hw).2⟩) hv.continuousOn
      (fun w _ ↦ hvK w) ((hconv.comp_tendsto hsh).tendstoLocallyUniformlyOn)
      (fun w _ ↦ (hpt w).comp hsh) (mem_ball_zero_iff.2 hm) hyα
  -- Convergence of the tail is convergence of the sequence.
  refine ⟨r, hr, hvα, hv1, ?_, heq⟩
  rw [← map_add_atTop_eq_nat k]
  exact tendstoLocallyUniformlyOn_map_iff.2 hconv'

omit [I.Boundaryless] in
/-- From the chart statements near every point to the manifold statements: if near every point of
the plane, in the chart at any point of `K` whose source contains the value of `v`, the coordinate
expression of `v` is `C¹` and `J(z₀, ·)`-holomorphic and the derivatives of those of maps `Qₙ`
converge to its derivative locally uniformly, then `v` is `C¹` and `J(z₀, ·)`-holomorphic, the
derivatives converge in each such chart where `v` lies in its source, and the derivatives of the
`Qₙ` converge to that of `v` in the tangent bundle. -/
private theorem contMDiff_and_tendsto_mfderiv_of_forall_exists_ball
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {z₀ : ℝ × ℝ} {K : Set M}
    {v : ℝ × ℝ → M} (hv : Continuous v) (hvK : ∀ w, v w ∈ K) {Q : ℕ → ℝ × ℝ → M}
    (hQ : ∀ w, ∀ᶠ n in atTop, ContinuousAt (Q n) w)
    (hpt : ∀ w, Tendsto (fun n ↦ Q n w) atTop (𝓝 (v w)))
    (hloc : ∀ α ∈ K, ∀ y, v y ∈ (extChartAt I α).source → ∃ r > 0,
      MapsTo v (ball y r) (extChartAt I α).source ∧
      ContDiffOn ℝ 1 (extChartAt I α ∘ v) (ball y r) ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ Q n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (ball y r) ∧
      ∀ w ∈ ball y r, fderiv ℝ (extChartAt I α ∘ v) w stdComplexLineImag =
        Floer.almostComplexInChartAt I α J (z₀, extChartAt I α (v w))
          (fderiv ℝ (extChartAt I α ∘ v) w stdComplexLineReal)) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v ∧
      (∀ α ∈ K, TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ Q n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (v ⁻¹' (extChartAt I α).source)) ∧
      (∀ w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag =
        J z₀ (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)) ∧
      ∀ w (a : ℝ × ℝ), Tendsto
        (fun n ↦ (⟨Q n w, mfderiv 𝓘(ℝ, ℝ × ℝ) I (Q n) w a⟩ : TangentBundle I M))
        atTop (𝓝 ⟨v w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w a⟩) := by
  -- `v` is `C¹` and the derivatives converge in the charts, as both are local.
  obtain ⟨hv1, hd⟩ :=
    contMDiffOn_and_tendstoLocallyUniformlyOn_fderiv_extChartAt_comp_of_forall_exists_ball
      isOpen_univ hv.continuousOn (fun w _ ↦ hvK w) (Q := Q) fun α hα y _ hyα ↦
        (hloc α hα y hyα).imp fun _ ⟨hr, h₁, h₂, h₃, _⟩ ↦ ⟨hr, h₁, h₂, h₃⟩
  refine ⟨contMDiffOn_univ.1 hv1, fun α hα ↦ by simpa using hd α hα, fun w ↦ ?_, fun w a ↦ ?_⟩
  · -- Read the coordinate equation back in the tangent spaces.
    have hw := mem_extChartAt_source (I := I) (v w)
    obtain ⟨r, hr, -, -, -, heq⟩ := hloc _ (hvK w) w hw
    have h := congrArg ((trivializationAt E (TangentSpace I) (v w)).symmL ℝ (v w))
      (heq w (mem_ball_self hr))
    rwa [hv.continuousAt.symmL_fderiv_extChartAt_comp_apply hw,
      Floer.almostComplexInChartAt_apply, (extChartAt I (v w)).left_inv hw,
      Bundle.Trivialization.symmL_continuousLinearMapAt _
        (FiberBundle.mem_baseSet_trivializationAt E _ (v w)),
      hv.continuousAt.symmL_fderiv_extChartAt_comp_apply hw] at h
  · obtain ⟨r, hr, -, -, hd, -⟩ := hloc _ (hvK w) w (mem_extChartAt_source (v w))
    refine tendsto_tangentBundle_mfderiv_of_tendsto_fderiv_extChartAt_comp hv.continuousAt
      (mem_extChartAt_source _) (hQ w) (hpt w) a ?_
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      ((ContinuousLinearMap.apply ℝ E a).continuous.tendsto _).comp
        (hd.tendsto_at (mem_ball_self hr))

/-- **The bubble at a bubbling point of Floer solutions in a manifold.** Let `uₙ` be smooth
solutions of the Floer equation `(du - X_K)^{0,1} = 0` on an open set `U` of the domain, for
domain-dependent structures `J(z, x)` on `T_x M` tamed by `ω`, with values in a compact set `K ⊆ M`
and continuous energy densities. Let the structures and the Hamiltonian vector fields of `K_s` and
`K_t`, read in the chart at every point of `K`, be `C¹` on `U` times the chart target. Let
`e : M → F` be a map into a normed space, differentiable at the points of `K` and injective on `K`,
with `J` uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J(z, x) v)` with `c > 0`, and the
pushforwards `d e (X_{K_s})`, `d e (X_{K_t})` bounded on `U × K`. If the energy densities of the
`uₙ` at points `zₙ → z₀ ∈ U` tend to `∞`, then there are a subsequence `φ`, centres `cₙ → z₀`,
scales `εₙ > 0` with `εₙ → 0`, and a `C¹` map `v : ℝ × ℝ → K` such that

* the rescaled maps `w ↦ u_{φ n}(cₙ + εₙ w)` converge to `v` locally uniformly through `e`, and in
  `C¹` in the charts at the points of `K`: the derivatives of their coordinate expressions converge
  to that of `v`, locally uniformly where `v` lies in the chart source;
* `v` is holomorphic for the structure `J(z₀, ·)` frozen at the bubbling point;
* its area density `ω(∂ₛv, ∂ₜv)` is `1` at the origin, so `v` is not constant, and at most `4`
  everywhere;
* for every `δ > 0`, the symplectic area `∫ ω(∂ₛv, ∂ₜv)` of `v` is at most the lower limit of the
  Floer energies of the `u_{φ n}` over the disc of radius `δ` about `z₀`.

This is the nonconstant pseudoholomorphic plane at an interior bubbling point; the vector-space
statement is `TauCeti.SymplecticForm.exists_tendstoLocallyUniformly_rescale_of_tendsto_norm_fderiv`.
-/
theorem IsNondegenerate.exists_rescale_tendstoLocallyUniformly_fderiv_extChartAt_comp
    (hω : ω.IsNondegenerate) {K : Set M} (hK : IsCompact K)
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ U, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ y ∈ U, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J y x v))
    (hBs : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks y) x)‖ ≤ B)
    (hBt : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt y) x)‖ ≤ B)
    {u : ℕ → ℝ × ℝ → M} {z : ℕ → ℝ × ℝ} (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) U)
    (huK : ∀ n, MapsTo (u n) U K) (hρ : ∀ n, ContinuousOn (ω.floerEnergyDensity Ks Kt (u n)) U)
    (hsol : ∀ n, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u n y))
      (ω.perturbedMFDeriv Ks Kt (u n) y).toLinearMap)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hblow : Tendsto (fun n ↦ ω.floerEnergyDensity Ks Kt (u n) (z n)) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (c' : ℕ → ℝ × ℝ) (ε : ℕ → ℝ) (v : ℝ × ℝ → M), StrictMono φ ∧
      (∀ n, 0 < ε n) ∧ Tendsto c' atTop (𝓝 z₀) ∧ Tendsto ε atTop (𝓝 0) ∧
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v ∧ (∀ w, v w ∈ K) ∧
      TendstoLocallyUniformly (fun n w ↦ e (u (φ n) (c' n + ε n • w))) (e ∘ v) atTop ∧
      (∀ α ∈ K, TendstoLocallyUniformlyOn
        (fun n ↦ fderiv ℝ (extChartAt I α ∘ fun w ↦ u (φ n) (c' n + ε n • w)))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (v ⁻¹' (extChartAt I α).source)) ∧
      (∀ w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag =
        J z₀ (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)) ∧
      SmoothBundleForm.eval₂ ω (v 0) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v 0 stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v 0 stdComplexLineImag) = 1 ∧
      (∀ w, SmoothBundleForm.eval₂ ω (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag) ≤ 4) ∧
      ∀ δ > 0, ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (v w)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag)) ≤
        liminf (fun n ↦ ∫⁻ y in ball z₀ δ,
          ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u (φ n)) y)) atTop := by
  have hec : ContinuousOn e K := fun x hx ↦ (he x hx).continuousAt.continuousWithinAt
  -- Rescale at the points chosen by Hofer's lemma, and extract a continuous limit `v`.
  obtain ⟨c₁, ε₁, R, hε₁, hc₁, hε₁0, hR, -, hres⟩ :=
    ω.exists_rescale_isComplexLinearMap_perturbedMFDeriv hU hz₀ hρ
      (Eventually.of_forall hsol) hz hblow
  obtain ⟨φ, hφ, v, hv, hvK, hconv, hpt⟩ :=
    hω.exists_strictMono_tendstoLocallyUniformly_comp_rescale hK he he_inj hc
      (fun n y hy ↦ ((hu n).mdifferentiableOn (by simp)).mdifferentiableAt (hU.mem_nhds hy))
      huK hJc hBs hBt hε₁0 hR (hres.mono fun i hi ↦ hi.2)
  have hφt := hφ.tendsto_atTop
  have hres' := hφt.eventually hres
  have hc' := hc₁.comp hφt
  have hε' := hε₁0.comp hφt
  -- In the chart at any point of `K`, near every point of the plane.
  have hloc {α : M} (hα : α ∈ K) {y : ℝ × ℝ} (hyα : v y ∈ (extChartAt I α).source) :=
    hω.exists_ball_tendstoLocallyUniformlyOn_fderiv_rescale_of_tendsto hK hec he_inj hU hz₀
      (hJ α hα) (hXs α hα) (hXt α hα) hJt (u := fun n ↦ u (φ n)) (fun n ↦ hu _)
      (fun n ↦ huK _) hc' hε' (hR.comp hφt) (A := 4) (hres'.mono fun n hn ↦ hn.2) hv hvK hconv
      hpt hyα
  obtain ⟨hvC1, hderiv, hhol, hdv⟩ := contMDiff_and_tendsto_mfderiv_of_forall_exists_ball
    (J := J) (z₀ := z₀) (Q := fun n w ↦ u (φ n) (c₁ (φ n) + ε₁ (φ n) • w)) hv hvK
    (fun w ↦ by
      filter_upwards [hres', (hR.comp hφt).eventually_ge_atTop ‖w‖] with n hn hnR
      exact ((hu (φ n)).continuousOn.continuousAt (hU.mem_nhds (hn.2 w hnR).1)).comp
        (f := fun w ↦ c₁ (φ n) + ε₁ (φ n) • w) (by fun_prop))
    hpt fun α hα y hyα ↦ hloc hα hyα
  -- The energy densities of the rescaled maps converge to the area density of `v`.
  have hXc {H : ℝ × ℝ → M → ℝ} (hH : ∀ x ∈ K,
      ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt x H) (U ×ˢ (extChartAt I x).target))
      (w : ℝ × ℝ) := ω.continuousAt_hamiltonianVectorField_of_continuousOn_inChartAt hU hz₀
    (hH _ (hvK w)).continuousOn
  have hdens (w : ℝ × ℝ) := ω.tendsto_floerEnergyDensity_rescale (u := fun n ↦ u (φ n)) hc' hε'
    (hdv w) (hXc hXs w) (hXc hXt w)
  have hρ0 : ∀ᶠ n in atTop,
      ε₁ (φ n) ^ 2 * ω.floerEnergyDensity Ks Kt (u (φ n)) (c₁ (φ n) + ε₁ (φ n) • 0) = 1 :=
    hres'.mono fun n hn ↦ by rw [← ω.floerEnergyDensity_rescale]; exact hn.1
  refine ⟨φ, c₁ ∘ φ, ε₁ ∘ φ, v, hφ, fun n ↦ hε₁ _, hc', hε', hvC1, hvK, hconv, hderiv, hhol,
    tendsto_nhds_unique (hdens 0) (tendsto_const_nhds.congr' (hρ0.mono fun n hn ↦ hn.symm)),
    fun w ↦ le_of_tendsto (hdens w) ?_, fun δ hδ ↦ ?_⟩
  · filter_upwards [hres', (hR.comp hφt).eventually_ge_atTop ‖w‖] with n hn hnR
    rw [← ω.floerEnergyDensity_rescale]
    exact (hn.2 w hnR).2.1
  · -- Fatou's lemma on a smaller disc inside `U`, where the energy densities are continuous.
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU z₀ hz₀
    have hBU : ball z₀ (min δ r) ⊆ U := (ball_subset_ball (min_le_right δ r)).trans hrU
    refine (ω.lintegral_eval₂_le_liminf_of_tendsto_rescale (u := fun n ↦ u (φ n)) (lt_min hδ hr)
      (fun n ↦ ((hρ (φ n)).mono hBU).aemeasurable isOpen_ball.measurableSet) hc' hε' hdv
      (fun w ↦ hXc hXs w) (fun w ↦ hXc hXt w)).trans ?_
    exact liminf_le_liminf (Eventually.of_forall fun n ↦
      MeasureTheory.lintegral_mono_set (ball_subset_ball (min_le_left δ r)))

/-- **The bubble is smooth and carries a quantum of area.** In the setting of
`IsNondegenerate.exists_rescale_tendstoLocallyUniformly_fderiv_extChartAt_comp`, let `M` be
Hausdorff and let the structure `J(z₀, ·)` frozen at the bubbling point be a smooth almost complex
structure `J₀`, which is then tamed by `ω`. There is an energy `κ > 0`, depending only on `ω`,
`J₀` and `K`, with the following property. If the energy densities of smooth solutions `uₙ` of the
Floer equation on `U`, with values in `K`, tend to `∞` at points `zₙ → z₀`, then there are a
subsequence `φ`, centres `cₙ → z₀`, scales `εₙ > 0` with `εₙ → 0`, and a smooth `J₀`-holomorphic
plane `v : ℝ × ℝ → K` such that

* the rescaled maps `w ↦ u_{φ n}(cₙ + εₙ w)` converge to `v` locally uniformly through `e`;
* the symplectic area `∫ ω(∂ₛv, ∂ₜv)` of `v` is at least `κ` and, for every `δ > 0`, at most the
  lower limit of the Floer energies of the `u_{φ n}` over the disc of radius `δ` about `z₀`.

So a bubbling point of a sequence of Floer solutions absorbs at least the energy `κ`, carried by a
smooth plane. -/
theorem IsNondegenerate.exists_pos_forall_exists_rescale_ofReal_le_lintegral_eval₂ [T2Space M]
    (hω : ω.IsNondegenerate) {K : Set M} (hK : IsCompact K)
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ U, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ y ∈ U, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J y x v))
    (hBs : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks y) x)‖ ≤ B)
    (hBt : ∀ y ∈ U, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt y) x)‖ ≤ B)
    {J₀ : SmoothAlmostComplexStructure I M} (hJ₀ : ∀ x v, J z₀ x v = J₀ x v) :
    ∃ κ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃z : ℕ → ℝ × ℝ⦄,
      (∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) U) → (∀ n, MapsTo (u n) U K) →
      (∀ n, ContinuousOn (ω.floerEnergyDensity Ks Kt (u n)) U) →
      (∀ n, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u n y))
        (ω.perturbedMFDeriv Ks Kt (u n) y).toLinearMap) →
      Tendsto z atTop (𝓝 z₀) →
      Tendsto (fun n ↦ ω.floerEnergyDensity Ks Kt (u n) (z n)) atTop atTop →
      ∃ (φ : ℕ → ℕ) (c' : ℕ → ℝ × ℝ) (ε : ℕ → ℝ) (v : ℝ × ℝ → M), StrictMono φ ∧
        (∀ n, 0 < ε n) ∧ Tendsto c' atTop (𝓝 z₀) ∧ Tendsto ε atTop (𝓝 0) ∧
        TendstoLocallyUniformly (fun n w ↦ e (u (φ n) (c' n + ε n • w))) (e ∘ v) atTop ∧
        ContMDiff 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) v ∧ (∀ w, v w ∈ K) ∧
        (∀ w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag =
          J₀ (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)) ∧
        ENNReal.ofReal κ ≤ ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (v w)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag)) ∧
        ∀ δ > 0, ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (v w)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag)) ≤
          liminf (fun n ↦ ∫⁻ y in ball z₀ δ,
            ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u (φ n)) y)) atTop := by
  have hJ₀t : ω.Tames J₀ := hω.tames_iff.2 fun x v hv ↦ by
    simpa [hJ₀] using hJt z₀ hz₀ x v hv
  obtain ⟨κ, hκ, hquant⟩ := hJ₀t.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne hK
  refine ⟨κ, hκ, fun u z hu huK hρ hsol hz hblow ↦ ?_⟩
  obtain ⟨φ, c', ε, v, hφ, hε, hc', hε0, hv1, hvK, hconv, -, hhol, hv0, -, harea⟩ :=
    hω.exists_rescale_tendstoLocallyUniformly_fderiv_extChartAt_comp hK he he_inj hU hz₀ hJ hXs
      hXt hJt hc hJc hBs hBt hu huK hρ hsol hz hblow
  have hhol₀ (w : ℝ × ℝ) : mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag =
      J₀ (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal) :=
    (hhol w).trans (hJ₀ _ _)
  -- The area density of `v` is `1` at the origin, so `v` is not constant.
  have hne : ∃ w w', v w ≠ v w' := by
    by_contra! hconst
    have hd : mfderiv 𝓘(ℝ, ℝ × ℝ) I v 0 stdComplexLineReal = 0 := by
      rw [show v = fun _ ↦ v 0 from funext fun w ↦ hconst w 0, mfderiv_const]
      -- `exact` rather than `rw`: `stdComplexLineReal` is typed in `ℝ × ℝ`, not `TangentSpace`.
      exact zero_apply _
    rw [hd, SmoothBundleForm.eval₂_zero_left] at hv0
    exact zero_ne_one hv0
  exact ⟨φ, c', ε, v, hφ, hε, hc', hε0, hconv,
    contMDiff_of_mfderiv_stdComplexLineImag_eq hv1 hhol₀, hvK, hhol₀,
    hquant hv1 hvK hhol₀ hne, harea⟩

end Bubble

end TauCeti.SmoothTwoForm
