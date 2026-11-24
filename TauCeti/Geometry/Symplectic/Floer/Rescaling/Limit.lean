/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Manifold

/-!
# The limit of rescaled Floer solutions in a manifold

At a point `z₀` where the energy densities of a sequence of Floer solutions `uᵢ` in a manifold `M`
blow up, bubbling analysis rescales the solutions at centres `cᵢ → z₀` by scales `εᵢ → 0` to maps
`w ↦ uᵢ(cᵢ + εᵢ w)`, which solve the Floer equation for the rescaled perturbation
`εᵢ K(cᵢ + εᵢ w)` and have energy density one at the origin and at most four on discs of radii
`Rᵢ → ∞` (`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv`). This file
shows that a subsequence of the rescaled maps converges to a continuous map `v : ℝ × ℝ → M`, the
candidate bubble at `z₀`.

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

The limit is only shown to be continuous. That it is pseudoholomorphic for the structure
`J(z₀, ·)` frozen at the bubbling point and nonconstant needs the convergence of the derivatives
of the rescaled maps, which is not treated here; given that convergence, these are
`TauCeti.SmoothTwoForm.isComplexLinearMap_of_tendsto_rescale` and
`TauCeti.SmoothTwoForm.tendsto_floerEnergyDensity_rescale`. That it extends to a sphere needs
removal of singularities, which is not provided either.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.2
  (rescaling at a point where the derivatives blow up) and Section 4.6 (bubbling off).
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
pointwise in `M`, to a continuous map `v : ℝ × ℝ → M` with values in `K`. This is the candidate
bubble, shown here only to be continuous, not holomorphic or nonconstant. -/
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
`e` and pointwise in `M`, to a continuous map `v : ℝ × ℝ → M` with values in `K`. The limit is
only shown to be continuous, not holomorphic or nonconstant. -/
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

end TauCeti.SmoothTwoForm
