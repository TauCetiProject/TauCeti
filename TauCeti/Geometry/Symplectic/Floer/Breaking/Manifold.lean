/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Rotation
public import TauCeti.Geometry.Symplectic.Floer.Stationary
import Mathlib.Analysis.Complex.Tietze
import TauCeti.Analysis.Calculus.StripTranslate
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Symplectic.Floer.Manifold.Limit
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.Topology.Compactness.Compact
/-!
# Limits of translated Floer cylinders in a manifold

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a closed symplectic manifold, and
`H : ℝ → M → ℝ` a `C¹` Hamiltonian. Let `u_k : ℝ × ℝ → M` be `C¹` solutions of the Floer equation

`∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0`

for the cylindrical perturbation `K = H_t dt`, with almost complex structures `J_k z` on the tangent
spaces `T_{u_k z} M`. Along a long neck of a sequence of Floer cylinders or pairs of pants that
breaks, the energy over translated windows `[a + s_k, b + s_k] × [0, 1]` tends to zero. This file
proves, for a manifold target, that every limit of the translates `(s, t) ↦ u_k(s + s_k, t)` along
such windows is a stationary cylinder `(s, t) ↦ x(t)` over a Hamiltonian orbit `x`
(`IsNondegenerate.exists_hasMFDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`, in the
namespace `TauCeti.SmoothTwoForm`).
For a single solution of finite energy and `s_k → ∞` this is the breaking off of an orbit at an
end; for a sequence of solutions it identifies the necks between the levels of a broken limit.
`TauCeti.Geometry.Symplectic.Floer.Breaking.Basic` proves the same for a symplectic vector space.

As in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`, convergence is measured through a
`C¹` map `e : M → F` into a finite-dimensional normed space, injective on a compact set `K`
containing the values of the `u_k` on the windows and with injective differential at the points of
`K`; on a compact manifold such a map exists by Mathlib's `exists_embedding_euclidean_of_compact`.
The hypothesis is that the maps `e ∘ u_k` translated by `s_k` converge locally uniformly on the
strip `ℝ × [0, 1]` to some `v`. The almost complex structures are uniformly tame with respect to
`e`: `c ‖d e w‖² ≤ ω(w, J_k z w)` with `c > 0`.

The proof transports the problem to `F`:

* by the Floer equation, `∂_s u = -J η` for `η = ∂_t u - X_{H_t}(u)`, and the energy density is
  `ω(∂_s u, J ∂_s u)`, so `‖d e (∂_s u)‖²` is at most the energy density divided by `c`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_fderiv_comp_le`); the defect
  `d e (η)` is bounded in the same way
  (`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`);
* hence `∂_s (e ∘ u_k)` and the defect `∂_t (e ∘ u_k) - Y(t, e ∘ u_k)` tend to zero in `L²`, and
  so in `L¹`, over the windows, where `Y` is a continuous extension of the pushforward
  `d e (X_{H_t})` from `e(K)` to `F` given by the Tietze extension theorem;
* by `TauCeti.eq_of_tendstoLocallyUniformlyOn_comp_add` and
  `TauCeti.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`, the limit `v` does not depend
  on `s`, and `y(t) = v(0, t)` solves `y' = Y(t, y)` on `[0, 1]`;
* the limit lies in the closed set `e(K)`, so `y = e ∘ x` for a path `x` in `K`, continuous on
  `[0, 1]` because `e` restricts to a closed embedding of `K`; since `d e` is injective, `x` has
  velocity `X_{H_t}(x)` (`ContinuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp`).

The convergence of the translates is an assumption here, as in the vector space case. If the
loops satisfy `u_k(s, 0) = u_k(s, 1)`, the relation passes to `v`
(`TauCeti.apply_eq_apply_of_tendstoLocallyUniformlyOn_comp_add`), and injectivity of `e` on `K`
then gives `x(0) = x(1)`.

## Limits of the translates of a single solution with `C¹` convergence

The second part of the file works without the map `e`, for the translates of a single solution
with `C¹` convergence. Let `u` solve the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0`
for `K = H_t dt` on a part `D` of the strip `ℝ × [0, 1]`, with almost complex structures `J_t(x)` on
`T_x M` independent of `s`, as on a cylindrical end, and let `u` have finite energy over `D`. Let
`s_k` be translation parameters with `|s_k| → ∞` such that every window
`[a + s_k, b + s_k] × [0, 1]` eventually lies in `D`. Suppose that the translates
`z ↦ u(z + (s_k, 0))` converge in `C¹` on the strip to a `C¹` map `v`: at every point of the strip
their derivatives converge in the tangent bundle to the derivative of `v`. Then:

* the energy densities of the translates converge pointwise to that of `v`, so by Fatou's lemma
  `v` has zero energy over the strip, the energy of `u` over the translated windows tending to
  zero (`SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add`);
* `v` solves the Floer equation on the strip, for the same structures `J_t`
  (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add`);
* hence, for structures tamed by `ω` along `v`, `v` does not depend on `s`
  (`SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`), by the characterization of
  stationary Floer cylinders by their zero energy
  (`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`);
* `x(t) = v(0, t)` is an orbit segment of the Hamiltonian vector field, `x'(t) = X_{H_t}(x(t))` for
  `t ∈ [0, 1]` (`SmoothTwoForm.IsNondegenerate.hasMFDerivAt_of_tendsto_mfderiv_comp_add`), and the
  perturbed derivative `dv - X_K(v)` vanishes on the strip, so `v` is the stationary Floer cylinder
  over `x` (`SmoothTwoForm.IsNondegenerate.perturbedMFDeriv_eq_zero_of_tendsto_mfderiv_comp_add`).

On a manifold the energy density `ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})` is intrinsic, but there is
no norm of the derivative without a choice of metric; the convergence of the derivatives is
therefore convergence in the tangent bundle, and the structures `J_t` enter through their
continuity in tangent coordinates (`ContinuousLinearMap.inCoordinates`). Unlike the first part,
this needs no compact set of values and no map `e`, and it identifies the limit itself as a Floer
cylinder of zero energy.

## References

* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813.
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their limits at the ends.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 4.5 and the
  chapter on Floer homology, on the removal of the ends of finite-energy solutions.
-/

public section

open Bundle Set Filter Topology MeasureTheory Function
open scoped Manifold ENNReal

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}
  {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}

/-- **The energy controls `∂_s`, measured through `e`.** Let `u` solve the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on a measurable set `U`, where `e : M → F` and `u` are
differentiable, with almost complex structures satisfying `c ‖d e w‖² ≤ ω(w, J z w)`. Then the
integral over `U` of `‖∂_s (e ∘ u)‖²` is at most `1 / c` times the energy over `U`. -/
theorem IsNondegenerate.lintegral_norm_sq_fderiv_comp_le (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {u : ℝ × ℝ → M}
    (he : ∀ z ∈ U, MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ w, c * ‖mvfderiv I e (u z) w‖ ^ 2 ≤ hω.symplecticFormAt (u z) w (J z w))
    (hfloer : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ (e ∘ u) z (1, 0)‖ ^ 2) ≤
      ENNReal.ofReal c⁻¹ *
        ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hU fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  set η := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)
  have hs : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal = -J z η :=
    eq_neg_of_add_eq_zero_left (hfloer z hz)
  -- The chain rule for `e ∘ u`, read as a map between vector spaces.
  have hd : fderiv ℝ (e ∘ u) z (1, 0) =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal) := by
    rw [← stdComplexLineReal_eq]
    exact (mvfderiv_eq_fderiv_apply (e ∘ u) z stdComplexLineReal).symm.trans
      (mvfderiv_comp_apply z (he z hz) (hu z hz) _)
  -- The energy density is `ω(∂_s u, J ∂_s u)`.
  have hρ : ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      hω.symplecticFormAt (u z) (-J z η) (J z (-J z η)) := by
    rw [hω.floerEnergyDensity_zero_left_eq_symplecticFormAt (hfloer z hz), map_neg,
      AlmostComplexStructure.apply_apply, neg_neg, ← (hω.symplecticFormAt (u z)).neg_eq (J z η)]
    simp [η]
  rw [hd, hs, hρ, le_inv_mul_iff₀ hc]
  exact hJc z hz _

section Helpers

variable {u : ℕ → ℝ × ℝ → M} {s : ℕ → ℝ}

omit [NormedSpace ℝ F] in
/-- On windows of width `b - a`, an `L²` bound by the energy, which tends to zero, gives `L¹`
convergence to zero. -/
private theorem tendsto_setLIntegral_enorm_of_le_mul_energy {U : Set (ℝ × ℝ)} {c : ℝ}
    (hWU : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ U)
    (hen : ∀ a b : ℝ, Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z)) atTop (𝓝 0))
    {g : ℕ → ℝ × ℝ → F} (hg : ∀ k, ContinuousOn (g k) U) (a b : ℝ)
    (hle : ∀ᶠ k in atTop, ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ENNReal.ofReal (‖g k z‖ ^ 2) ≤ ENNReal.ofReal c⁻¹ *
        ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z)) :
    Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1, ‖g k z‖ₑ) atTop (𝓝 0) := by
  have hlim := ENNReal.Tendsto.const_mul (hen a b) (Or.inr (ENNReal.ofReal_ne_top (r := c⁻¹)))
  rw [mul_zero] at hlim
  exact tendsto_setLIntegral_enorm_Icc_prod_of_tendsto_setLIntegral_ofReal_norm_sq
    ((hWU a b).mono fun k hk ↦ ((hg k).mono hk).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Icc))
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ ↦ zero_le) hle)

omit [NormedSpace ℝ F] in
/-- A stationary limit `v` of the translates of `e ∘ u_k`, where the translates eventually take
values in a compact set `K` on which `e` is injective, is read back in `M`: there is a path `x` in
`K` with `v(s, t) = e (x t)`, continuous on `[0, 1]`, to which the translates converge in `M`. -/
private theorem exists_eq_comp_tendsto_of_tendstoLocallyUniformlyOn {K : Set M}
    (he : Continuous e) (hK : IsCompact K) (he_inj : InjOn e K) {v : ℝ × ℝ → F}
    (hzK : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1, ∀ᶠ k in atTop, u k (z + (s k, 0)) ∈ K)
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ e (u k (z + (s k, 0)))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hstat : ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t))
    (hyc : ContinuousOn (fun t ↦ v (0, t)) (Icc 0 1)) :
    ∃ x : ℝ → M, (∀ t, x t ∈ K) ∧ (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, v z = e (x z.2)) ∧
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, Tendsto (fun k ↦ u k (z + (s k, 0))) atTop (𝓝 (x z.2))) ∧
      ContinuousOn x (Icc 0 1) := by
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    hK.isClosedEmbedding_domRestrict he.continuousOn he_inj
  -- The limit lies in the closed set `e(K)`.
  have hvK : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1, v z ∈ e '' K := fun z hz ↦
    (hK.image he).isClosed.mem_of_tendsto (hv.tendsto_at hz)
      ((hzK z hz).mono fun _ hk ↦ mem_image_of_mem e hk)
  have hmem : ∀ t, ∃ p ∈ K, t ∈ Icc (0 : ℝ) 1 → e p = v (0, t) := fun t ↦ by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · obtain ⟨p, hp, hpe⟩ := hvK (0, t) ⟨mem_univ _, ht⟩
      exact ⟨p, hp, fun _ ↦ hpe⟩
    · obtain ⟨p, hp, -⟩ := hvK (0, 0) ⟨mem_univ _, left_mem_Icc.2 zero_le_one⟩
      exact ⟨p, hp, fun h ↦ absurd h ht⟩
  choose x hxK hx using hmem
  have hvx : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1, v z = e (x z.2) := fun z hz ↦ by
    rw [hx z.2 hz.2, hstat z.1 z.2 hz.2]
  -- Inside `K`, convergence and continuity are measured by `e`.
  refine ⟨x, hxK, hvx, fun z hz ↦ ?_, continuous_subtypeVal.comp_continuousOn
    (f := fun t ↦ (⟨x t, hxK t⟩ : K)) ?_⟩
  · refine hK.tendsto_nhds_of_tendsto_comp he.continuousOn he_inj (hzK z hz) (hxK z.2) ?_
    simpa only [comp_def, ← hvx z hz] using hv.tendsto_at hz
  · exact hemb.isEmbedding.continuousOn_iff.2 (hyc.congr fun t ht ↦ hx t ht)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The pushforward `(t, p) ↦ d e_p (X_{H_t}(p))` of the Hamiltonian vector field, on `ℝ × K` for
a compact set `K` on which `e` is injective, extends to a continuous field on `ℝ × F`. -/
private theorem exists_continuous_apply_eq_mvfderiv_hamiltonianVectorField
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K) :
    ∃ Φ : ℝ × F → F, Continuous Φ ∧
      ∀ t, ∀ p ∈ K, Φ (t, e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p) := by
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    hK.isClosedEmbedding_domRestrict he.continuous.continuousOn he_inj
  have hXe := hω.continuous_mvfderiv_hamiltonianVectorField hH he
  -- The Tietze extension theorem along the closed embedding `ℝ × K → ℝ × F`.
  obtain ⟨Φ, hΦ⟩ := ContinuousMap.exists_extension' (IsClosedEmbedding.id.prodMap hemb)
    ⟨fun q : ℝ × K ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2),
      hXe.comp (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))⟩
  exact ⟨Φ, Φ.continuous, fun t p hp ↦ congrFun hΦ ((t, ⟨p, hp⟩) : ℝ × K)⟩

end Helpers

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Limits of translated Floer cylinders in a manifold along windows of vanishing energy are
stationary cylinders over Hamiltonian orbits.** Let `ω` be a nondegenerate two-form on a manifold
`M` and `H` a `C¹` Hamiltonian. Let each `u_k` be `C¹` on an open set `U` and solve the Floer
equation `∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on `E ⊆ U`, with values in a compact set `K` on
`E`. Let `e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `K` and
with injective differential at the points of `K`, and let the almost complex structures be
uniformly tame with respect to `e`: `c ‖d e w‖² ≤ ω(w, J_k z w)` on `E`, with `c > 0`
independent of `k`. Let `s_k` be translation parameters such that each window
`[a + s_k, b + s_k] × [0, 1]` eventually lies in `E` and the energy of `u_k` over it tends to
zero. If the translates `(s, t) ↦ e (u_k(s + s_k, t))` converge locally uniformly on the strip
`ℝ × [0, 1]` to `v`, then there is a path `x` in `K` such that `v(s, t) = e (x t)` on the strip,
the translates `u_k(s + s_k, t)` converge to `x t` in `M`, and `x' = X_{H_t}(x)` on `[0, 1]`.

For a single solution `u_k = u` of finite energy over `E` and `s_k → ∞`, the energy hypothesis
follows from `TauCeti.tendsto_setLIntegral_of_eventually_subset`. -/
theorem IsNondegenerate.exists_hasMFDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℕ → ℝ × ℝ → M} {U E : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u k) U) (hEU : E ⊆ U)
    (huK : ∀ k, ∀ z ∈ E, u k z ∈ K)
    (J : ∀ k z, AlmostComplexStructure (TangentSpace I (u k z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ E, ∀ w,
      c * ‖mvfderiv I e (u k z) w‖ ^ 2 ≤ hω.symplecticFormAt (u k z) w (J k z w))
    (hfloer : ∀ k, ∀ z ∈ E, mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal +
      J k z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u k z)) = 0)
    {s : ℕ → ℝ} (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hen : ∀ a b : ℝ, Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z)) atTop (𝓝 0))
    {v : ℝ × ℝ → F} (hv : TendstoLocallyUniformlyOn (fun k z ↦ e (u k (z + (s k, 0)))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    ∃ x : ℝ → M, (∀ t, x t ∈ K) ∧ (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, v z = e (x z.2)) ∧
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, Tendsto (fun k ↦ u k (z + (s k, 0))) atTop (𝓝 (x z.2))) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I x (Icc 0 1) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) := by
  obtain ⟨Φ, hΦc, hΦe⟩ :=
    exists_continuous_apply_eq_mvfderiv_hamiltonianVectorField hω hH he hK he_inj
  -- The maps `e ∘ u_k` are `C¹` maps into `F`.
  have hw : ∀ k, ContDiffOn ℝ 1 (e ∘ u k) U := fun k ↦
    contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn (hu k))
  have hmd : ∀ k, ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z := fun k z hz ↦
    ((hu k).contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hWU (a b : ℝ) : ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ U :=
    (hW a b).mono fun _ hk ↦ hk.trans hEU
  -- `∂_s (e ∘ u_k)` and the defect `∂_t (e ∘ u_k) - Φ(t, e ∘ u_k)` tend to zero in `L¹`.
  have hd (a b : ℝ) : Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ‖fderiv ℝ (e ∘ u k) z (1, 0)‖ₑ) atTop (𝓝 0) := by
    refine tendsto_setLIntegral_enorm_of_le_mul_energy (c := c) hWU hen (fun k ↦
      ((hw k).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const) a b ?_
    filter_upwards [hW a b] with k hk
    exact hω.lintegral_norm_sq_fderiv_comp_le (measurableSet_Icc.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero) (fun z hz ↦ hmd k z (hEU (hk hz))) (J k) hc
      (fun z hz ↦ hJc k z (hk hz)) fun z hz ↦ hfloer k z (hk hz)
  have hdΦ : Tendsto (fun k ↦ ∫⁻ z in Icc (s k) (1 + s k) ×ˢ Icc 0 1,
      ‖fderiv ℝ (e ∘ u k) z (0, 1) - Φ (z.2, (e ∘ u k) z)‖ₑ) atTop (𝓝 0) := by
    have h := tendsto_setLIntegral_enorm_of_le_mul_energy (c := c) hWU hen
      (g := fun k ↦ sliceDefect (fun t y ↦ Φ (t, y)) (e ∘ u k)) (fun k ↦
        ((((hw k).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).sub
          (hΦc.comp_continuousOn (continuousOn_snd.prodMk (hw k).continuousOn))).congr
          fun z _ ↦ sliceDefect_def _ _ z) 0 1 ?_
    · simpa only [zero_add, sliceDefect_def] using h
    filter_upwards [hW 0 1] with k hk
    exact hω.lintegral_norm_sq_sliceDefect_comp_le (measurableSet_Icc.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero) (fun z hz ↦ hmd k z (hEU (hk hz)))
      (fun z hz ↦ hΦe _ _ (huK k z (hk hz))) (J k) hc (fun z hz ↦ hJc k z (hk hz))
      fun z hz ↦ hfloer k z (hk hz)
  -- The limit is independent of `s` and its loop `y = v(0, ·)` solves `y' = Φ(t, y)`.
  have hstat := TauCeti.eq_of_tendstoLocallyUniformlyOn_comp_add hU hw hWU hd hv
  have hy := TauCeti.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add hΦc hU hw hWU hd
    hdΦ hv
  -- Read the limit back in `M`: it is `e ∘ x` for a path `x` in `K`.
  obtain ⟨x, hxK, hvx, hconv, hxc⟩ := exists_eq_comp_tendsto_of_tendstoLocallyUniformlyOn
    he.continuous hK he_inj (fun z hz ↦ (hW z.1 z.1).mono fun k hk ↦
      huK k _ (hk ⟨⟨by simp, by simp⟩, by simpa using hz.2⟩)) hv hstat
    fun t ht ↦ (hy t ht).continuousWithinAt
  refine ⟨x, hxK, hvx, hconv, fun t ht ↦ ?_⟩
  -- Since `d e` is injective, `x` has velocity `X_{H_t}(x)`.
  refine (hxc t ht).hasMFDerivWithinAt_of_hasDerivWithinAt_comp
    (.of_injective_of_finiteDimensional (hde _ (hxK t))) ?_
  rw [← hΦe t _ (hxK t), ← hvx (0, t) ⟨mem_univ _, ht⟩]
  exact (hy t ht).congr_of_mem (fun τ hτ ↦ (hvx (0, τ) ⟨mem_univ _, hτ⟩).symm) ht

section TangentBundleLimit

variable {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {u v : ℝ × ℝ → M} {s : ℕ → ℝ} {U D : Set (ℝ × ℝ)}

/-- For `K = H_t dt` with `H` jointly `C¹`, the Hamiltonian vector field of the `dt` component of
`K` is continuous on the domain times `M`, as a map into the tangent bundle. -/
private theorem IsNondegenerate.continuous_hamiltonianVectorField_cylindrical
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) :
    Continuous fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField ((fun w : ℝ × ℝ ↦ H w.2) p.1) p.2⟩ : TangentBundle I M) := by
  have hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (0 + 1) (uncurry fun (w : ℝ × ℝ) ↦ H w.2) := by
    rw [zero_add]
    exact hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  exact (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp) hK).continuous

/-- The Hamiltonian vector field of the zero `ds` component of `K = H_t dt` is continuous on the
domain times `M`, as a map into the tangent bundle. -/
private theorem IsNondegenerate.continuous_hamiltonianVectorField_zero (hω : ω.IsNondegenerate) :
    Continuous fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField ((fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) p.1) p.2⟩ :
        TangentBundle I M) := by
  have hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (0 + 1)
      (uncurry fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) := contMDiff_const
  exact (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp) hK).continuous

/-- The energy of the limit of the translates over a rectangle `[a, b] × [0, 1]` vanishes, by
Fatou's lemma: the energy densities of the translates converge pointwise to that of `v`, and the
energy of `u` over the translated windows `[a + s_k, b + s_k] × [0, 1]` tends to zero. -/
private theorem setLIntegral_Icc_prod_floerEnergyDensity_eq_zero (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩)) (a b : ℝ) :
    ∫⁻ z in Icc a b ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) = 0 := by
  set e : (ℝ × ℝ → M) → ℝ × ℝ → ENNReal := fun w z ↦
    ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) w z) with he
  have hXt := hω.continuous_hamiltonianVectorField_cylindrical hH
  have hXs := hω.continuous_hamiltonianVectorField_zero (I := I)
  have hcont : ContinuousOn (e u) U := ENNReal.continuous_ofReal.comp_continuousOn
    (ω.continuousOn_floerEnergyDensity hU hu hXs.continuousOn hXt.continuousOn)
  set W : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 1
  have hWm : MeasurableSet W := measurableSet_Icc.prod measurableSet_Icc
  -- The translation `z ↦ z + (c, 0)` preserves the Lebesgue measure of the plane and maps `W`
  -- onto the window `[a + c, b + c] × [0, 1]`.
  have hμ (c : ℝ) : MeasurePreserving (fun z : ℝ × ℝ ↦ z + ((c, 0) : ℝ × ℝ)) volume volume := by
    have hfun : (fun z : ℝ × ℝ ↦ z + ((c, 0) : ℝ × ℝ)) = Prod.map (· + c) id :=
      funext fun z ↦ Prod.ext (by simp) (by simp)
    rw [hfun]
    exact (measurePreserving_add_right volume c).prod (MeasurePreserving.id volume)
  have hpre (c : ℝ) :
      W = (fun z ↦ z + ((c, 0) : ℝ × ℝ)) ⁻¹' (Icc (a + c) (b + c) ×ˢ Icc 0 1) := by
    ext ⟨x, y⟩
    simp only [W, mem_preimage, mem_prod, Prod.mk_add_mk, mem_Icc, add_zero]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hW a b)
  have hmem {n : ℕ} {z : ℝ × ℝ} (hz : z ∈ W) : z + (s (n + N), 0) ∈ D := by
    rw [hpre (s (n + N))] at hz
    exact hN (n + N) (Nat.le_add_left N n) hz
  -- Along the tail `k = n + N`, the translated energy densities converge pointwise on `W` to the
  -- energy density of `v`.
  have hlim (z : ℝ × ℝ) (hz : z ∈ W) :
      Tendsto (fun n : ℕ ↦ e u (z + (s (n + N), 0))) atTop (𝓝 (e v z)) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp
      (ω.tendsto_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
        (u := fun k w ↦ u (w + (s k, 0))) tendsto_const_nhds
        (hdu z ⟨mem_univ _, hz.2⟩) hXs.continuousAt hXt.continuousAt)
    refine ((tendsto_add_atTop_iff_nat N).2 h).congr fun n ↦ ?_
    simp only [comp_apply, he]
    rw [floerEnergyDensity_cylindrical_comp_add_right]
  -- The energies of `u` over the translated windows tend to zero.
  have hE : Tendsto (fun n : ℕ ↦ ∫⁻ z in W, e u (z + (s (n + N), 0))) atTop (𝓝 0) := by
    have h := tendsto_setLIntegral_of_eventually_subset hfin
      (A := fun k ↦ Icc (a + s k) (b + s k) ×ˢ Icc 0 1)
      (eventually_Icc_add_prod_subset_inter hs (hW a b))
    refine ((tendsto_add_atTop_iff_nat N).2 h).congr fun n ↦ ?_
    rw [hpre (s (n + N))]
    exact ((hμ (s (n + N))).setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _)
      (e u) _).symm
  -- Fatou's lemma.
  have hmeas (n : ℕ) : AEMeasurable (fun z ↦ e u (z + (s (n + N), 0))) (volume.restrict W) :=
    (hcont.comp (continuous_id.add continuous_const).continuousOn
      fun z hz ↦ hDU (hmem hz)).aemeasurable hWm
  refine le_antisymm ?_ zero_le
  calc ∫⁻ z in W, e v z
      = ∫⁻ z in W, liminf (fun n : ℕ ↦ e u (z + (s (n + N), 0))) atTop :=
        setLIntegral_congr_fun hWm fun z hz ↦ (hlim z hz).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ ↦ ∫⁻ z in W, e u (z + (s (n + N), 0))) atTop :=
        lintegral_liminf_le' hmeas
    _ = 0 := hE.liminf_eq

/-- **The limit of translated Floer cylinders has zero energy.** Let `u` be `C¹` on an open set `U`
containing `D`, with finite energy over `D` for the cylindrical perturbation `K = H_t dt`, where `H`
is jointly `C¹`. Let `|s_k| → ∞`, with every window `[a + s_k, b + s_k] × [0, 1]` eventually in
`D`, and suppose that at every point of the strip `ℝ × [0, 1]` the derivatives of the translates
`w ↦ u (w + (s_k, 0))` converge in the tangent bundle to the derivative of a map `v`. Then the
energy of `v` over the strip vanishes. No Floer equation is needed: the energy densities converge
pointwise, and the energy of `u` over the translated windows tends to zero. -/
theorem lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) = 0 := by
  -- The rectangles `[-n, n] × [0, 1]` exhaust the strip.
  rw [← iUnion_Icc_neg_prod]
  exact le_antisymm ((lintegral_iUnion_le _ _).trans (tsum_eq_zero_iff.2 fun n ↦
    setLIntegral_Icc_prod_floerEnergyDensity_eq_zero hω hH hU hu hDU hfin hs hW hdu _ _).le)
    zero_le

/-- **The limit of translated Floer cylinders is a Floer cylinder.** Let `u` solve the Floer
equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on `D`, for the cylindrical perturbation
`K = H_t dt` with `H` jointly `C¹` and structures `J_t` independent of `s`. Suppose that at every
point `z` of the strip `ℝ × [0, 1]` the translates `z + (s_k, 0)` eventually lie in `D`, the
derivatives of the translates `w ↦ u (w + (s_k, 0))` converge in the tangent bundle to the
derivative of a map `v`, and that `J` is continuous at `(z.2, v z)` in the tangent coordinates at
`v z`. Then `v` solves the Floer equation on the strip. -/
theorem isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hD : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ᶠ k in atTop, z + (s k, 0) ∈ D)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z)) :
    ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (v z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z).toLinearMap := by
  intro z hz
  -- The translates solve the Floer equation at `z` as soon as `z + (s_k, 0)` lies in `D`.
  have hsol : ∀ᶠ k in atTop, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u (z + (s k, 0)))) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ u (w + (s k, 0))) z).toLinearMap := by
    filter_upwards [hD z hz] with k hzk
    have hF := hfloer _ hzk
    have h2 : (z + (s k, 0)).2 = z.2 := by simp
    rw [h2] at hF
    exact ω.isComplexLinearMap_perturbedMFDeriv_comp_add_right rfl (by simp) hF
  have hJ' := (hJ z hz).comp (x := (z, v z)) (f := fun p : (ℝ × ℝ) × M ↦ (p.1.2, p.2))
    (by fun_prop)
  exact ω.isComplexLinearMap_perturbedMFDeriv_of_tendsto (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (J := fun w x ↦ J w.2 x) (u := fun k w ↦ u (w + (s k, 0)))
    tendsto_const_nhds (hdu z hz) hJ' hω.continuous_hamiltonianVectorField_zero.continuousAt
    (hω.continuous_hamiltonianVectorField_cylindrical hH).continuousAt hsol

/-- **The limit of translated Floer cylinders is independent of `s`.** Under the hypotheses of
`TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add` and
`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add`, if the
limit `v` is `C¹` and the structures `J_t` are tamed by `ω` at the points of `v` on the strip
`ℝ × [0, 1]`, then `v (r, t) = v (0, t)` on the strip. -/
theorem IsNondegenerate.eq_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z))) :
    ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t) := by
  have hsol := isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add hω hH hfloer
    (fun z hz ↦ (hW z.1 z.1).mono fun _ hk ↦ hk ⟨⟨by simp, by simp⟩, by simpa using hz.2⟩) hdu hJ
  refine (hω.lintegral_floerEnergyDensity_eq_zero_iff (J := fun z ↦ J z.2 (v z)) hH hv hJt
    (fun z hz ↦ ?_)).1 (lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add hω hH hU
      hu hDU hfin hs hW hdu)
  have h := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ v z _).1 (hsol z hz)
  -- The `ds` component of `K` vanishes, and so does its Hamiltonian vector field.
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at h

/-- Both components of the perturbed derivative of the limit vanish on the strip: `∂_s v = 0` and
`∂_t v = X_{H_t}(v)`. -/
private theorem IsNondegenerate.mfderiv_eq_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z)))
    {z : ℝ × ℝ} (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal = 0 ∧
      mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineImag = ω.hamiltonianVectorField (H z.2) (v z) := by
  have hstat := hω.eq_of_tendsto_mfderiv_comp_add hH hU hu hDU hfloer hfin hs hW hv hdu hJ hJt
  have hs0 : mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal = 0 := by
    rw [stdComplexLineReal_eq]
    exact Manifold.mfderiv_apply_one_zero_eq_zero_of_apply_eq
      ((hv z).mdifferentiableAt one_ne_zero) fun q ↦ hstat q z.2 hz.2
  refine ⟨hs0, ?_⟩
  -- The Floer equation `∂_s v + J (∂_t v - X) = 0` with `∂_s v = 0` gives `J (∂_t v - X) = 0`, and
  -- an almost complex structure is injective, since `J (J w) = -w`.
  have hF := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ v z _).1
    (isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add hω hH hfloer
      (fun z hz ↦ (hW z.1 z.1).mono fun _ hk ↦ hk ⟨⟨by simp, by simp⟩, by simpa using hz.2⟩)
      hdu hJ z hz)
  rw [hs0, hamiltonianVectorField_const, Pi.zero_apply, sub_zero, zero_add] at hF
  have h' := congrArg (J z.2 (v z)) hF
  rw [AlmostComplexStructure.apply_apply, map_zero, neg_eq_zero] at h'
  exact sub_eq_zero.1 h'

/-- **The limit of translated Floer cylinders is a Hamiltonian orbit segment.** Under the
hypotheses of `TauCeti.SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`, the curve
`x(t) = v (0, t)` solves `x'(t) = X_{H_t}(x(t))` for every `t ∈ [0, 1]`. -/
theorem IsNondegenerate.hasMFDerivAt_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z))) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ v (0, t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H t) (v (0, t)))) := by
  intro t ht
  have hvt : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (0, t) := (hv _).mdifferentiableAt one_ne_zero
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun t ↦ v (0, t)) t :=
    hvt.comp t ((differentiableAt_const 0).prodMk differentiableAt_id).mdifferentiableAt
  have h := Manifold.hasMFDerivAt_curveVelocity hc
  rwa [Manifold.curveVelocity_eq_mfderiv_snd (f := fun a b ↦ v (a, b)) hvt, ← stdComplexLineImag_eq,
    (hω.mfderiv_eq_of_tendsto_mfderiv_comp_add hH hU hu hDU hfloer hfin hs hW hv hdu hJ hJt
      (z := (0, t)) ⟨mem_univ _, ht⟩).2] at h

/-- **The limit of translated Floer cylinders is a stationary Floer cylinder.** Under the
hypotheses of `TauCeti.SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`, the
perturbed derivative `dv - X_K(v)` of the limit vanishes on the strip `ℝ × [0, 1]`. -/
theorem IsNondegenerate.perturbedMFDeriv_eq_zero_of_tendsto_mfderiv_comp_add
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z))) :
    ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z = 0 := by
  intro z hz
  obtain ⟨hs0, ht0⟩ :=
    hω.mfderiv_eq_of_tendsto_mfderiv_comp_add hH hU hu hDU hfloer hfin hs hW hv hdu hJ hJt hz
  -- A linear map on `ℝ × ℝ` vanishes when it vanishes on `(1, 0)` and `(0, 1)`.
  refine ContinuousLinearMap.ext fun e ↦ ?_
  have he : e = e.1 • stdComplexLineReal + e.2 • stdComplexLineImag := by
    simp [stdComplexLineReal_eq, stdComplexLineImag_eq]
  rw [he, map_add, map_smul, map_smul, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag, hs0, ht0, hamiltonianVectorField_const]
  simp

end TangentBundleLimit

end TauCeti.SmoothTwoForm
