/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
import Mathlib.Analysis.Complex.Tietze
import TauCeti.Analysis.Calculus.StripTranslate
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity
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

## References

* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their limits at the ends.
-/

public section

open Set Filter Topology MeasureTheory Function
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
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
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

end TauCeti.SmoothTwoForm
