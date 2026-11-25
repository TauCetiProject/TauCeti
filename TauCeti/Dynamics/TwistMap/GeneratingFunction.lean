/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.Exact
public import TauCeti.Dynamics.TwistMap.OpenStrip
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The generating function of an exact monotone twist map

Let `F` be a monotone twist map of the open strip `ℝ × J` (`TauCeti.IsMonotoneTwistMap`) and
`Q(x, y) = (x, F₁(x, y))` its *endpoint map* (`TauCeti.twistEndpointMap`), which records the
first coordinates of the two ends of the step `(x, y) ↦ F(x, y)`. Since `y ↦ F₁(x, y)` is strictly
increasing with `∂_y F₁ > 0`, `Q` is injective on the strip
(`TauCeti.IsMonotoneTwistMap.injOn_twistEndpointMap`) with invertible derivative
`(u, v) ↦ (u, (dF(u, v))₁)`, so its image `D` is open
(`TauCeti.IsMonotoneTwistMap.isOpen_image_twistEndpointMap`) and the inverse of `Q` on `D` is
differentiable.

If `F` is exact for the primitive `λ = g dx` with primitive `S`, that is
`dS_p = g(F p) (dF_p)₁ − g(p) dx` on the strip, then `h = S ∘ Q⁻¹ : D → ℝ`
(`TauCeti.twistGeneratingFunction`) is a generating function of `F`
(`TauCeti.IsMonotoneTwistMap.hasFDerivAt_twistGeneratingFunction`):

`dh_{Q(p)} = g(F p) dX − g(p) dx`, that is `g(x, y) = −∂₁h(x, F₁(x, y))` and
`g(F(x, y)) = ∂₂h(x, F₁(x, y))`,

with `h ∘ Q = S` on the strip (`TauCeti.IsMonotoneTwistMap.twistGeneratingFunction_apply`), and `h`
is invariant under the diagonal deck translation `(x, X) ↦ (x + ℓ, X + ℓ)` when `S` is `ℓ`-periodic
(`TauCeti.IsMonotoneTwistMap.twistGeneratingFunction_add_period`).

## References

* M. R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau, Vol. 1*,
  Astérisque 103–104, 1983, Chapitre I, §4.3.
-/

public section

noncomputable section

open Set Filter Topology Function

namespace TauCeti

/-- The *endpoint map* `Q(x, y) = (x, F₁(x, y))` of a map `F` of the plane. -/
def twistEndpointMap (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, (F p).1)

theorem twistEndpointMap_def (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) :
    twistEndpointMap F p = (p.1, (F p).1) :=
  (rfl)

/-- The *generating function* `h = S ∘ Q⁻¹` of a map `F` of the strip `ℝ × J` with primitive `S`,
`Q⁻¹` being the inverse of the endpoint map `Q` on the strip. -/
def twistGeneratingFunction (J : Set ℝ) (F : ℝ × ℝ → ℝ × ℝ) (S : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  S ∘ invFunOn (twistEndpointMap F) (univ ×ˢ J)

theorem twistGeneratingFunction_def (J : Set ℝ) (F : ℝ × ℝ → ℝ × ℝ) (S : ℝ × ℝ → ℝ) :
    twistGeneratingFunction J F S = S ∘ invFunOn (twistEndpointMap F) (univ ×ˢ J) :=
  (rfl)

/-- The linear map `(u, v) ↦ (u, A(u, v))` is invertible when `A(0, 1) ≠ 0`. -/
private def fstProdEquiv (A : ℝ × ℝ →L[ℝ] ℝ) (hA : A (0, 1) ≠ 0) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  (LinearEquiv.ofInjectiveEndo ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod A : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ)
    (by
      intro v w h
      have h1 : v.1 = w.1 := by simpa using congrArg Prod.fst h
      have h2 : A v = A w := by simpa using congrArg Prod.snd h
      have hv : v = (v.1, 0) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      have hw : w = (w.1, 0) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      rw [hv, hw, map_add, map_add, map_smul, map_smul, h1, smul_eq_mul, smul_eq_mul] at h2
      have h3 : v.2 = w.2 := mul_right_cancel₀ hA (add_left_cancel h2)
      exact Prod.ext h1 h3)).toContinuousLinearEquiv

private theorem coe_fstProdEquiv (A : ℝ × ℝ →L[ℝ] ℝ) (hA : A (0, 1) ≠ 0) :
    (fstProdEquiv A hA : ℝ × ℝ →L[ℝ] ℝ × ℝ) = (ContinuousLinearMap.fst ℝ ℝ ℝ).prod A := by
  ext <;> rfl

namespace IsMonotoneTwistMap

variable {ℓ : ℝ} {J : Set ℝ} {F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}

theorem isOpen_strip (hF : IsMonotoneTwistMap ℓ J F) : IsOpen (univ ×ˢ J : Set (ℝ × ℝ)) :=
  isOpen_univ.prod hF.isOpen

/-- On the strip, the endpoint map has the strict derivative `(u, v) ↦ (u, (dF(u, v))₁)`. -/
theorem hasStrictFDerivAt_twistEndpointMap (hF : IsMonotoneTwistMap ℓ J F) {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ J) :
    HasStrictFDerivAt (twistEndpointMap F)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p))) p := by
  have hC : ContDiffAt ℝ 1 F p := hF.contDiffOn.contDiffAt (hF.isOpen_strip.mem_nhds hp)
  have hFs : HasStrictFDerivAt F (fderiv ℝ F p) p := hC.hasStrictFDerivAt_fderiv one_ne_zero
  exact hasStrictFDerivAt_fst.prodMk hFs.fst

/-- **The endpoint map is injective on the strip**, by the twist condition. -/
theorem injOn_twistEndpointMap (hF : IsMonotoneTwistMap ℓ J F) :
    InjOn (twistEndpointMap F) (univ ×ˢ J) := by
  rintro ⟨x, y⟩ ⟨-, hy⟩ ⟨x', y'⟩ ⟨-, hy'⟩ h
  simp only [twistEndpointMap_def, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact Prod.ext rfl ((hF.strictMonoOn_fst x).injOn hy hy' h)

/-- On the strip, the endpoint map sends neighbourhoods to neighbourhoods. -/
theorem map_twistEndpointMap_nhds (hF : IsMonotoneTwistMap ℓ J F) {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ J) : map (twistEndpointMap F) (𝓝 p) = 𝓝 (twistEndpointMap F p) := by
  have hA : (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) (0, 1) ≠ 0 :=
    (hF.fderiv_fst_pos p hp).ne'
  have h := hF.hasStrictFDerivAt_twistEndpointMap hp
  rw [← coe_fstProdEquiv _ hA] at h
  exact h.map_nhds_eq_of_equiv

/-- **The image `D` of the strip under the endpoint map is open.** -/
theorem isOpen_image_twistEndpointMap (hF : IsMonotoneTwistMap ℓ J F) :
    IsOpen (twistEndpointMap F '' (univ ×ˢ J)) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨p, hp, rfl⟩
  rw [← hF.map_twistEndpointMap_nhds hp]
  exact image_mem_map (hF.isOpen_strip.mem_nhds hp)

/-- The inverse of the endpoint map on the strip is a left inverse on the strip. -/
theorem invFunOn_twistEndpointMap (hF : IsMonotoneTwistMap ℓ J F) {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ J) :
    invFunOn (twistEndpointMap F) (univ ×ˢ J) (twistEndpointMap F p) = p :=
  hF.injOn_twistEndpointMap.leftInvOn_invFunOn hp

/-- The inverse of the endpoint map on the strip is continuous at every point of `D`. -/
theorem continuousAt_invFunOn_twistEndpointMap (hF : IsMonotoneTwistMap ℓ J F) {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ J) :
    ContinuousAt (invFunOn (twistEndpointMap F) (univ ×ˢ J)) (twistEndpointMap F p) := by
  intro V hV
  rw [hF.invFunOn_twistEndpointMap hp] at hV
  rw [Filter.mem_map, ← hF.map_twistEndpointMap_nhds hp]
  refine mem_of_superset (image_mem_map (inter_mem hV (hF.isOpen_strip.mem_nhds hp))) ?_
  rintro _ ⟨p', hp', rfl⟩
  rw [mem_preimage, hF.invFunOn_twistEndpointMap hp'.2]
  exact hp'.1

/-- **The generating function recovers the primitive**: `h ∘ Q = S` on the strip. -/
theorem twistGeneratingFunction_apply (hF : IsMonotoneTwistMap ℓ J F) (S : ℝ × ℝ → ℝ)
    {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ J) :
    twistGeneratingFunction J F S (twistEndpointMap F p) = S p := by
  rw [twistGeneratingFunction_def, comp_apply, hF.invFunOn_twistEndpointMap hp]

/-- **The generating function of an exact monotone twist map.** If `S` is a primitive of
`F*λ − λ` for `λ = g dx`, that is `dS_p = g(F p) (dF_p)₁ − g(p) dx` on the strip, then
`h = S ∘ Q⁻¹` has derivative `g(F p) dX − g(p) dx` at `Q(p) = (x, F₁(x, y))`:
`∂₁h(x, F₁(x, y)) = −g(x, y)` and `∂₂h(x, F₁(x, y)) = g(F(x, y))`. -/
theorem hasFDerivAt_twistGeneratingFunction (hF : IsMonotoneTwistMap ℓ J F) {g S : ℝ × ℝ → ℝ}
    (hS : ∀ p ∈ univ ×ˢ J, HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (fderiv ℝ F p) - g p • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ J) :
    HasFDerivAt (twistGeneratingFunction J F S)
      (g (F p) • ContinuousLinearMap.snd ℝ ℝ ℝ - g p • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (twistEndpointMap F p) := by
  set R := invFunOn (twistEndpointMap F) (univ ×ˢ J)
  have hA : (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) (0, 1) ≠ 0 :=
    (hF.fderiv_fst_pos p hp).ne'
  set L := fstProdEquiv _ hA
  have hRp : R (twistEndpointMap F p) = p := hF.invFunOn_twistEndpointMap hp
  -- The inverse `R` has derivative `L⁻¹` at `Q(p)`.
  have hQ : HasFDerivAt (twistEndpointMap F) (L : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      (R (twistEndpointMap F p)) := by
    rw [hRp, coe_fstProdEquiv]
    exact (hF.hasStrictFDerivAt_twistEndpointMap hp).hasFDerivAt
  have hR : HasFDerivAt R (L.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) (twistEndpointMap F p) := by
    refine HasFDerivAt.of_local_left_inverse (hF.continuousAt_invFunOn_twistEndpointMap hp) hQ ?_
    filter_upwards [hF.isOpen_image_twistEndpointMap.mem_nhds (mem_image_of_mem _ hp)] with q hq
    exact invFunOn_eq (by simpa using hq)
  have hS' : HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) -
      g p • ContinuousLinearMap.fst ℝ ℝ ℝ) (R (twistEndpointMap F p)) := by
    rw [hRp]
    exact hS p hp
  rw [twistGeneratingFunction_def]
  convert hS'.comp (twistEndpointMap F p) hR using 1
  -- `dS_p ∘ L⁻¹ = g(F p) dX − g(p) dx`, since `dS_p = (g(F p) dX − g(p) dx) ∘ L`.
  rw [ContinuousLinearMap.ext_iff]
  intro v
  obtain ⟨u, rfl⟩ := L.surjective v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [← ContinuousLinearEquiv.coe_coe L, coe_fstProdEquiv]
  simp

/-- **The generating function is invariant under the diagonal deck translation**
`(x, X) ↦ (x + ℓ, X + ℓ)` on `D`, when the primitive `S` is `ℓ`-periodic in `x`. -/
theorem twistGeneratingFunction_add_period (hF : IsMonotoneTwistMap ℓ J F) {S : ℝ × ℝ → ℝ}
    (hper : ∀ x, ∀ y ∈ J, S (x + ℓ, y) = S (x, y)) {q : ℝ × ℝ}
    (hq : q ∈ twistEndpointMap F '' (univ ×ˢ J)) :
    twistGeneratingFunction J F S (q + (ℓ, ℓ)) = twistGeneratingFunction J F S q := by
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := hq
  have hshift : twistEndpointMap F (x, y) + (ℓ, ℓ) = twistEndpointMap F (x + ℓ, y) := by
    simp [twistEndpointMap_def, hF.apply_add_period x y hp.2]
  rw [hshift, hF.twistGeneratingFunction_apply S (p := (x + ℓ, y)) ⟨mem_univ _, hp.2⟩,
    hF.twistGeneratingFunction_apply S hp, hper x y hp.2]

end IsMonotoneTwistMap

end TauCeti
