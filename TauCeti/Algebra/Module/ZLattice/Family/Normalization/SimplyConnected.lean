/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Normalization.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.AffineAction

/-!
# Normalizing torus-valued cyclic translations

A cyclic affine action with trivial linear part on a varying torus family over a simply
connected base admits a vector lift of its translation section. The action law forces the
orbit sum of this lift to be one constant lattice vector. Thus neither a vector lift nor its
orbit-sum equation has to be supplied as extra input to cyclic normalization.

For an invariant period family, the centered cyclic correction gives a differentiable gauge
conjugating the generator to translation by the period divided by the cyclic period. Over
`ℂ`, holomorphic data give a biholomorphic gauge. At a fixed base point the original translation
section is already this normalized translation; it records the lattice vector modulo `mΛ`.
The lift-independence comparisons are in
`TauCeti.Algebra.Module.ZLattice.Family.Normalization.Basic`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Chapter V, section on logarithmic transformations.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
  {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace 𝕜 E] {Γ : Type*} [Monoid Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (ρ : Representation ℤ Γ Λ)
  (hPeq : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbmul : ∀ (g h : Γ) (y : Y),
    b (g * h) y = torusFamilyAffineMap R P ρ hPeq b hb g (b h y))
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)
  {g : Γ} (hR : ∀ y v, R g y v = v)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))

include hbmul hinj hP hR hbc

/-- A differentiable torus-valued cyclic translation over a simply connected base has a
differentiable vector lift whose orbit sum is a single period. The lattice vector is derived
from the cocycle law, not assumed. No exact-order hypothesis is required. -/
theorem exists_contMDiff_lift_and_birkhoffSum_eq_period {m : ℕ} (hg : g ^ m = 1) :
    ∃ β : Y → E, ContMDiff I 𝓘(𝕜, E) n β ∧
      (∀ y, b g y = Quotient.mk _ (g • y, β y)) ∧
      ∃ l : Λ, ∀ y, birkhoffSum (g • ·) β m y = P y l := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  obtain ⟨β, hβ, hβeq⟩ := exists_contMDiff_lift_torusFamily P hinj hP hbc
  have hβb : ∀ y, b g y = Quotient.mk _ (g • y, β y) := by
    intro y
    simpa only [hb] using (hβeq y).symm
  have hr : Continuous (fun y : Y ↦ g • y) := by
    simpa only [Function.comp_def, hb] using
      (continuous_torusFamilyProjection P).comp hbc.continuous
  refine ⟨β, hβ, hβb, exists_eq_period_of_mem_range P
    (fun l ↦ (hP l).continuous) hinj continuous_id
    (continuous_finsetSum _ fun j _ ↦ hβ.continuous.comp (hr.iterate j)) ?_⟩
  exact birkhoffSum_translation_mem_range_of_pow_eq_one R P ρ hPeq b hb hbmul hR hβb hg

/-- A torus-valued cyclic translation over a simply connected base is conjugate to translation
by a period divided by `m`. The conjugating gauge is the correction of the centered lift,
so the existing change-of-lift theorem applies to this very gauge. In particular, holomorphic
data give a biholomorphic normalization without replacing the varying period family by a
constant torus. The hypotheses assert period dividing `m`, not exact order. -/
theorem exists_torusFamilyGaugeDiffeomorph_normalization_of_simplyConnected
    {m : ℕ} (hg : g ^ m = 1) (hm : (m : 𝕜) ≠ 0)
    (hPinv : ∀ y, P (g • y) = P y) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ∃ β : Y → E, ContMDiff I 𝓘(𝕜, E) n β ∧ ∃ l : Λ,
      (∀ y, b g y = Quotient.mk _ (g • y, β y)) ∧
      (∀ y, birkhoffSum (g • ·) β m y = P y l) ∧
      (∀ y, g • y = y → b g y = Quotient.mk _ (y, (m : 𝕜)⁻¹ • P y l)) ∧
      ∃ hc : ContMDiff I 𝓘(𝕜, E) n
          (cyclicCorrection 𝕜 (g • ·) (fun y ↦ β y - (m : 𝕜)⁻¹ • P y l) m),
        ∀ y v,
          let G := torusFamilyGaugeDiffeomorph P hinj hP _ hc
          G (torusFamilyAffineMap R P ρ hPeq b hb g
            (G.symm (Quotient.mk _ (y, v)))) =
              Quotient.mk _ (g • y, v + (m : 𝕜)⁻¹ • P y l) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  obtain ⟨β, hβ, hβb, l, hsum⟩ := exists_contMDiff_lift_and_birkhoffSum_eq_period
    R P ρ hPeq b hb hbmul hinj hP hR hbc hg
  have hr : ContMDiff I I n (fun y : Y ↦ g • y) := by
    simpa only [Function.comp_def, hb] using
      (contMDiff_torusFamilyProjection P hinj hP).comp hbc
  have hcenter : ContMDiff I 𝓘(𝕜, E) n (fun y ↦ β y - (m : 𝕜)⁻¹ • P y l) :=
    hβ.sub ((contMDiff_const (I' := 𝓘(𝕜))).smul (hP l))
  have hc := contMDiff_cyclicCorrection hr hcenter m
  have hfixed : ∀ y, g • y = y → b g y = Quotient.mk _ (y, (m : 𝕜)⁻¹ • P y l) := by
    intro y hy
    have hnorm := hsum y
    rw [Function.IsFixedPt.birkhoffSum_eq hy, ← Nat.cast_smul_eq_nsmul 𝕜] at hnorm
    have hβy : β y = (m : 𝕜)⁻¹ • P y l := by
      rw [← hnorm, inv_smul_smul₀ hm]
    rw [hβb, hy, hβy]
  refine ⟨β, hβ, l, hβb, hsum, hfixed, hc, fun y v ↦ ?_⟩
  have hperiod : (g • ·)^[m] = (id : Y → Y) := by
    funext y
    simp [smul_iterate, hg]
  have hF : ∀ y v, torusFamilyAffineMap R P ρ hPeq b hb g
      (Quotient.mk _ (y, v)) = Quotient.mk _ (g • y, v + β y) := by
    intro y v
    rw [torusFamilyAffineMap_mk_of_eq R P ρ hPeq b hb (hβb y), hR]
  simpa only [← Diffeomorph.coe_toEquiv, Diffeomorph.symm_toEquiv,
    torusFamilyGaugeDiffeomorph_toEquiv] using
    torusFamilyGauge_cyclicCorrection_centered_conj_mk P (g • ·) hPinv β l
      hperiod hm hsum (torusFamilyAffineMap R P ρ hPeq b hb g) hF y v

end TauCeti
