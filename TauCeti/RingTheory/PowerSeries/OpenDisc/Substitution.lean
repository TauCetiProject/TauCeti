/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.AnalyticSubst
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Topology

/-!
# Analytic substitution on open discs

Suppose `g` is a series on the open disc of radius `S`, and its Gauss norm at every smaller
positive radius is strictly less than `R₀`. Substitution by `g` takes series on the open disc
of radius `R₀` to series on the open disc of radius `S`. It is a continuous ring homomorphism
for the topologies of all smaller-radius Gauss norms. Nonzero constant terms of `g` are allowed.

The radius bound is uniform on each smaller closed disc, rather than merely a pointwise bound
on values at coefficient-ring-valued points. This distinction is essential over finite residue
fields. The substitution uses the radius-independent coefficient sums of
`PowerSeries.analyticSubst`, not formal substitution, which has stronger constant-term hypotheses.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S : ℝ} {g f : R⟦X⟧}

/-- Substitution maps the open disc of radius `S` into the open disc of radius `R₀` when the
inner series has Gauss norm less than `R₀` on every smaller positive closed disc. -/
theorem OnOpenDisc.analyticSubst (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀) :
    (PowerSeries.analyticSubst g f).OnOpenDisc S := by
  apply onOpenDisc_iff.mpr
  intro s hs hsS
  let : Fact (0 < s) := ⟨hs⟩
  obtain ⟨r, hgr', hrR⟩ := exists_between (hgr s hs hsS)
  have hr : 0 < r := (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr'
  exact (onOpenDisc_iff.mp hf r hr hrR).analyticSubst
    (onOpenDisc_iff.mp hg s hs hsS) hgr'.le

/-- Analytic substitution between open-disc series algebras. The inner series may have a
nonzero constant coefficient; its smaller-radius Gauss norms must be strictly below `R₀`. -/
noncomputable def OnOpenDisc.analyticSubstHom (hS : 0 < S) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S := by
  let s := S / 2
  have hs : 0 < s := half_pos hS
  have hsS : s < S := half_lt_self hS
  letI : Fact (0 < s) := ⟨hs⟩
  let r := (g.gaussNorm norm s + R₀) / 2
  have hgr' : g.gaussNorm norm s < r := by
    dsimp [r]
    linarith [hgr s hs hsS]
  have hrR : r < R₀ := by
    dsimp [r]
    linarith [hgr s hs hsS]
  have hr : 0 < r := (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr'
  exact
    { toFun f := ⟨PowerSeries.analyticSubst g f,
        OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).analyticSubst hg hgr)⟩
      map_one' := Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' f h := Subtype.ext <|
        (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp f.2) r hr hrR).analyticSubst_add
          (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp h.2) r hr hrR)
          (onOpenDisc_iff.mp hg s hs hsS) hgr'.le
      map_mul' f h := Subtype.ext <|
        (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp f.2) r hr hrR).analyticSubst_mul
          (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp h.2) r hr hrR)
          (onOpenDisc_iff.mp hg s hs hsS) hgr'.le }

/-- The substitution homomorphism is given by the analytic coefficient sums. -/
@[simp]
theorem OnOpenDisc.coe_analyticSubstHom (hS : 0 < S) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀)
    (f : OnOpenDisc.subring R R₀) :
    (OnOpenDisc.analyticSubstHom hS hg hgr f : R⟦X⟧) = PowerSeries.analyticSubst g f := by
  unfold OnOpenDisc.analyticSubstHom
  rfl

/-- Substitution fixes constants. -/
@[simp]
theorem OnOpenDisc.analyticSubstHom_C (hS : 0 < S) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀) (a : R) :
    OnOpenDisc.analyticSubstHom hS hg hgr ⟨C a, OnOpenDisc.mem_subring.mpr (onOpenDisc_C a)⟩ =
      ⟨C a, OnOpenDisc.mem_subring.mpr (onOpenDisc_C a)⟩ := by
  apply Subtype.ext
  simp

/-- Substitution sends the variable to the inner series. -/
@[simp]
theorem OnOpenDisc.analyticSubstHom_X (hS : 0 < S) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀) :
    OnOpenDisc.analyticSubstHom hS hg hgr ⟨X, OnOpenDisc.mem_subring.mpr onOpenDisc_X⟩ =
      ⟨g, OnOpenDisc.mem_subring.mpr hg⟩ := by
  apply Subtype.ext
  simp

end PowerSeries

namespace TauCeti.PowerSeries.OnOpenDisc

open _root_.PowerSeries Filter
open scoped Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S : ℝ} {g : R⟦X⟧}

attribute [local instance] radius_pos

/-- Analytic substitution is continuous for the topology of all smaller-radius Gauss norms. -/
theorem continuous_analyticSubstHom (hS : 0 < S) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀) :
    Continuous (OnOpenDisc.analyticSubstHom hS hg hgr) := by
  apply continuous_iff.mpr
  intro s
  obtain ⟨r, hgr', hrR⟩ := exists_between (hgr s s.2.1 s.2.2)
  have hr : 0 < r := (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr'
  let r' : Set.Ioo (0 : ℝ) R₀ := ⟨r, hr, hrR⟩
  let : Fact (0 < r) := ⟨hr⟩
  let Φ := (restrict (R := R) s).comp (OnOpenDisc.analyticSubstHom hS hg hgr)
  apply continuous_of_continuousAt_zero Φ
  rw [ContinuousAt, map_zero]
  have H : Tendsto (restrict (R := R) r') (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (uniformContinuous_restrict (R := R) r').continuous.tendsto 0
  refine squeeze_zero_norm (a := fun f ↦ ‖restrict r' f‖) (fun f ↦ ?_) ?_
  · simp only [Φ, RingHom.coe_comp, Function.comp_apply, norm_eq_gaussNorm, coe_restrict,
      OnOpenDisc.coe_analyticSubstHom]
    exact (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp f.2) r hr hrR).gaussNorm_analyticSubst_le
      (onOpenDisc_iff.mp hg s s.2.1 s.2.2) hgr'.le
  · simpa using H.norm

/-- A continuous ring homomorphism fixing constants and sending `X` to `g` is analytic
substitution by `g`. -/
theorem eq_analyticSubstHom (hS : 0 < S) (hg : g.OnOpenDisc S)
    (hgr : ∀ s, 0 < s → s < S → g.gaussNorm norm s < R₀)
    (ψ : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S) (hψ : Continuous ψ)
    (hC : ∀ a, ψ ⟨C a, OnOpenDisc.mem_subring.mpr (onOpenDisc_C a)⟩ =
      ⟨C a, OnOpenDisc.mem_subring.mpr (onOpenDisc_C a)⟩)
    (hX : ψ ⟨X, OnOpenDisc.mem_subring.mpr onOpenDisc_X⟩ =
      ⟨g, OnOpenDisc.mem_subring.mpr hg⟩) :
    ψ = OnOpenDisc.analyticSubstHom hS hg hgr := by
  let : Fact (0 < S) := ⟨hS⟩
  have H : ψ.comp OnOpenDisc.polynomialHom =
      (OnOpenDisc.analyticSubstHom hS hg hgr).comp OnOpenDisc.polynomialHom := by
    apply Polynomial.ringHom_ext
    · intro a
      have hCa : OnOpenDisc.polynomialHom (R₀ := R₀) (Polynomial.C a) =
          ⟨C a, OnOpenDisc.mem_subring.mpr (onOpenDisc_C a)⟩ := Subtype.ext (by simp)
      simp only [RingHom.comp_apply, hCa, hC, OnOpenDisc.analyticSubstHom_C]
    · have hXa : OnOpenDisc.polynomialHom (R := R) (R₀ := R₀) Polynomial.X =
          ⟨X, OnOpenDisc.mem_subring.mpr onOpenDisc_X⟩ := Subtype.ext (by simp)
      simp only [RingHom.comp_apply, hXa, hX, OnOpenDisc.analyticSubstHom_X]
  apply DFunLike.coe_injective
  exact denseRange_polynomialHom.equalizer hψ (continuous_analyticSubstHom hS hg hgr)
    (congrArg DFunLike.coe H)

end TauCeti.PowerSeries.OnOpenDisc
