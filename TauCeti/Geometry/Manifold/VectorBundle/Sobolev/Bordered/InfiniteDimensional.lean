/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The identity of `W^{k,p}(V)` over a surface with boundary is not compact

Let `M` be a `Cᵏ` manifold modelled on the closed upper half-plane and `V → M` a `Cᵏ` vector bundle
with finite-dimensional fibre. The bordered Sobolev space `W^{k,p}(V)` of
`TauCeti.BorderedSobolevSection A p k` contains the `Cᵏ` sections
(`TauCeti.BorderedSobolevSection.ofContMDiffSection_injective`), so it is infinite-dimensional as
soon as the `Cᵏ` sections are, and then its identity is not a compact operator, by Riesz's theorem
(`TauCeti.BorderedSobolevSection.not_isCompactOperator_id`).

On the closed unit disc `Complex.UnitClosedDisc` with the trivial bundle of a nonzero fibre, the
sections `z ↦ P(re z) v` for real polynomials `P` and a nonzero vector `v` are linearly independent,
so the `Cᵏ` sections are infinite-dimensional
(`TauCeti.BorderedSobolevSection.not_finiteDimensional_contMDiffSection_unitClosedDisc`). Hence
`W^{k,p} → W^{k,p}` is not compact on the closed disc, for every finite bundle atlas and every
order `k` (`TauCeti.BorderedSobolevSection.not_isCompactOperator_id_unitClosedDisc`); this is the
negative half of the roadmap's Rellich check, where `W^{k+1,p} → W^{k,p}` is compact.

## Main results

* `TauCeti.BorderedSobolevSection.not_isCompactOperator_id`: the identity of `W^{k,p}(V)` is not
  compact when the `Cᵏ` sections are infinite-dimensional.
* `TauCeti.BorderedSobolevSection.not_isCompactOperator_id_unitClosedDisc`: the case of the closed
  disc.
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ENNReal ContDiff Complex.UnitDisc

namespace TauCeti

namespace BorderedSobolevSection

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} [IsManifold closedUpperHalfPlaneModel k M]
  [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel]

/-- **The identity is not compact.** If the `Cᵏ` sections of `V` form an infinite-dimensional
space, the identity of `W^{k,p}(V)` is not a compact operator. -/
theorem not_isCompactOperator_id (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)
    (h : ¬ FiniteDimensional ℝ Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    ¬ IsCompactOperator (id : BorderedSobolevSection A p k → BorderedSobolevSection A p k) :=
  fun hc ↦ h <|
    have : FiniteDimensional ℝ (BorderedSobolevSection A p k) :=
      FiniteDimensional.of_isCompactOperator_id hc
    FiniteDimensional.of_injective (ofContMDiffSection A p k) (ofContMDiffSection_injective A p k)

end General

section Disc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The section `z ↦ P(re z) v` of the trivial bundle over the closed disc, for a real polynomial
`P`. -/
private def polySection (k : ℕ) (v : F) (P : Polynomial ℝ) :
    Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ :=
  ⟨fun z ↦ P.eval (z : ℂ).re • v, fun x ↦ (contMDiffAt_section_iff x).2 (by
    have hre : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, ℝ) k fun z : 𝕔𝔻 ↦ (z : ℂ).re :=
      Complex.reCLM.contDiff.contMDiff.comp Complex.UnitClosedDisc.contMDiff_coe
    have hP : ContDiff ℝ k fun t : ℝ ↦ P.eval t := by
      simpa using Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) P k
    exact (hP.contMDiff.comp hre).smul contMDiff_const x)⟩

private theorem polySection_apply (k : ℕ) (v : F) (P : Polynomial ℝ) (z : 𝕔𝔻) :
    polySection k v P z = P.eval (z : ℂ).re • v :=
  rfl

/-- **The `Cᵏ` sections over the closed disc are infinite-dimensional.** For a nonzero fibre `F`,
the sections `z ↦ P(re z) v` for real polynomials `P` and a fixed `v ≠ 0` are linearly
independent. -/
theorem not_finiteDimensional_contMDiffSection_unitClosedDisc [Nontrivial F] (k : ℕ) :
    ¬ FiniteDimensional ℝ Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let L : Polynomial ℝ →ₗ[ℝ] Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ :=
    { toFun := polySection k v
      map_add' := fun P Q ↦ ContMDiffSection.ext fun z ↦ by
        simp [polySection_apply, add_smul]
      map_smul' := fun c P ↦ ContMDiffSection.ext fun z ↦ by
        simp [polySection_apply, smul_smul] }
  intro hfin
  refine Polynomial.not_finite (R := ℝ) (FiniteDimensional.of_injective L fun P Q hPQ ↦ ?_)
  -- A polynomial vanishing on `[-1, 1]` is zero.
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_infinite_isRoot _ ((Set.Icc_infinite (by norm_num :
    (-1 : ℝ) < 1)).mono fun t ht ↦ ?_)
  have ht' : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ht
  have h := congrArg (fun s : Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ ↦
    s (Complex.UnitClosedDisc.mk t ht')) hPQ
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, polySection_apply, Complex.UnitClosedDisc.coe_mk,
    Complex.ofReal_re] at h
  simpa [Polynomial.IsRoot, sub_eq_zero, smul_left_injective ℝ hv |>.eq_iff] using h

/-- **`W^{k,p} → W^{k,p}` is not compact on the closed disc.** For the trivial bundle over the
closed unit disc with a nonzero finite-dimensional fibre, every finite bundle atlas, every order `k`
and `1 ≤ p ≤ ∞`, the identity of the Sobolev space of sections is not a compact operator. -/
theorem not_isCompactOperator_id_unitClosedDisc [Nontrivial F] [FiniteDimensional ℝ F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}
    (A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F)) :
    ¬ IsCompactOperator (id : BorderedSobolevSection A p k → BorderedSobolevSection A p k) :=
  not_isCompactOperator_id A (not_finiteDimensional_contMDiffSection_unitClosedDisc k)

end Disc

end BorderedSobolevSection

end TauCeti
