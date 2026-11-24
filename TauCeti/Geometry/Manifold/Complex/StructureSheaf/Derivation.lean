/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import Mathlib.RingTheory.Derivation.Basic
import TauCeti.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivatives of holomorphic germs along a holomorphic vector field

On a complex normed space `V`, a vector field `ξ : V → V` analytic at `p` differentiates
holomorphic germs at `p`: the germ of `f` goes to the germ of `z ↦ f'(z) (ξ z)`. This is a
derivation of the holomorphic stalk at `p`
(`TauCeti.holomorphicStructureSheaf.stalkDerivative`), computed on any function representative
(`TauCeti.holomorphicStructureSheaf.toFilterGerm_stalkDerivative`).

Composed with the quotient map by an ideal, such a derivation descends to the quotient once the
composite kills that ideal (`Derivation.liftQuotient`, in `TauCeti.RingTheory.Derivation.Quotient`).
This is how derivations of the local rings of analytic hypersurfaces are produced from vector
fields tangent to them.
-/

public noncomputable section

open Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {p : V} {ξ : V → V}

/-- A holomorphic germ whose representatives are the derivatives along `ξ` of the
representatives of a given germ. -/
private theorem exists_toFilterGerm_eq_fderiv (hξ : AnalyticAt ℂ ξ p)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) :
    ∃ t : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p, ∀ f : V → ℂ,
      toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl s = f →
        toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl t = (fun z ↦ fderiv ℂ f z (ξ z) : V → ℂ) := by
  obtain ⟨f₀, hf₀, hs⟩ := exists_analyticAt_toFilterGerm_eq p s
  obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_analyticAt (hf₀.fderiv_apply hξ)
  refine ⟨t, fun f hf ↦ ?_⟩
  have hff₀ : f =ᶠ[𝓝 p] f₀ := Germ.coe_eq.1 (hf.symm.trans (hs _ le_rfl))
  rw [ht _ le_rfl, Germ.coe_eq]
  filter_upwards [hff₀.eventuallyEq_nhds] with z hz
  rw [hz.fderiv_eq]

/-- A function representing a holomorphic germ is differentiable near the point. -/
private theorem eventually_differentiableAt_of_toFilterGerm_eq
    {s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p} {f : V → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl s = f) :
    ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z := by
  obtain ⟨f₀, hf₀, hs₀⟩ := exists_analyticAt_toFilterGerm_eq p s
  have hff₀ : f =ᶠ[𝓝 p] f₀ := Germ.coe_eq.1 (hs.symm.trans (hs₀ _ le_rfl))
  filter_upwards [hff₀.eventuallyEq_nhds, hf₀.eventually_analyticAt] with z hz hz₀
  exact hz₀.differentiableAt.congr_of_eventuallyEq hz

/-- The derivative along `ξ` of a holomorphic germ, as a bare function of the germ. -/
private def stalkDerivativeFun (hξ : AnalyticAt ℂ ξ p)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) :
    (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p :=
  (exists_toFilterGerm_eq_fderiv hξ s).choose

private theorem toFilterGerm_stalkDerivativeFun (hξ : AnalyticAt ℂ ξ p)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p} {f : V → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl (stalkDerivativeFun hξ s) =
      (fun z ↦ fderiv ℂ f z (ξ z) : V → ℂ) :=
  (exists_toFilterGerm_eq_fderiv hξ s).choose_spec f hs

/-- Every holomorphic germ has a representative, differentiable near `p`, whose derivative along `ξ`
represents the derivative of the germ. -/
private theorem exists_toFilterGerm_stalkDerivativeFun (hξ : AnalyticAt ℂ ξ p)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) :
    ∃ f : V → ℂ, toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl s = f ∧
      toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl (stalkDerivativeFun hξ s) =
        (fun z ↦ fderiv ℂ f z (ξ z) : V → ℂ) ∧
      ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z := by
  obtain ⟨f, -, hf⟩ := exists_analyticAt_toFilterGerm_eq p s
  exact ⟨f, hf _ le_rfl, toFilterGerm_stalkDerivativeFun hξ (hf _ le_rfl),
    eventually_differentiableAt_of_toFilterGerm_eq (hf _ le_rfl)⟩

variable (ξ) in
/-- The derivative of holomorphic germs at `p` along a vector field `ξ` analytic at `p`: the germ
of `f` goes to the germ of `z ↦ f'(z) (ξ z)`. -/
def stalkDerivative (hξ : AnalyticAt ℂ ξ p) :
    Derivation ℤ ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p)
      ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) :=
  Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      (M₂ := (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p)
      { toFun := stalkDerivativeFun hξ
        map_zero' := by
          apply toFilterGerm_nhds_injective p
          rw [toFilterGerm_stalkDerivativeFun hξ (f := (0 : V → ℂ)) (by simp), map_zero]
          simp [← Germ.coe_zero, Pi.zero_def]
        map_add' := fun s t ↦ by
          obtain ⟨f, hf, hf', hfd⟩ := exists_toFilterGerm_stalkDerivativeFun hξ s
          obtain ⟨g, hg, hg', hgd⟩ := exists_toFilterGerm_stalkDerivativeFun hξ t
          apply toFilterGerm_nhds_injective p
          rw [map_add, toFilterGerm_stalkDerivativeFun hξ (f := f + g)
              (by rw [map_add, hf, hg, Germ.coe_add]), hf', hg', ← Germ.coe_add, Germ.coe_eq]
          filter_upwards [hfd, hgd] with z hfz hgz
          simp [fderiv_add hfz hgz] })
    fun s t ↦ by
      obtain ⟨f, hf, hf', hfd⟩ := exists_toFilterGerm_stalkDerivativeFun hξ s
      obtain ⟨g, hg, hg', hgd⟩ := exists_toFilterGerm_stalkDerivativeFun hξ t
      apply toFilterGerm_nhds_injective p
      simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        smul_eq_mul, map_add, map_mul]
      rw [toFilterGerm_stalkDerivativeFun hξ (f := f * g) (by rw [map_mul, hf, hg, Germ.coe_mul]),
        hf', hg', hf, hg, ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add, Germ.coe_eq]
      filter_upwards [hfd, hgd] with z hfz hgz
      simp [fderiv_mul hfz hgz]

/-- The derivative of a germ along `ξ` is represented by the derivative along `ξ` of any of its
function representatives. -/
theorem toFilterGerm_stalkDerivative (hξ : AnalyticAt ℂ ξ p)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p} {f : V → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl (stalkDerivative ξ hξ s) =
      (fun z ↦ fderiv ℂ f z (ξ z) : V → ℂ) :=
  toFilterGerm_stalkDerivativeFun hξ hs

end TauCeti.holomorphicStructureSheaf
