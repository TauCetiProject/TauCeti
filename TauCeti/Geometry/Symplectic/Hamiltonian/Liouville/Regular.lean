/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable
public import TauCeti.Geometry.Symplectic.Lagrangian.Fibration
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.Connected.Basic

/-!
# The regular part of an integrable system is a Lagrangian torus fibration

Let `F : M → ℝⁿ` be a completely integrable system on a `2n`-dimensional manifold with a
nondegenerate two-form `σ` (`TauCeti.SmoothTwoForm.IsIntegrableSystem`), and let `U ⊆ ℝⁿ` be an
open set of regular values of `F` over which the fibres of `F` are connected and `F` is proper.
Then `F`, restricted to the open set `F⁻¹(U)` and corestricted to `U`, is a regular Lagrangian
torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
for the restriction of `σ` to `F⁻¹(U)`
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangianTorusFibration_restrictPreimage`):

* it is a submersion, since every point over `U` is a regular point of `F`;
* its fibres are Lagrangian, since the integrals Poisson-commute and there are `n` of them
  (`TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangian_ker_mfderiv`);
* it is proper with connected fibres by hypothesis.

Connected fibres are nonempty, so `U` lies in the image of `F`. Only properness of `F` over `U` is
assumed, not properness of `F` on the whole of `M`.

This is how integrable systems enter the global theory of Lagrangian torus fibrations: when `σ` is
moreover closed, so symplectic, the fibres over `U` are tori
(`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`) carrying the fibrewise action of
`T*U` and its period lattice (`IsLagrangianTorusFibration.periodLattice`), whose transport around
loops in `U` is the monodromy of the system.

## Main results

* `TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangianTorusFibration_restrictPreimage`: the
  restriction of an integrable system over an open set of regular values with connected fibres,
  over which it is proper, is a regular Lagrangian torus fibration.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
-/

public section

open Function Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsIntegrableSystem

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [Fintype ι]
  {σ : SmoothTwoForm I M} {F : M → ι → ℝ}

/-- **The regular part of an integrable system is a regular Lagrangian torus fibration.** Let `F`
be an integrable system for a nondegenerate form `σ`, and let `U` be an open set of regular values
of `F` whose fibres are connected and over which `F` is proper. Then the restriction of `F` to the
open set `F⁻¹(U)`, as a map onto `U`, is a regular Lagrangian torus fibration for the restriction
of `σ` to `F⁻¹(U)`. -/
theorem isLagrangianTorusFibration_restrictPreimage (h : σ.IsIntegrableSystem F)
    (hσ : σ.IsNondegenerate) (U : Opens (ι → ℝ))
    (hreg : ∀ c ∈ U, IsRegularValue I 𝓘(ℝ, ι → ℝ) F c)
    (hconn : ∀ c ∈ U, IsConnected (F ⁻¹' {c}))
    (hprop : IsProperMap ((U : Set (ι → ℝ)).restrictPreimage F)) :
    (hσ.mpullback_subtype_val (U.comap ⟨F, h.contMDiff.continuous⟩)).IsLagrangianTorusFibration
      𝓘(ℝ, ι → ℝ) (fun x : U.comap ⟨F, h.contMDiff.continuous⟩ ↦ (⟨F x, x.property⟩ : U)) := by
  set V := U.comap ⟨F, h.contMDiff.continuous⟩
  set π : V → U := fun x ↦ ⟨F x, x.property⟩
  -- `π` is smooth, since its composite with the inclusion of `U` is.
  have hπs : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ π := fun x ↦
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff π univ x).1
      ((h.contMDiff.comp contMDiff_subtypeVal) x)
  -- The differential of `π` is that of `F`, on the common model spaces.
  have hdπ (x : V) (v : TangentSpace I x) :
      mfderiv I 𝓘(ℝ, ι → ℝ) π x v = mfderiv I 𝓘(ℝ, ι → ℝ) F x v :=
    Manifold.mfderiv_apply_of_subtype_val_comp_eq (f := π) rfl v
  have hFreg (x : V) : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x :=
    (hreg (F x) x.property).isRegularPoint rfl
  have hsurj (x : V) : Surjective (mfderiv I 𝓘(ℝ, ι → ℝ) π x) := fun w ↦ by
    obtain ⟨v, hv⟩ := isRegularPoint_iff.1 (hFreg x) w
    exact ⟨v, (hdπ x v).trans hv⟩
  refine
    { isSubmersion :=
        (hπs.isSubmersionOfComplement_of_surjective_mfderiv (by simp) hsurj).isSubmersion
      isLagrangian_ker_mfderiv := fun x ↦ ?_
      -- `π` is `Set.restrictPreimage U F`, once the subtype of `V` is identified with that of
      -- `F⁻¹(U)`, which is its carrier by definition of `Opens.comap`.
      isProperMap := hprop
      isConnected_preimage_singleton := fun c ↦ ?_ }
  · -- On `V` the restriction of `F` is an integrable system for the restricted form, regular at
    -- `x`, and its differential has the same kernel as that of `π`.
    have : Nonempty V := ⟨x⟩
    have hV := h.comp_isLocalDiffeomorph (M := V) hσ isLocalDiffeomorph_subtype_val rfl
    have hker : (mfderiv I 𝓘(ℝ, ι → ℝ) π x).ker =
        (mfderiv I 𝓘(ℝ, ι → ℝ) (F ∘ (Subtype.val : V → M)) x).ker := by
      ext v
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hdπ,
        Manifold.mfderiv_comp_subtype_val_apply]
      -- The zeros of the tangent spaces at `π x` and at `F x` are both the zero of `ι → ℝ`.
      exact Iff.rfl
    rw [hker]
    exact hV.isLagrangian_ker_mfderiv (hσ.mpullback_subtype_val V)
      ((hFreg x).comp (isRegularPoint_subtype_val x))
  · -- The inclusion of `V` carries the fibre of `π` over `c` onto the fibre of `F` over `c`.
    have himage : Subtype.val '' (π ⁻¹' {c}) = F ⁻¹' {(c : ι → ℝ)} :=
      (image_val_preimage_restrictPreimage (t := (U : Set (ι → ℝ))) (f := F) (u := {c})).trans
        (by rw [image_singleton])
    exact Topology.IsInducing.subtypeVal.isConnected_image.1 (himage ▸ hconn c c.property)

end TauCeti.SmoothTwoForm.IsIntegrableSystem
