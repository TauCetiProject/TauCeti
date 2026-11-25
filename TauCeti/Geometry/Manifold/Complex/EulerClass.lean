/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.FiniteCWType
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# The Euler number of the tangent bundle of a compact Riemann surface

Let `M` be a Riemann surface, a complex manifold modelled on `𝓘(ℂ, ℂ)`. Its holomorphic tangent
bundle `TM`, with fibres `TangentSpace 𝓘(ℂ, ℂ) x`, is a complex line bundle, so it has an Euler
class `TauCeti.complexEulerClass`, that of its underlying real plane bundle with the canonical
complex orientation. With the same charts `M` is a smooth real surface, whose tangent bundle, with
fibres `TangentSpace 𝓘(ℝ, ℂ) x`, carries the orientation induced by the canonical orientation of
`M` (`TauCeti.complexManifoldOrientation`).

The two bundles are the same real oriented bundle: the identity of `ℂ` on fibres is continuous on
total spaces in both directions (`TangentBundle.restrictScalarsHomeomorph`), and it carries the
complex orientation of each fibre, that of the real basis `(1, i)`, to the canonical orientation of
`M` at that point (`TauCeti.orientationAt_reindex_complexManifoldOrientation_complex`). So the
complex Euler class of `TM` is the Euler class of the oriented real tangent bundle
(`TauCeti.complexEulerClass_tangentSpace_eq_eulerClass`). For `M` compact, evaluating on the
fundamental class `[M]` of the complex orientation and applying `e(TM)[M] = χ(M)`
(`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`) gives
`⟨e(TM), [M]⟩ = χ(M)` (`TauCeti.evalFundamentalClass_complexEulerClass_tangentSpace`), the Euler
characteristic of a finite CW model of `M`. Since `complexEulerClass` defines the first Chern class
of a complex line bundle, this is `c₁(TM)[M] = χ(M)`.

## Main results

* `TauCeti.complexEulerClass_tangentSpace_eq_eulerClass`: the complex Euler class of the tangent
  bundle of a Riemann surface is the Euler class of its oriented real tangent bundle.
* `TauCeti.evalFundamentalClass_complexEulerClass_tangentSpace`: on a compact Riemann surface,
  `⟨e(TM), [M]⟩ = χ(M)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (the Riemann–Roch formula, whose closed case uses `c₁(TΣ)[Σ] = χ(Σ)`).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector bundle) and Corollary 11.12.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]

local instance instVectorBundleRealTangentSpaceComplex :
    VectorBundle ℝ ℂ (TangentSpace 𝓘(ℂ, ℂ) : M → Type) :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

/-- **The complex Euler class of the tangent bundle of a Riemann surface is its real Euler
class.** The Euler class of the holomorphic tangent bundle of a Riemann surface `M`, as a complex
line bundle (`TauCeti.complexEulerClass`), is the Euler class of the tangent bundle of the
underlying real surface, oriented by the canonical orientation of `M`. -/
theorem complexEulerClass_tangentSpace_eq_eulerClass [IsManifold 𝓘(ℝ, ℂ) 1 M] :
    complexEulerClass ℂ (TangentSpace 𝓘(ℂ, ℂ) : M → Type) (r := 0) (finrank_self ℂ) =
      ((complexManifoldOrientation ℂ M).reindex
        (finCongr (by simp))).toVectorBundleOrientation.eulerClass
        Complex.finrank_real_complex := by
  rw [complexEulerClass_def]
  -- The identity of `ℂ` on fibres, read through the two tangent-space model identifications.
  let φ (x : M) : TangentSpace 𝓘(ℂ, ℂ) x ≃L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x :=
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) x).restrictScalars ℝ).trans
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) x).symm
  -- On total spaces `φ` is the scalar-restriction homeomorphism of tangent bundles.
  have hφ : Continuous fun v : TangentBundle 𝓘(ℂ, ℂ) M ↦
      (TotalSpace.mk' ℂ v.proj (φ v.proj v.snd) : TangentBundle 𝓘(ℝ, ℂ) M) := by
    have h : (fun v : TangentBundle 𝓘(ℂ, ℂ) M ↦
        (TotalSpace.mk' ℂ v.proj (φ v.proj v.snd) : TangentBundle 𝓘(ℝ, ℂ) M)) =
          TangentBundle.restrictScalarsHomeomorph ℝ M :=
      funext fun v ↦ (TangentBundle.restrictScalarsHomeomorph_apply ℝ M v.proj v.snd).symm
    rw [h]
    exact (TangentBundle.restrictScalarsHomeomorph ℝ M).continuous
  refine VectorBundleOrientation.eulerClass_eq_of_fiberwise _ _ _ _ (φ := φ) hφ fun x ↦ ?_
  rw [Manifold.Orientation.toVectorBundleOrientation_apply,
    orientationAt_reindex_complexManifoldOrientation_complex,
    VectorBundleOrientation.reindex_apply, VectorBundleOrientation.complex_apply,
    Orientation.reindex_finCongr_reindex_finCongr, Orientation.map_reindex]
  -- `φ x` is the identity of `ℂ`, which is complex linear once the real tangent space is given
  -- the complex structure of `ℂ`.
  let : Module ℂ (TangentSpace 𝓘(ℝ, ℂ) x) := inferInstanceAs (Module ℂ ℂ)
  have : IsScalarTower ℝ ℂ (TangentSpace 𝓘(ℝ, ℂ) x) := inferInstanceAs (IsScalarTower ℝ ℂ ℂ)
  have : FiniteDimensional ℂ (TangentSpace 𝓘(ℝ, ℂ) x) := inferInstanceAs (FiniteDimensional ℂ ℂ)
  let ψ : TangentSpace 𝓘(ℂ, ℂ) x ≃ₗ[ℂ] TangentSpace 𝓘(ℝ, ℂ) x := LinearEquiv.refl ℂ ℂ
  have hψ : (φ x).toLinearEquiv = ψ.restrictScalars ℝ := LinearEquiv.ext fun _ ↦ rfl
  rw [hψ, LinearEquiv.map_complexOrientation, Orientation.reindex_finCongr_reindex_finCongr]
  exact reindex_complexOrientation_complex

variable [T2Space M] [CompactSpace M]

/-- **The Euler number of the tangent bundle of a compact Riemann surface is its Euler
characteristic.** For a compact Riemann surface `M`, the Euler class of its holomorphic tangent
bundle (`TauCeti.complexEulerClass`, which defines `c₁(TM)`), evaluated on the fundamental class
of the canonical orientation, is the Euler characteristic of `M`: `c₁(TM)[M] = χ(M)`. -/
theorem evalFundamentalClass_complexEulerClass_tangentSpace :
    ((complexHomologicalOrientation M).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
        (complexEulerClass ℂ (TangentSpace 𝓘(ℂ, ℂ) : M → Type) (r := 0)
          (finrank_self ℂ))).down = eulerChar M := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := by
    have h := 𝓘(ℂ, ℂ).isManifold_restrictScalars ℝ
      ((inferInstance : IsManifold 𝓘(ℂ, ℂ) 1 M).of_ne_zero ∞ one_ne_zero)
    rwa [modelWithCornersSelf_restrictScalars] at h
  rw [complexEulerClass_tangentSpace_eq_eulerClass, complexHomologicalOrientation_def]
  exact Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar
    Complex.finrank_real_complex
    ((complexManifoldOrientation ℂ M).reindex (finCongr (by simp)))

end TauCeti
