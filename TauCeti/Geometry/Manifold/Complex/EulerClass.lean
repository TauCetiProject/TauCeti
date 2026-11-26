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
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# The Euler class of the tangent bundle of a complex manifold

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, with `E` of complex dimension `r + 1`. Its
holomorphic tangent bundle `TM`, with fibres `TangentSpace 𝓘(ℂ, E) x`, is a complex vector
bundle, so it has an Euler class `TauCeti.complexEulerClass`, that of its underlying real bundle
with the canonical complex orientation. With the same charts `M` is a real manifold, whose tangent
bundle, with fibres `TangentSpace 𝓘(ℝ, E) x`, carries the orientation induced by the canonical
orientation of `M` (`TauCeti.complexManifoldOrientation`).

The two bundles are the same real oriented bundle: the identity of `E` on fibres is continuous on
total spaces in both directions (`TangentBundle.restrictScalarsHomeomorph`), and it carries the
complex orientation of each fibre to the canonical orientation of `M` at that point, which in the
preferred chart is the complex orientation of `E`
(`TauCeti.orientationAt_complexManifoldOrientation_eq_complexOrientation`). So the complex Euler
class of `TM` is the Euler class of the oriented real tangent bundle
(`TauCeti.complexEulerClass_tangentSpace_eq_eulerClass`).

For a compact Riemann surface `M`, evaluating on the fundamental class `[M]` of the complex
orientation and applying `e(TM)[M] = χ(M)`
(`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`) gives
`⟨e(TM), [M]⟩ = χ(M)`
(`TauCeti.evalFundamentalClass_complexEulerClass_tangentSpace_eq_eulerChar`), the Euler
characteristic of a finite CW model of `M`. Since `complexEulerClass` defines the first Chern class
of a complex line bundle, this is `c₁(TM)[M] = χ(M)`.

## Main results

* `TauCeti.complexEulerClass_tangentSpace_eq_eulerClass`: the complex Euler class of the tangent
  bundle of a complex manifold is the Euler class of its oriented real tangent bundle.
* `TauCeti.evalFundamentalClass_complexEulerClass_tangentSpace_eq_eulerChar`: on a compact Riemann
  surface, `⟨e(TM), [M]⟩ = χ(M)`.

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

universe w

namespace TauCeti

section General

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]

local instance instVectorBundleRealTangentSpaceComplex :
    VectorBundle ℝ E (TangentSpace 𝓘(ℂ, E) : M → Type w) :=
  VectorBundle.restrictScalars ℝ ℂ E _

/-- **The complex Euler class of the tangent bundle of a complex manifold is its real Euler
class.** The Euler class of the holomorphic tangent bundle of a complex manifold `M` modelled on
`𝓘(ℂ, E)`, of complex dimension `r + 1`, as a complex vector bundle (`TauCeti.complexEulerClass`),
is the Euler class of the tangent bundle of the underlying real manifold, oriented by the
canonical orientation of `M`. -/
theorem complexEulerClass_tangentSpace_eq_eulerClass [IsManifold 𝓘(ℝ, E) 1 M] {r : ℕ}
    (hE : finrank ℂ E = r + 1) :
    complexEulerClass E (TangentSpace 𝓘(ℂ, E) : M → Type w) hE =
      ((complexManifoldOrientation E M).reindex
        (finCongr (by rw [hE]; omega))).toVectorBundleOrientation.eulerClass
        (by rw [finrank_real_eq_two_mul_finrank_complex, hE]; ring) := by
  rw [complexEulerClass_def]
  -- The identity of `E` on fibres, read through the two tangent-space model identifications.
  let φ (x : M) : TangentSpace 𝓘(ℂ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
    ((tangentSpaceCastModel 𝓘(ℂ, E) x).restrictScalars ℝ).trans
      (tangentSpaceCastModel 𝓘(ℝ, E) x).symm
  -- On total spaces `φ` is the scalar-restriction homeomorphism of tangent bundles.
  have hφ : Continuous fun v : TangentBundle 𝓘(ℂ, E) M ↦
      (TotalSpace.mk' E v.proj (φ v.proj v.snd) : TangentBundle 𝓘(ℝ, E) M) := by
    have h : (fun v : TangentBundle 𝓘(ℂ, E) M ↦
        (TotalSpace.mk' E v.proj (φ v.proj v.snd) : TangentBundle 𝓘(ℝ, E) M)) =
          TangentBundle.restrictScalarsHomeomorph ℝ M :=
      funext fun v ↦ (TangentBundle.restrictScalarsHomeomorph_apply ℝ M v.proj v.snd).symm
    rw [h]
    exact (TangentBundle.restrictScalarsHomeomorph ℝ M).continuous
  refine VectorBundleOrientation.eulerClass_eq_of_fiberwise _ _ _ _ (φ := φ) hφ fun x ↦ ?_
  rw [Manifold.Orientation.toVectorBundleOrientation_apply,
    Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation,
    VectorBundleOrientation.reindex_apply, VectorBundleOrientation.complex_apply,
    Orientation.reindex_finCongr_reindex_finCongr, Orientation.map_reindex]
  -- `φ x` is the identity of `E`, which is complex linear once the real tangent space is given
  -- the complex structure of `E`.
  let : Module ℂ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (Module ℂ E)
  have : IsScalarTower ℝ ℂ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (IsScalarTower ℝ ℂ E)
  have : FiniteDimensional ℂ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (FiniteDimensional ℂ E)
  let ψ : TangentSpace 𝓘(ℂ, E) x ≃ₗ[ℂ] TangentSpace 𝓘(ℝ, E) x := LinearEquiv.refl ℂ E
  have hψ : (φ x).toLinearEquiv = ψ.restrictScalars ℝ := LinearEquiv.ext fun _ ↦ rfl
  rw [hψ, LinearEquiv.map_complexOrientation, Orientation.reindex_finCongr_reindex_finCongr]
  -- Both sides reindex the canonical orientation of `E`, seen on the tangent space `T_x M = E`.
  rfl

end General

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]

variable [T2Space M] [CompactSpace M]

/-- **The Euler number of the tangent bundle of a compact Riemann surface is its Euler
characteristic.** For a compact Riemann surface `M`, the Euler class of its holomorphic tangent
bundle (`TauCeti.complexEulerClass`, which defines `c₁(TM)`), evaluated on the fundamental class
of the canonical orientation, is the Euler characteristic of `M`: `c₁(TM)[M] = χ(M)`. -/
theorem evalFundamentalClass_complexEulerClass_tangentSpace_eq_eulerChar :
    ((complexHomologicalOrientation M).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
        (complexEulerClass ℂ (TangentSpace 𝓘(ℂ, ℂ) : M → Type) (r := 0)
          (finrank_self ℂ))).down = eulerChar M := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  rw [complexEulerClass_tangentSpace_eq_eulerClass, complexHomologicalOrientation_def]
  exact Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar
    Complex.finrank_real_complex
    ((complexManifoldOrientation ℂ M).reindex (finCongr (by simp)))

end TauCeti
