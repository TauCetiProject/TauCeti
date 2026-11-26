/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Orientation.Viterbo
public import TauCeti.AlgebraicTopology.DGLocalSystem.TorusSign

/-!
# The degree-zero Viterbo twist

Let `M` be a topological manifold of dimension `d` and `R` a commutative ring. The Viterbo
isomorphism with DG coefficients for the cotangent bundle of `M` identifies symplectic homology
with the homology of the free loop space `𝓛M` twisted by the degree-zero rank-one local system

`η₀ = σ ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})`

(Barraud–Damian–Humilière–Oancea, §§1.5 and 4.1). Here `σ` is the sign system along which a loop of
free loops sweeping out a torus `Γ : T² → M` acts by `(-1) ^ ⟨w₂(TM), Γ_*[T²]⟩`, and the other two
factors form the orientation part `TauCeti.RankOneLocalSystem.viterboOrientationTwist`.

The sign system only sees the second Stiefel–Whitney class through its pairing with integral torus
classes. So this file takes that pairing as an arbitrary additive map `c : H₂(M; ℤ) → ℤ/2` and
defines the **Viterbo twist** of `c` as the product of the torus sign `σ_c`
(`TauCeti.RankOneLocalSystem.torusSign`) with the orientation part
(`TauCeti.RankOneLocalSystem.viterboTwist`). For `c = ⟨w₂(TM), -⟩` it is `η₀`.

The laws of the twist follow from those of its two factors.

* **Rotations.** Rotating a free loop `γ` once around itself is a loop of free loops based at `γ`
  (`TauCeti.MooreFreeLoopSpace.rotationLoop`). Its torus `(s, t) ↦ γ(s + t)` factors through the
  circle, so the torus sign is trivial along it; the orientation part is trivial along it too, and
  so is the twist (`TauCeti.RankOneLocalSystem.viterboTwist_ρ_rotationLoop`). On a loop `γ`
  reversing the orientation of `M`, as on `ℝP²`, the factor `ev₀^*(o_M^{-1})` alone acts by `-1`
  along this loop when `2 ≠ 0`
  (`TauCeti.RankOneLocalSystem.pullback_basepointMap_orientation_ρ_rotationLoop_ne_one`), so the
  factor `ev₀^*(o_M^{-w})` is needed for this.
* **Constant loops.** Along the inclusion `M → 𝓛M` of the constant loops the torus sign is
  trivial and the orientation part is `o_M`, so the twist pulls back to the orientation local
  system: `i_M^* η₀ ≃ o_M` (`TauCeti.RankOneLocalSystem.pullback_constMap_viterboTwist`).
* **Triviality.** The twist is its own inverse, and it is trivial over a ring in which `2 = 0`. On
  an orientable manifold it is the torus sign
  (`TauCeti.HomologicalOrientation.viterboTwist_eq_torusSign`), so it is trivial when moreover `c`
  vanishes on torus classes (`TauCeti.HomologicalOrientation.viterboTwist_eq_one`), as for the
  pairing with `w₂` on an orientable spin manifold.

## Main definitions

* `TauCeti.RankOneLocalSystem.viterboTwist R hd c γ`: the degree-zero Viterbo twist
  `σ_c ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` on the free loop space of `M`, based at `γ`.

## Main results

* `TauCeti.RankOneLocalSystem.viterboTwist_ρ_rotationLoop`: it is trivial along the rotation of
  every loop.
* `TauCeti.RankOneLocalSystem.pullback_constMap_viterboTwist`: along the constant loops it is the
  orientation local system.
* `TauCeti.HomologicalOrientation.viterboTwist_eq_torusSign`,
  `TauCeti.HomologicalOrientation.viterboTwist_eq_one`: on an orientable manifold it is the torus
  sign, and it is trivial when `c` also vanishes on torus classes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
-/

public section

noncomputable section

open AlgebraicTopology Module

namespace TauCeti

open MooreFreeLoopSpace

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}
  (R : Type*) [CommRing R] (hd : finrank ℝ E = d)
  (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of M) →+
    ZMod 2)

namespace RankOneLocalSystem

/-- **The degree-zero Viterbo twist** of an additive map `c : H₂(M; ℤ) → ℤ/2`, on the free loop
space of a manifold `M` based at a free loop `γ`: the rank-one local system
`σ_c ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})`, the product of the torus sign of `c` with the orientation
part of the twist. For `c` the pairing with the second Stiefel–Whitney class of `M`, it is the twist
`η₀` of the Viterbo isomorphism with DG coefficients for the cotangent bundle of `M`. -/
def viterboTwist (γ : MooreFreeLoopSpace M) : RankOneLocalSystem (MooreFreeLoopSpace M) γ R :=
  torusSign R c γ * viterboOrientationTwist R hd γ

variable {R}

theorem viterboTwist_def (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = torusSign R c γ * viterboOrientationTwist R hd γ :=
  (rfl)

/-- A loop of free loops acts on the Viterbo twist by the product of its actions on the torus sign
and on the orientation part. -/
theorem viterboTwist_ρ_apply (γ : MooreFreeLoopSpace M)
    (Λ : MooreLoopSpace (MooreFreeLoopSpace M) γ) :
    (viterboTwist R hd c γ).ρ Λ = (torusSign R c γ).ρ Λ * (viterboOrientationTwist R hd γ).ρ Λ := by
  rw [viterboTwist_def, mul_ρ, MonoidHom.mul_apply]

/-- **The Viterbo twist is trivial along the rotation of every loop.** -/
@[simp]
theorem viterboTwist_ρ_rotationLoop (γ : MooreFreeLoopSpace M) :
    (viterboTwist R hd c γ).ρ γ.rotationLoop = 1 := by
  rw [viterboTwist_ρ_apply, torusSign_ρ_rotationLoop, viterboOrientationTwist_ρ_rotationLoop,
    mul_one]

/-- **The Viterbo twist is its own inverse.** -/
@[simp]
theorem inv_viterboTwist (γ : MooreFreeLoopSpace M) :
    (viterboTwist R hd c γ)⁻¹ = viterboTwist R hd c γ := by
  rw [viterboTwist_def, mul_inv, inv_torusSign, viterboOrientationTwist_eq_freeLoopTwist,
    inv_freeLoopTwist]

/-- The Viterbo twist of the zero map is the orientation part. -/
@[simp]
theorem viterboTwist_zero (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd 0 γ = viterboOrientationTwist R hd γ := by
  rw [viterboTwist_def, torusSign_zero, one_mul]

/-- **Over a ring of characteristic two the Viterbo twist is trivial.** -/
theorem viterboTwist_eq_one_of_two_eq_zero (h2 : (2 : R) = 0) (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = 1 := by
  rw [viterboTwist_def, torusSign_eq_one_of_two_eq_zero c h2,
    viterboOrientationTwist_eq_freeLoopTwist, freeLoopTwist_eq_one_of_two_eq_zero h2, one_mul]

/-- **Along the constant loops the Viterbo twist is the orientation local system**: its pullback
along the inclusion `M → 𝓛M` of the constant loops is `o_M`, that is `i_M^* η₀ ≃ o_M`. -/
@[simp]
theorem pullback_constMap_viterboTwist (x : M) :
    pullback (constMap M) (constMap_apply x) (viterboTwist R hd c (const x)) =
      orientation R hd x := by
  rw [viterboTwist_def, map_mul, pullback_constMap_torusSign,
    pullback_constMap_viterboOrientationTwist, one_mul]

end RankOneLocalSystem

/-- **On an orientable manifold the Viterbo twist is the torus sign.** -/
theorem HomologicalOrientation.viterboTwist_eq_torusSign (o : HomologicalOrientation M E d)
    (γ : MooreFreeLoopSpace M) :
    RankOneLocalSystem.viterboTwist R hd c γ = RankOneLocalSystem.torusSign R c γ := by
  rw [RankOneLocalSystem.viterboTwist_def, o.viterboOrientationTwist_eq_one R hd γ, mul_one]

/-- **On an orientable manifold the Viterbo twist is trivial when `c` vanishes on torus classes**,
as the pairing with the second Stiefel–Whitney class does on a spin manifold. -/
theorem HomologicalOrientation.viterboTwist_eq_one (o : HomologicalOrientation M E d)
    {γ : MooreFreeLoopSpace M} (hc : ∀ g, c (γ.torusClassHom (Additive.ofMul g)) = 0) :
    RankOneLocalSystem.viterboTwist R hd c γ = 1 := by
  rw [o.viterboTwist_eq_torusSign R hd c γ, RankOneLocalSystem.torusSign_eq_one_iff]
  exact .inl hc

end TauCeti
