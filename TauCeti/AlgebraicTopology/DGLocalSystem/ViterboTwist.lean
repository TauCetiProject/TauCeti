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

Let `M` be a topological manifold of dimension `d`, `R` a commutative ring and
`c : H₂(M; ℤ) → ℤ/2` an additive map. The Viterbo isomorphism with DG coefficients for the
cotangent bundle of `M` (Barraud–Damian–Humilière–Oancea, §§1.5 and 4.1) twists the coefficients on
the free loop space `𝓛M` by the degree-zero rank-one local system

`η₀ = σ ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})`

(`TauCeti.RankOneLocalSystem.viterboTwist`). Here `σ` is the torus sign of `c`, along which a loop
of free loops acts by `(-1) ^ c(a)` for the class `a` of the torus it sweeps out
(`TauCeti.RankOneLocalSystem.torusSign`); for the Viterbo isomorphism `c` is the pairing with the
second Stiefel–Whitney class `w₂(TM)`. The remaining factors are the orientation part
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist`): `o_M` is the orientation local system of
`M`, `ev₀` the evaluation at the base point, and `w(γ)` is `0` or `-1` according to whether `γ`
preserves or reverses the local orientations.

The twist has the following properties.

* **Rotations.** Along the loop of free loops rotating a free loop `γ` once around itself
  (`TauCeti.MooreFreeLoopSpace.rotationLoop`), `η₀` acts trivially
  (`TauCeti.RankOneLocalSystem.viterboTwist_ρ_rotationLoop`): the torus swept out factors through
  the circle, so `σ` acts trivially, and the factor `ev₀^*(o_M^{-w})` cancels the action of
  `ev₀^*(o_M^{-1})`, which is the orientation sign of `γ`
  (`TauCeti.RankOneLocalSystem.pullback_basepointMap_orientation_ρ_rotationLoop`). For an
  orientation-reversing loop `γ`, as on `M = ℝP²`, `ev₀^* o_M` alone acts nontrivially along the
  rotation of `γ` as soon as `2 ≠ 0` in `R`
  (`TauCeti.RankOneLocalSystem.pullback_basepointMap_orientation_ρ_rotationLoop_ne_one`), while
  `η₀` acts trivially.
* **Constant loops.** The pullback of `η₀` along the inclusion `M → 𝓛M` of the constant loops is
  the orientation local system `o_M` (`TauCeti.RankOneLocalSystem.pullback_constMap_viterboTwist`),
  since a loop of constant loops sweeps out a degenerate torus.
* **Orientable and spin manifolds.** On an orientable manifold `η₀` is the torus sign `σ`
  (`TauCeti.HomologicalOrientation.viterboTwist_eq_torusSign`), and the torus sign of `c = 0` is
  trivial. So if `c = ⟨w₂, -⟩` vanishes, as on a spin manifold, `η₀` is trivial on an orientable
  manifold (`TauCeti.RankOneLocalSystem.viterboTwist_zero`, which reduces `η₀` to its orientation
  part).
* **Inverse and characteristic two.** `η₀` is its own inverse
  (`TauCeti.RankOneLocalSystem.inv_viterboTwist`), and it is trivial over a ring in which `2 = 0`
  (`TauCeti.RankOneLocalSystem.viterboTwist_eq_one_of_two_eq_zero`).

## Main definitions

* `TauCeti.RankOneLocalSystem.viterboTwist`: the degree-zero Viterbo twist `η₀`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, EMS (2015), §§5–6 (the local system on the free
  loop space in the Viterbo isomorphism).
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

/-- The **degree-zero Viterbo twist** `η₀ = σ ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` on the free loop
space of a manifold `M`, based at a free loop `γ`: the product of the torus sign `σ` of an additive
map `c : H₂(M; ℤ) → ℤ/2` with the orientation part of the twist. For `c` the pairing with the
second Stiefel–Whitney class of `M`, this is the local system of the Viterbo isomorphism for the
cotangent bundle of `M`. -/
def viterboTwist (γ : MooreFreeLoopSpace M) : RankOneLocalSystem (MooreFreeLoopSpace M) γ R :=
  torusSign R c γ * viterboOrientationTwist R hd γ

variable {R}

theorem viterboTwist_def (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = torusSign R c γ * viterboOrientationTwist R hd γ :=
  (rfl)

/-- **The Viterbo twist is trivial along the rotation of every loop**: the torus sign is, since the
torus swept out by the rotation factors through the circle, and so is the orientation part. -/
@[simp]
theorem viterboTwist_ρ_rotationLoop (γ : MooreFreeLoopSpace M) :
    (viterboTwist R hd c γ).ρ γ.rotationLoop = 1 := by
  rw [viterboTwist_def, mul_ρ, MonoidHom.mul_apply, torusSign_ρ_rotationLoop,
    viterboOrientationTwist_ρ_rotationLoop, mul_one]

/-- **Along the constant loops the Viterbo twist is the orientation local system**: its pullback
along the inclusion `M → 𝓛M` of the constant loops is `o_M`. -/
@[simp]
theorem pullback_constMap_viterboTwist (x : M) :
    pullback (constMap M) (constMap_apply x) (viterboTwist R hd c (const x)) =
      orientation R hd x := by
  rw [viterboTwist_def, map_mul, pullback_constMap_torusSign,
    pullback_constMap_viterboOrientationTwist, one_mul]

/-- **The Viterbo twist is its own inverse.** -/
@[simp]
theorem inv_viterboTwist (γ : MooreFreeLoopSpace M) :
    (viterboTwist R hd c γ)⁻¹ = viterboTwist R hd c γ := by
  rw [viterboTwist_def, mul_inv, inv_torusSign, viterboOrientationTwist_eq_freeLoopTwist,
    inv_freeLoopTwist]

/-- **Over a ring of characteristic two the Viterbo twist is trivial.** -/
theorem viterboTwist_eq_one_of_two_eq_zero (h2 : (2 : R) = 0) (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = 1 := by
  rw [viterboTwist_def, torusSign_eq_one_of_two_eq_zero c h2,
    viterboOrientationTwist_eq_freeLoopTwist, freeLoopTwist_eq_one_of_two_eq_zero h2, one_mul]

/-- For `c = 0` the Viterbo twist is its orientation part. -/
@[simp]
theorem viterboTwist_zero (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd 0 γ = viterboOrientationTwist R hd γ := by
  rw [viterboTwist_def, torusSign_zero, one_mul]

end RankOneLocalSystem

/-- **On an orientable manifold the Viterbo twist is the torus sign.** -/
theorem HomologicalOrientation.viterboTwist_eq_torusSign (o : HomologicalOrientation M E d)
    (γ : MooreFreeLoopSpace M) :
    RankOneLocalSystem.viterboTwist R hd c γ = RankOneLocalSystem.torusSign R c γ := by
  rw [RankOneLocalSystem.viterboTwist_def, o.viterboOrientationTwist_eq_one R hd γ, mul_one]

end TauCeti
