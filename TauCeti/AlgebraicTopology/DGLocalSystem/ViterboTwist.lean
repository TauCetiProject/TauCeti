/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Orientation.Viterbo
public import TauCeti.AlgebraicTopology.DGLocalSystem.TorusSign

/-!
# The degree-zero Viterbo twist on the free loop space

Let `M` be a topological manifold of dimension `d`, `R` a commutative ring and
`c : H₂(M; ℤ) → ℤ/2` an additive map. The Viterbo isomorphism with DG coefficients for the
cotangent bundle of `M` identifies symplectic homology with the homology of the free loop space
`𝓛M` twisted by the degree-zero rank-one local system

`η₀ = σ ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})`

of Barraud–Damian–Humilière–Oancea (§§1.5 and 4.1), where `σ` is the sign system along which a
loop of free loops acts by `(-1) ^ ⟨w₂(TM), a⟩` for the class `a` of the torus it sweeps out,
`o_M` is the orientation local system and `w(γ)` is `0` on loops preserving the local orientations
and `-1` on the others. This file defines the twist for an arbitrary `c` in place of the pairing
with the second Stiefel–Whitney class (`TauCeti.RankOneLocalSystem.viterboTwist`), as the product
of the torus sign of `c` (`TauCeti.RankOneLocalSystem.torusSign`) with the orientation part
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist`); for `c = ⟨w₂(TM), -⟩` it is `η₀`.

The laws of the two factors combine:

* along the constant loops the twist is the orientation local system of `M`,
  `i_M^* η₀ = o_M` (`TauCeti.RankOneLocalSystem.pullback_constMap_viterboTwist`), since the torus
  sign is trivial there;
* it is trivial along the rotation of every loop
  (`TauCeti.RankOneLocalSystem.viterboTwist_ρ_rotationLoop`). Rotating a loop `γ` once around
  itself sweeps out the torus `(s, t) ↦ γ(s + t)`, which factors through the circle, so `c`
  vanishes on its class; and the factor `ev₀^*(o_M^{-w})` cancels the orientation sign of `γ` by
  which `ev₀^* o_M` alone acts along it. This is the source's check on `ℝP²`: on the component of
  an orientation-reversing loop `η₀ = σ`, and it has monodromy `+1` along the rotation;
* it is its own inverse (`TauCeti.RankOneLocalSystem.inv_viterboTwist`), and it is trivial over a
  ring in which `2 = 0` (`TauCeti.RankOneLocalSystem.viterboTwist_eq_one_of_two_eq_zero`);
* it is defined over `ℤ`: extending its coefficients along a ring homomorphism `R →+* R'` gives
  the twist with coefficients in `R'` (`TauCeti.RankOneLocalSystem.mapRingHom_viterboTwist`), since
  both factors act by signs `±1`
  (`TauCeti.RankOneLocalSystem.mapRingHom_torusSign`,
  `TauCeti.RankOneLocalSystem.mapRingHom_viterboOrientationTwist`). So the twist over any
  commutative ring is the extension of coefficients of the twist over `ℤ`;
* it is additive in the class through the torus sign, `η₀(c + c') = η₀(c) ⊗ σ_{c'}`
  (`TauCeti.RankOneLocalSystem.viterboTwist_add`);
* on an orientable manifold it is the torus sign
  (`TauCeti.HomologicalOrientation.viterboTwist_eq_torusSign`), so it is trivial exactly when `c`
  vanishes on the torus classes or `2 = 0`
  (`TauCeti.HomologicalOrientation.viterboTwist_eq_one_iff`); for `c = 0`, the case of an
  orientable spin manifold, it is trivial.

The torus sign, and so the twist, is defined for manifolds `M` in the lowest universe.

## Main definitions

* `TauCeti.RankOneLocalSystem.viterboTwist R hd c γ`: the degree-zero Viterbo twist
  `σ_c ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` on the free loop space based at `γ`.

## Main results

* `TauCeti.RankOneLocalSystem.pullback_constMap_viterboTwist`: `i_M^* η₀ = o_M`.
* `TauCeti.RankOneLocalSystem.viterboTwist_ρ_rotationLoop`: the twist is trivial along the rotation
  of every loop.
* `TauCeti.RankOneLocalSystem.inv_viterboTwist`: the twist is its own inverse.
* `TauCeti.RankOneLocalSystem.mapRingHom_viterboTwist`: the twist is compatible with extension of
  coefficients.
* `TauCeti.RankOneLocalSystem.viterboTwist_add`: `η₀(c + c') = η₀(c) ⊗ σ_{c'}`.
* `TauCeti.HomologicalOrientation.viterboTwist_eq_one_iff`: on an orientable manifold the twist is
  trivial exactly when `c` vanishes on the torus classes or `2 = 0`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, EMS (2015), §§5–6.
-/

public section

noncomputable section

open Module

namespace TauCeti

open MooreFreeLoopSpace

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}
  (R : Type*) [CommRing R] (hd : finrank ℝ E = d)
  (c : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of M) →+ ZMod 2)

namespace RankOneLocalSystem

/-- The **degree-zero Viterbo twist** `σ_c ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` on the free loop
space of a manifold `M`, based at a free loop `γ`: the product of the torus sign of an additive map
`c : H₂(M; ℤ) → ℤ/2` with the orientation part of the twist. For `c` the pairing with the second
Stiefel–Whitney class of `M` it is the twist `η₀` of the Viterbo isomorphism with DG coefficients
for the cotangent bundle of `M`. -/
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

/-- For `c = 0` the Viterbo twist is its orientation part. -/
@[simp]
theorem viterboTwist_zero (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd 0 γ = viterboOrientationTwist R hd γ := by
  rw [viterboTwist_def, torusSign_zero, one_mul]

/-- **The Viterbo twist is trivial along the rotation of every loop.** Rotating a loop once around
itself sweeps out a torus that factors through the circle, so the torus sign is trivial along it
(`TauCeti.RankOneLocalSystem.torusSign_ρ_rotationLoop`), and so is the orientation part
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_rotationLoop`). -/
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

/-- **Over a ring of characteristic two the Viterbo twist is trivial.** -/
theorem viterboTwist_eq_one_of_two_eq_zero (h2 : (2 : R) = 0) (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = 1 := by
  rw [viterboTwist_def, torusSign_eq_one_of_two_eq_zero c h2,
    viterboOrientationTwist_eq_freeLoopTwist, freeLoopTwist_eq_one_of_two_eq_zero h2, one_mul]

/-- **The Viterbo twist is defined over `ℤ`**: extending its coefficients along a ring
homomorphism `φ : R →+* R'` gives the Viterbo twist with coefficients in `R'`. Taking for `φ` the
map `ℤ →+* R`, the twist over any commutative ring is the extension of coefficients of the twist
over `ℤ`. -/
@[simp]
theorem mapRingHom_viterboTwist {R' : Type*} [CommRing R'] (φ : R →+* R')
    (γ : MooreFreeLoopSpace M) : mapRingHom φ (viterboTwist R hd c γ) = viterboTwist R' hd c γ := by
  rw [viterboTwist_def, viterboTwist_def, map_mul, mapRingHom_torusSign,
    mapRingHom_viterboOrientationTwist]

/-- **The tensor law of the Viterbo twist in the class**: replacing `c` by `c + c'` tensors the
twist with the torus sign of `c'`, `η₀(c + c') = η₀(c) ⊗ σ_{c'}`. -/
theorem viterboTwist_add
    (c' : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of M) →+ ZMod 2) (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd (c + c') γ = viterboTwist R hd c γ * torusSign R c' γ := by
  rw [viterboTwist_def, viterboTwist_def, torusSign_add, mul_right_comm]

/-- **Along the constant loops the Viterbo twist is the orientation local system**:
`i_M^* η₀ = o_M`, since the torus sign is trivial along the constant loops. -/
@[simp]
theorem pullback_constMap_viterboTwist (x : M) :
    pullback (constMap M) (constMap_apply x) (viterboTwist R hd c (const x)) =
      orientation R hd x := by
  rw [viterboTwist_def, map_mul, pullback_constMap_torusSign,
    pullback_constMap_viterboOrientationTwist, one_mul]

end RankOneLocalSystem

namespace HomologicalOrientation

open RankOneLocalSystem

variable {R}

/-- **On an orientable manifold the Viterbo twist is the torus sign.** -/
theorem viterboTwist_eq_torusSign (o : HomologicalOrientation M E d) (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = torusSign R c γ := by
  rw [viterboTwist_def, o.viterboOrientationTwist_eq_one R hd γ, mul_one]

/-- **On an orientable manifold the Viterbo twist is trivial exactly when `c` vanishes on the
torus classes at `γ`, or `2 = 0` in `R`.** In particular it is trivial for `c = 0`, the case of an
orientable spin manifold. -/
theorem viterboTwist_eq_one_iff (o : HomologicalOrientation M E d) (γ : MooreFreeLoopSpace M) :
    viterboTwist R hd c γ = 1 ↔
      (∀ g, c (γ.torusClassHom (Additive.ofMul g)) = 0) ∨ (2 : R) = 0 := by
  rw [o.viterboTwist_eq_torusSign, torusSign_eq_one_iff]

end HomologicalOrientation

end TauCeti
