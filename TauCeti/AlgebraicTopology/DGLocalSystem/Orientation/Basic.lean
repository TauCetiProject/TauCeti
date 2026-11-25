/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Character

/-!
# The orientation local system as a rank-one DG local system

Let `M` be a topological manifold of dimension `d`, modelled on a real normed space `E`, with a
base point `x`. Transport of the integral local homology `H_d(M, M ∖ {x}; ℤ)` along a loop is
multiplication by the orientation character `w₁ : π₁(M, x) →* ℤˣ`
(`TauCeti.orientationCharacter`). Over a commutative ring `R`, the **orientation local system**
`o_M` is the rank-one local system on `(M, x)` whose monodromy is `w₁` read in `Rˣ`
(`TauCeti.RankOneLocalSystem.orientation`): a DG local system concentrated in degree zero, on which
a Moore loop acts by the sign by which transport along it acts on local orientations
(`TauCeti.RankOneLocalSystem.orientation_ρ_apply`). Twisting DG local systems and twisting cocycles
by `o_M` and by its inverse is then the rank-one twisting of `TauCeti.RankOneLocalSystem`.

The character takes only the values `±1`, so `o_M` is its own inverse
(`TauCeti.RankOneLocalSystem.inv_orientation`). It is trivial on an orientable manifold
(`TauCeti.HomologicalOrientation.rankOneLocalSystem_orientation_eq_one`) and, since `-1 = 1` there,
over every ring in which `2 = 0` (`TauCeti.RankOneLocalSystem.orientation_eq_one_of_two_eq_zero`).
Over a ring in which `2 ≠ 0` it is trivial exactly when the orientation character is
(`TauCeti.RankOneLocalSystem.orientation_eq_one_iff_orientationCharacter_eq_one`), so it detects
orientability: on a connected manifold it is trivial exactly when the manifold is orientable
(`TauCeti.RankOneLocalSystem.orientation_eq_one_iff`). These coefficient laws are those of every
rank-one local system of a `ℤˣ`-valued character
(`TauCeti.RankOneLocalSystem.ofMonodromy_unitsMap_comp_eq_one_iff`).

## Main definitions

* `TauCeti.RankOneLocalSystem.orientation`: the orientation local system `o_M` with coefficients
  in `R`.

## Main results

* `TauCeti.RankOneLocalSystem.monodromy_orientation`: the monodromy of `o_M` is the orientation
  character.
* `TauCeti.RankOneLocalSystem.inv_orientation`: `o_M⁻¹ = o_M`.
* `TauCeti.RankOneLocalSystem.orientation_eq_one_iff_orientationCharacter_eq_one`: over a ring
  with `2 ≠ 0`, `o_M` is trivial exactly when the orientation character is.
* `TauCeti.RankOneLocalSystem.orientation_eq_one_iff`: over a ring with `2 ≠ 0`, `o_M` is trivial
  exactly when the connected manifold `M` is orientable.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 and Section 3.H, local coefficients.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.3 and §4.1.
-/

public section

noncomputable section

open Module

universe w

namespace TauCeti

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}
  (R : Type*) [CommRing R]

namespace RankOneLocalSystem

/-- The **orientation local system** `o_M` of a manifold `M` of dimension `d`, with coefficients
in a commutative ring `R`, as a rank-one DG local system on `(M, x)`: its monodromy is the
orientation character `π₁(M, x) →* ℤˣ` read in `Rˣ`. -/
def orientation (hd : finrank ℝ E = d) (x : M) : RankOneLocalSystem M x R :=
  ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (orientationCharacter hd x))

theorem orientation_def (hd : finrank ℝ E = d) (x : M) :
    orientation R hd x =
      ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (orientationCharacter hd x)) :=
  (rfl)

variable {R}

/-- The monodromy of the orientation local system is the orientation character. -/
@[simp]
theorem monodromy_orientation (hd : finrank ℝ E = d) (x : M) :
    (orientation R hd x).monodromy =
      (Units.map (Int.castRingHom R).toMonoidHom).comp (orientationCharacter hd x) :=
  monodromy_ofMonodromy _

/-- A Moore loop acts on the orientation local system by the orientation character of its class,
the sign by which transport along it acts on local orientations. -/
@[simp]
theorem orientation_ρ_apply (hd : finrank ℝ E = d) {x : M} (γ : MooreLoopSpace M x) :
    (orientation R hd x).ρ γ =
      Units.map (Int.castRingHom R).toMonoidHom
        (orientationCharacter hd x (MooreLoopSpace.fundamentalGroupHom x γ)) :=
  ofMonodromy_unitsMap_comp_ρ_apply _ γ

/-- **The orientation local system is its own inverse**, since the orientation character takes
only the values `±1`. -/
@[simp]
theorem inv_orientation (hd : finrank ℝ E = d) (x : M) :
    (orientation R hd x)⁻¹ = orientation R hd x :=
  inv_ofMonodromy_unitsMap_comp _

/-- The square of the orientation local system is trivial. -/
@[simp]
theorem orientation_mul_self (hd : finrank ℝ E = d) (x : M) :
    orientation R hd x * orientation R hd x = 1 := by
  nth_rw 1 [← inv_orientation hd x]
  exact inv_mul_cancel _

/-- **Over a ring of characteristic two the orientation local system is trivial**: there `-1 = 1`,
so every sign acts trivially. -/
theorem orientation_eq_one_of_two_eq_zero (h : (2 : R) = 0) (hd : finrank ℝ E = d) (x : M) :
    orientation R hd x = 1 :=
  (ofMonodromy_unitsMap_comp_eq_one_iff _).2 (.inr h)

/-- Over a ring in which `2 ≠ 0`, the orientation local system is trivial exactly when the
orientation character is trivial. -/
theorem orientation_eq_one_iff_orientationCharacter_eq_one (h : (2 : R) ≠ 0)
    (hd : finrank ℝ E = d) (x : M) : orientation R hd x = 1 ↔ orientationCharacter hd x = 1 :=
  (ofMonodromy_unitsMap_comp_eq_one_iff _).trans (or_iff_left h)

end RankOneLocalSystem

/-- **The orientation local system of an orientable manifold is trivial**, with coefficients in
every commutative ring. -/
theorem HomologicalOrientation.rankOneLocalSystem_orientation_eq_one
    (o : HomologicalOrientation M E d) (hd : finrank ℝ E = d) (x : M) :
    RankOneLocalSystem.orientation R hd x = 1 :=
  RankOneLocalSystem.monodromy_injective <| by
    rw [RankOneLocalSystem.monodromy_orientation, RankOneLocalSystem.monodromy_one,
      o.orientationCharacter_eq_one hd x, MonoidHom.comp_one]

namespace RankOneLocalSystem

variable {R}

/-- **The orientation local system detects orientability**: over a ring in which `2 ≠ 0`, the
orientation local system of a connected manifold is trivial exactly when the manifold is
orientable. -/
theorem orientation_eq_one_iff [ConnectedSpace M] (h : (2 : R) ≠ 0) (hd : finrank ℝ E = d)
    (x : M) : orientation R hd x = 1 ↔ Nonempty (HomologicalOrientation M E d) :=
  (orientation_eq_one_iff_orientationCharacter_eq_one h hd x).trans
    (nonempty_homologicalOrientation_iff hd x).symm

end RankOneLocalSystem

end TauCeti
