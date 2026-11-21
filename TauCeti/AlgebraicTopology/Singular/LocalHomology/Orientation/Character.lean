/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The orientation character of a manifold

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E` of dimension
`d`, a topological manifold without boundary. The integral local homology `H_d(M, M ∖ {x}; ℤ)` is
infinite cyclic, with two generators, the local orientations at `x`, and transport of local homology
along a path class carries local orientations to local orientations
(`TauCeti.localOrientationTransport`). Along a loop at `x` it either fixes both local orientations
or exchanges them. The **orientation character** `w₁ : π₁(M, x) →* ℤˣ`
(`TauCeti.orientationCharacter`), the sign of this permutation of the two local orientations,
records which: transport along `γ` is multiplication by `w₁ γ`
(`TauCeti.coe_localOrientationTransport_eq_zsmul`). It is the monodromy of the orientation local
system `localHomologySystem` in degree `d` with integer coefficients, and it does not depend on
the base point, up to the identification of fundamental groups along a path
(`TauCeti.orientationCharacter_fundamentalGroupMulEquivOfPath`).

A connected manifold is orientable exactly when its orientation character is trivial
(`TauCeti.nonempty_homologicalOrientation_iff`). An orientation is invariant under transport, so
it forces the character to be trivial
(`TauCeti.HomologicalOrientation.orientationCharacter_eq_one`).
Conversely, when the character is trivial, transport from `x` does not depend on the path, so a
local orientation at `x` extends by transport to an orientation of `M`
(`TauCeti.HomologicalOrientation.ofOrientationCharacterEqOne`), through the same construction
(`TauCeti.HomologicalOrientation.ofLocalOrientationTransport`) as the orientation of a simply
connected manifold (`TauCeti.HomologicalOrientation.ofSimplyConnectedSpace`).

## Main definitions

* `TauCeti.orientationCharacter`: the orientation character `π₁(M, x) →* ℤˣ`.
* `TauCeti.HomologicalOrientation.ofOrientationCharacterEqOne`: the orientation of a path-connected
  manifold with trivial orientation character extending a local orientation at the base point.

## Main results

* `TauCeti.coe_localOrientationTransport_eq_zsmul`: transport along a loop is multiplication by
  its orientation character.
* `TauCeti.orientationCharacter_eq_one_iff`, `TauCeti.orientationCharacter_eq_neg_one_iff`: the
  character is `1` when transport fixes a local orientation and `-1` when it reverses it.
* `TauCeti.orientationCharacter_fundamentalGroupMulEquivOfPath`: independence of the base point.
* `TauCeti.nonempty_homologicalOrientation_iff`: a connected manifold is orientable exactly when
  its orientation character is trivial.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the orientation double cover and Proposition 3.25.
-/

public section

noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}

/-! ### The orientation character -/

section Character

open Classical in
/-- The **orientation character** `w₁ : π₁(M, x) →* ℤˣ` of a manifold of dimension `d`: the sign
of the permutation of the two local orientations at `x` given by transport along a loop. It is
`1` on the loops along which transport preserves the local orientations and `-1` on those along
which it reverses them, so transport of local homology `H_d(M, M ∖ {x}; ℤ)` along a loop `γ` is
multiplication by `w₁ γ` (`TauCeti.coe_localOrientationTransport_eq_zsmul`). -/
def orientationCharacter (hd : finrank ℝ E = d) (x : M) : FundamentalGroup M x →* ℤˣ :=
  haveI := LocalOrientation.finite hd x
  letI := Fintype.ofFinite (LocalOrientation M x d)
  Equiv.Perm.sign.comp (localOrientationTransportPerm M E d x)

/-- The orientation character is the sign of the transport permutation, for any choice of the
finiteness and decidability instances on the local orientations. -/
theorem orientationCharacter_apply (hd : finrank ℝ E = d) {x : M}
    [Fintype (LocalOrientation M x d)] [DecidableEq (LocalOrientation M x d)]
    (γ : FundamentalGroup M x) :
    orientationCharacter hd x γ = Equiv.Perm.sign (localOrientationTransportPerm M E d x γ) := by
  rw [orientationCharacter, MonoidHom.comp_apply]
  congr!

/-- The orientation character of a loop is `1` exactly when transport along it fixes a given local
orientation. -/
theorem orientationCharacter_eq_one_iff (hd : finrank ℝ E = d) {x : M} (γ : FundamentalGroup M x)
    (z : LocalOrientation M x d) :
    orientationCharacter hd x γ = 1 ↔ localOrientationTransport M E d γ.asHom z = z := by
  classical
  have := LocalOrientation.finite hd x
  let := Fintype.ofFinite (LocalOrientation M x d)
  -- A permutation of the two local orientations has sign `1` exactly when it is the identity,
  -- since the alternating group of a set with two elements is trivial.
  rw [orientationCharacter_apply, ← Equiv.Perm.mem_alternatingGroup,
    alternatingGroup.eq_bot_of_card_le_two (LocalOrientation.nat_card_eq_two hd x).le,
    Subgroup.mem_bot]
  refine ⟨fun h ↦ by simpa using Equiv.ext_iff.1 h z, fun h ↦ Equiv.ext fun z' ↦ ?_⟩
  simpa using localOrientationTransport_eq_self_of_eq_self E hd γ.asHom h z'

/-- The orientation character of a loop is `-1` exactly when transport along it reverses a given
local orientation. -/
theorem orientationCharacter_eq_neg_one_iff (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroup M x) (z : LocalOrientation M x d) :
    orientationCharacter hd x γ = -1 ↔ localOrientationTransport M E d γ.asHom z = -z := by
  rw [← Int.units_ne_iff_eq_neg, Ne, orientationCharacter_eq_one_iff hd γ z]
  rcases LocalOrientation.eq_or_eq_neg hd z (localOrientationTransport M E d γ.asHom z) with
    h | h <;> rw [h]
  · exact iff_of_false (not_not.2 rfl) fun h' ↦ LocalOrientation.neg_ne hd z h'.symm
  · exact iff_of_true (LocalOrientation.neg_ne hd z) rfl

/-- **Transport along a loop is multiplication by its orientation character**, on the integral
local homology `H_d(M, M ∖ {x}; ℤ)`, for every local orientation. -/
theorem coe_localOrientationTransport_eq_zsmul (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroup M x) (z : LocalOrientation M x d) :
    (localOrientationTransport M E d γ.asHom z).val =
      ((orientationCharacter hd x γ : ℤˣ) : ℤ) • z.val := by
  rcases Int.units_eq_one_or (orientationCharacter hd x γ) with h | h
  · rw [(orientationCharacter_eq_one_iff hd γ z).1 h, h, Units.val_one, one_zsmul]
  · rw [(orientationCharacter_eq_neg_one_iff hd γ z).1 h, h, LocalOrientation.coe_neg,
      Units.val_neg, Units.val_one, neg_one_zsmul]

/-- The orientation character takes only the values `1` and `-1`, so it is its own inverse. -/
@[simp]
theorem orientationCharacter_inv (hd : finrank ℝ E = d) (x : M) :
    (orientationCharacter hd x)⁻¹ = orientationCharacter hd x :=
  MonoidHom.ext fun _ ↦ Int.units_inv_eq_self _

/-- Two path classes from the base point with the same end transport local orientations in the
same way when the orientation character is trivial. -/
theorem localOrientationTransport_eq_of_orientationCharacter_eq_one (hd : finrank ℝ E = d) {x : M}
    (h : orientationCharacter hd x = 1) {y : FundamentalGroupoid M}
    (f g : FundamentalGroupoid.mk x ⟶ y) (z : LocalOrientation M x d) :
    localOrientationTransport M E d f z = localOrientationTransport M E d g z := by
  have hfg : localOrientationTransport M E d (f ≫ inv g) z = z :=
    (orientationCharacter_eq_one_iff hd (End.of (f ≫ inv g)) z).1 (DFunLike.congr_fun h _)
  rwa [localOrientationTransport_comp, localOrientationTransport_inv, Equiv.trans_apply,
    Equiv.symm_apply_eq] at hfg

/-- **Independence of the base point.** Along a path `p` from `x` to `y`, the orientation
character at `y` of the loop `p⁻¹ γ p` is the orientation character at `x` of `γ`: the two
transport permutations are conjugate by transport along `p`. -/
@[simp]
theorem orientationCharacter_fundamentalGroupMulEquivOfPath (hd : finrank ℝ E = d) {x y : M}
    (p : Path x y) (γ : FundamentalGroup M x) :
    orientationCharacter hd y (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ) =
      orientationCharacter hd x γ := by
  classical
  have := LocalOrientation.finite hd x
  have := LocalOrientation.finite hd y
  let := Fintype.ofFinite (LocalOrientation M x d)
  let := Fintype.ofFinite (LocalOrientation M y d)
  let q : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := Path.Homotopic.Quotient.mk p
  -- The loop at `y` is `q⁻¹ ≫ γ ≫ q`; transport along it is transport back along `q`, then
  -- along `γ`, then along `q`.
  have hγ : (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ).asHom = inv q ≫ γ.asHom ≫ q := by
    simp [FundamentalGroup.fundamentalGroupMulEquivOfPath, q, Groupoid.inv_eq_inv]
  rw [orientationCharacter_apply, orientationCharacter_apply,
    ← Equiv.Perm.sign_permCongr (localOrientationTransport M E d q)]
  congr 1
  ext z : 1
  rw [localOrientationTransportPerm_apply, hγ, Equiv.permCongr_apply,
    localOrientationTransportPerm_apply, localOrientationTransport_comp,
    localOrientationTransport_comp, localOrientationTransport_inv, Equiv.trans_apply,
    Equiv.trans_apply]

end Character

/-! ### Orientability -/

namespace HomologicalOrientation

/-- **An orientable manifold has trivial orientation character**: an orientation is invariant
under transport, so transport along every loop fixes the local orientation it selects. -/
theorem orientationCharacter_eq_one (o : HomologicalOrientation M E d) (hd : finrank ℝ E = d)
    (x : M) : orientationCharacter hd x = 1 :=
  MonoidHom.ext fun γ ↦ (orientationCharacter_eq_one_iff hd γ (o x)).2
    (o.localOrientationTransport_apply γ.asHom)

/-- **Orientations from a trivial orientation character.** If the orientation character of a
path-connected manifold is trivial, transport from the base point does not depend on the path, so a
local orientation `z` at the base point extends, by transport along paths, to an orientation. -/
def ofOrientationCharacterEqOne [PathConnectedSpace M] (hd : finrank ℝ E = d) (x : M)
    (h : orientationCharacter hd x = 1) (z : LocalOrientation M x d) :
    HomologicalOrientation M E d :=
  ofLocalOrientationTransport x z (localOrientationTransport_eq_of_orientationCharacter_eq_one hd h
    · · z)

/-- The orientation extending a local orientation `z` at `x` is, at `y`, the transport of `z`
along any path class from `x` to `y`. -/
theorem ofOrientationCharacterEqOne_apply [PathConnectedSpace M] (hd : finrank ℝ E = d) (x : M)
    (h : orientationCharacter hd x = 1) (z : LocalOrientation M x d) (y : M)
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ofOrientationCharacterEqOne hd x h z y = localOrientationTransport M E d f z :=
  ofLocalOrientationTransport_apply x z _ y f

/-- The orientation extending a local orientation `z` at `x` is `z` at `x`. -/
@[simp]
theorem ofOrientationCharacterEqOne_apply_self [PathConnectedSpace M] (hd : finrank ℝ E = d)
    (x : M) (h : orientationCharacter hd x = 1) (z : LocalOrientation M x d) :
    ofOrientationCharacterEqOne hd x h z x = z :=
  ofLocalOrientationTransport_apply_self x z _

end HomologicalOrientation

/-- **A connected manifold is orientable exactly when its orientation character is trivial**, at
any base point. -/
theorem nonempty_homologicalOrientation_iff [ConnectedSpace M] (hd : finrank ℝ E = d) (x : M) :
    Nonempty (HomologicalOrientation M E d) ↔ orientationCharacter hd x = 1 := by
  refine ⟨fun ⟨o⟩ ↦ o.orientationCharacter_eq_one hd x, fun h ↦ ?_⟩
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  exact ⟨.ofOrientationCharacterEqOne hd x h (LocalOrientation.nonempty hd x).some⟩

end TauCeti
