/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological

/-!
# The orientation character of a manifold

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E` of dimension
`d`, a topological manifold without boundary. The integral local homology `H_d(M, M ∖ {x}; ℤ)` is
infinite cyclic, with two generators, the local orientations at `x`, and transport of local homology
along a path class carries local orientations to local orientations
(`TauCeti.localOrientationTransport`). Along a loop at `x` it either fixes both local orientations
or exchanges them. The **orientation character** `w₁ : π₁(M, x) →* ℤˣ`
(`TauCeti.orientationCharacter`) records which: transport along `γ` is multiplication by `w₁ γ`
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
(`TauCeti.HomologicalOrientation.ofOrientationCharacterEqOne`). This generalizes the orientation of
a simply connected manifold (`TauCeti.HomologicalOrientation.ofSimplyConnectedSpace`).

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

namespace LocalOrientation

/-- In the dimension of the manifold, every point has a local orientation. -/
theorem nonempty (hd : finrank ℝ E = d) (x : M) : Nonempty (LocalOrientation M x d) := by
  cases d with
  | zero => exact exists_localOrientation_of_zero_dim_chart x hd
  | succ d => exact exists_localOrientation_of_chart x hd

/-- In the dimension of the manifold, two local orientations at a point agree up to reversal. -/
theorem eq_or_eq_neg (hd : finrank ℝ E = d) {x : M} (z z' : LocalOrientation M x d) :
    z' = z ∨ z' = -z := by
  subst hd
  exact (IsLocalOrientation.eq_or_eq_neg
    (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))
    z.property z'.property).imp Subtype.ext Subtype.ext

/-- In the dimension of the manifold, a local orientation differs from its reversal. -/
theorem neg_ne (hd : finrank ℝ E = d) {x : M} (z : LocalOrientation M x d) : -z ≠ z := by
  subst hd
  exact fun h ↦ IsLocalOrientation.neg_ne
    (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))
    z.property (congrArg Subtype.val h)

end LocalOrientation

/-! ### Transport along a loop -/

section Loop

variable (E) in
/-- Transport of local orientations along a loop is the identity as soon as it fixes one local
orientation. -/
theorem localOrientationTransport_eq_self_of_eq_self (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) {z₀ : LocalOrientation M x d}
    (h : localOrientationTransport M E d γ z₀ = z₀) (z : LocalOrientation M x d) :
    localOrientationTransport M E d γ z = z := by
  rcases LocalOrientation.eq_or_eq_neg hd z₀ z with rfl | rfl
  · exact h
  · rw [localOrientationTransport_neg, h]

variable (E) in
/-- Transport of local orientations along a loop reverses every local orientation as soon as it
reverses one. -/
theorem localOrientationTransport_eq_neg_of_eq_neg (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) {z₀ : LocalOrientation M x d}
    (h : localOrientationTransport M E d γ z₀ = -z₀) (z : LocalOrientation M x d) :
    localOrientationTransport M E d γ z = -z := by
  rcases LocalOrientation.eq_or_eq_neg hd z₀ z with rfl | rfl
  · exact h
  · rw [localOrientationTransport_neg, h]

end Loop

/-! ### The orientation character -/

section Character

open Classical in
/-- The sign by which transport along a loop acts on local orientations: `1` if it fixes them,
`-1` if it reverses them. The characteristic property is
`TauCeti.coe_localOrientationTransport_eq_zsmul`. -/
private def orientationSign (hd : finrank ℝ E = d) (x : M) (γ : FundamentalGroup M x) : ℤˣ :=
  if localOrientationTransport M E d γ.asHom (LocalOrientation.nonempty hd x).some =
      (LocalOrientation.nonempty hd x).some then 1 else -1

/-- Transport along a loop is multiplication by its sign, on every local orientation. -/
private theorem localOrientationTransport_eq_orientationSign_smul (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroup M x) (z : LocalOrientation M x d) :
    (localOrientationTransport M E d γ.asHom z).val =
      ((orientationSign hd x γ : ℤˣ) : ℤ) • z.val := by
  set z₀ := (LocalOrientation.nonempty hd x).some
  rcases LocalOrientation.eq_or_eq_neg hd z₀ (localOrientationTransport M E d γ.asHom z₀) with
    h | h
  · have hs : orientationSign hd x γ = 1 := by
      rw [orientationSign]
      split_ifs with h'
      · rfl
      · exact absurd h h'
    rw [localOrientationTransport_eq_self_of_eq_self E hd γ.asHom h z, hs, Units.val_one,
      one_zsmul]
  · have hs : orientationSign hd x γ = -1 := by
      rw [orientationSign]
      split_ifs with h'
      · exact absurd (h.symm.trans h') (LocalOrientation.neg_ne hd z₀)
      · rfl
    rw [localOrientationTransport_eq_neg_of_eq_neg E hd γ.asHom h z, hs, Units.val_neg,
      Units.val_one, neg_one_zsmul, LocalOrientation.coe_neg]

/-- Two units of `ℤ` acting identically on a local orientation in the dimension of the manifold
are equal. -/
private theorem units_eq_of_zsmul_eq (hd : finrank ℝ E = d) {x : M} (z : LocalOrientation M x d)
    {u v : ℤˣ} (h : (u : ℤ) • z.val = (v : ℤ) • z.val) : u = v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
  all_goals first
    | rfl
    | exact absurd (Subtype.ext (by simpa using h)) (LocalOrientation.neg_ne hd z)
    | exact absurd (Subtype.ext (by simpa using h.symm)) (LocalOrientation.neg_ne hd z)

/-- The **orientation character** `w₁ : π₁(M, x) →* ℤˣ` of a manifold of dimension `d`: transport
of local homology `H_d(M, M ∖ {x}; ℤ)` along a loop `γ` is multiplication by `w₁ γ`
(`TauCeti.coe_localOrientationTransport_eq_zsmul`). It is `1` on the loops along which transport
preserves the local orientations and `-1` on those along which it reverses them. -/
def orientationCharacter (hd : finrank ℝ E = d) (x : M) : FundamentalGroup M x →* ℤˣ where
  toFun := orientationSign hd x
  map_one' := by
    obtain ⟨z⟩ := LocalOrientation.nonempty hd x
    refine units_eq_of_zsmul_eq hd z ?_
    rw [← localOrientationTransport_eq_orientationSign_smul, End.one_asHom,
      localOrientationTransport_id, Equiv.refl_apply, Units.val_one, one_zsmul]
  map_mul' γ δ := by
    obtain ⟨z⟩ := LocalOrientation.nonempty hd x
    refine units_eq_of_zsmul_eq hd z ?_
    rw [← localOrientationTransport_eq_orientationSign_smul, End.mul_asHom,
      localOrientationTransport_comp, Equiv.trans_apply,
      localOrientationTransport_eq_orientationSign_smul hd γ,
      localOrientationTransport_eq_orientationSign_smul hd δ, Units.val_mul, mul_smul]

/-- **Transport along a loop is multiplication by its orientation character**, on the integral
local homology `H_d(M, M ∖ {x}; ℤ)`, for every local orientation. -/
theorem coe_localOrientationTransport_eq_zsmul (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroup M x) (z : LocalOrientation M x d) :
    (localOrientationTransport M E d γ.asHom z).val =
      ((orientationCharacter hd x γ : ℤˣ) : ℤ) • z.val :=
  localOrientationTransport_eq_orientationSign_smul hd γ z

/-- The orientation character of a loop is `1` exactly when transport along it fixes a given local
orientation. -/
theorem orientationCharacter_eq_one_iff (hd : finrank ℝ E = d) {x : M} (γ : FundamentalGroup M x)
    (z : LocalOrientation M x d) :
    orientationCharacter hd x γ = 1 ↔ localOrientationTransport M E d γ.asHom z = z := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ units_eq_of_zsmul_eq hd z ?_⟩
  · rw [coe_localOrientationTransport_eq_zsmul hd, h, Units.val_one, one_zsmul]
  · rw [← coe_localOrientationTransport_eq_zsmul hd, h, Units.val_one, one_zsmul]

/-- The orientation character of a loop is `-1` exactly when transport along it reverses a given
local orientation. -/
theorem orientationCharacter_eq_neg_one_iff (hd : finrank ℝ E = d) {x : M}
    (γ : FundamentalGroup M x) (z : LocalOrientation M x d) :
    orientationCharacter hd x γ = -1 ↔ localOrientationTransport M E d γ.asHom z = -z := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ units_eq_of_zsmul_eq hd z ?_⟩
  · rw [coe_localOrientationTransport_eq_zsmul hd, h, LocalOrientation.coe_neg, Units.val_neg,
      Units.val_one, neg_one_zsmul]
  · rw [← coe_localOrientationTransport_eq_zsmul hd, h, LocalOrientation.coe_neg, Units.val_neg,
      Units.val_one, neg_one_zsmul]

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
character at `y` of the loop `p⁻¹ γ p` is the orientation character at `x` of `γ`. -/
@[simp]
theorem orientationCharacter_fundamentalGroupMulEquivOfPath (hd : finrank ℝ E = d) {x y : M}
    (p : Path x y) (γ : FundamentalGroup M x) :
    orientationCharacter hd y (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ) =
      orientationCharacter hd x γ := by
  obtain ⟨z⟩ := LocalOrientation.nonempty hd x
  let q : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := Path.Homotopic.Quotient.mk p
  refine units_eq_of_zsmul_eq hd (localOrientationTransport M E d q z) ?_
  rw [← coe_localOrientationTransport_eq_zsmul hd]
  -- The loop at `y` is `q⁻¹ ≫ γ ≫ q`; transport along it is transport back along `q`, then
  -- along `γ`, then along `q`.
  have hγ : (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ).asHom = inv q ≫ γ.asHom ≫ q := by
    simp [FundamentalGroup.fundamentalGroupMulEquivOfPath, q, Groupoid.inv_eq_inv]
  rw [hγ, localOrientationTransport_comp, localOrientationTransport_comp,
    localOrientationTransport_inv, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply,
    coe_localOrientationTransport, coe_localOrientationTransport_eq_zsmul hd, map_zsmul,
    ← coe_localOrientationTransport]

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
    HomologicalOrientation M E d where
  toFun y := localOrientationTransport M E d
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y) :
      FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) z
  localOrientationTransport_toFun' f := by
    rw [← Equiv.trans_apply, ← localOrientationTransport_comp]
    exact localOrientationTransport_eq_of_orientationCharacter_eq_one hd h _ _ z

/-- The orientation extending a local orientation `z` at `x` is, at `y`, the transport of `z`
along any path class from `x` to `y`. -/
theorem ofOrientationCharacterEqOne_apply [PathConnectedSpace M] (hd : finrank ℝ E = d) (x : M)
    (h : orientationCharacter hd x = 1) (z : LocalOrientation M x d) (y : M)
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ofOrientationCharacterEqOne hd x h z y = localOrientationTransport M E d f z :=
  localOrientationTransport_eq_of_orientationCharacter_eq_one hd h _ f z

/-- The orientation extending a local orientation `z` at `x` is `z` at `x`. -/
@[simp]
theorem ofOrientationCharacterEqOne_apply_self [PathConnectedSpace M] (hd : finrank ℝ E = d)
    (x : M) (h : orientationCharacter hd x = 1) (z : LocalOrientation M x d) :
    ofOrientationCharacterEqOne hd x h z x = z := by
  rw [ofOrientationCharacterEqOne_apply hd x h z x (𝟙 _), localOrientationTransport_id,
    Equiv.refl_apply]

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
