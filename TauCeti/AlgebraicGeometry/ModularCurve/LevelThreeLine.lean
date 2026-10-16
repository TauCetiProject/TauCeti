/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Tactic.ComputeDegree

/-!
# The level-three line over the `j`-line

The **level-three line** over a commutative ring `R` is `Spec R[μ, (μ³ - 1)⁻¹]`, the base of the
level-three normal form

  `Y² + 3 μ X Y + (μ³ - 1) Y = X³`,

which carries the basis of its `3`-torsion with first point `(0, 0)` once a primitive cube root of
unity is adjoined. This curve has `c₄ = 9 μ (μ³ + 8)` and `Δ = 27 (μ³ - 1)³`, so its `j`-invariant
is

  `j = c₄³ / Δ = 27 μ³ (μ³ + 8)³ / (μ³ - 1)³ = 27 u`,  `u = μ³ (μ³ + 8)³ / (μ³ - 1)³`.

This file shows that, when `3` is invertible in `R`, the ring `R[μ, (μ³ - 1)⁻¹]` is a free module
of rank twelve over the polynomial ring `R[u]`. Since `R[u]` is then the polynomial ring `R[j]` of
the `j`-line, the level-three line is a finite free cover of degree twelve of the `j`-line. This is
the ring-theoretic input for identifying the coarse `j`-line away from `3` through the universal
curve with a basis of its `3`-torsion (Katz–Mazur 2.2.11 and 8.2.1).

## The presentation over `R[u]`

Put `d = μ³ - 1`, so that `μ³ = d + 1` and `μ³ + 8 = d + 9`. The defining identity
`μ³ (μ³ + 8)³ = u (μ³ - 1)³` says that `μ` is a root of the polynomial
`T³ (T³ + 8)³ - u (T³ - 1)³` over `R[u]`, which is monic of degree twelve
(`TauCeti.levelThreeRelation`). This is the relation `c₄³ = j Δ` divided by `3⁶`. Conversely, in
`R[u][T] / (T³ (T³ + 8)³ - u (T³ - 1)³)` the identity `(d + 1) (d + 9)³ = u d³` rearranges to

  `d (d³ + (28 - u) d² + 270 d + 972) = -3⁶`,

so `d` is a unit as soon as `3` is (`TauCeti.LevelThreeRing.isUnit_mu_pow_three_sub_one`). The ring
is therefore *defined* as this quotient (`TauCeti.LevelThreeRing`), which makes it free with basis
`1, μ, …, μ¹¹` over `R[u]` for every `R`, and, when `3` is invertible in `R`, it is identified with
the localization `R[μ][(μ³ - 1)⁻¹]` by its universal property (`TauCeti.LevelThreeRing.lift`,
`TauCeti.LevelThreeRing.equivLocalization`).

Without the hypothesis on `3` the quotient is still free of rank twelve, but it is no longer the
localization: modulo `3` the relation becomes `(T - 1)⁹ (T³ - u)`, and the quotient has points with
`μ = 1` and arbitrary `u`.

## Main definitions and results

* `TauCeti.levelThreeRelation`: the monic polynomial `T³ (T³ + 8)³ - u (T³ - 1)³` of degree twelve
  over `R[u]`.
* `TauCeti.LevelThreeRing`: the quotient `R[u][μ] / (μ³ (μ³ + 8)³ - u (μ³ - 1)³)`, which is the
  coordinate ring of the level-three line when `3` is invertible in `R`.
* `TauCeti.finrank_levelThreeRing`: it is free of rank twelve over `R[u]`.
* `TauCeti.LevelThreeRing.isUnit_mu_pow_three_sub_one`: `μ³ - 1`, hence the discriminant, is a unit
  when `3` is invertible.
* `TauCeti.LevelThreeRing.lift`, `TauCeti.LevelThreeRing.algHom_ext`: its universal property; when
  `3` is invertible in `R`, `R`-algebra maps to `S` are elements `x` of `S` with `x³ - 1` a unit.
* `TauCeti.LevelThreeRing.equivLocalization`: when `3` is invertible in `R`, it is the localization
  `R[μ][(μ³ - 1)⁻¹]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.11 and 8.2.1.
-/

public section

open Polynomial

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- The **level-three relation** `T³ (T³ + 8)³ - u (T³ - 1)³` over the polynomial ring `R[u]`. Its
root `T = μ` and the coordinate `u = μ³ (μ³ + 8)³ / (μ³ - 1)³ = j / 27` present, when `3` is
invertible in `R`, the coordinate ring of the level-three line over the `u`-line. -/
noncomputable def levelThreeRelation : R[X][X] :=
  X ^ 3 * (X ^ 3 + 8) ^ 3 - C X * (X ^ 3 - 1) ^ 3

/-- The level-three relation is monic in `T`: the term `u (T³ - 1)³` has degree nine. -/
theorem monic_levelThreeRelation : (levelThreeRelation R).Monic := by
  unfold levelThreeRelation
  monicity!

/-- The level-three relation has degree twelve in `T`. -/
theorem natDegree_levelThreeRelation [Nontrivial R] : (levelThreeRelation R).natDegree = 12 := by
  unfold levelThreeRelation
  compute_degree!

/-- The **level-three ring** over `R`: the `R[u]`-algebra `R[u][μ] / (μ³ (μ³ + 8)³ - u (μ³ - 1)³)`,
where `u = j / 27`. When `3` is invertible in `R`, it is the coordinate ring `R[μ, (μ³ - 1)⁻¹]` of
the level-three line, that is, the localization of `R[μ]` away from `μ³ - 1`
(`TauCeti.LevelThreeRing.equivLocalization`). -/
def LevelThreeRing : Type _ :=
  AdjoinRoot (levelThreeRelation R)

noncomputable instance : CommRing (LevelThreeRing R) :=
  inferInstanceAs (CommRing (AdjoinRoot (levelThreeRelation R)))

noncomputable instance : Algebra R[X] (LevelThreeRing R) :=
  inferInstanceAs (Algebra R[X] (AdjoinRoot (levelThreeRelation R)))

noncomputable instance : Algebra R (LevelThreeRing R) :=
  inferInstanceAs (Algebra R (AdjoinRoot (levelThreeRelation R)))

instance : IsScalarTower R R[X] (LevelThreeRing R) :=
  inferInstanceAs (IsScalarTower R R[X] (AdjoinRoot (levelThreeRelation R)))

/-- The level-three ring is free over `R[u]`, with basis `1, μ, …, μ¹¹`. -/
instance : Module.Free R[X] (LevelThreeRing R) :=
  (monic_levelThreeRelation R).free_adjoinRoot

instance : Module.Finite R[X] (LevelThreeRing R) :=
  (monic_levelThreeRelation R).finite_adjoinRoot

/-- The level-three ring is free of rank twelve over `R[u]`; when `3` is invertible in `R`, the
level-three line is a cover of degree twelve of the `u`-line. -/
theorem finrank_levelThreeRing [Nontrivial R] : Module.finrank R[X] (LevelThreeRing R) = 12 := by
  rw [← natDegree_levelThreeRelation R]
  exact (AdjoinRoot.isAdjoinRootMonic _ (monic_levelThreeRelation R)).finrank

namespace LevelThreeRing

/-- The coordinate `μ` of the level-three line. -/
noncomputable def mu : LevelThreeRing R :=
  AdjoinRoot.root _

/-- The defining identity `μ³ (μ³ + 8)³ = u (μ³ - 1)³` of the coordinate `u` of the `u`-line,
pulled back to the level-three line. -/
@[simp]
theorem mu_pow_three_mul_mu_pow_three_add_eight_pow_three :
    mu R ^ 3 * (mu R ^ 3 + 8) ^ 3 =
      algebraMap R[X] (LevelThreeRing R) X * (mu R ^ 3 - 1) ^ 3 := by
  have h : aeval (mu R) (levelThreeRelation R) = 0 := AdjoinRoot.eval₂_root _
  simp only [levelThreeRelation, map_sub, map_pow, map_add, map_mul, aeval_X, map_one, aeval_C,
    map_ofNat] at h
  linear_combination h

/-- **The discriminant is a unit on the level-three line.** When `3` is invertible in `R`, the
element `μ³ - 1`, whose cube is `Δ / 27`, is a unit: with `d = μ³ - 1`, the defining identity reads
`d (d³ + (28 - u) d² + 270 d + 972) = -3⁶`. -/
theorem isUnit_mu_pow_three_sub_one (h3 : IsUnit (3 : R)) : IsUnit (mu R ^ 3 - 1) := by
  set d := mu R ^ 3 - 1
  set u := algebraMap R[X] (LevelThreeRing R) X
  have h729 : IsUnit (729 : LevelThreeRing R) := by
    have h := (h3.map (algebraMap R (LevelThreeRing R))).pow 6
    rwa [map_ofNat, show (3 : LevelThreeRing R) ^ 6 = 729 by norm_num] at h
  refine isUnit_of_mul_isUnit_left (y := -(d ^ 3 + (28 - u) * d ^ 2 + 270 * d + 972)) ?_
  convert h729 using 1
  linear_combination -mu_pow_three_mul_mu_pow_three_add_eight_pow_three R

section lift

variable {R} {S : Type*} [CommRing S] [Algebra R S]

/-- An `R`-algebra map out of the level-three ring sends the coordinate `u` to
`x³ (x³ + 8)³ / (x³ - 1)³`, where `x` is the image of `μ`. -/
theorem map_algebraMap_X_mul (φ : LevelThreeRing R →ₐ[R] S) :
    φ (algebraMap R[X] (LevelThreeRing R) X) * (φ (mu R) ^ 3 - 1) ^ 3 =
      φ (mu R) ^ 3 * (φ (mu R) ^ 3 + 8) ^ 3 := by
  have h := congrArg φ (mu_pow_three_mul_mu_pow_three_add_eight_pow_three R)
  simp only [map_pow, map_add, map_sub, map_mul, map_one, map_ofNat] at h
  exact h.symm

/-- The **universal property** of the level-three ring: an element `x` of an `R`-algebra `S` such
that `x³ - 1` is a unit determines an `R`-algebra map sending `μ` to `x`. It is unique when `3` is
invertible in `R` (`TauCeti.LevelThreeRing.algHom_ext`). -/
noncomputable def lift (x : S) (hx : IsUnit (x ^ 3 - 1)) : LevelThreeRing R →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (levelThreeRelation R)
    (aeval (x ^ 3 * (x ^ 3 + 8) ^ 3 * ↑hx.unit⁻¹ ^ 3)) x (by
      have h := hx.mul_val_inv
      simp only [levelThreeRelation, eval₂_sub, eval₂_pow, eval₂_add, eval₂_mul, eval₂_X,
        eval₂_one, eval₂_C, eval₂_ofNat, AlgHom.coe_toRingHom, aeval_X]
      linear_combination (-(x ^ 3 * (x ^ 3 + 8) ^ 3) *
        (1 + (x ^ 3 - 1) * ↑hx.unit⁻¹ + ((x ^ 3 - 1) * ↑hx.unit⁻¹) ^ 2)) * h)

@[simp]
theorem lift_mu (x : S) (hx : IsUnit (x ^ 3 - 1)) : lift (R := R) x hx (mu R) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The map `TauCeti.LevelThreeRing.lift` sends the coordinate `u` to
`x³ (x³ + 8)³ / (x³ - 1)³`. -/
@[simp]
theorem lift_algebraMap_X (x : S) (hx : IsUnit (x ^ 3 - 1)) :
    lift (R := R) x hx (algebraMap R[X] (LevelThreeRing R) X) =
      x ^ 3 * (x ^ 3 + 8) ^ 3 * ↑hx.unit⁻¹ ^ 3 :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ X).trans (aeval_X _)

/-- When `3` is invertible in `R`, two `R`-algebra maps out of the level-three ring agree once
they agree on `μ`. The hypothesis on `3` is necessary: modulo `3`, the maps sending `μ` to `1` may
send `u` anywhere. -/
theorem algHom_ext (h3 : IsUnit (3 : R)) {φ ψ : LevelThreeRing R →ₐ[R] S}
    (h : φ (mu R) = ψ (mu R)) : φ = ψ := by
  have hu :
      φ (algebraMap R[X] (LevelThreeRing R) X) = ψ (algebraMap R[X] (LevelThreeRing R) X) := by
    have hd := ((isUnit_mu_pow_three_sub_one R h3).map φ).pow 3
    rw [map_sub, map_pow, map_one] at hd
    refine hd.mul_right_cancel ?_
    rw [map_algebraMap_X_mul, h, ← map_algebraMap_X_mul ψ]
  exact AdjoinRoot.algHom_ext' (Polynomial.algHom_ext hu) h

omit [Algebra R S] in
/-- Two `R[u]`-algebra maps out of the level-three ring agree once they agree on `μ`. -/
@[ext]
theorem algHom_ext' [Algebra R[X] S] {φ ψ : LevelThreeRing R →ₐ[R[X]] S}
    (h : φ (mu R) = ψ (mu R)) : φ = ψ :=
  AdjoinRoot.algHom_ext h

end lift

section equivLocalization

variable {R}

/-- When `3` is invertible in `R`, the level-three ring is the localization `R[μ][(μ³ - 1)⁻¹]` of
the polynomial ring in `μ`. -/
noncomputable def equivLocalization (h3 : IsUnit (3 : R)) :
    LevelThreeRing R ≃ₐ[R] Localization.Away (X ^ 3 - 1 : R[X]) :=
  have hX : IsUnit (algebraMap R[X] (Localization.Away (X ^ 3 - 1 : R[X])) X ^ 3 - 1) := by
    have h := IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (X ^ 3 - 1 : R[X])) (X ^ 3 - 1 : R[X])
    rwa [map_sub, map_pow, map_one] at h
  AlgEquiv.ofAlgHom (lift _ hX)
    (IsLocalization.Away.liftAlgHom (X ^ 3 - 1 : R[X]) (f := aeval (mu R))
      (by simpa using isUnit_mu_pow_three_sub_one R h3))
    (AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (.powers (X ^ 3 - 1 : R[X])) <|
      Polynomial.ringHom_ext
        (fun r ↦ by
          simp [IsScalarTower.algebraMap_apply R R[X] (Localization.Away (X ^ 3 - 1 : R[X]))])
        (by simp))
    (algHom_ext h3 (by simp))

@[simp]
theorem equivLocalization_mu (h3 : IsUnit (3 : R)) :
    equivLocalization h3 (mu R) = algebraMap R[X] (Localization.Away (X ^ 3 - 1 : R[X])) X := by
  simp [equivLocalization]

@[simp]
theorem equivLocalization_symm_algebraMap_X (h3 : IsUnit (3 : R)) :
    (equivLocalization h3).symm (algebraMap R[X] (Localization.Away (X ^ 3 - 1 : R[X])) X) =
      mu R :=
  (equivLocalization h3).symm_apply_eq.mpr (equivLocalization_mu h3).symm

/-- The identification `TauCeti.LevelThreeRing.equivLocalization` sends the coordinate `u` to
`μ³ (μ³ + 8)³ / (μ³ - 1)³`. -/
theorem equivLocalization_algebraMap_X (h3 : IsUnit (3 : R)) :
    equivLocalization h3 (algebraMap R[X] (LevelThreeRing R) X) =
      IsLocalization.mk' (Localization.Away (X ^ 3 - 1 : R[X])) (X ^ 3 * (X ^ 3 + 8) ^ 3 : R[X])
        (⟨(X ^ 3 - 1) ^ 3, 3, rfl⟩ : Submonoid.powers (X ^ 3 - 1 : R[X])) := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  simpa [map_ofNat] using map_algebraMap_X_mul (equivLocalization h3).toAlgHom

end equivLocalization

end LevelThreeRing

end TauCeti
