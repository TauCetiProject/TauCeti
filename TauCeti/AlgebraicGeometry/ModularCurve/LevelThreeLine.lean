/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Ring.GeomSum
import TauCeti.Algebra.Group.Subgroup.Closure
import TauCeti.Algebra.Polynomial.AlgHom
import TauCeti.RingTheory.PowerBasis
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Tactic.ComputeDegree

/-!
# The level-three line over the `j`-line

The **level-three line** over a commutative ring `R` is `Spec R[μ, (μ³ - 1)⁻¹]`, the base of the
level-three normal form

  `Y² + 3 μ X Y + (μ³ - 1) Y = X³`,

which, when `3` is invertible, carries the basis of its `3`-torsion with first point `(0, 0)` once
a primitive cube root of unity is adjoined. This curve has `c₄ = 9 μ (μ³ + 8)` and
`Δ = 27 (μ³ - 1)³`, so its `j`-invariant is

  `j = c₄³ / Δ = 27 μ³ (μ³ + 8)³ / (μ³ - 1)³ = 27 u`,  `u = μ³ (μ³ + 8)³ / (μ³ - 1)³`.

This file shows that, when `3` is invertible in `R`, the ring `R[μ, (μ³ - 1)⁻¹]` is a free module
of rank twelve over the polynomial ring `R[u]`. Since `R[u]` is then the polynomial ring `R[j]` of
the `j`-line, the level-three line is a finite free cover of degree twelve of the `j`-line. If
moreover `R` contains a root `ζ` of `T² + T + 1` and `2` is a nonzerodivisor, the substitutions
`μ ↦ ζ μ` and `μ ↦ (μ + 2) / (μ - 1)` generate a finite group of automorphisms over `R[u]`, the
tetrahedral group, whose ring of invariants is exactly `R[u]`. This is the ring-theoretic input for
identifying the coarse `j`-line away from `3` through the universal curve with a basis of its
`3`-torsion (Katz–Mazur 2.2.11 and 8.2.1).

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

## The tetrahedral group

Let `ζ² + ζ + 1 = 0` in `R`, with `3` invertible. The rotation `τ : μ ↦ ζ μ` fixes `μ³`, hence `u`.
The involution `σ : μ ↦ (μ + 2) / (μ - 1)` also fixes `u`: with `x = σ(μ)`,

  `x³ - 1 = 9 (μ² + μ + 1) / (μ - 1)³`,  `x³ + 8 = 9 μ (μ² - 2 μ + 4) / (μ - 1)³`.

In `PGL₂` these are the classes of `[[ζ, 0], [0, 1]]` and `[[1, 2], [1, -1]]`, and they satisfy
`τ³ = σ² = 1` and `σ τ σ = τ² σ τ²`, so the group they generate consists of the twelve elements
`τ^a` and `τ^a σ τ^b` with `a, b < 3` (`TauCeti.LevelThreeRing.mem_tetrahedralGroup_iff`), which
coincide when `R` is the zero ring. Classically, this is the tetrahedral group `PSL₂(𝔽₃) ≅ A₄`
acting on the level-three line; that identification is not formalized here.

The invariants are computed as for the Legendre line, by an orbit sum. Summing over the rotations
kills `μ^k` unless `3 ∣ k`, and keeps `3 μ^{3j}`. The conjugates of `μ³` are `μ³` and the three
rotations of `w = σ(μ)³`; they are the roots of `V (V + 8)³ - u (V - 1)³`, so their power sums lie
in `R[u]`. To compute these, `w (μ³ - 1)³ = (μ + 2)³ (μ² + μ + 1)³` is split as `A + μ B + μ² C`
with `A`, `B`, `C` polynomials in `μ³`. The orbit sum of a point `a` of the level-three ring
therefore lies in `R[u]`. If `a` is invariant this sum is `12 a`, and comparing coefficients in the
basis `1, μ, …, μ¹¹` shows that `a ∈ R[u]` once `12` is a nonzerodivisor.

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
* `TauCeti.LevelThreeRing.rotationAut`, `TauCeti.LevelThreeRing.addTwoDivSubOneAut`: the
  substitutions `μ ↦ ζ μ` and `μ ↦ (μ + 2) / (μ - 1)` over `R[u]`.
* `TauCeti.LevelThreeRing.tetrahedralGroup`: the group they generate.
* `TauCeti.LevelThreeRing.mem_tetrahedralGroup_iff`: its elements are the twelve substitutions
  `τ^a` and `τ^a σ τ^b`.
* `TauCeti.LevelThreeRing.isInvariant_tetrahedralGroup`: its invariants are `R[u]`.

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
  exact sub_eq_zero.mp h

/-- **The discriminant is a unit on the level-three line.** When `3` is invertible in `R`, the
element `μ³ - 1`, whose cube is `Δ / 27`, is a unit: with `d = μ³ - 1`, the defining identity reads
`d (d³ + (28 - u) d² + 270 d + 972) = -3⁶`. -/
theorem isUnit_mu_pow_three_sub_one (h3 : IsUnit (3 : R)) : IsUnit (mu R ^ 3 - 1) := by
  set d := mu R ^ 3 - 1
  set u := algebraMap R[X] (LevelThreeRing R) X
  have h729 : IsUnit (729 : LevelThreeRing R) := by
    convert (h3.map (algebraMap R (LevelThreeRing R))).pow 6 using 1
    norm_num [map_ofNat]
  refine isUnit_of_mul_isUnit_left (y := -(d ^ 3 + (28 - u) * d ^ 2 + 270 * d + 972)) ?_
  convert h729 using 1
  linear_combination -mu_pow_three_mul_mu_pow_three_add_eight_pow_three R

section lift

variable {R} {S : Type*}

/-- A ring map out of the level-three ring preserves the relation between the coordinates
`u` and `μ`. The target ring need not be commutative. -/
theorem map_algebraMap_X_mul [Ring S] (φ : LevelThreeRing R →+* S) :
    φ (algebraMap R[X] (LevelThreeRing R) X) * (φ (mu R) ^ 3 - 1) ^ 3 =
      φ (mu R) ^ 3 * (φ (mu R) ^ 3 + 8) ^ 3 := by
  have h := congrArg φ (mu_pow_three_mul_mu_pow_three_add_eight_pow_three R)
  simp only [map_pow, map_add, map_sub, map_mul, map_one, map_ofNat] at h
  exact h.symm

/-- Two `R`-algebra maps out of the level-three ring agree once they agree on `μ`, provided
the common image `x` has `x³ - 1` a unit. This does not require `3` to be invertible in `R`.
The unit condition is necessary: modulo `3`, maps sending `μ` to `1` may send `u` anywhere. -/
theorem algHom_ext [Ring S] [Algebra R S] {φ ψ : LevelThreeRing R →ₐ[R] S}
    (hx : IsUnit (φ (mu R) ^ 3 - 1)) (h : φ (mu R) = ψ (mu R)) : φ = ψ := by
  have hu :
      φ (algebraMap R[X] (LevelThreeRing R) X) = ψ (algebraMap R[X] (LevelThreeRing R) X) := by
    apply (hx.pow 3).mul_right_cancel
    have hφ := map_algebraMap_X_mul φ.toRingHom
    have hψ := map_algebraMap_X_mul ψ.toRingHom
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hφ hψ
    rw [hφ, h, ← hψ]
  exact AdjoinRoot.algHom_ext' (Polynomial.algHom_ext hu) h

/-- Two `R[u]`-algebra maps out of the level-three ring agree once they agree on `μ`. -/
@[ext]
theorem algHom_ext' [Semiring S] [Algebra R[X] S] {φ ψ : LevelThreeRing R →ₐ[R[X]] S}
    (h : φ (mu R) = ψ (mu R)) : φ = ψ :=
  AdjoinRoot.algHom_ext h

variable [CommRing S] [Algebra R S]

/-- The **universal property** of the level-three ring: an element `x` of an `R`-algebra `S` such
that `x³ - 1` is a unit determines a unique `R`-algebra map sending `μ` to `x`
(`TauCeti.LevelThreeRing.algHom_ext`). -/
noncomputable def lift (x : S) (hx : IsUnit (x ^ 3 - 1)) : LevelThreeRing R →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (levelThreeRelation R)
    (aeval (x ^ 3 * (x ^ 3 + 8) ^ 3 * ↑hx.unit⁻¹ ^ 3)) x (by
      simp only [levelThreeRelation, eval₂_sub, eval₂_pow, eval₂_add, eval₂_mul, eval₂_X,
        eval₂_one, eval₂_C, eval₂_ofNat, AlgHom.coe_toRingHom, aeval_X]
      rw [mul_assoc, ← mul_pow (↑hx.unit⁻¹ : S) (x ^ 3 - 1), hx.val_inv_mul, one_pow, mul_one,
        sub_self])

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
    (algHom_ext (by simpa using isUnit_mu_pow_three_sub_one R h3) (by simp))

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
  simpa [map_ofNat] using map_algebraMap_X_mul (equivLocalization h3).toRingHom

end equivLocalization

section tetrahedral

variable {R}

/-- When `3` is invertible in `R`, `μ - 1` is a unit of the level-three ring: it divides the unit
`μ³ - 1`. -/
theorem isUnit_mu_sub_one (h3 : IsUnit (3 : R)) : IsUnit (mu R - 1) :=
  isUnit_of_mul_isUnit_left (y := mu R ^ 2 + mu R + 1) <| by
    convert isUnit_mu_pow_three_sub_one R h3 using 1
    ring

/-- The substitution `μ ↦ ω μ` for `ω³ = 1`, as an endomorphism of the level-three ring over the
`u`-line. It fixes `u`, which is a function of `μ³`. -/
private noncomputable def rotationAlgHom (ω : R) (hω : ω ^ 3 = 1) :
    LevelThreeRing R →ₐ[R[X]] LevelThreeRing R :=
  AdjoinRoot.liftAlgHom (levelThreeRelation R) (Algebra.ofId R[X] (LevelThreeRing R))
    (algebraMap R (LevelThreeRing R) ω * mu R) (by
      have hω' : algebraMap R (LevelThreeRing R) ω ^ 3 = 1 := by rw [← map_pow, hω, map_one]
      simp only [levelThreeRelation, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X,
        eval₂_C, eval₂_ofNat, eval₂_one, AlgHom.coe_toRingHom, Algebra.ofId_apply]
      rw [mul_pow, hω', one_mul, sub_eq_zero]
      exact mu_pow_three_mul_mu_pow_three_add_eight_pow_three R)

private theorem rotationAlgHom_mu (ω : R) (hω : ω ^ 3 = 1) :
    rotationAlgHom ω hω (mu R) = algebraMap R (LevelThreeRing R) ω * mu R :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem rotationAlgHom_comp_rotationAlgHom {ω ω' : R} (hω : ω ^ 3 = 1)
    (hω' : ω' ^ 3 = 1) (h : ω * ω' = 1) :
    (rotationAlgHom ω hω).comp (rotationAlgHom ω' hω') = AlgHom.id R[X] _ := by
  refine algHom_ext' ?_
  rw [AlgHom.comp_apply, rotationAlgHom_mu, map_mul, AlgHom.map_algebraMap,
    rotationAlgHom_mu, AlgHom.id_apply, ← mul_assoc, ← map_mul, mul_comm ω' ω, h, map_one,
    one_mul]

/-- The **rotation** `μ ↦ ζ μ` of the level-three line by an element `ζ` with `ζ³ = 1`, an
automorphism of the level-three ring over the `u`-line. -/
noncomputable def rotationAut (ζ : R) (hζ : ζ ^ 3 = 1) :
    LevelThreeRing R ≃ₐ[R[X]] LevelThreeRing R :=
  have hζ2 : (ζ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  AlgEquiv.ofAlgHom (rotationAlgHom ζ hζ) (rotationAlgHom (ζ ^ 2) hζ2)
    (rotationAlgHom_comp_rotationAlgHom hζ hζ2 (by rw [← pow_succ', hζ]))
    (rotationAlgHom_comp_rotationAlgHom hζ2 hζ (by rw [← pow_succ, hζ]))

@[simp]
theorem rotationAut_mu (ζ : R) (hζ : ζ ^ 3 = 1) :
    rotationAut ζ hζ (mu R) = algebraMap R (LevelThreeRing R) ζ * mu R :=
  rotationAlgHom_mu ζ hζ

/-- The element `(μ + 2) / (μ - 1)` of the level-three ring, when `3` is invertible. -/
private noncomputable def addTwoDivSubOne (h3 : IsUnit (3 : R)) : LevelThreeRing R :=
  (mu R + 2) * ↑(isUnit_mu_sub_one h3).unit⁻¹

private theorem addTwoDivSubOne_mul (h3 : IsUnit (3 : R)) :
    addTwoDivSubOne h3 * (mu R - 1) = mu R + 2 := by
  rw [addTwoDivSubOne, mul_assoc, (isUnit_mu_sub_one h3).val_inv_mul, mul_one]

/-- With `x = (μ + 2) / (μ - 1)`, the element `x³ - 1 = 9 (μ² + μ + 1) / (μ - 1)³` is a unit. -/
private theorem isUnit_addTwoDivSubOne_pow_three_sub_one (h3 : IsUnit (3 : R)) :
    IsUnit (addTwoDivSubOne h3 ^ 3 - 1) := by
  set i : LevelThreeRing R := ↑(isUnit_mu_sub_one h3).unit⁻¹
  have hi : i * (mu R - 1) = 1 := (isUnit_mu_sub_one h3).val_inv_mul
  have hq : IsUnit (mu R ^ 2 + mu R + 1) :=
    isUnit_of_mul_isUnit_right (x := mu R - 1) <| by
      convert isUnit_mu_pow_three_sub_one R h3 using 1
      ring
  have h9 : IsUnit (9 : LevelThreeRing R) := by
    convert (h3.map (algebraMap R (LevelThreeRing R))).pow 2 using 1
    norm_num [map_ofNat]
  have e : addTwoDivSubOne h3 ^ 3 - 1 = 9 * (mu R ^ 2 + mu R + 1) * i ^ 3 := by
    rw [addTwoDivSubOne]
    linear_combination ((i * (mu R - 1)) ^ 2 + i * (mu R - 1) + 1) * hi
  rw [e]
  exact (h9.mul hq).mul ((Units.isUnit _).pow 3)

/-- The substitution `μ ↦ (μ + 2) / (μ - 1)`, as an `R`-algebra endomorphism. -/
private noncomputable def addTwoDivSubOneAlgHom (h3 : IsUnit (3 : R)) :
    LevelThreeRing R →ₐ[R] LevelThreeRing R :=
  lift (addTwoDivSubOne h3) (isUnit_addTwoDivSubOne_pow_three_sub_one h3)

private theorem addTwoDivSubOneAlgHom_mu (h3 : IsUnit (3 : R)) :
    addTwoDivSubOneAlgHom h3 (mu R) = addTwoDivSubOne h3 :=
  lift_mu _ _

/-- The substitution `μ ↦ (μ + 2) / (μ - 1)` fixes `u`. With `x = (μ + 2) / (μ - 1)`, one has
`x³ - 1 = 9 (μ² + μ + 1) / (μ - 1)³` and `x³ + 8 = 9 μ (μ² - 2 μ + 4) / (μ - 1)³`, so that
`x³ (x³ + 8)³ / (x³ - 1)³ = μ³ (μ³ + 8)³ / (μ³ - 1)³`. -/
private theorem addTwoDivSubOneAlgHom_algebraMap_X (h3 : IsUnit (3 : R)) :
    addTwoDivSubOneAlgHom h3 (algebraMap R[X] (LevelThreeRing R) X) =
      algebraMap R[X] (LevelThreeRing R) X := by
  set m := mu R
  set x := addTwoDivSubOne h3
  set u := algebraMap R[X] (LevelThreeRing R) X
  have hx : x * (m - 1) = m + 2 := addTwoDivSubOne_mul h3
  have e : x ^ 3 * (m - 1) ^ 3 = (m + 2) ^ 3 := by rw [← mul_pow, hx]
  have rel : m ^ 3 * (m ^ 3 + 8) ^ 3 = u * (m ^ 3 - 1) ^ 3 :=
    mu_pow_three_mul_mu_pow_three_add_eight_pow_three R
  have h := map_algebraMap_X_mul (addTwoDivSubOneAlgHom h3).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, addTwoDivSubOneAlgHom_mu] at h
  refine ((isUnit_addTwoDivSubOne_pow_three_sub_one h3).pow 3).mul_right_cancel ?_
  rw [h]
  refine ((isUnit_mu_sub_one h3).pow 12).mul_right_cancel ?_
  calc x ^ 3 * (x ^ 3 + 8) ^ 3 * (m - 1) ^ 12
      = x ^ 3 * (m - 1) ^ 3 * (x ^ 3 * (m - 1) ^ 3 + 8 * (m - 1) ^ 3) ^ 3 := by ring
    _ = (m + 2) ^ 3 * ((m + 2) ^ 3 + 8 * (m - 1) ^ 3) ^ 3 := by rw [e]
    _ = u * (m - 1) ^ 3 * ((m + 2) ^ 3 - (m - 1) ^ 3) ^ 3 := by linear_combination 729 * rel
    _ = u * (m - 1) ^ 3 * (x ^ 3 * (m - 1) ^ 3 - (m - 1) ^ 3) ^ 3 := by rw [e]
    _ = u * (x ^ 3 - 1) ^ 3 * (m - 1) ^ 12 := by ring

/-- The substitution `μ ↦ (μ + 2) / (μ - 1)` is an involution. -/
private theorem addTwoDivSubOneAlgHom_comp_addTwoDivSubOneAlgHom (h3 : IsUnit (3 : R)) :
    ((addTwoDivSubOneAlgHom h3).toPolynomialAlgHom (addTwoDivSubOneAlgHom_algebraMap_X h3)).comp
      ((addTwoDivSubOneAlgHom h3).toPolynomialAlgHom (addTwoDivSubOneAlgHom_algebraMap_X h3)) =
      AlgHom.id R[X] _ := by
  refine algHom_ext' ?_
  simp only [AlgHom.comp_apply, AlgHom.toPolynomialAlgHom_apply, AlgHom.id_apply,
    addTwoDivSubOneAlgHom_mu]
  set m := mu R
  set x := addTwoDivSubOne h3
  have hx : x * (m - 1) = m + 2 := addTwoDivSubOne_mul h3
  -- applying the substitution to `x (μ - 1) = μ + 2` gives `σ(x) (x - 1) = x + 2`
  have hσx : addTwoDivSubOneAlgHom h3 x * (x - 1) = x + 2 := by
    have h := congrArg (addTwoDivSubOneAlgHom h3) hx
    rwa [map_mul, map_sub, map_add, map_one, map_ofNat, addTwoDivSubOneAlgHom_mu] at h
  -- and `x - 1 = 3 / (μ - 1)` is a unit with `μ (x - 1) = x + 2`
  have h3' : IsUnit (3 : LevelThreeRing R) := by
    simpa [map_ofNat] using h3.map (algebraMap R (LevelThreeRing R))
  have hx1 : IsUnit (x - 1) := by
    refine isUnit_of_mul_isUnit_left (y := m - 1) ?_
    convert h3' using 1
    linear_combination hx
  refine hx1.mul_right_cancel ?_
  rw [hσx]
  refine (isUnit_mu_sub_one h3).mul_right_cancel ?_
  linear_combination (1 - m) * hx

/-- The **involution** `μ ↦ (μ + 2) / (μ - 1)` of the level-three line, an automorphism of the
level-three ring over the `u`-line when `3` is invertible. -/
noncomputable def addTwoDivSubOneAut (h3 : IsUnit (3 : R)) :
    LevelThreeRing R ≃ₐ[R[X]] LevelThreeRing R :=
  AlgEquiv.ofAlgHom _ _ (addTwoDivSubOneAlgHom_comp_addTwoDivSubOneAlgHom h3)
    (addTwoDivSubOneAlgHom_comp_addTwoDivSubOneAlgHom h3)

@[simp]
theorem addTwoDivSubOneAut_mu (h3 : IsUnit (3 : R)) :
    addTwoDivSubOneAut h3 (mu R) = (mu R + 2) * ↑(isUnit_mu_sub_one h3).unit⁻¹ := by
  simp [addTwoDivSubOneAut, addTwoDivSubOneAlgHom_mu, addTwoDivSubOne]

theorem addTwoDivSubOneAut_mu_mul_mu_sub_one (h3 : IsUnit (3 : R)) :
    addTwoDivSubOneAut h3 (mu R) * (mu R - 1) = mu R + 2 := by
  rw [addTwoDivSubOneAut_mu, mul_assoc, (isUnit_mu_sub_one h3).val_inv_mul, mul_one]

@[simp]
theorem addTwoDivSubOneAut_addTwoDivSubOneAut (h3 : IsUnit (3 : R)) (a : LevelThreeRing R) :
    addTwoDivSubOneAut h3 (addTwoDivSubOneAut h3 a) = a :=
  congr($(addTwoDivSubOneAlgHom_comp_addTwoDivSubOneAlgHom h3) a)

/-- The **tetrahedral group** of the level-three line: for a root `ζ` of `T² + T + 1`, the group of
automorphisms of the level-three ring over the `u`-line generated by the rotation `μ ↦ ζ μ` and the
involution `μ ↦ (μ + 2) / (μ - 1)`. Its elements are the twelve substitutions `τ^a` and
`τ^a σ τ^b`, `a, b < 3` (`TauCeti.LevelThreeRing.mem_tetrahedralGroup_iff`), and, when `2` is a
nonzerodivisor, its ring of invariants is `R[u]`
(`TauCeti.LevelThreeRing.isInvariant_tetrahedralGroup`). -/
noncomputable def tetrahedralGroup (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (h3 : IsUnit (3 : R)) :
    Subgroup (LevelThreeRing R ≃ₐ[R[X]] LevelThreeRing R) :=
  Subgroup.closure
    {rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ), addTwoDivSubOneAut h3}

theorem rotationAut_mem_tetrahedralGroup {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) (h3 : IsUnit (3 : R)) :
    rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ∈ tetrahedralGroup ζ hζ h3 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem addTwoDivSubOneAut_mem_tetrahedralGroup {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (h3 : IsUnit (3 : R)) : addTwoDivSubOneAut h3 ∈ tetrahedralGroup ζ hζ h3 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- The rotation `μ ↦ ζ μ` has order dividing three. -/
theorem rotationAut_pow_three (ζ : R) (hζ : ζ ^ 3 = 1) : rotationAut ζ hζ ^ 3 = 1 := by
  refine AlgEquiv.coe_toAlgHom_injective (algHom_ext' ?_)
  have hω : algebraMap R (LevelThreeRing R) ζ ^ 3 = 1 := by rw [← map_pow, hζ, map_one]
  have hτω : rotationAut ζ hζ (algebraMap R (LevelThreeRing R) ζ) =
      algebraMap R (LevelThreeRing R) ζ := (rotationAut ζ hζ).toAlgHom.map_algebraMap ζ
  simp only [AlgEquiv.coe_toAlgHom, pow_succ, pow_zero, one_mul, AlgEquiv.mul_apply,
    rotationAut_mu, map_mul, hτω, AlgEquiv.one_apply]
  linear_combination mu R * hω

/-- The rotation `τ : μ ↦ ζ μ` and the involution `σ : μ ↦ (μ + 2) / (μ - 1)` satisfy
`σ τ σ = τ² σ τ²` when `ζ² + ζ + 1 = 0`: both send `μ` to `ζ² (ζ² μ + 2) / (ζ² μ - 1)`. -/
theorem addTwoDivSubOneAut_mul_rotationAut_mul_addTwoDivSubOneAut {ζ : R}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (h3 : IsUnit (3 : R)) :
    addTwoDivSubOneAut h3 * rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) *
        addTwoDivSubOneAut h3 =
      rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ^ 2 * addTwoDivSubOneAut h3 *
        rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ^ 2 := by
  refine AlgEquiv.coe_toAlgHom_injective (algHom_ext' ?_)
  have hζ3 := pow_three_eq_one_of_sq_add_add_one_eq_zero hζ
  set τ := rotationAut ζ hζ3
  set σ := addTwoDivSubOneAut h3
  set m := mu R
  set ω := algebraMap R (LevelThreeRing R) ζ
  have hω : ω ^ 2 + ω + 1 = 0 := by simpa [ω] using congrArg (algebraMap R (LevelThreeRing R)) hζ
  have hτω : τ ω = ω := τ.toAlgHom.map_algebraMap ζ
  have hσω : σ ω = ω := σ.toAlgHom.map_algebraMap ζ
  have hτm : τ m = ω * m := rotationAut_mu ζ hζ3
  have hD := isUnit_mu_pow_three_sub_one R h3
  -- `s = σ μ`, `t = τ s` and `t₂ = τ t` satisfy the transforms of `s (μ - 1) = μ + 2`
  set s := σ m
  have hs : s * (m - 1) = m + 2 := addTwoDivSubOneAut_mu_mul_mu_sub_one h3
  have ht : τ s * (ω * m - 1) = ω * m + 2 := by
    simpa [hτm, map_ofNat] using congrArg τ hs
  have ht₂ : τ (τ s) * (ω * (ω * m) - 1) = ω * (ω * m) + 2 := by
    simpa [hτm, hτω, map_ofNat] using congrArg τ ht
  have hℓ : σ (τ s) * (ω * s - 1) = ω * s + 2 := by
    simpa [hσω, map_ofNat] using congrArg σ ht
  -- the three factors of the common denominator are units
  have hu₁ : IsUnit (ω * (ω * m) - 1) := isUnit_of_mul_isUnit_left
    (y := (ω * (ω * m)) ^ 2 + ω * (ω * m) + 1) (by
      convert hD using 1
      linear_combination (m ^ 3 * (ω ^ 3 + 1) * (ω - 1)) * hω)
  have hω₁ : IsUnit (ω - 1) := isUnit_of_mul_isUnit_left (y := ω + 2) (by
    convert (h3.map (algebraMap R (LevelThreeRing R))).neg using 1
    rw [map_ofNat]
    linear_combination hω)
  have hu₂ : IsUnit (ω * s - 1) := by
    refine isUnit_of_mul_isUnit_left (y := m - 1) ?_
    have hmω : IsUnit (m - ω) := isUnit_of_mul_isUnit_left (y := m ^ 2 + ω * m + ω ^ 2) (by
      convert hD using 1
      linear_combination (1 - ω) * hω)
    convert hω₁.mul hmω using 1
    linear_combination ω * hs + hω
  simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.mul_apply, pow_two, hτm, map_mul, hτω, hσω]
  refine ((hu₂.mul hu₁).mul (isUnit_mu_sub_one h3)).mul_right_cancel ?_
  linear_combination (ω * (ω * m) - 1) * (m - 1) * hℓ - ω ^ 2 * (ω * s - 1) * (m - 1) * ht₂ +
    (ω * (ω ^ 2 * m - 1) - ω ^ 3 * (ω ^ 2 * m + 2)) * hs +
    (-ω ^ 3 * m ^ 2 - 2 * ω ^ 3 * m + 2 * ω ^ 2 * m ^ 2 + ω ^ 2 * m - 4 * ω + ω * m + 2 -
      2 * m) * hω

/-- The tetrahedral group consists of the twelve substitutions `τ^a` and `τ^a σ τ^b`, for
`a, b < 3`, where `τ : μ ↦ ζ μ` and `σ : μ ↦ (μ + 2) / (μ - 1)`. This follows from the relations
`τ³ = σ² = 1` and `σ τ σ = τ² σ τ²` alone (`Subgroup.mem_closure_pair_iff_of_tetrahedral`). -/
theorem mem_tetrahedralGroup_iff {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) (h3 : IsUnit (3 : R))
    {g : LevelThreeRing R ≃ₐ[R[X]] LevelThreeRing R} :
    g ∈ tetrahedralGroup ζ hζ h3 ↔ ∃ a < 3, ∃ b < 3,
      g = rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ^ a ∨
        g = rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ^ a *
          addTwoDivSubOneAut h3 *
          rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ^ b :=
  Subgroup.mem_closure_pair_iff_of_tetrahedral (rotationAut_pow_three ζ _)
    (AlgEquiv.ext (addTwoDivSubOneAut_addTwoDivSubOneAut h3))
    (addTwoDivSubOneAut_mul_rotationAut_mul_addTwoDivSubOneAut hζ h3)

instance {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) (h3 : IsUnit (3 : R)) :
    Finite (tetrahedralGroup ζ hζ h3) := by
  set τ := rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)
  set σ := addTwoDivSubOneAut h3
  refine Set.Finite.to_subtype <| ((Set.finite_range fun a : Fin 3 ↦ τ ^ (a : ℕ)).union
    (Set.finite_range fun p : Fin 3 × Fin 3 ↦ τ ^ (p.1 : ℕ) * σ * τ ^ (p.2 : ℕ))).subset ?_
  intro g hg
  obtain ⟨a, ha, b, hb, h | h⟩ := (mem_tetrahedralGroup_iff hζ h3).mp hg
  · exact Or.inl ⟨⟨a, ha⟩, h.symm⟩
  · exact Or.inr ⟨(⟨a, ha⟩, ⟨b, hb⟩), h.symm⟩

section invariants

variable {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0)

/-- The sum `y + τ y + τ² y` over the rotations `τ : μ ↦ ζ μ`. -/
private noncomputable def rotationSum : LevelThreeRing R →ₗ[R[X]] LevelThreeRing R :=
  let τ := (rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)).toLinearMap
  LinearMap.id + τ + τ ∘ₗ τ

private theorem rotationSum_apply (y : LevelThreeRing R) :
    rotationSum hζ y = y + rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) y +
      rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)
        (rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) y) :=
  rfl

/-- The rotation fixes `μ³`. -/
private theorem rotationAut_mu_pow_three :
    rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) (mu R ^ 3) = mu R ^ 3 := by
  rw [map_pow, rotationAut_mu, mul_pow, ← map_pow, pow_three_eq_one_of_sq_add_add_one_eq_zero hζ,
    map_one, one_mul]

/-- Writing a point of the level-three ring as `A + μ B + μ² C` with `A`, `B`, `C` fixed by the
rotation, the rotation sum keeps `3 A`. -/
private theorem rotationSum_add_mu_mul_add_mu_sq_mul {A B C : LevelThreeRing R}
    (hA : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) A = A)
    (hB : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) B = B)
    (hC : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) C = C) :
    rotationSum hζ (A + mu R * B + mu R ^ 2 * C) = 3 * A := by
  have hτω : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)
      (algebraMap R (LevelThreeRing R) ζ) = algebraMap R (LevelThreeRing R) ζ :=
    (rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)).toAlgHom.map_algebraMap ζ
  simp only [rotationSum_apply, map_add, map_mul, map_pow, rotationAut_mu, hA, hB, hC, hτω]
  set ω := algebraMap R (LevelThreeRing R) ζ
  have hω : ω ^ 2 + ω + 1 = 0 := by
    simpa [ω] using congrArg (algebraMap R (LevelThreeRing R)) hζ
  linear_combination (mu R * B + mu R ^ 2 * C * (1 - ω + ω ^ 2)) * hω

/-- The rotation sum is linear over the points fixed by the rotation. -/
private theorem rotationSum_mul {y c : LevelThreeRing R}
    (hc : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) c = c) :
    rotationSum hζ (y * c) = rotationSum hζ y * c := by
  simp only [rotationSum_apply, map_mul, hc]
  ring

/-- The rotation sum of a square, `(A + μ B + μ² C)² = (A² + 2 μ³ B C) + μ (⋯) + μ² (⋯)`. -/
private theorem rotationSum_add_mu_mul_add_mu_sq_mul_pow_two {A B C ν : LevelThreeRing R}
    (hA : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) A = A)
    (hB : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) B = B)
    (hC : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) C = C)
    (hν : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ν = ν)
    (hμν : mu R ^ 3 = ν) :
    rotationSum hζ ((A + mu R * B + mu R ^ 2 * C) ^ 2) = 3 * (A ^ 2 + 2 * ν * B * C) := by
  have hsq : (A + mu R * B + mu R ^ 2 * C) ^ 2 = (A ^ 2 + 2 * ν * B * C) +
      mu R * (2 * A * B + ν * C ^ 2) + mu R ^ 2 * (B ^ 2 + 2 * A * C) := by
    rw [← hμν]; ring
  rw [hsq]
  exact rotationSum_add_mu_mul_add_mu_sq_mul hζ (by simp [hA, hB, hC, hν, map_ofNat])
    (by simp [hA, hB, hC, hν, map_ofNat]) (by simp [hA, hB, hC, map_ofNat])

/-- The rotation sum of a cube, whose `μ³`-part is `A³ + μ³ B³ + μ⁶ C³ + 6 μ³ A B C`. -/
private theorem rotationSum_add_mu_mul_add_mu_sq_mul_pow_three {A B C ν : LevelThreeRing R}
    (hA : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) A = A)
    (hB : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) B = B)
    (hC : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) C = C)
    (hν : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) ν = ν)
    (hμν : mu R ^ 3 = ν) :
    rotationSum hζ ((A + mu R * B + mu R ^ 2 * C) ^ 3) =
      3 * (A ^ 3 + ν * B ^ 3 + ν ^ 2 * C ^ 3 + 6 * ν * A * B * C) := by
  have hcube : (A + mu R * B + mu R ^ 2 * C) ^ 3 =
      (A ^ 3 + ν * B ^ 3 + ν ^ 2 * C ^ 3 + 6 * ν * A * B * C) +
      mu R * (3 * A ^ 2 * B + 3 * ν * B ^ 2 * C + 3 * ν * A * C ^ 2) +
      mu R ^ 2 * (3 * A ^ 2 * C + 3 * A * B ^ 2 + 3 * ν * B * C ^ 2) := by
    rw [← hμν]; ring
  rw [hcube]
  exact rotationSum_add_mu_mul_add_mu_sq_mul hζ (by simp [hA, hB, hC, hν, map_ofNat])
    (by simp [hA, hB, hC, hν, map_ofNat]) (by simp [hA, hB, hC, hν, map_ofNat])

variable (h3 : IsUnit (3 : R))

/-- Let `w = σ(μ)³ = ((μ + 2) / (μ - 1))³`. Since `w (μ³ - 1)³ = (μ + 2)³ (μ² + μ + 1)³` is
`A + μ B + μ² C` with `A`, `B`, `C` polynomials in `μ³`, and the rotation fixes `μ³ - 1`, the
rotation sums of `w`, `w²` and `w³`, multiplied by powers of `μ³ - 1`, are three times the
`μ³`-parts of `A + μ B + μ² C` and of its square and cube. -/
private theorem rotationSum_addTwoDivSubOneAut_mu_pow_three_pow_mul :
    let m := mu R
    let A := (m ^ 3) ^ 3 + 87 * (m ^ 3) ^ 2 + 147 * m ^ 3 + 8
    let B := 36 * (m ^ 3) ^ 2 + 171 * m ^ 3 + 36
    let C := 9 * (m ^ 3) ^ 2 + 144 * m ^ 3 + 90
    let w := addTwoDivSubOneAut h3 m ^ 3
    rotationSum hζ w * (m ^ 3 - 1) ^ 3 = 3 * A ∧
      rotationSum hζ (w ^ 2) * (m ^ 3 - 1) ^ 6 = 3 * (A ^ 2 + 2 * m ^ 3 * B * C) ∧
      rotationSum hζ (w ^ 3) * (m ^ 3 - 1) ^ 9 =
        3 * (A ^ 3 + m ^ 3 * B ^ 3 + (m ^ 3) ^ 2 * C ^ 3 + 6 * m ^ 3 * A * B * C) := by
  intro m A B C w
  set τ := rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)
  have hx : addTwoDivSubOneAut h3 m * (m - 1) = m + 2 := addTwoDivSubOneAut_mu_mul_mu_sub_one h3
  have hν : τ (m ^ 3) = m ^ 3 := rotationAut_mu_pow_three hζ
  -- `μ³ - 1 = (μ - 1) (μ² + μ + 1)`, so `w (μ³ - 1)³ = (μ + 2)³ (μ² + μ + 1)³`
  have hwm : w * (m ^ 3 - 1) ^ 3 =
      (addTwoDivSubOneAut h3 m * (m - 1)) ^ 3 * (m ^ 2 + m + 1) ^ 3 := by ring
  have hwD : w * (m ^ 3 - 1) ^ 3 = A + m * B + m ^ 2 * C := by
    rw [hwm, hx]
    ring
  -- the rotation fixes every polynomial in `μ³`
  have hA : τ A = A := by
    simp only [A]; generalize m ^ 3 = ν at hν ⊢; simp [hν, map_ofNat]
  have hB : τ B = B := by
    simp only [B]; generalize m ^ 3 = ν at hν ⊢; simp [hν, map_ofNat]
  have hC : τ C = C := by
    simp only [C]; generalize m ^ 3 = ν at hν ⊢; simp [hν, map_ofNat]
  have hDk (k : ℕ) : τ ((m ^ 3 - 1) ^ k) = (m ^ 3 - 1) ^ k := by
    generalize m ^ 3 = ν at hν ⊢; simp [hν]
  have hw2 : w ^ 2 * (m ^ 3 - 1) ^ 6 = (w * (m ^ 3 - 1) ^ 3) ^ 2 := by ring
  have hw3 : w ^ 3 * (m ^ 3 - 1) ^ 9 = (w * (m ^ 3 - 1) ^ 3) ^ 3 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← rotationSum_mul hζ (hDk 3), hwD, rotationSum_add_mu_mul_add_mu_sq_mul hζ hA hB hC]
  · rw [← rotationSum_mul hζ (hDk 6), hw2, hwD,
      rotationSum_add_mu_mul_add_mu_sq_mul_pow_two hζ hA hB hC hν rfl]
  · rw [← rotationSum_mul hζ (hDk 9), hw3, hwD,
      rotationSum_add_mu_mul_add_mu_sq_mul_pow_three hζ hA hB hC hν rfl]

/-- **The power sums of the orbit of `μ³`.** With `w = σ(μ)³ = ((μ + 2) / (μ - 1))³`, the four
points `μ³`, `w`, `τ w`, `τ² w` are the conjugates of `μ³`, the roots of
`V (V + 8)³ - u (V - 1)³`, whose elementary symmetric functions are `u - 24`, `3 u + 192`,
`3 u - 512` and `u`. Their first three power sums are `u - 24`, `u² - 54 u + 192` and
`u³ - 81 u² + 1377 u - 1536`. -/
private theorem rotationSum_addTwoDivSubOneAut_mu_pow_three_pow :
    rotationSum hζ (addTwoDivSubOneAut h3 (mu R) ^ 3) + mu R ^ 3 =
        algebraMap R[X] (LevelThreeRing R) (X - 24) ∧
      rotationSum hζ ((addTwoDivSubOneAut h3 (mu R) ^ 3) ^ 2) + (mu R ^ 3) ^ 2 =
        algebraMap R[X] (LevelThreeRing R) (X ^ 2 - 54 * X + 192) ∧
      rotationSum hζ ((addTwoDivSubOneAut h3 (mu R) ^ 3) ^ 3) + (mu R ^ 3) ^ 3 =
        algebraMap R[X] (LevelThreeRing R) (X ^ 3 - 81 * X ^ 2 + 1377 * X - 1536) := by
  obtain ⟨hT₁, hT₂, hT₃⟩ := rotationSum_addTwoDivSubOneAut_mu_pow_three_pow_mul hζ h3
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  set u := algebraMap R[X] (LevelThreeRing R) X
  set R₀ := mu R ^ 3 * (mu R ^ 3 + 8) ^ 3
  set D := mu R ^ 3 - 1
  have rel : R₀ = u * D ^ 3 := mu_pow_three_mul_mu_pow_three_add_eight_pow_three R
  have hD : IsUnit D := isUnit_mu_pow_three_sub_one R h3
  -- cancel the unit `(μ³ - 1)^{3k}` and use `μ³ (μ³ + 8)³ = u (μ³ - 1)³`
  refine ⟨(hD.pow 3).mul_right_cancel ?_, (hD.pow 6).mul_right_cancel ?_,
    (hD.pow 9).mul_right_cancel ?_⟩
  · linear_combination hT₁ + rel
  · linear_combination hT₂ + (R₀ + u * D ^ 3 - 54 * D ^ 3) * rel
  · linear_combination hT₃ +
      (1377 * D ^ 6 - 81 * D ^ 3 * (R₀ + u * D ^ 3) + R₀ ^ 2 + R₀ * u * D ^ 3 + u ^ 2 * D ^ 6) *
        rel

/-- The sum of a point of the level-three ring over the twelve substitutions `τ^a` and
`τ^a σ τ^b` (`a, b ∈ {0, 1, 2}`) of the tetrahedral group, where `τ : μ ↦ ζ μ` and
`σ : μ ↦ (μ + 2) / (μ - 1)`. -/
private noncomputable def orbitSum : LevelThreeRing R →ₗ[R[X]] LevelThreeRing R :=
  rotationSum hζ + rotationSum hζ ∘ₗ (addTwoDivSubOneAut h3).toLinearMap ∘ₗ rotationSum hζ

private theorem orbitSum_apply (y : LevelThreeRing R) :
    orbitSum hζ h3 y =
      rotationSum hζ y + rotationSum hζ (addTwoDivSubOneAut h3 (rotationSum hζ y)) :=
  rfl

/-- The orbit sum of every basis vector `μ ^ k`, `k < 12`, lies in `R[u]`: it vanishes unless
`3 ∣ k`, and for `k = 3 j` it is three times the `j`-th power sum of the orbit of `μ³`. -/
private theorem orbitSum_mu_pow_mem {k : ℕ} (hk : k < 12) :
    orbitSum hζ h3 (mu R ^ k) ∈ (1 : Submodule R[X] (LevelThreeRing R)) := by
  set τ := rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ)
  have hfix (j : ℕ) : τ ((mu R ^ 3) ^ j) = (mu R ^ 3) ^ j := by
    rw [map_pow, rotationAut_mu_pow_three hζ]
  have h3fix : τ 3 = 3 := map_ofNat τ 3
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 3 ∧ k = 3 * j + r :=
    ⟨k / 3, k % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 3).symm⟩
  rw [pow_add, pow_mul, Submodule.mem_one]
  interval_cases r
  · -- `k = 3 j`: the orbit sum is `3 (μ^{3j} + Σ (τ^b w)^j)` with `w = σ(μ)³`
    have hT : rotationSum hζ ((mu R ^ 3) ^ j * mu R ^ 0) = 3 * (mu R ^ 3) ^ j := by
      simpa using rotationSum_add_mu_mul_add_mu_sq_mul hζ (A := (mu R ^ 3) ^ j) (B := 0) (C := 0)
        (hfix j) (map_zero τ) (map_zero τ)
    have hO : orbitSum hζ h3 ((mu R ^ 3) ^ j * mu R ^ 0) =
        3 * (rotationSum hζ ((addTwoDivSubOneAut h3 (mu R) ^ 3) ^ j) + (mu R ^ 3) ^ j) := by
      have h3mul (y : LevelThreeRing R) : rotationSum hζ (3 * y) = 3 * rotationSum hζ y := by
        rw [mul_comm, rotationSum_mul hζ h3fix, mul_comm]
      rw [orbitSum_apply, hT, map_mul, map_ofNat, map_pow, map_pow, h3mul]
      ring
    rw [hO]
    obtain ⟨h₁, h₂, h₃⟩ := rotationSum_addTwoDivSubOneAut_mu_pow_three_pow hζ h3
    have hj : j < 4 := by omega
    interval_cases j
    · refine ⟨12, ?_⟩
      simp only [pow_zero, rotationSum_apply, map_one, map_ofNat]
      norm_num
    · exact ⟨3 * (X - 24), by rw [pow_one, pow_one, h₁, map_mul, map_ofNat]⟩
    · exact ⟨3 * (X ^ 2 - 54 * X + 192), by rw [h₂, map_mul, map_ofNat]⟩
    · exact ⟨3 * (X ^ 3 - 81 * X ^ 2 + 1377 * X - 1536), by rw [h₃, map_mul, map_ofNat]⟩
  · -- `k = 3 j + 1`: the rotation sum already vanishes
    refine ⟨0, ?_⟩
    have hT : rotationSum hζ ((mu R ^ 3) ^ j * mu R ^ 1) = 0 := by
      simpa [mul_comm] using rotationSum_add_mu_mul_add_mu_sq_mul hζ (A := 0)
        (B := (mu R ^ 3) ^ j) (C := 0) (map_zero τ) (hfix j) (map_zero τ)
    rw [map_zero, orbitSum_apply, hT, map_zero, map_zero, add_zero]
  · -- `k = 3 j + 2`: the rotation sum already vanishes
    refine ⟨0, ?_⟩
    have hT : rotationSum hζ ((mu R ^ 3) ^ j * mu R ^ 2) = 0 := by
      simpa [mul_comm] using rotationSum_add_mu_mul_add_mu_sq_mul hζ (A := 0) (B := 0)
        (C := (mu R ^ 3) ^ j) (map_zero τ) (map_zero τ) (hfix j)
    rw [map_zero, orbitSum_apply, hT, map_zero, map_zero, add_zero]

end invariants

/-- **The invariants of the tetrahedral group.** Let `ζ` be a root of `T² + T + 1` in `R`, and
suppose that `3` is invertible and `2` is a nonzerodivisor in `R`. A point of the level-three ring
fixed by the rotation `μ ↦ ζ μ` and the involution `μ ↦ (μ + 2) / (μ - 1)` lies in `R[u]`. Thus
the `u`-line, which is the `j`-line since `j = 27 u`, is the quotient of the level-three line by
the tetrahedral group. -/
theorem isInvariant_tetrahedralGroup {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) (h3 : IsUnit (3 : R))
    (h2 : (2 : R) ∈ nonZeroDivisors R) :
    Algebra.IsInvariant R[X] (LevelThreeRing R) (tetrahedralGroup ζ hζ h3) := by
  refine ⟨fun a ha => ?_⟩
  have hτ : rotationAut ζ (pow_three_eq_one_of_sq_add_add_one_eq_zero hζ) a = a :=
    ha ⟨_, rotationAut_mem_tetrahedralGroup hζ h3⟩
  have hσ : addTwoDivSubOneAut h3 a = a := ha ⟨_, addTwoDivSubOneAut_mem_tetrahedralGroup hζ h3⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (LevelThreeRing R)
    exact ⟨0, Subsingleton.elim _ _⟩
  let pb : PowerBasis R[X] (LevelThreeRing R) :=
    AdjoinRoot.powerBasis' (monic_levelThreeRelation R)
  have hdim : pb.dim = 12 :=
    (AdjoinRoot.powerBasis'_dim _).trans (natDegree_levelThreeRelation R)
  have hgen : pb.gen = mu R := AdjoinRoot.powerBasis'_gen _
  -- The orbit sum of `a` is `12 a`, and it lies in `R[u]`.
  obtain ⟨c, hc⟩ : ∃ c, algebraMap R[X] (LevelThreeRing R) c = (12 : R[X]) • a := by
    refine Submodule.mem_one.mp ?_
    have : orbitSum hζ h3 a = (12 : R[X]) • a := by
      simp only [orbitSum_apply, rotationSum_apply, map_add, hτ, hσ, Algebra.smul_def, map_ofNat]
      ring
    rw [← this, ← pb.basis.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, pb.basis_eq_pow, hgen]
    exact Submodule.smul_mem _ _ (orbitSum_mu_pow_mem hζ h3 (hdim ▸ j.2))
  -- Since `12` is a nonzerodivisor, `a` itself lies in `R[u]`.
  have h12 : (12 : R[X]) ∈ nonZeroDivisors R[X] := by
    refine mem_nonZeroDivisors_of_coeff_mem 0 ?_
    have : (12 : R) = 2 * 2 * 3 := by norm_num
    simpa [this] using mul_mem (mul_mem h2 h2) h3.mem_nonZeroDivisors
  exact pb.exists_algebraMap_eq_of_algebraMap_eq_smul h12 hc

end tetrahedral

end LevelThreeRing

end TauCeti
