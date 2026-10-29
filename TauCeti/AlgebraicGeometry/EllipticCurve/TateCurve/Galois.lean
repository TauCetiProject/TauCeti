/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The Tate uniformisation over extensions: compatibility and Galois equivariance

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`, so that the Tate
curve `E_q` is an elliptic curve over `K`. For a complete normed extension `L` of `K`, the Tate
coordinates over `L` give a map

```text
tateUniformizationBaseChange L q hq : Lˣ / q^ℤ → E_q(L),
```

valued in the points of the base change of `E_q` to `L`. On this curve, Mathlib's
`WeierstrassCurve.Affine.Point.map` lets a `K`-algebra map `ι : L → M` act on points, and
`ι` acts on parameters through `tateParameterMap q ι : Lˣ / q^ℤ → Mˣ / q^ℤ`. The uniformisation
**commutes with every continuous `K`-algebra map** (`map_tateUniformizationBaseChange`). Every
`K`-automorphism of an algebraic extension preserves the spectral norm, which is the norm of `L`,
so it is continuous and the uniformisation is **Galois-equivariant**
(`map_algEquiv_tateUniformizationBaseChange`). On classes coming from `Kˣ / q^ℤ`, it is the
base change to `L` of `tateUniformization` over `K`
(`tateUniformizationBaseChange_tateParameterBaseChange`).

Unlike `tateParameterBaseChange f q`, whose target is the quotient by `f q`, the map
`tateParameterMap q ι` lands in the quotient by the image of `q ∈ K` in `M`. So for `M = L` it
is an endomorphism of `Lˣ / q^ℤ`, and the automorphisms of `L/K` act on a single group.

On the parameter side, for a finite Galois extension `L/K` and `q` of infinite order, a class in
`Lˣ / q^ℤ` is fixed by `Gal(L/K)` exactly when it comes from `Kˣ / q^ℤ`
(`mem_range_tateParameterBaseChange_iff`). Indeed if `σ u = u qⁿ`, then `σᵏ u = u q^{kn}`, and
`σ` has finite order. This is the parameter half of Galois descent for the uniformisation: by
equivariance, a point `tateUniformizationBaseChange L q hq x` fixed by `Gal(L/K)` has a fixed
parameter `x`, and hence one defined over `K`, as soon as the uniformisation is injective.

## Main definitions

* `TauCeti.tateParameterMap`: the map `Lˣ / q^ℤ → Mˣ / q^ℤ` induced by a `K`-algebra map.
* `TauCeti.tateUniformizationBaseChange`: the Tate uniformisation `Lˣ / q^ℤ → E_q(L)`.

## Main results

* `TauCeti.baseChange_tateCurveAt`: the base change of `E_q` to `L` is the Tate curve of the
  image of `q`.
* `TauCeti.map_tateUniformizationBaseChange`: compatibility with continuous `K`-algebra maps.
* `TauCeti.map_algEquiv_tateUniformizationBaseChange`: Galois equivariance.
* `TauCeti.mem_range_tateParameterBaseChange_iff`: the Galois-fixed parameters are those
  defined over `K`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### Maps of multiplicative parameters -/

section Parameters

variable {K L M N : Type*} [CommRing K] [CommRing L] [CommRing M] [CommRing N]
  [Algebra K L] [Algebra K M] [Algebra K N]

/-- A `K`-algebra map fixes the image of a unit of `K`. -/
private theorem units_map_units_map_algebraMap (ι : L →ₐ[K] M) (q : Kˣ) :
    Units.map (ι : L →* M) (Units.map (algebraMap K L : K →* L) q) =
      Units.map (algebraMap K M : K →* M) q :=
  Units.ext (ι.commutes q)

/-- The map `Lˣ / q^ℤ → Mˣ / q^ℤ` induced by a `K`-algebra map `ι : L → M`, for `q ∈ Kˣ`. -/
noncomputable def tateParameterMap (q : Kˣ) (ι : L →ₐ[K] M) :
    Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q) →*
      Mˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K M : K →* M) q) :=
  QuotientGroup.map _ _ (Units.map (ι : L →* M)) <| by
    rw [← Subgroup.map_le_iff_le_comap, MonoidHom.map_zpowers,
      units_map_units_map_algebraMap]

/-- The parameter map sends the class of a unit to the class of its image. -/
@[simp]
theorem tateParameterMap_mk (q : Kˣ) (ι : L →ₐ[K] M) (u : Lˣ) :
    tateParameterMap q ι (u : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) =
      (Units.map (ι : L →* M) u :
        Mˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K M : K →* M) q)) :=
  QuotientGroup.map_mk _ _ _ _ u

/-- The identity map acts trivially on parameters. -/
@[simp]
theorem tateParameterMap_id (q : Kˣ) :
    tateParameterMap q (AlgHom.id K L) = MonoidHom.id _ := by
  ext u
  simpa using congrArg _ (Units.ext (by simp))

/-- The parameter map is functorial. -/
theorem tateParameterMap_comp (q : Kˣ) (ι : L →ₐ[K] M) (κ : M →ₐ[K] N) :
    tateParameterMap q (κ.comp ι) = (tateParameterMap q κ).comp (tateParameterMap q ι) := by
  ext u
  simpa using congrArg _ (Units.ext (by simp))

/-- The parameter map is compatible with base change from `K`. -/
@[simp]
theorem tateParameterMap_tateParameterBaseChange (q : Kˣ) (ι : L →ₐ[K] M)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateParameterMap q ι (tateParameterBaseChange (algebraMap K L) q x) =
      tateParameterBaseChange (algebraMap K M) q x := by
  induction x using QuotientGroup.induction_on with
  | H u => simpa using congrArg _ (Units.ext (by simp))

/-- An injective `K`-algebra map induces an injective map on parameters. -/
theorem tateParameterMap_injective (q : Kˣ) {ι : L →ₐ[K] M} (hι : Function.Injective ι) :
    Function.Injective (tateParameterMap q ι) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [tateParameterMap_mk, QuotientGroup.eq_one_iff] at hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine (QuotientGroup.eq_one_iff u).mpr <| Subgroup.mem_zpowers_iff.mpr
      ⟨n, Units.map_injective (f := (ι : L →* M)) hι ?_⟩
    rwa [map_zpow, units_map_units_map_algebraMap]

end Parameters

/-! ### Galois-fixed parameters -/

section Fixed

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If a `K`-automorphism `σ` moves `u` by `σ u = u qⁿ` for `q ∈ K`, its powers move `u` by
`σᵏ u = u q^{kn}`. -/
private theorem pow_apply_eq_mul_zpow (σ : L ≃ₐ[K] L) (q : Kˣ) (u : L) (n : ℤ)
    (h : σ u = u * algebraMap K L q ^ n) (k : ℕ) :
    (σ ^ k) u = u * algebraMap K L q ^ ((k : ℤ) * n) := by
  have hq : algebraMap K L q ≠ 0 := by simp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgEquiv.mul_apply, h, map_mul, ih, map_zpow₀, AlgEquiv.commutes, mul_assoc,
      ← zpow_add₀ hq, Nat.cast_succ, add_one_mul]

/-- **The Galois-fixed Tate parameters are those defined over the ground field.** For a finite
Galois extension `L/K` and `q ∈ Kˣ` of infinite order, a class in `Lˣ / q^ℤ` is fixed by every
`K`-automorphism of `L` exactly when it is the image of a class in `Kˣ / q^ℤ`. -/
theorem mem_range_tateParameterBaseChange_iff [FiniteDimensional K L] [IsGalois K L] {q : Kˣ}
    (hq : ¬ IsOfFinOrder q)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    x ∈ (tateParameterBaseChange (algebraMap K L) q).range ↔
      ∀ σ : L ≃ₐ[K] L, tateParameterMap q (σ : L →ₐ[K] L) x = x := by
  refine ⟨fun ⟨y, hy⟩ σ ↦ hy ▸ tateParameterMap_tateParameterBaseChange q _ y, fun hx ↦ ?_⟩
  induction x using QuotientGroup.induction_on with
  | H u =>
  -- every `σ` moves `u` by a power of `q`, and that power vanishes since `σ` has finite order
  have hfix (σ : L ≃ₐ[K] L) : σ (u : L) = u := by
    have h := hx σ
    rw [tateParameterMap_mk, eq_comm, QuotientGroup.eq] at h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    have hσ : σ (u : L) = u * algebraMap K L q ^ n := by
      simpa [Units.val_zpow_eq_zpow_val] using congrArg Units.val (eq_mul_of_inv_mul_eq hn.symm)
    have hk := pow_apply_eq_mul_zpow σ q u n hσ (orderOf σ)
    rw [pow_orderOf_eq_one, AlgEquiv.one_apply, left_eq_mul₀ u.ne_zero, ← map_zpow₀,
      FaithfulSMul.algebraMap_eq_one_iff, ← Units.val_zpow_eq_zpow_val, Units.val_eq_one] at hk
    have hn : n = 0 := by
      by_contra hn
      exact hq (isOfFinOrder_iff_zpow_eq_one.mpr ⟨_, mul_ne_zero (by
        exact_mod_cast (orderOf_pos σ).ne') hn, hk⟩)
    simpa [hn] using hσ
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp
    ((InfiniteGalois.mem_bot_iff_fixed (u : L)).mpr hfix)
  have hb₀ : b ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by simpa using hb.symm)
  refine ⟨(Units.mk0 b hb₀ : Kˣ), ?_⟩
  rw [tateParameterBaseChange_mk]
  congr 1
  ext
  simpa using hb

end Fixed

/-! ### The uniformisation over an extension -/

variable {K : Type*} [NormedField K] (L : Type*) [NormedField L] [NormedAlgebra K L]

variable [CompleteSpace L] [IsUltrametricDist L] {M : Type*} [NormedField M] [NormedAlgebra K M]

variable {L} in
/-- The Tate coordinates on parameters commute with a continuous `K`-algebra map. -/
theorem tateQuotientCoordinates_tateParameterMap (q : Kˣ) (hq : ‖(q : K)‖ < 1) (ι : L →ₐ[K] M)
    (hι : Continuous ι)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateQuotientCoordinates _ (tateParameterMap q ι x) =
      (ι (tateQuotientCoordinates _ x).1, ι (tateQuotientCoordinates _ x).2) := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    have hq' : ‖((Units.map (algebraMap K L : K →* L) q : Lˣ) : L)‖ < 1 := by simpa using hq
    rw [tateParameterMap_mk, tateQuotientCoordinates_mk, tateQuotientCoordinates_mk]
    have hX := map_tateUniformizationX (ι : L →+* M) hι _ u hq'
    have hY := map_tateUniformizationY (ι : L →+* M) hι _ u hq'
    rw [show Units.map ((ι : L →+* M) : L →* M) (Units.map (algebraMap K L : K →* L) q) =
      Units.map (algebraMap K M : K →* M) q from units_map_units_map_algebraMap ι q] at hX hY
    exact Prod.ext hX.symm hY.symm

variable [CompleteSpace K] [IsUltrametricDist K]

/-- **The base change of the Tate curve is the Tate curve of the image of `q`.** -/
theorem baseChange_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq)⁄L =
      tateCurveAt (Units.map (algebraMap K L : K →* L) q) (by simpa using hq) :=
  haveI : RingHomIsometric (algebraMap K L) := ⟨norm_algebraMap' L _⟩
  map_tateCurveAt (algebraMap K L) q hq

/-- The **Tate uniformisation over an extension** `L` of `K`, the map `Lˣ / q^ℤ → E_q(L)` into the
points of the base change of `E_q` to `L`. It is `tateUniformization` for the image of `q` in `L`,
transported along `baseChange_tateCurveAt`. -/
noncomputable def tateUniformizationBaseChange (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    ((tateCurveAt q hq)⁄L).toAffine.Point :=
  cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point)
    (baseChange_tateCurveAt L q hq).symm)
    (tateUniformization _ ((by simpa using hq)) x)

/-- Exactly the identity parameter maps to infinity. -/
@[simp]
theorem tateUniformizationBaseChange_eq_zero_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateUniformizationBaseChange L q hq x = 0 ↔ x = 1 := by
  rw [← tateUniformization_eq_zero_iff _ ((by simpa using hq)) x,
    ← Point.cast_zero (baseChange_tateCurveAt L q hq).symm, tateUniformizationBaseChange]
  exact cast_inj _

/-- The identity parameter maps to the point at infinity. -/
@[simp]
theorem tateUniformizationBaseChange_one (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateUniformizationBaseChange L q hq 1 = 0 :=
  (tateUniformizationBaseChange_eq_zero_iff L q hq 1).mpr rfl

/-- An affine point is the image of a parameter exactly when both its coordinates are the
Tate coordinates and the parameter is not the identity. -/
@[simp]
theorem tateUniformizationBaseChange_eq_some_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) {a b : L}
    (h : ((tateCurveAt q hq)⁄L).toAffine.Nonsingular a b) :
    tateUniformizationBaseChange L q hq x = .some a b h ↔
      x ≠ 1 ∧ (tateQuotientCoordinates _ x).1 = a ∧ (tateQuotientCoordinates _ x).2 = b := by
  have e := baseChange_tateCurveAt L q hq
  rw [← tateUniformization_eq_some_iff _ ((by simpa using hq)) x (e ▸ h),
    tateUniformizationBaseChange, ← cast_inj (congrArg (fun W : WeierstrassCurve L ↦
      W.toAffine.Point) e), cast_cast, cast_eq, Point.cast_some e]

/-- **The Tate uniformisation is compatible with base change from `K`**: moving the image of a
class of `Kˣ / q^ℤ` to `L` gives the image of the class it defines in `Lˣ / q^ℤ`. -/
theorem tateUniformizationBaseChange_tateParameterBaseChange (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformizationBaseChange L q hq (tateParameterBaseChange (algebraMap K L) q x) =
      Point.mapAlong (algebraMap K L) (algebraMap K L).injective (tateUniformization q hq x) := by
  have : RingHomIsometric (algebraMap K L) := ⟨norm_algebraMap' L _⟩
  rw [tateUniformizationBaseChange, ← mapAlong_tateUniformization (algebraMap K L) q hq x,
    cast_cast]
  -- `(tateCurveAt q hq)⁄L` is `(tateCurveAt q hq).map (algebraMap K L)` by definition, so the
  -- remaining transport is along a definitional equality of point types
  rfl

variable {L} [CompleteSpace M] [IsUltrametricDist M] [DecidableEq L] [DecidableEq M]

/-- **The Tate uniformisation is compatible with continuous maps of extensions**: for a continuous
`K`-algebra map `ι : L → M`, applying `ι` to the image of a parameter `x` gives the image of
`ι x`. -/
theorem map_tateUniformizationBaseChange (q : Kˣ) (hq : ‖(q : K)‖ < 1) (ι : L →ₐ[K] M)
    (hι : Continuous ι)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    Point.map ι (tateUniformizationBaseChange L q hq x) =
      tateUniformizationBaseChange M q hq (tateParameterMap q ι x) := by
  by_cases hx : x = 1
  · simp [hx]
  obtain ⟨a, b, h, hP⟩ := Point.exists_eq_some_of_ne_zero
    ((tateUniformizationBaseChange_eq_zero_iff L q hq x).not.mpr hx)
  obtain ⟨-, ha, hb⟩ := (tateUniformizationBaseChange_eq_some_iff L q hq x h).mp hP
  rw [hP, Point.map_some, eq_comm, tateUniformizationBaseChange_eq_some_iff,
    tateQuotientCoordinates_tateParameterMap q hq ι hι, ha, hb]
  exact ⟨(map_ne_one_iff _ (tateParameterMap_injective q ι.injective)).mpr hx, rfl, rfl⟩

/-- **The Tate uniformisation is Galois-equivariant.** For an algebraic extension `L/K`, every
`K`-automorphism `σ` of `L` is an isometry, and applying `σ` to the image of a parameter `x`
gives the image of `σ x`. -/
theorem map_algEquiv_tateUniformizationBaseChange [Algebra.IsAlgebraic K L] (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) (σ : L ≃ₐ[K] L)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    Point.map (σ : L →ₐ[K] L) (tateUniformizationBaseChange L q hq x) =
      tateUniformizationBaseChange L q hq (tateParameterMap q (σ : L →ₐ[K] L) x) := by
  -- `q` has norm strictly between `0` and `1`, so the norm of `K` is nontrivial
  let := NontriviallyNormedField.ofNormNeOne ⟨(q : K), q.ne_zero, hq.ne⟩
  refine map_tateUniformizationBaseChange q hq _ ?_ x
  refine (AddMonoidHomClass.isometry_of_norm (σ : L →ₐ[K] L) fun y ↦ ?_).continuous
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K]
  exact (spectralNorm_eq_of_equiv σ y).symm

end TauCeti

end
