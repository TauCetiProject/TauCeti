/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Functoriality
public import TauCeti.RingTheory.Localization.AlgHom
public import Mathlib.Topology.Algebra.Constructions

/-!
# Localizations give open embeddings of point spaces

Let `B` be a localization of a commutative `k`-algebra `A` away from `f`, so that `Spec B` is the
basic open subset `D(f)` of `Spec A`. For a topological `k`-algebra `R`, restriction along
`A → B` maps the points `B →ₐ[k] R` injectively onto the points `x : A →ₐ[k] R` with `x f` a unit
(`IsLocalization.Away.range_comp_toAlgHom`). This file compares the point topologies.

* If inversion is continuous on the units of `R` with the subspace topology, that is, if
  `Units.val : Rˣ → R` is an embedding, then the restriction map is an embedding. The value of a
  point of `B` at a fraction `a / fⁿ` is `x a * (x f)⁻¹ ^ n`, which depends continuously on the
  restricted point `x` as long as `x f` stays among the units.
* If moreover the units are open in `R`, then the restriction map is an open embedding.

Both hypotheses are needed: for `A = k[X]` and `f = X`, the points of `A` are identified with `R`,
and the restriction map with the inclusion of the units of `R`. So it is an embedding exactly when
inversion is continuous on the units, and an open embedding exactly when the units are moreover
open. Both hold for fields with a nontrivial absolute value and for complete normed rings, while
both fail for the adeles. The open embeddings of basic open subsets are the gluing input for the
point topology on the points of a scheme over a local topological ring.

## Main results

* `TauCeti.PointTopology.isEmbedding_localization`: restriction to `A` embeds the points of a
  localization away from `f`, when `Units.val : Rˣ → R` is an embedding.
* `TauCeti.PointTopology.isOpenEmbedding_localization`: it is an open embedding when moreover the
  units of `R` are open.
* `TauCeti.PointTopology.localizationAwayXHomeomorph`: the points of the localization of `k[X]`
  away from `X` are homeomorphic to the units of `R`.
* `TauCeti.PointTopology.isEmbedding_localization_X_iff` and
  `TauCeti.PointTopology.isOpenEmbedding_localization_X_iff`: for the localization of `k[X]` away
  from `X`, these hypotheses are also necessary.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §3 and the proof of Prop. 3.1, pp. 3–4.
-/

public section

open Topology

namespace TauCeti.PointTopology

section Sufficiency

variable {k A B R : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A]
  [CommSemiring B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- If inversion is continuous on the units of `R`, restriction to `A` embeds the points of a
localization of `A` away from `f` in the points of `A`. -/
theorem isEmbedding_localization [Semiring R] [Algebra k R] [TopologicalSpace R]
    [ContinuousMul R] (f : A) [IsLocalization.Away f B]
    (hR : IsEmbedding (Units.val : Rˣ → R)) :
    IsEmbedding fun x : B →ₐ[k] R ↦ x.comp (IsScalarTower.toAlgHom k A B) := by
  let U := {y : A →ₐ[k] R | IsUnit (y f)}
  -- Restriction lands in `U`, since `f` is a unit in `B`.
  let r (x : B →ₐ[k] R) : U :=
    ⟨x.comp (IsScalarTower.toAlgHom k A B), (IsLocalization.Away.algebraMap_isUnit f).map x⟩
  have hr : Continuous r := (continuous_comap _).subtype_mk _
  -- On `U`, the inverse of the value at `f` is continuous.
  have hinv : Continuous fun y : U ↦ (↑y.2.unit⁻¹ : R) :=
    Units.continuous_coe_inv.comp <| hR.continuous_iff.2 <|
      (continuous_eval f).comp continuous_subtype_val
  -- Every `b : B` is a fraction `a b / f ^ n b`, so its value is a continuous function on `U`.
  choose n a ha using IsLocalization.Away.surj (S := B) f
  let g (y : U) (b : B) : R := y.1 (a b) * (↑y.2.unit⁻¹ : R) ^ n b
  have hg : Continuous g := continuous_pi fun b ↦
    ((continuous_eval (a b)).comp continuous_subtype_val).mul (hinv.pow (n b))
  have hgr : g ∘ r = fun x : B →ₐ[k] R ↦ (x : B → R) := by
    funext x b
    dsimp only [Function.comp_apply, g]
    rw [← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_eq_iff_eq_mul]
    simp [r, ← ha b]
  exact IsEmbedding.subtypeVal.comp (.of_comp hr hg (hgr ▸ isEmbedding_coeFn))

/-- If the units of `R` are open and inversion is continuous on them, restriction to `A` is an
open embedding of the points of a localization of `A` away from `f` in the points of `A`, onto
the points at which `f` takes a unit value. -/
theorem isOpenEmbedding_localization [CommSemiring R] [Algebra k R] [TopologicalSpace R]
    [ContinuousMul R] (f : A) [IsLocalization.Away f B]
    (hR : IsEmbedding (Units.val : Rˣ → R)) (hU : IsOpen {r : R | IsUnit r}) :
    IsOpenEmbedding fun x : B →ₐ[k] R ↦ x.comp (IsScalarTower.toAlgHom k A B) := by
  refine ⟨isEmbedding_localization f hR, ?_⟩
  rw [IsLocalization.Away.range_comp_toAlgHom f]
  exact hU.preimage (continuous_eval f)

end Sufficiency

section Necessity

open Polynomial

variable {k L R : Type*} [CommSemiring k] [CommSemiring L] [Algebra k L] [Algebra k[X] L]
  [IsScalarTower k k[X] L] [IsLocalization.Away (X : k[X]) L]
  [CommSemiring R] [Algebra k R] [TopologicalSpace R] [IsTopologicalSemiring R]

variable (k L R) in
/-- The points of the localization `L` of `k[X]` away from `X` are the units of `R`: a point is
determined by its values at `X` and at `1 / X`, which are inverse units. This is a homeomorphism
onto `Rˣ` with the topology induced by `Units.embedProduct`; the inverse sends `u` to the extension
of `Polynomial.aeval u` to `L`. -/
noncomputable def localizationAwayXHomeomorph : (L →ₐ[k] R) ≃ₜ Rˣ where
  toFun x :=
    { val := x (algebraMap k[X] L X)
      inv := x (IsLocalization.Away.invSelf (X : k[X]))
      val_inv := by rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      inv_val := by rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one] }
  invFun u := IsLocalization.liftAlgHom (M := Submonoid.powers (X : k[X])) (S := L)
    (f := aeval (u : R)) (by rintro ⟨_, n, rfl⟩; simpa using u.isUnit.pow n)
  left_inv x := IsLocalization.algHom_ext (Submonoid.powers (X : k[X])) <|
    Polynomial.algHom_ext <| (IsLocalization.lift_eq _ X).trans (aeval_X _)
  right_inv u := Units.ext <| (IsLocalization.lift_eq _ X).trans (aeval_X _)
  continuous_toFun := Units.continuous_iff.2
    ⟨continuous_eval _, continuous_eval (IsLocalization.Away.invSelf (X : k[X]) : L)⟩
  continuous_invFun := by
    refine continuous_iff.2 fun b ↦ ?_
    -- Writing `b` as a fraction `a / X ^ n`, its value at the point of `u` is `a(u) * u⁻¹ ^ n`.
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := L) (X : k[X]) b
    refine (((Polynomial.continuous_aeval a).comp Units.continuous_val).mul
      (Units.continuous_coe_inv.pow n)).congr fun u ↦ ?_
    have hu (y : Submonoid.powers (X : k[X])) : IsUnit (aeval (u : R) (y : k[X])) := by
      obtain ⟨_, n, rfl⟩ := y
      simpa using u.isUnit.pow n
    have hb := congrArg (IsLocalization.lift (S := L) hu) ha
    simp only [map_mul, map_pow, IsLocalization.lift_eq] at hb
    simp only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply, IsLocalization.coe_liftAlgHom]
    rw [← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_eq_iff_eq_mul]
    simpa using hb.symm

/-- The unit attached to a point of the localization of `k[X]` away from `X` is its value at
`X`. -/
@[simp]
theorem val_localizationAwayXHomeomorph_apply (x : L →ₐ[k] R) :
    (localizationAwayXHomeomorph k L R x : R) = x (algebraMap k[X] L X) :=
  (rfl)

/-- The point attached to a unit `u` restricts to `Polynomial.aeval u` on `k[X]`. -/
@[simp]
theorem localizationAwayXHomeomorph_symm_apply_algebraMap (u : Rˣ) (p : k[X]) :
    (localizationAwayXHomeomorph k L R).symm u (algebraMap k[X] L p) = aeval (u : R) p :=
  IsLocalization.lift_eq _ p

/-- Restriction to `k[X]` embeds the points of the localization of `k[X]` away from `X` exactly
when inversion is continuous on the units of `R`. Up to the identification of the points of
`k[X]` with `R`, the restriction map is the inclusion of the units. -/
theorem isEmbedding_localization_X_iff :
    IsEmbedding (fun x : L →ₐ[k] R ↦ x.comp (IsScalarTower.toAlgHom k k[X] L)) ↔
      IsEmbedding (Units.val : Rˣ → R) := by
  refine ⟨fun h ↦ ?_, isEmbedding_localization X⟩
  convert (polynomialHomeomorph k R).isEmbedding.comp
    (h.comp (localizationAwayXHomeomorph k L R).symm.isEmbedding) using 1
  funext u
  simp

/-- Restriction to `k[X]` is an open embedding of the points of the localization of `k[X]` away
from `X` exactly when inversion is continuous on the units of `R` and the units are open. -/
theorem isOpenEmbedding_localization_X_iff :
    IsOpenEmbedding (fun x : L →ₐ[k] R ↦ x.comp (IsScalarTower.toAlgHom k k[X] L)) ↔
      IsEmbedding (Units.val : Rˣ → R) ∧ IsOpen {r : R | IsUnit r} := by
  refine ⟨fun h ↦ ⟨isEmbedding_localization_X_iff.1 h.isEmbedding, ?_⟩,
    fun h ↦ isOpenEmbedding_localization X h.1 h.2⟩
  have hrange := h.isOpen_range
  rw [IsLocalization.Away.range_comp_toAlgHom (X : k[X])] at hrange
  convert hrange.preimage (polynomialHomeomorph k R).symm.continuous using 1
  ext r
  simp

end Necessity

end TauCeti.PointTopology
