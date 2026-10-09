/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Topology
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The local Weil group inside the abelianized absolute Galois group

Let `K` be a nonarchimedean local field.  The inclusion `W_K → G_K` induces a continuous
homomorphism

`W_K^{ab} → G_K^{ab}`.

This file identifies its image without choosing a Frobenius lift: it consists exactly of the
classes whose unramified coordinate in `ℤ̂` is an integer.  It also descends the Weil degree to
`W_K^{ab}` and proves that the resulting square with `ℤ → ℤ̂` commutes.  These statements are the
image half of the local Weil reciprocity isomorphism `Kˣ ≃ₜ* W_K^{ab}`.

## Main definitions

* `TauCeti.ClassFieldTheory.weilToAbsoluteAbelianization`: the continuous map
  `W_K^{ab} → G_K^{ab}` induced by `W_K → G_K`.
* `TauCeti.ClassFieldTheory.weilDegreeAbelianization`: the Weil degree descended to `W_K^{ab}`.
* `TauCeti.ClassFieldTheory.integralUnramifiedSubgroup`: the subgroup of `G_K^{ab}` whose
  unramified coordinate is integral.
* `TauCeti.ClassFieldTheory.weilToIntegralUnramified`: the induced surjection from `W_K^{ab}`
  onto that subgroup.

## Main results

* `TauCeti.ClassFieldTheory.unramifiedCoordinate_weilToAbsoluteAbelianization`: the unramified
  coordinate of a Weil class is the image of its degree in `ℤ̂`.
* `TauCeti.ClassFieldTheory.range_weilToAbsoluteAbelianization`: the image of `W_K^{ab}` is
  precisely `integralUnramifiedSubgroup K`.
* `TauCeti.ClassFieldTheory.denseRange_weilToAbsoluteAbelianization`: this image is dense in
  `G_K^{ab}`.

## References

* A. Weil, *Sur la théorie du corps de classes*, J. Math. Soc. Japan 3 (1951).
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The continuous homomorphism `W_K^{ab} → G_K^{ab}` induced by the inclusion `W_K → G_K`. -/
def weilToAbsoluteAbelianization :
    TopologicalAbelianization (WeilGroup K) →ₜ*
      Field.absoluteGaloisGroupAbelianization K where
  toMonoidHom := TopologicalAbelianization.map (weilToAbsolute K) (continuous_weilToAbsolute K)
  continuous_toFun :=
    TopologicalAbelianization.continuous_map (weilToAbsolute K) (continuous_weilToAbsolute K)

/-- The induced map on topological abelianizations sends the class of `w` to the class of its
image in the absolute Galois group. -/
@[simp]
theorem weilToAbsoluteAbelianization_mk (w : WeilGroup K) :
    weilToAbsoluteAbelianization K
        (w : TopologicalAbelianization (WeilGroup K)) =
      (weilToAbsolute K w : Field.absoluteGaloisGroupAbelianization K) :=
  TopologicalAbelianization.map_mk _ _ _

/-- The Weil degree descended to the topological abelianization of `W_K`. -/
def weilDegreeAbelianization :
    TopologicalAbelianization (WeilGroup K) →ₜ* Multiplicative ℤ :=
  TopologicalAbelianization.lift
    { toMonoidHom := weilDegree K
      continuous_toFun := continuous_weilDegree K }

/-- The abelianized Weil degree agrees with the degree on representatives. -/
@[simp]
theorem weilDegreeAbelianization_mk (w : WeilGroup K) :
    weilDegreeAbelianization K (w : TopologicalAbelianization (WeilGroup K)) = weilDegree K w :=
  TopologicalAbelianization.lift_mk _ _

/-- **Compatibility of degree and the unramified coordinate.**  The square formed by
`W_K^{ab} → G_K^{ab}`, the abelianized Weil degree, and `ℤ → ℤ̂` commutes. -/
theorem unramifiedCoordinate_weilToAbsoluteAbelianization
    (w : TopologicalAbelianization (WeilGroup K)) :
    unramifiedCoordinate K (weilToAbsoluteAbelianization K w) =
      zHat.ofInt (weilDegreeAbelianization K w) := by
  induction w using QuotientGroup.induction_on with
  | H w =>
      simpa only [weilToAbsoluteAbelianization_mk, weilDegreeAbelianization_mk] using
        unramifiedCoordinate_weilDegree w

/-- The subgroup of `G_K^{ab}` consisting of classes with integral unramified coordinate. -/
def integralUnramifiedSubgroup : Subgroup (Field.absoluteGaloisGroupAbelianization K) :=
  (zHat.ofInt : Multiplicative ℤ →* zHat.{u}).range.comap
    (unramifiedCoordinate K).toMonoidHom

/-- Membership in the integral-unramified subgroup means exactly that the unramified coordinate
belongs to the image of `ℤ → ℤ̂`. -/
theorem mem_integralUnramifiedSubgroup_iff
    (x : Field.absoluteGaloisGroupAbelianization K) :
    x ∈ integralUnramifiedSubgroup K ↔
      unramifiedCoordinate K x ∈ (zHat.ofInt : Multiplicative ℤ →* zHat.{u}).range :=
  Iff.rfl

/-- **The image of the abelianized Weil group.**  A class in `G_K^{ab}` comes from `W_K^{ab}`
exactly when its unramified coordinate is an integer. -/
theorem range_weilToAbsoluteAbelianization :
    (weilToAbsoluteAbelianization K).toMonoidHom.range = integralUnramifiedSubgroup K := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [mem_integralUnramifiedSubgroup_iff]
    change unramifiedCoordinate K (weilToAbsoluteAbelianization K w) ∈ _
    rw [unramifiedCoordinate_weilToAbsoluteAbelianization]
    exact ⟨weilDegreeAbelianization K w, rfl⟩
  · intro hx
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
    have hσ : σ ∈ localWeilGroup K :=
      mem_localWeilGroup_iff_unramifiedCoordinate.2
        ((mem_integralUnramifiedSubgroup_iff K _).1 hx)
    let w : WeilGroup K := (weilGroupEquivLocalWeilGroup K).symm ⟨σ, hσ⟩
    exact ⟨(w : TopologicalAbelianization (WeilGroup K)), by
      change weilToAbsoluteAbelianization K
        (w : TopologicalAbelianization (WeilGroup K)) = _
      rw [weilToAbsoluteAbelianization_mk]
      exact congrArg (fun g : Field.absoluteGaloisGroup K ↦
        (g : Field.absoluteGaloisGroupAbelianization K))
        (weilToAbsolute_weilGroupEquivLocalWeilGroup_symm (K := K)
          (⟨σ, hσ⟩ : localWeilGroup K))⟩

/-- The map from `W_K^{ab}` to its image in `G_K^{ab}`, with codomain restricted to the classes
having integral unramified coordinate. -/
def weilToIntegralUnramified :
    TopologicalAbelianization (WeilGroup K) →ₜ* integralUnramifiedSubgroup K where
  toMonoidHom := (weilToAbsoluteAbelianization K).toMonoidHom.codRestrict
    (integralUnramifiedSubgroup K) fun w ↦ by
      rw [← range_weilToAbsoluteAbelianization]
      exact ⟨w, rfl⟩
  continuous_toFun := continuous_induced_rng.2 (weilToAbsoluteAbelianization K).continuous

/-- The range-restricted abelianized inclusion has the same underlying value in `G_K^{ab}`. -/
@[simp]
theorem coe_weilToIntegralUnramified
    (w : TopologicalAbelianization (WeilGroup K)) :
    (weilToIntegralUnramified K w : Field.absoluteGaloisGroupAbelianization K) =
      weilToAbsoluteAbelianization K w :=
  by rfl

/-- The abelianized Weil group surjects onto the subgroup of classes with integral unramified
coordinate. -/
theorem surjective_weilToIntegralUnramified :
    Function.Surjective (weilToIntegralUnramified K) := fun x ↦ by
  have hx : (x : Field.absoluteGaloisGroupAbelianization K) ∈
      (weilToAbsoluteAbelianization K).toMonoidHom.range := by
    rw [range_weilToAbsoluteAbelianization]
    exact x.2
  obtain ⟨w, hw⟩ := hx
  exact ⟨w, Subtype.ext hw⟩

/-- The induced map `W_K^{ab} → G_K^{ab}` has dense image.  Equivalently, classes with integral
unramified coordinate are dense in `G_K^{ab}`. -/
theorem denseRange_weilToAbsoluteAbelianization :
    DenseRange (weilToAbsoluteAbelianization K) := by
  apply DenseRange.of_comp (g :=
    (QuotientGroup.mk : WeilGroup K → TopologicalAbelianization (WeilGroup K)))
  have hcomp : weilToAbsoluteAbelianization K ∘
        (QuotientGroup.mk : WeilGroup K → TopologicalAbelianization (WeilGroup K)) =
      (QuotientGroup.mk : Field.absoluteGaloisGroup K →
        Field.absoluteGaloisGroupAbelianization K) ∘ weilToAbsolute K := by
    funext w
    exact weilToAbsoluteAbelianization_mk K w
  rw [hcomp]
  exact (QuotientGroup.mk_surjective.denseRange).comp
    (denseRange_weilToAbsolute K) QuotientGroup.continuous_mk

end TauCeti.ClassFieldTheory
