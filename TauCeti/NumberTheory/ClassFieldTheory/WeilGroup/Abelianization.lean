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
`W_K^{ab}` and proves that the resulting square with `ℤ → ℤ̂` commutes.

The map is injective.  The commutators of `W_K` lie in inertia, on which the Weil topology is the
profinite topology of `G_K`, and `W_K` is dense in `G_K`, so the closed commutator subgroup of
`W_K` is the trace on `W_K` of the closed commutator subgroup of `G_K`.  Hence `W_K^{ab}` is
isomorphic, as an abstract group, to the classes in `G_K^{ab}` with integral unramified
coordinate, and its topology is the one induced by `x ↦ (x, deg x)` into `G_K^{ab} × ℤ`, exactly
as for `W_K` itself.  These are the inputs about `W_K^{ab}` itself to the local Weil reciprocity
isomorphism `Kˣ ≃ₜ* W_K^{ab}`.

## Main definitions

* `TauCeti.ClassFieldTheory.weilToAbsoluteAbelianization`: the continuous map
  `W_K^{ab} → G_K^{ab}` induced by `W_K → G_K`.
* `TauCeti.ClassFieldTheory.weilDegreeAbelianization`: the Weil degree descended to `W_K^{ab}`.
* `TauCeti.ClassFieldTheory.integralUnramifiedSubgroup`: the subgroup of `G_K^{ab}` whose
  unramified coordinate is integral.
* `TauCeti.ClassFieldTheory.weilToIntegralUnramified`: the induced surjection from `W_K^{ab}`
  onto that subgroup.
* `TauCeti.ClassFieldTheory.weilAbelianizationEquivIntegralUnramified`: the same map, as an
  isomorphism of groups.

## Main results

* `TauCeti.ClassFieldTheory.unramifiedCoordinate_weilToAbsoluteAbelianization`: the unramified
  coordinate of a Weil class is the image of its degree in `ℤ̂`.
* `TauCeti.ClassFieldTheory.range_weilToAbsoluteAbelianization`: the image of `W_K^{ab}` is
  precisely `integralUnramifiedSubgroup K`.
* `TauCeti.ClassFieldTheory.injective_weilToAbsoluteAbelianization`: the map
  `W_K^{ab} → G_K^{ab}` is injective.
* `TauCeti.ClassFieldTheory.ker_weilDegreeAbelianization`: the classes of degree zero in
  `W_K^{ab}` are the classes of inertia.
* `isEmbedding_weilToAbsoluteAbelianization_prod_weilDegreeAbelianization`, in the same
  namespace: `x ↦ (x, deg x)` is a topological embedding `W_K^{ab} → G_K^{ab} × ℤ`.
* `TauCeti.ClassFieldTheory.denseRange_weilToAbsoluteAbelianization`: the image is dense in
  `G_K^{ab}`.

## References

* A. Weil, *Sur la théorie du corps de classes*, J. Math. Soc. Japan 3 (1951).
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

open Topology

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
@[simp]
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
@[simp]
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
    exact ⟨weilDegreeAbelianization K w,
      (unramifiedCoordinate_weilToAbsoluteAbelianization K w).symm⟩
  · intro hx
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
    have hσ : σ ∈ localWeilGroup K :=
      mem_localWeilGroup_iff_unramifiedCoordinate.2
        ((mem_integralUnramifiedSubgroup_iff K _).1 hx)
    refine ⟨((weilGroupEquivLocalWeilGroup K).symm ⟨σ, hσ⟩ : WeilGroup K), ?_⟩
    simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      weilToAbsoluteAbelianization_mk, weilToAbsolute_weilGroupEquivLocalWeilGroup_symm]

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
    Function.Surjective (weilToIntegralUnramified K) :=
  (Set.surjective_codRestrict _).2 <| by
    rw [← MonoidHom.coe_range, range_weilToAbsoluteAbelianization]

/-- **The abelianized Weil group injects into the abelianized absolute Galois group**: the map
`W_K^{ab} → G_K^{ab}` induced by the inclusion `W_K → G_K` is injective. -/
theorem injective_weilToAbsoluteAbelianization :
    Function.Injective (weilToAbsoluteAbelianization K) := by
  -- `W_K` is dense in `G_K`, and inertia carries the same topology in `W_K` and in `G_K`.
  refine TopologicalAbelianization.map_injective_of_isInducing (weilToAbsolute K)
    (continuous_weilToAbsolute K) (denseRange_weilToAbsolute K) (inertiaToWeil K)
    (isOpenEmbedding_inertiaToWeil K).continuous ?_ ?_
  · have : weilToAbsolute K ∘ inertiaToWeil K = Subtype.val := funext weilToAbsolute_inertiaToWeil
    rw [this]
    exact .subtypeVal
  · -- An element dying in `G_K^{ab}` has trivial unramified coordinate, so it lies in inertia.
    intro w hw
    rw [range_inertiaToWeil, Subgroup.mem_comap, ← unramifiedCoordinate_mk_eq_one_iff,
      (QuotientGroup.eq_one_iff (weilToAbsolute K w)).2 hw, map_one]

/-- **The abelianized inertia sequence**: the classes of degree zero in `W_K^{ab}` are exactly
the classes of elements of inertia. This is the abelianized form of `ker_weilDegree`. -/
theorem ker_weilDegreeAbelianization :
    (weilDegreeAbelianization K).toMonoidHom.ker =
      ((QuotientGroup.mk' (commutator (WeilGroup K)).topologicalClosure).comp
        (inertiaToWeil K)).range := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    have hw : w ∈ (inertiaToWeil K).range := by
      rw [range_inertiaToWeil, ← ker_weilDegree, MonoidHom.mem_ker, ← weilDegreeAbelianization_mk]
      exact hx
    obtain ⟨σ, rfl⟩ := hw
    exact ⟨σ, rfl⟩
  · rintro _ ⟨σ, rfl⟩
    simp

/-- **The topology of `W_K^{ab}`**: `x ↦ (x, deg x)` is a topological embedding of `W_K^{ab}`
into `G_K^{ab} × ℤ`, with `ℤ` discrete. This is the abelianized form of the characterization of
the Weil topology, `isEmbedding_weilToAbsolute_prod_weilDegree`. -/
theorem isEmbedding_weilToAbsoluteAbelianization_prod_weilDegreeAbelianization :
    IsEmbedding ((weilToAbsoluteAbelianization K).prod (weilDegreeAbelianization K)) := by
  set Φ := (weilToAbsoluteAbelianization K).prod (weilDegreeAbelianization K)
  have hinj : Function.Injective Φ := fun _ _ h ↦
    injective_weilToAbsoluteAbelianization K (congrArg Prod.fst h)
  refine Φ.toMonoidHom.isEmbedding_of_isCompact_preimage Φ.continuous hinj
    (prod_mem_nhds Filter.univ_mem ((isOpen_discrete {1}).mem_nhds rfl)) ?_
  -- The preimage of `G_K^{ab} × {0}` is the subgroup of classes of degree zero, which is compact
  -- as the image of the compact group `I_K`.
  have hA : Φ.toMonoidHom ⁻¹' (Set.univ ×ˢ {1}) =
      ((weilDegreeAbelianization K).toMonoidHom.ker : Set _) := by
    ext x
    simp [Φ]
  have : CompactSpace (inertiaSubgroup K) :=
    isCompact_iff_compactSpace.1 (isClosed_inertiaSubgroup K).isCompact
  rw [hA, ker_weilDegreeAbelianization, MonoidHom.coe_range]
  exact isCompact_range (QuotientGroup.continuous_mk.comp
    (isOpenEmbedding_inertiaToWeil K).continuous)

/-- The abelianized Weil group is isomorphic, as an abstract group, to the subgroup of `G_K^{ab}`
of classes with integral unramified coordinate, through the map induced by `W_K → G_K`. -/
def weilAbelianizationEquivIntegralUnramified :
    TopologicalAbelianization (WeilGroup K) ≃* integralUnramifiedSubgroup K :=
  MulEquiv.ofBijective (weilToIntegralUnramified K)
    ⟨fun _ _ h ↦ injective_weilToAbsoluteAbelianization K (congrArg Subtype.val h),
      surjective_weilToIntegralUnramified K⟩

/-- The isomorphism `W_K^{ab} ≃* integralUnramifiedSubgroup K` has the same underlying value in
`G_K^{ab}` as the induced map `W_K^{ab} → G_K^{ab}`. -/
@[simp]
theorem coe_weilAbelianizationEquivIntegralUnramified
    (w : TopologicalAbelianization (WeilGroup K)) :
    (weilAbelianizationEquivIntegralUnramified K w : Field.absoluteGaloisGroupAbelianization K) =
      weilToAbsoluteAbelianization K w :=
  (rfl)

/-- The inverse of `W_K^{ab} ≃* integralUnramifiedSubgroup K` sends a class with integral
unramified coordinate to the unique Weil class mapping to it in `G_K^{ab}`. -/
@[simp]
theorem weilToAbsoluteAbelianization_weilAbelianizationEquivIntegralUnramified_symm
    (x : integralUnramifiedSubgroup K) :
    weilToAbsoluteAbelianization K ((weilAbelianizationEquivIntegralUnramified K).symm x) = x := by
  rw [← coe_weilAbelianizationEquivIntegralUnramified, MulEquiv.apply_symm_apply]

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
