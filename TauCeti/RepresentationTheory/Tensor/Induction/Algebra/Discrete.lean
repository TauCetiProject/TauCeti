/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Algebra
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Tensor.Induction.Algebra.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Ring.Discrete
import TauCeti.RingTheory.PiTensorProduct.Basic

/-!
# Smooth tensor-induced algebras and cup-product compatibility

When `U` is an open finite-index subgroup of a topological group `G` and `A` is a discrete `R`-ring
with continuous action of `U` by `R`-algebra automorphisms, the tensor-induced module
`⨂[R] _ : G ⧸ U, A` equipped with the discrete topology is both a discrete continuous
`G`-representation (`TauCeti.DiscreteRep.tensorInduced`) and a `G`-algebra
(`Subgroup.tensorInducedMulSemiringAction`). This file records the multiplicative structure of the
smooth tensor-induced representation of `TauCeti.SmoothDiscreteTopRep.of R U A`: its carrier is a
monoid on which every group element acts by `Subgroup.tensorInducedAlgAut`, and the tensor
induction of the multiplication pairing `TauCeti.SmoothDiscreteTopRep.ofMulPairing` evaluates to
ring multiplication in `⨂[R] _ : G ⧸ U, A` (`TauCeti.smoothTensorInduced_ofMulPairing_bil_apply`).

When `A` is a discrete commutative `G`-algebra with continuous `G`-action, Evens' transversal
multiplication `TauCeti.smoothTensorInducedMulHom` (from
`TauCeti.RepresentationTheory.Tensor.Induction.Ring.Discrete`) intertwines the tensor-induced
multiplication pairing with the multiplication pairing of `A` over `G`. Passing to continuous
cohomology via `TauCeti.TopPairing.cup_coeffMap` yields cup-product compatibility
(`TauCeti.cup_coeffMap_smoothTensorInducedMulHom`) in every bidegree. Specializing `R = ℤ` gives
the topological coefficient bridge for the Evens norm of a discrete commutative `G`-ring.

## Main results

* `TauCeti.smoothTensorInduced_of_obj_ρ_apply`, `TauCeti.smoothTensorInduced_of_obj_ρ_one`,
  `TauCeti.smoothTensorInduced_of_obj_ρ_mul`: the smooth tensor-induced representation of
  `SmoothDiscreteTopRep.of R U A` acts on `⨂[R] _ : G ⧸ U, A` by `Subgroup.tensorInducedAlgAut`,
  fixing `1` and preserving `*`.
* `TauCeti.smoothTensorInduced_ofMulPairing_bil_apply`: tensor induction of the multiplication
  pairing of `A` is ring multiplication in `⨂[R] _ : G ⧸ U, A`.
* `coeffMap_smoothTensorInducedChangeTransversalIso_hom_comp_coeffMap_smoothTensorInducedMulHom`
  (in namespace `TauCeti`): transversal independence of the coefficient maps of transversal
  multiplication.
* `TauCeti.cup_coeffMap_smoothTensorInducedMulHom`: the cohomology map induced by
  `smoothTensorInducedMulHom` carries the tensor-induced cup product to the canonical
  multiplication cup product `ofDiscreteModuleMulPairing R G A`.

## Implementation notes

* The `Monoid` / `CommMonoid` carrier instances and `TauCeti.smoothTensorInduced_of_obj_ρ_apply`
  are polymorphic in three independent universes `R : Type u`, `G : Type v`, `A : Type w`.
* Morphisms `tensorInduced U hU s { V := A } ⟶ { V := A }` in `DiscreteRep` and
  `SmoothDiscreteTopRep` require the tensor power and `A` to inhabit the same carrier universe.
  The cohomological results place `R : Type u`, `G : Type v`, and `A : Type (max v u)`, using
  `TauCeti.smoothTensorInducedMulHom` at the universe instance `A : Type (max u v u)`, so every
  universe parameter is determined directly from `R` and `G`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 5--6, pp. 60--62.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

/-! ### Carrier monoids and transversal multiplication in `DiscreteRep` -/

namespace TauCeti.DiscreteRep

section AlgebraAction

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

/-- The underlying module of `DiscreteRep.tensorInduced U hU s (of R U A)` inherits the monoid
structure of `⨂[R] _ : G ⧸ U, A` at instance transparency. -/
noncomputable instance instMonoidTensorInducedOfV (A : Type w) [Ring A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A] :
    Monoid (tensorInduced U hU s (of R U A)).V :=
  inferInstanceAs (Monoid (⨂[R] _ : G ⧸ U, A))

/-- When `A` is commutative, the underlying module of `DiscreteRep.tensorInduced U hU s (of R U A)`
inherits the commutative monoid structure of `⨂[R] _ : G ⧸ U, A` at instance transparency. -/
noncomputable instance instCommMonoidTensorInducedOfV (A : Type w) [CommRing A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A] :
    CommMonoid (tensorInduced U hU s (of R U A)).V :=
  inferInstanceAs (CommMonoid (⨂[R] _ : G ⧸ U, A))

end AlgebraAction

section Multiplication

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (A : Type (max u v w)) [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A] [ContinuousSMul G A]

/-- Precomposing transversal multiplication along `t` with the inverse change-of-transversal
comparison gives transversal multiplication along `s`. -/
@[reassoc (attr := simp)]
theorem tensorInducedChangeTransversalIso_inv_tensorInducedMulHom (s t : U.LeftTransversal) :
    (tensorInducedChangeTransversalIso U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).inv ≫
        tensorInducedMulHom (R := R) U hU A t =
      tensorInducedMulHom (R := R) U hU A s := by
  rw [Iso.inv_comp_eq, tensorInducedChangeTransversalIso_hom_tensorInducedMulHom]

end Multiplication

end TauCeti.DiscreteRep

/-! ### Smooth discrete tensor-induced pairing, multiplication, and cup-product compatibility -/

namespace TauCeti

section SmoothPairing

section CarrierAndAction

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

/-- The underlying module of the smooth tensor-induced representation of a discrete `U`-algebra
inherits the monoid structure of `⨂[R] _ : G ⧸ U, A` at instance transparency. -/
noncomputable instance instMonoidSmoothTensorInducedOfV {A : Type w} [Ring A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A] :
    Monoid ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.V :=
  inferInstanceAs (Monoid (⨂[R] _ : G ⧸ U, A))

/-- When `A` is commutative, the underlying module of the smooth tensor-induced representation of
`SmoothDiscreteTopRep.of R U A` inherits the commutative monoid structure of `⨂[R] _ : G ⧸ U, A` at
instance transparency. -/
noncomputable instance instCommMonoidSmoothTensorInducedOfV {A : Type w} [CommRing A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A] :
    CommMonoid ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.V :=
  inferInstanceAs (CommMonoid (⨂[R] _ : G ⧸ U, A))

/-- The smooth tensor-induced representation of `SmoothDiscreteTopRep.of R U A` acts on its
underlying carrier by `Subgroup.tensorInducedAlgAut`. -/
theorem smoothTensorInduced_of_obj_ρ_apply {A : Type w} [Ring A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]
    (g : G)
    (z : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.V) :
    ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.ρ g z =
      U.tensorInducedAlgAut R A s g z :=
  -- Term-mode `Eq.trans` bridges the exposed `toSmoothDiscrete` / `tensorInduced` carrier with
  -- `⨂[R] _ : G ⧸ U, A`, where `rw` fails at `implicit` transparency.
  (toSmoothDiscrete_obj_obj_ρ_apply _ g z).trans <|
    (DiscreteRep.tensorInduced_ρ_apply U hU s _ g z).trans
      (LinearMap.congr_fun (U.tensorInducedAlgAut_toLinearMap R A s g) z).symm

/-- On the smooth tensor-induced representation of `SmoothDiscreteTopRep.of R U A`, every group
element fixes `1` (the unit invariance input for `TopPairing.cup_one_left`,
`TopPairing.cup_one_right`, and `TopPairing.cohomologyGRing`). -/
@[simp]
theorem smoothTensorInduced_of_obj_ρ_one {A : Type w} [Ring A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A] (g : G) :
    ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.ρ g 1 = 1 :=
  (smoothTensorInduced_of_obj_ρ_apply U hU s g 1).trans
    (map_one (U.tensorInducedAlgAut R A s g))

/-- On the smooth tensor-induced representation of `SmoothDiscreteTopRep.of R U A`, every group
element preserves multiplication on the carrier. -/
theorem smoothTensorInduced_of_obj_ρ_mul {A : Type w} [Ring A] [Algebra R A]
    [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]
    (g : G)
    (x y : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.V) :
    ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.ρ g (x * y) =
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.ρ g x *
        ((toSmoothDiscrete R G).obj
          (DiscreteRep.tensorInduced U hU s
            ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj.ρ g y := by
  rw [smoothTensorInduced_of_obj_ρ_apply, smoothTensorInduced_of_obj_ρ_apply,
    smoothTensorInduced_of_obj_ρ_apply]
  exact map_mul (U.tensorInducedAlgAut R A s g) x y

end CarrierAndAction

section BilApply

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  {A : Type (max v w)} [Ring A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]

/-- Evaluating the tensor-induced multiplication pairing multiplies elements in the tensor-induced
algebra `⨂[R] _ : G ⧸ U, A`.

This is not a simp lemma: `TopPairing.smoothTensorInduced_bil` already simplifies its left-hand
side. -/
theorem smoothTensorInduced_ofMulPairing_bil_apply (x y : ⨂[R] _ : G ⧸ U, A) :
    ((SmoothDiscreteTopRep.ofMulPairing R U A).smoothTensorInduced.{u, v, w} U hU s
      (A := SmoothDiscreteTopRep.of R U A)
      (B := SmoothDiscreteTopRep.of R U A)
      (C := SmoothDiscreteTopRep.of R U A)).bil x y =
      (x * y : ⨂[R] _ : G ⧸ U, A) := by
  rw [TopPairing.smoothTensorInduced_bil]
  -- Align the `toSmoothDiscrete` carrier with `A` so `PiTensorProduct.map₂_mul` synthesizes
  -- `[Semiring A]` without equipping `TopModuleCat` carriers with a competing `AddCommMonoid`.
  change (PiTensorProduct.map₂ (s := fun _ : G ⧸ U ↦ A) (t := fun _ : G ⧸ U ↦ A)
    (t' := fun _ : G ⧸ U ↦ A)
    (fun _ ↦ (SmoothDiscreteTopRep.ofMulPairing R U A).bil)) x y = x * y
  simp [PiTensorProduct.map₂_mul]

end BilApply

end SmoothPairing

section SmoothMultiplication

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  {A : Type (max v u)} [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A] [ContinuousSMul G A]
  (s t : U.LeftTransversal)

/-- `smoothTensorInducedMulHom` preserves multiplication on underlying carriers. -/
theorem smoothTensorInducedMulHom_hom_hom_mul (x y : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom.hom (x * y) =
      ((smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom.hom x : A) *
        ((smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom.hom y : A) :=
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  (smoothTensorInducedMulHom_hom_hom_apply.{u, v, u} U hU A s (x * y)).trans <|
    (map_mul (U.tensorInducedMulAlgHom R A s) x y).trans <|
    congrArg₂ ((· * ·) : A → A → A)
      (smoothTensorInducedMulHom_hom_hom_apply.{u, v, u} U hU A s x).symm
      (smoothTensorInducedMulHom_hom_hom_apply.{u, v, u} U hU A s y).symm

/-- Precomposing `smoothTensorInducedMulHom` along `t` with the inverse smooth
change-of-transversal isomorphism gives `smoothTensorInducedMulHom` along `s`. -/
@[reassoc (attr := simp)]
theorem smoothTensorInducedChangeTransversalIso_inv_smoothTensorInducedMulHom :
    (smoothTensorInducedChangeTransversalIso U hU s t
        ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩).inv ≫
        smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A t =
      smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s := by
  rw [Iso.inv_comp_eq,
    smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom.{u, v, u}]

/-- On continuous cohomology, composing the change-of-transversal coefficient map from `t` to `s`
with the multiplication coefficient map along `s` gives the multiplication coefficient map along
`t`. -/
theorem coeffMap_smoothTensorInducedChangeTransversalIso_hom_comp_coeffMap_smoothTensorInducedMulHom
    (n : ℕ) :
    ContinuousCohomology.coeffMap
        (smoothTensorInducedChangeTransversalIso U hU s t
          ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩).hom.hom n ≫
      ContinuousCohomology.coeffMap
        (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom n =
      ContinuousCohomology.coeffMap
        (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A t).hom n := by
  rw [← ContinuousCohomology.coeffMap_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom.{u, v, u}]

/-- **Cup-product compatibility of smooth tensor-induced multiplication**: on continuous
cohomology, `ContinuousCohomology.coeffMap` along `smoothTensorInducedMulHom` carries the cup
product for the tensor-induced multiplication pairing to the canonical multiplication cup product
`ofDiscreteModuleMulPairing R G A` on `ofDiscreteModule R G A` in every bidegree `(m, n)`. -/
theorem cup_coeffMap_smoothTensorInducedMulHom (m n : ℕ)
    (a : continuousCohomology m
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩))).obj)
    (b : continuousCohomology n
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩))).obj) :
    ContinuousCohomology.coeffMap (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom
        (m + n)
        (((ofDiscreteModuleMulPairing R U A).smoothTensorInduced.{u, v, max v u} U hU s
          (A := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
          (B := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
          (C := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)).cup.{u, v,
            max v u} m n a b) =
      (ofDiscreteModuleMulPairing R G A).cup.{u, v, max v u} m n
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom m a)
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom n b) :=
  ((ofDiscreteModuleMulPairing R U A).smoothTensorInduced.{u, v, max v u} U hU s
    (A := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
    (B := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
    (C := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)).cup_coeffMap.{u, v,
      max v u}
    (ofDiscreteModuleMulPairing R G A)
    (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom
    (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom
    (smoothTensorInducedMulHom.{u, v, u} (R := R) U hU A s).hom
    (smoothTensorInducedMulHom_bil_of_eq_mul.{u, v, u} (R := R) U hU
      (ofDiscreteModuleMulPairing R U A) (ofDiscreteModuleMulPairing_bil_apply R U A)
      (ofDiscreteModuleMulPairing R G A) (ofDiscreteModuleMulPairing_bil_apply R G A) s)
    m n a b

end SmoothMultiplication

/-! ### Concrete specialization to discrete commutative `G`-rings (`R = ℤ`) -/

section Examples

/-- For any discrete commutative `G`-ring `A` (with `R = ℤ`), `SmoothDiscreteTopRep.ofMulPairing`,
`ofDiscreteModuleMulPairing`, and `cup_coeffMap_smoothTensorInducedMulHom` apply in the group's
own universe `v` without extra scalar-continuity hypotheses, while `simp` discharges `.flip`
symmetry and operator `1` invariance and `smoothTensorInduced_of_obj_ρ_mul` gives operator `*`
preservation on the smooth tensor-induced representation. -/
example {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) (s : U.toSubgroup.LeftTransversal) [U.toSubgroup.FiniteIndex]
    (A : Type v) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [ContinuousSMul G A] (m n : ℕ)
    (a : continuousCohomology m
      ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            ⟨ofDiscreteModule ℤ U.toSubgroup A,
              ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩))).obj)
    (b : continuousCohomology n
      ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            ⟨ofDiscreteModule ℤ U.toSubgroup A,
              ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩))).obj) :
    (((SmoothDiscreteTopRep.ofMulPairing ℤ U.toSubgroup A).smoothTensorInduced.{0, v, v}
        U.toSubgroup U.isOpen' s
        (A := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)
        (B := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)
        (C := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)).flip =
      (SmoothDiscreteTopRep.ofMulPairing ℤ U.toSubgroup A).smoothTensorInduced.{0, v, v}
        U.toSubgroup U.isOpen' s
        (A := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)
        (B := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)
        (C := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)) ∧
    (∀ g : G,
      ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj.ρ g 1 = 1) ∧
    (∀ (g : G)
      (x y : ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj.V),
      ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj.ρ g (x * y) =
        ((toSmoothDiscrete ℤ G).obj
          (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
            ((ofSmoothDiscrete ℤ U.toSubgroup).obj
              (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj.ρ g x *
          ((toSmoothDiscrete ℤ G).obj
            (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
              ((ofSmoothDiscrete ℤ U.toSubgroup).obj
                (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj.ρ g y) ∧
    ContinuousCohomology.coeffMap
        (smoothTensorInducedMulHom.{0, v, 0} (R := ℤ) U.toSubgroup U.isOpen' A s).hom (m + n)
        (((ofDiscreteModuleMulPairing ℤ U.toSubgroup A).smoothTensorInduced.{0, v, v}
          U.toSubgroup U.isOpen' s
          (A := ⟨ofDiscreteModule ℤ U.toSubgroup A,
            ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩)
          (B := ⟨ofDiscreteModule ℤ U.toSubgroup A,
            ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩)
          (C := ⟨ofDiscreteModule ℤ U.toSubgroup A,
            ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩)).cup.{0, v, v} m n a b) =
      (ofDiscreteModuleMulPairing ℤ G A).cup.{0, v, v} m n
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedMulHom.{0, v, 0} (R := ℤ) U.toSubgroup U.isOpen' A s).hom m a)
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedMulHom.{0, v, 0} (R := ℤ) U.toSubgroup U.isOpen' A s).hom n b) :=
  ⟨by simp, by simp, smoothTensorInduced_of_obj_ρ_mul U.toSubgroup U.isOpen' s,
    cup_coeffMap_smoothTensorInducedMulHom U.toSubgroup U.isOpen' s m n a b⟩

end Examples

end TauCeti
