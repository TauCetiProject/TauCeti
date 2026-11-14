/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Algebra
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Tensor.Induction.Algebra.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Discrete

/-!
# Discrete and smooth tensor-induced algebras and cup-product compatibility

When `U` is an open finite-index subgroup of a topological group `G` and `A` is a discrete `R`-ring
with continuous action of `U` by `R`-algebra automorphisms, the tensor-induced module
`⨂[R] _ : G ⧸ U, A` equipped with the discrete topology is both a discrete continuous
`G`-representation (`TauCeti.DiscreteRep.tensorInduced`) and a `G`-algebra
(`Subgroup.tensorInducedMulSemiringAction`) with the same underlying `G`-action. Consequently its
action by `R`-algebra automorphisms is continuous
(`Subgroup.continuousSMul_tensorInducedMulSemiringAction`), and the tensor induction of the
multiplication pairing `TauCeti.SmoothDiscreteTopRep.ofMulPairing` evaluates to ring multiplication
in `⨂[R] _ : G ⧸ U, A` (`TauCeti.smoothTensorInduced_ofMulPairing_bil_apply`).

When `A` is a discrete commutative `G`-algebra with continuous `G`-action, Evens' transversal
multiplication `Subgroup.tensorInducedMulAlgHom` upgrades to a morphism in `TauCeti.DiscreteRep`
(`TauCeti.DiscreteRep.tensorInducedMulHom`) and in `TauCeti.SmoothDiscreteTopRep`
(`TauCeti.smoothTensorInducedMulHom`). Both morphisms are invariant under change of transversal
and intertwine the tensor-induced multiplication pairing (`TauCeti.TopPairing.smoothTensorInduced`
applied to `TauCeti.SmoothDiscreteTopRep.ofMulPairing`) with the multiplication pairing of `A` over
`G`. Passing to continuous cohomology via `TauCeti.TopPairing.cup_coeffMap` yields cup-product
compatibility (`TauCeti.cup_coeffMap_smoothTensorInducedMulHom`) in every bidegree. Specializing
`R = ℤ` gives the topological coefficient bridge for the Evens norm of a discrete commutative
`G`-ring.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedMulHom`: transversal multiplication on a discrete commutative
  `G`-algebra as a morphism `tensorInduced U hU s (of R U A) ⟶ of R G A` in `DiscreteRep R G`.
* `TauCeti.smoothTensorInducedMulHom`: the corresponding morphism of smooth discrete topological
  representations in `SmoothDiscreteTopRep R G`.

## Main results

* `Subgroup.continuousSMul_tensorInducedMulSemiringAction`: the `G`-algebra action on the discrete
  tensor-induced algebra `⨂[R] _ : G ⧸ U, A` is continuous.
* `TauCeti.smoothTensorInduced_of_obj_ρ_apply`, `TauCeti.smoothTensorInduced_of_obj_ρ_one`,
  `TauCeti.smoothTensorInduced_of_obj_ρ_mul`: the smooth tensor-induced representation of
  `SmoothDiscreteTopRep.of R U A` acts on `⨂[R] _ : G ⧸ U, A` by `Subgroup.tensorInducedAlgAut`,
  fixing `1` and preserving `*`.
* `TauCeti.smoothTensorInduced_ofMulPairing_bil_apply`: tensor induction of the multiplication
  pairing of `A` is ring multiplication in `⨂[R] _ : G ⧸ U, A`.
* `TauCeti.DiscreteRep.tensorInducedChangeTransversalIso_hom_tensorInducedMulHom`,
  `TauCeti.smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom`: transversal
  multiplication is independent of the chosen transversal in `DiscreteRep` and
  `SmoothDiscreteTopRep`.
* `TauCeti.cup_coeffMap_smoothTensorInducedMulHom`: the cohomology map induced by
  `smoothTensorInducedMulHom` carries the tensor-induced cup product to the canonical
  multiplication cup product on `continuousCohomology * (SmoothDiscreteTopRep.of R G A).obj`.

## Implementation notes

* `Subgroup.continuousSMul_tensorInducedMulSemiringAction`, the `Monoid` / `CommMonoid` carrier
  instances, and `TauCeti.smoothTensorInduced_of_obj_ρ_apply` are polymorphic in three independent
  universes `R : Type u`, `G : Type v`, `A : Type w`.
* Morphisms `tensorInduced U hU s (of R U A) ⟶ of R G A` in `DiscreteRep` and
  `SmoothDiscreteTopRep` require the tensor power and `A` to inhabit the same carrier universe
  (`max u v w_A = w_A`, cf.
  `TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Resolution`).
  Accordingly, `DiscreteRep.tensorInducedMulHom`, `smoothTensorInducedMulHom`, and
  `cup_coeffMap_smoothTensorInducedMulHom` place `R : Type u`, `G : Type v`, and
  `A : Type (max v u)` so every universe parameter is determined directly from `R` and `G`
  (covering both `R : Type` with `G, A : Type v` and `R = A^G` or equal-universe setups with
  `u = v`); the unrestricted underlying intertwining map remains available as
  `Subgroup.tensorInducedMulIntertwiningMap`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 5--6, pp. 60--62.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

/-! ### Continuity of the tensor-induced algebra action -/

namespace Subgroup

open TauCeti

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]

include hU in
/-- When `U` is an open finite-index subgroup of `G` and `A` is a discrete `R`-algebra with
continuous action of `U` by `R`-algebra automorphisms, the tensor-induced `MulSemiringAction` of
`G` on `⨂[R] _ : G ⧸ U, A` is continuous for the discrete topology. -/
theorem continuousSMul_tensorInducedMulSemiringAction :
    letI : TopologicalSpace (⨂[R] _ : G ⧸ U, A) := ⊥
    letI := U.tensorInducedMulSemiringAction s R A
    ContinuousSMul G (⨂[R] _ : G ⧸ U, A) :=
  -- Both `DiscreteRep.tensorInduced` and `tensorInducedMulSemiringAction` install the same
  -- `SMul G (⨂[R] _ : G ⧸ U, A)` and the discrete topology `⊥`.
  (DiscreteRep.tensorInduced U hU s (DiscreteRep.of R U A)).continuousSMul

end Subgroup

/-! ### Transversal multiplication in `DiscreteRep` -/

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

variable {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]
  (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (A : Type (max v u)) [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A]

/-- **Transversal multiplication in `DiscreteRep`**: for an open finite-index subgroup `U ≤ G` and
a discrete commutative `G`-algebra `A` with continuous `G`-action, `Subgroup.tensorInducedMulAlgHom`
as a morphism `tensorInduced U hU s (of R U A) ⟶ of R G A` in `DiscreteRep R G`. -/
noncomputable def tensorInducedMulHom :
    tensorInduced U hU s (of R U A) ⟶ of R G A :=
  letI : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  U.tensorInducedMulIntertwiningMap s R A

variable {R A}

/-- The underlying linear map of `DiscreteRep.tensorInducedMulHom` is that of
`Subgroup.tensorInducedMulAlgHom` for any `Fintype (G ⧸ U)` instance. -/
@[simp]
theorem tensorInducedMulHom_toLinearMap [Fintype (G ⧸ U)] :
    (tensorInducedMulHom U hU s R A).toLinearMap =
      (U.tensorInducedMulAlgHom s R A).toLinearMap := by
  have hF : U.fintypeQuotientOfFiniteIndex = ‹Fintype (G ⧸ U)› := Subsingleton.elim _ _
  rw [tensorInducedMulHom, hF]
  exact U.tensorInducedMulIntertwiningMap_toLinearMap s R A

/-- Applying `DiscreteRep.tensorInducedMulHom` evaluates `Subgroup.tensorInducedMulAlgHom`. -/
theorem tensorInducedMulHom_apply [Fintype (G ⧸ U)] (z : ⨂[R] _ : G ⧸ U, A) :
    (tensorInducedMulHom U hU s R A).toLinearMap z = U.tensorInducedMulAlgHom s R A z :=
  LinearMap.congr_fun (tensorInducedMulHom_toLinearMap U hU s (R := R) (A := A)) z

/-- On a pure tensor, `DiscreteRep.tensorInducedMulHom` multiplies the coset-translated factors
`r_s(x) • m x`. -/
theorem tensorInducedMulHom_tprod [Fintype (G ⧸ U)] (m : G ⧸ U → A) :
    (tensorInducedMulHom U hU s R A).toLinearMap (PiTensorProduct.tprod R m) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • m x := by
  rw [tensorInducedMulHom_apply, Subgroup.tensorInducedMulAlgHom_tprod]

/-- **Change-of-transversal invariance in `DiscreteRep`**: precomposing transversal multiplication
along `s` with the comparison `tensorInducedChangeTransversalIso` from `t` to `s` gives transversal
multiplication along `t`. -/
@[reassoc (attr := simp)]
theorem tensorInducedChangeTransversalIso_hom_tensorInducedMulHom :
    (tensorInducedChangeTransversalIso U hU s t (of R U A)).hom ≫
        tensorInducedMulHom U hU s R A =
      tensorInducedMulHom U hU t R A := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  rw [comp_toLinearMap, LinearMap.comp_apply, tensorInducedChangeTransversalIso_hom_toLinearMap,
    tensorInducedMulHom_toLinearMap, tensorInducedMulHom_toLinearMap]
  exact U.tensorInducedMulAlgHom_changeTransversal s t R A z

/-- Precomposing transversal multiplication along `t` with the inverse change-of-transversal
comparison gives transversal multiplication along `s`. -/
@[reassoc (attr := simp)]
theorem tensorInducedChangeTransversalIso_inv_tensorInducedMulHom :
    (tensorInducedChangeTransversalIso U hU s t (of R U A)).inv ≫
        tensorInducedMulHom U hU t R A =
      tensorInducedMulHom U hU s R A := by
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
      U.tensorInducedAlgAut s R A g z :=
  (toSmoothDiscrete_obj_obj_ρ_apply _ g z).trans <|
    (DiscreteRep.tensorInduced_ρ_apply U hU s _ g z).trans
      (U.tensorInducedAlgAut_apply s R A g z).symm

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
    (map_one (U.tensorInducedAlgAut s R A g))

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
  exact map_mul (U.tensorInducedAlgAut s R A g) x y

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

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]
  (A : Type (max v u)) [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A]

/-- **Transversal multiplication in `SmoothDiscreteTopRep`**: for an open finite-index subgroup
`U ≤ G` and a discrete commutative `G`-algebra `A` with continuous `G`-action, the morphism of
smooth discrete topological representations carrying `⨂ₜ x, m x` to `∏ x, r_s(x) • m x`.

Its source is written in the `smoothTensorInductionFunctor_obj` normal form
`(toSmoothDiscrete R G).obj (DiscreteRep.tensorInduced U hU s
((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))`, matching
`smoothTensorInducedChangeTransversalIso` and `TopPairing.smoothTensorInduced` on the nose. -/
noncomputable def smoothTensorInducedMulHom :
    (toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A))) ⟶
      SmoothDiscreteTopRep.of R G A :=
  (toSmoothDiscrete R G).map (DiscreteRep.tensorInducedMulHom U hU s R A)

variable {R G A}

/-- Applying `smoothTensorInducedMulHom` on the underlying module evaluates
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem smoothTensorInducedMulHom_hom_hom_apply [Fintype (G ⧸ U)] (z : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom R G U hU s A).hom.hom z =
      U.tensorInducedMulAlgHom s R A z :=
  (toSmoothDiscrete_map_hom_hom_apply R G
    (DiscreteRep.tensorInducedMulHom U hU s R A) z).trans
    (DiscreteRep.tensorInducedMulHom_apply U hU s z)

/-- On a pure tensor, `smoothTensorInducedMulHom` multiplies `r_s(x) • m x` over the cosets. -/
@[simp]
theorem smoothTensorInducedMulHom_hom_hom_tprod [Fintype (G ⧸ U)] (m : G ⧸ U → A) :
    (smoothTensorInducedMulHom R G U hU s A).hom.hom (PiTensorProduct.tprod R m) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • m x :=
  (smoothTensorInducedMulHom_hom_hom_apply U hU s (PiTensorProduct.tprod R m)).trans
    (U.tensorInducedMulAlgHom_tprod s R A m)

/-- `smoothTensorInducedMulHom` preserves multiplication on underlying carriers. -/
theorem smoothTensorInducedMulHom_hom_hom_mul (x y : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom R G U hU s A).hom.hom (x * y) =
      (smoothTensorInducedMulHom R G U hU s A).hom.hom x *
        (smoothTensorInducedMulHom R G U hU s A).hom.hom y := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  simp only [smoothTensorInducedMulHom_hom_hom_apply, map_mul]
  -- Multiplication on `(SmoothDiscreteTopRep.of R G A).obj.V` is `inferInstanceAs (Monoid A)`.
  rfl

/-- **Change-of-transversal invariance in `SmoothDiscreteTopRep`**: precomposing
`smoothTensorInducedMulHom` along `s` with `smoothTensorInducedChangeTransversalIso` from `t` to
`s` gives `smoothTensorInducedMulHom` along `t`. -/
@[reassoc (attr := simp)]
theorem smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom :
    (smoothTensorInducedChangeTransversalIso U hU s t (SmoothDiscreteTopRep.of R U A)).hom ≫
        smoothTensorInducedMulHom R G U hU s A =
      smoothTensorInducedMulHom R G U hU t A := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  -- Type the underlying linear maps on `⨂[R] _ : G ⧸ U, A` and `A` explicitly so tensor
  -- induction reduces to pure tensors without unfolding sealed coefficient wrappers.
  let e : (⨂[R] _ : G ⧸ U, A) →ₗ[R] ⨂[R] _ : G ⧸ U, A :=
    (smoothTensorInducedChangeTransversalIso U hU s t
      (SmoothDiscreteTopRep.of R U A)).hom.hom.hom.toLinearMap
  let μs : (⨂[R] _ : G ⧸ U, A) →ₗ[R] A :=
    (smoothTensorInducedMulHom R G U hU s A).hom.hom.toLinearMap
  let μt : (⨂[R] _ : G ⧸ U, A) →ₗ[R] A :=
    (smoothTensorInducedMulHom R G U hU t A).hom.hom.toLinearMap
  have he (m : G ⧸ U → A) :
      e (PiTensorProduct.tprod R m) =
        U.tensorInducedChangeTransversalAlgEquiv s t R A (PiTensorProduct.tprod R m) :=
    (smoothTensorInducedChangeTransversalIso_hom_apply_tprod U hU s t
      (SmoothDiscreteTopRep.of R U A) m).trans
      (U.tensorInducedChangeTransversalAlgEquiv_tprod s t R A m).symm
  have hμs (z : ⨂[R] _ : G ⧸ U, A) : μs z = U.tensorInducedMulAlgHom s R A z :=
    smoothTensorInducedMulHom_hom_hom_apply U hU s z
  have hμt (z : ⨂[R] _ : G ⧸ U, A) : μt z = U.tensorInducedMulAlgHom t R A z :=
    smoothTensorInducedMulHom_hom_hom_apply U hU t z
  have hlin (z : ⨂[R] _ : G ⧸ U, A) : μs (e z) = μt z := by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      rw [map_smul, map_smul, map_smul, he, hμs, hμt,
        U.tensorInducedMulAlgHom_changeTransversalAlgEquiv]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  exact DFunLike.ext _ _ hlin

/-- Precomposing `smoothTensorInducedMulHom` along `t` with the inverse smooth
change-of-transversal isomorphism gives `smoothTensorInducedMulHom` along `s`. -/
@[reassoc (attr := simp)]
theorem smoothTensorInducedChangeTransversalIso_inv_smoothTensorInducedMulHom :
    (smoothTensorInducedChangeTransversalIso U hU s t (SmoothDiscreteTopRep.of R U A)).inv ≫
        smoothTensorInducedMulHom R G U hU t A =
      smoothTensorInducedMulHom R G U hU s A := by
  rw [Iso.inv_comp_eq, smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom]

/-- On continuous cohomology, composing the change-of-transversal coefficient map from `t` to `s`
with the multiplication coefficient map along `s` gives the multiplication coefficient map along
`t`. -/
theorem coeffMap_smoothTensorInducedChangeTransversalIso_hom_comp_coeffMap_smoothTensorInducedMulHom
    (n : ℕ) :
    ContinuousCohomology.coeffMap
        (smoothTensorInducedChangeTransversalIso U hU s t
          (SmoothDiscreteTopRep.of R U A)).hom.hom n ≫
      ContinuousCohomology.coeffMap (smoothTensorInducedMulHom R G U hU s A).hom n =
      ContinuousCohomology.coeffMap (smoothTensorInducedMulHom R G U hU t A).hom n := by
  rw [← ContinuousCohomology.coeffMap_comp]
  exact congrArg (fun f :
      (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU t
          ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A))) ⟶
        SmoothDiscreteTopRep.of R G A ↦
    ContinuousCohomology.coeffMap f.hom n)
    (smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom U hU s t)

/-- `smoothTensorInducedMulHom` intertwines the tensor-induced multiplication pairing with the
canonical multiplication pairing `SmoothDiscreteTopRep.ofMulPairing R G A`. -/
theorem smoothTensorInducedMulHom_apply_smoothTensorInduced_bil
    (x y : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom R G U hU s A).hom.hom
        (((SmoothDiscreteTopRep.ofMulPairing R U A).smoothTensorInduced.{u, v, max v u} U hU s
          (A := SmoothDiscreteTopRep.of R U A)
          (B := SmoothDiscreteTopRep.of R U A)
          (C := SmoothDiscreteTopRep.of R U A)).bil x y) =
      (SmoothDiscreteTopRep.ofMulPairing R G A).bil
        ((smoothTensorInducedMulHom R G U hU s A).hom.hom x)
        ((smoothTensorInducedMulHom R G U hU s A).hom.hom y) := by
  rw [smoothTensorInduced_ofMulPairing_bil_apply, SmoothDiscreteTopRep.ofMulPairing_bil]
  exact smoothTensorInducedMulHom_hom_hom_mul U hU s x y

/-- **Cup-product compatibility of smooth tensor-induced multiplication**: on continuous
cohomology, `ContinuousCohomology.coeffMap` along `smoothTensorInducedMulHom` carries the cup
product for the tensor-induced multiplication pairing to the canonical multiplication cup product
on `(SmoothDiscreteTopRep.of R G A).obj` in every bidegree `(m, n)`. -/
theorem cup_coeffMap_smoothTensorInducedMulHom (m n : ℕ)
    (a : continuousCohomology m
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj)
    (b : continuousCohomology n
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj (SmoothDiscreteTopRep.of R U A)))).obj) :
    ContinuousCohomology.coeffMap (smoothTensorInducedMulHom R G U hU s A).hom (m + n)
        (((SmoothDiscreteTopRep.ofMulPairing R U A).smoothTensorInduced.{u, v, max v u} U hU s
          (A := SmoothDiscreteTopRep.of R U A)
          (B := SmoothDiscreteTopRep.of R U A)
          (C := SmoothDiscreteTopRep.of R U A)).cup.{u, v, max v u} m n a b) =
      (SmoothDiscreteTopRep.ofMulPairing R G A).cup.{u, v, max v u} m n
        (ContinuousCohomology.coeffMap (smoothTensorInducedMulHom R G U hU s A).hom m a)
        (ContinuousCohomology.coeffMap (smoothTensorInducedMulHom R G U hU s A).hom n b) :=
  ((SmoothDiscreteTopRep.ofMulPairing R U A).smoothTensorInduced.{u, v, max v u} U hU s
    (A := SmoothDiscreteTopRep.of R U A)
    (B := SmoothDiscreteTopRep.of R U A)
    (C := SmoothDiscreteTopRep.of R U A)).cup_coeffMap.{u, v, max v u}
    (SmoothDiscreteTopRep.ofMulPairing R G A)
    (smoothTensorInducedMulHom R G U hU s A).hom
    (smoothTensorInducedMulHom R G U hU s A).hom
    (smoothTensorInducedMulHom R G U hU s A).hom
    (fun (x y : ⨂[R] _ : G ⧸ U, A) ↦
      smoothTensorInducedMulHom_apply_smoothTensorInduced_bil U hU s x y)
    m n a b

end SmoothMultiplication

/-! ### Concrete specialization to discrete commutative `G`-rings (`R = ℤ`) -/

section Examples

/-- For any discrete commutative `G`-ring `A` (with `R = ℤ`), `SmoothDiscreteTopRep.ofMulPairing`
and `cup_coeffMap_smoothTensorInducedMulHom` apply in the group's own universe `v` without extra
scalar-continuity hypotheses, while `simp` discharges `.flip` symmetry and operator `1` / `*`
preservation on the smooth tensor-induced representation. -/
example {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) (s : U.toSubgroup.LeftTransversal) [U.toSubgroup.FiniteIndex]
    (A : Type v) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [ContinuousSMul G A] (m n : ℕ)
    (a : continuousCohomology m
      ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj)
    (b : continuousCohomology n
      ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' s
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj
            (SmoothDiscreteTopRep.of ℤ U.toSubgroup A)))).obj) :
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
    ContinuousCohomology.coeffMap
        (smoothTensorInducedMulHom ℤ G U.toSubgroup U.isOpen' s A).hom (m + n)
        (((SmoothDiscreteTopRep.ofMulPairing ℤ U.toSubgroup A).smoothTensorInduced.{0, v, v}
          U.toSubgroup U.isOpen' s
          (A := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)
          (B := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)
          (C := SmoothDiscreteTopRep.of ℤ U.toSubgroup A)).cup.{0, v, v} m n a b) =
      (SmoothDiscreteTopRep.ofMulPairing ℤ G A).cup.{0, v, v} m n
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedMulHom ℤ G U.toSubgroup U.isOpen' s A).hom m a)
        (ContinuousCohomology.coeffMap
          (smoothTensorInducedMulHom ℤ G U.toSubgroup U.isOpen' s A).hom n b) :=
  ⟨by simp, by simp,
    cup_coeffMap_smoothTensorInducedMulHom U.toSubgroup U.isOpen' s m n a b⟩

end Examples

end TauCeti
