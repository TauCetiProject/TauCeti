/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.BaseChange
-- Private: right exactness of the tensor product is used only inside the proof of
-- `TauCeti.baseChangeModNEquiv`; no statement of this file mentions it.
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The reduction of a `G`-module to a coefficient ring

A **`G`-module** is an abelian group `V` carrying a `DistribMulAction G V`, that is, a
`ℤ[G]`-module whose `ℤ`-module structure is the canonical one. Its **reduction** to a commutative
ring `k` is the representation of `G` on `k ⊗[ℤ] V` that acts on the right-hand factor. This file
builds that reduction as an object of `FDRep k G`, together with the two pieces of input it needs:
the action of `G` on the `n`-torsion subgroup `V[n]`, which is the other `G`-module whose reduction
enters the picture, and a criterion for `k ⊗[ℤ] V` to be a finite `k`-module.

The criterion is the one that makes the whole construction usable in characteristic `ℓ`: `V` itself
is typically infinite (a `ℤ`-lattice, say), so `k ⊗[ℤ] V` can only be finite-dimensional because the
coefficients kill `ℓ`. Concretely, `k ⊗[ℤ] −` applied to the right exact sequence
`V --(ℓ • ·)--> V --> V/ℓV --> 0` has zero left-hand map, since multiplication by `ℓ` on `k ⊗[ℤ] V`
is multiplication by the scalar `(ℓ : k) = 0`; right exactness of the tensor product therefore turns
the quotient map into an isomorphism `k ⊗[ℤ] V ≅ k ⊗[ℤ] (V/ℓV)` (`TauCeti.baseChangeModNEquiv`).
Finiteness of `V/ℓV` — Mathlib's `ModN V ℓ` — then suffices
(`TauCeti.finite_baseChange_of_finite_modN`), and Mathlib's `ModN.instFinite` supplies it for a
finitely generated `V`, a `ℤ`-lattice in particular.

The `G`-action on `V[n]` is the restriction of the action on `V`: the `n`-torsion condition
`n • x = 0` is preserved because `g • −` is additive, hence commutes with `n • −`. It is packaged as
a `def` rather than an `instance` because `AddSubgroup.torsionBy` is a reducible abbreviation for a
submodule, so a global instance on it would be found by unification in unrelated situations; make it
local with `attribute [local instance]`, or supply it with `letI`, where it is wanted.

## Implementation notes

`TauCeti.reduction` and `TauCeti.torsionByDistribMulAction` are `@[expose]`: a consumer has to see
that the carrier of the reduction is `k ⊗[ℤ] V` in order to state anything about it at all, and
`TauCeti.reduction_ρ` and `TauCeti.coe_smul_torsionBy` then hold by `rfl`.

## Main definitions

* `TauCeti.torsionByDistribMulAction`: the action of `G` on the `n`-torsion subgroup `V[n]` of a
  `G`-module `V`.
* `TauCeti.reduction`: the reduction `k ⊗[ℤ] V` of a `G`-module, as an object of `FDRep k G`.
* `TauCeti.baseChangeModNEquiv`: in characteristic `ℓ`, the comparison
  `k ⊗[ℤ] V ≃ₗ[k] k ⊗[ℤ] (V/ℓV)`.

## Main results

* `TauCeti.finite_baseChange_of_finite_modN`: in characteristic `ℓ`, a `G`-module with finite
  `V/ℓV` has finite reduction, so that `TauCeti.reduction` applies to it.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed. (2008), §VII.3,
  (7.3.3), where the reduction of a `G`-module modulo `ℓ` and its torsion companion are the two
  terms of the lattice defect.
* [Modular-induction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ModularInduction/README.md),
  Layer 3, "Torsion and reduction".
-/

public section

namespace TauCeti

open TensorProduct

universe u v

section TorsionAction

variable (G : Type v) [Monoid G] (V : Type u) [AddCommGroup V] [DistribMulAction G V] (n : ℕ)

/-- **The `n`-torsion subgroup of a `G`-module is stable under the action.** The action of `g` is
additive, so it commutes with multiplication by `n`. -/
theorem smul_mem_torsionBy (g : G) {x : V} (hx : x ∈ AddSubgroup.torsionBy V n) :
    g • x ∈ AddSubgroup.torsionBy V n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hx ⊢
  rw [smul_comm, hx, smul_zero]

/-- **The `G`-action on the `n`-torsion subgroup `V[n]`**, restricted from the action on `V` by
`TauCeti.smul_mem_torsionBy`.

This is not a global instance: `AddSubgroup.torsionBy` is a reducible abbreviation, so an instance
on it would be tried against the underlying submodule in unrelated goals. Introduce it with
`attribute [local instance]` or `letI` where it is needed; `TauCeti.coe_smul_torsionBy` is then the
only interface it has, and it determines the action completely. -/
@[expose, instance_reducible]
def torsionByDistribMulAction : DistribMulAction G (AddSubgroup.torsionBy V n) where
  smul g x := ⟨g • (x : V), smul_mem_torsionBy G V n g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : V))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : V))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : V) (y : V))

attribute [local instance] torsionByDistribMulAction

/-- The action of `TauCeti.torsionByDistribMulAction` on `V[n]` is the action of `G` on `V`. -/
@[simp]
theorem coe_smul_torsionBy (g : G) (x : AddSubgroup.torsionBy V n) :
    ((g • x : AddSubgroup.torsionBy V n) : V) = g • (x : V) :=
  rfl

end TorsionAction

section Reduction

variable (k : Type u) [CommRing k] (G : Type v) [Monoid G]
variable (V : Type u) [AddCommGroup V] [DistribMulAction G V]

/-- **The reduction of a `G`-module `V` to `k`**: the representation of `G` on `k ⊗[ℤ] V` acting on
the right-hand tensor factor, bundled as an object of `FDRep k G`.

The `G`-module structure is used through Mathlib's `Representation.ofDistribMulAction` over `ℤ`,
whose scalars are then extended by `Representation.baseChange`. The finiteness hypothesis is a
genuine restriction on `V`: `TauCeti.finite_baseChange_of_finite_modN` supplies it in characteristic
`ℓ` from finiteness of `V/ℓV`. -/
@[expose]
noncomputable def reduction [Module.Finite k (k ⊗[ℤ] V)] : FDRep k G :=
  FDRep.of (Representation.baseChange k (Representation.ofDistribMulAction ℤ G V))

/-- The representation underlying `TauCeti.reduction` is the base change to `k` of the `G`-module
structure of `V`. -/
theorem reduction_ρ [Module.Finite k (k ⊗[ℤ] V)] :
    (reduction k G V).ρ = Representation.baseChange k (Representation.ofDistribMulAction ℤ G V) :=
  rfl

/-- `g` acts on the reduction by acting on the right-hand tensor factor. -/
@[simp]
theorem reduction_ρ_tmul [Module.Finite k (k ⊗[ℤ] V)] (g : G) (a : k) (x : V) :
    (reduction k G V).ρ g (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] (g • x) := by
  -- `TauCeti.reduction_ρ` cannot be rewritten with directly: the type of the argument
  -- `a ⊗ₜ[ℤ] x` mentions the carrier of `reduction k G V`, so the motive is dependent.
  have h : (reduction k G V).ρ g (a ⊗ₜ[ℤ] x)
      = Representation.baseChange k (Representation.ofDistribMulAction ℤ G V) g (a ⊗ₜ[ℤ] x) :=
    rfl
  rw [h, Representation.baseChange_apply, LinearMap.baseChange_tmul,
    Representation.ofDistribMulAction_apply_apply]

end Reduction

section ModN

variable (k : Type u) [CommRing k] (ℓ : ℕ) [CharP k ℓ] (V : Type u) [AddCommGroup V]

/-- Multiplication by `ℓ` on `V` becomes the zero map after tensoring with a ring of characteristic
`ℓ`: it is multiplication by the scalar `(ℓ : k) = 0`. -/
private theorem lTensor_lsmul_natCast_eq_zero :
    LinearMap.lTensor k (LinearMap.lsmul ℤ V (ℓ : ℤ)) = 0 := by
  have hk : ((ℓ : ℤ) : k) = 0 := by
    rw [Int.cast_natCast, CharP.cast_eq_zero]
  refine LinearMap.ext fun x ↦ ?_
  induction x with
  | tmul a x =>
    rw [LinearMap.lTensor_tmul, LinearMap.lsmul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul, hk,
      zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  | add x y hx hy => simp [hx, hy]

/-- **In characteristic `ℓ` the reduction of `V` only sees `V/ℓV`.** Tensoring the right exact
sequence `V --(ℓ • ·)--> V --> V/ℓV --> 0` with `k` leaves the quotient map surjective, and its
kernel is the image of multiplication by `ℓ`, which is zero because `(ℓ : k) = 0`. -/
noncomputable def baseChangeModNEquiv : (k ⊗[ℤ] V) ≃ₗ[k] (k ⊗[ℤ] ModN V ℓ) :=
  LinearEquiv.ofBijective
    (LinearMap.baseChange k (Submodule.mkQ (LinearMap.range (LinearMap.lsmul ℤ V (ℓ : ℤ)))))
    (by
      have hsurj := Submodule.mkQ_surjective (LinearMap.range (LinearMap.lsmul ℤ V (ℓ : ℤ)))
      have hexact := lTensor_exact (R := ℤ) k
        (LinearMap.exact_map_mkQ_range (LinearMap.lsmul ℤ V (ℓ : ℤ))) hsurj
      rw [lTensor_lsmul_natCast_eq_zero k ℓ V, LinearMap.exact_zero_iff_injective] at hexact
      constructor
      · simpa [LinearMap.baseChange_eq_ltensor] using hexact
      · simpa [LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective k hsurj)

/-- The comparison `TauCeti.baseChangeModNEquiv` is the base change of the quotient map. -/
@[simp]
theorem baseChangeModNEquiv_tmul (a : k) (x : V) :
    baseChangeModNEquiv k ℓ V (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] (ModN.mkQ ℓ x) := by
  simp only [baseChangeModNEquiv]
  rfl

/-- **A `G`-module with finite reduction modulo `ℓ` has a finite-dimensional reduction to `k`**, in
characteristic `ℓ`. This is what lets `TauCeti.reduction` be formed for an infinite `V`, a
`ℤ`-lattice in particular. -/
theorem finite_baseChange_of_finite_modN [Finite (ModN V ℓ)] : Module.Finite k (k ⊗[ℤ] V) :=
  Module.Finite.equiv (baseChangeModNEquiv k ℓ V).symm

end ModN

end TauCeti
