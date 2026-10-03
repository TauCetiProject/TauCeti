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
is typically infinite (a `ℤ`-lattice, say), so `k ⊗[ℤ] V` can only be a finite `k`-module because
the coefficients kill `ℓ`. Concretely, `k ⊗[ℤ] −` applied to the right exact sequence
`V --(ℓ • ·)--> V --> V/ℓV --> 0` has zero left-hand map, since multiplication by `ℓ` on `k ⊗[ℤ] V`
is multiplication by the scalar `(ℓ : k)`, which vanishes; right exactness of the tensor product
therefore turns the quotient map into an isomorphism `k ⊗[ℤ] V ≅ k ⊗[ℤ] (V/ℓV)`
(`TauCeti.baseChangeModNEquiv`). Finiteness of `V/ℓV` — Mathlib's `ModN V ℓ` — over `ℤ` then
suffices (`TauCeti.finite_baseChange_of_finite_modN`), and for `ℓ ≠ 0` Mathlib's `ModN.instFinite`
even makes `V/ℓV` a finite type as soon as `V` is finitely generated, a `ℤ`-lattice in particular.

The `G`-action on `V[n]` is the restriction of the action on `V`: the `n`-torsion condition
`n • x = 0` is preserved because `g • −` is additive, hence commutes with `n • −`. It is packaged as
a `def` rather than an `instance` because `AddSubgroup.torsionBy` is a reducible abbreviation for a
submodule, so a global instance on it would be found by unification in unrelated situations; make it
local with `attribute [local instance]`, or supply it with `letI`, where it is wanted.

## Implementation notes

`TauCeti.reduction` is `@[expose]`: a consumer has to see that the carrier of the reduction is
`k ⊗[ℤ] V` in order to state anything about it at all, and `TauCeti.reduction_ρ` then holds by
`rfl`. `TauCeti.torsionByDistribMulAction` is not exposed: `TauCeti.coe_smul_torsionBy` is its
complete interface, and it is proved by `(rfl)`, which does not make consumers depend on the body.

## Main definitions

* `TauCeti.torsionByDistribMulAction`: the action of `G` on the `n`-torsion subgroup `V[n]` of a
  `G`-module `V`.
* `TauCeti.reduction`: the reduction `k ⊗[ℤ] V` of a `G`-module, as an object of `FDRep k G`.
* `TauCeti.baseChangeModNEquiv`: the comparison `k ⊗[ℤ] V ≃ₗ[k] k ⊗[ℤ] (V/ℓV)`, for any `ℓ` with
  `(ℓ : k) = 0`.

## Main results

* `TauCeti.finite_baseChange_of_finite_modN`: in characteristic `ℓ`, an abelian group `V` with
  `V/ℓV` finite over `ℤ` has `k ⊗[ℤ] V` finite over `k`, so that `TauCeti.reduction` applies to it.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed. (2008), §VII.3,
  (7.3.3), where the reduction of a `G`-module modulo `ℓ` and its torsion companion are the two
  terms of the lattice defect.
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
@[instance_reducible]
def torsionByDistribMulAction : DistribMulAction G (AddSubgroup.torsionBy V n) :=
  letI : SMul G (AddSubgroup.torsionBy V n) :=
    ⟨fun g x ↦ ⟨g • (x : V), smul_mem_torsionBy G V n g x.2⟩⟩
  Function.Injective.distribMulAction (AddSubgroup.torsionBy V n).subtype
    Subtype.coe_injective fun _ _ ↦ rfl

attribute [local instance] torsionByDistribMulAction

/-- The action of `TauCeti.torsionByDistribMulAction` on `V[n]` is the action of `G` on `V`. -/
@[simp]
theorem coe_smul_torsionBy (g : G) (x : AddSubgroup.torsionBy V n) :
    ((g • x : AddSubgroup.torsionBy V n) : V) = g • (x : V) :=
  (rfl)

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

variable (k : Type u) [CommRing k] (ℓ : ℕ) (V : Type u) [AddCommGroup V]

/-- Multiplication by `ℓ` on `V` becomes the zero map after tensoring with a ring in which the
scalar `(ℓ : k)` vanishes. -/
private theorem lTensor_lsmul_natCast_eq_zero (hℓ : (ℓ : k) = 0) :
    LinearMap.lTensor k (LinearMap.lsmul ℤ V (ℓ : ℤ)) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  induction x with
  | tmul a x =>
    rw [LinearMap.lTensor_tmul, LinearMap.lsmul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul,
      Int.cast_natCast, hℓ, zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  | add x y hx hy => simp [hx, hy]

/-- Tensoring the right exact sequence `V --(ℓ • ·)--> V --> V/ℓV --> 0` with `k` leaves the
quotient map surjective, and its kernel is the image of multiplication by `ℓ`, which is zero
because `(ℓ : k) = 0`. -/
private theorem bijective_baseChange_mkQ (hℓ : (ℓ : k) = 0) : Function.Bijective
    (LinearMap.baseChange k (Submodule.mkQ (LinearMap.range (LinearMap.lsmul ℤ V (ℓ : ℤ))))) := by
  have hsurj := Submodule.mkQ_surjective (LinearMap.range (LinearMap.lsmul ℤ V (ℓ : ℤ)))
  have hexact := lTensor_exact (R := ℤ) k
    (LinearMap.exact_map_mkQ_range (LinearMap.lsmul ℤ V (ℓ : ℤ))) hsurj
  rw [lTensor_lsmul_natCast_eq_zero k ℓ V hℓ, LinearMap.exact_zero_iff_injective] at hexact
  refine ⟨?_, ?_⟩
  · simpa [LinearMap.baseChange_eq_ltensor] using hexact
  · simpa [LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective k hsurj

/-- **When `(ℓ : k) = 0` the base change of `V` to `k` only sees `V/ℓV`.**

Only the vanishing of the scalar `(ℓ : k)` is used, not `[CharP k ℓ]`: `k` may have characteristic
a proper divisor of `ℓ`. -/
noncomputable def baseChangeModNEquiv (hℓ : (ℓ : k) = 0) :
    (k ⊗[ℤ] V) ≃ₗ[k] (k ⊗[ℤ] ModN V ℓ) :=
  LinearEquiv.ofBijective
    (LinearMap.baseChange k (Submodule.mkQ (LinearMap.range (LinearMap.lsmul ℤ V (ℓ : ℤ)))))
    (bijective_baseChange_mkQ k ℓ V hℓ)

/-- The comparison `TauCeti.baseChangeModNEquiv` is the base change of the quotient map. -/
@[simp]
theorem baseChangeModNEquiv_tmul (hℓ : (ℓ : k) = 0) (a : k) (x : V) :
    baseChangeModNEquiv k ℓ V hℓ (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] (ModN.mkQ ℓ x) := by
  -- `ModN.mkQ` has no interface lemma in Mathlib, so it is unfolded to `Submodule.mkQ`; the
  -- equivalence and its base-changed map are handled by their own interface lemmas.
  simp only [baseChangeModNEquiv, ModN.mkQ]
  rw [LinearEquiv.ofBijective_apply]
  exact LinearMap.baseChange_tmul ..

/-- **An abelian group whose reduction modulo `ℓ` is finite over `ℤ` has `k ⊗[ℤ] V` finite over
`k`**, in characteristic `ℓ`. This is what lets `TauCeti.reduction` be formed for an infinite `V`, a
`ℤ`-lattice in particular; a finite `V/ℓV` qualifies through `Module.Finite.of_finite`. -/
theorem finite_baseChange_of_finite_modN [CharP k ℓ] [Module.Finite ℤ (ModN V ℓ)] :
    Module.Finite k (k ⊗[ℤ] V) :=
  Module.Finite.equiv (baseChangeModNEquiv k ℓ V (CharP.cast_eq_zero k ℓ)).symm

end ModN

end TauCeti
