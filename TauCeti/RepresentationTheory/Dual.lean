/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.LinearAlgebra.Dual.Contraction
public import TauCeti.LinearAlgebra.LinearEquiv.Basic
public import TauCeti.RepresentationTheory.Invariants

/-!
# Invariants of the dual representation

The inverse automorphism of the dual representation is the transpose of the original
representation's automorphism.

The dual `ρ.dual` of a representation acts on functionals by `ψ ↦ ψ ∘ ρ g⁻¹`, so a functional
invariant for it is exactly one that the action of `G` on the space leaves unchanged:
`ψ (ρ g u) = ψ u`.  That characterization of membership in `ρ.dual.invariants` is all a
construction out of an invariant functional, or of one, ever needs.

Counting those invariants needs only an invertible `|G|`. An invariant functional factors through
the averaging projection onto `ρ.invariants`, and every functional on `ρ.invariants` extends
through it, so the invariant functionals are the `k`-dual of `ρ.invariants`: the dual has as many
invariants as the representation itself.

For a one-dimensional representation the dual is the inverse character: `Dual V ⊗ V` is the trivial
line.

Applied to `Dual X ⊗ Y`, whose invariants are the intertwiners `X → Y` and whose dual is
`Dual Y ⊗ X`, this counts intertwiners in both directions alike.

## Main results

* `TauCeti.Representation.mem_invariants_dual_iff`: a functional is invariant for `ρ.dual` exactly
  when the action of `G` leaves it unchanged, with
  `TauCeti.Representation.apply_of_mem_invariants_dual` the elimination direction.
* `TauCeti.Representation.finrank_invariants_dual`: **the dual of a representation has as many
  invariants as the representation** whenever `|G|` is invertible in `k`.
* `Representation.dualTprodEquivDualDualTprod`: `Dual W ⊗ V` is the dual of `Dual V ⊗ W` as
  representations.
* `Representation.dualTprodEquivTrivialOfFinrankEqOne`: for a line `V`, the contraction
  `Dual V ⊗ V → k` is an equivalence onto the trivial representation.
* `FDRep.finrank_invariants_dual_tprod`: the intertwiners `X → Y` are as many as the invariants
  of `Dual X ⊗ Y`.
* `FDRep.finrank_hom_comm`: when `|G|` is invertible in `k`, there are as many
  intertwiners `X → Y` as `Y → X`.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7, “Invariant bilinear forms”: the invariant forms of `ρ` are the intertwiners into
  `ρ.dual`, so counting them is counting invariants of a dual.
-/

public section

namespace Representation

/-- The inverse linear automorphism of the dual representation is the transpose of the
original representation's linear automorphism. -/
theorem generalLinearEquiv_dual_asGroupHom_symm
    {R G V : Type*} [CommSemiring R] [Group G] [AddCommMonoid V] [Module R V]
    (ρ : Representation R G V) (g : G) :
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (Module.Dual R V))
      (ρ.dual.asGroupHom g)).symm =
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V) (ρ.asGroupHom g)).dualMap := by
  rw [LinearEquiv.symm_eq_inv, ← map_inv, ← map_inv]
  ext φ v
  simp only [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    asGroupHom_apply, dual_apply, inv_inv, Module.Dual.transpose_apply,
    LinearEquiv.dualMap_apply, LinearMap.comp_apply]

end Representation

namespace TauCeti

open Module (finrank)

namespace Representation

/-! ### Invariant functionals -/

section Group

variable {k G V : Type*} [CommRing k] [Group G] [AddCommMonoid V] [Module k V]

/-- **A functional is invariant for the dual of a representation exactly when the action of `G`
leaves it unchanged.** -/
theorem mem_invariants_dual_iff {ρ : Representation k G V} {ψ : Module.Dual k V} :
    ψ ∈ ρ.dual.invariants ↔ ∀ (g : G) (u : V), ψ (ρ g u) = ψ u := by
  constructor
  · intro hψ g u
    have h := DFunLike.congr_fun (hψ g⁻¹) u
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h
  · refine fun h g => LinearMap.ext fun u => ?_
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h g⁻¹ u

/-- A functional invariant for the dual of a representation is unchanged by the action. -/
@[grind =]
theorem apply_of_mem_invariants_dual {ρ : Representation k G V} {ψ : Module.Dual k V}
    (hψ : ψ ∈ ρ.dual.invariants) (g : G) (u : V) : ψ (ρ g u) = ψ u :=
  mem_invariants_dual_iff.mp hψ g u

end Group

/-! ### Counting the invariants of a dual -/

section Averaging

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- **An invariant functional factors through the averaging projection**: averaging `u` over the
group does not change its value under a functional the action leaves unchanged. -/
theorem apply_averageMap_of_mem_invariants_dual [Fintype G] [Invertible (Fintype.card G : k)]
    {ρ : Representation k G V} {ψ : Module.Dual k V} (hψ : ψ ∈ ρ.dual.invariants) (u : V) :
    ψ (ρ.averageMap u) = ψ u := by
  rw [Representation.averageMap_eq_invOf_card_smul_norm, LinearMap.smul_apply, map_smul,
    Representation.norm, LinearMap.sum_apply, map_sum]
  simp only [apply_of_mem_invariants_dual hψ, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

end Averaging

section Finite

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable [Finite G] [Invertible (Nat.card G : k)]

/-- **The dual of a representation has as many invariants as the representation**, whenever `|G|`
is invertible in `k`. Restricting functionals to the invariants identifies the invariant functionals
with the `k`-dual of `ρ.invariants`: an invariant functional factors through the averaging
projection onto `ρ.invariants` (`apply_averageMap_of_mem_invariants_dual`), and every functional
on `ρ.invariants` extends through that projection to an invariant one. -/
theorem finrank_invariants_dual (ρ : Representation k G V) :
    finrank k ρ.dual.invariants = finrank k ρ.invariants := by
  have : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact (isUnit_of_invertible _).ne_zero)
  -- Restriction of an invariant functional to the invariants.
  let r : ρ.dual.invariants →ₗ[k] Module.Dual k ρ.invariants :=
    { toFun := fun ψ => (ψ : Module.Dual k V).comp ρ.invariants.subtype
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let avg : V →ₗ[k] ρ.invariants :=
    ρ.averageMap.codRestrict ρ.invariants ρ.averageMap_invariant
  have hr : Function.Bijective r := by
    refine ⟨fun ψ φ h => Subtype.ext (LinearMap.ext fun u => ?_), fun χ => ?_⟩
    · rw [← apply_averageMap_of_mem_invariants_dual ψ.2,
        ← apply_averageMap_of_mem_invariants_dual φ.2]
      exact DFunLike.congr_fun h (avg u)
    · refine ⟨⟨χ.comp avg, mem_invariants_dual_iff.2 fun g u => ?_⟩, ?_⟩
      · exact congrArg χ (Subtype.ext (LinearMap.congr_fun (ρ.averageMap_comp_ρ g) u))
      · exact LinearMap.ext fun v => congrArg χ (Subtype.ext (ρ.averageMap_id v v.2))
  rw [(LinearEquiv.ofBijective r hr).finrank_eq, Subspace.dual_finrank_eq]

end Finite

end Representation

end TauCeti

/-! ### Intertwiners in both directions -/

namespace Representation

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]

/-- **`Dual W ⊗ V` is the dual of `Dual V ⊗ W`** as representations,
`η ⊗ v ↦ (ξ ⊗ w ↦ ξ v · η w)`: the duality of tensor products `TensorProduct.dualDistribEquiv`
after the double-dual identification `Module.evalEquiv`. -/
noncomputable def dualTprodEquivDualDualTprod (ρ : Representation k G V)
    (σ : Representation k G W) :
    (tprod (dual σ) ρ).Equiv (dual (tprod (dual ρ) σ)) :=
  .mk ((_root_.TensorProduct.comm k _ _).trans
      ((_root_.TensorProduct.congr (Module.evalEquiv k V) (LinearEquiv.refl k _)).trans
        (_root_.TensorProduct.dualDistribEquiv k (Module.Dual k V) W))) fun g => by
    refine _root_.TensorProduct.ext' fun η v => _root_.TensorProduct.ext' fun ξ w => ?_
    simp [dual_apply, Module.Dual.transpose_apply, _root_.TensorProduct.dualDistribEquiv, mul_comm]

/-- The equivalence `dualTprodEquivDualDualTprod` sends a pure tensor to the functional obtained
by evaluating the two dual factors. -/
@[simp]
theorem dualTprodEquivDualDualTprod_tmul_apply (ρ : Representation k G V)
    (σ : Representation k G W) (η : Module.Dual k W) (v : V) (ξ : Module.Dual k V) (w : W) :
    dualTprodEquivDualDualTprod ρ σ (η ⊗ₜ[k] v) (ξ ⊗ₜ[k] w) = ξ v * η w := by
  simp [dualTprodEquivDualDualTprod, _root_.TensorProduct.dualDistribEquiv, mul_comm]

end Representation

/-! ### The dual of a line -/

namespace Representation

open Module (finrank)

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **The dual of a line tensored with the line is trivial.** For a one-dimensional
representation, the contraction `Dual V ⊗ V ≃ k`, `f ⊗ v ↦ f v`
(`TauCeti.contractLeftEquivOfFinrankEqOne`), is an equivalence onto the trivial
representation. -/
noncomputable def dualTprodEquivTrivialOfFinrankEqOne (ρ : Representation k G V)
    (h : finrank k V = 1) :
    (tprod (dual ρ) ρ).Equiv (trivial k G k) :=
  .mk (TauCeti.contractLeftEquivOfFinrankEqOne h) fun g ↦
    _root_.TensorProduct.ext' fun f v ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, tprod_apply, TensorProduct.map_tmul,
        LinearEquiv.coe_coe, TauCeti.contractLeftEquivOfFinrankEqOne_tmul, dual_apply,
        Module.Dual.transpose_apply, trivial_apply]
      rw [inv_self_apply]

@[simp]
theorem dualTprodEquivTrivialOfFinrankEqOne_tmul (ρ : Representation k G V)
    (h : finrank k V = 1) (f : Module.Dual k V) (v : V) :
    dualTprodEquivTrivialOfFinrankEqOne ρ h (f ⊗ₜ v) = f v :=
  TauCeti.contractLeftEquivOfFinrankEqOne_tmul h f v

end Representation

namespace FDRep

open CategoryTheory Module

universe u

variable {k G : Type u} [Field k] [Group G]

/-- **The intertwiners `X → Y` are as many as the invariants of `Dual X ⊗ Y`**: Mathlib's
contraction `Representation.Equiv.dualTensorHom` identifies `Dual X ⊗ Y` with `Hom_k(X, Y)` as
representations, whose invariants are the intertwiners
(`Representation.linHom.invariantsEquivFDRepHom`). -/
theorem finrank_invariants_dual_tprod (X Y : FDRep k G) :
    finrank k (Representation.invariants (V := TensorProduct k (Module.Dual k X) Y)
      (Representation.tprod (Representation.dual X.ρ) Y.ρ)) = finrank k (X ⟶ Y) :=
  ((Representation.Equiv.dualTensorHom X.ρ Y.ρ).invariantsLinearEquiv.trans
    (Representation.linHom.invariantsEquivFDRepHom X Y)).finrank_eq

/-- **There are as many intertwiners `X → Y` as `Y → X`** when `|G|` is invertible in `k`. The
intertwiners `X → Y` are the invariants of `Dual X ⊗ Y`, and those `Y → X` the invariants of its
dual `Dual Y ⊗ X` (`Representation.dualTprodEquivDualDualTprod`), which are as many
(`TauCeti.Representation.finrank_invariants_dual`). Over a semisimple group algebra this is the
symmetry of the multiplicity pairing of `X` and `Y`. -/
theorem finrank_hom_comm [Finite G] [Invertible (Nat.card G : k)] (X Y : FDRep k G) :
    finrank k (X ⟶ Y) = finrank k (Y ⟶ X) := by
  rw [← finrank_invariants_dual_tprod X Y, ← finrank_invariants_dual_tprod Y X,
    (Representation.Equiv.invariantsLinearEquiv (V := TensorProduct k (Module.Dual k Y) X)
      (Representation.dualTprodEquivDualDualTprod X.ρ Y.ρ)).finrank_eq,
    TauCeti.Representation.finrank_invariants_dual (V := TensorProduct k (Module.Dual k X) Y)]

end FDRep
