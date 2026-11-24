/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Restrict
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Completed group algebras are free over open subgroups

Let `H` be an open subgroup of finite index of a topological group `Γ`, for instance an open
subgroup of a profinite group. Through the algebra homomorphism `map R H.subtype _` induced by
the inclusion, `R[[Γ]]` is a left and a right module over `R[[H]]`. This file shows that both are
free of rank `[Γ : H]`:

* as a left `R[[H]]`-module (`r • x = r * x`), `R[[Γ]]` has the basis of group elements at any
  right transversal `T` of `H`, a set of representatives of the right cosets `H * t`;
* as a right `R[[H]]`-module (`R[[H]]ᵐᵒᵖ` acting by `op r • x = x * r`), `R[[Γ]]` has the basis of
  group elements at any left transversal `S` of `H`, a set of representatives of the left cosets
  `s * H`.

The coordinates are given by the restriction `completedGroupAlgebra.restrict` to `H`: the
coordinate of `x` at `t ∈ T` is the restriction of `x * t⁻¹`, and at `s ∈ S` that of `s⁻¹ * x`.
The bases are indexed by the transversals themselves, which have `[Γ : H]` elements
(`Subgroup.IsComplement.card_right`, `Subgroup.IsComplement.card_left`). They do not depend on any
level of the inverse limit, and for a commutative `Γ` the two bases at the same set of
representatives coincide.

Consequently a module over `R[[Γ]]` is finitely generated exactly when it is finitely generated
over `R[[H]]` (`finite_iff_finite`). For `R = ℤ_p` and `R = 𝔽_p` this is the statement, used
throughout noncommutative Iwasawa theory, that the Iwasawa algebra `Λ(G)` of a profinite group is
a free module of rank `[G : U]` over the Iwasawa algebra `Λ(U)` of an open subgroup `U`.

## Main definitions

* `TauCeti.completedGroupAlgebra.basisRightTransversal`: the basis of the left `R[[H]]`-module
  `R[[Γ]]` given by a right transversal of `H`.
* `TauCeti.completedGroupAlgebra.basisLeftTransversal`: the basis of the right `R[[H]]`-module
  `R[[Γ]]` given by a left transversal of `H`.

## Main results

* `TauCeti.completedGroupAlgebra.free_of_isOpen`, `TauCeti.completedGroupAlgebra.finite_of_isOpen`:
  `R[[Γ]]` is a free and finite left `R[[H]]`-module.
* `TauCeti.completedGroupAlgebra.free_mulOpposite_of_isOpen`,
  `TauCeti.completedGroupAlgebra.finite_mulOpposite_of_isOpen`: `R[[Γ]]` is a free and finite
  right `R[[H]]`-module.
* `TauCeti.completedGroupAlgebra.finrank_eq_index`,
  `TauCeti.completedGroupAlgebra.finrank_mulOpposite_eq_index`: the rank of `R[[Γ]]` over `R[[H]]`,
  on either side, is the index `[Γ : H]`, when `R[[H]]` satisfies the strong rank condition.
* `TauCeti.completedGroupAlgebra.finite_iff_finite`: an `R[[Γ]]`-module is finitely generated
  exactly when it is finitely generated over `R[[H]]`.

## References

* M. Lazard, *Groupes analytiques p-adiques*, Publ. Math. IHÉS 26 (1965), Chapitre II, (2.2.7).
* J. Coates, T. Fukaya, K. Kato, R. Sujatha, O. Venjakob, *The GL₂ main conjecture for elliptic
  curves without complex multiplication*, Publ. Math. IHÉS 101 (2005), §2.
-/

public section

namespace TauCeti.completedGroupAlgebra

universe u v

variable (R : Type u) [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
  [SeparatelyContinuousMul Γ] {H : Subgroup Γ} (hH : IsOpen (H : Set Γ)) [H.FiniteIndex]

/-! ### The left module -/

section Left

variable {T : Set Γ} (hT : Subgroup.IsComplement (H : Set Γ) T)

include hH hT

/-- The coordinates of an element `x` of `R[[Γ]]` along a right transversal `T` of `H`: the
restrictions of the `x * t⁻¹`, `t ∈ T`. -/
private noncomputable def rightCoordinates :
    letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
    completedGroupAlgebra R Γ ≃ₗ[completedGroupAlgebra R H] (T → completedGroupAlgebra R H) :=
  letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  letI := hT.finite_right.fintype
  { toFun x t := restrict R hH (x * of R Γ (t : Γ)⁻¹)
    invFun a := ∑ t : T, map R H.subtype H.continuous_subtype (a t) * of R Γ (t : Γ)
    map_add' x y := funext fun t ↦ by simp only [add_mul, map_add, Pi.add_apply]
    map_smul' c x := funext fun t ↦ by
      simp only [RingHom.toModule_smul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mul_assoc,
        restrict_map_mul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    left_inv x := sum_map_restrict_mul_of R hH hT x
    right_inv a := funext fun t ↦ by
      classical
      simp only [Finset.sum_mul, map_sum, mul_assoc, restrict_map_mul,
        restrict_of_mul_inv_of_isComplement R hH hT, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true] }

/-- **The coset basis of a completed group algebra over an open subgroup.** For an open subgroup
`H` of finite index and a right transversal `T` of `H`, the group elements at the points of `T`
form a basis of `R[[Γ]]` as a left `R[[H]]`-module, `R[[H]]` acting by left multiplication through
the inclusion. The coordinate of `x` at `t` is the restriction of `x * t⁻¹` to `H`
(`basisRightTransversal_repr_apply`). -/
noncomputable def basisRightTransversal :
    letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
    Module.Basis T (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) :=
  letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  have := hT.finite_right.to_subtype
  .ofEquivFun (rightCoordinates R hH hT)

/-- The basis vector of `basisRightTransversal` at `t` is the group element `t`. -/
@[simp]
theorem basisRightTransversal_apply (t : T) :
    basisRightTransversal R hH hT t = of R Γ (t : Γ) := by
  classical
  let _ := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  have := hT.finite_right.to_subtype
  let _ := hT.finite_right.fintype
  rw [basisRightTransversal, Module.Basis.coe_ofEquivFun]
  simp only [rightCoordinates, LinearEquiv.coe_symm_mk', Pi.single_apply, apply_ite, map_one,
    map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The coordinate of `x` at `t` for `basisRightTransversal` is the restriction of `x * t⁻¹` to
`H`. -/
@[simp]
theorem basisRightTransversal_repr_apply (x : completedGroupAlgebra R Γ) (t : T) :
    letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
    (basisRightTransversal R hH hT).repr x t = restrict R hH (x * of R Γ (t : Γ)⁻¹) := by
  let _ := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  have := hT.finite_right.to_subtype
  rw [basisRightTransversal, Module.Basis.ofEquivFun_repr_apply]
  rfl

end Left

include hH in
/-- **A completed group algebra is free over an open subgroup** of finite index, as a left
module. -/
theorem free_of_isOpen :
    letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
    Module.Free (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) :=
  letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  .of_basis (basisRightTransversal R hH (H.exists_isComplement_right 1).choose_spec.1)

include hH in
/-- **A completed group algebra is finite over an open subgroup** of finite index, as a left
module. -/
theorem finite_of_isOpen :
    letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
    Module.Finite (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) :=
  letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  let hT := (H.exists_isComplement_right 1).choose_spec.1
  have := hT.finite_right.to_subtype
  .of_basis (basisRightTransversal R hH hT)

include hH in
/-- **The rank of a completed group algebra over an open subgroup is the index**, as a left
module. The hypothesis `StrongRankCondition` makes the rank well behaved; it holds for instance
when `R[[H]]` is Noetherian (`IsNoetherianRing.strongRankCondition`). -/
theorem finrank_eq_index [StrongRankCondition (completedGroupAlgebra R H)] :
    letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
    Module.finrank (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) = H.index :=
  letI := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  let hT := (H.exists_isComplement_right 1).choose_spec.1
  (Module.finrank_eq_nat_card_basis (basisRightTransversal R hH hT)).trans hT.card_right

include hH in
/-- **Finite generation over an open subgroup.** Let `M` be an `R[[Γ]]`-module on which `R[[H]]`
acts through the inclusion. Then `M` is finitely generated over `R[[H]]` exactly when it is
finitely generated over `R[[Γ]]`. -/
theorem finite_iff_finite (M : Type*) [AddCommMonoid M] [Module (completedGroupAlgebra R Γ) M]
    [Module (completedGroupAlgebra R H) M]
    (hM : ∀ (a : completedGroupAlgebra R H) (m : M),
      a • m = map R H.subtype H.continuous_subtype a • m) :
    Module.Finite (completedGroupAlgebra R H) M ↔ Module.Finite (completedGroupAlgebra R Γ) M := by
  let _ := (map R H.subtype H.continuous_subtype).toRingHom.toModule
  have : IsScalarTower (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) M :=
    ⟨fun a x m ↦ by
      rw [hM, RingHom.toModule_smul, mul_smul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩
  have := finite_of_isOpen R hH
  exact ⟨fun _ ↦ .of_restrictScalars_finite (completedGroupAlgebra R H) _ M,
    fun _ ↦ .trans (completedGroupAlgebra R Γ) M⟩

/-! ### The right module -/

omit [SeparatelyContinuousMul Γ] [H.FiniteIndex] in
/-- The right action of `R[[H]]` on `R[[Γ]]`, through `R[[H]]ᵐᵒᵖ`, is right multiplication by the
image under the inclusion. -/
private theorem op_smul_eq_mul_map (c : (completedGroupAlgebra R H)ᵐᵒᵖ)
    (x : completedGroupAlgebra R Γ) :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    c • x = x * map R H.subtype H.continuous_subtype c.unop :=
  (rfl)

section Right

variable {S : Set Γ} (hS : Subgroup.IsComplement S (H : Set Γ))

include hH hS

/-- The coordinates of an element `x` of `R[[Γ]]` along a left transversal `S` of `H`: the
restrictions of the `s⁻¹ * x`, `s ∈ S`. -/
private noncomputable def leftCoordinates :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    completedGroupAlgebra R Γ ≃ₗ[(completedGroupAlgebra R H)ᵐᵒᵖ]
      (S → (completedGroupAlgebra R H)ᵐᵒᵖ) :=
  letI := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  letI := hS.finite_left.fintype
  { toFun x s := .op (restrict R hH (of R Γ (s : Γ)⁻¹ * x))
    invFun a := ∑ s : S, of R Γ (s : Γ) * map R H.subtype H.continuous_subtype (a s).unop
    map_add' x y := funext fun s ↦ by simp only [mul_add, map_add, MulOpposite.op_add,
      Pi.add_apply]
    map_smul' c x := funext fun s ↦ by
      rw [op_smul_eq_mul_map, ← mul_assoc, restrict_mul_map, RingHom.id_apply, Pi.smul_apply,
        smul_eq_mul, MulOpposite.op_mul, MulOpposite.op_unop]
    left_inv x := sum_of_mul_map_restrict R hH hS x
    right_inv a := funext fun s ↦ by
      classical
      simp only [Finset.mul_sum, map_sum, ← mul_assoc, restrict_mul_map,
        restrict_of_inv_mul_of_isComplement R hH hS, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, MulOpposite.op_unop] }

/-- **The coset basis of a completed group algebra over an open subgroup, on the right.** For an
open subgroup `H` of finite index and a left transversal `S` of `H`, the group elements at the
points of `S` form a basis of `R[[Γ]]` as a right `R[[H]]`-module, that is as a module over
`R[[H]]ᵐᵒᵖ` acting by `op a • x = x * a` through the inclusion. The coordinate of `x` at `s` is
the restriction of `s⁻¹ * x` to `H` (`basisLeftTransversal_repr_apply`). -/
noncomputable def basisLeftTransversal :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    Module.Basis S (completedGroupAlgebra R H)ᵐᵒᵖ (completedGroupAlgebra R Γ) :=
  letI := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  have := hS.finite_left.to_subtype
  .ofEquivFun (leftCoordinates R hH hS)

/-- The basis vector of `basisLeftTransversal` at `s` is the group element `s`. -/
@[simp]
theorem basisLeftTransversal_apply (s : S) :
    basisLeftTransversal R hH hS s = of R Γ (s : Γ) := by
  classical
  let _ := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  have := hS.finite_left.to_subtype
  let _ := hS.finite_left.fintype
  rw [basisLeftTransversal, Module.Basis.coe_ofEquivFun]
  simp only [leftCoordinates, LinearEquiv.coe_symm_mk', Pi.single_apply, apply_ite,
    MulOpposite.unop_one, MulOpposite.unop_zero, map_one, map_zero, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The coordinate of `x` at `s` for `basisLeftTransversal` is the restriction of `s⁻¹ * x` to
`H`. -/
@[simp]
theorem basisLeftTransversal_repr_apply (x : completedGroupAlgebra R Γ) (s : S) :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    (basisLeftTransversal R hH hS).repr x s = .op (restrict R hH (of R Γ (s : Γ)⁻¹ * x)) := by
  let _ := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  have := hS.finite_left.to_subtype
  rw [basisLeftTransversal, Module.Basis.ofEquivFun_repr_apply]
  rfl

end Right

include hH in
/-- **A completed group algebra is free over an open subgroup** of finite index, as a right
module. -/
theorem free_mulOpposite_of_isOpen :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    Module.Free (completedGroupAlgebra R H)ᵐᵒᵖ (completedGroupAlgebra R Γ) :=
  letI := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  .of_basis (basisLeftTransversal R hH (H.exists_isComplement_left 1).choose_spec.1)

include hH in
/-- **A completed group algebra is finite over an open subgroup** of finite index, as a right
module. -/
theorem finite_mulOpposite_of_isOpen :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    Module.Finite (completedGroupAlgebra R H)ᵐᵒᵖ (completedGroupAlgebra R Γ) :=
  letI := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  let hS := (H.exists_isComplement_left 1).choose_spec.1
  have := hS.finite_left.to_subtype
  .of_basis (basisLeftTransversal R hH hS)

include hH in
/-- **The rank of a completed group algebra over an open subgroup is the index**, as a right
module. The hypothesis `StrongRankCondition` holds for instance when `R[[H]]ᵐᵒᵖ` is Noetherian,
that is when `R[[H]]` is right Noetherian. -/
theorem finrank_mulOpposite_eq_index
    [StrongRankCondition (completedGroupAlgebra R H)ᵐᵒᵖ] :
    letI := Module.compHom (completedGroupAlgebra R Γ)
      (map R H.subtype H.continuous_subtype).toRingHom.op
    Module.finrank (completedGroupAlgebra R H)ᵐᵒᵖ (completedGroupAlgebra R Γ) = H.index :=
  letI := Module.compHom (completedGroupAlgebra R Γ)
    (map R H.subtype H.continuous_subtype).toRingHom.op
  let hS := (H.exists_isComplement_left 1).choose_spec.1
  (Module.finrank_eq_nat_card_basis (basisLeftTransversal R hH hS)).trans hS.card_left

end TauCeti.completedGroupAlgebra
