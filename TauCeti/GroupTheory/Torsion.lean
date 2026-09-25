/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The torsion subgroup under a product decomposition

Let `A` be an abelian group isomorphic to `Multiplicative (M × T)`, where `M` is a torsion-free
additive group and `T` is a torsion additive group. Then the torsion subgroup of `A` is exactly the
preimage of the factor `T`, and the quotient `A ⧸ torsion A` is identified with `M`.

These are the statements behind the uniqueness clauses of the structure theorems for finitely
generated abelian groups and for topologically finitely generated abelian pro-`p` groups: in a
decomposition `A ≅ M × T` of this shape the factor `T` is the torsion subgroup and `M` is the
torsion-free quotient, so both are determined by `A` up to isomorphism. The topological version
of the quotient identification is `TauCeti.quotientTorsionContinuousMulEquiv` in
`TauCeti.Topology.Algebra.Group.Torsion`.

## Main definitions

* `TauCeti.subsingleton_of_mulEquiv`: if `A` is torsion-free, the factor `T` is trivial (this
  needs no hypothesis on `M`).
* `TauCeti.mem_torsion_iff_of_mulEquiv`: an element is torsion exactly when its `M`-coordinate
  vanishes.
* `TauCeti.torsionMulEquiv`: the torsion subgroup of `A` is isomorphic to `T`.
* `TauCeti.torsionFactorAddEquiv`: two decompositions of `A` have isomorphic torsion factors.
* `TauCeti.quotientTorsionMulEquiv`: the quotient of `A` by its torsion subgroup is isomorphic to
  `M`.
-/

public section

namespace TauCeti

open CommGroup (torsion)
open Multiplicative

variable {A M T : Type*} [CommGroup A] [AddCommGroup M] [AddCommGroup T]

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `T` torsion, if `A` is torsion-free
then the factor `T` is trivial: every element of `T` embeds as a torsion element of `A`. -/
theorem subsingleton_of_mulEquiv [IsMulTorsionFree A] (hT : IsAddTorsion T)
    (e : A ≃* Multiplicative (M × T)) : Subsingleton T :=
  subsingleton_of_forall_eq 0 fun t ↦ by
    have h := e.symm.toMonoidHom.isOfFinOrder
      (isOfFinOrder_ofAdd_iff.2 ((IsOfFinAddOrder.zero (G := M)).prod_mk (hT t)))
    simpa using (isOfFinOrder_iff_eq_one _).1 h

variable [IsAddTorsionFree M]

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `M` torsion-free and `T` torsion, an
element of `A` is torsion exactly when its `M`-coordinate vanishes. -/
theorem mem_torsion_iff_of_mulEquiv (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    {x : A} : x ∈ torsion A ↔ (e x).toAdd.1 = 0 := by
  rw [CommGroup.mem_torsion, ← e.injective.isOfFinOrder_iff (f := e.toMonoidHom),
    MulEquiv.coe_toMonoidHom, ← ofAdd_toAdd (e x), isOfFinOrder_ofAdd_iff]
  simp [IsOfFinAddOrder.prod_iff, isOfFinAddOrder_iff_eq_zero, hT (e x).toAdd.2]

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `M` torsion-free and `T` torsion, the
torsion subgroup of `A` is the factor `T`. -/
def torsionMulEquiv (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T)) :
    torsion A ≃* Multiplicative T where
  toFun x := ofAdd (e x).toAdd.2
  invFun t := ⟨e.symm (ofAdd (0, t.toAdd)), (mem_torsion_iff_of_mulEquiv hT e).2 (by simp)⟩
  left_inv x :=
    Subtype.ext (e.symm_apply_eq.2 (Multiplicative.ext
      (Prod.ext ((mem_torsion_iff_of_mulEquiv hT e).1 x.2).symm rfl)))
  right_inv t := by simp
  map_mul' x y := by simp

@[simp]
theorem torsionMulEquiv_apply (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    (x : torsion A) : torsionMulEquiv hT e x = ofAdd (e x).toAdd.2 :=
  (rfl)

@[simp]
theorem coe_torsionMulEquiv_symm_apply (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    (t : Multiplicative T) : ((torsionMulEquiv hT e).symm t : A) = e.symm (ofAdd (0, t.toAdd)) :=
  (rfl)

/-- Two decompositions of `A` as torsion-free times torsion have isomorphic torsion factors: both
are the torsion subgroup of `A`. -/
def torsionFactorAddEquiv {M' T' : Type*} [AddCommGroup M'] [IsAddTorsionFree M']
    [AddCommGroup T'] (hT : IsAddTorsion T) (hT' : IsAddTorsion T')
    (e : A ≃* Multiplicative (M × T)) (e' : A ≃* Multiplicative (M' × T')) : T ≃+ T' :=
  AddEquiv.toMultiplicative.symm ((torsionMulEquiv hT e).symm.trans (torsionMulEquiv hT' e'))

@[simp]
theorem torsionFactorAddEquiv_apply {M' T' : Type*} [AddCommGroup M'] [IsAddTorsionFree M']
    [AddCommGroup T'] (hT : IsAddTorsion T) (hT' : IsAddTorsion T')
    (e : A ≃* Multiplicative (M × T)) (e' : A ≃* Multiplicative (M' × T')) (t : T) :
    torsionFactorAddEquiv hT hT' e e' t = (e' (e.symm (ofAdd (0, t)))).toAdd.2 :=
  (rfl)

@[simp]
theorem torsionFactorAddEquiv_symm_apply {M' T' : Type*} [AddCommGroup M'] [IsAddTorsionFree M']
    [AddCommGroup T'] (hT : IsAddTorsion T) (hT' : IsAddTorsion T')
    (e : A ≃* Multiplicative (M × T)) (e' : A ≃* Multiplicative (M' × T')) (t' : T') :
    (torsionFactorAddEquiv hT hT' e e').symm t' = (e (e'.symm (ofAdd (0, t')))).toAdd.2 :=
  (rfl)

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `M` torsion-free and `T` torsion, the
quotient of `A` by its torsion subgroup is the factor `M`. -/
noncomputable def quotientTorsionMulEquiv (hT : IsAddTorsion T)
    (e : A ≃* Multiplicative (M × T)) : A ⧸ torsion A ≃* Multiplicative M :=
  QuotientGroup.liftEquiv (torsion A)
    (φ := (AddMonoidHom.fst M T).toMultiplicative.comp e.toMonoidHom)
    (fun v ↦ ⟨e.symm (ofAdd (v.toAdd, 0)), by simp [AddMonoidHom.coe_toMultiplicative]⟩)
    (by
      ext x
      rw [MonoidHom.mem_ker, mem_torsion_iff_of_mulEquiv hT e]
      simp)

@[simp]
theorem quotientTorsionMulEquiv_mk (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    (x : A) : quotientTorsionMulEquiv hT e (x : A ⧸ torsion A) = ofAdd (e x).toAdd.1 :=
  (rfl)

@[simp]
theorem quotientTorsionMulEquiv_symm_apply (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    (v : Multiplicative M) :
    (quotientTorsionMulEquiv hT e).symm v = ((e.symm (ofAdd (v.toAdd, 0)) : A) : A ⧸ torsion A) :=
  (quotientTorsionMulEquiv hT e).injective (by simp)

end TauCeti
