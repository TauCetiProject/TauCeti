/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.BaseChange.Points
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Base change of the defining ideals of dynamic subgroups

The defining Hopf ideals of the dynamic parabolic, Levi, and unipotent subgroup commute
with arbitrary extension of the base ring. Thus formation of these closed subgroup
schemes commutes with base change, including passage to geometric fibres.

The proof compares points over every commutative value algebra using
`Dynamic.BaseChange.Points`, then recovers the defining ideals by their universal quotient
points. No reducedness or flatness assumption is needed; in particular the result retains
infinitesimal subgroup structure. The existing `CommHopfAlgCat.quotientBaseChangeIso`
turns these ideal identities into the corresponding coordinate-algebra isomorphisms.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open WithConv

namespace TauCeti.Cocharacter

variable {R S H : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing H] [HopfAlgebra R H]

/-- Formation of the dynamic parabolic defining Hopf ideal commutes with arbitrary base change. -/
@[simp]
theorem baseChangeHopfIdeal_parabolicDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.baseChangeHopfIdeal (H := _root_.CommHopfAlgCat.of R H)
        (K := S) (parabolicDefiningHopfIdeal l) =
      parabolicDefiningHopfIdeal (l.baseChangeCocharacter S) := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  rintro ⟨A, _, _⟩
  let : Algebra R A := Algebra.compHom A (algebraMap R S)
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  ext g
  let g₀ := (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (R := A)).symm g
  have hp := CommHopfAlgCat.mem_quotientPointsSubgroup_iff_baseChangePointsMulEquiv_mem
    (H := _root_.CommHopfAlgCat.of R H) (K := S) (parabolicDefiningHopfIdeal l) g₀
  rw [quotientPointsSubgroup_parabolicDefiningHopfIdeal] at hp ⊢
  simpa only [g₀, MulEquiv.apply_symm_apply] using
    hp.symm.trans (baseChangePointsMulEquiv_mem_parabolic_iff (S := S) l g₀).symm

/-- Formation of the dynamic Levi defining Hopf ideal commutes with arbitrary base change. -/
@[simp]
theorem baseChangeHopfIdeal_leviDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.baseChangeHopfIdeal (H := _root_.CommHopfAlgCat.of R H)
        (K := S) (leviDefiningHopfIdeal l) =
      leviDefiningHopfIdeal (l.baseChangeCocharacter S) := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  rintro ⟨A, _, _⟩
  let : Algebra R A := Algebra.compHom A (algebraMap R S)
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  ext g
  let g₀ := (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (R := A)).symm g
  have hp := CommHopfAlgCat.mem_quotientPointsSubgroup_iff_baseChangePointsMulEquiv_mem
    (H := _root_.CommHopfAlgCat.of R H) (K := S) (leviDefiningHopfIdeal l) g₀
  rw [quotientPointsSubgroup_leviDefiningHopfIdeal] at hp ⊢
  simpa only [g₀, MulEquiv.apply_symm_apply] using
    hp.symm.trans (baseChangePointsMulEquiv_mem_levi_iff (S := S) l g₀).symm

/-- Formation of the dynamic unipotent defining Hopf ideal commutes with arbitrary base change. -/
@[simp]
theorem baseChangeHopfIdeal_unipotentDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.baseChangeHopfIdeal (H := _root_.CommHopfAlgCat.of R H)
        (K := S) l.unipotentDefiningHopfIdeal =
      (l.baseChangeCocharacter S).unipotentDefiningHopfIdeal := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  rintro ⟨A, _, _⟩
  let : Algebra R A := Algebra.compHom A (algebraMap R S)
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  ext g
  let g₀ := (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (R := A)).symm g
  have hp := CommHopfAlgCat.mem_quotientPointsSubgroup_iff_baseChangePointsMulEquiv_mem
    (H := _root_.CommHopfAlgCat.of R H) (K := S) l.unipotentDefiningHopfIdeal g₀
  rw [BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal] at hp ⊢
  simpa only [g₀, MulEquiv.apply_symm_apply] using
    hp.symm.trans (baseChangePointsMulEquiv_mem_unipotent_iff (S := S) l g₀).symm

end TauCeti.Cocharacter
