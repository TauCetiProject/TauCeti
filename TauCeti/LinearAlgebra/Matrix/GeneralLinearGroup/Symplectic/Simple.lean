/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Perfect
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Primitive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Projective
public import Mathlib.GroupTheory.IsPerfect

/-!
# Simplicity of the projective symplectic groups

Let `K` be a field and `m ≥ 1`. The projective symplectic group
`PSp_{2m}(K) = Sp_{2m}(K) ⧸ Z(Sp_{2m}(K))` acts on the projective space `ℙ K (Fin (m + m) → K)`.
This file assembles the inputs of Iwasawa's criterion `MulAction.IwasawaStructure.isSimpleGroup`
for that action:

* it is faithful, because the kernel of the action of `Sp_{2m}(K)` is its centre
  (`TauCeti.GLSymplecticFin.ker_projective_toPermHom`);
* it is primitive, because the action of `Sp_{2m}(K)` is
  (`TauCeti.GLSymplecticFin.instIsPreprimitiveProjectivization`), and primitivity passes to the
  quotient, which acts through the same permutations;
* the images of the groups of symplectic transvections along the points form an Iwasawa structure,
  because the transvection groups form one for `Sp_{2m}(K)`
  (`TauCeti.GLSymplecticFin.iwasawaStructure`).

Iwasawa's criterion then shows that `PSp_{2m}(K)` is simple as soon as `Sp_{2m}(K)` is perfect.
By `TauCeti.GLSymplecticFin.commutator_eq_top_of_two_le` this gives the classical statement: for
`m ≥ 2`, `PSp_{2m}(K)` is simple unless `m = 2` and `K = 𝔽₂`. In particular every finite group
`PSp_{2m}(𝔽_q)` with `m ≥ 3` is simple, including those over `𝔽₂` and `𝔽₃`.

## Main definitions and results

* `TauCeti.GLSymplecticFin.instIsPreprimitiveQuotientCenterProjectivization`: the projective
  symplectic group acts primitively on projective space.
* `TauCeti.GLSymplecticFin.quotientCenterIwasawaStructure`: the Iwasawa structure of that action.
* `TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center_of_commutator_eq_top`: the projective
  symplectic group is simple when the symplectic group is perfect.
* `TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center_of_two_le`: the classical simplicity of
  `PSp_{2m}(K)` for `m ≥ 2`, outside `PSp₄(𝔽₂)`.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* E. Artin, *Geometric Algebra* (1957), Chapter IV, §1, Theorem 4.13.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8, Theorem 8.6.

The assembly follows `Matrix.ProjectiveSpecialLinearGroup.iwasawaStructure` and
`Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_commutator_eq_top`, the same argument for the
projective special linear groups.
-/

public section

open MulAction
open scoped LinearAlgebra.Projectivization Pointwise

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ} {K : Type u} [Field K]

/-- **The projective symplectic group acts primitively on projective space**: it acts through the
same permutations as the symplectic group, whose action is primitive. -/
instance instIsPreprimitiveQuotientCenterProjectivization :
    IsPreprimitive (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K))
      (ℙ K (Fin (m + m) → K)) :=
  IsPreprimitive.of_surjective
    (f := ({ toFun := id
             map_smul' := fun g p ↦ (quotient_center_mk_smul g p).symm } :
      ℙ K (Fin (m + m) → K) →ₑ[(QuotientGroup.mk :
        GLSymplecticFin m K → GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K))]
        ℙ K (Fin (m + m) → K)))
    Function.surjective_id

/-- **The Iwasawa structure of the projective symplectic group on projective space**: the subgroup
attached to a point `p` is the image of the group of symplectic transvections along `p`. These
subgroups are abelian, permuted by conjugation compatibly with the action, and generate the
projective symplectic group. -/
noncomputable def quotientCenterIwasawaStructure :
    IwasawaStructure (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K))
      (ℙ K (Fin (m + m) → K)) where
  T p := (transvectionSubgroup p).map (QuotientGroup.mk' _)
  is_comm _ := Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [quotient_center_mk_smul, transvectionSubgroup_smul]
    exact Subgroup.map_map_conj _ (QuotientGroup.mk' _) g
  is_generator := by
    rw [← Subgroup.map_iSup, iSup_transvectionSubgroup]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- The subgroup that `quotientCenterIwasawaStructure` attaches to a point `p` is the image of the
group of symplectic transvections along `p`. -/
@[simp]
theorem quotientCenterIwasawaStructure_T (p : ℙ K (Fin (m + m) → K)) :
    (quotientCenterIwasawaStructure (m := m)).T p =
      (transvectionSubgroup p).map (QuotientGroup.mk' _) :=
  (rfl)

/-- **Iwasawa's theorem for the projective symplectic group.** In positive rank, `PSp_{2m}(K)` is
simple as soon as `Sp_{2m}(K)` is perfect. -/
theorem isSimpleGroup_quotient_center_of_commutator_eq_top [NeZero m]
    (h : commutator (GLSymplecticFin m K) = ⊤) :
    IsSimpleGroup (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) :=
  have : Group.IsPerfect (GLSymplecticFin m K) := ⟨h⟩
  quotientCenterIwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top inferInstance

/-- **The projective symplectic group `PSp_{2m}(K)` is simple for `m ≥ 2`**, except for
`PSp₄(𝔽₂)`: it suffices that the rank is at least three, or that `K` has an element other than
`0` and `1`. -/
theorem isSimpleGroup_quotient_center_of_two_le (hm : 2 ≤ m)
    (hK : 3 ≤ m ∨ ∃ a : K, a ≠ 0 ∧ a ≠ 1) :
    IsSimpleGroup (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) :=
  have : NeZero m := ⟨by omega⟩
  isSimpleGroup_quotient_center_of_commutator_eq_top (commutator_eq_top_of_two_le hm hK)

end TauCeti.GLSymplecticFin
