/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import TauCeti.GroupTheory.DerivedCentralQuotient
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.GroupTheory.QuotientGroup.Simple

/-!
# Iwasawa's criterion for central quotients

Mathlib's `MulAction.IwasawaStructure` attaches to every point `x` of a `G`-set a commutative
subgroup `T x` of `G`, such that `T (g • x) = g (T x) g⁻¹` and the subgroups `T x` generate `G`.
Iwasawa's criterion `MulAction.IwasawaStructure.isSimpleGroup` says that a perfect group with such
a structure is simple when its action is quasiprimitive and **faithful**.

The classical groups do not act faithfully on the points they are naturally attached to: the
special linear, symplectic and unitary groups act on projective points, isotropic or not, and the
kernel of the action consists of the scalar matrices in the group, which are central. The simple
group is the quotient by that kernel. This file states Iwasawa's criterion in that form.

* A normal subgroup of a perfect group with an Iwasawa structure on a quasiprimitive action either
  acts trivially or is the whole group (`MulAction.IwasawaStructure.fixedPoints_eq_univ_or_eq_top`).
* Hence the quotient by any proper normal subgroup containing the kernel of the action is simple
  (`MulAction.IwasawaStructure.isSimpleGroup_quotient`), in particular the quotient by the centre
  when the kernel is central (`MulAction.IwasawaStructure.isSimpleGroup_quotient_center`).
* In that case the kernel is exactly the centre (`MulAction.IwasawaStructure.mem_center_iff`), so
  the centre of a concrete group can be read off from its action.
* The derived subgroup modulo its centre, `TauCeti.DerivedCentralQuotient`, is then simple
  (`MulAction.IwasawaStructure.isSimpleGroup_derivedCentralQuotient`). This is the form in which
  simplicity is needed for the fixed-point groups of Steinberg endomorphisms. When the group `H` of
  interest is not perfect but its derived subgroup is, the quotient criterion applies to an
  Iwasawa structure on `commutator H` itself: `TauCeti.DerivedCentralQuotient H` is by definition
  the quotient of `commutator H` by its centre.

The criterion needs one subgroup for every point. On a transitive action these are the conjugates
of a single commutative subgroup `T` at a base point `a` that is normalized by the stabilizer of
`a`; `MulAction.IwasawaStructure.ofConj` builds the structure from that data, provided the
conjugates of `T` generate the group. This is the usual situation: `T` is a group of root elements
(transvections, or the centre of the unipotent radical of a Borel subgroup) fixing the base point.

## Main definitions

* `MulAction.IwasawaStructure.ofConj`: the Iwasawa structure given by the conjugates of one
  commutative subgroup normalized by a point stabilizer.

## Main results

* `MulAction.IwasawaStructure.fixedPoints_eq_univ_or_eq_top`: the normal-subgroup dichotomy for
  a perfect group.
* `MulAction.IwasawaStructure.isSimpleGroup_quotient`: the quotient by a proper normal subgroup
  containing the kernel of the action is simple.
* `MulAction.IwasawaStructure.isSimpleGroup_quotient_center`: the quotient by the centre is simple
  when the kernel of the action is central.
* `MulAction.IwasawaStructure.mem_center_iff`: the centre is then the kernel of the action.
* `MulAction.IwasawaStructure.isSimpleGroup_derivedCentralQuotient`: the derived subgroup modulo
  its centre is simple.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* The faithful criterion and the normal-subgroup step `MulAction.IwasawaStructure.commutator_le`
  that every result here rests on are in Mathlib's `Mathlib.GroupTheory.GroupAction.Iwasawa`.
-/

public section

open Subgroup
open scoped Pointwise

namespace MulAction.IwasawaStructure

variable {G α : Type*} [Group G] [MulAction G α]

/-! ### Iwasawa structures from a base point -/

section OfConj

variable [IsPretransitive G α] (a : α) (T : Subgroup G) [IsMulCommutative T]
  (hT : stabilizer G a ≤ normalizer (T : Set G)) (hgen : normalClosure (T : Set G) = ⊤)

/-- **The Iwasawa structure of the conjugates of one subgroup.** Let `G` act transitively on `α`,
and let `T` be a commutative subgroup normalized by the stabilizer of a point `a`, whose conjugates
generate `G`. The subgroup at the point `g • a` is the conjugate `g T g⁻¹`, which depends only on
the point because the stabilizer of `a` normalizes `T`. -/
noncomputable def ofConj : IwasawaStructure G α where
  T x := MulAut.conj (exists_smul_eq G a x).choose • T
  is_comm x := by
    rw [pointwise_smul_def]
    exact map_isMulCommutative _ _
  is_conj g x := by
    rw [← mul_smul, ← map_mul]
    refine TauCeti.conj_smul_eq_conj_smul_of_smul_eq hT ?_
    rw [(exists_smul_eq G a (g • x)).choose_spec, mul_smul, (exists_smul_eq G a x).choose_spec]
  is_generator := by
    rw [eq_top_iff, ← hgen, normalClosure, closure_le]
    intro y hy
    obtain ⟨t, ht, hty⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hty
    refine le_iSup (fun x ↦ MulAut.conj (exists_smul_eq G a x).choose • T) (c • a) ?_
    rw [TauCeti.conj_smul_eq_conj_smul_of_smul_eq hT (exists_smul_eq G a (c • a)).choose_spec]
    exact smul_mem_pointwise_smul t (MulAut.conj c) T ht

/-- The subgroup of `MulAction.IwasawaStructure.ofConj` at the point `g • a` is `g T g⁻¹`. -/
@[simp]
theorem ofConj_T_smul (g : G) : (ofConj a T hT hgen).T (g • a) = MulAut.conj g • T :=
  TauCeti.conj_smul_eq_conj_smul_of_smul_eq hT (exists_smul_eq G a (g • a)).choose_spec

/-- The subgroup of `MulAction.IwasawaStructure.ofConj` at the base point is `T`. -/
@[simp]
theorem ofConj_T_self : (ofConj a T hT hgen).T a = T := by
  simpa using ofConj_T_smul a T hT hgen 1

end OfConj

/-! ### Simplicity of quotients -/

section Quotient

variable [IsQuasiPreprimitive G α] (IwaS : IwasawaStructure G α)
include IwaS

/-- **Iwasawa's normal-subgroup theorem for a perfect group.** If a perfect group has an Iwasawa
structure on a quasiprimitive action, each of its normal subgroups either fixes every point or is
the whole group. -/
theorem fixedPoints_eq_univ_or_eq_top [Group.IsPerfect G] (N : Subgroup G) [N.Normal] :
    fixedPoints N α = Set.univ ∨ N = ⊤ :=
  or_iff_not_imp_left.mpr fun h ↦
    top_le_iff.mp (Group.IsPerfect.commutator_eq_top (G := G) ▸ IwaS.commutator_le N h)

/-- **Iwasawa's criterion for a quotient.** Let a perfect group `G` have an Iwasawa structure on a
quasiprimitive action. If a proper normal subgroup `N` contains every element acting trivially,
then `G ⧸ N` is simple. -/
theorem isSimpleGroup_quotient [Group.IsPerfect G] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊤)
    (hker : ∀ g : G, (∀ x : α, g • x = x) → g ∈ N) : IsSimpleGroup (G ⧸ N) :=
  QuotientGroup.isSimpleGroup_of_forall_normal hN fun K _ ↦
    -- A normal subgroup acting trivially lies in `N`.
    (IwaS.fixedPoints_eq_univ_or_eq_top K).imp_left fun (h : fixedPoints K α = _) g hg ↦
      hker g fun x ↦ (Set.eq_univ_iff_forall.mp h x) ⟨g, hg⟩

/-- **Iwasawa's criterion for the central quotient.** Let a nontrivial perfect group `G` have an
Iwasawa structure on a quasiprimitive action. If every element acting trivially is central, then
`G` modulo its centre is simple. -/
theorem isSimpleGroup_quotient_center [Group.IsPerfect G] [Nontrivial G]
    (hker : ∀ g : G, (∀ x : α, g • x = x) → g ∈ center G) : IsSimpleGroup (G ⧸ center G) :=
  IwaS.isSimpleGroup_quotient (QuotientGroup.nontrivial_iff.mp inferInstance) hker

/-- **The centre is the kernel of the action.** Let a perfect group `G` have an Iwasawa structure on
a quasiprimitive action. If every element acting trivially is central, then the central elements
are exactly the elements acting trivially. -/
theorem mem_center_iff [Group.IsPerfect G]
    (hker : ∀ g : G, (∀ x : α, g • x = x) → g ∈ center G) {g : G} :
    g ∈ center G ↔ ∀ x : α, g • x = x := by
  refine ⟨fun hg x ↦ ?_, hker g⟩
  rcases IwaS.fixedPoints_eq_univ_or_eq_top (center G) with h | h
  · exact (Set.eq_univ_iff_forall.mp h x) ⟨g, hg⟩
  · -- A perfect group equal to its centre is commutative, hence trivial.
    have : IsMulCommutative G := center_eq_top_iff.mp h
    rw [Subsingleton.elim g 1, one_smul]

/-- **Iwasawa's criterion for the derived central quotient.** Let a nontrivial perfect group `G`
have an Iwasawa structure on a quasiprimitive action whose kernel is central. Then the derived
subgroup of `G` modulo its centre, `TauCeti.DerivedCentralQuotient G`, is simple. -/
theorem isSimpleGroup_derivedCentralQuotient [Group.IsPerfect G] [Nontrivial G]
    (hker : ∀ g : G, (∀ x : α, g • x = x) → g ∈ center G) :
    IsSimpleGroup (TauCeti.DerivedCentralQuotient G) :=
  TauCeti.DerivedCentralQuotient.mulEquivQuotientCenter.isSimpleGroup_congr.mpr
    (IwaS.isSimpleGroup_quotient_center hker)

end Quotient

end MulAction.IwasawaStructure
