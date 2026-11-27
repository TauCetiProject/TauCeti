/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Completion
import Mathlib.RingTheory.Filtration

/-!
# The congruence kernel of `SLₙ`

Let `A` be a commutative ring with finite quotients, such as a ring of `S`-integers of a number
field, and `Γ = SL(n, A)`. For a nonzero ideal `I` the principal congruence subgroup
`Γ(I) = ker (Γ → SL(n, A ⧸ I))` is normal of finite index. The congruence completion
`lim_{I ≠ 0} Γ ⧸ Γ(I)` is the completion of `Γ` relative to these subgroups, and the profinite
completion `Γ̂` maps onto it. The **congruence kernel** `C(Γ)` is the kernel of this map: the
elements of `Γ̂` whose coordinates at every `Γ(I)` of nonzero level are trivial,
equivalently the intersection of the closures in `Γ̂` of the `Γ(I)`. The zero ideal is not a
level: `Γ(0)` is trivial, and it has finite index only when `Γ` is finite.

The congruence kernel measures the failure of the congruence subgroup property:
`congruenceKernel_eq_bot_iff` shows that, over a domain, it is trivial exactly when every
finite-index subgroup of `SL(n, A)` contains a principal congruence subgroup of nonzero level.
Bass, Milnor and Serre compute it for `n ≥ 3` over `S`-integers: it is trivial when `S` is
nonempty or the field has a real place, and it is the group of roots of unity of the field
otherwise. The canonical map `Γ → Γ̂` meets it only in `1` as soon as `A` is a domain that is not
a field (`etaFn_mem_congruenceKernel_iff_eq_one`), by Krull's intersection theorem.

## Main definitions

* `TauCeti.SpecialLinearGroup.principalCongruenceSubgroup`: the principal congruence subgroup of a
  nonzero level, as a finite-index normal subgroup.
* `TauCeti.SpecialLinearGroup.congruenceKernel`: the congruence kernel, a subgroup of the
  profinite completion of `SL(n, A)`.

## Main results

* `TauCeti.SpecialLinearGroup.isClosed_congruenceKernel`, `congruenceKernel_normal`: the
  congruence kernel is a closed normal subgroup.
* `TauCeti.SpecialLinearGroup.congruenceKernel_eq_iInf_topologicalClosure`: it is the
  intersection of the closures of the principal congruence subgroups of nonzero level.
* `TauCeti.SpecialLinearGroup.etaFn_mem_congruenceKernel_iff_eq_one`: over a domain that is not a
  field, the image of `SL(n, A)` meets the congruence kernel only in `1`.
* `TauCeti.SpecialLinearGroup.congruenceKernel_eq_bot_iff`: the congruence kernel is trivial
  exactly when every finite-index subgroup contains a principal congruence subgroup of nonzero
  level.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for
  `SLₙ (n ≥ 3)` and `Sp₂ₙ (n ≥ 2)`*, Publ. Math. IHÉS 33 (1967), §14 and Theorem 14.1.
* J.-P. Serre, *Le problème des groupes de congruence pour SL₂*, Ann. of Math. 92 (1970),
  §1.1–§1.2.
-/

public section

namespace TauCeti.SpecialLinearGroup

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (A : Type*) [CommRing A]
  [Ring.HasFiniteQuotients A]

/-- The principal congruence subgroup `Γ(I) = ker (SL(n, A) → SL(n, A ⧸ I))` of a nonzero level
`I`, as a finite-index normal subgroup: its quotient embeds in the finite group
`SL(n, A ⧸ I)`. -/
def principalCongruenceSubgroup {I : Ideal A} (hI : I ≠ ⊥) :
    FiniteIndexNormalSubgroup (SpecialLinearGroup n A) :=
  haveI := Ring.HasFiniteQuotients.finiteQuotient hI
  .ofSubgroup (map (Ideal.Quotient.mk I)).ker

@[simp]
theorem toSubgroup_principalCongruenceSubgroup {I : Ideal A} (hI : I ≠ ⊥) :
    (principalCongruenceSubgroup n A hI).toSubgroup = (map (Ideal.Quotient.mk I)).ker :=
  (rfl)

@[simp]
theorem mem_principalCongruenceSubgroup_iff {I : Ideal A} (hI : I ≠ ⊥)
    {γ : SpecialLinearGroup n A} :
    γ ∈ principalCongruenceSubgroup n A hI ↔ γ ∈ (map (Ideal.Quotient.mk I)).ker :=
  Iff.rfl

/-- The **congruence kernel** of `SL(n, A)`: the kernel of the comparison from the profinite
completion of `SL(n, A)` to its congruence completion `lim_{I ≠ 0} SL(n, A) ⧸ Γ(I)`, that is the
elements of the profinite completion whose coordinates at all principal congruence subgroups of
nonzero level are trivial. -/
def congruenceKernel :
    Subgroup (ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (SpecialLinearGroup n A))) :=
  ProfiniteCompletion.familyKernel _
    (Set.range fun I : {I : Ideal A // I ≠ ⊥} ↦ principalCongruenceSubgroup n A I.property)

instance congruenceKernel_normal : (congruenceKernel n A).Normal :=
  ProfiniteCompletion.familyKernel_normal _

theorem isClosed_congruenceKernel : IsClosed (SetLike.coe (congruenceKernel n A)) :=
  ProfiniteCompletion.isClosed_familyKernel _

/-- The congruence kernel is the intersection of the closures in the profinite completion of
the principal congruence subgroups of nonzero level. -/
theorem congruenceKernel_eq_iInf_topologicalClosure :
    congruenceKernel n A = ⨅ (I : Ideal A) (_ : I ≠ ⊥), ((map (n := n)
      (Ideal.Quotient.mk I)).ker.map
        (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (SpecialLinearGroup n A))).hom
        ).topologicalClosure := by
  simp only [congruenceKernel, ProfiniteCompletion.familyKernel_eq_iInf_topologicalClosure,
    iInf_range, iInf_subtype, toSubgroup_principalCongruenceSubgroup]

variable {n A}

theorem mem_congruenceKernel_iff {x : ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (SpecialLinearGroup n A))} :
    x ∈ congruenceKernel n A ↔ ∀ (I : Ideal A) (hI : I ≠ ⊥),
      ProfiniteCompletion.coordinateHom _ (principalCongruenceSubgroup n A hI) x = 1 := by
  simp only [congruenceKernel, ProfiniteCompletion.mem_familyKernel_iff, Set.forall_mem_range,
    Subtype.forall]

/-- The image of `γ ∈ SL(n, A)` in the profinite completion lies in the congruence kernel
exactly when `γ` lies in every principal congruence subgroup of nonzero level. -/
@[simp]
theorem etaFn_mem_congruenceKernel_iff {γ : SpecialLinearGroup n A} :
    ProfiniteGrp.ProfiniteCompletion.etaFn _ γ ∈ congruenceKernel n A ↔
      ∀ I : Ideal A, I ≠ ⊥ → γ ∈ (map (Ideal.Quotient.mk I)).ker := by
  simp only [congruenceKernel, ProfiniteCompletion.etaFn_mem_familyKernel_iff,
    Set.forall_mem_range, Subtype.forall, mem_principalCongruenceSubgroup_iff]

/-- Over a domain with finite quotients that is not a field, the image of `SL(n, A)` in its
profinite completion meets the congruence kernel only in the identity. -/
theorem etaFn_mem_congruenceKernel_iff_eq_one [IsDomain A] (hA : ¬ IsField A)
    {γ : SpecialLinearGroup n A} :
    ProfiniteGrp.ProfiniteCompletion.etaFn _ γ ∈ congruenceKernel n A ↔ γ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ one_mem _⟩
  rw [etaFn_mem_congruenceKernel_iff] at h
  -- by Krull's intersection theorem the powers of a nonzero proper ideal `J` meet in `0`
  obtain ⟨J, hJ, hJ'⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 hA
  have hJk : ∀ k, J ^ k ≠ ⊥ := fun k ↦ pow_ne_zero k hJ.ne'
  ext i j
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isDomain J hJ'.ne,
    Submodule.mem_iInf]
  exact fun k ↦ mem_ker_map_quotientMk_iff.1 (h _ (hJk k)) i j

/-- **The congruence kernel detects the congruence subgroup property.** Over a domain with
finite quotients, the congruence kernel of `SL(n, A)` is trivial exactly when every finite-index
subgroup of `SL(n, A)` contains the principal congruence subgroup of some nonzero level. -/
theorem congruenceKernel_eq_bot_iff [IsDomain A] :
    congruenceKernel n A = ⊥ ↔ ∀ H : Subgroup (SpecialLinearGroup n A), H.FiniteIndex →
      ∃ I : Ideal A, I ≠ ⊥ ∧ (map (Ideal.Quotient.mk I)).ker ≤ H := by
  rw [congruenceKernel, ProfiniteCompletion.familyKernel_eq_bot_iff_forall_finiteIndex
    ⟨_, Set.mem_range_self (⟨⊤, top_ne_bot⟩ : {I : Ideal A // I ≠ ⊥})⟩ ?_]
  · simp
  · -- the levels are directed: `Γ(I * J) ≤ Γ(I) ⊓ Γ(J)`, and `I * J ≠ 0` in a domain
    rintro _ ⟨⟨I, hI⟩, rfl⟩ _ ⟨⟨J, hJ⟩, rfl⟩
    exact ⟨_, ⟨⟨I * J, mul_ne_zero hI hJ⟩, rfl⟩, ker_map_quotientMk_mono Ideal.mul_le_left,
      ker_map_quotientMk_mono Ideal.mul_le_right⟩

end TauCeti.SpecialLinearGroup
