/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.TraceSplit

/-!
# Blocks of defect zero

For a block idempotent `e` of `k[G]`, `k` of characteristic `p`, the trivial subgroup is a defect
group exactly when `e = Tr_1^G(a) = ∑_g g a g⁻¹` for some `a`
(`TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff`, from the characterization of defect groups as
minimal trace subgroups). Since `e` then acts as the identity on every module of the block, the
averaging results of `TauCeti.RepresentationTheory.GroupAlgebra.TraceSplit` apply: for a block
of defect group `1`, every module on which `e` acts as the identity is projective over `k[G]` if it
is projective over `k`; over a field it is also semisimple, and the block algebra `e k[G]` is
semisimple as a left `k[G]`-module (Webb,
Corollary 12.4.8, p. 242, with Proposition 11.3.4, pp. 198–199, for `H = 1`).

## Main results

* `TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff`: `1` is a defect group of a block idempotent
  `e` exactly when `e = Tr_1^G(a)` for some `a`.
* `TauCeti.IsBlockIdempotent.moduleProjective_of_isDefectGroup_bot`,
  `TauCeti.IsBlockIdempotent.isSemisimpleModule_of_isDefectGroup_bot`,
  `TauCeti.IsBlockIdempotent.isSemisimpleModule_span_of_isDefectGroup_bot`: for a block of defect
  group `1`, modules on which `e` acts as the identity are projective (given projectivity over
  `k`) and, over a field, semisimple; so is the left ideal `k[G] e`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 11.3.4, pp. 198–199, and
  Corollary 12.4.8, p. 242.
-/

public section

namespace TauCeti

open MonoidAlgebra

namespace IsBlockIdempotent

section DefectGroup

variable {R G : Type*} [CommRing R] [IsArtinianRing R] [Group G] [Fintype G] {p : ℕ}
  [Fact p.Prime] [CharP R p] {b : Subalgebra.center R (MonoidAlgebra R G)}

/-- **Blocks with defect group `1`.** For a block idempotent `e` of `R[G]`, with `R` an Artinian
ring of characteristic `p`, the trivial subgroup is a defect group of `e` exactly when
`e = Tr_1^G(a) = ∑_g g a g⁻¹` for some `a ∈ R[G]`. -/
theorem isDefectGroup_bot_iff (hb : IsBlockIdempotent b) :
    IsDefectGroup R p (b : MonoidAlgebra R G) ⊥ ↔
      ∃ a : MonoidAlgebra R G, ∑ g : G, conjRepresentation R G g a = b := by
  rw [hb.isDefectGroup_iff_minimal]
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ⟨⟨⟨a, ?_⟩, ?_⟩, fun _ _ _ => bot_le⟩⟩
  · obtain ⟨a, ha⟩ := h.prop
    exact ⟨a, by rw [← ha, coe_relTrace_bot_top]⟩
  · rw [conjInvariants_bot]
    exact Algebra.mem_top
  · rw [coe_relTrace_bot_top]
    exact ha

end DefectGroup

section Projective

variable {R G : Type*} [CommRing R] [IsArtinianRing R] [Group G] [Finite G] {p : ℕ}
  [Fact p.Prime] [CharP R p] {b : Subalgebra.center R (MonoidAlgebra R G)}
  {V : Type*} [AddCommGroup V] [Module R V] [Module (MonoidAlgebra R G) V]
  [IsScalarTower R (MonoidAlgebra R G) V] [Module.Projective R V]

/-- **Modules in a block of defect zero are projective.** If `1` is a defect group of a block
idempotent `e` of `R[G]`, `R` an Artinian ring of characteristic `p`, then every `R[G]`-module
that is projective over `R` and on which `e` acts as the identity is projective over `R[G]`. -/
theorem moduleProjective_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup R p (b : MonoidAlgebra R G) ⊥)
    (hV : ∀ v : V, (b : MonoidAlgebra R G) • v = v) :
    Module.Projective (MonoidAlgebra R G) V := by
  have := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := hb.isDefectGroup_bot_iff.1 hD
  exact moduleProjective_of_sumOfConjugates_eq_id (φ := DistribSMul.toLinearMap R V a)
    (LinearMap.ext fun v => by
      rw [sumOfConjugates_distribSMul_toLinearMap_apply, ha, hV, LinearMap.id_apply])

end Projective

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]
  {b : Subalgebra.center k (MonoidAlgebra k G)}
  {V : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

/-- **Modules in a block of defect zero are semisimple.** If `1` is a defect group of a block
idempotent `e` of `k[G]`, `k` a field of characteristic `p`, then every `k[G]`-module on which `e`
acts as the identity is semisimple. -/
theorem isSemisimpleModule_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥)
    (hV : ∀ v : V, (b : MonoidAlgebra k G) • v = v) :
    IsSemisimpleModule (MonoidAlgebra k G) V := by
  have := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := hb.isDefectGroup_bot_iff.1 hD
  exact isSemisimpleModule_of_forall_sum_conjRepresentation_smul_eq_self (a := a) (by rwa [ha])

/-- **A block of defect zero is semisimple.** If `1` is a defect group of a block idempotent `e`
of `k[G]`, `k` a field of characteristic `p`, then the block `k[G] e = e k[G]` is a semisimple
left `k[G]`-module. -/
theorem isSemisimpleModule_span_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) :
    IsSemisimpleModule (MonoidAlgebra k G)
      (Ideal.span {(b : MonoidAlgebra k G)} : Ideal (MonoidAlgebra k G)) := by
  refine hb.isSemisimpleModule_of_isDefectGroup_bot hD fun ⟨x, hx⟩ => Subtype.ext ?_
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [Submodule.coe_smul, smul_eq_mul, ← mul_assoc,
    ← (Subalgebra.mem_center_iff.1 b.property y), mul_assoc, hb.isIdempotentElem_val.eq]

end IsBlockIdempotent

end TauCeti
