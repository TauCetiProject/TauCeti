/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Blocks of defect zero

Let `G` be a finite group and `x = ∑_{g ∈ G} g a g⁻¹ = Tr_1^G(a)` a trace from the trivial
subgroup in `k[G]`. If `x` acts as the identity on a `k[G]`-module `V`, then every `k`-linear
one-sided inverse of a `k[G]`-linear map out of or onto `V` can be averaged into a `k[G]`-linear
one, by `φ ↦ ∑_g g⁻¹ φ(a g ·)` as in Maschke's theorem, with `a` in place of `1 / |G|`. Over a
field `k`, `V` is then projective, and every submodule of `V` has a complement, so `V` is
semisimple.

For a block idempotent `e` of `k[G]`, `k` of characteristic `p`, the trivial subgroup is a defect
group exactly when `e = Tr_1^G(a)` for some `a` (`TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff`,
from the characterization of defect groups as minimal trace subgroups). So a block of defect
group `1` has every module on which `e` acts as the identity projective and semisimple, and its
block algebra `e k[G]` is semisimple as a left `k[G]`-module. This is the first half of the
defect-zero bullet of ModularCharactersAndBlocks §6.2 (Webb, Corollary 12.4.8, p. 242, with
Proposition 11.3.4, pp. 198–199, for `H = 1`).

## Main results

* `TauCeti.exists_leftInverse_of_forall_sum_conj_smul_eq`,
  `TauCeti.exists_rightInverse_of_forall_sum_conj_smul_eq`: averaging one-sided inverses through
  a trace from `1` acting as the identity.
* `TauCeti.moduleProjective_of_forall_sum_conj_smul_eq`,
  `TauCeti.isSemisimpleModule_of_forall_sum_conj_smul_eq`: over a field, such a module is
  projective and semisimple.
* `TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff`: `1` is a defect group of a block idempotent
  `e` exactly when `e = Tr_1^G(a)` for some `a`.
* `TauCeti.IsBlockIdempotent.moduleProjective_of_isDefectGroup_bot`,
  `TauCeti.IsBlockIdempotent.isSemisimpleModule_of_isDefectGroup_bot`,
  `TauCeti.IsBlockIdempotent.isSemisimpleModule_span_of_isDefectGroup_bot`: for a block of defect
  group `1`, modules on which `e` acts as the identity are projective and semisimple, and so is
  the left ideal `k[G] e`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 11.3.4, pp. 198–199, and
  Corollary 12.4.8, p. 242.
-/

public section

namespace TauCeti

open MonoidAlgebra

section Averaging

variable {k G : Type*} [CommRing k] [Group G] [Fintype G]
  {V W : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V] [AddCommGroup W] [Module k W]
  [Module (MonoidAlgebra k G) W] [IsScalarTower k (MonoidAlgebra k G) W]

/-- The sum of the conjugates by `g` of `a ∘ φ` applied to `w` is `∑_g g⁻¹ a φ(g w)`. -/
private theorem sumOfConjugatesEquivariant_lsmul_comp_apply (a : MonoidAlgebra k G)
    (φ : W →ₗ[k] V) (w : W) :
    (DistribSMul.toLinearMap k V a ∘ₗ φ).sumOfConjugatesEquivariant G w =
      ∑ g : G, of k G g⁻¹ • a • φ (of k G g • w) := by
  rw [LinearMap.sumOfConjugatesEquivariant_apply]
  rfl

/-- `∑_g g⁻¹ a g` is the trace `∑_g g a g⁻¹`, reindexed by `g ↦ g⁻¹`. -/
private theorem sum_of_inv_mul_mul_of (a : MonoidAlgebra k G) :
    ∑ g : G, of k G g⁻¹ * a * of k G g = ∑ g : G, conjRepresentation k G g a := by
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [conjRepresentation_apply_eq_mul, Equiv.inv_apply, inv_inv]

variable {a : MonoidAlgebra k G}
  (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v)
include ha

/-- **Averaging a retraction.** If the trace `∑_g g a g⁻¹` acts as the identity on `V`, then a
`k[G]`-linear map `i : V → W` with a `k`-linear left inverse has a `k[G]`-linear left inverse. -/
theorem exists_leftInverse_of_forall_sum_conj_smul_eq (i : V →ₗ[MonoidAlgebra k G] W)
    (π : W →ₗ[k] V) (hπ : ∀ v, π (i v) = v) :
    ∃ r : W →ₗ[MonoidAlgebra k G] V, ∀ v, r (i v) = v := by
  refine ⟨(DistribSMul.toLinearMap k V a ∘ₗ π).sumOfConjugatesEquivariant G, fun v => ?_⟩
  rw [sumOfConjugatesEquivariant_lsmul_comp_apply]
  conv_rhs => rw [← ha v, ← sum_of_inv_mul_mul_of, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← i.map_smul, hπ, smul_smul, smul_smul]

/-- **Averaging a section.** If the trace `∑_g g a g⁻¹` acts as the identity on `V`, then a
`k[G]`-linear map `p : W → V` with a `k`-linear right inverse has a `k[G]`-linear right
inverse. -/
theorem exists_rightInverse_of_forall_sum_conj_smul_eq (p : W →ₗ[MonoidAlgebra k G] V)
    (s : V →ₗ[k] W) (hs : ∀ v, p (s v) = v) :
    ∃ σ : V →ₗ[MonoidAlgebra k G] W, ∀ v, p (σ v) = v := by
  refine ⟨(DistribSMul.toLinearMap k W a ∘ₗ s).sumOfConjugatesEquivariant G, fun v => ?_⟩
  rw [sumOfConjugatesEquivariant_lsmul_comp_apply, map_sum]
  conv_rhs => rw [← ha v, ← sum_of_inv_mul_mul_of, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [p.map_smul, p.map_smul, hs, smul_smul, smul_smul]

end Averaging

section Field

variable {k G : Type*} [Field k] [Group G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V] {a : MonoidAlgebra k G}

/-- **Higman's criterion, easy direction, relative to a trace.** Over a field `k`, a
`k[G]`-module on which a trace `∑_g g a g⁻¹` from the trivial subgroup acts as the identity is
projective. -/
theorem moduleProjective_of_forall_sum_conj_smul_eq
    (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v) :
    Module.Projective (MonoidAlgebra k G) V := by
  let p := Finsupp.linearCombination (MonoidAlgebra k G) (id : V → V)
  have hp : Function.Surjective p := fun v => ⟨Finsupp.single v 1, by simp [p]⟩
  obtain ⟨s, hs⟩ := (p.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hp)
  obtain ⟨σ, hσ⟩ := exists_rightInverse_of_forall_sum_conj_smul_eq ha p s
    fun v => LinearMap.congr_fun hs v
  exact Module.Projective.of_split σ p (LinearMap.ext hσ)

/-- Over a field `k`, a `k[G]`-module on which a trace `∑_g g a g⁻¹` from the trivial subgroup
acts as the identity is semisimple: every submodule has a complement. -/
theorem isSemisimpleModule_of_forall_sum_conj_smul_eq
    (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v) :
    IsSemisimpleModule (MonoidAlgebra k G) V where
  exists_isCompl N := by
    obtain ⟨π, hπ⟩ := (N.subtype.restrictScalars k).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    obtain ⟨r, hr⟩ := exists_leftInverse_of_forall_sum_conj_smul_eq
      (fun v : N => Subtype.ext (ha v.val)) N.subtype π fun v => LinearMap.congr_fun hπ v
    exact ⟨LinearMap.ker r, LinearMap.isCompl_of_proj hr⟩

end Field

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
  have hs : Function.Bijective fun g : G =>
      ((⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) : (⊤ : Subgroup G) ⧸
        (⊥ : Subgroup G).subgroupOf ⊤) := by
    refine ⟨fun g h hgh => ?_, fun q => ?_⟩
    · have := QuotientGroup.leftRel_apply.1 (Quotient.exact hgh)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
      simpa [inv_mul_eq_one] using this
    · induction q using QuotientGroup.induction_on with
      | H x => exact ⟨x, rfl⟩
  rw [hb.isDefectGroup_iff_minimal]
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ⟨⟨⟨a, ?_⟩, ?_⟩, fun _ _ _ => bot_le⟩⟩
  · obtain ⟨a, ha⟩ := h.prop
    exact ⟨a, by rw [← ha, relTrace_apply_eq_sum_of_bijective _ hs]⟩
  · rw [conjInvariants_bot]
    exact Algebra.mem_top
  · rw [relTrace_apply_eq_sum_of_bijective _ hs]
    exact ha

end DefectGroup

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]
  {b : Subalgebra.center k (MonoidAlgebra k G)}
  {V : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

/-- **Modules in a block of defect zero are projective.** If `1` is a defect group of a block
idempotent `e` of `k[G]`, `k` a field of characteristic `p`, then every `k[G]`-module on which `e`
acts as the identity is projective. -/
theorem moduleProjective_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥)
    (hV : ∀ v : V, (b : MonoidAlgebra k G) • v = v) :
    Module.Projective (MonoidAlgebra k G) V := by
  have := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := hb.isDefectGroup_bot_iff.1 hD
  exact moduleProjective_of_forall_sum_conj_smul_eq (a := a) (by rwa [ha])

/-- **Modules in a block of defect zero are semisimple.** If `1` is a defect group of a block
idempotent `e` of `k[G]`, `k` a field of characteristic `p`, then every `k[G]`-module on which `e`
acts as the identity is semisimple. -/
theorem isSemisimpleModule_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥)
    (hV : ∀ v : V, (b : MonoidAlgebra k G) • v = v) :
    IsSemisimpleModule (MonoidAlgebra k G) V := by
  have := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := hb.isDefectGroup_bot_iff.1 hD
  exact isSemisimpleModule_of_forall_sum_conj_smul_eq (a := a) (by rwa [ha])

/-- **A block of defect zero is semisimple.** If `1` is a defect group of a block idempotent `e`
of `k[G]`, `k` a field of characteristic `p`, then the block `k[G] e = e k[G]` is a semisimple
left `k[G]`-module. -/
theorem isSemisimpleModule_span_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) :
    IsSemisimpleModule (MonoidAlgebra k G)
      (Ideal.span {(b : MonoidAlgebra k G)} : Ideal (MonoidAlgebra k G)) := by
  refine hb.isSemisimpleModule_of_isDefectGroup_bot hD fun ⟨x, hx⟩ => Subtype.ext ?_
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  change (b : MonoidAlgebra k G) * (y * b) = y * b
  rw [← mul_assoc, ← (Subalgebra.mem_center_iff.1 b.property y), mul_assoc,
    hb.isIdempotentElem_val.eq]

end IsBlockIdempotent

end TauCeti
