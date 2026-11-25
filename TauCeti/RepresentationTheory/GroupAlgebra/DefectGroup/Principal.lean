/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Kernel
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup

/-!
# Defect groups of the principal block

Let `R` be a commutative ring of characteristic `p` and `P` a `p`-subgroup of a finite group `G`.
The Brauer projection `Br_P` preserves the augmentation of `P`-invariant elements:
`ε(Br_P(x)) = ε(x)` for `x ∈ R[G]^P` (`TauCeti.augmentation_brauerProjection`). Indeed a trace
`Tr_Q^P(a)` from `Q < P` has augmentation `|P : Q| ε(a) = 0`, and `x` minus the part of `x`
supported on `C_G(P)` has vanishing Brauer projection, so it is a sum of such traces
(`TauCeti.mem_iSup_relTraceIdeal_of_brauerProjection_eq_zero`).

Hence a central element `e` of nonzero augmentation has `Br_S(e) ≠ 0` at every Sylow
`p`-subgroup `S`, and its defect groups are exactly the Sylow `p`-subgroups
(`TauCeti.isDefectGroup_iff_sylow_of_augmentation_ne_zero`): a defect group `D` lies in a Sylow
subgroup `S` with `Br_S(e) ≠ 0`, so `D = S` by maximality. In particular the defect groups of the
principal block of `k[G]`, `k` a field of characteristic `p`, are the Sylow `p`-subgroups
(`TauCeti.isDefectGroup_principalBlockIdempotent_iff`; Webb, Corollary 12.4.7, p. 242). The
argument needs neither vertices nor the conjugacy of defect groups.

## Main results

* `TauCeti.augmentation_relTrace`: `ε(Tr_Q^P(a)) = |P : Q| ε(a)`.
* `TauCeti.augmentation_brauerProjection`: `ε(Br_P(x)) = ε(x)` for a `p`-subgroup `P` and
  `x ∈ R[G]^P`.
* `TauCeti.isDefectGroup_iff_sylow_of_augmentation_ne_zero`: the defect groups of a central
  element of nonzero augmentation are the Sylow `p`-subgroups.
* `TauCeti.isDefectGroup_principalBlockIdempotent_iff`: the defect groups of the principal block
  are the Sylow `p`-subgroups.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Corollary 12.4.7, p. 242.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommRing R] [Group G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Conjugation preserves the augmentation. -/
theorem augmentation_conjRepresentation (g : G) (x : MonoidAlgebra R G) :
    augmentation R G (conjRepresentation R G g x) = augmentation R G x := by
  rw [conjRepresentation_apply_eq_mul, map_mul, map_mul, of_apply, of_apply, augmentation_single,
    augmentation_single, one_mul, mul_one]

/-- The relative trace multiplies the augmentation by the index: `ε(Tr_Q^P(a)) = |P : Q| ε(a)`. -/
theorem augmentation_relTrace {Q P : Subgroup G} [(Q.subgroupOf P).FiniteIndex]
    (a : conjInvariants R Q) :
    augmentation R G (relTrace R Q P a : MonoidAlgebra R G) =
      (Q.subgroupOf P).index • augmentation R G (a : MonoidAlgebra R G) := by
  rw [coe_relTrace, map_sum]
  simp only [augmentation_conjRepresentation, Finset.sum_const, Finset.card_univ,
    Subgroup.index, Nat.card_eq_fintype_card]

variable {p : ℕ} [Fact p.Prime] [CharP R p]

/-- **The Brauer projection preserves augmentations.** For a `p`-subgroup `P` of a finite group in
characteristic `p` and `x ∈ R[G]^P`, the coefficients of `x` on `C_G(P)` have the same sum as all
the coefficients of `x`. -/
theorem augmentation_brauerProjection [Finite G] {P : Subgroup G} (hP : IsPGroup p P)
    {x : MonoidAlgebra R G} (hx : x ∈ conjInvariants R P) :
    augmentation R (Subgroup.centralizer (P : Set G)) (brauerProjection P x) =
      augmentation R G x := by
  classical
  -- `y`, the part of `x` supported on `C_G(P)`, is `P`-invariant with `Br_P(y) = Br_P(x)`.
  set C := Subgroup.centralizer (P : Set G)
  set y : MonoidAlgebra R G := mapDomainRingHom R C.subtype (brauerProjection P x)
  have hy : augmentation R G y = augmentation R C (brauerProjection P x) :=
    RingHom.congr_fun (augmentation_comp_mapDomainRingHom R C.subtype) _
  have hyc (g : G) : y.coeff g = if g ∈ C then x.coeff g else 0 := by
    split_ifs with hg
    · change (Finsupp.mapDomain C.subtype (brauerProjection P x).coeff) (C.subtype ⟨g, hg⟩) = _
      rw [Finsupp.mapDomain_apply_of_injective C.subtype_injective, coeff_brauerProjection]
    · exact Finsupp.mapDomain_of_notMem_range _ _ (by simpa using hg)
  have hconj {h : G} (hh : h ∈ P) {g : G} (hg : g ∈ C) : h * g * h⁻¹ = g := by
    rw [Subgroup.mem_centralizer_iff.1 hg h hh, mul_inv_cancel_right]
  have hymem : y ∈ conjInvariants R P := by
    rw [mem_conjInvariants_iff_coeff]
    intro h hh g
    by_cases hg : g ∈ C
    · rw [hconj hh hg]
    · have hg' : h * g * h⁻¹ ∉ C := fun hg' => hg <| by
        have := hconj (P.inv_mem hh) hg'
        rw [inv_inv, show h⁻¹ * (h * g * h⁻¹) * h = g by group] at this
        exact this ▸ hg'
      simp only [hyc, hg, hg', ite_false]
  have hBy : brauerProjection P y = brauerProjection P x := by
    ext c
    simp only [coeff_brauerProjection, hyc]
    exact ite_eq_left c.property
  -- `x - y` lies in the kernel of `Br_P`, a sum of traces from proper subgroups.
  have hker := mem_iSup_relTraceIdeal_of_brauerProjection_eq_zero (⟨x - y, sub_mem hx hymem⟩ :
    conjInvariants R P) (by rw [map_sub, hBy, sub_self])
  rw [iSup_subtype'] at hker
  have h0 : augmentation R G (x - y) = 0 := by
    refine Submodule.iSup_induction _ (motive := fun z : conjInvariants R P =>
      augmentation R G (z : MonoidAlgebra R G) = 0) hker (fun Q z hz => ?_) (by simp)
      (fun z w hz hw => by rw [Subalgebra.coe_add, map_add, hz, hw, add_zero])
    obtain ⟨b, rfl⟩ := (mem_relTraceIdeal_iff _).1 hz
    obtain ⟨n, hn⟩ := hP.index ((Q : Subgroup G).subgroupOf P)
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hn
      exact Q.property.not_ge hn
    rw [augmentation_relTrace, hn, ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, CharP.cast_eq_zero,
      zero_pow hn0, zero_smul]
  rw [← hy]
  exact (sub_eq_zero.1 (by rwa [map_sub] at h0)).symm

/-- A `P`-invariant element of nonzero augmentation has nonzero Brauer projection at the
`p`-subgroup `P`. -/
theorem brauerProjection_ne_zero_of_augmentation_ne_zero [Finite G] {P : Subgroup G}
    (hP : IsPGroup p P) {x : MonoidAlgebra R G} (hx : x ∈ conjInvariants R P)
    (hε : augmentation R G x ≠ 0) : brauerProjection P x ≠ 0 := fun h => hε <| by
  rw [← augmentation_brauerProjection hP hx, h, map_zero]

/-- **Defect groups of an element of nonzero augmentation.** In characteristic `p`, the defect
groups of a central element `e` of `R[G]` with nonzero augmentation are exactly the Sylow
`p`-subgroups of `G` (Webb, Corollary 12.4.7, p. 242, for the principal block). -/
theorem isDefectGroup_iff_sylow_of_augmentation_ne_zero [Finite G] {e : MonoidAlgebra R G}
    (he : e ∈ Subalgebra.center R (MonoidAlgebra R G)) (hε : augmentation R G e ≠ 0)
    {D : Subgroup G} : IsDefectGroup R p e D ↔ ∃ S : Sylow p G, D = S := by
  have hne (S : Sylow p G) : brauerProjection (S : Subgroup G) e ≠ 0 :=
    brauerProjection_ne_zero_of_augmentation_ne_zero S.isPGroup
      (center_le_conjInvariants _ he) hε
  refine ⟨fun hD => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hD.isPGroup.exists_le_sylow
    exact ⟨S, ((isDefectGroup_iff.1 hD).2.2 S S.isPGroup (hne S) hS).symm⟩
  · rintro ⟨S, rfl⟩
    exact isDefectGroup_iff.2 ⟨S.isPGroup, hne S, fun Q hQ _ hSQ =>
      (S.maximal_isPGroup.eq_of_le hQ hSQ).symm⟩

/-- **The defect groups of the principal block are the Sylow subgroups.** For a field `k` of
characteristic `p`, the defect groups of the principal block idempotent of `k[G]` are exactly the
Sylow `p`-subgroups of `G` (Webb, Corollary 12.4.7, p. 242). -/
theorem isDefectGroup_principalBlockIdempotent_iff {k : Type*} [Field k] [CharP k p] [Finite G]
    {D : Subgroup G} :
    IsDefectGroup k p (principalBlockIdempotent k G : MonoidAlgebra k G) D ↔
      ∃ S : Sylow p G, D = S :=
  isDefectGroup_iff_sylow_of_augmentation_ne_zero (principalBlockIdempotent k G).property
    (by rw [augmentation_principalBlockIdempotent]; exact one_ne_zero)

end TauCeti
