/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# The relative norm and the relative transfer of a subgroup

Let `ρ : Representation R G V` and let `H ≤ G` be a subgroup of finite index. Summing the action
over a left transversal of `H` gives two endomorphisms of `V`,

`relNorm ρ H = ∑ q : G ⧸ H, ρ q.out`   and   `relTransfer ρ H = ∑ q : G ⧸ H, ρ q.out⁻¹`,

which refine the norm `Representation.norm ρ = ∑ g : G, ρ g` of a finite group: the norm of `G`
is the relative norm composed with the norm of `H`, and it is also the norm of `H` composed with
the relative transfer.

Neither endomorphism is canonical — each depends on the chosen transversal, here `Quotient.out` —
but each becomes canonical after passing to the appropriate quotient. The relative norm is
independent of the transversal on the invariants `V^H`, where it takes values in `V^G` and
restricts to multiplication by `[G : H]` on `V^G`; the relative transfer is independent of the
transversal modulo the augmentation submodule of `H`, into which it carries the augmentation
submodule of `G`. Modulo the larger augmentation submodule of `G`, the relative transfer is
multiplication by `[G : H]`.

These are the two maps that give restriction and corestriction on the Tate cohomology of a
subgroup in the two degrees where Tate cohomology is not ordinary group cohomology or homology.

## Main definitions

* `Representation.relNorm`: the relative norm `∑ q : G ⧸ H, ρ q.out`.
* `Representation.relTransfer`: the relative transfer `∑ q : G ⧸ H, ρ q.out⁻¹`.

## Main results

* `Representation.relNorm_comp_norm`: `N_{G/H} ∘ N_H = N_G`.
* `Representation.norm_comp_relTransfer`: `N_H ∘ N_{G/H}' = N_G`.
* `Representation.relNorm_mem_invariants`: the relative norm carries `V^H` into `V^G`.
* `Representation.relNorm_apply_of_mem_invariants`: on `V^G` the relative norm is `[G : H] • ·`.
* `Representation.relTransfer_mem_coinvariantsKer`: the relative transfer carries the augmentation
  submodule of `G` into the augmentation submodule of `H`.
* `Representation.relTransfer_sub_index_nsmul_mem`: modulo the augmentation submodule of `G` the
  relative transfer is `[G : H] • ·`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1.
-/

public noncomputable section

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  (ρ : Representation R G V) (H : Subgroup G)

section Defs

variable [Fintype (G ⧸ H)]

/-- The relative norm of a finite-index subgroup `H ≤ G`: the sum of `ρ` over the transversal of
`H` given by `Quotient.out`. On the `H`-invariants it does not depend on that choice and lands in
the `G`-invariants; see `Representation.relNorm_mem_invariants`. -/
def relNorm : Module.End R V := ∑ q : G ⧸ H, ρ q.out

/-- The relative transfer of a finite-index subgroup `H ≤ G`: the sum of `ρ` over the inverses of
the transversal of `H` given by `Quotient.out`, which form a transversal of the right cosets.
Modulo the augmentation submodule of `H` it does not depend on that choice; see
`Representation.relTransfer_mem_coinvariantsKer`. -/
def relTransfer : Module.End R V := ∑ q : G ⧸ H, ρ q.out⁻¹

variable {ρ H}

theorem relNorm_apply (x : V) : relNorm ρ H x = ∑ q : G ⧸ H, ρ q.out x := by
  simp [relNorm]

theorem relTransfer_apply (x : V) : relTransfer ρ H x = ∑ q : G ⧸ H, ρ q.out⁻¹ x := by
  simp [relTransfer]

end Defs

section Norm

variable [Fintype G] {ρ H}

/-- A subgroup of a finite group is a finite type. -/
noncomputable local instance fintypeSubgroup : Fintype H := Fintype.ofFinite H

/-- The quotient of a finite group by a subgroup is a finite type. -/
noncomputable local instance fintypeQuotientGroup : Fintype (G ⧸ H) :=
  H.fintypeQuotientOfFiniteIndex

private theorem norm_apply' (x : V) : ρ.norm x = ∑ g : G, ρ g x := by
  simp [Representation.norm]

/-- The norm of `G` is the relative norm of `H` evaluated on the norm of `H`. -/
theorem relNorm_norm_apply (x : V) :
    relNorm ρ H (Representation.norm (ρ.comp H.subtype) x) = ρ.norm x := by
  conv_rhs => rw [norm_apply', TauCeti.sum_eq_sum_quotient_sum H fun g => ρ g x]
  rw [relNorm_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Representation.norm, map_sum, ← Module.End.mul_apply, ← map_mul]

/-- The norm of `G` is the relative norm of `H` composed with the norm of `H`. -/
theorem relNorm_comp_norm :
    relNorm ρ H ∘ₗ Representation.norm (ρ.comp H.subtype) = ρ.norm :=
  LinearMap.ext relNorm_norm_apply

/-- The norm of `G` is the norm of `H` evaluated on the relative transfer of `H`. -/
theorem norm_relTransfer_apply (x : V) :
    Representation.norm (ρ.comp H.subtype) (relTransfer ρ H x) = ρ.norm x := by
  conv_rhs => rw [norm_apply', TauCeti.sum_eq_sum_quotient_sum' H fun g => ρ g x]
  rw [relTransfer_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Representation.norm, LinearMap.sum_apply, ← Module.End.mul_apply, ← map_mul]

/-- The norm of `G` is the norm of `H` composed with the relative transfer of `H`. -/
theorem norm_comp_relTransfer :
    Representation.norm (ρ.comp H.subtype) ∘ₗ relTransfer ρ H = ρ.norm :=
  LinearMap.ext norm_relTransfer_apply

/-- The image of the norm of `G` is contained in the image of the norm of `H`. -/
theorem range_norm_le_range_norm_comp_subtype :
    LinearMap.range ρ.norm ≤ LinearMap.range (Representation.norm (ρ.comp H.subtype)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨relTransfer ρ H x, norm_relTransfer_apply x⟩

/-- The kernel of the norm of `H` is contained in the kernel of the norm of `G`. -/
theorem ker_norm_comp_subtype_le_ker_norm :
    LinearMap.ker (Representation.norm (ρ.comp H.subtype)) ≤ LinearMap.ker ρ.norm := by
  intro x hx
  rw [LinearMap.mem_ker, ← relNorm_norm_apply (H := H) x, LinearMap.mem_ker.mp hx, map_zero]

variable (ρ H)

/-- The relative transfer maps the kernel of the norm of `G` to the kernel of the norm of `H`. -/
def relTransferKerNorm :
    LinearMap.ker ρ.norm →ₗ[R]
      LinearMap.ker (Representation.norm (ρ.comp H.subtype)) :=
  (relTransfer ρ H).restrict fun x hx =>
    LinearMap.mem_ker.2 <| (norm_relTransfer_apply x).trans (LinearMap.mem_ker.mp hx)

@[simp]
theorem coe_relTransferKerNorm (x : LinearMap.ker ρ.norm) :
    (relTransferKerNorm ρ H x : V) = relTransfer ρ H x := by
  unfold relTransferKerNorm
  rfl

end Norm

section Invariants

variable {ρ H}

/-- The image of an `H`-invariant element under `ρ` depends only on the coset `aH`, which is why
the relative norm is independent of the transversal on the `H`-invariants. -/
theorem apply_eq_apply_of_mk_eq {x : V}
    (hx : x ∈ Representation.invariants (ρ.comp H.subtype)) {a b : G}
    (hab : (a : G ⧸ H) = (b : G ⧸ H)) : ρ a x = ρ b x := by
  obtain ⟨h, rfl⟩ : ∃ h : H, a * (h : G) = b :=
    ⟨⟨a⁻¹ * b, QuotientGroup.eq.mp hab⟩, by simp⟩
  rw [map_mul, Module.End.mul_apply]
  exact congrArg (ρ a) (((mem_invariants _ _).mp hx h).symm)

/-- A `G`-invariant element is `H`-invariant. -/
theorem invariants_le_invariants_comp_subtype :
    ρ.invariants ≤ Representation.invariants (ρ.comp H.subtype) :=
  fun _ hx h => hx (h : G)

variable [Fintype (G ⧸ H)]

/-- The relative norm carries the `H`-invariants into the `G`-invariants. -/
theorem relNorm_mem_invariants {x : V}
    (hx : x ∈ Representation.invariants (ρ.comp H.subtype)) :
    relNorm ρ H x ∈ ρ.invariants := by
  rw [mem_invariants]
  intro g
  rw [relNorm_apply, map_sum]
  refine Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  refine apply_eq_apply_of_mk_eq hx ?_
  rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']

/-- On `G`-invariant elements the relative norm is multiplication by the index. -/
theorem relNorm_apply_of_mem_invariants {x : V} (hx : x ∈ ρ.invariants) :
    relNorm ρ H x = H.index • x := by
  rw [relNorm_apply, Finset.sum_congr rfl fun q _ => (mem_invariants _ _).mp hx q.out,
    Finset.sum_const, Finset.card_univ]
  simp [Subgroup.index, Nat.card_eq_fintype_card]

variable (ρ H)

/-- The relative norm as a linear map from the `H`-invariants to the `G`-invariants. -/
def relNormInvariants :
    Representation.invariants (ρ.comp H.subtype) →ₗ[R] ρ.invariants :=
  (relNorm ρ H).restrict fun _ hx => relNorm_mem_invariants hx

@[simp]
theorem coe_relNormInvariants (x : Representation.invariants (ρ.comp H.subtype)) :
    (relNormInvariants ρ H x : V) = relNorm ρ H x := by
  unfold relNormInvariants
  rfl

end Invariants

section Coinvariants

variable {ρ H}

/-- The augmentation submodule of `H` is contained in the augmentation submodule of `G`. -/
theorem coinvariantsKer_comp_subtype_le :
    Coinvariants.ker (ρ.comp H.subtype) ≤ Coinvariants.ker ρ := by
  rw [Coinvariants.ker, Coinvariants.ker, Submodule.span_le]
  rintro _ ⟨⟨h, y⟩, rfl⟩
  exact Submodule.subset_span ⟨((h : G), y), rfl⟩

variable [Fintype (G ⧸ H)]

/-- Modulo the augmentation submodule of `G`, the relative transfer is multiplication by the
index. -/
theorem relTransfer_sub_index_nsmul_mem (x : V) :
    relTransfer ρ H x - H.index • x ∈ Coinvariants.ker ρ := by
  have hrw : relTransfer ρ H x - H.index • x = ∑ q : G ⧸ H, (ρ (q.out : G)⁻¹ x - x) := by
    rw [relTransfer_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    simp [Subgroup.index, Nat.card_eq_fintype_card]
  rw [hrw]
  exact Submodule.sum_mem _ fun q _ => Coinvariants.sub_mem_ker _ _

/-- The relative transfer carries the augmentation submodule of `G` into the augmentation
submodule of `H`; it is therefore the transfer of `H` on coinvariants. -/
theorem relTransfer_mem_coinvariantsKer {x : V} (hx : x ∈ Coinvariants.ker ρ) :
    relTransfer ρ H x ∈ Coinvariants.ker (ρ.comp H.subtype) := by
  have hmem : ∀ (g : G) (q : G ⧸ H), (g * ((g⁻¹ • q).out : G))⁻¹ * (q.out : G) ∈ H := by
    intro g q
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe,
      QuotientGroup.out_eq', smul_inv_smul]
  have hgrp : ∀ (g : G) (q : G ⧸ H),
      ((g * ((g⁻¹ • q).out : G))⁻¹ * (q.out : G))⁻¹ * ((g⁻¹ • q).out : G)⁻¹ =
        (q.out : G)⁻¹ * g := fun g q => by group
  have hmap : (Coinvariants.ker ρ).map (relTransfer ρ H) ≤
      Coinvariants.ker (ρ.comp H.subtype) := by
    rw [Coinvariants.ker, Submodule.map_span_le]
    rintro _ ⟨⟨g, y⟩, rfl⟩
    have hreindex : ∑ q : G ⧸ H, ρ (q.out : G)⁻¹ y =
        ∑ q : G ⧸ H, ρ (((g⁻¹ • q).out : G))⁻¹ y :=
      (Fintype.sum_bijective (g⁻¹ • ·) (MulAction.bijective _) _ _ fun _ => rfl).symm
    have hsum : relTransfer ρ H (ρ g y - y) =
        ∑ q : G ⧸ H, (ρ (q.out : G)⁻¹ (ρ g y) - ρ (((g⁻¹ • q).out : G))⁻¹ y) := by
      rw [map_sub, relTransfer_apply, relTransfer_apply, hreindex, ← Finset.sum_sub_distrib]
    rw [hsum]
    refine Submodule.sum_mem _ fun q _ => ?_
    refine Coinvariants.mem_ker_of_eq
      (⟨(g * ((g⁻¹ • q).out : G))⁻¹ * (q.out : G), hmem g q⟩⁻¹)
      (ρ (((g⁻¹ • q).out : G))⁻¹ y) _ ?_
    congr 1
    rw [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
      ← map_mul]
    congr 1
    exact congrArg ρ (hgrp g q)
  exact hmap ⟨x, hx, rfl⟩

end Coinvariants

end Representation
