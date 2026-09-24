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
* `Representation.relTransfer_sub_sum_mem`: modulo the augmentation submodule of `H` the relative
  transfer is the sum over any transversal of `H`.
* `Representation.relTransfer_map_sub_mem`: modulo the augmentation submodule of `H'` the relative
  transfer commutes with a map of representations along a group isomorphism carrying `H` to `H'`.
* `Representation.relTransfer_relTransfer_sub_relTransfer_mem`: modulo the augmentation submodule
  of `K` the relative transfer is transitive along a tower `K ≤ H ≤ G`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1.
-/

public noncomputable section

namespace Representation

variable {R G V : Type*} [Group G]

section Semiring

variable [Semiring R] [AddCommMonoid V] [Module R V]
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
  conv_rhs => rw [norm_apply', H.sum_eq_sum_leftCosets fun g => ρ g x]
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
  conv_rhs => rw [norm_apply', H.sum_eq_sum_rightCosets fun g => ρ g x]
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

end Semiring

section Ring

variable [CommRing R] [AddCommGroup V] [Module R V]
  (ρ : Representation R G V) (H : Subgroup G)

section Invariants

variable {ρ H}

/-- The image of an `H`-invariant element under `ρ` depends only on the coset `aH`, which is why
the relative norm is independent of the transversal on the `H`-invariants. -/
theorem apply_eq_apply_of_quotientGroup_mk_eq {x : V}
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
  refine apply_eq_apply_of_quotientGroup_mk_eq hx ?_
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

/-- **An intertwining map carries the augmentation submodule into the augmentation submodule.**
Only the compatibility of the actions is used, so `e` need not be a homomorphism. -/
theorem coinvariantsKer_map_le {G' V' : Type*} [Group G'] [AddCommGroup V'] [Module R V']
    {ρ' : Representation R G' V'} (e : G → G') (φ : V →ₗ[R] V')
    (hφ : ∀ g x, φ (ρ g x) = ρ' (e g) (φ x)) :
    (Coinvariants.ker ρ).map φ ≤ Coinvariants.ker ρ' := by
  rw [Coinvariants.ker, Submodule.map_span_le]
  rintro _ ⟨⟨g, x⟩, rfl⟩
  rw [map_sub, hφ]
  exact Coinvariants.sub_mem_ker _ _

/-- **Precomposing the restricting homomorphism with a surjection does not change the
augmentation submodule.** -/
theorem coinvariantsKer_comp_comp_of_surjective {G' G'' : Type*} [Group G'] [Group G'']
    (ψ : G' →* G) (ε : G'' →* G') (hε : Function.Surjective ε) :
    Coinvariants.ker (ρ.comp (ψ.comp ε)) = Coinvariants.ker (ρ.comp ψ) := by
  rw [Coinvariants.ker, Coinvariants.ker]
  exact congrArg (Submodule.span R)
    ((Prod.map_surjective.2 ⟨hε, Function.surjective_id⟩).range_comp
      fun gv : G' × V => (ρ.comp ψ) gv.1 gv.2 - gv.2)

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

/-- **The relative transfer is computed by any transversal, modulo the augmentation submodule of
`H`.** `relTransfer` sums `ρ q.out⁻¹` over the transversal `Quotient.out`; any family `f` whose
classes exhaust `G ⧸ H` bijectively computes the same element of the coinvariants. -/
theorem relTransfer_sub_sum_mem {ι : Type*} [Fintype ι] (f : ι → G)
    (hf : Function.Bijective fun i => ((f i : G) : G ⧸ H)) (x : V) :
    relTransfer ρ H x - ∑ i, ρ (f i)⁻¹ x ∈ Coinvariants.ker (ρ.comp H.subtype) := by
  set e : ι ≃ G ⧸ H := Equiv.ofBijective _ hf
  rw [relTransfer_apply, ← Equiv.sum_comp e.symm fun i => ρ (f i)⁻¹ x, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => ?_
  -- Two representatives of the coset `q` differ by an element of `H`.
  have hq : (f (e.symm q))⁻¹ * (q.out : G) ∈ H :=
    QuotientGroup.eq.mp ((e.apply_symm_apply q).trans q.out_eq'.symm)
  have hg : H.subtype ⟨(f (e.symm q))⁻¹ * (q.out : G), hq⟩⁻¹ * (f (e.symm q))⁻¹ =
      ((q.out : G))⁻¹ := by
    rw [Subgroup.subtype_apply, InvMemClass.coe_inv, Subgroup.coe_mk]
    group
  refine Coinvariants.mem_ker_of_eq (ρ := ρ.comp H.subtype) ⟨_, hq⟩⁻¹
    (ρ (f (e.symm q))⁻¹ x) _ ?_
  congr 1
  rw [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, hg]

/-- **The relative transfer commutes with a map of representations along a group isomorphism**,
modulo the augmentation submodule of `H'`. Here `e : G ≃* G'` carries `H` onto `H'` and `φ`
intertwines `ρ` with `ρ'` along `e`. -/
theorem relTransfer_map_sub_mem {G' V' : Type*} [Group G'] [AddCommGroup V'] [Module R V']
    {ρ' : Representation R G' V'} (e : G ≃* G') (φ : V →ₗ[R] V')
    (hφ : ∀ g x, φ (ρ g x) = ρ' (e g) (φ x)) {H' : Subgroup G'}
    (he : H.map (e : G →* G') = H') [Fintype (G' ⧸ H')] (x : V) :
    φ (relTransfer ρ H x) - relTransfer ρ' H' (φ x) ∈ Coinvariants.ker (ρ'.comp H'.subtype) := by
  have hmem : ∀ a b : G, ((e a : G') : G' ⧸ H') = ((e b : G') : G' ⧸ H') ↔
      ((a : G ⧸ H) = (b : G ⧸ H)) := fun a b => by
    rw [QuotientGroup.eq, QuotientGroup.eq, ← he, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_iff_mem e.injective
  -- Carrying the `Quotient.out` transversal of `H` across `e` gives a transversal of `H'`, but
  -- not the one `Quotient.out` picks there.
  have hbij : Function.Bijective fun q : G ⧸ H => ((e (q.out : G) : G') : G' ⧸ H') := by
    refine ⟨fun a b hab => ?_, fun r => ⟨((e.symm (r.out : G') : G) : G ⧸ H), ?_⟩⟩
    · simpa using (hmem _ _).1 hab
    · dsimp only
      rw [(hmem (Quotient.out _) (e.symm (r.out : G'))).2 (QuotientGroup.out_eq' _),
        e.apply_symm_apply, QuotientGroup.out_eq']
  have hsum : φ (relTransfer ρ H x) = ∑ q : G ⧸ H, ρ' (e (q.out : G))⁻¹ (φ x) := by
    simp [relTransfer_apply, hφ]
  rw [hsum, ← neg_sub (relTransfer ρ' H' (φ x))]
  exact Submodule.neg_mem _ (relTransfer_sub_sum_mem _ hbij (φ x))

/-- **The relative transfer is transitive along a tower `K ≤ H ≤ G`, modulo the augmentation
submodule of `K`.** Transferring from `G` to `H` and then from `H` to `K` agrees with the
transfer from `G` to `K`. -/
theorem relTransfer_relTransfer_sub_relTransfer_mem {K : Subgroup G} (hKH : K ≤ H)
    [Fintype (G ⧸ K)] [Fintype (H ⧸ K.subgroupOf H)] (x : V) :
    relTransfer (ρ.comp H.subtype) (K.subgroupOf H) (relTransfer ρ H x) - relTransfer ρ K x ∈
      Coinvariants.ker (ρ.comp K.subtype) := by
  set e := Subgroup.quotientEquivProdOfLE hKH
  -- The composite transfer sums over the products `q.out * s.out` of the two chosen
  -- transversals, which form a transversal of `K` in `G` but not the one `Quotient.out` picks.
  have hcoset : ∀ t : G ⧸ K, (((e t).1.out * ((e t).2.out : G) : G) : G ⧸ K) = t := fun t => by
    conv_rhs => rw [← e.symm_apply_apply t, ← Prod.mk.eta (p := e t), ← (e t).2.out_eq']
    rw [Subgroup.quotientEquivProdOfLE_symm_apply, Quotient.map'_mk'']
  have hprod : ∑ t : G ⧸ K, ρ ((e t).1.out * ((e t).2.out : G))⁻¹ x =
      relTransfer (ρ.comp H.subtype) (K.subgroupOf H) (relTransfer ρ H x) := by
    rw [← Equiv.sum_comp e.symm fun t : G ⧸ K => ρ ((e t).1.out * ((e t).2.out : G))⁻¹ x]
    simp only [e.apply_symm_apply]
    rw [relTransfer_apply, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [relTransfer_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [← Module.End.mul_apply, ← map_mul]
  rw [← hprod, ← neg_sub (relTransfer ρ K x)]
  exact Submodule.neg_mem _ (relTransfer_sub_sum_mem _ (by simp [hcoset]) x)

end Coinvariants

end Ring

end Representation
