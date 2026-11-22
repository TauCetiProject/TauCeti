/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.Group.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder
import TauCeti.RepresentationTheory.Invariants

/-!
# The averaging projector onto the invariants of a compact group

Let `K` be a compact group with separately continuous multiplication, `A` a commutative ring in
which `K` has invertible pro-order (`TauCeti.HasUnitProOrder A K`: every open subgroup has index
invertible in `A`), and `σ` a smooth representation of `K` on an `A`-module `V`. Every vector `v`
has an open stabilizer, hence a finite orbit, and the **averaging projector**
`Representation.smoothAverage σ hK` sends `v` to the barycentre `|K v|⁻¹ • ∑_{w ∈ K v} w` of its
orbit. For every open subgroup `H` fixing `v` it is given by the familiar formula
`[K : H]⁻¹ • ∑_{q ∈ K ⧸ H} σ q v`, so it agrees with the average over any finite quotient through
which `v` sees the action, and with Mathlib's `Representation.averageMap` for a finite discrete
group.

For a locally profinite group `G`, a smooth representation `ρ` and a compact open subgroup `U`
of invertible pro-order, `smoothAverage (ρ.comp U.subtype) hU` is the projector `e_U` of
Bernstein's notes onto `V^U`.

## Main definitions

* `Representation.smoothAverage σ hK`: the averaging projector `e_K : V →ₗ[A] V`.

## Main results

* `Representation.smoothAverage_apply_of_le`: `e_K v = [K : H]⁻¹ • ∑_{q ∈ K ⧸ H} σ q v` for every
  open subgroup `H` fixing `v`.
* `Representation.isProj_smoothAverage`, `Representation.range_smoothAverage`: `e_K` is a
  projection onto the invariants `V^K`, and it is idempotent
  (`Representation.smoothAverage_smoothAverage`).
* `Representation.smoothAverage_apply_apply`: `e_K (σ k v) = e_K v`.
* `Representation.ker_smoothAverage`: the kernel of `e_K` is the span of the vectors `σ k x - x`.
* `Representation.IntertwiningMap.smoothAverage_apply`: `e_K` commutes with intertwining maps.
* `Representation.smoothAverage_comp_smoothAverage_subgroup`,
  `Representation.smoothAverage_subgroup_comp_smoothAverage`: for a compact subgroup `H` of
  invertible pro-order, `e_K e_H = e_H e_K = e_K`.
* `Representation.smoothAverage_eq_averageMap`: for a finite discrete group of invertible order,
  `e_K` is Mathlib's `Representation.averageMap`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, p. 11, and Proposition 6(1), p. 14.
-/

public section

open Set

namespace Representation

variable {A K V W : Type*} [CommRing A] [Group K] [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W]

section Formula

variable (σ : Representation A K V)

/-- For `v` fixed by `H`, `σ k v` depends only on the coset `k H`. -/
private theorem apply_out_eq {H : Subgroup K} {v : V} (hv : H ≤ σ.stabilizer v) {k : K}
    {q : K ⧸ H} (hq : (k : K ⧸ H) = q) : σ q.out v = σ k v := by
  subst hq
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H k
  rw [hh, map_mul, mul_apply_eq_comp, mem_stabilizer.1 (hv h.property)]

/-- Summing over the cosets of a smaller subgroup multiplies the sum by the relative index. -/
private theorem finsum_out_of_le {H H' : Subgroup K} (hle : H' ≤ H) [Finite (K ⧸ H')] {v : V}
    (hv : H ≤ σ.stabilizer v) :
    ∑ᶠ q : K ⧸ H', σ q.out v = H'.relIndex H • ∑ᶠ q : K ⧸ H, σ q.out v := by
  classical
  let e := Subgroup.quotientEquivProdOfLE hle
  have : Finite (K ⧸ H) := Finite.of_surjective (Prod.fst ∘ e) <|
    Prod.fst_surjective.comp e.surjective
  have : Finite (H ⧸ H'.subgroupOf H) := Finite.of_surjective (Prod.snd ∘ e) <|
    Prod.snd_surjective.comp e.surjective
  let _ := Fintype.ofFinite (K ⧸ H')
  let _ := Fintype.ofFinite (K ⧸ H)
  let _ := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  have key (x : (K ⧸ H) × (H ⧸ H'.subgroupOf H)) : σ (e.symm x).out v = σ x.1.out v := by
    refine (apply_out_eq σ hv ?_).symm
    have h2 : ((e.symm x).out : K ⧸ H) = (e (e.symm x)).1 := by
      conv_rhs => rw [← QuotientGroup.out_eq' (e.symm x)]
      rfl
    rw [h2, e.apply_symm_apply]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← e.symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [key, Finset.sum_const, Finset.card_univ, Finset.smul_sum]
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/-- The averaging formula over the cosets of `H` does not change when `H` is replaced by a smaller
subgroup of finite index invertible in `A`. -/
private theorem smul_finsum_out_of_le {H H' : Subgroup K} (hle : H' ≤ H) [Finite (K ⧸ H')]
    (hu : IsUnit (H'.index : A)) {v : V} (hv : H ≤ σ.stabilizer v) :
    Ring.inverse (H'.index : A) • ∑ᶠ q : K ⧸ H', σ q.out v =
      Ring.inverse (H.index : A) • ∑ᶠ q : K ⧸ H, σ q.out v := by
  rw [finsum_out_of_le σ hle hv, ← Subgroup.relIndex_mul_index hle, Nat.cast_mul] at *
  obtain ⟨hr, hi⟩ := IsUnit.mul_iff.1 hu
  rw [← Nat.cast_smul_eq_nsmul A, smul_smul]
  congr 1
  obtain ⟨r, hr⟩ := hr
  obtain ⟨i, hi⟩ := hi
  rw [← hr, ← hi, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, mul_comm r i,
    mul_inv_rev, Units.val_mul, mul_assoc, mul_left_comm, Units.inv_mul, mul_one]

/-- The sum over the orbit of `v` is the sum over the cosets of its stabilizer. -/
private theorem finsum_mem_range_eq (v : V) :
    ∑ᶠ w ∈ range fun k : K ↦ σ k v, w = ∑ᶠ q : K ⧸ σ.stabilizer v, σ q.out v := by
  rw [← range_orbitMap, finsum_mem_range (σ.orbitMap_injective v)]
  refine finsum_congr fun q ↦ ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  exact σ.orbitMap_mk v _

/-- The orbit of `v` has as many points as the cosets of its stabilizer. -/
private theorem natCard_range_eq (v : V) :
    Nat.card (range fun k : K ↦ σ k v) = (σ.stabilizer v).index := by
  rw [← range_orbitMap, Nat.card_range_of_injective (σ.orbitMap_injective v), Subgroup.index]

end Formula

section Compact

variable [TopologicalSpace K] [SeparatelyContinuousMul K] [CompactSpace K]
  (σ : Representation A K V) [IsSmooth σ] (hK : TauCeti.HasUnitProOrder A K)

omit [IsSmooth σ] in
include hK in
/-- The barycentre of the orbit of `v` is given by the averaging formula over the cosets of any open
subgroup fixing `v`. -/
private theorem orbitAverage_eq {H : Subgroup K} (hH : IsOpen (H : Set K)) {v : V}
    (hv : H ≤ σ.stabilizer v) :
    Ring.inverse (Nat.card (range fun k : K ↦ σ k v) : A) • ∑ᶠ w ∈ range fun k : K ↦ σ k v, w =
      Ring.inverse (H.index : A) • ∑ᶠ q : K ⧸ H, σ q.out v := by
  have := H.quotient_finite_of_isOpen hH
  rw [natCard_range_eq, finsum_mem_range_eq,
    smul_finsum_out_of_le σ hv (hK.isUnit_index hH) le_rfl]

/-- **The averaging projector** of a smooth representation of a compact group whose pro-order is
invertible in `A`: it sends `v` to the barycentre `|K v|⁻¹ • ∑_{w ∈ K v} w` of its orbit, which
is finite since the stabilizer of `v` is open. -/
noncomputable def smoothAverage : V →ₗ[A] V where
  toFun v :=
    Ring.inverse (Nat.card (range fun k : K ↦ σ k v) : A) • ∑ᶠ w ∈ range fun k : K ↦ σ k v, w
  map_add' v w := by
    have hH := (IsSmooth.isOpen_stabilizer (ρ := σ) v).inter
      (IsSmooth.isOpen_stabilizer (ρ := σ) w)
    let H := σ.stabilizer v ⊓ σ.stabilizer w
    have := H.quotient_finite_of_isOpen hH
    have hv : H ≤ σ.stabilizer v := inf_le_left
    have hw : H ≤ σ.stabilizer w := inf_le_right
    have hvw : H ≤ σ.stabilizer (v + w) := fun h hh ↦ by
      rw [mem_stabilizer, map_add, mem_stabilizer.1 (hv hh), mem_stabilizer.1 (hw hh)]
    rw [orbitAverage_eq σ hK hH hv, orbitAverage_eq σ hK hH hw, orbitAverage_eq σ hK hH hvw,
      ← smul_add, ← finsum_add_distrib (toFinite _) (toFinite _)]
    simp only [map_add]
  map_smul' c v := by
    have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
    have := (σ.stabilizer v).quotient_finite_of_isOpen hH
    have hcv : σ.stabilizer v ≤ σ.stabilizer (c • v) := fun h hh ↦ by
      rw [mem_stabilizer, map_smul, mem_stabilizer.1 hh]
    simp only [RingHom.id_apply]
    rw [orbitAverage_eq σ hK hH le_rfl, orbitAverage_eq σ hK hH hcv, smul_comm c]
    let _ := Fintype.ofFinite (K ⧸ σ.stabilizer v)
    simp only [finsum_eq_sum_of_fintype, map_smul, Finset.smul_sum]

/-- The averaging projector sends `v` to the barycentre of its orbit. -/
theorem smoothAverage_apply (v : V) :
    σ.smoothAverage hK v =
      Ring.inverse (Nat.card (range fun k : K ↦ σ k v) : A) • ∑ᶠ w ∈ range fun k : K ↦ σ k v, w :=
  (rfl)

/-- **Independence of the subgroup.** For every open subgroup `H` fixing `v`, the average of `v` is
`[K : H]⁻¹ • ∑_{q ∈ K ⧸ H} σ q v`. -/
theorem smoothAverage_apply_of_le {H : Subgroup K} (hH : IsOpen (H : Set K)) {v : V}
    (hv : H ≤ σ.stabilizer v) :
    σ.smoothAverage hK v = Ring.inverse (H.index : A) • ∑ᶠ q : K ⧸ H, σ q.out v :=
  orbitAverage_eq σ hK hH hv

/-- The average of a vector is invariant. -/
theorem smoothAverage_apply_mem_invariants (v : V) : σ.smoothAverage hK v ∈ invariants σ := by
  intro k
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
  have := (σ.stabilizer v).quotient_finite_of_isOpen hH
  let _ := Fintype.ofFinite (K ⧸ σ.stabilizer v)
  rw [smoothAverage_apply_of_le σ hK hH le_rfl, map_smul, finsum_eq_sum_of_fintype, map_sum]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm k) _ _ fun q ↦ ?_
  rw [← mul_apply_eq_comp, ← map_mul]
  refine (apply_out_eq σ le_rfl ?_).symm
  rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out, MulAction.toPerm_apply]

omit [TopologicalSpace K] [SeparatelyContinuousMul K] [CompactSpace K] [IsSmooth σ] in
/-- For an invariant vector, the sum over the cosets of `H` is `[K : H]` copies of the vector. -/
private theorem finsum_out_of_mem_invariants {H : Subgroup K} [Finite (K ⧸ H)] {v : V}
    (hv : v ∈ invariants σ) : ∑ᶠ q : K ⧸ H, σ q.out v = H.index • v := by
  let _ := Fintype.ofFinite (K ⧸ H)
  simp only [finsum_eq_sum_of_fintype, hv _, Finset.sum_const, Finset.card_univ,
    Subgroup.index, Nat.card_eq_fintype_card]

/-- The averaging projector fixes the invariant vectors. -/
theorem smoothAverage_apply_of_mem_invariants {v : V} (hv : v ∈ invariants σ) :
    σ.smoothAverage hK v = v := by
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
  have := (σ.stabilizer v).quotient_finite_of_isOpen hH
  rw [smoothAverage_apply_of_le σ hK hH le_rfl, finsum_out_of_mem_invariants σ hv,
    ← Nat.cast_smul_eq_nsmul A, smul_smul, Ring.inverse_mul_cancel _ (hK.isUnit_index hH),
    one_smul]

/-- The averaging projector is a projection onto the invariants. -/
theorem isProj_smoothAverage : LinearMap.IsProj (invariants σ) (σ.smoothAverage hK) :=
  ⟨σ.smoothAverage_apply_mem_invariants hK, fun _ ↦ σ.smoothAverage_apply_of_mem_invariants hK⟩

/-- The range of the averaging projector is the submodule of invariants. -/
theorem range_smoothAverage : LinearMap.range (σ.smoothAverage hK) = invariants σ :=
  (σ.isProj_smoothAverage hK).range

/-- The averaging projector is idempotent. -/
@[simp]
theorem smoothAverage_smoothAverage (v : V) :
    σ.smoothAverage hK (σ.smoothAverage hK v) = σ.smoothAverage hK v :=
  σ.smoothAverage_apply_of_mem_invariants hK (σ.smoothAverage_apply_mem_invariants hK v)

/-- The averaging projector does not see the action: `v` and `σ k v` have the same orbit. -/
@[simp]
theorem smoothAverage_apply_apply (k : K) (v : V) :
    σ.smoothAverage hK (σ k v) = σ.smoothAverage hK v := by
  have : (range fun g : K ↦ σ g (σ k v)) = range fun g : K ↦ σ g v := by
    conv_rhs => rw [← (Equiv.mulRight k).surjective.range_comp]
    congr 1
    funext g
    simp only [Function.comp_apply, Equiv.coe_mulRight, map_mul, mul_apply_eq_comp]
  rw [smoothAverage_apply, smoothAverage_apply, this]

/-- The difference between the average of a vector and the vector lies in the span of the
vectors `σ k x - x`. -/
theorem smoothAverage_apply_sub_mem_ker (v : V) :
    σ.smoothAverage hK v - v ∈ Coinvariants.ker σ := by
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
  have := (σ.stabilizer v).quotient_finite_of_isOpen hH
  let _ := Fintype.ofFinite (K ⧸ σ.stabilizer v)
  have hv : v = Ring.inverse ((σ.stabilizer v).index : A) • ∑ _q : K ⧸ σ.stabilizer v, v := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index,
      ← Nat.cast_smul_eq_nsmul A, smul_smul, Ring.inverse_mul_cancel _ (hK.isUnit_index hH),
      one_smul]
  have hsub : Ring.inverse ((σ.stabilizer v).index : A) •
      ∑ q : K ⧸ σ.stabilizer v, σ q.out v - v =
      Ring.inverse ((σ.stabilizer v).index : A) •
        ∑ q : K ⧸ σ.stabilizer v, (σ q.out v - v) := by
    rw [Finset.sum_sub_distrib, smul_sub, ← hv]
  rw [smoothAverage_apply_of_le σ hK hH le_rfl, finsum_eq_sum_of_fintype, hsub]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ ↦ Coinvariants.sub_mem_ker _ _)

/-- The kernel of the averaging projector is the span of the vectors `σ k x - x`. -/
theorem ker_smoothAverage : LinearMap.ker (σ.smoothAverage hK) = Coinvariants.ker σ := by
  refine le_antisymm (fun v hv ↦ ?_) (Submodule.span_le.2 ?_)
  · simpa [LinearMap.mem_ker.1 hv] using
      Submodule.neg_mem _ (σ.smoothAverage_apply_sub_mem_ker hK v)
  · rintro _ ⟨⟨k, x⟩, rfl⟩
    simp

/-- The averaging projector commutes with intertwining maps between smooth representations. -/
theorem IntertwiningMap.smoothAverage_apply {ρ : Representation A K W} [IsSmooth ρ]
    (f : σ.IntertwiningMap ρ) (v : V) :
    f (σ.smoothAverage hK v) = ρ.smoothAverage hK (f v) := by
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
  have := (σ.stabilizer v).quotient_finite_of_isOpen hH
  let _ := Fintype.ofFinite (K ⧸ σ.stabilizer v)
  rw [σ.smoothAverage_apply_of_le hK hH le_rfl, ρ.smoothAverage_apply_of_le hK hH
    (f.stabilizer_le v), map_smul, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  simp only [f.isIntertwining]

/-- **Nested averages.** For a compact subgroup `H` of invertible pro-order, averaging over `H` and
then over `K` is averaging over `K`. -/
theorem smoothAverage_comp_smoothAverage_subgroup (H : Subgroup K) [CompactSpace H]
    (hH : TauCeti.HasUnitProOrder A H) :
    σ.smoothAverage hK ∘ₗ smoothAverage (σ.comp H.subtype) hH = σ.smoothAverage hK := by
  ext v
  rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_smoothAverage]
  refine Submodule.span_mono ?_ (smoothAverage_apply_sub_mem_ker (σ.comp H.subtype) hH v)
  rintro _ ⟨⟨h, x⟩, rfl⟩
  exact ⟨⟨h, x⟩, rfl⟩

/-- **Nested averages.** For a compact subgroup `H` of invertible pro-order, averaging over `K` and
then over `H` is averaging over `K`. -/
theorem smoothAverage_subgroup_comp_smoothAverage (H : Subgroup K) [CompactSpace H]
    (hH : TauCeti.HasUnitProOrder A H) :
    smoothAverage (σ.comp H.subtype) hH ∘ₗ σ.smoothAverage hK = σ.smoothAverage hK := by
  ext v
  exact smoothAverage_apply_of_mem_invariants (σ.comp H.subtype) hH
    fun h ↦ σ.smoothAverage_apply_mem_invariants hK v h

end Compact

/-- For a finite discrete group of order invertible in `A`, the averaging projector is Mathlib's
`Representation.averageMap`. -/
theorem smoothAverage_eq_averageMap [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
    [Invertible (Fintype.card K : A)] (σ : Representation A K V)
    (hK : TauCeti.HasUnitProOrder A K) : σ.smoothAverage hK = σ.averageMap := by
  ext v
  let _ := Fintype.ofFinite (K ⧸ (⊥ : Subgroup K))
  rw [σ.smoothAverage_apply_of_le hK (isOpen_discrete ((⊥ : Subgroup K) : Set K)) bot_le,
    averageMap_apply, Subgroup.index_bot, Nat.card_eq_fintype_card, Ring.inverse_invertible,
    finsum_eq_sum_of_fintype]
  congr 1
  exact Fintype.sum_equiv (QuotientGroup.quotientBot (G := K)).toEquiv _ _ fun q ↦ by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl

end Representation
