/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import TauCeti.RepresentationTheory.RelativeNorm
public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.Group.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder
import TauCeti.Algebra.Module.NatInt
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

* `Representation.smoothAverage_apply_of_le`, `Representation.smoothAverage_apply_eq_relNorm`:
  `e_K v = [K : H]⁻¹ • ∑_{q ∈ K ⧸ H} σ q v = [K : H]⁻¹ • relNorm σ H v` for every open subgroup `H`
  fixing `v`.
* `Representation.isProj_smoothAverage`, `Representation.range_smoothAverage`: `e_K` is a
  projection onto the invariants `V^K`, and it is idempotent
  (`Representation.smoothAverage_smoothAverage`, `Representation.smoothAverage_comp_smoothAverage`).
* `Representation.smoothAverage_apply_apply`, `Representation.apply_smoothAverage_apply`:
  `e_K (σ k v) = e_K v` and `σ k (e_K v) = e_K v`.
* `Representation.ker_smoothAverage`: the kernel of `e_K` is the span of the vectors `σ k x - x`.
* `Representation.IntertwiningMap.map_smoothAverage`: `e_K` commutes with intertwining maps.
* `Representation.smoothAverage_smoothAverage_subgroup`,
  `Representation.smoothAverage_subgroup_smoothAverage`,
  `Representation.smoothAverage_comp_smoothAverage_subgroup`,
  `Representation.smoothAverage_subgroup_comp_smoothAverage`: for a compact subgroup `H` of
  invertible pro-order, `e_K e_H = e_H e_K = e_K`.
* `Representation.smoothAverage_eq_averageMap`: for a finite group of invertible order (with any
  topology for which `σ` is smooth), `e_K` is Mathlib's `Representation.averageMap`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, p. 11, and Proposition 6(1), p. 14.
-/

public section

open Set

namespace Representation

variable {A K V W : Type*} [CommRing A] [Group K] [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

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
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : (σ.stabilizer v).FiniteIndex := Subgroup.finiteIndex_of_le hv
  rw [natCard_range_eq_index_stabilizer, finsum_mem_range_eq_finsum_out, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, ← relNorm_apply, ← relNorm_apply,
    inverse_index_smul_relNorm_apply_of_le σ hv (hK.isUnit_index hH) fun h ↦
      mem_stabilizer.1 h.property]

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
    have hcv : σ.stabilizer v ≤ σ.stabilizer (c • v) := fun h hh ↦ by
      rw [mem_stabilizer, map_smul, mem_stabilizer.1 hh]
    simp only [RingHom.id_apply]
    rw [orbitAverage_eq σ hK hH le_rfl, orbitAverage_eq σ hK hH hcv, smul_comm c]
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

/-- The averaging projector in terms of the relative norm: for every open subgroup `H` fixing `v`,
`e_K v = [K : H]⁻¹ • relNorm σ H v`. -/
theorem smoothAverage_apply_eq_relNorm {H : Subgroup K} [Fintype (K ⧸ H)]
    (hH : IsOpen (H : Set K)) {v : V} (hv : H ≤ σ.stabilizer v) :
    σ.smoothAverage hK v = Ring.inverse (H.index : A) • relNorm σ H v := by
  rw [σ.smoothAverage_apply_of_le hK hH hv, finsum_eq_sum_of_fintype, relNorm_apply]

/-- The average of a vector is invariant. -/
theorem smoothAverage_apply_mem_invariants (v : V) : σ.smoothAverage hK v ∈ invariants σ := by
  intro k
  rw [σ.smoothAverage_apply_eq_relNorm hK (IsSmooth.isOpen_stabilizer v) le_rfl, map_smul,
    relNorm_apply_eq_self σ (fun h ↦ mem_stabilizer.1 h.property) k]

/-- The group acts trivially on the average of a vector. -/
@[simp]
theorem apply_smoothAverage_apply (k : K) (v : V) :
    σ k (σ.smoothAverage hK v) = σ.smoothAverage hK v :=
  σ.smoothAverage_apply_mem_invariants hK v k

/-- The averaging projector fixes the invariant vectors. -/
theorem smoothAverage_apply_of_mem_invariants {v : V} (hv : v ∈ invariants σ) :
    σ.smoothAverage hK v = v := by
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
  rw [σ.smoothAverage_apply_eq_relNorm hK hH le_rfl, relNorm_apply_of_forall_apply_eq σ hv,
    Ring.inverse_natCast_smul_nsmul (hK.isUnit_index hH)]

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

/-- The averaging projector is idempotent, as an identity of linear maps: `e_K ∘ e_K = e_K`. -/
@[simp]
theorem smoothAverage_comp_smoothAverage :
    σ.smoothAverage hK ∘ₗ σ.smoothAverage hK = σ.smoothAverage hK :=
  LinearMap.ext (σ.smoothAverage_smoothAverage hK)

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
  have h := Submodule.smul_mem _ (Ring.inverse ((σ.stabilizer v).index : A))
    (relNorm_sub_index_nsmul_mem (ρ := σ) (H := σ.stabilizer v) v)
  rwa [smul_sub, Ring.inverse_natCast_smul_nsmul (hK.isUnit_index hH),
    ← σ.smoothAverage_apply_eq_relNorm hK hH le_rfl] at h

/-- The kernel of the averaging projector is the span of the vectors `σ k x - x`. -/
theorem ker_smoothAverage : LinearMap.ker (σ.smoothAverage hK) = Coinvariants.ker σ := by
  refine le_antisymm (fun v hv ↦ ?_) (Submodule.span_le.2 ?_)
  · simpa [LinearMap.mem_ker.1 hv] using
      Submodule.neg_mem _ (σ.smoothAverage_apply_sub_mem_ker hK v)
  · rintro _ ⟨⟨k, x⟩, rfl⟩
    simp

/-- The averaging projector commutes with intertwining maps between smooth representations. -/
theorem IntertwiningMap.map_smoothAverage {ρ : Representation A K W} [IsSmooth ρ]
    (f : σ.IntertwiningMap ρ) (v : V) :
    f (σ.smoothAverage hK v) = ρ.smoothAverage hK (f v) := by
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) v
  rw [σ.smoothAverage_apply_eq_relNorm hK hH le_rfl,
    ρ.smoothAverage_apply_eq_relNorm hK hH (f.stabilizer_le v), map_smul, relNorm_apply,
    relNorm_apply, map_sum]
  simp only [f.isIntertwining]

/-- **Nested averages.** For a compact subgroup `H` of invertible pro-order, averaging over `H` and
then over `K` is averaging over `K`. -/
@[simp]
theorem smoothAverage_smoothAverage_subgroup (H : Subgroup K) [CompactSpace H]
    (hH : TauCeti.HasUnitProOrder A H) (v : V) :
    σ.smoothAverage hK (smoothAverage (σ.comp H.subtype) hH v) = σ.smoothAverage hK v := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_smoothAverage]
  refine Submodule.span_mono ?_ (smoothAverage_apply_sub_mem_ker (σ.comp H.subtype) hH v)
  rintro _ ⟨⟨h, x⟩, rfl⟩
  exact ⟨⟨h, x⟩, rfl⟩

/-- **Nested averages.** For a compact subgroup `H` of invertible pro-order, averaging over `K` and
then over `H` is averaging over `K`. -/
@[simp]
theorem smoothAverage_subgroup_smoothAverage (H : Subgroup K) [CompactSpace H]
    (hH : TauCeti.HasUnitProOrder A H) (v : V) :
    smoothAverage (σ.comp H.subtype) hH (σ.smoothAverage hK v) = σ.smoothAverage hK v :=
  smoothAverage_apply_of_mem_invariants (σ.comp H.subtype) hH
    fun h ↦ σ.smoothAverage_apply_mem_invariants hK v h

/-- **Nested averages**, as an identity of linear maps: `e_K ∘ e_H = e_K`. -/
@[simp]
theorem smoothAverage_comp_smoothAverage_subgroup (H : Subgroup K) [CompactSpace H]
    (hH : TauCeti.HasUnitProOrder A H) :
    σ.smoothAverage hK ∘ₗ smoothAverage (σ.comp H.subtype) hH = σ.smoothAverage hK :=
  LinearMap.ext (σ.smoothAverage_smoothAverage_subgroup hK H hH)

/-- **Nested averages**, as an identity of linear maps: `e_H ∘ e_K = e_K`. -/
@[simp]
theorem smoothAverage_subgroup_comp_smoothAverage (H : Subgroup K) [CompactSpace H]
    (hH : TauCeti.HasUnitProOrder A H) :
    smoothAverage (σ.comp H.subtype) hH ∘ₗ σ.smoothAverage hK = σ.smoothAverage hK :=
  LinearMap.ext (σ.smoothAverage_subgroup_smoothAverage hK H hH)

end Compact

/-- For a finite group of order invertible in `A`, the averaging projector of a smooth
representation is Mathlib's `Representation.averageMap`. The topology on the group need not be
discrete. -/
theorem smoothAverage_eq_averageMap [Fintype K] [TopologicalSpace K] [SeparatelyContinuousMul K]
    [Invertible (Fintype.card K : A)] (σ : Representation A K V) [IsSmooth σ]
    (hK : TauCeti.HasUnitProOrder A K) : σ.smoothAverage hK = σ.averageMap := by
  ext v
  have hu : IsUnit ((⊥ : Subgroup K).index : A) := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card]
    exact isUnit_of_invertible _
  have hbot : ∀ h : (⊥ : Subgroup K), σ h v = v := fun h ↦ by
    rw [Subgroup.mem_bot.1 h.property, map_one, one_apply_eq_self]
  rw [σ.smoothAverage_apply_eq_relNorm hK (IsSmooth.isOpen_stabilizer v) le_rfl,
    ← inverse_index_smul_relNorm_apply_of_le σ bot_le hu fun h ↦ mem_stabilizer.1 h.property,
    averageMap_apply, Subgroup.index_bot, Nat.card_eq_fintype_card, Ring.inverse_invertible,
    relNorm_apply]
  congr 1
  -- The cosets of `⊥` are the elements of `K`.
  exact (Fintype.sum_equiv QuotientGroup.quotientBot.symm.toEquiv _ _ fun g ↦
    σ.apply_eq_apply_of_quotientGroup_mk_eq hbot (QuotientGroup.out_eq' _).symm).symm

end Representation
