/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Signature

import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality

import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RingTheory.Ideal.Operations

/-!
# Kneser neighbors from isotropic vectors

Let `L` be an integral lattice, `p` a positive integer and `v ∈ L` a vector whose norm is
divisible by `p²`. Keep the vectors of `L` whose pairing with `v` is divisible by `p`, and adjoin
`v / p`. The result `L.neighbor p v` is again an integral lattice on the same rational quadratic
space. When some lattice vector pairs with `v` coprimely to `p`, the kept vectors are exactly
`L ∩ L.neighbor p v` and have index `p` in both lattices, so `L.neighbor p v` is a Kneser
`p`-neighbor of `L`. It is even when `L` is even and the norm of `v` is divisible by `2p²`.

A vector which is only isotropic modulo an odd `p` can be corrected: if `w ∈ L` pairs with `v`
coprimely to `p`, then adding a suitable multiple of `p w` to `v` makes the norm divisible by
`p²` without changing the kept vectors. So every vector of `L` that is isotropic modulo an odd `p`
and pairs coprimely to `p` with some lattice vector produces a `p`-neighbor of `L`.

## Main definitions

* `TauCeti.IntegralLattice.neighborKernel`: the vectors of `L` whose pairing with `v` lies in
  `pℤ`.
* `TauCeti.IntegralLattice.neighbor`: the lattice spanned by `neighborKernel` and `v / p`.

## Main results

* `TauCeti.IntegralLattice.isNeighbor_neighbor`: `L.neighbor p v` is a `p`-neighbor of `L` when
  `p²` divides the norm of `v` and some `w ∈ L` pairs with `v` coprimely to `p`.
* `TauCeti.IntegralLattice.isEven_neighbor`: the neighbor of an even lattice is even when the
  norm of `v` is divisible by `2p²`.
* `TauCeti.IntegralLattice.exists_dvd_integralNorm_add_smul`: for odd `p`, a vector isotropic
  modulo `p` and pairing coprimely to `p` with some `w ∈ L` lifts to one isotropic modulo `p²`.
* `TauCeti.IntegralLattice.exists_isNeighbor_of_dvd_integralNorm`: for odd `p`, a vector isotropic
  modulo `p` and pairing coprimely to `p` with some `w ∈ L` gives a `p`-neighbor meeting `L` in
  `neighborKernel`.
* `TauCeti.IntegralLattice.exists_isNeighbor_of_not_dvd_discriminant`: for an odd prime `p ∤ det L`,
  every `v ∈ L ∖ p L` isotropic modulo `p` gives a `p`-neighbor.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* J. Voight, *Kneser's method of neighbors*, arXiv:2308.11566, §3.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) (p : ℕ)

/-- Pairing with `v`, reduced modulo `p`, as an additive character of the lattice. -/
noncomputable def neighborCharacter (v : L) : L →ₗ[ℤ] ZMod p :=
  (Int.castAddHom (ZMod p)).toIntLinearMap.comp (L.integralForm v)

/-- The neighbor character is the pairing with `v` modulo `p`. -/
@[simp]
theorem neighborCharacter_apply (v x : L) :
    L.neighborCharacter p v x = (L.integralForm v x : ZMod p) :=
  (rfl)

/-- The vectors of `L` whose pairing with `v` is divisible by `p`, as a submodule of the ambient
space. -/
noncomputable def neighborKernel (v : L) : Submodule ℤ V :=
  (LinearMap.ker (L.neighborCharacter p v)).map L.carrier.subtype

/-- A lattice vector lies in the neighbor kernel exactly when `p` divides its pairing with `v`. -/
@[simp]
theorem coe_mem_neighborKernel_iff (v x : L) :
    (x : V) ∈ L.neighborKernel p v ↔ (p : ℤ) ∣ L.integralForm v x := by
  rw [neighborKernel, Submodule.mem_map]
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The neighbor kernel is contained in the original carrier. -/
theorem neighborKernel_le (v : L) : L.neighborKernel p v ≤ L.carrier := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- **Membership in the neighbor kernel**: its vectors are the lattice vectors whose pairing with
`v` is divisible by `p`. -/
theorem mem_neighborKernel_iff (v : L) (x : V) :
    x ∈ L.neighborKernel p v ↔ ∃ y : L, (y : V) = x ∧ (p : ℤ) ∣ L.integralForm v y := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact ⟨y, rfl, (L.coe_mem_neighborKernel_iff p v y).mp (Submodule.mem_map_of_mem hy)⟩
  · rintro ⟨y, rfl, hy⟩
    exact (L.coe_mem_neighborKernel_iff p v y).mpr hy

/-- Pairing with `v + p t w` differs from pairing with `v` by a multiple of `p`. -/
private theorem integralForm_add_smul_apply (v w y : L) (t : ℤ) :
    L.integralForm (v + ((p : ℤ) * t) • w) y =
      L.integralForm v y + p * (t * L.integralForm w y) := by
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_assoc]

/-- The kernels of two vectors agree when the vectors agree modulo `p L`. -/
theorem neighborKernel_add_smul (v w : L) (t : ℤ) :
    L.neighborKernel p (v + ((p : ℤ) * t) • w) = L.neighborKernel p v := by
  ext x
  simp only [mem_neighborKernel_iff, integralForm_add_smul_apply,
    dvd_add_left (dvd_mul_right _ _)]

/-- The neighbor kernel contains `p L`. -/
theorem smul_mem_neighborKernel (v x : L) : (p : ℤ) • (x : V) ∈ L.neighborKernel p v := by
  have h := (L.coe_mem_neighborKernel_iff p v ((p : ℤ) • x)).mpr
    (by rw [map_smul, smul_eq_mul]; exact dvd_mul_right _ _)
  rwa [Submodule.coe_smul] at h

/-- `v` lies in its own neighbor kernel when `p` divides its norm. -/
theorem coe_mem_neighborKernel_self {v : L} (hv : (p : ℤ) ∣ L.integralNorm v) :
    (v : V) ∈ L.neighborKernel p v := by
  rwa [coe_mem_neighborKernel_iff, ← integralNorm_apply]

/-- An integer coprime to `p` among the pairings with `v` makes the neighbor character onto. -/
theorem neighborCharacter_surjective {v w : L} (hvw : IsCoprime (L.integralForm v w) p) :
    Function.Surjective (L.neighborCharacter p v) := by
  obtain ⟨a, b, hab⟩ := hvw
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨(k * a) • w, ?_⟩
  have h : ((L.integralForm v w * a + b * p : ℤ) : ZMod p) = 1 := by
    rw [mul_comm (L.integralForm v w), hab, Int.cast_one]
  push_cast at h
  rw [ZMod.natCast_self, mul_zero, add_zero] at h
  rw [neighborCharacter_apply, map_smul, smul_eq_mul, Int.cast_mul, Int.cast_mul, mul_assoc,
    mul_comm (a : ZMod p), h, mul_one]

/-- The neighbor kernel has index `p` in `L` when some lattice vector pairs with `v` coprimely
to `p`. -/
theorem relIndex_neighborKernel {v w : L} (hvw : IsCoprime (L.integralForm v w) p) :
    (L.neighborKernel p v).toAddSubgroup.relIndex L.carrier.toAddSubgroup = p := by
  have htop : (⊤ : AddSubgroup L).map L.carrier.subtype.toAddMonoidHom =
      L.carrier.toAddSubgroup :=
    (AddSubgroup.map_top _).trans (AddSubgroup.range_subtype L.carrier.toAddSubgroup)
  rw [neighborKernel, Submodule.map_toAddSubgroup, ← htop, LinearMap.ker_toAddSubgroup]
  -- The coerced linear inclusion and its additive-hom projection are the same subtype map.
  change ((L.neighborCharacter p v).toAddMonoidHom.ker.map
    L.carrier.subtype.toAddMonoidHom).relIndex
      ((⊤ : AddSubgroup L).map L.carrier.subtype.toAddMonoidHom) = p
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ L.carrier.injective_subtype,
    AddSubgroup.relIndex_top_right, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (L.neighborCharacter_surjective p hvw)]
  simp

/-- The neighbor kernel is a full lattice in the ambient space, since it contains `p L`. -/
instance isLattice_neighborKernel [NeZero p] (v : L) :
    (L.neighborKernel p v).IsLattice ℚ where
  fg := by
    rw [neighborKernel]
    exact (IsNoetherian.noetherian _).map _
  span_eq_top := by
    apply top_unique
    rw [← L.isLattice.span_eq_top, Submodule.span_le]
    intro x hx
    have h := (Submodule.span ℚ (L.neighborKernel p v : Set V)).smul_mem (p : ℚ)⁻¹
      (Submodule.subset_span (L.smul_mem_neighborKernel p v ⟨x, hx⟩))
    rwa [smul_comm, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_inv_smul₀ (Nat.cast_ne_zero.mpr (NeZero.ne p))] at h

private theorem isLattice_neighborCarrier [NeZero p] (v : L) :
    (L.neighborKernel p v ⊔ ℤ ∙ ((p : ℚ)⁻¹ • (v : V))).IsLattice ℚ :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ le_sup_left
    (Submodule.IsLattice.fg.sup (Submodule.fg_span_singleton _))

attribute [local instance] isLattice_neighborCarrier

variable {L p}

/-- The vector `v / p` pairs integrally with the neighbor kernel. -/
private theorem exists_form_inv_smul_eq [NeZero p] {v : L} {x : V}
    (hx : x ∈ L.neighborKernel p v) : ∃ k : ℤ, L.form ((p : ℚ)⁻¹ • (v : V)) x = k := by
  obtain ⟨y, rfl, k, hk⟩ := (L.mem_neighborKernel_iff p v x).mp hx
  refine ⟨k, ?_⟩
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← L.integralForm_cast, hk]
  push_cast
  field_simp

/-- The vector `v / p` has integral norm when `p²` divides the norm of `v`. -/
private theorem exists_form_inv_smul_self_eq [NeZero p] {v : L}
    (hv : (p : ℤ) ^ 2 ∣ L.integralNorm v) :
    ∃ k : ℤ, L.form ((p : ℚ)⁻¹ • (v : V)) ((p : ℚ)⁻¹ • (v : V)) = k := by
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← L.integralForm_cast,
    ← integralNorm_apply, hk]
  push_cast
  field_simp

/-- Pairings of vectors of `neighborKernel ⊔ ℤ (v / p)` are integral. -/
private theorem neighborCarrier_le_dualSubmodule [NeZero p] {v : L}
    (hv : (p : ℤ) ^ 2 ∣ L.integralNorm v) :
    L.neighborKernel p v ⊔ ℤ ∙ ((p : ℚ)⁻¹ • (v : V)) ≤
      L.form.dualSubmodule (L.neighborKernel p v ⊔ ℤ ∙ ((p : ℚ)⁻¹ • (v : V))) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  obtain ⟨a, ha, _, hm, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hm
  obtain ⟨b, hb, _, hn, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hn
  obtain ⟨k₁, hk₁⟩ := exists_form_inv_smul_eq ha
  obtain ⟨k₂, hk₂⟩ := exists_form_inv_smul_eq hb
  obtain ⟨k₃, hk₃⟩ := exists_form_inv_smul_self_eq hv
  have hab := L.le_dual (L.neighborKernel_le p v ha) b (L.neighborKernel_le p v hb)
  obtain ⟨k₀, hk₀⟩ := Submodule.mem_one.mp hab
  rw [eq_intCast] at hk₀
  refine Submodule.mem_one.mpr ⟨k₀ + n * k₁ + m * k₂ + m * n * k₃, ?_⟩
  rw [eq_intCast]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, zsmul_eq_mul]
  rw [L.isSymm.eq a ((p : ℚ)⁻¹ • (v : V)), ← hk₀, hk₁, hk₂, hk₃]
  push_cast
  ring

/-- **The neighbor of `L` along `v`.** For `p ≠ 0` and `p²` dividing the norm of `v`, the lattice
spanned by the vectors of `L` whose pairing with `v` is divisible by `p`, together with `v / p`,
with the form of `L`. It is a `p`-neighbor of `L` when some lattice vector pairs with `v`
coprimely to `p`, by `isNeighbor_neighbor`. -/
noncomputable def neighbor (p : ℕ) [NeZero p] (v : L) (hv : (p : ℤ) ^ 2 ∣ L.integralNorm v) :
    IntegralLattice V :=
  ofSubmodule (L.neighborKernel p v ⊔ ℤ ∙ ((p : ℚ)⁻¹ • (v : V))) L.form L.isSymm
    (neighborCarrier_le_dualSubmodule hv)

variable [NeZero p] {v : L} (hv : (p : ℤ) ^ 2 ∣ L.integralNorm v)
include hv

/-- The carrier of the neighbor is spanned by the neighbor kernel and `v / p`. -/
theorem neighbor_carrier :
    (L.neighbor p v hv).carrier = L.neighborKernel p v ⊔ ℤ ∙ ((p : ℚ)⁻¹ • (v : V)) :=
  ofSubmodule_carrier ..

/-- The neighbor carries the form of `L`. -/
@[simp]
theorem neighbor_form : (L.neighbor p v hv).form = L.form :=
  ofSubmodule_form ..

/-- **Membership in the neighbor**: it consists of the vectors of the neighbor kernel plus
integer multiples of `v / p`. -/
theorem mem_neighbor_carrier_iff (x : V) :
    x ∈ (L.neighbor p v hv).carrier ↔
      ∃ y ∈ L.neighborKernel p v, ∃ n : ℤ, y + n • ((p : ℚ)⁻¹ • (v : V)) = x := by
  simp only [neighbor_carrier, Submodule.mem_sup, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, hy, _, ⟨n, rfl⟩, rfl⟩
    exact ⟨y, hy, n, rfl⟩
  · rintro ⟨y, hy, n, rfl⟩
    exact ⟨y, hy, _, ⟨n, rfl⟩, rfl⟩

/-- The neighbor kernel is contained in the neighbor. -/
theorem neighborKernel_le_neighbor_carrier :
    L.neighborKernel p v ≤ (L.neighbor p v hv).carrier := by
  rw [neighbor_carrier]
  exact le_sup_left

/-- The vector `v / p` belongs to the neighbor. -/
theorem inv_smul_mem_neighbor_carrier : (p : ℚ)⁻¹ • (v : V) ∈ (L.neighbor p v hv).carrier := by
  rw [neighbor_carrier]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- The neighbor of a nondegenerate lattice is nondegenerate. -/
instance instIsNondegenerateNeighbor [L.IsNondegenerate] : (L.neighbor p v hv).IsNondegenerate :=
  ⟨by rw [neighbor_form]; exact L.form_nondegenerate⟩

/-- The neighbor is positive definite exactly when `L` is. -/
theorem isPosDef_neighbor_iff : (L.neighbor p v hv).IsPosDef ↔ L.IsPosDef := by
  simp only [IsPosDef, neighbor_form]

/-- **Neighbors of even lattices are even** when the norm of `v` is divisible by `2p²`. -/
theorem isEven_neighbor (hL : L.IsEven) (hv₂ : 2 * (p : ℤ) ^ 2 ∣ L.integralNorm v) :
    (L.neighbor p v hv).IsEven := by
  rw [isEven_iff_forall_norm]
  intro x
  obtain ⟨y, hy, n, hx⟩ := (L.mem_neighbor_carrier_iff hv x).mp x.2
  obtain ⟨a, ha⟩ := hL.exists_norm_eq_two_mul ⟨y, L.neighborKernel_le p v hy⟩
  obtain ⟨c, hc⟩ := exists_form_inv_smul_eq hy
  obtain ⟨b, hb⟩ := hv₂
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hu : L.norm ((p : ℚ)⁻¹ • (v : V)) = 2 * b := by
    rw [norm_smul, ← integralNorm_cast, hb]
    push_cast
    field_simp
  have ha' : L.norm y = 2 * a := ha
  refine ⟨a + n * c + n ^ 2 * b, ?_⟩
  rw [norm_apply, neighbor_form, ← norm_apply, ← hx, ← Int.cast_smul_eq_zsmul ℚ, L.norm_add,
    L.norm_smul, hu, L.isSymm.eq y, map_smul, LinearMap.smul_apply, smul_eq_mul, hc, ha']
  push_cast
  ring

omit hv in
/-- A multiple of `v / p` lies in `L` exactly when `p` divides the multiplier, as soon as some
lattice vector pairs with `v` coprimely to `p`. -/
theorem zsmul_inv_smul_mem_carrier_iff {w : L} (hvw : IsCoprime (L.integralForm v w) p)
    (k : ℤ) : k • ((p : ℚ)⁻¹ • (v : V)) ∈ L.carrier ↔ (p : ℤ) ∣ k := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  constructor
  · intro hk
    have hcast := L.integralForm_cast ⟨_, hk⟩ w
    rw [map_zsmul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      zsmul_eq_mul, ← L.integralForm_cast] at hcast
    have hdvd : (p : ℤ) ∣ k * L.integralForm v w := by
      refine ⟨L.integralForm ⟨_, hk⟩ w, ?_⟩
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hcast]
      field_simp
    exact hvw.symm.dvd_of_dvd_mul_right hdvd
  · rintro ⟨m, rfl⟩
    rw [mul_comm, mul_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_inv_smul₀ hp]
    exact L.carrier.smul_mem m v.2

/-- The multiples of `p (v / p)` lie in the neighbor kernel. -/
private theorem zsmul_inv_smul_mem_neighborKernel (m : ℤ) :
    ((p : ℤ) * m) • ((p : ℚ)⁻¹ • (v : V)) ∈ L.neighborKernel p v := by
  rw [mul_comm, mul_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_inv_smul₀ (Nat.cast_ne_zero.mpr (NeZero.ne p))]
  exact Submodule.smul_mem _ m
    (L.coe_mem_neighborKernel_self p (dvd_trans (dvd_pow_self _ two_ne_zero) hv))

/-- With a pairing coprime to `p`, the neighbor meets `L` exactly in the neighbor kernel. -/
theorem carrier_inf_neighbor_carrier {w : L} (hvw : IsCoprime (L.integralForm v w) p) :
    L.carrier ⊓ (L.neighbor p v hv).carrier = L.neighborKernel p v := by
  refine le_antisymm ?_ (le_inf (L.neighborKernel_le p v) (L.neighborKernel_le_neighbor_carrier hv))
  rintro x ⟨hxL, hxM⟩
  obtain ⟨y, hy, n, rfl⟩ := (L.mem_neighbor_carrier_iff hv x).mp hxM
  have hn : n • ((p : ℚ)⁻¹ • (v : V)) ∈ L.carrier := by
    simpa using L.carrier.sub_mem hxL (L.neighborKernel_le p v hy)
  obtain ⟨m, rfl⟩ := (zsmul_inv_smul_mem_carrier_iff hvw n).mp hn
  exact add_mem hy (L.zsmul_inv_smul_mem_neighborKernel hv m)

/-- With a pairing coprime to `p`, the neighbor kernel has index `p` in the neighbor. -/
theorem relIndex_neighborKernel_neighbor {w : L} (hvw : IsCoprime (L.integralForm v w) p) :
    (L.neighborKernel p v).toAddSubgroup.relIndex (L.neighbor p v hv).carrier.toAddSubgroup =
      p := by
  set u : V := (p : ℚ)⁻¹ • (v : V)
  set H := (L.neighborKernel p v).toAddSubgroup
  have hsup : (L.neighbor p v hv).carrier.toAddSubgroup = H ⊔ AddSubgroup.zmultiples u := by
    rw [neighbor_carrier, Submodule.sup_toAddSubgroup,
      Submodule.span_singleton_toAddSubgroup_eq_zmultiples]
  -- The multiples of `u` landing in the kernel are exactly the multiples of `p`.
  have hmem (k : ℤ) : k • u ∈ H ↔ (p : ℤ) ∣ k := by
    refine ⟨fun hk ↦ (zsmul_inv_smul_mem_carrier_iff hvw k).mp (L.neighborKernel_le p v hk), ?_⟩
    rintro ⟨m, rfl⟩
    rw [Submodule.mem_toAddSubgroup]
    exact L.zsmul_inv_smul_mem_neighborKernel hv m
  -- The index of `H` in `H + ℤ u` is that of the multipliers of `u` landing in `H`.
  have hcomap : H.comap (zmultiplesHom V u) = AddSubgroup.zmultiples (p : ℤ) := by
    ext k
    rw [AddSubgroup.mem_comap, zmultiplesHom_apply, hmem, Int.mem_zmultiples_iff]
  rw [hsup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.range_zmultiplesHom,
    ← AddSubgroup.index_comap, hcomap, Int.index_zmultiples, Int.natAbs_natCast]

/-- **The neighbor is a Kneser neighbor.** If `p²` divides the norm of `v` and some lattice
vector pairs with `v` coprimely to `p`, then `L.neighbor p v` is a `p`-neighbor of `L`. -/
theorem isNeighbor_neighbor {w : L} (hvw : IsCoprime (L.integralForm v w) p) :
    L.IsNeighbor (L.neighbor p v hv) p where
  form_eq := (L.neighbor_form hv).symm
  relIndex_inf_left := by
    rw [L.carrier_inf_neighbor_carrier hv hvw]
    exact L.relIndex_neighborKernel p hvw
  relIndex_inf_right := by
    rw [L.carrier_inf_neighbor_carrier hv hvw]
    exact L.relIndex_neighborKernel_neighbor hv hvw

omit [NeZero p] hv in
/-- **Lifting isotropic vectors from `p` to `p²`.** For odd `p`, if `p` divides the norm of `v`
and `w` pairs with `v` coprimely to `p`, then some `v + p t w` has norm divisible by `p²`. -/
theorem exists_dvd_integralNorm_add_smul (hp : Odd p) {v w : L}
    (hv : (p : ℤ) ∣ L.integralNorm v) (hvw : IsCoprime (L.integralForm v w) p) :
    ∃ t : ℤ, (p : ℤ) ^ 2 ∣ L.integralNorm (v + ((p : ℤ) * t) • w) := by
  obtain ⟨a, ha⟩ := hv
  have h2 : IsCoprime (2 * L.integralForm v w) p :=
    (Odd.isCoprime_two (by exact_mod_cast hp.natCast)).symm.mul_left hvw
  obtain ⟨s, r, hsr⟩ := h2
  refine ⟨-(a * s), a * r + (a * s) ^ 2 * L.integralNorm w, ?_⟩
  rw [integralNorm_add, integralNorm_zsmul, map_smul, smul_eq_mul, ha]
  linear_combination -((p : ℤ) * a) * hsr

omit [NeZero p] hv in
/-- **Kneser neighbors from isotropic vectors.** For odd `p`, if `p` divides the norm of `v` and
some lattice vector `w` pairs with `v` coprimely to `p`, then `L` has a `p`-neighbor `M` meeting
`L` in the vectors whose pairing with `v` is divisible by `p`. If `L` is even, so is `M`. -/
theorem exists_isNeighbor_of_dvd_integralNorm (hp : Odd p) {v w : L}
    (hv : (p : ℤ) ∣ L.integralNorm v) (hvw : IsCoprime (L.integralForm v w) p) :
    ∃ M : IntegralLattice V, L.IsNeighbor M p ∧ L.carrier ⊓ M.carrier = L.neighborKernel p v ∧
      (L.IsEven → M.IsEven) := by
  have : NeZero p := ⟨by rintro rfl; exact (Nat.not_odd_zero hp)⟩
  obtain ⟨t, ht⟩ := L.exists_dvd_integralNorm_add_smul hp hv hvw
  set v' := v + ((p : ℤ) * t) • w
  have hvw' : IsCoprime (L.integralForm v' w) p := by
    rw [integralForm_add_smul_apply]
    exact hvw.add_mul_left_left _
  refine ⟨L.neighbor p v' ht, L.isNeighbor_neighbor ht hvw', ?_, fun hL ↦ ?_⟩
  · rw [L.carrier_inf_neighbor_carrier ht hvw', neighborKernel_add_smul]
  · refine L.isEven_neighbor ht hL ?_
    have h2 : (2 : ℤ) ∣ L.integralNorm v' := even_iff_two_dvd.mp
      ((L.even_integralNorm_iff v').mpr (hL.exists_norm_eq_two_mul v'))
    exact (Odd.isCoprime_two (by exact_mod_cast hp.natCast.pow)).symm.mul_dvd h2 ht

omit [NeZero p] hv in
/-- **Kneser neighbors at a prime not dividing the discriminant.** Let `p` be an odd prime not
dividing the discriminant of a nondegenerate lattice `L`, and let `v ∈ L ∖ p L` be isotropic
modulo `p`. Then `L` has a `p`-neighbor `M` meeting `L` in the vectors whose pairing with `v` is
divisible by `p`. If `L` is even, so is `M`. -/
theorem exists_isNeighbor_of_not_dvd_discriminant [L.IsNondegenerate] (hp : p.Prime) (hp₂ : p ≠ 2)
    (hdisc : ¬p ∣ L.discriminant) {v : L} (hv : (p : ℤ) ∣ L.integralNorm v)
    (hv₀ : (p : ℚ)⁻¹ • (v : V) ∉ L.carrier) :
    ∃ M : IntegralLattice V, L.IsNeighbor M p ∧ L.carrier ⊓ M.carrier = L.neighborKernel p v ∧
      (L.IsEven → M.IsEven) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨w, hw⟩ : ∃ w : L, ¬(p : ℤ) ∣ L.integralForm v w := by
    by_contra! h
    exact hv₀
      (L.inv_smul_mem_carrier_of_forall_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdisc) h)
  exact exists_isNeighbor_of_dvd_integralNorm (hp.odd_of_ne_two hp₂) hv
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hw).symm

end TauCeti.IntegralLattice
