/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction

import Mathlib.Tactic.FinCases

/-!
# Even two-neighbors

For an even lattice `L` and a lattice vector `v` of norm divisible by eight, first keep the
vectors pairing evenly with `v`, then glue in `v / 2`. The construction uses the existing
quadratic-isotropic discriminant-subgroup gluing operation. When `L` is unimodular and some
lattice vector pairs oddly with `v`, the result is an even unimodular two-neighbor.

The carrier is the union of the even-pairing kernel and its half-vector translate. An odd
pairing makes this kernel the intersection with the original lattice, of index two in each.

## References

* G. Nebe, [*Extremal lattices*](https://www.math.rwth-aachen.de/homes/Gabriele.Nebe/talks/OW12.pdf),
  slide 11, for the two-neighbor construction of the Leech lattice.
* R. E. Borcherds, [*The Leech lattice and other lattices*](https://math.berkeley.edu/~reb/papers/thesis/thesis.pdf),
  §0.2, for the even-pairing kernel and its discriminant glue.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- Pairing with `v`, reduced modulo two, as an additive character of the lattice. -/
noncomputable def twoNeighborCharacter (v : L) : L →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp (L.integralForm v)

/-- The two-neighbor character is the parity of the integral pairing. -/
@[simp]
theorem twoNeighborCharacter_apply (v x : L) :
    L.twoNeighborCharacter v x = (L.integralForm v x : ZMod 2) := by
  rw [twoNeighborCharacter]
  rfl

/-- The full sublattice of ambient vectors in `L` pairing evenly with `v`. -/
noncomputable def twoNeighborKernel (v : L) : Submodule ℤ V :=
  (LinearMap.ker (L.twoNeighborCharacter v)).map L.carrier.subtype

/-- A lattice vector lies in the neighbor kernel exactly when its pairing with `v` is even. -/
@[simp]
theorem coe_mem_twoNeighborKernel_iff (v x : L) :
    (x : V) ∈ L.twoNeighborKernel v ↔ Even (L.integralForm v x) := by
  rw [twoNeighborKernel, Submodule.mem_map]
  -- The mapped-kernel witness is in the carrier subtype, whose inclusion is its coercion.
  change (∃ y : L, L.twoNeighborCharacter v y = 0 ∧ (y : V) = (x : V)) ↔ _
  simp only [Subtype.coe_inj, exists_eq_right, twoNeighborCharacter_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat, even_iff_two_dvd]

/-- The neighbor kernel is contained in the original carrier. -/
theorem twoNeighborKernel_le (v : L) : L.twoNeighborKernel v ≤ L.carrier := by
  intro x hx
  rw [twoNeighborKernel, Submodule.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

private theorem isLattice_twoNeighborKernel (v : L) :
    (L.twoNeighborKernel v).IsLattice ℚ where
  fg := by
    rw [twoNeighborKernel]
    exact (IsNoetherian.noetherian _).map _
  span_eq_top := by
    apply top_unique
    rw [← L.isLattice.span_eq_top, Submodule.span_le]
    intro x hx
    have hx2 : (2 : ℚ) • x ∈ L.twoNeighborKernel v := by
      have h := (L.coe_mem_twoNeighborKernel_iff v ((2 : ℤ) • (⟨x, hx⟩ : L))).mpr
        (by rw [map_smul]; exact even_two_mul _)
      simpa only [Submodule.coe_smul, two_smul, Submodule.coe_add] using h
    have h := (Submodule.span ℚ (L.twoNeighborKernel v : Set V)).smul_mem (1 / 2 : ℚ)
      (Submodule.subset_span hx2)
    have hcancel : (1 / 2 : ℚ) * 2 = 1 := by norm_num
    simpa only [SetLike.mem_coe, smul_smul, hcancel, one_smul] using h

attribute [local instance] isLattice_twoNeighborKernel

/-- The even-pairing kernel, with the original ambient rational form. -/
noncomputable def twoNeighborKernelLattice (v : L) : IntegralLattice V :=
  L.restrictFull (L.twoNeighborKernel v) (L.twoNeighborKernel_le v)

/-- The kernel lattice has the even-pairing carrier. -/
@[simp]
theorem twoNeighborKernelLattice_carrier (v : L) :
    (L.twoNeighborKernelLattice v).carrier = L.twoNeighborKernel v := by
  unfold twoNeighborKernelLattice
  exact restrictFull_carrier ..

/-- Passing to the neighbor kernel keeps the ambient form. -/
@[simp]
theorem twoNeighborKernelLattice_form (v : L) : (L.twoNeighborKernelLattice v).form = L.form := by
  unfold twoNeighborKernelLattice
  exact restrictFull_form ..

/-- The neighbor kernel of a nondegenerate lattice is nondegenerate. -/
instance instIsNondegenerateTwoNeighborKernelLattice [L.IsNondegenerate] (v : L) :
    (L.twoNeighborKernelLattice v).IsNondegenerate := by
  unfold twoNeighborKernelLattice
  infer_instance

/-- The even-pairing kernel of an even lattice is even. -/
theorem IsEven.twoNeighborKernelLattice {L : IntegralLattice V} (hL : L.IsEven) (v : L) :
    (L.twoNeighborKernelLattice v).IsEven := by
  unfold IntegralLattice.twoNeighborKernelLattice
  exact isEven_restrictFull hL _ _

/-- The even-pairing kernel is positive definite exactly when the original lattice is. -/
theorem isPosDef_twoNeighborKernelLattice_iff (v : L) :
    (L.twoNeighborKernelLattice v).IsPosDef ↔ L.IsPosDef := by
  simp only [IsPosDef, twoNeighborKernelLattice_form]

private theorem half_mem_twoNeighborKernelLattice_dualCarrier (v : L) :
    (1 / 2 : ℚ) • (v : V) ∈ (L.twoNeighborKernelLattice v).dualCarrier := by
  rw [dualCarrier, twoNeighborKernelLattice_form, twoNeighborKernelLattice_carrier,
    LinearMap.BilinForm.mem_dualSubmodule]
  intro x hx
  let y : L := ⟨x, L.twoNeighborKernel_le v hx⟩
  have heven := (L.coe_mem_twoNeighborKernel_iff v y).mp hx
  obtain ⟨n, hn⟩ := even_iff_two_dvd.mp heven
  refine Submodule.mem_one.mpr ⟨n, ?_⟩
  have hform := L.integralForm_cast v y
  rw [hn] at hform
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  push_cast at hform
  simp only [eq_intCast]
  linarith

/-- The vector `v / 2`, as an element of the dual of the even-pairing kernel. -/
noncomputable def twoNeighborGlueVector (v : L) : (L.twoNeighborKernelLattice v).dualCarrier :=
  ⟨(1 / 2 : ℚ) • (v : V), half_mem_twoNeighborKernelLattice_dualCarrier L v⟩

/-- The explicit rational representative of the neighbor glue. -/
@[simp]
theorem coe_twoNeighborGlueVector (v : L) :
    (L.twoNeighborGlueVector v : V) = (1 / 2 : ℚ) • (v : V) := by
  rw [twoNeighborGlueVector]

/-- An odd pairing makes the parity character onto `ℤ/2`. -/
theorem twoNeighborCharacter_surjective (v : L)
    (hv : ∃ w : L, Odd (L.integralForm v w)) : Function.Surjective (L.twoNeighborCharacter v) := by
  obtain ⟨w, hw⟩ := hv
  intro z
  fin_cases z
  · exact ⟨0, map_zero _⟩
  · exact ⟨w, (L.twoNeighborCharacter_apply v w).trans hw.intCast_zmod_two⟩

/-- The even-pairing kernel has index two when `v` has an odd pairing with some lattice vector. -/
theorem relIndex_twoNeighborKernel (v : L) (hv : ∃ w : L, Odd (L.integralForm v w)) :
    (L.twoNeighborKernel v).toAddSubgroup.relIndex L.carrier.toAddSubgroup = 2 := by
  have htop : (⊤ : AddSubgroup L).map L.carrier.subtype.toAddMonoidHom =
      L.carrier.toAddSubgroup :=
    (AddSubgroup.map_top _).trans (AddSubgroup.range_subtype L.carrier.toAddSubgroup)
  rw [twoNeighborKernel, Submodule.map_toAddSubgroup, ← htop,
    LinearMap.ker_toAddSubgroup]
  -- The coerced linear inclusion and its additive-hom projection are the same subtype map.
  change ((L.twoNeighborCharacter v).toAddMonoidHom.ker.map
    L.carrier.subtype.toAddMonoidHom).relIndex
      ((⊤ : AddSubgroup L).map L.carrier.subtype.toAddMonoidHom) = 2
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ L.carrier.injective_subtype,
    AddSubgroup.relIndex_top_right, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (L.twoNeighborCharacter_surjective v hv)]
  simp

/-- An odd pairing with `v` prevents its half from belonging to the original lattice. -/
theorem half_not_mem_carrier (v : L) (hv : ∃ w : L, Odd (L.integralForm v w)) :
    (1 / 2 : ℚ) • (v : V) ∉ L.carrier := by
  intro hx
  obtain ⟨w, hw⟩ := hv
  let t : L := ⟨(1 / 2 : ℚ) • (v : V), hx⟩
  have ht := L.integralForm_cast t w
  -- Expand only the bundled half-vector's coercion before applying the public scalar law.
  change (L.integralForm t w : ℚ) = L.form ((1 / 2 : ℚ) • (v : V)) w at ht
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at ht
  have hform := L.integralForm_cast v w
  have heq : L.integralForm v w = 2 * L.integralForm t w := by
    have hq : (L.integralForm v w : ℚ) = 2 * (L.integralForm t w : ℚ) := by linarith
    exact_mod_cast hq
  apply (Int.not_even_iff_odd.mpr hw)
  rw [heq]
  exact even_two_mul _

variable [L.IsNondegenerate]

/-- The discriminant class of `v / 2` in the even-pairing kernel. -/
noncomputable def twoNeighborGlueClass (v : L) : (L.twoNeighborKernelLattice v).DiscriminantGroup :=
  Submodule.Quotient.mk (L.twoNeighborGlueVector v)

/-- The cyclic discriminant subgroup generated by the neighbor glue. -/
noncomputable def twoNeighborGlueSubgroup (v : L) :
    AddSubgroup (L.twoNeighborKernelLattice v).DiscriminantGroup :=
  AddSubgroup.zmultiples (L.twoNeighborGlueClass v)

/-- Norm divisibility by eight makes the half-vector glue quadratically isotropic in the
half-norm convention of the discriminant module. -/
theorem isIsotropic_twoNeighborGlueSubgroup (hL : L.IsEven) (v : L)
    (hv : (8 : ℤ) ∣ L.integralNorm v) :
    ((L.twoNeighborKernelLattice v).discriminantQuadraticModule
      (hL.twoNeighborKernelLattice v)).IsIsotropic (L.twoNeighborGlueSubgroup v) := by
  have hq : ((L.twoNeighborKernelLattice v).discriminantQuadraticModule
      (hL.twoNeighborKernelLattice v)).quadratic (L.twoNeighborGlueClass v) = 0 := by
    rw [discriminantQuadraticModule_quadratic, twoNeighborGlueClass,
      discriminantQuadraticMap_mk_eq_zero_iff]
    obtain ⟨n, hn⟩ := hv
    refine ⟨n, ?_⟩
    have hnorm : L.form v v = ((8 * n : ℤ) : ℚ) := by
      rw [← norm_apply, ← integralNorm_cast, hn]
    rw [← norm_apply, coe_twoNeighborGlueVector, norm_smul, norm_apply,
      twoNeighborKernelLattice_form, hnorm]
    push_cast
    ring
  refine (FiniteQuadraticModule.isIsotropic_def _).mpr ?_
  intro x hx
  rw [twoNeighborGlueSubgroup] at hx
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  exact (QuadraticMap.map_smul _ n (L.twoNeighborGlueClass v)).trans
    ((congrArg (fun q : AddCircle (1 : ℚ) ↦ (n * n) • q) hq).trans (smul_zero _))

/-- The even lattice from the two-neighbor formula: glue the even-pairing kernel along the
class of `v / 2`. The index-two assertions require an odd pairing with the chosen vector. -/
noncomputable def twoNeighbor (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    IntegralLattice V :=
  (L.twoNeighborKernelLattice v).ofIsotropicSubgroup (hL.twoNeighborKernelLattice v)
    (L.twoNeighborGlueSubgroup v) (L.isIsotropic_twoNeighborGlueSubgroup hL v hv)

/-- The carrier of the neighbor is the actual inverse image of its cyclic discriminant glue. -/
theorem twoNeighbor_carrier (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    (L.twoNeighbor hL v hv).carrier =
      ((L.twoNeighborKernelLattice v).intermediateCarrierOfDiscriminantSubgroup
        (L.twoNeighborGlueSubgroup v)).1 := by
  rw [twoNeighbor, ofIsotropicSubgroup_carrier]

/-- The two-neighbor carries the original ambient form. -/
@[simp]
theorem twoNeighbor_form (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    (L.twoNeighbor hL v hv).form = L.form := by
  rw [twoNeighbor, ofIsotropicSubgroup_form, twoNeighborKernelLattice_form]

/-- The two-neighbor carries the original ambient norm form. -/
@[simp]
theorem twoNeighbor_norm (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) (x : V) :
    (L.twoNeighbor hL v hv).norm x = L.norm x := by
  rw [norm_apply, twoNeighbor_form, norm_apply]

/-- Gluing the half-vector gives an even lattice. -/
theorem isEven_twoNeighbor (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    (L.twoNeighbor hL v hv).IsEven := by
  rw [twoNeighbor]
  exact isEven_ofIsotropicSubgroup _ _ _ _

/-- A two-neighbor is nondegenerate when its original lattice is. -/
instance instIsNondegenerateTwoNeighbor (hL : L.IsEven) (v : L)
    (hv : (8 : ℤ) ∣ L.integralNorm v) : (L.twoNeighbor hL v hv).IsNondegenerate := by
  constructor
  rw [twoNeighbor_form]
  exact L.form_nondegenerate

/-- A two-neighbor is positive definite exactly when the original lattice is. -/
theorem isPosDef_twoNeighbor_iff (he : L.IsEven) (v : L)
    (hv : (8 : ℤ) ∣ L.integralNorm v) :
    (L.twoNeighbor he v hv).IsPosDef ↔ L.IsPosDef := by
  rw [twoNeighbor]
  exact ((L.twoNeighborKernelLattice v).isPosDef_ofIsotropicSubgroup_iff
    (he.twoNeighborKernelLattice v) (L.twoNeighborGlueSubgroup v)
    (L.isIsotropic_twoNeighborGlueSubgroup he v hv)).trans
      (L.isPosDef_twoNeighborKernelLattice_iff v)

/-- The rank is preserved because the two-neighbor is a full lattice in the same ambient space. -/
theorem finrank_twoNeighbor (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    Module.finrank ℤ (L.twoNeighbor hL v hv) = Module.finrank ℤ L := by
  rw [finrank_carrier, finrank_carrier]

/-- The parity kernel is contained in the glued neighbor carrier. -/
theorem twoNeighborKernel_le_carrier (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    L.twoNeighborKernel v ≤ (L.twoNeighbor hL v hv).carrier := by
  rw [twoNeighbor_carrier]
  simpa only [twoNeighborKernelLattice_carrier] using
    ((L.twoNeighborKernelLattice v).intermediateCarrierOfDiscriminantSubgroup
      (L.twoNeighborGlueSubgroup v)).2.1

/-- The half-vector actually belongs to the neighbor, rather than only to the kernel's dual. -/
theorem half_mem_twoNeighbor_carrier (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v) :
    (1 / 2 : ℚ) • (v : V) ∈ (L.twoNeighbor hL v hv).carrier := by
  rw [← coe_twoNeighborGlueVector L v, twoNeighbor_carrier,
    coe_mem_intermediateCarrierOfDiscriminantSubgroup_iff, twoNeighborGlueSubgroup]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by rw [one_smul, twoNeighborGlueClass]⟩

/-- **Membership in the two-neighbor**: it is the parity kernel plus the integer multiples
of the explicit half-vector. -/
theorem mem_twoNeighbor_carrier_iff (hL : L.IsEven) (v : L) (hv : (8 : ℤ) ∣ L.integralNorm v)
    (x : V) : x ∈ (L.twoNeighbor hL v hv).carrier ↔
      ∃ y ∈ L.twoNeighborKernel v, ∃ n : ℤ, y + n • ((1 / 2 : ℚ) • (v : V)) = x := by
  constructor
  · intro hx
    rw [twoNeighbor_carrier, mem_intermediateCarrierOfDiscriminantSubgroup_iff,
      twoNeighborGlueSubgroup] at hx
    obtain ⟨hxdual, n, hn⟩ := hx
    have heq : (Submodule.Quotient.mk (⟨x, hxdual⟩ : (L.twoNeighborKernelLattice v).dualCarrier) :
        (L.twoNeighborKernelLattice v).DiscriminantGroup) =
        Submodule.Quotient.mk (n • L.twoNeighborGlueVector v) := by
      rw [Submodule.Quotient.mk_smul]
      exact hn.symm
    have hy : x - n • ((1 / 2 : ℚ) • (v : V)) ∈ L.twoNeighborKernel v := by
      simpa only [Submodule.coe_sub, Submodule.coe_smul, coe_twoNeighborGlueVector,
        twoNeighborKernelLattice_carrier] using
        (discriminantGroup_mk_eq_iff _ _ _).mp heq
    exact ⟨_, hy, n, sub_add_cancel _ _⟩
  · rintro ⟨y, hy, n, rfl⟩
    exact Submodule.add_mem _ (L.twoNeighborKernel_le_carrier hL v hv hy)
      (Submodule.smul_mem _ n (L.half_mem_twoNeighbor_carrier hL v hv))

omit [L.IsNondegenerate] in
/-- For a unimodular original lattice, the even-pairing kernel has discriminant four. -/
theorem discriminant_twoNeighborKernelLattice (hL : L.IsUnimodular) (v : L)
    (hv : ∃ w : L, Odd (L.integralForm v w)) : (L.twoNeighborKernelLattice v).discriminant = 4 := by
  let : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have h := (L.twoNeighborKernelLattice v).discriminant_eq_mul_relIndex_sq L
    (L.twoNeighborKernelLattice_form v)
    (by rw [twoNeighborKernelLattice_carrier]; exact L.twoNeighborKernel_le v)
  rw [twoNeighborKernelLattice_carrier, L.relIndex_twoNeighborKernel v hv,
    L.isUnimodular_iff_discriminant_eq_one.mp hL] at h
  simpa using h

omit [L.IsNondegenerate] in
/-- The original vector lies in the even-pairing kernel when its norm is even. -/
theorem coe_mem_twoNeighborKernel_of_even_integralNorm (v : L) (hv : Even (L.integralNorm v)) :
    (v : V) ∈ L.twoNeighborKernel v := by
  rw [coe_mem_twoNeighborKernel_iff, ← integralNorm_apply]
  exact hv

omit [L.IsNondegenerate] in
/-- Twice the half-vector glue class vanishes in the kernel discriminant group. -/
theorem two_nsmul_twoNeighborGlueClass (v : L) (hv : Even (L.integralNorm v)) :
    (2 : ℕ) • L.twoNeighborGlueClass v = 0 := by
  rw [two_nsmul, twoNeighborGlueClass, ← Submodule.Quotient.mk_add,
    discriminantGroup_mk_eq_zero_iff, Submodule.coe_add, coe_twoNeighborGlueVector,
    twoNeighborKernelLattice_carrier, ← add_smul]
  norm_num
  simpa only [← integralNorm_apply] using hv

omit [L.IsNondegenerate] in
/-- An odd pairing makes the half-vector class nonzero in the kernel discriminant group. -/
theorem twoNeighborGlueClass_ne_zero (v : L) (hv : ∃ w : L, Odd (L.integralForm v w)) :
    L.twoNeighborGlueClass v ≠ 0 := by
  intro hz
  rw [twoNeighborGlueClass, discriminantGroup_mk_eq_zero_iff,
    coe_twoNeighborGlueVector, twoNeighborKernelLattice_carrier] at hz
  exact L.half_not_mem_carrier v hv (L.twoNeighborKernel_le v hz)

omit [L.IsNondegenerate] in
/-- The cyclic glue has exactly two elements when the original vector has an odd pairing. -/
theorem natCard_twoNeighborGlueSubgroup (v : L) (hn : Even (L.integralNorm v))
    (hv : ∃ w : L, Odd (L.integralForm v w)) : Nat.card (L.twoNeighborGlueSubgroup v) = 2 := by
  rw [twoNeighborGlueSubgroup, Nat.card_zmultiples]
  exact addOrderOf_eq_prime (L.two_nsmul_twoNeighborGlueClass v hn)
    (L.twoNeighborGlueClass_ne_zero v hv)

/-- The two-neighbor is the union of its even-pairing kernel and the translate of that
kernel by the half-vector. -/
@[simp]
theorem mem_twoNeighbor_carrier_iff_mem_or_sub_half_mem (he : L.IsEven) (v : L)
    (hn : (8 : ℤ) ∣ L.integralNorm v) (x : V) :
    x ∈ (L.twoNeighbor he v hn).carrier ↔
      x ∈ L.twoNeighborKernel v ∨ x - (1 / 2 : ℚ) • (v : V) ∈ L.twoNeighborKernel v := by
  let h : V := (1 / 2 : ℚ) • (v : V)
  have hh : h + h = (v : V) := by
    dsimp [h]
    rw [← add_smul]
    norm_num
  have hv := L.coe_mem_twoNeighborKernel_of_even_integralNorm v
    (even_iff_two_dvd.mpr (dvd_trans (by decide : (2 : ℤ) ∣ 8) hn))
  constructor
  · intro hx
    obtain ⟨y, hy, n, rfl⟩ := (L.mem_twoNeighbor_carrier_iff he v hn x).mp hx
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      have hmul : n • h = k • (v : V) := by rw [hk, add_smul, ← smul_add, hh]
      -- Name the explicit half-vector with the local abbreviation `h` in the coset expression.
      change y + n • h ∈ _
      rw [hmul]
      exact Submodule.add_mem _ hy (Submodule.smul_mem _ k hv)
    · right
      have hmul : n • h = k • (v : V) + h := by
        rw [hk, two_mul, add_smul, add_smul, one_smul, ← smul_add, hh]
      -- The translate being subtracted is the same local half-vector `h`.
      change y + n • h - h ∈ _
      rw [hmul, ← add_assoc, add_sub_cancel_right]
      exact Submodule.add_mem _ hy (Submodule.smul_mem _ k hv)
  · rintro (hx | hx)
    · exact L.twoNeighborKernel_le_carrier he v hn hx
    · have hsum := Submodule.add_mem (L.twoNeighbor he v hn).carrier
        (L.twoNeighborKernel_le_carrier he v hn hx) (L.half_mem_twoNeighbor_carrier he v hn)
      simpa only [sub_add_cancel] using hsum

/-- With an odd pairing, the intersection of the original and neighboring carriers is
exactly the even-pairing kernel. -/
theorem carrier_inf_twoNeighbor_carrier (he : L.IsEven) (v : L)
    (hn : (8 : ℤ) ∣ L.integralNorm v) (hv : ∃ w : L, Odd (L.integralForm v w)) :
    L.carrier ⊓ (L.twoNeighbor he v hn).carrier = L.twoNeighborKernel v := by
  apply le_antisymm
  · rintro x ⟨hxL, hxN⟩
    rcases (L.mem_twoNeighbor_carrier_iff_mem_or_sub_half_mem he v hn x).mp hxN with hx | hx
    · exact hx
    · have hhalf := L.carrier.sub_mem hxL (L.twoNeighborKernel_le v hx)
      simp only [sub_sub_cancel] at hhalf
      exact (L.half_not_mem_carrier v hv hhalf).elim
  · exact le_inf (L.twoNeighborKernel_le v) (L.twoNeighborKernel_le_carrier he v hn)

/-- The even-pairing kernel also has index two in the neighbor, since the half-vector
generates a discriminant subgroup of order two. -/
theorem relIndex_twoNeighborKernel_twoNeighbor (he : L.IsEven) (v : L)
    (hn : (8 : ℤ) ∣ L.integralNorm v) (hv : ∃ w : L, Odd (L.integralForm v w)) :
    (L.twoNeighborKernel v).toAddSubgroup.relIndex
      (L.twoNeighbor he v hn).carrier.toAddSubgroup = 2 := by
  have h := IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup
    (L := L.twoNeighborKernelLattice v) (L.twoNeighborGlueSubgroup v)
  rw [IntermediateCarrier.index_def, twoNeighborKernelLattice_carrier,
    ← twoNeighbor_carrier] at h
  exact h.trans (L.natCard_twoNeighborGlueSubgroup v
    (even_iff_two_dvd.mpr (dvd_trans (by decide : (2 : ℤ) ∣ 8) hn)) hv)

omit [L.IsNondegenerate] in
/-- **Even two-neighbors of unimodular lattices are unimodular.** The parity kernel has
discriminant four, and its isotropic half-vector glue has order two and is therefore Lagrangian. -/
theorem isUnimodular_twoNeighbor (he : L.IsEven) (hL : L.IsUnimodular) (v : L)
    (hn : (8 : ℤ) ∣ L.integralNorm v) (hv : ∃ w : L, Odd (L.integralForm v w)) :
    letI : L.IsNondegenerate := ⟨hL.nondegenerate⟩
    (L.twoNeighbor he v hn).IsUnimodular := by
  let : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have hIso := L.isIsotropic_twoNeighborGlueSubgroup he v hn
  have hcard : Nat.card (L.twoNeighborGlueSubgroup v) ^ 2 =
      Nat.card ((L.twoNeighborKernelLattice v).discriminantQuadraticModule
        (he.twoNeighborKernelLattice v)) := by
    -- The quadratic discriminant module's carrier is the same existing discriminant group.
    change Nat.card (L.twoNeighborGlueSubgroup v) ^ 2 =
      Nat.card (L.twoNeighborKernelLattice v).DiscriminantGroup
    rw [natCard_discriminantGroup, L.natCard_twoNeighborGlueSubgroup v
      (even_iff_two_dvd.mpr (dvd_trans (by decide : (2 : ℤ) ∣ 8) hn)) hv,
      L.discriminant_twoNeighborKernelLattice hL v hv]
    norm_num
  have hLag := FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq _ hIso
    (isNondegenerate_discriminantQuadraticModule _ _) hcard
  have hLagB : (L.twoNeighborKernelLattice v).discriminantBilinearModule.IsLagrangian
      (L.twoNeighborGlueSubgroup v) := by
    simpa only [discriminantQuadraticModule_toFiniteBilinearModule] using
      hLag.toFiniteBilinearModule
  rw [twoNeighbor]
  exact (isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _ _).mpr hLagB

end TauCeti.IntegralLattice
