/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalBasis
public import TauCeti.NumberTheory.LocalField.UnitFiltration.GaloisAction
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded

/-!
# The unit filtration of a lattice

Let `L/K` be an extension of nonarchimedean local fields, let `ϖ ≠ 0` be an element of the maximal
ideal of `𝒪[K]`, and let `A ⊆ 𝒪[L]` be an `𝒪[K]`-submodule which is open, that is, contains a
power of `𝓂[L]`, and which satisfies `A * A ≤ ϖ • A`. Then for every `j : ℕ` the set

`1 + ϖ ^ j • A = {1 + ϖ ^ j • a | a ∈ A}`

is an open subgroup of `Lˣ`, contained in `U(L, j + 1)`. These subgroups form a decreasing,
separated filtration, and `1 + ϖ ^ j • a ↦ a mod ϖ • A` is a surjective homomorphism onto the
additive group of `A ⧸ ϖ • A` whose kernel is `1 + ϖ ^ (j + 1) • A`: every graded piece of the
filtration is `A ⧸ ϖ • A`. If `A` is stable under the automorphisms of `L/K`, so is each step.

For a finite Galois extension with group `G` a lattice of this kind is supplied by a scaled normal
basis element (`TauCeti.exists_span_orbit_mul_le_smul`), and is then free over `𝒪[K][G]`, so that
every graded piece is free over `(𝒪[K] ⧸ ϖ)[G]`. This filtration therefore replaces the unit
filtration `U(L, i)` of `L`, whose graded pieces are the residue field and are in general not free
over the group ring, when one computes the Tate cohomology of the units of `L` by successive
approximation: this is how the Herbrand quotient of `𝒪[L]ˣ` is shown to be `1` for cyclic `G`.

## Main definitions

* `TauCeti.IsUnitFiltrationLattice ϖ A`: `ϖ` is a nonzero element of `𝓂[K]` and `A` is an open
  `𝒪[K]`-submodule of `𝒪[L]` with `A * A ≤ ϖ • A`.
* `TauCeti.IsUnitFiltrationLattice.filtration`: the subgroup `1 + ϖ ^ j • A` of `Lˣ`.
* `TauCeti.IsUnitFiltrationLattice.filtrationToQuotient`: the homomorphism
  `1 + ϖ ^ j • a ↦ a mod ϖ • A` onto the graded piece.

## Main results

* `TauCeti.IsUnitFiltrationLattice.filtration_antitone`: the filtration is decreasing.
* `TauCeti.IsUnitFiltrationLattice.filtration_le_unitFiltration_succ`: its `j`-th step lies
  in `U(L, j + 1)`; in particular `TauCeti.IsUnitFiltrationLattice.iInf_filtration`: it is
  separated.
* `TauCeti.IsUnitFiltrationLattice.exists_unitFiltration_le_filtration` and
  `TauCeti.IsUnitFiltrationLattice.isOpen_filtration`: each step contains some `U(L, m)`, and
  is open.
* `TauCeti.IsUnitFiltrationLattice.ker_filtrationToQuotient` and
  `TauCeti.IsUnitFiltrationLattice.filtrationToQuotient_surjective`: the graded piece of
  the filtration at `j` is `A ⧸ ϖ • A`.
* `TauCeti.IsUnitFiltrationLattice.unitsMap_mem_filtration`: if `A` is stable under an
  automorphism of `L/K`, so is every step of the filtration.
* `TauCeti.exists_isUnitFiltrationLattice_span_orbit`: for a finite Galois extension, the
  `𝒪[K]`-span of the orbit of a suitable normal basis element is such a lattice.

## References

* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing Submodule MulAction
open scoped Pointwise

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- `A` is a lattice defining a unit filtration with respect to `ϖ`: `ϖ` is a nonzero element of
the maximal ideal of `𝒪[K]`, and `A` is an `𝒪[K]`-submodule of `𝒪[L]` that contains a power of
`𝓂[L]` and satisfies `A * A ≤ ϖ • A`. The sets `1 + ϖ ^ j • A` are then subgroups of `Lˣ`
(`TauCeti.IsUnitFiltrationLattice.filtration`). -/
structure IsUnitFiltrationLattice (ϖ : 𝒪[K]) (A : Submodule 𝒪[K] 𝒪[L]) : Prop where
  /-- The element `ϖ` is nonzero. -/
  ne_zero : ϖ ≠ 0
  /-- The element `ϖ` lies in the maximal ideal of `𝒪[K]`. -/
  mem_maximalIdeal : ϖ ∈ 𝓂[K]
  /-- The lattice is nearly closed under multiplication: `A * A ≤ ϖ • A`. -/
  mul_le_smul : A * A ≤ ϖ • A
  /-- The lattice is open: it contains a power of the maximal ideal of `𝒪[L]`. -/
  exists_pow_maximalIdeal_le : ∃ n : ℕ, (𝓂[L] ^ n).restrictScalars 𝒪[K] ≤ A

namespace IsUnitFiltrationLattice

variable {ϖ : 𝒪[K]} {A : Submodule 𝒪[K] 𝒪[L]} (hA : IsUnitFiltrationLattice ϖ A)

include hA

/-- The image of `ϖ` in `𝒪[L]` lies in the maximal ideal. -/
private theorem algebraMap_mem_maximalIdeal : algebraMap 𝒪[K] 𝒪[L] ϖ ∈ 𝓂[L] :=
  map_maximalIdeal_le (algebraMap 𝒪[K] 𝒪[L]) (Ideal.mem_map_of_mem _ hA.mem_maximalIdeal)

/-- Every element of `A` lies in the maximal ideal of `𝒪[L]`: its square lies in `ϖ • A`. -/
theorem mem_maximalIdeal_of_mem {a : 𝒪[L]} (ha : a ∈ A) : a ∈ 𝓂[L] := by
  obtain ⟨b, -, hb⟩ :=
    (mem_smul_pointwise_iff_exists _ _ _).1 (hA.mul_le_smul (mul_mem_mul ha ha))
  refine (maximalIdeal.isMaximal 𝒪[L]).isPrime.mem_of_pow_mem 2 ?_
  rw [pow_two, ← hb, Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ hA.algebraMap_mem_maximalIdeal

/-- `ϖ ^ j • a` lies in the `(j + 1)`-st power of the maximal ideal of `𝒪[L]` for `a ∈ A`. -/
private theorem pow_smul_mem_maximalIdeal_pow (j : ℕ) {a : 𝒪[L]} (ha : a ∈ A) :
    ϖ ^ j • a ∈ 𝓂[L] ^ (j + 1) := by
  rw [Algebra.smul_def, map_pow, pow_succ]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hA.algebraMap_mem_maximalIdeal j)
    (hA.mem_maximalIdeal_of_mem ha)

/-- `1 + ϖ ^ j • a` is a unit of `𝒪[L]` for `a ∈ A`. -/
private theorem isUnit_one_add_pow_smul (j : ℕ) {a : 𝒪[L]} (ha : a ∈ A) :
    IsUnit (1 + ϖ ^ j • a) := by
  have h : -(ϖ ^ j • a) ∈ 𝓂[L] :=
    neg_mem (Ideal.pow_le_self j.succ_ne_zero (hA.pow_smul_mem_maximalIdeal_pow j ha))
  simpa using isUnit_one_sub_self_of_mem_nonunits _ h

/-- The element `a` is determined by `1 + ϖ ^ j • a`. -/
private theorem eq_of_one_add_pow_smul_eq (j : ℕ) {a b : 𝒪[L]}
    (h : ((1 + ϖ ^ j • a : 𝒪[L]) : L) = ((1 + ϖ ^ j • b : 𝒪[L]) : L)) : a = b := by
  have hϖ : algebraMap 𝒪[K] 𝒪[L] ϖ ^ j ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L])).2 hA.ne_zero)
  have h' := add_left_cancel (Subtype.coe_injective h)
  rw [Algebra.smul_def, Algebra.smul_def, map_pow] at h'
  exact mul_left_cancel₀ hϖ h'

/-- The product of two elements of `1 + ϖ ^ j • A` lies in `1 + ϖ ^ j • A`, with correction term
in `ϖ • A`. -/
private theorem exists_one_add_mul_one_add (j : ℕ) {a b : 𝒪[L]} (ha : a ∈ A) (hb : b ∈ A) :
    ∃ c ∈ ϖ • A, (1 + ϖ ^ j • a) * (1 + ϖ ^ j • b) = 1 + ϖ ^ j • (a + b + c) := by
  obtain ⟨d, hd, hab⟩ :=
    (mem_smul_pointwise_iff_exists _ _ _).1 (hA.mul_le_smul (mul_mem_mul ha hb))
  refine ⟨ϖ ^ j • (a * b), smul_mem _ _ (hab ▸ smul_mem_pointwise_smul _ _ _ hd), ?_⟩
  simp only [Algebra.smul_def, map_pow]
  ring

omit hA in
/-- The units `1 + ϖ ^ j • a` with `a ∈ A`, before they are known to form a subgroup. -/
private def carrier (ϖ : 𝒪[K]) (A : Submodule 𝒪[K] 𝒪[L]) (j : ℕ) : Set Lˣ :=
  {x | ∃ a ∈ A, (x : L) = ((1 + ϖ ^ j • a : 𝒪[L]) : L)}

/-- The set `1 + ϖ ^ j • A` is a submonoid of `Lˣ`. -/
private def submonoid (j : ℕ) : Submonoid Lˣ where
  carrier := carrier ϖ A j
  one_mem' := ⟨0, zero_mem _, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    obtain ⟨c, hc, h⟩ := hA.exists_one_add_mul_one_add j ha hb
    exact ⟨a + b + c, add_mem (add_mem ha hb) (smul_le_self_of_tower ϖ A hc), by
      rw [Units.val_mul, hx, hy, ← Subring.coe_mul, h]⟩

/-- The set `1 + ϖ ^ j • A` lies in `U(L, j + 1)`. -/
private theorem carrier_subset (j : ℕ) :
    carrier ϖ A j ⊆ (unitFiltration L (j + 1) : Set Lˣ) := by
  rintro x ⟨a, ha, hx⟩
  exact mem_unitFiltration_iff_exists.2
    ⟨(hA.isUnit_one_add_pow_smul j ha).unit, by simpa using hA.pow_smul_mem_maximalIdeal_pow j ha,
      hx.symm⟩

/-- The set `1 + ϖ ^ j • A` contains some `U(L, m)`. -/
private theorem exists_unitFiltration_subset_carrier (j : ℕ) :
    ∃ m : ℕ, (unitFiltration L m : Set Lˣ) ⊆ carrier ϖ A j := by
  obtain ⟨n, hn⟩ := hA.exists_pow_maximalIdeal_le
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hc : Ideal.span {algebraMap 𝒪[K] 𝒪[L] ϖ ^ j} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L])).2
      hA.ne_zero)
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hc hπ
  have hk' : 𝓂[L] ^ k = Ideal.span {algebraMap 𝒪[K] 𝒪[L] ϖ ^ j} := by
    rw [hk, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.span_singleton_pow]
  refine ⟨k + n, fun x hx ↦ ?_⟩
  obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.1 hx
  rw [pow_add, hk', Ideal.mem_span_singleton_mul] at hu
  obtain ⟨a, ha, hau⟩ := hu
  refine ⟨a, hn ha, ?_⟩
  rw [← hux, Algebra.smul_def, map_pow, hau, add_sub_cancel]

/-- **The unit filtration of a lattice.** For a lattice `A` defining a unit filtration with
respect to `ϖ`, the subgroup `1 + ϖ ^ j • A` of `Lˣ`: the units of the form `1 + ϖ ^ j • a` with
`a ∈ A`. -/
def filtration (j : ℕ) : Subgroup Lˣ where
  __ := hA.submonoid j
  inv_mem' {x} hx := by
    -- `1 + ϖ ^ j • A` is a submonoid containing an open subgroup `U(L, m)` of finite index in
    -- `U(L, 1)`, which contains `1 + ϖ ^ j • A`. Hence `x ^ (n + 1) ∈ U(L, m)` for some `n`, and
    -- `x⁻¹ = x ^ n * (x ^ (n + 1))⁻¹`.
    obtain ⟨m, hm⟩ := hA.exists_unitFiltration_subset_carrier j
    have hx1 : x ∈ unitFiltration L (0 + 1) :=
      unitFiltration_antitone (by omega) (hA.carrier_subset j hx)
    obtain ⟨_ | n, hn, -, hxn⟩ :=
      Subgroup.exists_pow_mem_of_relIndex_ne_zero
        (Subgroup.relIndex_ne_zero (H := unitFiltration L m)) hx1
    · exact absurd hn (lt_irrefl 0)
    have hinv : x⁻¹ = x ^ n * (x ^ (n + 1))⁻¹ := by
      rw [pow_succ, mul_inv, mul_inv_cancel_left]
    rw [hinv]
    exact (hA.submonoid j).mul_mem ((hA.submonoid j).pow_mem hx n) (hm (inv_mem hxn.1))

/-- Membership in the unit filtration of a lattice: `x = 1 + ϖ ^ j • a` with `a ∈ A`. -/
theorem mem_filtration_iff {j : ℕ} {x : Lˣ} :
    x ∈ hA.filtration j ↔ ∃ a ∈ A, (x : L) = ((1 + ϖ ^ j • a : 𝒪[L]) : L) :=
  Iff.rfl

/-- The step `1 + ϖ ^ j • A` lies in `U(L, j + 1)`. -/
theorem filtration_le_unitFiltration_succ (j : ℕ) :
    hA.filtration j ≤ unitFiltration L (j + 1) :=
  hA.carrier_subset j

/-- The step `1 + ϖ ^ j • A` contains some `U(L, m)`. -/
theorem exists_unitFiltration_le_filtration (j : ℕ) :
    ∃ m : ℕ, unitFiltration L m ≤ hA.filtration j :=
  hA.exists_unitFiltration_subset_carrier j

/-- Each step `1 + ϖ ^ j • A` is an open subgroup of `Lˣ`. -/
theorem isOpen_filtration (j : ℕ) : IsOpen (hA.filtration j : Set Lˣ) := by
  obtain ⟨m, hm⟩ := hA.exists_unitFiltration_le_filtration j
  exact Subgroup.isOpen_mono hm (isOpen_unitFiltration m)

/-- The unit filtration of a lattice is decreasing. -/
theorem filtration_antitone : Antitone hA.filtration := by
  refine antitone_nat_of_succ_le fun j x hx ↦ ?_
  obtain ⟨a, ha, hx⟩ := hx
  refine ⟨ϖ • a, smul_mem _ _ ha, ?_⟩
  rw [hx, pow_succ, mul_smul]

/-- The unit filtration of a lattice separates points: an element lying in every step is `1`. -/
theorem iInf_filtration : ⨅ j, hA.filtration j = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  rw [← iInf_unitFiltration (K := L), Subgroup.mem_iInf]
  exact fun i ↦ unitFiltration_antitone i.le_succ
    (hA.filtration_le_unitFiltration_succ i (Subgroup.mem_iInf.1 hx i))

/-! ### The graded pieces -/

/-- The coordinate `a ∈ A` of an element `x = 1 + ϖ ^ j • a` of the `j`-th step. -/
private def coord {j : ℕ} (x : hA.filtration j) : A :=
  ⟨x.2.choose, x.2.choose_spec.1⟩

private theorem coe_coord {j : ℕ} (x : hA.filtration j) :
    ((x : Lˣ) : L) = ((1 + ϖ ^ j • (hA.coord x : 𝒪[L]) : 𝒪[L]) : L) :=
  x.2.choose_spec.2

private theorem coord_eq {j : ℕ} (x : hA.filtration j) {a : 𝒪[L]}
    (hx : ((x : Lˣ) : L) = ((1 + ϖ ^ j • a : 𝒪[L]) : L)) : (hA.coord x : 𝒪[L]) = a :=
  hA.eq_of_one_add_pow_smul_eq j ((hA.coe_coord x).symm.trans hx)

/-- **The graded pieces of the unit filtration of a lattice.** The homomorphism
`1 + ϖ ^ j • a ↦ a mod ϖ • A` from the `j`-th step onto the additive group of `A ⧸ ϖ • A`. Its
kernel is the next step (`TauCeti.IsUnitFiltrationLattice.ker_filtrationToQuotient`), and it
is surjective (`TauCeti.IsUnitFiltrationLattice.filtrationToQuotient_surjective`). -/
def filtrationToQuotient (j : ℕ) :
    hA.filtration j →* Multiplicative (A ⧸ (ϖ • ⊤ : Submodule 𝒪[K] A)) where
  toFun x := Multiplicative.ofAdd (Submodule.Quotient.mk (hA.coord x))
  map_one' := by
    have h : hA.coord (1 : hA.filtration j) = 0 := Subtype.ext (hA.coord_eq 1 (by simp))
    rw [h, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' x y := by
    obtain ⟨c, hc, h⟩ := hA.exists_one_add_mul_one_add j (hA.coord x).2 (hA.coord y).2
    have hxy : (hA.coord (x * y) : 𝒪[L]) = hA.coord x + hA.coord y + c := by
      refine hA.coord_eq (x * y) ?_
      rw [Subgroup.coe_mul, Units.val_mul, hA.coe_coord x, hA.coe_coord y, ← Subring.coe_mul, h]
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
    refine congrArg _ ((Submodule.Quotient.eq _).2 ?_)
    rw [← ideal_span_singleton_smul, mem_smul_top_iff, ideal_span_singleton_smul]
    simpa [hxy] using hc

/-- The value of `filtrationToQuotient` at `1 + ϖ ^ j • a` is `a mod ϖ • A`. -/
theorem filtrationToQuotient_apply {j : ℕ} (x : hA.filtration j) {a : 𝒪[L]}
    (ha : a ∈ A) (hx : ((x : Lˣ) : L) = ((1 + ϖ ^ j • a : 𝒪[L]) : L)) :
    hA.filtrationToQuotient j x =
      Multiplicative.ofAdd (Submodule.Quotient.mk ⟨a, ha⟩) := by
  have h : hA.coord x = ⟨a, ha⟩ := Subtype.ext (hA.coord_eq x hx)
  simp only [filtrationToQuotient, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h]

/-- The kernel of `filtrationToQuotient` on the `j`-th step is the `(j + 1)`-st step: the graded
piece of the unit filtration of `A` at `j` embeds into `A ⧸ ϖ • A`. -/
theorem ker_filtrationToQuotient (j : ℕ) :
    (hA.filtrationToQuotient j).ker = (hA.filtration (j + 1)).subgroupOf (hA.filtration j) := by
  ext x
  obtain ⟨a, ha, hx⟩ := x.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hA.filtrationToQuotient_apply x ha hx,
    ofAdd_eq_one, Submodule.Quotient.mk_eq_zero, ← ideal_span_singleton_smul, mem_smul_top_iff,
    ideal_span_singleton_smul, mem_smul_pointwise_iff_exists]
  refine ⟨fun ⟨b, hb, hab⟩ ↦ ⟨b, hb, ?_⟩, fun ⟨b, hb, hxb⟩ ↦ ⟨b, hb, ?_⟩⟩
  · rw [hx, pow_succ, mul_smul, hab]
  · refine hA.eq_of_one_add_pow_smul_eq j ?_
    rw [← hx, hxb, pow_succ, mul_smul]

/-- `filtrationToQuotient` is surjective: every class in `A ⧸ ϖ • A` is the class of the
coordinate of some `1 + ϖ ^ j • a`. -/
theorem filtrationToQuotient_surjective (j : ℕ) :
    Function.Surjective (hA.filtrationToQuotient j) := by
  intro q
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd q)
  have hu := hA.isUnit_one_add_pow_smul j ha
  let x : Lˣ := Units.map (Subring.subtype 𝒪[L] : 𝒪[L] →* L) hu.unit
  have hx : (x : L) = ((1 + ϖ ^ j • a : 𝒪[L]) : L) := rfl
  exact ⟨⟨x, a, ha, hx⟩, hA.filtrationToQuotient_apply _ ha hx⟩

/-! ### Galois stability -/

variable [Module.Finite K L]

/-- If the lattice `A` is stable under an automorphism `σ` of `L/K`, so is every step
`1 + ϖ ^ j • A` of its unit filtration. -/
theorem unitsMap_mem_filtration (σ : L ≃ₐ[K] L) (hσ : ∀ a ∈ A, σ • a ∈ A) {j : ℕ} {x : Lˣ}
    (hx : x ∈ hA.filtration j) : Units.map (σ : L →* L) x ∈ hA.filtration j := by
  obtain ⟨a, ha, hx⟩ := hx
  refine ⟨σ • a, hσ a ha, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, hx, ← AlgEquiv.coe_smul_integerRing, smul_add,
    smul_one, smul_comm]

end IsUnitFiltrationLattice

/-- **Lattices defining a unit filtration exist.** For a finite Galois extension `L/K` of
nonarchimedean local fields and a nonzero `ϖ ∈ 𝓂[K]`, some `α ∈ 𝒪[L]` has conjugates forming a
`K`-basis of `L` and is such that the `𝒪[K]`-span of its orbit defines a unit filtration with
respect to `ϖ`. That span is stable under the Galois group and free over `𝒪[K][G]` on `α`
(`TauCeti.spanOrbitEquiv`). -/
theorem exists_isUnitFiltrationLattice_span_orbit [Module.Finite K L] [IsGalois K L]
    {ϖ : 𝒪[K]} (hϖ : ϖ ≠ 0) (hϖm : ϖ ∈ 𝓂[K]) :
    ∃ α : 𝒪[L], LinearIndependent K (fun σ : L ≃ₐ[K] L ↦ σ (α : L)) ∧
      IsUnitFiltrationLattice ϖ (span 𝒪[K] (orbit (L ≃ₐ[K] L) α)) := by
  obtain ⟨α, hα, hmul⟩ := exists_span_orbit_mul_le_smul (L := L) hϖ
  exact ⟨α, hα, hϖ, hϖm, hmul, exists_pow_maximalIdeal_le_span_orbit hα⟩

end TauCeti
