/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `isLocalHom_of_le_jacobson` makes reduction modulo `I ≤ jacobson` reflect units.
public import Mathlib.RingTheory.Jacobson.Ideal
-- `Subgroup.index_comap_of_surjective` and `Subgroup.index_ker`.
public import Mathlib.GroupTheory.Index
-- `Matrix.GeneralLinearGroup.map_surjective` lifts invertible matrices modulo `I`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
-- `TauCeti.parahoricSubgroup` gives the general parahoric congruence subgroup.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
-- `TauCeti.UpperTriangularGroup.map_surjective` lifts invertible upper-triangular matrices.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Lift
-- `Matrix.exists_blockUnitriangular_mul_blockTriangular` is block row reduction.
public import TauCeti.LinearAlgebra.Matrix.LDU

/-!
# Upper-triangular congruence subgroups

For an ideal `I` of a commutative ring `R`, the **upper-triangular congruence subgroup**
`B(I) ⊆ GL_m(R)` consists of the invertible matrices that are upper triangular modulo `I`, and the
**upper-unitriangular congruence subgroup** `U(I) ⊆ B(I)` of those that are upper unitriangular
modulo `I`. They are the preimages, under reduction `GL_m(R) → GL_m(R ⧸ I)`, of the
upper-triangular and upper-unitriangular subgroups of `GL_m(R ⧸ I)`.

Over the valuation ring of a nonarchimedean local field, with `I` the maximal ideal, these are the
Iwahori subgroup and the pro-`p` Iwahori subgroup (`TauCeti.iwahori`, `TauCeti.iwahoriOne`); for
`m = 2` and `R = ℤ`, their determinant-one parts are the classical `Γ₀(N)` and `Γ₁(N)`. They are
the standard level subgroups at a finite place.

Reading off the diagonal modulo `I` is a homomorphism `B(I) → (m → (R ⧸ I)ˣ)` with kernel `U(I)`,
so `U(I)` is normal in `B(I)`. When `I` lies in the Jacobson radical, units and invertible
matrices lift modulo `I`; then the diagonal map is surjective, so
`B(I) ⧸ U(I) ≃* (m → (R ⧸ I)ˣ)`, and the indices of `B(I)` and `U(I)` in `GL_m(R)` are those of
the upper-triangular and upper-unitriangular subgroups of `GL_m(R ⧸ I)`.

When `I` lies in the Jacobson radical, every `g ∈ B(I)` also has an **Iwahori factorization**
`g = u * l`, with `u` upper unitriangular and `l` lower triangular (both then lie in `B(I)`).
Indeed the trailing principal blocks of `g`, on the indices above a given one, are upper
triangular with unit diagonal modulo `I`, so their determinants are units, and block row reduction
(`Matrix.exists_blockUnitriangular_mul_blockTriangular`, for the reversed order of the indices)
clears the entries of `g` above the diagonal by an upper-unitriangular matrix acting on the left.

## Main declarations

* `TauCeti.upperTriangularCongruenceSubgroup`, `TauCeti.upperUnitriangularCongruenceSubgroup`:
  the subgroups `B(I)` and `U(I)` of `GL_m(R)`.
* `TauCeti.mem_upperTriangularCongruenceSubgroup_iff`,
  `TauCeti.mem_upperUnitriangularCongruenceSubgroup_iff`: membership through the entries below
  the diagonal and the diagonal congruences.
* `TauCeti.comap_generalLinearGroupMap_upperTriangularGroup`: the preimage of the
  upper-triangular group under any ring homomorphism `f` is `B(ker f)`.
* `TauCeti.UpperTriangularCongruenceSubgroup.diag`: the diagonal modulo `I`, with kernel `U(I)`
  (`TauCeti.UpperTriangularCongruenceSubgroup.ker_diag`).
* `TauCeti.UpperTriangularCongruenceSubgroup.quotientEquiv`: `B(I) ⧸ U(I) ≃* (m → (R ⧸ I)ˣ)`
  for `I` in the Jacobson radical.
* `TauCeti.relIndex_upperUnitriangularCongruenceSubgroup_upperTriangularCongruenceSubgroup`:
  `[B(I) : U(I)] = #((R ⧸ I)ˣ) ^ #m`.
* `TauCeti.index_upperTriangularCongruenceSubgroup`: `[GL_m(R) : B(I)]` is the index of the
  upper-triangular subgroup of `GL_m(R ⧸ I)`.
* `TauCeti.exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul`: the Iwahori
  factorization of `B(I)` for `I` in the Jacobson radical.

## References

* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), §5.2.1 and §9.0.1.
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §2.
-/

public section

namespace TauCeti

open Matrix

variable (m : Type*) [Fintype m] [LinearOrder m] {R : Type*} [CommRing R]

/-- The **upper-triangular congruence subgroup** of `GL_m(R)` modulo an ideal `I`: the invertible
matrices that are upper triangular modulo `I`, that is, the preimage of the upper-triangular
subgroup of `GL_m(R ⧸ I)` under reduction modulo `I`. -/
def upperTriangularCongruenceSubgroup (I : Ideal R) : Subgroup (GL m R) :=
  (upperTriangularGroup m (R ⧸ I)).comap (GeneralLinearGroup.map (Ideal.Quotient.mk I))

/-- The **upper-unitriangular congruence subgroup** of `GL_m(R)` modulo an ideal `I`: the invertible
matrices that are upper unitriangular modulo `I`, that is, the preimage of the upper-unitriangular
subgroup of `GL_m(R ⧸ I)` under reduction modulo `I`. -/
def upperUnitriangularCongruenceSubgroup (I : Ideal R) : Subgroup (GL m R) :=
  (upperUnitriangularGroup m (R ⧸ I)).comap (GeneralLinearGroup.map (Ideal.Quotient.mk I))

variable {m} {I J : Ideal R}

/-- An invertible matrix lies in the upper-triangular congruence subgroup modulo `I` exactly when
its reduction modulo `I` is upper triangular. -/
theorem map_mem_upperTriangularGroup_iff {g : GL m R} :
    GeneralLinearGroup.map (Ideal.Quotient.mk I) g ∈ upperTriangularGroup m (R ⧸ I) ↔
      g ∈ upperTriangularCongruenceSubgroup m I :=
  Iff.rfl

/-- An invertible matrix lies in the upper-unitriangular congruence subgroup modulo `I` exactly
when its reduction modulo `I` is upper unitriangular. -/
theorem map_mem_upperUnitriangularGroup_iff {g : GL m R} :
    GeneralLinearGroup.map (Ideal.Quotient.mk I) g ∈ upperUnitriangularGroup m (R ⧸ I) ↔
      g ∈ upperUnitriangularCongruenceSubgroup m I :=
  Iff.rfl

/-- Membership in the upper-triangular congruence subgroup modulo `I`: every entry below the
diagonal lies in `I`. -/
@[simp]
theorem mem_upperTriangularCongruenceSubgroup_iff {g : GL m R} :
    g ∈ upperTriangularCongruenceSubgroup m I ↔
      ∀ ⦃i j : m⦄, j < i → (g : Matrix m m R) i j ∈ I := by
  simp only [← map_mem_upperTriangularGroup_iff, UpperTriangularGroup.mem_iff,
    Matrix.IsUpperTriangular, Matrix.BlockTriangular, id, GeneralLinearGroup.map_apply,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The upper-triangular congruence subgroup modulo `I` coincides with `parahoricSubgroup` for the
dual order `OrderDual.toDual : m → mᵒᵈ`. -/
theorem parahoricSubgroup_toDual_eq_upperTriangularCongruenceSubgroup (I : Ideal R) :
    parahoricSubgroup (OrderDual.toDual : m → mᵒᵈ) I = upperTriangularCongruenceSubgroup m I := by
  ext g
  simp [mem_parahoricSubgroup, mem_upperTriangularCongruenceSubgroup_iff]

/-- Membership in the upper-unitriangular congruence subgroup modulo `I`: every entry below the
diagonal lies in `I`, and every diagonal entry is congruent to `1` modulo `I`. -/
@[simp]
theorem mem_upperUnitriangularCongruenceSubgroup_iff {g : GL m R} :
    g ∈ upperUnitriangularCongruenceSubgroup m I ↔
      (∀ ⦃i j : m⦄, j < i → (g : Matrix m m R) i j ∈ I) ∧
        ∀ i, (g : Matrix m m R) i i - 1 ∈ I := by
  simp only [← map_mem_upperUnitriangularGroup_iff, UpperUnitriangularGroup.mem_iff,
    Matrix.isUpperUnitriangular_def, ← map_mem_upperTriangularGroup_iff.trans
      mem_upperTriangularCongruenceSubgroup_iff, UpperTriangularGroup.mem_iff,
    GeneralLinearGroup.map_apply, ← Ideal.Quotient.eq, map_one]

/-- The upper-unitriangular congruence subgroup lies in the upper-triangular one. -/
theorem upperUnitriangularCongruenceSubgroup_le_upperTriangularCongruenceSubgroup :
    upperUnitriangularCongruenceSubgroup m I ≤ upperTriangularCongruenceSubgroup m I :=
  Subgroup.comap_mono UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup

/-- The upper-triangular congruence subgroup grows with the ideal. -/
theorem upperTriangularCongruenceSubgroup_mono (h : I ≤ J) :
    upperTriangularCongruenceSubgroup m I ≤ upperTriangularCongruenceSubgroup m J := fun _ hg ↦
  mem_upperTriangularCongruenceSubgroup_iff.mpr fun _ _ hji ↦
    h (mem_upperTriangularCongruenceSubgroup_iff.mp hg hji)

/-- The upper-unitriangular congruence subgroup grows with the ideal. -/
theorem upperUnitriangularCongruenceSubgroup_mono (h : I ≤ J) :
    upperUnitriangularCongruenceSubgroup m I ≤ upperUnitriangularCongruenceSubgroup m J :=
  fun _ hg ↦
    have hg := mem_upperUnitriangularCongruenceSubgroup_iff.mp hg
    mem_upperUnitriangularCongruenceSubgroup_iff.mpr
      ⟨fun _ _ hji ↦ h (hg.1 hji), fun i ↦ h (hg.2 i)⟩

/-- The preimage of the upper-triangular subgroup under entrywise application of a ring
homomorphism `f` is the upper-triangular congruence subgroup modulo `ker f`. -/
theorem comap_generalLinearGroupMap_upperTriangularGroup {S : Type*} [CommRing S] (f : R →+* S) :
    (upperTriangularGroup m S).comap (GeneralLinearGroup.map f) =
      upperTriangularCongruenceSubgroup m (RingHom.ker f) := by
  ext g
  simp only [Subgroup.mem_comap, UpperTriangularGroup.mem_iff, Matrix.IsUpperTriangular,
    Matrix.BlockTriangular, id, GeneralLinearGroup.map_apply,
    mem_upperTriangularCongruenceSubgroup_iff, RingHom.mem_ker]

/-- The preimage of the upper-unitriangular subgroup under entrywise application of a ring
homomorphism `f` is the upper-unitriangular congruence subgroup modulo `ker f`. -/
theorem comap_generalLinearGroupMap_upperUnitriangularGroup {S : Type*} [CommRing S]
    (f : R →+* S) :
    (upperUnitriangularGroup m S).comap (GeneralLinearGroup.map f) =
      upperUnitriangularCongruenceSubgroup m (RingHom.ker f) := by
  ext g
  simp only [Subgroup.mem_comap, UpperUnitriangularGroup.mem_iff, Matrix.isUpperUnitriangular_def,
    Matrix.IsUpperTriangular, Matrix.BlockTriangular, id, GeneralLinearGroup.map_apply,
    mem_upperUnitriangularCongruenceSubgroup_iff, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

/-- Modulo the zero ideal, the upper-triangular congruence subgroup is the upper-triangular
subgroup. -/
@[simp]
theorem upperTriangularCongruenceSubgroup_bot :
    upperTriangularCongruenceSubgroup m (⊥ : Ideal R) = upperTriangularGroup m R := by
  ext g
  simp [Matrix.IsUpperTriangular, Matrix.BlockTriangular]

/-- Modulo the zero ideal, the upper-unitriangular congruence subgroup is the upper-unitriangular
subgroup. -/
@[simp]
theorem upperUnitriangularCongruenceSubgroup_bot :
    upperUnitriangularCongruenceSubgroup m (⊥ : Ideal R) = upperUnitriangularGroup m R := by
  ext g
  simp [Matrix.isUpperUnitriangular_def, Matrix.IsUpperTriangular, Matrix.BlockTriangular,
    sub_eq_zero]

/-- Modulo the unit ideal, every invertible matrix is upper triangular. -/
@[simp]
theorem upperTriangularCongruenceSubgroup_top :
    upperTriangularCongruenceSubgroup m (⊤ : Ideal R) = ⊤ := by
  ext g
  simp

/-- Modulo the unit ideal, every invertible matrix is upper unitriangular. -/
@[simp]
theorem upperUnitriangularCongruenceSubgroup_top :
    upperUnitriangularCongruenceSubgroup m (⊤ : Ideal R) = ⊤ := by
  ext g
  simp

namespace UpperTriangularCongruenceSubgroup

variable (I) in
/-- Reduction modulo `I`, from the upper-triangular congruence subgroup to the upper-triangular
subgroup of `GL_m(R ⧸ I)`. -/
def reduction : upperTriangularCongruenceSubgroup m I →* upperTriangularGroup m (R ⧸ I) :=
  ((GeneralLinearGroup.map (Ideal.Quotient.mk I)).domRestrict
      (upperTriangularCongruenceSubgroup m I)).codRestrict
    (upperTriangularGroup m (R ⧸ I)) fun g ↦ map_mem_upperTriangularGroup_iff.mpr g.property

/-- The matrix underlying the reduction modulo `I` is the entrywise reduction. -/
@[simp]
theorem coe_reduction (g : upperTriangularCongruenceSubgroup m I) :
    ((reduction I g : upperTriangularGroup m (R ⧸ I)) : GL m (R ⧸ I)) =
      GeneralLinearGroup.map (Ideal.Quotient.mk I) (g : GL m R) :=
  (rfl)

/-- If `I` lies in the Jacobson radical, every invertible upper-triangular matrix modulo `I` is the
reduction of an element of the upper-triangular congruence subgroup. -/
theorem reduction_surjective (hI : I ≤ Ring.jacobson R) :
    Function.Surjective (reduction (m := m) I) := by
  have := isLocalHom_of_le_jacobson hI
  intro b
  obtain ⟨a, ha⟩ := UpperTriangularGroup.map_surjective (n := m) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective b
  have hmem : (a : GL m R) ∈ upperTriangularCongruenceSubgroup m I := by
    rw [← map_mem_upperTriangularGroup_iff, ← UpperTriangularGroup.coe_map, ha]
    exact b.property
  refine ⟨⟨a, hmem⟩, Subtype.ext ?_⟩
  rw [coe_reduction, ← ha, UpperTriangularGroup.coe_map]

variable (I) in
/-- The **diagonal modulo `I`** of an element of the upper-triangular congruence subgroup, as a
homomorphism to the coordinatewise units of `R ⧸ I`. -/
def diag : upperTriangularCongruenceSubgroup m I →* (m → (R ⧸ I)ˣ) :=
  UpperTriangularGroup.diag.comp (reduction I)

/-- The `i`-th coordinate of the diagonal modulo `I` is the `i`-th diagonal entry reduced
modulo `I`. -/
@[simp]
theorem diag_apply_val (g : upperTriangularCongruenceSubgroup m I) (i : m) :
    ((diag I g i : (R ⧸ I)ˣ) : R ⧸ I) =
      Ideal.Quotient.mk I (((g : GL m R) : Matrix m m R) i i) := by
  simp [diag]

/-- The kernel of the diagonal modulo `I` is the upper-unitriangular congruence subgroup. -/
theorem ker_diag :
    (diag (m := m) I).ker =
      (upperUnitriangularCongruenceSubgroup m I).subgroupOf
        (upperTriangularCongruenceSubgroup m I) := by
  ext g
  rw [MonoidHom.mem_ker, diag, MonoidHom.comp_apply, UpperTriangularGroup.diag_eq_one_iff,
    Subgroup.mem_subgroupOf, coe_reduction, map_mem_upperUnitriangularGroup_iff]

/-- The upper-unitriangular congruence subgroup is normal in the upper-triangular one. -/
instance normal_upperUnitriangularCongruenceSubgroup_subgroupOf :
    ((upperUnitriangularCongruenceSubgroup m I).subgroupOf
      (upperTriangularCongruenceSubgroup m I)).Normal :=
  ker_diag (m := m) (I := I) ▸ MonoidHom.normal_ker _

/-- If `I` lies in the Jacobson radical, the diagonal modulo `I` is surjective. -/
theorem diag_surjective (hI : I ≤ Ring.jacobson R) :
    Function.Surjective (diag (m := m) I) :=
  UpperTriangularGroup.diag_surjective.comp (reduction_surjective hI)

/-- If `I` lies in the Jacobson radical, the diagonal modulo `I` identifies the quotient of the
upper-triangular congruence subgroup by the upper-unitriangular one with `m → (R ⧸ I)ˣ`. -/
noncomputable def quotientEquiv (hI : I ≤ Ring.jacobson R) :
    upperTriangularCongruenceSubgroup m I ⧸
        (upperUnitriangularCongruenceSubgroup m I).subgroupOf
          (upperTriangularCongruenceSubgroup m I) ≃*
      (m → (R ⧸ I)ˣ) :=
  (QuotientGroup.quotientMulEquivOfEq ker_diag.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (diag_surjective hI))

/-- The identification of the quotient sends a class to the diagonal modulo `I` of a
representative. -/
@[simp]
theorem quotientEquiv_mk (hI : I ≤ Ring.jacobson R) (g : upperTriangularCongruenceSubgroup m I) :
    quotientEquiv hI (g : upperTriangularCongruenceSubgroup m I ⧸
        (upperUnitriangularCongruenceSubgroup m I).subgroupOf
          (upperTriangularCongruenceSubgroup m I)) = diag I g :=
  (rfl)

end UpperTriangularCongruenceSubgroup

open UpperTriangularCongruenceSubgroup in
/-- If `I` lies in the Jacobson radical, the index of the upper-unitriangular congruence subgroup
in the upper-triangular one is `#((R ⧸ I)ˣ) ^ #m`. -/
theorem relIndex_upperUnitriangularCongruenceSubgroup_upperTriangularCongruenceSubgroup
    (hI : I ≤ Ring.jacobson R) :
    (upperUnitriangularCongruenceSubgroup m I).relIndex (upperTriangularCongruenceSubgroup m I) =
      Nat.card (R ⧸ I)ˣ ^ Fintype.card m := by
  rw [Subgroup.relIndex, ← ker_diag, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (diag_surjective hI), Subgroup.card_top, Nat.card_fun,
    Nat.card_eq_fintype_card (α := m)]

/-- If `I` lies in the Jacobson radical, the index of the upper-triangular congruence subgroup
modulo `I` in `GL_m(R)` is the index of the upper-triangular subgroup in `GL_m(R ⧸ I)`. -/
theorem index_upperTriangularCongruenceSubgroup (hI : I ≤ Ring.jacobson R) :
    (upperTriangularCongruenceSubgroup m I).index = (upperTriangularGroup m (R ⧸ I)).index :=
  have := isLocalHom_of_le_jacobson hI
  Subgroup.index_comap_of_surjective _
    (GeneralLinearGroup.map_surjective _ Ideal.Quotient.mk_surjective)

/-- If `I` lies in the Jacobson radical, the index of the upper-unitriangular congruence subgroup
modulo `I` in `GL_m(R)` is the index of the upper-unitriangular subgroup in `GL_m(R ⧸ I)`. -/
theorem index_upperUnitriangularCongruenceSubgroup (hI : I ≤ Ring.jacobson R) :
    (upperUnitriangularCongruenceSubgroup m I).index =
      (upperUnitriangularGroup m (R ⧸ I)).index :=
  have := isLocalHom_of_le_jacobson hI
  Subgroup.index_comap_of_surjective _
    (GeneralLinearGroup.map_surjective _ Ideal.Quotient.mk_surjective)

open OrderDual in
/-- **The Iwahori factorization.** If `I` lies in the Jacobson radical, every element `g` of the
upper-triangular congruence subgroup modulo `I` is `u * l` with `u` upper unitriangular and
`l = u⁻¹ * g` lower triangular. For the Iwahori subgroup of `GL_m` over the valuation ring of a
nonarchimedean local field this writes it as the product of its upper-unitriangular and its
lower-triangular parts. -/
theorem exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul (hI : I ≤ Ring.jacobson R)
    {g : GL m R} (hg : g ∈ upperTriangularCongruenceSubgroup m I) :
    ∃ u ∈ upperUnitriangularGroup m R, ((u⁻¹ * g : GL m R) : Matrix m m R).IsLowerTriangular := by
  have := isLocalHom_of_le_jacobson hI
  -- The trailing principal blocks of `g` have unit determinants: modulo `I` they are upper
  -- triangular, with the units `diag I g j` on the diagonal.
  have hblock (i : m) :
      IsUnit ((g : Matrix m m R).toSquareBlockProp fun j ↦ toDual j < toDual i).det :=
    isUnit_det_of_isUpperTriangular_map (f := Ideal.Quotient.mk I) (fun a b hab ↦ by
      rw [map_apply, toSquareBlockProp_def, of_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact mem_upperTriangularCongruenceSubgroup_iff.mp hg hab) fun a ↦ by
      rw [toSquareBlockProp_def, of_apply,
        ← UpperTriangularCongruenceSubgroup.diag_apply_val ⟨g, hg⟩]
      exact Units.isUnit _
  obtain ⟨P, hP, hPg⟩ :=
    exists_blockUnitriangular_mul_blockTriangular (b := toDual) (g : Matrix m m R) hblock
  have hPU : P.IsUpperUnitriangular := (isUpperUnitriangular_iff P).mpr
    ⟨fun _ _ hji ↦ hP.blockTriangular (toDual_lt_toDual.mpr (toDual_lt_toDual.mpr hji)),
      fun i ↦ (hP.apply_of_eq rfl).trans (one_apply_eq i)⟩
  refine ⟨hPU.toGL⁻¹, inv_mem (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hPU), ?_⟩
  rwa [inv_inv, Units.val_mul, hPU.coe_toGL]

end TauCeti
