/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.AbelianLayer
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.Existence

/-!
# The local class-field correspondence

For a nonarchimedean local field `K`, finite abelian extensions inside its separable closure are
determined by their norm subgroups. Combined with local existence, this identifies the abelian
open normal subgroups of the absolute Galois group with the open finite-index subgroups of `Kˣ`.
The subgroup correspondence is order preserving; after taking fixed fields it becomes the usual
order-reversing local class-field correspondence.

In characteristic zero the correspondence includes every finite-index subgroup of `Kˣ`. In
arbitrary characteristic it is restricted to subgroups whose index is prime to the residue
characteristic. This restriction records exactly the range supplied by Kummer theory, without
asserting the excluded `p`-primary equal-characteristic existence theorem.

## Main definitions

* `TauCeti.ClassFieldTheory.LocalNormSubgroups`: open finite-index subgroups of `Kˣ`.
* `TauCeti.ClassFieldTheory.localClassField`: the abelian layer attached to such a subgroup in
  characteristic zero.
* `TauCeti.ClassFieldTheory.localClassFieldCorrespondence`: the order isomorphism between norm
  subgroups and finite abelian layers in characteristic zero.
* `TauCeti.ClassFieldTheory.localClassFieldCorrespondencePrimeToResidueCharacteristic`: the
  corresponding order isomorphism in the prime-to-residue-characteristic range.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §§5–6.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer
open _root_.ValuativeRel

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Uniqueness -/

/-- For finite abelian local layers, inclusion of norm subgroups is equivalent to inclusion of
the layer subgroups. On fixed fields the latter inclusion is reversed. -/
theorem localNormSubgroup_le_iff_of_isAbelian
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : V.IsAbelianClassFieldLayer) (hW : W.IsAbelianClassFieldLayer) :
    localNormSubgroup K V ≤ localNormSubgroup K W ↔ V ≤ W := by
  refine ⟨fun h ↦ ?_, fun h ↦ localNormSubgroup_mono K h⟩
  have hinf : localNormSubgroup K (V ⊓ W) = localNormSubgroup K V := by
    rw [localNormSubgroup_inf_of_isAbelian hV hW, inf_eq_left.mpr h]
  have hdegree : (ofOpenNormal (V ⊓ W)).degree = (ofOpenNormal V).degree := by
    rw [← index_localNormSubgroup (K := K) (hV.inf hW), hinf,
      index_localNormSubgroup (K := K) hV]
  have hindex : (V ⊓ W).toSubgroup.index = V.toSubgroup.index := by
    simpa only [NormalLayer.degree_eq_relIndex, NormalLayer.top_ofOpenNormal,
      NormalLayer.ground_ofOpenNormal, OpenSubgroup.toSubgroup_top,
      Subgroup.relIndex_top_right] using hdegree
  have hle : (V ⊓ W).toSubgroup ≤ V.toSubgroup := by
    exact fun _ hx ↦ (inf_le_left : V ⊓ W ≤ V) hx
  have heq : (V ⊓ W).toSubgroup = V.toSubgroup := by
    rcases hle.lt_or_eq with hlt | heq
    · exact False.elim ((Subgroup.index_strictAnti hlt).ne hindex.symm)
    · exact heq
  rw [← OpenNormalSubgroup.toSubgroup_injective heq]
  exact inf_le_right

/-- **Uniqueness of finite abelian local class fields.** Two abelian layers of a
nonarchimedean local field with the same norm subgroup are equal. The abelianity hypotheses are
essential: norm limitation identifies the norm subgroup of every layer with that of its maximal
abelian sublayer. -/
theorem localClassField_unique
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : V.IsAbelianClassFieldLayer) (hW : W.IsAbelianClassFieldLayer)
    (h : localNormSubgroup K V = localNormSubgroup K W) :
    V = W := by
  exact le_antisymm
    ((localNormSubgroup_le_iff_of_isAbelian hV hW).1 h.le)
    ((localNormSubgroup_le_iff_of_isAbelian hW hV).1 h.ge)

/-! ### The full correspondence in characteristic zero -/

/-- The source of the local class-field correspondence: open subgroups of finite index in `Kˣ`. -/
abbrev LocalNormSubgroups (K : Type) [Field K] [TopologicalSpace K] : Type :=
  {N : OpenSubgroup Kˣ // N.toSubgroup.FiniteIndex}

/-- The norm subgroup of a finite layer, bundled as an open finite-index subgroup of `Kˣ`. -/
def localNormOpenSubgroup
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    LocalNormSubgroups K :=
  ⟨⟨localNormSubgroup K V, isOpen_localNormSubgroup K V⟩,
    finiteIndex_localNormSubgroup K V⟩

/-- The subgroup underlying `localNormOpenSubgroup` is the norm subgroup of the layer. -/
@[simp]
theorem localNormOpenSubgroup_toSubgroup
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (localNormOpenSubgroup K V).1.toSubgroup = localNormSubgroup K V :=
  (rfl)

/-- In characteristic zero, an open finite-index subgroup of `Kˣ` is the norm subgroup of a
finite abelian layer. This is the bundled form used to define its class field. -/
theorem exists_localClassField [CharZero K] (N : LocalNormSubgroups K) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      V.IsAbelianClassFieldLayer ∧ localNormSubgroup K V = N.1.toSubgroup := by
  let _ := N.2
  exact localAbelianExistence N.1.toSubgroup

/-- **The local class field attached to `N`.** In characteristic zero this is the unique finite
abelian layer whose norm subgroup is `N`. -/
def localClassField [CharZero K] (N : LocalNormSubgroups K) :
    AbelianLayer (AbsoluteGaloisGroup K) :=
  ⟨(exists_localClassField N).choose, (exists_localClassField N).choose_spec.1⟩

/-- The norm subgroup of the local class field attached to `N` is `N`. -/
@[simp]
theorem localClassField_normSubgroup [CharZero K] (N : LocalNormSubgroups K) :
    localNormSubgroup K (localClassField N).1 = N.1.toSubgroup :=
  (exists_localClassField N).choose_spec.2

/-- The subgroup order in the local class-field correspondence is preserved: a larger norm
subgroup corresponds to a larger subgroup of the absolute Galois group. -/
theorem localClassField_le_iff [CharZero K] (N₁ N₂ : LocalNormSubgroups K) :
    N₁ ≤ N₂ ↔ (localClassField N₁).1 ≤ (localClassField N₂).1 := by
  rw [← localNormSubgroup_le_iff_of_isAbelian (localClassField N₁).2
    (localClassField N₂).2, localClassField_normSubgroup, localClassField_normSubgroup]
  rfl

/-- On fixed fields, the local class-field correspondence reverses inclusions. -/
theorem localClassField_orderReversing [CharZero K] (N₁ N₂ : LocalNormSubgroups K) :
    N₁ ≤ N₂ ↔
      classField K (localClassField N₂).1 ≤ classField K (localClassField N₁).1 :=
  (localClassField_le_iff N₁ N₂).trans
    (classField_le_classField_iff K (localClassField N₁).1 (localClassField N₂).1).symm

/-- **The local class-field correspondence in characteristic zero.** It identifies open
finite-index subgroups of `Kˣ` with finite abelian layers. Read through `classField`, it is the
usual order-reversing correspondence with finite abelian extensions. -/
def localClassFieldCorrespondence [CharZero K] :
    LocalNormSubgroups K ≃o AbelianLayer (AbsoluteGaloisGroup K) where
  toFun := localClassField
  invFun V := localNormOpenSubgroup K V.1
  left_inv N := by
    apply Subtype.ext
    exact OpenSubgroup.toSubgroup_injective (localClassField_normSubgroup N)
  right_inv V := by
    apply Subtype.ext
    exact localClassField_unique (localClassField (localNormOpenSubgroup K V.1)).2 V.2
      (localClassField_normSubgroup (localNormOpenSubgroup K V.1))
  map_rel_iff' := fun {N₁ N₂} ↦ (localClassField_le_iff N₁ N₂).symm

/-- The characteristic-zero correspondence sends `N` to its local class field. -/
@[simp]
theorem localClassFieldCorrespondence_apply [CharZero K] (N : LocalNormSubgroups K) :
    localClassFieldCorrespondence N = localClassField N := by
  unfold localClassFieldCorrespondence
  rfl

/-- The inverse of the characteristic-zero correspondence sends a layer to its norm subgroup. -/
@[simp]
theorem localClassFieldCorrespondence_symm_apply [CharZero K]
    (V : AbelianLayer (AbsoluteGaloisGroup K)) :
    localClassFieldCorrespondence.symm V = localNormOpenSubgroup K V.1 := by
  unfold localClassFieldCorrespondence
  rfl

/-- The Galois group of the class field attached to `N` is canonically `Kˣ/N`. -/
def localClassFieldGaloisEquiv [CharZero K] (N : LocalNormSubgroups K) :
    Kˣ ⧸ N.1.toSubgroup ≃* (ofOpenNormal (localClassField N).1).Gal :=
  (QuotientGroup.quotientMulEquivOfEq (localClassField_normSubgroup N).symm).trans
    (localAbelianGaloisEquiv K (localClassField N).2)

/-- `localClassFieldGaloisEquiv` sends the class of `x` to its Artin symbol. -/
@[simp]
theorem localClassFieldGaloisEquiv_mk [CharZero K] (N : LocalNormSubgroups K) (x : Kˣ) :
    localClassFieldGaloisEquiv N (QuotientGroup.mk x) =
      localAbelianArtinHom K (localClassField N).2 x := by
  rw [localClassFieldGaloisEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, localAbelianGaloisEquiv_mk]

/-- The index of `N` is the degree of its local class field. -/
theorem localClassField_index [CharZero K] (N : LocalNormSubgroups K) :
    N.1.toSubgroup.index = (ofOpenNormal (localClassField N).1).degree := by
  rw [← index_localNormSubgroup (K := K) (localClassField N).2,
    localClassField_normSubgroup]

/-! ### The prime-to-residue-characteristic correspondence -/

/-- Open finite-index subgroups of `Kˣ` whose index is prime to `p`. -/
abbrev LocalNormSubgroupsPrimeTo
    (K : Type) [Field K] [TopologicalSpace K] (p : ℕ) : Type :=
  {N : LocalNormSubgroups K // N.1.toSubgroup.index.Coprime p}

/-- Finite abelian layers whose degree is prime to `p`. -/
abbrev AbelianLayerPrimeTo
    (K : Type) [Field K] (p : ℕ) : Type :=
  {V : AbelianLayer (AbsoluteGaloisGroup K) // (ofOpenNormal V.1).degree.Coprime p}

/-- Prime-to-residue-characteristic local existence on the bundled carriers. -/
theorem exists_localClassField_primeToResidueCharacteristic
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] (N : LocalNormSubgroupsPrimeTo K p) :
    ∃ V : AbelianLayerPrimeTo K p,
      localNormSubgroup K V.1.1 = N.1.1.toSubgroup := by
  obtain ⟨V, hV, hN⟩ :=
    localAbelianExistence_primeToResidueCharacteristic p N.1.1.toSubgroup N.2
  refine ⟨⟨⟨V, hV⟩, ?_⟩, hN⟩
  rw [← index_localNormSubgroup (K := K) hV, hN]
  exact N.2

/-- The local class field attached to a prime-to-`p` norm subgroup. -/
def localClassFieldPrimeToResidueCharacteristic
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] (N : LocalNormSubgroupsPrimeTo K p) :
    AbelianLayerPrimeTo K p :=
  (exists_localClassField_primeToResidueCharacteristic p N).choose

/-- The prime-to-`p` local class field has the prescribed norm subgroup. -/
@[simp]
theorem localClassFieldPrimeToResidueCharacteristic_normSubgroup
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] (N : LocalNormSubgroupsPrimeTo K p) :
    localNormSubgroup K (localClassFieldPrimeToResidueCharacteristic p N).1.1 =
      N.1.1.toSubgroup :=
  (exists_localClassField_primeToResidueCharacteristic p N).choose_spec

/-- The prime-to-`p` local class-field assignment preserves the subgroup order. -/
theorem localClassFieldPrimeToResidueCharacteristic_le_iff
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p]
    (N₁ N₂ : LocalNormSubgroupsPrimeTo K p) :
    N₁ ≤ N₂ ↔
      (localClassFieldPrimeToResidueCharacteristic p N₁).1.1 ≤
        (localClassFieldPrimeToResidueCharacteristic p N₂).1.1 := by
  rw [← localNormSubgroup_le_iff_of_isAbelian
    (localClassFieldPrimeToResidueCharacteristic p N₁).1.2
    (localClassFieldPrimeToResidueCharacteristic p N₂).1.2,
    localClassFieldPrimeToResidueCharacteristic_normSubgroup,
    localClassFieldPrimeToResidueCharacteristic_normSubgroup]
  rfl

/-- **The prime-to-residue-characteristic local class-field correspondence.** This is the full
range available in equal characteristic without Artin–Schreier–Witt theory. -/
def localClassFieldCorrespondencePrimeToResidueCharacteristic
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] :
    LocalNormSubgroupsPrimeTo K p ≃o AbelianLayerPrimeTo K p where
  toFun := localClassFieldPrimeToResidueCharacteristic p
  invFun V := ⟨localNormOpenSubgroup K V.1.1, by
    rw [localNormOpenSubgroup_toSubgroup, index_localNormSubgroup (K := K) V.1.2]
    exact V.2⟩
  left_inv N := by
    apply Subtype.ext
    apply Subtype.ext
    exact OpenSubgroup.toSubgroup_injective
      (localClassFieldPrimeToResidueCharacteristic_normSubgroup p N)
  right_inv V := by
    apply Subtype.ext
    apply Subtype.ext
    exact localClassField_unique
      (localClassFieldPrimeToResidueCharacteristic p ⟨localNormOpenSubgroup K V.1.1, by
        rw [localNormOpenSubgroup_toSubgroup, index_localNormSubgroup (K := K) V.1.2]
        exact V.2⟩).1.2
      V.1.2
      (localClassFieldPrimeToResidueCharacteristic_normSubgroup p _)
  map_rel_iff' := fun {N₁ N₂} ↦
    (localClassFieldPrimeToResidueCharacteristic_le_iff p N₁ N₂).symm

/-- The prime-to-residue-characteristic correspondence sends `N` to its local class field. -/
@[simp]
theorem localClassFieldCorrespondencePrimeToResidueCharacteristic_apply
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] (N : LocalNormSubgroupsPrimeTo K p) :
    localClassFieldCorrespondencePrimeToResidueCharacteristic p N =
      localClassFieldPrimeToResidueCharacteristic p N := by
  unfold localClassFieldCorrespondencePrimeToResidueCharacteristic
  rfl

/-- The inverse of the prime-to-residue-characteristic correspondence sends a layer to its norm
subgroup. -/
@[simp]
theorem localClassFieldCorrespondencePrimeToResidueCharacteristic_symm_apply_coe
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] (V : AbelianLayerPrimeTo K p) :
    ((localClassFieldCorrespondencePrimeToResidueCharacteristic (K := K) p).symm V).1 =
      localNormOpenSubgroup K V.1.1 := by
  unfold localClassFieldCorrespondencePrimeToResidueCharacteristic
  rfl

/-- On fixed fields, the prime-to-residue-characteristic correspondence reverses inclusions. -/
theorem localClassFieldPrimeToResidueCharacteristic_orderReversing
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p]
    (N₁ N₂ : LocalNormSubgroupsPrimeTo K p) :
    N₁ ≤ N₂ ↔
      classField K (localClassFieldPrimeToResidueCharacteristic p N₂).1.1 ≤
        classField K (localClassFieldPrimeToResidueCharacteristic p N₁).1.1 :=
  (localClassFieldPrimeToResidueCharacteristic_le_iff p N₁ N₂).trans
    (classField_le_classField_iff K
      (localClassFieldPrimeToResidueCharacteristic p N₁).1.1
      (localClassFieldPrimeToResidueCharacteristic p N₂).1.1).symm

end TauCeti.ClassFieldTheory
