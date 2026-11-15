/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.CharacterTable.IrreducibleClassification
import TauCeti.RepresentationTheory.Rep.DirectSum.Basic
import TauCeti.RingTheory.Semisimple.Multiplicity
import TauCeti.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Equiv

/-!
# Intrinsic multiplicities of the irreducible representations

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible, and
let `Zᵢ = TauCeti.irreducibleRepresentation k i` be the chosen irreducible representations, one for
each row `i` of the character table. For a representation `ρ` of `G` over `k`, the
**intrinsic multiplicity** of `Zᵢ` in `ρ` is the dimension of the space of intertwining maps from
`Zᵢ` to `ρ`:

`m_ρ(i) = dim_k Hom_G(Zᵢ, ρ)` (`Representation.intrinsicMultiplicity`).

It needs no decomposition of `ρ` to be defined, and a finite-dimensional `ρ` admits a
decomposition with exactly `m_ρ(i)` copies of each `Zᵢ`: it regroups, as a `k[G]`-module, into
`Π₀ i, Fin (m_ρ(i)) → Zᵢ` (`Representation.nonempty_regrouping`). The carrier of `ρ`
may live in any universe, in particular in one other than that of `k`, where the models `Zᵢ` live.

The regrouping decomposes `ρ` into simple submodules (Maschke's theorem makes `k[G]` semisimple)
and identifies each summand with one of the models; this lookup of a simple `k[G]`-module in any
universe is `TauCeti.existsUnique_nonempty_linearEquiv_irreducibleRepresentation`. It then counts
the summands of each class by the multiplicity theorem for semisimple modules, a consequence of
Schur's lemma (`TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`), the models being pairwise
non-isomorphic.

## Main definitions

* `Representation.intrinsicMultiplicity ρ i`: the dimension of `Hom_G(Zᵢ, ρ)`.

## Main results

* `Representation.characterPairing_ofCharacter_irreducibleRepresentation_eq_intrinsicMultiplicity`:
  for finite-dimensional `ρ`, the pairing of the character of `ρ` with the `i`-th irreducible
  character is `(m_ρ(i) : k)`. The equality holds in `k`, so in characteristic `p` it determines
  `m_ρ(i)` only modulo `p`; this is why the multiplicity is defined as a Hom dimension rather
  than as a pairing.
* `FDRep.intrinsicMultiplicity_ρ_eq_finrank_hom`: in `FDRep`, `m_V(i)` is the dimension of the
  space of morphisms `Zᵢ ⟶ V`.
* `Representation.intrinsicMultiplicity_congr`: the multiplicities are invariant under
  equivalences of representations, across carriers in different universes.
* `Representation.intrinsicMultiplicity_prod`, `Representation.intrinsicMultiplicity_directSum`:
  they are additive on binary products (`Representation.prod`) and on finite direct sums
  (`Representation.directSum`) of finite-dimensional representations.
* `Representation.intrinsicMultiplicity_of_subsingleton`: they vanish on the zero representation.
* `Representation.intrinsicMultiplicity_of_isIrreducible`: an irreducible representation has
  multiplicity `1` at its own class and `0` at every other, and in particular
  `TauCeti.intrinsicMultiplicity_irreducibleRepresentation`: `m_{Zⱼ}(i) = δᵢⱼ`.
* `Representation.nonempty_regrouping`: **the regrouping**. A finite-dimensional `ρ` is, as a
  `k[G]`-module, the direct sum of `m_ρ(i)` copies of each `Zᵢ`.
* `Representation.nonempty_equiv_iff_intrinsicMultiplicity_eq`: two finite-dimensional
  representations are equivalent exactly when their intrinsic multiplicities agree.
* `Representation.finrank_eq_sum_intrinsicMultiplicity_mul_characterDegree`: the dimension of
  `ρ` is `∑ᵢ m_ρ(i) · deg Zᵢ`.
* `Representation.character_eq_sum_intrinsicMultiplicity_nsmul`: the character of `ρ` is
  `∑ᵢ m_ρ(i) • χᵢ`.
* `Representation.character_eq_iff_forall_intrinsicMultiplicity_modEq`: in characteristic `p`,
  two finite-dimensional representations have the same character exactly when their
  multiplicities are congruent modulo `p`.
* `Representation.intrinsicMultiplicity_leftRegular`: `Zᵢ` occurs in the left regular
  representation with multiplicity its degree.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Corollaries 2.14–2.18
  and §2.4, formula (2.31).
-/

public section

open Module
open scoped MonoidAlgebra

universe u v w w'

namespace Representation

open TauCeti

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]
variable {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- **The intrinsic multiplicity** of the `i`-th irreducible model `Zᵢ` in a representation `ρ`:
the dimension of the space `Hom_G(Zᵢ, ρ)` of intertwining maps from `Zᵢ` to `ρ`. For
finite-dimensional `ρ` it is the number of copies of `Zᵢ` in `ρ`
(`Representation.nonempty_regrouping`). -/
noncomputable def intrinsicMultiplicity (i : Fin (Nat.card (ConjClasses G))) : ℕ :=
  finrank k (IntertwiningMap (irreducibleRepresentation k i) ρ)

/-- The intrinsic multiplicity is the dimension of the space of intertwining maps from the model. -/
theorem intrinsicMultiplicity_def (i : Fin (Nat.card (ConjClasses G))) :
    ρ.intrinsicMultiplicity i = finrank k (IntertwiningMap (irreducibleRepresentation k i) ρ) :=
  (rfl)

/-- **The character pairing computes the intrinsic multiplicity**: for finite-dimensional `ρ`,
`⟨χ_ρ, χᵢ⟩ = (m_ρ(i) : k)`.
The equality holds in `k`, so in characteristic `p` the pairing determines `m_ρ(i)` only modulo
`p`. -/
theorem characterPairing_ofCharacter_irreducibleRepresentation_eq_intrinsicMultiplicity
    [Fintype G] [FiniteDimensional k V] (i : Fin (Nat.card (ConjClasses G))) :
    ClassFunction.characterPairing (ClassFunction.ofCharacter ρ)
        (ClassFunction.ofCharacter (irreducibleRepresentation k i)) =
      ρ.intrinsicMultiplicity i :=
  ClassFunction.characterPairing_ofCharacter_eq_finrank _ _

/-- **The intrinsic multiplicity counts morphisms of `FDRep`**: for `V : FDRep k G` it is the
dimension of the space of morphisms from the model `Zᵢ` to `V`. -/
theorem _root_.FDRep.intrinsicMultiplicity_ρ_eq_finrank_hom (V : FDRep k G)
    (i : Fin (Nat.card (ConjClasses G))) :
    intrinsicMultiplicity V.ρ i = finrank k (FDRep.of (irreducibleRepresentation k i) ⟶ V) := by
  rw [← ((invariantsEquivIntertwiningMap _ _).symm.trans
    (linHom.invariantsEquivFDRepHom (FDRep.of (irreducibleRepresentation k i)) V)).finrank_eq,
    FDRep.of_ρ', intrinsicMultiplicity_def]

/-- **The zero representation has no multiplicities**: on a subsingleton carrier there are no
nonzero intertwining maps from the models. -/
@[simp, nontriviality]
theorem intrinsicMultiplicity_of_subsingleton [Subsingleton V]
    (i : Fin (Nat.card (ConjClasses G))) : ρ.intrinsicMultiplicity i = 0 := by
  have : Subsingleton (IntertwiningMap (irreducibleRepresentation k i) ρ) :=
    ⟨fun _ _ ↦ IntertwiningMap.ext (Subsingleton.elim _ _)⟩
  rw [intrinsicMultiplicity_def, finrank_zero_of_subsingleton]

variable {ρ} in
/-- **The intrinsic multiplicities are invariant under equivalence**, including transport to a
carrier in another universe: composing with `e` identifies `Hom_G(Zᵢ, ρ)` with `Hom_G(Zᵢ, σ)`. -/
theorem intrinsicMultiplicity_congr {W : Type w'} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.intrinsicMultiplicity = σ.intrinsicMultiplicity := by
  funext i
  exact (IntertwiningMap.equivLinearMapAsModule _ ρ ≪≫ₗ
    LinearEquiv.homCongrRight k (TauCeti.Representation.asModuleLinearEquivOfEquiv e) ≪≫ₗ
    (IntertwiningMap.equivLinearMapAsModule _ σ).symm).finrank_eq

/-- **The intrinsic multiplicities are additive on binary products** (`Representation.prod`) of
finite-dimensional representations. -/
@[simp]
theorem intrinsicMultiplicity_prod [FiniteDimensional k V] {W : Type w'} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (σ : Representation k G W)
    (i : Fin (Nat.card (ConjClasses G))) :
    (ρ.prod σ).intrinsicMultiplicity i =
      ρ.intrinsicMultiplicity i + σ.intrinsicMultiplicity i := by
  rw [intrinsicMultiplicity_def, intrinsicMultiplicity_def, intrinsicMultiplicity_def,
    ← finrank_prod]
  -- `Hom(Zᵢ, ρ × σ)` is `Hom(Zᵢ, ρ) × Hom(Zᵢ, σ)`, computed on the `k[G]`-modules.
  exact (IntertwiningMap.equivLinearMapAsModule _ _ ≪≫ₗ
    LinearEquiv.homCongrRight k (prodAsModuleEquiv ρ σ) ≪≫ₗ (LinearMap.prodEquiv k).symm ≪≫ₗ
    (IntertwiningMap.equivLinearMapAsModule _ _).symm.prodCongr
      (IntertwiningMap.equivLinearMapAsModule _ _).symm).finrank_eq

/-- **The intrinsic multiplicities are additive on finite direct sums**
(`Representation.directSum`) of finite-dimensional representations: an intertwining map into the
direct sum is the family of its components. -/
@[simp]
theorem intrinsicMultiplicity_directSum {ι : Type*} [Fintype ι] {W : ι → Type w'}
    [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)] [∀ j, FiniteDimensional k (W j)]
    (σ : ∀ j, Representation k G (W j)) (i : Fin (Nat.card (ConjClasses G))) :
    (directSum σ).intrinsicMultiplicity i = ∑ j, (σ j).intrinsicMultiplicity i := by
  simp only [intrinsicMultiplicity_def, ← finrank_pi_fintype]
  exact (IntertwiningMap.directSumLinearEquiv _ σ).finrank_eq

open Classical in
/-- **The cross-universe Hom-dimension formula**: an irreducible representation, with carrier in
any universe, has intrinsic multiplicity `1` at the row of the model it is equivalent to and `0` at
every other row. -/
theorem intrinsicMultiplicity_of_isIrreducible [ρ.IsIrreducible]
    (i : Fin (Nat.card (ConjClasses G))) :
    ρ.intrinsicMultiplicity i =
      if Nonempty (ρ.Equiv (irreducibleRepresentation k i)) then 1 else 0 := by
  split_ifs with h
  · rw [intrinsicMultiplicity_congr h.some, intrinsicMultiplicity_def,
      IsIrreducible.finrank_intertwiningMap_self]
  · have : IsEmpty ((irreducibleRepresentation k i).Equiv ρ) := ⟨fun e ↦ h ⟨e.symm⟩⟩
    rw [intrinsicMultiplicity_def, finrank_zero_of_subsingleton]

/-- **The multiplicities of the models are a Kronecker delta**: `m_{Zⱼ}(i) = δᵢⱼ`. -/
@[simp]
theorem _root_.TauCeti.intrinsicMultiplicity_irreducibleRepresentation
    (i j : Fin (Nat.card (ConjClasses G))) :
    (irreducibleRepresentation k j).intrinsicMultiplicity i = if i = j then 1 else 0 := by
  classical
  rw [intrinsicMultiplicity_of_isIrreducible]
  exact if_congr ((TauCeti.Representation.nonempty_equiv_iff_eq _
    (pairwise_isEmpty_equiv_irreducibleRepresentation k)).trans eq_comm) rfl rfl

/-- **The regrouping.** A finite-dimensional representation `ρ` is, as a `k[G]`-module, the direct
sum of `m_ρ(i)` copies of the model `Zᵢ` over the rows `i` of the character table. The carrier of
`ρ` may lie in any universe. Choosing such an equivalence amounts to choosing bases of the
multiplicity spaces, so only its existence is intrinsic. -/
theorem nonempty_regrouping [FiniteDimensional k V] :
    Nonempty (ρ.asModule ≃ₗ[k[G]]
      Π₀ i, Fin (ρ.intrinsicMultiplicity i) → (irreducibleRepresentation k i).asModule) := by
  classical
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  have : Module.Finite k[G] ρ.asModule := .of_restrictScalars_finite k k[G] ρ.asModule
  -- Decompose `ρ` into simple submodules and identify each with a model.
  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp k[G] ρ.asModule
  choose c f using fun j ↦
    have := hS j
    (existsUnique_nonempty_linearEquiv_irreducibleRepresentation k G (S j)).exists
  let E : ρ.asModule ≃ₗ[k[G]] Π j, (irreducibleRepresentation k (c j)).asModule :=
    e ≪≫ₗ DFinsupp.mapRange.linearEquiv (fun j ↦ (f j).some) ≪≫ₗ
      DFinsupp.linearEquivFunOnFintype
  -- Count the summands in each class by the multiplicity theorem.
  have hcount (i) : Fintype.card {j // c j = i} = ρ.intrinsicMultiplicity i := by
    rw [intrinsicMultiplicity_def, (IntertwiningMap.equivLinearMapAsModule _ _).finrank_eq,
      finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) E, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun j ↦ ?_)
    rw [← TauCeti.Representation.nonempty_equiv_iff,
      TauCeti.Representation.nonempty_equiv_iff_eq _
        (pairwise_isEmpty_equiv_irreducibleRepresentation k), eq_comm]
  -- Regroup the summands by class.
  exact ⟨E ≪≫ₗ LinearEquiv.piCongrLeft k[G] (fun s ↦ (irreducibleRepresentation k s.1).asModule)
      (Equiv.sigmaFiberEquiv c).symm ≪≫ₗ
    LinearEquiv.piCurry k[G] (fun i _ ↦ (irreducibleRepresentation k i).asModule) ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦ LinearEquiv.funCongrLeft k[G] _
      (Fintype.equivFinOfCardEq (hcount i)).symm) ≪≫ₗ
    DFinsupp.linearEquivFunOnFintype.symm⟩

variable {ρ} in
/-- **Finite-dimensional representations are classified by their intrinsic multiplicities**,
in every characteristic not dividing `|G|` and across carrier universes: `ρ` and `σ` are
equivalent exactly when `m_ρ(i) = m_σ(i)` for every row `i`. -/
theorem nonempty_equiv_iff_intrinsicMultiplicity_eq [FiniteDimensional k V] {W : Type w'}
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {σ : Representation k G W} :
    Nonempty (ρ.Equiv σ) ↔ ρ.intrinsicMultiplicity = σ.intrinsicMultiplicity := by
  refine ⟨fun ⟨e⟩ ↦ intrinsicMultiplicity_congr e, fun h ↦ ?_⟩
  obtain ⟨eρ⟩ := ρ.nonempty_regrouping
  obtain ⟨eσ⟩ := σ.nonempty_regrouping
  rw [h] at eρ
  exact TauCeti.Representation.nonempty_equiv_iff.mpr ⟨eρ ≪≫ₗ eσ.symm⟩

/-- **The dimension formula**: a finite-dimensional representation has dimension
`∑ᵢ m_ρ(i) · deg Zᵢ`. -/
theorem finrank_eq_sum_intrinsicMultiplicity_mul_characterDegree [FiniteDimensional k V] :
    finrank k V = ∑ i, ρ.intrinsicMultiplicity i * characterDegree k i := by
  classical
  obtain ⟨e⟩ := ρ.nonempty_regrouping
  rw [← ρ.asModuleEquiv.finrank_eq, (e.restrictScalars k).finrank_eq,
    (DFinsupp.linearEquivFunOnFintype (R := k)).finrank_eq, finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    (irreducibleRepresentation k i).asModuleEquiv.finrank_eq, finrank_fin_fun]

/-- **The character expansion**: the character of a finite-dimensional representation is
`∑ᵢ m_ρ(i) • χᵢ`. This is `TauCeti.character_eq_sum_nsmul_irreducibleCharacter` with the
coefficients written as intrinsic multiplicities, for carriers in any universe. -/
theorem character_eq_sum_intrinsicMultiplicity_nsmul [FiniteDimensional k V] :
    ρ.character = ∑ i, ρ.intrinsicMultiplicity i • irreducibleCharacter k i := by
  have : Fintype G := Fintype.ofFinite G
  funext g
  have h := ClassFunction.apply_eq_sum_characterPairing_mul_character
    (irreducibleRepresentation k) (pairwise_isEmpty_equiv_irreducibleRepresentation k)
    (by simp) (ClassFunction.ofCharacter ρ) g
  rw [ClassFunction.ofCharacter_apply] at h
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ClassFunction.characterPairing_symm,
    characterPairing_ofCharacter_irreducibleRepresentation_eq_intrinsicMultiplicity,
    Pi.smul_apply, nsmul_eq_mul, character_irreducibleRepresentation]

/-- **Characters determine multiplicities modulo the characteristic.** In characteristic `p`
(not dividing `|G|`), two finite-dimensional representations have the same character exactly when
their intrinsic multiplicities are congruent modulo `p`. For `p = 0` this says that the character
determines the multiplicities; for `p > 0` the congruence cannot be sharpened to equality, since
`p` copies of a representation have the zero character. -/
theorem character_eq_iff_forall_intrinsicMultiplicity_modEq (p : ℕ) [CharP k p]
    [FiniteDimensional k V] {W : Type w'} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W) :
    ρ.character = σ.character ↔
      ∀ i, ρ.intrinsicMultiplicity i ≡ σ.intrinsicMultiplicity i [MOD p] := by
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rw [← CharP.natCast_eq_natCast k p,
      ← characterPairing_ofCharacter_irreducibleRepresentation_eq_intrinsicMultiplicity,
      ← characterPairing_ofCharacter_irreducibleRepresentation_eq_intrinsicMultiplicity]
    exact congrArg (ClassFunction.characterPairing · _)
      (Subtype.ext (funext fun g ↦ by simpa using congrFun h g))
  · rw [character_eq_sum_intrinsicMultiplicity_nsmul, character_eq_sum_intrinsicMultiplicity_nsmul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Nat.cast_smul_eq_nsmul k, ← Nat.cast_smul_eq_nsmul k,
      (CharP.natCast_eq_natCast k p).mpr (h i)]

/-- **The regular multiplicity**: the `i`-th irreducible representation occurs in the left regular
representation `k[G]` with multiplicity its degree, in every characteristic not dividing `|G|`. -/
@[simp]
theorem intrinsicMultiplicity_leftRegular (i : Fin (Nat.card (ConjClasses G))) :
    (leftRegular k G).intrinsicMultiplicity i = characterDegree k i := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  rw [intrinsicMultiplicity_def, finrank_intertwiningMap_comm,
    (leftRegularMapEquiv (irreducibleRepresentation k i)).finrank_eq, finrank_fin_fun]

end Representation
