/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.OfModule

/-!
# Intrinsic multiplicities of the irreducible representations

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible, and
let `Zᵢ = TauCeti.irreducibleRepresentation k i` be the chosen irreducible representations, one for
each row `i` of the character table. For a representation `ρ` of `G` over `k`, the
**intrinsic multiplicity** of `Zᵢ` in `ρ` is the dimension of the space of intertwining maps from
`Zᵢ` to `ρ`:

`m_ρ(i) = dim_k Hom_G(Zᵢ, ρ)` (`Representation.intrinsicMultiplicity`).

It needs no decomposition of `ρ` to be defined, and it is the number of copies of `Zᵢ` in every
decomposition of a finite-dimensional `ρ` into irreducibles: `ρ` regroups, as a `k[G]`-module, into
exactly `m_ρ(i)` copies of each `Zᵢ` (`Representation.nonempty_regrouping`). The carrier of `ρ`
may live in any universe, in particular in one other than that of `k`, where the models `Zᵢ` live.

The regrouping decomposes `ρ` into simple submodules (Maschke's theorem makes `k[G]` semisimple)
and identifies each summand with one of the models; this lookup of a simple `k[G]`-module in any
universe is `TauCeti.existsUnique_nonempty_linearEquiv_irreducibleRepresentation`. It then counts
the summands of each class by Schur's lemma: `Hom_G(Zⱼ, Zᵢ)` is `k` when `i = j` and zero otherwise
(`Representation.intrinsicMultiplicity_irreducibleRepresentation`).

## Main definitions

* `Representation.intrinsicMultiplicity ρ i`: the dimension of `Hom_G(Zᵢ, ρ)`.

## Main results

* `Representation.characterPairing_ofCharacter_irreducibleRepresentation`: the pairing of the
  character of `ρ` with the `i`-th irreducible character is `m_ρ(i)`.
* `FDRep.intrinsicMultiplicity_ρ_eq_finrank_hom`: in `FDRep`, `m_V(i)` is the dimension of the
  space of morphisms `Zᵢ ⟶ V`.
* `Representation.intrinsicMultiplicity_congr`: the multiplicities are invariant under
  equivalences of representations, across carriers in different universes.
* `Representation.intrinsicMultiplicity_prod`: they are additive on direct sums.
* `Representation.intrinsicMultiplicity_of_isIrreducible`: an irreducible representation has
  multiplicity `1` at its own class and `0` at every other, and in particular
  `Representation.intrinsicMultiplicity_irreducibleRepresentation`: `m_{Zⱼ}(i) = δᵢⱼ`.
* `TauCeti.existsUnique_nonempty_linearEquiv_irreducibleRepresentation`: every simple
  `k[G]`-module, in any universe, is isomorphic to `Zᵢ` for exactly one `i`.
* `Representation.nonempty_regrouping`: **the regrouping**. A finite-dimensional `ρ` is, as a
  `k[G]`-module, the direct sum of `m_ρ(i)` copies of each `Zᵢ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Corollary 2.16 and
  §2.4, formula (2.31).
-/

public section

open Module
open scoped MonoidAlgebra

universe u v w w'

namespace TauCeti

variable (k : Type u) {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]

/-- **Every simple `k[G]`-module is one of the chosen irreducible models**, and only one: for a
simple `k[G]`-module `N` whose `k`-module structure is the restricted one, there is exactly one row
`i` of the character table with `N ≅ Zᵢ` as `k[G]`-modules. The module `N` may lie in any universe,
not only in that of `k`. -/
theorem existsUnique_nonempty_linearEquiv_irreducibleRepresentation (N : Type w) [AddCommGroup N]
    [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] [IsSimpleModule k[G] N] :
    ∃! i : Fin (Nat.card (ConjClasses G)),
      Nonempty (N ≃ₗ[k[G]] (irreducibleRepresentation k i).asModule) := by
  have : (_root_.Representation.ofModule' (k := k) (G := G) N).IsIrreducible :=
    (Representation.isIrreducible_ofModule'_iff N).mpr inferInstance
  obtain ⟨i, ⟨φ⟩⟩ := ClassFunction.exists_nonempty_equiv (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)
    (_root_.Representation.ofModule' (k := k) (G := G) N)
  refine ⟨i, ⟨(Representation.ofModule'AsModuleEquiv N).symm ≪≫ₗ
    Representation.asModuleLinearEquivOfEquiv φ⟩, fun j ⟨e⟩ ↦ ?_⟩
  by_contra hji
  exact (pairwise_isEmpty_equiv_irreducibleRepresentation k hji).elim
    (Representation.equivOfAsModuleLinearEquiv (e.symm ≪≫ₗ
      (Representation.ofModule'AsModuleEquiv N).symm ≪≫ₗ
      Representation.asModuleLinearEquivOfEquiv φ))

end TauCeti

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

/-- **The character pairing computes the intrinsic multiplicity**: `⟨χ_ρ, χᵢ⟩ = m_ρ(i)`. -/
theorem characterPairing_ofCharacter_irreducibleRepresentation [Fintype G]
    [FiniteDimensional k V] (i : Fin (Nat.card (ConjClasses G))) :
    ClassFunction.characterPairing (ClassFunction.ofCharacter ρ)
        (ClassFunction.ofCharacter (irreducibleRepresentation k i)) =
      ρ.intrinsicMultiplicity i :=
  ClassFunction.characterPairing_ofCharacter_eq_finrank _ _

/-- **The intrinsic multiplicity counts morphisms of `FDRep`**: for `V : FDRep k G` it is the
dimension of the space of morphisms from the model `Zᵢ` to `V`. -/
theorem _root_.FDRep.intrinsicMultiplicity_ρ_eq_finrank_hom (V : FDRep k G)
    (i : Fin (Nat.card (ConjClasses G))) :
    intrinsicMultiplicity V.ρ i = finrank k (FDRep.of (irreducibleRepresentation k i) ⟶ V) :=
  ((invariantsEquivIntertwiningMap _ _).symm.trans
    (linHom.invariantsEquivFDRepHom (FDRep.of _) V)).finrank_eq

/-- The intrinsic multiplicity computed with the arguments of `Hom` exchanged, as the dimension of
the `k[G]`-linear maps from `ρ` to `Zᵢ`. The two directions agree by Maschke's theorem. -/
private theorem intrinsicMultiplicity_eq_finrank_linearMap [FiniteDimensional k V]
    (i : Fin (Nat.card (ConjClasses G))) :
    ρ.intrinsicMultiplicity i =
      finrank k (ρ.asModule →ₗ[k[G]] (irreducibleRepresentation k i).asModule) := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  rw [intrinsicMultiplicity_def, finrank_intertwiningMap_comm,
    (IntertwiningMap.equivLinearMapAsModule _ _).finrank_eq]

/-- **The intrinsic multiplicities are invariant under equivalence**, including transport to a
carrier in another universe: composing with `e` identifies `Hom_G(Zᵢ, ρ)` with `Hom_G(Zᵢ, σ)`. -/
theorem intrinsicMultiplicity_congr {W : Type w'} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.intrinsicMultiplicity = σ.intrinsicMultiplicity := by
  funext i
  exact (LinearEquiv.ofLinearMap (IntertwiningMap.llcomp _ ρ σ e.toIntertwiningMap)
    (IntertwiningMap.llcomp _ σ ρ e.symm.toIntertwiningMap)
    (by ext f v; simp [← IntertwiningMap.comp_def])
    (by ext f v; simp [← IntertwiningMap.comp_def])).finrank_eq

/-- **The intrinsic multiplicities are additive on direct sums.** -/
@[simp]
theorem intrinsicMultiplicity_prod [FiniteDimensional k V] {W : Type w'} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (σ : Representation k G W)
    (i : Fin (Nat.card (ConjClasses G))) :
    (ρ.prod σ).intrinsicMultiplicity i =
      ρ.intrinsicMultiplicity i + σ.intrinsicMultiplicity i := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  rw [intrinsicMultiplicity_eq_finrank_linearMap, intrinsicMultiplicity_def,
    intrinsicMultiplicity_def, finrank_intertwiningMap_comm _ ρ,
    finrank_intertwiningMap_comm _ σ, ← finrank_prod]
  -- `Hom(ρ × σ, Zᵢ)` is `Hom(ρ, Zᵢ) × Hom(σ, Zᵢ)`, computed on the `k[G]`-modules.
  exact ((LinearEquiv.congrLeft _ k (prodAsModuleEquiv ρ σ)).trans
    ((LinearMap.coprodEquiv k).symm.trans
      ((IntertwiningMap.equivLinearMapAsModule _ _).symm.prodCongr
        (IntertwiningMap.equivLinearMapAsModule _ _).symm))).finrank_eq

open Classical in
/-- **The cross-universe Hom-dimension formula**: an irreducible representation, with carrier in
any universe, has intrinsic multiplicity `1` at the row of the model it is equivalent to and `0` at
every other row. -/
theorem intrinsicMultiplicity_of_isIrreducible [ρ.IsIrreducible]
    (i : Fin (Nat.card (ConjClasses G))) :
    ρ.intrinsicMultiplicity i =
      if Nonempty (ρ.Equiv (irreducibleRepresentation k i)) then 1 else 0 := by
  split_ifs with h
  · rw [intrinsicMultiplicity_congr ρ h.some, intrinsicMultiplicity_def,
      IsIrreducible.finrank_intertwiningMap_self]
  · have : IsEmpty ((irreducibleRepresentation k i).Equiv ρ) := ⟨fun e ↦ h ⟨e.symm⟩⟩
    rw [intrinsicMultiplicity_def, finrank_zero_of_subsingleton]

/-- **The multiplicities of the models are a Kronecker delta**: `m_{Zⱼ}(i) = δᵢⱼ`. -/
@[simp]
theorem intrinsicMultiplicity_irreducibleRepresentation (i j : Fin (Nat.card (ConjClasses G))) :
    (irreducibleRepresentation k j).intrinsicMultiplicity i = if i = j then 1 else 0 := by
  classical
  rw [intrinsicMultiplicity_of_isIrreducible]
  refine if_congr ⟨fun ⟨e⟩ ↦ by_contra fun hij ↦ ?_, fun h ↦ by subst h; exact ⟨Equiv.refl _⟩⟩
    rfl rfl
  exact (pairwise_isEmpty_equiv_irreducibleRepresentation k (Ne.symm hij)).elim e

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
    (existsUnique_nonempty_linearEquiv_irreducibleRepresentation (G := G) k (S j)).exists
  let E : ρ.asModule ≃ₗ[k[G]] Π j, (irreducibleRepresentation k (c j)).asModule :=
    e ≪≫ₗ DFinsupp.mapRange.linearEquiv (fun j ↦ (f j).some) ≪≫ₗ
      DFinsupp.linearEquivFunOnFintype
  -- Count the summands in each class by Schur's lemma.
  have hcount (i) : Fintype.card {j // c j = i} = ρ.intrinsicMultiplicity i := by
    rw [intrinsicMultiplicity_eq_finrank_linearMap, (LinearEquiv.congrLeft _ k E).finrank_eq,
      ← (LinearMap.lsum k[G] (fun j ↦ (irreducibleRepresentation k (c j)).asModule) k
        (M := (irreducibleRepresentation k i).asModule)).finrank_eq,
      (LinearEquiv.piCongrRight fun j ↦ (IntertwiningMap.equivLinearMapAsModule
        (irreducibleRepresentation k (c j)) (irreducibleRepresentation k i)).symm).finrank_eq,
      finrank_pi_fintype]
    simp_rw [← intrinsicMultiplicity_def, intrinsicMultiplicity_irreducibleRepresentation,
      Finset.sum_boole, Fintype.card_subtype]
    simp [eq_comm]
  -- Regroup the summands by class.
  exact ⟨E ≪≫ₗ LinearEquiv.piCongrLeft k[G] (fun s ↦ (irreducibleRepresentation k s.1).asModule)
      (Equiv.sigmaFiberEquiv c).symm ≪≫ₗ
    LinearEquiv.piCurry k[G] (fun i _ ↦ (irreducibleRepresentation k i).asModule) ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦ LinearEquiv.funCongrLeft k[G] _
      (Fintype.equivFinOfCardEq (hcount i)).symm) ≪≫ₗ
    DFinsupp.linearEquivFunOnFintype.symm⟩

end Representation
