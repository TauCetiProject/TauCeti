/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Tilting bound on kernel lengths of linear combinations over a DVR

Let `O` be a discrete valuation ring, `I` an ideal of `O` such that `O ⧸ I` is Artinian, and
`evγ, evφ : B →ₗ[O] m → O ⧸ I` two `O`-linear maps into a finite product of copies of `O ⧸ I`.
For any submodule `C : Submodule O B`, there is a list `bad` of at most `Fintype.card m` elements
of the residue field `IsLocalRing.ResidueField O` such that for every `a : O` whose residue avoids
`bad`, the kernel of `a • evγ - evφ` on `C` has length at most that of
`C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ` (`TauCeti.exists_list_length_ker_smul_sub_le`). In
particular, whenever `Fintype.card m < ENat.card (IsLocalRing.ResidueField O)`, such a scalar
`a : O` exists (`TauCeti.exists_length_ker_smul_sub_le`).

## Main results

* `TauCeti.exists_list_length_ker_smul_sub_le`: outside at most `Fintype.card m` residue classes,
  the kernel of `a • evγ - evφ` on `C` is no longer than `C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ`.
* `TauCeti.exists_length_ker_smul_sub_le`: existence of such a scalar `a : O` whenever the
  residue field has strictly more than `Fintype.card m` elements.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Congruences/Selmer/Descent.lean`, declaration `New.Selmer.tilting`, stated over an
arbitrary discrete valuation ring `O` with an `ENat.card` existence corollary.
-/

public section

namespace TauCeti

open Module IsLocalRing LinearMap Submodule

/-- For any linear map `f : B →ₗ[R] N` and submodule `C : Submodule R B`, the lengths of
`C.map f` and `C ⊓ f.ker` add up to the length of `C`. -/
theorem length_map_add_length_inf_ker {R B N : Type*} [Ring R] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N] (f : B →ₗ[R] N) (C : Submodule R B) :
    Module.length R (C.map f) + Module.length R ↥(C ⊓ f.ker) = Module.length R C := by
  have heq : Module.length R ↥(C ⊓ f.ker) = Module.length R (LinearMap.ker (f.submoduleMap C)) :=
    LinearEquiv.length_eq
      { toFun := fun x ↦ ⟨⟨x.val, x.property.left⟩, Subtype.ext x.property.right⟩
        invFun := fun x ↦ ⟨x.val.val, x.val.property, congrArg Subtype.val x.property⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  rw [heq, add_comm]
  exact (Module.length_eq_add_of_exact (LinearMap.ker (f.submoduleMap C)).subtype
    (f.submoduleMap C) (Submodule.injective_subtype _) (f.submoduleMap_surjective C)
    (LinearMap.exact_subtype_ker_map _)).symm

/-- **Tilting lemma.** Let `evγ, evφ : B →ₗ[O] m → O ⧸ I` be linear maps over a discrete valuation
ring `O` with `O ⧸ I` Artinian, and let `C : Submodule O B`. Outside at most `Fintype.card m`
residue classes in `ResidueField O`, the kernel of `a • evγ - evφ` on `C` has length at most that
of `C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ`. -/
theorem exists_list_length_ker_smul_sub_le {O m B : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Fintype m] [AddCommGroup B] [Module O B] {I : Ideal O}
    [IsArtinian O (O ⧸ I)] (evγ evφ : B →ₗ[O] m → O ⧸ I) (C : Submodule O B) :
    ∃ bad : List (ResidueField O),
      bad.length ≤ Fintype.card m ∧
      ∀ a : O, residue O a ∉ bad →
        Module.length O ↥(C ⊓ (a • evγ - evφ).ker) ≤
          Module.length O ↥(C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ) := by
  let C' : Submodule O B := ⨆ a : O, C ⊓ (a • evγ - evφ).ker
  have hC' : C' ≤ C := by simp [C']
  have h_image : C' ≤ (C'.map evγ).comap evφ := iSup_le fun a z ⟨hzC, hz_ker⟩ ↦
    ⟨a • z, C'.smul_mem a (mem_iSup_of_mem a ⟨hzC, hz_ker⟩), by simpa [sub_eq_zero] using hz_ker⟩
  let Λ : Submodule O (m → O) := (C'.map evγ).comap (I.mkQ.compLeft m)
  let π : Λ →ₗ[O] C'.map evγ := (I.mkQ.compLeft m).submoduleComap (C'.map evγ)
  have hπ : Function.Surjective π :=
    submoduleComap_surjective_of_surjective _ _ I.mkQ_surjective.comp_left
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (evγ.submoduleMap C') π
    (evγ.submoduleMap_surjective C')
  obtain ⟨U, hU⟩ := Module.projective_lifting_property π (evφ.restrict h_image ∘ₗ σ) hπ
  refine ⟨(U.charpoly.aroots (ResidueField O)).toList, ?_, fun a ha ↦ ?_⟩
  · grw [Multiset.length_toList, Polynomial.card_roots_map_le_natDegree,
      LinearMap.charpoly_natDegree, Submodule.finrank_le, Module.finrank_pi]
  have h_bij : Function.Bijective (algebraMap O (Λ →ₗ[O] Λ) a - U) := by
    have h_unit : IsUnit (U.charpoly.eval a) := by
      simpa [Polynomial.map_monic_ne_zero, LinearMap.charpoly_monic] using ha
    rwa [LinearMap.eval_charpoly, ← LinearMap.isUnit_iff_isUnit_det,
      Module.End.isUnit_iff] at h_unit
  have h_map : C'.map evγ ≤ C'.map (a • evγ - evφ) := fun x hx ↦ by
    obtain ⟨u, hu⟩ := hπ.comp h_bij.surjective ⟨x, hx⟩
    have h1 : evγ (σ u) = π u := congrArg Subtype.val (LinearMap.congr_fun hσ u)
    have h2 : π (U u) = evφ (σ u) := congrArg Subtype.val (LinearMap.congr_fun hU u)
    exact ⟨σ u, (σ u).property, by simpa [h1, h2] using congrArg Subtype.val hu⟩
  have h_ker : C' ⊓ evγ.ker ≤ C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ :=
    le_inf (inf_le_inf_right _ hC') (inf_le_left.trans (h_image.trans (comap_mono (map_mono hC'))))
  have h_le : C ⊓ (a • evγ - evφ).ker ≤ C' ⊓ (a • evγ - evφ).ker :=
    le_inf (le_iSup (fun t : O ↦ C ⊓ (t • evγ - evφ).ker) a) inf_le_right
  refine (ENat.add_le_add_iff_left (k := Module.length O (C'.map (a • evγ - evφ)))
    Module.length_ne_top).mp ?_
  calc Module.length O (C'.map (a • evγ - evφ)) + Module.length O ↥(C ⊓ (a • evγ - evφ).ker)
    _ ≤ Module.length O (C'.map (a • evγ - evφ)) + Module.length O ↥(C' ⊓ (a • evγ - evφ).ker) :=
      add_le_add_right (Module.length_le_of_injective _ (Submodule.inclusion_injective h_le)) _
    _ = Module.length O (C'.map evγ) + Module.length O ↥(C' ⊓ evγ.ker) := by
      rw [length_map_add_length_inf_ker, length_map_add_length_inf_ker]
    _ ≤ Module.length O (C'.map (a • evγ - evφ)) +
          Module.length O ↥(C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ) :=
      add_le_add (Module.length_le_of_injective _ (Submodule.inclusion_injective h_map))
        (Module.length_le_of_injective _ (Submodule.inclusion_injective h_ker))

/-- Under the hypotheses of `exists_list_length_ker_smul_sub_le`, if the residue field has
strictly more than `Fintype.card m` elements, then there exists `a : O` whose kernel length on `C`
is bounded by `Module.length O ↥(C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ)`. -/
theorem exists_length_ker_smul_sub_le {O m B : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Fintype m] [AddCommGroup B] [Module O B] {I : Ideal O}
    [IsArtinian O (O ⧸ I)] (evγ evφ : B →ₗ[O] m → O ⧸ I) (C : Submodule O B)
    (hcard : (Fintype.card m : ENat) < ENat.card (ResidueField O)) :
    ∃ a : O, Module.length O ↥(C ⊓ (a • evγ - evφ).ker) ≤
      Module.length O ↥(C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ) := by
  classical
  obtain ⟨bad, hlen, hbad⟩ := exists_list_length_ker_smul_sub_le evγ evφ C
  have hlt : (bad.toFinset.card : ENat) < ENat.card (ResidueField O) :=
    lt_of_le_of_lt (Nat.cast_le.mpr (bad.toFinset_card_le.trans hlen)) hcard
  have hne : (bad.toFinset : Set (ResidueField O)) ≠ Set.univ := by
    intro huniv
    have h_eq : (bad.toFinset.card : ENat) = ENat.card (ResidueField O) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, huniv, Set.encard_univ]
    exact hlt.ne h_eq
  obtain ⟨r, hr⟩ := Set.nonempty_compl.mpr hne
  obtain ⟨a, rfl⟩ := residue_surjective r
  exact ⟨a, hbad a (by simpa using hr)⟩

end TauCeti
