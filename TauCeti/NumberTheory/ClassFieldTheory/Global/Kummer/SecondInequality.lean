/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The second inequality inside an S-unit Kummer field

Let `K` contain the `p`-th roots of unity, let `S` contain the places above the prime `p`
and generate the ideal class group, and put `M = K(U_S^{1/p})`. For every intermediate field
`L` of `M/K`, the idele-class norm index divides `[L : K]`, and in particular is at most
`[L : K]`.

The auxiliary places give a subgroup `E_{S,T}` contained in the norm group with
`p ^ #T = [M : L]`. Its computed index satisfies
`[C_K : E_{S,T}] * p ^ #T = p ^ (#S + #S∞) = [M : K]`.
The tower law therefore identifies its index with `[L : K]`. This proves the second
inequality without using global reciprocity or the global class formation. When `L/K` is
cyclic, the first inequality gives equality, and the auxiliary subgroup is the whole norm
group.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6, proof of the second inequality.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §6.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E]

/-- **An auxiliary Kummer subgroup of index `[L : K]` contained in the norm group.**
Here `L` is any intermediate field of `K(U_S^{1/p})`, with `S` containing the places above
`p` and generating the ideal class group. -/
theorem exists_auxiliaryKummerIdeleClassSubgroup_index_eq_finrank
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) [NumberField L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      (auxiliaryKummerIdeleClassSubgroup S T p).index = Module.finrank K L ∧
      auxiliaryKummerIdeleClassSubgroup S T p ≤
        (GlobalNumberFields.ideleClassNormMap K L).range := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : HasEnoughRootsOfUnity K p :=
    hasEnoughRootsOfUnity_of_isPrimitiveRoot
      (hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K))
  obtain ⟨T, hST, hcard, hsurj, hnorm⟩ :=
    exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap hp S hpS hζ hroots L
  have hindex := index_auxiliaryKummerIdeleClassSubgroup_mul_pow_card hp hST hcl hpS hsurj
  have hdegree : Module.finrank K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) =
      p ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [finrank_kummerField hroots, relIndex_range_powMonoidHom_sUnits_numberField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.add_comm]
  refine ⟨T, Finset.disjoint_coe.1 hST, ?_, hnorm⟩
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos T.card)
  rw [hindex, hcard, Module.finrank_mul_finrank, hdegree]

/-- **The second fundamental inequality inside an S-unit Kummer field**, in divisibility form:
for `L ⊆ K(U_S^{1/p})`, the idele-class norm index divides `[L : K]`. -/
theorem index_range_ideleClassNormMap_dvd_finrank_of_le_kummerField_sUnits
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) [NumberField L] :
    (GlobalNumberFields.ideleClassNormMap K L).range.index ∣ Module.finrank K L := by
  obtain ⟨T, _, hindex, hnorm⟩ :=
    exists_auxiliaryKummerIdeleClassSubgroup_index_eq_finrank hp S hcl hpS hζ hroots L
  exact hindex ▸ Subgroup.index_dvd_of_le hnorm

/-- **The cyclic norm index inside an S-unit Kummer field.** Combining the two fundamental
inequalities gives `[C_K : N_{L/K}(C_L)] = [L : K]` for a cyclic intermediate field
`L ⊆ K(U_S^{1/p})`, without invoking global reciprocity. -/
theorem index_range_ideleClassNormMap_eq_finrank_of_le_kummerField_sUnits
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)))
    [NumberField L] [IsCyclic Gal(L/K)] :
    (GlobalNumberFields.ideleClassNormMap K L).range.index = Module.finrank K L := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : HasEnoughRootsOfUnity K p :=
    hasEnoughRootsOfUnity_of_isPrimitiveRoot
      (hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K))
  -- These instances give `IsGalois K L` via `isAbelianGalois_kummerField`.
  exact le_antisymm
    (Nat.le_of_dvd Module.finrank_pos
      (index_range_ideleClassNormMap_dvd_finrank_of_le_kummerField_sUnits
        hp S hcl hpS hζ hroots L))
    (finrank_le_index_range_ideleClassNormMap K L)

end TauCeti.ClassFieldTheory
