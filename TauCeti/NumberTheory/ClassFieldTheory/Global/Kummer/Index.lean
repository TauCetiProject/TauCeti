/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
import TauCeti.GroupTheory.Index.Map

/-!
# Principal units in the Kummer idele index

Let `E` be the Kummer idele subgroup and `I_S` the group of `S`-ideles. When the primes in `S`
generate the ideal class group, the index of the image of `E` in the idele class group, multiplied
by the index of the principal `S`-units that belong to `E`, is exactly `[I_S : E]`.

The latter index is the product of the local power-class counts. This identity isolates the
principal-unit contribution needed to compare the Kummer idele-class index with the degree of a
Kummer extension. It does not assume that a principal idele which is locally an `n`-th power at
`S` is globally an `n`-th power.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §§5 and 9.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- **The exact Kummer idele-class index formula.** If the primes in `S` generate the ideal
class group, the idele-class index multiplied by the relative index of the principal `S`-units
satisfying the local power conditions equals the product of local power-class counts.
No finiteness or roots-of-unity hypothesis is required; infinite indices are recorded as zero. -/
theorem index_kummerIdeleClassSubgroup_mul_relIndex (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ)
    (hS : Subgroup.closure
      (HeightOneSpectrum.classGroupMk (R := 𝓞 K) '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤) :
    (kummerIdeleClassSubgroup S n).index *
      ((kummerIdeleSubgroup S n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      (∏ v : S, Nat.card ((v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  let J := kummerIdeleSubgroup S 1
  let E := (kummerIdeleSubgroup S n).subgroupOf J
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let f : J →* IdeleClassGroup (𝓞 K) K := q.comp J.subtype
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact (kummerIdeleClassSubgroup_def S 1).symm.trans
      (kummerIdeleClassSubgroup_one_eq_top S hS)
  have hmap : E.map f = kummerIdeleClassSubgroup S n := by
    dsimp only [E, f, J]
    rw [kummerIdeleClassSubgroup_def, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    exact congrArg (Subgroup.map _) (inf_eq_left.mpr (kummerIdeleSubgroup_le_one S n))
  have hker : f.ker.map J.subtype = IdeleGroup.principalSubgroup (𝓞 K) K ⊓ J := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.map_comap_eq,
      Subgroup.range_subtype, inf_comm]
  have hprincipal : E.relIndex f.ker =
      ((kummerIdeleSubgroup S n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) := by
    -- `E` is the pullback to the subtype of `S`-ideles, as in `Subgroup.subgroupOf`.
    dsimp only [E, Subgroup.subgroupOf]
    rw [Subgroup.relIndex_comap, hker, ← comap_unitEmbedding_kummerIdeleSubgroup_one,
      Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_comm]
  have hmul := TauCeti.subgroup_index_map_mul_relIndex_ker E f hf
  rw [hmap, hprincipal] at hmul
  exact hmul.trans (relIndex_kummerIdeleSubgroup S n)

/-- If the classes of `S` generate the ideal class group, the index of the Kummer idele class
subgroup divides the product of the local power-class counts. -/
theorem index_kummerIdeleClassSubgroup_dvd (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hS : Subgroup.closure
      (HeightOneSpectrum.classGroupMk (R := 𝓞 K) '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤) :
    (kummerIdeleClassSubgroup S n).index ∣
      (∏ v : S, Nat.card ((v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) :=
  Dvd.intro _ (index_kummerIdeleClassSubgroup_mul_relIndex S n hS)

end TauCeti.ClassFieldTheory
