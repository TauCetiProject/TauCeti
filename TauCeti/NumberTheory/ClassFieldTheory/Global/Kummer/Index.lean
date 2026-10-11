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

/-- The principal ideles lying in the `S`-ideles are precisely the principal `S`-units. -/
@[simp]
theorem comap_unitEmbedding_kummerIdeleSubgroup_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (kummerIdeleSubgroup S 1).comap (IdeleGroup.unitEmbedding (𝓞 K) K) =
      (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
  ext a
  exact (mem_kummerIdeleSubgroup_one_iff S _).trans
    (IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff a)

/-- If the classes of the primes in `S` generate the ideal class group, every idele class has
an `S`-idele representative. -/
@[simp]
theorem kummerIdeleClassSubgroup_one_eq_top (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : Subgroup.closure
      (HeightOneSpectrum.classGroupMk (R := 𝓞 K) '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤) :
    kummerIdeleClassSubgroup S 1 = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨x, hx, hc⟩ := IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq hS c
  exact (mem_kummerIdeleClassSubgroup_iff S 1 c).2
    ⟨x, (mem_kummerIdeleSubgroup_one_iff S x).2 hx, hc⟩

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
  have hmul := E.index_map_mul_relIndex_ker f hf
  rw [hmap, hprincipal] at hmul
  exact hmul.trans (relIndex_kummerIdeleSubgroup S n)

end TauCeti.ClassFieldTheory
