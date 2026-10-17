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

Let `E` be the auxiliary Kummer idele subgroup and `I` the group of `(S ∪ T)`-ideles. When the
primes in `S ∪ T` generate the ideal class group, the index of the image of `E` in the idele
class group, multiplied by the index of the principal `(S ∪ T)`-units that belong to `E`, is
exactly `[I : E]`.

The latter index is the product of the local power-class counts. This identity isolates the
principal-unit contribution needed to compare the Kummer idele-class index with the degree of a
Kummer extension. It does not assume that a principal idele which is locally an `n`-th power at
`S` is globally an `n`-th power.

The arithmetic input is the existence of `(S ∪ T)`-idele representatives. The remaining
factorization is the image-index formula for a surjective group homomorphism, with the principal
ideles accounting for its kernel.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §§5 and 9.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- **The exact Kummer idele-class index formula.** If the primes in `S ∪ T` generate the
ideal class group, the idele-class index multiplied by the relative index of the principal
`(S ∪ T)`-units satisfying the local power conditions equals the product of local power-class
counts.
No finiteness or roots-of-unity hypothesis is required; infinite indices are recorded as zero. -/
theorem index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K))))) = ⊤) :
    (auxiliaryKummerIdeleClassSubgroup S T n).index *
      ((auxiliaryKummerIdeleSubgroup S T n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
        (((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K) =
      (∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  let J := auxiliaryKummerIdeleSubgroup S T 1
  let E := (auxiliaryKummerIdeleSubgroup S T n).subgroupOf J
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let f : J →* IdeleClassGroup (𝓞 K) K := q.comp J.subtype
  have hf : Function.Surjective f := auxiliaryKummerIdeleSubgroup_mk_surjective S T hST
  have hmap : E.map f = auxiliaryKummerIdeleClassSubgroup S T n :=
    map_subgroupOf_auxiliaryKummerIdeleSubgroup S T n
  have hker : f.ker.map J.subtype = IdeleGroup.principalSubgroup (𝓞 K) K ⊓ J := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.map_comap_eq,
      Subgroup.range_subtype, inf_comm]
  have hprincipal : E.relIndex f.ker =
      ((auxiliaryKummerIdeleSubgroup S T n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
        (((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K) := by
    -- `E` is the pullback to the subtype of `(S ∪ T)`-ideles, as in `Subgroup.subgroupOf`.
    dsimp only [E, Subgroup.subgroupOf]
    rw [Subgroup.relIndex_comap, hker, ← comap_unitEmbedding_auxiliaryKummerIdeleSubgroup_one,
      Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_comm]
  have hmul := TauCeti.subgroup_index_map_mul_relIndex_ker E f hf
  rw [hmap, hprincipal] at hmul
  exact hmul.trans (relIndex_auxiliaryKummerIdeleSubgroup S T n)

end TauCeti.ClassFieldTheory
