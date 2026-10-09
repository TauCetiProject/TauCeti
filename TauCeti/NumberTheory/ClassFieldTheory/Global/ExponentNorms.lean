/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

/-!
# Idele norms from a Galois extension of exponent `n`

Let `L/K` be a finite Galois extension of number fields such that `n` kills `Gal(L/K)`, for
instance a Kummer extension `K(Δ^{1/n})` of a field containing the `n`-th roots of unity. This
file shows that the ideles of the following shape are norms of ideles of `L`:

```text
∏_{v ∈ S} (K_vˣ)ⁿ × ∏_{v ∈ T} K_vˣ × ∏_{v ∉ S ∪ T} 𝒪_vˣ × ∏_{v ∣ ∞} (K_vˣ)ⁿ,
```

where `L/K` is unramified at the finite places outside `S ∪ T` and the places of `T` split
completely in `L`. By the placewise criterion `GlobalNumberFields.mem_range_ideleNormMap_iff` it is
enough to treat one place at a time.

* At a finite place, the local Galois group `Gal(L_w/K_v)` is the decomposition group of `w`, a
  subgroup of `Gal(L/K)`, so `n` kills it, and local reciprocity makes every `n`-th power a norm
  (`powerSubgroup_le_normGroup_of_exponent_dvd`).
* At an infinite place, the local degree `[L_w : K_v]` is the order of the decomposition group,
  which is `1` or `2`; that group is cyclic, so its order divides `n` and every `n`-th power is a
  power of `a ^ [L_w : K_v] = N_{L_w/K_v}(a)` (`TauCeti.pow_mem_range_normUnits_completion`).
* At a place outside `S ∪ T`, units are norms from the unramified completions
  (`TauCeti.exists_unit_preimages_of_isUnramifiedAt`).
* At a place of local degree one, every element is a norm
  (`TauCeti.mem_range_normUnits_adicCompletion_of_finrank_eq_one`).

This is the inclusion of the "Kummer idele subgroup" in the norms of the Kummer extension, the
norm half of the computation of the norm index of a Kummer extension through `S`-units in the
proof of the second fundamental inequality and of global existence.

## Main results

* `TauCeti.ClassFieldTheory.pow_mem_range_normUnits_adicCompletion`: at a finite place every
  `n`-th power is a local norm.
* `TauCeti.ClassFieldTheory.mem_range_ideleNormMap_of_exponent_dvd`: the ideles displayed above
  are idele norms from `L`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §5 (the second inequality through
  Kummer theory) and §9 (the existence theorem).
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **`n`-th powers are local norms at a finite place.** If `n` kills `Gal(L/K)`, then every
`n`-th power of `K_vˣ` is a norm from the local étale algebra `K_v ⊗[K] L`: the local Galois group
at a place above `v` is a decomposition group, so `n` kills it too, and local reciprocity applies.
-/
theorem pow_mem_range_normUnits_adicCompletion {n : ℕ} (hn : Monoid.exponent Gal(L/K) ∣ n)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    a ^ n ∈ (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range := by
  classical
  let : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨P, hP.isPrime, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := hPv
  have hloc :
      Monoid.exponent (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) ∣ n :=
    (Monoid.exponent_dvd_of_monoidHom
      ((Subgroup.subtype _).comp (decompositionEquiv v w).symm.toMonoidHom)
      (Subtype.val_injective.comp (decompositionEquiv v w).symm.injective)).trans hn
  obtain ⟨b, hb⟩ := mem_normGroup_iff.1 <| powerSubgroup_le_normGroup_of_exponent_dvd
    (v.adicCompletion K) (w.adicCompletion L) hloc ((mem_powerSubgroup_iff n).2 ⟨a, rfl⟩)
  rw [mem_range_normUnits_adicCompletion_iff]
  refine ⟨Pi.mulSingle ⟨w, hw⟩ b, ?_⟩
  rw [finprod_eq_single _ ⟨w, hw⟩ fun w' hw' ↦ by simp [Pi.mulSingle_eq_of_ne hw']]
  ext
  simp [hb]

/-- **Idele norms from a Galois extension of exponent `n`.** Let `L/K` be a finite Galois
extension of number fields such that `n` kills `Gal(L/K)`. Let `S` and `T` be sets of finite
places of `K` such that each place of `T` has a completion of `L` above it of degree one, and each
finite place outside `S ∪ T` has an unramified place of `L` above it. Then an idele of `K` is the
norm of an idele of `L` as soon as its coordinates are `n`-th powers at the places of `S` and at
the infinite places, and units at the finite places outside `S ∪ T`. -/
theorem mem_range_ideleNormMap_of_exponent_dvd {n : ℕ} (hn : Monoid.exponent Gal(L/K) ∣ n)
    {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T → ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal)
    {x : IdeleGroup (𝓞 K) K}
    (hxS : ∀ v ∈ S, v.ideleFiniteCoord x ∈ powerSubgroup _ n)
    (hxU : ∀ v ∉ S, v ∉ T → Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1)
    (hxinf : ∀ v : InfinitePlace K, v.ideleInfiniteCoord x ∈ powerSubgroup _ n) :
    x ∈ (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  refine (GlobalNumberFields.mem_range_ideleNormMap_iff K L x).2 ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · by_cases hvS : v ∈ S
    · obtain ⟨y, hy⟩ := (mem_powerSubgroup_iff n).1 (hxS v hvS)
      exact hy ▸ pow_mem_range_normUnits_adicCompletion K L hn v y
    by_cases hvT : v ∈ T
    · exact mem_range_normUnits_adicCompletion_of_finrank_eq_one K L v (hT v hvT) _
    · obtain ⟨u, hu, -⟩ := exists_unit_preimages_of_isUnramifiedAt K L v _ (hxU v hvS hvT)
        (hU v hvS hvT)
      exact (mem_range_normUnits_adicCompletion_iff K L v _).2 ⟨u, hu⟩
  · obtain ⟨y, hy⟩ := (mem_powerSubgroup_iff n).1 (hxinf v)
    exact hy ▸ pow_mem_range_normUnits_completion K L hn v y

end TauCeti.ClassFieldTheory
