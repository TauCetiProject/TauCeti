/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindDomain.Kummer.SelmerGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.NumberField

/-!
# Finiteness of the Kummer classes unramified outside `S`

Over a Dedekind domain with finite residue fields, the classes of `H¹(G_K, μₙ)` unramified outside
`S` are the Kummer classes of the Selmer group `K(S, n)` once `S` contains the primes dividing `n`
(`TauCeti.mem_unramifiedOutsideKummerCohomology_iff_exists`). For a number field `K` and a finite
`S`, the group `K(S, n)` is finite by the finiteness of the class group and Dirichlet's unit
theorem (`IsDedekindDomain.finite_selmerGroup_of_numberField`), so the classes of `H¹(G_K, μₙ)`
unramified outside `S` form a finite group (`TauCeti.finite_unramifiedOutsideKummerCohomology`).
This is the Kummer-theoretic step in the finiteness of the Selmer groups of an elliptic curve over
a number field: over a field containing the `n`-torsion, the Weil pairing reduces
`H¹(G_K, E[n])` to copies of `H¹(G_K, μₙ)`, and the Selmer classes land in the classes unramified
outside the primes of bad reduction and those dividing `n`.

## Main results

* `TauCeti.finite_unramifiedOutsideKummerCohomology`: over a number field and for finite `S`, there
  are finitely many classes unramified outside `S`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1, the proof of
  Proposition VIII.1.6, and X.4.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]
  {τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)}
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

/-- **Finiteness of the Kummer classes unramified outside `S`.** Over a number field `K`, if `n` is
invertible in `K` and `S` is a finite set of finite places, only finitely many classes of
`H¹(G_K, μₙ)` are unramified outside `S`. This follows by enlarging `S` by the finitely many places
dividing `n`, where the classes are the Kummer classes of the finite group `K(S, n)`. -/
theorem finite_unramifiedOutsideKummerCohomology (hSf : S.Finite) (hn : IsUnit (n : K)) :
    Finite (unramifiedOutsideKummerCohomology τ S n) := by
  have : NeZero n := ⟨fun h ↦ by simp [h] at hn⟩
  let T := S ∪ {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}
  have hdiv : {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}.Finite :=
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one (R := 𝓞 K) hn.ne_zero).subset <| by
      intro v hv
      exact ne_of_lt ((v.valuation_lt_one_iff_mem (K := K) (n : 𝓞 K)).2 hv)
  have hTf : T.Finite := hSf.union hdiv
  have hT : ∀ v ∉ T, (n : 𝓞 K) ∉ v.asIdeal := by
    intro v hvT hvn
    exact hvT (Set.mem_union_right S hvn)
  have hfinT : Finite (unramifiedOutsideKummerCohomology τ T n) := by
    have := finite_selmerGroup_of_numberField K T n hTf
    -- the Kummer map descends to the power classes, and every class is the image of `K(T, n)`
    let f := (kummerClassMap K n hn).comp
      (QuotientGroup.quotientMulEquivOfEq
        (powerSubgroup_eq_range_powMonoidHom Kˣ n).symm).toMonoidHom
    refine Set.Finite.to_subtype ((Set.finite_range fun x : selmerGroup (R := 𝓞 K) (K := K)
      (S := T) (n := n) ↦ (f x).toAdd).subset fun c hc ↦ ?_)
    obtain ⟨a, ha, rfl⟩ :=
      (mem_unramifiedOutsideKummerCohomology_iff_exists hn hT).1 hc
    exact ⟨⟨_, ha⟩, by
      simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        QuotientGroup.quotientMulEquivOfEq_mk, kummerClassMap_mk]⟩
  refine @Finite.of_injective _ _ hfinT
    (fun c : unramifiedOutsideKummerCohomology τ S n =>
      (⟨c, ?_⟩ : unramifiedOutsideKummerCohomology τ T n)) ?_
  · rw [mem_unramifiedOutsideKummerCohomology_iff]
    have hc := c.property
    rw [mem_unramifiedOutsideKummerCohomology_iff] at hc
    intro v hvT
    exact hc v fun hvS ↦ hvT (Set.mem_union_left _ hvS)
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun c : unramifiedOutsideKummerCohomology τ T n =>
      (c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n))) hab

end TauCeti
