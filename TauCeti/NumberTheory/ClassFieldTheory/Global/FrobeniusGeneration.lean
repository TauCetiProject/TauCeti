/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The Frobenius elements generate the Galois group of a solvable extension

Let `L/K` be a Galois extension of number fields and `S` a finite set of finite places of `K`.
If `Gal(L/K)` is solvable, the arithmetic Frobenius elements at the places of `L` above the finite
places of `K` outside `S` generate `Gal(L/K)` (`closure_isArithFrobAt_eq_top`). If moreover
almost every finite place of `K` has a place of `L` above it with trivial decomposition group,
then `L = K` (`finrank_eq_one_of_stabilizer_eq_bot`): a nontrivial solvable extension has
infinitely many places that do not split completely.

Both statements are proved without the Chebotarev density theorem. If either failed, the fixed
field of a normal subgroup of prime index containing the relevant decomposition groups would be
a cyclic extension `E/K` of prime degree from which every idele class is a norm
(`exists_finrank_prime_ideleClassNormMap_surjective_of_closure_isArithFrobAt_ne_top` and
`exists_finrank_prime_ideleClassNormMap_surjective_of_stabilizer_eq_bot`, in the namespace
`TauCeti.GlobalNumberFields`).
The first fundamental inequality `[C_K : N_{E/K}(C_E)] ≥ [E : K]` excludes such a field
(`finrank_eq_one_of_surjective_ideleClassNormMap`).

The Kummer-theoretic proof of the second fundamental inequality uses the generation statement
for an extension `M/L` inside a tower `K ⊆ L ⊆ M`, with the excluded places given as places of
the ground field `K`: the Frobenius elements of `M/L` at the places of `M` above the finite places
of `K` outside `S` generate `Gal(M/L)` (`closure_isArithFrobAt_eq_top_tower`). A Frobenius basis
of `Gal(M/L)` is then extracted from them
(`NumberField.exists_finset_closure_artinElementAway_eq_range_restrictScalarsHom`).

## Main results

* `TauCeti.ClassFieldTheory.closure_isArithFrobAt_eq_top`: the Frobenius elements at the places
  outside a finite set generate the Galois group of a solvable extension of number fields.
* `TauCeti.ClassFieldTheory.closure_isArithFrobAt_eq_top_tower`: the same statement for `M/L` in a
  tower `K ⊆ L ⊆ M`, with the excluded set given by places of `K`.
* `TauCeti.ClassFieldTheory.finrank_eq_one_of_stabilizer_eq_bot`: a solvable extension in which
  almost every place has a place above it with trivial decomposition group is trivial.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 4.6 and Proposition 4.7.
-/

public section

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped Pointwise

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A Galois subextension of prime degree of an extension of number fields has an idele-class norm
map that is not surjective: it is cyclic, so the first fundamental inequality applies. -/
private theorem not_surjective_ideleClassNormMap_of_finrank_prime {E : IntermediateField K L}
    [IsGalois K E] (hE : (Module.finrank K E).Prime) :
    ¬ Function.Surjective (ideleClassNormMap K E) := by
  intro hsurj
  have : Fact (Module.finrank K E).Prime := ⟨hE⟩
  have : IsCyclic Gal(E/K) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K E)
  exact hE.ne_one (finrank_eq_one_of_surjective_ideleClassNormMap K E hsurj)

/-- **The Frobenius elements generate the Galois group** (Milne VII, Proposition 4.7). Let `L/K` be
a Galois extension of number fields and `S` a finite set of finite places of `K`. If the quotient
of `Gal(L/K)` by the normal closure of the arithmetic Frobenius elements at the places of `L` above
the finite places of `K` outside `S` is solvable, for instance if `L/K` is solvable, then these
Frobenius elements generate `Gal(L/K)`. -/
theorem closure_isArithFrobAt_eq_top [IsGalois K L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    [Group.IsSolvable ((L ≃ₐ[K] L) ⧸ Subgroup.normalClosure {σ : L ≃ₐ[K] L | ∃ v ∉ S,
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 K) σ w.1.asIdeal})] :
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v ∉ S,
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 K) σ w.1.asIdeal} = ⊤ := by
  by_contra hgen
  obtain ⟨E, _, hE, hsurj⟩ :=
    exists_finrank_prime_ideleClassNormMap_surjective_of_closure_isArithFrobAt_ne_top S hgen
  exact not_surjective_ideleClassNormMap_of_finrank_prime hE hsurj

/-- **A solvable extension that splits almost everywhere is trivial** (Milne VII,
Proposition 4.6). Let `L/K` be a Galois extension of number fields with solvable Galois group. If
every finite place `v` of `K` outside a finite set `S` has a place `w` of `L` above it with trivial
decomposition group, then `[L : K] = 1`, that is, `L = K`. -/
theorem finrank_eq_one_of_stabilizer_eq_bot [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal = ⊥) :
    Module.finrank K L = 1 := by
  refine (Nat.eq_or_lt_of_le Module.finrank_pos).elim Eq.symm fun hL ↦ ?_
  obtain ⟨E, _, hE, hsurj⟩ :=
    exists_finrank_prime_ideleClassNormMap_surjective_of_stabilizer_eq_bot hL S hS
  exact (not_surjective_ideleClassNormMap_of_finrank_prime hE hsurj).elim

variable {M : Type} [Field M] [NumberField M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

omit [NumberField K] in
/-- **The Frobenius elements generate the Galois group of the top of a tower.** Let `K ⊆ L ⊆ M` be
a tower of fields with `L` and `M` number fields and `M/L` Galois and solvable, and let `S` be a
finite set of finite places of `K`. Then
`Gal(M/L)` is generated by its arithmetic Frobenius elements at the places of `M` above the finite
places of `K` outside `S`.

This is `closure_isArithFrobAt_eq_top` for `M/L`, applied to the places of `L` above `S`. -/
theorem closure_isArithFrobAt_eq_top_tower [IsGalois L M] [Group.IsSolvable (M ≃ₐ[L] M)]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup.closure {τ : M ≃ₐ[L] M | ∃ v ∉ S,
      ∃ Q : {Q : HeightOneSpectrum (𝓞 M) // Q.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 L) τ Q.1.asIdeal} = ⊤ := by
  -- The places of `L` above `S`.
  let SL : Finset (HeightOneSpectrum (𝓞 L)) :=
    (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 L) S.finite_toSet).toFinset
  refine eq_top_mono (Subgroup.closure_mono ?_) (closure_isArithFrobAt_eq_top SL)
  -- A Frobenius element at a place `Q` above a place `w ∉ SL` of `L` is one at a place above
  -- the contraction of `w` to `K`, which lies outside `S`.
  rintro τ ⟨w, hw, Q, hτ⟩
  have : Q.1.asIdeal.LiesOver w.asIdeal := Q.2
  refine ⟨w.under (𝓞 K), fun h ↦ hw ?_,
    ⟨Q.1, Ideal.LiesOver.trans Q.1.asIdeal w.asIdeal (w.under (𝓞 K)).asIdeal⟩, hτ⟩
  simpa [SL] using h

end TauCeti.ClassFieldTheory
