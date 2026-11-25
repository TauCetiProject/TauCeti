/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import TauCeti.NumberTheory.RamificationInertia.Splitting

/-!
# Complete splitting at Frobenius-generating primes forces linear disjointness

Let `D / K` be a finite Galois extension of number fields and let `T` be a set of primes of `𝓞 K`
whose arithmetic Frobenius elements, taken at all primes of `𝓞 D` above `T`, generate
`Gal(D/K)`. If every prime of `T` splits completely in a finite extension `E / K`, then
`E ∩ D = K`, and so `E` and `D` are linearly disjoint over `K`.

The reason is that a prime `p` splits completely in an intermediate field `F` of `D / K` exactly
when every decomposition group above `p` fixes `F`
(`Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le`), and an arithmetic Frobenius
at `Q` lies in the decomposition group of `Q`. So every Frobenius element at a prime above a prime
that splits completely in `F` fixes `F`; when these elements generate the whole Galois group,
`F = K`. For `E` not inside `D`, the field `E ∩ D` is a subextension of `E`, and complete
splitting descends to it (`Ideal.ncard_primesOver_eq_finrank_tower_bot`).

No unramifiedness is assumed: at a ramified prime the arithmetic Frobenius elements still lie in
the decomposition group. Generators of the whole group are needed. For `D = ℚ(√2, √3)` over `ℚ`,
primes whose Frobenius elements lie in the subgroup fixing `√6` may all split completely in
`ℚ(√6)`, which meets `D` nontrivially.

This is the first step in the construction of soluble extensions of a number field with
prescribed completions, and in the linear disjointness refinement of Moret-Bailly's theorem:
there, finitely many primes whose Frobenius classes generate `Gal(D/K)` are added to the set of
primes at which complete splitting is imposed.

## Main results

* `IsArithFrobAt.mem_fixingSubgroup_of_ncard_primesOver_eq_finrank`: an arithmetic Frobenius at a
  prime above a prime that splits completely in `F` fixes `F`.
* `IntermediateField.eq_bot_of_closure_isArithFrobAt_eq_top`: an intermediate field of `D / K` in
  which every prime of a Frobenius-generating set splits completely is `K`.
* `IntermediateField.inf_eq_bot_of_closure_isArithFrobAt_eq_top`: the same for the intersection
  `E ⊓ D`, when the primes split completely in `E`.
* `IntermediateField.linearDisjoint_of_closure_isArithFrobAt_eq_top`: then `E` and `D` are
  linearly disjoint over `K`.

## References

* L. Clozel, M. Harris and R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l
  Galois representations*, Publ. Math. IHÉS 108 (2008), proof of Lemma 4.1.2.
* L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem II*, Ann. Sci. ÉNS 22 (1989),
  Remarque 1.5.
-/

public section

open IsDedekindDomain Module NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A Frobenius at a completely split prime fixes the field.** Let `M / K` be a finite Galois
extension of number fields and `F` an intermediate field. If a prime `p` of `𝓞 K` splits
completely in `F`, then every arithmetic Frobenius `σ` at a prime `Q` of `𝓞 M` above `p` fixes
`F` pointwise. -/
theorem IsArithFrobAt.mem_fixingSubgroup_of_ncard_primesOver_eq_finrank {M : Type*} [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M] {F : IntermediateField K M} {p : Ideal (𝓞 K)}
    [p.IsPrime] (hp : (p.primesOver (𝓞 F)).ncard = finrank K F) {Q : Ideal (𝓞 M)} [Q.IsPrime]
    [Q.LiesOver p] {σ : M ≃ₐ[K] M} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    σ ∈ F.fixingSubgroup :=
  (Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le p F).1 hp Q ⟨‹_›, ‹_›⟩
    hσ.mem_stabilizer

namespace IntermediateField

/-- **Complete splitting at Frobenius-generating primes.** Let `M / K` be a finite Galois extension
of number fields and `T` a set of primes of `𝓞 K` such that the arithmetic Frobenius elements at
the primes of `𝓞 M` above `T` generate `Gal(M/K)`. An intermediate field `F` in which every prime
of `T` splits completely is `K`. -/
theorem eq_bot_of_closure_isArithFrobAt_eq_top {M : Type*} [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : Subgroup.closure {σ : M ≃ₐ[K] M | ∃ v ∈ T,
      ∃ w : {w : HeightOneSpectrum (𝓞 M) // w.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 K) σ w.val.asIdeal} = ⊤)
    {F : IntermediateField K M} (hF : ∀ v ∈ T, (v.asIdeal.primesOver (𝓞 F)).ncard = finrank K F) :
    F = ⊥ := by
  have hle : (⊤ : Subgroup (M ≃ₐ[K] M)) ≤ F.fixingSubgroup := by
    rw [← hT, Subgroup.closure_le]
    rintro σ ⟨v, hv, ⟨w, _⟩, hσ⟩
    exact hσ.mem_fixingSubgroup_of_ncard_primesOver_eq_finrank (hF v hv)
  rw [← IsGalois.fixedField_fixingSubgroup F, top_le_iff.1 hle, IsGalois.fixedField_top]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {E D : IntermediateField K Ω}

/-- **Complete splitting at Frobenius-generating primes meets `D` trivially.** Let `D / K` be a
finite Galois extension and `E / K` a finite extension inside a common field `Ω`, and let `T` be
a set of primes of `𝓞 K` such that the arithmetic Frobenius elements at the primes of `𝓞 D` above
`T` generate `Gal(D/K)`. If every prime of `T` splits completely in `E`, then `E ∩ D = K`. -/
theorem inf_eq_bot_of_closure_isArithFrobAt_eq_top [FiniteDimensional K E] [FiniteDimensional K D]
    [IsGalois K D] {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : Subgroup.closure {σ : D ≃ₐ[K] D | ∃ v ∈ T,
      ∃ w : {w : HeightOneSpectrum (𝓞 D) // w.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 K) σ w.val.asIdeal} = ⊤)
    (hE : ∀ v ∈ T, (v.asIdeal.primesOver (𝓞 E)).ncard = finrank K E) :
    E ⊓ D = ⊥ := by
  have : NumberField E := .of_module_finite K E
  have : NumberField D := .of_module_finite K D
  -- `E ⊓ D`, viewed inside `D`, is a subextension of `E` over `K`
  let F : IntermediateField K D := restrict (inf_le_right : E ⊓ D ≤ D)
  let ι : F →ₐ[K] E := (inclusion inf_le_left).comp (restrictAlgEquiv inf_le_right).symm.toAlgHom
  let _ : Algebra F E := ι.toAlgebra
  have : IsScalarTower K F E := .of_algHom ι
  have hF : ∀ v ∈ T, (v.asIdeal.primesOver (𝓞 F)).ncard = finrank K F := fun v hv ↦ by
    rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F)]
    refine Ideal.ncard_primesOver_eq_finrank_tower_bot (T := 𝓞 E) v.asIdeal ?_
    rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
    exact hE v hv
  have hF₀ : restrict (inf_le_right : E ⊓ D ≤ D) = ⊥ := eq_bot_of_closure_isArithFrobAt_eq_top hT hF
  rw [← lift_restrict (inf_le_right : E ⊓ D ≤ D), hF₀, lift_bot]

/-- **Complete splitting at Frobenius-generating primes forces linear disjointness.** Let `D / K`
be a finite Galois extension and `E / K` a finite extension inside a common field `Ω`, and let `T`
be a set of primes of `𝓞 K` such that the arithmetic Frobenius elements at the primes of `𝓞 D`
above `T` generate `Gal(D/K)`. If every prime of `T` splits completely in `E`, then `E` and `D`
are linearly disjoint over `K`. -/
theorem linearDisjoint_of_closure_isArithFrobAt_eq_top [FiniteDimensional K E]
    [FiniteDimensional K D] [IsGalois K D] {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : Subgroup.closure {σ : D ≃ₐ[K] D | ∃ v ∈ T,
      ∃ w : {w : HeightOneSpectrum (𝓞 D) // w.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 K) σ w.val.asIdeal} = ⊤)
    (hE : ∀ v ∈ T, (v.asIdeal.primesOver (𝓞 E)).ncard = finrank K E) :
    E.LinearDisjoint D :=
  (LinearDisjoint.of_inf_eq_bot (by
    rw [inf_comm, inf_eq_bot_of_closure_isArithFrobAt_eq_top hT hE])).symm

end IntermediateField
