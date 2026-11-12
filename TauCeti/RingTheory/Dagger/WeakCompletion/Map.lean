/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Functoriality of the Monsky–Washnitzer weak completion

An algebra homomorphism `f : S →ₐ[O] T` between finitely generated algebras induces
`S† →ₐ[O] T†`. The induced map is the restriction of `AdicCompletion.mapₐ`: an expansion
`∑ πʲ Pⱼ(x)` maps to `∑ πʲ Pⱼ(f(x))`, with the same degree bound. Changing generators
in the target then proves that the image lies in its weak completion.

The maps preserve identities and composition on every weakly completed element, not only
on the image of the original algebra. Consequently they preserve retractions. In particular,
evaluation at any `a : S` retracts the constant inclusion `S† → (S[X])†`.

No completeness, noetherianity, valuation, or regularity of the parameter is required.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23
  (1986), §2.
-/

public section

namespace TauCeti.Dagger

open MvPolynomial

variable {O S T U : Type*} [CommRing O] [CommRing S] [CommRing T] [CommRing U]
  [Algebra O S] [Algebra O T] [Algebra O U] (π : O)

/-- Mapping an expansion applies the algebra map to its generating family without changing
its polynomials or its degree bound. -/
private theorem map_mem_weakCompletionSet (f : S →ₐ[O] T) {ι : Type*} {x : ι → S}
    {z : piAdicCompletion π S} (hz : z ∈ weakCompletionSet π x) :
    AdicCompletion.mapₐ f (by simp [← Ideal.map_le_iff_le_comap, Ideal.map_span]) z ∈
      weakCompletionSet π (f ∘ x) := by
  obtain ⟨c, P, hP, hz⟩ := mem_weakCompletionSet_iff.mp hz
  apply mem_weakCompletionSet_iff.mpr
  refine ⟨c, P, hP, fun k ↦ ?_⟩
  rw [AdicCompletion.evalₐ_mapₐ, hz k, Ideal.quotientMap_mk]
  congr 1
  simp only [map_sum, map_mul, map_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    f.commutes, comp_aeval_apply, Function.comp_def]

variable [Algebra.FiniteType O S] [Algebra.FiniteType O T]

/-- The map of adic completions restricts to the weak completions. -/
private theorem map_mem_weakCompletion (f : S →ₐ[O] T) (z : weakCompletion π S) :
    AdicCompletion.mapₐ f (by simp [← Ideal.map_le_iff_le_comap, Ideal.map_span])
      (z : piAdicCompletion π S) ∈ weakCompletion π T := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := O) (A := S)
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := O) (A := T)
  have hs' : Algebra.adjoin O (Set.range ((↑) : s → S)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
  have ht' : Algebra.adjoin O (Set.range ((↑) : t → T)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht
  rw [← SetLike.mem_coe, coe_weakCompletion π _ ht']
  apply weakCompletionSet_subset_of_forall_mem_adjoin (x := f ∘ ((↑) : s → S))
    (y := ((↑) : t → T)) (fun i ↦ ht'.symm ▸ Algebra.mem_top)
  apply map_mem_weakCompletionSet π f
  rw [← coe_weakCompletion π _ hs']
  exact z.property

namespace weakCompletion

/-- The homomorphism `S† → T†` induced by an algebra homomorphism `S → T`, obtained by
restricting the map of parameter-adic completions. -/
noncomputable def map (f : S →ₐ[O] T) : weakCompletion π S →ₐ[O] weakCompletion π T :=
  ((AdicCompletion.mapₐ f (by simp [← Ideal.map_le_iff_le_comap, Ideal.map_span])).comp
    (weakCompletion π S).val).codRestrict _ (map_mem_weakCompletion π f)

/-- On the ambient adic completions, the induced map is `AdicCompletion.mapₐ`. -/
@[simp]
theorem coe_map (f : S →ₐ[O] T) (z : weakCompletion π S) :
    (map π f z : piAdicCompletion π T) =
      AdicCompletion.mapₐ f (by simp [← Ideal.map_le_iff_le_comap, Ideal.map_span])
        (z : piAdicCompletion π S) :=
  (rfl)

/-- The induced map extends the original map of algebras. -/
@[simp]
theorem map_of (f : S →ₐ[O] T) (s : S) : map π f (of π S s) = of π T (f s) := by
  apply Subtype.ext
  rw [coe_map, coe_of, AdicCompletion.mapₐ_of, coe_of]

/-- The identity algebra map induces the identity on the weak completion. -/
@[simp]
theorem map_id : map π (AlgHom.id O S) = AlgHom.id O (weakCompletion π S) := by
  apply AlgHom.ext
  intro z
  apply Subtype.ext
  rw [coe_map, AdicCompletion.mapₐ_id]
  rfl

variable [Algebra.FiniteType O U]

/-- Weak completion preserves composition of algebra homomorphisms. -/
theorem map_comp (g : T →ₐ[O] U) (f : S →ₐ[O] T) :
    map π (g.comp f) = (map π g).comp (map π f) := by
  apply AlgHom.ext
  intro z
  apply Subtype.ext
  simp only [AlgHom.comp_apply, coe_map, AdicCompletion.mapₐ_mapₐ]

/-- Pointwise composition on an arbitrary weakly completed element. -/
@[simp]
theorem map_map (g : T →ₐ[O] U) (f : S →ₐ[O] T) (z : weakCompletion π S) :
    map π g (map π f z) = map π (g.comp f) z :=
  (DFunLike.congr_fun (map_comp π g f) z).symm

/-- A retraction of algebra maps remains a retraction after weak completion. -/
theorem leftInverse_map {f : S →ₐ[O] T} {g : T →ₐ[O] S} (h : Function.LeftInverse g f) :
    Function.LeftInverse (map π g) (map π f) := by
  have hcomp : g.comp f = AlgHom.id O S := AlgHom.ext h
  intro z
  rw [map_map, hcomp, map_id]
  rfl

/-- Evaluation at `a` retracts the constant inclusion on weak completions of polynomial
algebras, for every `a : S`, including zero and one. -/
theorem leftInverse_map_aeval (a : S) :
    Function.LeftInverse (map π ((Polynomial.aeval a).restrictScalars O))
      (map π (IsScalarTower.toAlgHom O S (Polynomial S))) := by
  apply leftInverse_map
  intro s
  exact Polynomial.aeval_C a s

end weakCompletion

end TauCeti.Dagger
