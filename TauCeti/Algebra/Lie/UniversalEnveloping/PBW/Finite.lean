/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import TauCeti.LinearAlgebra.Multilinear.Span

/-!
# Finite images of enveloping algebras from monic relations

If the images of a finite spanning family of a Lie algebra satisfy monic polynomial relations
over central scalars, every surjective image of its enveloping algebra is module-finite over
those scalars. The target algebra need not be commutative. Ordered PBW monomials group the
powers of each generator together. Reducing each power by its monic relation and using
multilinearity expresses every such product in terms of the bounded products.

This provides the finiteness argument both for enveloping algebras over central subalgebras and
for two-sided quotients by noncentral monic relations.

## References

* N. Jacobson, *Lie Algebras*, Chapter V (PBW).
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2.
-/

public section

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section IntegralBasis

variable {A : Type x} [Ring A] [Algebra R A]
variable (S : Type w) [CommRing S] [Algebra R S]
variable [Algebra S A]
variable [IsScalarTower R S A]

/-- The nondecreasing list in which `i` occurs `c i` times. -/
private def repeatedIndices (n : ℕ) (c : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun i ↦ List.replicate (c i) i

private theorem repeatedIndices_pairwise (n : ℕ) (c : Fin n → ℕ) :
    (repeatedIndices n c).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [repeatedIndices]
  | succ n ih =>
      rw [repeatedIndices, List.finRange_succ, List.flatMap_cons]
      simp only [List.flatMap_map]
      rw [List.pairwise_append]
      refine ⟨by simp, ?_, ?_⟩
      · have h := (ih (fun i ↦ c i.succ)).map Fin.succ
            (fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h)
        simpa [repeatedIndices, List.map_flatMap] using h
      · simp

private theorem count_repeatedIndices (n : ℕ) (c : Fin n → ℕ) (i : Fin n) :
    (repeatedIndices n c).count i = c i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      have hexpand : repeatedIndices (n + 1) c = List.replicate (c 0) 0 ++
          (repeatedIndices n fun j ↦ c j.succ).map Fin.succ := by
        rw [repeatedIndices, List.finRange_succ, List.flatMap_cons, repeatedIndices,
          List.flatMap_map]
        rw [List.map_flatMap]
        simp
      rw [hexpand, List.count_append]
      by_cases hi : i = 0
      · subst i
        simp [List.count_eq_zero]
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
        rw [List.count_map_of_injective _ Fin.succ (Fin.succ_injective n) j, ih]
        simp [List.count_replicate, Ne.symm hi]

private theorem eq_repeatedIndices {n : ℕ} {word : List (Fin n)}
    (hword : word.Pairwise (· ≤ ·)) :
    word = repeatedIndices n fun i ↦ word.count i := by
  apply List.Perm.eq_of_pairwise' hword (repeatedIndices_pairwise n _)
  rw [List.perm_iff_count]
  exact fun i ↦ (count_repeatedIndices n (fun i ↦ word.count i) i).symm

private theorem pbwMonomial_flatMap_replicate {n : ℕ} (e : Fin n → L)
    (c : Fin n → ℕ) (l : List (Fin n)) :
    pbwMonomial R L e (l.flatMap fun i ↦ List.replicate (c i) i) =
      (l.map fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (e i) ^ c i).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.flatMap_cons, pbwMonomial_append, List.map_cons, List.prod_cons, ih]
      simp [pbwMonomial_def]

private theorem pbwMonomial_repeatedIndices (n : ℕ) (e : Fin n → L) (c : Fin n → ℕ) :
    pbwMonomial R L e (repeatedIndices n c) =
      ((List.finRange n).map fun i ↦
        _root_.UniversalEnvelopingAlgebra.ι R (e i) ^ c i).prod := by
  exact pbwMonomial_flatMap_replicate R L e c _

/-- Ordered products of generator powers span every surjective image of an enveloping algebra.
Only a spanning family of the Lie algebra is required. -/
theorem span_range_orderedPowerProducts_eq_top {n : ℕ} (e : Fin n → L)
    (he : Submodule.span R (Set.range e) = ⊤) (q : U →ₐ[R] A)
    (hq : Function.Surjective q) :
    Submodule.span S (Set.range fun c : Fin n → ℕ ↦
      ((List.finRange n).map fun i ↦ q (_root_.UniversalEnvelopingAlgebra.ι R (e i)) ^ c i).prod)
      = ⊤ := by
  let M := Submodule.span S (Set.range fun c : Fin n → ℕ ↦
    ((List.finRange n).map fun i ↦ q (_root_.UniversalEnvelopingAlgebra.ι R (e i)) ^ c i).prod)
  have hle : Submodule.span R (⋃ k, orderedPBWMonomials R L e k) ≤
      (M.restrictScalars R).comap q.toLinearMap := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨k, hak⟩ := Set.mem_iUnion.mp ha
    obtain ⟨word, hword, -, rfl⟩ := (mem_orderedPBWMonomials_iff R L e).mp hak
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.coe_toLinearMap,
      Submodule.restrictScalars_mem, eq_repeatedIndices hword,
      pbwMonomial_repeatedIndices, map_list_prod]
    simp only [List.map_map, Function.comp_def, map_pow]
    exact Submodule.subset_span ⟨_, rfl⟩
  rw [span_iUnion_orderedPBWMonomials_eq_top R L e he] at hle
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨a, rfl⟩ := hq x
  exact hle Submodule.mem_top

/-- If the generator images satisfy monic relations `p i`, the ordered products with exponent
of generator `i` strictly less than `(p i).natDegree` span the target. This is an explicit finite
spanning family even when the target is noncommutative. -/
theorem span_range_bounded_orderedPowerProducts_eq_top {n : ℕ} (e : Fin n → L)
    (he : Submodule.span R (Set.range e) = ⊤) (q : U →ₐ[R] A)
    (hq : Function.Surjective q) (p : Fin n → Polynomial S)
    (hp : ∀ i, (p i).Monic)
    (hpx : ∀ i, Polynomial.aeval (q (_root_.UniversalEnvelopingAlgebra.ι R (e i))) (p i) = 0) :
    Submodule.span S (Set.range fun c : ∀ i, Fin ((p i).natDegree) ↦
      ((List.finRange n).map fun i ↦
        q (_root_.UniversalEnvelopingAlgebra.ι R (e i)) ^ (c i : ℕ)).prod) = ⊤ := by
  classical
  let x i := q (_root_.UniversalEnvelopingAlgebra.ι R (e i))
  let f := MultilinearMap.mkPiAlgebraFin S n A
  let s i : Set A := (Finset.range (p i).natDegree).image (x i ^ ·)
  have himage : f '' Set.univ.pi s ⊆ Set.range (fun c : ∀ i, Fin ((p i).natDegree) ↦
      ((List.finRange n).map fun i ↦ x i ^ (c i : ℕ)).prod) := by
    rintro a ⟨m, hm, rfl⟩
    have hm' : ∀ i, ∃ k, k < (p i).natDegree ∧ x i ^ k = m i := by
      intro i
      simpa [s] using hm i (Set.mem_univ i)
    choose k hk hkm using hm'
    refine ⟨fun i ↦ ⟨k i, hk i⟩, ?_⟩
    simp [f, MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_eq_map, hkm]
  apply top_unique
  rw [← span_range_orderedPowerProducts_eq_top R L S e he q hq, Submodule.span_le]
  rintro a ⟨c, rfl⟩
  have hsingle : ∀ i, x i ^ c i ∈ Submodule.span S (s i) := by
    intro i
    simp only [s]
    rw [Submodule.span_range_natDegree_eq_adjoin (hp i) (hpx i)]
    exact (Algebra.adjoin S {x i}).pow_mem (Algebra.subset_adjoin rfl) _
  have h := Submodule.span_mono himage (f.map_mem_span_image_pi s hsingle)
  simpa [f, x, MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_eq_map] using h

/-- A surjective image of an enveloping algebra is module-finite over central scalars `S`
if the images of a finite spanning family of the Lie algebra are integral over `S`.
The target algebra may be noncommutative. -/
theorem moduleFinite_of_isIntegral_of_span_eq_top {n : ℕ} (e : Fin n → L)
    (he : Submodule.span R (Set.range e) = ⊤) (q : U →ₐ[R] A)
    (hq : Function.Surjective q)
    (h : ∀ i, IsIntegral S (q (_root_.UniversalEnvelopingAlgebra.ι R (e i)))) :
    Module.Finite S A := by
  classical
  choose p hp hpx using h
  have hpx' : ∀ i, Polynomial.aeval (q (_root_.UniversalEnvelopingAlgebra.ι R (e i))) (p i) = 0 :=
    fun i ↦ by simpa only [Polynomial.aeval_def] using hpx i
  exact Module.finite_def.mpr (Submodule.fg_def.mpr
    ⟨_, Set.finite_range _, span_range_bounded_orderedPowerProducts_eq_top R L S e he q hq
      p hp hpx'⟩)

end IntegralBasis

end TauCeti.UniversalEnvelopingAlgebra
