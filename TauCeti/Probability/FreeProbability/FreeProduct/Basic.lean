/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FreeProduct.ReducedWords
public import TauCeti.Probability.FreeProbability.StarIndependence

/-!
# The free-product expectation

Given unital `R`-algebras `A i` over a commutative ring `R` equipped with normalized `R`-linear
functionals `φ i : A i →ₗ[R] R` (`φ i 1 = 1`), the reduced-word decomposition
`LinearAlgebra.FreeProduct.equivReducedWords` splits `LinearAlgebra.FreeProduct R A` into its empty
word summand `R` and the centered alternating tensor summands of positive length. Projecting onto
the empty-word summand defines the canonical free-product expectation
`TauCeti.freeProductExpectation φ hφ : LinearAlgebra.FreeProduct R A →ₗ[R] R`.

This functional is normalized, extends `φ i` along each canonical factor embedding
`LinearAlgebra.FreeProduct.ι R A i`, makes the factor subalgebras `(ι R A i).range` freely
independent, and is the unique normalized linear functional with these properties. Consequently,
any family of factor elements `i ↦ ι R A i (a i)` is freely independent (and star-freely
independent in the star setting), with individual algebraic and star distributions matching those in
the factors. Moreover, `freeProductExpectation φ hφ` is tracial whenever every `φ i` is tracial,
and commutes with `star` whenever every `φ i` commutes with `star`.

## Main definitions

* `TauCeti.freeProductExpectation φ hφ` — the universal free-product linear functional on
  `LinearAlgebra.FreeProduct R A` extending normalized functionals `φ i`.

## Main results

* `TauCeti.isFreelyIndependent_freeProductExpectation` and
  `TauCeti.existsUnique_freeProductExpectation` — freeness of the factor subalgebras and uniqueness
  of the free-product expectation.
* `TauCeti.freeProductExpectation_star`, `TauCeti.isStarFreelyIndependentElements_ι`, and
  `TauCeti.freeProductExpectation_mul_comm` — star preservation, star-freeness of factor elements,
  and traciality of the free-product expectation.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§1.2–1.5, Proposition 2.5.3.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 5–7.

Uniqueness of `freeProductExpectation` uses `TauCeti.IsFreelyIndependent.eq_of_iSup_eq_top` together
with `LinearAlgebra.FreeProduct.iSup_range_ι`, and traciality uses
`TauCeti.IsFreelyIndependent.apply_mul_comm_of_iSup_eq_top`.
-/

public section

namespace TauCeti

section FreeProductExpectation

open LinearAlgebra.FreeProduct

variable {I R : Type*} [DecidableEq I] [CommRing R]
  {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]

/-- The canonical free-product expectation on `LinearAlgebra.FreeProduct R A` associated to a family
of normalized `R`-linear functionals `φ i : A i →ₗ[R] R` (`φ i 1 = 1`): it projects onto the scalar
summand indexed by the empty reduced word `ReducedWord.nil`. -/
noncomputable def freeProductExpectation (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    LinearAlgebra.FreeProduct R A →ₗ[R] R :=
  (wordTensorNilEquiv φ).toLinearMap.comp
    ((DirectSum.component R (ReducedWord I) (WordTensor φ) .nil).comp
      (equivReducedWords φ hφ).toLinearMap)

@[simp]
theorem freeProductExpectation_algebraMap (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) (r : R) :
    freeProductExpectation φ hφ (algebraMap R (LinearAlgebra.FreeProduct R A) r) = r := by
  simp [freeProductExpectation]

@[simp]
theorem freeProductExpectation_one (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    freeProductExpectation φ hφ 1 = 1 := by
  simpa using freeProductExpectation_algebraMap φ hφ 1

/-- Every reduced-word tensor product of nonempty word `w ≠ .nil` lies in the kernel of
`freeProductExpectation`. -/
theorem freeProductExpectation_wordMul_eq_zero_of_ne_nil (φ : ∀ i, A i →ₗ[R] R)
    (hφ : ∀ i, φ i 1 = 1) {w : ReducedWord I} (hw : w ≠ .nil) (z : WordTensor φ w) :
    freeProductExpectation φ hφ (wordMul φ w z) = 0 := by
  simp [freeProductExpectation, DirectSum.component.of, hw]

/-- `freeProductExpectation` vanishes on `reducedWordSubmodule φ w` for every nonempty reduced word
`w ≠ .nil`. -/
theorem freeProductExpectation_eq_zero_of_mem_reducedWordSubmodule
    (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    {w : ReducedWord I} (hw : w ≠ .nil) {x : LinearAlgebra.FreeProduct R A}
    (hx : x ∈ reducedWordSubmodule φ w) :
    freeProductExpectation φ hφ x = 0 := by
  obtain ⟨z, rfl⟩ := mem_reducedWordSubmodule.1 hx
  exact freeProductExpectation_wordMul_eq_zero_of_ne_nil φ hφ hw z

@[simp]
theorem freeProductExpectation_ι (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (i : I) (a : A i) :
    freeProductExpectation φ hφ (ι R A i a) = φ i a := by
  simp [freeProductExpectation, equivReducedWords_ι, DirectSum.component.of]

@[simp]
theorem freeProductExpectation_comp_ι (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) (i : I) :
    (freeProductExpectation φ hφ).comp (ι R A i).toLinearMap = φ i := by
  apply LinearMap.ext
  intro a
  simp

/-- The canonical factor subalgebras `(ι R A i).range` are freely independent in
`LinearAlgebra.FreeProduct R A` with respect to `freeProductExpectation φ hφ`. -/
theorem isFreelyIndependent_freeProductExpectation
    (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    IsFreelyIndependent (freeProductExpectation φ hφ) fun i ↦ (ι R A i).range := by
  rw [isFreelyIndependent_iff]
  intro w hne halt hw hc
  choose g hg using fun x (hx : x ∈ w) ↦ (AlgHom.mem_range _).1 (hw x hx)
  let l : List (Σ i, A i) := w.pmap (fun x hx ↦ ⟨x.1, g x hx⟩) fun _ hx ↦ hx
  have hfst : l.map Sigma.fst = w.map Prod.fst := by
    simp [l, List.map_pmap]
  have hsnd : (l.map fun u ↦ ι R A u.1 u.2).prod = (w.map Prod.snd).prod := by
    simp [l, List.map_pmap, hg]
  have halt' : (l.map Sigma.fst).IsChain (· ≠ ·) := hfst ▸ halt
  have hker : ∀ u ∈ l, u.2 ∈ LinearMap.ker (φ u.1) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_pmap.1 hu
    rw [LinearMap.mem_ker, ← freeProductExpectation_ι φ hφ, hg x hx]
    exact hc x hx
  have hwnil : (⟨l.map Sigma.fst, halt'⟩ : ReducedWord I) ≠ .nil := by
    intro h
    have hl0 : l.map Sigma.fst = [] := congrArg ReducedWord.toList h
    rw [hfst, List.map_eq_nil_iff] at hl0
    exact hne hl0
  rw [← hsnd]
  exact freeProductExpectation_eq_zero_of_mem_reducedWordSubmodule φ hφ hwnil
    (list_prod_mem_reducedWordSubmodule φ l halt' hker)

/-- Uniqueness of the free-product expectation: any normalized linear functional on
`LinearAlgebra.FreeProduct R A` that extends every `φ i` and makes the factor subalgebras freely
independent equals `freeProductExpectation φ hφ`. -/
theorem eq_freeProductExpectation {φ : ∀ i, A i →ₗ[R] R} (hφ : ∀ i, φ i 1 = 1)
    {ψ : LinearAlgebra.FreeProduct R A →ₗ[R] R} (hψ : ψ 1 = 1)
    (hfree : IsFreelyIndependent ψ fun i ↦ (ι R A i).range)
    (hext : ∀ i a, ψ (ι R A i a) = φ i a) :
    ψ = freeProductExpectation φ hφ := by
  refine IsFreelyIndependent.eq_of_iSup_eq_top hψ (freeProductExpectation_one φ hφ) hfree
    (isFreelyIndependent_freeProductExpectation φ hφ) (fun i x hx ↦ ?_) (iSup_range_ι R A)
  obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).1 hx
  rw [hext, freeProductExpectation_ι]

/-- Existence and uniqueness of the universal free-product expectation on
`LinearAlgebra.FreeProduct R A`. -/
theorem existsUnique_freeProductExpectation (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    ∃! ψ : LinearAlgebra.FreeProduct R A →ₗ[R] R,
      ψ 1 = 1 ∧ IsFreelyIndependent ψ (fun i ↦ (ι R A i).range) ∧
        ∀ i, ψ.comp (ι R A i).toLinearMap = φ i := by
  refine ⟨freeProductExpectation φ hφ, ⟨freeProductExpectation_one φ hφ,
    isFreelyIndependent_freeProductExpectation φ hφ, freeProductExpectation_comp_ι φ hφ⟩, ?_⟩
  rintro ψ ⟨hψ, hfree, hext⟩
  exact eq_freeProductExpectation hφ hψ hfree fun i a ↦ LinearMap.congr_fun (hext i) a

/-- Any family of elements chosen one from each factor of `LinearAlgebra.FreeProduct R A` is freely
independent with respect to `freeProductExpectation φ hφ`. -/
theorem isFreelyIndependentElements_ι (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (a : ∀ i, A i) :
    IsFreelyIndependentElements (freeProductExpectation φ hφ) fun i ↦ ι R A i (a i) := by
  rw [isFreelyIndependentElements_iff]
  exact (isFreelyIndependent_freeProductExpectation φ hφ).mono fun i ↦
    Algebra.adjoin_le <| Set.singleton_subset_iff.2 (AlgHom.mem_range_self (ι R A i) (a i))

/-- Embedding a family of elements from the `i`-th factor into `LinearAlgebra.FreeProduct R A`
preserves their joint algebraic distribution. -/
theorem jointDistribution_freeProductExpectation_comp_ι
    (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) {κ : Type*} (i : I) (f : κ → A i) :
    jointDistribution (freeProductExpectation φ hφ) (fun k ↦ ι R A i (f k)) =
      jointDistribution (φ i) f := by
  simpa [Function.comp_def] using
    (jointDistribution_map (freeProductExpectation φ hφ) (ι R A i) f).symm

/-- **Traciality of the free-product expectation.** If each normalized functional `φ i` is tracial
on `A i`, then `freeProductExpectation φ hφ` is tracial on `LinearAlgebra.FreeProduct R A`. -/
theorem freeProductExpectation_mul_comm (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (htr : ∀ i (a b : A i), φ i (a * b) = φ i (b * a))
    (x y : LinearAlgebra.FreeProduct R A) :
    freeProductExpectation φ hφ (x * y) = freeProductExpectation φ hφ (y * x) := by
  refine (isFreelyIndependent_freeProductExpectation φ hφ).apply_mul_comm_of_iSup_eq_top
    (freeProductExpectation_one φ hφ) (fun i u hu v hv ↦ ?_) (iSup_range_ι R A) x y
  obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).1 hu
  obtain ⟨b, rfl⟩ := (AlgHom.mem_range _).1 hv
  rw [← map_mul, ← map_mul, freeProductExpectation_ι, freeProductExpectation_ι, htr]

section Star

variable [StarRing R] [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]

/-- If each normalized functional `φ i` commutes with `star`, then `freeProductExpectation φ hφ`
commutes with `star`. -/
theorem freeProductExpectation_star (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (hstar : ∀ i (a : A i), φ i (star a) = star (φ i a))
    (x : LinearAlgebra.FreeProduct R A) :
    freeProductExpectation φ hφ (star x) = star (freeProductExpectation φ hφ x) := by
  rw [← (equivReducedWords φ hφ).symm_apply_apply x]
  generalize equivReducedWords φ hφ x = v
  induction v using DirectSum.induction_on with
  | zero => simp
  | of w z =>
    rw [← DirectSum.lof_eq_of R, equivReducedWords_symm_apply, reducedWordsToFreeProduct_lof]
    by_cases hw : w = .nil
    · subst hw
      rw [wordMul_nil, ← algebraMap_star_comm, freeProductExpectation_algebraMap,
        freeProductExpectation_algebraMap]
    · have hrev : w.reverse ≠ .nil := fun h ↦
        hw (by simpa using congrArg ReducedWord.reverse h)
      rw [freeProductExpectation_eq_zero_of_mem_reducedWordSubmodule φ hφ hrev
          (star_mem_reducedWordSubmodule hstar (mem_reducedWordSubmodule.2 ⟨z, rfl⟩)),
        freeProductExpectation_wordMul_eq_zero_of_ne_nil φ hφ hw z, star_zero]
  | add v₁ v₂ hv₁ hv₂ =>
    rw [map_add, star_add, map_add, map_add, star_add, hv₁, hv₂]

/-- Any family of elements chosen one from each factor of a star free product is star-freely
independent with respect to `freeProductExpectation φ hφ`. -/
theorem isStarFreelyIndependentElements_ι (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (a : ∀ i, A i) :
    IsStarFreelyIndependentElements (freeProductExpectation φ hφ) fun i ↦ ι R A i (a i) := by
  rw [isStarFreelyIndependentElements_iff]
  refine (isFreelyIndependent_freeProductExpectation φ hφ).mono fun i ↦ ?_
  rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, star_ι]
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · exact AlgHom.mem_range_self (ι R A i) (a i)
  · exact AlgHom.mem_range_self (ι R A i) (star (a i))

/-- Embedding a family of elements from the `i`-th factor into a star free product preserves their
joint star distribution. -/
theorem starDistribution_freeProductExpectation_comp_ι
    (φ : ∀ i, A i →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) {κ : Type*} (i : I) (f : κ → A i) :
    starDistribution (freeProductExpectation φ hφ) (fun k ↦ ι R A i (f k)) =
      starDistribution (φ i) f := by
  simpa [Function.comp_def] using
    (starDistribution_map (freeProductExpectation φ hφ) (ιStar R A i) f).symm

end Star

end FreeProductExpectation

end TauCeti
