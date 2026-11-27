/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered
public import TauCeti.Data.List.MonomialWord

/-!
# Ordered PBW monomials indexed by exponent vectors

Let `X₁, …, X_m` be a family in a Lie algebra `L`. The ordered PBW monomials of degree at most `k`
in this family are exactly the monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}` of the exponent vectors `α`
with `|α| ≤ k`, that is, of the indices in `TauCeti.SobolevIndex m k`. When the family spans `L`,
the spanning half of the Poincaré–Birkhoff–Witt theorem then shows that under any algebra map `φ`
out of `U(L)`, the image `φ(X_{i₁}) ⋯ φ(X_{iₙ})` of a word of length at most `k` is a linear
combination of the images `φ(X^α)` of these ordered monomials.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials`: the
  ordered PBW monomials of degree at most `k` are the monomials `X^α` with `|α| ≤ k`.
* `TauCeti.UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord`: under an algebra map out
  of `U(L)`, words of length at most `k` are combinations of ordered monomials of degree at most
  `k`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

/-- The ordered PBW monomials of degree at most `k` in a family `X₁, …, X_m` are exactly the
monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}` of the exponent vectors `α` in `SobolevIndex m k`. -/
theorem range_pbwMonomial_monomialWord_eq_orderedPBWMonomials (R : Type*) (L : Type*)
    [CommRing R] [LieRing L] [LieAlgebra R L] {m : ℕ} (X : Fin m → L) (k : ℕ) :
    Set.range (fun α : SobolevIndex m k ↦ pbwMonomial R L X (monomialWord α.exponent)) =
      orderedPBWMonomials R L X k := by
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨α, rfl⟩
    refine pbwMonomial_mem_orderedPBWMonomials R L X (pairwise_monomialWord _) ?_
    rw [length_monomialWord]
    simpa only [SobolevIndex.exponent_apply] using α.property
  · intro ha
    obtain ⟨word, hsorted, hlength, rfl⟩ := (mem_orderedPBWMonomials_iff R L X).1 ha
    obtain ⟨α, hα⟩ := exists_sobolevIndex_monomialWord_eq hsorted hlength
    exact ⟨α, congrArg (pbwMonomial R L X) hα⟩

/-- **Words are combinations of ordered monomials in any representation of `U(L)`.** For an
algebra map `φ` out of `U(L)` and a spanning family `X₁, …, X_m` of `L`, write `D i = φ(X_i)`.
The product `D_w = D_{i₁} ⋯ D_{iₙ}` along a word `w` of length at most `k` is an `R`-combination
of the ordered monomials `D^α = D₁^{α₁} ⋯ D_m^{α_m}` with `|α| ≤ k`. -/
theorem prod_map_mem_span_monomialWord (R : Type*) {L A : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [Ring A] [Algebra R A] (φ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] A)
    {m : ℕ} (X : Fin m → L) (hX : Submodule.span R (Set.range X) = ⊤) {k : ℕ}
    {w : List (Fin m)} (hw : w.length ≤ k) :
    (w.map fun i ↦ φ (_root_.UniversalEnvelopingAlgebra.ι R (X i))).prod ∈ Submodule.span R
      (Set.range fun α : SobolevIndex m k ↦
        ((monomialWord α.exponent).map fun i ↦
          φ (_root_.UniversalEnvelopingAlgebra.ι R (X i))).prod) := by
  have hφ : ∀ w : List (Fin m), φ (pbwMonomial R L X w) =
      (w.map fun i ↦ φ (_root_.UniversalEnvelopingAlgebra.ι R (X i))).prod := fun w ↦ by
    simp [pbwMonomial_def, map_list_prod, List.map_map, Function.comp_def]
  have hmem : pbwMonomial R L X w ∈ Submodule.span R
      (Set.range fun α : SobolevIndex m k ↦ pbwMonomial R L X (monomialWord α.exponent)) := by
    rw [range_pbwMonomial_monomialWord_eq_orderedPBWMonomials,
      span_orderedPBWMonomials_eq_pbwFiltration R L X hX]
    exact pbwFiltration_mono R L hw (pbwMonomial_mem_pbwFiltration R L X w)
  have h := Submodule.apply_mem_span_image_of_mem_span φ.toLinearMap hmem
  rw [← Set.range_comp] at h
  simpa only [AlgHom.toLinearMap_apply, Function.comp_def, hφ] using h

end TauCeti.UniversalEnvelopingAlgebra
