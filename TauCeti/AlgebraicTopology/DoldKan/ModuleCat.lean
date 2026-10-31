/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Elementwise Dold–Kan facts for simplicial modules

For a simplicial module `G` over a ring `R`, this file records elementwise facts about the
alternating face map complex `C(G)` and Mathlib's Dold–Kan projector
`AlgebraicTopology.DoldKan.PInfty`, and packages the homotopy equivalence between the normalized
Moore complex `N(G)` and `C(G)` as an `R`-linear isomorphism on homology.

## Main declarations

* `CategoryTheory.SimplicialObject.alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero`: on an
  element whose faces `δᵢ`, `i ≥ 1`, vanish, the differential of `C(G)` is the face `δ₀`.
* `CategoryTheory.SimplicialObject.δ_succ_PInfty_f_apply`,
  `CategoryTheory.SimplicialObject.PInfty_f_apply_of_δ_succ_eq_zero`: the values of `PInfty` have
  vanishing faces `δᵢ` for `i ≥ 1`, and `PInfty` fixes such elements.
* `CategoryTheory.SimplicialObject.toNormalizedMooreComplexHomology`: the isomorphism
  `H_k(C(G)) ≃ₗ[R] H_k(N(G))`, with its naturality
  (`CategoryTheory.SimplicialObject.toNormalizedMooreComplexHomology_homologyMap`).
-/

public noncomputable section

universe u

open CategoryTheory Simplicial AlgebraicTopology AlgebraicTopology.DoldKan

namespace CategoryTheory.SimplicialObject

variable {R : Type*} [Ring R] (G : SimplicialObject (ModuleCat.{u} R)) {n : ℕ}

/-! ### Elementwise facts about the alternating face map complex -/

/-- The differential of the alternating face map complex of a simplicial module, on an element. -/
lemma alternatingFaceMapComplex_d_apply (z : G _⦋n + 1⦌) :
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).d (n + 1) n z =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • G.δ i z := by
  simp

/-- On an element whose faces `δᵢ`, `i ≥ 1`, vanish, the differential of the alternating face map
complex is the face `δ₀`. -/
lemma alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero {z : G _⦋n + 1⦌}
    (hz : ∀ i : Fin (n + 1), G.δ i.succ z = 0) :
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).d (n + 1) n z = G.δ 0 z := by
  rw [alternatingFaceMapComplex_d_apply]
  simp [Fin.sum_univ_succ, hz]

/-- The faces `δᵢ`, `i ≥ 1`, vanish on the values of the projector `PInfty`. -/
lemma δ_succ_PInfty_f_apply (z : G _⦋n + 1⦌) (i : Fin (n + 1)) :
    G.δ i.succ ((PInfty.f (n + 1) : G _⦋n + 1⦌ ⟶ G _⦋n + 1⦌) z) = 0 := by
  have := (HigherFacesVanish.of_P (X := G) (n + 1) n) i (by omega)
  rw [← PInfty_f] at this
  exact congr($this z)

/-- The projector `PInfty` fixes the elements whose faces `δᵢ`, `i ≥ 1`, vanish. -/
lemma PInfty_f_apply_of_δ_succ_eq_zero {z : G _⦋n + 1⦌}
    (hz : ∀ i : Fin (n + 1), G.δ i.succ z = 0) :
    (PInfty.f (n + 1) : G _⦋n + 1⦌ ⟶ G _⦋n + 1⦌) z = z := by
  let N : Submodule R (G _⦋n + 1⦌) := ⨅ i : Fin (n + 1), LinearMap.ker (G.δ i.succ).hom
  have hv : HigherFacesVanish (n + 1) (ModuleCat.ofHom N.subtype ≫ 𝟙 (G _⦋n + 1⦌)) :=
    fun i _ ↦ by ext ⟨z, hz⟩; exact (Submodule.mem_iInf _).1 hz i
  have := hv.comp_P_eq_self
  rw [Category.comp_id, ← PInfty_f] at this
  exact congr($this ⟨z, (Submodule.mem_iInf _).2 hz⟩)

/-! ### The comparison with the homology of the normalized Moore complex -/

/-- The isomorphism `H_k(C(G)) ≃ H_k(N(G))`, the inverse of the map induced by the inclusion of the
normalized Moore complex, a homotopy equivalence. -/
def toNormalizedMooreComplexHomology (k : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology k ≃ₗ[R]
      ((normalizedMooreComplex (ModuleCat R)).obj G).homology k :=
  ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := G)).toHomologyIso
    k).symm.toLinearEquiv

variable {G}

/-- The isomorphism `H_k(C(G)) ≃ H_k(N(G))` is inverse to the map induced by the inclusion
`N(G) ⟶ C(G)`. -/
lemma homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology {k : ℕ}
    (x : ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology k) :
    HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) k
      (toNormalizedMooreComplexHomology G k x) = x :=
  ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := G)).toHomologyIso
    k).toLinearEquiv.apply_symm_apply x

/-- The map induced on homology by the inclusion `N(G) ⟶ C(G)` is injective. -/
lemma homologyMap_inclusionOfMooreComplexMap_injective (k : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) k) :=
  ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := G)).toHomologyIso
    k).toLinearEquiv.injective

/-- The isomorphism `H_k(C(G)) ≃ H_k(N(G))` is natural in the simplicial module `G`. -/
lemma toNormalizedMooreComplexHomology_homologyMap {G' : SimplicialObject (ModuleCat.{u} R)}
    (f : G ⟶ G') {k : ℕ} (x : ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology k) :
    toNormalizedMooreComplexHomology G' k
        (HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat R)).map f) k x) =
      HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat R)).map f) k
        (toNormalizedMooreComplexHomology G k x) := by
  have h : HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat R)).map f) k ≫
      HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G') k =
        HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) k ≫
          HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat R)).map f) k := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (HomologicalComplex.homologyMap · k)
      ((inclusionOfMooreComplex (ModuleCat R)).naturality f)
  apply homologyMap_inclusionOfMooreComplexMap_injective (G := G') k
  rw [homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology,
    ← ModuleCat.comp_apply, h, ModuleCat.comp_apply,
    homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology]

end CategoryTheory.SimplicialObject
