/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence

/-!
# Pairs with trivial relative homology with local coefficients

This file collects criteria, read off the long exact sequence of a pair, for the relative singular
homology `Hₙ(X, A; L)` with coefficients in a local system `L` to vanish or to agree with the
homology of `X`.

* The twisted homology of an empty space vanishes, since it has no singular simplices
  (`TauCeti.LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty`). So for a pair with empty
  subspace the quotient map `Hₙ(X; L) ⟶ Hₙ(X, ∅; L)` is an isomorphism
  (`TopPair.isIso_twistedHomologyπ_of_isEmpty`).
* In degree zero that quotient map is surjective for every pair
  (`TopPair.epi_twistedHomologyπ_zero`).
* If the inclusion `A ⟶ X` induces isomorphisms on twisted homology, the relative twisted homology
  vanishes (`TopPair.isZero_twistedHomology_of_isIso`). In particular it vanishes modulo a set `S`
  into which `X` deforms through maps keeping `S` inside `S`
  (`TopPair.isZero_twistedHomology_ofSubset_of_homotopy`), the twisted counterpart of
  `TopPair.isZero_singularHomology_ofSubset_of_homotopy`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

/-- The twisted homology of an empty space vanishes. -/
theorem isZero_twistedHomology_of_isEmpty {Y : TopCat.{v}} [IsEmpty Y]
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (k : ℕ) :
    IsZero (L.twistedHomology k) := by
  have : Subsingleton (L.twistedChainComplex.X k) :=
    ⟨fun _ _ ↦ twistedChainComplex_ext_coeff L fun ρ ↦ isEmptyElim (initialVertex ρ).as⟩
  exact (L.twistedChainComplex.sc k).isZero_homology_of_isZero_X₂
    (ModuleCat.isZero_of_subsingleton (L.twistedChainComplex.X k))

end TauCeti.LocalCoefficientSystem

namespace TopPair

open TauCeti

variable {R : Type u} [Ring R] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- In degree zero, every relative twisted homology class comes from the ambient space. -/
instance epi_twistedHomologyπ_zero : Epi (P.twistedHomologyπ L 0) := by
  have : Epi ((P.twistedChainComplexπ L).f 0) :=
    (ModuleCat.epi_iff_surjective _).2 (P.twistedChainComplexπ_f_surjective L (k := 0))
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (P.twistedChainComplexπ L) 0
    (by simp)

/-- For a pair with empty subspace, relative twisted homology is the twisted homology of the
ambient space. -/
instance isIso_twistedHomologyπ_of_isEmpty [IsEmpty P.snd] (k : ℕ) :
    IsIso (P.twistedHomologyπ L k) := by
  have hA (j : ℕ) :=
    LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty (P.subspaceSystem L) j
  have : Mono (P.twistedHomologyπ L k) :=
    (P.twistedHomology_exact_space L k).mono_g ((hA k).eq_of_src _ _)
  cases k with
  | zero => exact isIso_of_mono_of_epi _
  | succ j =>
    have : Epi (P.twistedHomologyπ L (j + 1)) :=
      (P.twistedHomology_exact_relative L (j + 1) j).epi_f ((hA j).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

/-- If the inclusion of the subspace induces isomorphisms on twisted homology in every degree, the
relative twisted homology of the pair vanishes. -/
theorem isZero_twistedHomology_of_isIso
    (h : ∀ k, IsIso (LocalCoefficientSystem.twistedHomologyMap P.map L k)) (n : ℕ) :
    IsZero (P.twistedHomology L n) := by
  -- The map `Hₖ(A) ⟶ Hₖ(X)` is onto, so the quotient map `Hₖ(X) ⟶ Hₖ(X, A)` vanishes.
  have hπ (k : ℕ) : P.twistedHomologyπ L k = 0 :=
    (P.twistedHomology_exact_space L k).epi_f_iff.1 (by dsimp; infer_instance)
  cases n with
  | zero => exact IsZero.of_epi_eq_zero _ (hπ 0)
  | succ m =>
    -- The connecting map out of `Hₘ₊₁(X, A)` is then injective, and it vanishes since
    -- `Hₘ(A) ⟶ Hₘ(X)` is injective.
    have : Mono (P.twistedHomologyδ L (m + 1) m) :=
      (P.twistedHomology_exact_relative L (m + 1) m).mono_g (hπ (m + 1))
    exact IsZero.of_mono_eq_zero _
      ((P.twistedHomology_exact_subspace L (m + 1) m).mono_g_iff.1 (by dsimp; infer_instance))

/-- **Relative twisted homology vanishes modulo a set into which the space deforms.** If a homotopy
`H` from the identity of `X` to a map `ρ` with values in `S` keeps `S` inside `S`, then
`Hₙ(X, S; L) = 0` for every local coefficient system `L` on `X`. -/
theorem isZero_twistedHomology_ofSubset_of_homotopy {X : TopCat.{v}} {S : Set X} {ρ : X ⟶ X}
    (H : (TopCat.Hom.hom (𝟙 X)).Homotopy ρ.hom)
    (hS : ∀ (τ : unitInterval) (x : X), x ∈ S → H (τ, x) ∈ S) (hρ : ∀ x, ρ x ∈ S)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (n : ℕ) :
    IsZero ((ofSubset S).twistedHomology L n) := by
  -- The inclusion of `S` is a homotopy equivalence, with homotopy inverse `ρ`.
  let r : C(X, S) := ⟨fun x ↦ ⟨ρ x, hρ x⟩, by fun_prop⟩
  let e : ContinuousMap.HomotopyEquiv S X :=
    { toFun := ⟨Subtype.val, continuous_subtype_val⟩
      invFun := r
      left_inv := ⟨{
        toFun := fun p ↦ ⟨H (unitInterval.symm p.1, p.2.1), hS _ _ p.2.2⟩
        continuous_toFun := by fun_prop
        map_zero_left := fun x ↦ Subtype.ext (by simp [r])
        map_one_left := fun x ↦ Subtype.ext (by simp) }⟩
      right_inv := ⟨H.symm⟩ }
  exact isZero_twistedHomology_of_isIso (ofSubset S) L (fun k ↦ e.isIso_twistedHomologyMap L k) n

end TopPair
