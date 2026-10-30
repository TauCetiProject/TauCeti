/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Biprod
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Splitting

/-!
# The torsion of a direct sum of based chain complexes

Let `0 → C₁ → C₂ → C₃ → 0` be a split short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`, and give `C₂` the basis made of the images of bases of `C₁`
followed by lifts of bases of `C₃`. Then

`τ(C₂) = ε · τ(C₁) · τ(C₃)`,

where `ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim B₁,ⱼ)` is the sign of the multiplicativity formula
`HomologicalComplex.reidemeisterTorsion_eq_mul_of_shortExact`, given by the dimensions of the
boundaries `Bₖ,ⱼ ⊆ Cₖ,ⱼ`. Unlike that formula, no acyclicity is assumed
(`HomologicalComplex.reidemeisterTorsion_eq_mul_of_splitting`): the homology of `C₁` and `C₃` is a
retract of that of `C₂` (`CategoryTheory.ShortComplex.Splitting.acyclic_X₁`,
`CategoryTheory.ShortComplex.Splitting.acyclic_X₃`), so `C₂` is acyclic exactly when `C₁` and `C₃`
are, and otherwise both sides are `0`.

In particular the torsion of the biproduct `C ⊞ D` of two based complexes, with the basis of each
term made of the basis of `C` followed by the basis of `D`
(`HomologicalComplex.biprodXBasis`), is `ε · τ(C) · τ(D)`
(`HomologicalComplex.reidemeisterTorsion_biprod`). The sign `ε` is not `1` in general: it records
the exchange of the boundaries of `D` in degree `j + 1` with the lifts of the boundaries of `C` in
degree `j`, which are interleaved in the bases used to compute the torsion of `C ⊞ D`.

## Main results

* `HomologicalComplex.reidemeisterTorsion_eq_mul_of_splitting`: the torsion of the middle term of
  a split short exact sequence of based complexes, with no acyclicity hypothesis.
* `HomologicalComplex.reidemeisterTorsion_biprod`: the torsion of a direct sum of based complexes.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
-/

public section

open CategoryTheory Limits Module

namespace HomologicalComplex

variable {F : Type*} [Field F]

/-- **Torsion of a split short exact sequence.** Let `0 → C₁ → C₂ → C₃ → 0` be a split short exact
sequence of chain complexes of vector spaces, with compatible bases: the basis `c₂ i` of `C₂ᵢ` is
the image of the basis `c₁ i` of `C₁ᵢ` followed by lifts of the basis `c₃ i` of `C₃ᵢ`. Then
`τ(C₂) = ε · τ(C₁) · τ(C₃)`, with the sign `ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim B₁,ⱼ)` given by the
dimensions of the boundaries `Bₖ,ⱼ ⊆ Cₖ,ⱼ`. This holds for all complexes: when `C₁` or `C₃` is
not acyclic, neither is `C₂`, and both sides are `0`. -/
theorem reidemeisterTorsion_eq_mul_of_splitting
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (σ : S.Splitting) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k) :
    S.X₂.reidemeisterTorsion c₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsion c₁ * S.X₃.reidemeisterTorsion c₃) := by
  by_cases h : S.X₁.Acyclic ∧ S.X₃.Acyclic
  · exact reidemeisterTorsion_eq_mul_of_shortExact σ.shortExact h.1 h.2 c₁ c₃ c₂ hc₁ hc₃
  have h₂ : ¬S.X₂.Acyclic := fun h₂ ↦ h ⟨σ.acyclic_X₁ h₂, σ.acyclic_X₃ h₂⟩
  rw [reidemeisterTorsion_of_not_acyclic _ _ h₂]
  rcases not_and_or.1 h with h₁ | h₃
  · simp [reidemeisterTorsion_of_not_acyclic _ _ h₁]
  · simp [reidemeisterTorsion_of_not_acyclic _ _ h₃]

/-- **Torsion of a direct sum.** The torsion of the biproduct `C ⊞ D` of two based chain complexes
of vector spaces, where each term `(C ⊞ D).X i` has the basis `c i` followed by the basis `d i`, is
`ε · τ(C) · τ(D)`, with the sign `ε = ∏ⱼ (-1) ^ (dim B_D,ⱼ₊₁ · dim B_C,ⱼ)` given by the dimensions
of the boundaries of `C` and `D`. In particular `C ⊞ D` has nonzero torsion exactly when both `C`
and `D` do. -/
theorem reidemeisterTorsion_biprod (C D : ChainComplex (ModuleCat F) ℤ) {n m : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (d : ∀ i, Basis (Fin (m i)) F (D.X i)) :
    (C ⊞ D).reidemeisterTorsion (fun i ↦ (biprodXBasis (c i) (d i)).reindex finSumFinEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (D.d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (C.d (j + 1) j).hom))) *
      (C.reidemeisterTorsion c * D.reidemeisterTorsion d) :=
  reidemeisterTorsion_eq_mul_of_splitting (ShortComplex.Splitting.ofHasBinaryBiproduct C D) c d _
    (fun i k ↦ by simp) (fun i k ↦ by simp [← ConcreteCategory.comp_apply])

end HomologicalComplex
