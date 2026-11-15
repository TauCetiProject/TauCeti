/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Milnor's multiplicativity formula for torsion with homology bases

Let `0 → C₁ → C₂ → C₃ → 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over a field, with compatible ordered bases of the chains (the basis of `C₂ᵢ` is the image
of the basis of `C₁ᵢ` followed by lifts of the basis of `C₃ᵢ`) and arbitrary ordered bases `hₖ` of
the homology groups. The complexes need not be acyclic. Then

`τ(C₂, c₂, h₂) = ± τ(C₁, c₁, h₁) · τ(C₃, c₃, h₃) · τ(H)`

(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_or_eq_neg_mul_of_shortExact`), where
`τ(Cₖ, cₖ, hₖ)` is the torsion of a based complex with based homology
(`HomologicalComplex.reidemeisterTorsionWithHomology`) and `H` is the long exact homology sequence
`⋯ → Hᵢ(C₁) → Hᵢ(C₂) → Hᵢ(C₃) → Hᵢ₋₁(C₁) → ⋯`, an acyclic complex based by the homology bases
(`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`). When `C₁` and `C₃` are
acyclic, `H` is zero and this is the multiplicativity of the torsion of acyclic complexes
`HomologicalComplex.reidemeisterTorsion_eq_mul_of_shortExact`, which there carries an explicit
sign; here the sign is not determined.

## Proof

Both sides are alternating products of brackets, for any choices of boundary bases, homology
representatives and lifts. In each degree the choices for `C₂` are assembled from those of `C₁`,
`C₃` and of the long exact sequence, following the filtrations `f(B₁) ⊆ f(C₁) ∩ B₂ ⊆ B₂` of the
boundaries (with quotients `im ∂` and `B₃`) and `im ∂ ⊆ H(C₁)`, `im f_* ⊆ H(C₂)`, `im g_* ⊆ H(C₃)`
of the homology; a basis of `im ∂` lifts through the differential of `C₂` by the description of
the connecting map. The bracket of `C₂` is then, up to sign, the product of the brackets of `C₁`
and `C₃` and of the determinants comparing the adapted homology bases with `h₁`, `h₂`, `h₃`, and
these are, up to sign, the brackets of the based long exact sequence. Equality up to sign is
handled as equality of squares, which turns into the stated disjunction by
`sq_eq_sq_iff_eq_or_eq_neg`.

## Main declarations

* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_or_eq_neg_mul_of_shortExact`: Milnor's
  formula.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
-/

public section

noncomputable section

open CategoryTheory Module

variable {F : Type*} [Field F]

/-- The regrouping of the eight families making up the brackets of the outer terms of a short
exact sequence into the three blocks of the bracket of the middle term. -/
private def regroupEquiv (A₁ R₁ Φ Q₁ A₃ Γ R₀ Q₃ : Type*) :
    ((A₁ ⊕ (R₁ ⊕ Φ)) ⊕ Q₁) ⊕ ((A₃ ⊕ (Γ ⊕ R₀)) ⊕ Q₃) ≃
      (((A₁ ⊕ R₁) ⊕ A₃) ⊕ (Φ ⊕ Γ)) ⊕ ((Q₁ ⊕ R₀) ⊕ Q₃) where
  toFun
    | .inl (.inl (.inl a)) => .inl (.inl (.inl (.inl a)))
    | .inl (.inl (.inr (.inl r))) => .inl (.inl (.inl (.inr r)))
    | .inl (.inl (.inr (.inr x))) => .inl (.inr (.inl x))
    | .inl (.inr q) => .inr (.inl (.inl q))
    | .inr (.inl (.inl a)) => .inl (.inl (.inr a))
    | .inr (.inl (.inr (.inl x))) => .inl (.inr (.inr x))
    | .inr (.inl (.inr (.inr r))) => .inr (.inl (.inr r))
    | .inr (.inr q) => .inr (.inr q)
  invFun
    | .inl (.inl (.inl (.inl a))) => .inl (.inl (.inl a))
    | .inl (.inl (.inl (.inr r))) => .inl (.inl (.inr (.inl r)))
    | .inl (.inl (.inr a)) => .inr (.inl (.inl a))
    | .inl (.inr (.inl x)) => .inl (.inl (.inr (.inr x)))
    | .inl (.inr (.inr x)) => .inr (.inl (.inr (.inl x)))
    | .inr (.inl (.inl q)) => .inl (.inr q)
    | .inr (.inl (.inr r)) => .inr (.inl (.inr (.inr r)))
    | .inr (.inr q) => .inr (.inr q)
  left_inv := by rintro (((a | r | x) | q) | ((a | x | r) | q)) <;> rfl
  right_inv := by rintro ((((a | r) | a) | (x | x)) | ((q | r) | q)) <;> rfl

/-! ### The based long exact homology sequence -/

namespace CategoryTheory.ShortComplex.ShortExact

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)

/-- The term of the long exact sequence in degree `3k + 2` is `Hₖ(S.X₁)`. This fixes the
interleaved complex of `ChainComplex.interleave.XIso₁` to `hS.homologySequenceComplex`, whose
proof arguments cannot be inferred where the isomorphism is applied. -/
private def lesIso₁ (n k : ℤ) (h : n = 3 * k + 2) :
    hS.homologySequenceComplex.X n ≅ S.X₁.homology k :=
  ChainComplex.interleave.XIso₁ _ _ _ n k h

/-- The term of the long exact sequence in degree `3k + 1` is `Hₖ(S.X₂)`. -/
private def lesIso₂ (n k : ℤ) (h : n = 3 * k + 1) :
    hS.homologySequenceComplex.X n ≅ S.X₂.homology k :=
  ChainComplex.interleave.XIso₂ _ _ _ n k h

/-- The term of the long exact sequence in degree `3k` is `Hₖ(S.X₃)`. -/
private def lesIso₃ (n k : ℤ) (h : n = 3 * k) :
    hS.homologySequenceComplex.X n ≅ S.X₃.homology k :=
  ChainComplex.interleave.XIso₃ _ _ _ n k h

private theorem lesIso₁_d (n k : ℤ) (h : n = 3 * k + 2)
    (x : hS.homologySequenceComplex.X (n + 1)) :
    (hS.lesIso₁ n k h).hom.hom
        ((hS.homologySequenceComplex.d (n + 1) n).hom x) =
      (hS.δ (k + 1) k rfl).hom
        ((hS.lesIso₃ (n + 1) (k + 1) (by omega)).hom.hom x) := by
  rw [lesIso₁, lesIso₃, ChainComplex.interleave_d_eq_of_eq_three_mul_add_two _ _ _ h]
  simp

private theorem lesIso₂_d (n k : ℤ) (h : n = 3 * k + 1)
    (x : hS.homologySequenceComplex.X (n + 1)) :
    (hS.lesIso₂ n k h).hom.hom
        ((hS.homologySequenceComplex.d (n + 1) n).hom x) =
      (HomologicalComplex.homologyMap S.f k).hom
        ((hS.lesIso₁ (n + 1) k (by omega)).hom.hom x) := by
  rw [lesIso₁, lesIso₂, ChainComplex.interleave_d_eq_of_eq_three_mul_add_one _ _ _ h]
  simp

private theorem lesIso₃_d (n k : ℤ) (h : n = 3 * k)
    (x : hS.homologySequenceComplex.X (n + 1)) :
    (hS.lesIso₃ n k h).hom.hom
        ((hS.homologySequenceComplex.d (n + 1) n).hom x) =
      (HomologicalComplex.homologyMap S.g k).hom
        ((hS.lesIso₂ (n + 1) k (by omega)).hom.hom x) := by
  rw [lesIso₂, lesIso₃, ChainComplex.interleave_d_eq_of_eq_three_mul _ _ _ h]
  simp

variable {m₁ m₂ m₃ : ℤ → ℕ} (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The basis of the long exact homology sequence given by the homology bases. -/
private abbrev lesBasis :
    ∀ n, Basis (Fin (ChainComplex.interleave.rank m₁ m₂ m₃ n)) F (hS.homologySequenceComplex.X n) :=
  ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃

/-- The index types of the bases `lesρ k`, `lesφ k` and `lesγ k` below. -/
private abbrev Idxρ (k : ℤ) : Type :=
  Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (3 * k + 2 + 1) (3 * k + 2)).hom))

private abbrev Idxφ (k : ℤ) : Type :=
  Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (3 * k + 1 + 1) (3 * k + 1)).hom))

private abbrev Idxγ (k : ℤ) : Type :=
  Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (3 * k + 1) (3 * k)).hom))

/-! The images of the maps of the long exact sequence, with bases and lifts read off the chosen
boundary bases and lifts of the based long exact sequence. -/

/-- The chosen boundary bases and lifts of the based long exact sequence. -/
private abbrev lesBoundaryBasis (n : ℤ) :=
  HomologicalComplex.chosenBoundaryBasis hS.homologySequenceComplex (hS.lesBasis h₁ h₂ h₃) (n + 1) n

private abbrev lesBoundaryLift (n : ℤ) :=
  HomologicalComplex.chosenBoundaryLift hS.homologySequenceComplex (hS.lesBasis h₁ h₂ h₃) (n + 1) n

section Transport

variable (n : ℤ) {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
  (e₁ : hS.homologySequenceComplex.X (n + 1) ≃ₗ[F] M)
  (e₂ : hS.homologySequenceComplex.X n ≃ₗ[F] N) (φ : M →ₗ[F] N)
  (hφ : ∀ x, e₂ ((hS.homologySequenceComplex.d (n + 1) n).hom x) = φ (e₁ x))

/-- The chosen boundary basis of the based long exact sequence in degree `n`, carried by linear
equivalences `e₁`, `e₂` of the terms of degrees `n + 1` and `n`, which turn the differential into
a map `φ`, to a basis of the image of `φ`. -/
private def mapBoundaryBasis :
    Basis (Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (n + 1) n).hom))) F
      (LinearMap.range φ) :=
  (hS.lesBoundaryBasis h₁ h₂ h₃ n).map (e₂.ofSubmodules _ _
    (LinearMap.map_range_eq_range_of_comp_eq _ e₁.surjective (LinearMap.ext fun x ↦ (hφ x).symm)))

private theorem coe_mapBoundaryBasis (i) :
    (hS.mapBoundaryBasis h₁ h₂ h₃ n e₁ e₂ φ hφ i : N) = e₂ (hS.lesBoundaryBasis h₁ h₂ h₃ n i) := by
  simp [mapBoundaryBasis]

/-- The images under `e₁` of the chosen lifts are lifts through `φ` of `mapBoundaryBasis`. -/
private theorem apply_mapBoundaryLift (i) :
    φ (e₁ (hS.lesBoundaryLift h₁ h₂ h₃ n i)) = hS.mapBoundaryBasis h₁ h₂ h₃ n e₁ e₂ φ hφ i := by
  rw [← hφ, HomologicalComplex.chosenBoundaryLift_spec, coe_mapBoundaryBasis]

end Transport

/-- A basis of the image of the connecting map `Hₖ₊₁(S.X₃) → Hₖ(S.X₁)`. -/
private def lesρ (k : ℤ) :
    Basis (hS.Idxρ k) F (LinearMap.range (hS.δ (k + 1) k rfl).hom) :=
  hS.mapBoundaryBasis h₁ h₂ h₃ (3 * k + 2)
    (hS.lesIso₃ (3 * k + 2 + 1) (k + 1) (by ring)).toLinearEquiv
    (hS.lesIso₁ (3 * k + 2) k rfl).toLinearEquiv _
    fun x ↦ by simpa using hS.lesIso₁_d _ _ rfl x

/-- Lifts through the connecting map `Hₖ₊₁(S.X₃) → Hₖ(S.X₁)` of the basis `lesρ`. -/
private def lesγ' (k : ℤ) (i : hS.Idxρ k) : S.X₃.homology (k + 1) :=
  (hS.lesIso₃ (3 * k + 2 + 1) (k + 1) (by ring)).toLinearEquiv
    (hS.lesBoundaryLift h₁ h₂ h₃ (3 * k + 2) i)

private theorem coe_lesρ (k : ℤ) (i) :
    (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k) =
      (hS.lesIso₁ (3 * k + 2) k rfl).toLinearEquiv
        (hS.lesBoundaryBasis h₁ h₂ h₃ (3 * k + 2) i) := by
  rw [lesρ, coe_mapBoundaryBasis]

private theorem δ_lesγ' (k : ℤ) (i) :
    (hS.δ (k + 1) k rfl).hom (hS.lesγ' h₁ h₂ h₃ k i) = hS.lesρ h₁ h₂ h₃ k i := by
  rw [lesγ', lesρ, apply_mapBoundaryLift]

/-- A basis of the image of `Hₖ(S.X₁) → Hₖ(S.X₂)`. -/
private def lesφ (k : ℤ) :
    Basis (hS.Idxφ k) F (LinearMap.range (HomologicalComplex.homologyMap S.f k).hom) :=
  hS.mapBoundaryBasis h₁ h₂ h₃ (3 * k + 1)
    (hS.lesIso₁ (3 * k + 1 + 1) k (by ring)).toLinearEquiv
    (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv _
    fun x ↦ by simpa using hS.lesIso₂_d _ _ rfl x

/-- Lifts through `Hₖ(S.X₁) → Hₖ(S.X₂)` of the basis `lesφ`. -/
private def lesψ (k : ℤ) (i : hS.Idxφ k) : S.X₁.homology k :=
  (hS.lesIso₁ (3 * k + 1 + 1) k (by ring)).toLinearEquiv
    (hS.lesBoundaryLift h₁ h₂ h₃ (3 * k + 1) i)

private theorem coe_lesφ (k : ℤ) (i) :
    (hS.lesφ h₁ h₂ h₃ k i : S.X₂.homology k) =
      (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv
        (hS.lesBoundaryBasis h₁ h₂ h₃ (3 * k + 1) i) := by
  rw [lesφ, coe_mapBoundaryBasis]

private theorem homologyMap_lesψ (k : ℤ) (i) :
    (HomologicalComplex.homologyMap S.f k).hom (hS.lesψ h₁ h₂ h₃ k i) = hS.lesφ h₁ h₂ h₃ k i := by
  rw [lesψ, lesφ, apply_mapBoundaryLift]

/-- A basis of the image of `Hₖ(S.X₂) → Hₖ(S.X₃)`. -/
private def lesγ (k : ℤ) :
    Basis (hS.Idxγ k) F (LinearMap.range (HomologicalComplex.homologyMap S.g k).hom) :=
  hS.mapBoundaryBasis h₁ h₂ h₃ (3 * k)
    (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv
    (hS.lesIso₃ (3 * k) k rfl).toLinearEquiv _
    fun x ↦ by simpa using hS.lesIso₃_d _ _ rfl x

/-- Lifts through `Hₖ(S.X₂) → Hₖ(S.X₃)` of the basis `lesγ`. -/
private def lesσ (k : ℤ) (i : hS.Idxγ k) : S.X₂.homology k :=
  (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv
    (hS.lesBoundaryLift h₁ h₂ h₃ (3 * k) i)

private theorem coe_lesγ (k : ℤ) (i) :
    (hS.lesγ h₁ h₂ h₃ k i : S.X₃.homology k) =
      (hS.lesIso₃ (3 * k) k rfl).toLinearEquiv
        (hS.lesBoundaryBasis h₁ h₂ h₃ (3 * k) i) := by
  rw [lesγ, coe_mapBoundaryBasis]

private theorem homologyMap_lesσ (k : ℤ) (i) :
    (HomologicalComplex.homologyMap S.g k).hom (hS.lesσ h₁ h₂ h₃ k i) = hS.lesγ h₁ h₂ h₃ k i := by
  rw [lesσ, lesγ, apply_mapBoundaryLift]

/-- The chosen boundary basis in a degree `n = 3k + 2` is `lesρ`, up to reindexing. -/
private theorem exists_lesIso₁_lesBoundaryBasis (k n : ℤ) (hn : n = 3 * k + 2) :
    ∃ e : Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (n + 1) n).hom)) ≃
        hS.Idxρ k,
      ∀ i, (hS.lesIso₁ n k hn).toLinearEquiv
          (hS.lesBoundaryBasis h₁ h₂ h₃ n i) = hS.lesρ h₁ h₂ h₃ k (e i) := by
  subst hn
  exact ⟨Equiv.refl _, fun i ↦ (hS.coe_lesρ h₁ h₂ h₃ k i).symm⟩

/-- The chosen boundary basis in a degree `n = 3k` is `lesγ`, up to reindexing. -/
private theorem exists_lesIso₃_lesBoundaryBasis (k n : ℤ) (hn : n = 3 * k) :
    ∃ e : Fin (finrank F (LinearMap.range (hS.homologySequenceComplex.d (n + 1) n).hom)) ≃
        hS.Idxγ k,
      ∀ i, (hS.lesIso₃ n k hn).toLinearEquiv
          (hS.lesBoundaryBasis h₁ h₂ h₃ n i) = hS.lesγ h₁ h₂ h₃ k (e i) := by
  subst hn
  exact ⟨Equiv.refl _, fun i ↦ (hS.coe_lesγ h₁ h₂ h₃ k i).symm⟩

/-- The bracket of the based long exact sequence in degree `n + 1`, for the chosen boundary bases
and lifts. -/
private abbrev lesBracket (n : ℤ) : F :=
  HomologicalComplex.torsionBracket (hS.lesBasis h₁ h₂ h₃) (by simp) (by simp)
    (hS.acyclic_homologySequenceComplex (n + 1)) (hS.lesBoundaryBasis h₁ h₂ h₃ (n + 1))
    (hS.lesBoundaryBasis h₁ h₂ h₃ n) (hS.lesBoundaryLift h₁ h₂ h₃ n)
    (HomologicalComplex.chosenBoundaryLift_spec _ _ (n + 1) n)

/-- The basis of `Hₖ(S.X₁)` adapted to the long exact sequence: the basis `lesρ k` of the image
of the connecting map followed by the lifts `lesψ k`. -/
private def homologyBasis₁ (k : ℤ) : Basis (hS.Idxρ k ⊕ hS.Idxφ k) F (S.X₁.homology k) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ (k + 1) k rfl)).range_subtype.rangeRestrict
    (hS.lesρ h₁ h₂ h₃ k) (hS.lesφ h₁ h₂ h₃ k) (hS.lesψ h₁ h₂ h₃ k)
    fun i ↦ Subtype.ext (hS.homologyMap_lesψ h₁ h₂ h₃ k i)

/-- The basis of `Hₖ(S.X₂)` adapted to the long exact sequence: the basis `lesφ k` of the image
of `Hₖ(S.X₁)` followed by the lifts `lesσ k`. -/
private def homologyBasis₂ (k : ℤ) : Basis (hS.Idxφ k ⊕ hS.Idxγ k) F (S.X₂.homology k) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ k)).range_subtype.rangeRestrict
    (hS.lesφ h₁ h₂ h₃ k) (hS.lesγ h₁ h₂ h₃ k) (hS.lesσ h₁ h₂ h₃ k)
    fun i ↦ Subtype.ext (hS.homologyMap_lesσ h₁ h₂ h₃ k i)

/-- The basis of `Hₖ₊₁(S.X₃)` adapted to the long exact sequence: the basis `lesγ (k + 1)` of the
image of `Hₖ₊₁(S.X₂)` followed by the lifts `lesγ' k`. -/
private def homologyBasis₃ (k : ℤ) :
    Basis (hS.Idxγ (k + 1) ⊕ hS.Idxρ k) F (S.X₃.homology (k + 1)) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ (k + 1) k rfl)).range_subtype.rangeRestrict
    (hS.lesγ h₁ h₂ h₃ (k + 1)) (hS.lesρ h₁ h₂ h₃ k) (hS.lesγ' h₁ h₂ h₃ k)
    fun i ↦ Subtype.ext (hS.δ_lesγ' h₁ h₂ h₃ k i)

/-- The bracket at `Hₖ(S.X₁)` is up to sign the determinant of the adapted basis
`homologyBasis₁ k`. -/
private theorem sq_lesBracket_one (k : ℤ) (e : hS.Idxρ k ⊕ hS.Idxφ k ≃ Fin (m₁ k)) :
    hS.lesBracket h₁ h₂ h₃ (3 * k + 1) ^ 2 =
      (h₁ k).det ((hS.homologyBasis₁ h₁ h₂ h₃ k).reindex e) ^ 2 := by
  obtain ⟨e', he'⟩ := hS.exists_lesIso₁_lesBoundaryBasis h₁ h₂ h₃ k (3 * k + 1 + 1) (by ring)
  rw [Basis.coe_reindex, homologyBasis₁, Basis.coe_ofExactLift]
  exact HomologicalComplex.sq_torsionBracket_eq_sq_det _ _ _ _ _ _ _ _
    (hS.lesIso₁ (3 * k + 1 + 1) k (by ring)).toLinearEquiv (h₁ k)
    (finCongr (ChainComplex.interleave.rank_of_eq_three_mul_add_two (by ring)))
    (fun i ↦ (Iso.toLinearEquiv_apply _ _).trans
      (ChainComplex.interleave.XIso₁_hom_basis _ _ _ h₁ h₂ h₃ _ i))
    _ _ e' he' (fun _ ↦ by rw [lesψ]) e.symm

/-- The bracket at `Hₖ(S.X₂)` is up to sign the determinant of the adapted basis
`homologyBasis₂ k`. -/
private theorem sq_lesBracket_two (k : ℤ) (e : hS.Idxφ k ⊕ hS.Idxγ k ≃ Fin (m₂ k)) :
    hS.lesBracket h₁ h₂ h₃ (3 * k) ^ 2 =
      (h₂ k).det ((hS.homologyBasis₂ h₁ h₂ h₃ k).reindex e) ^ 2 := by
  rw [Basis.coe_reindex, homologyBasis₂, Basis.coe_ofExactLift]
  exact HomologicalComplex.sq_torsionBracket_eq_sq_det _ _ _ _ _ _ _ _
    (hS.lesIso₂ (3 * k + 1) k rfl).toLinearEquiv (h₂ k)
    (finCongr (ChainComplex.interleave.rank_of_eq_three_mul_add_one rfl))
    (fun i ↦ (Iso.toLinearEquiv_apply _ _).trans
      (ChainComplex.interleave.XIso₂_hom_basis _ _ _ h₁ h₂ h₃ _ i))
    _ _ (.refl _) (fun i ↦ (hS.coe_lesφ h₁ h₂ h₃ k i).symm)
    (fun _ ↦ by rw [lesσ])
    e.symm

/-- The bracket at `Hₖ₊₁(S.X₃)`, in degree `3k + 3`, is up to sign the determinant of the adapted
basis `homologyBasis₃ k`. -/
private theorem sq_lesBracket_three (k : ℤ)
    (e : hS.Idxγ (k + 1) ⊕ hS.Idxρ k ≃ Fin (m₃ (k + 1))) :
    hS.lesBracket h₁ h₂ h₃ (3 * k + 2) ^ 2 =
      (h₃ (k + 1)).det ((hS.homologyBasis₃ h₁ h₂ h₃ k).reindex e) ^ 2 := by
  obtain ⟨e', he'⟩ :=
    hS.exists_lesIso₃_lesBoundaryBasis h₁ h₂ h₃ (k + 1) (3 * k + 2 + 1) (by ring)
  rw [Basis.coe_reindex, homologyBasis₃, Basis.coe_ofExactLift]
  exact HomologicalComplex.sq_torsionBracket_eq_sq_det _ _ _ _ _ _ _ _
    (hS.lesIso₃ (3 * k + 2 + 1) (k + 1) (by ring)).toLinearEquiv
    (h₃ (k + 1)) (finCongr (ChainComplex.interleave.rank_of_eq_three_mul (by ring)))
    (fun i ↦ (Iso.toLinearEquiv_apply _ _).trans
      (ChainComplex.interleave.XIso₃_hom_basis _ _ _ h₁ h₂ h₃ _ i))
    _ _ e' he' (fun _ ↦ by rw [lesγ']) e.symm

/-! ### Adapted choices in the middle term -/

section Middle

variable {n₁ n₃ : ℤ → ℕ} (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
  (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))

/-- The class `lesγ' k i` lifts to an element of `S.X₂` whose boundary is the image of a cycle
representing its image `lesρ k i` under the connecting map. -/
private theorem exists_liftδ (k : ℤ) (i : hS.Idxρ k) :
    ∃ (x₂ : S.X₂.X (k + 1)) (z₃ : S.X₃.cycles (k + 1)),
      (S.X₂.d (k + 1) k).hom x₂ = (S.f.f k).hom ((S.X₁.iCycles k).hom
        (HomologicalComplex.chosenCycle (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k))) ∧
        (S.g.f (k + 1)).hom x₂ = (S.X₃.iCycles (k + 1)).hom z₃ ∧
          (S.X₃.homologyπ (k + 1)).hom z₃ = hS.lesγ' h₁ h₂ h₃ k i :=
  hS.moduleCat_exists_d_eq_of_δ_eq (k + 1) k rfl _ _ <| by
    rw [δ_lesγ', HomologicalComplex.chosenCycle_spec]

/-- The lift of `lesγ' k i` to `S.X₂`. -/
private def liftδ (k : ℤ) (i : hS.Idxρ k) : S.X₂.X (k + 1) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose

/-- The cycle of `S.X₃` represented by the image of `liftδ k i`. -/
private def cycγ' (k : ℤ) (i : hS.Idxρ k) : S.X₃.cycles (k + 1) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose

private theorem d_liftδ (k : ℤ) (i : hS.Idxρ k) :
    (S.X₂.d (k + 1) k).hom (hS.liftδ h₁ h₂ h₃ k i) = (S.f.f k).hom ((S.X₁.iCycles k).hom
      (HomologicalComplex.chosenCycle (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k))) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose_spec.1

private theorem g_liftδ (k : ℤ) (i : hS.Idxρ k) :
    (S.g.f (k + 1)).hom (hS.liftδ h₁ h₂ h₃ k i) =
      (S.X₃.iCycles (k + 1)).hom (hS.cycγ' h₁ h₂ h₃ k i) :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose_spec.2.1

private theorem homologyπ_cycγ' (k : ℤ) (i : hS.Idxρ k) :
    S.X₃.homologyπ (k + 1) (hS.cycγ' h₁ h₂ h₃ k i) = hS.lesγ' h₁ h₂ h₃ k i :=
  (hS.exists_liftδ h₁ h₂ h₃ k i).choose_spec.choose_spec.2.2

/-- The elements of `S.X₁` in degree `k` whose image in `S.X₂` is a boundary. -/
private def boundaryPreimage (k : ℤ) : Submodule F (S.X₁.X k) :=
  (LinearMap.range (S.X₂.d (k + 1) k).hom).comap (S.f.f k).hom

private theorem mem_boundaryPreimage {k : ℤ} {w : S.X₁.X k} :
    w ∈ boundaryPreimage (S := S) k ↔ (S.f.f k).hom w ∈ LinearMap.range (S.X₂.d (k + 1) k).hom :=
  Submodule.mem_comap

private theorem range_le_boundaryPreimage (k : ℤ) :
    LinearMap.range (S.X₁.d (k + 1) k).hom ≤ boundaryPreimage (S := S) k := by
  rintro _ ⟨y, rfl⟩
  exact mem_boundaryPreimage.2 ⟨(S.f.f (k + 1)).hom y, HomologicalComplex.Hom.comm_apply S.f _ _ y⟩

include hS in
private theorem boundaryPreimage_le_ker (k : ℤ) :
    boundaryPreimage (S := S) k ≤ LinearMap.ker (S.X₁.d k (k - 1)).hom := by
  intro w hw
  obtain ⟨y, hy⟩ := mem_boundaryPreimage.1 hw
  rw [LinearMap.mem_ker]
  apply hS.moduleCat_injective_f_f (k - 1)
  rw [map_zero, ← HomologicalComplex.Hom.comm_apply, ← hy]
  exact S.X₂.d_comp_d_apply _ _ _ y

/-- The homology class of an element of `boundaryPreimage k`, a class in the image of the
connecting map. -/
private def boundaryPreimageClass (k : ℤ) :
    boundaryPreimage (S := S) k →ₗ[F] LinearMap.range (hS.δ (k + 1) k rfl).hom :=
  LinearMap.codRestrict _ (S.X₁.moduleCatKerHomologyClass (ChainComplex.next ℤ k) ∘ₗ
    Submodule.inclusion (boundaryPreimage_le_ker hS k)) fun w ↦ by
    obtain ⟨y, hy⟩ := mem_boundaryPreimage.1 w.2
    obtain ⟨z, hz⟩ : ∃ z : S.X₁.cycles k, (S.X₁.iCycles k).hom z = w :=
      ⟨_, S.X₁.iCycles_moduleCatCyclesMk k _ _ (ChainComplex.next ℤ k)
        (boundaryPreimage_le_ker hS k w.2)⟩
    -- The image of `y` in `S.X₃` is a cycle, whose class is sent by the connecting map to the
    -- class of `w`.
    obtain ⟨z₃, hz₃⟩ : ∃ z₃ : S.X₃.cycles (k + 1), (S.X₃.iCycles (k + 1)).hom z₃ =
        (S.g.f (k + 1)).hom y := ⟨_, S.X₃.iCycles_moduleCatCyclesMk (k + 1) _ k
          ((ComplexShape.down ℤ).next_eq' rfl) (by
            rw [HomologicalComplex.Hom.comm_apply, hy]
            exact (hS.moduleCat_exact_f_f_g_f k).apply_apply_eq_zero _)⟩
    refine ⟨(S.X₃.homologyπ (k + 1)).hom z₃, ?_⟩
    rw [hS.moduleCat_δ_homologyπ (k + 1) k rfl z₃ y hz₃.symm z (by rw [hz, hy]),
      LinearMap.comp_apply, S.X₁.moduleCatKerHomologyClass_eq_homologyπ _ z _ hz.symm]

private theorem coe_boundaryPreimageClass_mk (k : ℤ) (z : S.X₁.cycles k)
    (hz : (S.X₁.iCycles k).hom z ∈ boundaryPreimage (S := S) k) :
    (hS.boundaryPreimageClass k ⟨_, hz⟩ : S.X₁.homology k) = S.X₁.homologyπ k z := by
  rw [boundaryPreimageClass, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  exact S.X₁.moduleCatKerHomologyClass_eq_homologyπ _ z _ rfl

private theorem exact_inclusion_boundaryPreimageClass (k : ℤ) :
    Function.Exact (Submodule.inclusion (range_le_boundaryPreimage (S := S) k))
      (hS.boundaryPreimageClass k) := by
  intro w
  have key := S.X₁.exact_inclusion_moduleCatKerHomologyClass (ChainComplex.next ℤ k)
    (ChainComplex.prev ℤ k) (Submodule.inclusion (boundaryPreimage_le_ker hS k) w)
  constructor
  · intro hw
    obtain ⟨a, ha⟩ := key.1 (congrArg Subtype.val hw)
    have ha' := congrArg Subtype.val ha
    exact ⟨a, Subtype.ext ha'⟩
  · rintro ⟨a, rfl⟩
    exact Subtype.ext (key.2 ⟨a, rfl⟩)

/-- The inclusion of `boundaryPreimage k` into the boundaries of `S.X₂` through `S.f`. -/
private def boundaryPreimageMap (k : ℤ) :
    boundaryPreimage (S := S) k →ₗ[F] LinearMap.range (S.X₂.d (k + 1) k).hom :=
  LinearMap.codRestrict _ ((S.f.f k).hom ∘ₗ (boundaryPreimage (S := S) k).subtype) fun w ↦
    mem_boundaryPreimage.1 w.2

private theorem coe_boundaryPreimageMap (k : ℤ) (w : boundaryPreimage (S := S) k) :
    (boundaryPreimageMap k w : S.X₂.X k) = (S.f.f k).hom w :=
  (rfl)

include hS in
private theorem injective_boundaryPreimageMap (k : ℤ) :
    Function.Injective (boundaryPreimageMap (S := S) k) := fun _ _ h ↦
  Subtype.ext (hS.moduleCat_injective_f_f k (congrArg Subtype.val h))

include hS in
private theorem exact_boundaryPreimageMap (k : ℤ) :
    Function.Exact (boundaryPreimageMap (S := S) k) (S.g.boundaryMap (k + 1) k) := by
  rintro ⟨y, hy⟩
  constructor
  · intro h
    have h' : (S.g.f k).hom y = 0 := by simpa using congrArg Subtype.val h
    obtain ⟨w, hw⟩ := (hS.moduleCat_exact_f_f_g_f k y).1 h'
    exact ⟨⟨w, mem_boundaryPreimage.2 (by rw [hw]; exact hy)⟩, Subtype.ext hw⟩
  · rintro ⟨w, h⟩
    rw [← h]
    apply Subtype.ext
    simpa [coe_boundaryPreimageMap] using
      (hS.moduleCat_exact_f_f_g_f k).apply_apply_eq_zero (w : S.X₁.X k)

/-- The chosen boundary bases and lifts of `S.X₁` and `S.X₃`. -/
private abbrev boundaryBasis₁ (k : ℤ) := HomologicalComplex.chosenBoundaryBasis S.X₁ c₁ (k + 1) k

private abbrev boundaryLift₁ (k : ℤ) := HomologicalComplex.chosenBoundaryLift S.X₁ c₁ (k + 1) k

private abbrev boundaryBasis₃ (k : ℤ) := HomologicalComplex.chosenBoundaryBasis S.X₃ c₃ (k + 1) k

private abbrev boundaryLift₃ (k : ℤ) := HomologicalComplex.chosenBoundaryLift S.X₃ c₃ (k + 1) k

/-- Lifts to `S.X₂` of the lifts of the boundary basis of `S.X₃`. -/
private def liftLift₃ (k : ℤ) (i : Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) :
    S.X₂.X (k + 1) :=
  Function.surjInv (hS.moduleCat_surjective_g_f (k + 1)) (boundaryLift₃ c₃ k i)

private theorem g_liftLift₃ (k : ℤ) (i : Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) :
    (S.g.f (k + 1)).hom (hS.liftLift₃ c₃ k i) = boundaryLift₃ c₃ k i :=
  Function.surjInv_eq (hS.moduleCat_surjective_g_f (k + 1)) _

/-- The basis of the boundaries of `S.X₂` in degree `k` made of the images of the boundary basis
of `S.X₁`, the images of cycles representing `lesρ k`, and the boundaries of the lifts
`liftLift₃ k`. -/
private def boundaryBasis₂ (k : ℤ) :
    Basis ((Fin (finrank F (LinearMap.range (S.X₁.d (k + 1) k).hom)) ⊕ hS.Idxρ k) ⊕
      Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) F
      (LinearMap.range (S.X₂.d (k + 1) k).hom) :=
  Basis.ofExactLift (injective_boundaryPreimageMap hS k) (exact_boundaryPreimageMap hS k)
    (Basis.ofExactLift (Submodule.inclusion_injective _)
      (hS.exact_inclusion_boundaryPreimageClass k) (boundaryBasis₁ c₁ k) (hS.lesρ h₁ h₂ h₃ k)
      (fun i ↦ ⟨(S.X₁.iCycles k).hom
          (HomologicalComplex.chosenCycle (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k)),
        mem_boundaryPreimage.2 ⟨hS.liftδ h₁ h₂ h₃ k i, hS.d_liftδ h₁ h₂ h₃ k i⟩⟩)
      fun i ↦ Subtype.ext ((hS.coe_boundaryPreimageClass_mk k _ _).trans
        (HomologicalComplex.chosenCycle_spec _)))
    (boundaryBasis₃ c₃ k)
    (fun i ↦ ⟨(S.X₂.d (k + 1) k).hom (hS.liftLift₃ c₃ k i), _, rfl⟩)
    fun i ↦ Subtype.ext <| by
      rw [HomologicalComplex.Hom.coe_boundaryMap, ← HomologicalComplex.Hom.comm_apply,
        hS.g_liftLift₃, HomologicalComplex.chosenBoundaryLift_spec]

private theorem boundaryBasis₂_inl_inl (k : ℤ) (i) :
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k (.inl (.inl i)) : S.X₂.X k) =
      (S.f.f k).hom (boundaryBasis₁ c₁ k i) := by
  simp [boundaryBasis₂, coe_boundaryPreimageMap]

private theorem boundaryBasis₂_inl_inr (k : ℤ) (i) :
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k (.inl (.inr i)) : S.X₂.X k) =
      (S.f.f k).hom ((S.X₁.iCycles k).hom
        (HomologicalComplex.chosenCycle (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k))) := by
  simp [boundaryBasis₂, coe_boundaryPreimageMap]

private theorem boundaryBasis₂_inr (k : ℤ) (i) :
    (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k (.inr i) : S.X₂.X k) =
      (S.X₂.d (k + 1) k).hom (hS.liftLift₃ c₃ k i) := by
  simp [boundaryBasis₂]

/-- Lifts through the differential of `S.X₂` of the basis `boundaryBasis₂ k`. -/
private def boundaryLift₂ (k : ℤ) :
    ((Fin (finrank F (LinearMap.range (S.X₁.d (k + 1) k).hom)) ⊕ hS.Idxρ k) ⊕
      Fin (finrank F (LinearMap.range (S.X₃.d (k + 1) k).hom))) → S.X₂.X (k + 1) :=
  Sum.elim (Sum.elim (fun i ↦ (S.f.f (k + 1)).hom (boundaryLift₁ c₁ k i)) (hS.liftδ h₁ h₂ h₃ k))
    (hS.liftLift₃ c₃ k)

private theorem d_boundaryLift₂ (k : ℤ) (i) :
    (S.X₂.d (k + 1) k).hom (hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ k i) =
      hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k i := by
  rcases i with (i | i) | i
  · rw [boundaryBasis₂_inl_inl, boundaryLift₂, Sum.elim_inl, Sum.elim_inl,
      HomologicalComplex.Hom.comm_apply, HomologicalComplex.chosenBoundaryLift_spec]
  · rw [boundaryBasis₂_inl_inr, boundaryLift₂, Sum.elim_inl, Sum.elim_inr, hS.d_liftδ]
  · rw [boundaryBasis₂_inr, boundaryLift₂, Sum.elim_inr]

/-- The boundary basis and lifts of `S.X₂`, reindexed by `Fin` for the brackets. -/
private abbrev bracketBasis₂ (k : ℤ) :=
  (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ k).reindex (Fintype.equivFin _)

private abbrev bracketLift₂ (k : ℤ) :=
  hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ k ∘ (Fintype.equivFin _).symm

private theorem d_bracketLift₂ (k : ℤ) (i) :
    (S.X₂.d (k + 1) k).hom (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ k i) =
      hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ k i := by
  simp [d_boundaryLift₂]

/-- Cycles of `S.X₁` representing the adapted basis `homologyBasis₁ k`. -/
private def adaptedCycles₁ (k : ℤ) : hS.Idxρ k ⊕ hS.Idxφ k → S.X₁.cycles k :=
  Sum.elim (fun i ↦ HomologicalComplex.chosenCycle (hS.lesρ h₁ h₂ h₃ k i : S.X₁.homology k))
    fun i ↦ HomologicalComplex.chosenCycle (hS.lesψ h₁ h₂ h₃ k i)

/-- Cycles of `S.X₂` representing the adapted basis `homologyBasis₂ k`. -/
private def adaptedCycles₂ (k : ℤ) : hS.Idxφ k ⊕ hS.Idxγ k → S.X₂.cycles k :=
  Sum.elim (fun i ↦ HomologicalComplex.cyclesMap S.f k
      (HomologicalComplex.chosenCycle (hS.lesψ h₁ h₂ h₃ k i)))
    fun i ↦ HomologicalComplex.chosenCycle (hS.lesσ h₁ h₂ h₃ k i)

/-- Cycles of `S.X₃` representing the adapted basis `homologyBasis₃ k`. -/
private def adaptedCycles₃ (k : ℤ) : hS.Idxγ (k + 1) ⊕ hS.Idxρ k → S.X₃.cycles (k + 1) :=
  Sum.elim (fun i ↦ HomologicalComplex.cyclesMap S.g (k + 1)
      (HomologicalComplex.chosenCycle (hS.lesσ h₁ h₂ h₃ (k + 1) i)))
    (hS.cycγ' h₁ h₂ h₃ k)

private theorem homologyπ_adaptedCycles₁ (k : ℤ) (i) :
    S.X₁.homologyπ k (hS.adaptedCycles₁ h₁ h₂ h₃ k i) = hS.homologyBasis₁ h₁ h₂ h₃ k i := by
  rcases i with i | i <;> simp [adaptedCycles₁, homologyBasis₁]

private theorem homologyπ_adaptedCycles₂ (k : ℤ) (i) :
    S.X₂.homologyπ k (hS.adaptedCycles₂ h₁ h₂ h₃ k i) = hS.homologyBasis₂ h₁ h₂ h₃ k i := by
  rcases i with i | i
  · simp [adaptedCycles₂, homologyBasis₂, ← HomologicalComplex.moduleCat_homologyMap_homologyπ,
      homologyMap_lesψ]
  · simp [adaptedCycles₂, homologyBasis₂]

private theorem homologyπ_adaptedCycles₃ (k : ℤ) (i) :
    S.X₃.homologyπ (k + 1) (hS.adaptedCycles₃ h₁ h₂ h₃ k i) = hS.homologyBasis₃ h₁ h₂ h₃ k i := by
  rcases i with i | i
  · simp [adaptedCycles₃, homologyBasis₃, ← HomologicalComplex.moduleCat_homologyMap_homologyπ,
      homologyMap_lesσ]
  · simp [adaptedCycles₃, homologyBasis₃, homologyπ_cycγ']

/-- With the adapted choices, the family of the bracket of `S.X₂` in degree `j + 1` is assembled
from those of `S.X₁` and `S.X₃`, so its determinant is, up to sign, the product of theirs, in
whatever orders `e₁`, `e₂`, `e₃` the three families are read. -/
private theorem sq_det_adapted {c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i)}
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k) (j : ℤ)
    (e₁ : Fin (n₁ (j + 1)) ≃ _) (e₂ : Fin (n₁ (j + 1) + n₃ (j + 1)) ≃ _)
    (e₃ : Fin (n₃ (j + 1)) ≃ _) :
    (c₂ (j + 1)).det (Sum.elim (Sum.elim
        (fun k ↦ (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1) k : S.X₂.X (j + 1)))
        fun k ↦ S.X₂.iCycles (j + 1) (hS.adaptedCycles₂ h₁ h₂ h₃ (j + 1) k))
        (hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ j) ∘ e₂) ^ 2 =
      ((c₁ (j + 1)).det (Sum.elim (Sum.elim (fun k ↦ (boundaryBasis₁ c₁ (j + 1) k : S.X₁.X (j + 1)))
          fun k ↦ S.X₁.iCycles (j + 1) (hS.adaptedCycles₁ h₁ h₂ h₃ (j + 1) k))
          (boundaryLift₁ c₁ j) ∘ e₁) *
        (c₃ (j + 1)).det (Sum.elim (Sum.elim
          (fun k ↦ (boundaryBasis₃ c₃ (j + 1) k : S.X₃.X (j + 1)))
          fun k ↦ S.X₃.iCycles (j + 1) (hS.adaptedCycles₃ h₁ h₂ h₃ j k))
          (boundaryLift₃ c₃ j) ∘ e₃)) ^ 2 := by
  rw [Basis.eq_reindex_ofExactLift (hS.moduleCat_injective_f_f (j + 1))
    (hS.moduleCat_exact_f_f_g_f (j + 1)) (c₁ (j + 1)) (c₃ (j + 1)) (c₂ (j + 1)) (hc₁ (j + 1))
    (hc₃ (j + 1)), Basis.det_reindex, Function.comp_assoc, ← Equiv.coe_trans,
    Basis.det_comp_equiv _ _ _ ((Equiv.sumCongr e₁ e₃).trans (regroupEquiv _ _ _ _ _ _ _ _)),
    smul_pow, Int.units_sq, one_smul,
    Basis.ofExactLift_det_eq_mul _ _ _ _ _ _ _ _ _ (fun i ↦ ?_) (fun i ↦ ?_)]
  · simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
    generalize e₁ i = t
    rcases t with ((a | r | x) | q)
    · simp [regroupEquiv, boundaryBasis₂_inl_inl]
    · simp [regroupEquiv, boundaryBasis₂_inl_inr, adaptedCycles₁]
    · simp [regroupEquiv, adaptedCycles₁, adaptedCycles₂]
    · simp [regroupEquiv, boundaryLift₂]
  · simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr]
    generalize e₃ i = t
    rcases t with ((a | x | r) | q)
    · simp [regroupEquiv, boundaryBasis₂_inr, ← HomologicalComplex.Hom.comm_apply, g_liftLift₃]
    · simp [regroupEquiv, adaptedCycles₂, adaptedCycles₃]
    · simp [regroupEquiv, boundaryLift₂, g_liftδ, adaptedCycles₃]
    · simp [regroupEquiv, boundaryLift₂, g_liftLift₃]

/-- **The bracket of the middle term in one degree.** With the adapted choices, the bracket of
`S.X₂` in degree `j + 1` is, up to sign, the product of the brackets of `S.X₁` and `S.X₃` and of
the three brackets of the based long exact sequence at `Hⱼ₊₁(S.X₁)`, `Hⱼ₊₁(S.X₃)` and
`Hⱼ₊₁(S.X₂)`, the last one inverted. -/
private theorem sq_torsionBracketWithHomology {c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i)}
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (y₁ : ∀ i, Fin (m₁ i) → S.X₁.cycles i) (hy₁ : ∀ i k, S.X₁.homologyπ i (y₁ i k) = h₁ i k)
    (y₂ : ∀ i, Fin (m₂ i) → S.X₂.cycles i) (hy₂ : ∀ i k, S.X₂.homologyπ i (y₂ i k) = h₂ i k)
    (y₃ : ∀ i, Fin (m₃ i) → S.X₃.cycles i) (hy₃ : ∀ i k, S.X₃.homologyπ i (y₃ i k) = h₃ i k)
    (j : ℤ) :
    HomologicalComplex.torsionBracketWithHomology c₂ (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1))
        (h₂ (j + 1)) (y₂ (j + 1)) (hy₂ (j + 1)) (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ j)
        (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ j) (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃ j) ^ 2 =
      (HomologicalComplex.torsionBracketWithHomology c₁ (boundaryBasis₁ c₁ (j + 1)) (h₁ (j + 1))
          (y₁ (j + 1)) (hy₁ (j + 1)) (boundaryBasis₁ c₁ j) (boundaryLift₁ c₁ j)
          (HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j) *
        HomologicalComplex.torsionBracketWithHomology c₃ (boundaryBasis₃ c₃ (j + 1)) (h₃ (j + 1))
          (y₃ (j + 1)) (hy₃ (j + 1)) (boundaryBasis₃ c₃ j) (boundaryLift₃ c₃ j)
          (HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j) *
        (hS.lesBracket h₁ h₂ h₃ (3 * (j + 1) + 1) * hS.lesBracket h₁ h₂ h₃ (3 * j + 2) *
          (hS.lesBracket h₁ h₂ h₃ (3 * (j + 1)))⁻¹)) ^ 2 := by
  -- Compute the three brackets with the adapted homology bases and their representatives.
  obtain ⟨e₁, he₁⟩ := HomologicalComplex.exists_det_comp_eq_torsionBracketWithHomology_mul c₁
    (boundaryBasis₁ c₁ (j + 1)) (h₁ (j + 1)) (y₁ (j + 1)) (hy₁ (j + 1)) (boundaryBasis₁ c₁ j)
    (boundaryLift₁ c₁ j) (HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j) (.refl _)
    (.refl _) (fun k ↦ (boundaryBasis₁ c₁ (j + 1) k : S.X₁.X (j + 1))) (fun _ ↦ rfl)
    (boundaryLift₁ c₁ j) (fun _ ↦ rfl) (hS.homologyBasis₁ h₁ h₂ h₃ (j + 1)) _
    (hS.homologyπ_adaptedCycles₁ h₁ h₂ h₃ (j + 1))
  obtain ⟨e₂, he₂⟩ := HomologicalComplex.exists_det_comp_eq_torsionBracketWithHomology_mul c₂
    (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1)) (h₂ (j + 1)) (y₂ (j + 1)) (hy₂ (j + 1))
    (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃ j) (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃ j)
    (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃ j) (Fintype.equivFin _) (Fintype.equivFin _)
    (fun k ↦ (hS.boundaryBasis₂ h₁ h₂ h₃ c₁ c₃ (j + 1) k : S.X₂.X (j + 1))) (fun _ ↦ by simp)
    (hS.boundaryLift₂ h₁ h₂ h₃ c₁ c₃ j) (fun _ ↦ by simp) (hS.homologyBasis₂ h₁ h₂ h₃ (j + 1)) _
    (hS.homologyπ_adaptedCycles₂ h₁ h₂ h₃ (j + 1))
  obtain ⟨e₃, he₃⟩ := HomologicalComplex.exists_det_comp_eq_torsionBracketWithHomology_mul c₃
    (boundaryBasis₃ c₃ (j + 1)) (h₃ (j + 1)) (y₃ (j + 1)) (hy₃ (j + 1)) (boundaryBasis₃ c₃ j)
    (boundaryLift₃ c₃ j) (HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j) (.refl _)
    (.refl _) (fun k ↦ (boundaryBasis₃ c₃ (j + 1) k : S.X₃.X (j + 1))) (fun _ ↦ rfl)
    (boundaryLift₃ c₃ j) (fun _ ↦ rfl) (hS.homologyBasis₃ h₁ h₂ h₃ j) _
    (hS.homologyπ_adaptedCycles₃ h₁ h₂ h₃ j)
  have core := hS.sq_det_adapted h₁ h₂ h₃ c₁ c₃ hc₁ hc₃ j e₁ e₂ e₃
  rw [he₁, he₂, he₃] at core
  -- The determinants comparing the adapted homology bases with the given ones are the brackets
  -- of the based long exact sequence, up to sign.
  simp only [mul_pow, inv_pow]
  rw [hS.sq_lesBracket_one h₁ h₂ h₃ (j + 1)
      ((hS.homologyBasis₁ h₁ h₂ h₃ (j + 1)).indexEquiv (h₁ (j + 1))),
    hS.sq_lesBracket_two h₁ h₂ h₃ (j + 1)
      ((hS.homologyBasis₂ h₁ h₂ h₃ (j + 1)).indexEquiv (h₂ (j + 1))),
    hS.sq_lesBracket_three h₁ h₂ h₃ j
      ((hS.homologyBasis₃ h₁ h₂ h₃ j).indexEquiv (h₃ (j + 1)))]
  have hD : (h₂ (j + 1)).det ((hS.homologyBasis₂ h₁ h₂ h₃ (j + 1)).reindex
      ((hS.homologyBasis₂ h₁ h₂ h₃ (j + 1)).indexEquiv (h₂ (j + 1)))) ≠ 0 :=
    (Basis.isUnit_det _ _).ne_zero
  field_simp
  linear_combination core

end Middle

end CategoryTheory.ShortComplex.ShortExact

/-! ### Milnor's formula -/

/-- The comparison of brackets in degree `j + 1`, raised to the power `(-1) ^ j`, with the
brackets of the long exact sequence raised to the powers of their own degrees. -/
private theorem sq_zpow_negOnePow {b₁ b₂ b₃ k₁ k₂ k₃ : F} {j : ℤ}
    (h : b₂ ^ 2 = (b₁ * b₃ * (k₁ * k₃ * k₂⁻¹)) ^ 2) :
    (b₂ ^ (j.negOnePow : ℤ)) ^ 2 = (b₁ ^ (j.negOnePow : ℤ) * b₃ ^ (j.negOnePow : ℤ) *
      (k₃ ^ ((3 * j + 2).negOnePow : ℤ) * k₂ ^ ((3 * (j + 1)).negOnePow : ℤ) *
        k₁ ^ ((3 * (j + 1) + 1).negOnePow : ℤ))) ^ 2 := by
  have e₁ : (3 * j + 2).negOnePow = j.negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨j + 1, by ring⟩
  have e₂ : (3 * (j + 1)).negOnePow = -j.negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨j + 1, by ring⟩
  have e₃ : (3 * (j + 1) + 1).negOnePow = j.negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨j + 2, by ring⟩
  have hsq (x : F) : (x ^ (j.negOnePow : ℤ)) ^ 2 = (x ^ 2) ^ (j.negOnePow : ℤ) := by
    rw [sq, sq, mul_zpow]
  rw [e₁, e₂, e₃, Units.val_neg, zpow_neg, hsq, h, ← hsq]
  simp only [mul_zpow, inv_zpow]
  ring

/-- Regroup a finitely supported product over `ℤ` by the residues modulo `3`, in the order in which
the long exact homology sequence meets them: the degrees `3j + 2`, `3(j + 1)` and `3(j + 1) + 1`,
at the homology of `C₃`, `C₂` and `C₁` respectively. -/
private theorem finprod_eq_finprod_regroup {M : Type*} [CommMonoid M] {G : ℤ → M}
    (hG : Function.HasFiniteMulSupport G) :
    ∏ᶠ n, G n = ∏ᶠ j, G (3 * j + 2) * G (3 * (j + 1)) * G (3 * (j + 1) + 1) := by
  rw [← finprod_comp_equiv (Equiv.addRight (2 : ℤ))]
  simp only [Equiv.coe_addRight]
  rw [TauCeti.finprod_eq_finprod_prod_mul_add 3 _
    (hG.fun_comp_of_injective (g := fun n : ℤ ↦ n + 2) (add_left_injective 2))]
  refine finprod_congr fun j ↦ ?_
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  rw [show j * 3 + 0 + 2 = 3 * j + 2 by ring, show j * 3 + 1 + 2 = 3 * (j + 1) by ring,
    show j * 3 + 2 + 2 = 3 * (j + 1) + 1 by ring]

/-- The factors of the regrouping `finprod_eq_finprod_regroup` have finite support. -/
private theorem hasFiniteMulSupport_regroup {M : Type*} [CommMonoid M] {G : ℤ → M}
    (hG : Function.HasFiniteMulSupport G) :
    Function.HasFiniteMulSupport fun j ↦ G (3 * j + 2) * G (3 * (j + 1)) * G (3 * (j + 1) + 1) :=
  ((hG.fun_comp_of_injective (g := fun j : ℤ ↦ 3 * j + 2) fun _ _ h ↦ by simpa using h).fun_mul
    (hG.fun_comp_of_injective (g := fun j : ℤ ↦ 3 * (j + 1)) fun _ _ h ↦ by simpa using h)).fun_mul
    (hG.fun_comp_of_injective (g := fun j : ℤ ↦ 3 * (j + 1) + 1) fun _ _ h ↦ by simpa using h)

/-- **Milnor's multiplicativity formula.** Let `0 → C₁ → C₂ → C₃ → 0` be a short exact sequence
of chain complexes of vector spaces, with compatible bases: the basis `c₂ i` of `C₂ᵢ` is the image
of the basis `c₁ i` of `C₁ᵢ` followed by lifts of the basis `c₃ i` of `C₃ᵢ`. For any bases
`h₁`, `h₂`, `h₃` of the homology groups,
`τ(C₂, c₂, h₂) = ± τ(C₁, c₁, h₁) · τ(C₃, c₃, h₃) · τ(H)`, where `H` is the long exact homology
sequence based by `h₁`, `h₂`, `h₃`. This holds for all complexes, both sides being `0` when the
complexes are unbounded. -/
theorem HomologicalComplex.reidemeisterTorsionWithHomology_eq_or_eq_neg_mul_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k) {m₁ m₂ m₃ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
        S.X₁.reidemeisterTorsionWithHomology c₁ h₁ * S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
          hS.homologySequenceComplex.reidemeisterTorsion
            (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃) ∨
      S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
        -(S.X₁.reidemeisterTorsionWithHomology c₁ h₁ * S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
          hS.homologySequenceComplex.reidemeisterTorsion
            (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃)) := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  have hset : {i | n₁ i + n₃ i ≠ 0} = {i | n₁ i ≠ 0} ∪ {i | n₃ i ≠ 0} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    omega
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · -- One of the outer terms is unbounded, so both sides are `0`.
    rw [HomologicalComplex.reidemeisterTorsionWithHomology_of_not_finite (hn := hn)]
    rw [hset, Set.finite_union, not_and_or] at hn
    rcases hn with hn | hn <;> simp [hn]
  obtain ⟨hn₁, hn₃⟩ := Set.finite_union.1 (hset ▸ hn)
  have hnK := ChainComplex.interleave.finite_setOf_rank_ne_zero
    (HomologicalComplex.finite_setOf_card_basis_homology_ne_zero c₁ h₁ hn₁)
    (HomologicalComplex.finite_setOf_card_basis_homology_ne_zero c₂ h₂ hn)
    (HomologicalComplex.finite_setOf_card_basis_homology_ne_zero c₃ h₃ hn₃)
  -- Cycles representing the homology bases.
  let y₁ (i : ℤ) (k : Fin (m₁ i)) := HomologicalComplex.chosenCycle (h₁ i k)
  let y₂ (i : ℤ) (k : Fin (m₂ i)) := HomologicalComplex.chosenCycle (h₂ i k)
  let y₃ (i : ℤ) (k : Fin (m₃ i)) := HomologicalComplex.chosenCycle (h₃ i k)
  have hy₁ (i : ℤ) (k) : S.X₁.homologyπ i (y₁ i k) = h₁ i k := HomologicalComplex.chosenCycle_spec _
  have hy₂ (i : ℤ) (k) : S.X₂.homologyπ i (y₂ i k) = h₂ i k := HomologicalComplex.chosenCycle_spec _
  have hy₃ (i : ℤ) (k) : S.X₃.homologyπ i (y₃ i k) = h₃ i k := HomologicalComplex.chosenCycle_spec _
  -- Expand the four torsions as alternating products of brackets.
  have hK := HomologicalComplex.hasFiniteMulSupport_torsionBracket
    (c := hS.lesBasis h₁ h₂ h₃) hnK hS.acyclic_homologySequenceComplex
    (hS.lesBoundaryBasis h₁ h₂ h₃) (hS.lesBoundaryLift h₁ h₂ h₃)
    fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j
  rw [HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn
      (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃) y₂ hy₂ (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃)
      (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃),
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn₁
      (ShortComplex.ShortExact.boundaryBasis₁ c₁) y₁ hy₁
      (ShortComplex.ShortExact.boundaryLift₁ c₁)
      (fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j),
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn₃
      (ShortComplex.ShortExact.boundaryBasis₃ c₃) y₃ hy₃
      (ShortComplex.ShortExact.boundaryLift₃ c₃)
      (fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j),
    HomologicalComplex.reidemeisterTorsion_eq_finprod hnK hS.acyclic_homologySequenceComplex
      (hS.lesBoundaryBasis h₁ h₂ h₃) (hS.lesBoundaryLift h₁ h₂ h₃)
      (fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j),
    finprod_eq_finprod_regroup hK]
  have hs₁ := HomologicalComplex.hasFiniteMulSupport_torsionBracketWithHomology (c := c₁)
    (h := h₁) hn₁ (ShortComplex.ShortExact.boundaryBasis₁ c₁) y₁ hy₁
    (ShortComplex.ShortExact.boundaryLift₁ c₁)
    (fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j)
  have hs₂ := HomologicalComplex.hasFiniteMulSupport_torsionBracketWithHomology (c := c₂)
    (h := h₂) hn (hS.bracketBasis₂ h₁ h₂ h₃ c₁ c₃) y₂ hy₂ (hS.bracketLift₂ h₁ h₂ h₃ c₁ c₃)
    (hS.d_bracketLift₂ h₁ h₂ h₃ c₁ c₃)
  have hs₃ := HomologicalComplex.hasFiniteMulSupport_torsionBracketWithHomology (c := c₃)
    (h := h₃) hn₃ (ShortComplex.ShortExact.boundaryBasis₃ c₃) y₃ hy₃
    (ShortComplex.ShortExact.boundaryLift₃ c₃)
    (fun j ↦ HomologicalComplex.chosenBoundaryLift_spec _ _ (j + 1) j)
  have hsK := hasFiniteMulSupport_regroup hK
  rw [← finprod_mul_distrib hs₁ hs₃, ← finprod_mul_distrib (hs₁.fun_mul hs₃) hsK,
    finprod_pow hs₂, finprod_pow ((hs₁.fun_mul hs₃).fun_mul hsK)]
  -- In each degree, the comparison of brackets raised to the power `(-1) ^ j`.
  exact finprod_congr fun j ↦ sq_zpow_negOnePow
    (hS.sq_torsionBracketWithHomology h₁ h₂ h₃ c₁ c₃ hc₁ hc₃ y₁ hy₁ y₂ hy₂ y₃ hy₃ j)
