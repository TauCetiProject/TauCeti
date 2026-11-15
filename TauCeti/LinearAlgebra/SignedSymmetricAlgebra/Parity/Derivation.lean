/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Supercommutativity
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.Homology.DG.Algebra.Parity
import TauCeti.Algebra.Homology.DG.Algebra.SignedDerivation
import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Parity

/-!
# Odd derivations of the parity-presented signed symmetric algebra

A linear assignment `δ : V → ParitySignedSym G` of parity `1 : ZMod 2` extends uniquely to a
linear endomorphism `d` of `TauCeti.ParitySignedSym G` satisfying the parity signed Leibniz rule

`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)` for `a` of parity `i`.

This extension `TauCeti.ParitySignedSym.liftDerivation` flips parity (`i ↦ i + 1`) without
requiring any integer lift of `G`. Its square is an unsigned derivation, so an odd signed Leibniz
endomorphism squares to zero if and only if its square vanishes on generators. When an integer
grading `H : InternalGrading R V ℤ` is present, `TauCeti.SignedSym.parityEquiv H` intertwines
`TauCeti.SignedSym.liftDerivation` with `TauCeti.ParitySignedSym.liftDerivation`.

Both `TauCeti.SignedSym.liftDerivation` and `TauCeti.ParitySignedSym.liftDerivation` are
instantiations of the general signed-Leibniz and lower-triangular `2 × 2` matrix API in
`TauCeti.Algebra.Homology.DG.Algebra.SignedDerivation`, using
`TauCeti.InternalGrading.parityTwistAlgEquiv` for the parity grade involution.

## Main definitions

* `TauCeti.ParitySignedSym.liftDerivation`: the odd derivation extending a parity-`1` assignment on
  generators.

## Main results

* `TauCeti.ParitySignedSym.liftDerivation_mul` and
  `TauCeti.ParitySignedSym.isHomogeneous_liftDerivation`: the parity Leibniz rule and odd degree
  law.
* `TauCeti.ParitySignedSym.eq_liftDerivation` and
  `TauCeti.ParitySignedSym.existsUnique_odd_extension`: odd derivations are uniquely determined by
  generators.
* `TauCeti.ParitySignedSym.comp_self_eq_zero_iff` and
  `TauCeti.ParitySignedSym.liftDerivation_comp_self_eq_zero_iff`: square-zero reduces to
  generators.
* `TauCeti.SignedSym.parityEquiv_liftDerivation` and
  `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff_parity`: compatibility with integer-graded odd
  derivations under `SignedSym.parityEquiv`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to symplectic field theory*, Section 1.9.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace ParitySignedSym

variable {G : InternalGrading R V (ZMod 2)}

section Lift

variable {δ : V →ₗ[R] ParitySignedSym G}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1)

/-- The algebra map `a ↦ [[a, 0], [d a, σ a]]` whose lower-left entry is the parity extension. -/
private noncomputable def triangularLift :
    ParitySignedSym G →ₐ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) :=
  lift G
    (lowerTriangularLinearMap (generator G) δ
      ((InternalGrading.parityTwistAlgEquiv (paritySignedSymPiece G) :
        ParitySignedSym G →ₐ[R] ParitySignedSym G).toLinearMap ∘ₗ generator G))
    fun _ _ _ _ hx hy =>
      lowerTriangularLinearMap_mul_eq_smul (uzpow_add (-1 : ℤˣ))
        (fun ha hb => mul_eq_uzpow_smul_mul G ha hb)
        (fun ha => InternalGrading.parityTwistAlgEquiv_apply_of_mem (paritySignedSymPiece G) ha)
        (isHomogeneous_paritySignedSymGenerator G) hδ hx hy

variable (δ) in
/-- The odd derivation of `ParitySignedSym G` extending a parity-`1` linear map
`δ : V → ParitySignedSym G`. It satisfies `TauCeti.ParitySignedSym.liftDerivation_mul`, flips
parity (`i ↦ i + 1`), and is the unique such extension of `δ`
(`TauCeti.ParitySignedSym.eq_liftDerivation`). -/
noncomputable def liftDerivation : ParitySignedSym G →ₗ[R] ParitySignedSym G :=
  lowerTriangularDerivation (triangularLift hδ)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation, lowerTriangularDerivation_apply, triangularLift]

/-- **The parity signed Leibniz rule**: for a left factor `a` of parity `i`,
`d (a * b) = d a * b + (-1) ^ i • (a * d b)`. -/
theorem liftDerivation_mul {i : ZMod 2} {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + ((-1 : ℤˣ) ^ i) • (a * liftDerivation δ hδ b) := by
  have h := lowerTriangularDerivation_mul_of_adjoin_range_eq_top (triangularLift hδ)
    (InternalGrading.parityTwistAlgEquiv (paritySignedSymPiece G) :
      ParitySignedSym G →ₐ[R] ParitySignedSym G)
    (adjoin_range_generator G) (lift_generator G _ _) a b
  simpa only [liftDerivation, AlgEquiv.coe_toAlgHom,
    InternalGrading.parityTwistAlgEquiv_apply_of_mem (paritySignedSymPiece G) ha,
    Units.smul_def, smul_mul_assoc] using h

/-- The odd derivation annihilates the coefficients. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) :
    liftDerivation δ hδ (algebraMap R _ r) = 0 :=
  lowerTriangularDerivation_algebraMap (triangularLift hδ) r

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 :=
  lowerTriangularDerivation_one (triangularLift hδ)

/-- The odd derivation has parity `1`, mapping `paritySignedSymPiece G i` into
`paritySignedSymPiece G (i + 1)`. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ)
      (paritySignedSymPiece G) (paritySignedSymPiece G) 1 := by
  have hcomp : liftDerivation δ hδ ∘ₗ generator G = δ :=
    LinearMap.ext (liftDerivation_generator hδ)
  exact isHomogeneous_of_signedLeibniz_of_adjoin_range_eq_top (𝒜 := paritySignedSymPiece G)
    (liftDerivation_mul hδ) (adjoin_range_generator G) G.isInternal.submodule_iSup_eq_top
    (isHomogeneous_paritySignedSymGenerator G) (by rwa [hcomp])

/-- **Uniqueness of parity odd derivations**: a linear endomorphism of `ParitySignedSym G`
satisfying the parity signed Leibniz rule and agreeing with `δ` on generators equals
`liftDerivation δ hδ`. No parity homogeneity assumption on `d` is needed. -/
theorem eq_liftDerivation {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ :=
  eq_of_signedLeibniz_of_adjoin_range_eq_top (𝒜 := paritySignedSymPiece G) hleibniz
    (liftDerivation_mul hδ) (adjoin_range_generator G) fun x =>
      (hgen x).trans (liftDerivation_generator hδ x).symm

end Lift

/-- **Parity odd derivations are free on generators**: a parity-`1` linear map
`δ : V → ParitySignedSym G` extends uniquely to a linear endomorphism satisfying the parity signed
Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    ∃! d : ParitySignedSym G →ₗ[R] ParitySignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
        ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) :=
  ⟨liftDerivation δ hδ, ⟨LinearMap.ext (liftDerivation_generator hδ), liftDerivation_mul hδ⟩,
    fun _ hd => eq_liftDerivation hδ hd.2 fun x => LinearMap.congr_fun hd.1 x⟩

/-- **The square of a parity odd derivation is determined by generators**: a parity-`1` linear
endomorphism of `ParitySignedSym G` satisfying the parity signed Leibniz rule squares to zero if
and only if its square vanishes on generators. -/
theorem comp_self_eq_zero_iff {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (paritySignedSymPiece G) (paritySignedSymPiece G) 1)
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 :=
  comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_range_eq_top hdeg hleibniz
    (fun i => by rw [uzpow_add, uzpow_one, mul_neg, mul_one]) (adjoin_range_generator G)

/-- The odd derivation `liftDerivation δ hδ` squares to zero if and only if it annihilates `δ x`
for every `x : V`. -/
theorem liftDerivation_comp_self_eq_zero_iff {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    liftDerivation δ hδ ∘ₗ liftDerivation δ hδ = 0 ↔
      ∀ x, liftDerivation δ hδ (δ x) = 0 := by
  simpa only [liftDerivation_generator] using
    comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ) (liftDerivation_mul hδ)

end ParitySignedSym

namespace SignedSym

variable {G : InternalGrading R V ℤ}

/-- Pushing a degree-`1` assignment `δ : V → SignedSym G` forward along `SignedSym.parityEquiv G`
produces a parity-`1` assignment into `ParitySignedSym G.parity`. -/
theorem isHomogeneous_parityEquiv_comp {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (paritySignedSymPiece G.parity) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i x hx => ?_
  rw [InternalGrading.parity_piece] at hx
  have h1 : Int.castAddHom (ZMod 2) 1 = 1 := Int.cast_one
  have hmem := (hδ.coarsenGrading (Int.castAddHom (ZMod 2))).map_mem hx
  rw [h1] at hmem
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    mem_paritySignedSymPiece_parityEquiv_iff] using hmem

/-- `SignedSym.parityEquiv G` intertwines `SignedSym.liftDerivation` with
`ParitySignedSym.liftDerivation`. -/
theorem parityEquiv_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) (a : SignedSym G) :
    parityEquiv G (liftDerivation δ hδ a) =
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) (parityEquiv G a) := by
  let d' : ParitySignedSym G.parity →ₗ[R] ParitySignedSym G.parity :=
    (parityEquiv G).toLinearMap ∘ₗ liftDerivation δ hδ ∘ₗ (parityEquiv G).symm.toLinearMap
  have hd' : d' = ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
      (isHomogeneous_parityEquiv_comp hδ) := by
    refine ParitySignedSym.eq_liftDerivation (isHomogeneous_parityEquiv_comp hδ)
      (fun {i b} hb c => ?_) fun x => ?_
    · have hb' : (parityEquiv G).symm b ∈ parityGrading (signedSymPiece G) i :=
        (mem_parityGrading_parityEquiv_symm_iff G).2 hb
      have hl := leibniz_parityGrading_of_leibniz (liftDerivation_mul hδ) hb'
        ((parityEquiv G).symm c)
      simpa only [d', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, map_add,
        Units.smul_def, map_zsmul, AlgEquiv.apply_symm_apply] using congrArg (parityEquiv G) hl
    · simp [d']
  simpa only [d', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply] using LinearMap.congr_fun hd' (parityEquiv G a)

/-- The inverse of `SignedSym.parityEquiv G` intertwines `ParitySignedSym.liftDerivation` with
`SignedSym.liftDerivation`. -/
theorem parityEquiv_symm_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1)
    (b : ParitySignedSym G.parity) :
    (parityEquiv G).symm
      (ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) b) =
      liftDerivation δ hδ ((parityEquiv G).symm b) := by
  apply (parityEquiv G).injective
  simpa only [AlgEquiv.apply_symm_apply] using
    (parityEquiv_liftDerivation hδ ((parityEquiv G).symm b)).symm

/-- For a degree-`1` assignment `δ : V → SignedSym G`, `SignedSym.liftDerivation δ hδ` makes
`SignedSym G` a differential graded algebra if and only if the induced parity odd derivation on
`ParitySignedSym G.parity` squares to zero. -/
theorem isDGAlgebra_liftDerivation_iff_parity {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ) ↔
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) ∘ₗ
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) = 0 := by
  rw [isDGAlgebra_liftDerivation_iff, ParitySignedSym.liftDerivation_comp_self_eq_zero_iff]
  refine forall_congr' fun x => ?_
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← parityEquiv_liftDerivation hδ]
  exact ⟨fun h => by rw [h, map_zero], fun h => (parityEquiv G).injective (by rwa [map_zero])⟩

end SignedSym

end TauCeti
