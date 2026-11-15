/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.Homology.DG.Algebra.SignedDerivation
import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra

/-!
# Odd derivations of the signed symmetric algebra

A linear map `δ : V → A(V)` into the signed symmetric algebra `A(V) = TauCeti.SignedSym G`
which raises degree by one extends uniquely to a linear endomorphism `d` of `A(V)` satisfying
the signed Leibniz rule

`d (a * b) = d a * b + (-1) ^ p • (a * d b)` for `a` of degree `p`.

This extension `TauCeti.SignedSym.liftDerivation` again raises degree by one. Its square is an
unsigned derivation, so it vanishes as soon as it vanishes on generators. Consequently `d` is the
differential of a differential graded algebra structure on `A(V)` exactly when `d (δ x) = 0`
for every `x : V`. This reduces the identity `d ∘ d = 0` for the differential of a free
supercommutative algebra, such as the contact homology differential, to a check on generators.

The extension is constructed through the universal property of `A(V)` and the lower-triangular
`2 × 2` matrix derivation machinery of `TauCeti.Algebra.Homology.DG.Algebra.SignedDerivation`: the
matrices `[[a, 0], [d a, σ a]]`, where `σ` is the grade involution `a ↦ (-1) ^ |a| • a`, multiply
as `a + ε d a` in the dual numbers over `A(V)` with one odd generator `ε`.

## Main definitions

* `TauCeti.SignedSym.liftDerivation`: the odd derivation extending a degree-one assignment on
  generators.

## Main results

* `TauCeti.SignedSym.liftDerivation_mul`: the signed Leibniz rule.
* `TauCeti.SignedSym.isHomogeneous_liftDerivation`: the extension raises degree by one.
* `TauCeti.SignedSym.eq_liftDerivation` and `TauCeti.SignedSym.existsUnique_odd_extension`:
  an odd derivation is determined by its values on generators.
* `TauCeti.SignedSym.comp_self_eq_zero_iff`: a degree-one signed Leibniz map squares to zero if
  and only if its square vanishes on generators.
* `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff`: the extension is a differential graded
  algebra differential if and only if it kills the image of the assignment.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the free
  supercommutative algebra on which the contact homology differential is defined.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {G : InternalGrading R V ℤ}

section Lift

variable {δ : V →ₗ[R] SignedSym G}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1)

/-- The algebra map `a ↦ [[a, 0], [d a, σ a]]` whose lower-left entry is the extension. -/
private noncomputable def triangularLift :
    SignedSym G →ₐ[R] Matrix (Fin 2) (Fin 2) (SignedSym G) :=
  lift G
    (lowerTriangularLinearMap (generator G) δ
      ((InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1 :
        SignedSym G →ₐ[R] SignedSym G).toLinearMap ∘ₗ generator G))
    fun _ _ _ _ hx hy => by
      simpa only [Units.smul_def] using
        lowerTriangularLinearMap_mul_eq_smul Int.negOnePow_add
          (fun ha hb => by
            simpa only [Units.smul_def] using mul_eq_negOnePow_smul_mul G ha hb)
          (fun ha => by
            simpa using InternalGrading.koszulTwistAlgEquiv_apply_of_mem (signedSymPiece G) 1 ha)
          (isHomogeneous_signedSymGenerator G) hδ hx hy

variable (δ) in
/-- The odd derivation of `A(V)` extending a degree-one linear map `δ : V → A(V)`. It satisfies
the signed Leibniz rule `TauCeti.SignedSym.liftDerivation_mul`, raises degree by one, and is the
unique such extension of `δ` (`TauCeti.SignedSym.eq_liftDerivation`). -/
noncomputable def liftDerivation : SignedSym G →ₗ[R] SignedSym G :=
  lowerTriangularDerivation (triangularLift hδ)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation, lowerTriangularDerivation_apply, triangularLift]

/-- **The signed Leibniz rule**: for a left factor of degree `p`,
`d (a * b) = d a * b + (-1) ^ p • (a * d b)`. -/
theorem liftDerivation_mul {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (b : SignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + p.negOnePow • (a * liftDerivation δ hδ b) := by
  have h := lowerTriangularDerivation_mul_of_adjoin_range_eq_top (triangularLift hδ)
    (InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1 : SignedSym G →ₐ[R] SignedSym G)
    (adjoin_range_generator G) (lift_generator G _ _) a b
  simpa only [liftDerivation, AlgEquiv.coe_toAlgHom,
    InternalGrading.koszulTwistAlgEquiv_apply_of_mem (signedSymPiece G) 1 ha, one_mul,
    Units.smul_def, smul_mul_assoc] using h

/-- The odd derivation annihilates the coefficients. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) : liftDerivation δ hδ (algebraMap R _ r) = 0 :=
  lowerTriangularDerivation_algebraMap (triangularLift hδ) r

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 :=
  lowerTriangularDerivation_one (triangularLift hδ)

/-- The odd derivation raises degree by one. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ) (signedSymPiece G) (signedSymPiece G) 1 := by
  have hcomp : liftDerivation δ hδ ∘ₗ generator G = δ :=
    LinearMap.ext (liftDerivation_generator hδ)
  exact isHomogeneous_of_signedLeibniz_of_adjoin_range_eq_top (𝒜 := signedSymPiece G)
    (liftDerivation_mul hδ) (adjoin_range_generator G) G.isInternal.submodule_iSup_eq_top
    (isHomogeneous_signedSymGenerator G) (by rwa [hcomp])

/-- **Uniqueness of odd derivations**: a linear endomorphism of `A(V)` satisfying the signed
Leibniz rule and agreeing with `δ` on generators is `liftDerivation δ hδ`. No degree condition
on the endomorphism is needed. -/
theorem eq_liftDerivation {d : SignedSym G →ₗ[R] SignedSym G}
    (hleibniz : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ :=
  eq_of_signedLeibniz_of_adjoin_range_eq_top (𝒜 := signedSymPiece G) hleibniz
    (liftDerivation_mul hδ) (adjoin_range_generator G) fun x =>
      (hgen x).trans (liftDerivation_generator hδ x).symm

end Lift

/-- **Odd derivations are free on generators**: a degree-one linear map `δ : V → A(V)` extends
uniquely to a linear endomorphism of `A(V)` satisfying the signed Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    ∃! d : SignedSym G →ₗ[R] SignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
        d (a * b) = d a * b + p.negOnePow • (a * d b) :=
  ⟨liftDerivation δ hδ, ⟨LinearMap.ext (liftDerivation_generator hδ), liftDerivation_mul hδ⟩,
    fun _ hd => eq_liftDerivation hδ hd.2 fun x => LinearMap.congr_fun hd.1 x⟩

/-- **The square of an odd derivation is determined by generators**: a degree-one linear
endomorphism of `A(V)` satisfying the signed Leibniz rule squares to zero if and only if its
square vanishes on generators. The square is an unsigned derivation, since the two cross terms
of the signed Leibniz rule cancel. -/
theorem comp_self_eq_zero_iff {d : SignedSym G →ₗ[R] SignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) 1)
    (hleibniz : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 :=
  comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_range_eq_top hdeg hleibniz
    Int.negOnePow_succ (adjoin_range_generator G)

/-- **The extension is a differential**: `liftDerivation δ hδ` makes `A(V)` a differential
graded algebra if and only if it annihilates `δ x` for every `x : V`. -/
theorem isDGAlgebra_liftDerivation_iff {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ) ↔
      ∀ x, liftDerivation δ hδ (δ x) = 0 := by
  refine ⟨fun h x => by simpa using h.sq_zero (generator G x), fun h => ?_⟩
  have hsq := (comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ)
    (liftDerivation_mul hδ)).2 (by simpa using h)
  exact
    { map_mem := fun ha => (isHomogeneous_liftDerivation hδ).map_mem ha
      sq_zero := fun a => LinearMap.congr_fun hsq a
      leibniz := fun ha b => liftDerivation_mul hδ ha b }

end TauCeti.SignedSym
