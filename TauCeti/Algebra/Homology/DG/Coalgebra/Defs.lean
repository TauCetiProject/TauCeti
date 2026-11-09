/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Noncounital differential graded coalgebras

A noncounital differential graded coalgebra over a commutative ring `R` is an internally
`ℤ`-graded `R`-module `C` with a coassociative coproduct `Δ : C ⟶ C ⊗ C` of degree zero and a
differential `d` of degree `+1` which squares to zero and is a coderivation for the Koszul sign
rule,

`Δ (d c) = ∑ d c' ⊗ c'' + (-1) ^ |c'| c' ⊗ d c''`   for `Δ c = ∑ c' ⊗ c''`.

The sign is carried by the Koszul twist `τ : c ↦ (-1) ^ |c| c` of
`TauCeti.InternalGrading.koszulTwist`, so the co-Leibniz rule is the sign-free identity of linear
maps `Δ ∘ d = (d ⊗ 1 + τ ⊗ d) ∘ Δ`.

This is the structure carried by the coaugmentation coideal `ker ε` of a coaugmented
differential graded coalgebra `R ⊕ ker ε`, with the reduced coproduct `c ↦ Δ c - 1 ⊗ c - c ⊗ 1`.
It is the input of the cobar construction `TauCeti.cobarDifferential`, which only sees the
coideal.  The reduced bar construction of an `A∞`
algebra, with reduced deconcatenation and the bar differential, has this shape.

## Main definitions

* `TauCeti.IsNonCounitalDGCoalgebra`: the axioms of a noncounital differential graded coalgebra.

## Main results

* `TauCeti.IsNonCounitalDGCoalgebra.comul_differential_apply`: the co-Leibniz rule on elements.
* `TauCeti.IsNonCounitalDGCoalgebra.koszulTwist_differential`: the differential anticommutes with
  the Koszul twist.
* `TauCeti.IsNonCounitalDGCoalgebra.comul_koszulTwist`: the coproduct commutes with the Koszul
  twist.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Chapter 1, for coaugmented and differential graded coalgebras.
-/

public section

open TensorProduct

namespace TauCeti

universe uR uC

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]

/-- A **noncounital differential graded coalgebra**: an internally `ℤ`-graded module with a
coassociative coproduct `Δ` of degree zero and a differential `d` of degree one which squares to
zero and satisfies the Koszul-signed co-Leibniz rule `Δ ∘ d = (d ⊗ 1 + τ ⊗ d) ∘ Δ`, where `τ`
multiplies an element of degree `p` by `(-1) ^ p`. -/
structure IsNonCounitalDGCoalgebra (G : InternalGrading R C) (Δ : C →ₗ[R] C ⊗[R] C)
    (d : C →ₗ[R] C) : Prop where
  /-- The coproduct is coassociative. -/
  coassoc : (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C ∘ₗ Δ = Δ.lTensor C ∘ₗ Δ
  /-- The coproduct preserves degrees, for the total grading of `C ⊗ C`. -/
  isHomogeneous_comul : LinearMap.IsHomogeneous Δ G.piece (G.tensorProduct G).piece 0
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {c : C}, c ∈ G.piece p → d c ∈ G.piece (p + 1)
  /-- The differential squares to zero. -/
  sq_zero (c : C) : d (d c) = 0
  /-- The Koszul-signed co-Leibniz rule. -/
  comul_differential : Δ ∘ₗ d = (d.rTensor C + TensorProduct.map (G.koszulTwist 1) d) ∘ₗ Δ

namespace IsNonCounitalDGCoalgebra

variable {G : InternalGrading R C} {Δ : C →ₗ[R] C ⊗[R] C} {d : C →ₗ[R] C}

/-- Coassociativity, on elements. -/
theorem coassoc_apply (h : IsNonCounitalDGCoalgebra G Δ d) (c : C) :
    TensorProduct.assoc R C C C (Δ.rTensor C (Δ c)) = Δ.lTensor C (Δ c) :=
  LinearMap.congr_fun h.coassoc c

/-- The co-Leibniz rule, on elements. -/
theorem comul_differential_apply (h : IsNonCounitalDGCoalgebra G Δ d) (c : C) :
    Δ (d c) = d.rTensor C (Δ c) + TensorProduct.map (G.koszulTwist 1) d (Δ c) :=
  LinearMap.congr_fun h.comul_differential c

/-- The differential is homogeneous of degree one. -/
theorem isHomogeneous_differential (h : IsNonCounitalDGCoalgebra G Δ d) :
    LinearMap.IsHomogeneous d G.piece G.piece 1 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hc ↦ h.map_mem hc

/-- **The differential anticommutes with the Koszul twist** `c ↦ (-1) ^ |c| c`, since it has odd
degree. -/
theorem koszulTwist_differential (h : IsNonCounitalDGCoalgebra G Δ d) (c : C) :
    G.koszulTwist 1 (d c) = -d (G.koszulTwist 1 c) := by
  rw [h.isHomogeneous_differential.koszulTwist_apply 1 c, mul_one, Int.negOnePow_one,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul]

/-- **The coproduct commutes with the Koszul twist**, since it has degree zero: the twist of the
total grading of `C ⊗ C` twists both tensor factors. -/
theorem comul_koszulTwist (h : IsNonCounitalDGCoalgebra G Δ d) (c : C) :
    Δ (G.koszulTwist 1 c) = TensorProduct.map (G.koszulTwist 1) (G.koszulTwist 1) (Δ c) := by
  rw [← InternalGrading.koszulTwist_tensorProduct, h.isHomogeneous_comul.koszulTwist_apply 1 c,
    mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul]

end IsNonCounitalDGCoalgebra

end TauCeti
