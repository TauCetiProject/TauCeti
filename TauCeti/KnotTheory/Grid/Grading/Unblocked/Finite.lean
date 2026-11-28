/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.KnotTheory.Grid.Grading.Unblocked.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Finite generation of homogeneous unblocked cycle pieces in characteristic two

For a grid diagram with an odd number of link components (`OddComponentGridDiagram`) and any
commutative ring `R` of characteristic two (without a Noetherian hypothesis), every homogeneous
cycle piece of the unblocked grid complex `GC⁻`—whether in a fixed `(O-Maslov, Alexander)`
bidegree or in a fixed Alexander degree—is finitely generated over `R`.

Because `ZMod 2` is a field, whenever only finitely many monomial basis elements have degrees in a
set `S`, the supported submodule `GridChainMinus.monomialDegreeSupported (ZMod 2) deg S` is
finite-dimensional over `ZMod 2`. Restricting `unblockedDifferential (ZMod 2)` to this supported
submodule defines a `ZMod 2`-linear map whose kernel stays finitely generated after base change
along `ZMod 2 →+* R` (`LinearMap.finite_ker_baseChange`). Comparing that base-changed differential
with the restriction of `unblockedDifferential R` to `GridChainMinus.monomialDegreeSupported R deg
S` via `GridChainMinus.baseChangeSupportedEquiv` and `GridChainMinus.baseChangeChainEquiv` yields
finite generation of the cycle pieces over `R`.

## Main results

* `TauCeti.OddComponentGridDiagram.finite_ker_unblockedDifferential_bigradedChainMinusPiece`:
  over any commutative ring of characteristic two, the kernel of `∂⁻` restricted to a
  Maslov--Alexander chain piece is finitely generated over the ground ring.
* `TauCeti.OddComponentGridDiagram.finite_ker_unblockedDifferential_alexanderChainMinusPiece`:
  over any commutative ring of characteristic two, the kernel of `∂⁻` restricted to an Alexander
  chain piece is finitely generated over the ground ring.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4; the chain bigrading and
Alexander pieces are in `TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain`, while
`TauCeti.KnotTheory.Grid.Homology.Finite` proves `MvPolynomial`-finite generation of unblocked
homology over Noetherian coefficients.
-/

public section

namespace TauCeti.OddComponentGridDiagram

open GridChainMinus MvPolynomial
open scoped TensorProduct

section CharacteristicTwoCycles

variable {n : ℕ} (G : OddComponentGridDiagram n)

private noncomputable def unblockedDifferentialSupported (F : Type*) [CommSemiring F]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    monomialDegreeSupported F deg S →ₗ[F] GridChainMinus F n :=
  ((G.val.unblockedDifferential F).restrictScalars F).comp
    (monomialDegreeSupported F deg S).subtype

private theorem baseChange_unblockedDifferential_comm_supported
    (F R : Type*) [CommSemiring F] [CommSemiring R] [Algebra F R]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    (baseChangeChainEquiv n F R).toLinearMap.comp
        ((G.unblockedDifferentialSupported F deg S).baseChange R) =
      (G.unblockedDifferentialSupported R deg S).comp
        (baseChangeSupportedEquiv F R deg S).toLinearMap := by
  refine ((monomialDegreeSupportedBasis F deg S).baseChange R).ext fun i ↦ ?_
  simp [unblockedDifferentialSupported]

private theorem finite_ker_unblockedDifferential_monomialDegreeSupported
    (R : Type*) [CommRing R] [CharP R 2]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (hfin : {ix : Σ _ : GridState n, Fin n →₀ ℕ | deg ix.fst ix.snd ∈ S}.Finite) :
    Module.Finite R
      (LinearMap.ker (((G.val.unblockedDifferential R).restrictScalars R).comp
        (monomialDegreeSupported R deg S).subtype)) := by
  let _ : Algebra (ZMod 2) R := ZMod.algebra R 2
  have _ : Module.Finite (ZMod 2) (monomialDegreeSupported (ZMod 2) deg S) :=
    finite_monomialDegreeSupported (ZMod 2) hfin
  -- Transport finite generation of `ker ((unblockedDifferentialSupported (ZMod 2) deg S).baseChange
  -- R)` over `ZMod 2` across the base-change commuting square.
  have _ : Module.Finite R
      (LinearMap.ker ((G.unblockedDifferentialSupported (ZMod 2) deg S).baseChange R)) := by
    convert LinearMap.finite_ker_baseChange (F := ZMod 2) (A := R)
      (M := ↥(monomialDegreeSupported (ZMod 2) deg S)) (N := GridChainMinus (ZMod 2) n)
      (G.unblockedDifferentialSupported (ZMod 2) deg S)
  have hker := LinearEquiv.map_ker_of_comm (baseChangeSupportedEquiv (ZMod 2) R deg S)
    (baseChangeChainEquiv n (ZMod 2) R)
    ((G.unblockedDifferentialSupported (ZMod 2) deg S).baseChange R)
    (G.unblockedDifferentialSupported R deg S)
    (G.baseChange_unblockedDifferential_comm_supported (ZMod 2) R deg S)
  exact Module.Finite.equiv
    (((baseChangeSupportedEquiv (ZMod 2) R deg S).submoduleMap _).trans (LinearEquiv.ofEq _ _ hker))

/-- Over any commutative ring of characteristic two, the kernel of the unblocked differential
restricted to a Maslov--Alexander chain piece is finitely generated over the ground ring. -/
theorem finite_ker_unblockedDifferential_bigradedChainMinusPiece (R : Type*) [CommRing R]
    [CharP R 2] (g : ℤ × ℤ) :
    Module.Finite R
      (LinearMap.ker (((G.val.unblockedDifferential R).restrictScalars R).comp
        (G.bigradedChainMinusPiece R g).subtype)) := by
  have hpiece : G.bigradedChainMinusPiece R g =
      GridChainMinus.monomialDegreeSupported R G.monomialBidegree {g} := by
    rw [monomialDegreeSupported_singleton]
    ext c
    simp only [mem_bigradedChainMinusPiece, mem_monomialDegreePiece]
  rw [hpiece]
  exact G.finite_ker_unblockedDifferential_monomialDegreeSupported R G.monomialBidegree {g} <|
    (G.finite_state_exponent_of_alexander_eq g.snd).subset
      fun ix (hix : G.monomialBidegree _ _ = g) ↦
        (G.monomialBidegree_snd ix.fst ix.snd).symm.trans (congrArg Prod.snd hix)

/-- Over any commutative ring of characteristic two, the kernel of the unblocked differential
restricted to an Alexander chain piece is finitely generated over the ground ring. -/
theorem finite_ker_unblockedDifferential_alexanderChainMinusPiece (R : Type*) [CommRing R]
    [CharP R 2] (a : ℤ) :
    Module.Finite R
      (LinearMap.ker (((G.val.unblockedDifferential R).restrictScalars R).comp
        (G.alexanderChainMinusPiece R a).subtype)) := by
  have hpiece : G.alexanderChainMinusPiece R a =
      GridChainMinus.monomialDegreeSupported R (fun x e ↦ G.alexanderℤ x - (e.degree : ℤ)) {a} := by
    rw [monomialDegreeSupported_singleton]
    ext c
    simp only [mem_alexanderChainMinusPiece, mem_monomialDegreePiece]
  rw [hpiece]
  exact G.finite_ker_unblockedDifferential_monomialDegreeSupported R
    (fun x e ↦ G.alexanderℤ x - (e.degree : ℤ)) {a} <|
      by simpa only [Set.mem_singleton_iff] using G.finite_state_exponent_of_alexander_eq a

end CharacteristicTwoCycles

end TauCeti.OddComponentGridDiagram
