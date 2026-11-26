/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Finite generation of homogeneous unblocked cycle pieces in characteristic two

Over any commutative ring `R` of characteristic two (without a Noetherian hypothesis), every
homogeneous cycle piece of the unblocked grid complex `GC⁻`—whether in a fixed
`(O-Maslov, Alexander)` bidegree or in a fixed Alexander degree—is finitely generated over `R`.

Because `ZMod 2` is a field, any finite subset `T` of the monomial basis of `GC⁻` defines a
differential `supportedDifferentialZMod` from the finite-rank free `ZMod 2`-module `T →₀ ZMod 2`
into `GridChainMinus (ZMod 2) n` whose kernel is finite-dimensional and therefore stays finitely
generated after base change along `ZMod 2 →+* R` (`LinearMap.finite_ker_baseChange`). Comparing
that base-changed differential with the restriction of `unblockedDifferential R` to
`bigradedChainMinusSupported R S` yields finite generation of the kernel over `R`.

## Main results

* `TauCeti.OddComponentGridDiagram.finite_ker_unblockedDifferential_bigradedChainMinusPiece`:
  over any commutative ring of characteristic two, the kernel of `∂⁻` restricted to a
  Maslov--Alexander chain piece is finitely generated over the ground ring.
* `TauCeti.OddComponentGridDiagram.finite_ker_unblockedDifferential_alexanderChainMinusPiece`:
  over any commutative ring of characteristic two, the kernel of `∂⁻` restricted to an Alexander
  chain piece is finitely generated over the ground ring.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4; the chain bigrading and
Alexander pieces are in `TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain`, and the analogous
base-change mechanism for finite generation of homology is in
`TauCeti.KnotTheory.Grid.Homology.Finite`.
-/

public section

namespace TauCeti.OddComponentGridDiagram

open GridChainMinus MvPolynomial
open scoped TensorProduct

section CharacteristicTwoCycles

variable {n : ℕ} (G : OddComponentGridDiagram n)

private noncomputable def monomialDegreeSupportedBasis (K : Type*) [CommSemiring K]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    Module.Basis
      {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S}
      K (monomialDegreeSupported K deg S) :=
  (Module.Basis.span
    ((monomialChainBasis (n := n) K).linearIndependent.comp
      Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ <| by
      rw [monomialDegreeSupported_eq_span K deg S, Set.image_eq_range]
      rfl)

@[simp]
private theorem coe_monomialDegreeSupportedBasis_apply (K : Type*) [CommSemiring K]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (i : {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S}) :
    ((monomialDegreeSupportedBasis K deg S i :
        monomialDegreeSupported K deg S) : GridChainMinus K n) =
      monomialChainBasis (n := n) K i.val := by
  simp [monomialDegreeSupportedBasis]

private noncomputable def baseChangeSupportedEquiv (R : Type*) [CommRing R]
    [Algebra (ZMod 2) R] {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    R ⊗[ZMod 2]
        ({ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S} →₀
          ZMod 2) ≃ₗ[R]
      monomialDegreeSupported R deg S :=
  (Finsupp.basisSingleOne.baseChange R).equiv
    (monomialDegreeSupportedBasis R deg S) (Equiv.refl _)

@[simp]
private theorem baseChangeSupportedEquiv_tmul_single (R : Type*) [CommRing R]
    [Algebra (ZMod 2) R] {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (i : {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S}) :
    baseChangeSupportedEquiv R deg S (1 ⊗ₜ[ZMod 2] Finsupp.single i 1) =
      monomialDegreeSupportedBasis R deg S i := by
  have hi : Finsupp.single i (1 : ZMod 2) = Finsupp.basisSingleOne i := by
    rw [Finsupp.coe_basisSingleOne]
  rw [hi, baseChangeSupportedEquiv, ← Module.Basis.baseChange_apply,
    Module.Basis.equiv_apply, Equiv.refl_apply]

private noncomputable def baseChangeChainEquiv (n : ℕ) (F R : Type*) [CommRing F] [CommRing R]
    [Algebra F R] :
    R ⊗[F] GridChainMinus F n ≃ₗ[R] GridChainMinus R n :=
  ((monomialChainBasis (n := n) F).baseChange R).equiv
    (monomialChainBasis (n := n) R) (Equiv.refl _)

@[simp]
private theorem baseChangeChainEquiv_tmul {F R : Type*} [CommRing F] [CommRing R]
    [Algebra F R] (c : GridChainMinus F n) :
    baseChangeChainEquiv n F R (1 ⊗ₜ[F] c) =
      c.mapRange (MvPolynomial.map (algebraMap F R)) (map_zero _) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp [TensorProduct.tmul_add, hc, hd,
      Finsupp.mapRange_add (hf' := fun _ _ ↦ map_add _ _ _)]
  | single x p =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp [Finsupp.single_add, TensorProduct.tmul_add, hp, hq,
        Finsupp.mapRange_add (hf' := fun _ _ ↦ map_add _ _ _)]
    | monomial d a =>
      have hsingle : (Finsupp.single x (monomial d a) : GridChainMinus F n) =
          a • monomialChainBasis (n := n) F ⟨x, d⟩ := by
        rw [monomialChainBasis_apply, Finsupp.smul_single, smul_monomial, smul_eq_mul, mul_one]
      have hbasis : baseChangeChainEquiv n F R
          (1 ⊗ₜ[F] monomialChainBasis (n := n) F ⟨x, d⟩) =
          monomialChainBasis (n := n) R ⟨x, d⟩ := by
        rw [baseChangeChainEquiv, ← Module.Basis.baseChange_apply,
          Module.Basis.equiv_apply, Equiv.refl_apply]
      rw [hsingle, TensorProduct.tmul_smul, ← algebraMap_smul R a, map_smul, hbasis, ← hsingle,
        monomialChainBasis_apply, Finsupp.smul_single, smul_monomial, smul_eq_mul, mul_one,
        Finsupp.mapRange_single, map_monomial]

private noncomputable def supportedDifferentialZMod {ι : Type*}
    (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    ({ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S} →₀ ZMod 2) →ₗ[ZMod 2]
      GridChainMinus (ZMod 2) n :=
  Finsupp.linearCombination (ZMod 2) fun i ↦
    (G.val.unblockedDifferential (ZMod 2)) (monomialChainBasis (n := n) (ZMod 2) i.val)

@[simp]
private theorem supportedDifferentialZMod_single {ι : Type*}
    (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (i : {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S}) :
    G.supportedDifferentialZMod deg S (Finsupp.single i 1) =
      G.val.unblockedDifferential (ZMod 2) (monomialChainBasis (n := n) (ZMod 2) i.val) := by
  simp [supportedDifferentialZMod]

private noncomputable def unblockedDifferentialSupported (R : Type*) [CommRing R]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    monomialDegreeSupported R deg S →ₗ[R] GridChainMinus R n :=
  ((G.val.unblockedDifferential R).restrictScalars R).comp
    (monomialDegreeSupported R deg S).subtype

@[simp]
private theorem unblockedDifferentialSupported_apply (R : Type*) [CommRing R]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (c : monomialDegreeSupported R deg S) :
    G.unblockedDifferentialSupported R deg S c = G.val.unblockedDifferential R c :=
  rfl

private theorem baseChange_unblockedDifferential_comm_supported
    (R : Type*) [CommRing R] [Algebra (ZMod 2) R]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    (baseChangeChainEquiv n (ZMod 2) R).toLinearMap.comp
        ((G.supportedDifferentialZMod deg S).baseChange R) =
      (G.unblockedDifferentialSupported R deg S).comp
        (baseChangeSupportedEquiv R deg S).toLinearMap := by
  refine (Finsupp.basisSingleOne.baseChange R).ext fun i ↦ ?_
  simp [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    G.val.mapRange_map_unblockedDifferential]

private theorem finite_ker_unblockedDifferential_monomialDegreeSupported
    (R : Type*) [CommRing R] [CharP R 2]
    {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (hfin : {ix : Σ _ : GridState n, Fin n →₀ ℕ | deg ix.fst ix.snd ∈ S}.Finite) :
    Module.Finite R
      (LinearMap.ker (((G.val.unblockedDifferential R).restrictScalars R).comp
        (monomialDegreeSupported R deg S).subtype)) := by
  let _ : Algebra (ZMod 2) R := ZMod.algebra R 2
  have _ : Finite {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S} := hfin
  -- Transport finite generation of `ker ((supportedDifferentialZMod deg S).baseChange R)`
  -- over `ZMod 2` across the base-change commuting square.
  have _ : Module.Finite R (LinearMap.ker ((G.supportedDifferentialZMod deg S).baseChange R)) :=
    LinearMap.finite_ker_baseChange (G.supportedDifferentialZMod deg S)
  have hker := LinearEquiv.map_ker_of_comm (baseChangeSupportedEquiv R deg S)
    (baseChangeChainEquiv n (ZMod 2) R) ((G.supportedDifferentialZMod deg S).baseChange R)
    (G.unblockedDifferentialSupported R deg S)
    (G.baseChange_unblockedDifferential_comm_supported R deg S)
  exact Module.Finite.equiv
    (((baseChangeSupportedEquiv R deg S).submoduleMap _).trans (LinearEquiv.ofEq _ _ hker))

/-- Over any commutative ring of characteristic two, the kernel of the unblocked differential
restricted to a Maslov--Alexander chain piece is finitely generated over the ground ring. -/
theorem finite_ker_unblockedDifferential_bigradedChainMinusPiece (R : Type*) [CommRing R]
    [CharP R 2] (g : ℤ × ℤ) :
    Module.Finite R
      (LinearMap.ker (((G.val.unblockedDifferential R).restrictScalars R).comp
        (G.bigradedChainMinusPiece R g).subtype)) := by
  rw [G.bigradedChainMinusPiece_def R g]
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
  rw [G.alexanderChainMinusPiece_def R a]
  exact G.finite_ker_unblockedDifferential_monomialDegreeSupported R
    (fun x e ↦ G.alexanderℤ x - (e.degree : ℤ)) {a} <|
      by simpa only [Set.mem_singleton_iff] using G.finite_state_exponent_of_alexander_eq a

end CharacteristicTwoCycles

end TauCeti.OddComponentGridDiagram
