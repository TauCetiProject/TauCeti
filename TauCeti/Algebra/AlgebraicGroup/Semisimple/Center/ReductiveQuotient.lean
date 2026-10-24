/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Lie
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Center.Lie
public import TauCeti.Algebra.AlgebraicGroup.Reductive.CenterQuotient
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.FormallySmooth
import TauCeti.Algebra.Lie.Solvable.Basic
import TauCeti.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Algebra.Lie.CartanCriterion

/-!
# Semisimplicity of the quotient of a reductive group by its center

Over a field of characteristic zero, a faithfully flat homomorphism from a reductive
affine group with kernel its full scheme-theoretic center has semisimple target.
In particular, the Hopf algebra of center-coinvariant functions represents a semisimple
group.

Over an algebraically closed field, the quotient differential is surjective with kernel
the center of the source Lie algebra, which is its solvable radical. The target Lie algebra
therefore has zero radical. Scalar extension of the given homomorphism and its kernel then
gives the result over the original field, without a splitting hypothesis.

The proof uses `Center.Lie`, `Reductive.Lie`, `LieIdeal.radical_map_eq`, and Cartier's theorem.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19, 21 and 22.
* A. Borel, *Linear Algebraic Groups*, §14.2.
-/

public section

open CategoryTheory

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {G Q : FiniteTypeCommHopfAlgCat.{u, u} k}

private theorem semisimple_of_kernel_eq_center_of_isAlgClosed [IsAlgClosed k]
    (hG : reductiveCommHopfAlgProperty k G)
    (f : Q.obj ⟶ G.obj) (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hker : CommHopfAlgCat.kernelHopfIdeal f = CommHopfAlgCat.centerDefiningIdeal G.obj) :
    semisimpleCommHopfAlgProperty k Q := by
  let _ : ConnectedSpace (PrimeSpectrum G) := hG.geometricallyConnected.connectedSpace k G.obj
  let _ := hG.hasCentralRadical_lieAlgebra
  let D := derivationCompLieHom (B := k) f.hom
  have hDker : D.ker =
      LieAlgebra.radical k (Derivation k G (Bialgebra.CounitAlgebra k G k)) := by
    ext d
    rw [← LieIdeal.mem_toLieSubalgebra,
      ← CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal, hker,
      FiniteTypeCommHopfAlgCat.lieSubalgebra_centerDefiningIdeal_eq_center,
      LieAlgebra.radical_eq_center, LieIdeal.mem_toLieSubalgebra]
  have hsmoothKernel : Algebra.Smooth k
      (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal f)) :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k _)
  have hsurj : Function.Surjective D :=
    derivationCompLieHom_surjective_of_formallySmooth f.hom
      ((_root_.CommHopfAlgCat.smooth_iff_algebraSmooth_quotient_kernelHopfIdeal f hf).mpr
        hsmoothKernel).formallySmooth
  have hsolvable : LieAlgebra.IsSolvable D.ker := by
    rw [hDker]
    infer_instance
  let _ : LieAlgebra.HasTrivialRadical k
      (Derivation k Q (Bialgebra.CounitAlgebra k Q k)) := by
    constructor
    rw [← LieIdeal.radical_map_eq D hsurj hsolvable, LieIdeal.map_eq_bot_iff]
    exact hDker.ge
  exact semisimpleCommHopfAlgProperty.of_isKilling
    ((smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k Q.obj))
    (geometricallyConnectedCommHopfAlgProperty.of_injective
      f.hom.toAlgHom hf.injective hG.geometricallyConnected)

/-- A faithfully flat quotient of a reductive affine group by its full scheme-theoretic
center is semisimple in characteristic zero. The ground field need not be algebraically
closed and the group need not split. -/
theorem semisimple_of_kernel_eq_center
    (hG : reductiveCommHopfAlgProperty k G)
    (f : Q.obj ⟶ G.obj) (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hker : CommHopfAlgCat.kernelHopfIdeal f = CommHopfAlgCat.centerDefiningIdeal G.obj) :
    semisimpleCommHopfAlgProperty k Q := by
  let K := AlgebraicClosure k
  let fK := CommHopfAlgCat.baseChangeMap (K := K) f
  have hfK : fK.hom.toAlgHom.toRingHom.FaithfullyFlat := by
    simpa only [fK, CommHopfAlgCat.hom_baseChangeMap, Bialgebra.TensorProduct.map_toAlgHom,
      BialgHom.id_toAlgHom] using hf.lTensor K
  have hkerK : CommHopfAlgCat.kernelHopfIdeal fK =
      CommHopfAlgCat.centerDefiningIdeal (FiniteTypeCommHopfAlgCat.baseChange (K := K) G).obj := by
    rw [← CommHopfAlgCat.baseChangeHopfIdeal_kernelHopfIdeal, hker,
      CommHopfAlgCat.baseChangeHopfIdeal_centerDefiningIdeal]
  exact semisimpleCommHopfAlgProperty.of_baseChange
    (semisimple_of_kernel_eq_center_of_isAlgClosed hG.algebraicClosureBaseChange fK hfK hkerK)

/-- The quotient of a reductive group by its center, represented by the Hopf algebra of
center-coinvariant functions, is semisimple in characteristic zero. -/
theorem semisimple_centerQuotient
    (hG : reductiveCommHopfAlgProperty k G) :
    semisimpleCommHopfAlgProperty k hG.centerQuotient :=
  hG.semisimple_of_kernel_eq_center hG.centerQuotientι
    hG.faithfullyFlat_centerQuotientι hG.kernelHopfIdeal_centerQuotientι_eq

end TauCeti.reductiveCommHopfAlgProperty
