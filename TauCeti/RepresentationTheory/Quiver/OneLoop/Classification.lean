/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.OneLoop.PolynomialModule
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.Algebra.Module.PID
public import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
public import TauCeti.RingTheory.AdjoinRoot.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Cyclic primary models for indecomposable loop representations

Every finite-dimensional indecomposable representation of the one-loop quiver
has a cyclic primary polynomial module `k[X]/(pⁿ)`, where `p` is irreducible and
`n` is positive. Over an algebraically closed field, `p` can be replaced by
`X - C a`. Thus the loop operator is conjugate to multiplication by the root
on `k[X]/((X - a)ⁿ)`, the cyclic model of a Jordan block.

The statements give linear equivalences intertwining the loop operators. They establish that the
cyclic primary models exhaust the finite-dimensional indecomposables; uniqueness
of the parameters is not asserted here.

The proof uses `Module.AEval.isTorsion_of_finiteDimensional` and
`TauCeti.exists_linearEquiv_quotient_pow_of_isIndecomposableModule`.

## References

* P. Etingof et al., *Introduction to Representation Theory*, Section 2.1.
* S. Lang, *Algebra*, Chapter III, the structure theorem over a principal ideal domain.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory Polynomial

universe u v

variable {k : Type u} [Field k]
  {M : QuiverRep.{u, 0, 0, v} k Quiver.OneLoop}

/-- The polynomial module of a finite-dimensional indecomposable loop representation
is cyclic primary, over an arbitrary field. -/
theorem exists_oneLoopModule_equiv_quotient_pow
    (hfin : IsFinDim k Quiver.OneLoop M) (hi : Indecomposable M) :
    ∃ p : k[X], Irreducible p ∧ ∃ n : ℕ, 0 < n ∧
      Nonempty (oneLoopModule M ≃ₗ[k[X]] k[X] ⧸ k[X] ∙ p ^ n) := by
  have := isFinDim_iff.mp hfin (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)
  have hi' := oneLoopPolynomialFunctor.indecomposable_obj_of_map_bijective hi
    ⟨oneLoopPolynomialFunctor.map_injective, oneLoopPolynomialFunctor.map_surjective⟩
  exact exists_linearEquiv_quotient_pow_of_isIndecomposableModule
    (Module.AEval.isTorsion_of_finiteDimensional k _ _)
    ((TauCeti.indecomposable_iff_isIndecomposableModule _).mp hi')

/-- Every finite-dimensional indecomposable loop operator is conjugate to
multiplication by the root on a cyclic primary quotient `k[X]/(pⁿ)`. -/
theorem exists_oneLoop_equiv_adjoinRoot_pow
    (hfin : IsFinDim k Quiver.OneLoop M) (hi : Indecomposable M) :
    ∃ p : k[X], Irreducible p ∧ ∃ n : ℕ, 0 < n ∧
      ∃ e : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ≃ₗ[k] AdjoinRoot (p ^ n),
        ∀ x, e ((M.map Quiver.OneLoop.loop.toPath).hom x) =
          AdjoinRoot.root (p ^ n) * e x := by
  obtain ⟨p, hp, n, hn, ⟨e⟩⟩ := exists_oneLoopModule_equiv_quotient_pow hfin hi
  refine ⟨p, hp, n, hn, (Module.AEval'.of _).trans
    ((e.restrictScalars k).trans (quotientSpanEquivAdjoinRoot (p ^ n))), ?_⟩
  intro x
  have hx := e.map_smul (X : k[X])
    (Module.AEval'.of (M.map Quiver.OneLoop.loop.toPath).hom x)
  rw [Module.AEval'.X_smul_of] at hx
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, hx,
    quotientSpanEquivAdjoinRoot_smul, AdjoinRoot.mk_X]

/-- Over an algebraically closed field, every finite-dimensional indecomposable
loop representation is a single Jordan block in its cyclic quotient model.
The block size is the dimension at the unique vertex. -/
theorem exists_oneLoop_equiv_jordanBlock [IsAlgClosed k]
    (hfin : IsFinDim k Quiver.OneLoop M) (hi : Indecomposable M) :
    ∃ (a : k) (n : ℕ), 0 < n ∧ n = dimVector M Quiver.OneLoop.vertex ∧
      ∃ e : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ≃ₗ[k]
          AdjoinRoot ((X - C a) ^ n),
        ∀ x, e ((M.map Quiver.OneLoop.loop.toPath).hom x) =
          AdjoinRoot.root ((X - C a) ^ n) * e x := by
  obtain ⟨p, hp, n, hn, e, he⟩ := exists_oneLoop_equiv_adjoinRoot_pow hfin hi
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (degree_pos_of_irreducible hp).ne'
  have hpa : Associated p (X - C a) :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha) |>.symm
  let q := AdjoinRoot.algEquivOfAssociated k (p ^ n) ((X - C a) ^ n) (hpa.pow_pow)
  let e' := e.trans q.toLinearEquiv
  have hsize : Module.finrank k (AdjoinRoot ((X - C a) ^ n)) = n := by
    rw [(AdjoinRoot.powerBasis (pow_ne_zero n (X_sub_C_ne_zero a))).finrank,
      AdjoinRoot.powerBasis_dim]
    simp
  refine ⟨a, n, hn, ?_, e', ?_⟩
  · rw [dimVector_apply, ← hsize]
    exact e'.finrank_eq.symm
  · intro x
    simp only [e', LinearEquiv.trans_apply, AlgEquiv.coe_toLinearEquiv, he,
      map_mul, q, AdjoinRoot.algEquivOfAssociated_root]

end TauCeti.QuiverRep
