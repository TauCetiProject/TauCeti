/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Circle
public import TauCeti.RepresentationTheory.Compact.PeterWeyl

/-!
# Fourier series as Peter--Weyl theory for the circle

The Peter--Weyl basis of a compact group consists of normalized matrix coefficients of a skeleton
of its irreducible unitary representations; for the circle it is the Fourier basis.  The
irreducible representations of `Multiplicative (AddCircle T)` were classified in
`TauCeti/RepresentationTheory/Compact/Circle.lean`; here they are transported to the standard
one-dimensional carrier required by `TauCeti.IrrepModel` and assembled into an
`IsIrrepSkeleton`.  Their matrix coefficients are the Fourier monomials, so the resulting abstract
Peter--Weyl basis, pulled back along `Multiplicative.ofAdd`, is Mathlib's `AddCircle.fourierBasis`
vector by vector.

There are two small but mathematically significant normalizations in the identification.

* An `IrrepModel` has carrier `EuclideanSpace ℂ (Fin 1)`, whereas `fourierRep T n` has carrier
  `ℂ`; `IrrepModel.oneDimensionalEquiv` supplies a fixed isometric transport between them.
* Mathlib's inner product is conjugate-linear in its first argument.  Consequently the matrix
  coefficient `⟪fourierRep T n · v, v⟫` of a unit vector is `fourier (-n)`, not `fourier n`.
  The indexing equivalence `fourierPeterWeylIndexEquiv` includes this negation.

After those choices, `compMeasurePreserving_peterWeylBasis_fourier` says that every vector of the
general Peter--Weyl basis is the corresponding vector of Mathlib's Fourier basis.

## Main definitions

* `TauCeti.fourierIrrepModel`: the Fourier representation on the standard one-dimensional model.
* `TauCeti.fourierPeterWeylIndexEquiv`: the index equivalence from the matrix-coefficient indices
  to `ℤ`, including the conjugate-linear sign convention.

## Main statements

* `TauCeti.isIrrepSkeleton_fourierIrrepModel`: the Fourier models form a skeleton of the unitary
  dual of the circle.
* `TauCeti.peterWeylFamily_fourierIrrepModel`: their normalized matrix coefficients are exactly
  Mathlib's Fourier monomials after reindexing.
* `TauCeti.coeFn_peterWeylBasis_fourier`: the almost-everywhere representatives of the Peter--Weyl
  basis vectors of the circle are the Fourier monomials.
* `TauCeti.compMeasurePreserving_peterWeylBasis_fourier`: transported to `L²(AddCircle T)`, the
  Peter--Weyl basis vectors of the circle are the vectors of `AddCircle.fourierBasis`.

The mathematical convention follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.

## Tags

circle group, Fourier series, Peter-Weyl
-/

public section

open MeasureTheory AddCircle
open scoped InnerProductSpace

namespace TauCeti

variable (T : ℝ) [hT : Fact (0 < T)]

/-! ### The Fourier skeleton -/

/-- The `n`-th Fourier representation, transported to the standard one-dimensional carrier used
by `IrrepModel`. -/
noncomputable def fourierIrrepModel (n : ℤ) :
  IrrepModel ℂ (Multiplicative (AddCircle T)) where
  dim := 1
  rep := ContRepresentation.congr (IrrepModel.oneDimensionalEquiv.toContinuousLinearEquiv)
    (fourierRep T n)
  continuous_rep := ContRepresentation.continuous_congr _ (continuous_fourierRep T n)
  isUnitary := (isUnitary_fourierRep T n).congr IrrepModel.oneDimensionalEquiv
  isIrreducible := ContRepresentation.isIrreducible_congr _ (isIrreducible_fourierRep T n)

omit hT in
@[simp]
theorem fourierIrrepModel_dim (n : ℤ) : (fourierIrrepModel T n).dim = 1 := by
  rfl

omit hT in
@[simp]
theorem fourierIrrepModel_rep_apply (n : ℤ) (x : Multiplicative (AddCircle T))
    (v : EuclideanSpace ℂ (Fin (fourierIrrepModel T n).dim)) :
    (fourierIrrepModel T n).rep x v = fourier n (Multiplicative.toAdd x) • v := by
  -- The carrier `EuclideanSpace ℂ (Fin (fourierIrrepModel T n).dim)` depends on the model, so
  -- `rw`/`simp` cannot unfold `fourierIrrepModel` in the goal without breaking the type of `v`
  -- (the motive is not type correct). Both steps below only unfold `fourierIrrepModel` by
  -- definition: first in the type of `v`, then in the representation applied to it.
  change EuclideanSpace ℂ (Fin 1) at v
  change ContRepresentation.congr IrrepModel.oneDimensionalEquiv.toContinuousLinearEquiv
    (fourierRep T n) x v = fourier n (Multiplicative.toAdd x) • v
  rw [ContRepresentation.congr_apply, fourierRep_apply, ← smul_eq_mul, map_smul]
  exact congrArg (fourier n (Multiplicative.toAdd x) • ·)
    (LinearIsometryEquiv.apply_symm_apply IrrepModel.oneDimensionalEquiv v)

/-- **The Fourier models form a skeleton of the unitary dual of the circle.** They are pairwise
inequivalent, and every irreducible unitary representation of the circle is unitarily equivalent to
one of them, so they are a valid input to `peterWeylBasis`. -/
theorem isIrrepSkeleton_fourierIrrepModel : IsIrrepSkeleton (fourierIrrepModel T) where
  pairwise_isEmpty_equiv m n hmn :=
    ⟨fun φ ↦ hmn <| (nonempty_equiv_fourierRep_iff T hT.out.ne').mp ⟨
      ((fourierRep T m).congrEquiv IrrepModel.oneDimensionalEquiv.toContinuousLinearEquiv).trans <|
        φ.trans ((fourierRep T n).congrEquiv
          IrrepModel.oneDimensionalEquiv.toContinuousLinearEquiv).symm⟩⟩
  exists_congr_eq n π hπ hu hirr := by
    obtain ⟨k, ⟨φ⟩⟩ := ContRepresentation.exists_nonempty_equiv_fourierRep π hπ hirr
    let ψ := φ.trans
      ((fourierRep T k).congrEquiv IrrepModel.oneDimensionalEquiv.toContinuousLinearEquiv)
    obtain ⟨e, he⟩ := ContRepresentation.exists_linearIsometryEquiv_congr_eq hu
      (fourierIrrepModel T k).isUnitary hirr ψ
    exact ⟨k, e, he⟩

/-! ### The matrix coefficients -/

/-- The matrix-coefficient index of the one-dimensional Fourier models is equivalent to `ℤ`.
The negation compensates for Mathlib's convention that the inner product is conjugate-linear in
its first argument. -/
noncomputable def fourierPeterWeylIndexEquiv :
    (Σ n : ℤ, Fin (fourierIrrepModel T n).dim × Fin (fourierIrrepModel T n).dim) ≃ ℤ :=
  ((Equiv.sigmaCongrRight fun n ↦
      (Equiv.prodCongr (finCongr (fourierIrrepModel_dim T n))
        (finCongr (fourierIrrepModel_dim T n))).trans (Equiv.prodUnique (Fin 1) (Fin 1))).trans
    (Equiv.sigmaUnique ℤ fun _ ↦ Fin 1)).trans (Equiv.neg ℤ)

omit hT in
@[simp]
theorem fourierPeterWeylIndexEquiv_apply
    (x : Σ n : ℤ, Fin (fourierIrrepModel T n).dim × Fin (fourierIrrepModel T n).dim) :
    fourierPeterWeylIndexEquiv T x = -x.1 := by
  rfl

omit hT in
@[simp]
theorem fourierPeterWeylIndexEquiv_symm_apply_fst (n : ℤ) :
    ((fourierPeterWeylIndexEquiv T).symm n).1 = -n := by
  have h := fourierPeterWeylIndexEquiv_apply T ((fourierPeterWeylIndexEquiv T).symm n)
  rw [Equiv.apply_symm_apply] at h
  simpa only [neg_neg] using congrArg Neg.neg h.symm

/-- **The Peter--Weyl matrix coefficients of the Fourier models are the Fourier monomials.**
The index equivalence absorbs the conjugation in the first argument of the inner product. -/
theorem peterWeylFamily_fourierIrrepModel (n : ℤ) :
    peterWeylFamily (fourierIrrepModel T) ((fourierPeterWeylIndexEquiv T).symm n) =
      ContRepresentation.characterLp (fourierRep T n) (continuous_fourierRep T n) := by
  let y := (fourierPeterWeylIndexEquiv T).symm n
  have hab : y.2.1 = y.2.2 := by
    apply (finCongr (fourierIrrepModel_dim T y.1)).injective
    exact Subsingleton.elim _ _
  have hsqrt : ((Real.sqrt ((fourierIrrepModel T y.1).dim : ℝ) : ℝ) : ℂ) = 1 := by
    norm_num [fourierIrrepModel_dim]
  apply Lp.ext
  filter_upwards [coeFn_peterWeylFamily (fourierIrrepModel T) y,
    ContRepresentation.coeFn_characterLp (fourierRep T n)
      (continuous_fourierRep T n)] with x hx hy
  rw [hx, hy]
  calc
    _ = 1 * ⟪(fourierIrrepModel T y.1).rep x
          ((fourierIrrepModel T y.1).basis y.2.1),
          (fourierIrrepModel T y.1).basis y.2.2⟫_ℂ :=
      congrArg (· * ⟪(fourierIrrepModel T y.1).rep x
        ((fourierIrrepModel T y.1).basis y.2.1),
        (fourierIrrepModel T y.1).basis y.2.2⟫_ℂ) hsqrt
    _ = fourier n (Multiplicative.toAdd x) := by
      rw [one_mul, fourierIrrepModel_rep_apply, hab, inner_smul_left,
        inner_self_eq_norm_sq_to_K, (fourierIrrepModel T y.1).basis.norm_eq_one]
      norm_num
      rw [fourierPeterWeylIndexEquiv_symm_apply_fst]
      simpa only [fourier_apply, neg_neg] using
        (fourier_neg (n := -n) (x := Multiplicative.toAdd x)).symm
    _ = _ := by
      symm
      convert DFunLike.congr_fun (character_fourierRep T n) x using 1
      · rw [ContRepresentation.character_apply]
      · rfl

/-! ### Identification with the Fourier Hilbert basis -/

/-- **The general Peter--Weyl basis specializes to the Fourier monomials.** After reindexing by
`fourierPeterWeylIndexEquiv`, the almost-everywhere representative of its `n`-th vector is
`fourier n`.  Together with `haarProb_eq_haarAddCircle` and Mathlib's `coe_fourierBasis`, this is
the elementwise identification of the specialized Peter--Weyl basis with
`AddCircle.fourierBasis`. -/
theorem coeFn_peterWeylBasis_fourier (n : ℤ) :
    (peterWeylBasis (isIrrepSkeleton_fourierIrrepModel T)
      ((fourierPeterWeylIndexEquiv T).symm n) :
        Multiplicative (AddCircle T) → ℂ) =ᵐ[haarProb (Multiplicative (AddCircle T))]
      fun x ↦ fourier n (Multiplicative.toAdd x) := by
  rw [coe_peterWeylBasis, peterWeylFamily_fourierIrrepModel]
  filter_upwards [ContRepresentation.coeFn_characterLp (fourierRep T n)
    (continuous_fourierRep T n)] with x hx
  rw [hx]
  convert DFunLike.congr_fun (character_fourierRep T n) x using 1
  · rw [ContRepresentation.character_apply]
  · rfl

/-- **The Peter--Weyl basis of the circle is Mathlib's Fourier basis.** Transported to
`L²(AddCircle T)` along `Multiplicative.ofAdd`, the Peter--Weyl basis vector with index
`(fourierPeterWeylIndexEquiv T).symm n` is the `n`-th vector of `AddCircle.fourierBasis`. -/
theorem compMeasurePreserving_peterWeylBasis_fourier (n : ℤ) :
    Lp.compMeasurePreserving Multiplicative.ofAdd (measurePreserving_ofAdd_haarAddCircle T)
      (peterWeylBasis (isIrrepSkeleton_fourierIrrepModel T)
        ((fourierPeterWeylIndexEquiv T).symm n)) = fourierBasis n := by
  rw [coe_fourierBasis]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (peterWeylBasis (isIrrepSkeleton_fourierIrrepModel T) ((fourierPeterWeylIndexEquiv T).symm n))
      (measurePreserving_ofAdd_haarAddCircle T),
    (measurePreserving_ofAdd_haarAddCircle T).quasiMeasurePreserving.ae_eq_comp
      (coeFn_peterWeylBasis_fourier T n), coeFn_fourierLp 2 n] with x h₁ h₂ h₃
  rw [h₁, h₃]
  exact h₂

end TauCeti
