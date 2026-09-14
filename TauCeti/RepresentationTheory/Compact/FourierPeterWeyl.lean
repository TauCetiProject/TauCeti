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

This file completes the circle acceptance check for the compact-group Peter--Weyl theorem.  The
irreducible representations of `Multiplicative (AddCircle T)` were classified in
`TauCeti/RepresentationTheory/Compact/Circle.lean`; here they are transported to the standard
one-dimensional carrier required by `TauCeti.IrrepModel` and assembled into an
`IsIrrepSkeleton`.  The resulting abstract Peter--Weyl basis is then identified with Mathlib's
`AddCircle.fourierBasis` at the level of its basis vectors.

There are two small but mathematically significant normalizations in the identification.

* An `IrrepModel` has carrier `EuclideanSpace ℂ (Fin 1)`, whereas `fourierRep T n` has carrier
  `ℂ`; `fourierModelEquiv` supplies a fixed isometric transport between them.
* Mathlib's inner product is conjugate-linear in its first argument.  Consequently the matrix
  coefficient `⟪fourierRep T n · v, v⟫` of a unit vector is `fourier (-n)`, not `fourier n`.
  The indexing equivalence `fourierPeterWeylIndexEquiv` includes this negation.

After those choices, `coeFn_peterWeylBasis_fourier` says that every vector of the general
Peter--Weyl basis is represented by the corresponding vector of Mathlib's Fourier basis.

## Main definitions

* `TauCeti.fourierIrrepModel`: the Fourier representation on the standard one-dimensional model.
* `TauCeti.fourierPeterWeylIndexEquiv`: the index equivalence from the matrix-coefficient indices
  to `ℤ`, including the conjugate-linear sign convention.

## Main statements

* `TauCeti.isIrrepSkeleton_fourierIrrepModel`: the Fourier models form a skeleton of the unitary
  dual of the circle.
* `TauCeti.peterWeylFamily_fourierIrrepModel`: their normalized matrix coefficients are exactly
  Mathlib's Fourier monomials after reindexing.
* `TauCeti.coeFn_peterWeylBasis_fourier`: Peter--Weyl for the circle has the Fourier monomials as
  its basis vectors.

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

/-- The canonical isometry from `ℂ` to the one-dimensional Euclidean model used by
`IrrepModel`.  It matches the standard orthonormal bases on the two spaces. -/
noncomputable def fourierModelEquiv : ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 1) :=
  let e : Fin (Module.finrank ℂ ℂ) ≃ Fin 1 := finCongr (by simp)
  ((stdOrthonormalBasis ℂ ℂ).reindex e).equiv
    (EuclideanSpace.basisFun (Fin 1) ℂ) (Equiv.refl (Fin 1))

/-- The `n`-th Fourier representation, transported to the standard one-dimensional carrier used
by `IrrepModel`. -/
@[expose] noncomputable def fourierIrrepModel (n : ℤ) :
    IrrepModel ℂ (Multiplicative (AddCircle T)) where
  dim := 1
  rep := ContRepresentation.congr (fourierModelEquiv.toContinuousLinearEquiv) (fourierRep T n)
  continuous_rep := ContRepresentation.continuous_congr _ (continuous_fourierRep T n)
  isUnitary := (isUnitary_fourierRep T n).congr fourierModelEquiv
  isIrreducible := ContRepresentation.isIrreducible_congr _ (isIrreducible_fourierRep T n)

omit hT in
theorem fourierIrrepModel_dim (n : ℤ) : (fourierIrrepModel T n).dim = 1 :=
  rfl

omit hT in
@[simp]
theorem fourierIrrepModel_rep_apply (n : ℤ) (x : Multiplicative (AddCircle T))
    (v : EuclideanSpace ℂ (Fin (fourierIrrepModel T n).dim)) :
    (fourierIrrepModel T n).rep x v = fourier n (Multiplicative.toAdd x) • v := by
  change EuclideanSpace ℂ (Fin 1) at v
  change ContRepresentation.congr fourierModelEquiv.toContinuousLinearEquiv
    (fourierRep T n) x v = fourier n (Multiplicative.toAdd x) • v
  rw [ContRepresentation.congr_apply, fourierRep_apply, ← smul_eq_mul, map_smul]
  exact congrArg (fourier n (Multiplicative.toAdd x) • ·)
    (LinearIsometryEquiv.apply_symm_apply fourierModelEquiv v)

/-- **The Fourier models form a skeleton of the unitary dual of the circle.** Pairwise
inequivalence is the injectivity of the Fourier index.  Exhaustiveness combines the classification
of circle irreducibles with the fact that an equivalence between irreducible unitary
representations can be rescaled to a linear isometry equivalence. -/
theorem isIrrepSkeleton_fourierIrrepModel : IsIrrepSkeleton (fourierIrrepModel T) where
  pairwise_isEmpty_equiv m n hmn :=
    ⟨fun φ ↦ hmn <| (nonempty_equiv_fourierRep_iff T hT.out.ne').mp ⟨
      ((fourierRep T m).congrEquiv fourierModelEquiv.toContinuousLinearEquiv).trans <|
        φ.trans ((fourierRep T n).congrEquiv
          fourierModelEquiv.toContinuousLinearEquiv).symm⟩⟩
  exists_congr_eq n π hπ hu hirr := by
    obtain ⟨k, ⟨φ⟩⟩ := ContRepresentation.exists_nonempty_equiv_fourierRep π hπ hirr
    let ψ := φ.trans ((fourierRep T k).congrEquiv fourierModelEquiv.toContinuousLinearEquiv)
    obtain ⟨e, he⟩ := ContRepresentation.exists_linearIsometryEquiv_congr_eq hu
      (fourierIrrepModel T k).isUnitary hirr ψ
    exact ⟨k, e, he⟩

/-! ### The matrix coefficients -/

/-- The matrix-coefficient index of the one-dimensional Fourier models is equivalent to `ℤ`.
The negation compensates for Mathlib's convention that the inner product is conjugate-linear in
its first argument. -/
@[expose] noncomputable def fourierPeterWeylIndexEquiv :
    (Σ n : ℤ, Fin (fourierIrrepModel T n).dim × Fin (fourierIrrepModel T n).dim) ≃ ℤ := by
  let collapse : (Σ _ : ℤ, Fin 1 × Fin 1) ≃ ℤ :=
    { toFun := Sigma.fst
      invFun := fun n ↦ ⟨n, 0, 0⟩
      left_inv := fun ⟨n, i, j⟩ ↦ by
        have hi : i = 0 := Fin.eq_zero i
        have hj : j = 0 := Fin.eq_zero j
        subst i
        subst j
        rfl
      right_inv := fun _ ↦ rfl }
  exact ((Equiv.sigmaCongrRight fun n ↦
    Equiv.prodCongr (finCongr (fourierIrrepModel_dim T n))
      (finCongr (fourierIrrepModel_dim T n))).trans collapse).trans (Equiv.neg ℤ)

omit hT in
@[simp]
theorem fourierPeterWeylIndexEquiv_apply
    (x : Σ n : ℤ, Fin (fourierIrrepModel T n).dim × Fin (fourierIrrepModel T n).dim) :
    fourierPeterWeylIndexEquiv T x = -x.1 :=
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

end TauCeti
