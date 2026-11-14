/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.Lie.AdjointAction.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Derivations of a matrix algebra are inner

Every linear endomorphism of a matrix algebra satisfying the associative Leibniz rule is
commutation with a matrix. This holds over any commutative ring, including in positive
characteristic, and identifies the infinitesimal algebra automorphisms of a matrix algebra.

`Matrix.adRangeEquivPi` parametrizes inner derivations by all matrix entries except one
chosen diagonal entry. Its coordinates normalize that entry to zero by subtracting a
scalar matrix, giving a free coordinate model without dividing by the matrix size.

Over a possibly noncommutative algebra `A`, a derivation `δ` of `A` applied to every entry is a
derivation `TauCeti.derivationLieAlgebra.mapMatrix δ` of the square matrices over `A`, and it
satisfies the Leibniz rule `δ(M v) = δ(M) v + M δ(v)` for matrices acting on column vectors. For
an idempotent matrix `e` it is off-diagonal, `e δ(e) e = 0`, and a trace `τ` on `A` invariant under
`δ` kills the corner `e δ(t) e` of every matrix `t` with `e t = t = t e`. These entrywise
derivations appear when a cyclic cocycle built from a trace and derivations is extended to
matrices, and in the Grassmann connection of a projective module presented by an idempotent
matrix.

## References

* N. Jacobson, *Basic Algebra II*, the innerness of derivations of matrix algebras.
-/

public section

open Matrix

namespace LinearMap

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A linear endomorphism of a matrix algebra satisfies the Leibniz rule exactly when it
is inner, over any commutative ring. No nonemptiness assumption on the matrix index type
is needed. -/
theorem leibniz_iff_exists_matrix_eq_mulLeft_sub_mulRight
    (D : Matrix ι ι R →ₗ[R] Matrix ι ι R) :
    (∀ A B, D (A * B) = D A * B + A * D B) ↔
      ∃ X : Matrix ι ι R, D = LinearMap.mulLeft R X - LinearMap.mulRight R X := by
  classical
  constructor
  · intro hD
    cases isEmpty_or_nonempty ι with
    | inl h =>
      exact ⟨0, Subsingleton.elim _ _⟩
    | inr h =>
      let r : ι := Classical.choice h
      let X : Matrix ι ι R := of fun a b => D (Matrix.single b r 1) a r
      refine ⟨X, (stdBasis R ι ι).ext fun ij => ?_⟩
      rcases ij with ⟨i, j⟩
      rw [stdBasis_eq_single]
      rw [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      ext a b
      have hab := congrArg (fun M : Matrix ι ι R => M a r)
        (hD (Matrix.single i j 1) (Matrix.single b r 1))
      by_cases hjb : j = b <;> by_cases hai : a = i <;>
        simp_all [single_mul_single_of_ne, X, of_apply, ne_comm]
  · rintro ⟨X, rfl⟩
    simpa only [LieAlgebra.ad_eq_lmul_left_sub_lmul_right, Pi.sub_apply,
      LinearMap.sub_apply] using
      (TauCeti.mem_derivationLieAlgebra.mp (TauCeti.ad_mem_derivationLieAlgebra R X))

end LinearMap

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

section CoordinateMatrix

variable (R ι : Type*) [Semiring R] [DecidableEq ι]

private def adCoordinateMatrix (p : ι) :
    ({ij : ι × ι // ij ≠ (p, p)} → R) →ₗ[R] Matrix ι ι R :=
  (ofLinearEquiv R).toLinearMap.comp <|
    LinearMap.pi fun i => LinearMap.pi fun j =>
      if h : (i, j) = (p, p) then 0 else LinearMap.proj ⟨(i, j), h⟩

private lemma adCoordinateMatrix_apply (p : ι)
    (c : {ij : ι × ι // ij ≠ (p, p)} → R) :
    adCoordinateMatrix R ι p c =
      (of fun i j => if h : (i, j) = (p, p) then 0 else c ⟨(i, j), h⟩) := by
  ext i j
  simp only [adCoordinateMatrix, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coe_ofLinearEquiv, of_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

end CoordinateMatrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- An inner derivation of a matrix algebra vanishes exactly when its defining matrix
is scalar. -/
theorem ad_eq_zero_iff (X : Matrix ι ι R) :
    LieAlgebra.ad R (Matrix ι ι R) X = 0 ↔ X ∈ Set.range (scalar ι) := by
  rw [TauCeti.LieAlgebra.ad_eq_zero_iff_mem_center]
  simp [← Matrix.center_eq_range, Subalgebra.mem_center_iff, Semigroup.mem_center_iff]

noncomputable section

variable (R ι)

private def adFromCoordinates (p : ι) :
    ({ij : ι × ι // ij ≠ (p, p)} → R) →ₗ[R]
      (LieAlgebra.ad R (Matrix ι ι R)).range :=
  (LieAlgebra.ad R (Matrix ι ι R)).rangeRestrict.toLinearMap.comp
    (adCoordinateMatrix R ι p)

private lemma adFromCoordinates_injective (p : ι) :
    Function.Injective (adFromCoordinates R ι p) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  have had : LieAlgebra.ad R (Matrix ι ι R) (adCoordinateMatrix R ι p c) = 0 :=
    congrArg Subtype.val hc
  obtain ⟨a, ha⟩ := (ad_eq_zero_iff _).mp had
  have ha0 : a = 0 := by
    have h := congrArg (fun X : Matrix ι ι R => X p p) ha
    simpa [adCoordinateMatrix_apply] using h
  have hm : adCoordinateMatrix R ι p c = 0 := by simpa [ha0] using ha.symm
  funext ij
  have h := congrArg (fun X : Matrix ι ι R => X ij.1.1 ij.1.2) hm
  simpa only [adCoordinateMatrix_apply, of_apply, dite_eq_right ij.2, Matrix.zero_apply,
    Pi.zero_apply] using h

private lemma adFromCoordinates_normalize (p : ι) (X : Matrix ι ι R) :
    adFromCoordinates R ι p
        (fun ij => X ij.1.1 ij.1.2 - if ij.1.1 = ij.1.2 then X p p else 0) =
      (LieAlgebra.ad R (Matrix ι ι R)).rangeRestrict X := by
  classical
  let c : {ij : ι × ι // ij ≠ (p, p)} → R :=
    fun ij => X ij.1.1 ij.1.2 - if ij.1.1 = ij.1.2 then X p p else 0
  have hmatrix : adCoordinateMatrix R ι p c = X - scalar ι (X p p) := by
    ext i j
    by_cases h : (i, j) = (p, p)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp [adCoordinateMatrix_apply]
    · simp only [adCoordinateMatrix_apply, of_apply,
        dite_eq_right h, c, Matrix.sub_apply, scalar_apply, diagonal_apply]
  apply Subtype.ext
  dsimp only [adFromCoordinates, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieHom.rangeRestrict_apply]
  rw [hmatrix, map_sub, (ad_eq_zero_iff _).mpr ⟨X p p, rfl⟩, sub_zero]

private lemma adFromCoordinates_surjective (p : ι) :
    Function.Surjective (adFromCoordinates R ι p) := by
  rintro ⟨D, X, rfl⟩
  exact ⟨_, adFromCoordinates_normalize R ι p X⟩

/-- Inner derivations of a matrix algebra are freely parametrized by all matrix entries
except one diagonal entry. The representative has its `(p,p)` entry normalized to zero.
This normalization works over every commutative ring, without dividing by the matrix size. -/
def adRangeEquivPi (p : ι) :
    (LieAlgebra.ad R (Matrix ι ι R)).range ≃ₗ[R]
      ({ij : ι × ι // ij ≠ (p, p)} → R) :=
  (LinearEquiv.ofBijective (adFromCoordinates R ι p)
    ⟨adFromCoordinates_injective R ι p, adFromCoordinates_surjective R ι p⟩).symm

/-- Coordinates of an inner derivation subtract the chosen diagonal entry on the diagonal
and keep the off-diagonal entries. -/
@[simp]
theorem adRangeEquivPi_apply_ad (p : ι) (X : Matrix ι ι R)
    (ij : {ij : ι × ι // ij ≠ (p, p)}) :
    adRangeEquivPi R ι p
        ⟨LieAlgebra.ad R (Matrix ι ι R) X, (LieAlgebra.ad R _).mem_range_self X⟩ ij =
      X ij.1.1 ij.1.2 - if ij.1.1 = ij.1.2 then X p p else 0 := by
  classical
  let c : {ij : ι × ι // ij ≠ (p, p)} → R :=
    fun ij => X ij.1.1 ij.1.2 - if ij.1.1 = ij.1.2 then X p p else 0
  have h : adFromCoordinates R ι p c =
      (LieAlgebra.ad R (Matrix ι ι R)).rangeRestrict X :=
    adFromCoordinates_normalize R ι p X
  rw [LieHom.rangeRestrict_apply] at h
  rw [← h]
  exact congrFun ((adRangeEquivPi R ι p).apply_symm_apply c) ij

/-- Filling the omitted diagonal entry with zero recovers the inner derivation from
its coordinates. -/
@[simp]
theorem adRangeEquivPi_symm_apply (p : ι)
    (c : {ij : ι × ι // ij ≠ (p, p)} → R) (Y : Matrix ι ι R) :
    ((adRangeEquivPi R ι p).symm c : Module.End R (Matrix ι ι R)) Y =
      (of fun i j => if h : (i, j) = (p, p) then 0 else c ⟨(i, j), h⟩) * Y -
        Y * (of fun i j => if h : (i, j) = (p, p) then 0 else c ⟨(i, j), h⟩) := by
  classical
  simp only [adRangeEquivPi, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply,
    adFromCoordinates, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieHom.rangeRestrict_apply, LieAlgebra.ad_apply, Ring.lie_def,
    adCoordinateMatrix_apply]

/-- A coordinate unit corresponds to commutation with the same matrix unit. -/
@[simp]
theorem adRangeEquivPi_symm_single (p : ι) (ij : {ij : ι × ι // ij ≠ (p, p)}) :
    (adRangeEquivPi R ι p).symm (Pi.single ij 1) =
      (LieAlgebra.ad R (Matrix ι ι R)).rangeRestrict (single ij.1.1 ij.1.2 1) := by
  apply (adRangeEquivPi R ι p).injective
  ext kl
  have hpp : single ij.1.1 ij.1.2 (1 : R) p p = 0 := by
    apply single_apply_of_ne
    exact fun h => ij.2 (Prod.ext h.1 h.2)
  simp only [LinearEquiv.apply_symm_apply, LieHom.rangeRestrict_apply,
    adRangeEquivPi_apply_ad, hpp, ite_self, sub_zero]
  simp [Pi.single_apply, single_apply, Subtype.ext_iff, Prod.ext_iff, eq_comm]

/-- Inner derivations of a finite matrix algebra form a free module, including when the
matrix index type is empty. -/
instance moduleFree_adRange : Module.Free R (LieAlgebra.ad R (Matrix ι ι R)).range := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => infer_instance
  | inr h => exact Module.Free.of_equiv (adRangeEquivPi R ι (Classical.choice h)).symm

/-- Inner derivations of a finite matrix algebra form a finite module. -/
instance moduleFinite_adRange : Module.Finite R (LieAlgebra.ad R (Matrix ι ι R)).range :=
  Module.Finite.range (LieAlgebra.ad R (Matrix ι ι R)).toLinearMap

/-- The module of inner derivations of a finite matrix algebra has rank `card ι ^ 2 - 1`,
including for an empty index type and in every characteristic. -/
@[simp]
theorem finrank_adRange [Nontrivial R] :
    Module.finrank R (LieAlgebra.ad R (Matrix ι ι R)).range = Fintype.card ι ^ 2 - 1 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp [Module.finrank_eq_zero_of_subsingleton]
  | inr h =>
    rw [(adRangeEquivPi R ι (Classical.choice h)).finrank_eq, Module.finrank_pi,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_prod, ← pow_two]

end

end Matrix

namespace TauCeti.derivationLieAlgebra

variable {k A : Type*} [CommRing k] [NonUnitalRing A] [Module k A] [SMulCommClass k A A]
  [IsScalarTower k A A] {ι κ : Type*} [Fintype ι]

/-- **The Leibniz rule for matrices acting on vectors**: applying a derivation `δ` to the
coordinates of `M v` gives `δ(M) v + M δ(v)`. -/
theorem comp_mulVec (δ : derivationLieAlgebra k A) (M : Matrix κ ι A) (v : ι → A) :
    (δ : Module.End k A) ∘ (M *ᵥ v) =
      M.map (δ : Module.End k A) *ᵥ v + M *ᵥ ((δ : Module.End k A) ∘ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, Finset.sum_add_distrib]

/-- A derivation `δ` of `A`, applied to every entry, is a derivation `M ↦ M.map δ` of the square
matrices over `A`. -/
def mapMatrix (δ : derivationLieAlgebra k A) : derivationLieAlgebra k (Matrix ι ι A) :=
  ⟨(δ : Module.End k A).mapMatrix, mem_derivationLieAlgebra.2 fun M N ↦ by
    ext i j
    simp [Matrix.mul_apply, map_sum, Finset.sum_add_distrib]⟩

@[simp]
theorem mapMatrix_apply (δ : derivationLieAlgebra k A) (M : Matrix ι ι A) :
    ((mapMatrix δ : derivationLieAlgebra k (Matrix ι ι A)) : Module.End k (Matrix ι ι A)) M =
      M.map (δ : Module.End k A) :=
  (rfl)

/-- The coordinate derivative of a column vector `v` fixed by a matrix `M` splits as
`δ(v) = δ(M) v + M δ(v)`. -/
theorem comp_eq_map_mulVec_add_of_mulVec_eq (δ : derivationLieAlgebra k A) {M : Matrix ι ι A}
    {v : ι → A} (hv : M *ᵥ v = v) :
    (δ : Module.End k A) ∘ v =
      M.map (δ : Module.End k A) *ᵥ v + M *ᵥ ((δ : Module.End k A) ∘ v) := by
  conv_lhs => rw [← hv]
  exact comp_mulVec δ M v

end TauCeti.derivationLieAlgebra

namespace IsIdempotentElem

open TauCeti

variable {k A : Type*} [CommRing k] [NonUnitalRing A] [Module k A] [SMulCommClass k A A]
  [IsScalarTower k A A] {ι : Type*} [Fintype ι] {e : Matrix ι ι A}

/-- `e δ(e) e = 0` for an idempotent matrix `e` and a derivation `δ` applied to every entry. -/
theorem mul_map_mul_eq_zero (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A) :
    e * e.map (δ : Module.End k A) * e = 0 := by
  simpa using derivationLieAlgebra.mul_apply_mul_eq_zero (derivationLieAlgebra.mapMatrix δ) he

/-- For a trace `τ` invariant under a derivation `δ` and an idempotent matrix `e`, the corner
`e δ(t) e` of the entrywise derivative of a matrix `t` with `e t = t = t e` has trace zero. -/
theorem map_trace_mul_map_mul_eq_zero (he : IsIdempotentElem e) {M : Type*} [AddCommGroup M]
    [Module k M] {τ : A →ₗ[k] M} (hτ : ∀ x y, τ (x * y) = τ (y * x))
    {δ : derivationLieAlgebra k A} (hδ : ∀ x, τ ((δ : Module.End k A) x) = 0)
    {t : Matrix ι ι A} (hl : e * t = t) (hr : t * e = t) :
    τ (e * t.map (δ : Module.End k A) * e).trace = 0 := by
  -- Differentiating `t = t e` gives `δ(t) e = δ(t) - t δ(e)`.
  have hL : t.map (δ : Module.End k A) =
      t.map (δ : Module.End k A) * e + t * e.map (δ : Module.End k A) := by
    simpa [hr] using derivationLieAlgebra.leibniz (derivationLieAlgebra.mapMatrix δ) t e
  have h₀ : τ (t.map (δ : Module.End k A)).trace = 0 := by
    simp [Matrix.trace, hδ]
  have h₁ : τ (t * e.map (δ : Module.End k A)).trace = 0 := by
    calc τ (t * e.map (δ : Module.End k A)).trace
        _ = τ (e * t * e.map (δ : Module.End k A)).trace := by rw [hl]
        _ = τ (t * e.map (δ : Module.End k A) * e).trace := by
          rw [Matrix.mul_assoc, map_trace_mul_comm τ hτ e]
        _ = τ (t * e * e.map (δ : Module.End k A) * e).trace := by rw [hr]
        _ = 0 := by
          rw [Matrix.mul_assoc t, Matrix.mul_assoc t, he.mul_map_mul_eq_zero δ,
            Matrix.mul_zero, trace_zero, map_zero]
  rw [Matrix.mul_assoc, map_trace_mul_comm τ hτ e, Matrix.mul_assoc, he.eq,
    eq_sub_of_add_eq hL.symm, trace_sub, map_sub, h₀, h₁, sub_zero]

end IsIdempotentElem
