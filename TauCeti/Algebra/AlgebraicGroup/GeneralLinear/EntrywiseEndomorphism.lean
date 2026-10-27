/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import Mathlib.LinearAlgebra.Matrix.Transvection
import TauCeti.Algebra.Polynomial.Laurent.Basic
import TauCeti.Algebra.Polynomial.Laurent.Detection
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Nontrivial entrywise field endomorphisms with infinitely many fixed points are not algebraic

A field endomorphism `σ : K →+* K` acts entrywise on `GL_n(K)`. This file shows that, as soon as
`σ` fixes infinitely many elements, this map on `K`-points is not regular unless `σ` is the
identity or `n = 0`. Regular functions on `GL_n` are the elements of the coordinate Hopf algebra
`K[Xᵢⱼ][det(X)⁻¹]`, evaluated at `K`-points through `TauCeti.GeneralLinear.generalLinearToPoint`.
No matrix entry `g ↦ σ (g i j)` is such a function, and consequently no `K`-algebra endomorphism
of the coordinate algebra (that is, no endomorphism of the variety `GL_n`, and in particular no
algebraic representation `GL_n → GL_n`) induces the entrywise map on `K`-points.

The main example is complex conjugation on `GL_n(ℂ)`: it is an automorphism of the abstract group
`GL_n(ℂ)`, but for `n > 0` it is not a complex algebraic representation. For `n = 0` the group is
trivial and conjugation is induced by the identity.

## Main results

* `RingHom.eq_id_of_forall_generalLinearToPoint_eq`: a regular function on `GL_n` whose value at
  every `g` is `σ (g i j)` forces `σ = id`.
* `RingHom.exists_algHom_pointToGeneralLinear_comp_eq_map_iff`: the entrywise map induced by `σ`
  on `K`-points comes from a `K`-algebra endomorphism of the coordinate algebra if and only if
  `n = 0` or `σ = id`.
* `TauCeti.GeneralLinear.exists_algHom_pointToGeneralLinear_comp_eq_map_starRingEnd_iff`:
  entrywise complex conjugation on `GL_n(ℂ)` is induced by an endomorphism of the coordinate
  algebra if and only if `n = 0`.
-/

public section

open LaurentPolynomial WithConv
open scoped ComplexConjugate

namespace RingHom

variable {K : Type*} [Field K] {n : ℕ}

open TauCeti.GeneralLinear

/-- **No matrix entry twisted by a nontrivial field endomorphism with infinitely many fixed points
is a regular function on `GL_n`.** Let `σ` be an endomorphism of `K` fixing infinitely many
elements. If a regular function `f` on `GL_n` takes the value `σ (g i j)` at every
`g ∈ GL_n(K)`, then `σ` is the identity. -/
theorem eq_id_of_forall_generalLinearToPoint_eq (σ : K →+* K)
    (hσ : {x : K | σ x = x}.Infinite) {i j : Fin n} (f : coordinateHopfAlgebra K n)
    (h : ∀ g : GL (Fin n) K, (generalLinearToPoint (R := K) n g).ofConv f = σ (g i j)) :
    σ = RingHom.id K := by
  classical
  -- A point of `GL_n` over `K[T;T⁻¹]` whose `(i, j)` entry is `T`: the diagonal torus
  -- `T ↦ diag(1, …, T, …, 1)` for a diagonal entry, and the transvection `1 + T Eᵢⱼ` otherwise.
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin n) K[T;T⁻¹], γ i j = T 1 := by
    rcases eq_or_ne i j with rfl | hij
    · exact ⟨TauCeti.diagGL (Pi.mulSingle i (isUnit_T 1).unit), by simp⟩
    · refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j (T 1)) ?_, ?_⟩
      · rw [Matrix.det_transvection_of_ne i j hij]
        exact isUnit_one
      · simp [Matrix.transvection, hij]
  -- Restricting `f` along this point gives a Laurent polynomial whose value at every unit `u` is
  -- `σ u`, which forces `σ = id`.
  refine σ.eq_id_of_forall_eval₂_eq hσ ((generalLinearToPoint (R := K) n γ).ofConv f) fun u ↦ ?_
  -- Specializing `T` to `u` is evaluation at the specialized matrix, whose `(i, j)` entry is `u`.
  have hu := congrArg (fun x ↦ x.ofConv f)
    (toConv_comp_generalLinearToPoint_ofConv n (TauCeti.laurentEval (R := K) u) γ)
  simpa [h, hγ, TauCeti.laurentEval_eq_eval₂] using hu

/-- **Nontrivial entrywise field endomorphisms with infinitely many fixed points are not
algebraic on `GL_n`.** Let `σ` be an endomorphism of `K` fixing infinitely many elements. The
map `g ↦ σ g` on `K`-points of `GL_n` is induced by a `K`-algebra endomorphism `φ` of the
coordinate algebra, acting on points by precomposition, if and only if `n = 0` or `σ` is the
identity. Bialgebra endomorphisms, which are the endomorphisms of the algebraic group `GL_n`, are
a special case. -/
theorem exists_algHom_pointToGeneralLinear_comp_eq_map_iff (σ : K →+* K)
    (hσ : {x : K | σ x = x}.Infinite) :
    (∃ φ : coordinateHopfAlgebra K n →ₐ[K] coordinateHopfAlgebra K n,
      ∀ x : WithConv (coordinateHopfAlgebra K n →ₐ[K] K),
        pointToGeneralLinear n (toConv (x.ofConv.comp φ)) =
          Matrix.GeneralLinearGroup.map σ (pointToGeneralLinear n x)) ↔
      n = 0 ∨ σ = RingHom.id K := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine or_iff_not_imp_left.mpr fun hn ↦ ?_
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    refine σ.eq_id_of_forall_generalLinearToPoint_eq hσ (i := i) (j := i)
      (φ (coordinateHopfAlgebraAlgEquiv K n (coordinateRingMap K n (MvPolynomial.X (i, i)))))
      fun g ↦ ?_
    simpa using congrArg (fun g : GL (Fin n) K ↦ g i i) (hφ (generalLinearToPoint (R := K) n g))
  · rintro (rfl | rfl)
    · exact ⟨AlgHom.id K _, fun _ ↦ Matrix.GeneralLinearGroup.ext fun i ↦ i.elim0⟩
    · exact ⟨AlgHom.id K _, fun x ↦ by simp [Matrix.GeneralLinearGroup.map_id]⟩

end RingHom

namespace TauCeti.GeneralLinear

variable {n : ℕ}

/-- **Complex conjugation on `GL_n(ℂ)` is not a complex algebraic representation.** Entrywise
conjugation on the complex points of `GL_n` is induced by a `ℂ`-algebra endomorphism of the
coordinate algebra, acting on points by precomposition, if and only if `n = 0`. -/
theorem exists_algHom_pointToGeneralLinear_comp_eq_map_starRingEnd_iff :
    (∃ φ : coordinateHopfAlgebra ℂ n →ₐ[ℂ] coordinateHopfAlgebra ℂ n,
      ∀ x : WithConv (coordinateHopfAlgebra ℂ n →ₐ[ℂ] ℂ),
        pointToGeneralLinear n (toConv (x.ofConv.comp φ)) =
          Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (pointToGeneralLinear n x)) ↔
      n = 0 := by
  have hfix : {z : ℂ | conj z = z}.Infinite :=
    (Set.infinite_range_of_injective Complex.ofReal_injective).mono <| by
      rintro _ ⟨r, rfl⟩
      exact Complex.conj_ofReal r
  have hne : starRingEnd ℂ ≠ RingHom.id ℂ := fun h ↦ by
    have hI := congrArg (· Complex.I) h
    simp only [Complex.conj_I, RingHom.id_apply, neg_eq_iff_add_eq_zero] at hI
    exact Complex.I_ne_zero (by linear_combination hI / 2)
  rw [(starRingEnd ℂ).exists_algHom_pointToGeneralLinear_comp_eq_map_iff hfix, or_iff_left hne]

end TauCeti.GeneralLinear
