/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FundamentalGroup
public import TauCeti.FieldTheory.Finite.GaloisZHat

/-!
# The étale fundamental group of a finite field

For a finite field `k` and a separably closed algebraic extension `Ω` of `k`, for instance an
algebraic closure, the étale fundamental group of `Spec k` at the geometric point
`Spec Ω ⟶ Spec k` is the profinite integers: it is `Gal(Ω/k)` as a topological group
(`TauCeti.FiniteEtaleScheme.galContinuousMulEquivAutFiber`), and `Gal(Ω/k) ≃ₜ* ℤ̂` with the
arithmetic Frobenius going to the canonical generator (`TauCeti.FiniteField.galoisGroupEquivZHat`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.etaleFundamentalGroupFiniteFieldEquivZHat`: the étale fundamental
  group of `Spec k` at `Spec Ω` is `ℤ̂`, with the automorphism given by the arithmetic Frobenius
  going to `zHat.gen`
  (`etaleFundamentalGroupFiniteFieldEquivZHat_galContinuousMulEquivAutFiber_frobenius`). It agrees
  with `FiniteField.galoisGroupEquivZHat` through `galContinuousMulEquivAutFiber`
  (`etaleFundamentalGroupFiniteFieldEquivZHat_galContinuousMulEquivAutFiber`), and its inverse is
  the lift of Frobenius (`etaleFundamentalGroupFiniteFieldEquivZHat_symm_apply`).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  [IsSepClosed Ω]

/-- **The étale fundamental group of a finite field is `ℤ̂`.** For a finite field `k` and a
separably closed algebraic extension `Ω`, the étale fundamental group of `Spec k` at the geometric
point `Spec Ω ⟶ Spec k` is isomorphic to `ℤ̂` as a topological group. -/
def etaleFundamentalGroupFiniteFieldEquivZHat :
    EtaleFundamentalGroup (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≃ₜ* zHat.{u} :=
  (galContinuousMulEquivAutFiber k Ω).symm.trans (FiniteField.galoisGroupEquivZHat k Ω)

/-- On the automorphism of the geometric fibre functor given by `σ ∈ Gal(Ω/k)`, the equivalence
is `FiniteField.galoisGroupEquivZHat`. -/
@[simp]
theorem etaleFundamentalGroupFiniteFieldEquivZHat_galContinuousMulEquivAutFiber
    (σ : Gal(Ω/k)) :
    etaleFundamentalGroupFiniteFieldEquivZHat k Ω (galContinuousMulEquivAutFiber k Ω σ) =
      FiniteField.galoisGroupEquivZHat k Ω σ := by
  simp [etaleFundamentalGroupFiniteFieldEquivZHat]

/-- The inverse equivalence sends `x : ℤ̂` to the automorphism of the geometric fibre functor given
by `zHat.lift` of the arithmetic Frobenius of `Ω`, evaluated at `x`. -/
@[simp]
theorem etaleFundamentalGroupFiniteFieldEquivZHat_symm_apply (x : zHat.{u}) :
    (etaleFundamentalGroupFiniteFieldEquivZHat k Ω).symm x =
      galContinuousMulEquivAutFiber k Ω
        (zHat.lift (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) x) := by
  rw [ContinuousMulEquiv.symm_apply_eq,
    etaleFundamentalGroupFiniteFieldEquivZHat_galContinuousMulEquivAutFiber,
    ← FiniteField.galoisGroupEquivZHat_symm_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The automorphism of the geometric fibre functor given by the arithmetic Frobenius of `Ω`
corresponds to the canonical generator of `ℤ̂`. -/
theorem etaleFundamentalGroupFiniteFieldEquivZHat_galContinuousMulEquivAutFiber_frobenius :
    etaleFundamentalGroupFiniteFieldEquivZHat k Ω
      (galContinuousMulEquivAutFiber k Ω
        (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) = zHat.gen := by
  rw [etaleFundamentalGroupFiniteFieldEquivZHat_galContinuousMulEquivAutFiber,
    FiniteField.galoisGroupEquivZHat_apply_frobenius]

end TauCeti.FiniteEtaleScheme
