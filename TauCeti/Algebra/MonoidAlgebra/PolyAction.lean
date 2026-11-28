/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Polynomial-coefficient group algebra actions and block decompositions

For a commutative ring `O`, a group `G`, and an index type `J`, this file extends matrix
representations `ρ : G →* Matrix n n O` and characters `ξ : G →* O` to `MvPolynomial J O`-algebra
homomorphisms `polyAction J ρ` and `polyChar J ξ` on the group algebra `(MvPolynomial J O)[G]`.
It proves their evaluation on single group elements and univariate polynomials, shows that a
block-diagonal decomposition `u = ρ ⊕ ⨁_e ξ_e` passes to `polyAction J u`, and factors the
constant-family map `MvPolynomial J O →+* (Y → MvPolynomial J L)` through any subalgebra `S`
containing the constant variable families `X j`.

## Main definitions and results

* `TauCeti.polyAction`, `TauCeti.polyChar`: extensions of `ρ : G →* Matrix n n O` and
  `ξ : G →* O` to `(MvPolynomial J O)[G]`.
* `TauCeti.polyAction_single`, `TauCeti.polyAction_aeval`: evaluation of `polyAction` on
  `MonoidAlgebra.single` and `Polynomial.aeval`.
* `TauCeti.polyAction_eq_reindex`: block-diagonal decomposition of `polyAction J u` into
  `polyAction J ρ` and diagonal `polyChar J (ξ e)`.
* `TauCeti.exists_ringHom_comp_eq_algebraMap`: factoring `algebraMap (MvPolynomial J O) _`
  through a subalgebra `S : Subalgebra O (Y → MvPolynomial J L)` containing all `X j`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/RibetMatrices.lean` (`New.Selmer.polyAction`,
`New.Selmer.polyChar`, `New.Selmer.polyAction_single`, `New.Selmer.polyAction_aeval`) and
`src/New/Congruences/FirstOrder/RibetLemma.lean` (`New.Selmer.polyAction_eq_reindex`,
`New.Selmer.exists_ringHom_comp_eq_algebraMap`) in <https://github.com/lsernau/grh-lean> at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Matrix MonoidAlgebra MvPolynomial Polynomial

/-- Extension of a matrix representation `ρ : G →* Matrix n n O` to an `MvPolynomial J O`-algebra
homomorphism on the group algebra `(MvPolynomial J O)[G]`. -/
noncomputable def polyAction (J : Type*) {O G n : Type*} [CommRing O] [Group G] [Fintype n]
    [DecidableEq n] (ρ : G →* Matrix n n O) :
    (MvPolynomial J O)[G] →ₐ[MvPolynomial J O] Matrix n n (MvPolynomial J O) :=
  MonoidAlgebra.lift (MvPolynomial J O) (Matrix n n (MvPolynomial J O)) G
    ((Algebra.ofId O (MvPolynomial J O)).mapMatrix.toMonoidHom.comp ρ)

/-- Extension of a character `ξ : G →* O` to an `MvPolynomial J O`-algebra homomorphism on the
group algebra `(MvPolynomial J O)[G]`. -/
noncomputable def polyChar (J : Type*) {O G : Type*} [CommRing O] [Group G] (ξ : G →* O) :
    (MvPolynomial J O)[G] →ₐ[MvPolynomial J O] MvPolynomial J O :=
  MonoidAlgebra.lift (MvPolynomial J O) (MvPolynomial J O) G
    ((Algebra.ofId O (MvPolynomial J O)).toMonoidHom.comp ξ)

/-- `polyAction J ρ` sends `c • g` to `c` times `ρ g` mapped into `MvPolynomial J O`. -/
theorem polyAction_single (J : Type*) {O G n : Type*} [CommRing O] [Group G] [Fintype n]
    [DecidableEq n] (ρ : G →* Matrix n n O) (g : G) (c : MvPolynomial J O) :
    polyAction J ρ (MonoidAlgebra.single g c) =
      c • (Algebra.ofId O (MvPolynomial J O)).mapMatrix (ρ g) := by
  simp [polyAction]

/-- `polyAction J ρ` intertwines `Polynomial.aeval (.single g 1)` with `Polynomial.aeval (ρ g)`. -/
theorem polyAction_aeval (J : Type*) {O G n : Type*} [CommRing O] [Group G] [Fintype n]
    [DecidableEq n] (ρ : G →* Matrix n n O) (g : G) (P : O[X]) :
    polyAction J ρ (Polynomial.aeval (MonoidAlgebra.single g (1 : MvPolynomial J O)) P) =
      (Algebra.ofId O (MvPolynomial J O)).mapMatrix (Polynomial.aeval (ρ g) P) := by
  have h_single : (polyAction J ρ).restrictScalars O (MonoidAlgebra.single g 1) =
      (Algebra.ofId O (MvPolynomial J O)).mapMatrix (ρ g) := by
    simp [polyAction_single]
  rw [← aeval_algHom_apply (Algebra.ofId O (MvPolynomial J O)).mapMatrix, ← h_single,
    aeval_algHom_apply, AlgHom.restrictScalars_apply]

/-- A block-diagonal decomposition `u g = reindex blockEquiv blockEquiv (fromBlocks (ρ g) 0 0
(diagonal (ξ · g)))` passes to `polyAction J u` on all of `(MvPolynomial J O)[G]`. -/
theorem polyAction_eq_reindex (J : Type*) {O G σ r : Type*} [CommRing O] [Group G] [Fintype σ]
    [DecidableEq σ] [Fintype r] [DecidableEq r] {t : ℕ} (blockEquiv : r ⊕ Fin t ≃ σ)
    {u : G →* Matrix σ σ O} {ρ : G →* Matrix r r O} {ξ : Fin t → G →* O}
    (hu : ∀ g : G, u g = reindex blockEquiv blockEquiv
      (fromBlocks (ρ g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (c : (MvPolynomial J O)[G]) :
    polyAction J u c = reindex blockEquiv blockEquiv
      (fromBlocks (polyAction J ρ c) 0 0 (diagonal fun e : Fin t ↦ polyChar J (ξ e) c)) := by
  rw [← Equiv.symm_apply_eq]
  ext1 (i | i) (j | j)
  · simp [polyAction, hu, MonoidAlgebra.lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, hu, MonoidAlgebra.lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, hu, MonoidAlgebra.lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, polyChar, hu, MonoidAlgebra.lift_apply, diagonal,
      apply_ite (Algebra.ofId O _), Finsupp.sum, Matrix.sum_apply]

/-- If a subalgebra `S : Subalgebra O (Y → MvPolynomial J L)` contains every constant variable
family `fun _ ↦ MvPolynomial.X j`, then `MvPolynomial.map (algebraMap O L)` composed with constant
functions factors through `S`. -/
theorem exists_ringHom_comp_eq_algebraMap {O L Y J : Type*} [CommRing O] [CommRing L] [Algebra O L]
    {S : Subalgebra O (Y → MvPolynomial J L)}
    (hS_X : ∀ j : J, (fun _ : Y ↦ MvPolynomial.X (R := L) j) ∈ S) :
    ∃ κ : MvPolynomial J O →+* S,
      (algebraMap S (Y → MvPolynomial J L)).comp κ =
        (Pi.constRingHom Y (MvPolynomial J L)).comp (MvPolynomial.map (algebraMap O L)) := by
  let X' : J → S := fun j ↦ ⟨fun _ ↦ MvPolynomial.X j, hS_X j⟩
  refine ⟨(MvPolynomial.aeval X').toRingHom, MvPolynomial.ringHom_ext (fun c ↦ ?_) fun j ↦ ?_⟩
  · ext
    simp
  · ext
    simp [X']

end TauCeti
