/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.PolynomialLaw.Determinant.Comap
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Examples: restriction of determinants and character twists

* Restriction along the identity returns the determinant itself.
* Restriction of `det ∘ ρ` along `φ` is `det ∘ (ρ ∘ φ)`.
* Restriction along `A[H] → A[G]` computes the determinant at the images of elements of `H`.
* For the rank-one identity determinant of `ℤ`, restriction along evaluation at two takes `X`
  to `2`, and restriction along evaluation at zero kills `X` and preserves `1`.
* Twisting by a character `θ` multiplies the characteristic coefficients at `g` by powers of
  `θ(g)` and the value at `g` by `θ(g)ᵈ`.
-/

open TauCeti Determinant Polynomial

variable {A : Type} [CommRing A]

-- Restriction along the identity returns `D` itself.
example {R : Type*} [Ring R] [Algebra A R] {d : ℕ} (D : Determinant A R d) :
    D.comap (AlgHom.id A R) = D :=
  comap_id D

-- Restriction of `det ∘ ρ` along `φ` is `det ∘ (ρ ∘ φ)`.
example {R R' : Type*} [Ring R] [Algebra A R] [Ring R'] [Algebra A R'] {n : Type*} [Fintype n]
    [DecidableEq n] (ρ : R →ₐ[A] Matrix n n A) (φ : R' →ₐ[A] R) :
    (algHomDet ρ).comap φ = algHomDet (ρ.comp φ) :=
  algHomDet_comap ρ φ

-- Restriction to a subgroup `H ≤ G` along `A[H] → A[G]` computes `D` on elements of `H`.
example {G : Type*} [Group G] (H : Subgroup G) {d : ℕ} (D : Determinant A (MonoidAlgebra A G) d)
    (h : H) :
    D.comap (MonoidAlgebra.mapDomainAlgHom A A H.subtype) (MonoidAlgebra.of A H h) =
      D (MonoidAlgebra.of A G h) :=
  comap_mapDomainAlgHom_apply_of D H.subtype h

-- `algHomPow (AlgHom.id ℤ ℤ) 1` is the rank-one identity determinant of `ℤ`.
-- Restriction along evaluation at two takes `X` to `2`.
example : (algHomPow (AlgHom.id ℤ ℤ) 1).comap (aeval (2 : ℤ)) X = 2 := by
  simp

-- Restriction along evaluation at zero kills `X` ...
example : (algHomPow (AlgHom.id ℤ ℤ) 1).comap (aeval (0 : ℤ)) X = 0 := by
  simp

-- ... and preserves `1`.
example : (algHomPow (AlgHom.id ℤ ℤ) 1).comap (aeval (0 : ℤ)) 1 = 1 := by
  simp

-- Twisting by `θ` multiplies `Λᵢ` at `g` by `θ(g)ⁱ`.
example {G : Type*} [Monoid G] {d : ℕ} (D : Determinant A (MonoidAlgebra A G) d)
    (θ : G →* Aˣ) (i : ℕ) (g : G) :
    (D.twist θ).charCoeff i (MonoidAlgebra.of A G g) =
      (θ g : A) ^ i * D.charCoeff i (MonoidAlgebra.of A G g) :=
  charCoeff_twist_of D θ i g

-- The twist of the square of a character `χ` by `θ` takes the value `θ(g)² χ(g)²` at `g`.
example {G : Type*} [Monoid G] (χ θ : G →* Aˣ) (g : G) :
    (algHomPow (MonoidAlgebra.lift A A G (Units.coeHom A |>.comp χ)) 2).twist θ
      (MonoidAlgebra.of A G g) = (θ g : A) ^ 2 * (χ g : A) ^ 2 := by
  rw [twist_apply_of, algHomPow_apply, MonoidAlgebra.lift_of, MonoidHom.comp_apply,
    Units.coeHom_apply]
