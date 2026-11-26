/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.CharacterTwist
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Restriction of determinants and character twists

For an `A`-algebra map `φ : R' →ₐ[A] R` and a `d`-dimensional determinant `D` on `R`, the
composite of the law of `D` with the degree-one law of `φ` is a `d`-dimensional determinant on
`R'`, the *restriction* `D.comap φ`, with value `D (φ x)` at `x`. For a monoid map `f : H →* G`,
restriction along `A[H] → A[G]` is the restriction of a determinant on `G` to `H`.

For a character `θ : G →* Aˣ`, restriction along the algebra automorphism `g ↦ θ(g) g` of
`A[G]` (`MonoidAlgebra.charTwist`) is the twist `D ⊗ θ`. Its characteristic
coefficients at `g` are `Λᵢ(g) θ(g)ⁱ`, its value at `g` is `θ(g)ᵈ D(g)`, and its characteristic
polynomial at `g` is `∑ᵢ (-1)ⁱ θ(g)ⁱ Λᵢ(g) X^(d - i)`.

## Main declarations

* `TauCeti.Determinant.comap`: restriction of a determinant along an algebra map, with
  `comap_apply`, `comap_id`, `comap_comp`, and invariance of the characteristic coefficients,
  trace and characteristic polynomial (`charCoeff_comap`, `trace_comap`, `charpoly_comap`).
* `TauCeti.Determinant.algHomDet_comap`, `TauCeti.Determinant.algHomPow_comap`: restriction of
  `det ∘ ρ` along `φ` is `det ∘ (ρ ∘ φ)`, and likewise for powers of algebra maps.
* `TauCeti.Determinant.comap_mapDomainAlgHom_apply_of`: restriction along `A[H] → A[G]`
  computes `D` on the images of elements of `H`.
* `TauCeti.Determinant.twist`: the twist `D ⊗ θ`, with `twist_apply`, `charCoeff_twist`,
  `trace_twist` and `charpoly_twist` at a general element, and `charCoeff_twist_of`,
  `twist_apply_of` and `charpoly_twist_of` at elements of `G`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.5](https://arxiv.org/abs/0809.0415)
* [P. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  §2.2.20–24, pp. 932–934](https://www.math.uchicago.edu/~fcale/papers/Ramanujan.pdf), for the
  twist by a character and its characteristic polynomial
-/

public section

noncomputable section

universe u

open TensorProduct Polynomial

namespace TauCeti

namespace Determinant

section CommSemiring

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]
  {R' : Type*} [Semiring R'] [Algebra A R'] {R'' : Type*} [Semiring R''] [Algebra A R'']
  {d : ℕ} (D : Determinant A R d)

/-- The restriction `D ∘ φ` of a determinant along an algebra map `φ : R' →ₐ[A] R`: the
composite of the law of `D` with the degree-one law of `φ`, a determinant of the same
dimension. -/
def comap (φ : R' →ₐ[A] R) : Determinant A R' d where
  toLaw := D.toLaw.comp φ.toLinearMap.toPolynomialLaw
  isHomogeneousOfDegree := by
    simpa using D.isHomogeneousOfDegree.comp φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw
  isMultiplicative := D.isMultiplicative.comp φ.isMultiplicative_toPolynomialLaw

theorem toLaw_comap (φ : R' →ₐ[A] R) :
    (D.comap φ).toLaw = D.toLaw.comp φ.toLinearMap.toPolynomialLaw :=
  (rfl)

/-- After scalar extension to `S`, the law of `D.comap φ` is the law of `D` composed with `φ`
extended to `S`. -/
@[simp]
theorem comap_toFun (φ : R' →ₐ[A] R) (S : Type*) [CommSemiring S] [Algebra A S]
    (x : S ⊗[A] R') :
    (D.comap φ).toLaw.toFun S x =
      D.toLaw.toFun S (Algebra.TensorProduct.map (AlgHom.id A S) φ x) := by
  rw [toLaw_comap, PolynomialLaw.toFun_comp_apply, LinearMap.toPolynomialLaw_toFun,
    LinearMap.baseChange_eq_lTensor, AlgHom.lTensor_toLinearMap_apply]

/-- The `toFun'` form of `comap_toFun`, for `S` in the universe of `A`: the law of `D.comap φ`
at `S` is the law of `D` at `S` composed with `φ` extended to `S`. -/
@[simp]
theorem comap_toFun' (φ : R' →ₐ[A] R) (S : Type u) [CommSemiring S] [Algebra A S]
    (x : S ⊗[A] R') :
    (D.comap φ).toLaw.toFun' S x =
      D.toLaw.toFun' S (Algebra.TensorProduct.map (AlgHom.id A S) φ x) := by
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun, comap_toFun]

/-- The value of the restriction `D.comap φ` at `x` is `D (φ x)`. -/
@[simp]
theorem comap_apply (φ : R' →ₐ[A] R) (x : R') : D.comap φ x = D (φ x) := by
  rw [apply_eq_lid_toFun, comap_toFun, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    ← apply_eq_lid_toFun]

/-- Restriction along the identity is the identity. -/
@[simp]
theorem comap_id : D.comap (AlgHom.id A R) = D := by
  ext S _ _ x
  rw [comap_toFun', Algebra.TensorProduct.map_id, AlgHom.id_apply]

/-- Restriction along `ψ ∘ φ` is restriction along `ψ`, then along `φ`. -/
theorem comap_comp (ψ : R' →ₐ[A] R) (φ : R'' →ₐ[A] R') :
    D.comap (ψ.comp φ) = (D.comap ψ).comap φ := by
  ext S _ _ x
  simp [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]

/-- The characteristic coefficients of a restriction: `Λᵢ(D ∘ φ, x) = Λᵢ(D, φ x)`. -/
@[simp]
theorem charCoeff_comap (φ : R' →ₐ[A] R) (i : ℕ) (x : R') :
    (D.comap φ).charCoeff i x = D.charCoeff i (φ x) := by
  rcases lt_or_ge d i with hi | hi
  · rw [charCoeff_eq_zero _ hi, charCoeff_eq_zero _ hi]
  rw [← coeff_rid_toFun_one_tmul_add_X_tmul_one _ hi,
    ← coeff_rid_toFun_one_tmul_add_X_tmul_one _ hi, comap_toFun]
  simp

/-- The trace of a restriction is the trace composed with `φ`. -/
@[simp]
theorem trace_comap (φ : R' →ₐ[A] R) (x : R') : (D.comap φ).trace x = D.trace (φ x) := by
  rw [trace_apply, trace_apply, charCoeff_comap]

/-- Restriction of `algHomPow ψ d` along `φ` is `algHomPow (ψ ∘ φ) d`. -/
@[simp]
theorem algHomPow_comap (ψ : R →ₐ[A] A) (φ : R' →ₐ[A] R) :
    (algHomPow ψ d).comap φ = algHomPow (ψ.comp φ) d := by
  ext S _ _ x
  simp [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]

/-- Restriction along `A[H] → A[G]` for a monoid map `f : H →* G` computes `D` at the image of
`h ∈ H`: it is the restriction of a determinant on `G` to `H`. -/
theorem comap_mapDomainAlgHom_apply_of {G H : Type*} [Monoid G] [Monoid H]
    (D : Determinant A (MonoidAlgebra A G) d) (f : H →* G) (h : H) :
    D.comap (MonoidAlgebra.mapDomainAlgHom A A f) (MonoidAlgebra.of A H h) =
      D (MonoidAlgebra.of A G (f h)) := by
  simp

end CommSemiring

section CommRing

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R]
  {R' : Type*} [Semiring R'] [Algebra A R'] {d : ℕ} (D : Determinant A R d)

/-- The characteristic polynomial of a restriction: `χ(D ∘ φ, x) = χ(D, φ x)`. -/
@[simp]
theorem charpoly_comap (φ : R' →ₐ[A] R) (x : R') : (D.comap φ).charpoly x = D.charpoly (φ x) := by
  simp [charpoly_eq_sum]

/-- Restriction of `det ∘ ρ` along `φ` is `det ∘ (ρ ∘ φ)`. -/
@[simp]
theorem algHomDet_comap {n : Type*} [Fintype n] [DecidableEq n] (ρ : R →ₐ[A] Matrix n n A)
    (φ : R' →ₐ[A] R) : (algHomDet ρ).comap φ = algHomDet (ρ.comp φ) := by
  ext S _ _ x
  simp [toLaw_comap, toLaw_algHomDet, LinearMap.toPolynomialLaw_comp, PolynomialLaw.comp_assoc]

end CommRing

section Twist

variable {A : Type u} [CommSemiring A] {G : Type*} [Monoid G] {d : ℕ}
  (D : Determinant A (MonoidAlgebra A G) d)

/-- The twist `D ⊗ θ` of a determinant on `G` by a character `θ : G →* Aˣ`: the restriction of
`D` along `g ↦ θ(g) g` (ACC §2.2.20–24). -/
def twist (θ : G →* Aˣ) : Determinant A (MonoidAlgebra A G) d :=
  D.comap (MonoidAlgebra.charTwist θ : MonoidAlgebra A G →ₐ[A] MonoidAlgebra A G)

theorem twist_eq_comap (θ : G →* Aˣ) :
    D.twist θ = D.comap (MonoidAlgebra.charTwist θ : MonoidAlgebra A G →ₐ[A] MonoidAlgebra A G) :=
  (rfl)

/-- The value of the twist at `x` is the value of `D` at the twisted element. -/
@[simp]
theorem twist_apply (θ : G →* Aˣ) (x : MonoidAlgebra A G) :
    D.twist θ x = D (MonoidAlgebra.charTwist θ x) := by
  rw [twist, comap_apply, AlgEquiv.coe_toAlgHom]

/-- The characteristic coefficients of the twist at `x` are those of `D` at the twisted
element. -/
@[simp]
theorem charCoeff_twist (θ : G →* Aˣ) (i : ℕ) (x : MonoidAlgebra A G) :
    (D.twist θ).charCoeff i x = D.charCoeff i (MonoidAlgebra.charTwist θ x) := by
  rw [twist, charCoeff_comap, AlgEquiv.coe_toAlgHom]

/-- The trace of the twist at `x` is the trace of `D` at the twisted element. -/
@[simp]
theorem trace_twist (θ : G →* Aˣ) (x : MonoidAlgebra A G) :
    (D.twist θ).trace x = D.trace (MonoidAlgebra.charTwist θ x) := by
  rw [trace_apply, trace_apply, charCoeff_twist]

/-- The characteristic coefficients of the twist at `g ∈ G`: `Λᵢ(D ⊗ θ, g) = θ(g)ⁱ Λᵢ(D, g)`. -/
theorem charCoeff_twist_of (θ : G →* Aˣ) (i : ℕ) (g : G) :
    (D.twist θ).charCoeff i (MonoidAlgebra.of A G g) =
      (θ g : A) ^ i * D.charCoeff i (MonoidAlgebra.of A G g) := by
  rw [charCoeff_twist, MonoidAlgebra.charTwist_of, charCoeff_smul]

/-- The value of the twist at `g ∈ G` is `θ(g)ᵈ D(g)`: the determinant character changes by
`θᵈ`. -/
theorem twist_apply_of (θ : G →* Aˣ) (g : G) :
    D.twist θ (MonoidAlgebra.of A G g) = (θ g : A) ^ d * D (MonoidAlgebra.of A G g) := by
  rw [twist_apply, MonoidAlgebra.charTwist_of, map_smul]

/-- Twisting by the trivial character does nothing. -/
@[simp]
theorem twist_one : D.twist 1 = D := by
  rw [twist, MonoidAlgebra.charTwist_one, AlgEquiv.refl_toAlgHom, comap_id]

/-- Twisting by `ψ` and then by `θ` is twisting by `θψ`. -/
@[simp]
theorem twist_twist (θ ψ : G →* Aˣ) : (D.twist ψ).twist θ = D.twist (θ * ψ) := by
  rw [twist, twist, twist, ← comap_comp]
  exact congrArg D.comap <| AlgHom.ext fun x ↦ by simp [mul_comm θ ψ]

end Twist

section TwistCharpoly

variable {A : Type u} [CommRing A] {G : Type*} [Monoid G] {d : ℕ}
  (D : Determinant A (MonoidAlgebra A G) d)

/-- The characteristic polynomial of the twist at `x` is that of `D` at the twisted element. -/
@[simp]
theorem charpoly_twist (θ : G →* Aˣ) (x : MonoidAlgebra A G) :
    (D.twist θ).charpoly x = D.charpoly (MonoidAlgebra.charTwist θ x) := by
  rw [twist, charpoly_comap, AlgEquiv.coe_toAlgHom]

/-- The characteristic polynomial of the twist at `g ∈ G`:
`χ(D ⊗ θ, g) = ∑ᵢ (-1)ⁱ θ(g)ⁱ Λᵢ(g) X^(d - i)` (ACC §2.2.20–24). -/
theorem charpoly_twist_of (θ : G →* Aˣ) (g : G) :
    (D.twist θ).charpoly (MonoidAlgebra.of A G g) =
      ∑ i ∈ Finset.range (d + 1),
        C ((-1) ^ i * (θ g : A) ^ i * D.charCoeff i (MonoidAlgebra.of A G g)) * X ^ (d - i) := by
  rw [charpoly_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [charCoeff_twist_of, mul_assoc]

end TwistCharpoly

end Determinant

end TauCeti
