/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineSpace.NoetherNormalization
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Examples of geometric linear Noether normalization on affine spaces

* **Standard affine space:** evaluating at the standard indeterminates `MvPolynomial.X` and
  composing with the identity linear map recovers the canonical isomorphism
  `(SpecIso n (.of R)).inv : Spec (.of (MvPolynomial n R)) ⟶ 𝔸(n; Spec (.of R))`.
* **Quotient presentations of closed subschemes:** for any proper ideal `I ≠ ⊤` in
  `MvPolynomial n k` over an infinite field `k`, the residue classes of `X` embed
  `Spec (.of (MvPolynomial n k ⧸ I))` as a closed subscheme of `𝔸(n; Spec (.of k))` admitting a
  finite surjective `k`-linear projection onto `𝔸(ULift (Fin d); Spec (.of k))` with
  `ringKrullDim (MvPolynomial n k ⧸ I) = d`.
* **Explicit projection of a nonreduced axis:** over *any* field `k`, the coordinate projection
  `!![1, 0]` sends the doubled axis `Spec (.of (k[X₀, X₁] ⧸ (X₁²))) ↪ 𝔸²_k` via a finite
  surjective morphism onto `𝔸¹_k`.
-/

public section

namespace AlgebraicGeometry.AffineSpace.NoetherNormalizationExamples

open CategoryTheory MvPolynomial

universe u

-- Standard coordinates on `MvPolynomial n R` composed with the identity matrix yield `SpecIso.inv`.
example (R : Type u) [CommRing R] (n : Type u) [Fintype n] [DecidableEq n] :
    homOfAlgebra (R := R) (MvPolynomial.X : n → MvPolynomial n R) ≫
        linearMap (Spec (.of R)) ((1 : Matrix n n R).map (Scheme.ΓSpecIso (.of R)).inv) =
      (SpecIso n (.of R)).inv := by
  have h1 : (1 : Matrix n n R).map (Scheme.ΓSpecIso (.of R)).inv = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h1, linearMap_one, Category.comp_id, homOfAlgebra_X]

-- Any proper ideal `I ≠ ⊤` in `MvPolynomial n k` over an infinite field `k` defines a closed
-- subscheme `Spec (.of (MvPolynomial n k ⧸ I)) ↪ 𝔸(n; Spec (.of k))` with a finite surjective
-- `k`-linear projection onto an affine space of dimension `ringKrullDim (MvPolynomial n k ⧸ I)`.
example (k : Type u) [Field k] [Infinite k] (n : Type u) [Fintype n]
    (I : Ideal (MvPolynomial n k)) (hI : I ≠ ⊤) :
    let x : n → MvPolynomial n k ⧸ I := fun j ↦ Ideal.Quotient.mk I (X j)
    IsClosedImmersion (homOfAlgebra (R := k) x) ∧
      ∃ (d : ℕ) (_ : d ≤ Fintype.card n) (C : Matrix (ULift.{u} (Fin d)) n k),
        let π := homOfAlgebra (R := k) x ≫
          linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv)
        IsFinite π ∧ Surjective π ∧ (∀ q, (π ⁻¹' {q}).Finite) ∧
          ringKrullDim (MvPolynomial n k ⧸ I) = d := by
  have : Nontrivial (MvPolynomial n k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact exists_linear_normalization (fun j ↦ Ideal.Quotient.mk I (X j))
    I.adjoin_range_quotient_mk_X_eq_top

-- Over any field `k`, projecting the doubled axis `Spec (k[X₀, X₁] ⧸ (X₁²))` along `!![1, 0]`
-- gives an explicit finite surjective linear morphism onto `𝔸¹_k`.
example (k : Type u) [Field k] :
    let I : Ideal (MvPolynomial (ULift.{u} (Fin 2)) k) := Ideal.span {X ⟨1⟩ ^ 2}
    let x : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I :=
      fun j ↦ Ideal.Quotient.mk I (X j)
    let C : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 2)) k :=
      (!![1, 0] : Matrix (Fin 1) (Fin 2) k).submatrix ULift.down ULift.down
    let π := homOfAlgebra (R := k) x ≫
      linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv)
    IsClosedImmersion (homOfAlgebra (R := k) x) ∧ IsFinite π ∧ Surjective π := by
  dsimp only
  set I : Ideal (MvPolynomial (ULift.{u} (Fin 2)) k) := Ideal.span {X ⟨1⟩ ^ 2}
  set x : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I :=
    fun j ↦ Ideal.Quotient.mk I (X j)
  let C : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 2)) k :=
    (!![1, 0] : Matrix (Fin 1) (Fin 2) k).submatrix ULift.down ULift.down
  have hadj : Algebra.adjoin k (Set.range x) = ⊤ := I.adjoin_range_quotient_mk_X_eq_top
  let y : ULift.{u} (Fin 1) → MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I := fun _ ↦ x ⟨0⟩
  have hπ : homOfAlgebra (R := k) x ≫
      linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv) =
      homOfAlgebra (R := k) y := by
    rw [homOfAlgebra_linearMap, homOfAlgebra_inj]
    funext ⟨i⟩
    fin_cases i
    have hsum := Equiv.ulift.sum_comp
      fun j : Fin 2 ↦ (!![1, 0] : Matrix (Fin 1) (Fin 2) k) 0 j • x ⟨j⟩
    simpa [C, y, Fin.sum_univ_two] using hsum
  have hproj_ker : ∀ p ∈ I,
      (aeval (R := k) (fun j : ULift.{u} (Fin 2) ↦
        if j.down = 0 then (X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) else 0)) p = 0 :=
    fun p hp ↦ RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ rfl; simp) hp
  let proj : (MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I) →ₐ[k]
      MvPolynomial (ULift.{u} (Fin 1)) k :=
    Ideal.Quotient.liftₐ I
      (aeval (R := k) (fun j : ULift.{u} (Fin 2) ↦ if j.down = 0 then X ⟨0⟩ else 0)) hproj_ker
  have hproj : proj (x ⟨0⟩) = X ⟨0⟩ := by
    simpa [proj, x] using congr($(Ideal.Quotient.liftₐ_comp I _ hproj_ker) (X ⟨0⟩))
  have hind : AlgebraicIndependent k y := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hleft : proj.comp (aeval (R := k) y) = AlgHom.id k _ :=
      MvPolynomial.algHom_ext fun ⟨i⟩ ↦ by fin_cases i; simp [y, hproj]
    exact Function.LeftInverse.injective fun p ↦ congr($hleft p)
  have hfin : (aeval (R := k) y).Finite := by
    refine TauCeti.finite_aeval_of_adjoin_eq_top hadj fun ⟨j⟩ ↦ ?_
    fin_cases j
    · simpa [y] using RingHom.isIntegralElem_map (aeval (R := k) y).toRingHom (x := X ⟨0⟩)
    · refine ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, ?_⟩
      have hx1 : x ⟨1⟩ ^ 2 = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      simp [hx1]
  rw [hπ]
  exact ⟨isClosedImmersion_homOfAlgebra_iff.mpr hadj, isFinite_homOfAlgebra_iff.mpr hfin,
    surjective_homOfAlgebra hind hfin.to_isIntegral⟩

end AlgebraicGeometry.AffineSpace.NoetherNormalizationExamples
