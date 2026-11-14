/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineSpace.NoetherNormalization
import TauCeti.Examples.RingTheory.NoetherNormalization
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
    homOfAlgebra R (MvPolynomial.X : n → MvPolynomial n R) ≫
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
    IsClosedImmersion (homOfAlgebra k x) ∧
      ∃ (d : ℕ) (_ : d ≤ Fintype.card n) (C : Matrix (ULift.{u} (Fin d)) n k),
        let π := homOfAlgebra k x ≫
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
    let π := homOfAlgebra k x ≫
      linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv)
    IsClosedImmersion (homOfAlgebra k x) ∧ IsFinite π ∧ Surjective π := by
  dsimp only
  set I : Ideal (MvPolynomial (ULift.{u} (Fin 2)) k) := Ideal.span {X ⟨1⟩ ^ 2}
  set x : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I :=
    fun j ↦ Ideal.Quotient.mk I (X j)
  let C : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 2)) k :=
    (!![1, 0] : Matrix (Fin 1) (Fin 2) k).submatrix ULift.down ULift.down
  let y : ULift.{u} (Fin 1) → MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I := fun _ ↦ x ⟨0⟩
  have hπ : homOfAlgebra k x ≫
      linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv) =
      homOfAlgebra k y := by
    rw [homOfAlgebra_linearMap, homOfAlgebra_inj]
    funext ⟨i⟩
    fin_cases i
    have hsum := Equiv.ulift.sum_comp
      fun j : Fin 2 ↦ (!![1, 0] : Matrix (Fin 1) (Fin 2) k) 0 j • x ⟨j⟩
    simpa [C, y, Fin.sum_univ_two] using hsum
  let I₀ : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 1 ^ 2}
  let y₀ : Fin 1 → MvPolynomial (Fin 2) k ⧸ I₀ := fun _ ↦ Ideal.Quotient.mk I₀ (X 0)
  let eMv : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (ULift.{u} (Fin 2)) k :=
    MvPolynomial.renameEquiv k Equiv.ulift.symm
  have hI : I = I₀.map (eMv : MvPolynomial (Fin 2) k →+* MvPolynomial (ULift.{u} (Fin 2)) k) := by
    simp [I, I₀, eMv, Ideal.map_span]
  let q : (MvPolynomial (Fin 2) k ⧸ I₀) ≃ₐ[k] (MvPolynomial (ULift.{u} (Fin 2)) k ⧸ I) :=
    Ideal.quotientEquivAlg I₀ I eMv hI
  have hqy : q.toAlgHom ∘ y₀ ∘ ULift.down = y := by
    funext ⟨i⟩
    simp [q, y₀, y, x, eMv]
  have hind : AlgebraicIndependent k y := by
    rw [← hqy]
    refine AlgebraicIndependent.of_comp q.symm.toAlgHom ?_
    have hsymm : q.symm.toAlgHom ∘ q.toAlgHom ∘ y₀ ∘ ULift.down = y₀ ∘ ULift.down := by
      funext j; simp
    rw [hsymm]
    exact (algebraicIndependent_equiv Equiv.ulift).mpr
      (TauCeti.NoetherNormalizationExamples.algebraicIndependent_mk_span_X_one_sq k)
  have hfin : (aeval (R := k) y).Finite := by
    have haeval : aeval (R := k) y =
        q.toAlgHom.comp ((aeval (R := k) y₀).comp (MvPolynomial.rename ULift.down)) := by
      ext ⟨i⟩
      simp [← hqy]
    rw [haeval]
    exact AlgHom.Finite.comp (AlgHom.Finite.of_surjective _ q.surjective)
      (AlgHom.Finite.comp
        (TauCeti.NoetherNormalizationExamples.finite_aeval_mk_span_X_one_sq k)
        (AlgHom.Finite.of_surjective _ (MvPolynomial.rename_surjective _ Equiv.ulift.surjective)))
  rw [hπ]
  exact ⟨isClosedImmersion_homOfAlgebra_iff.mpr I.adjoin_range_quotient_mk_X_eq_top,
    isFinite_homOfAlgebra_iff.mpr hfin, surjective_homOfAlgebra hind hfin.to_isIntegral⟩

end AlgebraicGeometry.AffineSpace.NoetherNormalizationExamples
