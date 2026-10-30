/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.SmoothPair.AlgebraicChart

/-!
# Checks for relative algebraic normal crossings charts

The identity models distinguish empty boundary, one coordinate hyperplane and two
intersecting hyperplanes. The doubled hyperplane is excluded even though it has the same
support as a reduced one. The zero ring admits the full boundary, unlike a nonzero ring.
-/

namespace TauCeti.SmoothPair

open _root_.MvPolynomial

variable (K : Type*) [Field K]

example : (modelAlgebraicChart K 0 0 le_rfl).generator = 1 := by simp

example (n : ℕ) : (modelAlgebraicChart K n 0 (Nat.zero_le n)).generator = 1 := by simp

example : (modelAlgebraicChart K 1 1 le_rfl).generator = X 0 := by simp

example : (modelAlgebraicChart K 2 2 le_rfl).generator = X 0 * X 1 := by
  simp [Fin.prod_univ_two]

example : (Ideal.span {X (0 : Fin 1)} : Ideal (MvPolynomial (Fin 1) K)).IsRadical := by
  simpa using (modelAlgebraicChart K 1 1 le_rfl).isRadical

example : (Ideal.span {X (0 : Fin 2) * X 1} : Ideal (MvPolynomial (Fin 2) K)).IsRadical := by
  simpa [Fin.prod_univ_two] using (modelAlgebraicChart K 2 2 le_rfl).isRadical

example : ¬ (Ideal.span {X (0 : Fin 2) * X 1} : Ideal (MvPolynomial (Fin 2) K)).IsPrime := by
  intro h
  have hxy : X (0 : Fin 2) * X 1 ∈ (Ideal.span {X 0 * X 1} : Ideal (MvPolynomial (Fin 2) K)) :=
    Ideal.subset_span rfl
  rcases h.mem_or_mem hxy with hx | hy
  · exact prime_X.not_isUnit ((mul_dvd_left_iff_isUnit (X_ne_zero _)).mp
      (Ideal.mem_span_singleton.mp hx))
  · exact prime_X.not_isUnit ((mul_dvd_right_iff_isUnit (X_ne_zero _)).mp
      (Ideal.mem_span_singleton.mp hy))

example : ¬ Nonempty (AlgebraicChart K (C : K →+* MvPolynomial (Fin 1) K)
    (Ideal.span {(X 0) ^ 2})) := by
  rintro ⟨c⟩
  have hrad := isRadical_iff_span_singleton.mpr c.isRadical
  have hsq := hrad.squarefree (pow_ne_zero 2 (X_ne_zero (0 : Fin 1)))
  exact prime_X.not_isUnit (hsq (X 0) (by simp [pow_two]))

example {R : Type*} [CommRing R] [Nontrivial R] (σ : K →+* R) :
    ¬ Nonempty (AlgebraicChart K σ (⊥ : Ideal R)) := not_nonempty_iff.mpr inferInstance

-- Localizing at zero gives the zero ring, where the zero and unit ideals agree.
example : Nonempty (AlgebraicChart K
    ((algebraMap (MvPolynomial (Fin 0) K) (Localization.Away (0 : MvPolynomial (Fin 0) K))).comp C)
    (⊥ : Ideal (Localization.Away (0 : MvPolynomial (Fin 0) K)))) := by
  refine ⟨{
    n := 0
    r := 0
    le := le_rfl
    coord := algebraMap _ _
    coord_comp_C := rfl
    etale := ?_
    ideal_eq := ?_ }⟩
  · exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway 0)
  · have : Subsingleton (Localization.Away (0 : MvPolynomial (Fin 0) K)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : MvPolynomial (Fin 0) K))
        (Submonoid.mem_powers 0)
    exact Subsingleton.elim _ _

end TauCeti.SmoothPair
