/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.SmoothPair.AlgebraicChart.Map

/-!
# Checks for restriction of algebraic normal crossings charts

Restrict the two-axis chart to a principal open. Both coordinates are retained, but
inverting one axis removes that factor from the boundary ideal. Inverting the boundary
equation removes the boundary entirely. Localization at zero tests the empty open.
The computations work over every field, including characteristic two.
-/

namespace TauCeti.SmoothPair

open _root_.MvPolynomial

variable (K : Type*) [Field K]

example (s : MvPolynomial (Fin 2) K) :
    ((modelAlgebraicChart K 2 2 le_rfl).localize s).n = 2 := by simp

example (s : MvPolynomial (Fin 2) K) :
    ((modelAlgebraicChart K 2 2 le_rfl).localize s).r = 2 := by simp

example (s : MvPolynomial (Fin 2) K) :
    ((modelAlgebraicChart K 2 2 le_rfl).localize s).coord (X (0 : Fin 2)) =
      algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s) (X 0) := by
  exact ((modelAlgebraicChart K 2 2 le_rfl).localize_coord_apply s (X (0 : Fin 2))).trans
    (congrArg (algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s))
      (modelAlgebraicChart_coord_apply 2 2 le_rfl (X (0 : Fin 2))))

example (s : MvPolynomial (Fin 2) K) :
    ((modelAlgebraicChart K 2 2 le_rfl).localize s).coord (X (1 : Fin 2)) =
      algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s) (X 1) := by
  exact ((modelAlgebraicChart K 2 2 le_rfl).localize_coord_apply s (X (1 : Fin 2))).trans
    (congrArg (algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s))
      (modelAlgebraicChart_coord_apply 2 2 le_rfl (X (1 : Fin 2))))

example (s : MvPolynomial (Fin 2) K) :
    ((modelAlgebraicChart K 2 2 le_rfl).localize s).generator =
      algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s) (X 0) *
        algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s) (X 1) := by
  simp [Fin.prod_univ_two]

-- The boundary on D(X₀) is the remaining axis.
example :
    let R := MvPolynomial (Fin 2) K
    let S := Localization.Away (X (0 : Fin 2) : R)
    (Ideal.span {X (0 : Fin 2) * X 1} : Ideal R).map (algebraMap R S) =
      Ideal.span {algebraMap R S (X 1)} := by
  dsimp only
  rw [Ideal.map_span, Set.image_singleton, map_mul]
  exact Ideal.span_singleton_mul_left_unit (IsLocalization.Away.algebraMap_isUnit _) _

example : (Ideal.span {∏ i : Fin 2, X (R := K) i}).map
    (algebraMap (MvPolynomial (Fin 2) K)
      (Localization.Away (modelAlgebraicChart K 2 2 le_rfl).generator)) = ⊤ :=
  (modelAlgebraicChart K 2 2 le_rfl).map_ideal_generator_eq_top

-- The actual restricted ideal, rather than just its support, is still radical.
example (s : MvPolynomial (Fin 2) K) :
    ((Ideal.span {X (0 : Fin 2) * X 1}).map
      (algebraMap (MvPolynomial (Fin 2) K) (Localization.Away s))).IsRadical := by
  simpa [Fin.prod_univ_two] using ((modelAlgebraicChart K 2 2 le_rfl).localize s).isRadical

example : ((modelAlgebraicChart K 2 2 le_rfl).localize (0 : MvPolynomial (Fin 2) K)).generator =
    0 := by
  have : Subsingleton (Localization.Away (0 : MvPolynomial (Fin 2) K)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : MvPolynomial (Fin 2) K))
      (Submonoid.mem_powers 0)
  exact Subsingleton.elim _ _

-- Empty boundary stays empty under restriction, including in positive dimension.
example (s : MvPolynomial (Fin 2) K) :
    ((modelAlgebraicChart K 2 0 (Nat.zero_le 2)).localize s).generator = 1 := by simp

end TauCeti.SmoothPair
