/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.RealProjective
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Surface
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Torus
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus

/-!
# The topological genus

The **topological genus** of a space `X` of finite CW type is
`genus X = (2 - χ(X)) / 2`, truncated at `0`, where `χ` is Tau Ceti's finite-CW Euler
characteristic `TauCeti.eulerChar`. This is the genus of a compact connected Riemann surface,
read off its underlying topological surface, hence the namespace `TauCeti.RiemannSurface`; it
needs only the Euler characteristic, so it lives here, below the complex-analytic theory. It is the
same convention as `TauCeti.RibbonGraph.genus` and `TauCeti.PermutationTriple.genus`. It is defined
from the Euler characteristic, not as the analytic genus `dim H¹(X, 𝒪)`; the two agree on compact
Riemann surfaces, but that is not proved here.

The genus is defined on every space of finite CW type, so it returns a value also where it has no
geometric meaning; the identity `χ(X) = 2 - 2 · genus X` holds exactly when `χ(X) ≤ 2` and
`χ(X)` is even (`TauCeti.RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff`). For a closed
connected homologically oriented surface `M`, the native computation `χ(M) = 2 - b₁(M)` gives
`χ(M) ≤ 2` and identifies `genus M` with half the first rational Betti number, rounded down
(`TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`); so `χ(M) = 2 - 2 · genus M` holds if and
only if `b₁(M)` is even
(`TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank`). Evenness
of `b₁` itself needs the nondegenerate alternating intersection pairing from Poincaré duality, and
is not asserted here.

## Main definitions

* `TauCeti.RiemannSurface.genus`: the topological genus `((2 - χ(X)) / 2).toNat`.

## Main results

* `TauCeti.RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff`: `χ = 2 - 2 · genus` holds if
  and only if `χ ≤ 2` and `χ` is even.
* `TauCeti.RiemannSurface.genus_eq_of_eulerChar_eq`: a space with `χ = 2 - 2g` has genus `g`.
* `ContinuousMap.HomotopyEquiv.genus_eq`: the genus is a homotopy invariant.
* `TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`: on a closed connected homologically
  oriented surface, `genus` agrees with `TauCeti.surfaceGenus`, half the first Betti number.
* `TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank`: on such a
  surface, `χ = 2 - 2 · genus` holds if and only if the first Betti number is even.

## Checks

* `TauCeti.RiemannSurface.genus_torus`: the torus `∀ i : Fin 2, AddCircle (p i)` has `χ = 0` and
  genus `1`; the unhalved `2 - χ` would give `2`.
* `TauCeti.RiemannSurface.genus_eq_two_of_eulerChar_eq_neg_two`: `χ = -2` gives genus `2`, while
  `(-χ / 2).toNat` would give `1`.
* `TauCeti.RiemannSurface.genus_realProjectiveSpace_two` and
  `TauCeti.RiemannSurface.eulerChar_realProjectiveSpace_two_ne_two_sub_two_mul_genus`: the real
  projective plane has `χ = 1` and genus `0`, and `χ = 2 - 2 · genus` fails, since `χ(RP²) = 1` is
  odd.

The Riemann sphere and the level-one modular curve have genus `0`: see
`TauCeti.RiemannSurface.genus_onePoint_complex` and
`TauCeti.ModularGroup.genus_compactifiedQuotient`.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module

universe u

namespace TauCeti

namespace RiemannSurface

section Genus

variable {X : Type u} [TopologicalSpace X] [FiniteCWType X]

variable (X) in
/-- The **topological genus** of a space of finite CW type: `(2 - χ(X)) / 2`, truncated at `0`,
where `χ` is the finite-CW Euler characteristic `TauCeti.eulerChar`. For a compact connected
Riemann surface this is its genus, with `χ(X) = 2 - 2 · genus X`; on other spaces the value is a
truncation and need not satisfy that identity
(`TauCeti.RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff`). -/
def genus : ℕ :=
  ((2 - eulerChar X) / 2).toNat

variable (X) in
/-- The defining formula for the topological genus. -/
theorem genus_def : genus X = ((2 - eulerChar X) / 2).toNat :=
  (rfl)

/-- **The Euler number in terms of the genus.** `χ(X) = 2 - 2 · genus X` holds if and only if
`χ(X) ≤ 2` and `χ(X)` is even. -/
theorem eulerChar_eq_two_sub_two_mul_genus_iff :
    eulerChar X = 2 - 2 * genus X ↔ eulerChar X ≤ 2 ∧ Even (eulerChar X) := by
  rw [genus_def]
  constructor
  · intro h
    refine ⟨by omega, ⟨1 - ((2 - eulerChar X) / 2).toNat, by omega⟩⟩
  · rintro ⟨hle, r, hr⟩
    omega

/-- A space of finite CW type with `χ(X) = 2 - 2g` has genus `g`. -/
theorem genus_eq_of_eulerChar_eq {g : ℕ} (h : eulerChar X = 2 - 2 * g) : genus X = g := by
  rw [genus_def, h]
  omega

/-- **Homotopy invariance of the genus.** Homotopy equivalent spaces of finite CW type have the
same genus. -/
theorem _root_.ContinuousMap.HomotopyEquiv.genus_eq {Y : Type u} [TopologicalSpace Y]
    [FiniteCWType Y] (e : ContinuousMap.HomotopyEquiv X Y) : genus X = genus Y := by
  rw [genus_def, genus_def, e.eulerChar_eq]

end Genus

section Checks

/-- **The torus has genus `1`.** The torus `∀ i : Fin 2, AddCircle (p i)`, a product of two circles
and the underlying surface of a complex torus `ℂ/Λ`, has Euler characteristic `0`, so its genus
is `1`; without the halving, `2 - χ` would give `2`. -/
@[simp]
theorem genus_torus (p : Fin 2 → ℝ) [∀ i, NeZero (p i)] :
    genus (∀ i, AddCircle (p i)) = 1 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_torus]; norm_num)

/-- **A surface with `χ = -2` has genus `2`.** The alternative convention `(-χ / 2).toNat`, which
agrees on the sphere, would give `1` here. -/
theorem genus_eq_two_of_eulerChar_eq_neg_two {X : Type u} [TopologicalSpace X] [FiniteCWType X]
    (h : eulerChar X = -2) : genus X = 2 ∧ ((-eulerChar X) / 2).toNat = 1 := by
  refine ⟨genus_eq_of_eulerChar_eq (by rw [h]; norm_num), ?_⟩
  rw [h]
  rfl

/-- **The real projective plane has genus `0`**: `χ(RP²) = 1`, and `(2 - 1) / 2` rounds down to
`0`. -/
@[simp]
theorem genus_realProjectiveSpace_two : genus (RealProjectiveSpace 2) = 0 := by
  rw [genus_def, eulerChar_realProjectiveSpace]
  decide

/-- **`χ = 2 - 2 · genus` fails on the real projective plane**: `χ(RP²) = 1` while `genus RP² = 0`.
The identity fails because `χ(RP²) = 1` is odd; see `eulerChar_eq_two_sub_two_mul_genus_iff`. -/
theorem eulerChar_realProjectiveSpace_two_ne_two_sub_two_mul_genus :
    eulerChar (RealProjectiveSpace 2) ≠ 2 - 2 * genus (RealProjectiveSpace 2) := by
  rw [eulerChar_realProjectiveSpace, genus_realProjectiveSpace_two]
  decide

end Checks

end RiemannSurface

namespace HomologicalOrientation

open RiemannSurface

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [FiniteCWType M] (o : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2)

include o hn

/-- **The topological genus of a closed oriented surface is half its first Betti number.** On a
compact connected homologically oriented surface of finite CW type, `genus M` equals
`TauCeti.surfaceGenus M`, the dimension of `H₁(M; ℚ)` halved and rounded down. -/
theorem genus_eq_surfaceGenus : genus M = surfaceGenus M := by
  rw [genus_def, o.eulerChar_eq_two_sub_finrank_singularHomology_one hn, surfaceGenus_def]
  omega

/-- **The Euler number of a closed oriented surface.** On a compact connected homologically
oriented surface of finite CW type, `χ(M) = 2 - 2 · genus M` holds if and only if the first
rational Betti number is even. Evenness itself follows from Poincaré duality and is not asserted
here. -/
theorem eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank :
    eulerChar M = 2 - 2 * genus M ↔ Even (finrank ℚ
      (((singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj
        (TopCat.of M))) := by
  rw [o.genus_eq_surfaceGenus hn, o.eulerChar_eq_two_sub_finrank_singularHomology_one hn,
    surfaceGenus_def, Nat.even_iff]
  omega

end HomologicalOrientation

end TauCeti
