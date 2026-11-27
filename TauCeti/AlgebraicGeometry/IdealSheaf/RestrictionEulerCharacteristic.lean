/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Euler characteristics of restriction to a closed subscheme

Tensoring the ideal sequence of a closed subscheme `D = V(I)` with a vector bundle
`E` gives `0 → E ⊗ I → E → i_* (E|D) → 0`. If `Hⁿ(D, E|D)` vanishes, its
connecting map is zero. Thus the degree-`n + 1` Euler characteristics on the ambient
scheme differ by the degree-`n` Euler characteristic of the restriction.

## References

* [The Stacks Project, Lemma 33.45.8, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU),
  the twisted ideal sequence used to compare intersection numbers with restriction.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry (FiniteLocallyFreeSheaf)

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (I : X.IdealSheafData)

/-- The difference of Euler characteristics of a vector bundle and its twist by an
ideal sheaf computes the Euler characteristic on the closed subscheme, provided the
cohomology of the restriction vanishes at the truncation degree. -/
theorem eulerCharBelow_sub_tensor_sheaf (E : FiniteLocallyFreeSheaf X) (n : ℕ)
    (hEI : ∀ i < n + 1, 0 < i → FiniteDimensional k (Cohomology (E.obj ⊗ I.sheaf) i))
    (hE : ∀ i < n + 1, FiniteDimensional k (Cohomology E.obj i))
    (hvan : Subsingleton
      (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj n)) :
    eulerCharBelow k X E.obj (n + 1) - eulerCharBelow k X (E.obj ⊗ I.sheaf) (n + 1) =
      eulerCharBelow k I.subscheme
        ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj n := by
  have hExact := I.shortExact_tensor_toPushforwardSubscheme E.obj
  have hvan' := (I.subsingleton_cohomology_tensor_pushforwardSubscheme_iff E n).mpr hvan
  have hδ : cohomologyδBaseLinear k X hExact n (n + 1) rfl = 0 :=
    LinearMap.ext fun x ↦ by rw [hvan'.elim x 0, map_zero, LinearMap.zero_apply]
  -- Display the terms of the mapped sequence for the right unitor and projection formula.
  have h : eulerCharBelow k X (E.obj ⊗ 𝟙_ X.Modules) (n + 1) =
      eulerCharBelow k X (E.obj ⊗ I.sheaf) (n + 1) +
        eulerCharBelow k X (E.obj ⊗ I.pushforwardSubscheme) (n + 1) :=
    eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hExact n hEI
      (fun i hi ↦ (finiteDimensional_cohomology_congr k (ρ_ E.obj) i).mpr (hE i hi)) hδ
  rw [eulerCharBelow_congr k (ρ_ E.obj) (n + 1),
    I.eulerCharBelow_tensor_pushforwardSubscheme k E (n + 1)] at h
  rw [eulerCharBelow_succ k ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj n,
    Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero, add_zero] at h
  omega

end AlgebraicGeometry.Scheme.IdealSheafData
