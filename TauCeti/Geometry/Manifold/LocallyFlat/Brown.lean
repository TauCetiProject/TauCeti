/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.LocallyFlat.Finite
public import TauCeti.Geometry.Manifold.LocallyFlat.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Brown's bicollaring theorem for spheres

Every locally flat embedding `Sⁿ → Sⁿ⁺¹` has a global bicollar, in every dimension `n`, and more
generally so does every injective locally bicollared map from the unit sphere of a real normed
space `E` into the unit sphere of a real normed space `F` of dimension `dim E + 1`. For source
spheres of positive dimension (`dim E ≥ 2`), Jordan–Brouwer separation supplies the disconnected
complement needed by the bicollaring theorem for separating spheres. When `dim E ≤ 1`, the source
sphere is empty or a pair of points, so finite bicollaring applies directly.

The global product neighbourhood is the structural input to the generalized Schoenflies and
annulus theorems; local flatness is essential, since a wild embedded sphere need not have a
bicollar.

## Main results

* `TauCeti.IsLocallyBicollared.isBicollared_of_finrank_eq`: an injective locally bicollared map
  `S(E) → S(F)` with `finrank ℝ F = finrank ℝ E + 1` is globally bicollared.
* `TauCeti.IsLocallyFlat.isBicollared_of_finrank_eq`: every codimension-one locally flat embedding
  between unit spheres of real normed spaces (`finrank ℝ F = finrank ℝ E + 1`) is globally
  bicollared.
* `TauCeti.brownBicollaring`: `BrownBicollaring n` holds in every dimension `n`.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75
  (1962), 331–341.
* A. Hatcher, *Algebraic Topology*, Section 2.B, Corollary 2B.2 (Jordan–Brouwer separation).
-/

public section

open Function Metric Module Set Topology
open scoped EuclideanSpace

namespace TauCeti

/-- **Brown's bicollaring theorem for normed-space spheres (local-bicollar form).** Let `σ` be an
injective locally bicollared map from the unit sphere of a real normed space `E` into the unit
sphere of a real normed space `F` with `finrank ℝ F = finrank ℝ E + 1`. Then `σ` admits a global
bicollar, including when `finrank ℝ E` is `0` or `1`. -/
theorem IsLocallyBicollared.isBicollared_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
    (h : IsLocallyBicollared σ) (hEF : finrank ℝ F = finrank ℝ E + 1) (hinj : Injective σ) :
    IsBicollared σ := by
  have : FiniteDimensional ℝ E := finiteDimensional_of_injective_sphere hEF hinj
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  rcases le_or_gt (finrank ℝ E) 1 with hE | hE
  · -- For `dim E ≤ 1`, the unit sphere of `E` is either empty or two points, hence finite.
    have : Finite (sphere (0 : E) 1) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hE with h0 | h1
      · have := finrank_zero_iff.1 h0
        have := isEmpty_coe_sort.2 (sphere_eq_empty_of_subsingleton (x := (0 : E)) one_ne_zero)
        infer_instance
      · exact finite_sphere_of_finrank_eq_one h1 0 1
    exact h.isBicollared_of_finite hinj
  · -- For `dim E ≥ 2`, both spheres are connected and locally connected, and `σ` separates `S(F)`.
    have : ConnectedSpace (sphere (0 : E) 1) := isConnected_iff_connectedSpace.1 <|
      isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast hE) 0 zero_le_one
    have : ConnectedSpace (sphere (0 : F) 1) := isConnected_iff_connectedSpace.1 <|
      isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
        0 zero_le_one
    have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E))) = (finrank ℝ E - 1) + 1) :=
      ⟨by simp; omega⟩
    have := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)
    have : LocallyConnectedSpace (sphere (0 : E) 1) :=
      (sphereHomeomorphOfFinrankEq
        (E := E) (F := EuclideanSpace ℝ (Fin (finrank ℝ E))) (by simp)).locallyConnectedSpace
    exact h.isBicollared_of_not_isPreconnected_compl_range hinj
      (not_isPreconnected_compl_range_sphere hEF h.continuous hinj)

/-- **Brown's bicollaring theorem for normed-space spheres.** Every codimension-one locally flat
embedding `σ : S(E) → S(F)` between unit spheres of real normed spaces with
`finrank ℝ F = finrank ℝ E + 1` is globally bicollared, for any tangential model `H`. -/
theorem IsLocallyFlat.isBicollared_of_finrank_eq
    {H E F : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
    (hf : IsLocallyFlat H ℝ σ) (hEF : finrank ℝ F = finrank ℝ E + 1) :
    IsBicollared σ :=
  hf.isLocallyBicollared.isBicollared_of_finrank_eq hEF hf.injective

/-- **Brown's bicollaring theorem:** every locally flat embedding of the standard `n`-sphere
in the standard `(n + 1)`-sphere is globally bicollared, including `n = 0`. -/
theorem brownBicollaring (n : ℕ) : BrownBicollaring n :=
  brownBicollaring_iff.2 fun _ hf ↦ hf.isBicollared_of_finrank_eq (by simp)

end TauCeti
