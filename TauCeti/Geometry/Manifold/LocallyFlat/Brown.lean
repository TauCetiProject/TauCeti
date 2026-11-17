/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.LocallyFlat.Finite
public import TauCeti.Geometry.Manifold.LocallyFlat.Sphere
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Manifold.CoordinateBall

/-!
# Brown's bicollaring theorem and dimension forcing for spheres

Every locally flat embedding `Sⁿ → Sⁿ⁺¹` has a global bicollar, in every dimension `n`, and more
generally so does every injective locally bicollared map from the unit sphere of a real normed
space `E` into the unit sphere of a real normed space `F` of dimension `dim E + 1`. For source
spheres of positive dimension (`dim E ≥ 2`), Jordan–Brouwer separation supplies the disconnected
complement needed by the bicollaring theorem for separating spheres. When `dim E ≤ 1`, the source
sphere is empty or a pair of points, so finite bicollaring applies directly.

In addition, a local bicollar of `TopCat.sphere n` into a real normed space `E` or into the unit
sphere `S(F)` of a real normed space `F` already forces `E` (resp. `F`) to be finite-dimensional
of dimension `n + 1` (resp. `n + 2`), by Riesz's theorem
(`FiniteDimensional.of_totallyBounded_nhds`) and Brouwer's invariance of dimension
(`Topology.IsOpenEmbedding.finrank_eq`).

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
* `TauCeti.IsLocallyBicollared.finiteDimensional_of_topCatSphere`,
  `TauCeti.IsLocallyBicollared.finrank_eq_of_topCatSphere`,
  `TauCeti.IsLocallyBicollared.finiteDimensional_of_topCatSphere_sphere`, and
  `TauCeti.IsLocallyBicollared.finrank_eq_of_topCatSphere_sphere`: a locally bicollared `n`-sphere
  in `E` (resp. `S(F)`) forces `FiniteDimensional ℝ E` and `finrank ℝ E = n + 1` (resp.
  `FiniteDimensional ℝ F` and `finrank ℝ F = n + 2`).

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

/-! ### Dimension forcing from local bicollars of spheres -/

section Dimension

universe u v

/-- Any locally bicollared map out of `TopCat.sphere n` yields an open embedding of
`EuclideanSpace ℝ (Fin n) × ℝ` into the target. -/
private lemma exists_isOpenEmbedding_prod_of_topCatSphere {Y : Type v} [TopologicalSpace Y]
    {n : ℕ} {f : TopCat.sphere.{u} n → Y} (hf : IsLocallyBicollared f) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) × ℝ → Y, IsOpenEmbedding ψ := by
  let V := EuclideanSpace ℝ (Fin (n + 1))
  have : Fact (finrank ℝ V = n + 1) := ⟨by simp [V]⟩
  let eS : TopCat.sphere.{u} n ≃ₜ sphere (0 : V) 1 := Homeomorph.ulift
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : V) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨U, hU, hx₀, hbic⟩ := isLocallyBicollared_iff.1 (hf.comp_homeomorph eS.symm) x₀
  obtain ⟨b, hb⟩ := isBicollared_iff.1 hbic
  obtain ⟨κ, hκ, -⟩ :=
    hU.exists_isOpenEmbedding_apply_zero_eq (E := EuclideanSpace ℝ (Fin n)) hx₀
  exact ⟨b ∘ Prod.map κ id, hb.isOpenEmbedding.comp (hκ.prodMap IsOpenEmbedding.id)⟩

/-- Any locally bicollared map from `TopCat.sphere n` into `sphere (0 : F) 1` yields an open
embedding of `(EuclideanSpace ℝ (Fin n) × ℝ) × ℝ` into `F`. -/
private lemma exists_isOpenEmbedding_prod_of_topCatSphere_sphere
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {f : TopCat.sphere.{u} n → sphere (0 : F) 1} (hf : IsLocallyBicollared f) :
    ∃ Φ : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ → F, IsOpenEmbedding Φ := by
  obtain ⟨ψ, hψ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere hf
  let ρ₀ := OpenPartialHomeomorph.univBall (1 : ℝ) (1 / 2)
  have hρ_pos (t : ℝ) : 0 < ρ₀ t := by
    have ht : dist (ρ₀ t) 1 < 1 / 2 := mem_ball.1 <|
      OpenPartialHomeomorph.univBall_target (1 : ℝ) (by positivity : (0 : ℝ) < 1 / 2) ▸
        ρ₀.map_source (by simp [ρ₀])
    linarith [(abs_lt.1 (Real.dist_eq (ρ₀ t) 1 ▸ ht)).1]
  let ρ : ℝ → Ioi (0 : ℝ) := fun t ↦ ⟨ρ₀ t, hρ_pos t⟩
  have hρ : IsOpenEmbedding ρ :=
    (isOpen_Ioi.isOpenEmbedding_subtypeVal.of_comp_iff ρ).1
      (ρ₀.isOpenEmbedding (OpenPartialHomeomorph.univBall_source _ _))
  exact ⟨Subtype.val ∘ (homeomorphUnitSphereProd F).symm ∘ Prod.map ψ ρ,
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp <|
      (homeomorphUnitSphereProd F).symm.isOpenEmbedding.comp (hψ.prodMap hρ)⟩

/-- **A locally bicollared `n`-sphere in a real normed space `E` forces `E` to be
finite-dimensional.** -/
theorem IsLocallyBicollared.finiteDimensional_of_topCatSphere
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {f : TopCat.sphere.{u} n → E} (hf : IsLocallyBicollared f) :
    FiniteDimensional ℝ E := by
  obtain ⟨ψ, hψ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere hf
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : EuclideanSpace ℝ (Fin n) × ℝ)
  exact .of_totallyBounded_nhds (𝕜 := ℝ) (hψ.image_mem_nhds.2 hK0)
    (hK.image hψ.continuous).totallyBounded

/-- **A locally bicollared `n`-sphere in a real normed space `E` forces `dim E = n + 1`.** -/
theorem IsLocallyBicollared.finrank_eq_of_topCatSphere
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {f : TopCat.sphere.{u} n → E} (hf : IsLocallyBicollared f) :
    finrank ℝ E = n + 1 := by
  have := hf.finiteDimensional_of_topCatSphere
  obtain ⟨_, hψ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere hf
  exact (hψ.finrank_eq IsOpenEmbedding.id).trans (by simp [Module.finrank_prod])

/-- **A locally bicollared `n`-sphere in `S(F)` forces `F` to be finite-dimensional.** -/
theorem IsLocallyBicollared.finiteDimensional_of_topCatSphere_sphere
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {f : TopCat.sphere.{u} n → sphere (0 : F) 1} (hf : IsLocallyBicollared f) :
    FiniteDimensional ℝ F := by
  obtain ⟨Φ, hΦ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere_sphere hf
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ)
  exact .of_totallyBounded_nhds (𝕜 := ℝ) (hΦ.image_mem_nhds.2 hK0)
    (hK.image hΦ.continuous).totallyBounded

/-- **A locally bicollared `n`-sphere in `S(F)` forces `dim F = n + 2`.** -/
theorem IsLocallyBicollared.finrank_eq_of_topCatSphere_sphere
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {f : TopCat.sphere.{u} n → sphere (0 : F) 1} (hf : IsLocallyBicollared f) :
    finrank ℝ F = n + 2 := by
  have := hf.finiteDimensional_of_topCatSphere_sphere
  obtain ⟨_, hΦ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere_sphere hf
  exact (hΦ.finrank_eq IsOpenEmbedding.id).trans (by simp [Module.finrank_prod])

end Dimension

end TauCeti
