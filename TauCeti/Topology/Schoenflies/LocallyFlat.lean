/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Brown
public import TauCeti.Topology.Schoenflies.Standard
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The generalized Schoenflies theorem for locally flat spheres

Combining M. Brown's bicollaring theorem (`TauCeti.IsLocallyFlat.isBicollared_of_finrank_eq`) with
his generalized Schoenflies theorem
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`, valid in every
dimension `m ≥ 0` and for arbitrary real normed spaces) yields the **locally flat generalized
Schoenflies theorem** in every dimension `m ≥ 0`: let `σ : S(E) → S(F)` be a codimension-one locally
flat embedding between unit spheres of real normed spaces (`finrank ℝ F = finrank ℝ E + 1`). Then
the complement of `range σ` in `S(F)` has two connected components, and the closure of each
component is homeomorphic to the closed unit ball of `E` by a homeomorphism inverting `σ` on
`range σ` and sending `range σ` onto the boundary sphere `S(E)`. Equivalently, `σ` extends across
each side to a closed embedding `closedBall (0 : E) 1 → S(F)` carrying `ball (0 : E) 1` onto that
complementary component. When `F` is a real inner product space,
`TauCeti.IsBicollar.exists_homeomorph_sphere_eq_equatorInclusion` yields an ambient
self-homeomorphism of `S(F)` straightening `σ` to `TauCeti.equatorInclusion`.

Finally, `TauCeti.isBicollared_equatorInclusion` and `TauCeti.isLocallyFlat_equatorInclusion` show
that the standard equatorial inclusion `S((ℝ ∙ p)ᗮ) → S(F)` is itself bicollared and locally flat,
using `TauCeti.latitudeHomeomorphComplPair` as an explicit global bicollar onto `S(F) \ {p, -p}`.

## Main results

* `TauCeti.isBicollared_equatorInclusion` and `TauCeti.isLocallyFlat_equatorInclusion`: the
  equatorial sphere around a unit vector `p` in a real inner product space is bicollared and
  locally flat.
* `TauCeti.IsLocallyFlat.closure_connectedComponentIn_compl_range` and
  `TauCeti.IsLocallyFlat.frontier_connectedComponentIn_compl_range`: closure and frontier of each
  complementary domain of a locally flat sphere in every dimension `m ≥ 0`.
* `TauCeti.IsLocallyFlat.exists_homeomorph_closure_connectedComponentIn_compl_range`,
  `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_closedBall`, and
  `TauCeti.IsLocallyFlat.exists_homeomorph_sphere_eq_equatorInclusion`: the locally flat
  generalized Schoenflies theorem, its closed-ball extension form, and ambient equatorial
  straightening in every dimension `m ≥ 0`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

/-! ### Equatorial spheres are bicollared and locally flat -/

section Equator

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The equatorial inclusion is globally bicollared.** In any real inner product space `F`, the
equatorial sphere `S((ℝ ∙ p)ᗮ) → S(F)` around a unit vector `p` admits a global bicollar. -/
theorem isBicollared_equatorInclusion (p : sphere (0 : F) 1) :
    IsBicollared (equatorInclusion (r := 1) (p : F)) := by
  have hball : ball (0 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
    ext t
    simp [abs_lt]
  let ρ : ℝ ≃ₜ Ioo (-1 : ℝ) 1 := Homeomorph.unitBall.trans (Homeomorph.setCongr hball)
  have hopen : IsOpen (({p, -p} : Set (sphere (0 : F) 1))ᶜ) :=
    ((Set.finite_singleton (-p)).insert p).isClosed.isOpen_compl
  let e := ((Homeomorph.refl _).prodCongr ρ).trans (latitudeHomeomorphComplPair p)
  refine isBicollared_iff.2 ⟨Subtype.val ∘ e,
    hopen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding, fun u ↦ ?_⟩
  have hρ0 : (ρ 0 : ℝ) = 0 := Homeomorph.coe_unitBall_apply_zero
  have he : ((Subtype.val ∘ e) (u, 0) : F) = (latitude p u (ρ 0) : F) := by simp [e]
  apply Subtype.ext
  rw [he, hρ0, coe_latitude_of_mem p u ⟨by norm_num, by norm_num⟩]
  simp [coe_equatorInclusion_apply]

/-- **The equatorial inclusion is locally flat.** When the equatorial sphere `S((ℝ ∙ p)ᗮ)` is
charted on a model space `H`, `TauCeti.equatorInclusion (p : F)` is locally flat with
one-dimensional complementary model `ℝ`. -/
theorem isLocallyFlat_equatorInclusion (p : sphere (0 : F) 1) {H : Type*} [TopologicalSpace H]
    [ChartedSpace H (sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)] :
    IsLocallyFlat H ℝ (equatorInclusion (r := 1) (p : F)) :=
  (isBicollared_equatorInclusion p).isLocallyFlat

end Equator

/-! ### The locally flat generalized Schoenflies theorem -/

namespace IsLocallyFlat

variable {H E F : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- **The closure of a complementary domain of a locally flat sphere (`m ≥ 0`).** -/
theorem closure_connectedComponentIn_compl_range (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.closure_connectedComponentIn_compl_range hEF hy

/-- **The frontier of a complementary domain of a locally flat sphere (`m ≥ 0`).** -/
theorem frontier_connectedComponentIn_compl_range (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.frontier_connectedComponentIn_compl_range hEF hy

/-- **The locally flat generalized Schoenflies theorem (`m ≥ 0`).** Every codimension-one locally
flat sphere `σ : S(E) → S(F)` (`finrank ℝ F = finrank ℝ E + 1`) bounds a closed `m`-ball on each
side: for every `y ∉ range σ`, `closure (connectedComponentIn (range σ)ᶜ y)` is homeomorphic to
`closedBall (0 : E) 1` by a homeomorphism inverting `σ` on `range σ` and sending `range σ` onto
`sphere (0 : E) 1`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hy

/-- **Closed-ball extension form of the locally flat generalized Schoenflies theorem (`m ≥ 0`).**
For every `y ∉ range σ`, `σ` extends to a closed embedding `g : closedBall (0 : E) 1 → S(F)` with
range `closure (connectedComponentIn (range σ)ᶜ y)` carrying `ball (0 : E) 1` onto
`connectedComponentIn (range σ)ᶜ y`. -/
theorem exists_isClosedEmbedding_closedBall (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ g : closedBall (0 : E) 1 → sphere (0 : F) 1, IsClosedEmbedding g ∧
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = σ x) ∧
      range g = closure (connectedComponentIn (range σ)ᶜ y) ∧
      (∀ z : closedBall (0 : E) 1,
        (z : E) ∈ ball (0 : E) 1 ↔ g z ∈ connectedComponentIn (range σ)ᶜ y) :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.exists_isClosedEmbedding_closedBall hEF hy

/-- **Ambient equatorial straightening for locally flat spheres (`m ≥ 0`).** In a real inner
product space `F` with `finrank ℝ F = finrank ℝ E + 1`, every locally flat sphere
`σ : S(E) → S(F)` is carried to the equator `equatorInclusion (p : F) ∘ e` by an ambient
self-homeomorphism of `S(F)` sending `closure (connectedComponentIn (range σ)ᶜ y)` onto the closed
hemisphere `{z | 0 ≤ ⟪z, p⟫}`. -/
theorem exists_homeomorph_sphere_eq_equatorInclusion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {σ : sphere (0 : E) 1 → sphere (0 : F) 1} (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1)
    (p : sphere (0 : F) 1) (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ z, 0 ≤ ⟪(h z : F), (p : F)⟫ ↔
        z ∈ closure (connectedComponentIn (range σ)ᶜ y)) ∧
      (∀ z, ⟪(h z : F), (p : F)⟫ < 0 ↔
        z ∉ closure (connectedComponentIn (range σ)ᶜ y)) :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.exists_homeomorph_sphere_eq_equatorInclusion hEF p e hy

end IsLocallyFlat

end TauCeti
