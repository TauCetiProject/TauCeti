/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level

import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Regular levels of moment maps as embedded submanifolds

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a finite-dimensional real
Lie algebra `𝔤` on a boundaryless manifold `M` with a two-form `σ`
(`TauCeti.SmoothTwoForm.IsMomentMap`), and let `c ∈ 𝔤*` be a **regular value** of `μ`: the
differential `dμ_x` (`TauCeti.SmoothTwoForm.IsMomentMap.differential`) is surjective at every
point of the level `μ⁻¹(c)`. For a symplectic form this holds when the action is locally free
along the level (`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff`), in particular
when a Lie group acts freely
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_of_stabilizer_eq_bot`).

This file makes the actual level `{x : M // μ x = c}`, with its subspace topology, into an
embedded submanifold of `M` of dimension `dim M - dim 𝔤`, and identifies its tangent spaces and
the null directions of the restricted form. This is the manifold `Z` of Marsden–Weinstein–Meyer
reduction, on which the stabilizer of `c` acts and whose quotient carries the reduced form.

* `TauCeti.SmoothTwoForm.IsMomentMap.levelChartedSpace`: the atlas of the level, modelled on
  `Fin n → ℝ` for `n = dim M - dim 𝔤`. The dual space `𝔤*` carries no norm, so the atlas is the
  regular-level atlas `TauCeti.regularLevelChartedSpace` of the coordinates `x ↦ (μ x (b i))ᵢ` of
  `μ` in the basis `Module.finBasis ℝ 𝔤`, transported to `μ⁻¹(c)` along the identity of points.
* `TauCeti.SmoothTwoForm.IsMomentMap.isManifold_level` and
  `TauCeti.SmoothTwoForm.IsMomentMap.isSmoothEmbedding_coe_level`: the level is a smooth manifold
  and its inclusion `i` is a smooth embedding.
* `TauCeti.SmoothTwoForm.IsMomentMap.range_mfderiv_coe_level`: **`T_x Z = ker dμ_x`**, and
  `TauCeti.SmoothTwoForm.IsMomentMap.range_mfderiv_coe_level_eq_orthogonal`: this is the
  `σ_x`-orthogonal `(𝔤 · x)^σ` of the orbit tangent space.
* `TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback_coe_level`: where `σ` is
  nondegenerate and the cocycle of `μ` vanishes, **the kernel of `i^* σ` at `z` consists of the
  tangent vectors that `di_z` sends into `𝔤_c · z`**, the orbit directions of the stabilizer
  `𝔤_c` of `c`. This is the kernel condition for `i^* σ` to descend to the quotient of the level
  by the stabilizer (`TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`).

For a coadjoint-equivariant moment map of a Lie group action, regularity of `c` propagates to every
point over the coadjoint orbit of `c`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_surjective_of_apply_eq`), so the
regular-value hypothesis here holds at every value in that orbit.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the level `μ⁻¹(c)` in the proof of the Marsden–Weinstein–Meyer
  theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Corollary 5.14 and
  Proposition 5.38 (regular level sets and their tangent spaces).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  {c : Module.Dual ℝ 𝔤} {n : ℕ}

/-! ### Coordinates of a moment map -/

variable (μ) in
/-- The coordinates `x ↦ (μ x (b i))ᵢ` of `μ` in the basis `b = Module.finBasis ℝ 𝔤`. -/
private def coords (x : M) : Fin (finrank ℝ 𝔤) → ℝ :=
  fun i ↦ μ x (Module.finBasis ℝ 𝔤 i)

omit [TopologicalSpace M] in
/-- A functional is determined by its coordinates in a basis. -/
private theorem coords_eq_iff {x : M} :
    coords μ x = (fun i ↦ c (Module.finBasis ℝ 𝔤 i)) ↔ μ x = c :=
  ⟨fun h ↦ (Module.finBasis ℝ 𝔤).ext fun i ↦ congrFun h i, fun h ↦ h ▸ rfl⟩

private theorem contMDiff_coords (h : σ.IsMomentMap a μ) :
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ 𝔤) → ℝ) ∞ (coords μ) :=
  contMDiff_pi_module_iff.2 fun i ↦ h.contMDiff (Module.finBasis ℝ 𝔤 i)

/-- The derivative of the coordinates of `μ` is the differential `dμ_x` read in the dual basis. -/
private theorem mfderiv_coords_apply (h : σ.IsMomentMap a μ) (x : M) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, Fin (finrank ℝ 𝔤) → ℝ) (coords μ) x v =
      fun i ↦ h.differential x v (Module.finBasis ℝ 𝔤 i) := by
  funext i
  have hd := (h.contMDiff_coords x).mdifferentiableAt (by simp)
  have := congrArg (fun L ↦ L v) (mvfderiv_apply hd i)
  simp only [ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply] at this
  rw [h.differential_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact this.symm

private theorem mfderiv_coords_eq (h : σ.IsMomentMap a μ) (x : M) :
    ⇑(mfderiv I 𝓘(ℝ, Fin (finrank ℝ 𝔤) → ℝ) (coords μ) x) =
      ⇑(Module.finBasis ℝ 𝔤).dualBasis.equivFun ∘ ⇑(h.differential x) := by
  funext v
  rw [h.mfderiv_coords_apply]
  funext i
  rw [Function.comp_apply, Basis.dualBasis_equivFun]

private theorem ker_mfderiv_coords (h : σ.IsMomentMap a μ) (x : M) :
    LinearMap.ker (mfderiv I 𝓘(ℝ, Fin (finrank ℝ 𝔤) → ℝ) (coords μ) x).toLinearMap =
      LinearMap.ker (h.differential x) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    congrFun (h.mfderiv_coords_eq x) v, Function.comp_apply]
  exact (Module.finBasis ℝ 𝔤).dualBasis.equivFun.map_eq_zero_iff

private theorem isRegularValue_coords (h : σ.IsMomentMap a μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x)) :
    IsRegularValue I 𝓘(ℝ, Fin (finrank ℝ 𝔤) → ℝ) (coords μ)
      (fun i ↦ c (Module.finBasis ℝ 𝔤 i)) := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  rw [isRegularPoint_iff, h.mfderiv_coords_eq]
  exact (EquivLike.comp_surjective _ _).2 (hreg x (coords_eq_iff.1 hx))

/-- The level of `μ` is the level of its coordinates, with the same points. -/
private def levelHomeomorph (μ : M → Module.Dual ℝ 𝔤) (c : Module.Dual ℝ 𝔤) :
    {x : M // μ x = c} ≃ₜ {x : M // coords μ x = fun i ↦ c (Module.finBasis ℝ 𝔤 i)} :=
  (Homeomorph.refl M).subtype fun _ ↦ coords_eq_iff.symm

private theorem coe_levelHomeomorph (x : {x : M // μ x = c}) :
    (levelHomeomorph μ c x : M) = x :=
  (rfl)

omit [FiniteDimensional ℝ 𝔤] in
private theorem finrank_sub_finrank_coords (hn : finrank ℝ E - finrank ℝ 𝔤 = n) :
    finrank ℝ E - finrank ℝ (Fin (finrank ℝ 𝔤) → ℝ) = n := by
  rwa [finrank_fin_fun]

/-! ### The atlas of a regular level -/

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- The regular-level atlas of the level of the coordinates of `μ`. -/
@[instance_reducible]
private def coordsChartedSpace (h : σ.IsMomentMap a μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E - finrank ℝ 𝔤 = n) :
    ChartedSpace (Fin n → ℝ) {x : M // coords μ x = fun i ↦ c (Module.finBasis ℝ 𝔤 i)} :=
  regularLevelChartedSpace (fun x _ ↦ (h.contMDiff_coords x).of_le (by simp))
    (h.isRegularValue_coords hreg) (finrank_sub_finrank_coords hn)

/-- The **atlas of a regular level** `μ⁻¹(c)` of a moment map, modelled on `Fin n → ℝ` for
`n = dim M - dim 𝔤`: the regular-level atlas of the coordinates of `μ` in the basis
`Module.finBasis ℝ 𝔤`, carried to the level `{x // μ x = c}` along the identity of points. -/
@[instance_reducible]
def levelChartedSpace (h : σ.IsMomentMap a μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E - finrank ℝ 𝔤 = n) :
    ChartedSpace (Fin n → ℝ) {x : M // μ x = c} :=
  letI := h.coordsChartedSpace hreg hn
  (levelHomeomorph μ c).pullbackChartedSpace

variable (h : σ.IsMomentMap a μ) (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (hn : finrank ℝ E - finrank ℝ 𝔤 = n)

/-- The level of `μ` is diffeomorphic to the level of its coordinates by the identity of points. -/
private def levelDiffeomorph :
    letI := h.levelChartedSpace hreg hn
    letI := h.coordsChartedSpace hreg hn
    {x : M // μ x = c} ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓘(ℝ, Fin n → ℝ)⟯
      {x : M // coords μ x = fun i ↦ c (Module.finBasis ℝ 𝔤 i)} :=
  letI := h.coordsChartedSpace hreg hn
  (levelHomeomorph μ c).pullbackDiffeomorph _ _

/-- The inclusion of the level of `μ` is the inclusion of the level of its coordinates after the
identification of the two levels. -/
private theorem coe_comp_levelDiffeomorph :
    letI := h.levelChartedSpace hreg hn
    letI := h.coordsChartedSpace hreg hn
    Subtype.val ∘ h.levelDiffeomorph hreg hn = (Subtype.val : {x : M // μ x = c} → M) := by
  let := h.levelChartedSpace hreg hn
  let := h.coordsChartedSpace hreg hn
  funext x
  rw [Function.comp_apply, levelDiffeomorph, Homeomorph.coe_pullbackDiffeomorph,
    coe_levelHomeomorph]

/-- **A regular level of a moment map is a smooth manifold** of dimension `dim M - dim 𝔤`, for the
atlas `TauCeti.SmoothTwoForm.IsMomentMap.levelChartedSpace`. -/
theorem isManifold_level :
    letI := h.levelChartedSpace hreg hn
    IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ {x : M // μ x = c} :=
  letI := h.coordsChartedSpace hreg hn
  letI := isManifold_regularLevel (n := n) (m := ∞) (by simp) (fun x _ ↦ h.contMDiff_coords x)
    (h.isRegularValue_coords hreg) (finrank_sub_finrank_coords hn)
  (levelHomeomorph μ c).pullback_isManifold _ _

/-- **A regular level of a moment map is an embedded submanifold**: for the atlas
`TauCeti.SmoothTwoForm.IsMomentMap.levelChartedSpace`, the inclusion `μ⁻¹(c) → M` is a smooth
embedding. -/
theorem isSmoothEmbedding_coe_level :
    letI := h.levelChartedSpace hreg hn
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) I ∞ (Subtype.val : {x : M // μ x = c} → M) := by
  let := h.levelChartedSpace hreg hn
  let := h.coordsChartedSpace hreg hn
  have := h.isManifold_level hreg hn
  rw [← h.coe_comp_levelDiffeomorph hreg hn]
  exact isSmoothEmbedding_comp_diffeomorph _
    (isSmoothEmbedding_coe_regularLevel (m := ∞) (by simp) (fun x _ ↦ h.contMDiff_coords x)
      (h.isRegularValue_coords hreg) (finrank_sub_finrank_coords hn))

/-- The inclusion of a regular level of a moment map is smooth. -/
theorem contMDiff_coe_level :
    letI := h.levelChartedSpace hreg hn
    ContMDiff 𝓘(ℝ, Fin n → ℝ) I ∞ (Subtype.val : {x : M // μ x = c} → M) :=
  letI := h.levelChartedSpace hreg hn
  (h.isSmoothEmbedding_coe_level hreg hn).contMDiff

/-- **The tangent space of a regular level of a moment map is the kernel of `dμ`.** At a point `z`
of a regular level `μ⁻¹(c)`, the differential of the inclusion has range `ker dμ_z`. -/
theorem range_mfderiv_coe_level (z : {x : M // μ x = c}) :
    letI := h.levelChartedSpace hreg hn
    LinearMap.range
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I (Subtype.val : {x : M // μ x = c} → M) z).toLinearMap =
      LinearMap.ker (h.differential z) := by
  let := h.levelChartedSpace hreg hn
  let := h.coordsChartedSpace hreg hn
  rw [← h.coe_comp_levelDiffeomorph hreg hn,
    Diffeomorph.range_mfderiv_comp_diffeomorph _ (by simp)]
  have := range_mfderiv_coe_regularLevel (fun x _ ↦ (h.contMDiff_coords x).of_le (by simp))
    (h.isRegularValue_coords hreg) (finrank_sub_finrank_coords hn)
    (h.levelDiffeomorph hreg hn z)
  rw [← h.ker_mfderiv_coords]
  exact this

/-- **The tangent space of a regular level is the symplectic complement of the orbit.** At a point
`z` of a regular level `μ⁻¹(c)`, the differential of the inclusion has range the `σ_z`-orthogonal
`(𝔤 · z)^σ` of the orbit tangent space. -/
theorem range_mfderiv_coe_level_eq_orthogonal (z : {x : M // μ x = c}) :
    letI := h.levelChartedSpace hreg hn
    LinearMap.range
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I (Subtype.val : {x : M // μ x = c} → M) z).toLinearMap =
      (σ.bilinFormAt z).orthogonal (a.orbitTangent z) := by
  rw [h.range_mfderiv_coe_level hreg hn, h.ker_differential]

/-- **The null directions of the form restricted to a regular level.** At a point `z` of a regular
level `μ⁻¹(c)` where `σ` is nondegenerate and the cocycle of `μ` vanishes, the kernel of the
pulled-back form `i^* σ` consists of the tangent vectors that the differential of the inclusion
`i` sends into the orbit tangent space `𝔤_c · z` of the stabilizer `𝔤_c` of `c`. -/
theorem ker_bilinFormAt_mpullback_coe_level (z : {x : M // μ x = c})
    (hσz : (σ.bilinFormAt z).Nondegenerate) (hcz : σ.momentCocycle a μ z = 0) :
    letI := h.levelChartedSpace hreg hn
    letI := h.isManifold_level hreg hn
    LinearMap.ker ((SmoothForm.mpullback Subtype.val (h.contMDiff_coe_level hreg hn) σ).bilinFormAt
        z) =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval z)).comap
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I (Subtype.val : {x : M // μ x = c} → M) z).toLinearMap := by
  let := h.levelChartedSpace hreg hn
  have := h.isManifold_level hreg hn
  rw [h.ker_bilinFormAt_mpullback (h.contMDiff_coe_level hreg hn) hσz hcz
    (h.range_mfderiv_coe_level hreg hn z), z.2]

end IsMomentMap

end SmoothTwoForm

end TauCeti
