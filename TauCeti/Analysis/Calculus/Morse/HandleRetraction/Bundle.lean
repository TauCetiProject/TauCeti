/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Analysis.Calculus.Morse.HandleRetraction.Basic
import TauCeti.Topology.FiberBundle.Prod
import TauCeti.Topology.VectorBundle.Smul

/-!
# Milnor's handle retraction in a sum of vector bundles

Near a nondegenerate critical submanifold `C` of index `λ` with critical value `c`, a Morse–Bott
function has, after the Morse–Bott lemma, the form `f = c - ‖u‖² + ‖v‖²` on a neighbourhood of the
zero section of its normal bundle `ν = ν⁻ ⊕ ν⁺`, where `u` runs over the fibre of the negative
normal bundle `ν⁻`, of rank `λ`, and `v` over the fibre of the positive one `ν⁺`. Passing the
critical level attaches the disc bundle `{‖u‖² ≤ ε, v = 0}` of `ν⁻` to the lower sublevel
`{f ≤ c - ε}` along its sphere bundle. For an isolated critical point the base is a point and this
is the attachment of a single `λ`-cell.

This file carries out Milnor's deformation for this quadratic model fibrewise. Let `Eᵤ` and `Eₛ`
be bundles over a common base `B` with normed fibres, whose fibre norms are continuous on the
total spaces, and with `Eₛ` a topological vector bundle. In the Whitney sum `Eᵤ ×ᵇ Eₛ`, the lower
sublevel together with the negative disc bundle is `TauCeti.bundleQuadraticSublevelUnionCell`,
the vectors `(u, v)` whose components lie in `TauCeti.quadraticSublevelUnionCell ε`: those with
`-‖u‖² + ‖v‖² ≤ -ε`, or with `‖u‖² ≤ ε` and `v = 0`. It is closed
(`TauCeti.isClosed_bundleQuadraticSublevelUnionCell`).

In each fibre the deformation is `TauCeti.quadraticHandleDeformation`: at time `t` it keeps `u` and
multiplies `v` by `(1 - t) min 1 (√(‖u‖² - ε) / ‖v‖) + t`. This scalar depends only on the two
fibre norms, so the fibrewise maps need no trivialization of the bundles to be defined. The scalar
jumps where `v = 0` and `‖u‖² ≥ ε`, but it lies in `[0, 1]`, so the rescaled vector `v` still
depends continuously on the point (`Continuous.smul_totalSpace_of_norm_le`). This gives the
retraction `TauCeti.bundleQuadraticHandleRetraction` of the total space onto
`TauCeti.bundleQuadraticSublevelUnionCell`, and the homotopy
`TauCeti.bundleQuadraticHandleDeformation` from it to the identity which fixes that set and the
base point throughout. Since the deformation only shrinks `v`, it preserves every set whose fibres
over each `u` are star-shaped about the origin, and for every such set `X` the intersection
`X ∩ bundleQuadraticSublevelUnionCell` is a strong deformation retract of `X`
(`TauCeti.exists_inter_bundleQuadraticSublevelUnionCell_deformation`).

## Main declarations

* `TauCeti.bundleQuadraticSublevelUnionCell`: the lower quadratic sublevel of the Whitney sum
  together with the negative disc bundle of radius `√ε`.
* `TauCeti.bundleQuadraticHandleRetraction`: the fibrewise retraction onto it.
* `TauCeti.bundleQuadraticHandleDeformation`: the fibrewise deformation from the retraction to the
  identity, relative to `TauCeti.bundleQuadraticSublevelUnionCell`.
* `TauCeti.exists_inter_bundleQuadraticSublevelUnionCell_deformation`: the strong deformation
  retraction of a set with star-shaped fibres onto its intersection with
  `TauCeti.bundleQuadraticSublevelUnionCell`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Bundle Set unitInterval

noncomputable section

namespace TauCeti

variable {B Fᵤ Fₛ : Type*} {Eᵤ Eₛ : B → Type*} [∀ x, NormedAddCommGroup (Eᵤ x)]
  [∀ x, NormedAddCommGroup (Eₛ x)] {ε : ℝ} {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)}

/-! ### The lower sublevel with the negative disc bundle attached -/

variable (Fᵤ Fₛ Eᵤ Eₛ) in
/-- The lower sublevel `{-‖u‖² + ‖v‖² ≤ -ε}` of the quadratic model `-‖u‖² + ‖v‖²` on the Whitney
sum `Eᵤ ×ᵇ Eₛ`, together with the disc bundle `{‖u‖² ≤ ε, v = 0}` of radius `√ε` of `Eᵤ`: the
vectors whose fibre components lie in `TauCeti.quadraticSublevelUnionCell ε`. -/
def bundleQuadraticSublevelUnionCell (ε : ℝ) : Set (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :=
  {z | z.2 ∈ quadraticSublevelUnionCell ε}

/-- A vector lies in `TauCeti.bundleQuadraticSublevelUnionCell` exactly when its fibre components
lie in `TauCeti.quadraticSublevelUnionCell`. -/
theorem mem_bundleQuadraticSublevelUnionCell_iff_snd_mem :
    z ∈ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε ↔ z.2 ∈ quadraticSublevelUnionCell ε :=
  Iff.rfl

@[simp]
theorem mem_bundleQuadraticSublevelUnionCell :
    z ∈ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε ↔
      -‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ -ε ∨ ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0 :=
  mem_quadraticSublevelUnionCell

/-- A vector lies in the lower quadratic sublevel with the negative disc bundle attached exactly
when its positive component has norm at most `√(‖u‖² - ε)`. -/
theorem mem_bundleQuadraticSublevelUnionCell_iff_norm_le :
    z ∈ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε ↔ ‖z.2.2‖ ≤ √(‖z.2.1‖ ^ 2 - ε) :=
  mem_quadraticSublevelUnionCell_iff_norm_le

variable [TopologicalSpace (TotalSpace Fᵤ Eᵤ)] [TopologicalSpace (TotalSpace Fₛ Eₛ)]
  (hᵤ : Continuous fun u : TotalSpace Fᵤ Eᵤ ↦ ‖u.2‖)
  (hₛ : Continuous fun v : TotalSpace Fₛ Eₛ ↦ ‖v.2‖)

include hᵤ hₛ in
/-- The lower quadratic sublevel with the negative disc bundle attached is closed when the fibre
norms are continuous. -/
theorem isClosed_bundleQuadraticSublevelUnionCell (ε : ℝ) :
    IsClosed (bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε) := by
  have hu := hᵤ.comp (FiberBundle.Prod.continuous_totalSpaceFst (F₂ := Fₛ) (E₂ := Eₛ))
  have hv := hₛ.comp (FiberBundle.Prod.continuous_totalSpaceSnd (F₁ := Fᵤ) (E₁ := Eᵤ))
  simp only [Function.comp_def] at hu hv
  have h : bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε =
      {z | ‖z.2.2‖ ≤ √(‖z.2.1‖ ^ 2 - ε)} :=
    Set.ext fun _ ↦ mem_bundleQuadraticSublevelUnionCell_iff_norm_le
  rw [h]
  exact isClosed_le hv (by fun_prop)

/-! ### The fibrewise deformation -/

variable [TopologicalSpace B] [NormedAddCommGroup Fₛ] [NormedSpace ℝ Fₛ] [∀ x, NormedSpace ℝ (Eₛ x)]
  [FiberBundle Fₛ Eₛ] [VectorBundle ℝ Fₛ Eₛ]

include hᵤ hₛ in
/-- Milnor's deformation of the quadratic model, run in every fibre of the Whitney sum, is
jointly continuous in the time and the vector. -/
private theorem continuous_quadraticHandleDeformation_totalSpace (ε : ℝ) :
    Continuous fun p : I × TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ) ↦
      (⟨p.2.proj, quadraticHandleDeformation ε (p.1, p.2.2)⟩ :
        TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) := by
  rw [(FiberBundle.Prod.isInducing_diag Fᵤ Eᵤ Fₛ Eₛ).continuous_iff]
  simp only [Function.comp_def, quadraticHandleDeformation_apply_eq_smul]
  refine (FiberBundle.Prod.continuous_totalSpaceFst.comp continuous_snd).prodMk ?_
  -- The positive component is `v` rescaled by a scalar in `[0, 1]`, continuous where `v ≠ 0`.
  have hu : Continuous fun p : I × TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ) ↦ ‖p.2.2.1‖ :=
    hᵤ.comp (FiberBundle.Prod.continuous_totalSpaceFst.comp continuous_snd)
  have hv : Continuous fun p : I × TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ) ↦ ‖p.2.2.2‖ :=
    hₛ.comp (FiberBundle.Prod.continuous_totalSpaceSnd.comp continuous_snd)
  refine (FiberBundle.Prod.continuous_totalSpaceSnd.comp
    continuous_snd).smul_totalSpace_of_norm_le (C := 1) (fun p ↦ ?_) fun p hp ↦ ?_
  · obtain ⟨h₀, h₁⟩ := mem_Icc_quadraticHandleDeformation_scalar ε p.1 p.2.2
    rwa [Real.norm_of_nonneg h₀]
  · have hp' : ‖p.2.2.2‖ ≠ 0 := norm_ne_zero_iff.2 hp
    exact (((continuous_const.sub continuous_subtype_val.fst').continuousAt.mul
      (continuousAt_const.min
        (((hu.pow 2).sub continuous_const).sqrt.continuousAt.div hv.continuousAt hp'))).add
      continuous_subtype_val.fst'.continuousAt)

include hᵤ hₛ in
/-- **Milnor's retraction in a sum of vector bundles**: in each fibre of `Eᵤ ×ᵇ Eₛ` it keeps `u`
and retracts `v` radially onto the closed ball of radius `√(‖u‖² - ε)`, so it retracts the total
space onto `TauCeti.bundleQuadraticSublevelUnionCell`. -/
def bundleQuadraticHandleRetraction (ε : ℝ) :
    C(TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ), TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) where
  toFun z := (⟨z.proj, quadraticHandleRetraction ε z.2⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ))
  continuous_toFun := by
    have h := (continuous_quadraticHandleDeformation_totalSpace hᵤ hₛ ε).comp
      (continuous_const.prodMk continuous_id :
        Continuous fun z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ) ↦ ((0 : I), z))
    simpa only [Function.comp_def, ContinuousMap.HomotopyWith.apply_zero] using h

@[simp]
theorem bundleQuadraticHandleRetraction_apply (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    bundleQuadraticHandleRetraction hᵤ hₛ ε z =
      (⟨z.proj, quadraticHandleRetraction ε z.2⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :=
  (rfl)

/-- The retraction takes values in the lower quadratic sublevel with the negative disc bundle
attached. -/
theorem bundleQuadraticHandleRetraction_mem (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    bundleQuadraticHandleRetraction hᵤ hₛ ε z ∈
      bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε :=
  quadraticHandleRetraction_mem ε z.2

/-- The fixed points of the retraction are exactly the vectors of the lower quadratic sublevel with
the negative disc bundle attached. -/
theorem bundleQuadraticHandleRetraction_eq_self_iff :
    bundleQuadraticHandleRetraction hᵤ hₛ ε z = z ↔
      z ∈ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε := by
  rw [bundleQuadraticHandleRetraction_apply, TotalSpace.ext_iff,
    mem_bundleQuadraticSublevelUnionCell_iff_snd_mem]
  simpa only [heq_eq_eq, true_and] using quadraticHandleRetraction_eq_self_iff

include hᵤ hₛ in
/-- **Milnor's deformation in a sum of vector bundles**: at time `t` it keeps the base point and
`u`, and replaces `v` by `(1 - t) r(v) + t v`, where `r(v)` is the radial retraction of `v` onto
the closed ball of radius `√(‖u‖² - ε)`. It is a homotopy from
`TauCeti.bundleQuadraticHandleRetraction` to the identity which fixes
`TauCeti.bundleQuadraticSublevelUnionCell`. -/
def bundleQuadraticHandleDeformation (ε : ℝ) :
    (bundleQuadraticHandleRetraction hᵤ hₛ ε).HomotopyRel
      (ContinuousMap.id (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)))
      (bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε) where
  toFun p := ⟨p.2.proj, quadraticHandleDeformation ε (p.1, p.2.2)⟩
  continuous_toFun := continuous_quadraticHandleDeformation_totalSpace hᵤ hₛ ε
  map_zero_left z := by simp
  map_one_left z := by simp
  prop' t z hz := by
    simp only [ContinuousMap.coe_mk, bundleQuadraticHandleRetraction_apply]
    rw [(quadraticHandleDeformation ε).eq_fst t hz]

@[simp]
theorem bundleQuadraticHandleDeformation_apply (t : I) (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    bundleQuadraticHandleDeformation hᵤ hₛ ε (t, z) =
      (⟨z.proj, quadraticHandleDeformation ε (t, z.2)⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :=
  (rfl)

/-- The deformation preserves every set `X` whose fibres `{v | (u, v) ∈ X}` over each base point
`x` and each `u` are star-shaped about the origin. -/
theorem bundleQuadraticHandleDeformation_mem_of_starConvex
    {X : Set (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ))}
    (hX : ∀ (x : B) (u : Eᵤ x),
      StarConvex ℝ 0 {v : Eₛ x | (⟨x, (u, v)⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) ∈ X})
    (ε : ℝ) (t : I) (hz : z ∈ X) :
    bundleQuadraticHandleDeformation hᵤ hₛ ε (t, z) ∈ X := by
  obtain ⟨s, hs, h⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t z.2
  rw [bundleQuadraticHandleDeformation_apply, h]
  exact starConvex_zero_iff.1 (hX z.proj z.2.1) (by simpa using hz) hs.1 hs.2

include hᵤ hₛ in
/-- **Milnor's handle retraction in a sum of vector bundles.** If every fibre
`{v | (u, v) ∈ X}` of `X` over a base point and a negative component `u` is star-shaped about the
origin, then `X ∩ bundleQuadraticSublevelUnionCell ε` is a strong deformation retract of `X`: there
is a retraction of `X` onto it, and a homotopy in `X` from this retraction to the identity which
fixes `X ∩ bundleQuadraticSublevelUnionCell ε`. Both are restrictions of
`TauCeti.bundleQuadraticHandleRetraction` and `TauCeti.bundleQuadraticHandleDeformation`, so they
preserve the base point. -/
theorem exists_inter_bundleQuadraticSublevelUnionCell_deformation
    {X : Set (TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ))}
    (hX : ∀ (x : B) (u : Eᵤ x),
      StarConvex ℝ 0 {v : Eₛ x | (⟨x, (u, v)⟩ : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) ∈ X})
    (ε : ℝ) :
    ∃ r : C(X, ↥(X ∩ bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε)),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      (∀ x, (r x : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)).proj =
        (x : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)).proj) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id X)
        {x | (x : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) ∈
          bundleQuadraticSublevelUnionCell Fᵤ Fₛ Eᵤ Eₛ ε}) := by
  set H := bundleQuadraticHandleDeformation hᵤ hₛ ε
  have hmem (x : X) : bundleQuadraticHandleRetraction hᵤ hₛ ε x ∈ X := by
    simpa [H] using bundleQuadraticHandleDeformation_mem_of_starConvex hᵤ hₛ hX ε 0 x.2
  refine ⟨⟨fun x ↦ ⟨bundleQuadraticHandleRetraction hᵤ hₛ ε x, hmem x,
      bundleQuadraticHandleRetraction_mem hᵤ hₛ _⟩, by fun_prop⟩,
    fun x ↦ Subtype.ext ((bundleQuadraticHandleRetraction_eq_self_iff hᵤ hₛ).2 x.2.2),
    fun x ↦ rfl, ⟨?_⟩⟩
  exact
    { toFun p := ⟨H (p.1, p.2),
        bundleQuadraticHandleDeformation_mem_of_starConvex hᵤ hₛ hX ε p.1 p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (H.apply_zero (x : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)))
      map_one_left x := Subtype.ext (H.apply_one (x : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)))
      prop' t x hx := Subtype.ext (H.eq_fst t hx) }

end TauCeti
