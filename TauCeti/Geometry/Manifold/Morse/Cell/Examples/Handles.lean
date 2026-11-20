/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.HandlePushout
public import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import TauCeti.AlgebraicTopology.Singular.IntervalGenerator

/-!
# Handles of index `0`, `1` and `m`

Milnor's handle attachment theorem in pushout form
(`TauCeti.IsMorse.exists_isPushout_sublevel_handle`) says that crossing a level `c` of a Morse
function with a single critical point `p` of index `λ` attaches the handle `𝔻 λ × 𝔻 (m - λ)` to the
lower sublevel `M_{c-ε} = {f ≤ c - ε}` along `∂𝔻 λ × 𝔻 (m - λ)`. This file works out the three
basic cases, which test the indexing of the handles and the attaching maps.

* **Index `0`.** For `f(x) = x²` on `ℝ` and `c = 0`, the critical point `0` has index `0`
  (`TauCeti.manifoldMorseIndex_sq_real`) and `M_{-ε}` is empty. The attaching region
  `∂𝔻 0 × 𝔻 1` is empty too, since the unit sphere of `ℝ⁰` is empty, so the pushout is the handle
  `𝔻 0 × 𝔻 1` itself, a compact interval, and the handle is homeomorphic to `M_ε = [-√ε, √ε]` with
  its top `𝔻 0 × ∂𝔻 1` going to the endpoints `±√ε`
  (`TauCeti.exists_homeomorph_sublevel_sq`). An index-`0` handle adds a new component.
* **Index `1`.** For `f(x) = -x²` on `ℝ` and `c = 0`, the critical point `0` has index `1`
  (`TauCeti.manifoldMorseIndex_neg_sq_real`), and `M_{-ε} = (-∞, -√ε] ∪ [√ε, ∞)` is two rays.
  The handle is `𝔻 1 × 𝔻 0`, an arc, attached along its two endpoints `∂𝔻 1 × 𝔻 0`, which go to
  the two points `±√ε` of the level `f = -ε` (`TauCeti.exists_isPushout_sublevel_handle_neg_sq`).
  So the arc joins the two rays, giving `M_ε = ℝ`.
* **Index `m`.** For the height `h` on the unit sphere `Sᵐ` and `c = 1`, the north pole has
  index `m` (`TauCeti.manifoldMorseIndex_sphereHeight_self`). The handle is `𝔻 m × 𝔻 0`, a disc,
  attached along its boundary sphere `∂𝔻 m × 𝔻 0`, which goes onto the whole level sphere
  `h = 1 - ε` (`TauCeti.exists_isPushout_sublevel_handle_sphereHeight`). Since `h ≤ 1`, the upper
  sublevel `M_{1+ε}` is the whole sphere, which is thus `M_{1-ε}` capped off by a disc.

## Main results

* `TauCeti.exists_homeomorph_sublevel_sq`: for `x²`, the sublevel `M_ε` is the index-`0` handle.
* `TauCeti.exists_isPushout_sublevel_handle_neg_sq`: for `-x²`, the index-`1` handle is attached
  at the two points `±√ε`.
* `TauCeti.exists_isPushout_sublevel_handle_sphereHeight`: for the height on `Sᵐ`, the index-`m`
  handle is attached along the whole level sphere below the maximum.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Set Metric Topology CategoryTheory Limits
open scoped Manifold

universe u

namespace TauCeti

/-! ### Index `0`: the quadratic well -/

/-- The level `0` of `x ↦ x²` on `ℝ` holds the single critical point `0`. -/
private theorem criticalPoints_sq_real_inter_preimage_zero :
    criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) ∩ (fun x : ℝ ↦ x ^ 2) ⁻¹' {0} = {0} := by
  rw [criticalPoints_sq_real]
  ext x
  simp +contextual

/-- A band `{-δ ≤ g ≤ δ}` of a continuous function `g` on `ℝ` with `x² ≤ |g x|`, such as `±x²`,
is compact. -/
private theorem isCompact_preimage_Icc_of_sq_le_abs {g : ℝ → ℝ} (hg : Continuous g)
    (hsq : ∀ x, x ^ 2 ≤ |g x|) (δ : ℝ) : IsCompact (g ⁻¹' Icc (0 - δ) (0 + δ)) := by
  refine (isCompact_closedBall (0 : ℝ) √δ).of_isClosed_subset (isClosed_Icc.preimage hg)
    fun x hx ↦ ?_
  rw [zero_sub, zero_add, mem_preimage, mem_Icc, ← abs_le] at hx
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact Real.abs_le_sqrt ((hsq x).trans hx)

/-- **The handle of index `0`.** For the Morse function `x ↦ x²` on `ℝ` and its critical level
`0`, Milnor's handle attachment theorem attaches the handle `𝔻 0 × 𝔻 1` of index `0` to the empty
lower sublevel `{x² ≤ -ε}` along the empty attaching region `∂𝔻 0 × 𝔻 1`. So for some small
`0 < ε ≤ δ` the handle is homeomorphic to the sublevel `{x² ≤ ε} = [-√ε, √ε]`, with its top
`𝔻 0 × ∂𝔻 1` going onto the endpoints, the level `x² = ε`. -/
theorem exists_homeomorph_sublevel_sq {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧
      ∃ χ : (TopCat.disk.{0} 0 × TopCat.disk.{0} 1) ≃ₜ {x : ℝ | x ^ 2 ≤ ε},
        ∀ w, (χ w : ℝ) ^ 2 = ε ↔ w.2 ∈ range (TopCat.diskBoundaryInclusion 1) := by
  obtain ⟨ε, hε, hεδ, α, χ, j, hpush, -, -, hχc, -⟩ :=
    isMorse_sq_real.exists_isPushout_sublevel_handle hδ
      (isCompact_preimage_Icc_of_sq_le_abs (by fun_prop) (fun _ ↦ le_abs_self _) δ)
      criticalPoints_sq_real_inter_preimage_zero
  -- The lower sublevel `{x² ≤ -ε}` is empty, so the attaching map is a map between empty spaces,
  -- an isomorphism, and then so is the map from the handle to the upper sublevel.
  have hempty : IsEmpty {x : ℝ | x ^ 2 ≤ 0 - ε} :=
    ⟨fun x ↦ by
      have hx : (x : ℝ) ^ 2 ≤ 0 - ε := x.2
      nlinarith [sq_nonneg (x : ℝ)]⟩
  have : IsIso α := TopCat.isIso_of_bijective_of_isOpenMap α
    ⟨fun s ↦ isEmptyElim (α s), fun x ↦ isEmptyElim x⟩ fun _ _ ↦ by simp
  have : IsIso χ := hpush.isIso_inr_of_isIso
  have key : ∃ χ : (TopCat.disk.{0} (manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0) ×
      TopCat.disk.{0} (Module.finrank ℝ ℝ -
        manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0)) ≃ₜ {x : ℝ | x ^ 2 ≤ 0 + ε},
      ∀ w, (χ w : ℝ) ^ 2 = 0 + ε ↔ w.2 ∈ range (TopCat.diskBoundaryInclusion
        (Module.finrank ℝ ℝ - manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0)) :=
    ⟨TopCat.homeoOfIso (asIso χ), hχc⟩
  rw [manifoldMorseIndex_sq_real, Module.finrank_self, zero_add] at key
  exact ⟨ε, hε, hεδ, key⟩

/-! ### Index `1`: the inverted well -/

/-- The function `x ↦ -x²` on `ℝ` has the single critical point `0`. -/
theorem criticalPoints_neg_sq_real : criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) = {0} :=
  -- `fun x ↦ -x ^ 2` is the pointwise negation `-fun x ↦ x ^ 2`, by the definition of `Pi.neg`.
  (criticalPoints_neg (f := fun x : ℝ ↦ x ^ 2)).trans criticalPoints_sq_real

/-- **The function `x ↦ -x²` on `ℝ` is a Morse function.** -/
theorem isMorse_neg_sq_real : IsMorse 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) :=
  -- `fun x ↦ -x ^ 2` is the pointwise negation `-fun x ↦ x ^ 2`, by the definition of `Pi.neg`.
  isMorse_sq_real.neg

/-- The critical point `0` of `x ↦ -x²` on `ℝ` is a maximum, of Morse index `1`. -/
theorem manifoldMorseIndex_neg_sq_real :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) 0 = 1 := by
  have h := (isMorse_sq_real.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 (criticalPoints_sq_real ▸ mem_singleton 0))
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rw [manifoldMorseIndex_sq_real, Module.finrank_self, add_zero] at h
  exact h

/-- The level `0` of `x ↦ -x²` on `ℝ` holds the single critical point `0`. -/
private theorem criticalPoints_neg_sq_real_inter_preimage_zero :
    criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) ∩ (fun x : ℝ ↦ -x ^ 2) ⁻¹' {0} = {0} := by
  rw [criticalPoints_neg_sq_real]
  ext x
  simp +contextual

/-- An injection `α` from the attaching region `∂𝔻 1 × 𝔻 0`, two points, into `ℝ` whose values
square to `ε` has image `{-√ε, √ε}`. -/
private theorem range_eq_of_injective_of_sq_eq {ε : ℝ} (hε : 0 < ε)
    {α : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 → ℝ} (hα : Function.Injective α)
    (hαε : ∀ s, α s ^ 2 = ε) : range α = {-√ε, √ε} := by
  have hpm (s) : α s = -√ε ∨ α s = √ε := by
    have h := hαε s
    rw [← Real.sq_sqrt hε.le, sq_eq_sq_iff_eq_or_eq_neg] at h
    exact h.symm
  refine (range_subset_iff.2 fun s ↦ hpm s).antisymm ?_
  -- The two endpoints `±1` of the arc `𝔻 1`, at the centre of the one-point disc `𝔻 0`.
  let s : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 := (sphereMinus, diskCenter 0)
  let t : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 := (spherePlus, diskCenter 0)
  have hαst : α s ≠ α t := hα.ne fun h ↦ sphereMinus_ne_spherePlus (congrArg Prod.fst h)
  rintro y (rfl | rfl) <;> rcases hpm s with hs | hs <;> rcases hpm t with ht | ht
  all_goals first
    | exact ⟨s, hs⟩ | exact ⟨t, ht⟩ | exact absurd (hs.trans ht.symm) hαst

/-- **The handle of index `1`.** For the Morse function `x ↦ -x²` on `ℝ` and its critical level `0`,
Milnor's handle attachment theorem attaches the arc `𝔻 1 × 𝔻 0`, a handle of index `1`, to the two
rays `{-x² ≤ -ε} = (-∞, -√ε] ∪ [√ε, ∞)` along its two endpoints `∂𝔻 1 × 𝔻 0`: for some small
`0 < ε ≤ δ` there is a pushout square in `TopCat` whose attaching map carries the two endpoints to
the two points `±√ε` of the level `-x² = -ε`. The pushout is the sublevel `{-x² ≤ ε}`, all of
`ℝ`. -/
theorem exists_isPushout_sublevel_handle_neg_sq {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧
      ∃ (α : TopCat.of (TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0) ⟶
          TopCat.of {x : ℝ | -x ^ 2 ≤ -ε})
        (χ : TopCat.of (TopCat.disk.{0} 1 × TopCat.disk.{0} 0) ⟶ TopCat.of {x : ℝ | -x ^ 2 ≤ ε})
        (j : TopCat.of {x : ℝ | -x ^ 2 ≤ -ε} ⟶ TopCat.of {x : ℝ | -x ^ 2 ≤ ε}),
        IsPushout α (TopCat.ofHom
          ((TopCat.diskBoundaryInclusion 1).hom.prodMap (ContinuousMap.id _))) j χ ∧
        range (fun s ↦ (α s : ℝ)) = {-√ε, √ε} := by
  obtain ⟨ε, hε, hεδ, key⟩ :=
    isMorse_neg_sq_real.exists_isPushout_sublevel_handle hδ
      (isCompact_preimage_Icc_of_sq_le_abs (by fun_prop)
        (fun x ↦ (le_abs_self _).trans_eq (abs_neg _).symm) δ)
      criticalPoints_neg_sq_real_inter_preimage_zero
  rw [manifoldMorseIndex_neg_sq_real, Module.finrank_self, zero_sub, zero_add] at key
  obtain ⟨α, χ, j, hpush, hα, hαc, -, -⟩ := key
  refine ⟨ε, hε, hεδ, α, χ, j, hpush, range_eq_of_injective_of_sq_eq hε
    (Subtype.val_injective.comp hα.injective) fun s ↦ ?_⟩
  have := hαc s
  simp only at this
  linarith

/-! ### Index `m`: the height on a sphere -/

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

/-- The level `1` of the height function on the sphere holds the single critical point `v`, the
north pole. -/
private theorem criticalPoints_sphereHeight_inter_preimage_one (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1} = {v} := by
  rw [criticalPoints_sphereHeight]
  ext x
  constructor
  · rintro ⟨rfl | rfl, hx⟩
    · rfl
    · norm_num [sphereHeight_neg_self] at hx
  · intro hx
    rw [mem_singleton_iff.1 hx]
    exact ⟨mem_insert v _, sphereHeight_self v⟩

/-- **The handle of index `m`.** For the height function `h` on the unit sphere `Sᵐ` and its top
critical level `1`, Milnor's handle attachment theorem attaches the disc `𝔻 m × 𝔻 0`, a handle of
index `m`, to the sublevel `{h ≤ 1 - ε}` along its boundary sphere `∂𝔻 m × 𝔻 0`: for some small
`0 < ε ≤ δ` there is a pushout square in `TopCat` whose attaching map is a closed embedding of the
boundary sphere onto the whole level sphere `h = 1 - ε`. The pushout is the sublevel `{h ≤ 1 + ε}`,
the whole sphere. -/
theorem exists_isPushout_sublevel_handle_sphereHeight (v : sphere (0 : E) 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧
      ∃ (α : TopCat.of (TopCat.diskBoundary.{u} n × TopCat.disk.{u} 0) ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 - ε})
        (χ : TopCat.of (TopCat.disk.{u} n × TopCat.disk.{u} 0) ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 + ε})
        (j : TopCat.of {x | sphereHeight v x ≤ 1 - ε} ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 + ε}),
        IsPushout α (TopCat.ofHom
          ((TopCat.diskBoundaryInclusion n).hom.prodMap (ContinuousMap.id _))) j χ ∧
        IsClosedEmbedding α ∧
        range (fun s ↦ (α s : sphere (0 : E) 1)) = {x | sphereHeight v x = 1 - ε} := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨ε, hε, hεδ, key⟩ := (isMorse_sphereHeight (n := n) v).exists_isPushout_sublevel_handle hδ
    ((isClosed_Icc.preimage (contMDiff_sphereHeight (n := n) (m := 0) v).continuous).isCompact)
    (criticalPoints_sphereHeight_inter_preimage_one v)
  rw [manifoldMorseIndex_sphereHeight_self, finrank_euclideanSpace_fin, Nat.sub_self] at key
  obtain ⟨α, χ, j, hpush, hα, hαc, -, hj⟩ := key
  refine ⟨ε, hε, hεδ, α, χ, j, hpush, hα, (range_subset_iff.2 hαc).antisymm fun x hx ↦ ?_⟩
  -- A point of the level `h = 1 - ε` off the attaching sphere would stay on the level
  -- `h = 1 + ε` of the upper sublevel, which is empty since `h ≤ 1`.
  by_contra hxα
  have h1 := (hj ⟨x, le_of_eq hx⟩ fun ⟨s, hs⟩ ↦ hxα ⟨s, congrArg Subtype.val hs⟩).2 hx
  linarith [sphereHeight_le_one v (j ⟨x, le_of_eq hx⟩ : sphere (0 : E) 1)]

end Sphere

end TauCeti
