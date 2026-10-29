/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Subgroup

/-!
# Extensions of amenable discrete groups

If `N` is a normal subgroup of a discrete group `G` and both `N` and `G ⧸ N` are amenable, then
`G` is amenable. As for solvable groups in Mathlib (`isSolvable_of_ker_le_range`), the result is
proved for homomorphisms `ψ : K →* G` and `φ : G →* Q` of discrete groups with
`φ.ker ≤ ψ.range`: if `K` and `Q` are amenable, so is `G`.

The mean on `G` is an iterated mean. For a mean `n` on `K` and a bounded function `f` on `G`,
the *fiber average* `x ↦ n (k ↦ f (x * ψ k))` (`TauCeti.UCB.fiberAverage`) is again bounded by
`‖f‖`, and it commutes with left translations. When `n` is left invariant, its value at `x`
depends only on the coset `x * ψ.range`, hence only on `φ x`. Choosing a section `s` of `φ`, the
function `q ↦ n (k ↦ f (s q * ψ k))` on `Q` is averaged by a mean `m` on `Q`
(`TauCeti.Mean.extension`). Translating `f` by `g` translates this function on `Q` by `φ g`, so
the iterated mean is left invariant when `n` and `m` are.

## Main definitions

* `TauCeti.UCB.fiberAverage ψ n`: the fiber average `f ↦ (x ↦ n (k ↦ f (x * ψ k)))`.
* `TauCeti.Mean.extension ψ n s m`: the iterated mean `f ↦ m (q ↦ n (k ↦ f (s q * ψ k)))`.

## Main results

* `TauCeti.Mean.IsLeftInvariant.extension`: the iterated mean of left-invariant means along a
  section of `φ` is left invariant when `φ.ker ≤ ψ.range`.
* `TauCeti.Amenable.of_ker_le_range`: if `φ.ker ≤ ψ.range` and `K`, `Q` are amenable, then `G` is
  amenable.
* `TauCeti.amenable_iff_subgroup_quotient`: a discrete group with a normal subgroup `N` is
  amenable exactly when `N` and `G ⧸ N` are.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

variable {G K Q : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [Group K] [TopologicalSpace K] [DiscreteTopology K] [Group Q]

namespace UCB

/-- The fiber average `x ↦ n (k ↦ f (x * ψ k))` of a bounded function `f` on a discrete group
`G`, for a mean `n` on a discrete group `K` mapping to `G` by `ψ`. -/
def fiberAverage (ψ : K →* G) (n : Mean K) : UCB G →ₗ[ℝ] UCB G where
  toFun f := (discreteAlgEquiv G).symm <|
    .ofNormedAddCommGroupDiscrete (fun x => n (compRightAlgHomOfDiscrete (x * ψ ·) f)) ‖f‖
      fun x => by
        rw [Real.norm_eq_abs]
        exact (n.abs_apply_le_norm _).trans (norm_compRightAlgHomOfDiscrete_apply_le _ f)
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

@[simp]
theorem fiberAverage_apply (ψ : K →* G) (n : Mean K) (f : UCB G) (x : G) :
    (fiberAverage ψ n f : G →ᵇ ℝ) x = n (compRightAlgHomOfDiscrete (x * ψ ·) f) := by
  simp [fiberAverage]

/-- The fiber average does not increase the supremum norm. -/
theorem norm_fiberAverage_apply_le (ψ : K →* G) (n : Mean K) (f : UCB G) :
    ‖fiberAverage ψ n f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x =>
    (Real.norm_eq_abs _).trans_le <| (congrArg abs (fiberAverage_apply ψ n f x)).trans_le <|
      (n.abs_apply_le_norm _).trans (norm_compRightAlgHomOfDiscrete_apply_le _ f)

/-- The fiber average preserves the pointwise order. -/
theorem monotone_fiberAverage (ψ : K →* G) (n : Mean K) : Monotone (fiberAverage ψ n) :=
  fun _ _ h => le_def.2 fun x => by
    simpa only [fiberAverage_apply] using OrderHomClass.mono n
      (monotone_compRightAlgHomOfDiscrete (x * ψ ·) h)

/-- The fiber average of the constant function one is one. -/
@[simp]
theorem fiberAverage_one (ψ : K →* G) (n : Mean K) : fiberAverage ψ n 1 = 1 := by
  ext x
  simp

/-- The fiber average commutes with left translations. -/
@[simp]
theorem fiberAverage_leftTranslation (ψ : K →* G) (n : Mean K) (g : G) (f : UCB G) :
    fiberAverage ψ n (leftTranslation g f) = leftTranslation g (fiberAverage ψ n f) := by
  ext x
  simp only [fiberAverage_apply, leftTranslation_apply]
  congr 1
  ext k
  simp [leftTranslation_apply, mul_assoc]

/-- For a left-invariant mean `n`, the fiber average is invariant under right multiplication by
the image of `ψ`. -/
theorem fiberAverage_apply_mul {n : Mean K} (hn : n.IsLeftInvariant) (ψ : K →* G) (f : UCB G)
    (x : G) (k : K) :
    (fiberAverage ψ n f : G →ᵇ ℝ) (x * ψ k) = (fiberAverage ψ n f : G →ᵇ ℝ) x := by
  -- The slice at `x * ψ k` is the slice at `x` translated by `k⁻¹`.
  have : compRightAlgHomOfDiscrete (x * ψ k * ψ ·) f =
      leftTranslation k⁻¹ (compRightAlgHomOfDiscrete (x * ψ ·) f) := by
    ext k'
    rw [leftTranslation_apply]
    simp [mul_assoc]
  rw [fiberAverage_apply, fiberAverage_apply, this, hn.apply_leftTranslation]

/-- For a left-invariant mean `n` and `φ.ker ≤ ψ.range`, the value of the fiber average at `x`
depends only on `φ x`. -/
theorem fiberAverage_apply_eq_of_map_eq {n : Mean K} (hn : n.IsLeftInvariant) {ψ : K →* G}
    {φ : G →* Q} (h : φ.ker ≤ ψ.range) (f : UCB G) {x y : G} (hxy : φ x = φ y) :
    (fiberAverage ψ n f : G →ᵇ ℝ) x = (fiberAverage ψ n f : G →ᵇ ℝ) y := by
  obtain ⟨k, hk⟩ := h (show x⁻¹ * y ∈ φ.ker by simp [hxy])
  rw [← fiberAverage_apply_mul hn ψ f x k, hk, mul_inv_cancel_left]

end UCB

namespace Mean

variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- The iterated mean `f ↦ m (q ↦ n (k ↦ f (s q * ψ k)))` on a discrete group `G`, built from a
mean `n` on `K`, a homomorphism `ψ : K →* G`, a map `s : Q → G` and a mean `m` on `Q`. -/
def extension (ψ : K →* G) (n : Mean K) (s : Q → G) (m : Mean Q) : Mean G :=
  mk₀ ((m.mapOfDiscrete s).toPositiveLinearMap.toLinearMap ∘ₗ UCB.fiberAverage ψ n)
    (fun f hf => map_nonneg (m.mapOfDiscrete s) (by
      simpa using UCB.monotone_fiberAverage ψ n hf))
    (by simp)

/-- The iterated mean formula: `extension ψ n s m f = m (q ↦ n (k ↦ f (s q * ψ k)))`. -/
@[simp]
theorem extension_apply (ψ : K →* G) (n : Mean K) (s : Q → G) (m : Mean Q) (f : UCB G) :
    extension ψ n s m f = m.mapOfDiscrete s (UCB.fiberAverage ψ n f) :=
  mk₀_apply _ _ _ f

/-- If `φ.ker ≤ ψ.range` and `s` is a section of `φ`, then the iterated mean of left-invariant
means `n` on `K` and `m` on `Q` is left invariant. -/
theorem IsLeftInvariant.extension {n : Mean K} {m : Mean Q} (hn : n.IsLeftInvariant)
    (hm : m.IsLeftInvariant) {ψ : K →* G} {φ : G →* Q} (h : φ.ker ≤ ψ.range) {s : Q → G}
    (hs : ∀ q, φ (s q) = q) : (Mean.extension ψ n s m).IsLeftInvariant := by
  refine isLeftInvariant_iff.2 fun g f => ?_
  -- Translating by `g` on `G` translates the function `q ↦ n (k ↦ f (s q * ψ k))` by `φ g`.
  have : UCB.compRightAlgHomOfDiscrete s (UCB.leftTranslation g (UCB.fiberAverage ψ n f)) =
      UCB.leftTranslation (φ g) (UCB.compRightAlgHomOfDiscrete s (UCB.fiberAverage ψ n f)) := by
    ext q
    simp only [UCB.compRightAlgHomOfDiscrete_apply, UCB.leftTranslation_apply]
    exact UCB.fiberAverage_apply_eq_of_map_eq hn h f (by simp [hs])
  rw [extension_apply, extension_apply, UCB.fiberAverage_leftTranslation, mapOfDiscrete_apply,
    mapOfDiscrete_apply, this, hm.apply_leftTranslation]

end Mean

variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- If `ψ : K →* G` and `φ : G →* Q` are homomorphisms of discrete groups with
`φ.ker ≤ ψ.range`, and `K` and `Q` are amenable, then `G` is amenable. -/
theorem Amenable.of_ker_le_range [Amenable K] [Amenable Q] (ψ : K →* G) (φ : G →* Q)
    (h : φ.ker ≤ ψ.range) : Amenable G := by
  -- Corestrict `φ` to its range, which is amenable as a subgroup of `Q`.
  have hφ := φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := Amenable.exists_isLeftInvariant (G := K)
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := φ.range)
  exact ⟨⟨_, hn.extension hm (φ.ker_rangeRestrict ▸ h) (Function.surjInv_eq hφ)⟩⟩

/-- A discrete group with a normal subgroup `N` is amenable exactly when `N` and `G ⧸ N` are
amenable. -/
theorem amenable_iff_subgroup_quotient (N : Subgroup G) [N.Normal] :
    Amenable G ↔ Amenable N ∧ Amenable (G ⧸ N) := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (N : Set G))
  refine ⟨fun _ => ⟨inferInstance, ?_⟩, fun ⟨_, _⟩ =>
    .of_ker_le_range N.subtype (QuotientGroup.mk' N) (by simp)⟩
  exact .of_surjective ⟨QuotientGroup.mk' N, continuous_of_discreteTopology⟩
    (QuotientGroup.mk'_surjective N)

/-- A discrete group is amenable when it has an amenable normal subgroup with amenable
quotient. -/
theorem Amenable.of_subgroup_quotient (N : Subgroup G) [N.Normal] [Amenable N]
    [Amenable (G ⧸ N)] : Amenable G :=
  (amenable_iff_subgroup_quotient N).2 ⟨‹_›, ‹_›⟩

end TauCeti
