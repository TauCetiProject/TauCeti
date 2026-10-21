/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Pulling a covering map back along a continuous map

Let `g : Z → Y` be a covering map and `f : X → Y` a continuous map. The fibre product
`X ×_Y Z = {(x, z) | f x = g z}` (Mathlib's `Function.Pullback f g`), with the subspace topology
of `X × Z`, projects to `X` by `Function.Pullback.fst`, and that projection is again a covering map
whose fibre over `x` is the fibre of `g` over `f x`. If `H : g ⁻¹' U ≃ₜ U × I` trivialises `g` over
an open `U ∋ f x`, then `(x', z) ↦ (x', (H z).2)` trivialises the projection over `f ⁻¹' U`.

The relative version is what produces covers from equations: for `n ≠ 0` the power map
`y ↦ y ^ n` is a covering of `ℂ` over `ℂ ∖ {0}`, so for a continuous `h : X → ℂ` without zeros
the curve `{(x, y) | h x = y ^ n}` is a covering of `X`.

## Main results

* `Function.Pullback.ext`, `Function.Pullback.continuous_fst`, `Function.Pullback.continuous_snd`:
  a point of the fibre product is determined by its coordinates, which depend continuously on it.
* `IsEvenlyCovered.pullback_fst`: a point evenly covered by `g` pulls back to evenly covered points
  of the projection, with the same fibre.
* `IsCoveringMap.pullback_fst`: the pullback of a covering map is a covering map.
* `IsCoveringMapOn.pullback_fst`: the pullback of a map that is a covering over `s` is a covering
  over the preimage of `s`.
* `IsCoveringMapOn.isCoveringMap_pullback_fst`: the pullback of a map that is a covering over `s`
  along a map into `s` is a covering map.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces and
  their lifting properties).
-/

public section

open Function

variable {X Y Z : Type*} {f : X → Y} {g : Z → Y}

/-- A point of the fibre product `X ×_Y Z` is determined by its two coordinates. -/
@[ext]
theorem Function.Pullback.ext {p q : f.Pullback g} (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) :
    p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

variable [TopologicalSpace X] [TopologicalSpace Z]

/-- The projection `X ×_Y Z → X` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_fst : Continuous (Pullback.fst : f.Pullback g → X) :=
  _root_.continuous_fst.comp continuous_subtype_val

/-- The projection `X ×_Y Z → Z` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_snd : Continuous (Pullback.snd : f.Pullback g → Z) :=
  _root_.continuous_snd.comp continuous_subtype_val

variable [TopologicalSpace Y]

/-- If `f x` is evenly covered by `g` with fibre `I`, then `x` is evenly covered with fibre `I` by
the projection `X ×_Y Z → X` of the fibre product of `f` and `g`. -/
theorem IsEvenlyCovered.pullback_fst {I : Type*} [TopologicalSpace I] {x : X} (hf : Continuous f)
    (h : IsEvenlyCovered g (f x) I) :
    IsEvenlyCovered (Pullback.fst : f.Pullback g → X) x I := by
  obtain ⟨hI, U, hxU, hU, hgU, H, hH⟩ := h
  -- The point of `g ⁻¹' U` under a point of the fibre product over `f ⁻¹' U`.
  let k (w : Pullback.fst ⁻¹' (f ⁻¹' U)) : g ⁻¹' U :=
    ⟨w.1.snd, by
      rw [Set.mem_preimage, ← (show f w.1.fst = g w.1.snd from w.1.2)]
      exact w.2⟩
  have hk : Continuous k := (Pullback.continuous_snd.comp continuous_subtype_val).subtype_mk _
  -- A point of the fibre of `g` over `f x'`, for `x' ∈ f ⁻¹' U`, from its sheet index.
  let l (v : f ⁻¹' U × I) : g ⁻¹' U := H.symm (⟨f v.1, v.1.2⟩, v.2)
  have hl : Continuous l :=
    H.symm.continuous.comp ((((hf.comp continuous_subtype_val).comp continuous_fst).subtype_mk
      _).prodMk continuous_snd)
  have hgl (v : f ⁻¹' U × I) : f v.1 = g (l v) := by
    rw [← hH, Homeomorph.apply_symm_apply]
  -- `l` inverts the sheet index of the point of `g ⁻¹' U` under a point of the fibre product.
  have hlk (w : Pullback.fst ⁻¹' (f ⁻¹' U)) : l (⟨w.1.fst, w.2⟩, (H (k w)).2) = k w := by
    have hHk : H (k w) = (⟨f w.1.fst, w.2⟩, (H (k w)).2) :=
      Prod.ext (Subtype.ext ((hH (k w)).trans w.1.2.symm)) rfl
    simp only [l, ← hHk, Homeomorph.symm_apply_apply]
  refine ⟨hI, f ⁻¹' U, hxU, hU.preimage hf, (hU.preimage hf).preimage Pullback.continuous_fst,
    { toFun w := (⟨w.1.fst, w.2⟩, (H (k w)).2)
      invFun v := ⟨⟨(v.1, l v), hgl v⟩, v.1.2⟩
      left_inv w := Subtype.ext (Subtype.ext (Prod.ext rfl (congrArg Subtype.val (hlk w))))
      right_inv v := by
        refine Prod.ext rfl ?_
        -- `k` of the inverse image of `v` is `l v`, up to eta for subtypes.
        exact (congrArg Prod.snd (H.apply_symm_apply (⟨f v.1, v.1.2⟩, v.2)) :)
      continuous_toFun :=
        ((Pullback.continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          (continuous_snd.comp (H.continuous.comp hk))
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp hl) },
    fun _ ↦ rfl⟩

/-- **The pullback of a covering map is a covering map**: for a covering map `g : Z → Y` and a
continuous `f : X → Y`, the projection `X ×_Y Z → X` of the fibre product is a covering map. -/
theorem IsCoveringMap.pullback_fst (hg : IsCoveringMap g) (hf : Continuous f) :
    IsCoveringMap (Pullback.fst : f.Pullback g → X) :=
  fun x ↦ ((hg (f x)).pullback_fst hf).to_isEvenlyCovered_preimage

/-- If `g : Z → Y` is a covering map over `s` and `f : X → Y` is continuous, then the projection
`X ×_Y Z → X` of the fibre product is a covering map over `f ⁻¹' s`. -/
theorem IsCoveringMapOn.pullback_fst {s : Set Y} (hg : IsCoveringMapOn g s) (hf : Continuous f) :
    IsCoveringMapOn (Pullback.fst : f.Pullback g → X) (f ⁻¹' s) :=
  fun x hx ↦ ((hg (f x) hx).pullback_fst hf).to_isEvenlyCovered_preimage

/-- If `g : Z → Y` is a covering map over `s` and the continuous map `f : X → Y` takes values in
`s`, then the projection `X ×_Y Z → X` of the fibre product is a covering map. -/
theorem IsCoveringMapOn.isCoveringMap_pullback_fst {s : Set Y} (hg : IsCoveringMapOn g s)
    (hf : Continuous f) (hfs : ∀ x, f x ∈ s) :
    IsCoveringMap (Pullback.fst : f.Pullback g → X) :=
  fun x ↦ hg.pullback_fst hf x (hfs x)
