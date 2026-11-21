/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Shrinking a smooth collar

A smooth collar `c : ∂M × [0, 1) → M` can be made thinner: for `0 < ε ≤ 1`, restricting `c` to
`∂M × [0, ε)` and precomposing with `(x, t) ↦ (x, ε t)` gives again a smooth collar, whose image
is the part of the image of `c` of depth less than `ε`. Gluing constructions shrink collars this
way to make them fit inside a prescribed neighbourhood of the boundary.

The depth rescaling is the restriction of the scaling diffeomorphism
`TauCeti.EuclideanHalfSpace.smulDiffeomorph` of the half-space model, and the shrunk collar is
the reparametrization `TauCeti.SmoothCollar.reparam` along it.

## Main definitions

* `TauCeti.EuclideanHalfSpace.smulDiffeomorph`: multiplication by a positive scalar, as a
  diffeomorphism of the half-space model.
* `TauCeti.EuclideanHalfSpace.normalIioOpensScale`: multiplication by `ε ∈ (0, 1]`, as a self-map
  of the depth parameter `[0, 1)`.
* `TauCeti.SmoothCollar.shrink`: the collar `(x, t) ↦ c (x, ε t)`.

## Main results

* `TauCeti.EuclideanHalfSpace.isLocalDiffeomorph_normalIioOpensScale`: the depth rescaling is a
  local diffeomorphism.
* `TauCeti.EuclideanHalfSpace.range_normalIioOpensScale`: its image is `[0, ε)`.
* `TauCeti.SmoothCollar.range_shrink`: the image of the shrunk collar is the image of `∂M × [0, ε)`.
* `TauCeti.SmoothCollar.shrink_one`: shrinking by `1` does nothing.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

variable {m : ℕ} [NeZero m] {k : WithTop ℕ∞} {ε : ℝ}

private theorem smul_mem_halfSpace (hε : 0 < ε) (x : EuclideanHalfSpace m) :
    0 ≤ (ε • x.1) 0 := by
  simpa using mul_nonneg hε.le x.2

private theorem smul_mem_range (hε : 0 < ε) (x : EuclideanHalfSpace m) :
    ε • (𝓡∂ m) x ∈ range (𝓡∂ m) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact smul_mem_halfSpace hε x

/-- Multiplication by `ε` on the half-space model, the map underlying `smulDiffeomorph`. -/
private def smulMap (hε : 0 < ε) (x : EuclideanHalfSpace m) : EuclideanHalfSpace m :=
  ⟨ε • x.1, smul_mem_halfSpace hε x⟩

private theorem contMDiff_smulMap (hε : 0 < ε) :
    ContMDiff (𝓡∂ m) (𝓡∂ m) k (smulMap (m := m) hε) := by
  have hcoord : ContMDiff (𝓡∂ m) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) k (fun x ↦ ε • (𝓡∂ m) x) :=
    (contDiff_const_smul ε).contMDiff.comp (𝓡∂ m).contMDiff
  refine ((𝓡∂ m).contMDiffOn_symm.comp_contMDiff hcoord (smul_mem_range hε)).congr fun x ↦ ?_
  apply Subtype.ext
  change ε • x.1 = ((𝓡∂ m).symm (ε • x.1)).1
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (smul_mem_halfSpace hε x)]

variable (m k) in
/-- **Scaling the half-space model.** Multiplication by a positive scalar `ε` is a `C^k`
diffeomorphism of the Euclidean half-space, with inverse multiplication by `ε⁻¹`. -/
def smulDiffeomorph (hε : 0 < ε) : EuclideanHalfSpace m ≃ₘ^k⟮𝓡∂ m, 𝓡∂ m⟯ EuclideanHalfSpace m where
  toFun := smulMap hε
  invFun := smulMap (inv_pos.2 hε)
  left_inv x := Subtype.ext (inv_smul_smul₀ hε.ne' x.1)
  right_inv x := Subtype.ext (smul_inv_smul₀ hε.ne' x.1)
  contMDiff_toFun := contMDiff_smulMap hε
  contMDiff_invFun := contMDiff_smulMap (inv_pos.2 hε)

/-- The scaling diffeomorphism multiplies the underlying vector by `ε`. -/
@[simp]
theorem coe_smulDiffeomorph_apply (hε : 0 < ε) (x : EuclideanHalfSpace m) :
    (smulDiffeomorph m k hε x).1 = ε • x.1 := (rfl)

/-- The inverse of the scaling diffeomorphism multiplies the underlying vector by `ε⁻¹`. -/
@[simp]
theorem coe_smulDiffeomorph_symm_apply (hε : 0 < ε) (x : EuclideanHalfSpace m) :
    ((smulDiffeomorph m k hε).symm x).1 = ε⁻¹ • x.1 := (rfl)

private theorem smul_mem_normalIio (hε : 0 < ε) (hε1 : ε ≤ 1) (t : normalIioOpens 1) :
    smulDiffeomorph 1 ⊤ hε (t : EuclideanHalfSpace 1) ∈ normalIioOpens 1 := by
  rw [mem_normalIioOpens, coe_smulDiffeomorph_apply, PiLp.smul_apply, smul_eq_mul]
  exact (mul_le_of_le_one_left t.1.2 hε1).trans_lt (mem_normalIioOpens.1 t.2)

/-- **Rescaling the depth of a collar.** For `0 < ε ≤ 1`, multiplication by `ε` maps the depth
parameter `[0, 1)` into itself. -/
def normalIioOpensScale (hε : 0 < ε) (hε1 : ε ≤ 1) : normalIioOpens 1 → normalIioOpens 1 :=
  fun t ↦
    ⟨smulDiffeomorph 1 ⊤ hε (t : EuclideanHalfSpace 1), smul_mem_normalIio hε hε1 t⟩

variable (hε : 0 < ε) (hε1 : ε ≤ 1)

/-- The depth rescaling multiplies the depth by `ε`. -/
@[simp]
theorem coe_normalIioOpensScale_apply (t : normalIioOpens 1) :
    ((normalIioOpensScale hε hε1 t : EuclideanHalfSpace 1).1 : EuclideanSpace ℝ (Fin 1)) =
      ε • (t : EuclideanHalfSpace 1).1 := (rfl)

/-- The depth rescaling is a `C^k` local diffeomorphism. -/
theorem isLocalDiffeomorph_normalIioOpensScale :
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) k (normalIioOpensScale hε hε1) := fun t ↦ by
  -- Read in the ambient half-space, the rescaling is the scaling diffeomorphism.
  have hval : IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) k
      (Subtype.val ∘ normalIioOpensScale hε hε1) t :=
    (isLocalDiffeomorph_subtype_val t).comp _ _ ((smulDiffeomorph 1 k hε).isLocalDiffeomorph _)
  exact hval.of_comp_left (isLocalDiffeomorph_subtype_val _)
    (((smulDiffeomorph 1 ⊤ hε).continuous.comp continuous_subtype_val).subtype_mk
      (smul_mem_normalIio hε hε1)).continuousAt

/-- The depth rescaling is injective. -/
theorem injective_normalIioOpensScale : Injective (normalIioOpensScale hε hε1) := fun _ _ h ↦
  Subtype.ext ((smulDiffeomorph 1 ⊤ hε).injective (congrArg Subtype.val h))

/-- The depth rescaling fixes depth zero. -/
@[simp]
theorem normalIioOpensScale_zero :
    normalIioOpensScale hε hε1 (normalIioOpensZero one_pos) = normalIioOpensZero one_pos := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_normalIioOpensScale_apply, coe_normalIioOpensZero]
  ext i
  fin_cases i
  simp [val_zero_apply]

/-- The image of the depth rescaling is the segment `[0, ε)`. -/
theorem range_normalIioOpensScale :
    range (normalIioOpensScale hε hε1) =
      {t : normalIioOpens 1 | (t : EuclideanHalfSpace 1).1 0 < ε} := by
  ext t
  refine ⟨?_, fun ht ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    change ε * (s : EuclideanHalfSpace 1).1 0 < ε
    exact mul_lt_of_lt_one_right hε (mem_normalIioOpens.1 s.2)
  · let s := (smulDiffeomorph 1 ⊤ hε).symm t
    have hs : s ∈ normalIioOpens 1 := by
      rw [mem_normalIioOpens, coe_smulDiffeomorph_symm_apply, PiLp.smul_apply, smul_eq_mul,
        inv_mul_lt_one₀ hε]
      exact ht
    refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
    exact (smulDiffeomorph 1 ⊤ hε).apply_symm_apply t

/-- Rescaling the depth by `1` is the identity. -/
@[simp]
theorem normalIioOpensScale_one : normalIioOpensScale one_pos le_rfl = id :=
  funext fun _ ↦ Subtype.ext (Subtype.ext (one_smul ℝ _))

end EuclideanHalfSpace

open _root_.TauCeti.EuclideanHalfSpace

namespace SmoothCollar

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  (c : SmoothCollar n k M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)

/-- **Shrinking a smooth collar.** For `0 < ε ≤ 1`, the restriction of a smooth collar `c` to
`∂M × [0, ε)`, precomposed with `(x, t) ↦ (x, ε t)`, is a smooth collar. -/
def shrink : SmoothCollar n k M :=
  c.reparam (normalIioOpensScale hε hε1) (isLocalDiffeomorph_normalIioOpensScale hε hε1)
    (injective_normalIioOpensScale hε hε1) (normalIioOpensScale_zero hε hε1)

/-- The shrunk collar evaluates the collar at `ε` times the depth. -/
@[simp]
theorem shrink_apply (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) :
    c.shrink hε hε1 p = c (p.1, normalIioOpensScale hε hε1 p.2) :=
  c.reparam_apply _ _ _ p

/-- The image of the shrunk collar is the image of `∂M × [0, ε)` under the collar. -/
theorem range_shrink :
    range (c.shrink hε hε1) = c '' {p | (p.2 : EuclideanHalfSpace 1).1 0 < ε} := by
  ext y
  simp only [mem_range, shrink_apply, mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1, normalIioOpensScale hε hε1 p.2), ?_, rfl⟩
    have hp : normalIioOpensScale hε hε1 p.2 ∈ range (normalIioOpensScale hε hε1) :=
      mem_range_self p.2
    rwa [range_normalIioOpensScale] at hp
  · rintro ⟨p, hp, rfl⟩
    have hp' : p.2 ∈ range (normalIioOpensScale hε hε1) := by
      rw [range_normalIioOpensScale]
      exact hp
    obtain ⟨s, hs⟩ := hp'
    exact ⟨(p.1, s), by rw [hs]⟩

/-- The image of the shrunk collar is contained in the image of the collar. -/
theorem opensRange_shrink_le : (c.shrink hε hε1).opensRange ≤ c.opensRange :=
  c.opensRange_reparam_le _ _ _

/-- Shrinking a collar by `1` gives the same collar. -/
@[simp]
theorem shrink_one : c.shrink one_pos le_rfl = c :=
  ext fun p ↦ by simp

end SmoothCollar

end TauCeti
