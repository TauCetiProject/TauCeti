/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Shrinking a smooth collar

A smooth collar `c : ∂M × [0, 1) → M` can be made thinner: for `0 < ε ≤ 1`, restricting `c` to
`∂M × [0, ε)` and precomposing with `(x, t) ↦ (x, ε t)` gives again a smooth collar, whose image
is the part of the image of `c` of depth less than `ε`. When the boundary is compact, gluing
constructions shrink collars this way to fit them inside a prescribed neighbourhood of the
boundary.

The depth rescaling is the restriction of the scaling diffeomorphism
`TauCeti.EuclideanHalfSpace.smulDiffeomorph` of the half-space model, and the shrunk collar is
the reparametrization `TauCeti.SmoothCollar.reparam` along it.

## Main definitions

* `TauCeti.EuclideanHalfSpace.prodScaleDiffeomorph`: positive variable-depth scaling over any
  charted base, at arbitrary regularity.
* `TauCeti.EuclideanHalfSpace.normalIioOpensScale`: multiplication by `ε ∈ (0, 1]`, as a self-map
  of the depth parameter `[0, 1)`.
* `TauCeti.SmoothCollar.shrink`: the collar `(x, t) ↦ c (x, ε t)`.

## Main results

* `TauCeti.EuclideanHalfSpace.isLocalDiffeomorph_normalIioOpensScale`: the depth rescaling is a
  local diffeomorphism.
* `TauCeti.EuclideanHalfSpace.range_normalIioOpensScale`: its image is `[0, ε)`.
* `TauCeti.SmoothCollar.range_shrink`: the image of the shrunk collar is the image of `∂M × [0, ε)`.
* `TauCeti.SmoothCollar.shrink_one`: shrinking by `1` does nothing.
* `TauCeti.SmoothCollar.shrink_shrink`: shrinking by `ε` and then by `δ` is shrinking by `ε δ`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

section ProdScale

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N] {k : WithTop ℕ∞}

/-- Scale each half-line fibre by a positive `C^k` function on an arbitrary charted space. -/
def prodScaleDiffeomorph (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) :
    (N × EuclideanHalfSpace 1) ≃ₘ^k⟮I.prod (𝓡∂ 1), I.prod (𝓡∂ 1)⟯ (N × EuclideanHalfSpace 1) := by
  let scale (r : N → ℝ) (p : N × EuclideanHalfSpace 1) := (p.1, normalRay (r p.1 * p.2.val 0))
  have hscale (r : N → ℝ) (hr : ContMDiff I 𝓘(ℝ) k r) (hr₀ : ∀ x, 0 ≤ r x) :
      ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) k (scale r) := by
    have htime : ContMDiff (𝓡∂ 1) 𝓘(ℝ) k (fun t : EuclideanHalfSpace 1 ↦ t.val 0) :=
      (EuclideanSpace.proj (0 : Fin 1)).contDiff.contMDiff.comp (𝓡∂ 1).contMDiff
    exact contMDiff_fst.prodMk <| ((hr.comp contMDiff_fst).mul (htime.comp contMDiff_snd)).normalRay
      fun p ↦ mul_nonneg (hr₀ p.1) p.2.property
  have hinv (r s : N → ℝ) (hr₀ : ∀ x, 0 ≤ r x) (hrs : ∀ x, s x * r x = 1)
      (p : N × EuclideanHalfSpace 1) : scale s (scale r p) = p := by
    refine Prod.ext rfl ?_
    -- Expose only the two applications of the local scale map.
    change normalRay (s p.1 * (normalRay (r p.1 * p.2.val 0)).val 0) = p.2
    rw [normalRay_coe_apply_of_nonneg (mul_nonneg (hr₀ _) p.2.property), ← mul_assoc,
      hrs, one_mul, normalRay_normalCoord]
  refine
    { toFun := scale δ
      invFun := scale (fun x ↦ (δ x)⁻¹)
      left_inv := hinv δ _ (fun x ↦ (hpos x).le) (fun x ↦ inv_mul_cancel₀ (hpos x).ne')
      right_inv := hinv _ δ (fun x ↦ inv_nonneg.mpr (hpos x).le)
        (fun x ↦ mul_inv_cancel₀ (hpos x).ne')
      contMDiff_toFun := hscale δ hδ (fun x ↦ (hpos x).le)
      contMDiff_invFun := hscale _ (hδ.inv₀ fun x ↦ (hpos x).ne')
        (fun x ↦ inv_nonneg.mpr (hpos x).le) }

-- Keep the point equations out of simp so bundled inverse cancellation still applies.
-- The projection equations below provide the coordinate simp rules.

/-- Fibrewise scaling preserves the base and multiplies the normal coordinate by the depth. -/
theorem prodScaleDiffeomorph_apply (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) (p : N × EuclideanHalfSpace 1) :
    prodScaleDiffeomorph δ hδ hpos p = (p.1, normalRay (δ p.1 * p.2.val 0)) :=
  -- Read the defining map through the bundled diffeomorphism coercion.
  (rfl)

/-- The inverse fibrewise scaling divides the normal coordinate by the depth. -/
theorem prodScaleDiffeomorph_symm_apply (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) (p : N × EuclideanHalfSpace 1) :
    (prodScaleDiffeomorph δ hδ hpos).symm p = (p.1, normalRay ((δ p.1)⁻¹ * p.2.val 0)) :=
  -- Read the defining map through the bundled diffeomorphism coercion.
  (rfl)

/-- Fibrewise scaling fixes the base coordinate. -/
@[simp]
theorem prodScaleDiffeomorph_fst (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) (p : N × EuclideanHalfSpace 1) :
    (prodScaleDiffeomorph δ hδ hpos p).1 = p.1 := by
  rw [prodScaleDiffeomorph_apply]

/-- Fibrewise scaling multiplies the nonnegative normal coordinate by the depth. -/
@[simp]
theorem prodScaleDiffeomorph_normalCoord (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) (p : N × EuclideanHalfSpace 1) :
    (prodScaleDiffeomorph δ hδ hpos p).2.val 0 = δ p.1 * p.2.val 0 := by
  rw [prodScaleDiffeomorph_apply, normalRay_coe_apply_of_nonneg
    (mul_nonneg (hpos _).le p.2.property)]

/-- Inverse fibrewise scaling fixes the base coordinate. -/
@[simp]
theorem prodScaleDiffeomorph_symm_fst (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) (p : N × EuclideanHalfSpace 1) :
    ((prodScaleDiffeomorph δ hδ hpos).symm p).1 = p.1 := by
  rw [prodScaleDiffeomorph_symm_apply]

/-- Inverse fibrewise scaling divides the nonnegative normal coordinate by the depth. -/
@[simp]
theorem prodScaleDiffeomorph_symm_normalCoord (δ : N → ℝ) (hδ : ContMDiff I 𝓘(ℝ) k δ)
    (hpos : ∀ x, 0 < δ x) (p : N × EuclideanHalfSpace 1) :
    ((prodScaleDiffeomorph δ hδ hpos).symm p).2.val 0 = (δ p.1)⁻¹ * p.2.val 0 := by
  rw [prodScaleDiffeomorph_symm_apply, normalRay_coe_apply_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (hpos _).le) p.2.property)]

end ProdScale

variable {m : ℕ} [NeZero m] {k : WithTop ℕ∞} {ε : ℝ}

private theorem smul_mem_normalIio (hε : 0 < ε) (hε1 : ε ≤ 1) (t : normalIioOpens 1) :
    smulDiffeomorph 1 ⊤ hε (t : EuclideanHalfSpace 1) ∈ normalIioOpens 1 := by
  rw [mem_normalIioOpens, coe_smulDiffeomorph_apply, PiLp.smul_apply, smul_eq_mul]
  exact (mul_le_of_le_one_left t.val.property hε1).trans_lt (mem_normalIioOpens.1 t.property)

/-- **Rescaling the depth of a collar.** For `0 < ε ≤ 1`, multiplication by `ε` maps the depth
parameter `[0, 1)` into itself. -/
def normalIioOpensScale (hε : 0 < ε) (hε1 : ε ≤ 1) : normalIioOpens 1 → normalIioOpens 1 :=
  fun t ↦
    ⟨smulDiffeomorph 1 ⊤ hε (t : EuclideanHalfSpace 1), smul_mem_normalIio hε hε1 t⟩

variable (hε : 0 < ε) (hε1 : ε ≤ 1)

/-- The depth rescaling multiplies the depth by `ε`. -/
@[simp]
theorem coe_normalIioOpensScale_apply (t : normalIioOpens 1) :
    ((normalIioOpensScale hε hε1 t : EuclideanHalfSpace 1).val : EuclideanSpace ℝ (Fin 1)) =
      ε • (t : EuclideanHalfSpace 1).val :=
  coe_smulDiffeomorph_apply (k := ⊤) hε _

variable (k) in
/-- Read in the ambient half-space, the depth rescaling is the `C^k` scaling diffeomorphism, for
every `k`. -/
theorem val_comp_normalIioOpensScale :
    Subtype.val ∘ normalIioOpensScale hε hε1 = smulDiffeomorph 1 k hε ∘ Subtype.val :=
  funext fun t ↦ Subtype.ext
    ((coe_normalIioOpensScale_apply hε hε1 t).trans (coe_smulDiffeomorph_apply hε _).symm)

/-- The depth rescaling is a `C^k` local diffeomorphism. -/
theorem isLocalDiffeomorph_normalIioOpensScale :
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) k (normalIioOpensScale hε hε1) := fun t ↦ by
  have hval : IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) k
      (Subtype.val ∘ normalIioOpensScale hε hε1) t := by
    rw [val_comp_normalIioOpensScale k]
    exact (isLocalDiffeomorph_subtype_val t).comp _ _
      ((smulDiffeomorph 1 k hε).isLocalDiffeomorph _)
  exact hval.of_comp_left (isLocalDiffeomorph_subtype_val _)
    (((smulDiffeomorph 1 ⊤ hε).continuous.comp continuous_subtypeVal).subtype_mk
      (smul_mem_normalIio hε hε1)).continuousAt

/-- The depth rescaling is injective. -/
theorem normalIioOpensScale_injective : Injective (normalIioOpensScale hε hε1) := fun _ _ h ↦
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
      {t : normalIioOpens 1 | (t : EuclideanHalfSpace 1).val 0 < ε} := by
  ext t
  refine ⟨?_, fun ht ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    rw [mem_ofPred_eq, coe_normalIioOpensScale_apply, PiLp.smul_apply, smul_eq_mul]
    exact mul_lt_of_lt_one_right hε (mem_normalIioOpens.1 s.property)
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
  funext fun t ↦
    Subtype.ext (Subtype.ext ((coe_normalIioOpensScale_apply _ _ t).trans (one_smul ℝ _)))

variable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)

/-- Rescaling the depth by `δ` and then by `ε` is rescaling it by `ε δ`. -/
theorem normalIioOpensScale_comp :
    normalIioOpensScale hε hε1 ∘ normalIioOpensScale hδ hδ1 =
      normalIioOpensScale (mul_pos hε hδ) ((mul_le_of_le_one_left hδ.le hε1).trans hδ1) :=
  funext fun t ↦ Subtype.ext (Subtype.ext (by simp only [comp_apply, coe_normalIioOpensScale_apply,
    smul_smul]))

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
    (normalIioOpensScale_injective hε hε1) (normalIioOpensScale_zero hε hε1)

/-- The shrunk collar evaluates the collar at `ε` times the depth. -/
@[simp]
theorem shrink_apply (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) :
    c.shrink hε hε1 p = c (p.1, normalIioOpensScale hε hε1 p.2) :=
  c.reparam_apply _ _ _ p

/-- The image of the shrunk collar is the image of `∂M × [0, ε)` under the collar. -/
theorem range_shrink :
    range (c.shrink hε hε1) = c '' {p | (p.2 : EuclideanHalfSpace 1).val 0 < ε} := by
  rw [shrink, range_reparam, range_normalIioOpensScale, univ_prod, preimage_ofPred_eq]

/-- The image of the shrunk collar is contained in the image of the collar. -/
theorem opensRange_shrink_le : (c.shrink hε hε1).opensRange ≤ c.opensRange :=
  c.opensRange_reparam_le _ _ _

/-- Shrinking a collar by `1` gives the same collar. -/
@[simp]
theorem shrink_one : c.shrink one_pos le_rfl = c :=
  ext fun p ↦ by simp

/-- Shrinking a collar by `ε` and then by `δ` is shrinking it by `ε δ`. -/
@[simp]
theorem shrink_shrink {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (c.shrink hε hε1).shrink hδ hδ1 =
      c.shrink (mul_pos hε hδ) ((mul_le_of_le_one_left hδ.le hε1).trans hδ1) :=
  ext fun p ↦ by
    simp only [shrink_apply]
    rw [← normalIioOpensScale_comp hε hε1 hδ hδ1, comp_apply]

end SmoothCollar

end TauCeti
