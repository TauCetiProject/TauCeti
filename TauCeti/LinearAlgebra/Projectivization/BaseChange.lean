/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Change of field for projective coordinates

A field embedding acts on projective coordinates by applying it to each entry. The resulting
map is Mathlib's `Projectivization.map` for the coordinatewise semilinear map. This supplies a
common target for compatibility statements between projective coordinate maps over different
fields, without choosing affine charts or representatives.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace RingHom

variable {K L M ι : Type*} [DivisionRing K] [DivisionRing L] [DivisionRing M]

/-- Apply a field embedding to every homogeneous coordinate of a projective point. -/
def mapProjective (f : K →+* L) : ℙ K (ι → K) → ℙ L (ι → L) :=
  Projectivization.map
    { toFun := fun v ↦ f ∘ v
      map_add' := fun v w ↦ funext fun i ↦ f.map_add (v i) (w i)
      map_smul' := fun c v ↦ funext fun i ↦ f.map_mul c (v i) }
    f.injective.comp_left

/-- On a nonzero vector, change of field applies the embedding to every coordinate. -/
@[simp]
theorem mapProjective_mk (f : K →+* L) (v : ι → K) (hv : v ≠ 0) :
    f.mapProjective (Projectivization.mk K v hv) =
      Projectivization.mk L (f ∘ v) (by
        intro h
        apply hv
        funext i
        exact f.injective (by simpa using congrFun h i)) := by
  rw [mapProjective, Projectivization.map_mk]
  rfl

/-- A field embedding does not identify distinct projective coordinate vectors. -/
theorem mapProjective_injective (f : K →+* L) :
    Function.Injective (f.mapProjective : ℙ K (ι → K) → ℙ L (ι → L)) := by
  intro p q
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      simp only [mapProjective_mk, Projectivization.mk_eq_mk_iff']
      rintro ⟨c, hc⟩
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
      have hfj : f (w j) ≠ 0 := (map_ne_zero f).mpr hj
      have hcj := congrFun hc j
      simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hcj
      have he : f (v j / w j) = c := by
        rw [map_div₀, ← hcj, mul_div_cancel_right₀ _ hfj]
      refine ⟨v j / w j, funext fun i ↦ f.injective ?_⟩
      simpa only [Pi.smul_apply, smul_eq_mul, map_mul, he, Function.comp_apply] using congrFun hc i

/-- Changing field along the identity preserves every projective point. -/
@[simp]
theorem mapProjective_id :
    (RingHom.id K).mapProjective = (_root_.id : ℙ K (ι → K) → ℙ K (ι → K)) := by
  funext p
  induction p using Projectivization.ind with
  | h v hv => simp

/-- Successive changes of field agree with the composite embedding. -/
@[simp]
theorem mapProjective_mapProjective (f : K →+* L) (g : L →+* M) (p : ℙ K (ι → K)) :
    g.mapProjective (f.mapProjective p) = (g.comp f).mapProjective p := by
  induction p using Projectivization.ind with
  | h v hv => simp [Function.comp_def]

end RingHom
