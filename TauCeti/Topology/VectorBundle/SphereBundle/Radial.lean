/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Radial
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Radial metric-change homeomorphisms of disc and sphere bundles

Any continuous bundle isomorphism `Φ : E₁ ≃ E₂` between real vector bundles over `B` with
continuous fibre norms induces, by radial rescaling `v ↦ (‖v‖₁ / ‖Φ v‖₂) • Φ v`
(`TauCeti.radialBundleMap`), a homeomorphism of unit sphere bundles
(`TauCeti.sphereBundleRadialHomeomorph`, in arbitrary rank) and, when `F₁` and `F₂` are
finite-dimensional, a homeomorphism of unit disc bundles (`TauCeti.discBundleRadialHomeomorph`)
commuting with the inclusion `S(E) → D(E)` (`TauCeti.discBundleRadialHomeomorph_comp_inclusion`).

In particular, the homeomorphism type of the disc–sphere pair `(D(E), S(E))` over `B` is
independent of the choice of continuous fibre metric.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2 (Euclidean metrics on vector bundles), §12, and §18.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (radial rescaling and metric independence of
  disc and sphere bundles).
-/

public section

noncomputable section

open Bundle Set Topology

namespace TauCeti

universe u

variable {B : Type u} [TopologicalSpace B]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B → Type u} {E₂ : B → Type u}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

/-- **Metric-change radial homeomorphism of unit disc bundles.** -/
def discBundleRadialHomeomorph [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    discBundle F₁ E₁ ≃ₜ discBundle F₂ E₂ :=
  (radialBundleHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).subtype fun v ↦ by simp

@[simp]
theorem coe_discBundleRadialHomeomorph_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (v : discBundle F₁ E₁) :
    (discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v : TotalSpace F₂ E₂) =
      radialBundleMap F₁ F₂ Φ v.val :=
  radialBundleHomeomorph_apply F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v.val

@[simp]
theorem coe_discBundleRadialHomeomorph_symm_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (w : discBundle F₂ E₂) :
    ((discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).symm w : TotalSpace F₁ E₁) =
      radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val :=
  radialBundleHomeomorph_symm_apply F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm w.val

omit [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] in
private lemma continuous_radialBundleMap_sphere (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)) :
    Continuous fun v : sphereBundle F₁ E₁ ↦ radialBundleMap F₁ F₂ Φ v.val := by
  have hΦ' : Continuous fun v : sphereBundle F₁ E₁ ↦
      TotalSpace.mk' F₂ v.val.proj (Φ v.val.proj v.val.snd) := hΦ.comp continuous_subtypeVal
  refine (Continuous.smul_totalSpace (𝕜 := ℝ) ?_ hΦ').congr fun v ↦
    (radialBundleMap_mk F₁ F₂ Φ v.val.proj v.val.snd).symm
  exact (hnorm₁.comp continuous_subtypeVal).div (hnorm₂.comp hΦ') fun v ↦
    norm_ne_zero_iff.2 <| (map_ne_zero_iff _ (Φ v.val.proj).injective).2 <|
      norm_ne_zero_iff.1 ((mem_sphereBundle.1 v.property).symm ▸ one_ne_zero)

-- Unlike `discBundleRadialHomeomorph`, vectors on `sphereBundle` stay away from the zero section,
-- so continuity holds without `FiniteDimensional` and does not factor via `radialBundleHomeomorph`.
/-- **Metric-change radial homeomorphism of unit sphere bundles.** Holds in arbitrary rank (no
`FiniteDimensional` hypothesis is needed since unit vectors stay away from the zero section). -/
def sphereBundleRadialHomeomorph (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    sphereBundle F₁ E₁ ≃ₜ sphereBundle F₂ E₂ where
  toFun v := ⟨radialBundleMap F₁ F₂ Φ v.val,
    mem_sphereBundle.2 ((norm_radialBundleMap F₁ F₂ Φ v.val).trans (mem_sphereBundle.1 v.property))⟩
  invFun w := ⟨radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val,
    mem_sphereBundle.2 ((norm_radialBundleMap F₂ F₁ _ w.val).trans (mem_sphereBundle.1 w.property))⟩
  left_inv v := Subtype.ext (radialBundleMap_symm_radialBundleMap F₁ F₂ Φ v.val)
  right_inv w := Subtype.ext (radialBundleMap_symm_radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val)
  continuous_toFun := (continuous_radialBundleMap_sphere F₁ F₂ Φ hnorm₁ hnorm₂ hΦ).subtype_mk _
  continuous_invFun :=
    (continuous_radialBundleMap_sphere F₂ F₁ (fun b ↦ (Φ b).symm) hnorm₂ hnorm₁
      hΦ_symm).subtype_mk _

@[simp]
theorem coe_sphereBundleRadialHomeomorph_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (v : sphereBundle F₁ E₁) :
    (sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v : TotalSpace F₂ E₂) =
      radialBundleMap F₁ F₂ Φ v.val :=
  (rfl)

@[simp]
theorem coe_sphereBundleRadialHomeomorph_symm_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (w : sphereBundle F₂ E₂) :
    ((sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).symm w : TotalSpace F₁ E₁) =
      radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val :=
  (rfl)

/-- The radial homeomorphisms on the unit disc and unit sphere bundles commute with the inclusion
`S(E) → D(E)`, giving a map of pairs `(D(E₁), S(E₁)) → (D(E₂), S(E₂))`. -/
theorem discBundleRadialHomeomorph_comp_inclusion
    [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    (ContinuousMap.mk (discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm)
          (discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).continuous).comp
        (ContinuousMap.inclusion (sphereBundle_subset_discBundle F₁ E₁)) =
      (ContinuousMap.inclusion (sphereBundle_subset_discBundle F₂ E₂)).comp
        (ContinuousMap.mk (sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm)
          (sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).continuous) := by
  refine ContinuousMap.ext fun v ↦ Subtype.ext ?_
  simp

end TauCeti
