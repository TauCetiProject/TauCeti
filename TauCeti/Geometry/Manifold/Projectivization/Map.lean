/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.LinearAlgebra.Projectivization.Action
public import TauCeti.Geometry.Manifold.Instances.Projectivization

/-!
# Linear maps of projective spaces are analytic

An injective linear map `f : 𝕜ᵐ⁺¹ → 𝕜ⁿ⁺¹` induces the map `Projectivization.map f` from
`ℙ 𝕜 (Fin (m + 1) → 𝕜)` to `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, sending the line `[v]` to `[f v]`. Read in
the standard affine charts at the coordinates `i` and `j`, it sends `z` to the homogeneous ratios
`(f w (j.succAbove k) / f w j)_k` of the vector `f w`, where `w = Fin.insertNth i 1 z`
(`Projectivization.affineChart_map_affineChart_symm`). These ratios are analytic where the
denominator does not vanish, so `Projectivization.map f` is `C^r` for every `r`, including the
analytic order `ω`, for the atlases of `Projectivization.instChartedSpace`
(`Projectivization.contMDiff_map`).

This covers the linear inclusions `ℙᵐ → ℙⁿ`, the coordinate permutations and, more generally,
the projective linear transformations. A linear equivalence induces a `C^r` diffeomorphism
(`Projectivization.mapDiffeomorph`), and every group acting linearly on `𝕜ⁿ⁺¹`, such as the
general linear group, acts on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` by analytic maps
(`Projectivization.instContMDiffConstSMul`); so does the projective general linear group
`PGL(Fin (n + 1), 𝕜)` (`Projectivization.instContMDiffConstSMulPGL`). Over `ℂ` these are the
holomorphic maps of complex projective spaces induced by linear maps, and the projective linear
transformations act on `ℂℙⁿ` by biholomorphisms.

## Main declarations

* `Projectivization.contMDiff_map`: the map induced by an injective linear map is `C^r` for every
  `r`.
* `Projectivization.mapDiffeomorph`: the `C^r` diffeomorphism induced by a linear equivalence.
* `Projectivization.instContMDiffConstSMul`, `Projectivization.instContMDiffConstSMulPGL`: linear
  group actions on projective space are by analytic maps.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public section

open Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization MatrixGroups

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n : ℕ}

/-! ### Analyticity -/

/-- The map of projective spaces induced by an injective linear map is `C^r` for every `r`; for
`r = ω` it is analytic. Over `ℂ` it is holomorphic. -/
theorem contMDiff_map (f : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜)
    (hf : Function.Injective f) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf) := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  obtain ⟨j, hj⟩ := exists_mem_affineOpen (map f hf x)
  let w : (Fin m → 𝕜) → Fin (n + 1) → 𝕜 := fun z ↦ f (Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z)
  have hw : ContDiff 𝕜 r w :=
    (⟨f, LinearMap.continuous_on_pi f⟩ : (Fin (m + 1) → 𝕜) →L[𝕜] Fin (n + 1) → 𝕜).contDiff.comp
      ((contDiff_const (c := (1 : 𝕜))).finInsertNth (F := fun _ ↦ 𝕜) i contDiff_id)
  -- In the charts at `i` and `j`, the map is given by the homogeneous ratios of `w z`.
  have hratio : ContDiffOn 𝕜 r (fun z k ↦ w z (j.succAbove k) / w z j) {z | w z j ≠ 0} :=
    contDiffOn_pi.2 fun k ↦ (contDiff_pi.1 hw _).contDiffOn.div (contDiff_pi.1 hw j).contDiffOn
      fun _ hz ↦ hz
  have hcont : Continuous (map f hf) := continuous_map hf (LinearMap.continuous_on_pi f)
  have hs : IsOpen (affineOpen i ∩ map f hf ⁻¹' affineOpen j) :=
    (isOpen_affineOpen i).inter ((isOpen_affineOpen j).preimage hcont)
  refine ContMDiffOn.contMDiffAt ?_ (hs.mem_nhds ⟨hi, hj⟩)
  refine ((contMDiff_affineChart_symm j r).comp_contMDiffOn (hratio.contMDiffOn.comp
    ((contMDiffOn_affineChart i r).mono inter_subset_left) ?_)).congr ?_
  all_goals
    rintro y ⟨hyi, hyj⟩
    -- Every point of the affine open at `i` is `[Fin.insertNth i 1 z]` for its chart value `z`.
    obtain ⟨z, rfl⟩ : ∃ z, (affineChart i).symm z = y :=
      ⟨_, (affineChart i).left_inv (by simpa using hyi)⟩
  · rw [mem_preimage, (affineChart i).right_inv (by simp)]
    exact (map_affineChart_symm_mem_affineOpen_iff f hf i j z).1 hyj
  · rw [Function.comp_apply, Function.comp_apply, (affineChart i).right_inv (by simp),
      ← affineChart_map_affineChart_symm, (affineChart j).left_inv (by simpa using hyj)]

/-! ### Diffeomorphisms induced by linear equivalences -/

/-- A linear equivalence `e : 𝕜ᵐ⁺¹ ≃ 𝕜ⁿ⁺¹` induces a `C^r` diffeomorphism of projective spaces,
for every `r`, sending `[v]` to `[e v]`. Over `ℂ` and for `r = ω` it is a biholomorphism. -/
def mapDiffeomorph (e : (Fin (m + 1) → 𝕜) ≃ₗ[𝕜] Fin (n + 1) → 𝕜) (r : ℕ∞ω) :
    ℙ 𝕜 (Fin (m + 1) → 𝕜) ≃ₘ^r⟮𝓘(𝕜, Fin m → 𝕜), 𝓘(𝕜, Fin n → 𝕜)⟯ ℙ 𝕜 (Fin (n + 1) → 𝕜) where
  toFun := map (e : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) e.injective
  invFun := map (e.symm : (Fin (n + 1) → 𝕜) →ₗ[𝕜] Fin (m + 1) → 𝕜) e.symm.injective
  left_inv := ind fun v hv ↦ by simp [map_mk]
  right_inv := ind fun v hv ↦ by simp [map_mk]
  contMDiff_toFun := contMDiff_map _ e.injective r
  contMDiff_invFun := contMDiff_map _ e.symm.injective r

@[simp]
theorem coe_mapDiffeomorph (e : (Fin (m + 1) → 𝕜) ≃ₗ[𝕜] Fin (n + 1) → 𝕜) (r : ℕ∞ω) :
    ⇑(mapDiffeomorph e r) = map (e : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) e.injective :=
  (rfl)

@[simp]
theorem mapDiffeomorph_symm (e : (Fin (m + 1) → 𝕜) ≃ₗ[𝕜] Fin (n + 1) → 𝕜) (r : ℕ∞ω) :
    (mapDiffeomorph e r).symm = mapDiffeomorph e.symm r :=
  (rfl)

/-! ### Linear group actions -/

/-- A group acting linearly on `𝕜ⁿ⁺¹`, such as the general linear group, its matrix form or the
special linear group, acts on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` by `C^r` maps for every `r`; each element
therefore acts by a diffeomorphism, `Diffeomorph.constSmul`. -/
instance instContMDiffConstSMul {G : Type*} [Group G] [DistribMulAction G (Fin (n + 1) → 𝕜)]
    [SMulCommClass G 𝕜 (Fin (n + 1) → 𝕜)] (r : ℕ∞ω) :
    ContMDiffConstSMul 𝓘(𝕜, Fin n → 𝕜) r G (ℙ 𝕜 (Fin (n + 1) → 𝕜)) where
  contMDiff_const_smul g := by
    let e := DistribMulAction.toLinearEquiv 𝕜 (Fin (n + 1) → 𝕜) g
    have h : (fun x : ℙ 𝕜 (Fin (n + 1) → 𝕜) ↦ g • x) =
        map (e : (Fin (n + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) e.injective := by
      funext x
      induction x using ind with | h v hv => simp [e, map_mk]
    rw [h]
    exact contMDiff_map _ e.injective r

/-- The projective general linear group `PGL(Fin (n + 1), 𝕜)` acts on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` by
`C^r` maps for every `r`. Over `ℂ` the projective linear transformations are biholomorphisms of
`ℂℙⁿ`. -/
instance instContMDiffConstSMulPGL (r : ℕ∞ω) :
    ContMDiffConstSMul 𝓘(𝕜, Fin n → 𝕜) r PGL(Fin (n + 1), 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) where
  contMDiff_const_smul g := by
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    simpa only [Matrix.ProjGenLinGroup.mk_smul] using
      contMDiff_const_smul (I := 𝓘(𝕜, Fin n → 𝕜)) (n := r) g

end Projectivization
