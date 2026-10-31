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
# Maps of projective spaces given in homogeneous coordinates are analytic

A map `f` from `ℙ 𝕜 (Fin (m + 1) → 𝕜)` to `ℙ 𝕜 (Fin (n + 1) → 𝕜)` which sends `[v]` to `[F v]`
for a map `F` of homogeneous coordinates is, read in the standard affine charts at the coordinates
`i` and `j`, the map sending `z` to the homogeneous ratios `(F w (j.succAbove k) / F w j)_k` of
the vector `F w`, where `w = Fin.insertNth i 1 z`. These ratios are `C^r` where the denominator
does not vanish whenever `F` is `C^r` on the nonzero vectors, so `f` is `C^r` for the atlases of
`Projectivization.instChartedSpace` (`Projectivization.contMDiff_of_contDiffOn`), and likewise on
an open set where it is given by such an `F` (`Projectivization.contMDiffOn_of_contDiffOn`). This
includes the analytic order `ω`. Over `ℂ`, with `F` given by homogeneous polynomials of a common
degree without common nonzero zero, these are holomorphic maps of complex projective spaces.

In particular, an injective linear map `f : 𝕜ᵐ⁺¹ → 𝕜ⁿ⁺¹` induces a `C^r` map
`Projectivization.map f`, sending the line `[v]` to `[f v]` (`Projectivization.contMDiff_map`).
This covers the linear inclusions `ℙᵐ → ℙⁿ`, the coordinate permutations and, more generally,
the projective linear transformations. A linear equivalence induces a `C^r` diffeomorphism
(`Projectivization.mapDiffeomorph`), and every group acting linearly on `𝕜ⁿ⁺¹`, such as the
general linear group, acts on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` by analytic maps
(`Projectivization.instContMDiffConstSMul`); so does the projective general linear group
`PGL(Fin (n + 1), 𝕜)` (`Projectivization.instContMDiffConstSMulPGL`). Over `ℂ` these are the
holomorphic maps of complex projective spaces induced by linear maps, and the projective linear
transformations act on `ℂℙⁿ` by biholomorphisms.

A linear map `G : 𝕜ᵐ⁺¹ → 𝕜ⁿ⁺¹` which is not injective still induces the map `[v] ↦ [G v]` on the
open set where `G` does not vanish, and it is `C^r` there
(`Projectivization.contMDiffOn_linearProjection`).

## Main declarations

* `Projectivization.contMDiffOn_of_contDiffOn`, `Projectivization.contMDiff_of_contDiffOn`: a map
  of projective spaces given by a `C^r` map of homogeneous coordinates is `C^r`.
* `Projectivization.contMDiff_map`: the map induced by an injective linear map is `C^r` for every
  `r`.
* `Projectivization.contMDiffOn_linearProjection`: the map induced by a linear map is `C^r` where
  the linear map does not vanish.
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

/-- A map of projective spaces sending `[v]` to `[F v]` on an open set `s`, for a map `F` of
homogeneous coordinates which is `C^r` on the nonzero vectors spanning points of `s` and does not
vanish there, is `C^r` on `s`; for `r = ω` it is analytic there. -/
theorem contMDiffOn_of_contDiffOn {f : ℙ 𝕜 (Fin (m + 1) → 𝕜) → ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    {F : (Fin (m + 1) → 𝕜) → Fin (n + 1) → 𝕜} {s : Set (ℙ 𝕜 (Fin (m + 1) → 𝕜))} {r : ℕ∞ω}
    (hs : IsOpen s) (hF : ContDiffOn 𝕜 r F {v | ∃ hv : v ≠ 0, mk 𝕜 v hv ∈ s})
    (hF₀ : ∀ v (hv : v ≠ 0), mk 𝕜 v hv ∈ s → F v ≠ 0)
    (hf : ∀ v (hv : v ≠ 0) (hvs : mk 𝕜 v hv ∈ s), f (mk 𝕜 v hv) = mk 𝕜 (F v) (hF₀ v hv hvs)) :
    ContMDiffOn 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r f s := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  obtain ⟨j, hj⟩ := exists_mem_affineOpen (f x)
  let w : (Fin m → 𝕜) → Fin (n + 1) → 𝕜 := fun z ↦ F (Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z)
  have hw : ContDiffOn 𝕜 r w ((affineChart i).symm ⁻¹' s) :=
    hF.comp ((contDiff_const (c := (1 : 𝕜))).finInsertNth (F := fun _ ↦ 𝕜) i
      contDiff_id).contDiffOn fun z hz ↦
        ⟨Fin.insertNth_one_ne_zero i z, by rwa [mem_preimage, affineChart_symm_apply] at hz⟩
  -- In the charts at `i` and `j`, the map is given by the homogeneous ratios of `w z`, on the
  -- open set `t` of chart values of points of `s` whose image lies in the affine open at `j`.
  let t := (affineChart i).symm ⁻¹' s ∩ w ⁻¹' {y | y j ≠ 0}
  have ht : IsOpen t := hw.continuousOn.isOpen_inter_preimage
    (hs.preimage (continuous_affineChart_symm i)) (isOpen_ne_fun (continuous_apply j)
      continuous_const)
  have hratio : ContDiffOn 𝕜 r (fun z k ↦ w z (j.succAbove k) / w z j) t :=
    contDiffOn_pi.2 fun k ↦ ((contDiffOn_pi.1 hw _).mono inter_subset_left).div
      ((contDiffOn_pi.1 hw j).mono inter_subset_left) fun _ hz ↦ hz.2
  have hu : IsOpen (affineOpen i ∩ affineChart i ⁻¹' t) :=
    (continuousOn_affineChart i).isOpen_inter_preimage (isOpen_affineOpen i) ht
  -- Every point `y` of the affine open at `i` is `[Fin.insertNth i 1 z]` for its chart value `z`.
  have hchart {y} (hy : y ∈ affineOpen i) : (affineChart (K := 𝕜) i).symm (affineChart i y) = y :=
    (affineChart i).left_inv (by simpa using hy)
  have hxs : (affineChart i).symm (affineChart i x) ∈ s := by rwa [hchart hi]
  have hxu : x ∈ affineOpen i ∩ affineChart i ⁻¹' t := by
    refine ⟨hi, hxs, (apply_affineChart_symm_mem_affineOpen_iff i j _ _
      (hf _ _ (by rwa [affineChart_symm_apply] at hxs))).1 ?_⟩
    rwa [hchart hi]
  refine (ContMDiffOn.contMDiffAt ?_ (hu.mem_nhds hxu)).contMDiffWithinAt
  refine ((contMDiff_affineChart_symm j r).comp_contMDiffOn (hratio.contMDiffOn.comp
    ((contMDiffOn_affineChart i r).mono inter_subset_left) fun _ hy ↦ hy.2)).congr ?_
  rintro y ⟨hyi, hys, hyj⟩
  obtain ⟨z, rfl⟩ : ∃ z, (affineChart i).symm z = y := ⟨_, hchart hyi⟩
  rw [mem_preimage, (affineChart i).right_inv (by simp), affineChart_symm_apply] at hys
  rw [mem_preimage, (affineChart i).right_inv (by simp)] at hyj
  have hzj := (apply_affineChart_symm_mem_affineOpen_iff i j _ _ (hf _ _ hys)).2 hyj
  rw [Function.comp_apply, Function.comp_apply, (affineChart i).right_inv (by simp),
    ← affineChart_apply_affineChart_symm i j _ _ (hf _ _ hys),
    (affineChart j).left_inv (by rwa [affineChart_source])]

/-- A map of projective spaces sending `[v]` to `[F v]`, for a map `F` of homogeneous coordinates
which is `C^r` on the nonzero vectors and does not vanish there, is `C^r`; for `r = ω` it is
analytic. Over `ℂ` and for polynomial `F` this is the holomorphy of maps of projective spaces given
by homogeneous polynomials of a common degree without common nonzero zero. -/
theorem contMDiff_of_contDiffOn {f : ℙ 𝕜 (Fin (m + 1) → 𝕜) → ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    {F : (Fin (m + 1) → 𝕜) → Fin (n + 1) → 𝕜} {r : ℕ∞ω} (hF : ContDiffOn 𝕜 r F {v | v ≠ 0})
    (hF₀ : ∀ v, v ≠ 0 → F v ≠ 0) (hf : ∀ v (hv : v ≠ 0), f (mk 𝕜 v hv) = mk 𝕜 (F v) (hF₀ v hv)) :
    ContMDiff 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r f := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_of_contDiffOn isOpen_univ (hF.mono fun v ⟨hv, _⟩ ↦ hv)
    (fun v hv _ ↦ hF₀ v hv) fun v hv _ ↦ hf v hv

/-- The map of projective spaces induced by an injective linear map is `C^r` for every `r`; for
`r = ω` it is analytic. Over `ℂ` it is holomorphic. -/
theorem contMDiff_map (f : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜)
    (hf : Function.Injective f) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf) :=
  contMDiff_of_contDiffOn
    (⟨f, LinearMap.continuous_on_pi f⟩ : (Fin (m + 1) → 𝕜) →L[𝕜]
      Fin (n + 1) → 𝕜).contDiff.contDiffOn
    (fun _ hv ↦ (map_ne_zero_iff f hf).2 hv) fun _ _ ↦ map_mk _ _ _ _

/-- The map `[w] ↦ [G w]` induced by a linear map `G` is `C^r` for every `r` on the open set
`Projectivization.linearProjectionDomain G` where `G` does not vanish; for `r = ω` it is analytic
there. -/
theorem contMDiffOn_linearProjection (G : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (linearProjection G)
      (linearProjectionDomain G) :=
  contMDiffOn_of_contDiffOn (isOpen_linearProjectionDomain (LinearMap.continuous_on_pi G))
    (⟨G, LinearMap.continuous_on_pi G⟩ : (Fin (m + 1) → 𝕜) →L[𝕜]
      Fin (n + 1) → 𝕜).contDiff.contDiffOn
    (fun _ hv h ↦ (mk_mem_linearProjectionDomain_iff G hv).1 h)
    fun _ hv _ ↦ linearProjection_mk G hv _

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
