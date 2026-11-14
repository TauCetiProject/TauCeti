/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Symmetric wedge product of linear maps on the exterior square

Given two linear maps `f, g : V →ₗ[K] W` over a field `K`, their symmetric wedge product
`exteriorPower.wedgeEnd f g : ⋀[K]^2 V →ₗ[K] ⋀[K]^2 W` acts on decomposable two-vectors by

`(f ∧ g)(u ∧ v) = 2⁻¹ • (f u ∧ g v + g u ∧ f v)`.

When `2 ≠ 0`, `f ∧ f` is the induced exterior-square map `⋀² f`, so `id ∧ id = id` on `⋀[K]^2 V`,
while `f ∧ id` is half the derivation action `exteriorPower.lieMap 2 f`. In Riemannian geometry
this operation expresses the Kulkarni–Nomizu product of symmetric bilinear forms directly as an
endomorphism of the bivector space `⋀[ℝ]^2 V` (following Böhm–Wilking).

## Main definitions

* `exteriorPower.wedgeEnd`: the bilinear map `(f, g) ↦ f ∧ g` sending pairs of linear maps
  `V →ₗ[K] W` to linear maps `⋀[K]^2 V →ₗ[K] ⋀[K]^2 W`.

## Main results

* `exteriorPower.wedgeEnd_apply_ιMulti` and `exteriorPower.wedgeEnd_apply_ιMulti_two`: evaluation
  on decomposable wedges.
* `exteriorPower.wedgeEnd_comm`: symmetry `f ∧ g = g ∧ f`.
* `exteriorPower.wedgeEnd_self` and `exteriorPower.wedgeEnd_id_id`: `f ∧ f = ⋀² f` and
  `id ∧ id = id` when `2 ≠ 0`.
* `exteriorPower.wedgeEnd_id_right` and `exteriorPower.wedgeEnd_id_left`: `f ∧ id` is half the Lie
  derivation `exteriorPower.lieMap 2 f`.
* `exteriorPower.map_comp_wedgeEnd`, `exteriorPower.wedgeEnd_comp_map`, and
  `exteriorPower.conj_map_wedgeEnd`: naturality with respect to `exteriorPower.map 2`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. (2) 167 (2008), 1079–1097, Section 1.
-/

public section

namespace exteriorPower

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The wedge `u ∧ w` is additive in `u`. -/
theorem ιMulti_two_add_left (u u' w : M) :
    ιMulti R 2 ![u + u', w] = ιMulti R 2 ![u, w] + ιMulti R 2 ![u', w] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail, add_mul]

end Ring

variable {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]

/-- The alternating bilinear map `v ↦ 2⁻¹ • (f (v 0) ∧ g (v 1) + g (v 0) ∧ f (v 1))` underlying
`exteriorPower.wedgeEnd`. -/
private noncomputable def wedgeEndAlternating (f g : V →ₗ[K] W) :
    V [⋀^Fin 2]→ₗ[K] (⋀[K]^2 W) :=
  (show (LinearMap.mk₂ K
      (fun u v ↦ (2 : K)⁻¹ • (ιMulti K 2 ![f u, g v] + ιMulti K 2 ![g u, f v]))
      (fun u₁ u₂ v ↦ by
        simp only [map_add, ιMulti_two_add_left, ← smul_add]
        congr 1; abel)
      (fun c u v ↦ by
        simp only [map_smul, ιMulti_two_smul_left, ← smul_add]
        rw [smul_comm])
      (fun u v₁ v₂ ↦ by
        simp only [map_add, ιMulti_two_add_right, ← smul_add]
        congr 1; abel)
      (fun c u v ↦ by
        simp only [map_smul, ιMulti_two_smul_right, ← smul_add]
        rw [smul_comm])).IsAlt from fun u ↦ by
    have hswap : ![g u, f u] = ![f u, g u] ∘ Equiv.swap 0 1 := by funext k; fin_cases k <;> rfl
    simp only [LinearMap.mk₂_apply]
    rw [hswap, (ιMulti K 2).map_add_swap _ (by decide), smul_zero]).toAlternatingMap

@[simp]
private theorem wedgeEndAlternating_apply (f g : V →ₗ[K] W) (v : Fin 2 → V) :
    wedgeEndAlternating f g v =
      (2 : K)⁻¹ • (ιMulti K 2 ![f (v 0), g (v 1)] + ιMulti K 2 ![g (v 0), f (v 1)]) := by
  simp only [wedgeEndAlternating, LinearMap.IsAlt.toAlternatingMap_apply, LinearMap.mk₂_apply]

/-- The symmetric wedge product `(f ∧ g)(u ∧ v) = 2⁻¹ • (f u ∧ g v + g u ∧ f v)` of two linear
maps `f, g : V →ₗ[K] W`, bundled as a bilinear map into `⋀[K]^2 V →ₗ[K] ⋀[K]^2 W`. -/
noncomputable def wedgeEnd :
    (V →ₗ[K] W) →ₗ[K] (V →ₗ[K] W) →ₗ[K] (⋀[K]^2 V →ₗ[K] ⋀[K]^2 W) :=
  LinearMap.mk₂ K
    (fun f g ↦ alternatingMapLinearEquiv (wedgeEndAlternating f g))
    (fun f₁ f₂ g ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
        alternatingMapLinearEquiv_apply_ιMulti, wedgeEndAlternating_apply,
        ιMulti_two_add_left, ιMulti_two_add_right, ← smul_add]
      congr 1; abel)
    (fun c f g ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
        alternatingMapLinearEquiv_apply_ιMulti, wedgeEndAlternating_apply,
        ιMulti_two_smul_left, ιMulti_two_smul_right, ← smul_add]
      rw [smul_comm])
    (fun f g₁ g₂ ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
        alternatingMapLinearEquiv_apply_ιMulti, wedgeEndAlternating_apply,
        ιMulti_two_add_left, ιMulti_two_add_right, ← smul_add]
      congr 1; abel)
    (fun c f g ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
        alternatingMapLinearEquiv_apply_ιMulti, wedgeEndAlternating_apply,
        ιMulti_two_smul_left, ιMulti_two_smul_right, ← smul_add]
      rw [smul_comm])

/-- Evaluation of `exteriorPower.wedgeEnd` on a decomposable wedge `ιMulti K 2 v`. -/
@[simp]
theorem wedgeEnd_apply_ιMulti (f g : V →ₗ[K] W) (v : Fin 2 → V) :
    wedgeEnd f g (ιMulti K 2 v) =
      (2 : K)⁻¹ • (ιMulti K 2 ![f (v 0), g (v 1)] + ιMulti K 2 ![g (v 0), f (v 1)]) := by
  simp only [wedgeEnd, LinearMap.mk₂_apply, alternatingMapLinearEquiv_apply_ιMulti,
    wedgeEndAlternating_apply]

/-- Evaluation of `exteriorPower.wedgeEnd` on `u ∧ v`. -/
theorem wedgeEnd_apply_ιMulti_two (f g : V →ₗ[K] W) (u v : V) :
    wedgeEnd f g (ιMulti K 2 ![u, v]) =
      (2 : K)⁻¹ • (ιMulti K 2 ![f u, g v] + ιMulti K 2 ![g u, f v]) :=
  wedgeEnd_apply_ιMulti f g ![u, v]

/-- The wedge product of linear maps is symmetric: `f ∧ g = g ∧ f`. -/
theorem wedgeEnd_comm (f g : V →ₗ[K] W) : wedgeEnd f g = wedgeEnd g f :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    simp only [LinearMap.compAlternatingMap_apply, wedgeEnd_apply_ιMulti, add_comm]

/-- When `2 ≠ 0`, `f ∧ f` is the exterior-square map `⋀² f`. -/
@[simp]
theorem wedgeEnd_self [NeZero (2 : K)] (f : V →ₗ[K] W) :
    wedgeEnd f f = map 2 f :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    simp only [LinearMap.compAlternatingMap_apply, wedgeEnd_apply_ιMulti, map_apply_ιMulti]
    have hv : (f ∘ v) = ![f (v 0), f (v 1)] := by funext k; fin_cases k <;> rfl
    rw [hv, ← two_smul K, smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : K)), one_smul]

/-- When `2 ≠ 0`, `id ∧ id = id` on `⋀[K]^2 V`. -/
theorem wedgeEnd_id_id [NeZero (2 : K)] :
    wedgeEnd (LinearMap.id : Module.End K V) LinearMap.id = LinearMap.id := by
  rw [wedgeEnd_self, map_id]

/-- Wedging an endomorphism `f` with `id` gives half the derivation `exteriorPower.lieMap 2 f`. -/
theorem wedgeEnd_id_right (f : Module.End K V) :
    wedgeEnd f LinearMap.id = (2 : K)⁻¹ • lieMap 2 f :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    have hv : v = ![v 0, v 1] := by funext k; fin_cases k <;> rfl
    conv_rhs => rw [hv]
    simp only [LinearMap.compAlternatingMap_apply, wedgeEnd_apply_ιMulti, LinearMap.id_apply,
      LinearMap.smul_apply, lieMap_two_apply_ιMulti]

/-- Wedging `id` with an endomorphism `f` gives half the derivation `exteriorPower.lieMap 2 f`. -/
theorem wedgeEnd_id_left (f : Module.End K V) :
    wedgeEnd LinearMap.id f = (2 : K)⁻¹ • lieMap 2 f := by
  rw [wedgeEnd_comm, wedgeEnd_id_right]

/-- Postcomposing `f ∧ g` with `⋀² h` distributes into both factors. -/
theorem map_comp_wedgeEnd (h : W →ₗ[K] U) (f g : V →ₗ[K] W) :
    (map 2 h).comp (wedgeEnd f g) = wedgeEnd (h.comp f) (h.comp g) :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, wedgeEnd_apply_ιMulti,
      map_smul, map_add, map_apply_ιMulti]
    have hp (a b : V →ₗ[K] W) : h ∘ ![a (v 0), b (v 1)] = ![h (a (v 0)), h (b (v 1))] := by
      funext k; fin_cases k <;> rfl
    rw [hp, hp]

/-- Precomposing `f ∧ g` with `⋀² h` distributes into both factors. -/
theorem wedgeEnd_comp_map (f g : W →ₗ[K] U) (h : V →ₗ[K] W) :
    (wedgeEnd f g).comp (map 2 h) = wedgeEnd (f.comp h) (g.comp h) :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    simp [LinearMap.compAlternatingMap_apply, map_apply_ιMulti]

/-- Conjugating `f ∧ g` by `⋀² e` for a linear equivalence `e` conjugates each factor. -/
theorem conj_map_wedgeEnd (e : V ≃ₗ[K] W) (f g : Module.End K V) :
    (map 2 e.toLinearMap).comp ((wedgeEnd f g).comp (map 2 e.symm.toLinearMap)) =
      wedgeEnd (e.conj f) (e.conj g) := by
  rw [wedgeEnd_comp_map, map_comp_wedgeEnd]
  rfl

end exteriorPower
