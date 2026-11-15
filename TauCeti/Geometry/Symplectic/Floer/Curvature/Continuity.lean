/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# Continuity of the curvature along a map, for a manifold target

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `K = K_s ds + K_t dt` be a Hamiltonian perturbation whose components
are jointly `C¹` over `U × M` for an open set `U` of the domain. Its curvature

`R_K = ∂s K_t - ∂t K_s - {K_s, K_t}`

(`TauCeti.SmoothTwoForm.hamiltonianCurvature`) is then continuous on `U × M`: the domain
derivatives of a jointly `C¹` function are jointly continuous
(`ContMDiffAt.fderiv_right`), and so is the Poisson bracket of a jointly `C¹` family
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_poissonBracket_uncurry`, applied with `U` as an
open submanifold of the plane). Evaluated along a map `u` continuous on `U`, the curvature
`R_K(u)` is continuous on `U`
(`TauCeti.SmoothTwoForm.IsNondegenerate.continuousOn_hamiltonianCurvature_comp`).

This is the manifold version of `TauCeti.SymplecticForm.continuousOn_hamiltonianCurvature_comp`.
It gives the measurability of `R_K(u)` on the punctured domains of Floer theory, where the
perturbation data are smooth only away from the punctures; together with a bound on the integral
of `|R_K(u)|`, this makes the curvature term of the energy identity integrable.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.continuousOn_hamiltonianCurvature`: the curvature of
  data which are `C¹` over `U × M` is continuous there.
* `TauCeti.SmoothTwoForm.IsNondegenerate.continuousOn_hamiltonianCurvature_comp`: the curvature
  evaluated along a map continuous on `U` is continuous on `U`.
-/

public section

open Function Set
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}

/-- **Continuity of the curvature, for a manifold target.** For a nondegenerate two-form on a
finite-dimensional manifold and perturbation data `K = K_s ds + K_t dt` which are jointly `C¹` over
`U × M` for an open set `U` of the domain, the curvature `R_K` is continuous on `U × M`. -/
theorem IsNondegenerate.continuousOn_hamiltonianCurvature (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ)) :
    ContinuousOn (fun p : (ℝ × ℝ) × M ↦ ω.hamiltonianCurvature Ks Kt p.1 p.2) (U ×ˢ univ) := by
  have hUM : IsOpen (U ×ˢ (univ : Set M)) := hU.prod isOpen_univ
  -- The domain derivatives of a jointly `C¹` function are jointly continuous.
  have hD (K : ℝ × ℝ → M → ℝ)
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) (v : ℝ × ℝ) :
      ContinuousOn (fun p : (ℝ × ℝ) × M ↦ fderiv ℝ (fun w ↦ K w p.2) p.1 v) (U ×ˢ univ) := by
    rintro ⟨z, x⟩ hp
    have hK' : ContMDiffAt (I.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) 1 (uncurry fun (y : M) (w : ℝ × ℝ) ↦ K w y)
        (x, z) :=
      (hK.contMDiffAt (hUM.mem_nhds hp)).comp (x, z) (contMDiffAt_snd.prodMk contMDiffAt_fst)
    have hd := ((hK'.fderiv_right (n := 0) (by norm_num)).continuousAt.comp
      (x := (z, x)) (continuous_snd.prodMk continuous_fst).continuousAt).clm_apply
        (continuousAt_const (y := v))
    exact hd.continuousWithinAt
  -- The Poisson bracket of the family is continuous, regarding `U` as an open submanifold.
  have hP : ContinuousOn (fun p : (ℝ × ℝ) × M ↦ ω.poissonBracket (Ks p.1) (Kt p.1) p.2)
      (U ×ˢ univ) := by
    let U' : TopologicalSpace.Opens (ℝ × ℝ) := ⟨U, hU⟩
    have hres (K : ℝ × ℝ → M → ℝ)
        (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) :
        ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (0 + 1)
          (uncurry fun (p : U') (y : M) ↦ K p y) := by
      rw [zero_add]
      exact hK.comp_contMDiff (contMDiff_subtype_val.prodMap contMDiff_id)
        fun q ↦ ⟨q.1.2, mem_univ _⟩
    have h := (hω.contMDiff_poissonBracket_uncurry (n := 0) (by simp) (hres Ks hKs)
      (hres Kt hKt)).continuous
    rw [continuousOn_iff_continuous_domRestrict]
    exact h.comp ((continuous_subtype_val.fst.subtype_mk fun q ↦ q.2.1).prodMk
      continuous_subtype_val.snd)
  exact (((hD Kt hKt _).sub (hD Ks hKs _)).sub hP).congr fun p _ ↦
    hamiltonianCurvature_def _ _ _ _ _

/-- **Continuity of the curvature along a map, for a manifold target.** For a nondegenerate
two-form on a finite-dimensional manifold, perturbation data `K = K_s ds + K_t dt` which are
jointly `C¹` over `U × M` for an open set `U` of the domain, and a map `u` continuous on `U`, the
curvature `R_K(u)` is continuous on `U`. The vector-space case is
`TauCeti.SymplecticForm.continuousOn_hamiltonianCurvature_comp`. -/
theorem IsNondegenerate.continuousOn_hamiltonianCurvature_comp (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → M} (hu : ContinuousOn u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ)) :
    ContinuousOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) U :=
  (hω.continuousOn_hamiltonianCurvature hU hKs hKt).comp (continuousOn_id.prodMk hu)
    fun _ hz ↦ ⟨hz, mem_univ _⟩

end TauCeti.SmoothTwoForm
