/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Pontryagin.MooreLoop
public import TauCeti.AlgebraicTopology.Sphere.Stiefel.DoubleLoop

/-!
# The meridian loops of a sphere as a Pontryagin product

Let `p` be a point of the unit sphere `Sⁿ` of a real inner product space `E`, and let
`S = S(p^⊥)` be the unit sphere of the tangent space at `p`. For `w ∈ S` the meridian `γ_w` runs
from `p` to `-p` leaving `p` in the direction `w` (`TauCeti.sphereMeridian`), and the map
`α : S × S → Ω_p Sⁿ`, `(u, w) ↦ γ_w · γ_u⁻¹` (`TauCeti.meridianLoop`), is the map through which
Barraud–Damian–Humilière–Oancea compute the class of their family of double loops in the proof of
Proposition 6.17 (see `TauCeti.homotopic_loopFamilyCircleMap_stiefelDoubleLoop`). Here `α` is read
in the Moore loop space (`TauCeti.meridianMooreLoop`), whose strictly associative concatenation
gives the Pontryagin product on its singular homology.

Fix `u₀ ∈ S` and put `λ(w) = γ_w · γ_{u₀}⁻¹` and `λ'(w) = γ_{u₀} · γ_w⁻¹`, the two restrictions of
`α` to `{u₀} × S` and `S × {u₀}`; `λ'` is `λ` followed by reversal of loops
(`TauCeti.meridianLoop_swap`). Inserting `γ_{u₀}⁻¹ · γ_{u₀}` in the middle of `γ_w · γ_u⁻¹` shows
that, up to the exchange of the two factors, `α` is homotopic to the pointwise product
`(w, u) ↦ λ(w) * λ'(u)`. On singular homology with coefficients in a commutative ring `k` this
gives

`α_* (a × b) = λ_* a · λ'_* b`

for all classes `a`, `b` of `S`, where `α` is precomposed with the exchange of factors
(`TauCeti.pontryaginMul_map_meridianMooreLoop`). For `a = b = [S]`, the fundamental class of
`S ≅ Sⁿ⁻¹`, put `x = λ_*[Sⁿ⁻¹]` and `x' = λ'_*[Sⁿ⁻¹]` (the source writes `λ'` and `x'` with a bar):
this identifies the image of `[Sⁿ⁻¹] × [Sⁿ⁻¹]` in `H_{2n-2}(Ω_p Sⁿ)`, under `α` composed with the
exchange of factors, with the Pontryagin product `x · x'`, whose nonvanishing the source's
proof of Proposition 6.17 then derives from the ring structure of `H_*(Ω_p Sⁿ)`.

## Main declarations

* `TauCeti.meridianMooreLoop`: the map `α`, with values in the Moore loop space.
* `TauCeti.meridianLoop_swap`: exchanging the two directions reverses the loop.
* `TauCeti.pontryaginMul_map_meridianMooreLoop`: `α_* (a × b) = λ_* a · λ'_* b`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, proof of Proposition 6.17.
-/

public noncomputable section

open CategoryTheory MonoidalCategory TopCat AlgebraicTopology TensorProduct Metric

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- Exchanging the two directions of a meridian loop reverses it: `γ_u · γ_w⁻¹` is the reverse of
`γ_w · γ_u⁻¹`. -/
theorem meridianLoop_swap (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    meridianLoop p x.swap = (meridianLoop p x).symm := by
  rw [meridianLoop_def, meridianLoop_def, Path.trans_symm, Path.symm_symm, Prod.fst_swap,
    Prod.snd_swap]

/-- The map `α : (u, w) ↦ γ_w · γ_u⁻¹` of meridian loops at `p`, with values in the Moore loop
space of the sphere at `p`. -/
def meridianMooreLoop :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1,
      MooreLoopSpace (sphere (0 : E) 1) p) :=
  ⟨fun x ↦ (meridianLoop p x).toMooreLoop, Path.continuous_toMooreLoop.comp (by fun_prop)⟩

@[simp]
theorem meridianMooreLoop_apply
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    meridianMooreLoop p x = (meridianLoop p x).toMooreLoop :=
  (rfl)

/-- The meridians as a continuous family of paths from `p` to `-p`. -/
private def sphereMeridianMap : C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, Path p (-p)) :=
  ⟨sphereMeridian p, continuous_sphereMeridian p⟩

/-- `α` is `(γ_u, γ_w) ↦ γ_w · γ_u⁻¹` on the meridians, with the factors exchanged. -/
private theorem meridianMooreLoop_comp_prodSwap :
    (meridianMooreLoop p).comp .prodSwap =
      (Path.mooreLoopTransSymm p (-p)).comp
        ((sphereMeridianMap p).prodMap (sphereMeridianMap p)) := by
  ext1 x
  simp [meridianLoop_def, sphereMeridianMap]

/-- **The meridian loops as a Pontryagin product** (Barraud–Damian–Humilière–Oancea, proof of
Proposition 6.17). For `u₀ ∈ S(p^⊥)`, the image of a cross product `a × b` under
`(w, u) ↦ α(u, w) = γ_w · γ_u⁻¹` is the Pontryagin product, in the Moore loop space at `p`, of the
image of `a` under `λ : w ↦ α(u₀, w) = γ_w · γ_{u₀}⁻¹` and the image of `b` under
`λ' : u ↦ α(u, u₀) = γ_{u₀} · γ_u⁻¹`. -/
theorem pontryaginMul_map_meridianMooreLoop {k : Type u} [CommRing k]
    (u₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (i j n : ℕ) (h : i + j = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).obj
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)))
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).obj
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))) :
    pontryaginMul k (TopCat.of (MooreLoopSpace (sphere (0 : E) 1) p)) i j n h
        (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).map
          (ofHom ((meridianMooreLoop p).comp ((ContinuousMap.const _ u₀).prodMk (.id _)))) a)
        (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).map
          (ofHom ((meridianMooreLoop p).comp ((ContinuousMap.id _).prodMk (.const _ u₀)))) b) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
          (ofHom ((meridianMooreLoop p).comp .prodSwap))
        (((singularHomologyFunctor (ModuleCat.{u} k) n).map (λ_ (𝟙_ _)).hom).app
          (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗ TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
          (singularHomologyCross (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
            (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) (𝟙_ (ModuleCat.{u} k)) (𝟙_ _) i j n h
            (a ⊗ₜ b))) := by
  have hfst : (meridianMooreLoop p).comp ((ContinuousMap.const _ u₀).prodMk (.id _)) =
      (Path.mooreLoopTransSymm p (-p)).comp
        ((sphereMeridianMap p).prodMk (.const _ (sphereMeridian p u₀))) := by
    ext1 w
    simp [meridianLoop_def, sphereMeridianMap]
  have hbar : (meridianMooreLoop p).comp ((ContinuousMap.id _).prodMk (.const _ u₀)) =
      (Path.mooreLoopTransSymm p (-p)).comp
        ((ContinuousMap.const _ (sphereMeridian p u₀)).prodMk (sphereMeridianMap p)) := by
    ext1 u
    simp [meridianLoop_def, sphereMeridianMap]
  rw [hfst, hbar, meridianMooreLoop_comp_prodSwap]
  exact pontryaginMul_map_mooreLoopTransSymm _ _ _ i j n h a b

end TauCeti
