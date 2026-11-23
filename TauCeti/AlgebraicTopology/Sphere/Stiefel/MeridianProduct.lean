/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Pontryagin.MooreLoop
public import TauCeti.AlgebraicTopology.Sphere.Stiefel.DoubleLoop
public import TauCeti.Topology.Homotopy.Path

/-!
# The meridian loops of a sphere as a Pontryagin product

Let `p` be a point of the unit sphere `Sⁿ` of a real inner product space `E`, and let
`S = S(p^⊥)` be the unit tangent sphere at `p`. For directions `u, w ∈ S` the loop
`α(u, w) = γ_w · γ_u⁻¹` at `p` (`TauCeti.meridianLoop`) runs to `-p` along the meridian in the
direction `w` and returns along the meridian in the direction `u`. Fix a direction `u₀ ∈ S`, and
let

* `λ(w) = γ_w · γ_{u₀}⁻¹` (`TauCeti.meridianLoopFixedReturn`): out along `w`, back along `u₀`;
* `λ'(u) = γ_{u₀} · γ_u⁻¹` (`TauCeti.meridianLoopFixedDeparture`): out along `u₀`, back along `u`.

Shrinking the detour `γ_{u₀}⁻¹ · γ_{u₀}` at `-p` to the constant path, uniformly in `(u, w)`, shows
that `α` is homotopic to the map `(u, w) ↦ λ(w) · λ'(u)` into the loop space
(`TauCeti.homotopic_meridianLoop_trans`, from `Path.homotopic_trans_symm_trans_trans_symm`). This
is the step of Barraud–Damian–Humilière–Oancea's proof of their Proposition 6.17 in which the class
`α_*([S] × [S])` is reduced to a Pontryagin product.

Concatenation of loops on the unit interval is only associative up to homotopy, so the Pontryagin
product is read on the Moore loop space `Ωᴹ_pSⁿ`, a topological monoid, through the homotopy
equivalence `MooreLoopSpace.homotopyEquivPath`, which is multiplicative up to homotopy, also for
families of loops (`Path.homotopic_mooreLoopTrans_comp_prodMap`). In Moore loops, the map
`(w, u) ↦ γ_w · γ_u⁻¹` (`TauCeti.mooreMeridianLoop`, the departure direction first) is homotopic
to `(w, u) ↦ λ(w) * λ'(u)` (`TauCeti.homotopic_mooreMeridianLoop_mul`). Hence, since a product of
two families of loops carries a cross product to a Pontryagin product
(`TauCeti.map_mulMooreLoop_comp_prodMap_singularHomologyCross`), for classes `a, b` of the singular
homology of `S` with coefficients in a commutative ring `k`,

`mooreMeridianLoop_* (a × b) = λ_* a · λ'_* b`

(`TauCeti.map_mooreMeridianLoop_singularHomologyCross`), and in the original order of the
variables, for `a ∈ H_i(S)` and `b ∈ H_j(S)`,

`α_* (a × b) = (-1)^(i j) λ_* b · λ'_* a`

(`TauCeti.map_meridianLoop_singularHomologyCross`). For `a = b = [S]` this is the identity
`α_*([S] × [S]) = ± x · x'` of the source, with `x = λ_*[S]` and `x' = λ'_*[S]`.

## Main declarations

* `TauCeti.meridianLoopFixedReturn`, `TauCeti.meridianLoopFixedDeparture`: the loops `λ` and `λ'`.
* `TauCeti.meridianLoopFixedTrans`: the loops `(u, w) ↦ λ(w) · λ'(u)`.
* `TauCeti.homotopic_meridianLoop_trans`: `α(u, w)` is homotopic to `λ(w) · λ'(u)`.
* `TauCeti.mooreMeridianLoop`: the meridian loops `(w, u) ↦ γ_w · γ_u⁻¹` as Moore loops.
* `TauCeti.mooreMeridianLoopFixedMul`: the products `(w, u) ↦ λ(w) * λ'(u)` of Moore loops.
* `TauCeti.homotopic_mooreMeridianLoop_mul`: in Moore loops, the meridian loops are homotopic to
  `(w, u) ↦ λ(w) * λ'(u)`.
* `TauCeti.map_mooreMeridianLoop_singularHomologyCross`,
  `TauCeti.map_meridianLoop_singularHomologyCross`: the image of a cross product is a Pontryagin
  product.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, proof of Proposition 6.17.
-/

public section

noncomputable section

open Metric CategoryTheory MonoidalCategory MonObj AlgebraicTopology TopCat
open scoped unitInterval TensorProduct

namespace TauCeti

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)
  (u₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)

/-! ### The loops `λ` and `λ'` -/

/-- The loop `λ(w) = γ_w · γ_{u₀}⁻¹` at `p`: out to `-p` along the meridian in the direction `w`,
back along the fixed meridian in the direction `u₀`. -/
def meridianLoopFixedReturn : C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, Path p p) :=
  ⟨fun w ↦ meridianLoop p (u₀, w), (continuous_meridianLoop p).comp (by fun_prop)⟩

@[simp]
theorem meridianLoopFixedReturn_apply (w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    meridianLoopFixedReturn p u₀ w = meridianLoop p (u₀, w) :=
  (rfl)

/-- The loop `λ'(u) = γ_{u₀} · γ_u⁻¹` at `p`: out to `-p` along the fixed meridian in the
direction `u₀`, back along the meridian in the direction `u`. -/
def meridianLoopFixedDeparture : C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, Path p p) :=
  ⟨fun u ↦ meridianLoop p (u, u₀), (continuous_meridianLoop p).comp (by fun_prop)⟩

@[simp]
theorem meridianLoopFixedDeparture_apply (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    meridianLoopFixedDeparture p u₀ u = meridianLoop p (u, u₀) :=
  (rfl)

/-- The loops `(u, w) ↦ λ(w) · λ'(u) = (γ_w · γ_{u₀}⁻¹) · (γ_{u₀} · γ_u⁻¹)` at `p`. -/
def meridianLoopFixedTrans :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, Path p p) :=
  ⟨fun x ↦ (meridianLoopFixedReturn p u₀ x.2).trans (meridianLoopFixedDeparture p u₀ x.1),
    ((meridianLoopFixedReturn p u₀).continuous.comp continuous_snd).path_trans
      ((meridianLoopFixedDeparture p u₀).continuous.comp continuous_fst)⟩

@[simp]
theorem meridianLoopFixedTrans_apply
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    meridianLoopFixedTrans p u₀ x =
      (meridianLoopFixedReturn p u₀ x.2).trans (meridianLoopFixedDeparture p u₀ x.1) :=
  (rfl)

/-- **The meridian loops factor through a fixed meridian up to homotopy.** The map
`α : (u, w) ↦ γ_w · γ_u⁻¹` into the loop space at `p` is homotopic to
`(u, w) ↦ λ(w) · λ'(u) = (γ_w · γ_{u₀}⁻¹) · (γ_{u₀} · γ_u⁻¹)`. -/
theorem homotopic_meridianLoop_trans :
    (⟨meridianLoop p, continuous_meridianLoop p⟩ :
        C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, Path p p)).Homotopic
      (meridianLoopFixedTrans p u₀) := by
  convert (Path.homotopic_trans_symm_trans_trans_symm
    ((continuous_sphereMeridian p).comp continuous_snd)
    (continuous_const (y := sphereMeridian p u₀))
    ((continuous_sphereMeridian p).comp continuous_fst)).symm using 1 <;>
  ext1 x <;> simp [meridianLoop_def]

/-! ### The Pontryagin product in Moore loops -/

/-- The meridian loops `(w, u) ↦ γ_w · γ_u⁻¹` as Moore loops at `p`, with the departure direction
`w` as the first variable. -/
def mooreMeridianLoop :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, MooreLoopSpace _ p) :=
  ⟨fun x ↦ (meridianLoop p (x.2, x.1)).toMooreLoop,
    Path.continuous_toMooreLoop.comp ((continuous_meridianLoop p).comp continuous_swap)⟩

@[simp]
theorem mooreMeridianLoop_apply
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    mooreMeridianLoop p x = (meridianLoop p (x.2, x.1)).toMooreLoop :=
  (rfl)

/-- The products `(w, u) ↦ λ(w) * λ'(u)` of Moore loops at `p`. -/
def mooreMeridianLoopFixedMul :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, MooreLoopSpace _ p) :=
  (Path.mulMooreLoop p).comp
    ((meridianLoopFixedReturn p u₀).prodMap (meridianLoopFixedDeparture p u₀))

@[simp]
theorem mooreMeridianLoopFixedMul_apply
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    mooreMeridianLoopFixedMul p u₀ x =
      (meridianLoopFixedReturn p u₀ x.1).toMooreLoop *
        (meridianLoopFixedDeparture p u₀ x.2).toMooreLoop :=
  Path.mulMooreLoop_apply _

/-- **In Moore loops, the meridian loops are a product up to homotopy**: the map
`(w, u) ↦ γ_w · γ_u⁻¹` into the Moore loops at `p` is homotopic to `(w, u) ↦ λ(w) * λ'(u)`. -/
theorem homotopic_mooreMeridianLoop_mul :
    (mooreMeridianLoop p).Homotopic (mooreMeridianLoopFixedMul p u₀) := by
  have h₁ := (ContinuousMap.Homotopic.refl (MooreLoopSpace.homotopyEquivPath p).symm.toFun).comp
    ((homotopic_meridianLoop_trans p u₀).comp (.refl ⟨Prod.swap, continuous_swap⟩))
  have h₂ := Path.homotopic_mooreLoopTrans_comp_prodMap (meridianLoopFixedReturn p u₀)
    (meridianLoopFixedDeparture p u₀)
  have e : (MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
      ((meridianLoopFixedTrans p u₀).comp ⟨Prod.swap, continuous_swap⟩) =
      (Path.mooreLoopTrans p).comp
        ((meridianLoopFixedReturn p u₀).prodMap (meridianLoopFixedDeparture p u₀)) := by
    ext1 x
    simp [Path.mooreLoopTrans_apply]
  rw [e] at h₁
  refine .trans ?_ h₂
  convert h₁ using 1
  ext1 x
  simp [Prod.swap]

/-- **The meridian loops carry a cross product to a Pontryagin product.** For classes `a` and `b`
of the singular homology of the unit tangent sphere `S` with coefficients in a commutative ring
`k`, the map `(w, u) ↦ γ_w · γ_u⁻¹` into the Moore loops at `p` sends the cross product `a × b` to
the Pontryagin product `λ_* a · λ'_* b`. -/
theorem map_mooreMeridianLoop_singularHomologyCross (k : Type u) [CommRing k] {i j n : ℕ}
    (h : i + j = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).obj
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)))
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).obj
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
        (ofHom (mooreMeridianLoop p) : TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗
          TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⟶ _)
        (((singularHomologyFunctor (ModuleCat.{u} k) n).map (λ_ (𝟙_ _)).hom).app
          (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗ TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
          (singularHomologyCross (C := ModuleCat.{u} k)
            (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
            (𝟙_ _) (𝟙_ _) i j n h (a ⊗ₜ b))) =
      pontryaginMul k (TopCat.of (MooreLoopSpace _ p)) i j n h
        (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).map
          (ofHom ((MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
            (meridianLoopFixedReturn p u₀))) a)
        (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).map
          (ofHom ((MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
            (meridianLoopFixedDeparture p u₀))) b) := by
  obtain ⟨H⟩ := homotopic_mooreMeridianLoop_mul p u₀
  have hH : ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
        (ofHom (mooreMeridianLoopFixedMul p u₀)) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
        (ofHom (mooreMeridianLoop p)) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{u} k)
      (f := ofHom _) (g := ofHom (mooreMeridianLoop p)) H.symm (𝟙_ _) n
  rw [← map_mulMooreLoop_comp_prodMap_singularHomologyCross]
  exact (ConcreteCategory.congr_hom hH _).symm

/-- **The meridian loops `α` carry a cross product to a signed Pontryagin product.** For classes
`a ∈ H_i(S; k)` and `b ∈ H_j(S; k)` of the unit tangent sphere `S`, the map
`α : (u, w) ↦ γ_w · γ_u⁻¹`, read in the Moore loops at `p`, sends the cross product `a × b` to
`(-1)^(i j) λ_* b · λ'_* a`. -/
theorem map_meridianLoop_singularHomologyCross (k : Type u) [CommRing k] {i j n : ℕ}
    (h : i + j = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).obj
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)))
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).obj
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
        (ofHom ((MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
            ⟨meridianLoop p, continuous_meridianLoop p⟩) :
          TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗ TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⟶ _)
        (((singularHomologyFunctor (ModuleCat.{u} k) n).map (λ_ (𝟙_ _)).hom).app
          (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗ TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
          (singularHomologyCross (C := ModuleCat.{u} k)
            (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
            (𝟙_ _) (𝟙_ _) i j n h (a ⊗ₜ b))) =
      ((-1 : ℤ) ^ (i * j)) • pontryaginMul k (TopCat.of (MooreLoopSpace _ p)) j i n (by omega)
        (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).map
          (ofHom ((MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
            (meridianLoopFixedReturn p u₀))) b)
        (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).map
          (ofHom ((MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
            (meridianLoopFixedDeparture p u₀))) a) := by
  -- `α` is `mooreMeridianLoop` after the swap of the two factors
  have hfac : (ofHom ((MooreLoopSpace.homotopyEquivPath p).symm.toFun.comp
      ⟨meridianLoop p, continuous_meridianLoop p⟩) :
        TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗ TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⟶ _) =
        (β_ (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
          (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))).hom ≫
          (ofHom (mooreMeridianLoop p) : TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⊗
            TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) ⟶ _) :=
    -- `β_` swaps the two factors, and `mooreMeridianLoop` swaps them back
    ConcreteCategory.hom_ext _ _ fun ⟨u, w⟩ ↦
      calc _ = (MooreLoopSpace.homotopyEquivPath p).symm (meridianLoop p (u, w)) := ofHom_apply _ _
        _ = (meridianLoop p (u, w)).toMooreLoop := MooreLoopSpace.homotopyEquivPath_symm_apply _
        _ = mooreMeridianLoop p (w, u) := (mooreMeridianLoop_apply p (w, u)).symm
        _ = ofHom (mooreMeridianLoop p) ((β_ (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
              (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))).hom (u, w)) := by
          rw [TopCat.braiding_hom_apply, ofHom_apply]
        _ = _ := (ConcreteCategory.comp_apply _ _ _).symm
  have hswap := ConcreteCategory.congr_hom
    (singularHomologyCross_comp_map_leftUnitor_comp_map_braiding (C := ModuleCat.{u} k)
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1))
      i j n h) (a ⊗ₜ b)
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply] at hswap
  rw [hfac]
  refine (ConcreteCategory.congr_hom (Functor.map_comp _ _ _) _).trans ?_
  refine ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _ hswap)).trans ?_
  rw [map_zsmul, ← map_mooreMeridianLoop_singularHomologyCross]
  -- the two sides differ only in writing the source of `mooreMeridianLoop` as `of (S × S)` or as
  -- `of S ⊗ of S`, which are the same object of `TopCat`
  rfl

end TauCeti
