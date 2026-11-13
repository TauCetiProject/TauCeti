/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Derivatives of maps that factor through a projection

A map `g ∘ Prod.fst` on a product `M × N` depends on the first factor only, and its derivative at
`p` is the derivative of `g` at `p.1` applied to the first component of a tangent vector; similarly
for `g ∘ Prod.snd`. No differentiability hypothesis is needed: when `g` is not differentiable at
`p.1`, neither is `g ∘ Prod.fst` at `p`, since `g` is recovered from it by composing with
`x ↦ (x, p.2)`, so both derivatives vanish.

These are the chain-rule identities used to differentiate functions of one factor along vector
fields on a product manifold.

## Main results

* `TauCeti.mfderiv_comp_fst` and `TauCeti.mfderiv_comp_snd`: the derivative of a map that factors
  through a projection.
* `TauCeti.mfderiv_snd_apply`: the derivative of the second projection takes the second component
  of a tangent vector.
* `TauCeti.mvfderiv_comp_fst_apply` and `TauCeti.mvfderiv_comp_snd_apply`: the same for
  vector-valued functions, applied to a tangent vector.
* `TauCeti.mvfderiv_comp_fst_add_comp_snd_apply`: the derivative of a separated sum
  `f ∘ Prod.fst + g ∘ Prod.snd` sends `(u, w)` to `df(u) + dg(w)`.
* `TauCeti.mvfderiv_comp_fst_add_comp_snd_eq_zero_iff` and
  `TauCeti.mfderiv_comp_fst_add_comp_snd_eq_zero_iff`: the differential of a separated sum vanishes
  at `p` exactly when the differentials of `f` at `p.1` and of `g` at `p.2` both vanish. For
  real-valued `f` and `g`: the critical points of the separated sum are the pairs of critical
  points.
* `TauCeti.mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd` and
  `TauCeti.mfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd`: the same, read in the
  product charts with values in `E × E'` (`TauCeti.chartedSpaceProd`) for the model
  `𝓘(𝕜, E × E')`.
* `ContinuousLinearMap.mvfderiv_comp_fst_apply` and `ContinuousLinearMap.mvfderiv_comp_snd_apply`:
  the derivative of a continuous linear map applied to a vector-valued function of one factor.
* `TauCeti.mvfderiv_comp_fst_mul_comp_snd_apply`: the product rule for a function of the first
  factor times a function of the second factor.
* `TauCeti.mvfderiv_comp_snd_apply_eq_smul_deriv`: for a scalar second factor, the same in terms of
  the one-variable derivative `deriv`.
* `TauCeti.mvfderiv_curry_right`: the derivative of a slice with fixed first coordinate.
* `TauCeti.mfderiv_inr_eq_zero_of_forall_apply_eq`: a map constant on a slice `{p} × N` has
  differential vanishing on the vectors tangent to that slice.
* `HasDerivAt.mvfderiv_comp_fst_apply`: the derivative of a function of the scalar coordinate of
  `𝕜 × N`.
* `TauCeti.mfderiv_prodMap_comp_prodMkLeft` and `TauCeti.mfderiv_prodMap_comp_prodMkRight`:
  composing the differential of `Prod.map f g` with a slice inclusion commutes with the
  differential on the varied factor.
* `MDifferentiableAt.hasLeftInverse_mfderiv_fst_prod_iff`: the differential of a
  parameter-preserving map splits exactly when the differential of its slice splits.
* `TauCeti.mfderiv_swap`: the derivative of the exchange of factors exchanges the components.

* `MDifferentiableAt.mfderiv_fst_apply` and `MDifferentiableAt.mfderiv_snd_apply`: the
  differential of a coordinate of a map into a product.
* `MDifferentiableAt.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct`: the derivative of a
  fibre-product condition `(f y).2 = (g y).1`.
* `MDifferentiableAt.mfderiv_prodMk_fst_snd_comp_apply`: the differential of
  `y ↦ ((φ (a y)).1, (ψ (b y)).2)`.
* `MDifferentiableAt.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct_comp`: the derivative of a
  fibre-product condition `(φ (a y)).2 = (ψ (b y)).1` along maps `a` and `b`.
* `MDifferentiableAt.mvfderiv_comp_prodMk` and `MDifferentiableAt.mvfderiv_diag`: the
  vector-valued derivative of `y ↦ h (a y, b y)` as the sum of the two partial derivatives along
  `a` and `b`, and its specialization `d(y ↦ h (y, y)) = d₁h + d₂h` along the diagonal.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of `g ∘ Prod.fst` at `p` is the derivative of `g` at `p.1` applied to the first
component. No differentiability is needed: both sides vanish when `g` is not differentiable. -/
theorem mfderiv_comp_fst (g : M → M'') (p : M × N) :
    mfderiv (I.prod J) I'' (g ∘ Prod.fst) p =
      (mfderiv I I'' g p.1).comp (ContinuousLinearMap.fst 𝕜 (TangentSpace I p.1)
        (TangentSpace J p.2)) := by
  by_cases hg : MDifferentiableAt I I'' g p.1
  · rw [mfderiv_comp p hg mdifferentiableAt_fst, mfderiv_fst]
    -- The sides differ only in the tangent-space index `(g ∘ Prod.fst) p`, which is `g p.1`.
    rfl
  · have hι : MDifferentiableAt I (I.prod J) (fun x : M ↦ (x, p.2)) p.1 :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hcomp : ¬MDifferentiableAt (I.prod J) I'' (g ∘ Prod.fst) p := fun h ↦
      hg (h.comp_of_eq _ hι (Prod.mk.eta (p := p)))
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hcomp,
      ContinuousLinearMap.zero_comp]
    -- Both zeros live in the same space of linear maps, up to the index of the target tangent
    -- space.
    rfl

/-- The derivative of `g ∘ Prod.snd` at `p` is the derivative of `g` at `p.2` applied to the second
component. No differentiability is needed: both sides vanish when `g` is not differentiable. -/
theorem mfderiv_comp_snd (g : N → M'') (p : M × N) :
    mfderiv (I.prod J) I'' (g ∘ Prod.snd) p =
      (mfderiv J I'' g p.2).comp (ContinuousLinearMap.snd 𝕜 (TangentSpace I p.1)
        (TangentSpace J p.2)) := by
  by_cases hg : MDifferentiableAt J I'' g p.2
  · rw [mfderiv_comp p hg mdifferentiableAt_snd, mfderiv_snd]
    -- The sides differ only in the tangent-space index `(g ∘ Prod.snd) p`, which is `g p.2`.
    rfl
  · have hι : MDifferentiableAt J (I.prod J) (fun y : N ↦ (p.1, y)) p.2 :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hcomp : ¬MDifferentiableAt (I.prod J) I'' (g ∘ Prod.snd) p := fun h ↦
      hg (h.comp_of_eq _ hι (Prod.mk.eta (p := p)))
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hcomp,
      ContinuousLinearMap.zero_comp]
    -- Both zeros live in the same space of linear maps, up to the index of the target tangent
    -- space.
    rfl

/-- The derivative of the second projection sends a tangent vector on a product to its second
component. -/
theorem mfderiv_snd_apply (p : M × N) (v : TangentSpace (I.prod J) p) :
    mfderiv (I.prod J) J Prod.snd p v = v.2 := by
  rw [mfderiv_snd]
  -- `ContinuousLinearMap.snd` is the second projection by definition. Its domain, the product of
  -- the coordinate tangent spaces, is the tangent space of the product only by definition, so
  -- `ContinuousLinearMap.coe_snd'` cannot be rewritten here.
  rfl

/-- The derivative of the exchange of factors `Prod.swap : M × N → N × M` exchanges the two
components of a tangent vector. -/
theorem mfderiv_swap (p : M × N) :
    mfderiv (I.prod J) (J.prod I) Prod.swap p =
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I p.1) (TangentSpace J p.2)).prod
        (ContinuousLinearMap.fst 𝕜 (TangentSpace I p.1) (TangentSpace J p.2)) := by
  -- `mfderiv_prodMk` applies to a pair of maps, so unfold `Prod.swap` to its pair expression.
  rw [show (Prod.swap : M × N → N × M) = fun q ↦ (q.2, q.1) from rfl,
    mfderiv_prodMk mdifferentiableAt_snd mdifferentiableAt_fst, mfderiv_snd, mfderiv_fst]
  -- The sides differ only in the target tangent-space index, `(p.2, p.1)` or `Prod.swap p`.
  rfl

/-- The derivative of a vector-valued function of the first factor, read on a product. -/
theorem mvfderiv_comp_fst_apply (g : M → F) (p : M × N) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (g ∘ Prod.fst) p v = mvfderiv I g p.1 v.1 := by
  rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp_fst]
  -- The identifications `NormedSpace.fromTangentSpace` at `(g ∘ Prod.fst) p` and at `g p.1` agree,
  -- as these points are equal by definition.
  rfl

/-- The derivative of a vector-valued function of the second factor, read on a product. -/
theorem mvfderiv_comp_snd_apply (g : N → F) (p : M × N) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (g ∘ Prod.snd) p v = mvfderiv J g p.2 v.2 := by
  rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp_snd]
  -- The identifications `NormedSpace.fromTangentSpace` at `(g ∘ Prod.snd) p` and at `g p.2` agree,
  -- as these points are equal by definition.
  rfl

/-- **The derivative of a separated sum.** When `f` is differentiable at `p.1` and `g` at `p.2`,
the derivative of `f ∘ Prod.fst + g ∘ Prod.snd` sends a tangent vector `v` at `p` to
`df(v.1) + dg(v.2)`. -/
theorem mvfderiv_comp_fst_add_comp_snd_apply {f : M → F} {g : N → F} {p : M × N}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f p.1) (hg : MDifferentiableAt J 𝓘(𝕜, F) g p.2)
    (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (f ∘ Prod.fst + g ∘ Prod.snd) p v =
      mvfderiv I f p.1 v.1 + mvfderiv J g p.2 v.2 := by
  rw [mvfderiv_add (hf.comp p mdifferentiableAt_fst) (hg.comp p mdifferentiableAt_snd), add_apply,
    mvfderiv_comp_fst_apply, mvfderiv_comp_snd_apply]

/-- **The differential of a separated sum vanishes exactly where both differentials vanish.** When
`f` is differentiable at `p.1` and `g` at `p.2`, the differential of `f ∘ Prod.fst + g ∘ Prod.snd`
vanishes at `p` exactly when the differentials of `f` at `p.1` and of `g` at `p.2` both vanish. -/
@[simp]
theorem mvfderiv_comp_fst_add_comp_snd_eq_zero_iff {f : M → F} {g : N → F} {p : M × N}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f p.1) (hg : MDifferentiableAt J 𝓘(𝕜, F) g p.2) :
    mvfderiv (I.prod J) (f ∘ Prod.fst + g ∘ Prod.snd) p = 0 ↔
      mvfderiv I f p.1 = 0 ∧ mvfderiv J g p.2 = 0 := by
  refine ⟨fun h0 ↦ ⟨ContinuousLinearMap.ext fun u ↦ ?_, ContinuousLinearMap.ext fun w ↦ ?_⟩,
    fun ⟨h₁, h₂⟩ ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  -- Below, the zero maps are applied to vectors read in the model spaces `E × E'`, `E` and `E'`,
  -- the tangent spaces at `p`, `p.1` and `p.2` by definition, where `zero_apply` does not match
  -- syntactically; such applications are `0` by definition.
  · calc mvfderiv I f p.1 u = mvfderiv I f p.1 u + mvfderiv J g p.2 0 := by
          rw [map_zero, add_zero]
      _ = mvfderiv (I.prod J) (f ∘ Prod.fst + g ∘ Prod.snd) p (u, 0) :=
        (mvfderiv_comp_fst_add_comp_snd_apply hf hg (u, 0)).symm
      _ = 0 := by rw [h0]; rfl
  · calc mvfderiv J g p.2 w = mvfderiv I f p.1 0 + mvfderiv J g p.2 w := by
          rw [map_zero, zero_add]
      _ = mvfderiv (I.prod J) (f ∘ Prod.fst + g ∘ Prod.snd) p (0, w) :=
        (mvfderiv_comp_fst_add_comp_snd_apply hf hg (0, w)).symm
      _ = 0 := by rw [h0]; rfl
  · rw [mvfderiv_comp_fst_add_comp_snd_apply hf hg, h₁, h₂]
    exact add_zero (0 : F)

/-- **The differential of a separated sum vanishes exactly where both differentials vanish**, for
`mfderiv`. When `f` is differentiable at `p.1` and `g` at `p.2`, the differential of
`f ∘ Prod.fst + g ∘ Prod.snd` vanishes at `p` exactly when the differentials of `f` at `p.1` and of
`g` at `p.2` both vanish. -/
@[simp]
theorem mfderiv_comp_fst_add_comp_snd_eq_zero_iff {f : M → F} {g : N → F} {p : M × N}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f p.1) (hg : MDifferentiableAt J 𝓘(𝕜, F) g p.2) :
    mfderiv (I.prod J) 𝓘(𝕜, F) (f ∘ Prod.fst + g ∘ Prod.snd) p = 0 ↔
      mfderiv I 𝓘(𝕜, F) f p.1 = 0 ∧ mfderiv J 𝓘(𝕜, F) g p.2 = 0 := by
  rw [← mvfderiv_eq_zero_iff, ← mvfderiv_eq_zero_iff, ← mvfderiv_eq_zero_iff]
  exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff hf hg

/-- The derivative of a continuous linear map applied to a vector-valued function of the first
factor, read on a product: the derivative of `y ↦ L (g y.1)` is `L` applied to the derivative of
`g` on the first component. -/
theorem _root_.ContinuousLinearMap.mvfderiv_comp_fst_apply {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] (L : F →L[𝕜] F') {g : M → F} {p : M × N}
    (hg : MDifferentiableAt I 𝓘(𝕜, F) g p.1) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (fun y ↦ L (g y.1)) p v = L (mvfderiv I g p.1 v.1) := by
  -- The map is `(L ∘ g) ∘ Prod.fst` by definition.
  exact (TauCeti.mvfderiv_comp_fst_apply (L ∘ g) p v).trans (L.mvfderiv_comp_apply hg _)

/-- The derivative of a continuous linear map applied to a vector-valued function of the second
factor, read on a product: the derivative of `y ↦ L (g y.2)` is `L` applied to the derivative of
`g` on the second component. -/
theorem _root_.ContinuousLinearMap.mvfderiv_comp_snd_apply {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] (L : F →L[𝕜] F') {g : N → F} {p : M × N}
    (hg : MDifferentiableAt J 𝓘(𝕜, F) g p.2) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (fun y ↦ L (g y.2)) p v = L (mvfderiv J g p.2 v.2) := by
  -- The map is `(L ∘ g) ∘ Prod.snd` by definition.
  exact (TauCeti.mvfderiv_comp_snd_apply (L ∘ g) p v).trans (L.mvfderiv_comp_apply hg _)

/-- **Product rule on a product.** The derivative of `(x, y) ↦ g x * h y` sends a tangent vector
`(u, w)` at `p` to `dg(u) * h p.2 + g p.1 * dh(w)`. -/
theorem mvfderiv_comp_fst_mul_comp_snd_apply {g : M → 𝕜} {h : N → 𝕜} {p : M × N}
    (hg : MDifferentiableAt I 𝓘(𝕜) g p.1) (hh : MDifferentiableAt J 𝓘(𝕜) h p.2)
    (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (fun q : M × N ↦ g q.1 * h q.2) p v =
      mvfderiv I g p.1 v.1 * h p.2 + g p.1 * mvfderiv J h p.2 v.2 := by
  have hv := congrArg (fun φ ↦ φ v)
    (mvfderiv_mul (hg.comp p mdifferentiableAt_fst) (hh.comp p mdifferentiableAt_snd))
  simp only [add_apply, smul_apply, smul_eq_mul,
    mvfderiv_comp_fst_apply, mvfderiv_comp_snd_apply, Function.comp_apply] at hv
  -- The product `(g ∘ Prod.fst) * (h ∘ Prod.snd)` is the function `(x, y) ↦ g x * h y`.
  exact hv.trans (by ring)

/-- The derivative of a vector-valued function of a scalar second factor, read on a product: the
scalar component `v.2` of a tangent vector is sent to `v.2 • g'(p.2)`. -/
theorem mvfderiv_comp_snd_apply_eq_smul_deriv (g : 𝕜 → F) (p : M × 𝕜)
    (v : TangentSpace (I.prod 𝓘(𝕜)) p) :
    mvfderiv (I.prod 𝓘(𝕜)) (g ∘ Prod.snd) p v = v.2 • deriv g p.2 := by
  rw [mvfderiv_comp_snd_apply, mvfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace` is the identity of `𝕜`.
  exact fderiv_eq_smul_deriv (f := g) (x := p.2) (v.2 : 𝕜)

/-- The derivative of a slice with fixed first coordinate is the product derivative composed
with the inclusion of the second tangent factor. -/
theorem mvfderiv_curry_right {f : M × N → F} (p : M) (x : N)
    (hf : MDifferentiableAt (I.prod J) 𝓘(𝕜, F) f (p, x)) :
    mvfderiv J (Function.curry f p) x =
      (mvfderiv (I.prod J) f (p, x)).comp
        (ContinuousLinearMap.inr 𝕜 (TangentSpace I p) (TangentSpace J x)) := by
  have hd := mvfderiv_comp_of_eq hf
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (rfl : (p, x) = (p, x))
  -- Remove the identity in the fixed-parameter inclusion `y ↦ (p, id y)`.
  dsimp only [id_eq] at hd
  rw [mfderiv_prod_right] at hd
  -- The product tangent synonym and the product of tangent synonyms have the same vectors;
  -- their `inr` maps agree pointwise. Composing with `y ↦ (p, y)` is currying at `p`.
  exact hd.trans (by ext v; rfl)

/-- A map on a product that is constant on the slice `{p} × N` through `(p, x)` has differential
at `(p, x)` vanishing on the vectors `(0, v)` tangent to that slice. No differentiability is
needed: the differential is zero where the map is not differentiable. -/
theorem mfderiv_inr_eq_zero_of_forall_apply_eq {f : M × N → M''} {p : M} {x : N}
    (hc : ∀ y, f (p, y) = f (p, x)) (v : TangentSpace J x) :
    mfderiv (I.prod J) I'' f (p, x) ((0 : TangentSpace I p), v) = 0 := by
  by_cases hf : MDifferentiableAt (I.prod J) I'' f (p, x)
  · have hd := mfderiv_comp_of_eq hf
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (rfl : (p, x) = (p, x))
    dsimp only [id_eq] at hd
    -- The composite with the slice inclusion `y ↦ (p, y)` is constant.
    rw [show (f ∘ fun y : N ↦ (p, y)) = fun _ ↦ f (p, x) from funext hc, mfderiv_const,
      mfderiv_prod_right] at hd
    exact (DFunLike.congr_fun hd v).symm
  · rw [mfderiv_zero_of_not_mdifferentiableAt hf]
    -- The zero map evaluates to zero; the product tangent space is the product of the factors.
    rfl

/-- The derivative of a function of the scalar coordinate of `𝕜 × N`, with derivative `g'` at
`p.1`, sends a tangent vector `(s, v)` at `p` to `s • g'`. -/
theorem _root_.HasDerivAt.mvfderiv_comp_fst_apply {g : 𝕜 → F} {g' : F} {p : 𝕜 × N}
    (hg : HasDerivAt g g' p.1) (v : TangentSpace (𝓘(𝕜).prod J) p) :
    mvfderiv (𝓘(𝕜).prod J) (g ∘ Prod.fst) p v =
      NormedSpace.fromTangentSpace (𝕜 := 𝕜) p.1 v.1 • g' := by
  rw [TauCeti.mvfderiv_comp_fst_apply, mvfderiv_eq_fderiv, hg.hasFDerivAt.fderiv]
  -- `ContinuousLinearMap.toSpanSingleton 𝕜 g'` sends `s` to `s • g'`, read through
  -- `NormedSpace.fromTangentSpace`.
  rfl

section ProdMap

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J'' : ModelWithCorners 𝕜 F' G'}
  {N'' : Type*} [TopologicalSpace N''] [ChartedSpace G' N'']

/-- Composing the differential of `Prod.map f g` at `(x, y)` with the differential of the
horizontal slice inclusion `x' ↦ (x', y)` equals the differential of `x' ↦ (x', g y)` composed with
`df_x`. Differentiability is needed only for `g` at `y`: when `f` is not differentiable at `x`,
neither is `Prod.map f g` at `(x, y)`, so both sides vanish. -/
theorem mfderiv_prodMap_comp_prodMkLeft {f : M → M''} {g : N → N''} {x : M} {y : N}
    (hg : MDifferentiableAt J J'' g y) :
    (mfderiv (I.prod J) (I''.prod J'') (Prod.map f g) (x, y)).comp
        (mfderiv I (I.prod J) (fun x' : M ↦ (x', y)) x) =
      (mfderiv I'' (I''.prod J'') (fun x' : M'' ↦ (x', g y)) (f x)).comp
        (mfderiv I I'' f x) := by
  have hι : MDifferentiableAt I (I.prod J) (fun x' : M ↦ (x', y)) x :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  by_cases hf : MDifferentiableAt I I'' f x
  · have hdiff : MDifferentiableAt (I.prod J) (I''.prod J'') (Prod.map f g) (x, y) :=
      (hf.comp (x, y) mdifferentiableAt_fst).prodMk (hg.comp (x, y) mdifferentiableAt_snd)
    exact (mfderiv_comp x hdiff hι).symm.trans
      (mfderiv_comp x (mdifferentiableAt_id.prodMk mdifferentiableAt_const) hf)
  · have hdiff : ¬MDifferentiableAt (I.prod J) (I''.prod J'') (Prod.map f g) (x, y) := fun h ↦
      hf (h.comp x hι).fst
    rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hdiff,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- Composing the differential of `Prod.map f g` at `(x, y)` with the differential of the
vertical slice inclusion `y' ↦ (x, y')` equals the differential of `y' ↦ (f x, y')` composed with
`dg_y`. Differentiability is needed only for `f` at `x`: when `g` is not differentiable at `y`,
neither is `Prod.map f g` at `(x, y)`, so both sides vanish. -/
theorem mfderiv_prodMap_comp_prodMkRight {f : M → M''} {g : N → N''} {x : M} {y : N}
    (hf : MDifferentiableAt I I'' f x) :
    (mfderiv (I.prod J) (I''.prod J'') (Prod.map f g) (x, y)).comp
        (mfderiv J (I.prod J) (fun y' : N ↦ (x, y')) y) =
      (mfderiv J'' (I''.prod J'') (fun y' : N'' ↦ (f x, y')) (g y)).comp
        (mfderiv J J'' g y) := by
  have hι : MDifferentiableAt J (I.prod J) (fun y' : N ↦ (x, y')) y :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  by_cases hg : MDifferentiableAt J J'' g y
  · have hdiff : MDifferentiableAt (I.prod J) (I''.prod J'') (Prod.map f g) (x, y) :=
      (hf.comp (x, y) mdifferentiableAt_fst).prodMk (hg.comp (x, y) mdifferentiableAt_snd)
    exact (mfderiv_comp y hdiff hι).symm.trans
      (mfderiv_comp y (mdifferentiableAt_const.prodMk mdifferentiableAt_id) hg)
  · have hdiff : ¬MDifferentiableAt (I.prod J) (I''.prod J'') (Prod.map f g) (x, y) := fun h ↦
      hg (h.comp y hι).snd
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hdiff,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

end ProdMap

end TauCeti

section ParameterPreserving

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' G : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G}
  {M M' N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [TopologicalSpace N] [ChartedSpace G N]
  {f : M × M' → N} {p : M × M'}

/-- The differential of a parameter-preserving map has a continuous linear left inverse
if and only if the differential of its slice at the fixed parameter does.
This holds for manifolds with corners and infinite-dimensional models. -/
theorem MDifferentiableAt.hasLeftInverse_mfderiv_fst_prod_iff
    (hf : MDifferentiableAt (I.prod I') J f p) :
    (mfderiv (I.prod I') (I.prod J) (fun q => (q.1, f q)) p).HasLeftInverse ↔
      (mfderiv I' J (fun x => f (p.1, x)) p.2).HasLeftInverse := by
  rw [mfderiv_prodMk mdifferentiableAt_fst hf, mfderiv_fst]
  -- Product tangent spaces use the model product, but their instance definitions
  -- require reducible unfolding to apply the operator-level product criterion.
  erw [ContinuousLinearMap.hasLeftInverse_fst_prod_iff]
  have hι : MDifferentiableAt I' (I.prod I') (fun x : M' => (p.1, x)) p.2 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hslice := mfderiv_comp_of_eq hf hι (Prod.mk.eta (p := p))
  rw [mfderiv_prod_right] at hslice
  -- The composite with the fixed-parameter inclusion is precisely the slice; the
  -- tangent-space indices at `p` and `(p.1, p.2)` agree by the product eta law.
  exact (congrArg ContinuousLinearMap.HasLeftInverse hslice.symm).to_iff

end ParameterPreserving

section Coordinates

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F F' F'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {H G G' G'' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  [TopologicalSpace G'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {J'' : ModelWithCorners 𝕜 F'' G''}
  {M N N' N'' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  [TopologicalSpace N''] [ChartedSpace G'' N'']
  {f : M → N × N'} {x : M}

/-- The differential of the first coordinate of a map into a product is the first coordinate of
its differential. -/
theorem MDifferentiableAt.mfderiv_fst_apply (hf : MDifferentiableAt I (J.prod J') f x)
    (v : TangentSpace I x) :
    mfderiv I J (fun y ↦ (f y).1) x v = (mfderiv I (J.prod J') f x v).1 := by
  have h := mfderiv_comp_apply x mdifferentiableAt_fst hf v
  rw [mfderiv_fst, Function.comp_def] at h
  -- `ContinuousLinearMap.fst` is the first projection by definition. Its domain, the product
  -- of the coordinate tangent spaces, is the tangent space of the product only by definition, so
  -- `ContinuousLinearMap.coe_fst'` cannot be rewritten here.
  exact h

/-- The differential of the second coordinate of a map into a product is the second coordinate of
its differential. -/
theorem MDifferentiableAt.mfderiv_snd_apply (hf : MDifferentiableAt I (J.prod J') f x)
    (v : TangentSpace I x) :
    mfderiv I J' (fun y ↦ (f y).2) x v = (mfderiv I (J.prod J') f x v).2 := by
  have h := mfderiv_comp_apply x mdifferentiableAt_snd hf v
  rw [mfderiv_snd, Function.comp_def] at h
  -- `ContinuousLinearMap.snd` is the second projection by definition. Its domain, the product
  -- of the coordinate tangent spaces, is the tangent space of the product only by definition, so
  -- `ContinuousLinearMap.coe_snd'` cannot be rewritten here.
  exact h

/-- Differentiating a fibre-product condition: if the second coordinate of `f` agrees everywhere
with the first coordinate of `g`, then so do the corresponding coordinates of their
differentials. -/
theorem MDifferentiableAt.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct {g : M → N' × N''}
    (hf : MDifferentiableAt I (J.prod J') f x) (hg : MDifferentiableAt I (J'.prod J'') g x)
    (hfg : ∀ y, (f y).2 = (g y).1) (v : TangentSpace I x) :
    (mfderiv I (J.prod J') f x v).2 = (mfderiv I (J'.prod J'') g x v).1 := by
  rw [← hf.mfderiv_snd_apply, ← hg.mfderiv_fst_apply]
  -- The two coordinate maps are equal; ascribing `F'` gives both sides one type, since the tangent
  -- spaces of `N'` at `(f x).2` and `(g x).1` are both `F'`.
  exact congrArg (fun φ : M → N' ↦ (mfderiv I J' φ x v : F')) (funext hfg)


section Comp

variable {EL EL' HL HL' L L' : Type*} [NormedAddCommGroup EL] [NormedSpace 𝕜 EL]
  [NormedAddCommGroup EL'] [NormedSpace 𝕜 EL'] [TopologicalSpace HL] [TopologicalSpace HL']
  {K : ModelWithCorners 𝕜 EL HL} {K' : ModelWithCorners 𝕜 EL' HL'}
  [TopologicalSpace L] [ChartedSpace HL L] [TopologicalSpace L'] [ChartedSpace HL' L']
  {φ : L → N × N'} {ψ : L' → N' × N''} {a : M → L} {b : M → L'}

/-- The differential of `y ↦ ((φ (a y)).1, (ψ (b y)).2)` reads off the first coordinate of
`dφ (da v)` and the second coordinate of `dψ (db v)`. -/
theorem MDifferentiableAt.mfderiv_prodMk_fst_snd_comp_apply
    (hφ : MDifferentiableAt K (J.prod J') φ (a x)) (hψ : MDifferentiableAt K' (J'.prod J'') ψ (b x))
    (ha : MDifferentiableAt I K a x) (hb : MDifferentiableAt I K' b x) (v : TangentSpace I x) :
    mfderiv I (J.prod J'') (fun y ↦ ((φ (a y)).1, (ψ (b y)).2)) x v =
      ((mfderiv K (J.prod J') φ (a x) (mfderiv I K a x v)).1,
        (mfderiv K' (J'.prod J'') ψ (b x) (mfderiv I K' b x v)).2) := by
  have hφa : MDifferentiableAt I (J.prod J') (φ ∘ a) x := hφ.comp x ha
  have hψb : MDifferentiableAt I (J'.prod J'') (ψ ∘ b) x := hψ.comp x hb
  have hh := hφa.fst.prodMk hψb.snd
  rw [← mfderiv_comp_apply x hφ ha, ← mfderiv_comp_apply x hψ hb, ← hφa.mfderiv_fst_apply,
    ← hψb.mfderiv_snd_apply]
  exact Prod.ext (hh.mfderiv_fst_apply v).symm (hh.mfderiv_snd_apply v).symm

/-- Differentiating a fibre-product condition `(φ (a y)).2 = (ψ (b y)).1` along maps `a` and `b`:
the matching coordinates of `dφ (da v)` and `dψ (db v)` agree. -/
theorem MDifferentiableAt.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct_comp
    (hφ : MDifferentiableAt K (J.prod J') φ (a x)) (hψ : MDifferentiableAt K' (J'.prod J'') ψ (b x))
    (ha : MDifferentiableAt I K a x) (hb : MDifferentiableAt I K' b x)
    (hab : ∀ y, (φ (a y)).2 = (ψ (b y)).1) (v : TangentSpace I x) :
    (mfderiv K (J.prod J') φ (a x) (mfderiv I K a x v)).2 =
      (mfderiv K' (J'.prod J'') ψ (b x) (mfderiv I K' b x v)).1 := by
  rw [← mfderiv_comp_apply x hφ ha, ← mfderiv_comp_apply x hψ hb]
  exact (hφ.comp x ha).mfderiv_snd_eq_mfderiv_fst_of_fiberProduct (hψ.comp x hb) hab v

end Comp

/-- **Two-factor chain rule for vector-valued functions.** The vector-valued differential of
`y ↦ h (a y, b y)` at `x` is the sum of the two partial differentials of `h` at `(a x, b x)`
precomposed with `da` and `db`. -/
theorem MDifferentiableAt.mvfderiv_comp_prodMk {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {h : N × N' → V} {a : M → N} {b : M → N'}
    (hh : MDifferentiableAt (J.prod J') 𝓘(𝕜, V) h (a x, b x))
    (ha : MDifferentiableAt I J a x) (hb : MDifferentiableAt I J' b x) :
    mvfderiv I (fun y ↦ h (a y, b y)) x =
      (mvfderiv J (fun z ↦ h (z, b x)) (a x)).comp (mfderiv I J a x) +
        (mvfderiv J' (fun z ↦ h (a x, z)) (b x)).comp (mfderiv I J' b x) := by
  ext v
  have hc := mvfderiv_comp_apply x hh (ha.prodMk hb) v
  rw [Function.comp_def, hh.mvfderiv_prod_eq_add_apply, ← (ha.prodMk hb).mfderiv_fst_apply,
    ← (ha.prodMk hb).mfderiv_snd_apply] at hc
  exact hc

/-- **Differential along the diagonal.** For a function `h` on `M × M` differentiable at `(x, x)`,
the differential of `y ↦ h (y, y)` at `x` is the sum of its two partial differentials at
`(x, x)`. -/
theorem MDifferentiableAt.mvfderiv_diag {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {h : M × M → V} (hh : MDifferentiableAt (I.prod I) 𝓘(𝕜, V) h (x, x)) :
    mvfderiv I (fun y ↦ h (y, y)) x =
      mvfderiv I (fun y ↦ h (y, x)) x + mvfderiv I (fun y ↦ h (x, y)) x := by
  simpa only [id_eq, mfderiv_id, ContinuousLinearMap.comp_id] using
    hh.mvfderiv_comp_prodMk mdifferentiableAt_id mdifferentiableAt_id

end Coordinates

/-! ### Product charts with values in a product of normed spaces -/

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N] {f : M → F} {g : N → F}

attribute [local instance low] chartedSpaceProd

/-- **The differential of a separated sum vanishes exactly where both differentials vanish**, in
the product charts with values in `E × E'`. When `f` is differentiable at `p.1` and `g` at `p.2`,
the differential of `f ∘ Prod.fst + g ∘ Prod.snd` for the model `𝓘(𝕜, E × E')` vanishes at `p`
exactly when the differentials of `f` at `p.1` and of `g` at `p.2` both vanish. -/
@[simp]
theorem mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd {p : M × N}
    (hf : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f p.1)
    (hg : MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, F) g p.2) :
    mvfderiv 𝓘(𝕜, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) p = 0 ↔
      mvfderiv 𝓘(𝕜, E) f p.1 = 0 ∧ mvfderiv 𝓘(𝕜, E') g p.2 = 0 := by
  rw [modelWithCornersSelf_prod]
  exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff hf hg

/-- **The differential of a separated sum vanishes exactly where both differentials vanish**, in
the product charts with values in `E × E'`. When `f` is differentiable at `p.1` and `g` at `p.2`,
the differential of `f ∘ Prod.fst + g ∘ Prod.snd` for the model `𝓘(𝕜, E × E')` vanishes at `p`
exactly when the differentials of `f` at `p.1` and of `g` at `p.2` both vanish. -/
@[simp]
theorem mfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd {p : M × N}
    (hf : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f p.1)
    (hg : MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, F) g p.2) :
    mfderiv 𝓘(𝕜, E × E') 𝓘(𝕜, F) (f ∘ Prod.fst + g ∘ Prod.snd) p = 0 ↔
      mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f p.1 = 0 ∧ mfderiv 𝓘(𝕜, E') 𝓘(𝕜, F) g p.2 = 0 := by
  rw [← mvfderiv_eq_zero_iff, ← mvfderiv_eq_zero_iff, ← mvfderiv_eq_zero_iff]
  exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd hf hg

end TauCeti
