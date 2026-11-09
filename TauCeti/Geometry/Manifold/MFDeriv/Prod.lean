/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse

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
* `TauCeti.mfderiv_fst_apply` and `TauCeti.mfderiv_snd_apply`: the derivative of a projection
  takes the corresponding component of a tangent vector.
* `TauCeti.mvfderiv_comp_fst_apply` and `TauCeti.mvfderiv_comp_snd_apply`: the same for
  vector-valued functions, applied to a tangent vector.
* `TauCeti.mvfderiv_comp_fst_mul_comp_snd_apply`: the product rule for a function of the first
  factor times a function of the second factor.
* `TauCeti.mvfderiv_comp_snd_apply_eq_smul_deriv`: for a scalar second factor, the same in terms of
  the one-variable derivative `deriv`.
* `TauCeti.mvfderiv_curry_right`: the derivative of a slice with fixed first coordinate.
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

/-- The derivative of the first projection sends a tangent vector on a product to its first
component. -/
theorem mfderiv_fst_apply (p : M × N) (v : TangentSpace (I.prod J) p) :
    mfderiv (I.prod J) I Prod.fst p v = v.1 := by
  rw [mfderiv_fst]
  -- `ContinuousLinearMap.fst` is the first projection by definition. Its domain, the product of
  -- the coordinate tangent spaces, is the tangent space of the product only by definition, so
  -- `ContinuousLinearMap.coe_fst'` cannot be rewritten here.
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

end Coordinates
