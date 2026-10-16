/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Prod

/-!
# Isometries of products of Riemannian manifolds

For the product metric on `M × N` (`TauCeti.Geometry.Manifold.Riemannian.Prod`), the product
`Φ × Ψ` of Riemannian isometries is again a Riemannian isometry. Products of self-isometries give a
group homomorphism `Isom(M) × Isom(N) → Isom(M × N)`, injective when both factors are nonempty.
Consequently a product of homogeneous Riemannian manifolds is homogeneous: if `Isom(M)` acts
transitively on `M` and `Isom(N)` on `N`, then `Isom(M × N)` acts transitively on `M × N`. This is
how the product model geometries `S² × ℝ` and `ℍ² × ℝ` among Thurston's eight inherit their
homogeneity from their factors.

## Main definitions

* `TauCeti.RiemannianIsometry.prodCongr`: the product of two Riemannian isometries.
* `TauCeti.RiemannianIsometry.prodCongrHom`: the homomorphism `Isom(M) × Isom(N) → Isom(M × N)`.

## Main results

* `TauCeti.RiemannianIsometry.prodCongrHom_injective`: the homomorphism is injective when `M` and
  `N` are nonempty.
* `TauCeti.RiemannianIsometry.isPretransitive_prod`: a product of homogeneous Riemannian manifolds
  is homogeneous.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487
  (the product geometries `S² × ℝ` and `ℍ² × ℝ`).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

section Congr

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [RiemannianBundle (fun y : N' ↦ TangentSpace J' y)]

/-- The product `Φ × Ψ` of two Riemannian isometries is a Riemannian isometry between the products,
for the product metrics. -/
def prodCongr (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N') :
    RiemannianIsometry (I.prod J) (I'.prod J') (M × N) (M' × N') where
  -- Mathlib's `Diffeomorph.prodCongr` requires `N` and `N'` to share a model vector space, so the
  -- product diffeomorphism is assembled directly.
  toEquiv := Φ.toDiffeomorph.toEquiv.prodCongr Ψ.toDiffeomorph.toEquiv
  contMDiff_toFun := (Φ.toDiffeomorph.contMDiff.comp contMDiff_fst).prodMk
    (Ψ.toDiffeomorph.contMDiff.comp contMDiff_snd)
  contMDiff_invFun := (Φ.toDiffeomorph.symm.contMDiff.comp contMDiff_fst).prodMk
    (Ψ.toDiffeomorph.symm.contMDiff.comp contMDiff_snd)
  inner_mfderiv' p v w := by
    -- The goal mentions the coercion of the `Diffeomorph` structure literal being built here; it
    -- unfolds through `Diffeomorph.toEquiv` and `Equiv.prodCongr` to `Prod.map Φ Ψ`. Mathlib has
    -- no `Diffeomorph.coe_mk` rewrite lemma, and `coe_prodCongr` below is not yet available
    -- inside this definition, so the unfolding is done by `change`.
    change inner ℝ (mfderiv (I.prod J) (I'.prod J') (Prod.map Φ Ψ) p v)
      (mfderiv (I.prod J) (I'.prod J') (Prod.map Φ Ψ) p w) = inner ℝ v w
    rw [Manifold.inner_tangentSpace_prod,
      Manifold.inner_tangentSpace_prod p,
      mfderiv_prodMap (Φ.mdifferentiableAt p.1) (Ψ.mdifferentiableAt p.2)]
    simp only [Manifold.tangentSpaceProdEquiv_apply]
    exact congrArg₂ (· + ·) (Φ.inner_mfderiv p.1 v.1 w.1) (Ψ.inner_mfderiv p.2 v.2 w.2)

@[simp]
theorem coe_prodCongr (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N') :
    ⇑(Φ.prodCongr Ψ) = Prod.map Φ Ψ :=
  (rfl)

theorem prodCongr_apply (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N')
    (p : M × N) : Φ.prodCongr Ψ p = (Φ p.1, Ψ p.2) :=
  (rfl)

/-- When `N` and `N'` share a model vector space, the underlying diffeomorphism of a product of
isometries is Mathlib's product of diffeomorphisms. -/
@[simp]
theorem toDiffeomorph_prodCongr {G'' : Type*} [TopologicalSpace G'']
    {J'' : ModelWithCorners ℝ F G''} {N'' : Type*} [TopologicalSpace N''] [ChartedSpace G'' N'']
    [RiemannianBundle (fun y : N'' ↦ TangentSpace J'' y)]
    (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J'' N N'') :
    (Φ.prodCongr Ψ).toDiffeomorph = Φ.toDiffeomorph.prodCongr Ψ.toDiffeomorph :=
  (rfl)

/-- The inverse of a product of isometries is the product of the inverses. -/
@[simp]
theorem prodCongr_symm (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N') :
    (Φ.prodCongr Ψ).symm = Φ.symm.prodCongr Ψ.symm := by
  refine RiemannianIsometry.ext fun p ↦ ?_
  obtain ⟨q, rfl⟩ := EquivLike.surjective (Φ.prodCongr Ψ) p
  rw [symm_apply_apply]
  ext <;> simp

/-- The product of identity isometries is the identity isometry. -/
@[simp]
theorem refl_prodCongr_refl :
    (RiemannianIsometry.refl I M).prodCongr (RiemannianIsometry.refl J N) =
      RiemannianIsometry.refl (I.prod J) (M × N) := by
  ext p <;> simp

end Congr

variable (I M J N) in
/-- Products of isometries give a group homomorphism `Isom(M) × Isom(N) → Isom(M × N)`. -/
def prodCongrHom : Isom I M × Isom J N →* Isom (I.prod J) (M × N) where
  toFun Φ := Φ.1.prodCongr Φ.2
  map_one' := refl_prodCongr_refl
  map_mul' _ _ := by ext p <;> simp

@[simp]
theorem prodCongrHom_apply (Φ : Isom I M × Isom J N) :
    prodCongrHom I M J N Φ = Φ.1.prodCongr Φ.2 :=
  (rfl)

/-- When both factors are nonempty, distinct pairs of isometries give distinct products. -/
theorem prodCongrHom_injective [Nonempty M] [Nonempty N] :
    Function.Injective (prodCongrHom I M J N) := by
  intro Φ Ψ h
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨y⟩ := ‹Nonempty N›
  refine Prod.ext (RiemannianIsometry.ext fun x' ↦ ?_) (RiemannianIsometry.ext fun y' ↦ ?_)
  · simpa using congrArg Prod.fst (DFunLike.congr_fun h (x', y))
  · simpa using congrArg Prod.snd (DFunLike.congr_fun h (x, y'))

/-- A product of homogeneous Riemannian manifolds is homogeneous: if the isometry groups of `M`
and of `N` act transitively, then so does the isometry group of `M × N`, already through products
of isometries. -/
instance isPretransitive_prod [MulAction.IsPretransitive (Isom I M) M]
    [MulAction.IsPretransitive (Isom J N) N] :
    MulAction.IsPretransitive (Isom (I.prod J) (M × N)) (M × N) where
  exists_smul_eq p q := by
    obtain ⟨Φ, hΦ⟩ := MulAction.exists_smul_eq (Isom I M) p.1 q.1
    obtain ⟨Ψ, hΨ⟩ := MulAction.exists_smul_eq (Isom J N) p.2 q.2
    exact ⟨Φ.prodCongr Ψ, Prod.ext hΦ hΨ⟩

end TauCeti.RiemannianIsometry
