/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.BaseChange
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# Base change of the degree-zero Picard functor

Let `f : X ⟶ S` be a morphism of schemes and `g : S' ⟶ S` a morphism of bases, with base change
`f' : X' = S' ×_S X ⟶ S'`. The relative Picard presheaf of `f'` is the relative Picard presheaf
of `f` restricted to schemes over `S'` along `Over.map g`
(`TauCeti.AlgebraicGeometry.relativePicardPresheafBaseChangeIso`), by pullback along
`T ×_S X ≅ T ×_{S'} X'`. This file shows that the comparison preserves the degree of a class on
every field-valued fibre, and hence identifies the degree-zero parts.

For a point `ξ : Spec Ω ⟶ T` of a scheme `T` over `S'`, the fibres of `X'_T` and of `X_T` over
`ξ` are `Spec Ω ×_{S'} X'` and `Spec Ω ×_S X`, which are isomorphic over `Spec Ω`. When `f` is
quasi-compact and separated, these fibres are quasi-compact and separated over `Ω`, and the
Euler-characteristic degree is invariant under this isomorphism
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback_of_isIso`). So the comparison
preserves the fibre degree
(`relativePicardFiberDegree_relativePicardPresheafBaseChangeIso_hom_app`), and a class has degree
zero on every geometric fibre of `f'` exactly when its image has degree zero on every geometric
fibre of `f` (`relativePicardPresheafBaseChangeIso_hom_app_mem_iff`).

For a smooth proper geometrically connected family of curves `f`, its base change `f'` is again
such a family, and the comparison restricts to a natural isomorphism of presheaves of commutative
groups `Pic⁰_{X'/S'} ≅ Pic⁰_{X/S} ∘ Over.map g`
(`relativePicardDegreeZeroFunctorBaseChangeIso`), compatible with the inclusions into the relative
Picard presheaves. As `Over.map g` is left adjoint to `Over.pullback g`, an `S`-scheme `P`
representing `Pic⁰_{X/S}` base changes to an `S'`-scheme `P ×_S S'` representing `Pic⁰_{X'/S'}`
(`relativePicardDegreeZeroFunctorBaseChangeRepresentableBy`). For a curve over a field `k` and a
field extension `K` of `k`, this says that the base change to `K` of a `k`-scheme representing
`Pic⁰` of the curve represents `Pic⁰` of the base-changed curve.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_relativePicardPresheafBaseChangeIso_hom_app`:
  the base change comparison of relative Picard presheaves preserves fibre degrees;
* `TauCeti.AlgebraicGeometry.relativePicardPresheafBaseChangeIso_hom_app_mem_iff`: it preserves
  and reflects degree zero on every geometric fibre;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctorBaseChangeIso`: `Pic⁰` of the base
  change of a family of curves is `Pic⁰` of the family restricted along `Over.map g`;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctorBaseChangeIso_hom_comp_ι`: it is the
  restriction of `relativePicardPresheafBaseChangeIso`;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctorBaseChangeRepresentableBy`,
  `TauCeti.AlgebraicGeometry.isRepresentable_relativePicardDegreeZeroFunctor_baseChange`: a
  representing scheme of `Pic⁰` base changes to a representing scheme.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.2 and 9.5.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S S' X : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

section FiberDegree

variable [QuasiCompact f] [IsSeparated f]

/-- **The base change comparison preserves fibre degrees.** For `f : X ⟶ S` quasi-compact and
separated, `g : S' ⟶ S`, a scheme `T` over `S'` and a point `ξ : Spec Ω ⟶ T`, the degree on the
fibre over `ξ` of a section of `T ↦ Pic(T ×_{S'} X') / Pic(T)` is the degree on the fibre over
`ξ` of its image in `T ↦ Pic(T ×_S X) / Pic(T)` under `relativePicardPresheafBaseChangeIso`. -/
-- Not `@[simp]`: `simp` rewrites the object `(Over.map g).op.obj T` by `Functor.op_obj`, after
-- which this left-hand side no longer matches.
theorem relativePicardFiberDegree_relativePicardPresheafBaseChangeIso_hom_app
    {T : (Over S')ᵒᵖ} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left)
    (c : (relativePicardPresheaf (pullback.fst g f)).obj T) :
    relativePicardFiberDegree f (T := (Over.map g).op.obj T) ξ
        ((relativePicardPresheafBaseChangeIso f g).hom.app T c) =
      relativePicardFiberDegree (pullback.fst g f) ξ c := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  rw [relativePicardPresheafBaseChangeIso_hom_app_mk, relativePicardFiberDegree_mk,
    relativePicardFiberDegree_mk]
  -- The two fibres `Spec Ω ×_S X` and `Spec Ω ×_{S'} X'` are isomorphic over `Spec Ω`.
  let e : pullback (ξ ≫ ((Over.map g).obj T.unop).hom) f ⟶
      pullback (ξ ≫ T.unop.hom) (pullback.fst g f) :=
    (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackRightPullbackFstIso g f (ξ ≫ T.unop.hom)).inv
  have he₁ : e ≫ pullback.fst (ξ ≫ T.unop.hom) (pullback.fst g f) =
      pullback.fst (ξ ≫ ((Over.map g).obj T.unop).hom) f := by
    simp [e]
  -- The isomorphism is compatible with the maps from the fibres to `X_T` and `X'_T`.
  have he₂ : e ≫ pullback.map (ξ ≫ T.unop.hom) (pullback.fst g f) T.unop.hom (pullback.fst g f) ξ
        (𝟙 _) (𝟙 S') (by simp) (by simp) =
      pullback.map (ξ ≫ ((Over.map g).obj T.unop).hom) f ((Over.map g).obj T.unop).hom f ξ
          (𝟙 X) (𝟙 S) (by simp) (by simp) ≫
        (pullbackRightPullbackFstIso g f T.unop.hom).inv := by
    apply pullback.hom_ext
    · simp [e]
    · apply pullback.hom_ext <;> simp [e]
  let _ : (pullback (ξ ≫ ((Over.map g).obj T.unop).hom) f).Over (Spec (.of Ω)) :=
    ⟨pullback.fst _ _⟩
  let _ : (pullback (ξ ≫ T.unop.hom) (pullback.fst g f)).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
  -- The fibre of `X'` is quasi-compact and separated, as a base change of `f`.
  have : CompactSpace ↥(pullback (ξ ≫ T.unop.hom) (pullback.fst g f)) :=
    (quasiCompact_iff_compactSpace (pullback.fst (ξ ≫ T.unop.hom) (pullback.fst g f))).mp
      inferInstance
  have : IsSeparated (terminal.from (pullback (ξ ≫ T.unop.hom) (pullback.fst g f))) := by
    rw [← terminal.comp_from (pullback.fst (ξ ≫ T.unop.hom) (pullback.fst g f))]
    infer_instance
  have h := LineBundleClass.eulerDegree_pullback_of_isIso (k := Ω) e he₁
    (LineBundleClass.pullback (pullback.map (ξ ≫ T.unop.hom) (pullback.fst g f) T.unop.hom
      (pullback.fst g f) ξ (𝟙 _) (𝟙 S') (by simp) (by simp)) a)
  rw [LineBundleClass.pullback_comp, he₂] at h
  rw [LineBundleClass.pullback_comp]
  exact h

/-- **The base change comparison preserves and reflects `Pic⁰`.** For `f` quasi-compact and
separated, a section of `T ↦ Pic(T ×_{S'} X') / Pic(T)` has degree zero on every geometric fibre
exactly when its image in `T ↦ Pic(T ×_S X) / Pic(T)` under
`relativePicardPresheafBaseChangeIso` does. -/
theorem relativePicardPresheafBaseChangeIso_hom_app_mem_iff
    {T : (Over S')ᵒᵖ} {c : (relativePicardPresheaf (pullback.fst g f)).obj T} :
    (relativePicardPresheafBaseChangeIso f g).hom.app T c ∈
        (relativePicardDegreeZeroSubfunctor f).obj ((Over.map g).op.obj T) ↔
      c ∈ (relativePicardDegreeZeroSubfunctor (pullback.fst g f)).obj T := by
  refine (mem_relativePicardDegreeZeroSubfunctor_obj_iff f).trans
    (Iff.trans ?_ (mem_relativePicardDegreeZeroSubfunctor_obj_iff _).symm)
  refine forall_congr' fun Ω ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun ξ ↦ ?_
  exact Iff.of_eq (congrArg (· = 0)
    (relativePicardFiberDegree_relativePicardPresheafBaseChangeIso_hom_app f g (T := T) ξ c))

end FiberDegree

section Smooth

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- **Base change of the degree-zero Picard functor.** For a smooth proper geometrically connected
family of curves `f : X ⟶ S` and `g : S' ⟶ S`, the degree-zero Picard functor `Pic⁰_{X'/S'}` of
the base change `X' = S' ×_S X ⟶ S'` is `Pic⁰_{X/S}` restricted to schemes over `S'` along
`Over.map g`. The isomorphism is the restriction of `relativePicardPresheafBaseChangeIso`, that is
pullback along `T ×_S X ≅ T ×_{S'} X'`
(`relativePicardDegreeZeroFunctorBaseChangeIso_hom_comp_ι`). -/
def relativePicardDegreeZeroFunctorBaseChangeIso :
    relativePicardDegreeZeroFunctor (pullback.fst g f) ≅
      (Over.map g).op ⋙ relativePicardDegreeZeroFunctor f where
  hom := relativePicardDegreeZeroFunctor.lift f (H := (Over.map g).op)
    (relativePicardDegreeZeroFunctorι (pullback.fst g f) ≫
      (relativePicardPresheafBaseChangeIso f g).hom) fun _ c ↦
        (relativePicardPresheafBaseChangeIso_hom_app_mem_iff f g).mpr
          (relativePicardDegreeZeroFunctorι_app_mem _ c)
  inv := relativePicardDegreeZeroFunctor.lift (pullback.fst g f) (H := 𝟭 _)
    (Functor.whiskerLeft (Over.map g).op (relativePicardDegreeZeroFunctorι f) ≫
      (relativePicardPresheafBaseChangeIso f g).inv) fun T c ↦
        (relativePicardPresheafBaseChangeIso_hom_app_mem_iff f g).mp <| by
          -- Membership is transported across the inverse of the full base change comparison.
          change (relativePicardPresheafBaseChangeIso f g).hom.app T
              ((relativePicardPresheafBaseChangeIso f g).inv.app T
                ((relativePicardDegreeZeroFunctorι f).app _ c)) ∈ _
          rw [Iso.inv_hom_id_app_apply]
          exact relativePicardDegreeZeroFunctorι_app_mem f c
  hom_inv_id := by
    ext1
    simp
  inv_hom_id := by
    ext1
    simp

/-- The base change isomorphism of `Pic⁰` sends a section `c` of `Pic⁰_{X'/S'}` to the section of
`Pic⁰_{X/S}` whose underlying relative Picard class is the image of `c` under
`relativePicardPresheafBaseChangeIso`. -/
-- Not `@[simp]`: `simp` rewrites the functor composite in the implicit type arguments of the
-- left-hand side by `Functor.comp_obj`, so it is not in simp-normal form.
theorem relativePicardDegreeZeroFunctorι_app_relativePicardDegreeZeroFunctorBaseChangeIso_hom_app
    {T : (Over S')ᵒᵖ} (c : (relativePicardDegreeZeroFunctor (pullback.fst g f)).obj T) :
    (relativePicardDegreeZeroFunctorι f).app (.op ((Over.map g).obj T.unop))
        ((relativePicardDegreeZeroFunctorBaseChangeIso f g).hom.app T c) =
      (relativePicardPresheafBaseChangeIso f g).hom.app T
        ((relativePicardDegreeZeroFunctorι (pullback.fst g f)).app T c) :=
  relativePicardDegreeZeroFunctorι_app_lift_app f (H := (Over.map g).op) _ _ T c

/-- The inverse base change isomorphism of `Pic⁰` sends a section `c` of `Pic⁰_{X/S}` over the
`S`-scheme underlying `T` to the section of `Pic⁰_{X'/S'}` whose underlying relative Picard class
is the image of `c` under the inverse of `relativePicardPresheafBaseChangeIso`. -/
-- Not `@[simp]`: `simp` rewrites the functor composite in the implicit type arguments of the
-- left-hand side by `Functor.comp_obj`, so it is not in simp-normal form.
theorem relativePicardDegreeZeroFunctorι_app_relativePicardDegreeZeroFunctorBaseChangeIso_inv_app
    {T : (Over S')ᵒᵖ}
    (c : ((Over.map g).op ⋙ relativePicardDegreeZeroFunctor f).obj T) :
    (relativePicardDegreeZeroFunctorι (pullback.fst g f)).app T
        ((relativePicardDegreeZeroFunctorBaseChangeIso f g).inv.app T c) =
      (relativePicardPresheafBaseChangeIso f g).inv.app T
        ((relativePicardDegreeZeroFunctorι f).app (.op ((Over.map g).obj T.unop)) c) :=
  relativePicardDegreeZeroFunctorι_app_lift_app (pullback.fst g f) (H := 𝟭 _) _ _ T c

/-- The base change isomorphism of `Pic⁰` is the restriction of the base change isomorphism of
the relative Picard presheaves. -/
@[reassoc (attr := simp)]
theorem relativePicardDegreeZeroFunctorBaseChangeIso_hom_comp_ι :
    (relativePicardDegreeZeroFunctorBaseChangeIso f g).hom ≫
        Functor.whiskerLeft (Over.map g).op (relativePicardDegreeZeroFunctorι f) =
      relativePicardDegreeZeroFunctorι (pullback.fst g f) ≫
        (relativePicardPresheafBaseChangeIso f g).hom :=
  relativePicardDegreeZeroFunctor.lift_comp_ι f (H := (Over.map g).op) _ _

/-- The inverse base change isomorphism of `Pic⁰` is the restriction of the inverse base change
isomorphism of the relative Picard presheaves. -/
@[reassoc (attr := simp)]
theorem relativePicardDegreeZeroFunctorBaseChangeIso_inv_comp_ι :
    (relativePicardDegreeZeroFunctorBaseChangeIso f g).inv ≫
        relativePicardDegreeZeroFunctorι (pullback.fst g f) =
      Functor.whiskerLeft (Over.map g).op (relativePicardDegreeZeroFunctorι f) ≫
        (relativePicardPresheafBaseChangeIso f g).inv :=
  relativePicardDegreeZeroFunctor.lift_comp_ι' (pullback.fst g f) _ _

/-- **A representing scheme of `Pic⁰` base changes to a representing scheme.** For a smooth proper
geometrically connected family of curves `f : X ⟶ S`, if the `S`-scheme `P` represents
`Pic⁰_{X/S}`, then `P_{S'} = P ×_S S'` represents `Pic⁰_{X'/S'}` of the base change
`X' = S' ×_S X ⟶ S'`. -/
def relativePicardDegreeZeroFunctorBaseChangeRepresentableBy {P : Over S}
    (e : (relativePicardDegreeZeroFunctor f ⋙ forget CommGrpCat).RepresentableBy P) :
    (relativePicardDegreeZeroFunctor (pullback.fst g f) ⋙ forget CommGrpCat).RepresentableBy
      ((Over.pullback g).obj P) :=
  ((Over.mapPullbackAdj g).representableByComp e).ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (relativePicardDegreeZeroFunctorBaseChangeIso f g).symm _)

/-- If `Pic⁰_{X/S}` of a smooth proper geometrically connected family of curves is representable,
so is `Pic⁰` of its base change along any `g : S' ⟶ S`. -/
theorem isRepresentable_relativePicardDegreeZeroFunctor_baseChange
    [(relativePicardDegreeZeroFunctor f ⋙ forget CommGrpCat).IsRepresentable] :
    (relativePicardDegreeZeroFunctor (pullback.fst g f) ⋙ forget CommGrpCat).IsRepresentable :=
  (relativePicardDegreeZeroFunctorBaseChangeRepresentableBy f g
    (Functor.representableBy _)).isRepresentable

end Smooth

end

end TauCeti.AlgebraicGeometry
