/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Basic
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.RingTheory.TensorProduct.CoefficientBaseChange

/-!
# Module categories over varying coefficient rings

Fix a commutative ring `k` and a `k`-algebra `Λ`, possibly noncommutative. To a commutative
`k`-algebra `R` attach the category `ModuleCat (R ⊗[k] Λ)` of modules over `Λ` with
coefficients in `R`. A morphism `f : R ⟶ S` of commutative `k`-algebras gives the base-change
functor

`CommAlgCat.moduleCatBaseChange Λ f : ModuleCat (R ⊗[k] Λ) ⥤ ModuleCat (S ⊗[k] Λ)`,
`N ↦ S ⊗[R] N`,

where `S` is an `R`-algebra through `f` and `s ⊗ l` acts by `s' ⊗ n ↦ (s * s') ⊗ ((1 ⊗ l) • n)`
(`TauCeti.CoefficientBaseChange.module`). It is additive, and semilinear along `f` on morphisms:
`(moduleCatBaseChange Λ f).map (r • φ) = f r • (moduleCatBaseChange Λ f).map φ`.

The base change along `𝟙 R` is isomorphic to the identity by `r ⊗ n ↦ r • n`, and the base
change along a composite is isomorphic to the composite of the base changes by
`t ⊗ n ↦ t ⊗ (1 ⊗ n)`. These comparisons are associative and unital, so the module categories
form a pseudofunctor

`CommAlgCat.moduleCatBaseChangePseudofunctor k Λ : LocallyDiscrete (CommAlgCat k) ⥤ᵖ Cat`.

For `Λ = k`, up to `R ⊗[k] k ≃ R`, this is base change of modules along maps of commutative
`k`-algebras, the analogue of Mathlib's `CommRingCat.moduleCatExtendScalarsPseudofunctor`. In
general it is the family of representation categories of `Λ` over all commutative coefficient
algebras, with its base-change functors and their coherent comparisons. Restricting along a full
subcategory of coefficient algebras, such as the local Artinian `k`-algebras with residue field
`k`, gives the corresponding family over that subcategory.

## Main definitions

* `CommAlgCat.moduleCatBaseChange Λ f`: the base-change functor along `f : R ⟶ S`.
* `CommAlgCat.moduleCatBaseChangeTmul Λ f s n`: the tensor `s ⊗ n` as an element of
  `(moduleCatBaseChange Λ f).obj N`. The evaluation lemmas of the functor and of the comparisons
  below are stated on these elements, and a morphism out of a base change is determined by its
  values on them (`CommAlgCat.moduleCatBaseChange_hom_ext`).
* `CommAlgCat.moduleCatBaseChangeId Λ R`: the isomorphism of the base change along `𝟙 R` with
  the identity functor, `r ⊗ n ↦ r • n`.
* `CommAlgCat.moduleCatBaseChangeComp Λ f g fg h`: for `h : f ≫ g = fg`, the isomorphism of the
  base change along `fg` with the composite of the base changes, `t ⊗ n ↦ t ⊗ (1 ⊗ n)`.
* `CommAlgCat.moduleCatBaseChangePseudofunctor k Λ`: the pseudofunctor with these unit and
  composition comparisons.

## Implementation notes

Only `CommAlgCat.moduleCatBaseChange` and the pseudofunctor are exposed, so that their objects
compute to `S ⊗[R] N` and `ModuleCat (R ⊗[k] Λ)`. The elements
`moduleCatBaseChangeTmul Λ f s n` are used through their lemmas: additivity in each argument,
`moduleCatBaseChangeTmul_smul` for scalars of `R`, the eliminator
`moduleCatBaseChange_obj_inductionOn`, and the unfolding `moduleCatBaseChangeTmul_def`. The
comparisons are characterized by their component lemmas on these elements, from which the
coherence laws are proved. Stating these lemmas on elements typed in the base-change object,
rather than on raw tensors in `S ⊗[R] N`, lets them rewrite morphisms of `ModuleCat` applied to
those elements.

## References

* Edward Frenkel and Dennis Gaitsgory, *Local geometric Langlands correspondence and affine
  Kac–Moody algebras*, in *Algebraic Geometry and Number Theory*, Progress in Mathematics 253,
  Birkhäuser, 2006: categories of modules over a varying commutative base and their base change.
* Mathlib's `CommRingCat.moduleCatExtendScalarsPseudofunctor`, the case `Λ = k` over all
  commutative rings, whose comparisons are built from adjunctions rather than tensor formulas.
-/

public section

open CategoryTheory Bicategory TauCeti
open scoped TensorProduct ModuleCat.Algebra

universe w v u

namespace CommAlgCat

variable {k : Type w} [CommRing k] (Λ : Type v) [Ring Λ] [Algebra k Λ]

attribute [local instance low] CoefficientBaseChange.module

section Functor

variable {R S : CommAlgCat.{u} k}

/-- Base change along a morphism `f : R ⟶ S` of commutative `k`-algebras, from modules over
`R ⊗[k] Λ` to modules over `S ⊗[k] Λ`: `N ↦ S ⊗[R] N`, where `S` is an `R`-algebra through `f`. -/
@[expose] noncomputable def moduleCatBaseChange (f : R ⟶ S) :
    ModuleCat.{u} (R ⊗[k] Λ) ⥤ ModuleCat.{u} (S ⊗[k] Λ) :=
  letI := f.hom.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algHom f.hom
  { obj N := ModuleCat.of _ (S ⊗[R] N)
    map φ := ModuleCat.ofHom (CoefficientBaseChange.map k Λ S φ.hom)
    map_id _ := ModuleCat.hom_ext CoefficientBaseChange.map_id
    map_comp _ _ := ModuleCat.hom_ext (CoefficientBaseChange.map_comp _ _) }

lemma moduleCatBaseChange_obj (f : R ⟶ S) (N : ModuleCat.{u} (R ⊗[k] Λ)) :
    letI := f.hom.toRingHom.toAlgebra
    haveI := IsScalarTower.of_algHom f.hom
    (moduleCatBaseChange Λ f).obj N = ModuleCat.of (S ⊗[k] Λ) (S ⊗[R] N) :=
  rfl

lemma moduleCatBaseChange_map_hom (f : R ⟶ S) {N N' : ModuleCat.{u} (R ⊗[k] Λ)} (φ : N ⟶ N') :
    letI := f.hom.toRingHom.toAlgebra
    haveI := IsScalarTower.of_algHom f.hom
    ((moduleCatBaseChange Λ f).map φ).hom = CoefficientBaseChange.map k Λ S φ.hom :=
  rfl

/-- The tensor `s ⊗ n` as an element of the base change `(moduleCatBaseChange Λ f).obj N`. Its
type is the carrier of the base-change object rather than `S ⊗[R] N`, so that the evaluation
lemmas of the base-change functor and of its comparisons rewrite morphisms applied to it. -/
noncomputable def moduleCatBaseChangeTmul (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)}
    (s : S) (n : N) : (moduleCatBaseChange Λ f).obj N :=
  letI := f.hom.toRingHom.toAlgebra
  s ⊗ₜ[R] n

lemma moduleCatBaseChangeTmul_def (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (s : S) (n : N) :
    letI := f.hom.toRingHom.toAlgebra
    moduleCatBaseChangeTmul Λ f s n = s ⊗ₜ[R] n :=
  (rfl)

@[simp]
lemma moduleCatBaseChangeTmul_add_left (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (s s' : S)
    (n : N) :
    moduleCatBaseChangeTmul Λ f (s + s') n =
      moduleCatBaseChangeTmul Λ f s n + moduleCatBaseChangeTmul Λ f s' n := by
  let _ := f.hom.toRingHom.toAlgebra
  exact TensorProduct.add_tmul s s' n

@[simp]
lemma moduleCatBaseChangeTmul_add_right (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (s : S)
    (n n' : N) :
    moduleCatBaseChangeTmul Λ f s (n + n') =
      moduleCatBaseChangeTmul Λ f s n + moduleCatBaseChangeTmul Λ f s n' := by
  let _ := f.hom.toRingHom.toAlgebra
  exact TensorProduct.tmul_add s n n'

@[simp]
lemma moduleCatBaseChangeTmul_zero_left (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (n : N) :
    moduleCatBaseChangeTmul Λ f 0 n = 0 := by
  let _ := f.hom.toRingHom.toAlgebra
  exact TensorProduct.zero_tmul S n

@[simp]
lemma moduleCatBaseChangeTmul_zero_right (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (s : S) :
    moduleCatBaseChangeTmul Λ f s (0 : N) = 0 := by
  let _ := f.hom.toRingHom.toAlgebra
  exact TensorProduct.tmul_zero N s

/-- A scalar of `R` moves across the tensor through `f`: `(f r * s) ⊗ n = s ⊗ (r • n)`. -/
lemma moduleCatBaseChangeTmul_smul (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (r : R) (s : S)
    (n : N) :
    moduleCatBaseChangeTmul Λ f (f.hom r * s) n = moduleCatBaseChangeTmul Λ f s (r • n) := by
  let _ := f.hom.toRingHom.toAlgebra
  -- For the algebra structure `f.hom.toRingHom.toAlgebra`, `r • s` is `f r * s`.
  exact TensorProduct.smul_tmul r s n

/-- Induction on elements of a base change: a property of the elements of
`(moduleCatBaseChange Λ f).obj N` holds if it holds for the tensors
`moduleCatBaseChangeTmul Λ f s n` and is closed under addition. -/
@[elab_as_elim]
lemma moduleCatBaseChange_obj_inductionOn (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)}
    {motive : (moduleCatBaseChange Λ f).obj N → Prop} (x : (moduleCatBaseChange Λ f).obj N)
    (tmul : ∀ (s : S) (n : N), motive (moduleCatBaseChangeTmul Λ f s n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  let _ := f.hom.toRingHom.toAlgebra
  exact TensorProduct.inductionOn x tmul add

/-- The action of `S ⊗[k] Λ` on the base change: `(s ⊗ l) • (s' ⊗ n) = (s * s') ⊗ ((1 ⊗ l) • n)`. -/
@[simp]
lemma tmul_smul_moduleCatBaseChangeTmul (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)} (s s' : S)
    (l : Λ) (n : N) :
    (s ⊗ₜ[k] l) • moduleCatBaseChangeTmul Λ f s' n =
      moduleCatBaseChangeTmul Λ f (s * s') (((1 : R) ⊗ₜ[k] l) • n) := by
  let _ := f.hom.toRingHom.toAlgebra
  have _ := IsScalarTower.of_algHom f.hom
  exact CoefficientBaseChange.tmul_smul_tmul s s' l n

@[simp]
lemma moduleCatBaseChange_map_hom_tmul (f : R ⟶ S) {N N' : ModuleCat.{u} (R ⊗[k] Λ)}
    (φ : N ⟶ N') (s : S) (n : N) :
    ((moduleCatBaseChange Λ f).map φ).hom (moduleCatBaseChangeTmul Λ f s n) =
      moduleCatBaseChangeTmul Λ f s (φ.hom n) := by
  let _ := f.hom.toRingHom.toAlgebra
  have _ := IsScalarTower.of_algHom f.hom
  exact CoefficientBaseChange.map_tmul _ _ _

/-- A morphism out of a base change is determined by its values on the tensors `1 ⊗ n`. -/
lemma moduleCatBaseChange_hom_ext (f : R ⟶ S) {N : ModuleCat.{u} (R ⊗[k] Λ)}
    {P : ModuleCat.{u} (S ⊗[k] Λ)} {φ ψ : (moduleCatBaseChange Λ f).obj N ⟶ P}
    (h : ∀ n : N,
      φ.hom (moduleCatBaseChangeTmul Λ f 1 n) = ψ.hom (moduleCatBaseChangeTmul Λ f 1 n)) :
    φ = ψ := by
  let _ := f.hom.toRingHom.toAlgebra
  have _ := IsScalarTower.of_algHom f.hom
  exact ModuleCat.hom_ext (CoefficientBaseChange.hom_ext h)

/-- The base-change functor is additive. -/
instance (f : R ⟶ S) : (moduleCatBaseChange Λ f).Additive where
  map_add {_ _ _ _} := by
    let _ := f.hom.toRingHom.toAlgebra
    have _ := IsScalarTower.of_algHom f.hom
    exact ModuleCat.hom_ext (CoefficientBaseChange.map_add _ _)

/-- Base change is semilinear along `f` on morphisms: it sends `r • φ` to `f r • ` its image of
`φ`, for the `R`-linear structure of `ModuleCat (R ⊗[k] Λ)` and the `S`-linear structure of
`ModuleCat (S ⊗[k] Λ)`. -/
@[simp]
lemma moduleCatBaseChange_map_smul (f : R ⟶ S) {N N' : ModuleCat.{u} (R ⊗[k] Λ)} (r : R)
    (φ : N ⟶ N') :
    (moduleCatBaseChange Λ f).map (r • φ) = f.hom r • (moduleCatBaseChange Λ f).map φ := by
  let _ := f.hom.toRingHom.toAlgebra
  have _ := IsScalarTower.of_algHom f.hom
  refine ModuleCat.hom_ext ?_
  rw [ModuleCat.hom_smul, moduleCatBaseChange_map_hom, moduleCatBaseChange_map_hom,
    ModuleCat.hom_smul, CoefficientBaseChange.map_smul]
  -- `CoefficientBaseChange.map_smul` scales by `algebraMap R S r = f r` through the `S`-module
  -- structure of `S ⊗[R] N'`, while the `S`-linear structure of `ModuleCat (S ⊗[k] Λ)` scales
  -- through `algebraMap S (S ⊗[k] Λ)`; the two actions agree by `algebraMap_smul`.
  exact LinearMap.ext fun x ↦
    (algebraMap_smul (S ⊗[k] Λ) (f.hom r) (CoefficientBaseChange.map k Λ S φ.hom x)).symm

end Functor

section Comparison

variable (R : CommAlgCat.{u} k)

/-- The base change along `𝟙 R` is isomorphic to the identity functor, by `r ⊗ n ↦ r • n`
(`TauCeti.CoefficientBaseChange.lid`). -/
noncomputable def moduleCatBaseChangeId : moduleCatBaseChange Λ (𝟙 R) ≅ 𝟭 _ :=
  -- The `R`-algebra structure on `R` given by `𝟙 R` unfolds to `Algebra.id`, so base change
  -- along `𝟙 R` is `R ⊗[R] N` with its standard module structures.
  NatIso.ofComponents (fun N ↦ (CoefficientBaseChange.lid k Λ R N).toModuleIso) fun φ ↦
    moduleCatBaseChange_hom_ext Λ (𝟙 R) fun n ↦ by
      -- Both sides are `1 • φ n`. The components `(lid _).toModuleIso` are morphisms between
      -- `ModuleCat.of _ (R ⊗[R] _)` and `_`, whereas the naturality square types them out of
      -- `(moduleCatBaseChange Λ (𝟙 R)).obj _`, which is `ModuleCat.of _ (R ⊗[R] _)` only after
      -- unfolding `moduleCatBaseChange`. Rewriting with `LinearEquiv.toModuleIso_hom` therefore
      -- produces a goal that is not type-correct at implicit transparency, as in
      -- `moduleCatBaseChangeComp`. Restate the square as the underlying linear maps
      -- (`moduleCatBaseChange_map_hom`) applied to `1 ⊗ n`.
      change CoefficientBaseChange.lid k Λ R _ (CoefficientBaseChange.map k Λ R φ.hom (1 ⊗ₜ n)) =
        φ.hom (CoefficientBaseChange.lid k Λ R _ (1 ⊗ₜ n))
      rw [CoefficientBaseChange.map_tmul, CoefficientBaseChange.lid_tmul,
        CoefficientBaseChange.lid_tmul, one_smul, one_smul]

/-- The unit comparison sends `r ⊗ n` to `r • n`.

Not a simp lemma: `simp` first rewrites `(𝟭 _).obj N` to `N` in the types of
the linear maps (`Functor.id_obj`), after which the left-hand side no longer matches. -/
lemma moduleCatBaseChangeId_hom_app_hom_tmul (N : ModuleCat.{u} (R ⊗[k] Λ)) (r : R) (n : N) :
    ((moduleCatBaseChangeId Λ R).hom.app N).hom (moduleCatBaseChangeTmul Λ (𝟙 R) r n) = r • n :=
  CoefficientBaseChange.lid_tmul r n

/-- The inverse unit comparison sends `n` to `1 ⊗ n`.

Not a simp lemma: `simp` first rewrites `(𝟭 _).obj N` to `N` in the types of
the linear maps (`Functor.id_obj`), after which the left-hand side no longer matches. -/
lemma moduleCatBaseChangeId_inv_app_hom_apply (N : ModuleCat.{u} (R ⊗[k] Λ)) (n : N) :
    ((moduleCatBaseChangeId Λ R).inv.app N).hom n = moduleCatBaseChangeTmul Λ (𝟙 R) 1 n :=
  CoefficientBaseChange.lid_symm_apply n

variable {R} {S T : CommAlgCat.{u} k}

/-- The base change along a composite `fg = f ≫ g` is isomorphic to the composite of the base
changes, by `t ⊗ n ↦ t ⊗ (1 ⊗ n)`, the inverse of
`TauCeti.CoefficientBaseChange.cancelBaseChange`. The composite is given as an arbitrary `fg`
with `f ≫ g = fg`, so that the comparison applies to composites that agree only
propositionally. -/
noncomputable def moduleCatBaseChangeComp (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T)
    (h : f ≫ g = fg) :
    moduleCatBaseChange Λ fg ≅ moduleCatBaseChange Λ f ⋙ moduleCatBaseChange Λ g :=
  letI := f.hom.toRingHom.toAlgebra
  letI := g.hom.toRingHom.toAlgebra
  letI := fg.hom.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algHom f.hom
  haveI := IsScalarTower.of_algHom g.hom
  haveI := IsScalarTower.of_algHom fg.hom
  haveI := isScalarTower_toAlgebra_of_comp f g fg h
  NatIso.ofComponents
    (fun N ↦ (CoefficientBaseChange.cancelBaseChange k Λ T
      (LinearEquiv.refl (S ⊗[k] Λ) ((moduleCatBaseChange Λ f).obj N))).symm.toModuleIso)
    fun {N N'} φ ↦ moduleCatBaseChange_hom_ext Λ fg fun n ↦ by
      -- Naturality is an equation of composites in `ModuleCat` whose carriers
      -- `(moduleCatBaseChange Λ _).obj _` are `_ ⊗[_] _` only after unfolding
      -- `moduleCatBaseChange`. The goal is not type-correct at implicit transparency, so
      -- `ModuleCat.hom_comp` and `LinearEquiv.toModuleIso_hom` do not fire under `rw` or
      -- `dsimp`. Restate it as the underlying linear maps (`moduleCatBaseChange_map_hom`) of
      -- both composites applied to `1 ⊗ n`.
      change (CoefficientBaseChange.cancelBaseChange k Λ T
          (LinearEquiv.refl (S ⊗[k] Λ) ((moduleCatBaseChange Λ f).obj N'))).symm
          (CoefficientBaseChange.map k Λ T φ.hom (1 ⊗ₜ n)) =
        CoefficientBaseChange.map k Λ T ((moduleCatBaseChange Λ f).map φ).hom
          ((CoefficientBaseChange.cancelBaseChange k Λ T
            (LinearEquiv.refl (S ⊗[k] Λ) ((moduleCatBaseChange Λ f).obj N))).symm (1 ⊗ₜ n))
      have e (P : ModuleCat.{u} (R ⊗[k] Λ)) (t : T) (p : P) :=
        CoefficientBaseChange.cancelBaseChange_symm_tmul (k := k) (Λ := Λ) T
          (LinearEquiv.refl (S ⊗[k] Λ) ((moduleCatBaseChange Λ f).obj P)) t p
      rw [CoefficientBaseChange.map_tmul, e, e, CoefficientBaseChange.map_tmul]
      -- Both sides are `1 ⊗ x` with `x` in `(moduleCatBaseChange Λ f).obj N'`, wrapped in
      -- `LinearEquiv.refl`: `x = 1 ⊗ φ n` on the left, and the image of `1 ⊗ n` under
      -- `(moduleCatBaseChange Λ f).map φ` on the right. The raw tensors `1 ⊗ₜ[R] _` are
      -- `moduleCatBaseChangeTmul Λ f 1 _` by definition (`moduleCatBaseChangeTmul_def`) and
      -- `LinearEquiv.refl` is the identity, so the inner equation is
      -- `moduleCatBaseChange_map_hom_tmul`, used up to these two unfoldings. They are not
      -- available to `rw` or `simp` (`LinearEquiv.refl_apply`): `LinearEquiv.refl` is typed on
      -- the carrier of the base-change object and its argument on `S ⊗[R] _`, so the goal is
      -- not type-correct at implicit transparency.
      exact congrArg (TensorProduct.tmul S (1 : T))
        (moduleCatBaseChange_map_hom_tmul Λ f φ 1 n).symm

/-- The composition comparison sends `t ⊗ n` to `t ⊗ (1 ⊗ n)`.

Not a simp lemma: `simp` first rewrites `(F ⋙ G).obj N` to `G.obj (F.obj N)` in the
types of the linear maps (`Functor.comp_obj`), after which the left-hand side no longer
matches. -/
lemma moduleCatBaseChangeComp_hom_app_hom_tmul (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T)
    (h : f ≫ g = fg) (N : ModuleCat.{u} (R ⊗[k] Λ)) (t : T) (n : N) :
    ((moduleCatBaseChangeComp Λ f g fg h).hom.app N).hom (moduleCatBaseChangeTmul Λ fg t n) =
      moduleCatBaseChangeTmul Λ g t (moduleCatBaseChangeTmul Λ f 1 n) := by
  let _ := f.hom.toRingHom.toAlgebra
  let _ := g.hom.toRingHom.toAlgebra
  let _ := fg.hom.toRingHom.toAlgebra
  have _ := IsScalarTower.of_algHom f.hom
  have _ := IsScalarTower.of_algHom g.hom
  have _ := IsScalarTower.of_algHom fg.hom
  have _ := isScalarTower_toAlgebra_of_comp f g fg h
  exact CoefficientBaseChange.cancelBaseChange_symm_tmul T
    (LinearEquiv.refl (S ⊗[k] Λ) ((moduleCatBaseChange Λ f).obj N)) t n

/-- The inverse composition comparison sends `t ⊗ (s ⊗ n)` to `(g s * t) ⊗ n`.

Not a simp lemma: `simp` first rewrites `(F ⋙ G).obj N` to `G.obj (F.obj N)` in the
types of the linear maps (`Functor.comp_obj`), after which the left-hand side no longer
matches. -/
lemma moduleCatBaseChangeComp_inv_app_hom_tmul (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T)
    (h : f ≫ g = fg) (N : ModuleCat.{u} (R ⊗[k] Λ)) (t : T) (s : S) (n : N) :
    ((moduleCatBaseChangeComp Λ f g fg h).inv.app N).hom
        (moduleCatBaseChangeTmul Λ g t (moduleCatBaseChangeTmul Λ f s n)) =
      moduleCatBaseChangeTmul Λ fg (g.hom s * t) n := by
  let _ := f.hom.toRingHom.toAlgebra
  let _ := g.hom.toRingHom.toAlgebra
  let _ := fg.hom.toRingHom.toAlgebra
  have _ := IsScalarTower.of_algHom f.hom
  have _ := IsScalarTower.of_algHom g.hom
  have _ := IsScalarTower.of_algHom fg.hom
  have _ := isScalarTower_toAlgebra_of_comp f g fg h
  exact CoefficientBaseChange.cancelBaseChange_tmul T
    (LinearEquiv.refl (S ⊗[k] Λ) ((moduleCatBaseChange Λ f).obj N)) t s n

/-- The composition comparisons are associative: the two composites of composition comparisons
from the base change along `fgh` to the base change along `h` of the base change along `g` of the
base change along `f` agree. -/
lemma moduleCatBaseChangeComp_associativity {U : CommAlgCat.{u} k} (f : R ⟶ S) (g : S ⟶ T)
    (h : T ⟶ U) (fg : R ⟶ T) (gh : S ⟶ U) (fgh : R ⟶ U) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (N : ModuleCat.{u} (R ⊗[k] Λ)) :
    (moduleCatBaseChangeComp Λ fg h fgh hfgh).hom.app N ≫
        (moduleCatBaseChange Λ h).map ((moduleCatBaseChangeComp Λ f g fg hfg).hom.app N) =
      (moduleCatBaseChangeComp Λ f gh fgh hfgh').hom.app N ≫
        (moduleCatBaseChangeComp Λ g h gh hgh).hom.app ((moduleCatBaseChange Λ f).obj N) :=
  -- Both sides send `1 ⊗ n` to `1 ⊗ (1 ⊗ (1 ⊗ n))`. `simp` would first rewrite the objects
  -- `(F ⋙ G).obj N` in the types of the linear maps to `G.obj (F.obj N)`, after which the
  -- evaluation lemmas of the comparisons no longer match, so the composites are evaluated by `rw`.
  moduleCatBaseChange_hom_ext Λ fgh fun n ↦ by
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      moduleCatBaseChangeComp_hom_app_hom_tmul, moduleCatBaseChange_map_hom_tmul,
      moduleCatBaseChangeComp_hom_app_hom_tmul, moduleCatBaseChangeComp_hom_app_hom_tmul,
      moduleCatBaseChangeComp_hom_app_hom_tmul]

/-- The left unit law of the comparisons: the composition comparison for `𝟙 R ≫ f = f`,
followed by the base change along `f` of the unit comparison for `R`, is the identity of
`S ⊗[R] N`. -/
lemma moduleCatBaseChangeComp_left_unitality (f : R ⟶ S) (hf : 𝟙 R ≫ f = f)
    (N : ModuleCat.{u} (R ⊗[k] Λ)) :
    (moduleCatBaseChangeComp Λ (𝟙 R) f f hf).hom.app N ≫
      (moduleCatBaseChange Λ f).map ((moduleCatBaseChangeId Λ R).hom.app N) = 𝟙 _ :=
  -- Both sides send `1 ⊗ n` to `1 ⊗ (1 • n)`; as in `moduleCatBaseChangeComp_associativity`,
  -- the composite is evaluated by `rw`.
  moduleCatBaseChange_hom_ext Λ f fun n ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatBaseChangeComp_hom_app_hom_tmul,
      moduleCatBaseChange_map_hom_tmul, moduleCatBaseChangeId_hom_app_hom_tmul, one_smul,
      ModuleCat.hom_id, LinearMap.id_apply]

/-- The right unit law of the comparisons: the composition comparison for `f ≫ 𝟙 S = f`,
followed by the unit comparison for `S` at `S ⊗[R] N`, is the identity of `S ⊗[R] N`. -/
lemma moduleCatBaseChangeComp_right_unitality (f : R ⟶ S) (hf : f ≫ 𝟙 S = f)
    (N : ModuleCat.{u} (R ⊗[k] Λ)) :
    (moduleCatBaseChangeComp Λ f (𝟙 S) f hf).hom.app N ≫
      (moduleCatBaseChangeId Λ S).hom.app ((moduleCatBaseChange Λ f).obj N) = 𝟙 _ :=
  -- Both sides send `1 ⊗ n` to `1 • (1 ⊗ n)`; as in `moduleCatBaseChangeComp_associativity`,
  -- the composite is evaluated by `rw`.
  moduleCatBaseChange_hom_ext Λ f fun n ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, moduleCatBaseChangeComp_hom_app_hom_tmul,
      moduleCatBaseChangeId_hom_app_hom_tmul, one_smul, ModuleCat.hom_id, LinearMap.id_apply]

end Comparison

variable (k) in
/-- The modules over `Λ` with coefficients in the commutative `k`-algebras, as a pseudofunctor
`LocallyDiscrete (CommAlgCat k) ⥤ᵖ Cat`: `R ↦ ModuleCat (R ⊗[k] Λ)`, with the base-change
functors `CommAlgCat.moduleCatBaseChange Λ f` and the comparisons
`CommAlgCat.moduleCatBaseChangeId` and `CommAlgCat.moduleCatBaseChangeComp`. -/
@[expose] noncomputable def moduleCatBaseChangePseudofunctor :
    LocallyDiscrete (CommAlgCat.{u} k) ⥤ᵖ Cat.{u, max (u + 1) v} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun R ↦ Cat.of (ModuleCat.{u} (R ⊗[k] Λ)))
    (fun f ↦ moduleCatBaseChange Λ f) (moduleCatBaseChangeId Λ)
    (fun f g fg h ↦ moduleCatBaseChangeComp Λ f g fg h)
    (moduleCatBaseChangeComp_associativity Λ) (moduleCatBaseChangeComp_left_unitality Λ)
    (moduleCatBaseChangeComp_right_unitality Λ)

variable (k) in
@[simp]
lemma moduleCatBaseChangePseudofunctor_obj (R : LocallyDiscrete (CommAlgCat.{u} k)) :
    (moduleCatBaseChangePseudofunctor k Λ).obj R = Cat.of (ModuleCat.{u} (R.as ⊗[k] Λ)) :=
  rfl

@[simp]
lemma moduleCatBaseChangePseudofunctor_map_toFunctor {R S : LocallyDiscrete (CommAlgCat.{u} k)}
    (f : R ⟶ S) :
    ((moduleCatBaseChangePseudofunctor k Λ).map f).toFunctor = moduleCatBaseChange Λ f.as :=
  rfl

@[simp]
lemma moduleCatBaseChangePseudofunctor_mapId_hom_toNatTrans_app
    (R : LocallyDiscrete (CommAlgCat.{u} k)) (N : ModuleCat.{u} (R.as ⊗[k] Λ)) :
    ((moduleCatBaseChangePseudofunctor k Λ).mapId R).hom.toNatTrans.app N =
      (moduleCatBaseChangeId Λ R.as).hom.app N :=
  rfl

@[simp]
lemma moduleCatBaseChangePseudofunctor_mapComp_hom_toNatTrans_app
    {R S T : LocallyDiscrete (CommAlgCat.{u} k)} (f : R ⟶ S) (g : S ⟶ T)
    (N : ModuleCat.{u} (R.as ⊗[k] Λ)) :
    ((moduleCatBaseChangePseudofunctor k Λ).mapComp f g).hom.toNatTrans.app N =
      (moduleCatBaseChangeComp Λ f.as g.as (f.as ≫ g.as) rfl).hom.app N :=
  rfl

@[simp]
lemma moduleCatBaseChangePseudofunctor_mapId_inv_toNatTrans_app
    (R : LocallyDiscrete (CommAlgCat.{u} k)) (N : ModuleCat.{u} (R.as ⊗[k] Λ)) :
    ((moduleCatBaseChangePseudofunctor k Λ).mapId R).inv.toNatTrans.app N =
      (moduleCatBaseChangeId Λ R.as).inv.app N :=
  rfl

@[simp]
lemma moduleCatBaseChangePseudofunctor_mapComp_inv_toNatTrans_app
    {R S T : LocallyDiscrete (CommAlgCat.{u} k)} (f : R ⟶ S) (g : S ⟶ T)
    (N : ModuleCat.{u} (R.as ⊗[k] Λ)) :
    ((moduleCatBaseChangePseudofunctor k Λ).mapComp f g).inv.toNatTrans.app N =
      (moduleCatBaseChangeComp Λ f.as g.as (f.as ≫ g.as) rfl).inv.app N :=
  rfl

end CommAlgCat
