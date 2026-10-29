/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The method of acyclic models

Let `F` and `G` be functors from a category `C` to chain complexes of modules over a ring `k`.
Suppose that `F` is **free on models**: in each degree `n` there are a model `Mₙ : C` and a
generator `uₙ ∈ Fₙ(Mₙ)`, and every element of `Fₙ(X)` is a combination of the images of `uₙ`
under the maps `σ : Mₙ ⟶ X`, with coefficients chosen naturally in `X`
(`ModelPresentation`; the coefficients need not be unique, so this is a presentation rather than
a basis).  Suppose that `G` is **acyclic on the models**: its homology vanishes in positive
degrees on every model, and in degree zero a chain of augmentation zero is a boundary
(`IsAcyclicOn`).  Then:

* a natural chain map `F ⟶ G` exists as soon as it exists in degree zero compatibly with the
  augmentations, provided the augmentation of `F` vanishes on boundaries
  (`ModelPresentation.chainMap`);
* two natural chain maps `F ⟶ G` which agree after augmentation in degree zero are chain
  homotopic (`ModelPresentation.homotopy`).

Both are built degree by degree.  A natural map out of `Fₙ` is determined by its value on the
generator `uₙ`, and every element `t ∈ Gₘ(Mₙ)` determines one,
`ModelPresentation.extend t`.  Its value on the generator need not be `t` itself, since the
coefficients of `uₙ` need not be those of a single basis element; what matters is that the
boundary of the extended map is controlled by the boundary of `t`
(`ModelPresentation.d_extend`).  So at each step it suffices to choose an element of `G(Mₙ)`
whose boundary is a prescribed chain; that chain is a cycle by the previous step, hence a
boundary by acyclicity.  The chosen elements are internal to the construction.

This is the form of the theorem of Eilenberg and Mac Lane used for the comparison of cubical and
simplicial singular chains.  The coefficients `σ ↦ aσ` need not be unique: the normalized cubical
chains are only a natural retract of the free modules on the cubes.

The method is also available with several models in each degree
(`MultiModelPresentation`, `IsAcyclicOnMulti`): the generator and the model are then indexed by
a type `ι n` in each degree `n`, as for the tensor product of two chain complexes, where the
models of degree `n` are indexed by the bidegrees `(p, q)` with `p + q = n`.  The single-model
statements above are the special case of one index, and are derived from the general ones
(`ModelPresentation.toMulti`).

## Main definitions

* `TauCeti.AcyclicModels.ModelPresentation`: a functor free on models.
* `TauCeti.AcyclicModels.ModelPresentation.extend`: the natural map determined by an element on a
  model.
* `TauCeti.AcyclicModels.IsAcyclicOn`: acyclicity of a functor on the models.
* `TauCeti.AcyclicModels.ModelPresentation.chainMap`: the natural chain map extending a
  degree-zero map.
* `TauCeti.AcyclicModels.ModelPresentation.homotopy`: the chain homotopy between two natural
  chain maps.
* `TauCeti.AcyclicModels.MultiModelPresentation`, `TauCeti.AcyclicModels.IsAcyclicOnMulti`,
  `TauCeti.AcyclicModels.MultiModelPresentation.chainMap`,
  `TauCeti.AcyclicModels.MultiModelPresentation.homotopy`: the same with several models in each
  degree.

## References

* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v w w'

namespace TauCeti

namespace AcyclicModels

variable {C : Type w} [Category.{v} C] {k : Type u} [Ring k]

/-- A functor to chain complexes is **free on models** when, in each degree `n`, every element
of `Fₙ(X)` is a combination `Σ aσ • F(σ)(uₙ)` of the images of a generator `uₙ ∈ Fₙ(Mₙ)` on a
model `Mₙ`, with coefficients `σ ↦ aσ` depending linearly and naturally on the element. -/
structure ModelPresentation (F : C ⥤ ChainComplex (ModuleCat.{u} k) ℕ) where
  /-- The model in degree `n`. -/
  model : ℕ → C
  /-- The generator in degree `n`, a chain of the model. -/
  gen (n : ℕ) : (F.obj (model n)).X n
  /-- The coefficients of a chain in terms of the images of the generator. -/
  coord (X : C) (n : ℕ) : (F.obj X).X n →ₗ[k] ((model n ⟶ X) →₀ k)
  /-- The coefficients are natural. -/
  coord_map {X Y : C} (f : X ⟶ Y) (n : ℕ) (x : (F.obj X).X n) :
    coord Y n ((F.map f).f n x) = mapDomain (· ≫ f) (coord X n x)
  /-- Every chain is the combination of the images of the generator with its coefficients. -/
  sum_coord (X : C) (n : ℕ) (x : (F.obj X).X n) :
    (coord X n x).sum (fun σ a ↦ a • (F.map σ).f n (gen n)) = x

/-- A functor to chain complexes is **acyclic on the models** `M` for the augmentation `ε` when,
on every model, its cycles of positive degree are boundaries and its `0`-chains of augmentation
zero are boundaries. -/
structure IsAcyclicOn (G : C ⥤ ChainComplex (ModuleCat.{u} k) ℕ) (M : ℕ → C)
    (ε : ∀ X : C, (G.obj X).X 0 →ₗ[k] k) : Prop where
  exists_d_eq_of_d_eq_zero (n q : ℕ) (z : (G.obj (M n)).X (q + 1))
    (hz : (G.obj (M n)).d (q + 1) q z = 0) : ∃ b, (G.obj (M n)).d (q + 2) (q + 1) b = z
  exists_d_eq_of_augment_eq_zero (n : ℕ) (z : (G.obj (M n)).X 0) (hz : ε (M n) z = 0) :
    ∃ b, (G.obj (M n)).d 1 0 b = z

variable {F G : C ⥤ ChainComplex (ModuleCat.{u} k) ℕ}

namespace ModelPresentation

variable (B : ModelPresentation F)

/-- The natural map `Fₙ(X) → Gₘ(X)` determined by an element `t ∈ Gₘ(Mₙ)`:
`Σ aσ • F(σ)(uₙ) ↦ Σ aσ • G(σ)(t)`. -/
def extend {m n : ℕ} (t : (G.obj (B.model n)).X m) (X : C) : (F.obj X).X n →ₗ[k] (G.obj X).X m :=
  linearCombination k (fun σ ↦ ((G.map σ).f m).hom t) ∘ₗ B.coord X n

theorem extend_apply {m n : ℕ} (t : (G.obj (B.model n)).X m) (X : C) (x : (F.obj X).X n) :
    B.extend t X x = (B.coord X n x).sum fun σ a ↦ a • (G.map σ).f m t := by
  simp [extend, linearCombination_apply]

end ModelPresentation

/-- A functor to chain complexes is **free on a family of models** when, in each degree `n`, there
is a family of models `Mₙᵢ` indexed by `i : ι n`, with generators `uₙᵢ ∈ Fₙ(Mₙᵢ)`, such that every
element of `Fₙ(X)` is a combination `Σ aσ • F(σ)(uₙᵢ)` over the pairs `(i, σ : Mₙᵢ ⟶ X)`, with
coefficients depending linearly and naturally on the element.  With `ι n` a singleton this is
`ModelPresentation`. -/
structure MultiModelPresentation (F : C ⥤ ChainComplex (ModuleCat.{u} k) ℕ)
    (ι : ℕ → Type w') where
  /-- The models in degree `n`. -/
  model (n : ℕ) : ι n → C
  /-- The generators in degree `n`, chains of the models. -/
  gen (n : ℕ) (i : ι n) : (F.obj (model n i)).X n
  /-- The coefficients of a chain in terms of the images of the generators. -/
  coord (X : C) (n : ℕ) : (F.obj X).X n →ₗ[k] ((Σ i : ι n, (model n i ⟶ X)) →₀ k)
  /-- The coefficients are natural. -/
  coord_map {X Y : C} (f : X ⟶ Y) (n : ℕ) (x : (F.obj X).X n) :
    coord Y n ((F.map f).f n x) =
      mapDomain (fun p : Σ i : ι n, (model n i ⟶ X) ↦
        (⟨p.1, p.2 ≫ f⟩ : Σ i : ι n, (model n i ⟶ Y))) (coord X n x)
  /-- Every chain is the combination of the images of the generators with its coefficients. -/
  sum_coord (X : C) (n : ℕ) (x : (F.obj X).X n) :
    (coord X n x).sum (fun p a ↦ a • (F.map p.2).f n (gen n p.1)) = x

/-- A functor to chain complexes is **acyclic on a family of models** `M` for the augmentation
`ε` when, on every model of every degree, its cycles of positive degree are boundaries and its
`0`-chains of augmentation zero are boundaries. -/
structure IsAcyclicOnMulti (G : C ⥤ ChainComplex (ModuleCat.{u} k) ℕ) {ι : ℕ → Type w'}
    (M : ∀ n, ι n → C) (ε : ∀ X : C, (G.obj X).X 0 →ₗ[k] k) : Prop where
  exists_d_eq_of_d_eq_zero (n : ℕ) (i : ι n) (q : ℕ) (z : (G.obj (M n i)).X (q + 1))
    (hz : (G.obj (M n i)).d (q + 1) q z = 0) : ∃ b, (G.obj (M n i)).d (q + 2) (q + 1) b = z
  exists_d_eq_of_augment_eq_zero (n : ℕ) (i : ι n) (z : (G.obj (M n i)).X 0)
    (hz : ε (M n i) z = 0) : ∃ b, (G.obj (M n i)).d 1 0 b = z

namespace MultiModelPresentation

variable {ι : ℕ → Type w'} (B : MultiModelPresentation F ι)

/-- The natural map `Fₙ(X) → Gₘ(X)` determined by elements `tᵢ ∈ Gₘ(Mₙᵢ)` of the models:
`Σ aσ • F(σ)(uₙᵢ) ↦ Σ aσ • G(σ)(tᵢ)`. -/
def extend {m n : ℕ} (t : ∀ i : ι n, (G.obj (B.model n i)).X m) (X : C) :
    (F.obj X).X n →ₗ[k] (G.obj X).X m :=
  linearCombination k
      (fun p : Σ i : ι n, (B.model n i ⟶ X) ↦ ((G.map p.2).f m).hom (t p.1)) ∘ₗ B.coord X n

theorem extend_apply {m n : ℕ} (t : ∀ i : ι n, (G.obj (B.model n i)).X m) (X : C)
    (x : (F.obj X).X n) :
    B.extend t X x = (B.coord X n x).sum fun p a ↦ a • (G.map p.2).f m (t p.1) := by
  simp [extend, linearCombination_apply]

/-- The map determined by elements on the models is natural. -/
theorem extend_map {m n : ℕ} (t : ∀ i : ι n, (G.obj (B.model n i)).X m) {X Y : C} (f : X ⟶ Y)
    (x : (F.obj X).X n) : B.extend t Y ((F.map f).f n x) = (G.map f).f m (B.extend t X x) := by
  rw [extend_apply, extend_apply, B.coord_map,
    sum_mapDomain_index
      (h := fun (p : Σ i : ι n, (B.model n i ⟶ Y)) a ↦ a • (G.map p.2).f m (t p.1))
      (fun _ ↦ zero_smul k _) (fun _ _ _ ↦ add_smul _ _ _), map_finsuppSum]
  refine Finsupp.sum_congr fun p _ ↦ ?_
  dsimp only
  rw [map_smul, Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply]

/-- The map `extend t` determined by elements `tᵢ ∈ Gₘ(Mₙᵢ)` of the models, as a natural
transformation from the degree-`n` chains of `F` to the degree-`m` chains of `G`. -/
def extendNatTrans {m n : ℕ} (t : ∀ i : ι n, (G.obj (B.model n i)).X m) :
    F ⋙ HomologicalComplex.eval _ _ n ⟶ G ⋙ HomologicalComplex.eval _ _ m where
  app X := ModuleCat.ofHom (B.extend t X)
  naturality _ _ f := by
    ext x
    exact B.extend_map t f x

/-- The component of `extendNatTrans t` at `X` is the map `extend t X`. -/
@[simp]
theorem extendNatTrans_app {m n : ℕ} (t : ∀ i : ι n, (G.obj (B.model n i)).X m) (X : C) :
    (B.extendNatTrans t).app X = ModuleCat.ofHom (B.extend t X) :=
  (rfl)

/-- A natural map `φ : Fₙ ⟶ Gₘ` is the map determined, through `extend`, by its values `φ(uₙᵢ)` on
the generators; in particular, it is determined by these values. -/
theorem eq_extend {m n : ℕ}
    (φ : F ⋙ HomologicalComplex.eval _ _ n ⟶ G ⋙ HomologicalComplex.eval _ _ m) (X : C)
    (x : (F.obj X).X n) : φ.app X x = B.extend (fun i ↦ φ.app (B.model n i) (B.gen n i)) X x := by
  conv_lhs => rw [← B.sum_coord X n x]
  simp only [map_finsuppSum, map_smul, extend_apply]
  exact Finsupp.sum_congr fun p _ ↦ congrArg _ <| φ.naturality_apply p.2 _

/-- The augmentation of the map determined by elements `tᵢ` of the models is the augmentation of
the source, when the augmentations are natural and each `tᵢ` has the augmentation of the
generator. -/
theorem augment_extend {εF : ∀ X : C, (F.obj X).X 0 →ₗ[k] k}
    {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
    (hεF : ∀ {X Y : C} (f : X ⟶ Y) x, εF Y ((F.map f).f 0 x) = εF X x)
    (hεG : ∀ {X Y : C} (f : X ⟶ Y) x, εG Y ((G.map f).f 0 x) = εG X x)
    (t : ∀ i : ι 0, (G.obj (B.model 0 i)).X 0)
    (ht : ∀ i, εG (B.model 0 i) (t i) = εF (B.model 0 i) (B.gen 0 i)) (X : C)
    (x : (F.obj X).X 0) : εG X (B.extend t X x) = εF X x := by
  conv_rhs => rw [← B.sum_coord X 0 x]
  rw [extend_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun p _ ↦ ?_
  rw [map_smul, map_smul, hεF, hεG, ht]

/-- Two natural chain maps `f, g : F ⟶ G` have the same augmentation in degree zero as soon as they
have the same augmentation on the generators of the models of degree zero, when the augmentation
of `G` is natural.  It reduces the hypothesis of `MultiModelPresentation.homotopy` to a check on
the generators. -/
theorem augment_eq_of_gen {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
    (hεG : ∀ {X Y : C} (f : X ⟶ Y) x, εG Y ((G.map f).f 0 x) = εG X x) (f g : F ⟶ G)
    (h : ∀ i : ι 0, εG (B.model 0 i) ((f.app (B.model 0 i)).f 0 (B.gen 0 i)) =
      εG (B.model 0 i) ((g.app (B.model 0 i)).f 0 (B.gen 0 i))) (X : C) (x : (F.obj X).X 0) :
    εG X ((f.app X).f 0 x) = εG X ((g.app X).f 0 x) := by
  have e := B.eq_extend (Functor.whiskerRight f (HomologicalComplex.eval _ _ 0)) X x
  simp only [Functor.whiskerRight_app, HomologicalComplex.eval_map] at e
  rw [e]
  refine B.augment_extend (εF := fun X ↦ εG X ∘ₗ ((g.app X).f 0).hom) (fun σ y ↦ ?_) hεG
    (fun i ↦ (f.app (B.model 0 i)).f 0 (B.gen 0 i)) h X x
  have := congr($(g.naturality σ).f 0 y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at this
  simp only [LinearMap.comp_apply, this, hεG]

/-- **The boundary of a map determined on the models**: if the boundary of each `tᵢ` is the value
on the generator `uₙᵢ` of a natural transformation `R`, then the boundary of the map determined by
the `tᵢ` is `R`. -/
theorem d_extend {m m' n : ℕ} (t : ∀ i : ι n, (G.obj (B.model n i)).X m)
    (R : F ⋙ HomologicalComplex.eval _ _ n ⟶ G ⋙ HomologicalComplex.eval _ _ m')
    (ht : ∀ i, (G.obj (B.model n i)).d m m' (t i) = R.app (B.model n i) (B.gen n i)) (X : C)
    (x : (F.obj X).X n) : (G.obj X).d m m' (B.extend t X x) = R.app X x := by
  -- `R` is the map determined by the boundaries of the `tᵢ`
  rw [B.eq_extend R, ← funext ht, extend_apply, extend_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun p _ ↦ ?_
  rw [map_smul, HomologicalComplex.Hom.comm_apply]

/-- The boundary followed by the map determined by `t`, as a natural transformation, takes `x` to
`extend t (∂ x)`. -/
private theorem whiskerLeft_dNatTrans_comp_extendNatTrans_app_apply {m n : ℕ}
    (t : ∀ i : ι n, (G.obj (B.model n i)).X m) (X : C) (x : (F.obj X).X (n + 1)) :
    (F.whiskerLeft (HomologicalComplex.dNatTrans _ _ (n + 1) n) ≫ B.extendNatTrans t).app X x =
      B.extend t X ((F.obj X).d (n + 1) n x) := by
  simp

/-- If the boundary of each `tᵢ` is the image of the boundary of the generator under the map
determined by `t'`, then the boundary of the map determined by `t` is the map determined by `t'`
applied to the boundary. -/
private theorem d_extend_eq_extend_d {m n : ℕ}
    (t : ∀ i : ι (n + 1), (G.obj (B.model (n + 1) i)).X (m + 1))
    (t' : ∀ i : ι n, (G.obj (B.model n i)).X m)
    (ht : ∀ i, (G.obj (B.model (n + 1) i)).d (m + 1) m (t i) =
      B.extend t' (B.model (n + 1) i) ((F.obj (B.model (n + 1) i)).d (n + 1) n (B.gen (n + 1) i)))
    (X : C) (x : (F.obj X).X (n + 1)) :
    (G.obj X).d (m + 1) m (B.extend t X x) = B.extend t' X ((F.obj X).d (n + 1) n x) := by
  rw [B.d_extend t
      (F.whiskerLeft (HomologicalComplex.dNatTrans _ _ (n + 1) n) ≫ B.extendNatTrans t')
      fun i ↦ (ht i).trans (B.whiskerLeft_dNatTrans_comp_extendNatTrans_app_apply _ _ _).symm,
    B.whiskerLeft_dNatTrans_comp_extendNatTrans_app_apply]

section ChainMap

variable {εF : ∀ X : C, (F.obj X).X 0 →ₗ[k] k} {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
  (hG : IsAcyclicOnMulti G B.model εG) (hεF : ∀ X x, εF X ((F.obj X).d 1 0 x) = 0)
  (t₀ : ∀ i : ι 0, (G.obj (B.model 0 i)).X 0) (ht₀ : ∀ X x, εG X (B.extend t₀ X x) = εF X x)

open Classical in
/-- The elements of the models chosen degree by degree to define the components of the natural
chain map extending `B.extend t₀` through `MultiModelPresentation.extend`. -/
private def chainMapGen (t₀ : ∀ i : ι 0, (G.obj (B.model 0 i)).X 0) :
    (n : ℕ) → (i : ι n) → (G.obj (B.model n i)).X n
  | 0, i => t₀ i
  | n + 1, i =>
    if h : ∃ b, (G.obj (B.model (n + 1) i)).d (n + 1) n b =
        B.extend (chainMapGen t₀ n) (B.model (n + 1) i)
          ((F.obj (B.model (n + 1) i)).d (n + 1) n (B.gen (n + 1) i))
    then h.choose else 0

/-- In degree zero the chosen elements are the given ones. -/
private theorem chainMapGen_zero (t₀ : ∀ i : ι 0, (G.obj (B.model 0 i)).X 0) :
    B.chainMapGen t₀ 0 = t₀ :=
  funext fun i ↦ chainMapGen.eq_1 B t₀ i

include hG hεF ht₀ in
/-- The boundary of the element chosen on a model of degree `n + 1` is the image of the boundary of
its generator under the map determined by the elements chosen in degree `n`. -/
private theorem d_chainMapGen (n : ℕ) (i : ι (n + 1)) :
    (G.obj (B.model (n + 1) i)).d (n + 1) n (B.chainMapGen t₀ (n + 1) i) =
      B.extend (B.chainMapGen t₀ n) (B.model (n + 1) i)
        ((F.obj (B.model (n + 1) i)).d (n + 1) n (B.gen (n + 1) i)) := by
  induction n with
  | zero =>
    rw [chainMapGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd (hG.exists_d_eq_of_augment_eq_zero 1 i _ ?_) hex
    rw [chainMapGen_zero, ht₀, hεF]
  | succ n ih =>
    rw [chainMapGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd (hG.exists_d_eq_of_d_eq_zero (n + 2) i n _ ?_) hex
    rw [B.d_extend_eq_extend_d _ _ ih, HomologicalComplex.d_comp_d_apply, map_zero]

include hG hεF ht₀ in
/-- The maps determined by the chosen elements commute with the boundaries. -/
private theorem d_extend_chainMapGen (n : ℕ) (X : C) (x : (F.obj X).X (n + 1)) :
    (G.obj X).d (n + 1) n (B.extend (B.chainMapGen t₀ (n + 1)) X x) =
      B.extend (B.chainMapGen t₀ n) X ((F.obj X).d (n + 1) n x) :=
  B.d_extend_eq_extend_d _ _ (B.d_chainMapGen hG hεF t₀ ht₀ n) X x

/-- **Existence of natural chain maps**: if `G` is acyclic on the models of `F` and the augmentation
of `F` vanishes on boundaries, the natural map `F₀ → G₀` determined by `t₀`, compatible with the
augmentations, extends to a natural chain map `F ⟶ G`. -/
def chainMap : F ⟶ G where
  app X := ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (B.extend (B.chainMapGen t₀ n) X))
    fun n ↦ by
      ext x
      exact B.d_extend_chainMapGen hG hεF t₀ ht₀ n X x
  naturality X Y f := by
    ext n x
    exact B.extend_map _ f x

/-- In degree zero the natural chain map is the map determined by `t₀`. -/
@[simp]
theorem chainMap_app_f_zero_apply (X : C) (x : (F.obj X).X 0) :
    ((B.chainMap hG hεF t₀ ht₀).app X).f 0 x = B.extend t₀ X x :=
  (rfl)

end ChainMap

section Homotopy

variable {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k} (hG : IsAcyclicOnMulti G B.model εG)
  (f g : F ⟶ G) (hfg : ∀ X x, εG X ((f.app X).f 0 x) = εG X ((g.app X).f 0 x))

open Classical in
/-- The elements of the models chosen degree by degree to define the components of the chain
homotopy between two natural chain maps through `MultiModelPresentation.extend`. -/
private def homotopyGen : (n : ℕ) → (i : ι n) → (G.obj (B.model n i)).X (n + 1)
  | 0, i =>
    if h : ∃ b, (G.obj (B.model 0 i)).d 1 0 b =
        (f.app (B.model 0 i)).f 0 (B.gen 0 i) - (g.app (B.model 0 i)).f 0 (B.gen 0 i)
    then h.choose else 0
  | n + 1, i =>
    if h : ∃ b, (G.obj (B.model (n + 1) i)).d (n + 2) (n + 1) b =
        (f.app (B.model (n + 1) i)).f (n + 1) (B.gen (n + 1) i) -
          (g.app (B.model (n + 1) i)).f (n + 1) (B.gen (n + 1) i) -
          B.extend (homotopyGen n) (B.model (n + 1) i)
            ((F.obj (B.model (n + 1) i)).d (n + 1) n (B.gen (n + 1) i))
    then h.choose else 0

/-- `f - g`, read in degree `n` as a natural transformation, takes `x` to
`(f.app X).f n x - (g.app X).f n x`. -/
private theorem whiskerRight_sub_eval_app_apply (n : ℕ) (X : C) (x : (F.obj X).X n) :
    (Functor.whiskerRight (f - g) (HomologicalComplex.eval _ _ n)).app X x =
      (f.app X).f n x - (g.app X).f n x := by
  simp

include hG hfg in
/-- The homotopy condition in degree zero. -/
private theorem d_extend_homotopyGen_zero (X : C) (x : (F.obj X).X 0) :
    (G.obj X).d 1 0 (B.extend (B.homotopyGen f g 0) X x) = (f.app X).f 0 x - (g.app X).f 0 x := by
  rw [← whiskerRight_sub_eval_app_apply f g]
  refine B.d_extend _ _ (fun i ↦ ?_) X x
  rw [whiskerRight_sub_eval_app_apply, homotopyGen.eq_1]
  split_ifs with hex
  · exact hex.choose_spec
  refine absurd (hG.exists_d_eq_of_augment_eq_zero 0 i _ ?_) hex
  simp [hfg]

/-- The natural transformation `x ↦ f x - g x - H (∂ x)` on the chains of degree `n + 1`, where `H`
is the map determined by the elements chosen in degree `n`: the boundaries prescribed for the
elements chosen in degree `n + 1` are its values on the generators. -/
private def homotopyTarget (n : ℕ) :
    F ⋙ HomologicalComplex.eval _ _ (n + 1) ⟶ G ⋙ HomologicalComplex.eval _ _ (n + 1) :=
  Functor.whiskerRight f (HomologicalComplex.eval _ _ (n + 1)) -
    Functor.whiskerRight g (HomologicalComplex.eval _ _ (n + 1)) -
    F.whiskerLeft (HomologicalComplex.dNatTrans _ _ (n + 1) n) ≫
      B.extendNatTrans (B.homotopyGen f g n)

private theorem homotopyTarget_app_apply (n : ℕ) (X : C) (x : (F.obj X).X (n + 1)) :
    (B.homotopyTarget f g n).app X x = (f.app X).f (n + 1) x - (g.app X).f (n + 1) x -
      B.extend (B.homotopyGen f g n) X ((F.obj X).d (n + 1) n x) := by
  simp [homotopyTarget]

include hG hfg in
/-- In positive degrees, the chosen elements have the prescribed boundaries. -/
private theorem d_homotopyGen_succ (n : ℕ) (i : ι (n + 1)) :
    (G.obj (B.model (n + 1) i)).d (n + 2) (n + 1) (B.homotopyGen f g (n + 1) i) =
      (B.homotopyTarget f g n).app (B.model (n + 1) i) (B.gen (n + 1) i) := by
  induction n with
  | zero =>
    rw [homotopyGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd (hG.exists_d_eq_of_d_eq_zero 1 i 0 _ ?_) hex
    rw [map_sub, map_sub, B.d_extend_homotopyGen_zero hG f g hfg,
      HomologicalComplex.Hom.comm_apply, HomologicalComplex.Hom.comm_apply, sub_self]
  | succ n ih =>
    rw [homotopyGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd (hG.exists_d_eq_of_d_eq_zero (n + 2) i (n + 1) _ ?_) hex
    rw [map_sub, map_sub, B.d_extend _ (B.homotopyTarget f g n) ih, homotopyTarget_app_apply,
      HomologicalComplex.d_comp_d_apply, map_zero, sub_zero, HomologicalComplex.Hom.comm_apply,
      HomologicalComplex.Hom.comm_apply, sub_self]

include hG hfg in
/-- The homotopy condition in positive degrees. -/
private theorem d_extend_homotopyGen_succ (n : ℕ) (X : C) (x : (F.obj X).X (n + 1)) :
    (G.obj X).d (n + 2) (n + 1) (B.extend (B.homotopyGen f g (n + 1)) X x) = (f.app X).f (n + 1) x -
      (g.app X).f (n + 1) x - B.extend (B.homotopyGen f g n) X ((F.obj X).d (n + 1) n x) := by
  rw [B.d_extend _ (B.homotopyTarget f g n) (B.d_homotopyGen_succ hG f g hfg n),
    homotopyTarget_app_apply]

/-- The components of the chain homotopy: `Fᵢ(X) → Gⱼ(X)`, determined on the models when
`j = i + 1`, and zero otherwise. -/
private def homotopyHom (X : C) (i j : ℕ) : (F.obj X).X i ⟶ (G.obj X).X j :=
  if h : i + 1 = j then
    ModuleCat.ofHom (B.extend (B.homotopyGen f g i) X) ≫ eqToHom (by rw [h])
  else 0

private theorem homotopyHom_succ (X : C) (i : ℕ) :
    B.homotopyHom f g X i (i + 1) = ModuleCat.ofHom (B.extend (B.homotopyGen f g i) X) := by
  simp [homotopyHom]

/-- **Uniqueness up to homotopy of natural chain maps**: two natural chain maps `F ⟶ G` which
agree after augmentation in degree zero are chain homotopic, if `G` is acyclic on the models of
`F`.  The homotopy is natural (`MultiModelPresentation.homotopy_hom_naturality`). -/
def homotopy (X : C) : Homotopy (f.app X) (g.app X) where
  hom := B.homotopyHom f g X
  zero i j hij := by
    have : ¬ i + 1 = j := by simpa [ComplexShape.down_Rel] using hij
    simp only [homotopyHom, this, ↓reduceDIte]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, homotopyHom_succ,
        zero_add]
      ext x
      simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
        ModuleCat.hom_ofHom]
      rw [B.d_extend_homotopyGen_zero hG f g hfg, sub_add_cancel]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, homotopyHom_succ,
        homotopyHom_succ]
      ext x
      simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
        ModuleCat.hom_ofHom]
      rw [B.d_extend_homotopyGen_succ hG f g hfg]
      abel

private theorem homotopy_hom (X : C) : (B.homotopy hG f g hfg X).hom = B.homotopyHom f g X :=
  (rfl)

/-- The components of the chain homotopy vanish off the shape of the complexes. -/
@[simp]
theorem homotopy_hom_eq_zero (X : C) {i j : ℕ} (h : i + 1 ≠ j) :
    (B.homotopy hG f g hfg X).hom i j = 0 := by
  simp only [homotopy_hom, homotopyHom, h, ↓reduceDIte]

/-- The chain homotopy is natural. -/
theorem homotopy_hom_naturality {X Y : C} (φ : X ⟶ Y) (i j : ℕ) :
    (F.map φ).f i ≫ (B.homotopy hG f g hfg Y).hom i j =
      (B.homotopy hG f g hfg X).hom i j ≫ (G.map φ).f j := by
  rw [homotopy_hom, homotopy_hom]
  by_cases h : i + 1 = j
  · subst h
    rw [homotopyHom_succ, homotopyHom_succ]
    ext x
    exact B.extend_map _ φ x
  · simp [homotopyHom, h]

end Homotopy

end MultiModelPresentation

namespace ModelPresentation

variable (B : ModelPresentation F)

/-- A presentation by one model in each degree is a presentation by a family of models indexed
by a singleton. -/
-- The body is exposed so that `B.toMulti.model n i` reduces to `B.model n` in the statements of
-- `toMulti_gen`, `toMulti_coord` and `toMulti_extend`.
@[expose] def toMulti : MultiModelPresentation F (fun _ ↦ PUnit.{1}) where
  model n _ := B.model n
  gen n _ := B.gen n
  coord X n := lmapDomain k k
    (fun σ : B.model n ⟶ X ↦ (⟨PUnit.unit, σ⟩ : Σ _ : PUnit.{1}, (B.model n ⟶ X))) ∘ₗ
      B.coord X n
  coord_map f n x := by
    simp only [LinearMap.coe_comp, Function.comp_apply, lmapDomain_apply, B.coord_map]
    rw [← mapDomain_comp, ← mapDomain_comp]
    -- both sides push `B.coord X n x` forward along `σ ↦ ⟨PUnit.unit, σ ≫ f⟩`, the two
    -- compositions agreeing by the definition of the maps of sigma types
    rfl
  sum_coord X n x := by
    simp only [LinearMap.coe_comp, Function.comp_apply, lmapDomain_apply]
    rw [sum_mapDomain_index
      (h := fun (p : Σ _ : PUnit.{1}, (B.model n ⟶ X)) a ↦ a • (F.map p.2).f n (B.gen n))
      (fun _ ↦ zero_smul k _) (fun _ _ _ ↦ add_smul _ _ _)]
    exact B.sum_coord X n x

/-- The models of `toMulti` are the models of the presentation. -/
@[simp]
theorem toMulti_model (n : ℕ) (i : PUnit.{1}) : B.toMulti.model n i = B.model n :=
  (rfl)

/-- The generators of `toMulti` are the generators of the presentation. -/
@[simp]
theorem toMulti_gen (n : ℕ) (i : PUnit.{1}) : B.toMulti.gen n i = B.gen n :=
  (rfl)

/-- The coefficients of `toMulti` are those of the presentation, indexed by the singleton. -/
@[simp]
theorem toMulti_coord (X : C) (n : ℕ) (x : (F.obj X).X n) :
    B.toMulti.coord X n x =
      mapDomain (fun σ : B.model n ⟶ X ↦ (⟨PUnit.unit, σ⟩ : Σ _ : PUnit.{1}, (B.model n ⟶ X)))
        (B.coord X n x) :=
  (rfl)

/-- The map determined by one element on the model is the map determined by the corresponding
family of elements. -/
@[simp]
theorem toMulti_extend {m n : ℕ} (t : (G.obj (B.model n)).X m) (X : C) (x : (F.obj X).X n) :
    B.toMulti.extend (fun _ ↦ t) X x = B.extend t X x := by
  refine (MultiModelPresentation.extend_apply B.toMulti (fun _ ↦ t) X x).trans ?_
  rw [extend_apply, toMulti_coord]
  exact sum_mapDomain_index
    (h := fun (p : Σ _ : PUnit.{1}, (B.model n ⟶ X)) a ↦ a • (G.map p.2).f m t)
    (fun _ ↦ zero_smul k _) (fun _ _ _ ↦ add_smul _ _ _)

/-- The augmentation of the map determined by an element `t` on the model is the augmentation of
the source, when the augmentations are natural and `t` has the augmentation of the generator. -/
theorem augment_extend {εF : ∀ X : C, (F.obj X).X 0 →ₗ[k] k} {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
    (hεF : ∀ {X Y : C} (f : X ⟶ Y) x, εF Y ((F.map f).f 0 x) = εF X x)
    (hεG : ∀ {X Y : C} (f : X ⟶ Y) x, εG Y ((G.map f).f 0 x) = εG X x)
    (t : (G.obj (B.model 0)).X 0) (ht : εG (B.model 0) t = εF (B.model 0) (B.gen 0)) (X : C)
    (x : (F.obj X).X 0) : εG X (B.extend t X x) = εF X x := by
  rw [← toMulti_extend]
  exact B.toMulti.augment_extend hεF hεG (fun _ ↦ t) (fun _ ↦ ht) X x

/-- Two natural chain maps `f, g : F ⟶ G` have the same augmentation in degree zero as soon as they
have the same augmentation on the generator of the model of degree zero, when the augmentation of
`G` is natural. -/
theorem augment_eq_of_gen {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
    (hεG : ∀ {X Y : C} (f : X ⟶ Y) x, εG Y ((G.map f).f 0 x) = εG X x) (f g : F ⟶ G)
    (h : εG (B.model 0) ((f.app (B.model 0)).f 0 (B.gen 0)) =
      εG (B.model 0) ((g.app (B.model 0)).f 0 (B.gen 0))) (X : C) (x : (F.obj X).X 0) :
    εG X ((f.app X).f 0 x) = εG X ((g.app X).f 0 x) :=
  B.toMulti.augment_eq_of_gen hεG f g (fun _ ↦ h) X x

/-- The map determined by an element on the model is natural. -/
theorem extend_map {m n : ℕ} (t : (G.obj (B.model n)).X m) {X Y : C} (f : X ⟶ Y)
    (x : (F.obj X).X n) : B.extend t Y ((F.map f).f n x) = (G.map f).f m (B.extend t X x) := by
  rw [← toMulti_extend, ← toMulti_extend]
  exact B.toMulti.extend_map (fun _ ↦ t) f x

/-- The map `extend t` determined by an element `t ∈ Gₘ(Mₙ)` on the model, as a natural
transformation from the degree-`n` chains of `F` to the degree-`m` chains of `G`. -/
def extendNatTrans {m n : ℕ} (t : (G.obj (B.model n)).X m) :
    F ⋙ HomologicalComplex.eval _ _ n ⟶ G ⋙ HomologicalComplex.eval _ _ m where
  app X := ModuleCat.ofHom (B.extend t X)
  naturality _ _ f := by
    ext x
    exact B.extend_map t f x

/-- The component of `extendNatTrans t` at `X` is the map `extend t X`. -/
@[simp]
theorem extendNatTrans_app {m n : ℕ} (t : (G.obj (B.model n)).X m) (X : C) :
    (B.extendNatTrans t).app X = ModuleCat.ofHom (B.extend t X) :=
  (rfl)

/-- A natural map `φ : Fₙ ⟶ Gₘ` is the map determined, through `extend`, by its value `φ(uₙ)` on
the generator; in particular, it is determined by this value. -/
theorem eq_extend {m n : ℕ}
    (φ : F ⋙ HomologicalComplex.eval _ _ n ⟶ G ⋙ HomologicalComplex.eval _ _ m) (X : C)
    (x : (F.obj X).X n) : φ.app X x = B.extend (φ.app (B.model n) (B.gen n)) X x := by
  rw [← toMulti_extend]
  exact B.toMulti.eq_extend φ X x

/-- **The boundary of a map determined on the model**: if the boundary of `t` is the value on
the generator `uₙ` of a natural transformation `R`, then the boundary of the map determined by
`t` is `R`. -/
theorem d_extend {m m' n : ℕ} (t : (G.obj (B.model n)).X m)
    (R : F ⋙ HomologicalComplex.eval _ _ n ⟶ G ⋙ HomologicalComplex.eval _ _ m')
    (ht : (G.obj (B.model n)).d m m' t = R.app (B.model n) (B.gen n)) (X : C) (x : (F.obj X).X n) :
    (G.obj X).d m m' (B.extend t X x) = R.app X x := by
  rw [← toMulti_extend]
  exact B.toMulti.d_extend (fun _ ↦ t) R (fun _ ↦ ht) X x

/-- Acyclicity on the models of a presentation by one model in each degree is acyclicity on the
family of models of `toMulti`. -/
theorem isAcyclicOnMulti {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
    (hG : IsAcyclicOn G B.model εG) : IsAcyclicOnMulti G B.toMulti.model εG where
  exists_d_eq_of_d_eq_zero n _ q z hz := hG.exists_d_eq_of_d_eq_zero n q z hz
  exists_d_eq_of_augment_eq_zero n _ z hz := hG.exists_d_eq_of_augment_eq_zero n z hz

section ChainMap

variable {εF : ∀ X : C, (F.obj X).X 0 →ₗ[k] k} {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
  (hG : IsAcyclicOn G B.model εG) (hεF : ∀ X x, εF X ((F.obj X).d 1 0 x) = 0)
  (t₀ : (G.obj (B.model 0)).X 0) (ht₀ : ∀ X x, εG X (B.extend t₀ X x) = εF X x)

/-- **Existence of natural chain maps**: if `G` is acyclic on the models of `F` and the augmentation
of `F` vanishes on boundaries, the natural map `F₀ → G₀` determined by `t₀`, compatible with the
augmentations, extends to a natural chain map `F ⟶ G`.  This is the case of one model in each
degree of `MultiModelPresentation.chainMap`. -/
def chainMap : F ⟶ G :=
  B.toMulti.chainMap (isAcyclicOnMulti B hG) hεF (fun _ ↦ t₀) (fun X x ↦ by
    rw [toMulti_extend]
    exact ht₀ X x)

/-- In degree zero the natural chain map is the map determined by `t₀`. -/
@[simp]
theorem chainMap_app_f_zero_apply (X : C) (x : (F.obj X).X 0) :
    ((B.chainMap hG hεF t₀ ht₀).app X).f 0 x = B.extend t₀ X x :=
  (MultiModelPresentation.chainMap_app_f_zero_apply B.toMulti _ hεF _ _ X x).trans
    (toMulti_extend B t₀ X x)

end ChainMap

section Homotopy

variable {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k} (hG : IsAcyclicOn G B.model εG) (f g : F ⟶ G)
  (hfg : ∀ X x, εG X ((f.app X).f 0 x) = εG X ((g.app X).f 0 x))

/-- **Uniqueness up to homotopy of natural chain maps**: two natural chain maps `F ⟶ G` which
agree after augmentation in degree zero are chain homotopic, if `G` is acyclic on the models of
`F`.  The homotopy is natural (`ModelPresentation.homotopy_hom_naturality`). -/
def homotopy (X : C) : Homotopy (f.app X) (g.app X) :=
  B.toMulti.homotopy (isAcyclicOnMulti B hG) f g hfg X

/-- The components of the chain homotopy vanish off the shape of the complexes. -/
@[simp]
theorem homotopy_hom_eq_zero (X : C) {i j : ℕ} (h : i + 1 ≠ j) :
    (B.homotopy hG f g hfg X).hom i j = 0 :=
  MultiModelPresentation.homotopy_hom_eq_zero _ _ f g hfg X h

/-- The chain homotopy is natural. -/
theorem homotopy_hom_naturality {X Y : C} (φ : X ⟶ Y) (i j : ℕ) :
    (F.map φ).f i ≫ (B.homotopy hG f g hfg Y).hom i j =
      (B.homotopy hG f g hfg X).hom i j ≫ (G.map φ).f j :=
  MultiModelPresentation.homotopy_hom_naturality _ _ f g hfg φ i j

end Homotopy

end ModelPresentation

end AcyclicModels

end TauCeti
