/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Algebra.Homology.ModuleCat

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

## Main definitions

* `TauCeti.AcyclicModels.ModelPresentation`: a functor free on models.
* `TauCeti.AcyclicModels.ModelPresentation.extend`: the natural map determined by an element on a
  model.
* `TauCeti.AcyclicModels.IsAcyclicOn`: acyclicity of a functor on the models.
* `TauCeti.AcyclicModels.ModelPresentation.chainMap`: the natural chain map extending a
  degree-zero map.
* `TauCeti.AcyclicModels.ModelPresentation.homotopy`: the chain homotopy between two natural
  chain maps.

## References

* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v w

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

/-- A family of linear maps `Fₙ(X) → Gₘ(X)`, natural in `X`. -/
structure NatLinear (F G : C ⥤ ChainComplex (ModuleCat.{u} k) ℕ) (n m : ℕ) where
  /-- The component at `X`. -/
  app (X : C) : (F.obj X).X n →ₗ[k] (G.obj X).X m
  /-- Naturality. -/
  naturality {X Y : C} (f : X ⟶ Y) (x : (F.obj X).X n) :
    app Y ((F.map f).f n x) = (G.map f).f m (app X x)

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

/-- The natural family `x ↦ φ (∂ x)`, of a natural family `φ` after the boundary of `F`. -/
def NatLinear.compD {m n : ℕ} (φ : NatLinear F G n m) : NatLinear F G (n + 1) m where
  app X := φ.app X ∘ₗ ((F.obj X).d (n + 1) n).hom
  naturality f x := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← φ.naturality, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, (F.map f).comm]

@[simp]
theorem NatLinear.compD_app {m n : ℕ} (φ : NatLinear F G n m) (X : C) (x : (F.obj X).X (n + 1)) :
    φ.compD.app X x = φ.app X ((F.obj X).d (n + 1) n x) :=
  (rfl)

/-- The component of a natural chain map in degree `n`, as a natural family. -/
def NatLinear.ofHom (f : F ⟶ G) (n : ℕ) : NatLinear F G n n where
  app X := ((f.app X).f n).hom
  naturality g x := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, f.naturality]

@[simp]
theorem NatLinear.ofHom_app (f : F ⟶ G) (n : ℕ) (X : C) (x : (F.obj X).X n) :
    (NatLinear.ofHom f n).app X x = (f.app X).f n x :=
  (rfl)

/-- The difference of two natural families. -/
def NatLinear.sub {m n : ℕ} (φ ψ : NatLinear F G n m) : NatLinear F G n m where
  app X := φ.app X - ψ.app X
  naturality f x := by simp [φ.naturality, ψ.naturality]

@[simp]
theorem NatLinear.sub_app {m n : ℕ} (φ ψ : NatLinear F G n m) (X : C) (x : (F.obj X).X n) :
    (φ.sub ψ).app X x = φ.app X x - ψ.app X x :=
  (rfl)

namespace ModelPresentation

variable (B : ModelPresentation F)

/-- The natural map `Fₙ(X) → Gₘ(X)` determined by an element `t ∈ Gₘ(Mₙ)`:
`Σ aσ • F(σ)(uₙ) ↦ Σ aσ • G(σ)(t)`. -/
def extend {m n : ℕ} (t : (G.obj (B.model n)).X m) (X : C) : (F.obj X).X n →ₗ[k] (G.obj X).X m :=
  linearCombination k (fun σ ↦ ((G.map σ).f m).hom t) ∘ₗ B.coord X n

theorem extend_apply {m n : ℕ} (t : (G.obj (B.model n)).X m) (X : C) (x : (F.obj X).X n) :
    B.extend t X x = (B.coord X n x).sum fun σ a ↦ a • (G.map σ).f m t := by
  simp [extend, linearCombination_apply]

/-- The map determined by an element on the model is natural. -/
theorem extend_map {m n : ℕ} (t : (G.obj (B.model n)).X m) {X Y : C} (f : X ⟶ Y)
    (x : (F.obj X).X n) : B.extend t Y ((F.map f).f n x) = (G.map f).f m (B.extend t X x) := by
  rw [extend_apply, extend_apply, B.coord_map,
    sum_mapDomain_index (h := fun σ a ↦ a • (G.map σ).f m t) (fun _ ↦ zero_smul k _)
      (fun _ _ _ ↦ add_smul _ _ _), map_finsuppSum]
  refine Finsupp.sum_congr fun σ _ ↦ ?_
  rw [map_smul, Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply]

/-- The map determined by an element on the model, as a natural family. -/
def extendNat {m n : ℕ} (t : (G.obj (B.model n)).X m) : NatLinear F G n m where
  app := B.extend t
  naturality := B.extend_map t

/-- A natural map is determined by its value on the generator. -/
theorem eq_extend {m n : ℕ} (φ : NatLinear F G n m) (X : C) (x : (F.obj X).X n) :
    φ.app X x = B.extend (φ.app (B.model n) (B.gen n)) X x := by
  conv_lhs => rw [← B.sum_coord X n x]
  rw [extend_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun σ _ ↦ ?_
  rw [map_smul, φ.naturality]

/-- The augmentation of the map determined by an element `t` on the model is the augmentation of
the source, when the augmentations are natural and `t` has the augmentation of the generator. -/
theorem augment_extend {εF : ∀ X : C, (F.obj X).X 0 →ₗ[k] k} {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
    (hεF : ∀ {X Y : C} (f : X ⟶ Y) x, εF Y ((F.map f).f 0 x) = εF X x)
    (hεG : ∀ {X Y : C} (f : X ⟶ Y) x, εG Y ((G.map f).f 0 x) = εG X x)
    (t : (G.obj (B.model 0)).X 0) (ht : εG (B.model 0) t = εF (B.model 0) (B.gen 0)) (X : C)
    (x : (F.obj X).X 0) : εG X (B.extend t X x) = εF X x := by
  conv_rhs => rw [← B.sum_coord X 0 x]
  rw [extend_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun σ _ ↦ ?_
  rw [map_smul, map_smul, hεF, hεG, ht]

/-- **The boundary of a map determined on the model**: if the boundary of `t` is the value on
the generator of a natural family `R`, then the boundary of the map determined by `t` is `R`. -/
theorem d_extend {m m' n : ℕ} (t : (G.obj (B.model n)).X m) (R : NatLinear F G n m')
    (ht : (G.obj (B.model n)).d m m' t = R.app (B.model n) (B.gen n)) (X : C)
    (x : (F.obj X).X n) : (G.obj X).d m m' (B.extend t X x) = R.app X x := by
  conv_rhs => rw [← B.sum_coord X n x]
  rw [extend_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun σ _ ↦ ?_
  rw [map_smul, map_smul, R.naturality, ← ht, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    (G.map σ).comm]

section ChainMap

variable {εF : ∀ X : C, (F.obj X).X 0 →ₗ[k] k} {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k}
  (hG : IsAcyclicOn G B.model εG) (hεF : ∀ X x, εF X ((F.obj X).d 1 0 x) = 0)
  (t₀ : (G.obj (B.model 0)).X 0) (ht₀ : ∀ X x, εG X (B.extend t₀ X x) = εF X x)

open Classical in
/-- The elements of the models chosen degree by degree to define the components of the natural
chain map extending `B.extend t₀` through `ModelPresentation.extend`. -/
private def chainMapGen (t₀ : (G.obj (B.model 0)).X 0) : (n : ℕ) → (G.obj (B.model n)).X n
  | 0 => t₀
  | n + 1 =>
    if h : ∃ b, (G.obj (B.model (n + 1))).d (n + 1) n b =
        B.extend (chainMapGen t₀ n) (B.model (n + 1))
          ((F.obj (B.model (n + 1))).d (n + 1) n (B.gen (n + 1)))
    then h.choose else 0

include hG hεF ht₀ in
/-- The chosen elements have the prescribed boundaries. -/
private theorem d_chainMapGen (n : ℕ) :
    (G.obj (B.model (n + 1))).d (n + 1) n (B.chainMapGen t₀ (n + 1)) =
      B.extend (B.chainMapGen t₀ n) (B.model (n + 1))
        ((F.obj (B.model (n + 1))).d (n + 1) n (B.gen (n + 1))) := by
  classical
  induction n with
  | zero =>
    rw [chainMapGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd ?_ hex
    refine hG.exists_d_eq_of_augment_eq_zero 1 _ ?_
    rw [chainMapGen.eq_1, ht₀, hεF]
  | succ n ih =>
    rw [chainMapGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd ?_ hex
    refine hG.exists_d_eq_of_d_eq_zero (n + 2) n _ ?_
    rw [B.d_extend _ (B.extendNat (B.chainMapGen t₀ n)).compD ih, NatLinear.compD_app,
      HomologicalComplex.d_comp_d_apply, map_zero]

include hG hεF ht₀ in
/-- The maps determined by the chosen elements commute with the boundaries. -/
private theorem d_extend_chainMapGen (n : ℕ) (X : C) (x : (F.obj X).X (n + 1)) :
    (G.obj X).d (n + 1) n (B.extend (B.chainMapGen t₀ (n + 1)) X x) =
      B.extend (B.chainMapGen t₀ n) X ((F.obj X).d (n + 1) n x) :=
  B.d_extend _ (B.extendNat (B.chainMapGen t₀ n)).compD (B.d_chainMapGen hG hεF t₀ ht₀ n) X x

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

variable {εG : ∀ X : C, (G.obj X).X 0 →ₗ[k] k} (hG : IsAcyclicOn G B.model εG) (f g : F ⟶ G)
  (hfg : ∀ X x, εG X ((f.app X).f 0 x) = εG X ((g.app X).f 0 x))

open Classical in
/-- The elements of the models chosen degree by degree to define the components of the chain
homotopy between two natural chain maps through `ModelPresentation.extend`. -/
private def homotopyGen : (n : ℕ) → (G.obj (B.model n)).X (n + 1)
  | 0 =>
    if h : ∃ b, (G.obj (B.model 0)).d 1 0 b =
        (f.app (B.model 0)).f 0 (B.gen 0) - (g.app (B.model 0)).f 0 (B.gen 0)
    then h.choose else 0
  | n + 1 =>
    if h : ∃ b, (G.obj (B.model (n + 1))).d (n + 2) (n + 1) b =
        (f.app (B.model (n + 1))).f (n + 1) (B.gen (n + 1)) -
          (g.app (B.model (n + 1))).f (n + 1) (B.gen (n + 1)) -
          B.extend (homotopyGen n) (B.model (n + 1))
            ((F.obj (B.model (n + 1))).d (n + 1) n (B.gen (n + 1)))
    then h.choose else 0

include hG hfg in
/-- The homotopy condition in degree zero. -/
private theorem d_extend_homotopyGen_zero (X : C) (x : (F.obj X).X 0) :
    (G.obj X).d 1 0 (B.extend (B.homotopyGen f g 0) X x) =
      (f.app X).f 0 x - (g.app X).f 0 x := by
  classical
  have h := B.d_extend (B.homotopyGen f g 0) ((NatLinear.ofHom f 0).sub (NatLinear.ofHom g 0))
    (by
      rw [homotopyGen.eq_1]
      split_ifs with hex
      · exact hex.choose_spec
      refine absurd ?_ hex
      refine hG.exists_d_eq_of_augment_eq_zero 0 _ ?_
      simp [hfg]) X x
  simpa using h

/-- The natural family `x ↦ (f - g) x - H (∂ x)`. -/
private def target (n : ℕ) : NatLinear F G (n + 1) (n + 1) :=
  ((NatLinear.ofHom f (n + 1)).sub (NatLinear.ofHom g (n + 1))).sub
    (B.extendNat (B.homotopyGen f g n)).compD

include hG hfg in
private theorem d_homotopyGen_succ (n : ℕ) :
    (G.obj (B.model (n + 1))).d (n + 2) (n + 1) (B.homotopyGen f g (n + 1)) =
      (target B f g n).app (B.model (n + 1)) (B.gen (n + 1)) := by
  classical
  induction n with
  | zero =>
    rw [homotopyGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd ?_ hex
    refine hG.exists_d_eq_of_d_eq_zero 1 0 _ ?_
    rw [map_sub, map_sub, B.d_extend_homotopyGen_zero hG f g hfg,
      HomologicalComplex.Hom.comm_apply, HomologicalComplex.Hom.comm_apply, sub_self]
  | succ n ih =>
    rw [homotopyGen.eq_2]
    split_ifs with hex
    · exact hex.choose_spec
    refine absurd ?_ hex
    refine hG.exists_d_eq_of_d_eq_zero (n + 2) (n + 1) _ ?_
    have h := B.d_extend _ (target B f g n) ih (B.model (n + 2))
      ((F.obj (B.model (n + 2))).d (n + 2) (n + 1) (B.gen (n + 2)))
    simp only [target, NatLinear.sub_app, NatLinear.ofHom_app, NatLinear.compD_app,
      extendNat] at h ⊢
    rw [map_sub, map_sub, h, HomologicalComplex.d_comp_d_apply, map_zero, sub_zero,
      HomologicalComplex.Hom.comm_apply, HomologicalComplex.Hom.comm_apply, sub_self]

include hG hfg in
/-- The homotopy condition in positive degrees. -/
private theorem d_extend_homotopyGen_succ (n : ℕ) (X : C) (x : (F.obj X).X (n + 1)) :
    (G.obj X).d (n + 2) (n + 1) (B.extend (B.homotopyGen f g (n + 1)) X x) =
      (f.app X).f (n + 1) x - (g.app X).f (n + 1) x -
        B.extend (B.homotopyGen f g n) X ((F.obj X).d (n + 1) n x) := by
  have := B.d_extend _ (target B f g n) (d_homotopyGen_succ B hG f g hfg n) X x
  simpa [target, extendNat] using this

/-- The components of the chain homotopy: `Fᵢ(X) → Gⱼ(X)`, determined on the model when
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
`F`.  The homotopy is natural (`ModelPresentation.homotopy_hom_naturality`). -/
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

end ModelPresentation

end AcyclicModels

end TauCeti
