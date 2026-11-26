/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex
public import TauCeti.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Simplices of internal homs and functors over a base

The `n`-simplices of the internal hom `K ⟶[SSet] X` of simplicial sets are the maps
`K ⊗ Δ[n] ⟶ X` (`SSet.ihomObjEquiv`), and its vertices are the maps `K ⟶ X`
(`SSet.ihomObj₀Equiv`); in particular `Fun(Δ[0], X) ≅ X` (`SSet.sHomObj₀Iso`). When `X` is a
quasicategory, `K ⟶[SSet] X` is the quasicategory `Fun(K, X)` of functors from `K` to `X`.

For a map `p : E ⟶ B` and a map `f : K ⟶ B`, the simplicial set `SSet.ihomOver p f` of functors
from `K` to `E` over `f` (written `Fun_B(K, E)`, or `Map_B(K, E)` by Lurie) is the fiber of
postcomposition with `p`, `K ⟶[SSet] E ⟶ K ⟶[SSet] B`, over the vertex `f`. Its `n`-simplices
are the maps `K ⊗ Δ[n] ⟶ E` lying over `f`, that is, whose composite with `p` is the projection
to `K` followed by `f`. Transformations between such functors thus lie over the identity of `f`.
For `K = B` and `f = 𝟙 B` this is the simplicial set `SSet.coherentSections p` of sections of
`p`, whose vertices are the sections of `p` in the ordinary sense.

When `p` is an inner fibration, `Fun_B(K, E)` is a quasicategory, and when `p` is a Kan fibration
it is a Kan complex. For `p = 𝟙 B` there is exactly one functor over `f`, and for the projection
`B ⊗ C ⟶ B` of a product the functors over `f` are the functors `K ⟶ C`.

## Main definitions

* `SSet.ihomObjEquiv`: the `n`-simplices of `K ⟶[SSet] X` are the maps `K ⊗ Δ[n] ⟶ X`.
* `SSet.ihomObj₀Equiv`: the vertices of `K ⟶[SSet] X` are the maps `K ⟶ X`.
* `SSet.sHomObj₀Iso`: the function complex `Fun(Δ[0], X)` out of the point is isomorphic to `X`.
* `SSet.ihomOver p f`: the simplicial set `Fun_B(K, E)` of functors over `f`.
* `SSet.coherentSections p`: the simplicial set of sections of `p`.

## Main results

* `SSet.ihomOver.homEquiv`: maps `Z ⟶ Fun_B(K, E)` are the maps `K ⊗ Z ⟶ E` over `f`.
* `SSet.ihomOver.objEquiv`: the `n`-simplices of `Fun_B(K, E)` are the maps `K ⊗ Δ[n] ⟶ E`
  over `f`.
* `SSet.ihomOver.obj₀Equiv`: the vertices of `Fun_B(K, E)` are the maps `K ⟶ E` over `f`.
* `SSet.ihomOver.quasicategory`, `SSet.ihomOver.kanComplex`: `Fun_B(K, E)` is a quasicategory
  when `p` is an inner fibration, and a Kan complex when `p` is a Kan fibration.
* `SSet.ihomOver.isTerminalId`: over the identity of `B`, `Fun_B(K, B)` is terminal.
* `SSet.ihomOver.fstIso`: for the projection `B ⊗ C ⟶ B`, `Fun_B(K, B ⊗ C) ≅ Fun(K, C)`.

## References

* J. Lurie, *Higher Topos Theory*, Warning 1.2.2.2, Notation 1.2.7.2 and Corollary 3.3.3.2.

The quasicategory and Kan complex statements are deduced from the Mathlib results that
postcomposition `(ihom K).map p` with an inner (resp. Kan) fibration `p` is an inner (resp. Kan)
fibration, proved by Jack McKoen and Joël Riou in
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct` and
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`.
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Limits
  HomotopicalAlgebra Opposite SimplicialCategory Simplicial

namespace SSet

section ihom

variable (K : SSet.{u}) {X Y Z : SSet.{u}}

/-- The `n`-simplices of the internal hom `K ⟶[SSet] X` are the maps `K ⊗ Δ[n] ⟶ X`: a simplex is
the uncurried form of the corresponding map `Δ[n] ⟶ (K ⟶[SSet] X)`. -/
def ihomObjEquiv (X : SSet.{u}) {n : ℕ} : ((ihom K).obj X) _⦋n⦌ ≃ (K ⊗ Δ[n] ⟶ X) :=
  yonedaEquiv.symm.trans ((ihom.adjunction K).homEquiv _ _).symm

lemma ihomObjEquiv_apply {n : ℕ} (x : ((ihom K).obj X) _⦋n⦌) :
    ihomObjEquiv K X x = uncurry (yonedaEquiv.symm x) :=
  (rfl)

lemma ihomObjEquiv_symm_apply {n : ℕ} (g : K ⊗ Δ[n] ⟶ X) :
    (ihomObjEquiv K X).symm g = yonedaEquiv (curry g) :=
  (rfl)

/-- Simplicial operators act on the simplices of `K ⟶[SSet] X` by precomposition. -/
@[simp]
lemma ihomObjEquiv_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : ((ihom K).obj X) _⦋n⦌) :
    ihomObjEquiv K X (((ihom K).obj X).map f.op x) =
      K ◁ stdSimplex.map f ≫ ihomObjEquiv K X x := by
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, ← yonedaEquiv_symm_naturality_left,
    uncurry_natural_left]

/-- Postcomposition with `g : X ⟶ Y` acts on the simplices of the internal homs by
postcomposition. -/
@[simp]
lemma ihomObjEquiv_ihom_map_app {n : ℕ} (g : X ⟶ Y) (x : ((ihom K).obj X) _⦋n⦌) :
    ihomObjEquiv K Y (((ihom K).map g).app _ x) = ihomObjEquiv K X x ≫ g := by
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, ← yonedaEquiv_symm_comp, uncurry_natural_right]

/-- The vertices of the internal hom `K ⟶[SSet] X` are the maps `K ⟶ X`. -/
def ihomObj₀Equiv (X : SSet.{u}) : ((ihom K).obj X) _⦋0⦌ ≃ (K ⟶ X) :=
  (ihomObjEquiv K X).trans (fstStdSimplexZeroIso K).homFromEquiv

/-- The vertex of `K ⟶[SSet] X` given by a map `g : K ⟶ X` corresponds to the map
`K ⊗ Δ[0] ⟶ X` that projects to `K` and then applies `g`. -/
@[simp]
lemma ihomObjEquiv_ihomObj₀Equiv_symm (g : K ⟶ X) :
    ihomObjEquiv K X ((ihomObj₀Equiv K X).symm g) = fst K Δ[0] ≫ g := by
  simp [ihomObj₀Equiv]

/-- A vertex `x` of `K ⟶[SSet] X`, viewed as a map `K ⊗ Δ[0] ⟶ X`, factors through the projection
to `K` by the map `K ⟶ X` it corresponds to. -/
@[reassoc (attr := simp)]
lemma fst_comp_ihomObj₀Equiv (x : ((ihom K).obj X) _⦋0⦌) :
    fst K Δ[0] ≫ ihomObj₀Equiv K X x = ihomObjEquiv K X x := by
  rw [← ihomObjEquiv_ihomObj₀Equiv_symm, Equiv.symm_apply_apply]

/-- Postcomposition with `g : X ⟶ Y` acts on the vertices of the internal homs by
postcomposition. -/
@[simp]
lemma ihomObj₀Equiv_ihom_map_app (g : X ⟶ Y) (x : ((ihom K).obj X) _⦋0⦌) :
    ihomObj₀Equiv K Y (((ihom K).map g).app _ x) = ihomObj₀Equiv K X x ≫ g := by
  rw [← cancel_epi (fst K Δ[0]), fst_comp_ihomObj₀Equiv, fst_comp_ihomObj₀Equiv_assoc,
    ihomObjEquiv_ihom_map_app]

/-- The constant map at the vertex given by `g : K ⟶ X` is the curried form of the projection to
`K` followed by `g`. -/
lemma const_ihomObj₀Equiv_symm (g : K ⟶ X) :
    (const ((ihomObj₀Equiv K X).symm g) : Z ⟶ ((ihom K).obj X)) = curry (fst K Z ≫ g) := by
  rw [← comp_const (stdSimplex.isTerminalObj₀.from Z), ← yonedaEquiv_symm_zero, eq_curry_iff,
    uncurry_natural_left, ← ihomObjEquiv_apply, ihomObjEquiv_ihomObj₀Equiv_symm,
    whiskerLeft_fst_assoc]

end ihom

section MappingSpace

variable {X Z : SSet.{u}}

/-- The map corresponding to a vertex of `Fun(X, Z)` evaluates at that vertex. -/
lemma ihomObj₀Equiv_apply (v : ((ihom X).obj Z) _⦋0⦌) :
    ihomObj₀Equiv X Z v = lift (𝟙 X) (const v) ≫ (ihom.ev X).app Z := by
  obtain ⟨f, rfl⟩ := (ihomObj₀Equiv X Z).symm.surjective v
  rw [Equiv.apply_symm_apply, const_ihomObj₀Equiv_symm,
    ← Category.id_comp (curry (fst X X ≫ f)), lift_curry_ihom_ev_app, lift_fst_assoc,
    Category.id_comp]

/-- The map `𝟙_ SSet ⟶ K` given by a vertex `x` of `K` is the constant map at `x`. This holds by
definition: both send every simplex to the corresponding degeneracy of `x`. -/
lemma unitHomEquiv_symm_apply {K : SSet.{u}} (x : K _⦋0⦌) : (unitHomEquiv K).symm x = const x :=
  rfl

/-- The map corresponding to the vertex of `Fun(X, Z)` given by `φ : 𝟙_ SSet ⟶ Fun(X, Z)` is the
uncurried form `MonoidalClosed.uncurry' φ` of `φ`. -/
lemma ihomObj₀Equiv_unitHomEquiv (φ : 𝟙_ SSet ⟶ (ihom X).obj Z) :
    ihomObj₀Equiv X Z (unitHomEquiv _ φ) = MonoidalClosed.uncurry' φ := by
  have h : toUnit X ≫ φ = const (unitHomEquiv _ φ) := by
    rw [← comp_const (toUnit X), ← unitHomEquiv_symm_apply, Equiv.symm_apply_apply]
  have hρ : lift (𝟙 X) (toUnit X) = (ρ_ X).inv := by ext <;> simp
  rw [ihomObj₀Equiv_apply, ← h, MonoidalClosed.uncurry', uncurry_eq, ← lift_whiskerLeft, hρ,
    Category.assoc]

/-- The map corresponding to the image of a vertex `y` under `b : Y ⟶ Fun(X, Z)` is the
restriction of the uncurried form of `b` to `X ⊗ {y}`. -/
lemma ihomObj₀Equiv_app {Y : SSet.{u}} (b : Y ⟶ (ihom X).obj Z) (y : Y _⦋0⦌) :
    ihomObj₀Equiv X Z (b.app _ y) = lift (𝟙 X) (const y) ≫ uncurry b := by
  rw [ihomObj₀Equiv_apply, uncurry_eq, lift_whiskerLeft_assoc, const_comp]

/-- The vertex of `Fun(X, Z)` corresponding to a map `f : X ⟶ Z` is adjoint to
`X ⊗ Δ[0] ⟶ X ⟶ Z`. -/
lemma yonedaEquiv_symm_ihomObj₀Equiv_symm (f : X ⟶ Z) :
    yonedaEquiv.symm ((ihomObj₀Equiv X Z).symm f) = curry (fst X Δ[0] ≫ f) := by
  rw [← ihomObjEquiv_ihomObj₀Equiv_symm, ihomObjEquiv_apply, curry_uncurry]

/-- Precomposition `Fun(Y, Z) ⟶ Fun(X, Z)` with `f : X ⟶ Y` acts on vertices by precomposition. -/
@[simp]
lemma pre_app_app_ihomObj₀Equiv_symm {Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((pre f).app Z).app _ ((ihomObj₀Equiv Y Z).symm g) = (ihomObj₀Equiv X Z).symm (f ≫ g) := by
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp, yonedaEquiv_symm_ihomObj₀Equiv_symm,
    yonedaEquiv_symm_ihomObj₀Equiv_symm, curry_pre_app, whiskerRight_fst_assoc]

/-- Restricting the homotopy defined by a `1`-simplex `s` of `Fun(X, Z)` to an end of the cylinder
gives the map corresponding to the matching face of `s`. -/
lemma whiskerLeft_δ_uncurry_yonedaEquiv_symm (s : ((ihom X).obj Z) _⦋1⦌) (i : Fin 2) :
    X ◁ stdSimplex.δ i ≫ uncurry (yonedaEquiv.symm s) =
      fst X Δ[0] ≫ ihomObj₀Equiv X Z (((ihom X).obj Z).δ i s) := by
  rw [← uncurry_natural_left, stdSimplex.δ_comp_yonedaEquiv_symm,
    ← (ihomObj₀Equiv X Z).symm_apply_apply (((ihom X).obj Z).δ i s),
    yonedaEquiv_symm_ihomObj₀Equiv_symm, uncurry_curry, Equiv.apply_symm_apply]

/-- A face of the `1`-simplex of `Fun(X, Z)` defined by a map `h : X ⊗ Δ[1] ⟶ Z` is adjoint to
the restriction of `h` along the matching face of `Δ[1]`. -/
lemma yonedaEquiv_symm_δ_yonedaEquiv_curry (h : X ⊗ Δ[1] ⟶ Z) (i : Fin 2) :
    yonedaEquiv.symm (((ihom X).obj Z).δ i (yonedaEquiv (curry h))) =
      curry (X ◁ stdSimplex.δ i ≫ h) := by
  rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, curry_natural_left]

/-- The function complex `Fun(Δ[0], X)` out of the point is isomorphic to `X`, obtained by
transporting `Δ[0] ≅ 𝟙_ SSet` along `MonoidalClosed.internalHom` into `MonoidalClosed.unitIsoSelf`.
Its forward direction evaluates at the unique simplex of `Δ[0]` (`sHomObj₀Iso_hom_app`) and its
inverse curries the second projection (`sHomObj₀Iso_inv_app_app`). -/
def sHomObj₀Iso (X : SSet.{u}) : sHom (Δ[0] : SSet.{u}) X ≅ X :=
  (internalHom.mapIso
    (stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit).op.symm).app X ≪≫
    unitIsoSelf X

/-- Evaluating the inverse of `sHomObj₀Iso` on an `m`-simplex `x` of `X` acts along `φ : m ⟶ k` by
`X.map φ x`, ignoring the `Δ[0]` factor. -/
@[simp]
lemma sHomObj₀Iso_inv_app_app (X : SSet.{u}) {m k : SimplexCategoryᵒᵖ} (x : X.obj m) (φ : m ⟶ k)
    (u₀ : (Δ[0] : SSet.{u}).obj k) :
    ((sHomObj₀Iso X).inv.app m x).app k φ u₀ = X.map φ x := by
  have hinv : (sHomObj₀Iso X).inv = curry (snd (Δ[0] : SSet.{u}) X) := by
    -- Unfolding the composite isomorphism `sHomObj₀Iso` gives `(unitIsoSelf X).inv` followed by
    -- precomposition `(pre u.hom).app X` along `u : Δ[0] ≅ 𝟙_ SSet` (`rw [Iso.trans_inv]` cannot
    -- match directly because `sHom`, `internalHom.obj`, and `ihom` only agree at default
    -- transparency).
    have h₁ : (unitIsoSelf X).inv ≫
        (pre (stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit).hom).app X =
        curry (snd (Δ[0] : SSet.{u}) X) := by
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, uncurry_eq]
      have hunit : 𝟙_ SSet.{u} ◁ (unitIsoSelf X).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app X =
          (λ_ X).hom :=
        (conjugateEquiv_counit (Adjunction.id (C := SSet.{u}))
          (ihom.adjunction (𝟙_ SSet.{u})) (leftUnitorNatIso SSet.{u}).hom X).trans
          (Category.comp_id _)
      rw [hunit, leftUnitor_hom, whiskerRight_snd]
    exact h₁
  rw [hinv]
  -- In `SSet`, `curry` (`FunctorToTypes.adj`) evaluates `snd Δ[0] X` on `(u₀, X.map φ x)`.
  rfl

/-- Evaluating `sHomObj₀Iso` on an `m`-simplex of `Fun(Δ[0], X)` evaluates it at the identity of
`m` and the unique `m`-simplex of `Δ[0]`. -/
@[simp]
lemma sHomObj₀Iso_hom_app (X : SSet.{u}) (m : SimplexCategoryᵒᵖ)
    (s : (sHom (Δ[0] : SSet.{u}) X).obj m) :
    (sHomObj₀Iso X).hom.app m s = s.app m (𝟙 m) (stdSimplex.const 0 0 m) := by
  obtain ⟨x, rfl⟩ := ((sHomObj₀Iso X).app m).toEquiv.symm.surjective s
  simp [sHomObj₀Iso_inv_app_app]

/-- On vertices, `sHomObj₀Iso` evaluates a map `Δ[0] ⟶ X` at the unique vertex of `Δ[0]`. -/
lemma sHomObj₀Iso_hom_app_zero (X : SSet.{u}) (v : (sHom (Δ[0] : SSet.{u}) X) _⦋0⦌) :
    (sHomObj₀Iso X).hom.app (op ⦋0⦌) v = yonedaEquiv ((homEquiv' Δ[0] X).symm v) := by
  obtain ⟨f, rfl⟩ := (homEquiv' (Δ[0] : SSet.{u}) X).surjective v
  rw [Equiv.symm_apply_apply]
  exact (sHomObj₀Iso_hom_app X (op ⦋0⦌) (homEquiv' Δ[0] X f)).trans
    (congrArg (f.app (op ⦋0⦌)) (stdSimplex.objEquiv.injective (by ext; simp)))

/-- On vertices, the inverse of `sHomObj₀Iso` sends a vertex `x` of `X` to the map `Δ[0] ⟶ X`
picking out `x`. -/
lemma sHomObj₀Iso_inv_app_zero (X : SSet.{u}) (x : X _⦋0⦌) :
    (sHomObj₀Iso X).inv.app (op ⦋0⦌) x = homEquiv' Δ[0] X (yonedaEquiv.symm x) := by
  apply ((sHomObj₀Iso X).app (op ⦋0⦌)).toEquiv.injective
  simp only [Iso.toEquiv_fun, Iso.app_hom, Iso.inv_hom_id_app_apply, sHomObj₀Iso_hom_app_zero,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The function complex `Fun(Δ[0], X)` out of the point is connected when `X` is connected. -/
instance (X : SSet.{u}) [X.IsConnected] : (sHom (Δ[0] : SSet.{u}) X).IsConnected := by
  rw [isConnected_iff_nonempty_unique]
  exact ⟨(Equiv.uniqueCongr (π₀Functor.mapIso (sHomObj₀Iso X)).toEquiv).invFun
    ((isConnected_iff_nonempty_unique X).1 inferInstance).some⟩

end MappingSpace

section ihomOver

open modelCategoryQuillen

variable {K E B : SSet.{u}} (p : E ⟶ B) (f : K ⟶ B)

/-- The simplicial set `Fun_B(K, E)` of functors from `K` to `E` over `f : K ⟶ B`, for a map
`p : E ⟶ B`: the fiber over the vertex `f` of the postcomposition map
`(K ⟶[SSet] E) ⟶ (K ⟶[SSet] B)` with `p`. Its `n`-simplices are the maps `K ⊗ Δ[n] ⟶ E` whose
composite with `p` is the projection to `K` followed by `f` (`SSet.ihomOver.objEquiv`). -/
def ihomOver : ((ihom K).obj E).Subcomplex :=
  fiber ((ihom K).map p) ((ihomObj₀Equiv K B).symm f)

/-- The simplicial set of sections of `p : E ⟶ B`: the functors from `B` to `E` over the identity
of `B`. Its vertices are the sections of `p`, and its `n`-simplices are the maps
`B ⊗ Δ[n] ⟶ E` over the projection to `B`. -/
abbrev coherentSections : ((ihom B).obj E).Subcomplex :=
  ihomOver p (𝟙 B)

variable {p f}

/-- A map `g : Z ⟶ (K ⟶[SSet] E)` lands in `Fun_B(K, E)` exactly when its uncurried form
`K ⊗ Z ⟶ E` lies over `f`. -/
lemma range_le_ihomOver_iff {Z : SSet.{u}} (g : Z ⟶ (ihom K).obj E) :
    Subcomplex.range g ≤ ihomOver p f ↔ uncurry g ≫ p = fst K Z ≫ f := by
  rw [ihomOver, range_le_fiber_iff, const_ihomObj₀Equiv_symm, eq_curry_iff, uncurry_natural_right]

/-- An `n`-simplex of `K ⟶[SSet] E` lies in `Fun_B(K, E)` exactly when the corresponding map
`K ⊗ Δ[n] ⟶ E` lies over `f`. -/
@[simp]
lemma mem_ihomOver_iff {n : ℕ} (σ : ((ihom K).obj E) _⦋n⦌) :
    σ ∈ (ihomOver p f).obj _ ↔ ihomObjEquiv K E σ ≫ p = fst K Δ[n] ≫ f := by
  have := range_le_ihomOver_iff (p := p) (f := f) (yonedaEquiv.symm σ)
  rwa [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply, Subcomplex.ofSimplex_le_iff,
    ← ihomObjEquiv_apply] at this

/-- A vertex of `K ⟶[SSet] E` lies in `Fun_B(K, E)` exactly when the corresponding map `K ⟶ E`
lies over `f`. -/
lemma mem_ihomOver_obj₀_iff (σ : ((ihom K).obj E) _⦋0⦌) :
    σ ∈ (ihomOver p f).obj _ ↔ ihomObj₀Equiv K E σ ≫ p = f := by
  rw [mem_ihomOver_iff, ← fst_comp_ihomObj₀Equiv, Category.assoc, cancel_epi]

namespace ihomOver

/-- **The universal property of `Fun_B(K, E)`**: maps `Z ⟶ Fun_B(K, E)` are the maps
`K ⊗ Z ⟶ E` over `f`, through uncurrying. -/
def homEquiv {Z : SSet.{u}} :
    (Z ⟶ ihomOver p f) ≃ {g : K ⊗ Z ⟶ E // g ≫ p = fst K Z ≫ f} where
  toFun φ := ⟨uncurry (φ ≫ (ihomOver p f).ι), (range_le_ihomOver_iff _).1
    (by rintro _ _ ⟨z, rfl⟩; exact (φ.app _ z).property)⟩
  invFun g := Subcomplex.lift (curry g.val)
    ((range_le_ihomOver_iff _).2 (by rw [uncurry_curry]; exact g.property))
  left_inv φ := (cancel_mono (ihomOver p f).ι).1 (by simp)
  right_inv g := Subtype.ext (by simp)

lemma homEquiv_apply_coe {Z : SSet.{u}} (φ : Z ⟶ ihomOver p f) :
    (homEquiv φ).val = uncurry (φ ≫ (ihomOver p f).ι) :=
  (rfl)

@[reassoc (attr := simp)]
lemma homEquiv_symm_apply_ι {Z : SSet.{u}} (g : {g : K ⊗ Z ⟶ E // g ≫ p = fst K Z ≫ f}) :
    homEquiv.symm g ≫ (ihomOver p f).ι = curry g.val :=
  (rfl)

/-- The universal property is natural in the source. -/
@[simp]
lemma homEquiv_comp_coe {Z Z' : SSet.{u}} (h : Z' ⟶ Z) (φ : Z ⟶ ihomOver p f) :
    (homEquiv (h ≫ φ)).val = K ◁ h ≫ (homEquiv φ).val := by
  rw [homEquiv_apply_coe, homEquiv_apply_coe, Category.assoc, uncurry_natural_left]

/-- **The relative simplex description of `Fun_B(K, E)`**: its `n`-simplices are the maps
`K ⊗ Δ[n] ⟶ E` over `f`, that is, whose composite with `p` is the projection to `K` followed
by `f`. -/
def objEquiv {n : ℕ} :
    (ihomOver p f : SSet) _⦋n⦌ ≃ {g : K ⊗ Δ[n] ⟶ E // g ≫ p = fst K Δ[n] ≫ f} :=
  (ihomObjEquiv K E).subtypeEquiv mem_ihomOver_iff

@[simp]
lemma objEquiv_apply_coe {n : ℕ} (σ : (ihomOver p f : SSet) _⦋n⦌) :
    dsimp% (objEquiv σ).val = ihomObjEquiv K E σ.val :=
  (rfl)

/-- The vertices of `Fun_B(K, E)` are the maps `K ⟶ E` over `f`. -/
def obj₀Equiv : (ihomOver p f : SSet) _⦋0⦌ ≃ {g : K ⟶ E // g ≫ p = f} :=
  (ihomObj₀Equiv K E).subtypeEquiv mem_ihomOver_obj₀_iff

@[simp]
lemma obj₀Equiv_apply_coe (σ : (ihomOver p f : SSet) _⦋0⦌) :
    dsimp% (obj₀Equiv σ).val = ihomObj₀Equiv K E σ.val :=
  (rfl)

/-- The functors over the base form a quasicategory when `p` is an inner fibration. -/
instance quasicategory [InnerFibration p] : Quasicategory (ihomOver p f) :=
  fiber.quasicategory _ _

/-- The functors over the base form a Kan complex when `p` is a Kan fibration. -/
instance kanComplex [Fibration p] : KanComplex (ihomOver p f) :=
  fiber.kanComplex _ _

variable (f) in
/-- There is exactly one functor over `f` to the base itself: `Fun_B(K, B)` is terminal. -/
def isTerminalId : IsTerminal (ihomOver (𝟙 B) f : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun Z ↦ homEquiv.symm ⟨fst K Z ≫ f, Category.comp_id _⟩)
    fun _ φ ↦ homEquiv.injective (Subtype.ext (by simpa using (homEquiv φ).property))

variable (f) in
/-- For the projection `B ⊗ C ⟶ B` of a product, the functors from `K` to `B ⊗ C` over `f` are
the functors from `K` to `C`: `Fun_B(K, B ⊗ C) ≅ Fun(K, C)`, through the second projection. -/
def fstIso (C : SSet.{u}) : (ihomOver (fst B C) f : SSet) ≅ (ihom K).obj C where
  hom := (ihomOver (fst B C) f).ι ≫ (ihom K).map (snd B C)
  inv := homEquiv.symm ⟨lift (fst K _ ≫ f) ((ihom.ev K).app C), lift_fst _ _⟩
  hom_inv_id := homEquiv.injective <| Subtype.ext <| by
    have h := (homEquiv (𝟙 (ihomOver (fst B C) f : SSet))).property
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [h, homEquiv_comp_coe, Equiv.apply_symm_apply, Category.assoc, lift_fst,
        whiskerLeft_fst_assoc]
    · rw [homEquiv_comp_coe, Equiv.apply_symm_apply, Category.assoc, lift_snd, homEquiv_apply_coe,
        Category.id_comp, ← uncurry_natural_right, uncurry_eq]
  inv_hom_id := by
    rw [homEquiv_symm_apply_ι_assoc, ← curry_natural_right, lift_snd,
      ← uncurry_id_eq_ev, curry_uncurry]

/-- The comparison `Fun_B(K, B ⊗ C) ⟶ Fun(K, C)` is the inclusion into `K ⟶[SSet] (B ⊗ C)`
followed by postcomposition with the second projection. -/
@[simp]
lemma fstIso_hom (C : SSet.{u}) :
    (fstIso f C).hom = (ihomOver (fst B C) f).ι ≫ (ihom K).map (snd B C) :=
  (rfl)

/-- The comparison `Fun(K, C) ⟶ Fun_B(K, B ⊗ C)` corresponds to the map `K ⊗ Fun(K, C) ⟶ B ⊗ C`
whose components are the projection to `K` followed by `f`, and the evaluation map. -/
@[simp]
lemma homEquiv_fstIso_inv_coe (C : SSet.{u}) :
    (homEquiv (fstIso f C).inv).val = lift (fst K _ ≫ f) ((ihom.ev K).app C) := by
  simp [fstIso]

/-- The comparison `Fun(K, C) ⟶ Fun_B(K, B ⊗ C)`, followed by the inclusion into
`K ⟶[SSet] (B ⊗ C)`, is the curried form of the map with components the projection to `K`
followed by `f`, and the evaluation map. -/
@[reassoc (attr := simp)]
lemma fstIso_inv_ι (C : SSet.{u}) :
    (fstIso f C).inv ≫ (ihomOver (fst B C) f).ι = curry (lift (fst K _ ≫ f) ((ihom.ev K).app C)) :=
  (rfl)

end ihomOver

end ihomOver

end SSet
