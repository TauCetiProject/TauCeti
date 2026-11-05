/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Simplices of internal homs and functors over a base

The `n`-simplices of the internal hom `K ⟶[SSet] X` of simplicial sets are the maps
`K ⊗ Δ[n] ⟶ X` (`SSet.ihomObjEquiv`), and its vertices are the maps `K ⟶ X`
(`SSet.ihomObj₀Equiv`). When `X` is a quasicategory, `K ⟶[SSet] X` is the quasicategory
`Fun(K, X)` of functors from `K` to `X`.

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
  HomotopicalAlgebra Simplicial

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
    (by rintro _ _ ⟨z, rfl⟩; exact (φ.app _ z).2)⟩
  invFun g := Subcomplex.lift (curry g.1)
    ((range_le_ihomOver_iff _).2 (by rw [uncurry_curry]; exact g.2))
  left_inv φ := (cancel_mono (ihomOver p f).ι).1 (by simp)
  right_inv g := Subtype.ext (by simp)

lemma homEquiv_apply_coe {Z : SSet.{u}} (φ : Z ⟶ ihomOver p f) :
    (homEquiv φ).1 = uncurry (φ ≫ (ihomOver p f).ι) :=
  (rfl)

@[reassoc (attr := simp)]
lemma homEquiv_symm_apply_ι {Z : SSet.{u}} (g : {g : K ⊗ Z ⟶ E // g ≫ p = fst K Z ≫ f}) :
    homEquiv.symm g ≫ (ihomOver p f).ι = curry g.1 :=
  (rfl)

/-- The universal property is natural in the source. -/
@[simp]
lemma homEquiv_comp_coe {Z Z' : SSet.{u}} (h : Z' ⟶ Z) (φ : Z ⟶ ihomOver p f) :
    (homEquiv (h ≫ φ)).1 = K ◁ h ≫ (homEquiv φ).1 := by
  rw [homEquiv_apply_coe, homEquiv_apply_coe, Category.assoc, uncurry_natural_left]

/-- **The relative simplex description of `Fun_B(K, E)`**: its `n`-simplices are the maps
`K ⊗ Δ[n] ⟶ E` over `f`, that is, whose composite with `p` is the projection to `K` followed
by `f`. -/
def objEquiv {n : ℕ} :
    (ihomOver p f : SSet) _⦋n⦌ ≃ {g : K ⊗ Δ[n] ⟶ E // g ≫ p = fst K Δ[n] ≫ f} :=
  (ihomObjEquiv K E).subtypeEquiv mem_ihomOver_iff

@[simp]
lemma objEquiv_apply_coe {n : ℕ} (σ : (ihomOver p f : SSet) _⦋n⦌) :
    dsimp% (objEquiv σ).1 = ihomObjEquiv K E σ.1 :=
  (rfl)

/-- The vertices of `Fun_B(K, E)` are the maps `K ⟶ E` over `f`. -/
def obj₀Equiv : (ihomOver p f : SSet) _⦋0⦌ ≃ {g : K ⟶ E // g ≫ p = f} :=
  (ihomObj₀Equiv K E).subtypeEquiv mem_ihomOver_obj₀_iff

@[simp]
lemma obj₀Equiv_apply_coe (σ : (ihomOver p f : SSet) _⦋0⦌) :
    dsimp% (obj₀Equiv σ).1 = ihomObj₀Equiv K E σ.1 :=
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
    fun _ φ ↦ homEquiv.injective (Subtype.ext (by simpa using (homEquiv φ).2))

variable (f) in
/-- For the projection `B ⊗ C ⟶ B` of a product, the functors from `K` to `B ⊗ C` over `f` are
the functors from `K` to `C`: `Fun_B(K, B ⊗ C) ≅ Fun(K, C)`, through the second projection. -/
def fstIso (C : SSet.{u}) : (ihomOver (fst B C) f : SSet) ≅ (ihom K).obj C where
  hom := (ihomOver (fst B C) f).ι ≫ (ihom K).map (snd B C)
  inv := homEquiv.symm ⟨lift (fst K _ ≫ f) ((ihom.ev K).app C), lift_fst _ _⟩
  hom_inv_id := homEquiv.injective <| Subtype.ext <| by
    have h := (homEquiv (𝟙 (ihomOver (fst B C) f : SSet))).2
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
    (homEquiv (fstIso f C).inv).1 = lift (fst K _ ≫ f) ((ihom.ev K).app C) := by
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
