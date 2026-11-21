/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map

/-!
# Inverse images of closed subgroup schemes, and their flat descent

Let `g : G' ⟶ G` be a morphism of group schemes lying over `f : S' ⟶ S` and compatible with
multiplication. Such a `g` is automatically compatible with the identity and inversion
(`TauCeti.GroupScheme.one_left_comp_of_mul_left_comp`,
`TauCeti.GroupScheme.inv_left_comp_of_mul_left_comp`), and the inverse image along `g` of a closed
subgroup scheme `V(D)` of `G` is a closed subgroup scheme of `G'`
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`).

Conversely, if `f` is flat and surjective and the square formed by `g`, `f` and the structure
morphisms is a pullback square, then `V(D)` is a subgroup scheme as soon as its inverse image in
`G'` is (`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`). No
finiteness or flatness hypothesis is placed on `V(D)`, and `f` need not be quasi-compact, so this is
not an instance of effective fpqc descent. Each of the three conditions of the closed-subgroup
criterion (`TauCeti.GroupScheme.exists_grpObj_isMonHom_iff_ker_le`) says that a family of points
lies in `V(D)`, and the parameter scheme of the family changes by a flat surjective base change.
Flat surjective morphisms are scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_flat_of_surjective`), so such a condition
holds before the base change exactly when it holds after it
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_le_ker_iff_of_isSchemeTheoreticallyDominant`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
  Scheme.IdealSheafData
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {g : G'.left ⟶ G.left}

/-! ### Compatibility with the identity and inversion -/

section Compatibility

variable (w : g ≫ G.hom = G'.hom ≫ f)
  (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left)
include hμ

/-- **A multiplicative morphism of group schemes preserves the identity.** If `g : G' ⟶ G` lies
over `f : S' ⟶ S` and is compatible with multiplication, then it carries the identity section of
`G'` to the base change along `f` of that of `G`. -/
theorem one_left_comp_of_mul_left_comp : η[G'].left ≫ g = f ≫ η[G].left := by
  -- `e = η ≫ g` is an idempotent in the group of `S'`-points of `G` over `f`
  have hη : η[G'].left ≫ G'.hom = 𝟙 S' := Over.w η[G']
  let e : Over.mk f ⟶ G := Over.homMk (η[G'].left ≫ g) (by simp [w, reassoc_of% hη])
  have he : e * e = e := by
    ext
    rw [Hom.mul_def, Over.comp_left, Over.lift_left]
    simp only [e, Over.homMk_left]
    have hl : pullback.lift (η[G'].left ≫ g) (η[G'].left ≫ g) (by simp [w]) =
        pullback.lift η[G'].left η[G'].left rfl ≫ pullback.map _ _ _ _ g g f w.symm w.symm := by
      apply pullback.hom_ext <;> simp
    rw [hl, Category.assoc, ← hμ, ← Category.assoc]
    congr 1
    have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over S'))) η[G']
    rw [Category.id_comp] at this
    simpa using congr($(this).left)
  have := congr($(mul_eq_left.mp he).left)
  simpa [e, Hom.one_def] using this

/-- **A multiplicative morphism of group schemes preserves inversion.** If `g : G' ⟶ G` lies over
`f : S' ⟶ S` and is compatible with multiplication, then it intertwines the inversions of `G'` and
`G`. -/
theorem inv_left_comp_of_mul_left_comp : ι[G'].left ≫ g = g ≫ ι[G].left := by
  -- `g` and `ι ≫ g` are mutually inverse points of `G` with values in `G'` over `G'.hom ≫ f`
  have hι : ι[G'].left ≫ G'.hom = G'.hom := Over.w ι[G']
  let a : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk g w
  let b : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (ι[G'].left ≫ g) (by simp [w, reassoc_of% hι])
  have hab : a * b = 1 := by
    ext
    rw [Hom.mul_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.lift_left, Over.toUnit_left]
    simp only [a, b, Over.homMk_left]
    have hl : pullback.lift g (ι[G'].left ≫ g) (by simp [w, reassoc_of% hι]) =
        pullback.lift (𝟙 _) ι[G'].left (by simp [hι]) ≫
          pullback.map _ _ _ _ g g f w.symm w.symm := by
      apply pullback.hom_ext <;> simp
    rw [hl, Category.assoc, ← hμ, ← Category.assoc]
    have := congr($(GrpObj.right_inv G').left)
    simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, Over.id_left] at this
    rw [this, Category.assoc, one_left_comp_of_mul_left_comp w hμ]
    simp
  have := congr($(eq_inv_of_mul_eq_one_right hab).left)
  simpa [a, b, Hom.inv_def] using this

end Compatibility

/-! ### Inverse images of closed subgroup schemes -/

/-- The closed-subgroup criterion for the closed subscheme `V(D)` of a group scheme. -/
private theorem exists_grpObj_isMonHom_iff_le {T : Scheme.{u}} {H : Over T} [GrpObj H]
    (D : H.left.IdealSheafData) :
    (∃ _ : GrpObj (Over.mk (D.subschemeι ≫ H.hom)),
        IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ H.hom) ⟶ H)) ↔
      D ≤ η[H].left.ker ∧
      D ≤ (pullback.map (D.subschemeι ≫ H.hom) (D.subschemeι ≫ H.hom) H.hom H.hom D.subschemeι
        D.subschemeι (𝟙 T) (by simp) (by simp) ≫ μ[H].left).ker ∧
      D ≤ (D.subschemeι ≫ ι[H].left).ker := by
  let i : Over.mk (D.subschemeι ≫ H.hom) ⟶ H := Over.homMk D.subschemeι
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion D.subschemeι)
  rw [exists_grpObj_isMonHom_iff_ker_le i]
  simp only [i, Over.comp_left, Over.homMk_left, Over.tensorHom_left, Over.tensorObj_left,
    Over.mk_hom, ker_subschemeι]

variable (w : g ≫ G.hom = G'.hom ≫ f) (D : G.left.IdealSheafData)

omit [GrpObj G] [GrpObj G'] in
include w in
/-- The square comparing `V(D.comap g)` with `V(D)` lies over `f`. -/
private theorem subschemeMap_comp_hom :
    ((D.comap g).subschemeι ≫ G'.hom) ≫ f =
      subschemeMap (D.comap g) D g (D.le_map_comap g) ≫ D.subschemeι ≫ G.hom := by
  rw [subschemeMap_subschemeι_assoc, w, Category.assoc]

/-- Sums of two points of `V(D.comap g)` are carried by `g` to sums of two points of `V(D)`. -/
private theorem mul_comparison
    (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left) :
    (pullback.map ((D.comap g).subschemeι ≫ G'.hom) ((D.comap g).subschemeι ≫ G'.hom) G'.hom
        G'.hom (D.comap g).subschemeι (D.comap g).subschemeι (𝟙 S') (by simp) (by simp) ≫
          μ[G'].left) ≫ g =
      pullback.map _ _ _ _ _ _ f (subschemeMap_comp_hom w D) (subschemeMap_comp_hom w D) ≫
        pullback.map (D.subschemeι ≫ G.hom) (D.subschemeι ≫ G.hom) G.hom G.hom D.subschemeι
          D.subschemeι (𝟙 S) (by simp) (by simp) ≫ μ[G].left := by
  rw [Category.assoc, hμ, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

/-- Negatives of points of `V(D.comap g)` are carried by `g` to negatives of points of `V(D)`. -/
private theorem inv_comparison (hι : ι[G'].left ≫ g = g ≫ ι[G].left) :
    ((D.comap g).subschemeι ≫ ι[G'].left) ≫ g =
      subschemeMap (D.comap g) D g (D.le_map_comap g) ≫ D.subschemeι ≫ ι[G].left := by
  rw [Category.assoc, hι, subschemeMap_subschemeι_assoc]

omit [GrpObj G] [GrpObj G'] in
/-- If `φ` factors through `V(D)`, then any `φ'` with `φ' ≫ g = p ≫ φ` factors through the inverse
image of `V(D)` along `g`. -/
private theorem comap_le_ker_of_le_ker {X' X : Scheme.{u}} {p : X' ⟶ X} {φ' : X' ⟶ G'.left}
    {φ : X ⟶ G.left} (h : φ' ≫ g = p ≫ φ) (hD : D ≤ φ.ker) : D.comap g ≤ φ'.ker := by
  rw [← le_map_iff_comap_le, map_ker, h]
  exact hD.trans (Scheme.Hom.le_ker_comp _ _)

/-- **Closed subgroup schemes are stable under inverse image.** Let `g : G' ⟶ G` be a morphism of
group schemes lying over `f : S' ⟶ S` and compatible with multiplication. If the closed subscheme
of `G` cut out by `D` is a subgroup scheme, then so is its inverse image in `G'`. -/
theorem exists_grpObj_isMonHom_comap
    (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left)
    (hD : ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ G.hom)),
      IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ G.hom) ⟶ G)) :
    ∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G') := by
  rw [exists_grpObj_isMonHom_iff_le] at hD ⊢
  obtain ⟨he, hm, hj⟩ := hD
  exact ⟨comap_le_ker_of_le_ker D (one_left_comp_of_mul_left_comp w hμ) he,
    comap_le_ker_of_le_ker D (mul_comparison w D hμ) hm,
    comap_le_ker_of_le_ker D (inv_comparison D (inv_left_comp_of_mul_left_comp w hμ)) hj⟩

/-- **Subgroup schemes descend along flat surjective morphisms.** Let `g : G' ⟶ G` be a morphism
of group schemes lying over a flat surjective `f : S' ⟶ S`, forming a pullback square with the
structure morphisms and compatible with multiplication, and let `V(D) ⊆ G` be a closed subscheme.
Then `V(D)` is a subgroup scheme of `G` exactly when its inverse image in `G'` is a subgroup scheme
of `G'`. The base-change direction (`.mpr`) is `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`,
which needs no hypothesis on `f`. -/
theorem exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective [Flat f] [Surjective f]
    (hg : IsPullback g G'.hom G.hom f)
    (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ μ[G].left)
    (D : G.left.IdealSheafData) :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G')) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ G.hom)),
        IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ G.hom) ⟶ G) := by
  rw [exists_grpObj_isMonHom_iff_le, exists_grpObj_isMonHom_iff_le]
  -- `ρ : V(D.comap g) ⟶ V(D)` is the base change of `V(D)` along `f`, so it and its fibre square
  -- over `f` are flat and surjective, hence scheme-theoretically dominant.
  have hD := (D.isPullback_subschemeMap_comap G.hom hg).flip
  have hDD := hD.pullback_map hD
  have : Flat (subschemeMap (D.comap g) D g (D.le_map_comap g)) :=
    MorphismProperty.of_isPullback hD ‹_›
  have : Surjective (subschemeMap (D.comap g) D g (D.le_map_comap g)) :=
    MorphismProperty.of_isPullback hD ‹_›
  have : Flat (pullback.map _ _ _ _ _ _ f (subschemeMap_comp_hom hg.w D)
      (subschemeMap_comp_hom hg.w D)) := MorphismProperty.of_isPullback hDD ‹_›
  have : Surjective (pullback.map _ _ _ _ _ _ f (subschemeMap_comp_hom hg.w D)
      (subschemeMap_comp_hom hg.w D)) := MorphismProperty.of_isPullback hDD ‹_›
  exact and_congr (comap_le_ker_iff_of_isSchemeTheoreticallyDominant D f
      (one_left_comp_of_mul_left_comp hg.w hμ))
    (and_congr (comap_le_ker_iff_of_isSchemeTheoreticallyDominant D _ (mul_comparison hg.w D hμ))
      (comap_le_ker_iff_of_isSchemeTheoreticallyDominant D _
        (inv_comparison D (inv_left_comp_of_mul_left_comp hg.w hμ))))

end TauCeti.GroupScheme
