/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.PicZero
public import TauCeti.AlgebraicGeometry.PicardFunctor.Fppf
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.BaseChange
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.Fppf
public import TauCeti.AlgebraicGeometry.PicardFunctor.SheafPoints

/-!
# Degree components of the relative Picard fppf sheaf

Let `f : X ⟶ S` be a morphism of schemes and `Pic_{X/S}` its relative Picard fppf sheaf, the
fppf sheafification of `T ↦ Pic(X_T) / Pic(T)`. A section of `Pic_{X/S}` over a test scheme `T`
need not be the class of a line bundle on `X_T`; it is only one fppf-locally on `T`. This file
nevertheless reads off its degree on each geometric fibre, and cuts out the subsheaf `Picᵈ_{X/S}`
of sections of degree `d` on every geometric fibre. Here the degree of a line bundle `L` on a
fibre over `K` is its Euler-characteristic degree `χ(L) - χ(𝒪)`, computed from `H⁰` and `H¹`
(`LineBundleClass.eulerDegree`). It is the usual degree when the fibres are proper curves; for
other `f` it is still defined, but can take junk values.

The point is that fppf covers of the spectrum of an algebraically closed field `K` split
(`AlgebraicGeometry.Scheme.eq_top_of_mem_fppfTopology_over_of_isAlgClosed`). Hence over a
geometric point `Spec K ⟶ S` the sheafification map `Pic(X_K) / Pic(Spec K) → Pic_{X/S}(Spec K)`
is bijective (`relativePicardToFppfSheaf_app_bijective_of_isAlgClosed`), and the restriction of a
section `σ` over `T` to a geometric point `ξ : Spec K ⟶ T` is the class of an actual line bundle
on the fibre `X_ξ`. Its degree is the fibre degree `relativePicardFppfSheafFiberDegree f ξ σ`.
It is the fibre degree `relativePicardFiberDegree` on actual classes
(`relativePicardFppfSheafFiberDegree_toFppfSheaf`), natural in `T`
(`relativePicardFppfSheafFiberDegree_map`), and additive for a smooth proper geometrically
connected family of curves.

The degree component `relativePicardDegreeFppfSubfunctor f d` consists of the sections whose
fibre degree is `d` at every geometric point. It is a subsheaf: a geometric point of `T` factors
through every fppf cover of `T`, since the cover splits over it
(`isSheaf_relativePicardDegreeFppfSubfunctor`). The class of a line bundle on `X_T` lies in
`Picᵈ_{X/S}(T)` exactly when it has degree `d` on every geometric fibre of `X_T ⟶ T`, and the
zero section lies in `Pic⁰`. Over a nonempty test scheme the components are disjoint. For `f`
quasi-compact and separated, the components commute with base change `S' ⟶ S` through
`relativePicardFppfSheafBaseChangeIso`.

For a smooth proper geometrically connected family of curves:

* addition sends `Picᵈ × Picᵉ` to `Picᵈ⁺ᵉ` and negation sends `Picᵈ` to `Pic⁻ᵈ`;
* the class of a relative effective Cartier divisor of degree `d` lies in `Picᵈ`;
* `Pic⁰` is the image of the degree-zero Picard sheaf `relativePicardDegreeZeroFppfSheaf f`
  (`range_relativePicardDegreeZeroFppfSheafι`).

Over a disconnected test scheme a section can have different degrees on different components,
and then lies in no `Picᵈ`: the components cover `Pic_{X/S}` only once the degree is known to be
locally constant.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardFppfSheafFiberDegree`: the degree of a section of the
  relative Picard fppf sheaf on the fibre over a geometric point;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeFppfSubfunctor`: the degree-`d` component
  `Picᵈ_{X/S}`, as a subfunctor of the relative Picard fppf sheaf;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeFppfSheaf`: the same component as an fppf sheaf
  of sets;
* `TauCeti.AlgebraicGeometry.relativePicardToFppfSheaf_app_mem_relativePicardDegreeFppfSubfunctor`
  `_iff`: membership of an actual line-bundle class;
* `TauCeti.AlgebraicGeometry.add_mem_relativePicardDegreeFppfSubfunctor_obj`: degrees add;
* `TauCeti.AlgebraicGeometry.range_relativePicardDegreeZeroFppfSheafι`: `Pic⁰` is the degree-zero
  Picard sheaf;
* `TauCeti.AlgebraicGeometry.relativePicardFppfSheafBaseChangeIso_hom_app_mem_relativePicardDegree`
  `FppfSubfunctor_iff`: base change of the components.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, proof of Theorem 9.4.8.
* V. Dimitrov, Z. Gao, P. Habegger, *Uniformity in Mordell–Lang for curves*, Ann. of Math. 194
  (2021), Section 6.1.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

section GeometricPoint

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **The fibre degree of a section of the relative Picard fppf sheaf** at a geometric point
`ξ : Spec K ⟶ T` of a test scheme `T`: the restriction of the section to `ξ` is the class of a
line bundle on the fibre `Spec K ×_S X` (`exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed`),
and this is the Euler-characteristic degree `χ(L) - χ(𝒪)` from `H⁰` and `H¹`
(`LineBundleClass.eulerDegree`) of that line bundle, the usual degree when the fibre is a proper
curve. On the class of a line bundle on `X_T` it is the fibre degree
`relativePicardFiberDegree` (`relativePicardFppfSheafFiberDegree_toFppfSheaf`). -/
def relativePicardFppfSheafFiberDegree {T : (Over S)ᵒᵖ} (ξ : Spec (.of K) ⟶ T.unop.left)
    (σ : (relativePicardFppfSheaf f).obj.obj T) : ℤ :=
  relativePicardFiberDegree f (T := op (Over.mk (ξ ≫ T.unop.hom))) (𝟙 _)
    (QuotientGroup.mk (exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed f (ξ ≫ T.unop.hom)
      ((relativePicardFppfSheaf f).obj.map
        (Over.homMk ξ : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop).op σ)).choose)

/-- **Computing the fibre degree from a local representative.** Let `σ` be a section of the
relative Picard fppf sheaf over `T` and `ξ : Spec K ⟶ T` a geometric point. If `ξ` factors as
`ζ` followed by `ψ : T' ⟶ T`, and the restriction of `σ` along `ψ` is the class of a line bundle
`a` on `X_{T'}`, then the fibre degree of `σ` at `ξ` is the fibre degree of `a` at `ζ`. -/
theorem relativePicardFppfSheafFiberDegree_eq_of_map_eq {T : (Over S)ᵒᵖ}
    (ξ : Spec (.of K) ⟶ T.unop.left) (σ : (relativePicardFppfSheaf f).obj.obj T) {T' : Over S}
    (ψ : T' ⟶ T.unop)
    (ζ : Spec (.of K) ⟶ T'.left) (hζ : ζ ≫ ψ.left = ξ) (a : LineBundleClass (pullback T'.hom f))
    (ha : (relativePicardToFppfSheaf f).app (op T') (relativePicardAddPresheafMk f (op T') a) =
      (relativePicardFppfSheaf f).obj.map ψ.op σ) :
    relativePicardFppfSheafFiberDegree f ξ σ =
      relativePicardFiberDegree f (T := op T') ζ (QuotientGroup.mk a) := by
  have hb := (exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed f (ξ ≫ T.unop.hom)
    ((relativePicardFppfSheaf f).obj.map
      (Over.homMk ξ : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop).op σ)).choose_spec
  -- The geometric point, as a scheme over `S`, maps to `T'` through `ζ`.
  let χ : Over.mk (ξ ≫ T.unop.hom) ⟶ T' := Over.homMk ζ (by simp [← hζ])
  have hχ : χ ≫ ψ = Over.homMk ξ := by
    ext
    simp [χ, hζ]
  -- The chosen representative at the geometric point is the pullback of `a`.
  have key : relativePicardAddPresheafMk f _
      (exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed f (ξ ≫ T.unop.hom)
        ((relativePicardFppfSheaf f).obj.map
          (Over.homMk ξ : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop).op σ)).choose =
      relativePicardAddPresheafMk f (op (Over.mk (ξ ≫ T.unop.hom)))
        (LineBundleClass.pullback ((Over.pullback f).map χ).left a) := by
    have hmap : relativePicardAddPresheafMk f (op (Over.mk (ξ ≫ T.unop.hom)))
        (LineBundleClass.pullback ((Over.pullback f).map χ).left a) =
        (relativePicardAddPresheaf f).map χ.op (relativePicardAddPresheafMk f (op T') a) :=
      (relativePicardAddPresheaf_map_mk f χ.op a).symm
    apply (relativePicardToFppfSheaf_app_bijective_of_isAlgClosed f _).1
    rw [hb, hmap, NatTrans.naturality_apply, ha, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, hχ]
  have hmap : (QuotientGroup.mk (LineBundleClass.pullback ((Over.pullback f).map χ).left a) :
      (relativePicardPresheaf f).obj (op (Over.mk (ξ ≫ T.unop.hom)))) =
      (relativePicardPresheaf f).map χ.op (QuotientGroup.mk a) :=
    (relativePicardPresheaf_map_mk f χ.op a).symm
  have hζ' : 𝟙 _ ≫ χ.op.unop.left = ζ := by simp [χ]
  rw [relativePicardFppfSheafFiberDegree, (relativePicardAddPresheafMk_eq_iff f _ _ _).1 key, hmap]
  -- `exact` compares the carrier of `Pic(X_{T'}) / Pic(T')` with the quotient group at default
  -- transparency, which the motive of `rw` does not.
  exact (relativePicardFiberDegree_map f χ.op (𝟙 _) (QuotientGroup.mk a)).trans
    (congrArg (relativePicardFiberDegree f · (QuotientGroup.mk a)) hζ')

/-- **Computing the fibre degree at the geometric point itself.** If the restriction of a section
`σ` over `T` to the geometric point `ξ : Spec K ⟶ T` is the class of a line bundle `a` on the
fibre, then the fibre degree of `σ` at `ξ` is the fibre degree of `a`. -/
theorem relativePicardFppfSheafFiberDegree_eq_of_restrict_eq {T : (Over S)ᵒᵖ}
    (ξ : Spec (.of K) ⟶ T.unop.left) (σ : (relativePicardFppfSheaf f).obj.obj T)
    (a : LineBundleClass (pullback (ξ ≫ T.unop.hom) f))
    (ha : (relativePicardToFppfSheaf f).app (op (Over.mk (ξ ≫ T.unop.hom)))
        (relativePicardAddPresheafMk f (op (Over.mk (ξ ≫ T.unop.hom))) a) =
      (relativePicardFppfSheaf f).obj.map
        (Over.homMk ξ : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop).op σ) :
    relativePicardFppfSheafFiberDegree f ξ σ =
      relativePicardFiberDegree f (T := op (Over.mk (ξ ≫ T.unop.hom))) (𝟙 _)
        (QuotientGroup.mk a) :=
  relativePicardFppfSheafFiberDegree_eq_of_map_eq f ξ σ
    (Over.homMk ξ : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop) (𝟙 _) (by simp) a ha

/-- The fibre degree of the class of a line bundle on `X_T` is its fibre degree
`relativePicardFiberDegree`. -/
@[simp]
theorem relativePicardFppfSheafFiberDegree_toFppfSheaf {T : (Over S)ᵒᵖ}
    (ξ : Spec (.of K) ⟶ T.unop.left) (a : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardFppfSheafFiberDegree f ξ
        ((relativePicardToFppfSheaf f).app T (relativePicardAddPresheafMk f T a)) =
      relativePicardFiberDegree f ξ (QuotientGroup.mk a) :=
  relativePicardFppfSheafFiberDegree_eq_of_map_eq f ξ _ (𝟙 T.unop) ξ (by simp) a (by simp)

/-- **Naturality of the fibre degree.** For a morphism `T' ⟶ T` of test schemes and a geometric
point `ξ : Spec K ⟶ T'`, the fibre degree at `ξ` of the restriction of a section to `T'` is its
fibre degree at the composite point `Spec K ⟶ T' ⟶ T`. -/
theorem relativePicardFppfSheafFiberDegree_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (ξ : Spec (.of K) ⟶ T'.unop.left) (σ : (relativePicardFppfSheaf f).obj.obj T) :
    relativePicardFppfSheafFiberDegree f ξ ((relativePicardFppfSheaf f).obj.map φ σ) =
      relativePicardFppfSheafFiberDegree f (ξ ≫ φ.unop.left) σ := by
  let ι : Over.mk (ξ ≫ T'.unop.hom) ⟶ T'.unop := Over.homMk ξ
  obtain ⟨a, ha⟩ := exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed f (ξ ≫ T'.unop.hom)
    ((relativePicardFppfSheaf f).obj.map ι.op ((relativePicardFppfSheaf f).obj.map φ σ))
  rw [relativePicardFppfSheafFiberDegree_eq_of_restrict_eq f ξ _ a ha,
    relativePicardFppfSheafFiberDegree_eq_of_map_eq f (ξ ≫ φ.unop.left) σ (ι ≫ φ.unop) (𝟙 _)
      (by simp [ι]) a (by rw [ha, op_comp, Quiver.Hom.op_unop, Functor.map_comp,
        ConcreteCategory.comp_apply])]

/-- The zero section has degree zero on every geometric fibre. -/
@[simp]
theorem relativePicardFppfSheafFiberDegree_zero {T : (Over S)ᵒᵖ}
    (ξ : Spec (.of K) ⟶ T.unop.left) :
    relativePicardFppfSheafFiberDegree f ξ (0 : (relativePicardFppfSheaf f).obj.obj T) = 0 := by
  rw [← map_zero ((relativePicardToFppfSheaf f).app T).hom, ← relativePicardAddPresheafMk_one,
    relativePicardFppfSheafFiberDegree_toFppfSheaf, relativePicardFiberDegree_mk,
    LineBundleClass.pullback_one, LineBundleClass.eulerDegree_one]

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- **The fibre degree is additive** for a smooth proper geometrically connected family of
curves. -/
@[simp]
theorem relativePicardFppfSheafFiberDegree_add {T : (Over S)ᵒᵖ} (ξ : Spec (.of K) ⟶ T.unop.left)
    (σ τ : (relativePicardFppfSheaf f).obj.obj T) :
    relativePicardFppfSheafFiberDegree f ξ (σ + τ) =
      relativePicardFppfSheafFiberDegree f ξ σ + relativePicardFppfSheafFiberDegree f ξ τ := by
  let ι : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop := Over.homMk ξ
  obtain ⟨a, ha⟩ := exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed f (ξ ≫ T.unop.hom)
    ((relativePicardFppfSheaf f).obj.map ι.op σ)
  obtain ⟨b, hb⟩ := exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed f (ξ ≫ T.unop.hom)
    ((relativePicardFppfSheaf f).obj.map ι.op τ)
  rw [relativePicardFppfSheafFiberDegree_eq_of_restrict_eq f ξ σ a ha,
    relativePicardFppfSheafFiberDegree_eq_of_restrict_eq f ξ τ b hb,
    relativePicardFppfSheafFiberDegree_eq_of_restrict_eq f ξ (σ + τ) (a * b)
      (by rw [relativePicardAddPresheafMk_mul, map_add, map_add, ha, hb])]
  -- The product in `Pic(X_T) / Pic(T)` is the product of the quotient group; `exact` sees this
  -- through the carrier at default transparency.
  exact relativePicardFiberDegree_mul_of_smooth f (T := op (Over.mk (ξ ≫ T.unop.hom))) (𝟙 _)
    (QuotientGroup.mk a) (QuotientGroup.mk b)

/-- The fibre degree of the negative of a section is the negative of its fibre degree. -/
@[simp]
theorem relativePicardFppfSheafFiberDegree_neg {T : (Over S)ᵒᵖ} (ξ : Spec (.of K) ⟶ T.unop.left)
    (σ : (relativePicardFppfSheaf f).obj.obj T) :
    relativePicardFppfSheafFiberDegree f ξ (-σ) = -relativePicardFppfSheafFiberDegree f ξ σ := by
  rw [eq_neg_iff_add_eq_zero, ← relativePicardFppfSheafFiberDegree_add, neg_add_cancel,
    relativePicardFppfSheafFiberDegree_zero]

/-- The fibre degree of a difference of sections is the difference of their fibre degrees. -/
@[simp]
theorem relativePicardFppfSheafFiberDegree_sub {T : (Over S)ᵒᵖ} (ξ : Spec (.of K) ⟶ T.unop.left)
    (σ τ : (relativePicardFppfSheaf f).obj.obj T) :
    relativePicardFppfSheafFiberDegree f ξ (σ - τ) =
      relativePicardFppfSheafFiberDegree f ξ σ - relativePicardFppfSheafFiberDegree f ξ τ := by
  rw [sub_eq_add_neg, relativePicardFppfSheafFiberDegree_add,
    relativePicardFppfSheafFiberDegree_neg, ← sub_eq_add_neg]

end GeometricPoint

section Component

/-- An fppf sheaf of abelian groups, such as the relative Picard fppf sheaf, is a sheaf of sets. -/
private lemma isSheaf_obj_comp_forget
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (F.obj ⋙ forget AddCommGrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _
    (forget AddCommGrpCat)).1 F.property)

/-- **The degree-`d` component `Picᵈ_{X/S}`** of the relative Picard fppf sheaf of `f : X ⟶ S`:
at a test scheme `T`, the sections whose fibre degree is `d` at every geometric point
`Spec K ⟶ T`. It is a subsheaf (`isSheaf_relativePicardDegreeFppfSubfunctor`).

The fibre degree is the Euler-characteristic degree `χ(L) - χ(𝒪)` from `H⁰` and `H¹`
(`LineBundleClass.eulerDegree`) of a line bundle on a geometric fibre. It is the usual degree
when the fibres are proper curves, so for a family of curves this is the sheaf of classes of
degree `d`. A section of degree `0` on one component of a
disconnected `T` and of degree `1` on another lies in no component. -/
def relativePicardDegreeFppfSubfunctor (d : ℤ) :
    Subfunctor ((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat) where
  obj T := {σ | ∀ (K : Type u) [Field K] [IsAlgClosed K] (ξ : Spec (.of K) ⟶ T.unop.left),
    relativePicardFppfSheafFiberDegree f ξ σ = d}
  map {_ _} φ σ hσ K _ _ ξ :=
    -- A section of the composite functor is a section of the fppf sheaf, restricted along `φ`.
    (relativePicardFppfSheafFiberDegree_map f φ ξ σ).trans (hσ K _)

/-- A section of the relative Picard fppf sheaf lies in `Picᵈ_{X/S}` exactly when its fibre
degree is `d` at every geometric point. -/
@[simp]
theorem mem_relativePicardDegreeFppfSubfunctor_obj_iff {d : ℤ} {T : (Over S)ᵒᵖ}
    (σ : (relativePicardFppfSheaf f).obj.obj T) :
    σ ∈ (relativePicardDegreeFppfSubfunctor f d).obj T ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (ξ : Spec (.of K) ⟶ T.unop.left),
        relativePicardFppfSheafFiberDegree f ξ σ = d :=
  Iff.rfl

/-- **Membership of an actual class.** The class of a line bundle on `X_T` lies in
`Picᵈ_{X/S}(T)` exactly when it has degree `d` on the fibre of `X_T ⟶ T` over every geometric
point of `T`. -/
theorem relativePicardToFppfSheaf_app_mem_relativePicardDegreeFppfSubfunctor_iff {d : ℤ}
    {T : (Over S)ᵒᵖ} (a : LineBundleClass (pullback T.unop.hom f)) :
    (relativePicardToFppfSheaf f).app T (relativePicardAddPresheafMk f T a) ∈
        (relativePicardDegreeFppfSubfunctor f d).obj T ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (ξ : Spec (.of K) ⟶ T.unop.left),
        relativePicardFiberDegree f ξ (QuotientGroup.mk a) = d := by
  simp only [mem_relativePicardDegreeFppfSubfunctor_obj_iff,
    relativePicardFppfSheafFiberDegree_toFppfSheaf]

/-- **`Picᵈ_{X/S}` is an fppf subsheaf.** A section that lies in `Picᵈ_{X/S}` fppf-locally lies
in it: a geometric point of the test scheme factors through every fppf cover, since the cover
splits over it. -/
theorem isSheaf_relativePicardDegreeFppfSubfunctor (d : ℤ) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (relativePicardDegreeFppfSubfunctor f d).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (isSheaf_obj_comp_forget (relativePicardFppfSheaf f))]
  intro T σ hσ K _ _ ξ
  let ι : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop := Over.homMk ξ
  -- The covering sieve pulled back to the geometric point is maximal, so it contains `ι`.
  have hι : (relativePicardDegreeFppfSubfunctor f d).sieveOfSection σ ι := by
    have htop := Scheme.eq_top_of_mem_fppfTopology_over_of_isAlgClosed K (ξ ≫ T.unop.hom) _
      ((Scheme.fppfTopology.over S).pullback_stable ι hσ)
    simpa using (Sieve.id_mem_iff_eq_top.2 htop : Sieve.pullback ι _ (𝟙 _))
  calc relativePicardFppfSheafFiberDegree f ξ σ =
        relativePicardFppfSheafFiberDegree f (𝟙 _ ≫ ι.op.unop.left) σ := by simp [ι]
    _ = relativePicardFppfSheafFiberDegree f (𝟙 _) ((relativePicardFppfSheaf f).obj.map ι.op σ) :=
        (relativePicardFppfSheafFiberDegree_map f ι.op (𝟙 _) σ).symm
    _ = d := hι K (𝟙 _)

/-- **The degree-`d` component `Picᵈ_{X/S}`** of the relative Picard fppf sheaf, as an fppf sheaf
of sets on schemes over `S`. -/
def relativePicardDegreeFppfSheaf (d : ℤ) : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨(relativePicardDegreeFppfSubfunctor f d).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_relativePicardDegreeFppfSubfunctor f d)⟩

/-- The underlying presheaf of `relativePicardDegreeFppfSheaf f d` is the subfunctor
`relativePicardDegreeFppfSubfunctor f d`. -/
@[simp]
theorem relativePicardDegreeFppfSheaf_obj (d : ℤ) :
    (relativePicardDegreeFppfSheaf f d).obj = (relativePicardDegreeFppfSubfunctor f d).toFunctor :=
  (rfl)

/-- The zero section lies in `Pic⁰_{X/S}`. -/
theorem zero_mem_relativePicardDegreeFppfSubfunctor_obj (T : (Over S)ᵒᵖ) :
    (0 : (relativePicardFppfSheaf f).obj.obj T) ∈ (relativePicardDegreeFppfSubfunctor f 0).obj T :=
  fun _ _ _ ξ ↦ relativePicardFppfSheafFiberDegree_zero f ξ

/-- **The components are disjoint** over a nonempty test scheme. -/
theorem eq_of_mem_relativePicardDegreeFppfSubfunctor_obj {d e : ℤ} {T : (Over S)ᵒᵖ}
    [Nonempty T.unop.left] {σ : (relativePicardFppfSheaf f).obj.obj T}
    (hd : σ ∈ (relativePicardDegreeFppfSubfunctor f d).obj T)
    (he : σ ∈ (relativePicardDegreeFppfSubfunctor f e).obj T) : d = e := by
  obtain ⟨x⟩ := ‹Nonempty T.unop.left›
  -- A geometric point over `x`, through an algebraic closure of its residue field.
  let ξ : Spec (.of (AlgebraicClosure (T.unop.left.residueField x))) ⟶ T.unop.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.unop.left.residueField x)
      (AlgebraicClosure (T.unop.left.residueField x)))) ≫ T.unop.left.fromSpecResidueField x
  exact (hd _ ξ).symm.trans (he _ ξ)

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- **Degrees add**: for a smooth proper geometrically connected family of curves, the sum of a
section of `Picᵈ_{X/S}` and a section of `Picᵉ_{X/S}` lies in `Picᵈ⁺ᵉ_{X/S}`. -/
theorem add_mem_relativePicardDegreeFppfSubfunctor_obj {d e : ℤ} {T : (Over S)ᵒᵖ}
    {σ τ : (relativePicardFppfSheaf f).obj.obj T}
    (hσ : σ ∈ (relativePicardDegreeFppfSubfunctor f d).obj T)
    (hτ : τ ∈ (relativePicardDegreeFppfSubfunctor f e).obj T) :
    σ + τ ∈ (relativePicardDegreeFppfSubfunctor f (d + e)).obj T := fun K _ _ ξ ↦ by
  rw [relativePicardFppfSheafFiberDegree_add, hσ K ξ, hτ K ξ]

/-- Negation sends `Picᵈ_{X/S}` to `Pic⁻ᵈ_{X/S}`. -/
theorem neg_mem_relativePicardDegreeFppfSubfunctor_obj {d : ℤ} {T : (Over S)ᵒᵖ}
    {σ : (relativePicardFppfSheaf f).obj.obj T}
    (hσ : σ ∈ (relativePicardDegreeFppfSubfunctor f d).obj T) :
    -σ ∈ (relativePicardDegreeFppfSubfunctor f (-d)).obj T := fun K _ _ ξ ↦ by
  rw [relativePicardFppfSheafFiberDegree_neg, hσ K ξ]

/-- The difference of a section of `Picᵈ_{X/S}` and a section of `Picᵉ_{X/S}` lies in
`Picᵈ⁻ᵉ_{X/S}`. -/
theorem sub_mem_relativePicardDegreeFppfSubfunctor_obj {d e : ℤ} {T : (Over S)ᵒᵖ}
    {σ τ : (relativePicardFppfSheaf f).obj.obj T}
    (hσ : σ ∈ (relativePicardDegreeFppfSubfunctor f d).obj T)
    (hτ : τ ∈ (relativePicardDegreeFppfSubfunctor f e).obj T) :
    σ - τ ∈ (relativePicardDegreeFppfSubfunctor f (d - e)).obj T := fun K _ _ ξ ↦ by
  rw [relativePicardFppfSheafFiberDegree_sub, hσ K ξ, hτ K ξ]

/-- **Divisors of degree `d` give sections of `Picᵈ_{X/S}`.** For a relative effective Cartier
divisor `D` of degree `d` on `X_T`, the class of `𝒪(D)`, the dual of its ideal sheaf, lies in
`Picᵈ_{X/S}(T)`. -/
theorem relativePicardToFppfSheaf_app_mem_relativePicardDegreeFppfSubfunctor_of_mem {d : ℕ}
    {T : (Over S)ᵒᵖ} {D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T}
    (hD : D ∈ (relativeEffectiveCartierDegreeSubfunctor f d).obj T) :
    (relativePicardToFppfSheaf f).app T (relativePicardAddPresheafMk f T
        (LineBundleClass.mk ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
          D.property).isEffectiveCartier.toInvertibleSheaf)⁻¹) ∈
      (relativePicardDegreeFppfSubfunctor f d).obj T :=
  (relativePicardToFppfSheaf_app_mem_relativePicardDegreeFppfSubfunctor_iff f _).2
    fun _ _ _ ξ ↦ by simpa using relativePicardFiberDegree_abelMap_app_of_mem f ξ hD

end Component

section DegreeZero

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- The image in the relative Picard fppf sheaf of a section of the degree-zero Picard presheaf
lies in `Pic⁰_{X/S}`. -/
private lemma relativePicardToFppfSheaf_app_relativePicardDegreeZeroAddPresheafι_app_mem
    {T : (Over S)ᵒᵖ} (c : (relativePicardDegreeZeroAddPresheaf f).obj T) :
    (relativePicardToFppfSheaf f).app T ((relativePicardDegreeZeroAddPresheafι f).app T c) ∈
      (relativePicardDegreeFppfSubfunctor f 0).obj T := by
  obtain ⟨c, rfl⟩ := (relativePicardDegreeZeroAddPresheafAddEquiv f T).surjective c
  obtain ⟨a, ha⟩ :=
    QuotientGroup.mk_surjective ((relativePicardDegreeZeroFunctorι f).app T c.toMul)
  rw [← ofMul_toMul c,
    relativePicardDegreeZeroAddPresheafι_app_addEquiv_ofMul f c.toMul a ha.symm,
    relativePicardToFppfSheaf_app_mem_relativePicardDegreeFppfSubfunctor_iff]
  have hc := relativePicardDegreeZeroFunctorι_app_mem f c.toMul
  rw [← ha] at hc
  exact (mem_relativePicardDegreeZeroSubfunctor_obj_iff f).1 hc

/-- The image of the inclusion `relativePicardDegreeZeroFppfSheafι` is a subsheaf: it is
isomorphic to the degree-zero Picard sheaf, as the inclusion is a monomorphism. -/
private lemma isSheaf_range_relativePicardDegreeZeroFppfSheafι :
    Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (Subfunctor.range (Functor.whiskerRight (relativePicardDegreeZeroFppfSheafι f).hom
        (forget AddCommGrpCat))).toFunctor := by
  have : Mono (Functor.whiskerRight (relativePicardDegreeZeroFppfSheafι f).hom
      (forget AddCommGrpCat)) := by
    have : Mono (relativePicardDegreeZeroFppfSheafι f).hom :=
      (sheafToPresheaf _ _).map_mono (relativePicardDegreeZeroFppfSheafι f)
    have := (NatTrans.mono_iff_mono_app _).1 this
    exact NatTrans.mono_of_mono_app _
  exact Presieve.isSheaf_iso _ (asIso (Subfunctor.toRange _))
    (isSheaf_obj_comp_forget (relativePicardDegreeZeroFppfSheaf f))

/-- A section of `Pic⁰_{X/S}` that is the class of a line bundle lies in the image of the
degree-zero Picard sheaf. -/
private lemma relativePicardToFppfSheaf_app_mem_range_relativePicardDegreeZeroFppfSheafι
    {T : (Over S)ᵒᵖ} (a : LineBundleClass (pullback T.unop.hom f))
    (ha : (relativePicardToFppfSheaf f).app T (relativePicardAddPresheafMk f T a) ∈
      (relativePicardDegreeFppfSubfunctor f 0).obj T) :
    (relativePicardToFppfSheaf f).app T (relativePicardAddPresheafMk f T a) ∈
      (Subfunctor.range (Functor.whiskerRight (relativePicardDegreeZeroFppfSheafι f).hom
        (forget AddCommGrpCat))).obj T := by
  rw [relativePicardToFppfSheaf_app_mem_relativePicardDegreeFppfSubfunctor_iff] at ha
  have ha' : (QuotientGroup.mk a : (relativePicardPresheaf f).obj T) ∈
      (relativePicardDegreeZeroSubfunctor f).obj T :=
    (mem_relativePicardDegreeZeroSubfunctor_obj_iff f).2 ha
  exact ⟨(relativePicardDegreeZeroToFppfSheaf f).app _
    (relativePicardDegreeZeroAddPresheafAddEquiv f _
      (Additive.ofMul (relativePicardDegreeZeroFunctor.mk f _ ha'))),
    (relativePicardDegreeZeroFppfSheafι_hom_app_toFppfSheaf f _).trans
      (congrArg _ (relativePicardDegreeZeroAddPresheafι_app_addEquiv_ofMul f _ a
        (relativePicardDegreeZeroFunctorι_app_mk f _ ha')))⟩

/-- **The degree-zero Picard sheaf is the component `Pic⁰_{X/S}`.** For a smooth proper
geometrically connected family of curves, the inclusion `relativePicardDegreeZeroFppfSheafι` of
the fppf sheafification of the degree-zero Picard presheaf into the relative Picard fppf sheaf has
image the degree-zero component `relativePicardDegreeFppfSubfunctor f 0`. -/
theorem range_relativePicardDegreeZeroFppfSheafι :
    Subfunctor.range (Functor.whiskerRight (relativePicardDegreeZeroFppfSheafι f).hom
      (forget AddCommGrpCat)) = relativePicardDegreeFppfSubfunctor f 0 := by
  have hF := isSheaf_obj_comp_forget (relativePicardFppfSheaf f)
  apply le_antisymm
  · -- A section of the image is fppf-locally the image of a degree-zero presheaf section.
    rintro T _ ⟨ρ, rfl⟩
    refine (Subfunctor.isSheaf_iff _ hF).1 (isSheaf_relativePicardDegreeFppfSubfunctor f 0) T _
      ((Scheme.fppfTopology.over S).superset_covering ?_
        (Presheaf.imageSieve_mem _ (relativePicardDegreeZeroToFppfSheaf f) ρ))
    rintro V h ⟨c, hc⟩
    have := relativePicardToFppfSheaf_app_relativePicardDegreeZeroAddPresheafι_app_mem f c
    rw [← relativePicardDegreeZeroFppfSheafι_hom_app_toFppfSheaf, hc,
      NatTrans.naturality_apply] at this
    exact this
  · -- A section of `Pic⁰_{X/S}` is fppf-locally the class of a line bundle of degree zero.
    intro T σ hσ
    refine (Subfunctor.isSheaf_iff _ hF).1 (isSheaf_range_relativePicardDegreeZeroFppfSheafι f) T σ
      ((Scheme.fppfTopology.over S).superset_covering ?_
        (Presheaf.imageSieve_mem _ (relativePicardToFppfSheaf f) σ))
    rintro V h ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := relativePicardAddPresheafMk_surjective f _ x
    have := relativePicardToFppfSheaf_app_mem_range_relativePicardDegreeZeroFppfSheafι f a
      (by rw [hx]; exact (relativePicardDegreeFppfSubfunctor f 0).map h.op hσ)
    rw [hx] at this
    exact this

end DegreeZero

section BaseChange

variable {S' : Scheme.{u}} (g : S' ⟶ S) [QuasiCompact f] [IsSeparated f]

/-- **Base change preserves the fibre degree.** For `f` quasi-compact and separated and
`g : S' ⟶ S`, the fibre degree at a geometric point of a section of the relative Picard fppf
sheaf of `X' = S' ×_S X ⟶ S'` is the fibre degree of its image under the base-change comparison
`relativePicardFppfSheafBaseChangeIso`. -/
@[simp]
theorem relativePicardFppfSheafFiberDegree_baseChangeIso_hom_app {K : Type u} [Field K]
    [IsAlgClosed K] {T : (Over S')ᵒᵖ} (ξ : Spec (.of K) ⟶ T.unop.left)
    (σ : (relativePicardFppfSheaf (pullback.fst g f)).obj.obj T) :
    relativePicardFppfSheafFiberDegree f (T := (Over.map g).op.obj T) ξ
        ((relativePicardFppfSheafBaseChangeIso f g).hom.hom.app T σ) =
      relativePicardFppfSheafFiberDegree (pullback.fst g f) ξ σ := by
  let ι : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop := Over.homMk ξ
  obtain ⟨a, ha⟩ := exists_relativePicardToFppfSheaf_app_eq_of_isAlgClosed (pullback.fst g f)
    (ξ ≫ T.unop.hom) ((relativePicardFppfSheaf (pullback.fst g f)).obj.map ι.op σ)
  rw [relativePicardFppfSheafFiberDegree_eq_of_restrict_eq (pullback.fst g f) ξ σ a ha]
  -- The comparison commutes with restriction to the geometric point, where it pulls back `a`.
  refine (relativePicardFppfSheafFiberDegree_eq_of_map_eq f (T := (Over.map g).op.obj T) ξ
    ((relativePicardFppfSheafBaseChangeIso f g).hom.hom.app T σ) ((Over.map g).map ι) (𝟙 _)
    (by simp [ι])
    (LineBundleClass.pullback (pullbackRightPullbackFstIso g f (ξ ≫ T.unop.hom)).inv a)
    ?_).trans ?_
  · exact (relativePicardFppfSheafBaseChangeIso_hom_app_toFppfSheaf_mk f g
      (T := op (Over.mk (ξ ≫ T.unop.hom))) a).symm.trans ((congrArg _ ha).trans
        (NatTrans.naturality_apply (relativePicardFppfSheafBaseChangeIso f g).hom.hom ι.op σ))
  exact (congrArg (relativePicardFiberDegree f (T := (Over.map g).op.obj (op (Over.mk _))) (𝟙 _))
    (relativePicardPresheafBaseChangeIso_hom_app_mk f g _ a)).symm.trans
      (relativePicardFiberDegree_relativePicardPresheafBaseChangeIso_hom_app f g
        (T := op (Over.mk (ξ ≫ T.unop.hom))) (𝟙 _) (QuotientGroup.mk a))

/-- **Base change of the degree components.** Under the base-change comparison
`relativePicardFppfSheafBaseChangeIso`, a section of the relative Picard fppf sheaf of
`X' = S' ×_S X ⟶ S'` lies in `Picᵈ_{X'/S'}` exactly when its image lies in `Picᵈ_{X/S}`: the
component `Picᵈ_{X/S}` restricted to schemes over `S'` is `Picᵈ_{X'/S'}`. -/
theorem relativePicardFppfSheafBaseChangeIso_hom_app_mem_relativePicardDegreeFppfSubfunctor_iff
    {d : ℤ} {T : (Over S')ᵒᵖ} (σ : (relativePicardFppfSheaf (pullback.fst g f)).obj.obj T) :
    (relativePicardFppfSheafBaseChangeIso f g).hom.hom.app T σ ∈
        (relativePicardDegreeFppfSubfunctor f d).obj ((Over.map g).op.obj T) ↔
      σ ∈ (relativePicardDegreeFppfSubfunctor (pullback.fst g f) d).obj T :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun ξ ↦
    iff_of_eq (congrArg (· = d)
      (relativePicardFppfSheafFiberDegree_baseChangeIso_hom_app f g (T := T) ξ σ))

end BaseChange

end

end TauCeti.AlgebraicGeometry
