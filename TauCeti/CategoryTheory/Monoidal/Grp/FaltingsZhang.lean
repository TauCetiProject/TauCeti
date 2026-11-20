/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Differences, shifts and Faltings–Zhang coordinates of maps to a group object

Let `G` be a group object in a cartesian monoidal category `C` and `X` an object of `C`. This file
builds the coordinate maps out of fibre powers of `X` that Faltings–Zhang type arguments apply to a
curve `X` mapping to its Jacobian `G`, in Mathlib's multiplicative notation for the group of points
`T ⟶ G`.

* The **difference** of a morphism `a : X ⟶ G` is `X ⊗ X ⟶ G`, `(x, y) ↦ a y / a x`. It vanishes
  on the diagonal, is inverted by swapping the factors, satisfies the cocycle relation
  `d(y, z) * d(x, y) = d(x, z)`, and is unchanged when `a` is right-translated by a global point.
  None of this needs `G` to be commutative.
* The **universal shift** of a morphism `c : X ⟶ G` is the morphism `G ⊗ X ⟶ G ⊗ G`,
  `(y, x) ↦ (y, y * c x)`, over the first factor `G`.
* The **Faltings–Zhang morphism** of a morphism `d : X ⊗ X ⟶ G` is the morphism from the
  `(m + 1)`-st power of `X` to the `m`-th power of `G` sending `(x₀, …, x_m)` to
  `(d(x₀, x₁), …, d(x₀, x_m))`. It is defined for an arbitrary `d`, so that it applies to the
  section-free difference morphism of a curve, which need not be the difference of any morphism
  `X ⟶ G`; when `d` is the difference of `a`, its coordinates are `a x_{r} / a x₀`.
* The **shifted Faltings–Zhang morphism** of `c : X ⟶ G` and `d : X ⊗ X ⟶ G` is the morphism
  from `X^{n+1} ⊗ G` to `G^{n+1}` sending `(x₀, …, x_n, y)` to
  `(c x₀ * y, d(x₀, x₁), …, d(x₀, x_n))`: the head coordinate is shifted by `y`, the tail
  coordinates are the unshifted Faltings–Zhang coordinates.

For a smooth projective curve `X` over a base `S` with relative Jacobian `J`, working in the
category `Over S` (where `⊗` is the fibre product over `S`), the relevant pairing `d` is the
curve difference `j(x, y) = [y] − [x]`, and the shifts use the canonical-bundle Abel map
`c = i_ω`, `x ↦ (2g − 2)[x] − ω`. With these inputs `faltingsZhang` and `shiftedFaltingsZhang` are
the Faltings–Zhang morphism of Dimitrov–Gao–Habegger (6.3) and its shifted form in Yuan §4.6.2.
When `X` has a degree-one point `x₀` and `a : X ⟶ J` is the Abel map based at it, `j` is the
difference of `a`. Since every statement here is an equality of morphisms, it holds on points with
values in every `S`-scheme, nonreduced ones included.

Every construction commutes with a functor `F : C ⥤ D` (for instance base change along `S' ⟶ S`)
through the canonical product comparison maps `prodComparison` and `piComparison`; for the maps
that multiply, `F` is monoidal and `F.obj G` carries the image group structure. The comparisons
need not be isomorphisms for this.

## Main definitions

* `TauCeti.GrpObj.difference a`: the morphism `(x, y) ↦ a y / a x`.
* `TauCeti.GrpObj.universalShift c`: the morphism `(y, x) ↦ (y, y * c x)`.
* `TauCeti.GrpObj.faltingsZhang d m`: the morphism `(x₀, …, x_m) ↦ (d(x₀, x_{r}))_{1 ≤ r ≤ m}`.
* `TauCeti.GrpObj.shiftedFaltingsZhang c d n`: the morphism
  `(x₀, …, x_n, y) ↦ (c x₀ * y, d(x₀, x₁), …, d(x₀, x_n))`.

## Main results

* `TauCeti.GrpObj.lift_comp_difference`, `TauCeti.GrpObj.lift_comp_universalShift`,
  `TauCeti.GrpObj.lift_comp_faltingsZhang`, `TauCeti.GrpObj.lift_comp_shiftedFaltingsZhang`: the
  four maps on points with values in an object.
* `TauCeti.GrpObj.lift_comp_difference_mul_lift_comp_difference`: the cocycle relation.
* `TauCeti.GrpObj.difference_mul_toUnit_comp`: the difference does not see right translation by a
  global point.
* `TauCeti.GrpObj.shiftedFaltingsZhang_comp_lift_π_succ`: the tail of the shifted Faltings–Zhang
  morphism is the Faltings–Zhang morphism of the curve coordinates.
* `TauCeti.GrpObj.map_difference`, `TauCeti.GrpObj.map_universalShift_comp_prodComparison`,
  `TauCeti.GrpObj.map_faltingsZhang_comp_piComparison`,
  `TauCeti.GrpObj.map_shiftedFaltingsZhang_comp_piComparison`: compatibility with functors.

## References

* V. Dimitrov, Z. Gao, P. Habegger, *Uniformity in Mordell–Lang for curves*, Ann. of Math. 194
  (2021), arXiv:2001.10276v3, §6.1, equation (6.3).
* X. Yuan, *Arithmetic bigness and a uniform Bogomolov-type result*, arXiv:2108.05625v4, §2.2.1,
  Theorem 2.10 and §4.6.2.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.GrpObj

universe v v' u u'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X G : C}

/-! ### The difference of a morphism to a group object -/

section Difference

variable [GrpObj G]

/-- The **difference** of a morphism `a : X ⟶ G` to a group object: the morphism `X ⊗ X ⟶ G`
sending a pair of points `(x, y)` to `a y / a x` (`lift_comp_difference`). -/
noncomputable def difference (a : X ⟶ G) : X ⊗ X ⟶ G :=
  snd X X ≫ a / fst X X ≫ a

theorem difference_def (a : X ⟶ G) : difference a = snd X X ≫ a / fst X X ≫ a :=
  (rfl)

/-- The difference of `a` sends a pair of points `(x, y)` to `a y / a x`. -/
@[reassoc (attr := simp)]
theorem lift_comp_difference {T : C} (x y : T ⟶ X) (a : X ⟶ G) :
    lift x y ≫ difference a = y ≫ a / x ≫ a := by
  simp [difference_def, GrpObj.comp_div]

/-- The difference vanishes on the diagonal. -/
theorem lift_self_comp_difference {T : C} (x : T ⟶ X) (a : X ⟶ G) :
    lift x x ≫ difference a = 1 := by
  simp

/-- Swapping the two points inverts the difference. -/
theorem lift_comp_difference_swap {T : C} (x y : T ⟶ X) (a : X ⟶ G) :
    lift y x ≫ difference a = (lift x y ≫ difference a)⁻¹ := by
  simp

/-- The **cocycle relation** of the difference, `d(y, z) * d(x, y) = d(x, z)`. The order of the
factors matters when `G` is not commutative. -/
theorem lift_comp_difference_mul_lift_comp_difference {T : C} (x y z : T ⟶ X) (a : X ⟶ G) :
    (lift y z ≫ difference a) * (lift x y ≫ difference a) = lift x z ≫ difference a := by
  simp

/-- Right-translating `a` by a global point `c` of `G` does not change its difference. -/
@[simp]
theorem difference_mul_toUnit_comp (a : X ⟶ G) (c : 𝟙_ C ⟶ G) :
    difference (a * (toUnit X ≫ c)) = difference a := by
  simp [difference_def, MonObj.comp_mul, mul_div_mul_right_eq_div]

/-- Composing `a` with a homomorphism of group objects composes its difference. -/
theorem difference_comp {H : C} [GrpObj H] (a : X ⟶ G) (f : G ⟶ H) [IsMonHom f] :
    difference (a ≫ f) = difference a ≫ f := by
  simp [difference_def, GrpObj.div_comp]

/-- Precomposing `a` with `g : Y ⟶ X` precomposes its difference with `g ⊗ g`. -/
theorem tensorHom_comp_difference {Y : C} (g : Y ⟶ X) (a : X ⟶ G) :
    (g ⊗ₘ g) ≫ difference a = difference (g ≫ a) := by
  simp [difference_def, GrpObj.comp_div]

end Difference

/-! ### The universal shift -/

section UniversalShift

variable [MonObj G]

/-- The **universal shift** of a morphism `c : X ⟶ G` to a monoid object: the morphism
`G ⊗ X ⟶ G ⊗ G` sending `(y, x)` to `(y, y * c x)` (`lift_comp_universalShift`). It is a morphism
over the first factor `G` (`universalShift_fst`). -/
noncomputable def universalShift (c : X ⟶ G) : G ⊗ X ⟶ G ⊗ G :=
  lift (fst G X) (fst G X * snd G X ≫ c)

/-- The universal shift keeps the first factor. -/
@[reassoc (attr := simp)]
theorem universalShift_fst (c : X ⟶ G) : universalShift c ≫ fst G G = fst G X := by
  simp [universalShift]

/-- The second coordinate of the universal shift is `y * c x`. -/
@[reassoc (attr := simp)]
theorem universalShift_snd (c : X ⟶ G) :
    universalShift c ≫ snd G G = fst G X * snd G X ≫ c := by
  simp [universalShift]

/-- The universal shift sends a pair of points `(y, x)` to `(y, y * c x)`. -/
@[reassoc (attr := simp)]
theorem lift_comp_universalShift {T : C} (y : T ⟶ G) (x : T ⟶ X) (c : X ⟶ G) :
    lift y x ≫ universalShift c = lift y (y * x ≫ c) := by
  ext <;> simp [MonObj.comp_mul]

/-- The universal shift of the trivial morphism is the diagonal shift `(y, x) ↦ (y, y)`. -/
@[simp]
theorem universalShift_one : universalShift (1 : X ⟶ G) = lift (fst G X) (fst G X) := by
  simp [universalShift]

end UniversalShift

/-! ### The Faltings–Zhang morphism -/

section FaltingsZhang

variable (m n : ℕ) [HasProduct fun _ : Fin (m + 1) => X] [HasProduct fun _ : Fin m => G]

/-- The **Faltings–Zhang morphism** of `d : X ⊗ X ⟶ G`: the morphism from the `(m + 1)`-st power
of `X` to the `m`-th power of `G` sending `(x₀, …, x_m)` to `(d(x₀, x₁), …, d(x₀, x_m))`; target
coordinate `r` uses the source coordinates `0` and `r + 1`, in that order. It is applied to a
difference morphism `d` (`lift_comp_faltingsZhang`). -/
noncomputable def faltingsZhang (d : X ⊗ X ⟶ G) :
    (∏ᶜ fun _ : Fin (m + 1) => X) ⟶ ∏ᶜ fun _ : Fin m => G :=
  Pi.lift fun r => lift (Pi.π _ 0) (Pi.π _ r.succ) ≫ d

/-- Coordinate `r` of the Faltings–Zhang morphism is `d(x₀, x_{r+1})`. -/
@[reassoc (attr := simp)]
theorem faltingsZhang_π (d : X ⊗ X ⟶ G) (r : Fin m) :
    faltingsZhang m d ≫ Pi.π _ r =
      lift (Pi.π (fun _ : Fin (m + 1) => X) 0) (Pi.π _ r.succ) ≫ d := by
  simp [faltingsZhang]

/-- The Faltings–Zhang morphism sends a tuple of points `(x₀, …, x_m)` to
`(d(x₀, x₁), …, d(x₀, x_m))`. -/
@[reassoc (attr := simp)]
theorem lift_comp_faltingsZhang {T : C} (x : Fin (m + 1) → (T ⟶ X)) (d : X ⊗ X ⟶ G) :
    Pi.lift x ≫ faltingsZhang m d = Pi.lift fun r => lift (x 0) (x r.succ) ≫ d :=
  Pi.hom_ext _ _ fun r => by simp [comp_lift_assoc]

variable [HasProduct fun _ : Fin (n + 1) => X] [HasProduct fun _ : Fin (n + 1) => G]

/-- The **shifted Faltings–Zhang morphism** of `c : X ⟶ G` and `d : X ⊗ X ⟶ G`: the morphism
`X^{n+1} ⊗ G ⟶ G^{n+1}` sending `(x₀, …, x_n, y)` to `(c x₀ * y, d(x₀, x₁), …, d(x₀, x_n))`
(`lift_comp_shiftedFaltingsZhang`). Only the head coordinate is shifted by `y`; the tail is the
Faltings–Zhang morphism of `(x₀, …, x_n)` (`shiftedFaltingsZhang_comp_lift_π_succ`). -/
noncomputable def shiftedFaltingsZhang [MonObj G] (c : X ⟶ G) (d : X ⊗ X ⟶ G) :
    (∏ᶜ fun _ : Fin (n + 1) => X) ⊗ G ⟶ ∏ᶜ fun _ : Fin (n + 1) => G :=
  Pi.lift <| Fin.cons (fst _ G ≫ Pi.π _ 0 ≫ c * snd _ G) fun r =>
    fst _ G ≫ lift (Pi.π (fun _ : Fin (n + 1) => X) 0) (Pi.π _ r.succ) ≫ d

variable [MonObj G]

/-- The head coordinate of the shifted Faltings–Zhang morphism is `c x₀ * y`. -/
@[reassoc (attr := simp)]
theorem shiftedFaltingsZhang_π_zero (c : X ⟶ G) (d : X ⊗ X ⟶ G) :
    shiftedFaltingsZhang n c d ≫ Pi.π _ 0 =
      fst _ G ≫ Pi.π (fun _ : Fin (n + 1) => X) 0 ≫ c * snd _ G := by
  simp [shiftedFaltingsZhang]

/-- The tail coordinate `r + 1` of the shifted Faltings–Zhang morphism is `d(x₀, x_{r+1})`. -/
@[reassoc (attr := simp)]
theorem shiftedFaltingsZhang_π_succ (c : X ⟶ G) (d : X ⊗ X ⟶ G) (r : Fin n) :
    shiftedFaltingsZhang n c d ≫ Pi.π _ r.succ =
      fst _ G ≫ lift (Pi.π (fun _ : Fin (n + 1) => X) 0) (Pi.π _ r.succ) ≫ d := by
  simp [shiftedFaltingsZhang]

/-- The shifted Faltings–Zhang morphism sends `(x₀, …, x_n, y)` to
`(c x₀ * y, d(x₀, x₁), …, d(x₀, x_n))`. -/
@[reassoc (attr := simp)]
theorem lift_comp_shiftedFaltingsZhang {T : C} (x : Fin (n + 1) → (T ⟶ X)) (y : T ⟶ G)
    (c : X ⟶ G) (d : X ⊗ X ⟶ G) :
    lift (Pi.lift x) y ≫ shiftedFaltingsZhang n c d =
      Pi.lift (Fin.cons (x 0 ≫ c * y) fun r => lift (x 0) (x r.succ) ≫ d) :=
  Pi.hom_ext _ _ fun r => by
    cases r using Fin.cases <;> simp [MonObj.comp_mul, comp_lift_assoc]

variable [HasProduct fun _ : Fin n => G]

/-- The tail of the shifted Faltings–Zhang morphism forgets the shift: it is the Faltings–Zhang
morphism of the curve coordinates. -/
@[reassoc (attr := simp)]
theorem shiftedFaltingsZhang_comp_lift_π_succ (c : X ⟶ G) (d : X ⊗ X ⟶ G) :
    shiftedFaltingsZhang n c d ≫ Pi.lift (fun r : Fin n => Pi.π _ r.succ) =
      fst _ G ≫ faltingsZhang n d :=
  Pi.hom_ext _ _ fun r => by simp

end FaltingsZhang

/-! ### Compatibility with functors -/

section Functor

open scoped CategoryTheory.Obj

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] (F : C ⥤ D)

local notation "prodComp" => CartesianMonoidalCategory.prodComparison

/-- A monoidal functor sends the difference of `a` to the difference of `F.map a` through the
product comparison map, where `F.obj G` carries the image group structure. -/
theorem map_difference [F.Monoidal] [GrpObj G] (a : X ⟶ G) :
    F.map (difference a) = prodComp F X X ≫ difference (F.map a) := by
  simp only [difference_def, div_eq_mul_inv, Functor.map_mul, Functor.map_inv', F.map_comp,
    MonObj.comp_mul, GrpObj.comp_inv, CartesianMonoidalCategory.prodComparison_fst_assoc,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

/-- A monoidal functor commutes with the universal shift through the product comparison maps,
where `F.obj G` carries the image monoid structure. -/
@[reassoc]
theorem map_universalShift_comp_prodComparison [F.Monoidal] [MonObj G] (c : X ⟶ G) :
    F.map (universalShift c) ≫ prodComp F G G = prodComp F G X ≫ universalShift (F.map c) := by
  ext
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst, ← F.map_comp,
      universalShift_fst]
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, ← F.map_comp,
      universalShift_snd]
    simp only [Functor.map_mul, F.map_comp, MonObj.comp_mul,
      CartesianMonoidalCategory.prodComparison_fst,
      CartesianMonoidalCategory.prodComparison_snd_assoc]

variable (m n : ℕ) [HasProduct fun _ : Fin (m + 1) => X] [HasProduct fun _ : Fin m => G]
  [HasProduct fun _ : Fin (m + 1) => F.obj X] [HasProduct fun _ : Fin m => F.obj G]

/-- A functor commutes with the Faltings–Zhang morphism through the product comparison maps, once
`F.map d` is written as `d'` after the comparison `F (X ⊗ X) ⟶ F X ⊗ F X`. -/
@[reassoc]
theorem map_faltingsZhang_comp_piComparison (d : X ⊗ X ⟶ G) (d' : F.obj X ⊗ F.obj X ⟶ F.obj G)
    (h : prodComp F X X ≫ d' = F.map d) :
    F.map (faltingsZhang m d) ≫ piComparison F _ =
      piComparison F (fun _ : Fin (m + 1) => X) ≫ faltingsZhang m d' :=
  Pi.hom_ext _ _ fun r => by
    have hl : F.map (lift (Pi.π (fun _ : Fin (m + 1) => X) 0) (Pi.π _ r.succ)) ≫
        prodComp F X X = piComparison F _ ≫ lift (Pi.π _ 0) (Pi.π _ r.succ) := by
      ext <;> simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
        CartesianMonoidalCategory.prodComparison_snd, lift_fst, lift_snd, piComparison_comp_π,
        ← F.map_comp]
    rw [Category.assoc, piComparison_comp_π, ← F.map_comp, faltingsZhang_π, F.map_comp, ← h,
      reassoc_of% hl, Category.assoc, faltingsZhang_π]

variable [HasProduct fun _ : Fin (n + 1) => X] [HasProduct fun _ : Fin (n + 1) => G]
  [HasProduct fun _ : Fin (n + 1) => F.obj X] [HasProduct fun _ : Fin (n + 1) => F.obj G]

/-- A monoidal functor commutes with the shifted Faltings–Zhang morphism through the product
comparison maps, once `F.map d` is written as `d'` after the comparison `F (X ⊗ X) ⟶ F X ⊗ F X`;
`F.obj G` carries the image monoid structure. -/
@[reassoc]
theorem map_shiftedFaltingsZhang_comp_piComparison [F.Monoidal] [MonObj G] (c : X ⟶ G)
    (d : X ⊗ X ⟶ G) (d' : F.obj X ⊗ F.obj X ⟶ F.obj G) (h : prodComp F X X ≫ d' = F.map d) :
    F.map (shiftedFaltingsZhang n c d) ≫ piComparison F _ =
      prodComp F _ G ≫ (piComparison F (fun _ : Fin (n + 1) => X) ▷ F.obj G) ≫
        shiftedFaltingsZhang n (F.map c) d' :=
  Pi.hom_ext _ _ fun r => by
    cases r using Fin.cases with
    | zero =>
      simp only [Category.assoc, piComparison_comp_π, ← F.map_comp, shiftedFaltingsZhang_π_zero]
      simp only [Functor.map_mul, F.map_comp, MonObj.comp_mul, whiskerRight_fst_assoc,
        whiskerRight_snd, piComparison_comp_π_assoc,
        CartesianMonoidalCategory.prodComparison_fst_assoc,
        CartesianMonoidalCategory.prodComparison_snd]
    | succ r =>
      have hl : F.map (lift (Pi.π (fun _ : Fin (n + 1) => X) 0) (Pi.π _ r.succ)) ≫
          prodComp F X X = piComparison F _ ≫ lift (Pi.π _ 0) (Pi.π _ r.succ) := by
        ext <;> simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
          CartesianMonoidalCategory.prodComparison_snd, lift_fst, lift_snd, piComparison_comp_π,
          ← F.map_comp]
      rw [Category.assoc, piComparison_comp_π, ← F.map_comp, shiftedFaltingsZhang_π_succ,
        F.map_comp, F.map_comp, ← h, reassoc_of% hl, Category.assoc, Category.assoc,
        shiftedFaltingsZhang_π_succ, whiskerRight_fst_assoc,
        CartesianMonoidalCategory.prodComparison_fst_assoc]

end Functor

end TauCeti.GrpObj
