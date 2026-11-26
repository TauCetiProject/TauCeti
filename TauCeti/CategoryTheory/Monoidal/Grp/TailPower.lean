/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.Pi
public import TauCeti.CategoryTheory.Monoidal.Grp.Difference
public import TauCeti.CategoryTheory.Monoidal.Grp.FaltingsZhang
public import TauCeti.CategoryTheory.Monoidal.Grp.Triangular

/-!
# Shifted powers, tail powers and the shifted-power factorization

Let `G` be a group object in a cartesian monoidal category `C`, let `X` be an object of `C` and
`c : X ⟶ G` a morphism, written in Mathlib's multiplicative notation for the group of points
`T ⟶ G`. This file builds two maps between powers of `X` and `G` and relates them to the
Faltings–Zhang coordinates of `TauCeti.GrpObj.shiftedFaltingsZhang`.

* The **shifted power** `shiftedPower J c : X^J ⊗ G ⟶ G^J` sends `((x_i)_i, y)` to the tuple
  `(c x_i * y)_i`: every coordinate is translated by the same `y`.
* The **tail power** `tailZPow G i₀ e : G^J ⟶ G^J`, for `e : ℤ`, keeps the head coordinate
  `q_{i₀}` and raises every other coordinate to the `e`-th power.

The main result `shiftedPower_comp_triangularIso_hom` is the factorization through the triangular
change of coordinates `R = TauCeti.GrpObj.triangularIso G 0` of `G^{n+1}`: if a morphism
`d : X ⊗ X ⟶ G` satisfies `difference c = d ^ e`, that is `c y / c x = d(x, y) ^ e`, then
`R ∘ shiftedPower c = tailZPow e ∘ shiftedFaltingsZhang c d`. On the tail coordinates the common
shift `y` cancels in `(c x_r * y) / (c x₀ * y) = c x_r / c x₀`, so no commutativity of `G` is
needed.

Separating the head coordinate by `piFinSuccIso`, the tail power is `𝟙 G ⊗ [e]ⁿ`, where
`[e] = 𝟙 G ^ e : G ⟶ G` is the `e`-th power map (`tailZPow_comp_piFinSuccIso_hom`). Hence any
property of morphisms that respects isomorphisms holds for the tail power exactly when it holds
for `G ◁ Pi.map (fun _ => [e])` (`morphismProperty_tailZPow_iff`). Both maps commute with monoidal
functors through the product comparison maps.

For a smooth projective curve `X` of genus `g > 1` over a base `S` with relative Jacobian `J`,
in the category `Over S` (where `⊗` is the fibre product over `S`), the inputs are the canonical
Abel map `c = i_ω`, `x ↦ (2g − 2)[x] − ω`, the curve difference `d(x, y) = [y] − [x]` and
`e = 2g − 2`, for which `i_ω(y) − i_ω(x) = (2g − 2)(y − x)`. The factorization then says that the
shifted canonical power `(x₁, …, x_m, y) ↦ (i_ω(x_r) + y)_r`, after the triangular change of
coordinates, is the shifted Faltings–Zhang morphism followed by multiplication by `2g − 2` on the
tail coordinates. Since every statement here is an equality of morphisms, it holds on points with
values in every `S`-scheme, nonreduced ones included.

## Main definitions

* `TauCeti.GrpObj.shiftedPower J c`: the morphism `((x_i)_i, y) ↦ (c x_i * y)_i`.
* `TauCeti.GrpObj.tailZPow G i₀ e`: the morphism keeping coordinate `i₀` and raising every other
  coordinate to the `e`-th power.

## Main results

* `TauCeti.GrpObj.shiftedPower_comp_triangularIso_hom`: **the shifted-power factorization**.
* `TauCeti.GrpObj.tailZPow_comp_piFinSuccIso_hom`: the tail power is `𝟙 G ⊗ [e]ⁿ` after
  separating the head coordinate; `TauCeti.GrpObj.morphismProperty_tailZPow_iff` transfers
  properties of morphisms along this identification.
* `TauCeti.GrpObj.tailZPow_mul`, `TauCeti.GrpObj.tailZPow_one`: the tail powers compose like the
  exponents; in particular `tailZPow G i₀ (-1)` is an isomorphism, inverse to itself
  (`TauCeti.GrpObj.inv_tailZPow_neg_one`).
* `TauCeti.GrpObj.map_shiftedPower_comp_piComparison`,
  `TauCeti.GrpObj.map_tailZPow_comp_piComparison`: compatibility with monoidal functors.

## References

* X. Yuan, *Arithmetic bigness and a uniform Bogomolov-type result*, arXiv:2108.05625v4,
  §4.6.2 and the proof of Theorem 4.17(5).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.GrpObj

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X G : C}

/-! ### The shifted power -/

section ShiftedPower

variable (J : Type w) [HasProduct fun _ : J => X] [HasProduct fun _ : J => G] [MonObj G]

/-- The **shifted power** of `c : X ⟶ G`: the morphism `X^J ⊗ G ⟶ G^J` sending `((x_i)_i, y)` to
`(c x_i * y)_i`, every coordinate translated by the same `y` (`lift_comp_shiftedPower`). -/
noncomputable def shiftedPower (c : X ⟶ G) : (∏ᶜ fun _ : J => X) ⊗ G ⟶ ∏ᶜ fun _ : J => G :=
  Pi.lift fun i => fst _ G ≫ Pi.π _ i ≫ c * snd _ G

/-- Coordinate `i` of the shifted power is `c x_i * y`. -/
@[reassoc (attr := simp)]
theorem shiftedPower_π (c : X ⟶ G) (i : J) :
    shiftedPower J c ≫ Pi.π _ i = fst _ G ≫ Pi.π (fun _ : J => X) i ≫ c * snd _ G := by
  simp [shiftedPower]

/-- The shifted power sends `((x_i)_i, y)` to `(c x_i * y)_i`. -/
@[reassoc (attr := simp)]
theorem lift_comp_shiftedPower {T : C} (x : J → (T ⟶ X)) (y : T ⟶ G) (c : X ⟶ G) :
    lift (Pi.lift x) y ≫ shiftedPower J c = Pi.lift fun i => x i ≫ c * y :=
  Pi.hom_ext _ _ fun i => by simp [MonObj.comp_mul]

end ShiftedPower

/-! ### The tail power -/

section TailZPow

variable (G) [GrpObj G] {J : Type w} [DecidableEq J] (i₀ : J) [HasProduct fun _ : J => G]

/-- The **tail power** with head index `i₀` and exponent `e`: the endomorphism of `G^J` keeping
the head coordinate `q_{i₀}` and replacing every other coordinate `q_i` by `q_i ^ e`
(`lift_comp_tailZPow`). -/
noncomputable def tailZPow (e : ℤ) : (∏ᶜ fun _ : J => G) ⟶ ∏ᶜ fun _ : J => G :=
  Pi.lift fun i => if i = i₀ then Pi.π (fun _ : J => G) i else Pi.π (fun _ : J => G) i ^ e

/-- The tail power keeps the head coordinate. -/
@[reassoc (attr := simp)]
theorem tailZPow_π_self (e : ℤ) :
    tailZPow G i₀ e ≫ Pi.π (fun _ : J => G) i₀ = Pi.π (fun _ : J => G) i₀ := by
  simp [tailZPow]

/-- The tail power raises each non-head coordinate to the `e`-th power. -/
@[reassoc (attr := simp)]
theorem tailZPow_π_of_ne (e : ℤ) {i : J} (h : i ≠ i₀) :
    tailZPow G i₀ e ≫ Pi.π (fun _ : J => G) i = Pi.π (fun _ : J => G) i ^ e := by
  simp [tailZPow, h]

/-- On a point `q` with values in `T`, the tail power keeps `q_{i₀}` and replaces `q_i` by
`q_i ^ e` for `i ≠ i₀`. -/
@[reassoc (attr := simp)]
theorem lift_comp_tailZPow {T : C} (q : J → (T ⟶ G)) (e : ℤ) :
    Pi.lift q ≫ tailZPow G i₀ e = Pi.lift fun i => if i = i₀ then q i else q i ^ e :=
  Pi.hom_ext _ _ fun i => by by_cases h : i = i₀ <;> simp [h, GrpObj.comp_zpow]

/-- The tail power with exponent `1` is the identity. -/
@[simp]
theorem tailZPow_one : tailZPow G i₀ 1 = 𝟙 _ :=
  Pi.hom_ext _ _ fun i => by by_cases h : i = i₀ <;> simp [h]

/-- Tail powers compose like their exponents: `(q_i ^ e) ^ e' = q_i ^ (e * e')`. -/
theorem tailZPow_mul (e e' : ℤ) : tailZPow G i₀ (e * e') = tailZPow G i₀ e ≫ tailZPow G i₀ e' :=
  Pi.hom_ext _ _ fun i => by
    by_cases h : i = i₀
    · subst h
      simp
    · simp [h, GrpObj.comp_zpow, zpow_mul]

/-- The tail power with exponent `-1`, which inverts every non-head coordinate, is an
isomorphism, inverse to itself. -/
instance isIso_tailZPow_neg_one : IsIso (tailZPow G i₀ (-1)) :=
  ⟨tailZPow G i₀ (-1), by simp [← tailZPow_mul], by simp [← tailZPow_mul]⟩

/-- The tail power with exponent `-1` is its own inverse. -/
@[simp]
theorem inv_tailZPow_neg_one : inv (tailZPow G i₀ (-1)) = tailZPow G i₀ (-1) :=
  IsIso.inv_eq_of_hom_inv_id (by simp [← tailZPow_mul])

/-- For a single factor there is no tail, and the tail power is the identity for every
exponent. -/
theorem tailZPow_eq_id [Subsingleton J] (e : ℤ) : tailZPow G i₀ e = 𝟙 _ :=
  Pi.hom_ext _ _ fun i => by simp [Subsingleton.elim i i₀]

end TailZPow

/-! ### Separating the head coordinate -/

section Head

variable (G) [GrpObj G] (n : ℕ) [HasProduct fun _ : Fin (n + 1) => G]
  [HasProduct fun _ : Fin n => G]

/-- After separating the head coordinate, the tail power with exponent `e` is `𝟙 G ⊗ [e]ⁿ`, where
`[e] = 𝟙 G ^ e` is the `e`-th power map of `G`. -/
@[reassoc]
theorem tailZPow_comp_piFinSuccIso_hom (e : ℤ) :
    tailZPow G 0 e ≫ (piFinSuccIso fun _ : Fin (n + 1) => G).hom =
      (piFinSuccIso fun _ : Fin (n + 1) => G).hom ≫
        G ◁ Limits.Pi.map fun _ : Fin n => 𝟙 G ^ e := by
  ext i
  · simp
  · simp [Fin.succ_ne_zero, GrpObj.comp_zpow]

/-- A property of morphisms that respects isomorphisms holds for the tail power with exponent `e`
exactly when it holds for `𝟙 G ⊗ [e]ⁿ`, where `[e] = 𝟙 G ^ e` is the `e`-th power map of `G`. -/
theorem morphismProperty_tailZPow_iff (P : MorphismProperty C) [P.RespectsIso] (e : ℤ) :
    P (tailZPow G (0 : Fin (n + 1)) e) ↔ P (G ◁ Limits.Pi.map fun _ : Fin n => 𝟙 G ^ e) :=
  P.arrow_mk_iso_iff <| Arrow.isoMk (piFinSuccIso _) (piFinSuccIso _)
    (tailZPow_comp_piFinSuccIso_hom G n e).symm

end Head

/-! ### The shifted-power factorization -/

section Factorization

variable [GrpObj G] (n : ℕ) [HasProduct fun _ : Fin (n + 1) => X]
  [HasProduct fun _ : Fin (n + 1) => G]

/-- **The shifted-power factorization.** Let `c : X ⟶ G` and `d : X ⊗ X ⟶ G` with
`difference c = d ^ e`, that is `c y / c x = d(x, y) ^ e`. Then the shifted power
`((x_i)_i, y) ↦ (c x_i * y)_i`, followed by the triangular change of coordinates with head `0`, is
the shifted Faltings–Zhang morphism `(x, y) ↦ (c x₀ * y, d(x₀, x₁), …, d(x₀, x_n))` followed by
the tail power with exponent `e`. -/
theorem shiftedPower_comp_triangularIso_hom (c : X ⟶ G) (d : X ⊗ X ⟶ G) (e : ℤ)
    (h : difference c = d ^ e) :
    shiftedPower (Fin (n + 1)) c ≫ (triangularIso G 0).hom =
      shiftedFaltingsZhang n c d ≫ tailZPow G 0 e :=
  Pi.hom_ext _ _ fun r => by
    cases r using Fin.cases with
    | zero => simp
    | succ r =>
      simp only [Category.assoc, triangularIso_hom_π_of_ne _ _ (Fin.succ_ne_zero r),
        tailZPow_π_of_ne _ _ _ (Fin.succ_ne_zero r), GrpObj.comp_div, GrpObj.comp_zpow,
        shiftedPower_π, shiftedFaltingsZhang_π_succ]
      rw [← GrpObj.comp_zpow, ← GrpObj.comp_zpow, ← h]
      simp [difference_def, GrpObj.comp_div]

end Factorization

/-! ### Compatibility with functors -/

section Functor

open scoped CategoryTheory.Obj

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

local notation "prodComp" => CartesianMonoidalCategory.prodComparison

/-- A monoidal functor commutes with the shifted power through the product comparison maps;
`F.obj G` carries the image monoid structure. -/
@[reassoc]
theorem map_shiftedPower_comp_piComparison (J : Type w) [HasProduct fun _ : J => X]
    [HasProduct fun _ : J => G] [HasProduct fun _ : J => F.obj X]
    [HasProduct fun _ : J => F.obj G] [MonObj G] (c : X ⟶ G) :
    F.map (shiftedPower J c) ≫ piComparison F _ =
      prodComp F _ G ≫ (piComparison F (fun _ : J => X) ▷ F.obj G) ≫
        shiftedPower J (F.map c) :=
  Pi.hom_ext _ _ fun i => by
    simp only [Category.assoc, piComparison_comp_π, ← F.map_comp, shiftedPower_π]
    simp only [Functor.map_mul, F.map_comp, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd, piComparison_comp_π_assoc,
      CartesianMonoidalCategory.prodComparison_fst_assoc,
      CartesianMonoidalCategory.prodComparison_snd]

/-- A monoidal functor commutes with the tail power through the product comparison map, where
`F.obj G` carries the image group structure. -/
@[reassoc]
theorem map_tailZPow_comp_piComparison [GrpObj G] {J : Type w} [DecidableEq J] (i₀ : J)
    [HasProduct fun _ : J => G] [HasProduct fun _ : J => F.obj G] (e : ℤ) :
    F.map (tailZPow G i₀ e) ≫ piComparison F (fun _ : J => G) =
      piComparison F (fun _ : J => G) ≫ tailZPow (F.obj G) i₀ e :=
  Pi.hom_ext _ _ fun i => by
    by_cases h : i = i₀
    · subst h
      simp [← F.map_comp]
    · simp only [Category.assoc, piComparison_comp_π, ← F.map_comp, tailZPow_π_of_ne _ _ _ h,
        GrpObj.comp_zpow]
      simpa using map_zpow F.homMonoidHom (Pi.π (fun _ : J => G) i) e

end Functor

end TauCeti.GrpObj
