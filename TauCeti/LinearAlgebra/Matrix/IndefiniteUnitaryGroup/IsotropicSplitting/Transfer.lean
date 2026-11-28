/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.IsotropicSplitting

/-!
# Base change and pullback of isotropic splittings

Let `D = (k, l, ι)` be an isotropic splitting of a hermitian Gram matrix `A` over a Gram matrix
`A₀` along `p` (`TauCeti.IsotropicSplitting`). This file transports `D` in two ways, and shows that
the Levi and unipotent elements of the transported splitting are the transported Levi and unipotent
elements.

* **Base change** (`TauCeti.IsotropicSplitting.map`): a ring homomorphism `f : R →+* S` commuting
  with the involutions carries `D` to the splitting `(k.map f, l.map f, ι.map f)` of `A.map f` over
  `A₀.map f`. Its Levi element of `(f a, f g₀)` is `f (m(a, g₀))`
  (`TauCeti.IsotropicSplitting.val_levi_map`), and its unipotent element of `(f c, f b)` is
  `f (n(c, b))` (`TauCeti.IsotropicSplitting.val_unipotent_map`).
* **Pullback by frames** (`TauCeti.IsotropicSplitting.pullback`): if invertible matrices `x` and
  `x₀` pull the forms back, `x* A x = B` and `x₀* A₀ x₀ = B₀`, then `(x⁻¹ k, x⁻¹ l, x⁻¹ ι x₀)` is a
  splitting of `B` over `B₀`. Its Levi element of `(a, x₀⁻¹ g₀ x₀)` is `x⁻¹ m(a, g₀) x`
  (`TauCeti.IsotropicSplitting.val_levi_pullback`), and its unipotent element of `(x₀⁻¹ c, b)` is
  `x⁻¹ n(c, b) x` (`TauCeti.IsotropicSplitting.val_unipotent_pullback`).

Together they give the adelic frames of a rational splitting of a hermitian space with an adelic
frame `x`: base change from the number field to the adeles, then pullback by `x`.
After base change, the core Levi parameter becomes `x₀⁻¹ g₀ x₀` and the unipotent
parameter becomes `x₀⁻¹ c`; `a` and `b` need no frame change. These elements are the images of
rational Levi and unipotent elements under `γ ↦ x⁻¹ γ x`.

## References

* M.-A. Knus, *Quadratic and Hermitian forms over rings* (1991), the Witt decomposition of a
  hermitian space.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace IsotropicSplitting

variable {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
  {n n₀ p : Type*} [Fintype n] [Fintype n₀] [Fintype p] [DecidableEq n₀] [DecidableEq p]
  {A : Matrix n n R} {A₀ : Matrix n₀ n₀ R} (D : IsotropicSplitting A A₀ p)

/-! ### Base change -/

section Map

variable {f : R →+* S} (hf : ∀ r, f (star r) = star (f r))

/-- The **base change** of an isotropic splitting along a ring homomorphism `f` commuting with the
involutions: the frames `k.map f`, `l.map f` and the core embedding `ι.map f` split `A.map f` over
`A₀.map f`. -/
def map : IsotropicSplitting (A.map f) (A₀.map f) p where
  k := D.k.map f
  l := D.l.map f
  ι := D.ι.map f
  isHermitian := D.isHermitian.map f hf
  isUnit_core := D.isUnit_core.map (RingHom.mapMatrix f)
  gram_kk := by simp only [conjTranspose_map_mul_mul hf, D.gram_kk, Matrix.map_zero _ (map_zero f)]
  gram_ll := by simp only [conjTranspose_map_mul_mul hf, D.gram_ll, Matrix.map_zero _ (map_zero f)]
  gram_lk := by
    simp only [conjTranspose_map_mul_mul hf, D.gram_lk, Matrix.map_one _ (map_zero f) (map_one f)]
  gram_ιι := by rw [conjTranspose_map_mul_mul hf, D.gram_ιι]
  gram_ιk := by simp only [conjTranspose_map_mul_mul hf, D.gram_ιk, Matrix.map_zero _ (map_zero f)]
  gram_ιl := by simp only [conjTranspose_map_mul_mul hf, D.gram_ιl, Matrix.map_zero _ (map_zero f)]
  card_eq := D.card_eq

@[simp]
theorem map_k : (D.map hf).k = D.k.map f :=
  (rfl)

@[simp]
theorem map_l : (D.map hf).l = D.l.map f :=
  (rfl)

@[simp]
theorem map_ι : (D.map hf).ι = D.ι.map f :=
  (rfl)

variable [DecidableEq n]

/-- The **Levi elements of a base change** are the images of the Levi elements: for `g₀'` the
image of `g₀`, the Levi element of `(f a, g₀')` is the image of the Levi element of `(a, g₀)`. -/
theorem val_levi_map (a : GL p R) {g₀ : unitaryGroupOf A₀} {g₀' : unitaryGroupOf (A₀.map f)}
    (hg₀ : ((g₀' : GL n₀ S) : Matrix n₀ n₀ S) = ((g₀ : GL n₀ R) : Matrix n₀ n₀ R).map f) :
    (((D.map hf).levi (GeneralLinearGroup.map f a, g₀') : GL n S) : Matrix n n S) =
      ((D.levi (a, g₀) : GL n R) : Matrix n n R).map f := by
  -- The inverse of `f a` is the image of the inverse of `a`.
  have ha : ((a : Matrix p p R).map f)⁻¹ = ((a : Matrix p p R)⁻¹).map f := by
    rw [← GeneralLinearGroup.val_map_apply, ← coe_units_inv, ← coe_units_inv, ← map_inv,
      GeneralLinearGroup.val_map_apply]
  refine (D.map hf).ext_mul ?_ ?_ ?_ <;>
    simp only [levi_mul_k, levi_mul_ι, levi_mul_l] <;>
    simp only [map_k, map_l, map_ι, ← Matrix.map_mul, levi_mul_k, levi_mul_ι, levi_mul_l] <;>
    simp only [Matrix.map_mul, GeneralLinearGroup.val_map_apply, hg₀, ha, conjTranspose_map f hf]

/-- Base change commutes with the bundled Levi homomorphism. -/
theorem levi_map (a : GL p R) (g₀ : unitaryGroupOf A₀) :
    (D.map hf).levi (GeneralLinearGroup.map f a, unitaryGroupOf.map hf g₀) =
      unitaryGroupOf.map hf (D.levi (a, g₀)) := by
  apply unitaryGroupOf.ext
  simp only [unitaryGroupOf.coe_map, GeneralLinearGroup.val_map_apply]
  exact D.val_levi_map hf a (by simp only [unitaryGroupOf.coe_map,
    GeneralLinearGroup.val_map_apply])

variable {j : Rˣ} (hj : star (j : R) = -j)

variable [Invertible (2 : R)] [Invertible (2 : S)]

/-- The **unipotent elements of a base change** are the images of the unipotent elements: the
unipotent element of `(f c, f b)` for the image `f j` of `j` is the image of `n(c, b)`. -/
theorem val_unipotent_map (c : Matrix n₀ p R) (b : Matrix p p R) :
    (((D.map hf).unipotent (Units.star_coe_map_eq_neg hf hj) (c.map f) (b.map f) : GL n S) :
        Matrix n n S) = ((D.unipotent hj c b : GL n R) : Matrix n n R).map f := by
  -- `f` carries `⅟2` to `⅟2` and `j⁻¹` to `(f j)⁻¹`.
  have h2 : f ⅟2 = ⅟(2 : S) := by
    let := Invertible.map f (2 : R)
    exact (map_invOf f (2 : R)).trans (Invertible.congr _ _ (map_ofNat f 2))
  have hj' : (↑(Units.map (f : R →* S) j)⁻¹ : S) = f ↑j⁻¹ :=
    Units.coe_map_inv (f : R →* S) j
  refine (D.map hf).ext_mul ?_ ?_ ?_ <;>
    simp only [unipotent_mul_k, unipotent_mul_ι, unipotent_mul_l] <;>
    simp only [map_k, map_l, map_ι, ← Matrix.map_mul, unipotent_mul_k, unipotent_mul_ι,
      unipotent_mul_l] <;>
    simp only [Matrix.map_mul, Matrix.map_add _ (map_add f), Matrix.map_sub _ (map_sub f),
      Matrix.map_smul' _ _ _ (map_mul f), conjTranspose_map f hf, h2, hj']

/-- Base change commutes with bundled unipotent elements. -/
theorem unipotent_map (c : Matrix n₀ p R) (b : Matrix p p R) :
    (D.map hf).unipotent (Units.star_coe_map_eq_neg hf hj) (c.map f) (b.map f) =
      unitaryGroupOf.map hf (D.unipotent hj c b) := by
  apply unitaryGroupOf.ext
  simpa only [unitaryGroupOf.coe_map, GeneralLinearGroup.val_map_apply] using
    D.val_unipotent_map hf hj c b

end Map

/-! ### Pullback by frames -/

section Pullback

variable [DecidableEq n] {B : Matrix n n R} {B₀ : Matrix n₀ n₀ R} {x : GL n R} {x₀ : GL n₀ R}
  (hx : star (x : Matrix n n R) * A * x = B) (hx₀ : star (x₀ : Matrix n₀ n₀ R) * A₀ * x₀ = B₀)

/-- The **pullback of an isotropic splitting by frames**: if `x* A x = B` and `x₀* A₀ x₀ = B₀`
for invertible `x` and `x₀`, the frames `x⁻¹ k`, `x⁻¹ l` and the core embedding `x⁻¹ ι x₀` split
`B` over `B₀`. -/
def pullback : IsotropicSplitting B B₀ p :=
  { k := (x : Matrix n n R)⁻¹ * D.k
    l := (x : Matrix n n R)⁻¹ * D.l
    ι := (x : Matrix n n R)⁻¹ * (D.ι * (x₀ : Matrix n₀ n₀ R))
    isHermitian := by
      rw [← hx, star_eq_conjTranspose]
      exact isHermitian_conjTranspose_mul_mul _ D.isHermitian
    isUnit_core := by
      rw [← hx₀]
      exact ((x₀.isUnit.star).mul D.isUnit_core).mul x₀.isUnit
    gram_kk := by rw [conjTranspose_inv_mul_mul_mul_inv_mul hx, D.gram_kk]
    gram_ll := by rw [conjTranspose_inv_mul_mul_mul_inv_mul hx, D.gram_ll]
    gram_lk := by rw [conjTranspose_inv_mul_mul_mul_inv_mul hx, D.gram_lk]
    gram_ιι := by
      rw [conjTranspose_inv_mul_mul_mul_inv_mul hx, conjTranspose_mul, ← hx₀, star_eq_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D.ιᴴ, ← Matrix.mul_assoc (D.ιᴴ * A), D.gram_ιι]
    gram_ιk := by
      rw [conjTranspose_inv_mul_mul_mul_inv_mul hx, conjTranspose_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Matrix.mul_assoc D.ιᴴ, D.gram_ιk, Matrix.mul_zero]
    gram_ιl := by
      rw [conjTranspose_inv_mul_mul_mul_inv_mul hx, conjTranspose_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Matrix.mul_assoc D.ιᴴ, D.gram_ιl, Matrix.mul_zero]
    card_eq := D.card_eq }

@[simp]
theorem pullback_k : (D.pullback hx hx₀).k = (x : Matrix n n R)⁻¹ * D.k :=
  (rfl)

@[simp]
theorem pullback_l : (D.pullback hx hx₀).l = (x : Matrix n n R)⁻¹ * D.l :=
  (rfl)

@[simp]
theorem pullback_ι :
    (D.pullback hx hx₀).ι = (x : Matrix n n R)⁻¹ * (D.ι * (x₀ : Matrix n₀ n₀ R)) :=
  (rfl)

/-- The **Levi elements of a pullback** are the conjugates of the Levi elements: for
`g₀' = x₀⁻¹ g₀ x₀`, the Levi element of `(a, g₀')` is `x⁻¹ m(a, g₀) x`. -/
theorem val_levi_pullback (a : GL p R) {g₀ : unitaryGroupOf A₀} {g₀' : unitaryGroupOf B₀}
    (hg₀ : ((g₀' : GL n₀ R) : Matrix n₀ n₀ R) =
      (x₀ : Matrix n₀ n₀ R)⁻¹ * ((g₀ : GL n₀ R) : Matrix n₀ n₀ R) * (x₀ : Matrix n₀ n₀ R)) :
    (((D.pullback hx hx₀).levi (a, g₀') : GL n R) : Matrix n n R) =
      (x : Matrix n n R)⁻¹ * ((D.levi (a, g₀) : GL n R) : Matrix n n R) * (x : Matrix n n R) := by
  have hdet : IsUnit (x : Matrix n n R).det := isUnits_det_units x
  have hdet₀ : IsUnit (x₀ : Matrix n₀ n₀ R).det := isUnits_det_units x₀
  refine (D.pullback hx hx₀).ext_mul ?_ ?_ ?_ <;>
    simp only [levi_mul_k, levi_mul_ι, levi_mul_l] <;>
    simp only [pullback_k, pullback_l, pullback_ι, hg₀, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hdet, mul_nonsing_inv_cancel_left _ _ hdet₀] <;>
    simp only [← Matrix.mul_assoc, levi_mul_k, levi_mul_ι, levi_mul_l]

/-- Change of frame commutes with bundled Levi elements, including the core frame change. -/
theorem levi_pullback (a : GL p R) (g₀ : unitaryGroupOf A₀) :
    (D.pullback hx hx₀).levi (a, unitaryGroupOf.frameEquiv hx₀ g₀) =
      unitaryGroupOf.frameEquiv hx (D.levi (a, g₀)) := by
  apply unitaryGroupOf.ext
  simp only [unitaryGroupOf.coe_frameEquiv, Units.val_mul, coe_units_inv]
  exact D.val_levi_pullback hx hx₀ a (by
    simp only [unitaryGroupOf.coe_frameEquiv, Units.val_mul, coe_units_inv])

variable [Invertible (2 : R)] {j : Rˣ} (hj : star (j : R) = -j)

/-- The **unipotent elements of a pullback** are the conjugates of the unipotent elements: the
unipotent element of `(x₀⁻¹ c, b)` is `x⁻¹ n(c, b) x`. -/
theorem val_unipotent_pullback (c : Matrix n₀ p R) (b : Matrix p p R) :
    (((D.pullback hx hx₀).unipotent hj ((x₀ : Matrix n₀ n₀ R)⁻¹ * c) b : GL n R) :
        Matrix n n R) =
      (x : Matrix n n R)⁻¹ * ((D.unipotent hj c b : GL n R) : Matrix n n R) *
        (x : Matrix n n R) := by
  subst hx₀
  have hdet : IsUnit (x : Matrix n n R).det := isUnits_det_units x
  -- `(x₀⁻¹)ᴴ = (x₀ᴴ)⁻¹` cancels against `x₀ᴴ` in the core form `x₀ᴴ A₀ x₀` of the pullback.
  have hdet₀ : IsUnit (x₀ : Matrix n₀ n₀ R).det := isUnits_det_units x₀
  have hdet₀' : IsUnit (x₀ : Matrix n₀ n₀ R)ᴴ.det := by
    simpa only [Units.coe_star, star_eq_conjTranspose] using isUnits_det_units (star x₀)
  refine (D.pullback (x₀ := x₀) hx rfl).ext_mul ?_ ?_ ?_ <;>
    simp only [unipotent_mul_k, unipotent_mul_ι, unipotent_mul_l] <;>
    simp only [pullback_k, pullback_l, pullback_ι, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_nonsing_inv, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hdet,
      mul_nonsing_inv_cancel_left _ _ hdet₀, nonsing_inv_mul_cancel_left _ _ hdet₀'] <;>
    simp only [← Matrix.mul_assoc, unipotent_mul_k, unipotent_mul_ι, unipotent_mul_l] <;>
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- Change of frame commutes with bundled unipotent elements when the core parameter is
changed by `x₀⁻¹`. -/
theorem unipotent_pullback (c : Matrix n₀ p R) (b : Matrix p p R) :
    (D.pullback hx hx₀).unipotent hj ((x₀ : Matrix n₀ n₀ R)⁻¹ * c) b =
      unitaryGroupOf.frameEquiv hx (D.unipotent hj c b) := by
  apply unitaryGroupOf.ext
  simpa only [unitaryGroupOf.coe_frameEquiv, Units.val_mul, coe_units_inv] using
    D.val_unipotent_pullback hx hx₀ hj c b

end Pullback

end IsotropicSplitting

end TauCeti
