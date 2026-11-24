/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import TauCeti.Algebra.Module.NatInt
public import Mathlib.RingTheory.NonUnitalSubring.Basic
public import TauCeti.RingTheory.WittVector.Big.Basic

import TauCeti.Algebra.Algebra.Unitization

/-!
# Big Witt vectors over nonunital commutative rings

For a nonunital commutative ring `R`, `NonUnitalBigWitt S R` is the kernel of the map
`W_S(ℤ ⊕ R) → W_S(ℤ)` induced by the canonical projection of the unitization. Its ring
operations are inherited from this kernel. Its coordinates lie in `R`, and every family
of such coordinates determines a unique nonunital Witt vector.

## References

* F. Wagner, *q-Witt vectors and q-Hodge complexes*, §2.6,
  <https://arxiv.org/abs/2410.23078v5>.
-/

public section

namespace TauCeti

open BigWitt

/-- Big Witt vectors over a nonunital commutative ring, defined as the kernel of the
projection from the Witt ring of its integral unitization. -/
noncomputable abbrev NonUnitalBigWitt (S : TruncationSet) (R : Type*)
    [NonUnitalCommRing R] :=
  ↥(NonUnitalSubring.comap (R := BigWitt S (Unitization ℤ R)) (S := BigWitt S ℤ)
    (BigWitt.map (R := Unitization ℤ R) (A := ℤ) S
      (Unitization.fstHom ℤ R).toRingHom).toNonUnitalRingHom ⊥)

namespace NonUnitalBigWitt

variable {S T : TruncationSet} {R : Type*} [NonUnitalCommRing R]

/-- The canonical inclusion in the Witt ring of the unitization. -/
noncomputable def toBigWitt : NonUnitalBigWitt S R →ₙ+* BigWitt S (Unitization ℤ R) :=
  NonUnitalSubringClass.subtype _

/-- The defining kernel equation. -/
@[simp]
theorem map_fst_toBigWitt (x : NonUnitalBigWitt S R) :
    BigWitt.map (R := Unitization ℤ R) (A := ℤ) S ↑(Unitization.fstHom ℤ R)
      (toBigWitt x) = 0 :=
  NonUnitalSubring.mem_bot.mp x.property

/-- The Witt coordinates of a nonunital Witt vector. -/
noncomputable def coeff (x : NonUnitalBigWitt S R) (n : S) : R :=
  ((toBigWitt x).coeff n).snd

private theorem fst_toBigWitt_coeff (x : NonUnitalBigWitt S R) (n : S) :
    ((toBigWitt x).coeff n).fst = 0 := by
  have h := congrArg (fun y : BigWitt S ℤ ↦ y.coeff n) (map_fst_toBigWitt x)
  rw [BigWitt.map_coeff, BigWitt.coeff_zero] at h
  exact h

/-- The coordinates of the kernel inclusion are obtained by including the coefficients
in the unitization. -/
@[simp]
theorem toBigWitt_coeff (x : NonUnitalBigWitt S R) (n : S) :
    (toBigWitt x).coeff n = (Unitization.inr (coeff x n) : Unitization ℤ R) := by
  apply Unitization.ext
  · exact fst_toBigWitt_coeff x n
  · rfl

/-- A family of coordinates in `R` determines a nonunital Witt vector. -/
noncomputable def mk (x : S → R) : NonUnitalBigWitt S R :=
  ⟨BigWitt.mk fun n ↦ (x n : Unitization ℤ R), by
    apply NonUnitalSubring.mem_bot.mpr
    -- Express kernel membership as the unital augmentation equation.
    change BigWitt.map (R := Unitization ℤ R) (A := ℤ) S
      (Unitization.fstHom ℤ R).toRingHom _ = 0
    apply BigWitt.ext
    funext n
    simp⟩

@[simp]
theorem coeff_mk (x : S → R) (n : S) : coeff (mk x) n = x n :=
  (rfl)

/-- Nonunital Witt vectors are determined by their coordinates. -/
@[ext]
theorem ext {x y : NonUnitalBigWitt S R} (h : ∀ n, coeff x n = coeff y n) : x = y := by
  apply Subtype.ext
  apply BigWitt.ext
  funext n
  -- Compare in the ambient Witt ring before extracting the nonunital coordinates.
  change (toBigWitt x).coeff n = (toBigWitt y).coeff n
  rw [toBigWitt_coeff, toBigWitt_coeff, h n]

@[simp]
theorem mk_coeff (x : NonUnitalBigWitt S R) : mk (coeff x) = x := by
  ext n
  rfl

/-- The coordinates extended by zero outside the truncation set. -/
noncomputable def coordinates (x : NonUnitalBigWitt S R) : ℕ → R :=
  BigWitt.coordinates (BigWitt.mk (coeff x))

@[simp]
theorem coordinates_coe (x : NonUnitalBigWitt S R) (n : S) :
    coordinates x n = coeff x n :=
  BigWitt.coordinates_coe _ n

open scoped Classical in
/-- The zero extension of the coordinates, evaluated at a natural number. -/
theorem coordinates_apply (x : NonUnitalBigWitt S R) (n : ℕ) :
    coordinates x n = if h : n ∈ S then coeff x ⟨n, h⟩ else 0 := by
  classical
  exact BigWitt.coordinates_apply (BigWitt.mk (coeff x)) n

private theorem coordinates_toBigWitt (x : NonUnitalBigWitt S R) :
    BigWitt.coordinates (toBigWitt x) =
      (Unitization.inrNonUnitalAlgHom ℤ R) ∘ coordinates x := by
  classical
  funext n
  simp only [BigWitt.coordinates_apply, coordinates, Function.comp_apply]
  split_ifs with hn
  · exact toBigWitt_coeff x ⟨n, hn⟩
  · rfl

private theorem inr_ghostPolynomial (x : NonUnitalBigWitt S R) (n : S) :
    (Unitization.inr (ghostPolynomial n (coordinates x)) : Unitization ℤ R) =
      BigWitt.ghostComponent n (toBigWitt x) := by
  change (Unitization.inrNonUnitalAlgHom ℤ R) (ghostPolynomial n (coordinates x)) = _
  rw [map_ghostPolynomial, BigWitt.ghostComponent_apply, coordinates_toBigWitt]

/-- A ghost component of a nonunital Witt vector, as a nonunital ring homomorphism. -/
noncomputable def ghostComponent (n : S) : NonUnitalBigWitt S R →ₙ+* R where
  toFun x := ghostPolynomial n (coordinates x)
  map_zero' := by
    apply Unitization.inr_injective (R := ℤ)
    rw [inr_ghostPolynomial, map_zero, map_zero, Unitization.inr_zero]
  map_add' x y := by
    apply Unitization.inr_injective (R := ℤ)
    rw [inr_ghostPolynomial, map_add, map_add, Unitization.inr_add,
      inr_ghostPolynomial, inr_ghostPolynomial]
  map_mul' x y := by
    apply Unitization.inr_injective (R := ℤ)
    rw [inr_ghostPolynomial, map_mul, map_mul, Unitization.inr_mul,
      inr_ghostPolynomial, inr_ghostPolynomial]

/-- The characteristic ghost-polynomial equation on nonunital coefficients. -/
theorem ghostComponent_apply (n : S) (x : NonUnitalBigWitt S R) :
    ghostComponent n x = ghostPolynomial n (coordinates x) :=
  (rfl)

/-- Ghost components commute with the canonical kernel inclusion. -/
@[simp]
theorem toBigWitt_ghostComponent (n : S) (x : NonUnitalBigWitt S R) :
    BigWitt.ghostComponent n (toBigWitt x) =
      (Unitization.inr (ghostComponent n x) : Unitization ℤ R) :=
  (inr_ghostPolynomial x n).symm

/-- Restriction to a smaller truncation set, inherited from the unital Witt ring. -/
noncomputable def restrict (h : T ≤ S) : NonUnitalBigWitt S R →ₙ+* NonUnitalBigWitt T R where
  toFun x := ⟨BigWitt.restrict h (toBigWitt x), by
    apply NonUnitalSubring.mem_bot.mpr
    -- Express kernel membership as the unital augmentation equation.
    change BigWitt.map (R := Unitization ℤ R) (A := ℤ) T
      (Unitization.fstHom ℤ R).toRingHom _ = 0
    apply BigWitt.ext
    funext n
    simp⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp]
theorem restrict_coeff (h : T ≤ S) (x : NonUnitalBigWitt S R) (n : T) :
    coeff (restrict h x) n = coeff x ⟨n, h n.property⟩ :=
  congrArg (fun a : Unitization ℤ R ↦ a.snd) (BigWitt.restrict_coeff h (toBigWitt x) n)

@[simp]
theorem restrict_refl : restrict (le_refl S) = NonUnitalRingHom.id (NonUnitalBigWitt S R) := by
  ext x n
  simp

@[simp]
theorem restrict_comp {U : TruncationSet} (h : T ≤ S) (k : U ≤ T) :
    (restrict k).comp (restrict h) = restrict (R := R) (k.trans h) := by
  ext x n
  simp

variable {A B : Type*} [NonUnitalCommRing A] [NonUnitalCommRing B]

private def coefficientAlgHom (f : R →ₙ+* A) : R →ₙₐ[ℤ] A :=
  { f with map_smul' := fun z x ↦ f.map_zsmul z x }

/-- Functoriality in the nonunital coefficient ring, obtained from functoriality of
unitization and of the unital Witt ring. -/
noncomputable def map (S : TruncationSet) (f : R →ₙ+* A) :
    NonUnitalBigWitt S R →ₙ+* NonUnitalBigWitt S A where
  toFun x := ⟨BigWitt.map (R := Unitization ℤ R) (A := Unitization ℤ A) S
      (Unitization.map (coefficientAlgHom f)).toRingHom (toBigWitt x), by
    apply NonUnitalSubring.mem_bot.mpr
    -- Express kernel membership as the unital augmentation equation.
    change BigWitt.map (R := Unitization ℤ A) (A := ℤ) S
      (Unitization.fstHom ℤ A).toRingHom _ = 0
    apply BigWitt.ext
    funext n
    simp⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp]
theorem map_coeff (f : R →ₙ+* A) (x : NonUnitalBigWitt S R) (n : S) :
    coeff (map S f x) n = f (coeff x n) := by
  -- Compute the coefficient of the inherited unitization map, then take its second component.
  change ((BigWitt.map (R := Unitization ℤ R) (A := Unitization ℤ A) S
      (Unitization.map (coefficientAlgHom f)).toRingHom
    (toBigWitt x)).coeff n).snd = _
  rw [BigWitt.map_coeff]
  change (Unitization.map (coefficientAlgHom f) ((toBigWitt x).coeff n)).snd = _
  rw [Unitization.snd_map]
  rfl

@[simp]
theorem map_id : map S (NonUnitalRingHom.id R) = NonUnitalRingHom.id (NonUnitalBigWitt S R) := by
  ext x n
  simp

@[simp]
theorem map_comp (f : R →ₙ+* A) (g : A →ₙ+* B) :
    map S (g.comp f) = (map S g).comp (map S f) := by
  ext x n
  simp

theorem restrict_map (h : T ≤ S) (f : R →ₙ+* A) :
    (restrict h).comp (map S f) = (map T f).comp (restrict h) := by
  ext x n
  simp

private theorem coordinates_map (f : R →ₙ+* A) (x : NonUnitalBigWitt S R) :
    coordinates (map S f x) = f ∘ coordinates x := by
  classical
  funext n
  simp only [coordinates_apply, Function.comp_apply]
  split_ifs <;> simp

/-- Ghost components are natural in the nonunital coefficient ring. -/
@[simp]
theorem ghostComponent_map (f : R →ₙ+* A) (x : NonUnitalBigWitt S R) (n : S) :
    ghostComponent n (map S f x) = f (ghostComponent n x) := by
  rw [ghostComponent_apply, ghostComponent_apply, map_ghostPolynomial, coordinates_map]

/-- Ghost components commute with restriction of truncation sets. -/
@[simp]
theorem ghostComponent_restrict (h : T ≤ S) (x : NonUnitalBigWitt S R) (n : T) :
    ghostComponent n (restrict h x) = ghostComponent ⟨n, h n.property⟩ x := by
  classical
  simp only [ghostComponent_apply]
  apply ghostPolynomial_congr
  intro d hd
  have hdT := T.mem_of_dvd n.property hd
  simp [coordinates_apply, hdT, h hdT]

/-- The full ghost map on nonunital Witt vectors. -/
noncomputable def ghostMap : NonUnitalBigWitt S R →ₙ+* (S → R) :=
  NonUnitalRingHom.pi ghostComponent

@[simp]
theorem ghostMap_apply (x : NonUnitalBigWitt S R) (n : S) :
    ghostMap x n = ghostComponent n x :=
  (rfl)

section Unital

variable {C : Type*} [CommRing C]

/-- On a unital ring, the canonical map from nonunital Witt vectors to the usual Witt ring
is induced by the unitization counit. -/
private noncomputable def toUnital : NonUnitalBigWitt S C →ₙ+* BigWitt S C :=
  (BigWitt.map (R := Unitization ℤ C) (A := C) S
    (Unitization.lift (NonUnitalAlgHom.id ℤ C)).toRingHom).toNonUnitalRingHom.comp
    toBigWitt

@[simp]
private theorem toUnital_coeff (x : NonUnitalBigWitt S C) (n : S) :
    (toUnital x).coeff n = coeff x n := by
  change (BigWitt.map (R := Unitization ℤ C) (A := C) S
    (Unitization.lift (NonUnitalAlgHom.id ℤ C)).toRingHom
    (toBigWitt x)).coeff n = _
  rw [BigWitt.map_coeff, toBigWitt_coeff]
  simp

/-- The nonunital kernel construction agrees with the usual Witt ring on unital rings. -/
noncomputable def unitalEquiv : NonUnitalBigWitt S C ≃+* BigWitt S C where
  toFun := toUnital
  invFun x := mk x.coeff
  left_inv x := by
    ext n
    simp
  right_inv x := by
    apply BigWitt.ext
    funext n
    simp
  map_mul' := map_mul toUnital
  map_add' := map_add toUnital

@[simp]
theorem unitalEquiv_coeff (x : NonUnitalBigWitt S C) (n : S) :
    (unitalEquiv x).coeff n = coeff x n :=
  toUnital_coeff x n

@[simp]
theorem unitalEquiv_symm_coeff (x : BigWitt S C) (n : S) :
    coeff (unitalEquiv.symm x) n = x.coeff n :=
  (rfl)

end Unital

end NonUnitalBigWitt

end TauCeti
