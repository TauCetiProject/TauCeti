/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.NonUnitalSubring.Basic
public import TauCeti.RingTheory.WittVector.Big.Basic

import TauCeti.Algebra.Algebra.NonUnitalHom
import TauCeti.Algebra.Algebra.Unitization

/-!
# Big Witt vectors over nonunital commutative rings

For a nonunital commutative ring `R`, `NonUnitalBigWitt S R` is the kernel of the map
`W_S(ℤ ⊕ R) → W_S(ℤ)` induced by the canonical projection of the unitization. Its ring
operations are inherited from this kernel. Its coordinates lie in `R`, and every family
of such coordinates determines a unique nonunital Witt vector.

## Main definitions

* `NonUnitalBigWitt.ghostComponent` and `NonUnitalBigWitt.ghostMap`: the ghost homomorphisms.
* `NonUnitalBigWitt.restrict`: restriction to a smaller truncation set.
* `NonUnitalBigWitt.map`: functoriality in the nonunital coefficient ring.
* `NonUnitalBigWitt.unitalEquiv`: agreement with `BigWittVector` on unital rings.

## References

* F. Wagner, *q-Witt vectors and q-Hodge complexes*, §2.6,
  <https://arxiv.org/abs/2410.23078v5>.
-/

public section

namespace TauCeti

open BigWitt

/-- The Witt ring of a unitization, using its standalone zero instance in the carrier. -/
@[instance_reducible]
noncomputable instance BigWittVector.unitizationCommRing {S : TruncationSet} {R : Type*}
    [NonUnitalCommRing R] : CommRing (BigWittVector S (Unitization ℤ R)) :=
  BigWittVector.instCommRing (R := Unitization ℤ R)

/-- Big Witt vectors over a nonunital commutative ring, defined as the kernel of the
projection from the Witt ring of its integral unitization. -/
noncomputable abbrev NonUnitalBigWitt (S : TruncationSet) (R : Type*)
    [NonUnitalCommRing R] :=
  ↥(NonUnitalSubring.comap (R := BigWittVector S (Unitization ℤ R)) (S := BigWittVector S ℤ)
    (BigWittVector.map (R := Unitization ℤ R) (R' := ℤ)
      (Unitization.fstHom ℤ R).toRingHom).toNonUnitalRingHom ⊥)

namespace NonUnitalBigWitt

variable {S T : TruncationSet} {R : Type*} [NonUnitalCommRing R]

/-- The canonical inclusion in the Witt ring of the unitization. -/
noncomputable def toBigWitt : NonUnitalBigWitt S R →ₙ+* BigWittVector S (Unitization ℤ R) :=
  NonUnitalSubringClass.subtype _

/-- The defining kernel equation. -/
@[simp]
theorem map_fst_toBigWitt (x : NonUnitalBigWitt S R) :
    BigWittVector.map (R := Unitization ℤ R) (R' := ℤ) ↑(Unitization.fstHom ℤ R)
      (toBigWitt x) = 0 :=
  NonUnitalSubring.mem_bot.mp x.property

/-- The Witt coordinates of a nonunital Witt vector. -/
noncomputable def coeff (x : NonUnitalBigWitt S R) (n : S) : R :=
  ((toBigWitt x).coeff n).snd

private theorem fst_toBigWitt_coeff (x : NonUnitalBigWitt S R) (n : S) :
    ((toBigWitt x).coeff n).fst = 0 := by
  have h := congrArg (fun y : BigWittVector S ℤ ↦ y.coeff n) (map_fst_toBigWitt x)
  rw [BigWittVector.coeff_map, BigWittVector.coeff_zero] at h
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
noncomputable def mk (x : S → R) : NonUnitalBigWitt S R := by
  classical
  refine ⟨BigWittVector.mk' (fun n ↦ if h : n ∈ S then
    (Unitization.inr (x ⟨n, h⟩) : Unitization ℤ R) else 0), ?_⟩
  apply NonUnitalSubring.mem_bot.mpr
  change BigWittVector.map (R := Unitization ℤ R) (R' := ℤ)
    (Unitization.fstHom ℤ R).toRingHom _ = 0
  apply BigWittVector.ext
  intro n
  by_cases hn : n ∈ S
  · simp [hn]
  · simp [BigWittVector.coeff_eq_zero_of_notMem _ n hn]

@[simp]
theorem coeff_mk (x : S → R) (n : S) : coeff (mk x) n = x n := by
  classical
  -- Expose the coordinate of the kernel inclusion before using the constructor equation.
  change ((BigWittVector.mk' _ : BigWittVector S (Unitization ℤ R)).coeff n).snd = _
  rw [BigWittVector.coeff_mk'_of_mem _ n.property]
  simp [n.property]

@[simp]
theorem coeff_zero (n : S) : coeff (0 : NonUnitalBigWitt S R) n = 0 := by
  change ((0 : BigWittVector S (Unitization ℤ R)).coeff n).snd = 0
  rw [BigWittVector.coeff_zero (R := Unitization ℤ R)]
  rfl

/-- Nonunital Witt vectors are determined by their coordinates. -/
@[ext]
theorem ext {x y : NonUnitalBigWitt S R} (h : ∀ n, coeff x n = coeff y n) : x = y := by
  apply Subtype.ext
  apply BigWittVector.ext
  intro n
  by_cases hn : n ∈ S
  · change (toBigWitt x).coeff n = (toBigWitt y).coeff n
    rw [toBigWitt_coeff x ⟨n, hn⟩, toBigWitt_coeff y ⟨n, hn⟩, h ⟨n, hn⟩]
  · exact (x.val.coeff_eq_zero_of_notMem n hn).trans
      (y.val.coeff_eq_zero_of_notMem n hn).symm

@[simp]
theorem mk_coeff (x : NonUnitalBigWitt S R) : mk (coeff x) = x := by
  ext n
  simp

/-- The coordinates extended by zero outside the truncation set. -/
noncomputable def coordinates (x : NonUnitalBigWitt S R) : ℕ → R :=
  fun n ↦ ((toBigWitt x).coeff n).snd

@[simp]
theorem coordinates_coe (x : NonUnitalBigWitt S R) (n : S) :
    coordinates x n = coeff x n :=
  (rfl)

open scoped Classical in
/-- The zero extension of the coordinates, evaluated at a natural number. -/
theorem coordinates_apply (x : NonUnitalBigWitt S R) (n : ℕ) :
    coordinates x n = if h : n ∈ S then coeff x ⟨n, h⟩ else 0 := by
  classical
  by_cases hn : n ∈ S
  · simp [hn, coordinates, coeff]
  · simp [hn, coordinates, BigWittVector.coeff_eq_zero_of_notMem _ n hn]

private theorem coordinates_toBigWitt (x : NonUnitalBigWitt S R) :
    (toBigWitt x).coeff =
      (Unitization.inrNonUnitalAlgHom ℤ R) ∘ coordinates x := by
  funext n
  by_cases hn : n ∈ S
  · exact toBigWitt_coeff x ⟨n, hn⟩
  · simp [coordinates, BigWittVector.coeff_eq_zero_of_notMem _ n hn]

private noncomputable def unitalGhostComponent (n : S) :
    BigWittVector S (Unitization ℤ R) →+* Unitization ℤ R :=
  (Pi.evalRingHom _ n).comp (BigWittVector.ghostMap (R := Unitization ℤ R))

private theorem inr_ghostPolynomial (x : NonUnitalBigWitt S R) (n : S) :
    (Unitization.inr (ghostPolynomial n (coordinates x)) : Unitization ℤ R) =
      unitalGhostComponent n (toBigWitt x) := by
  change (Unitization.inrNonUnitalAlgHom ℤ R) (ghostPolynomial n (coordinates x)) = _
  rw [map_ghostPolynomial]
  simp only [unitalGhostComponent, RingHom.comp_apply, Pi.evalRingHom_apply,
    BigWittVector.ghostMap_apply]
  rw [coordinates_toBigWitt]

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
theorem ghostComponent_toBigWitt (n : S) (x : NonUnitalBigWitt S R) :
    BigWittVector.ghostMap (toBigWitt x) n =
      (Unitization.inr (ghostComponent n x) : Unitization ℤ R) :=
  (inr_ghostPolynomial x n).symm

/-- Restriction to a smaller truncation set, inherited from the unital Witt ring. -/
noncomputable def restrict (h : T ≤ S) : NonUnitalBigWitt S R →ₙ+* NonUnitalBigWitt T R :=
  NonUnitalRingHom.codRestrict
    ((BigWittVector.restrict (R := Unitization ℤ R) h).toNonUnitalRingHom.comp toBigWitt) _
    fun x ↦ by
      apply NonUnitalSubring.mem_bot.mpr
      -- Express kernel membership as the unital augmentation equation.
      change BigWittVector.map (R := Unitization ℤ R) (R' := ℤ)
        (Unitization.fstHom ℤ R).toRingHom (BigWittVector.restrict h (toBigWitt x)) = 0
      rw [← RingHom.comp_apply, BigWittVector.map_comp_restrict, RingHom.comp_apply]
      -- Match the algebra-hom coercion used in the public kernel equation.
      change BigWittVector.restrict h
        (BigWittVector.map (R := Unitization ℤ R) (R' := ℤ)
          ↑(Unitization.fstHom ℤ R) (toBigWitt x)) = 0
      rw [map_fst_toBigWitt, map_zero]

@[simp]
theorem restrict_coeff (h : T ≤ S) (x : NonUnitalBigWitt S R) (n : T) :
    coeff (restrict h x) n = coeff x ⟨n, h n.property⟩ :=
  congrArg (fun a : Unitization ℤ R ↦ a.snd)
    (BigWittVector.coeff_restrict_of_mem (R := Unitization ℤ R) h (toBigWitt x) n.property)

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

/-- Functoriality in the nonunital coefficient ring, obtained from functoriality of
unitization and of the unital Witt ring. -/
noncomputable def map (S : TruncationSet) (f : R →ₙ+* A) :
    NonUnitalBigWitt S R →ₙ+* NonUnitalBigWitt S A :=
  NonUnitalRingHom.codRestrict
    ((BigWittVector.map (R := Unitization ℤ R) (R' := Unitization ℤ A)
      (Unitization.map f.toIntNonUnitalAlgHom).toRingHom).toNonUnitalRingHom.comp toBigWitt) _
    fun x ↦ by
      apply NonUnitalSubring.mem_bot.mpr
      -- Express kernel membership as the unital augmentation equation.
      change BigWittVector.map (R := Unitization ℤ A) (R' := ℤ)
        (Unitization.fstHom ℤ A).toRingHom
          (BigWittVector.map (R := Unitization ℤ R) (R' := Unitization ℤ A)
            (Unitization.map f.toIntNonUnitalAlgHom).toRingHom (toBigWitt x)) = 0
      apply BigWittVector.ext
      intro n
      have hx := congrArg (fun y : BigWittVector S ℤ ↦ y.coeff n)
        (map_fst_toBigWitt x)
      simpa only [BigWittVector.coeff_map, BigWittVector.coeff_zero,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Unitization.fstHom_apply,
        Unitization.fst_map] using hx

@[simp]
theorem map_coeff (f : R →ₙ+* A) (x : NonUnitalBigWitt S R) (n : S) :
    coeff (map S f x) n = f (coeff x n) := by
  -- Compute the coefficient of the inherited unitization map, then take its second component.
  change ((BigWittVector.map (R := Unitization ℤ R) (R' := Unitization ℤ A)
      (Unitization.map f.toIntNonUnitalAlgHom).toRingHom
    (toBigWitt x)).coeff n).snd = _
  rw [BigWittVector.coeff_map]
  -- Remove the ring-homomorphism wrapper on the unitization algebra homomorphism.
  change (Unitization.map f.toIntNonUnitalAlgHom ((toBigWitt x).coeff n)).snd = _
  rw [Unitization.snd_map, NonUnitalRingHom.toIntNonUnitalAlgHom_apply, coeff]

@[simp]
theorem map_id : map S (NonUnitalRingHom.id R) = NonUnitalRingHom.id (NonUnitalBigWitt S R) := by
  ext x n
  simp

@[simp]
theorem map_comp (f : R →ₙ+* A) (g : A →ₙ+* B) :
    map S (g.comp f) = (map S g).comp (map S f) := by
  ext x n
  simp

theorem restrict_comp_map (h : T ≤ S) (f : R →ₙ+* A) :
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
private noncomputable def toUnital : NonUnitalBigWitt S C →ₙ+* BigWittVector S C :=
  (BigWittVector.map (R := Unitization ℤ C) (R' := C)
    (Unitization.lift (NonUnitalAlgHom.id ℤ C)).toRingHom).toNonUnitalRingHom.comp
    toBigWitt

@[simp]
private theorem toUnital_coeff (x : NonUnitalBigWitt S C) (n : S) :
    (toUnital x).coeff n = coeff x n := by
  rw [toUnital, NonUnitalRingHom.comp_apply]
  -- The underlying nonunital ring homomorphism has the same application as the ring map.
  change (BigWittVector.map (R := Unitization ℤ C) (R' := C)
    (Unitization.lift (NonUnitalAlgHom.id ℤ C)).toRingHom
    (toBigWitt x)).coeff n = _
  rw [BigWittVector.coeff_map, toBigWitt_coeff]
  simp

/-- The nonunital kernel construction agrees with the usual Witt ring on unital rings. -/
noncomputable def unitalEquiv : NonUnitalBigWitt S C ≃+* BigWittVector S C where
  toFun := toUnital
  invFun x := mk (fun n ↦ x.coeff n)
  left_inv x := by
    ext n
    simp
  right_inv x := by
    apply BigWittVector.ext
    intro n
    by_cases hn : n ∈ S
    · simpa [hn] using toUnital_coeff (mk (fun n ↦ x.coeff n)) ⟨n, hn⟩
    · simp [BigWittVector.coeff_eq_zero_of_notMem _ n hn]
  map_mul' := map_mul toUnital
  map_add' := map_add toUnital

@[simp]
theorem unitalEquiv_coeff (x : NonUnitalBigWitt S C) (n : S) :
    (unitalEquiv x).coeff n = coeff x n :=
  toUnital_coeff x n

@[simp]
theorem unitalEquiv_symm_coeff (x : BigWittVector S C) (n : S) :
    coeff (unitalEquiv.symm x) n = x.coeff n :=
  coeff_mk _ n

end Unital

end NonUnitalBigWitt

end TauCeti
