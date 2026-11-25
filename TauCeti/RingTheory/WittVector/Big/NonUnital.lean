/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.NonUnitalSubring.Basic
public import TauCeti.Algebra.Algebra.NonUnitalHom
public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.RingTheory.WittVector.Big.Basic

/-!
# Big Witt vectors over nonunital commutative rings

For a nonunital commutative ring `R`, `NonUnitalBigWittVector S R` is the kernel of the map
`W_S(ℤ ⊕ R) → W_S(ℤ)` induced by the canonical projection of the unitization. Its ring
operations are inherited from this kernel. Its coordinates lie in `R`, and every family
of such coordinates determines a unique nonunital Witt vector.

## Main definitions

* `NonUnitalBigWittVector`: the kernel of the big Witt map induced by the unitization projection.
* `NonUnitalBigWittVector.toBigWitt`: the inclusion into the big Witt ring of the unitization.
* `NonUnitalBigWittVector.coeff`: the coordinate of a nonunital Witt vector at a given index.
* `NonUnitalBigWittVector.mk`: the nonunital Witt vector with a prescribed family of coordinates.
* `NonUnitalBigWittVector.ghostComponent` and `NonUnitalBigWittVector.ghostMap`:
  the ghost homomorphisms.
* `NonUnitalBigWittVector.restrict`: restriction to a smaller truncation set.
* `NonUnitalBigWittVector.map`: functoriality in the nonunital coefficient ring.
* `NonUnitalBigWittVector.unitalEquiv`: agreement with `BigWittVector` on unital rings.

## Main results

* `NonUnitalBigWittVector.coeff_add`, `NonUnitalBigWittVector.coeff_mul`, and
  `NonUnitalBigWittVector.coeff_neg`: coordinate formulas for the ring operations.

## References

* F. Wagner, *q-Witt vectors and q-Hodge complexes*, §2.6,
  <https://arxiv.org/abs/2410.23078v5>.
-/

public section

namespace TauCeti

open BigWitt MvPolynomial

/-- Supplies the ambient ring structure for the `NonUnitalSubring.comap` defining
`NonUnitalBigWittVector`. The carrier `BigWittVector S (Unitization ℤ R)` uses the standalone
`Unitization.instZero` as a type parameter. The generic Witt ring instance uses the zero
projected from the coefficient ring, and typeclass search does not match the two in the
kernel declaration. This specialization registers the same ring structure on that carrier. -/
@[instance_reducible]
noncomputable instance BigWittVector.unitizationCommRing {S : TruncationSet} {R : Type*}
    [NonUnitalCommRing R] : CommRing (BigWittVector S (Unitization ℤ R)) :=
  BigWittVector.instCommRing (R := Unitization ℤ R)

/-- Big Witt vectors over a nonunital commutative ring, defined as the kernel of the
projection from the Witt ring of its integral unitization. -/
noncomputable abbrev NonUnitalBigWittVector (S : TruncationSet) (R : Type*)
    [NonUnitalCommRing R] :=
  ↥(NonUnitalSubring.comap (R := BigWittVector S (Unitization ℤ R)) (S := BigWittVector S ℤ)
    (BigWittVector.map (R := Unitization ℤ R) (R' := ℤ)
      (Unitization.fstHom ℤ R).toRingHom).toNonUnitalRingHom ⊥)

namespace NonUnitalBigWittVector

variable {S T : TruncationSet} {R : Type*} [NonUnitalCommRing R]

/-- The canonical inclusion in the Witt ring of the unitization. -/
noncomputable def toBigWitt : NonUnitalBigWittVector S R →ₙ+* BigWittVector S (Unitization ℤ R) :=
  NonUnitalSubringClass.subtype _

/-- The kernel inclusion is injective. -/
theorem toBigWitt_injective :
    Function.Injective
      (toBigWitt : NonUnitalBigWittVector S R → BigWittVector S (Unitization ℤ R)) :=
  Subtype.val_injective

/-- An ambient Witt vector comes from the nonunital ring exactly when its augmentation is zero. -/
theorem mem_range_toBigWitt (y : BigWittVector S (Unitization ℤ R)) :
    y ∈ (toBigWitt (S := S) (R := R)).range ↔
      BigWittVector.map (R := Unitization ℤ R) (R' := ℤ) ↑(Unitization.fstHom ℤ R) y = 0 := by
  rw [toBigWitt, NonUnitalSubring.range_subtype]
  exact NonUnitalSubring.mem_bot

/-- The defining kernel equation. -/
@[simp]
theorem map_fst_toBigWitt (x : NonUnitalBigWittVector S R) :
    BigWittVector.map (R := Unitization ℤ R) (R' := ℤ) ↑(Unitization.fstHom ℤ R)
      (toBigWitt x) = 0 :=
  NonUnitalSubring.mem_bot.mp x.property

/-- The Witt coordinates of a nonunital Witt vector. -/
noncomputable def coeff (x : NonUnitalBigWittVector S R) (n : S) : R :=
  ((toBigWitt x).coeff n).snd

private theorem fst_toBigWitt_coeff (x : NonUnitalBigWittVector S R) (n : S) :
    ((toBigWitt x).coeff n).fst = 0 := by
  have h := congrArg (fun y : BigWittVector S ℤ ↦ y.coeff n) (map_fst_toBigWitt x)
  rw [BigWittVector.coeff_map, BigWittVector.coeff_zero] at h
  exact h

/-- The coordinates of the kernel inclusion are obtained by including the coefficients
in the unitization. -/
@[simp]
theorem coeff_toBigWitt (x : NonUnitalBigWittVector S R) (n : S) :
    (toBigWitt x).coeff n = (Unitization.inr (coeff x n) : Unitization ℤ R) := by
  apply Unitization.ext
  · exact fst_toBigWitt_coeff x n
  · rfl

/-- A family of coordinates in `R` determines a nonunital Witt vector. -/
noncomputable def mk (x : S → R) : NonUnitalBigWittVector S R := by
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

/-- The vector constructed from a family has that family as its coordinates. -/
@[simp]
theorem coeff_mk (x : S → R) (n : S) : coeff (mk x) n = x n := by
  classical
  -- Expose the coordinate of the kernel inclusion before using the constructor equation.
  change ((BigWittVector.mk' _ : BigWittVector S (Unitization ℤ R)).coeff n).snd = _
  rw [BigWittVector.coeff_mk'_of_mem _ n.property]
  simp [n.property]

@[simp]
theorem coeff_zero (n : S) : coeff (0 : NonUnitalBigWittVector S R) n = 0 := by
  change ((0 : BigWittVector S (Unitization ℤ R)).coeff n).snd = 0
  rw [BigWittVector.coeff_zero (R := Unitization ℤ R)]
  rfl

/-- Nonunital Witt vectors are determined by their coordinates. -/
@[ext]
theorem ext {x y : NonUnitalBigWittVector S R} (h : ∀ n, coeff x n = coeff y n) : x = y := by
  apply Subtype.ext
  apply BigWittVector.ext
  intro n
  by_cases hn : n ∈ S
  · change (toBigWitt x).coeff n = (toBigWitt y).coeff n
    rw [coeff_toBigWitt x ⟨n, hn⟩, coeff_toBigWitt y ⟨n, hn⟩, h ⟨n, hn⟩]
  · exact (x.val.coeff_eq_zero_of_notMem n hn).trans
      (y.val.coeff_eq_zero_of_notMem n hn).symm

/-- Reconstructing a vector from its coordinates recovers the original vector. -/
@[simp]
theorem mk_coeff (x : NonUnitalBigWittVector S R) : mk (coeff x) = x := by
  ext n
  simp

/-- The coordinates extended by zero outside the truncation set. -/
noncomputable def coordinates (x : NonUnitalBigWittVector S R) : ℕ → R :=
  fun n ↦ ((toBigWitt x).coeff n).snd

@[simp]
theorem coordinates_coe (x : NonUnitalBigWittVector S R) (n : S) :
    coordinates x n = coeff x n :=
  (rfl)

open scoped Classical in
/-- The zero extension of the coordinates, evaluated at a natural number. -/
theorem coordinates_apply (x : NonUnitalBigWittVector S R) (n : ℕ) :
    coordinates x n = if h : n ∈ S then coeff x ⟨n, h⟩ else 0 := by
  classical
  by_cases hn : n ∈ S
  · simp [hn, coordinates, coeff]
  · simp [hn, coordinates, BigWittVector.coeff_eq_zero_of_notMem _ n hn]

private theorem coordinates_toBigWitt (x : NonUnitalBigWittVector S R) :
    (toBigWitt x).coeff =
      (Unitization.inrNonUnitalAlgHom ℤ R) ∘ coordinates x := by
  funext n
  by_cases hn : n ∈ S
  · exact coeff_toBigWitt x ⟨n, hn⟩
  · simp [coordinates, BigWittVector.coeff_eq_zero_of_notMem _ n hn]

private theorem coeff_toBigWitt_pair (x y : NonUnitalBigWittVector S R) :
    (fun ik : Fin 2 × ℕ ↦ (![toBigWitt x, toBigWitt y] ik.1).coeff ik.2) =
      fun ik ↦ (Unitization.inr (coordinates (![x, y] ik.1) ik.2) : Unitization ℤ R) := by
  funext ⟨i, k⟩
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨congrFun (coordinates_toBigWitt x) k, congrFun (coordinates_toBigWitt y) k⟩

/-- Extend the summands' coordinates by zero and include them in the integral unitization.
The coordinates of the sum are the second components of the addition structure polynomials
evaluated on those inputs. -/
theorem coeff_add (x y : NonUnitalBigWittVector S R) (n : S) :
    coeff (x + y) n = (eval₂ (Int.castRingHom (Unitization ℤ R)) (fun ik : Fin 2 × ℕ ↦
      (Unitization.inr (coordinates (![x, y] ik.1) ik.2) : Unitization ℤ R))
      (wittStructure (X 0 + X 1) n)).snd := by
  rw [coeff, map_add, BigWittVector.coeff_add_of_mem (R := Unitization ℤ R) _ _ n.property,
    coeff_toBigWitt_pair]
  simp only [aeval_def, algebraMap_int_eq]

/-- Extend the factors' coordinates by zero and include them in the integral unitization.
The coordinates of the product are the second components of the multiplication structure
polynomials evaluated on those inputs. -/
theorem coeff_mul (x y : NonUnitalBigWittVector S R) (n : S) :
    coeff (x * y) n = (eval₂ (Int.castRingHom (Unitization ℤ R)) (fun ik : Fin 2 × ℕ ↦
      (Unitization.inr (coordinates (![x, y] ik.1) ik.2) : Unitization ℤ R))
      (wittStructure (X 0 * X 1) n)).snd := by
  rw [coeff, map_mul, BigWittVector.coeff_mul_of_mem (R := Unitization ℤ R) _ _ n.property,
    coeff_toBigWitt_pair]
  simp only [aeval_def, algebraMap_int_eq]

/-- Extend the vector's coordinates by zero and include them in the integral unitization.
The coordinates of the negative are the second components of the negation structure
polynomials evaluated on those inputs. -/
theorem coeff_neg (x : NonUnitalBigWittVector S R) (n : S) :
    coeff (-x) n = (eval₂ (Int.castRingHom (Unitization ℤ R)) (fun ik : Fin 1 × ℕ ↦
      (Unitization.inr (coordinates x ik.2) : Unitization ℤ R))
      (wittStructure (-X 0) n)).snd := by
  rw [coeff, map_neg, BigWittVector.coeff_neg_of_mem (R := Unitization ℤ R) _ n.property]
  have h : (fun ik : Fin 1 × ℕ ↦ (![toBigWitt x] ik.1).coeff ik.2) =
      fun ik ↦ (Unitization.inr (coordinates x ik.2) : Unitization ℤ R) := by
    funext ⟨i, k⟩
    rw [Subsingleton.elim i 0]
    exact congrFun (coordinates_toBigWitt x) k
  rw [h]
  simp only [aeval_def, algebraMap_int_eq]

private noncomputable def unitalGhostComponent (n : S) :
    BigWittVector S (Unitization ℤ R) →+* Unitization ℤ R :=
  (Pi.evalRingHom _ n).comp (BigWittVector.ghostMap (R := Unitization ℤ R))

private theorem inr_ghostPolynomial (x : NonUnitalBigWittVector S R) (n : S) :
    (Unitization.inr (ghostPolynomial n (coordinates x)) : Unitization ℤ R) =
      unitalGhostComponent n (toBigWitt x) := by
  -- Use the bundled form of the inclusion to apply polynomial naturality.
  change (Unitization.inrNonUnitalAlgHom ℤ R) (ghostPolynomial n (coordinates x)) = _
  rw [map_ghostPolynomial]
  simp only [unitalGhostComponent, RingHom.comp_apply, Pi.evalRingHom_apply,
    BigWittVector.ghostMap_apply]
  rw [coordinates_toBigWitt]

/-- A ghost component of a nonunital Witt vector, as a nonunital ring homomorphism. -/
noncomputable def ghostComponent (n : S) : NonUnitalBigWittVector S R →ₙ+* R where
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
theorem ghostComponent_apply (n : S) (x : NonUnitalBigWittVector S R) :
    ghostComponent n x = ghostPolynomial n (coordinates x) :=
  (rfl)

/-- Ghost components commute with the canonical kernel inclusion. -/
@[simp]
theorem ghostMap_toBigWitt (n : S) (x : NonUnitalBigWittVector S R) :
    BigWittVector.ghostMap (toBigWitt x) n =
      (Unitization.inr (ghostComponent n x) : Unitization ℤ R) :=
  (inr_ghostPolynomial x n).symm

/-- Restriction to a smaller truncation set, inherited from the unital Witt ring. -/
noncomputable def restrict (h : T ≤ S) :
    NonUnitalBigWittVector S R →ₙ+* NonUnitalBigWittVector T R :=
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

/-- The kernel inclusion commutes with restriction of truncation sets. -/
@[simp]
theorem toBigWitt_restrict (h : T ≤ S) (x : NonUnitalBigWittVector S R) :
    toBigWitt (restrict h x) = BigWittVector.restrict (R := Unitization ℤ R) h (toBigWitt x) :=
  (rfl)

/-- A coordinate of a restriction is the original coordinate at the included index. -/
@[simp]
theorem coeff_restrict (h : T ≤ S) (x : NonUnitalBigWittVector S R) (n : T) :
    coeff (restrict h x) n = coeff x ⟨n, h n.property⟩ :=
  congrArg (fun a : Unitization ℤ R ↦ a.snd)
    (BigWittVector.coeff_restrict_of_mem (R := Unitization ℤ R) h (toBigWitt x) n.property)

@[simp]
theorem restrict_self :
    restrict (le_refl S) = NonUnitalRingHom.id (NonUnitalBigWittVector S R) := by
  ext x n
  simp

@[simp]
theorem restrict_comp_restrict {U : TruncationSet} (hUT : U ≤ T) (hTS : T ≤ S) :
    (restrict hUT).comp (restrict hTS) = restrict (R := R) (hUT.trans hTS) := by
  ext x n
  simp

variable {A B : Type*} [NonUnitalCommRing A] [NonUnitalCommRing B]

/-- Functoriality in the nonunital coefficient ring, obtained from functoriality of
unitization and of the unital Witt ring. -/
noncomputable def map (f : R →ₙ+* A) :
    NonUnitalBigWittVector S R →ₙ+* NonUnitalBigWittVector S A :=
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

/-- The kernel inclusion carries a coefficient map to the map induced by unitization. -/
@[simp]
theorem toBigWitt_map (f : R →ₙ+* A) (x : NonUnitalBigWittVector S R) :
    toBigWitt (map f x) = BigWittVector.map
      (R := Unitization ℤ R) (R' := Unitization ℤ A)
      (Unitization.map f.toIntNonUnitalAlgHom).toRingHom (toBigWitt x) :=
  (rfl)

/-- A coefficient map applies the underlying nonunital homomorphism to each coordinate. -/
@[simp]
theorem coeff_map (f : R →ₙ+* A) (x : NonUnitalBigWittVector S R) (n : S) :
    coeff (map f x) n = f (coeff x n) := by
  simp only [coeff, toBigWitt_map, BigWittVector.coeff_map, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,
    Unitization.snd_map, NonUnitalRingHom.toIntNonUnitalAlgHom_apply]

@[simp]
theorem map_id :
    map (NonUnitalRingHom.id R) = NonUnitalRingHom.id (NonUnitalBigWittVector S R) := by
  ext x n
  simp

@[simp]
theorem map_comp (f : R →ₙ+* A) (g : A →ₙ+* B) :
    map (S := S) (g.comp f) = (map g).comp (map f) := by
  ext x n
  simp

/-- An injective coefficient map induces an injective map of nonunital Witt vectors. -/
theorem map_injective (f : R →ₙ+* A) (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalBigWittVector S R → NonUnitalBigWittVector S A) := by
  intro x y h
  apply ext
  intro n
  exact hf (by simpa using congrArg (coeff · n) h)

/-- A surjective coefficient map induces a surjective map of nonunital Witt vectors. -/
theorem map_surjective (f : R →ₙ+* A) (hf : Function.Surjective f) :
    Function.Surjective (map f : NonUnitalBigWittVector S R → NonUnitalBigWittVector S A) := by
  intro y
  choose x hx using fun n : S ↦ hf (coeff y n)
  refine ⟨mk x, ext fun n ↦ ?_⟩
  simpa only [coeff_map, coeff_mk] using hx n

/-- Restriction is natural in the nonunital coefficient ring. -/
theorem map_comp_restrict (h : T ≤ S) (f : R →ₙ+* A) :
    (map f).comp (restrict h) = (restrict h).comp (map f) := by
  ext x n
  simp

/-- Mapping coefficients acts pointwise on the coordinate function extended by zero. -/
@[simp]
theorem coordinates_map (f : R →ₙ+* A) (x : NonUnitalBigWittVector S R) :
    coordinates (map f x) = f ∘ coordinates x := by
  classical
  funext n
  simp only [coordinates_apply, Function.comp_apply]
  split_ifs <;> simp

/-- Ghost components are natural in the nonunital coefficient ring. -/
@[simp]
theorem ghostComponent_map (f : R →ₙ+* A) (x : NonUnitalBigWittVector S R) (n : S) :
    ghostComponent n (map f x) = f (ghostComponent n x) := by
  rw [ghostComponent_apply, ghostComponent_apply, map_ghostPolynomial, coordinates_map]

/-- Ghost components commute with restriction of truncation sets. -/
@[simp]
theorem ghostComponent_restrict (h : T ≤ S) (x : NonUnitalBigWittVector S R) (n : T) :
    ghostComponent n (restrict h x) = ghostComponent ⟨n, h n.property⟩ x := by
  classical
  simp only [ghostComponent_apply]
  apply ghostPolynomial_congr
  intro d hd
  have hdT := T.mem_of_dvd n.property hd
  simp [coordinates_apply, hdT, h hdT]

/-- The full ghost map on nonunital Witt vectors. -/
noncomputable def ghostMap : NonUnitalBigWittVector S R →ₙ+* (S → R) :=
  NonUnitalRingHom.pi ghostComponent

@[simp]
theorem ghostMap_apply (x : NonUnitalBigWittVector S R) (n : S) :
    ghostMap x n = ghostComponent n x :=
  (rfl)

section Unital

variable {C : Type*} [CommRing C]

/-- On a unital ring, the canonical map from nonunital Witt vectors to the usual Witt ring
is induced by the unitization counit. -/
private noncomputable def toUnital : NonUnitalBigWittVector S C →ₙ+* BigWittVector S C :=
  (BigWittVector.map (R := Unitization ℤ C) (R' := C)
    (Unitization.lift (NonUnitalAlgHom.id ℤ C)).toRingHom).toNonUnitalRingHom.comp
    toBigWitt

@[simp]
private theorem coeff_toUnital (x : NonUnitalBigWittVector S C) (n : S) :
    (toUnital x).coeff n = coeff x n := by
  rw [toUnital, NonUnitalRingHom.comp_apply]
  -- The underlying nonunital ring homomorphism has the same application as the ring map.
  change (BigWittVector.map (R := Unitization ℤ C) (R' := C)
    (Unitization.lift (NonUnitalAlgHom.id ℤ C)).toRingHom
    (toBigWitt x)).coeff n = _
  rw [BigWittVector.coeff_map, coeff_toBigWitt]
  simp

/-- The nonunital kernel construction agrees with the usual Witt ring on unital rings. -/
noncomputable def unitalEquiv : NonUnitalBigWittVector S C ≃+* BigWittVector S C where
  toFun := toUnital
  invFun x := mk (fun n ↦ x.coeff n)
  left_inv x := by
    ext n
    simp
  right_inv x := by
    apply BigWittVector.ext
    intro n
    by_cases hn : n ∈ S
    · simpa [hn] using coeff_toUnital (mk (fun n ↦ x.coeff n)) ⟨n, hn⟩
    · simp [BigWittVector.coeff_eq_zero_of_notMem _ n hn]
  map_mul' := map_mul toUnital
  map_add' := map_add toUnital

/-- The comparison with unital Witt vectors preserves coordinates. -/
@[simp]
theorem coeff_unitalEquiv (x : NonUnitalBigWittVector S C) (n : S) :
    (unitalEquiv x).coeff n = coeff x n :=
  coeff_toUnital x n

/-- The inverse comparison with unital Witt vectors preserves coordinates. -/
@[simp]
theorem coeff_unitalEquiv_symm (x : BigWittVector S C) (n : S) :
    coeff (unitalEquiv.symm x) n = x.coeff n :=
  coeff_mk _ n

/-- The comparison with unital Witt vectors commutes with coefficient ring maps. -/
@[simp]
theorem unitalEquiv_map {D : Type*} [CommRing D] (f : C →+* D) (x : NonUnitalBigWittVector S C) :
    unitalEquiv (map f.toNonUnitalRingHom x) = BigWittVector.map f (unitalEquiv x) := by
  apply unitalEquiv.symm.injective
  apply ext
  intro n
  simp
  -- Forgetting the unit leaves the underlying coefficient function unchanged.
  rfl

/-- The comparison with unital Witt vectors commutes with restriction. -/
@[simp]
theorem unitalEquiv_restrict (h : T ≤ S) (x : NonUnitalBigWittVector S C) :
    unitalEquiv (restrict h x) = BigWittVector.restrict h (unitalEquiv x) := by
  apply unitalEquiv.symm.injective
  apply ext
  intro n
  simp only [RingEquiv.symm_apply_apply, coeff_restrict, coeff_unitalEquiv_symm, SetLike.coe_mem,
    BigWittVector.coeff_restrict_of_mem]
  exact (coeff_unitalEquiv x ⟨n, h n.property⟩).symm

/-- The comparison with unital Witt vectors preserves the ghost map. -/
@[simp]
theorem ghostMap_unitalEquiv (x : NonUnitalBigWittVector S C) :
    BigWittVector.ghostMap (unitalEquiv x) = ghostMap x := by
  funext n
  rw [BigWittVector.ghostMap_apply, ghostMap_apply, ghostComponent_apply]
  apply ghostPolynomial_congr
  intro d hd
  have hdS := S.mem_of_dvd n.property hd
  rw [coordinates_apply, dite_eq_left hdS]
  exact coeff_unitalEquiv x ⟨d, hdS⟩

end Unital

end NonUnitalBigWittVector

end TauCeti
