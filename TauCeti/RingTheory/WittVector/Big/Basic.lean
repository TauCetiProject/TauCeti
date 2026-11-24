/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Pi
public import TauCeti.RingTheory.WittVector.Big.Ghost

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Counit
import Mathlib.RingTheory.Ideal.Quotient.Defs
import TauCeti.RingTheory.MvPolynomial.Expand

/-!
# Big Witt rings

The integral operation polynomials are obtained by Dwork's criterion over a torsion-free
polynomial ring. Ring identities are checked there by ghosts and then specialized.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Proposition 1.2,
  <https://arxiv.org/abs/1006.3125v3>.
-/

public section

namespace TauCeti

/-- Big Witt vectors indexed by the truncation set `S`, with coefficients in `R`. -/
@[ext]
structure BigWitt (S : BigWitt.TruncationSet) (R : Type*) where
  /-- The Witt coordinates. -/
  coeff : S → R

namespace BigWitt

open _root_.MvPolynomial

variable {S T U : TruncationSet} {R A B : Type*}

@[simp]
theorem coeff_mk (x : S → R) (n : S) : (mk x).coeff n = x n := by rfl

@[simp]
theorem mk_coeff (x : BigWitt S R) : mk x.coeff = x := by rfl

section
variable [Zero R]

/-- Extend the coordinates by zero outside their truncation set. -/
noncomputable def coordinates (x : BigWitt S R) (n : ℕ) : R :=
  by
    classical
    exact if h : n ∈ S then x.coeff ⟨n, h⟩ else 0

open scoped Classical in
theorem coordinates_apply (x : BigWitt S R) (n : ℕ) :
    coordinates x n = if h : n ∈ S then x.coeff ⟨n, h⟩ else 0 := by
  classical
  rfl

@[simp]
theorem coordinates_coe (x : BigWitt S R) (n : S) : coordinates x n = x.coeff n := by
  classical
  simp [coordinates]

end

section
variable [CommRing R] [CommRing A] [CommRing B]

/-- The ghost component before bundling its ring map. -/
private noncomputable def ghost (x : BigWitt S R) (n : S) : R :=
  ghostPolynomial n (coordinates x)

/-- Coefficientwise transport, before bundling its ring map. -/
private def mapData (f : R →+* A) (x : BigWitt S R) : BigWitt S A :=
  mk fun n ↦ f (x.coeff n)

private theorem coordinates_mapData (f : R →+* A) (x : BigWitt S R) :
    coordinates (mapData f x) = f ∘ coordinates x := by
  classical
  funext n
  by_cases h : n ∈ S <;> simp [coordinates, mapData, h]

private theorem ghost_mapData (f : R →+* A) (x : BigWitt S R) (n : S) :
    ghost (mapData f x) n = f (ghost x n) := by
  rw [ghost, coordinates_mapData, ← map_ghostPolynomial]
  rfl

/-- Ghosts determine a vector when multiplication by each index is injective. -/
private theorem ghost_injective (hR : ∀ n ∈ S, Function.Injective (n • · : R → R)) :
    Function.Injective (ghost : BigWitt S R → S → R) := by
  intro x y h
  apply BigWitt.ext
  funext n
  have he := eqOn_of_ghostPolynomial_eq S hR (x := coordinates x) (y := coordinates y)
    (fun n hn ↦ congrFun h ⟨n, hn⟩)
  simpa using he n.property

private theorem polynomial_ghost_injective {ι : Type*} :
    Function.Injective (ghost : BigWitt S (MvPolynomial ι ℤ) → S → MvPolynomial ι ℤ) :=
  ghost_injective fun n hn ↦ by
    exact nsmul_right_injective (S.ne_zero_of_mem hn)

/-- The universal polynomial giving an operation on ghosts has integral Witt coordinates. -/
private theorem exists_operation (Φ : MvPolynomial Bool ℤ) :
    ∃ z : ℕ → MvPolynomial (Bool × S) ℤ, ∀ n ∈ S,
      ghostPolynomial n z =
        eval₂Hom (Int.castRingHom _) (fun i ↦
          ghostPolynomial n (coordinates (mk fun d : S ↦ X (i, d)))) Φ := by
  let P := MvPolynomial (Bool × S) ℤ
  let b : ℕ → P := fun n ↦ eval₂Hom (Int.castRingHom _)
    (fun i ↦ ghostPolynomial n (coordinates (mk fun d : S ↦ X (i, d)))) Φ
  let φ : ℕ → P →+* P := fun p ↦ (expand p).toRingHom
  have hφ : ∀ p, p.Prime → p ∈ S → ∀ a : P,
      φ p a - a ^ p ∈ Ideal.span {(p : P)} := by
    intro p hp _ a
    have : Fact p.Prime := ⟨hp⟩
    exact Ideal.mem_span_singleton.2 (MvPolynomial.natCast_dvd_expand_sub_pow p a)
  apply (ghost_image S φ hφ b).2
  intro p hp n hn hpn
  let I : Ideal P := Ideal.span {(p : P) ^ multiplicity p n}
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1
  -- Name the modulus so the two evaluations have the same quotient codomain.
  change Ideal.Quotient.mk I (b n) = Ideal.Quotient.mk I (φ p (b (n / p)))
  have hc (i : Bool) :
      Ideal.Quotient.mk I (ghostPolynomial n (coordinates (mk fun d : S ↦ X (i, d)))) =
        Ideal.Quotient.mk I (φ p
          (ghostPolynomial (n / p) (coordinates (mk fun d : S ↦ X (i, d))))) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      (ghostPolynomial_sub_map_ghostPolynomial_div_mem hp (φ p)
        (hφ p hp (S.mem_of_dvd hn hpn)) n _)
  simp only [b, map_eval₂Hom]
  have hcoeff : (Ideal.Quotient.mk I).comp (Int.castRingHom P) =
      (Ideal.Quotient.mk I).comp ((φ p).comp (Int.castRingHom P)) := Subsingleton.elim _ _
  rw [hcoeff]
  exact congrArg (fun g ↦ eval₂Hom _ g Φ) (funext hc)

private noncomputable def operationPolynomial (Φ : MvPolynomial Bool ℤ) (n : S) :
    MvPolynomial (Bool × S) ℤ :=
  (exists_operation Φ).choose n

private theorem operationPolynomial_ghost (Φ : MvPolynomial Bool ℤ) (n : S) :
    ghostPolynomial n (coordinates (mk (operationPolynomial Φ))) =
      eval₂Hom (Int.castRingHom _) (fun i ↦
        ghostPolynomial n (coordinates (mk fun d : S ↦ X (i, d)))) Φ := by
  rw [ghostPolynomial_congr (y := (exists_operation Φ).choose)]
  · exact (exists_operation Φ).choose_spec n n.property
  · intro d hd
    simp [coordinates, S.mem_of_dvd n.property hd, operationPolynomial]

private noncomputable def operation (Φ : MvPolynomial Bool ℤ) (x : Bool → BigWitt S R) :
    BigWitt S R :=
  mk fun n ↦ eval₂Hom (Int.castRingHom R) (fun id ↦ (x id.1).coeff id.2)
    (operationPolynomial Φ n)

private theorem mapData_operation (f : R →+* A) (Φ : MvPolynomial Bool ℤ)
    (x : Bool → BigWitt S R) :
    mapData f (operation Φ x) = operation Φ (fun i ↦ mapData f (x i)) := by
  apply BigWitt.ext
  funext n
  -- Evaluate the coordinate polynomial before commuting the coefficient map with evaluation.
  change f (eval₂Hom _ _ _) = eval₂Hom _ _ _
  rw [map_eval₂Hom]
  rw [RingHom.eq_intCast' (f.comp (Int.castRingHom R))]
  rfl

private theorem ghost_operation (Φ : MvPolynomial Bool ℤ) (x : Bool → BigWitt S R) (n : S) :
    ghost (operation Φ x) n = eval₂Hom (Int.castRingHom R) (fun i ↦ ghost (x i) n) Φ := by
  let f : MvPolynomial (Bool × S) ℤ →+* R :=
    eval₂Hom (Int.castRingHom R) fun id ↦ (x id.1).coeff id.2
  have h (i : Bool) : mapData f (mk fun d : S ↦ X (i, d)) = x i := by
    ext d
    simp [mapData, f]
  have he : mapData f (mk (operationPolynomial Φ)) = operation Φ x := by rfl
  rw [← he, ghost_mapData]
  -- The private ghost function at this stage is the original divisor polynomial.
  change f (ghostPolynomial n _) = _
  rw [operationPolynomial_ghost, map_eval₂Hom]
  rw [RingHom.eq_intCast' (f.comp (Int.castRingHom _))]
  have hi : (fun i ↦ f (ghostPolynomial n (coordinates (mk fun d : S ↦ X (i, d))))) =
      (fun i ↦ ghost (x i) n) := by
    funext i
    exact (ghost_mapData f _ n).symm.trans (congrArg (fun z ↦ ghost z n) (h i))
  rw [hi]

noncomputable instance : Zero (BigWitt S R) := ⟨mk fun _ ↦ 0⟩
noncomputable instance : One (BigWitt S R) := ⟨mk fun n ↦ if (n : ℕ) = 1 then 1 else 0⟩
@[no_expose] noncomputable instance : Add (BigWitt S R) := by
  exact ⟨fun x y ↦ operation (X false + X true) (fun i ↦ cond i y x)⟩
@[no_expose] noncomputable instance : Mul (BigWitt S R) := by
  exact ⟨fun x y ↦ operation (X false * X true) (fun i ↦ cond i y x)⟩
@[no_expose] noncomputable instance : Neg (BigWitt S R) := by
  exact ⟨fun x ↦ operation (-X false) (fun _ ↦ x)⟩

@[simp]
theorem coeff_zero (n : S) : (0 : BigWitt S R).coeff n = 0 := by rfl

@[simp]
theorem coeff_one (n : S) : (1 : BigWitt S R).coeff n = if (n : ℕ) = 1 then 1 else 0 := by rfl

@[simp]
private theorem ghost_zero (n : S) : ghost (0 : BigWitt S R) n = 0 := by
  classical
  rw [ghost, ghostPolynomial_eq_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have he := (Nat.div_ne_zero_iff_of_dvd (Nat.dvd_of_mem_divisors hd)).2
    ⟨S.ne_zero_of_mem n.property, (Nat.pos_of_mem_divisors hd).ne'⟩
  simp [coordinates, he]

@[simp]
private theorem ghost_one (n : S) : ghost (1 : BigWitt S R) n = 1 := by
  classical
  rw [ghost, ghostPolynomial_eq_sum]
  have hc : coordinates (1 : BigWitt S R) = fun d ↦ if d = 1 then 1 else 0 := by
    funext d
    by_cases hd : d ∈ S
    · simp [coordinates, hd, coeff_one]
    · by_cases hd1 : d = 1
      · subst d
        exact (hd (S.one_mem_of_mem n.property)).elim
      · simp [coordinates, hd, hd1]
  rw [hc, Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    have he := (Nat.div_ne_zero_iff_of_dvd (Nat.dvd_of_mem_divisors hd)).2
      ⟨S.ne_zero_of_mem n.property, (Nat.pos_of_mem_divisors hd).ne'⟩
    simp [hd1, he]
  · simp [Nat.mem_divisors, S.ne_zero_of_mem n.property]

@[simp]
private theorem ghost_add (x y : BigWitt S R) (n : S) :
    ghost (x + y) n = ghost x n + ghost y n := by
  exact (ghost_operation (X false + X true) _ n).trans (by simp)

@[simp]
private theorem ghost_mul (x y : BigWitt S R) (n : S) :
    ghost (x * y) n = ghost x n * ghost y n := by
  exact (ghost_operation (X false * X true) _ n).trans (by simp)

@[simp]
private theorem ghost_neg (x : BigWitt S R) (n : S) : ghost (-x) n = -ghost x n := by
  exact (ghost_operation (-X false) _ n).trans (by simp)

@[simp] private theorem mapData_zero (f : R →+* A) : mapData f (0 : BigWitt S R) = 0 := by
  ext n
  simp [mapData]

@[simp] private theorem mapData_one (f : R →+* A) : mapData f (1 : BigWitt S R) = 1 := by
  classical
  ext n
  simp only [mapData, coeff_mk, coeff_one]
  split_ifs <;> simp

@[simp] private theorem mapData_add (f : R →+* A) (x y : BigWitt S R) :
    mapData f (x + y) = mapData f x + mapData f y := by
  -- The opaque primitive addition is given by evaluation at the two input vectors.
  change mapData f (operation (X false + X true) (fun i ↦ cond i y x)) =
    operation (X false + X true) (fun i ↦ cond i (mapData f y) (mapData f x))
  simpa only [Bool.apply_cond] using
    mapData_operation f (X false + X true) (fun i ↦ cond i y x)

@[simp] private theorem mapData_mul (f : R →+* A) (x y : BigWitt S R) :
    mapData f (x * y) = mapData f x * mapData f y := by
  -- As for addition, expose the primitive operation locally to apply evaluation naturality.
  change mapData f (operation (X false * X true) (fun i ↦ cond i y x)) =
    operation (X false * X true) (fun i ↦ cond i (mapData f y) (mapData f x))
  simpa only [Bool.apply_cond] using
    mapData_operation f (X false * X true) (fun i ↦ cond i y x)

@[simp] private theorem mapData_neg (f : R →+* A) (x : BigWitt S R) :
    mapData f (-x) = -mapData f x := mapData_operation f (-X false) _

@[instance_reducible] private noncomputable def polyRing (ι : Type*) :
    CommRing (BigWitt S (MvPolynomial ι ℤ)) where
  add_assoc x y z := polynomial_ghost_injective (funext fun n ↦ by simp [add_assoc])
  zero_add x := polynomial_ghost_injective (funext fun n ↦ by simp)
  add_zero x := polynomial_ghost_injective (funext fun n ↦ by simp)
  add_comm x y := polynomial_ghost_injective (funext fun n ↦ by simp [add_comm])
  neg_add_cancel x := polynomial_ghost_injective (funext fun n ↦ by simp)
  mul_assoc x y z := polynomial_ghost_injective (funext fun n ↦ by simp [mul_assoc])
  one_mul x := polynomial_ghost_injective (funext fun n ↦ by simp)
  mul_one x := polynomial_ghost_injective (funext fun n ↦ by simp)
  mul_comm x y := polynomial_ghost_injective (funext fun n ↦ by simp [mul_comm])
  left_distrib x y z := polynomial_ghost_injective (funext fun n ↦ by simp [mul_add])
  right_distrib x y z := polynomial_ghost_injective (funext fun n ↦ by simp [add_mul])
  zero_mul x := polynomial_ghost_injective (funext fun n ↦ by simp)
  mul_zero x := polynomial_ghost_injective (funext fun n ↦ by simp)
  nsmul := nsmulRec
  zsmul := zsmulRec

private noncomputable def lift (x : BigWitt S R) : BigWitt S (MvPolynomial R ℤ) :=
  mk fun n ↦ X (x.coeff n)

private noncomputable abbrev specialize : BigWitt S (MvPolynomial R ℤ) → BigWitt S R :=
  mapData (counit R)

@[simp] private theorem specialize_lift (x : BigWitt S R) :
    mapData (counit R) (lift x) = x := by
  ext n
  simp [mapData, lift]

noncomputable instance : CommRing (BigWitt S R) where
  add_assoc x y z := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).add_assoc (lift x) (lift y) (lift z))
  zero_add x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).zero_add (lift x))
  add_zero x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).add_zero (lift x))
  add_comm x y := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).add_comm (lift x) (lift y))
  neg_add_cancel x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).neg_add_cancel (lift x))
  mul_assoc x y z := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).mul_assoc (lift x) (lift y) (lift z))
  one_mul x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).one_mul (lift x))
  mul_one x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).mul_one (lift x))
  mul_comm x y := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).mul_comm (lift x) (lift y))
  left_distrib x y z := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).left_distrib (lift x) (lift y) (lift z))
  right_distrib x y z := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).right_distrib (lift x) (lift y) (lift z))
  zero_mul x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).zero_mul (lift x))
  mul_zero x := by
    simpa using congrArg (specialize (S := S) (R := R))
      ((polyRing (S := S) R).mul_zero (lift x))
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The `n`-th ghost component is a ring homomorphism. -/
noncomputable def ghostComponent (n : S) : BigWitt S R →+* R where
  toFun x := ghost x n
  map_zero' := ghost_zero n
  map_one' := ghost_one n
  map_add' x y := ghost_add x y n
  map_mul' x y := ghost_mul x y n

/-- Evaluate a ghost component by its divisor polynomial. -/
theorem ghostComponent_apply (n : S) (x : BigWitt S R) :
    ghostComponent n x = ghostPolynomial n (coordinates x) := by rfl

/-- The joint ghost map to the ring of functions on the truncation set. -/
noncomputable def ghostMap : BigWitt S R →+* (S → R) :=
  RingHom.pi ghostComponent

@[simp]
theorem ghostMap_apply (x : BigWitt S R) (n : S) :
    ghostMap x n = ghostComponent n x := by rfl

/-- Ghost components determine vectors if multiplication by every index is injective. -/
theorem ghostMap_injective
    (hR : ∀ n ∈ S, Function.Injective (n • · : R → R)) :
    Function.Injective (ghostMap : BigWitt S R →+* (S → R)) :=
  ghost_injective hR

/-- Apply a coefficient ring homomorphism to every Witt coordinate. -/
noncomputable def map (S : TruncationSet) (f : R →+* A) : BigWitt S R →+* BigWitt S A where
  toFun := mapData f
  map_zero' := mapData_zero f
  map_one' := mapData_one f
  map_add' := mapData_add f
  map_mul' := mapData_mul f

@[simp]
theorem map_coeff (f : R →+* A) (x : BigWitt S R) (n : S) :
    (map S f x).coeff n = f (x.coeff n) := by rfl

@[simp]
theorem map_id : map S (RingHom.id R) = RingHom.id (BigWitt S R) := by
  ext x n
  rfl

@[simp]
theorem map_comp (f : R →+* A) (g : A →+* B) :
    map S (g.comp f) = (map S g).comp (map S f) := by
  ext x n
  rfl

@[simp]
theorem ghostComponent_map (f : R →+* A) (x : BigWitt S R) (n : S) :
    ghostComponent n (map S f x) = f (ghostComponent n x) := ghost_mapData f x n

private def restrictData (h : T ≤ S) (x : BigWitt S R) : BigWitt T R :=
  mk fun n ↦ x.coeff ⟨n, h n.property⟩

private theorem ghost_restrictData (h : T ≤ S) (x : BigWitt S R) (n : T) :
    ghost (restrictData h x) n = ghost x ⟨n, h n.property⟩ := by
  classical
  apply ghostPolynomial_congr
  intro d hd
  simp [coordinates, T.mem_of_dvd n.property hd,
    S.mem_of_dvd (h n.property) hd, restrictData]

private theorem mapData_restrictData (h : T ≤ S) (f : R →+* A) (x : BigWitt S R) :
    mapData f (restrictData h x) = restrictData h (mapData f x) := by rfl

private theorem restrictData_add (h : T ≤ S) (x y : BigWitt S R) :
    restrictData h (x + y) = restrictData h x + restrictData h y := by
  have he : restrictData h (lift x + lift y) =
      restrictData h (lift x) + restrictData h (lift y) :=
    polynomial_ghost_injective (funext fun n ↦ by simp [ghost_restrictData])
  simpa only [mapData_add, mapData_restrictData, specialize_lift] using
    congrArg (mapData (counit R)) he

private theorem restrictData_mul (h : T ≤ S) (x y : BigWitt S R) :
    restrictData h (x * y) = restrictData h x * restrictData h y := by
  have he : restrictData h (lift x * lift y) =
      restrictData h (lift x) * restrictData h (lift y) :=
    polynomial_ghost_injective (funext fun n ↦ by simp [ghost_restrictData])
  simpa only [mapData_mul, mapData_restrictData, specialize_lift] using
    congrArg (mapData (counit R)) he

/-- Restrict a big Witt vector to a smaller truncation set. -/
noncomputable def restrict (h : T ≤ S) : BigWitt S R →+* BigWitt T R where
  toFun := restrictData h
  map_zero' := by rfl
  map_one' := by rfl
  map_add' := restrictData_add h
  map_mul' := restrictData_mul h

@[simp]
theorem restrict_coeff (h : T ≤ S) (x : BigWitt S R) (n : T) :
    (restrict h x).coeff n = x.coeff ⟨n, h n.property⟩ := by rfl

@[simp]
theorem restrict_refl : restrict (le_refl S) = RingHom.id (BigWitt S R) := by
  ext x n
  rfl

@[simp]
theorem restrict_comp (h : T ≤ S) (k : U ≤ T) :
    (restrict k).comp (restrict h) = (restrict (R := R) (k.trans h)) := by
  ext x n
  rfl

@[simp]
theorem ghostComponent_restrict (h : T ≤ S) (x : BigWitt S R) (n : T) :
    ghostComponent n (restrict h x) = ghostComponent ⟨n, h n.property⟩ x :=
  ghost_restrictData h x n

/-- Restriction commutes with applying a coefficient homomorphism. -/
theorem restrict_map (h : T ≤ S) (f : R →+* A) :
    (restrict h).comp (map S f) = (map T f).comp (restrict h) := by
  ext x n
  rfl

end
end BigWitt
end TauCeti
