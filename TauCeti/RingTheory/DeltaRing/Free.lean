/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeltaRing.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Free `δ`-rings

Fix a prime `p` and a type `S`. The free `δ`-ring on `S` is the polynomial ring
`ℤ[x_{s,n} | s ∈ S, n ∈ ℕ]` with `δ x_{s,n} = x_{s,n+1}`. Its Frobenius sends `x_{s,n}` to
`x_{s,n} ^ p + p * x_{s,n+1}`; since `p` is a nonzerodivisor on this polynomial ring and this
endomorphism lifts the `p`-th power map modulo `p`, it determines the `δ`-structure
(`TauCeti.DeltaRing.ofFrobeniusLift`).

The ring is free on `S` among `δ`-rings: for every `δ`-ring `B`, `δ`-maps
`FreeDeltaRing p S → B` correspond to functions `S → B`, by restriction to the generators
`x_{s,0}`. The `δ`-map attached to `f : S → B` sends `x_{s,n}` to `δ^[n] (f s)`. The polynomial
ring `ℤ[x_{s,0} | s ∈ S]` is strictly smaller, since `x_{s,1} = δ x_{s,0}`. No hypothesis on
`B` is needed: it may have `p`-torsion or be the zero ring.

The free `δ`-ring is a type synonym for `MvPolynomial (S × ℕ) ℤ` rather than an instance on that
ring, which carries other natural `δ`-structures, such as the monoid-algebra structure with
`δ x = 0` on every variable (`TauCeti.DeltaRing.monoidAlgebra`). The identification with the
polynomial ring is `TauCeti.FreeDeltaRing.equivMvPolynomial`.

## Main definitions

* `TauCeti.FreeDeltaRing p S`: the free `δ`-ring on `S`, with generators
  `TauCeti.FreeDeltaRing.X s n` standing for `x_{s,n}`.
* `TauCeti.FreeDeltaRing.equivMvPolynomial`: its identification with `MvPolynomial (S × ℕ) ℤ`.
* `TauCeti.FreeDeltaRing.lift`: the universal property, `(S → B) ≃` the `δ`-maps
  `FreeDeltaRing p S → B`.

## Main results

* `TauCeti.FreeDeltaRing.delta_X`: `δ x_{s,n} = x_{s,n+1}`.
* `TauCeti.FreeDeltaRing.frobenius_X`: `φ x_{s,n} = x_{s,n} ^ p + p * x_{s,n+1}`.
* `TauCeti.FreeDeltaRing.lift_apply_X`: the `δ`-map attached to `f` sends `x_{s,n}` to
  `δ^[n] (f s)`.
* `TauCeti.FreeDeltaRing.isDeltaMap_ext`: `δ`-maps out of `FreeDeltaRing p S` agreeing on every
  `x_{s,0}` are equal.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Lemma 2.11 and its proof.
-/

public section

namespace TauCeti

open DeltaRing

/-- The free `δ`-ring on a type `S` for the prime `p`: the polynomial ring
`ℤ[x_{s,n} | s ∈ S, n ∈ ℕ]` with `δ x_{s,n} = x_{s,n+1}` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.11). The ring does not depend on `p`, but its `δ`-structure does. -/
def FreeDeltaRing (_p : ℕ) (S : Type*) : Type _ :=
  MvPolynomial (S × ℕ) ℤ

namespace FreeDeltaRing

variable (p : ℕ) (S : Type*)

noncomputable instance instCommRing : CommRing (FreeDeltaRing p S) :=
  inferInstanceAs (CommRing (MvPolynomial (S × ℕ) ℤ))

instance instIsDomain : IsDomain (FreeDeltaRing p S) :=
  inferInstanceAs (IsDomain (MvPolynomial (S × ℕ) ℤ))

instance instCharZero : CharZero (FreeDeltaRing p S) :=
  inferInstanceAs (CharZero (MvPolynomial (S × ℕ) ℤ))

/-- The free `δ`-ring on `S` is the polynomial ring `ℤ[x_{s,n} | s ∈ S, n ∈ ℕ]`. -/
noncomputable def equivMvPolynomial : FreeDeltaRing p S ≃+* MvPolynomial (S × ℕ) ℤ :=
  RingEquiv.refl _

variable {p S}

/-- The generator `x_{s,n}` of the free `δ`-ring, equal to `δ^[n] x_{s,0}`
(`delta_iterate_X`). -/
noncomputable def X (s : S) (n : ℕ) : FreeDeltaRing p S :=
  (equivMvPolynomial p S).symm (MvPolynomial.X (s, n))

/-- The identification with the polynomial ring sends `x_{s,n}` to the variable `X (s, n)`. -/
@[simp]
theorem equivMvPolynomial_X (s : S) (n : ℕ) :
    equivMvPolynomial p S (X s n) = MvPolynomial.X (s, n) :=
  (equivMvPolynomial p S).apply_symm_apply _

/-- The variable `X (s, n)` of the polynomial ring is the generator `x_{s,n}`. -/
@[simp]
theorem equivMvPolynomial_symm_X (s : S) (n : ℕ) :
    (equivMvPolynomial p S).symm (MvPolynomial.X (s, n)) = X s n :=
  (rfl)

variable (p S) in
/-- The generators `x_{s,n}` generate the free `δ`-ring as a ring. -/
theorem closure_range_X :
    Subring.closure (Set.range fun i : S × ℕ => (X i.1 i.2 : FreeDeltaRing p S)) = ⊤ := by
  have h : Subring.closure (Set.range (MvPolynomial.X : S × ℕ → MvPolynomial (S × ℕ) ℤ)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rintro x -
    induction x using MvPolynomial.induction_on with
    | C a => exact eq_intCast MvPolynomial.C a ▸ intCast_mem _ a
    | add f g hf hg => exact add_mem hf hg
    | mul_X f i hf => exact mul_mem hf (Subring.subset_closure ⟨i, rfl⟩)
  have hrange : (Set.range fun i : S × ℕ => (X i.1 i.2 : FreeDeltaRing p S)) =
      (equivMvPolynomial p S).symm.toRingHom '' Set.range MvPolynomial.X := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => (equivMvPolynomial_symm_X i.1 i.2).symm)
  rw [hrange, ← RingHom.map_closure, h, ← RingHom.range_eq_map, RingHom.range_eq_top]
  exact (equivMvPolynomial p S).symm.surjective

/-- Two ring homomorphisms out of the free `δ`-ring agreeing on every generator `x_{s,n}` are
equal. -/
@[ext]
theorem ringHom_ext {B : Type*} [Semiring B] {f g : FreeDeltaRing p S →+* B}
    (h : ∀ s n, f (X s n) = g (X s n)) : f = g := by
  have hint := RingHom.ext_int (f.comp (Int.castRingHom _)) (g.comp (Int.castRingHom _))
  have := MvPolynomial.ringHom_ext (f := f.comp (equivMvPolynomial p S).symm.toRingHom)
    (g := g.comp (equivMvPolynomial p S).symm.toRingHom)
    (fun r => by simpa using RingHom.congr_fun hint r) fun i => h i.1 i.2
  exact RingHom.ext fun x => by simpa using RingHom.congr_fun this (equivMvPolynomial p S x)

section LiftRingHom

variable {B : Type*} [CommRing B] [DeltaRing p B]

variable (p) in
/-- The ring homomorphism `x_{s,n} ↦ δ^[n] (f s)` out of the free `δ`-ring. -/
private noncomputable def liftRingHom (f : S → B) : FreeDeltaRing p S →+* B :=
  (MvPolynomial.aeval fun i : S × ℕ => (delta p)^[i.2] (f i.1)).toRingHom.comp
    (equivMvPolynomial p S).toRingHom

private theorem liftRingHom_X (f : S → B) (s : S) (n : ℕ) :
    liftRingHom p f (X s n) = (delta p)^[n] (f s) := by
  simp [liftRingHom]

end LiftRingHom

section Delta

variable [hp : Fact p.Prime]

/-- `p` is a nonzerodivisor on the free `δ`-ring, a polynomial ring over `ℤ`. -/
private theorem isRegular_natCast : IsRegular (p : FreeDeltaRing p S) :=
  isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)

variable (p S) in
/-- The Frobenius lift of the free `δ`-ring, `x_{s,n} ↦ x_{s,n} ^ p + p * x_{s,n+1}`. -/
private noncomputable def frobeniusLift : FreeDeltaRing p S →+* FreeDeltaRing p S :=
  ((equivMvPolynomial p S).symm.toRingHom.comp
      (MvPolynomial.aeval fun i : S × ℕ =>
        MvPolynomial.X i ^ p +
          (p : MvPolynomial (S × ℕ) ℤ) * MvPolynomial.X (i.1, i.2 + 1)).toRingHom).comp
    (equivMvPolynomial p S).toRingHom

omit hp in
private theorem frobeniusLift_X (s : S) (n : ℕ) :
    frobeniusLift p S (X s n) = X s n ^ p + (p : FreeDeltaRing p S) * X s (n + 1) := by
  simp [frobeniusLift]

/-- The endomorphism `x_{s,n} ↦ x_{s,n} ^ p + p * x_{s,n+1}` lifts Frobenius modulo `p`: the
elements `x` with `p ∣ φ x - x ^ p` form a subring containing the generators. -/
private theorem isFrobeniusLift_frobeniusLift : IsFrobeniusLift p (frobeniusLift p S) := by
  refine ⟨fun x => ?_⟩
  induction (closure_range_X p S ▸ Subring.mem_top x : x ∈ Subring.closure _)
    using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨⟨s, n⟩, rfl⟩ := hx
    exact ⟨X s (n + 1), by rw [frobeniusLift_X]; ring⟩
  | zero => simp [zero_pow hp.out.ne_zero]
  | one => simp
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b + addCorrection p x y, ?_⟩
    rw [map_add]
    linear_combination ha + hb - natCast_mul_addCorrection (p := p) x y
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a - addCorrection p x (-x), ?_⟩
    have h0 := natCast_mul_addCorrection (p := p) x (-x)
    rw [add_neg_cancel, zero_pow hp.out.ne_zero, sub_zero] at h0
    rw [map_neg]
    linear_combination -ha + h0
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * frobeniusLift p S y + x ^ p * b, ?_⟩
    rw [map_mul]
    linear_combination frobeniusLift p S y * ha + x ^ p * hb

variable (p S) in
/-- The `δ`-structure of the Frobenius lift `frobeniusLift`, on which `instDeltaRing` is built. -/
@[instance_reducible]
private noncomputable def deltaRingOfFrobeniusLift : DeltaRing p (FreeDeltaRing p S) :=
  ofFrobeniusLift isRegular_natCast (frobeniusLift p S) isFrobeniusLift_frobeniusLift

variable (p S) in
/-- The `δ`-operation of the free `δ`-ring. -/
-- A separate, semireducible definition, so that `simp` does not unfold `instDeltaRing` to
-- `ofFrobeniusLift` and rewrite `frobenius` through `frobenius_ofFrobeniusLift` to the private
-- `frobeniusLift`.
private noncomputable def deltaFun : FreeDeltaRing p S → FreeDeltaRing p S :=
  (deltaRingOfFrobeniusLift p S).delta

/-- The `δ`-structure of the free `δ`-ring, with `δ x_{s,n} = x_{s,n+1}` (`delta_X`). -/
-- A `def` made an instance afterwards, rather than an `instance`, so that its body, which uses
-- private definitions, is not exported; `delta_X` characterises it.
@[instance_reducible]
noncomputable def instDeltaRing : DeltaRing p (FreeDeltaRing p S) where
  delta := deltaFun p S
  delta_zero := (deltaRingOfFrobeniusLift p S).delta_zero
  delta_one := (deltaRingOfFrobeniusLift p S).delta_one
  delta_add := (deltaRingOfFrobeniusLift p S).delta_add
  delta_mul := (deltaRingOfFrobeniusLift p S).delta_mul

attribute [instance] instDeltaRing

/-- `δ x_{s,n} = x_{s,n+1}` in the free `δ`-ring. -/
@[simp]
theorem delta_X (s : S) (n : ℕ) : delta p (X s n : FreeDeltaRing p S) = X s (n + 1) := by
  apply isRegular_natCast.left
  have h := natCast_mul_delta_ofFrobeniusLift isRegular_natCast (frobeniusLift p S)
    isFrobeniusLift_frobeniusLift (X s n)
  rw [frobeniusLift_X] at h
  -- `h` is about `deltaRingOfFrobeniusLift`, whose `δ`-operation is `deltaFun` by definition.
  exact h.trans (by ring)

/-- `δ^[k] x_{s,n} = x_{s,n+k}` in the free `δ`-ring. -/
theorem delta_iterate_X (s : S) (n k : ℕ) :
    (delta p)^[k] (X s n : FreeDeltaRing p S) = X s (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, delta_X, add_assoc]

/-- The Frobenius of the free `δ`-ring: `φ x_{s,n} = x_{s,n} ^ p + p * x_{s,n+1}`. -/
@[simp]
theorem frobenius_X (s : S) (n : ℕ) :
    frobenius p (FreeDeltaRing p S) (X s n) =
      X s n ^ p + (p : FreeDeltaRing p S) * X s (n + 1) := by
  rw [frobenius_apply, delta_X]

/-- Two `δ`-maps out of the free `δ`-ring agreeing on every generator `x_{s,0}` are equal. -/
theorem isDeltaMap_ext {B : Type*} [CommRing B] [DeltaRing p B] {f g : FreeDeltaRing p S →+* B}
    (hf : IsDeltaMap p f) (hg : IsDeltaMap p g) (h : ∀ s, f (X s 0) = g (X s 0)) : f = g := by
  refine ringHom_ext fun s n => ?_
  induction n with
  | zero => exact h s
  | succ n ih => rw [← delta_X, hf.map_delta, hg.map_delta, ih]

section Lift

variable {B : Type*} [CommRing B] [DeltaRing p B]

private theorem isDeltaMap_liftRingHom (f : S → B) : IsDeltaMap p (liftRingHom p f) := by
  refine isDeltaMap_of_closure_eq_top (closure_range_X p S) _ ?_
  rintro _ ⟨⟨s, n⟩, rfl⟩
  rw [delta_X, liftRingHom_X, liftRingHom_X, Function.iterate_succ_apply']

private theorem liftRingHom_apply_X_zero {f : FreeDeltaRing p S →+* B} (hf : IsDeltaMap p f) :
    liftRingHom p (fun s => f (X s 0)) = f := by
  refine isDeltaMap_ext (isDeltaMap_liftRingHom _) hf fun s => ?_
  rw [liftRingHom_X, Function.iterate_zero_apply]

variable (p S B) in
/-- The universal property of the free `δ`-ring (Bhatt and Scholze, *Prisms and prismatic
cohomology*, Lemma 2.11): `δ`-maps `FreeDeltaRing p S → B` correspond to functions `S → B`. The
`δ`-map attached to `f` sends `x_{s,n}` to `δ^[n] (f s)` (`lift_apply_X`), and a `δ`-map
corresponds to its values on the generators `x_{s,0}` (`lift_symm_apply`). -/
noncomputable def lift : (S → B) ≃ {f : FreeDeltaRing p S →+* B // IsDeltaMap p f} where
  toFun f := ⟨liftRingHom p f, isDeltaMap_liftRingHom f⟩
  invFun f s := f.val (X s 0)
  left_inv f := funext fun s => by simp only [liftRingHom_X, Function.iterate_zero_apply]
  right_inv f := Subtype.ext (liftRingHom_apply_X_zero f.property)

/-- The `δ`-map attached to `f : S → B` sends `x_{s,n}` to `δ^[n] (f s)`. -/
@[simp]
theorem lift_apply_X (f : S → B) (s : S) (n : ℕ) :
    (lift p S B f).val (X s n) = (delta p)^[n] (f s) :=
  liftRingHom_X f s n

/-- The function attached to a `δ`-map out of the free `δ`-ring is its restriction to the
generators `x_{s,0}`. -/
@[simp]
theorem lift_symm_apply (f : {f : FreeDeltaRing p S →+* B // IsDeltaMap p f}) (s : S) :
    (lift p S B).symm f s = f.val (X s 0) :=
  (rfl)

end Lift

end Delta

end FreeDeltaRing

end TauCeti
