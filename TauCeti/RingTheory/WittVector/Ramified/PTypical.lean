/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Ramified.Basic
public import Mathlib.RingTheory.WittVector.Basic

import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Comparison with p-typical Witt vectors

When the uniformizer and residue cardinality both equal the prime `p`, the ramified
structure polynomials are the base changes of Mathlib's `p`-typical structure polynomials.
Identifying the coordinates then gives a ghost-preserving ring equivalence on every coefficient
algebra. The ramified Dwork criterion also specializes to the `p`-typical ghost map.

## Main results

* `TauCeti.ramifiedWittStructure_natCast_eq_map_wittStructureInt` compares structure polynomials.
* `TauCeti.RamifiedWittVector.ringEquivWittVector` gives the coordinatewise ring equivalence.
* `TauCeti.WittVector.mem_range_ghostMap_iff` gives Dwork's criterion for the `p`-typical ghost map.
* `TauCeti.WittVector.ghostMap_injective` gives injectivity of the ghost map when `p` is regular.
-/

public section

namespace TauCeti

open IsLocalRing MvPolynomial

section Ghost

variable {O : Type*} [CommRing O]

/-- For `π = q = p` the ramified Witt polynomials are Mathlib's `p`-typical Witt polynomials. -/
theorem ramifiedWittPolynomial_natCast_self (p n : ℕ) :
    ramifiedWittPolynomial (p : O) p n = wittPolynomial p O n := by
  simp [ramifiedWittPolynomial_def, wittPolynomial_eq_sum_C_mul_X_pow]

/-- For `π = q = p`, the ramified ghost components of the coordinates of a `p`-typical Witt vector
are its ghost components. -/
@[simp]
theorem ramifiedGhost_natCast_self_coeff {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Algebra O R] (x : _root_.WittVector p R) (n : ℕ) :
    ramifiedGhost (p : O) p n x.coeff = _root_.WittVector.ghostComponent n x := by
  simp [_root_.WittVector.ghostComponent_apply, aeval_wittPolynomial, ramifiedGhost_def]

end Ghost

namespace WittVector

open _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]

/-- **Dwork's criterion** for `p`-typical Witt vectors: if `σ` is a ring endomorphism of `A`
lifting the Frobenius modulo `p`, a sequence `y` is the ghost sequence of a Witt vector if and only
if `y (n + 1) ≡ σ (y n)` modulo `p ^ (n + 1)` for every `n`. -/
theorem mem_range_ghostMap_iff (σ : A →+* A) (hσ : ∀ a, (p : A) ∣ σ a - a ^ p) (y : ℕ → A) :
    y ∈ Set.range (ghostMap : _root_.WittVector p A → ℕ → A) ↔
      ∀ n, (p : A) ^ (n + 1) ∣ y (n + 1) - σ (y n) := by
  have h := exists_ramifiedGhost_eq_iff (π := (p : ℤ)) (q := p) (by simp) σ.toIntAlgHom
    (by simpa using hσ) y
  simp only [map_natCast, RingHom.toIntAlgHom_apply] at h
  rw [← h]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.coeff, fun n ↦ by rw [ramifiedGhost_natCast_self_coeff, ghostMap_apply]⟩
  · rintro ⟨x, hx⟩
    exact ⟨mk p x, funext fun n ↦ by
      rw [ghostMap_apply, ← ramifiedGhost_natCast_self_coeff (O := ℤ), coeff_mk, hx]⟩

/-- If `p` is a nonzerodivisor of `A`, the ghost map of `p`-typical Witt vectors over `A` is
injective. -/
theorem ghostMap_injective (hp : (p : A) ∈ nonZeroDivisors A) :
    Function.Injective (ghostMap : _root_.WittVector p A → ℕ → A) := fun x y h ↦ by
  refine ext fun n ↦ congrFun (ramifiedGhost_injective (O := ℤ) (π := p) (q := p)
    (by simpa using hp) (funext fun k ↦ ?_)) n
  simpa [ramifiedGhost_natCast_self_coeff, ghostMap_apply] using congrFun h k

end WittVector

variable {O : Type*} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  {ι : Type*}

/-- When the uniformizer and residue cardinality are both `p`, the ramified structure
polynomials of an integer polynomial are the base changes of Mathlib's `p`-typical ones. -/
theorem ramifiedWittStructure_natCast_eq_map_wittStructureInt {p : ℕ} [Fact p.Prime]
    (hq : Nat.card (ResidueField O) = p) (hp : maximalIdeal O = Ideal.span {(p : O)})
    (hpreg : (p : O) ∈ nonZeroDivisors O) (Φ : MvPolynomial ι ℤ) (n : ℕ) :
    ramifiedWittStructure hp hpreg (map (Int.castRingHom O) Φ) n =
      map (Int.castRingHom O) (wittStructureInt p Φ n) := by
  symm
  refine map_eq_ramifiedWittStructure hp hpreg (Int.castRingHom O)
    (ρ := (p : ℤ)) (by simp) Φ (s := wittStructureInt p Φ) ?_ n
  intro k
  simpa only [hq, ← aeval_ramifiedWittPolynomial, ramifiedWittPolynomial_natCast_self,
    rename_eq_aeval, Function.comp_def] using wittStructureInt_prop p Φ k

namespace RamifiedWittVector

variable {p : ℕ} [Fact p.Prime]
  [Fact (maximalIdeal O = Ideal.span {(p : O)})] [Fact ((p : O) ∈ nonZeroDivisors O)]
  {A : Type*} [CommRing A] [Algebra O A]

private theorem aeval_ramifiedWittStructure_map_intCast (hq : Nat.card (ResidueField O) = p)
    (x : ι × ℕ → A) (Φ : MvPolynomial ι ℤ) (n : ℕ) :
    aeval x (ramifiedWittStructure
      (Fact.out : maximalIdeal O = Ideal.span {(p : O)})
      (Fact.out : (p : O) ∈ nonZeroDivisors O) (MvPolynomial.map (Int.castRingHom O) Φ) n) =
      aeval x (wittStructureInt p Φ n) := by
  rw [ramifiedWittStructure_natCast_eq_map_wittStructureInt hq, ← algebraMap_int_eq,
    aeval_map_algebraMap]

/-- For uniformizer `p` and residue cardinality `p`, identifying Witt coordinates gives a ring
isomorphism with Mathlib's `p`-typical Witt vectors. -/
def ringEquivWittVector (hq : Nat.card (ResidueField O) = p) :
    RamifiedWittVector (p : O) A ≃+* _root_.WittVector p A where
  toFun x := _root_.WittVector.mk p x.coeff
  invFun x := mk x.coeff
  left_inv x := by ext n; rfl
  right_inv x := by ext n; rfl
  map_add' x y := by
    ext n
    rw [_root_.WittVector.coeff_mk, _root_.WittVector.add_coeff, add_coeff]
    have h := aeval_ramifiedWittStructure_map_intCast hq (Function.uncurry ![x.coeff, y.coeff])
      (X (0 : Fin 2) + X 1) n
    rw [map_add, map_X, map_X] at h
    exact h
  map_mul' x y := by
    ext n
    rw [_root_.WittVector.coeff_mk, _root_.WittVector.mul_coeff, mul_coeff]
    have h := aeval_ramifiedWittStructure_map_intCast hq (Function.uncurry ![x.coeff, y.coeff])
      (X (0 : Fin 2) * X 1) n
    rw [map_mul, map_X, map_X] at h
    exact h

@[simp]
theorem coeff_ringEquivWittVector (hq : Nat.card (ResidueField O) = p)
    (x : RamifiedWittVector (p : O) A) (n : ℕ) :
    (ringEquivWittVector hq x).coeff n = x.coeff n :=
  (rfl)

@[simp]
theorem coeff_ringEquivWittVector_symm (hq : Nat.card (ResidueField O) = p)
    (x : _root_.WittVector p A) (n : ℕ) :
    ((ringEquivWittVector hq).symm x : RamifiedWittVector (p : O) A).coeff n = x.coeff n :=
  (rfl)

/-- The coordinate comparison intertwines the ramified and `p`-typical ghost homomorphisms. -/
@[simp]
theorem ghostComponent_ringEquivWittVector (hq : Nat.card (ResidueField O) = p)
    (x : RamifiedWittVector (p : O) A) (n : ℕ) :
    _root_.WittVector.ghostComponent n (ringEquivWittVector hq x) = ghostComponent n x := by
  rw [ghostComponent_apply, hq, ← ramifiedGhost_natCast_self_coeff (O := O)]
  exact ramifiedGhost_congr (fun i _ ↦ coeff_ringEquivWittVector hq x i)

end RamifiedWittVector

end TauCeti
