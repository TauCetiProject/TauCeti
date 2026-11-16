/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Slab algebras, normal-form bases, and chamber homomorphisms

For a commutative ring `R` and an arbitrary parameter `q : R`, the *slab algebra* is the quotient
`SlabAlgebra R q := R[X, Y] ⧸ (X Y - q)`. Across a codimension-one slab in a toric degeneration or
broken-line scattering diagram, `X` and `Y` represent monomials pointing to opposite sides of the
slab whose product equals a wall factor `q`.

Writing `Z q n` for `X ^ (-n)` when `n < 0`, `1` when `n = 0`, and `Y ^ n` when `n > 0`, the
defining relation `X * Y = q` reduces every product `Z q n * Z q m` to a single normal-form
monomial multiplied by a power of `q`:
`Z q n * Z q m = q ^ ((|n| + |m| - |n + m|) / 2) • Z q (n + m)`.

Mapping into the two adjacent Laurent polynomial chamber algebras `R[T; T⁻¹]` via
`chamberLeft : (X, Y) ↦ (T, q T⁻¹)` and `chamberRight : (X, Y) ↦ (q T⁻¹, T)` separates nonpositive
and nonnegative normal-form indices cleanly: `chamberLeft` sends `{Z q n | n ≤ 0}` to nonnegative
powers of `T` and `{Z q n | 0 < n}` to strictly negative powers of `T`, while `chamberRight` does
the reverse. This yields both the `R`-basis `SlabAlgebra.basis` indexed by `ℤ` (hence freeness of
`SlabAlgebra R q` over `R` for every `q : R`, without any regularity or non-zerodivisor hypothesis
on `q`) and joint injectivity of the two chamber homomorphisms.

## Main definitions

* `TauCeti.SlabAlgebra`: the quotient `R[X, Y] ⧸ (X Y - q)`.
* `TauCeti.SlabAlgebra.X`, `TauCeti.SlabAlgebra.Y`: the two slab generators.
* `TauCeti.SlabAlgebra.lift`, `TauCeti.SlabAlgebra.liftAlgHom`, `TauCeti.SlabAlgebra.mapRingHom`,
  `TauCeti.SlabAlgebra.mapAlgHom`: universal property and functoriality in `(R, q)`.
* `TauCeti.SlabAlgebra.Z`: the normal-form monomials indexed by `ℤ`.
* `TauCeti.SlabAlgebra.chamberLeft`, `TauCeti.SlabAlgebra.chamberRight`: the two `R`-algebra
  homomorphisms into `LaurentPolynomial R`.
* `TauCeti.SlabAlgebra.basis`: the `R`-basis of `SlabAlgebra R q` given by `Z q`.

## Main results

* `TauCeti.SlabAlgebra.Z_mul_Z`: normal-form multiplication formula
  `Z q n * Z q m = q ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) • Z q (n + m)`.
* `TauCeti.SlabAlgebra.basis_repr_of_nonpos`, `TauCeti.SlabAlgebra.basis_repr_of_nonneg`:
  coordinates in `basis q` are read directly from nonnegative Laurent coefficients of
  `chamberLeft q` and `chamberRight q`.
* `TauCeti.SlabAlgebra.chamberLeft_prod_chamberRight_injective`: joint injectivity of the two
  chamber homomorphisms for arbitrary `R` and `q`.

## References

* [M. Gross and B. Siebert, *An Invitation to Toric Degenerations*][GrossSiebert2011], §2.3
  (arXiv:0808.2749).
* [M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*][GrossHackingSiebert2022], §3, Definition 3.3 (arXiv:1601.07081).
-/

public noncomputable section

namespace TauCeti

/-- Variable index for the two transverse generators `X` and `Y` of a slab algebra. -/
inductive SlabGenerator : Type
  | X | Y
  deriving DecidableEq

/-- The principal ideal `(X Y - q)` in `R[X, Y]` defining `SlabAlgebra R q`. -/
def slabIdeal (R : Type*) [CommRing R] (q : R) : Ideal (MvPolynomial SlabGenerator R) :=
  Ideal.span {MvPolynomial.X .X * MvPolynomial.X .Y - MvPolynomial.C q}

/-- The slab algebra `R[X, Y] ⧸ (X Y - q)` over a commutative ring `R` with wall factor `q : R`. -/
abbrev SlabAlgebra (R : Type*) [CommRing R] (q : R) : Type _ :=
  MvPolynomial SlabGenerator R ⧸ slabIdeal R q

namespace SlabAlgebra

section Basic

variable {R : Type*} [CommRing R]

/-- The quotient `R`-algebra map `R[X, Y] →ₐ[R] SlabAlgebra R q`. -/
def mk (q : R) : MvPolynomial SlabGenerator R →ₐ[R] SlabAlgebra R q :=
  Ideal.Quotient.mkₐ R (slabIdeal R q)

/-- The first transverse generator `X` of `SlabAlgebra R q`. -/
def X (q : R) : SlabAlgebra R q := Ideal.Quotient.mk (slabIdeal R q) (MvPolynomial.X .X)

/-- The second transverse generator `Y` of `SlabAlgebra R q`. -/
def Y (q : R) : SlabAlgebra R q := Ideal.Quotient.mk (slabIdeal R q) (MvPolynomial.X .Y)

@[simp] theorem mk_X (q : R) : mk q (MvPolynomial.X .X) = X q := by
  rw [mk, Ideal.Quotient.mkₐ_eq_mk, X]

@[simp] theorem mk_Y (q : R) : mk q (MvPolynomial.X .Y) = Y q := by
  rw [mk, Ideal.Quotient.mkₐ_eq_mk, Y]

/-- The quotient map onto `SlabAlgebra R q` is surjective. -/
theorem mk_surjective (q : R) : Function.Surjective (mk q) := Ideal.Quotient.mk_surjective

/-- The defining slab relation `X * Y = q`. -/
@[simp] theorem X_mul_Y (q : R) : X q * Y q = algebraMap R (SlabAlgebra R q) q := by
  rw [X, Y, ← map_mul, ← MvPolynomial.algHom_C (mk q), mk, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

/-- Commuted form `Y * X = q` of the defining slab relation. -/
@[simp] theorem Y_mul_X (q : R) : Y q * X q = algebraMap R (SlabAlgebra R q) q := by
  rw [mul_comm, X_mul_Y]

/-- Ring homomorphisms out of `SlabAlgebra R q` are determined by their restriction to `R` and
their values on `X q` and `Y q`. -/
theorem ringHom_ext {A : Type*} [NonAssocSemiring A] {q : R} {f g : SlabAlgebra R q →+* A}
    (hR : ∀ r : R, f (algebraMap R (SlabAlgebra R q) r) = g (algebraMap R (SlabAlgebra R q) r))
    (hX : f (X q) = g (X q)) (hY : f (Y q) = g (Y q)) : f = g := by
  apply Ideal.Quotient.ringHom_ext; ext p
  induction p using MvPolynomial.induction_on with
  | C r => exact hR r
  | add p₁ p₂ hp₁ hp₂ => simp only [RingHom.comp_apply, map_add] at hp₁ hp₂ ⊢; rw [hp₁, hp₂]
  | mul_X p₁ v hp₁ =>
    simp only [RingHom.comp_apply, map_mul] at hp₁ ⊢
    cases v <;> [rw [hp₁, ← X, hX]; rw [hp₁, ← Y, hY]]

/-- Algebra homomorphisms out of `SlabAlgebra R q` over a base semiring `K` are determined by their
restriction to `R` and their values on `X q` and `Y q`. -/
theorem algHom_ext_of_tower {K A : Type*} [CommSemiring K] [Algebra K R] [Semiring A] [Algebra K A]
    {q : R} {f g : SlabAlgebra R q →ₐ[K] A}
    (hR : ∀ r : R, f (algebraMap R (SlabAlgebra R q) r) = g (algebraMap R (SlabAlgebra R q) r))
    (hX : f (X q) = g (X q)) (hY : f (Y q) = g (Y q)) : f = g :=
  AlgHom.toRingHom_injective (ringHom_ext hR hX hY)

/-- `R`-algebra homomorphisms out of `SlabAlgebra R q` are determined by their values on `X q`
and `Y q`. -/
@[ext] theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {q : R}
    {f g : SlabAlgebra R q →ₐ[R] A} (hX : f (X q) = g (X q)) (hY : f (Y q) = g (Y q)) : f = g :=
  algHom_ext_of_tower (fun _ => by simp) hX hY

/-- Universal property of `SlabAlgebra R q` for ring homomorphisms: a ring map `φ : R →+* A`
together with elements `x, y : A` satisfying `x * y = φ q` induces `SlabAlgebra R q →+* A`. -/
def liftRingHom {A : Type*} [CommRing A] {q : R} (φ : R →+* A) (x y : A)
    (hxy : x * y = φ q) : SlabAlgebra R q →+* A :=
  Ideal.Quotient.lift (slabIdeal R q)
    (MvPolynomial.eval₂Hom φ fun v => SlabGenerator.casesOn v x y) fun _ hp =>
      RingHom.mem_ker.mp <| (Ideal.span_singleton_le_iff_mem _).mpr
        (by simp [RingHom.mem_ker, hxy]) hp

@[simp] theorem liftRingHom_algebraMap {A : Type*} [CommRing A] {q : R} (φ : R →+* A) (x y : A)
    (hxy : x * y = φ q) (r : R) :
    liftRingHom φ x y hxy (algebraMap R (SlabAlgebra R q) r) = φ r :=
  (Ideal.Quotient.lift_mk (slabIdeal R q) _ _).trans (MvPolynomial.eval₂Hom_C _ _ r)

@[simp] theorem liftRingHom_X {A : Type*} [CommRing A] {q : R} (φ : R →+* A) (x y : A)
    (hxy : x * y = φ q) : liftRingHom φ x y hxy (X q) = x := by
  rw [liftRingHom, X, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']

@[simp] theorem liftRingHom_Y {A : Type*} [CommRing A] {q : R} (φ : R →+* A) (x y : A)
    (hxy : x * y = φ q) : liftRingHom φ x y hxy (Y q) = y := by
  rw [liftRingHom, Y, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']

/-- Universal property of `SlabAlgebra R q` over a base semiring `K`: a `K`-algebra map
`φ : R →ₐ[K] A` and elements `x, y : A` satisfying `x * y = φ q` induce
`SlabAlgebra R q →ₐ[K] A`. -/
def liftAlgHom {K A : Type*} [CommSemiring K] [Algebra K R] [CommRing A] [Algebra K A]
    {q : R} (φ : R →ₐ[K] A) (x y : A) (hxy : x * y = φ q) : SlabAlgebra R q →ₐ[K] A where
  toRingHom := liftRingHom φ.toRingHom x y hxy
  commutes' k := by
    rw [IsScalarTower.algebraMap_apply K R (SlabAlgebra R q), RingHom.toMonoidHom_eq_coe,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_ofClass, liftRingHom_algebraMap]
    exact φ.commutes k

@[simp] theorem liftAlgHom_algebraMap {K A : Type*} [CommSemiring K] [Algebra K R] [CommRing A]
    [Algebra K A] {q : R} (φ : R →ₐ[K] A) (x y : A) (hxy : x * y = φ q) (r : R) :
    liftAlgHom φ x y hxy (algebraMap R (SlabAlgebra R q) r) = φ r :=
  liftRingHom_algebraMap φ.toRingHom x y hxy r

@[simp] theorem liftAlgHom_X {K A : Type*} [CommSemiring K] [Algebra K R] [CommRing A] [Algebra K A]
    {q : R} (φ : R →ₐ[K] A) (x y : A) (hxy : x * y = φ q) : liftAlgHom φ x y hxy (X q) = x :=
  liftRingHom_X φ.toRingHom x y hxy

@[simp] theorem liftAlgHom_Y {K A : Type*} [CommSemiring K] [Algebra K R] [CommRing A] [Algebra K A]
    {q : R} (φ : R →ₐ[K] A) (x y : A) (hxy : x * y = φ q) : liftAlgHom φ x y hxy (Y q) = y :=
  liftRingHom_Y φ.toRingHom x y hxy

/-- Universal property of `SlabAlgebra R q`: any pair `x, y` in an `R`-algebra `A` satisfying
`x * y = algebraMap R A q` determines a unique `R`-algebra homomorphism `SlabAlgebra R q →ₐ[R] A`.
-/
def lift {A : Type*} [CommRing A] [Algebra R A] (q : R) (x y : A)
    (hxy : x * y = algebraMap R A q) : SlabAlgebra R q →ₐ[R] A :=
  liftAlgHom (Algebra.ofId R A) x y hxy

@[simp] theorem lift_X {A : Type*} [CommRing A] [Algebra R A] (q : R) (x y : A)
    (hxy : x * y = algebraMap R A q) : lift q x y hxy (X q) = x :=
  liftAlgHom_X (Algebra.ofId R A) x y hxy

@[simp] theorem lift_Y {A : Type*} [CommRing A] [Algebra R A] (q : R) (x y : A)
    (hxy : x * y = algebraMap R A q) : lift q x y hxy (Y q) = y :=
  liftAlgHom_Y (Algebra.ofId R A) x y hxy

/-- Uniqueness of the `R`-algebra homomorphism induced by `SlabAlgebra.lift`. -/
theorem eq_lift {A : Type*} [CommRing A] [Algebra R A] {q : R} {x y : A}
    (hxy : x * y = algebraMap R A q) (f : SlabAlgebra R q →ₐ[R] A)
    (hX : f (X q) = x) (hY : f (Y q) = y) : f = lift q x y hxy :=
  algHom_ext (hX.trans (lift_X q x y hxy).symm) (hY.trans (lift_Y q x y hxy).symm)

/-- Functoriality of `SlabAlgebra` along a ring homomorphism `f : R →+* R'` sending `q` to `q'`. -/
def mapRingHom {R' : Type*} [CommRing R'] {q : R} {q' : R'} (f : R →+* R')
    (hf : f q = q') : SlabAlgebra R q →+* SlabAlgebra R' q' :=
  liftRingHom ((algebraMap R' (SlabAlgebra R' q')).comp f) (X q') (Y q') <| by
    rw [X_mul_Y, RingHom.comp_apply, hf]

@[simp] theorem mapRingHom_algebraMap {R' : Type*} [CommRing R'] {q : R} {q' : R'} (f : R →+* R')
    (hf : f q = q') (r : R) :
    mapRingHom f hf (algebraMap R (SlabAlgebra R q) r) = algebraMap R' (SlabAlgebra R' q') (f r) :=
  liftRingHom_algebraMap _ _ _ _ r

@[simp] theorem mapRingHom_X {R' : Type*} [CommRing R'] {q : R} {q' : R'} (f : R →+* R')
    (hf : f q = q') : mapRingHom f hf (X q) = X q' :=
  liftRingHom_X _ _ _ _

@[simp] theorem mapRingHom_Y {R' : Type*} [CommRing R'] {q : R} {q' : R'} (f : R →+* R')
    (hf : f q = q') : mapRingHom f hf (Y q) = Y q' :=
  liftRingHom_Y _ _ _ _

@[simp] theorem mapRingHom_id (q : R) :
    mapRingHom (RingHom.id R) rfl = RingHom.id (SlabAlgebra R q) :=
  ringHom_ext (fun _ => by simp) (by simp) (by simp)

theorem mapRingHom_comp {R' R'' : Type*} [CommRing R'] [CommRing R''] {q : R} {q' : R'} {q'' : R''}
    (g : R' →+* R'') (hg : g q' = q'') (f : R →+* R') (hf : f q = q') :
    (mapRingHom g hg).comp (mapRingHom f hf) =
      mapRingHom (g.comp f) (by rw [RingHom.comp_apply, hf, hg]) :=
  ringHom_ext (fun _ => by simp) (by simp) (by simp)

/-- Functoriality of `SlabAlgebra` along a `K`-algebra homomorphism `f : R →ₐ[K] R'` sending `q`
to `q'`. -/
def mapAlgHom {K R' : Type*} [CommSemiring K] [Algebra K R] [CommRing R'] [Algebra K R']
    {q : R} {q' : R'} (f : R →ₐ[K] R') (hf : f q = q') : SlabAlgebra R q →ₐ[K] SlabAlgebra R' q' :=
  liftAlgHom ((IsScalarTower.toAlgHom K R' (SlabAlgebra R' q')).comp f) (X q') (Y q') (by simp [hf])

@[simp] theorem coe_mapAlgHom {K R' : Type*} [CommSemiring K] [Algebra K R] [CommRing R']
    [Algebra K R'] {q : R} {q' : R'} (f : R →ₐ[K] R') (hf : f q = q') :
    (mapAlgHom f hf : SlabAlgebra R q →+* SlabAlgebra R' q') = mapRingHom f.toRingHom hf :=
  ringHom_ext (fun _ => by simp [mapAlgHom]) (by simp [mapAlgHom]) (by simp [mapAlgHom])

@[simp] theorem mapAlgHom_algebraMap {K R' : Type*} [CommSemiring K] [Algebra K R] [CommRing R']
    [Algebra K R'] {q : R} {q' : R'} (f : R →ₐ[K] R') (hf : f q = q') (r : R) :
    mapAlgHom f hf (algebraMap R (SlabAlgebra R q) r) = algebraMap R' (SlabAlgebra R' q') (f r) :=
  liftAlgHom_algebraMap _ _ _ _ r

@[simp] theorem mapAlgHom_X {K R' : Type*} [CommSemiring K] [Algebra K R] [CommRing R']
    [Algebra K R'] {q : R} {q' : R'} (f : R →ₐ[K] R') (hf : f q = q') :
    mapAlgHom f hf (X q) = X q' :=
  liftAlgHom_X _ _ _ _

@[simp] theorem mapAlgHom_Y {K R' : Type*} [CommSemiring K] [Algebra K R] [CommRing R']
    [Algebra K R'] {q : R} {q' : R'} (f : R →ₐ[K] R') (hf : f q = q') :
    mapAlgHom f hf (Y q) = Y q' :=
  liftAlgHom_Y _ _ _ _

/-- The involutive `R`-algebra automorphism of `SlabAlgebra R q` exchanging `X q` and `Y q`. -/
def swap (q : R) : SlabAlgebra R q ≃ₐ[R] SlabAlgebra R q :=
  AlgEquiv.ofAlgHom (lift q (Y q) (X q) (Y_mul_X q)) (lift q (Y q) (X q) (Y_mul_X q))
    (by ext <;> simp) (by ext <;> simp)

@[simp] theorem swap_X (q : R) : swap q (X q) = Y q := lift_X q (Y q) (X q) (Y_mul_X q)

@[simp] theorem swap_Y (q : R) : swap q (Y q) = X q := lift_Y q (Y q) (X q) (Y_mul_X q)

@[simp] theorem swap_symm (q : R) : (swap q).symm = swap q := (rfl)

@[simp] theorem swap_swap (q : R) (z : SlabAlgebra R q) : swap q (swap q z) = z :=
  (swap q).symm_apply_apply z

/-! ### Normal-form monomials and multiplication law -/

/-- The normal-form monomial `Z q n` in `SlabAlgebra R q`: `X q ^ (-n)` for `n < 0`, `1` for
`n = 0`, and `Y q ^ n` for `n > 0`. -/
def Z (q : R) (n : ℤ) : SlabAlgebra R q := if n < 0 then X q ^ n.natAbs else Y q ^ n.natAbs

@[simp] theorem Z_zero (q : R) : Z q 0 = 1 := by simp [Z]

theorem Z_of_neg (q : R) {n : ℤ} (hn : n < 0) : Z q n = X q ^ n.natAbs := by simp [Z, hn]

theorem Z_of_nonneg (q : R) {n : ℤ} (hn : 0 ≤ n) : Z q n = Y q ^ n.natAbs := by
  simp [Z, not_lt.mpr hn]

@[simp] theorem Z_natCast (q : R) (a : ℕ) : Z q (a : ℤ) = Y q ^ a := by simp [Z]

@[simp] theorem Z_neg_natCast (q : R) (a : ℕ) : Z q (-(a : ℤ)) = X q ^ a := by
  rcases eq_or_ne a 0 with rfl | ha <;> simp [Z, Nat.pos_of_ne_zero, *]

@[simp] theorem Z_one (q : R) : Z q 1 = Y q := by simpa using Z_natCast q 1

@[simp] theorem Z_neg_one (q : R) : Z q (-1) = X q := by simpa using Z_neg_natCast q 1

@[simp] theorem swap_Z (q : R) (n : ℤ) : swap q (Z q n) = Z q (-n) := by
  rcases Int.eq_nat_or_neg n with ⟨a, rfl | rfl⟩ <;> simp

@[simp] theorem mapRingHom_Z {R' : Type*} [CommRing R'] {q : R} {q' : R'} (f : R →+* R')
    (hf : f q = q') (n : ℤ) : mapRingHom f hf (Z q n) = Z q' n := by
  unfold Z; split_ifs <;> simp

@[simp] theorem mapAlgHom_Z {K R' : Type*} [CommSemiring K] [Algebra K R] [CommRing R']
    [Algebra K R'] {q : R} {q' : R'} (f : R →ₐ[K] R') (hf : f q = q') (n : ℤ) :
    mapAlgHom f hf (Z q n) = Z q' n :=
  mapRingHom_Z f.toRingHom hf n

/-- Mixed powers of `X q` and `Y q` cancel `min a b` pairs against the relation `X * Y = q`. -/
theorem X_pow_mul_Y_pow (q : R) (a b : ℕ) :
    X q ^ a * Y q ^ b = q ^ min a b • Z q ((b : ℤ) - (a : ℤ)) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    cases b with
    | zero => simpa using (Z_neg_natCast q (a + 1)).symm
    | succ b =>
      have hsub : ((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) := by omega
      calc
        X q ^ (a + 1) * Y q ^ (b + 1) = (X q * Y q) * (X q ^ a * Y q ^ b) := by ring
        _ = (q * q ^ min a b) • Z q ((b : ℤ) - (a : ℤ)) := by
          rw [X_mul_Y, ih b, ← Algebra.smul_def, smul_smul]
        _ = q ^ min (a + 1) (b + 1) • Z q (((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ)) := by
          rw [Nat.succ_min_succ, pow_succ', hsub]

/-- Normal-form product law in `SlabAlgebra R q`: for all `n, m : ℤ`,
`Z q n * Z q m = q ^ ((|n| + |m| - |n + m|) / 2) • Z q (n + m)`. -/
theorem Z_mul_Z (q : R) (n m : ℤ) :
    Z q n * Z q m = q ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) • Z q (n + m) := by
  rcases Int.eq_nat_or_neg n with ⟨a, rfl | rfl⟩ <;>
    rcases Int.eq_nat_or_neg m with ⟨b, rfl | rfl⟩
  · have hr : ((a : ℤ).natAbs + (b : ℤ).natAbs - ((a : ℤ) + (b : ℤ)).natAbs) / 2 = 0 := by omega
    rw [hr, pow_zero, one_smul, Z_natCast, Z_natCast, ← pow_add, ← Nat.cast_add, Z_natCast]
  · have hr : ((a : ℤ).natAbs + (-(b : ℤ)).natAbs - ((a : ℤ) + -(b : ℤ)).natAbs) / 2 =
        min b a := by omega
    rw [Z_natCast, Z_neg_natCast, mul_comm, X_pow_mul_Y_pow, hr, sub_eq_add_neg, add_comm]
  · have hr : ((-(a : ℤ)).natAbs + (b : ℤ).natAbs - (-(a : ℤ) + (b : ℤ)).natAbs) / 2 =
        min a b := by omega
    rw [Z_neg_natCast, Z_natCast, X_pow_mul_Y_pow, hr, sub_eq_neg_add]
  · have hr : ((-(a : ℤ)).natAbs + (-(b : ℤ)).natAbs - (-(a : ℤ) + -(b : ℤ)).natAbs) / 2 = 0 := by
      omega
    have hsum : -(a : ℤ) + -(b : ℤ) = -((a + b : ℕ) : ℤ) := by omega
    rw [hr, pow_zero, one_smul, Z_neg_natCast, Z_neg_natCast, ← pow_add, hsum, Z_neg_natCast]

/-- Multiplying `Z q n` on the left by `X q` shifts the index down by `1`, picking up `q` when
`0 < n`. -/
theorem X_mul_Z (q : R) (n : ℤ) :
    X q * Z q n = if n ≤ 0 then Z q (n - 1) else q • Z q (n - 1) := by
  rw [← Z_neg_one, Z_mul_Z, neg_add_eq_sub]
  split_ifs with hn
  · have hr : ((-1 : ℤ).natAbs + n.natAbs - (n - 1).natAbs) / 2 = 0 := by omega
    rw [hr, pow_zero, one_smul]
  · have hr : ((-1 : ℤ).natAbs + n.natAbs - (n - 1).natAbs) / 2 = 1 := by omega
    rw [hr, pow_one]

/-- Multiplying `Z q n` on the left by `Y q` shifts the index up by `1`, picking up `q` when
`n < 0`. -/
theorem Y_mul_Z (q : R) (n : ℤ) :
    Y q * Z q n = if 0 ≤ n then Z q (n + 1) else q • Z q (n + 1) := by
  apply (swap q).injective
  rw [map_mul, swap_Y, swap_Z, X_mul_Z]
  split_ifs <;> first | omega | simp [sub_eq_add_neg, add_comm]

/-! ### Chamber homomorphisms, normal-form basis, and joint injectivity -/

/-- Left chamber `R`-algebra homomorphism `SlabAlgebra R q →ₐ[R] LaurentPolynomial R` sending
`X q ↦ T 1` and `Y q ↦ C q * T (-1)`. -/
def chamberLeft (q : R) : SlabAlgebra R q →ₐ[R] LaurentPolynomial R :=
  lift q (LaurentPolynomial.T 1) (LaurentPolynomial.C q * LaurentPolynomial.T (-1)) <| by
    rw [mul_left_comm, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one, LaurentPolynomial.C_eq_algebraMap]

/-- Right chamber `R`-algebra homomorphism `SlabAlgebra R q →ₐ[R] LaurentPolynomial R` sending
`X q ↦ C q * T (-1)` and `Y q ↦ T 1`. -/
def chamberRight (q : R) : SlabAlgebra R q →ₐ[R] LaurentPolynomial R :=
  lift q (LaurentPolynomial.C q * LaurentPolynomial.T (-1)) (LaurentPolynomial.T 1) <| by
    rw [LaurentPolynomial.mul_T_assoc, neg_add_cancel, LaurentPolynomial.T_zero, mul_one,
      LaurentPolynomial.C_eq_algebraMap]

@[simp] theorem chamberLeft_X (q : R) : chamberLeft q (X q) = LaurentPolynomial.T 1 :=
  lift_X _ _ _ _

@[simp] theorem chamberLeft_Y (q : R) :
    chamberLeft q (Y q) = LaurentPolynomial.C q * LaurentPolynomial.T (-1) :=
  lift_Y _ _ _ _

@[simp] theorem chamberRight_X (q : R) :
    chamberRight q (X q) = LaurentPolynomial.C q * LaurentPolynomial.T (-1) :=
  lift_X _ _ _ _

@[simp] theorem chamberRight_Y (q : R) : chamberRight q (Y q) = LaurentPolynomial.T 1 :=
  lift_Y _ _ _ _

@[simp] theorem chamberRight_comp_swap (q : R) :
    (chamberRight q).comp (swap q).toAlgHom = chamberLeft q := by ext <;> simp

@[simp] theorem chamberLeft_comp_swap (q : R) :
    (chamberLeft q).comp (swap q).toAlgHom = chamberRight q := by ext <;> simp

@[simp] theorem chamberRight_swap (q : R) (z : SlabAlgebra R q) :
    chamberRight q (swap q z) = chamberLeft q z :=
  AlgHom.congr_fun (chamberRight_comp_swap q) z

@[simp] theorem chamberLeft_swap (q : R) (z : SlabAlgebra R q) :
    chamberLeft q (swap q z) = chamberRight q z :=
  AlgHom.congr_fun (chamberLeft_comp_swap q) z

@[simp] theorem chamberLeft_X_pow (q : R) (a : ℕ) :
    chamberLeft q (X q ^ a) = LaurentPolynomial.T (a : ℤ) := by
  rw [map_pow, chamberLeft_X, LaurentPolynomial.T_pow, mul_one]

@[simp] theorem chamberRight_Y_pow (q : R) (a : ℕ) :
    chamberRight q (Y q ^ a) = LaurentPolynomial.T (a : ℤ) := by
  rw [map_pow, chamberRight_Y, LaurentPolynomial.T_pow, mul_one]

@[simp] theorem chamberRight_X_pow (q : R) (a : ℕ) :
    chamberRight q (X q ^ a) = LaurentPolynomial.C (q ^ a) * LaurentPolynomial.T (-(a : ℤ)) := by
  rw [map_pow, chamberRight_X, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.single_pow, nsmul_eq_mul, mul_neg, mul_one,
    LaurentPolynomial.single_eq_C_mul_T]

@[simp] theorem chamberLeft_Y_pow (q : R) (a : ℕ) :
    chamberLeft q (Y q ^ a) = LaurentPolynomial.C (q ^ a) * LaurentPolynomial.T (-(a : ℤ)) := by
  rw [← swap_X, ← map_pow, chamberLeft_swap, chamberRight_X_pow]

/-- Image of a normal-form monomial `Z q n` in the left chamber algebra. -/
theorem chamberLeft_Z (q : R) (n : ℤ) :
    chamberLeft q (Z q n) =
      LaurentPolynomial.C (if 0 < n then q ^ n.natAbs else 1) * LaurentPolynomial.T (-n) := by
  rcases Int.eq_nat_or_neg n with ⟨a, rfl | rfl⟩
  · rcases eq_or_ne a 0 with rfl | ha <;> simp [Nat.pos_of_ne_zero, *]
  · simp [not_lt.mpr (Int.natCast_nonneg a)]

/-- Image of a normal-form monomial `Z q n` in the right chamber algebra. -/
theorem chamberRight_Z (q : R) (n : ℤ) :
    chamberRight q (Z q n) =
      LaurentPolynomial.C (if n < 0 then q ^ n.natAbs else 1) * LaurentPolynomial.T n := by
  rw [← chamberLeft_swap, swap_Z, chamberLeft_Z, neg_neg, Int.natAbs_neg]; simp only [neg_pos]

private theorem coeff_chamberLeft_Z_of_nonpos (q : R) {n : ℤ} (hn : n ≤ 0) (m : ℤ) :
    (chamberLeft q (Z q m)).coeff (-n) = if m = n then 1 else 0 := by
  rw [chamberLeft_Z, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  by_cases hmn : m = n
  · subst hmn; simp [not_lt.mpr hn]
  · simp [hmn, neg_injective.ne hmn]

private theorem coeff_chamberRight_Z_of_nonneg (q : R) {n : ℤ} (hn : 0 ≤ n) (m : ℤ) :
    (chamberRight q (Z q m)).coeff n = if m = n then 1 else 0 := by
  rw [← chamberLeft_swap, swap_Z]
  simpa [neg_inj] using coeff_chamberLeft_Z_of_nonpos q (Int.neg_nonpos_of_nonneg hn) (-m)

private theorem coeff_chamberLeft_linearCombination_of_nonpos (q : R) (l : ℤ →₀ R) {n : ℤ}
    (hn : n ≤ 0) : (chamberLeft q (Finsupp.linearCombination R (Z q) l)).coeff (-n) = l n := by
  induction l using Finsupp.induction with
  | zero => simp
  | single_add m r l _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, map_add, map_smul, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, AddMonoidAlgebra.coeff_smul_apply, coeff_chamberLeft_Z_of_nonpos q hn m,
      ih, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hmn : m = n <;> simp [hmn]

private theorem coeff_chamberRight_linearCombination_of_nonneg (q : R) (l : ℤ →₀ R) {n : ℤ}
    (hn : 0 ≤ n) : (chamberRight q (Finsupp.linearCombination R (Z q) l)).coeff n = l n := by
  induction l using Finsupp.induction with
  | zero => simp
  | single_add m r l _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, map_add, map_smul, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, AddMonoidAlgebra.coeff_smul_apply, coeff_chamberRight_Z_of_nonneg q hn m,
      ih, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hmn : m = n <;> simp [hmn]

/-- The normal-form monomials `Z q : ℤ → SlabAlgebra R q` are `R`-linearly independent for every
commutative ring `R` and parameter `q : R`. -/
theorem linearIndependent_Z (q : R) : LinearIndependent R (Z q) := by
  rw [linearIndependent_iff]; intro l hl; ext n
  rcases le_total n 0 with hn | hn
  · rw [Finsupp.zero_apply, ← coeff_chamberLeft_linearCombination_of_nonpos q l hn, hl, map_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · rw [Finsupp.zero_apply, ← coeff_chamberRight_linearCombination_of_nonneg q l hn, hl, map_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The normal-form monomials `Z q` span `SlabAlgebra R q` as an `R`-module. -/
theorem span_range_Z (q : R) : Submodule.span R (Set.range (Z q)) = ⊤ := by
  rw [eq_top_iff]
  have hX_mem : ∀ z ∈ Submodule.span R (Set.range (Z q)),
      X q * z ∈ Submodule.span R (Set.range (Z q)) := fun z hz => by
    refine Submodule.span_induction ?_ (by simp)
      (fun u v _ _ hu hv => by rw [mul_add]; exact add_mem hu hv)
      (fun r u _ hu => by rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu) hz
    rintro _ ⟨n, rfl⟩
    rw [X_mul_Z]; split_ifs
    · exact Submodule.subset_span ⟨n - 1, rfl⟩
    · exact Submodule.smul_mem _ q (Submodule.subset_span ⟨n - 1, rfl⟩)
  have hswap : ∀ z ∈ Submodule.span R (Set.range (Z q)),
      swap q z ∈ Submodule.span R (Set.range (Z q)) := fun z hz =>
    Submodule.span_induction (fun _ ⟨n, hn⟩ => hn ▸ swap_Z q n ▸ Submodule.subset_span ⟨-n, rfl⟩)
      (by simp) (fun _ _ _ _ hu hv => by rw [map_add]; exact add_mem hu hv)
      (fun r _ _ hu => by rw [map_smul]; exact Submodule.smul_mem _ r hu) hz
  rintro z -
  obtain ⟨p, rfl⟩ := mk_surjective q z
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.algHom_C, Algebra.algebraMap_eq_smul_one, ← Z_zero q]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨0, rfl⟩)
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | mul_X f v hf =>
    cases v
    · rw [map_mul, mk_X, mul_comm]; exact hX_mem _ hf
    · rw [map_mul, mk_Y, mul_comm, ← swap_swap q (Y q * mk q f), map_mul, swap_Y]
      exact hswap _ (hX_mem _ (hswap _ hf))

/-- The normal-form `R`-basis of `SlabAlgebra R q` indexed by `ℤ`, sending `n` to `Z q n`
(`X q ^ (-n)` for `n < 0`, `1` for `n = 0`, and `Y q ^ n` for `0 < n`). -/
def basis (q : R) : Module.Basis ℤ R (SlabAlgebra R q) :=
  Module.Basis.mk (linearIndependent_Z q) (span_range_Z q).ge

@[simp] theorem basis_apply (q : R) (n : ℤ) : basis q n = Z q n :=
  Module.Basis.mk_apply (linearIndependent_Z q) (span_range_Z q).ge n

@[simp] theorem coe_basis (q : R) : ⇑(basis q) = Z q := funext (basis_apply q)

@[simp] theorem basis_repr_Z (q : R) (n : ℤ) : (basis q).repr (Z q n) = Finsupp.single n 1 := by
  rw [← basis_apply, Module.Basis.repr_self]

instance (q : R) : Module.Free R (SlabAlgebra R q) := Module.Free.of_basis (basis q)

/-- Over a nontrivial commutative ring, every normal-form monomial `Z q n` is nonzero. -/
theorem Z_ne_zero [Nontrivial R] (q : R) (n : ℤ) : Z q n ≠ 0 :=
  basis_apply q n ▸ (basis q).ne_zero n

/-- For `n ≤ 0`, the `n`-th coordinate of `z` in `basis q` is the `(-n)`-th Laurent coefficient of
`chamberLeft q z`. -/
theorem basis_repr_of_nonpos (q : R) (z : SlabAlgebra R q) {n : ℤ} (hn : n ≤ 0) :
    (basis q).repr z n = (chamberLeft q z).coeff (-n) := by
  conv_rhs => rw [← (basis q).linearCombination_repr z, coe_basis]
  exact (coeff_chamberLeft_linearCombination_of_nonpos q ((basis q).repr z) hn).symm

/-- For `0 ≤ n`, the `n`-th coordinate of `z` in `basis q` is the `n`-th Laurent coefficient of
`chamberRight q z`. -/
theorem basis_repr_of_nonneg (q : R) (z : SlabAlgebra R q) {n : ℤ} (hn : 0 ≤ n) :
    (basis q).repr z n = (chamberRight q z).coeff n := by
  conv_rhs => rw [← (basis q).linearCombination_repr z, coe_basis]
  exact (coeff_chamberRight_linearCombination_of_nonneg q ((basis q).repr z) hn).symm

/-- The two chamber homomorphisms out of `SlabAlgebra R q` are jointly injective for any
commutative ring `R` and any parameter `q : R`. -/
theorem chamberLeft_prod_chamberRight_injective (q : R) :
    Function.Injective (fun z => (chamberLeft q z, chamberRight q z)) := by
  intro z w h
  obtain ⟨hL, hR⟩ := Prod.mk.inj h
  apply (basis q).repr.injective; ext n
  rcases le_total n 0 with hn | hn
  · rw [basis_repr_of_nonpos q z hn, basis_repr_of_nonpos q w hn, hL]
  · rw [basis_repr_of_nonneg q z hn, basis_repr_of_nonneg q w hn, hR]

/-- Linear-map form of joint injectivity of `chamberLeft q` and `chamberRight q`. -/
theorem chamberLeft_linearProd_chamberRight_injective (q : R) :
    Function.Injective ((chamberLeft q).toLinearMap.prod (chamberRight q).toLinearMap) :=
  chamberLeft_prod_chamberRight_injective q

end Basic

end SlabAlgebra

end TauCeti
