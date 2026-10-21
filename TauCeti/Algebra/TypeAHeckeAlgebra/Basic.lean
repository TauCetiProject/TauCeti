/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic
import Mathlib.Tactic.Module

/-!
# The finite type-A Hecke algebra by generators and relations

For a commutative ring `R` and a unit `q : Rˣ`, the type-A Hecke algebra
`TypeAHeckeAlgebra R q n` on `n` strands is the associative unital `R`-algebra on generators
`T 0, …, T (n - 2)` subject to

* the quadratic relation `T i * T i = (q - q⁻¹) • T i + 1`, equivalently
  `(T i - q) * (T i + q⁻¹) = 0`,
* the braid relation `T i * T j * T i = T j * T i * T j` when `|i - j| = 1`, and
* distant commutation `T i * T j = T j * T i` when `|i - j| ≥ 2`.

It is built as the quotient of the free algebra by these relations, which makes the universal
property `TauCeti.TypeAHeckeAlgebra.lift` available. Everything else in this file is a consequence
of that universal property: the generators are units, so the elementary braids map to them
(`TauCeti.TypeAHeckeAlgebra.braidHom`); adding an uncrossed last strand gives the tower map
`TauCeti.TypeAHeckeAlgebra.strandIncl`; the presentation is functorial in the coefficient ring
(`TauCeti.TypeAHeckeAlgebra.map`) and admits the sign twist `T i ↦ -T i` between the parameters
`q` and `-q` (`TauCeti.TypeAHeckeAlgebra.negEquiv`).

## Conventions

The algebra is indexed by the number `n` of *strands*, so its generators are indexed by
`Fin (n - 1)`, matching `TauCeti.BraidGroup n`. In particular the algebras on `0` and `1` strands
are the base ring (`TauCeti.TypeAHeckeAlgebra.algEquivOfLeOne`).

The quadratic relation is normalized so that the two eigenvalues of each generator are `q` and
`-q⁻¹`. At `q = 1` it reads `T i * T i = 1`, and the presentation becomes the Coxeter presentation
of the group algebra of the symmetric group. Rescaling `g i = q • T i` gives the other common
normalization `(g i + 1) * (g i - q ^ 2) = 0`, and `T i - (T i)⁻¹ = q - q⁻¹` is the skein
normalization of `TauCeti.BraidGroup.heckeSkein` with `z = q - q⁻¹`.

## Non-degeneracy

The two eigenvalues give two algebra maps to the base ring, the index character `T i ↦ q` and the
sign character `T i ↦ -q⁻¹`. The first shows that the base ring embeds
(`TauCeti.TypeAHeckeAlgebra.algebraMap_injective`); comparing both shows that a generator is not
a scalar as soon as `q ≠ -q⁻¹` (`TauCeti.TypeAHeckeAlgebra.T_ne_algebraMap`). The basis theorem,
that the algebra is free of rank `n!` on elements `T w` indexed by permutations, needs the
reduced-word theory of the symmetric group and is not proved here.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.Rel`: the defining relations on the free algebra.
* `TauCeti.TypeAHeckeAlgebra`: the type-A Hecke algebra on `n` strands with parameter `q`.
* `TauCeti.TypeAHeckeAlgebra.T`: the generators, and `TauCeti.TypeAHeckeAlgebra.unitT` the
  same generators as units.
* `TauCeti.TypeAHeckeAlgebra.lift`: the universal property.
* `TauCeti.TypeAHeckeAlgebra.braidHom`: the canonical homomorphism from the braid group to the
  units.
* `TauCeti.TypeAHeckeAlgebra.strandIncl`: the tower map adding an uncrossed last strand.
* `TauCeti.TypeAHeckeAlgebra.indexCharacter` and `TauCeti.TypeAHeckeAlgebra.signCharacter`: the
  two one-dimensional representations.
* `TauCeti.TypeAHeckeAlgebra.map`: change of coefficients.
* `TauCeti.TypeAHeckeAlgebra.negEquiv`: the sign twist between parameters `q` and `-q`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.T_mul_self`, `TauCeti.TypeAHeckeAlgebra.T_braid` and
  `TauCeti.TypeAHeckeAlgebra.commute_T`: the defining relations.
* `TauCeti.TypeAHeckeAlgebra.lift_T` and `TauCeti.TypeAHeckeAlgebra.hom_ext`: the computation
  rule and uniqueness half of the universal property.
* `TauCeti.TypeAHeckeAlgebra.span_range_braidHom`: the braids span the algebra as an `R`-module.
* `TauCeti.TypeAHeckeAlgebra.strandIncl_braidHom`: the tower maps of braid groups and Hecke
  algebras are compatible.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 4.
* M. Geck, G. Pfeiffer, *Characters of finite Coxeter groups and Iwahori-Hecke algebras*,
  London Math. Soc. Monographs 21, Oxford University Press (2000), Chapter 4.
* The quotient presentation and universal-property API follow the construction pattern in
  `Mathlib.LinearAlgebra.CliffordAlgebra.Basic` and in `TauCeti.Algebra.TemperleyLieb.Basic`.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R] (q : Rˣ) (n : ℕ)

namespace TypeAHeckeAlgebra

/-- The defining relations of the type-A Hecke algebra on `n` strands with parameter `q`, as a
relation on the free algebra over the generators `Fin (n - 1)`: the quadratic relation
`T i * T i = (q - q⁻¹) • T i + 1`, the braid relation for adjacent generators and commutation of
distant generators. Each of the last two is imposed for one ordering of the pair, which suffices
since the quotient relation is symmetric. -/
inductive Rel : FreeAlgebra R (Fin (n - 1)) → FreeAlgebra R (Fin (n - 1)) → Prop
  | mul_self (i : Fin (n - 1)) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R i)
        (((q : R) - ↑q⁻¹) • FreeAlgebra.ι R i + 1)
  | braid {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R j * FreeAlgebra.ι R i)
        (FreeAlgebra.ι R j * FreeAlgebra.ι R i * FreeAlgebra.ι R j)
  | distant {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R j) (FreeAlgebra.ι R j * FreeAlgebra.ι R i)

end TypeAHeckeAlgebra

/-- The type-A Hecke algebra on `n` strands over `R` with parameter `q`: the free `R`-algebra on
`Fin (n - 1)` modulo `TauCeti.TypeAHeckeAlgebra.Rel`. -/
@[expose] def TypeAHeckeAlgebra : Type _ := RingQuot (TypeAHeckeAlgebra.Rel R q n)

instance : Ring (TypeAHeckeAlgebra R q n) :=
  inferInstanceAs (Ring (RingQuot (TypeAHeckeAlgebra.Rel R q n)))

/-- The type-A Hecke algebra over `R` is an algebra over every ring that `R` is an algebra over.
This is the instance that change of coefficients restricts scalars along. -/
instance (priority := 900) TypeAHeckeAlgebra.instAlgebra' {S : Type*} [CommSemiring S]
    [Algebra S R] : Algebra S (TypeAHeckeAlgebra R q n) :=
  inferInstanceAs (Algebra S (RingQuot (TypeAHeckeAlgebra.Rel R q n)))

instance : Algebra R (TypeAHeckeAlgebra R q n) := inferInstance

instance {S T : Type*} [CommSemiring S] [CommSemiring T] [SMul S T] [Algebra S R] [Algebra T R]
    [IsScalarTower S T R] : IsScalarTower S T (TypeAHeckeAlgebra R q n) :=
  inferInstanceAs (IsScalarTower S T (RingQuot (TypeAHeckeAlgebra.Rel R q n)))

namespace TypeAHeckeAlgebra

/-- The quotient map from the free algebra to the type-A Hecke algebra. -/
def mkAlgHom : FreeAlgebra R (Fin (n - 1)) →ₐ[R] TypeAHeckeAlgebra R q n :=
  RingQuot.mkAlgHom R (Rel R q n)

variable {R n}

/-- The generator `T i` of the type-A Hecke algebra, the image of the elementary braid crossing
the strands `i` and `i + 1`. -/
def T (i : Fin (n - 1)) : TypeAHeckeAlgebra R q n :=
  mkAlgHom R q n (FreeAlgebra.ι R i)

variable {q}

/-- The quotient map takes each free-algebra generator to the corresponding Hecke generator. -/
@[simp]
theorem mkAlgHom_ι (i : Fin (n - 1)) : mkAlgHom R q n (FreeAlgebra.ι R i) = T q i := (rfl)

/-- Every element of the type-A Hecke algebra is represented by a free-algebra element. -/
theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom R q n) :=
  RingQuot.mkAlgHom_surjective _ _

/-- Related elements of the free algebra have the same image in the type-A Hecke algebra. -/
theorem mkAlgHom_rel {x y : FreeAlgebra R (Fin (n - 1))} (h : Rel R q n x y) :
    mkAlgHom R q n x = mkAlgHom R q n y :=
  RingQuot.mkAlgHom_rel R h

/-- The quadratic relation of a Hecke generator. -/
@[simp]
theorem T_mul_self (i : Fin (n - 1)) : T q i * T q i = ((q : R) - ↑q⁻¹) • T q i + 1 := by
  simpa only [map_mul, map_add, map_smul, map_one, mkAlgHom_ι] using
    mkAlgHom_rel (Rel.mul_self (q := q) i)

/-- The quadratic relation in factored form: each generator is annihilated by the polynomial with
roots `q` and `-q⁻¹`. -/
theorem T_sub_algebraMap_mul_T_add_algebraMap_eq_zero (i : Fin (n - 1)) :
    (T q i - algebraMap R _ (q : R)) * (T q i + algebraMap R _ (↑q⁻¹ : R)) = 0 := by
  have hq : algebraMap R (TypeAHeckeAlgebra R q n) (q : R) * algebraMap R _ (↑q⁻¹ : R) = 1 := by
    simp [← map_mul]
  simp only [sub_mul, mul_add, T_mul_self, ← Algebra.commutes _ (T q i), hq,
    Algebra.smul_def, map_sub]
  abel

/-- Two generators on adjacent pairs of strands satisfy the braid relation. -/
theorem T_braid {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    T q i * T q j * T q i = T q j * T q i * T q j := by
  rcases h with h | h
  · simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Rel.braid (R := R) (q := q) h)
  · simpa only [map_mul, mkAlgHom_ι] using (mkAlgHom_rel (Rel.braid (R := R) (q := q) h)).symm

/-- Two generators on disjoint pairs of strands commute. -/
theorem commute_T {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (T q i) (T q j) := by
  rw [commute_iff_eq]
  rcases h with h | h
  · simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Rel.distant (R := R) (q := q) h)
  · simpa only [map_mul, mkAlgHom_ι] using (mkAlgHom_rel (Rel.distant (R := R) (q := q) h)).symm

section Units

variable (q) in
/-- The generator `T i` as a unit. Its inverse is `T i - (q - q⁻¹)`, by the quadratic
relation. -/
def unitT (i : Fin (n - 1)) : (TypeAHeckeAlgebra R q n)ˣ where
  val := T q i
  inv := T q i - algebraMap R _ ((q : R) - ↑q⁻¹)
  val_inv := by
    rw [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, T_mul_self, add_sub_cancel_left]
  inv_val := by
    rw [sub_mul, ← Algebra.smul_def, T_mul_self, add_sub_cancel_left]

/-- The underlying element of `unitT q i` is the generator `T q i`. -/
@[simp]
theorem val_unitT (i : Fin (n - 1)) : (unitT q i : TypeAHeckeAlgebra R q n) = T q i := (rfl)

/-- The inverse of a generator is `T i - (q - q⁻¹)`. -/
@[simp]
theorem val_inv_unitT (i : Fin (n - 1)) :
    (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) = T q i - algebraMap R _ ((q : R) - ↑q⁻¹) :=
  (rfl)

/-- Each generator of the type-A Hecke algebra is a unit. -/
theorem isUnit_T (i : Fin (n - 1)) : IsUnit (T q i) := (unitT q i).isUnit

end Units

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- The universal property of the type-A Hecke presentation: a family in an `R`-algebra
satisfying the quadratic relation, the braid relation for adjacent indices and commutation for
distant indices extends to an algebra map out of `TypeAHeckeAlgebra R q n`. -/
def lift (f : Fin (n - 1) → A) (hself : ∀ i, f i * f i = ((q : R) - ↑q⁻¹) • f i + 1)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → f i * f j * f i = f j * f i * f j)
    (hdist : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j → f i * f j = f j * f i) :
    TypeAHeckeAlgebra R q n →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R f, by
    rintro x y (i | @⟨i, j, h⟩ | @⟨i, j, h⟩)
    · simpa only [map_mul, map_add, map_smul, map_one, FreeAlgebra.lift_ι_apply] using hself i
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply] using hbraid h
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply] using hdist h⟩

/-- The algebra map built by `TauCeti.TypeAHeckeAlgebra.lift` takes each generator to its
prescribed value. -/
@[simp]
theorem lift_T (f : Fin (n - 1) → A) (hself) (hbraid) (hdist) (i : Fin (n - 1)) :
    lift (q := q) f hself hbraid hdist (T q i) = f i :=
  (RingQuot.liftAlgHom_mkAlgHom_apply R _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

/-- Two algebra maps out of the type-A Hecke algebra agreeing on the generators are equal. -/
@[ext high]
theorem hom_ext {F G : TypeAHeckeAlgebra R q n →ₐ[R] A} (h : ∀ i, F (T q i) = G (T q i)) :
    F = G :=
  RingQuot.ringQuot_ext' R F G <| FreeAlgebra.hom_ext (funext h)

end Lift

/-- The generators generate the type-A Hecke algebra as an `R`-algebra. -/
theorem adjoin_range_T : Algebra.adjoin R (Set.range (T q (n := n))) = ⊤ := by
  have hrange : Set.range (T q (n := n))
      = mkAlgHom R q n '' Set.range (FreeAlgebra.ι R (X := Fin (n - 1))) := by
    simp only [← Set.range_comp, Function.comp_def, mkAlgHom_ι]
  rw [hrange, ← AlgHom.map_adjoin, FreeAlgebra.adjoin_range_ι, Algebra.map_top]
  exact (AlgHom.range_eq_top _).2 mkAlgHom_surjective

section Braid

variable (R q n) in
/-- The canonical homomorphism from the braid group on `n` strands to the units of the type-A
Hecke algebra, sending the elementary braid `σ i` to the generator `T i`. -/
def braidHom : BraidGroup n →* (TypeAHeckeAlgebra R q n)ˣ :=
  BraidGroup.lift (unitT q) (fun h ↦ Units.ext (commute_T h).eq) (fun h ↦ Units.ext (T_braid h))

/-- The braid homomorphism sends each elementary braid to the corresponding generator. -/
@[simp]
theorem braidHom_sigma (i : Fin (n - 1)) : braidHom R q n (BraidGroup.sigma i) = unitT q i :=
  BraidGroup.lift_sigma _ _ _ i

/-- The images of the braids span the type-A Hecke algebra as an `R`-module: a linear map out of
the Hecke algebra is determined by its values on braids. -/
theorem span_range_braidHom :
    Submodule.span R (Set.range fun b ↦ (braidHom R q n b : TypeAHeckeAlgebra R q n)) = ⊤ := by
  set M : Submonoid (TypeAHeckeAlgebra R q n) :=
    MonoidHom.mrange ((Units.coeHom _).comp (braidHom R q n))
  have hM : (M : Set (TypeAHeckeAlgebra R q n))
      = Set.range fun b ↦ (braidHom R q n b : TypeAHeckeAlgebra R q n) := by
    simp [M, MonoidHom.coe_mrange, Function.comp_def]
  rw [← hM, ← Submonoid.closure_eq M, ← Algebra.adjoin_eq_span, Algebra.toSubmodule_eq_top,
    eq_top_iff, ← adjoin_range_T (q := q)]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨BraidGroup.sigma i, by simp⟩

end Braid

section StrandIncl

variable (R q n) in
/-- The algebra map from the type-A Hecke algebra on `n + 1` strands to the one on `n + 2`
strands that adds an uncrossed last strand: each generator is sent to the generator of the same
index. -/
def strandIncl : TypeAHeckeAlgebra R q (n + 1) →ₐ[R] TypeAHeckeAlgebra R q (n + 2) :=
  lift (fun i : Fin n ↦ T q i.castSucc) (fun _ ↦ T_mul_self _)
    (fun h ↦ T_braid (Or.inl (by simpa using h)))
    (fun h ↦ (commute_T (Or.inl (by simpa using h))).eq)

/-- The strand inclusion sends each generator to the generator of the same index. -/
@[simp]
theorem strandIncl_T (i : Fin n) : strandIncl R q n (T q i) = T q i.castSucc := by
  rw [strandIncl, lift_T]

/-- The strand inclusions of braid groups and of type-A Hecke algebras are compatible with the
braid homomorphisms. -/
@[simp]
theorem strandIncl_braidHom (b : BraidGroup (n + 1)) :
    strandIncl R q n (braidHom R q (n + 1) b) = braidHom R q (n + 2) (BraidGroup.strandIncl b) := by
  have h : (Units.map (strandIncl R q n : _ →* _)).comp (braidHom R q (n + 1))
      = (braidHom R q (n + 2)).comp BraidGroup.strandIncl :=
    BraidGroup.hom_ext fun i ↦ Units.ext (by simp)
  exact congrArg Units.val (DFunLike.congr_fun h b)

end StrandIncl

section Characters

variable (R q n) in
/-- The index character of the type-A Hecke algebra, the algebra map to the base ring sending
every generator to the eigenvalue `q`. At `q = 1` it is the trivial representation of the
symmetric group. -/
def indexCharacter : TypeAHeckeAlgebra R q n →ₐ[R] R :=
  lift (fun _ ↦ (q : R)) (fun _ ↦ by simp [smul_eq_mul, sub_mul]) (fun _ ↦ rfl) (fun _ ↦ rfl)

variable (R q n) in
/-- The sign character of the type-A Hecke algebra, the algebra map to the base ring sending
every generator to the eigenvalue `-q⁻¹`. At `q = 1` it is the sign representation of the
symmetric group. -/
def signCharacter : TypeAHeckeAlgebra R q n →ₐ[R] R :=
  lift (fun _ ↦ -(↑q⁻¹ : R)) (fun _ ↦ by simp [smul_eq_mul, sub_mul]) (fun _ ↦ rfl)
    (fun _ ↦ rfl)

/-- The index character sends each generator to `q`. -/
@[simp]
theorem indexCharacter_T (i : Fin (n - 1)) : indexCharacter R q n (T q i) = q :=
  lift_T _ _ _ _ i

/-- The sign character sends each generator to `-q⁻¹`. -/
@[simp]
theorem signCharacter_T (i : Fin (n - 1)) : signCharacter R q n (T q i) = -(↑q⁻¹ : R) :=
  lift_T _ _ _ _ i

/-- The base ring embeds into the type-A Hecke algebra. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (TypeAHeckeAlgebra R q n)) :=
  fun x y hxy ↦ by simpa using congrArg (indexCharacter R q n) hxy

instance [Nontrivial R] : Nontrivial (TypeAHeckeAlgebra R q n) :=
  algebraMap_injective.nontrivial

/-- A generator is not a scalar when the two eigenvalues `q` and `-q⁻¹` are distinct. -/
theorem T_ne_algebraMap (hq : (q : R) ≠ -↑q⁻¹) (i : Fin (n - 1)) (r : R) :
    T q i ≠ algebraMap R _ r := fun h ↦
  hq <| by
    rw [← indexCharacter_T (n := n) i, ← signCharacter_T (n := n) i, h, AlgHom.commutes,
      AlgHom.commutes]

/-- Over a nontrivial base ring, no generator vanishes. -/
theorem T_ne_zero [Nontrivial R] (i : Fin (n - 1)) : T q i ≠ 0 :=
  (isUnit_T i).ne_zero

end Characters

section SmallCases

variable (R q) in
/-- On at most one strand there are no generators, so the type-A Hecke algebra is the base ring.
This matches the triviality of `TauCeti.BraidGroup 0` and `TauCeti.BraidGroup 1`. -/
def algEquivOfLeOne (h : n ≤ 1) : TypeAHeckeAlgebra R q n ≃ₐ[R] R :=
  have : IsEmpty (Fin (n - 1)) := ⟨fun i ↦ absurd i.isLt (by omega)⟩
  AlgEquiv.ofAlgHom (indexCharacter R q n) (Algebra.ofId R _) (AlgHom.ext fun x ↦ by simp)
    (hom_ext fun i ↦ isEmptyElim i)

/-- On at most one strand, the forward map of `algEquivOfLeOne` is the index character. -/
@[simp]
theorem algEquivOfLeOne_apply (h : n ≤ 1) (x : TypeAHeckeAlgebra R q n) :
    algEquivOfLeOne R q h x = indexCharacter R q n x := (rfl)

/-- On at most one strand, the inverse of `algEquivOfLeOne` is the algebra structure map. -/
@[simp]
theorem algEquivOfLeOne_symm_apply (h : n ≤ 1) (r : R) :
    (algEquivOfLeOne R q h).symm r = algebraMap R (TypeAHeckeAlgebra R q n) r := (rfl)

end SmallCases

section Map

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Change of coefficients along `algebraMap R S`: the algebra map from the type-A Hecke algebra
over `R` with parameter `q` to the one over `S` with parameter `q'`, the image of `q`, sending
each generator to the generator of the same index. -/
def map (q' : Sˣ) (h : algebraMap R S q = q') :
    TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra S q' n :=
  lift (fun i ↦ T q' i)
    (fun i ↦ by
      obtain rfl : q' = Units.map (algebraMap R S : R →* S) q := Units.ext h.symm
      rw [T_mul_self, ← algebraMap_smul S ((q : R) - ↑q⁻¹), map_sub]
      simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_ofClass])
    (fun h ↦ T_braid (Or.inl h)) (fun h ↦ (commute_T (Or.inl h)).eq)

/-- Change of coefficients sends each generator to the generator of the same index. -/
@[simp]
theorem map_T (q' : Sˣ) (h : algebraMap R S q = q') (i : Fin (n - 1)) :
    map q' h (T q i) = T q' i :=
  lift_T _ _ _ _ i

/-- Change of coefficients along the identity is the identity. -/
@[simp]
theorem map_self (h : algebraMap R R q = q) : map (n := n) q h = AlgHom.id R _ :=
  hom_ext fun i ↦ by simp

/-- Change of coefficients is functorial: changing coefficients from `R` to `S` and then to `S'`
is the change of coefficients from `R` to `S'`. -/
theorem map_comp_map {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S'] (q' : Sˣ) (q'' : S'ˣ) (h : algebraMap R S q = q')
    (h' : algebraMap S S' q' = q'') :
    ((map q'' h').restrictScalars R).comp (map (n := n) q' h)
      = map q'' (by rw [IsScalarTower.algebraMap_apply R S S', h, h']) :=
  hom_ext fun i ↦ by simp

end Map

section Neg

/-- The algebra map from the type-A Hecke algebra with parameter `q` to the one with parameter
`q' = -q` sending `T i` to `-T i`. -/
private def negHom (q' : Rˣ) (h : -q = q') :
    TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra R q' n :=
  lift (fun i ↦ -T q' i)
    (fun i ↦ by
      subst h
      simp only [neg_mul_neg, T_mul_self, inv_neg, Units.val_neg, smul_neg]
      module)
    (fun h ↦ by simp only [mul_neg, neg_mul, T_braid (Or.inl h)])
    (fun h ↦ by simp only [neg_mul_neg, (commute_T (Or.inl h)).eq])

private theorem negHom_T (q' : Rˣ) (h : -q = q') (i : Fin (n - 1)) :
    negHom q' h (T q i) = -T q' i :=
  lift_T _ _ _ _ i

variable (R q n) in
/-- The sign twist: the type-A Hecke algebras with parameters `q` and `-q` are isomorphic by
`T i ↦ -T i`. Both parameters give the same quadratic relation up to this sign. -/
def negEquiv : TypeAHeckeAlgebra R q n ≃ₐ[R] TypeAHeckeAlgebra R (-q) n :=
  AlgEquiv.ofAlgHom (negHom (-q) rfl) (negHom q (neg_neg q))
    (hom_ext fun i ↦ by simp [negHom_T]) (hom_ext fun i ↦ by simp [negHom_T])

/-- The sign twist sends `T i` to `-T i`. -/
@[simp]
theorem negEquiv_T (i : Fin (n - 1)) : negEquiv R q n (T q i) = -T (-q) i :=
  negHom_T _ _ i

/-- The inverse of the sign twist sends `T i` to `-T i`. -/
@[simp]
theorem negEquiv_symm_T (i : Fin (n - 1)) : (negEquiv R q n).symm (T (-q) i) = -T q i :=
  negHom_T _ _ i

end Neg

end TypeAHeckeAlgebra

end TauCeti
