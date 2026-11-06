/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import TauCeti.RingTheory.DiscreteValuationRing.AdjoinRoot
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.KummerPolynomial
import TauCeti.Algebra.CharP.Two
import TauCeti.RingTheory.LocalRing.Quotient

/-!
# A fierce biquadratic extension of a discrete valuation ring

Let `A` be a discrete valuation ring of characteristic two with uniformizer `t` and residue field
`k`, and let `s, u ∈ A` have residues `s₀, u₀ ∈ k` that are `2`-independent over `k`: `s₀` is
not a square in `k`, and `u₀` is not a square in `k(√s₀)`, that is `u₀ ≠ a ^ 2 + s₀ b ^ 2` for
all `a, b ∈ k`. For instance `A = k[t]` localized at `t`, or `A = k[[t]]`, with `k = 𝔽₂(s, u)`.
Put

`B = A[y, z]`, with `y ^ 2 + t y = s` and `z ^ 2 + t z = u`.

Then:

* `B` is a discrete valuation ring, finite free of rank `4` over `A`, and `t` is a uniformizer of
  `B`, so the ramification index is `e = 1`;
* the residue field of `B` is `k(√s₀, √u₀)`, purely inseparable of degree `4` over `k`;
* the `A`-algebra automorphisms of `B` are the four translations `y ↦ y + ε t`, `z ↦ z + δ t`
  with `ε, δ ∈ {0, 1}`, and form a Klein four-group;
* every automorphism acts trivially on the residue field, so the inertia group `G_0` is the whole
  group, while a nontrivial automorphism moves `y` or `z` by `t`, which does not lie in the square
  of the maximal ideal, so `G_1` is trivial.

So the inertia group has order `4` although `e = 1`: the residue field extension is purely
inseparable of degree `f_ins = 4`, and `|G_0| = e f_ins`. This is a **fierce** extension, one
whose residue field extension is purely inseparable of degree equal to the degree `[B : A] = 4`,
and the classical equality `|G_0| = e`, valid when the residue field extension is separable, fails
for it. The same example tests the formulas for the different exponent, which are not computed
here: Hilbert's formula `d = ∑ (|G_i| - 1)` also needs a separable residue field extension.

Each quadratic step is a ring `R[X] ⧸ (g)` with `g` monic with irreducible but inseparable
reduction, and is a discrete valuation ring by
`Polynomial.Monic.isDiscreteValuationRing_adjoinRoot`.

## Main definitions

* `TauCeti.FierceBiquadratic.quadratic t s`: the polynomial `X ^ 2 + t X - s`.
* `TauCeti.FierceBiquadratic.RingY t s`: the ring `A[y] = A[Y] ⧸ (Y ^ 2 + t Y - s)`.
* `TauCeti.FierceBiquadratic.RingYZ t s u`: the ring `B = A[y][Z] ⧸ (Z ^ 2 + t Z - u)`.
* `TauCeti.FierceBiquadratic.y`, `TauCeti.FierceBiquadratic.z`: its generators.
* `TauCeti.FierceBiquadratic.lift`: the `A`-algebra homomorphism out of `B` determined by roots
  of the two defining quadratics.
* `TauCeti.FierceBiquadratic.translateEquiv`: the translation automorphism `y ↦ y + a`,
  `z ↦ z + b` of `B`, for `a (a + t) = 0` and `b (b + t) = 0`.

## Main results

* `TauCeti.FierceBiquadratic.isDiscreteValuationRing_ringYZ`: `B` is a discrete valuation ring.
* `TauCeti.FierceBiquadratic.irreducible_algebraMap_ringYZ`: `t` is a uniformizer of `B`.
* `Module.Free A B` and `Module.Finite A B` instances, and
  `TauCeti.FierceBiquadratic.finrank_ringYZ`: `B` is finite free of rank `4` over `A`.
* `TauCeti.FierceBiquadratic.finrank_residueField_ringYZ` and
  `TauCeti.FierceBiquadratic.isPurelyInseparable_residueField_ringYZ`: the residue field extension
  is purely inseparable of degree `4`.
* `TauCeti.FierceBiquadratic.natCard_algEquiv` and
  `TauCeti.FierceBiquadratic.algEquiv_sq_eq_one`: `Aut_A(B)` has four elements, all involutions.
* `TauCeti.FierceBiquadratic.isKleinFour_algEquiv`: `Aut_A(B)` is a Klein four-group.
* `TauCeti.FierceBiquadratic.ramificationGroup_zero_eq_top` and
  `TauCeti.FierceBiquadratic.ramificationGroup_one_eq_bot`: `G_0 = Aut_A(B)` and `G_1 = 1`.

## References

* I. B. Fesenko, S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., AMS, 2002, for
  ferociously ramified extensions, those whose residue field extension is purely inseparable of
  degree equal to the degree of the extension.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter IV, §1, for the lower ramification
  groups `G_i = {σ | ∀ x ∈ B, v_B (σ x - x) ≥ i + 1}`.
-/

public section

open Polynomial IsLocalRing

namespace TauCeti.FierceBiquadratic

variable {R : Type*} [CommRing R]

/-- The polynomial `X ^ 2 + t X - s`. In a ring of characteristic two without zero divisors, two
distinct roots differ by `t`, by `TauCeti.eq_or_eq_add_of_sq_add_mul_eq_of_charTwo`. -/
noncomputable def quadratic (t s : R) : R[X] := X ^ 2 + C t * X - C s

/-- `X ^ 2 + t X - s` is monic. -/
@[simp]
theorem monic_quadratic (t s : R) : (quadratic t s).Monic := by
  unfold quadratic
  monicity!

/-- `X ^ 2 + t X - s` has degree `2`. -/
@[simp]
theorem natDegree_quadratic [Nontrivial R] (t s : R) : (quadratic t s).natDegree = 2 := by
  unfold quadratic
  compute_degree!

@[simp]
theorem map_quadratic {S : Type*} [CommRing S] (f : R →+* S) (t s : R) :
    (quadratic t s).map f = quadratic (f t) (f s) := by
  simp [quadratic]

@[simp]
theorem eval₂_quadratic {S : Type*} [CommRing S] (f : R →+* S) (t s : R) (x : S) :
    (quadratic t s).eval₂ f x = x ^ 2 + f t * x - f s := by
  simp [quadratic]

/-- Over a local ring, if `t` lies in the maximal ideal and the residue of `s` is not a square,
then the reduction of `X ^ 2 + t X - s` is irreducible. -/
theorem irreducible_map_residue_quadratic [IsLocalRing R] {t s : R} (ht : t ∈ maximalIdeal R)
    (hs : ∀ a : ResidueField R, a ^ 2 ≠ residue R s) :
    Irreducible ((quadratic t s).map (residue R)) := by
  simpa [quadratic, (residue_eq_zero_iff t).mpr ht] using
    irreducible_X_pow_sub_C_of_prime Nat.prime_two hs

variable {A : Type*} [CommRing A]

/-- The ring `A[y] = A[Y] ⧸ (Y ^ 2 + t Y - s)`. -/
abbrev RingY (t s : A) : Type _ := AdjoinRoot (quadratic t s)

/-- The ring `B = A[y, z] = A[y][Z] ⧸ (Z ^ 2 + t Z - u)`, with `y ^ 2 + t y = s` in `A[y]`. -/
abbrev RingYZ (t s u : A) : Type _ :=
  AdjoinRoot (quadratic (algebraMap A (RingY t s) t) (algebraMap A (RingY t s) u))

section Free

variable {t s u : A}

/-- `A[y]` is free over `A`, with basis `1, y`. -/
instance : Module.Free A (RingY t s) := (monic_quadratic t s).free_adjoinRoot

instance : Module.Finite A (RingY t s) := (monic_quadratic t s).finite_adjoinRoot

/-- `B` is free over `A[y]`, with basis `1, z`. -/
instance : Module.Free (RingY t s) (RingYZ t s u) := (monic_quadratic _ _).free_adjoinRoot

instance : Module.Finite (RingY t s) (RingYZ t s u) := (monic_quadratic _ _).finite_adjoinRoot

/-- `B` is free over `A`, with basis `1, y, z, y z`. -/
instance : Module.Free A (RingYZ t s u) := .trans (S := RingY t s)

instance : Module.Finite A (RingYZ t s u) := .trans (RingY t s) _

end Free

section Generators

variable (t s u : A)

/-- The generator `y` of `B = A[y, z]`, with `y ^ 2 + t y = s`. -/
noncomputable def y : RingYZ t s u := algebraMap (RingY t s) (RingYZ t s u) (AdjoinRoot.root _)

/-- The generator `z` of `B = A[y, z]`, with `z ^ 2 + t z = u`. -/
noncomputable def z : RingYZ t s u := AdjoinRoot.root _

/-- `y` is a root of `Y ^ 2 + t Y - s`. -/
theorem y_sq_add_mul_y :
    y t s u ^ 2 + algebraMap A (RingYZ t s u) t * y t s u = algebraMap A (RingYZ t s u) s := by
  have h := AdjoinRoot.eval₂_root (quadratic t s)
  rw [eval₂_quadratic, sub_eq_zero] at h
  simpa [y, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply] using
    congr(algebraMap (RingY t s) (RingYZ t s u) $h)

/-- `z` is a root of `Z ^ 2 + t Z - u`. -/
theorem z_sq_add_mul_z :
    z t s u ^ 2 + algebraMap A (RingYZ t s u) t * z t s u = algebraMap A (RingYZ t s u) u := by
  have h := AdjoinRoot.eval₂_root
    (quadratic (algebraMap A (RingY t s) t) (algebraMap A (RingY t s) u))
  rw [eval₂_quadratic, sub_eq_zero] at h
  simpa [z, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply] using h

/-- `B = A[y, z]` is generated by `y` and `z` as an `A`-algebra. -/
theorem adjoin_y_z : Algebra.adjoin A {y t s u, z t s u} = ⊤ := by
  have := Algebra.adjoin_eq_adjoin_union (R := A) {AdjoinRoot.root (quadratic t s)}
    {z t s u} AdjoinRoot.adjoinRoot_eq_top
  rw [z, AdjoinRoot.adjoinRoot_eq_top, Subalgebra.restrictScalars_top, Set.image_singleton,
    Set.singleton_union] at this
  exact this.symm

/-- Two `A`-algebra homomorphisms out of `B = A[y, z]` agreeing on `y` and `z` are equal. -/
theorem algHom_ext {C : Type*} [Semiring C] [Algebra A C] {f g : RingYZ t s u →ₐ[A] C}
    (hy : f (y t s u) = g (y t s u)) (hz : f (z t s u) = g (z t s u)) : f = g :=
  AlgHom.ext_of_adjoin_eq_top (adjoin_y_z t s u) (by rintro _ (rfl | rfl) <;> assumption)

/-- The `A`-algebra homomorphism `B → C` with `y ↦ y'` and `z ↦ z'`, for a root `y'` of
`Y ^ 2 + t Y - s` and a root `z'` of `Z ^ 2 + t Z - u` in a commutative `A`-algebra `C`. It is
unique by `algHom_ext`. -/
noncomputable def lift {C : Type*} [CommRing C] [Algebra A C] (y' z' : C)
    (hy : y' ^ 2 + algebraMap A C t * y' = algebraMap A C s)
    (hz : z' ^ 2 + algebraMap A C t * z' = algebraMap A C u) : RingYZ t s u →ₐ[A] C :=
  AdjoinRoot.liftAlgHom _
    (AdjoinRoot.liftAlgHom (quadratic t s) (Algebra.ofId A C) y' (by simpa [sub_eq_zero] using hy))
    z' (by simpa [sub_eq_zero] using hz)

@[simp]
theorem lift_y {C : Type*} [CommRing C] [Algebra A C] (y' z' : C) (hy hz) :
    lift t s u y' z' hy hz (y t s u) = y' := by
  -- `y` is the image of the root of `A[y]`, and `algebraMap A[y] B` is `AdjoinRoot.of` by `rfl`.
  exact (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)

@[simp]
theorem lift_z {C : Type*} [CommRing C] [Algebra A C] (y' z' : C) (hy hz) :
    lift t s u y' z' hy hz (z t s u) = z' :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `B` is free of rank `4` over `A`. -/
theorem finrank_ringYZ [Nontrivial A] : Module.finrank A (RingYZ t s u) = 4 := by
  have : Nontrivial (RingY t s) := (AdjoinRoot.nontrivial_iff_of_monic (monic_quadratic t s)).mpr
    (by rw [degree_eq_natDegree (monic_quadratic t s).ne_zero, natDegree_quadratic]; decide)
  rw [← Module.finrank_mul_finrank A (RingY t s),
    (AdjoinRoot.powerBasis' (monic_quadratic t s)).finrank,
    (AdjoinRoot.powerBasis' (monic_quadratic (algebraMap A (RingY t s) t) _)).finrank,
    AdjoinRoot.powerBasis'_dim, AdjoinRoot.powerBasis'_dim, natDegree_quadratic,
    natDegree_quadratic]

variable [CharP A 2]

/-- Every square in `B` is congruent to an element of `A` modulo `t`: in characteristic two,
squaring is additive, and `y ^ 2 ≡ s`, `z ^ 2 ≡ u`. -/
theorem exists_sq_sub_algebraMap_mem_span (x : RingYZ t s u) :
    ∃ a : A, x ^ 2 - algebraMap A _ a ∈ Ideal.span {algebraMap A (RingYZ t s u) t} := by
  set I := Ideal.span {algebraMap A (RingYZ t s u) t}
  -- The elements whose square is congruent to an element of `A` form a subalgebra.
  let S : Subalgebra A (RingYZ t s u) :=
    { carrier := {x | ∃ a : A, x ^ 2 - algebraMap A _ a ∈ I}
      mul_mem' := by
        rintro x x' ⟨a, ha⟩ ⟨a', ha'⟩
        refine ⟨a * a', ?_⟩
        have : (x * x') ^ 2 - algebraMap A _ (a * a') =
            x ^ 2 * (x' ^ 2 - algebraMap A _ a') + algebraMap A _ a' * (x ^ 2 - algebraMap A _ a) :=
          by rw [map_mul]; ring
        rw [this]
        exact I.add_mem (I.mul_mem_left _ ha') (I.mul_mem_left _ ha)
      add_mem' := by
        rintro x x' ⟨a, ha⟩ ⟨a', ha'⟩
        refine ⟨a + a', ?_⟩
        have : (x + x') ^ 2 - algebraMap A _ (a + a') =
            (x ^ 2 - algebraMap A _ a) + (x' ^ 2 - algebraMap A _ a') + (x * x' + x * x') := by
          rw [map_add]; ring
        rw [this, TauCeti.add_self_eq_zero_of_charTwo A, add_zero]
        exact I.add_mem ha ha'
      algebraMap_mem' := fun a ↦ ⟨a ^ 2, by simp⟩ }
  have hy : y t s u ∈ S := ⟨s, by
    rw [← y_sq_add_mul_y, sub_add_cancel_left, neg_mem_iff]
    exact I.mul_mem_right _ (Ideal.mem_span_singleton_self _)⟩
  have hz : z t s u ∈ S := ⟨u, by
    rw [← z_sq_add_mul_z, sub_add_cancel_left, neg_mem_iff]
    exact I.mul_mem_right _ (Ideal.mem_span_singleton_self _)⟩
  have : Algebra.adjoin A {y t s u, z t s u} ≤ S :=
    Algebra.adjoin_le (Set.insert_subset_iff.mpr ⟨hy, Set.singleton_subset_iff.mpr hz⟩)
  exact this ((adjoin_y_z t s u).symm ▸ Algebra.mem_top)

/-- In characteristic two, if `x` is a root of `X ^ 2 + t X - r` and `a (a + t) = 0`, then
`x + a` is again a root. -/
private theorem add_algebraMap_sq_add_mul {x : RingYZ t s u} {r a : A}
    (hx : x ^ 2 + algebraMap A _ t * x = algebraMap A _ r) (ha : a * (a + t) = 0) :
    (x + algebraMap A _ a) ^ 2 + algebraMap A _ t * (x + algebraMap A _ a) = algebraMap A _ r := by
  have ha' : algebraMap A (RingYZ t s u) a * (algebraMap A _ a + algebraMap A _ t) = 0 := by
    rw [← map_add, ← map_mul, ha, map_zero]
  linear_combination hx + ha' + TauCeti.add_self_eq_zero_of_charTwo A (x * algebraMap A _ a)

/-- In characteristic two, `y ↦ y + a`, `z ↦ z + b` defines an `A`-algebra endomorphism of `B`
when `a (a + t) = 0` and `b (b + t) = 0`, that is when `y + a` and `z + b` are again roots. -/
private noncomputable def translate (a b : A) (ha : a * (a + t) = 0) (hb : b * (b + t) = 0) :
    RingYZ t s u →ₐ[A] RingYZ t s u :=
  lift t s u (y t s u + algebraMap A _ a) (z t s u + algebraMap A _ b)
    (add_algebraMap_sq_add_mul t s u (y_sq_add_mul_y t s u) ha)
    (add_algebraMap_sq_add_mul t s u (z_sq_add_mul_z t s u) hb)

private theorem translate_y (a b : A) (ha hb) :
    translate t s u a b ha hb (y t s u) = y t s u + algebraMap A _ a :=
  lift_y ..

private theorem translate_z (a b : A) (ha hb) :
    translate t s u a b ha hb (z t s u) = z t s u + algebraMap A _ b :=
  lift_z ..

/-- The `A`-algebra automorphism `y ↦ y + a`, `z ↦ z + b` of `B`, when `a (a + t) = 0` and
`b (b + t) = 0`. In characteristic two it is an involution. Taking `a, b ∈ {0, t}` translates
each generator by `0` or `t`; these four choices give distinct automorphisms when `t` is nonzero
in `B`, as under the hypotheses of `natCard_algEquiv`. -/
noncomputable def translateEquiv (a b : A) (ha : a * (a + t) = 0)
    (hb : b * (b + t) = 0) : RingYZ t s u ≃ₐ[A] RingYZ t s u :=
  have h : (translate t s u a b ha hb).comp (translate t s u a b ha hb) = .id A _ :=
    algHom_ext t s u (AlgHom.apply_apply_of_apply_eq_add_algebraMap _ (translate_y t s u a b ha hb))
      (AlgHom.apply_apply_of_apply_eq_add_algebraMap _ (translate_z t s u a b ha hb))
  .ofAlgHom _ _ h h

@[simp]
theorem translateEquiv_apply_y (a b : A) (ha : a * (a + t) = 0) (hb : b * (b + t) = 0) :
    translateEquiv t s u a b ha hb (y t s u) = y t s u + algebraMap A _ a :=
  translate_y t s u a b ha hb

@[simp]
theorem translateEquiv_apply_z (a b : A) (ha : a * (a + t) = 0) (hb : b * (b + t) = 0) :
    translateEquiv t s u a b ha hb (z t s u) = z t s u + algebraMap A _ b :=
  translate_z t s u a b ha hb

end Generators

section PurelyInseparable

variable [IsLocalRing A] [CharP A 2] {t s u : A}

/-- **The residue field extension is purely inseparable**: the square of every element of `B` is
congruent to an element of `A` modulo `t`. -/
theorem isPurelyInseparable_residueField_ringYZ (ht : t ∈ maximalIdeal A)
    [IsLocalRing (RingYZ t s u)] [IsLocalHom (algebraMap A (RingYZ t s u))] :
    IsPurelyInseparable (ResidueField A) (ResidueField (RingYZ t s u)) := by
  have : CharP (ResidueField A) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (one_add_one_eq_two (R := ResidueField A) ▸ TauCeti.add_self_eq_zero_of_charTwo A 1)
  refine (isPurelyInseparable_iff_pow_mem _ 2).mpr fun c ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective c
  obtain ⟨a, ha⟩ := exists_sq_sub_algebraMap_mem_span t s u x
  refine ⟨1, residue A a, ?_⟩
  rw [pow_one, ResidueField.algebraMap_residue, ← map_pow, eq_comm, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff]
  exact (Ideal.span_singleton_le_iff_mem _).mpr (map_nonunit _ _ ht) ha

end PurelyInseparable

/-! ### `B` is a local ring with residue field of degree `4` -/

section LocalRing

variable [IsLocalRing A] {t s u : A}
  (ht : t ∈ maximalIdeal A) (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
include ht hs

private theorem isLocalRing_ringY : IsLocalRing (RingY t s) :=
  (monic_quadratic t s).isLocalRing_adjoinRoot (irreducible_map_residue_quadratic ht hs)

variable [CharP A 2] (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u)
include hu

/-- The residue of `u` is not a square in the residue field of `A[y]`: the squares there are
the residues of `a ^ 2 + s b ^ 2` with `a, b ∈ A`, since `(a + b y) ^ 2 = a ^ 2 + b ^ 2 (s - t y)`.
So the second quadratic has irreducible reduction. -/
private theorem irreducible_map_residue_quadratic_ringYZ [IsLocalRing (RingY t s)] :
    Irreducible ((quadratic (algebraMap A (RingY t s) t) (algebraMap A (RingY t s) u)).map
      (residue (RingY t s))) := by
  have : IsLocalHom (algebraMap A (RingY t s)) :=
    AdjoinRoot.isLocalHom_algebraMap (irreducible_map_residue_quadratic ht hs)
  refine irreducible_map_residue_quadratic (map_nonunit _ _ ht) fun c hc ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective c
  obtain ⟨f, hf, rfl⟩ := (AdjoinRoot.powerBasis' (monic_quadratic t s)).exists_eq_aeval x
  rw [AdjoinRoot.powerBasis'_dim, natDegree_quadratic] at hf
  rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega), AdjoinRoot.powerBasis'_gen] at hc
  set a := f.coeff 0
  set b := f.coeff 1
  have hroot := AdjoinRoot.eval₂_root (quadratic t s)
  rw [eval₂_quadratic, ← AdjoinRoot.algebraMap_eq] at hroot
  have h2 := TauCeti.add_self_eq_zero_of_charTwo A (1 : RingY t s)
  set r := AdjoinRoot.root (quadratic t s)
  have key : aeval r (C b * X + C a) ^ 2 =
      algebraMap A _ (a ^ 2 + s * b ^ 2) - algebraMap A _ t * (algebraMap A _ b ^ 2 * r) := by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X]
    linear_combination algebraMap A _ b ^ 2 * hroot + algebraMap A _ a * algebraMap A _ b * r * h2
  rw [← map_pow, key] at hc
  apply hu (residue A a) (residue A b)
  apply (algebraMap (ResidueField A) (ResidueField (RingY t s))).injective
  simpa [(residue_eq_zero_iff _).mpr (map_nonunit _ _ ht), ResidueField.algebraMap_residue,
    ← AdjoinRoot.algebraMap_eq] using hc

/-- `B` is a local ring. -/
theorem isLocalRing_ringYZ : IsLocalRing (RingYZ t s u) :=
  have := isLocalRing_ringY ht hs
  (monic_quadratic _ _).isLocalRing_adjoinRoot (irreducible_map_residue_quadratic_ringYZ ht hs hu)

/-- The maximal ideal of `A` generates the maximal ideal of `B`, so `B / 𝔪_A B` is the residue
field of `B`; when `t` is a uniformizer of `A`, this is `B / t B`. -/
theorem maximalIdeal_ringYZ [IsLocalRing (RingYZ t s u)] :
    maximalIdeal (RingYZ t s u) = (maximalIdeal A).map (algebraMap A (RingYZ t s u)) := by
  have := isLocalRing_ringY ht hs
  rw [AdjoinRoot.maximalIdeal_eq_map (irreducible_map_residue_quadratic_ringYZ ht hs hu),
    AdjoinRoot.maximalIdeal_eq_map (irreducible_map_residue_quadratic ht hs), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- `A → B` is a local homomorphism. -/
theorem isLocalHom_algebraMap_ringYZ [IsLocalRing (RingYZ t s u)] :
    IsLocalHom (algebraMap A (RingYZ t s u)) :=
  ((local_hom_tfae _).out 1 3).mpr (maximalIdeal_ringYZ ht hs hu).ge

/-- **The residue field of `B` has degree `4` over that of `A`.** -/
theorem finrank_residueField_ringYZ [IsLocalRing (RingYZ t s u)]
    [IsLocalHom (algebraMap A (RingYZ t s u))] :
    Module.finrank (ResidueField A) (ResidueField (RingYZ t s u)) = 4 := by
  rw [IsLocalRing.finrank_residueField_eq_finrank (maximalIdeal_ringYZ ht hs hu).symm,
    finrank_ringYZ]

end LocalRing

/-! ### `B` is a discrete valuation ring with uniformizer `t` -/

section DiscreteValuationRing

variable [IsDomain A] [IsDiscreteValuationRing A] {t s u : A}

section Step

variable (ht : t ∈ maximalIdeal A) (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
include ht hs

/-- `A[y]` is a domain and a discrete valuation ring. -/
private theorem isDiscreteValuationRing_ringY :
    ∃ _ : IsDomain (RingY t s), IsDiscreteValuationRing (RingY t s) :=
  have := (monic_quadratic t s).isDomain_adjoinRoot (irreducible_map_residue_quadratic ht hs)
  ⟨this, (monic_quadratic t s).isDiscreteValuationRing_adjoinRoot
    (irreducible_map_residue_quadratic ht hs)⟩

variable [CharP A 2] (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u)
include hu

/-- `B` is a domain. -/
theorem isDomain_ringYZ : IsDomain (RingYZ t s u) := by
  obtain ⟨_, _⟩ := isDiscreteValuationRing_ringY ht hs
  exact (monic_quadratic _ _).isDomain_adjoinRoot
    (irreducible_map_residue_quadratic_ringYZ ht hs hu)

/-- `B` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_ringYZ [IsDomain (RingYZ t s u)] :
    IsDiscreteValuationRing (RingYZ t s u) := by
  obtain ⟨_, _⟩ := isDiscreteValuationRing_ringY ht hs
  exact (monic_quadratic _ _).isDiscreteValuationRing_adjoinRoot
    (irreducible_map_residue_quadratic_ringYZ ht hs hu)

end Step

variable [CharP A 2]

/-- **`t` is a uniformizer of `B`**: the extension `A → B` has ramification index one. -/
theorem irreducible_algebraMap_ringYZ (ht : Irreducible t)
    (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
    (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u) :
    Irreducible (algebraMap A (RingYZ t s u) t) := by
  have hmem := (mem_maximalIdeal t).mpr ht.not_isUnit
  have := isDomain_ringYZ hmem hs hu
  have := isDiscreteValuationRing_ringYZ hmem hs hu
  exact TauCeti.IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq
    (maximalIdeal_ringYZ hmem hs hu).symm ht

end DiscreteValuationRing

/-! ### The automorphisms and the ramification groups -/

section Automorphism

variable [IsDomain A] [IsDiscreteValuationRing A] [CharP A 2] {t s u : A}

section Translation

variable (ht : t ∈ maximalIdeal A) (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
  (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u)
include ht hs hu

/-- An `A`-algebra automorphism of `B` moves a root of `X ^ 2 + t X - r`, with `r ∈ A`, by `0`
or by `t`, since these are the two roots in the domain `B`. -/
private theorem algEquiv_apply_eq_or_eq_add (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u)
    {x : RingYZ t s u} {r : A}
    (hx : x ^ 2 + algebraMap A (RingYZ t s u) t * x = algebraMap A (RingYZ t s u) r) :
    σ x = x ∨ σ x = x + algebraMap A _ t := by
  have := isDomain_ringYZ ht hs hu
  have := CharP.of_ringHom_of_ne_zero (algebraMap A (RingYZ t s u)) 2 two_ne_zero
  exact TauCeti.eq_or_eq_add_of_sq_add_mul_eq_of_charTwo hx (by simpa using congr(σ $hx))

/-- Every `A`-algebra automorphism of `B` moves `y` by `0` or by `t`: these are the two roots of
`Y ^ 2 + t Y - s` in the domain `B`. -/
theorem algEquiv_apply_y (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) :
    σ (y t s u) = y t s u ∨ σ (y t s u) = y t s u + algebraMap A _ t :=
  algEquiv_apply_eq_or_eq_add ht hs hu σ (y_sq_add_mul_y t s u)

/-- Every `A`-algebra automorphism of `B` moves `z` by `0` or by `t`. -/
theorem algEquiv_apply_z (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) :
    σ (z t s u) = z t s u ∨ σ (z t s u) = z t s u + algebraMap A _ t :=
  algEquiv_apply_eq_or_eq_add ht hs hu σ (z_sq_add_mul_z t s u)

/-- **Every `A`-algebra automorphism of `B` is an involution**: it moves `y` and `z` by `0` or by
`t`, and in characteristic two moving by `t` twice is the identity. -/
theorem algEquiv_sq_eq_one (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) : σ ^ 2 = 1 := by
  have hinv {x : RingYZ t s u} (hx : σ x = x ∨ σ x = x + algebraMap A _ t) : σ (σ x) = x := by
    rcases hx with h | h
    · rw [h, h]
    · exact AlgHom.apply_apply_of_apply_eq_add_algebraMap σ.toAlgHom h
  exact AlgEquiv.coe_toAlgHom_injective <| algHom_ext t s u
    (by simpa [sq] using hinv (algEquiv_apply_y ht hs hu σ))
    (by simpa [sq] using hinv (algEquiv_apply_z ht hs hu σ))

/-- **The inertia group is everything**: every `A`-algebra automorphism of `B` acts trivially on
the residue field, since it moves the generators by multiples of `t`. -/
theorem ramificationGroup_zero_eq_top [IsLocalRing (RingYZ t s u)] :
    IsLocalRing.ramificationGroup (RingYZ t s u ≃ₐ[A] RingYZ t s u) (RingYZ t s u) 0 = ⊤ := by
  have := isLocalHom_algebraMap_ringYZ ht hs hu
  have hT : algebraMap A (RingYZ t s u) t ∈ maximalIdeal _ := map_nonunit _ _ ht
  refine eq_top_iff.mpr fun σ _ ↦
    (IsLocalRing.mem_ramificationGroup_iff_of_adjoin_eq_top (adjoin_y_z t s u)).mpr ?_
  rintro _ (rfl | rfl)
  · rcases algEquiv_apply_y ht hs hu σ with h | h <;> simp [AlgEquiv.smul_def, h, hT]
  · rcases algEquiv_apply_z ht hs hu σ with h | h <;> simp [AlgEquiv.smul_def, h, hT]

end Translation

variable (ht : Irreducible t) (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
  (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u)
include ht hs hu

/-- **`B` has exactly four `A`-algebra automorphisms**, the translations `y ↦ y + ε t`,
`z ↦ z + δ t` with `ε, δ ∈ {0, 1}`: an automorphism is determined by the images of `y` and `z`,
which are `y` or `y + t`, and `z` or `z + t`, and all four choices occur by `translateEquiv`. -/
theorem natCard_algEquiv : Nat.card (RingYZ t s u ≃ₐ[A] RingYZ t s u) = 4 := by
  have hmem := (mem_maximalIdeal t).mpr ht.not_isUnit
  have hT0 := (irreducible_algebraMap_ringYZ ht hs hu).ne_zero
  have htt : t * (t + t) = 0 := by rw [← two_mul, CharTwo.two_eq_zero, zero_mul, mul_zero]
  have h0t : (0 : A) * (0 + t) = 0 := zero_mul _
  set Y := y t s u
  set Z := z t s u
  set T := algebraMap A (RingYZ t s u) t
  let F : (RingYZ t s u ≃ₐ[A] RingYZ t s u) → RingYZ t s u × RingYZ t s u := fun σ ↦ (σ Y, σ Z)
  have hF : Function.Injective F := fun σ τ h ↦ AlgEquiv.coe_toAlgHom_injective <|
    algHom_ext t s u (congr_arg Prod.fst h) (congr_arg Prod.snd h)
  have hroot {X : RingYZ t s u} {v : RingYZ t s u} (hv : v = X ∨ v = X + T) :
      ∃ a : A, a * (a + t) = 0 ∧ v = X + algebraMap A _ a := by
    rcases hv with rfl | rfl
    · exact ⟨0, h0t, by simp⟩
    · exact ⟨t, htt, rfl⟩
  have hrange : Set.range F = {Y, Y + T} ×ˢ {Z, Z + T} := by
    ext ⟨v, w⟩
    refine ⟨?_, fun ⟨hv, hw⟩ ↦ ?_⟩
    · rintro ⟨σ, hσ⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hσ
      exact ⟨algEquiv_apply_y hmem hs hu σ, algEquiv_apply_z hmem hs hu σ⟩
    · obtain ⟨a, ha, rfl⟩ := hroot hv
      obtain ⟨b, hb, rfl⟩ := hroot hw
      exact ⟨translateEquiv t s u a b ha hb, Prod.ext (translateEquiv_apply_y t s u a b ha hb)
        (translateEquiv_apply_z t s u a b ha hb)⟩
  have hne (X : RingYZ t s u) : X ≠ X + T := fun h ↦ hT0 (by linear_combination -h)
  rw [← Set.ncard_range_of_injective hF, hrange, Set.ncard_prod, Set.ncard_pair (hne Y),
    Set.ncard_pair (hne Z)]

/-- **The `A`-algebra automorphisms of `B` form a Klein four-group**, made of the translations
`y ↦ y + ε t`, `z ↦ z + δ t` with `ε, δ ∈ {0, 1}`. -/
theorem isKleinFour_algEquiv : IsKleinFour (RingYZ t s u ≃ₐ[A] RingYZ t s u) := by
  have hcard := natCard_algEquiv ht hs hu
  have : Finite (RingYZ t s u ≃ₐ[A] RingYZ t s u) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (RingYZ t s u ≃ₐ[A] RingYZ t s u) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun σ hσ ↦
    orderOf_eq_prime (algEquiv_sq_eq_one ((mem_maximalIdeal t).mpr ht.not_isUnit) hs hu σ) hσ⟩

/-- **The first ramification group is trivial**: a nontrivial automorphism moves `y` or `z` by
the uniformizer `t`, which does not lie in the square of the maximal ideal of `B`. -/
theorem ramificationGroup_one_eq_bot [IsLocalRing (RingYZ t s u)] :
    IsLocalRing.ramificationGroup (RingYZ t s u ≃ₐ[A] RingYZ t s u) (RingYZ t s u) 1 = ⊥ := by
  have hmem := (mem_maximalIdeal t).mpr ht.not_isUnit
  have := isDomain_ringYZ hmem hs hu
  have := isDiscreteValuationRing_ringYZ hmem hs hu
  have hT : algebraMap A (RingYZ t s u) t ∉ maximalIdeal (RingYZ t s u) ^ 2 := by
    rw [TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
      TauCeti.IsDiscreteValuationRing.addVal_eq_one_iff_irreducible.mpr
        (irreducible_algebraMap_ringYZ ht hs hu)]
    norm_num
  refine eq_bot_iff.mpr fun σ hσ ↦ ?_
  rw [IsLocalRing.mem_ramificationGroup_iff_of_adjoin_eq_top (adjoin_y_z t s u)] at hσ
  have hy := hσ _ (Set.mem_insert _ _)
  have hz := hσ _ (Set.mem_insert_of_mem _ rfl)
  refine Subgroup.mem_bot.mpr (AlgEquiv.coe_toAlgHom_injective (algHom_ext t s u ?_ ?_))
  · rcases algEquiv_apply_y hmem hs hu σ with h | h
    · simpa using h
    · exact absurd (by simpa [AlgEquiv.smul_def, h] using hy) hT
  · rcases algEquiv_apply_z hmem hs hu σ with h | h
    · simpa using h
    · exact absurd (by simpa [AlgEquiv.smul_def, h] using hz) hT

end Automorphism

end TauCeti.FierceBiquadratic
