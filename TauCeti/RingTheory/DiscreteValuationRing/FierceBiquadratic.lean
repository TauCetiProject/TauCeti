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
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Set.Card
import TauCeti.RingTheory.LocalRing.Quotient

/-!
# A fierce biquadratic extension of a discrete valuation ring

Let `A` be a discrete valuation ring of characteristic two with uniformizer `t` and residue field
`k`, and let `s, u ∈ A` have residues that are `2`-independent over `k`: `s̄` is not a square in
`k`, and `ū` is not a square in `k(√s̄)`, that is `ū ≠ a ^ 2 + s̄ b ^ 2` for all `a, b ∈ k`. For
instance `A = k[t]` localized at `t`, or `A = k[[t]]`, with `k = 𝔽₂(s, u)`. Put

`B = A[y, z]`, with `y ^ 2 + t y = s` and `z ^ 2 + t z = u`.

Then:

* `B` is a discrete valuation ring, finite free of rank `4` over `A`, and `t` is a uniformizer of
  `B`, so the ramification index is `e = 1`;
* the residue field of `B` is `k(√s̄, √ū)`, purely inseparable of degree `4` over `k`;
* the `A`-algebra automorphisms of `B` are the four translations `y ↦ y + ε t`, `z ↦ z + δ t`
  with `ε, δ ∈ {0, 1}`, and form a Klein four-group;
* every automorphism acts trivially on the residue field, so the inertia group `G_0` is the whole
  group, while a nontrivial automorphism moves `y` or `z` by `t`, which does not lie in the square
  of the maximal ideal, so `G_1` is trivial.

So the inertia group has order `4` although `e = 1`: the residue field extension is purely
inseparable of degree `f_ins = 4`, and `|G_0| = e f_ins`. This is a **fierce** extension, one
whose residue field extension is inseparable, and the classical equality `|G_0| = e`, valid when
the residue field extension is separable, fails for it. The same example tests the formulas for
the different exponent, which are not computed here: Hilbert's formula `d = ∑ (|G_i| - 1)` also
needs a separable residue field extension.

Each quadratic step is a ring `R[X] ⧸ (g)` with `g` monic with irreducible but inseparable
reduction, and is a discrete valuation ring by
`Polynomial.Monic.isDiscreteValuationRing_adjoinRoot`.

## Main definitions

* `TauCeti.FierceBiquadratic.quadratic t s`: the polynomial `X ^ 2 + t X - s`.
* `TauCeti.FierceBiquadratic.RingY t s`: the ring `A[y] = A[Y] ⧸ (Y ^ 2 + t Y - s)`.
* `TauCeti.FierceBiquadratic.RingYZ t s u`: the ring `B = A[y][Z] ⧸ (Z ^ 2 + t Z - u)`.
* `TauCeti.FierceBiquadratic.y`, `TauCeti.FierceBiquadratic.z`: its generators.

## Main results

* `TauCeti.FierceBiquadratic.isDiscreteValuationRing_ringYZ`: `B` is a discrete valuation ring.
* `TauCeti.FierceBiquadratic.irreducible_algebraMap_ringYZ`: `t` is a uniformizer of `B`.
* `TauCeti.FierceBiquadratic.finrank_ringYZ`: `B` has rank `4` over `A`.
* `TauCeti.FierceBiquadratic.finrank_residueField_ringYZ` and
  `TauCeti.FierceBiquadratic.isPurelyInseparable_residueField_ringYZ`: the residue field extension
  is purely inseparable of degree `4`.
* `TauCeti.FierceBiquadratic.isKleinFour_algEquiv`: `Aut_A(B)` is a Klein four-group.
* `TauCeti.FierceBiquadratic.ramificationGroup_zero_eq_top` and
  `TauCeti.FierceBiquadratic.ramificationGroup_one_eq_bot`: `G_0 = Aut_A(B)` and `G_1 = 1`.

## References

* I. B. Fesenko, S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., AMS, 2002, for
  ferociously ramified extensions, those with inseparable residue field extension.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter IV, §1, for the lower ramification
  groups `G_i = {σ | ∀ x ∈ B, v_B (σ x - x) ≥ i + 1}`.
-/

public section

open Polynomial IsLocalRing

namespace TauCeti.FierceBiquadratic

variable {R : Type*} [CommRing R]

/-- The polynomial `X ^ 2 + t X - s`. In characteristic two its roots differ by `t`. -/
noncomputable def quadratic (t s : R) : R[X] := X ^ 2 + C t * X - C s

/-- `X ^ 2 + t X - s` is monic. -/
theorem monic_quadratic (t s : R) : (quadratic t s).Monic := by
  unfold quadratic
  monicity!

/-- `X ^ 2 + t X - s` has degree `2`. -/
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
  rw [map_quadratic, (residue_eq_zero_iff t).mpr ht,
    (monic_quadratic _ _).irreducible_iff_roots_eq_zero_of_degree_le_three
      (natDegree_quadratic _ _).ge (by rw [natDegree_quadratic]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ hs a ?_
  rw [mem_roots (monic_quadratic _ _).ne_zero, IsRoot.def, eval, eval₂_quadratic] at ha
  simpa [sub_eq_zero] using ha

/-- In a domain of characteristic two, two roots of `X ^ 2 + t X - s` are equal or differ by `t`. -/
private theorem eq_or_eq_add_of_sq_add_mul_eq {S : Type*} [CommRing S] [IsDomain S]
    (h2 : (2 : S) = 0) {t s a b : S} (ha : a ^ 2 + t * a = s) (hb : b ^ 2 + t * b = s) :
    b = a ∨ b = a + t := by
  have h : (b + a) * (b + a + t) = 0 := by linear_combination hb + ha + (a * b + s) * h2
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (by linear_combination h - a * h2)
  · exact Or.inr (by linear_combination h - (a + t) * h2)

variable {A : Type*} [CommRing A]

/-- The target of a ring homomorphism out of a ring of characteristic two has `2 = 0`. -/
private theorem two_eq_zero [CharP A 2] {B : Type*} [Semiring B] (f : A →+* B) : (2 : B) = 0 := by
  rw [← map_ofNat f 2, CharTwo.two_eq_zero, map_zero]

/-- The ring `A[y] = A[Y] ⧸ (Y ^ 2 + t Y - s)`. -/
abbrev RingY (t s : A) : Type _ := AdjoinRoot (quadratic t s)

/-- The ring `B = A[y, z] = A[y][Z] ⧸ (Z ^ 2 + t Z - u)`, with `y ^ 2 + t y = s` in `A[y]`. -/
abbrev RingYZ (t s u : A) : Type _ :=
  AdjoinRoot (quadratic (algebraMap A (RingY t s) t) (algebraMap A (RingY t s) u))

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
  have h := congr(algebraMap (RingY t s) (RingYZ t s u) $h)
  rw [map_add, map_mul, map_pow, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply] at h
  exact h

/-- `z` is a root of `Z ^ 2 + t Z - u`. -/
theorem z_sq_add_mul_z :
    z t s u ^ 2 + algebraMap A (RingYZ t s u) t * z t s u = algebraMap A (RingYZ t s u) u := by
  have h := AdjoinRoot.eval₂_root
    (quadratic (algebraMap A (RingY t s) t) (algebraMap A (RingY t s) u))
  rw [eval₂_quadratic, sub_eq_zero, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply] at h
  exact h

/-- `B = A[y, z]` is generated by `y` and `z` as an `A`-algebra. -/
theorem adjoin_y_z : Algebra.adjoin A {y t s u, z t s u} = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [← AdjoinRoot.aeval_eq, aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  refine Subalgebra.mul_mem _ ?_
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)) _)
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (p.coeff i)
  rw [← hq, ← AdjoinRoot.aeval_eq, ← aeval_algebraMap_apply]
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert (y t s u) _))
    (aeval_mem_adjoin_singleton A _)

/-- Two `A`-algebra homomorphisms out of `B = A[y, z]` agreeing on `y` and `z` are equal. -/
theorem algHom_ext {C : Type*} [Semiring C] [Algebra A C] {f g : RingYZ t s u →ₐ[A] C}
    (hy : f (y t s u) = g (y t s u)) (hz : f (z t s u) = g (z t s u)) : f = g :=
  AlgHom.ext_of_adjoin_eq_top (adjoin_y_z t s u) (by rintro _ (rfl | rfl) <;> assumption)

/-- `B` is free of rank `4` over `A`. -/
theorem finrank_ringYZ [Nontrivial A] : Module.finrank A (RingYZ t s u) = 4 := by
  have : Nontrivial (RingY t s) := (AdjoinRoot.nontrivial_iff_of_monic (monic_quadratic t s)).mpr
    (by rw [degree_eq_natDegree (monic_quadratic t s).ne_zero, natDegree_quadratic]; decide)
  have := (monic_quadratic t s).free_adjoinRoot
  have := (monic_quadratic (algebraMap A (RingY t s) t)
    (algebraMap A (RingY t s) u)).free_adjoinRoot
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
  have h2 := two_eq_zero (algebraMap A (RingYZ t s u))
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
            (x ^ 2 - algebraMap A _ a) + (x' ^ 2 - algebraMap A _ a') + x * x' * 2 := by
          rw [map_add]; ring
        rw [this, h2, mul_zero, add_zero]
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

/-- The `A`-algebra homomorphism `A[y] → B` with `y ↦ y + a`, when `a (a + t) = 0`. -/
private noncomputable def translateY (a : A) (ha : a * (a + t) = 0) :
    RingY t s →ₐ[A] RingYZ t s u :=
  AdjoinRoot.liftAlgHom (quadratic t s) (Algebra.ofId A _) (y t s u + algebraMap A _ a) (by
    have ha' : algebraMap A (RingYZ t s u) a * (algebraMap A _ a + algebraMap A _ t) = 0 := by
      rw [← map_add, ← map_mul, ha, map_zero]
    simp only [eval₂_quadratic, RingHom.coe_coe, Algebra.ofId_apply]
    linear_combination y_sq_add_mul_y t s u + ha' +
      y t s u * algebraMap A _ a * two_eq_zero (algebraMap A (RingYZ t s u)))

/-- In characteristic two, `y ↦ y + a`, `z ↦ z + b` defines an `A`-algebra endomorphism of `B`
when `a (a + t) = 0` and `b (b + t) = 0`, that is when `y + a` and `z + b` are again roots. -/
private noncomputable def translate (a b : A) (ha : a * (a + t) = 0) (hb : b * (b + t) = 0) :
    RingYZ t s u →ₐ[A] RingYZ t s u :=
  AdjoinRoot.liftAlgHom _ (translateY t s u a ha) (z t s u + algebraMap A _ b) (by
    have hb' : algebraMap A (RingYZ t s u) b * (algebraMap A _ b + algebraMap A _ t) = 0 := by
      rw [← map_add, ← map_mul, hb, map_zero]
    simp only [eval₂_quadratic, RingHom.coe_coe, AlgHom.commutes]
    linear_combination z_sq_add_mul_z t s u + hb' +
      z t s u * algebraMap A _ b * two_eq_zero (algebraMap A (RingYZ t s u)))

private theorem translate_y (a b : A) (ha hb) :
    translate t s u a b ha hb (y t s u) = y t s u + algebraMap A _ a := by
  -- `y` is the image of the root of `A[y]`, and `algebraMap A[y] B` is `AdjoinRoot.of` by `rfl`.
  exact (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)

private theorem translate_z (a b : A) (ha hb) :
    translate t s u a b ha hb (z t s u) = z t s u + algebraMap A _ b :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The translation `y ↦ y + a`, `z ↦ z + b` is an involution, hence an automorphism. -/
private noncomputable def translateEquiv (a b : A) (ha : a * (a + t) = 0)
    (hb : b * (b + t) = 0) : RingYZ t s u ≃ₐ[A] RingYZ t s u :=
  have h : (translate t s u a b ha hb).comp (translate t s u a b ha hb) = .id A _ :=
    algHom_ext t s u
      (by rw [AlgHom.comp_apply, translate_y, map_add, translate_y, AlgHom.commutes, add_assoc,
        ← map_add, ← two_mul, CharTwo.two_eq_zero, zero_mul, map_zero, add_zero, AlgHom.id_apply])
      (by rw [AlgHom.comp_apply, translate_z, map_add, translate_z, AlgHom.commutes, add_assoc,
        ← map_add, ← two_mul, CharTwo.two_eq_zero, zero_mul, map_zero, add_zero, AlgHom.id_apply])
  .ofAlgHom _ _ h h

end Generators

/-! ### `B` is a discrete valuation ring with uniformizer `t` -/

section DiscreteValuationRing

variable [IsDomain A] [IsDiscreteValuationRing A] {t s u : A}

section Step

variable (ht : t ∈ maximalIdeal A) (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
include ht hs

private theorem isLocalRing_ringY : IsLocalRing (RingY t s) :=
  (monic_quadratic t s).isLocalRing_adjoinRoot (irreducible_map_residue_quadratic ht hs)

private theorem isDomain_ringY : IsDomain (RingY t s) :=
  (monic_quadratic t s).isDomain_adjoinRoot (irreducible_map_residue_quadratic ht hs)

private theorem isDiscreteValuationRing_ringY [IsDomain (RingY t s)] :
    IsDiscreteValuationRing (RingY t s) :=
  (monic_quadratic t s).isDiscreteValuationRing_adjoinRoot
    (irreducible_map_residue_quadratic ht hs)

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
  have h2 := two_eq_zero (algebraMap A (RingY t s))
  set r := AdjoinRoot.root (quadratic t s)
  have key : aeval r (C b * X + C a) ^ 2 =
      algebraMap A _ (a ^ 2 + s * b ^ 2) - algebraMap A _ t * (algebraMap A _ b ^ 2 * r) := by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X]
    linear_combination algebraMap A _ b ^ 2 * hroot + algebraMap A _ a * algebraMap A _ b * r * h2
  rw [← map_pow, key, map_sub, map_mul (residue _) (algebraMap A _ t),
    (residue_eq_zero_iff _).mpr (map_nonunit _ _ ht), zero_mul, sub_zero,
    ← ResidueField.algebraMap_residue, ← ResidueField.algebraMap_residue] at hc
  apply hu (residue A a) (residue A b)
  simpa using (algebraMap (ResidueField A) (ResidueField (RingY t s))).injective hc

/-- `B` is a local ring. -/
theorem isLocalRing_ringYZ : IsLocalRing (RingYZ t s u) :=
  have := isLocalRing_ringY ht hs
  (monic_quadratic _ _).isLocalRing_adjoinRoot (irreducible_map_residue_quadratic_ringYZ ht hs hu)

/-- `B` is a domain. -/
theorem isDomain_ringYZ : IsDomain (RingYZ t s u) :=
  have := isLocalRing_ringY ht hs
  have := isDomain_ringY ht hs
  have := isDiscreteValuationRing_ringY ht hs
  (monic_quadratic _ _).isDomain_adjoinRoot (irreducible_map_residue_quadratic_ringYZ ht hs hu)

/-- `B` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_ringYZ [IsDomain (RingYZ t s u)] :
    IsDiscreteValuationRing (RingYZ t s u) :=
  have := isLocalRing_ringY ht hs
  have := isDomain_ringY ht hs
  have := isDiscreteValuationRing_ringY ht hs
  (monic_quadratic _ _).isDiscreteValuationRing_adjoinRoot
    (irreducible_map_residue_quadratic_ringYZ ht hs hu)

/-- The maximal ideal of `A` generates the maximal ideal of `B`, so `B / t B` is the residue field
of `B`. -/
theorem maximalIdeal_ringYZ [IsLocalRing (RingYZ t s u)] :
    maximalIdeal (RingYZ t s u) = (maximalIdeal A).map (algebraMap A (RingYZ t s u)) := by
  have := isLocalRing_ringY ht hs
  rw [AdjoinRoot.maximalIdeal_eq_map (irreducible_map_residue_quadratic_ringYZ ht hs hu),
    AdjoinRoot.maximalIdeal_eq_map (irreducible_map_residue_quadratic ht hs), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- `A → B` is a local homomorphism. -/
theorem isLocalHom_algebraMap_ringYZ [IsLocalRing (RingYZ t s u)] :
    IsLocalHom (algebraMap A (RingYZ t s u)) :=
  ((local_hom_TFAE _).out 1 3).mpr (maximalIdeal_ringYZ ht hs hu).ge

/-- **The residue field of `B` has degree `4` over that of `A`.** -/
theorem finrank_residueField_ringYZ [IsLocalRing (RingYZ t s u)]
    [IsLocalHom (algebraMap A (RingYZ t s u))] :
    Module.finrank (ResidueField A) (ResidueField (RingYZ t s u)) = 4 := by
  have := isDomain_ringY ht hs
  have hg := monic_quadratic (algebraMap A (RingY t s) t) (algebraMap A (RingY t s) u)
  have := (monic_quadratic t s).free_adjoinRoot
  have := (monic_quadratic t s).finite_adjoinRoot
  have := hg.free_adjoinRoot
  have := hg.finite_adjoinRoot
  have : Module.Free A (RingYZ t s u) := .trans (S := RingY t s)
  have : Module.Finite A (RingYZ t s u) := .trans (RingY t s) _
  rw [IsLocalRing.finrank_residueField_eq_finrank (maximalIdeal_ringYZ ht hs hu).symm,
    finrank_ringYZ]

end Step

variable [CharP A 2]

/-- **`t` is a uniformizer of `B`**: the extension `A → B` has ramification index one. -/
theorem irreducible_algebraMap_ringYZ (ht : Irreducible t)
    (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
    (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u) :
    Irreducible (algebraMap A (RingYZ t s u) t) := by
  have hmem := ht.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self t
  have := isDomain_ringYZ hmem hs hu
  have := isDiscreteValuationRing_ringYZ hmem hs hu
  exact TauCeti.IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq
    (maximalIdeal_ringYZ hmem hs hu).symm ht

/-- **The residue field extension is purely inseparable**: the square of every element of `B` is
congruent to an element of `A` modulo `t`. -/
theorem isPurelyInseparable_residueField_ringYZ (ht : t ∈ maximalIdeal A)
    [IsLocalRing (RingYZ t s u)] [IsLocalHom (algebraMap A (RingYZ t s u))] :
    IsPurelyInseparable (ResidueField A) (ResidueField (RingYZ t s u)) := by
  have : CharP (ResidueField A) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero (residue A))
  refine (isPurelyInseparable_iff_pow_mem _ 2).mpr fun c ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective c
  obtain ⟨a, ha⟩ := exists_sq_sub_algebraMap_mem_span t s u x
  refine ⟨1, residue A a, ?_⟩
  rw [pow_one, ResidueField.algebraMap_residue, ← map_pow, eq_comm, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff]
  exact (Ideal.span_singleton_le_iff_mem _).mpr (map_nonunit _ _ ht) ha

end DiscreteValuationRing

/-! ### The automorphisms and the ramification groups -/

section Automorphism

variable [IsDomain A] [IsDiscreteValuationRing A] [CharP A 2] {t s u : A}

section Translation

variable (ht : t ∈ maximalIdeal A) (hs : ∀ a : ResidueField A, a ^ 2 ≠ residue A s)
  (hu : ∀ a b : ResidueField A, a ^ 2 + residue A s * b ^ 2 ≠ residue A u)
include ht hs hu

/-- Every `A`-algebra automorphism of `B` moves `y` by `0` or by `t`: these are the two roots of
`Y ^ 2 + t Y - s` in the domain `B`. -/
theorem algEquiv_apply_y (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) :
    σ (y t s u) = y t s u ∨ σ (y t s u) = y t s u + algebraMap A _ t := by
  have := isDomain_ringYZ ht hs hu
  refine eq_or_eq_add_of_sq_add_mul_eq (two_eq_zero (algebraMap A (RingYZ t s u)))
    (y_sq_add_mul_y t s u) ?_
  simpa using congr(σ $(y_sq_add_mul_y t s u))

/-- Every `A`-algebra automorphism of `B` moves `z` by `0` or by `t`. -/
theorem algEquiv_apply_z (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) :
    σ (z t s u) = z t s u ∨ σ (z t s u) = z t s u + algebraMap A _ t := by
  have := isDomain_ringYZ ht hs hu
  refine eq_or_eq_add_of_sq_add_mul_eq (two_eq_zero (algebraMap A (RingYZ t s u)))
    (z_sq_add_mul_z t s u) ?_
  simpa using congr(σ $(z_sq_add_mul_z t s u))

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

/-- **The `A`-algebra automorphisms of `B` form a Klein four-group**, made of the translations
`y ↦ y + ε t`, `z ↦ z + δ t` with `ε, δ ∈ {0, 1}`. -/
theorem isKleinFour_algEquiv : IsKleinFour (RingYZ t s u ≃ₐ[A] RingYZ t s u) := by
  have hmem := ht.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self t
  have := isDomain_ringYZ hmem hs hu
  have hT0 := (irreducible_algebraMap_ringYZ ht hs hu).ne_zero
  have htt : t * (t + t) = 0 := by rw [← two_mul, CharTwo.two_eq_zero, zero_mul, mul_zero]
  have h0t : (0 : A) * (0 + t) = 0 := zero_mul _
  set Y := y t s u
  set Z := z t s u
  set T := algebraMap A (RingYZ t s u) t
  -- An automorphism is determined by the images of `y` and `z`, which are `y` or `y + t`, and
  -- `z` or `z + t`; all four choices occur.
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
      exact ⟨translateEquiv t s u a b ha hb, Prod.ext (translate_y t s u a b ha hb)
        (translate_z t s u a b ha hb)⟩
  have hne (X : RingYZ t s u) : X ≠ X + T := fun h ↦ hT0 (by linear_combination -h)
  have hcard : Nat.card (RingYZ t s u ≃ₐ[A] RingYZ t s u) = 4 := by
    rw [← Set.ncard_range_of_injective hF, hrange, Set.ncard_prod, Set.ncard_pair (hne Y),
      Set.ncard_pair (hne Z)]
  -- Every automorphism is an involution.
  have hinv (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) {X : RingYZ t s u} (hX : σ X = X ∨ σ X = X + T) :
      σ (σ X) = X := by
    rcases hX with h | h
    · rw [h, h]
    · rw [h, map_add, h, AlgEquiv.commutes, add_assoc, ← two_mul,
        two_eq_zero (algebraMap A (RingYZ t s u)), zero_mul, add_zero]
  have hsq (σ : RingYZ t s u ≃ₐ[A] RingYZ t s u) : σ ^ 2 = 1 :=
    AlgEquiv.coe_toAlgHom_injective <| algHom_ext t s u
      (by simpa [sq] using hinv σ (algEquiv_apply_y hmem hs hu σ))
      (by simpa [sq] using hinv σ (algEquiv_apply_z hmem hs hu σ))
  have : Finite (RingYZ t s u ≃ₐ[A] RingYZ t s u) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (RingYZ t s u ≃ₐ[A] RingYZ t s u) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun σ hσ ↦
    orderOf_eq_prime (hsq σ) hσ⟩

/-- **The first ramification group is trivial**: a nontrivial automorphism moves `y` or `z` by
the uniformizer `t`, which does not lie in the square of the maximal ideal of `B`. -/
theorem ramificationGroup_one_eq_bot [IsLocalRing (RingYZ t s u)] :
    IsLocalRing.ramificationGroup (RingYZ t s u ≃ₐ[A] RingYZ t s u) (RingYZ t s u) 1 = ⊥ := by
  have hmem := ht.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self t
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
