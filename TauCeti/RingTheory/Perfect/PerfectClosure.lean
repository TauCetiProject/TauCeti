/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat
import TauCeti.RingTheory.Perfect.Basic

/-!
# Perfect closures of flat algebras over a perfect ring

Let `A` be a perfect ring of exponential characteristic `p`, let `K` be a flat `A`-algebra, and let
`K → L` be a perfect closure of `K` in the sense of Mathlib's `IsPerfectClosure`, for instance
Mathlib's colimit perfection `PerfectClosure K p`. Then `L` is flat over `A`.

The main example is the perfect polynomial algebra `A[X_s ^ (1 / p ^ ∞) : s ∈ σ]`, the perfection
`PerfectClosure (MvPolynomial σ A) p`, which is therefore flat over `A`. Every map of perfect
rings `A → B` factors through the perfect polynomial algebra on the elements of `B`, followed by a
surjection onto `B` whose kernel is radical. Together these reduce statements about arbitrary maps
of perfect rings, such as the vanishing of `Tor_i^A(B, C)` for perfect `A`-algebras `B` and `C`
and `i > 0`, to quotients of perfect rings by radical ideals.

## Main results

* `IsPRadical.pow_mem_of_finite`: finitely many elements of a `p`-radical extension have
  `p ^ n`-th powers in the base for a common exponent `n`.
* `Module.Flat.of_isPerfectClosure`: a perfect closure of a flat algebra over a perfect ring is
  flat.
* `RingHom.Flat.perfectClosureOf_comp`: the colimit perfection of a flat algebra over a perfect
  ring is flat.
* `TauCeti.flat_perfectClosureOf_comp_C`: the perfect polynomial algebra
  `PerfectClosure (MvPolynomial σ A) p` is flat over a perfect ring `A`.
* `TauCeti.exists_surjective_perfectClosure_mvPolynomial`: every map of perfect rings
  `A → B` factors through a perfect polynomial algebra over `A`, followed by a surjection with
  radical kernel.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 3.16 and its proof.
* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK), the equational
  criterion for flatness.
-/

public section

open Module

section IsPRadical

variable {K L : Type*} [CommSemiring K] [CommSemiring L] (i : K →+* L) (p : ℕ) [IsPRadical i p]

/-- In a `p`-radical extension `i : K →+* L`, every finite family of elements of `L` has
`p ^ n`-th powers in the image of `K` for a common exponent `n`. -/
theorem IsPRadical.pow_mem_of_finite {ι : Type*} [Finite ι] (z : ι → L) :
    ∃ (n : ℕ) (y : ι → K), ∀ j, i (y j) = z j ^ p ^ n := by
  cases nonempty_fintype ι
  choose n y hy using fun j ↦ IsPRadical.pow_mem i p (z j)
  refine ⟨Finset.univ.sup n, fun j ↦ y j ^ p ^ (Finset.univ.sup n - n j), fun j ↦ ?_⟩
  rw [map_pow, hy, ← pow_mul, ← pow_add,
    Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ j))]

end IsPRadical

namespace Module.Flat

variable {A K L : Type*} [CommRing A] [CommRing K] [CommRing L] [Algebra A K] [Algebra A L]
  [Algebra K L] [IsScalarTower A K L] (p : ℕ) [ExpChar A p] [PerfectRing A p] [ExpChar K p]
  [ExpChar L p] [PerfectRing L p] [IsPerfectClosure (algebraMap K L) p]

include p in
/-- A perfect closure of a flat algebra over a perfect ring is flat: if `A` is a perfect ring of
exponential characteristic `p`, `K` is a flat `A`-algebra and `K → L` is a perfect closure of `K`,
then `L` is a flat `A`-module. -/
theorem of_isPerfectClosure [Module.Flat A K] : Module.Flat A L := by
  -- We use the equational criterion for flatness. A relation `∑ fⱼ zⱼ = 0` in `L` becomes, after
  -- raising it to a power `p ^ N`, a relation `∑ fⱼ ^ p ^ N yⱼ = 0` in `K` with `zⱼ ^ p ^ N` the
  -- image of `yⱼ`, since the kernel of `K → L` consists of `p`-nilpotent elements. Flatness of
  -- `K` makes this relation trivial, and the `p ^ N`-th roots, which exist in `A` and in `L`, of
  -- the coefficients and generators of that trivialization trivialize the original relation.
  refine of_forall_isTrivialRelation fun {l f z} hfz ↦ ?_
  obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem_of_finite (algebraMap K L) p z
  -- The `p ^ n`-th power of the relation is the image of `∑ fⱼ ^ p ^ n • yⱼ`, which is therefore
  -- `p`-nilpotent.
  have hker : ∑ j, f j ^ p ^ n • y j ∈ pNilradical K p := by
    refine IsPRadical.ker_le (algebraMap K L) p ?_
    rw [RingHom.mem_ker, map_sum]
    simp_rw [algebraMap.coe_smul, hy, ← smul_pow, ← sum_pow_char_pow, hfz,
      zero_pow (expChar_pow_pos L p n).ne']
  obtain ⟨k, hk⟩ := mem_pNilradical.1 hker
  -- A relation in `K` between the `p ^ k`-th powers of the `yⱼ`, which flatness trivializes.
  have hrel : ∑ j, f j ^ p ^ (n + k) • y j ^ p ^ k = 0 := by
    rw [← hk, sum_pow_char_pow]
    simp_rw [smul_pow, ← pow_mul, ← pow_add]
  obtain ⟨m, a, w, hyw, ha⟩ := isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := K) hrel
  simp only at hyw ha
  -- Taking `p ^ (n + k)`-th roots of this trivialization trivializes the relation in `L`.
  have hA (x : A) : (iterateFrobeniusEquiv A p (n + k)).symm x ^ p ^ (n + k) = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  have hL (x : L) : (iterateFrobeniusEquiv L p (n + k)).symm x ^ p ^ (n + k) = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  refine ⟨m, fun j i ↦ (iterateFrobeniusEquiv A p (n + k)).symm (a j i),
    fun i ↦ (iterateFrobeniusEquiv L p (n + k)).symm (algebraMap K L (w i)), fun j ↦ ?_,
    fun i ↦ ?_⟩
  · apply (iterateFrobeniusEquiv L p (n + k)).injective
    simp_rw [iterateFrobeniusEquiv_def, sum_pow_char_pow, smul_pow, hA, hL,
      ← algebraMap.coe_smul, ← map_sum, ← hyw, map_pow, hy, ← pow_mul, ← pow_add]
  · apply (iterateFrobeniusEquiv A p (n + k)).injective
    simp_rw [iterateFrobeniusEquiv_def, sum_pow_char_pow, mul_pow, hA,
      zero_pow (expChar_pow_pos A p (n + k)).ne']
    exact ha i

end Module.Flat

section PerfectClosure

variable {A K : Type*} [CommRing A] [CommRing K] (p : ℕ) [Fact p.Prime] [ExpChar A p]
  [PerfectRing A p] [CharP K p]

/-- The colimit perfection of a flat algebra over a perfect ring is flat: if `f : A →+* K` is flat
and `A` is perfect of exponential characteristic `p`, then `A → PerfectClosure K p` is flat. -/
theorem RingHom.Flat.perfectClosureOf_comp {f : A →+* K} (hf : f.Flat) :
    ((PerfectClosure.of K p).comp f).Flat := by
  algebraize [f, PerfectClosure.of K p, (PerfectClosure.of K p).comp f]
  -- `algebraMap K (PerfectClosure K p)` is `PerfectClosure.of K p` by `algebraize`.
  have : IsPerfectClosure (algebraMap K (PerfectClosure K p)) p := PerfectClosure.isPRadical K p
  exact Module.Flat.of_isPerfectClosure (K := K) p

end PerfectClosure

namespace TauCeti

/-- The perfect polynomial algebra `A[X_s ^ (1 / p ^ ∞) : s ∈ σ]`, the colimit perfection of
`MvPolynomial σ A`, is flat over a perfect ring `A` of characteristic `p`. -/
theorem flat_perfectClosureOf_comp_C (A σ : Type*) [CommRing A] (p : ℕ)
    [Fact p.Prime] [CharP A p] [PerfectRing A p] :
    ((PerfectClosure.of (MvPolynomial σ A) p).comp MvPolynomial.C).Flat :=
  RingHom.Flat.perfectClosureOf_comp p <| by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance

/-- Every map `f : A →+* B` to a perfect ring of characteristic `p` factors through the perfect
polynomial algebra over `A` on the elements of `B`: there is a surjection
`PerfectClosure (MvPolynomial B A) p →+* B` with radical kernel which restricts to `f` on `A`. -/
theorem exists_surjective_perfectClosure_mvPolynomial {A B : Type*} [CommRing A]
    [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [PerfectRing B p] (f : A →+* B) :
    ∃ g : PerfectClosure (MvPolynomial B A) p →+* B, Function.Surjective g ∧
      g.comp ((PerfectClosure.of (MvPolynomial B A) p).comp MvPolynomial.C) = f ∧
      (RingHom.ker g).IsRadical := by
  let g := PerfectRing.lift (PerfectClosure.of (MvPolynomial B A) p)
    (MvPolynomial.eval₂Hom f id) p
  have hg (x : MvPolynomial B A) : g (PerfectClosure.of _ p x) = MvPolynomial.eval₂Hom f id x :=
    PerfectRing.lift_comp_apply _ _ p x
  have hsurj : Function.Surjective g := fun b ↦
    ⟨PerfectClosure.of _ p (MvPolynomial.X b), by rw [hg, MvPolynomial.eval₂Hom_X', id]⟩
  have := isReduced_of_perfectRing B p
  exact ⟨g, hsurj, RingHom.ext fun a ↦ by simp [hg],
    (RingHom.ker_isRadical_iff_reduced_of_surjective hsurj).2 this⟩

end TauCeti
