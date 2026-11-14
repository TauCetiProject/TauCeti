/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import TauCeti.Algebra.Group.Primary.Decomposition
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Primary components of finite bilinear and quadratic modules

The primary components of a finite abelian group are already defined by Mathlib as
`AddCommGroup.primaryComponent`. This file proves the form-theoretic fact needed to decompose
finite bilinear and quadratic modules: components belonging to distinct primes are orthogonal. It
also packages the restricted quadratic module `FiniteQuadraticModule.primaryComponent` together with
its cardinality, isometry functoriality, and compatibility with orthogonal products.

For a bilinear module, orthogonality follows because the value of the pairing on a `p`-primary and
a `q`-primary element is annihilated by powers of both `p` and `q`.  Those powers are coprime when
the primes are distinct.  The quadratic statements then follow from the polar identity.  Finite-sum
versions record that both raw forms split as sums of their restrictions whenever the summands lie
in pairwise distinct primary components.

## Main results

* `TauCeti.FiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent`: distinct primary
  components are orthogonal elementwise.
* `TauCeti.FiniteBilinearModule.primaryComponent_le_orthogonalComplement_primaryComponent`: the
  corresponding inclusion of additive subgroups.
* `TauCeti.FiniteBilinearModule.isNondegenerate_restrict_primaryComponent`: a nondegenerate
  pairing restricts nondegenerately to each prime-primary component.
* `TauCeti.FiniteBilinearModule.pairing_sum_eq_sum_pairing_of_mem_primaryComponent`: a bilinear
  pairing of primary decompositions is the sum of the component pairings.
* `TauCeti.FiniteQuadraticModule.primaryComponent`,
  `TauCeti.FiniteQuadraticModule.natCard_primaryComponent`,
  `TauCeti.FiniteQuadraticModule.Isometry.primaryComponentEquiv`, and
  `TauCeti.FiniteQuadraticModule.primaryComponentProdIsometry`: the `p`-primary finite quadratic
  module, its prime-power cardinality, transport along isometries, and compatibility with `prod`.
* `TauCeti.FiniteQuadraticModule.quadratic_sum_of_mem_primaryComponent`: a quadratic value on a
  sum of primary components is the sum of the component values.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

universe u v

private theorem eq_zero_of_coprime_nsmul_eq_zero {M : Type*} [AddMonoid M] {m n : ℕ} {x : M}
    (hmn : m.Coprime n) (hm : m • x = 0) (hn : n • x = 0) : x = 0 := by
  have horder_m : addOrderOf x ∣ m := by
    rwa [addOrderOf_dvd_iff_nsmul_eq_zero]
  have horder_n : addOrderOf x ∣ n := by
    rwa [addOrderOf_dvd_iff_nsmul_eq_zero]
  rw [← AddMonoid.addOrderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hmn horder_m horder_n

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-! ## Orthogonality -/

/-- Elements in the primary components for two distinct primes pair to zero. -/
theorem pairing_eq_zero_of_mem_primaryComponent {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {x y : A} (hx : x ∈ AddCommGroup.primaryComponent A p)
    (hy : y ∈ AddCommGroup.primaryComponent A q) : A.pairing x y = 0 := by
  rw [AddCommGroup.mem_primaryComponent] at hx hy
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  apply eq_zero_of_coprime_nsmul_eq_zero (Nat.coprime_pow_primes m n hp hq hpq)
  · rw [A.pairing_comm x y, ← map_nsmul (A.pairing y) (p ^ m) x, hm, map_zero]
  · rw [← map_nsmul (A.pairing x) (q ^ n) y, hn, map_zero]

/-- The `p`-primary component is contained in the orthogonal complement of the `q`-primary
component when `p` and `q` are distinct primes. -/
theorem primaryComponent_le_orthogonalComplement_primaryComponent {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    AddCommGroup.primaryComponent A p ≤
      A.orthogonalComplement (AddCommGroup.primaryComponent A q) := by
  intro x hx
  rw [A.mem_orthogonalComplement_iff]
  intro y hy
  exact A.pairing_eq_zero_of_mem_primaryComponent hp hq hpq hx hy

/-! ## Nondegeneracy of the restricted pairing -/

/-- Multiplication by the prime-to-`p` part of the group cardinality sends every element into the
`p`-primary component.

This is the elementary projection onto the primary part needed to detect the radical of the
restricted pairing. It is stated for the underlying group because it is independent of the form. -/
private theorem ordCompl_natCard_nsmul_mem_primaryComponent (p : ℕ) (x : A) :
    ordCompl[p] (Nat.card A) • x ∈ AddCommGroup.primaryComponent A p := by
  rw [AddCommGroup.mem_primaryComponent]
  refine ⟨(Nat.card A).factorization p, ?_⟩
  rw [← mul_nsmul, Nat.mul_comm, Nat.ordProj_mul_ordCompl_eq_self, card_nsmul_eq_zero']

/-- The restriction of a nondegenerate finite bilinear module to any prime-primary component is
nondegenerate. -/
theorem isNondegenerate_restrict_primaryComponent (hA : A.IsNondegenerate) {p : ℕ}
    (hp : p.Prime) :
    (A.restrict (AddCommGroup.primaryComponent A p)).IsNondegenerate := by
  -- For `x` in the radical of the restricted pairing and arbitrary `z`, pairing `x` with
  -- `ordCompl[p] (Nat.card A) • z` shows the prime-to-`p` part of the cardinality annihilates
  -- `A.pairing x z`, while a power of `p` annihilates it because `x` is `p`-primary.  Those two
  -- integers are coprime, so `A.pairing x z = 0` for every `z` and ambient nondegeneracy applies.
  rw [(A.restrict (AddCommGroup.primaryComponent A p)).isNondegenerate_iff_injective]
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hA.eq_zero_of_forall_pairing_eq_zero
  intro z
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp (sub_mem x.property y.property)
  have hcard : Nat.card A ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩
  apply eq_zero_of_coprime_nsmul_eq_zero
      ((Nat.coprime_ordCompl hp hcard).pow_left k)
  · have hmap := DFunLike.congr_fun
      (map_nsmul A.pairing (p ^ k) (x.1 - y.1)) z
    rw [hk, map_zero] at hmap
    calc
      p ^ k • A.pairing (x.1 - y.1) z =
          (p ^ k • A.pairing (x.1 - y.1)) z :=
        (AddMonoidHom.nsmul_apply _ _ _).symm
      _ = (0 : CharacterModule A) z := hmap.symm
      _ = 0 := AddMonoidHom.zero_apply z
  · rw [← map_nsmul (A.pairing (x.1 - y.1))]
    have hz := ordCompl_natCard_nsmul_mem_primaryComponent A p z
    have heval := DFunLike.congr_fun hxy
      (⟨ordCompl[p] (Nat.card A) • z, hz⟩ : AddCommGroup.primaryComponent A p)
    rw [map_sub]
    exact sub_eq_zero.mpr heval

/-! ## Finite sums -/

/-- Pairing sums of elements from pairwise distinct primary components keeps only the diagonal
component pairings.  This is the raw bilinear identity used by the canonical primary-decomposition
isometry. -/
theorem pairing_sum_eq_sum_pairing_of_mem_primaryComponent {ι : Type*}
    (s : Finset ι) (p : ι → ℕ) (x y : ι → A)
    (hprime : ∀ i ∈ s, (p i).Prime)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i ≠ p j)
    (hx : ∀ i ∈ s, x i ∈ AddCommGroup.primaryComponent A (p i))
    (hy : ∀ i ∈ s, y i ∈ AddCommGroup.primaryComponent A (p i)) :
    A.pairing (∑ i ∈ s, x i) (∑ i ∈ s, y i) =
      ∑ i ∈ s, A.pairing (x i) (y i) := by
  classical
  rw [← A.toBilin_apply, A.toBilin.map_sum₂ s x]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum (A.toBilin (x i)) y s]
  have hoff : ∀ j ∈ s, j ≠ i → A.toBilin (x i) (y j) = 0 := by
    intro j hj hji
    rw [A.toBilin_apply]
    exact A.pairing_eq_zero_of_mem_primaryComponent (hprime i hi) (hprime j hj)
      (hdistinct i hi j hj hji.symm) (hx i hi) (hy j hj)
  rw [Finset.sum_eq_single i hoff (fun hnot ↦ (hnot hi).elim), A.toBilin_apply]

end FiniteBilinearModule

namespace FiniteQuadraticModule

/-- The `p`-primary component of a finite quadratic module: `A.restrict` to
`AddCommGroup.primaryComponent A p`. -/
protected abbrev primaryComponent (A : FiniteQuadraticModule.{u}) (p : ℕ) :
    FiniteQuadraticModule.{u} :=
  A.restrict (AddCommGroup.primaryComponent A p)

/-- The cardinality of the `p`-primary component of `A` for a prime `p` is the `p`-part of
`Nat.card A`, since `A.primaryComponent p` has carrier `AddCommGroup.primaryComponent A p`. -/
theorem natCard_primaryComponent (A : FiniteQuadraticModule.{u}) {p : ℕ} (hp : p.Prime) :
    Nat.card (A.primaryComponent p) = p ^ (Nat.card A).factorization p :=
  TauCeti.AddCommGroup.natCard_primaryComponent A hp

/-- A quadratic isometry induces an isometry on `p`-primary components. -/
def Isometry.primaryComponentEquiv {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : Isometry A B) (p : ℕ) : Isometry (A.primaryComponent p) (B.primaryComponent p) where
  toLinearEquiv := (f.toLinearEquiv.toAddEquiv.primaryComponent p).toIntLinearEquiv
  map_app' x :=
    (B.restrict_quadratic _ _).trans <|
      (congrArg B.quadratic
        (AddEquiv.coe_primaryComponent_apply f.toLinearEquiv.toAddEquiv p x)).trans <|
      (f.map_app x.1).trans (A.restrict_quadratic _ x).symm

@[simp]
theorem Isometry.coe_primaryComponentEquiv_apply {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (p : ℕ) (x : A.primaryComponent p) :
    (f.primaryComponentEquiv p x).1 = f x.1 :=
  AddEquiv.coe_primaryComponent_apply f.toLinearEquiv.toAddEquiv p x

/-- Taking the `p`-primary component commutes with orthogonal products. -/
def primaryComponentProdIsometry (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v})
    (p : ℕ) :
    Isometry ((A.prod B).primaryComponent p)
      ((A.primaryComponent p).prod (B.primaryComponent p)) where
  toLinearEquiv := (TauCeti.AddCommGroup.primaryComponentProd A B p).toIntLinearEquiv
  map_app' z :=
    ((A.primaryComponent p).prod_quadratic (B.primaryComponent p) _ _).trans <|
      (congrArg₂ (· + ·)
        ((A.restrict_quadratic _ _).trans
          (congrArg A.quadratic (TauCeti.AddCommGroup.coe_primaryComponentProd_apply_fst A B p z)))
        ((B.restrict_quadratic _ _).trans
          (congrArg B.quadratic
            (TauCeti.AddCommGroup.coe_primaryComponentProd_apply_snd A B p z)))).trans <|
      ((A.prod_quadratic B z.1.1 z.1.2).symm.trans ((A.prod B).restrict_quadratic _ z).symm)

@[simp]
theorem coe_primaryComponentProdIsometry_apply_fst (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) (p : ℕ) (z : (A.prod B).primaryComponent p) :
    ((primaryComponentProdIsometry A B p z).1).1 = z.1.1 :=
  TauCeti.AddCommGroup.coe_primaryComponentProd_apply_fst A B p z

@[simp]
theorem coe_primaryComponentProdIsometry_apply_snd (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) (p : ℕ) (z : (A.prod B).primaryComponent p) :
    ((primaryComponentProdIsometry A B p z).2).1 = z.1.2 :=
  TauCeti.AddCommGroup.coe_primaryComponentProd_apply_snd A B p z

variable (A : FiniteQuadraticModule)

/-- The polar pairing of a nondegenerate finite quadratic module restricts nondegenerately to each
prime-primary component. -/
theorem isNondegenerate_restrict_primaryComponent (hA : A.IsNondegenerate) {p : ℕ}
    (hp : p.Prime) :
    (A.restrict (AddCommGroup.primaryComponent A p)).IsNondegenerate :=
  A.toFiniteBilinearModule.isNondegenerate_restrict_primaryComponent hA hp

/-- A quadratic map is additive on elements belonging to primary components for distinct primes. -/
theorem quadratic_add_of_mem_primaryComponent {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {x y : A}
    (hx : x ∈ AddCommGroup.primaryComponent A p)
    (hy : y ∈ AddCommGroup.primaryComponent A q) :
    A.quadratic (x + y) = A.quadratic x + A.quadratic y := by
  rw [QuadraticMap.map_add A.quadratic, A.polar_eq_pairing,
    A.toFiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent hp hq hpq hx hy, add_zero]

/-- The quadratic value of a sum of elements from pairwise distinct primary components is the sum
of their quadratic values.  This is the raw quadratic identity used by the canonical
primary-decomposition isometry. -/
theorem quadratic_sum_of_mem_primaryComponent {ι : Type*}
    (s : Finset ι) (p : ι → ℕ) (x : ι → A)
    (hprime : ∀ i ∈ s, (p i).Prime)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i ≠ p j)
    (hx : ∀ i ∈ s, x i ∈ AddCommGroup.primaryComponent A (p i)) :
    A.quadratic (∑ i ∈ s, x i) = ∑ i ∈ s, A.quadratic (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiprime : (p i).Prime := hprime i (Finset.mem_insert_self i s)
      have hisum :
          A.toFiniteBilinearModule.pairing (x i) (∑ j ∈ s, x j) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact A.toFiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent hiprime
          (hprime j (Finset.mem_insert_of_mem hj))
          (hdistinct i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
            (Ne.symm (ne_of_mem_of_not_mem hj hi)))
          (hx i (Finset.mem_insert_self i s)) (hx j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hi, QuadraticMap.map_add A.quadratic, A.polar_eq_pairing, hisum,
        add_zero, Finset.sum_insert hi]
      exact congrArg (A.quadratic (x i) + ·) <| ih
        (fun j hj ↦ hprime j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hjk ↦ hdistinct j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk)
        (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

end FiniteQuadraticModule

end TauCeti
