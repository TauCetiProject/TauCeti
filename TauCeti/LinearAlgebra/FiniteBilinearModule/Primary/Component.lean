/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Basic
public import Mathlib.GroupTheory.Torsion
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.Algebra.Group.Primary.Card

/-!
# Primary components of finite bilinear and quadratic modules

The primary components of a finite abelian group are already defined by Mathlib as
`AddCommGroup.primaryComponent`. This file proves the form-theoretic fact needed to decompose
finite bilinear and quadratic modules: components belonging to distinct primes are orthogonal, and
isometries restrict to each primary component.

For a bilinear module, orthogonality follows because the value of the pairing on a `p`-primary and
a `q`-primary element is annihilated by powers of both `p` and `q`.  Those powers are coprime when
the primes are distinct.  The quadratic statements then follow from the polar identity.  Finite-sum
versions record that both raw forms split as sums of their restrictions whenever the summands lie
in pairwise distinct primary components. Primary components are also functorial: an isometry
restricts to them, and the `p`-primary component of an orthogonal product is the orthogonal product
of the `p`-primary components.

## Main results

* `TauCeti.FiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent`: distinct primary
  components are orthogonal elementwise.
* `TauCeti.FiniteBilinearModule.primaryComponent_le_orthogonalComplement_primaryComponent`: the
  corresponding inclusion of additive subgroups.
* `TauCeti.FiniteBilinearModule.isNondegenerate_restrict_primaryComponent`: a nondegenerate
  pairing restricts nondegenerately to each prime-primary component.
* `TauCeti.FiniteBilinearModule.Isometry.restrictPrimaryComponent` and
  `TauCeti.FiniteQuadraticModule.Isometry.restrictPrimaryComponent`: an isometry restricts to each
  `n`-primary component.
* `TauCeti.FiniteQuadraticModule.odd_natCard_restrict_primaryComponent`: for an odd prime `p`, the
  `p`-primary restriction has odd cardinality.
* `TauCeti.FiniteBilinearModule.pairing_sum_eq_sum_pairing_of_mem_primaryComponent`: a bilinear
  pairing of primary decompositions is the sum of the component pairings.
* `TauCeti.FiniteQuadraticModule.quadratic_sum_of_mem_primaryComponent`: a quadratic value on a
  sum of primary components is the sum of the component values.
* `TauCeti.FiniteQuadraticModule.Isometry.restrictPrimaryComponent`: an isometry restricts to an
  isometry of `p`-primary components.
* `TauCeti.FiniteQuadraticModule.restrictPrimaryComponentProdIsometry`: the `p`-primary component
  of an orthogonal product is the orthogonal product of the `p`-primary components.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

universe u v w

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
      (map_nsmul A.pairing (p ^ k) (x.val - y.val)) z
    rw [hk, map_zero] at hmap
    calc
      p ^ k • A.pairing (x.val - y.val) z =
          (p ^ k • A.pairing (x.val - y.val)) z :=
        (AddMonoidHom.nsmul_apply _ _ _).symm
      _ = (0 : CharacterModule A) z := hmap.symm
      _ = 0 := AddMonoidHom.zero_apply z
  · rw [← map_nsmul (A.pairing (x.val - y.val))]
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

/-! ## Restricting isometries to primary components -/

/-- An isometry of finite bilinear modules restricts to each `n`-primary component. -/
def Isometry.restrictPrimaryComponent {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
    (f : Isometry A B) (n : ℕ) :
    Isometry (A.restrict (AddCommGroup.primaryComponent A n))
      (B.restrict (AddCommGroup.primaryComponent B n)) where
  toAddEquiv := f.toAddEquiv.primaryComponent n
  map_pairing' x y := by
    rw [restrict_pairing, restrict_pairing, AddEquiv.coe_primaryComponent_apply,
      AddEquiv.coe_primaryComponent_apply, Isometry.coe_toAddEquiv]
    exact f.map_pairing x y

/-- Restricting a bilinear isometry to `n`-primary components commutes with coercion to the
ambient module. -/
@[simp]
theorem Isometry.coe_restrictPrimaryComponent_apply {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : Isometry A B) (n : ℕ)
    (x : AddCommGroup.primaryComponent A n) : (f.restrictPrimaryComponent n x : B) = f x :=
  f.toAddEquiv.coe_primaryComponent_apply n x

/-- The additive equivalence underlying a restricted bilinear isometry is the restricted additive
equivalence. -/
@[simp]
theorem Isometry.restrictPrimaryComponent_toAddEquiv {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : Isometry A B) (n : ℕ) :
    (f.restrictPrimaryComponent n).toAddEquiv = f.toAddEquiv.primaryComponent n :=
  (rfl)

/-- Restricting the identity bilinear isometry to an `n`-primary component gives the identity
bilinear isometry. -/
@[simp]
theorem Isometry.refl_restrictPrimaryComponent (A : FiniteBilinearModule.{u}) (n : ℕ) :
    (Isometry.refl A).restrictPrimaryComponent n =
      Isometry.refl (A.restrict (AddCommGroup.primaryComponent A n)) :=
  Isometry.toAddEquiv_injective (by simp)

/-- Restricting the inverse bilinear isometry to `n`-primary components gives the inverse of the
restricted isometry. -/
@[simp]
theorem Isometry.symm_restrictPrimaryComponent {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : Isometry A B) (n : ℕ) :
    f.symm.restrictPrimaryComponent n = (f.restrictPrimaryComponent n).symm :=
  Isometry.toAddEquiv_injective (by simp)

/-- Restricting a composite bilinear isometry to `n`-primary components gives the composite of the
restricted isometries. -/
@[simp]
theorem Isometry.trans_restrictPrimaryComponent {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} {C : FiniteBilinearModule.{w}}
    (f : Isometry A B) (g : Isometry B C) (n : ℕ) :
    (f.trans g).restrictPrimaryComponent n =
      (f.restrictPrimaryComponent n).trans (g.restrictPrimaryComponent n) :=
  Isometry.toAddEquiv_injective (by simp)

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- The polar pairing of a nondegenerate finite quadratic module restricts nondegenerately to each
prime-primary component. -/
theorem isNondegenerate_restrict_primaryComponent (hA : A.IsNondegenerate) {p : ℕ}
    (hp : p.Prime) :
    (A.restrict (AddCommGroup.primaryComponent A p)).IsNondegenerate :=
  A.toFiniteBilinearModule.isNondegenerate_restrict_primaryComponent hA hp

/-- For an odd prime `p`, the `p`-primary restriction of a finite quadratic module has odd
cardinality. -/
theorem odd_natCard_restrict_primaryComponent {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Odd (Nat.card (A.restrict (AddCommGroup.primaryComponent A p))) := by
  rw [A.natCard_restrict, TauCeti.AddCommGroup.natCard_primaryComponent A hp]
  exact (hp.odd_of_ne_two hp2).pow

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
      have hisum : A.toFiniteBilinearModule.pairing (x i) (∑ j ∈ s, x j) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun j hj ↦
          A.toFiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent
            (hprime i (Finset.mem_insert_self i s)) (hprime j (Finset.mem_insert_of_mem hj))
            (hdistinct i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
              (Ne.symm (ne_of_mem_of_not_mem hj hi)))
            (hx i (Finset.mem_insert_self i s)) (hx j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hi, QuadraticMap.map_add A.quadratic, A.polar_eq_pairing, hisum,
        add_zero, Finset.sum_insert hi]
      exact congrArg (A.quadratic (x i) + ·) <| ih
        (fun j hj ↦ hprime j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk ↦ hdistinct j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
        (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

/-! ## Primary components under isometries and orthogonal products -/

variable {A} in
/-- An isometry carries `p`-primary components onto `p`-primary components, so it restricts to an
isometry between them. -/
def Isometry.restrictPrimaryComponent {B : FiniteQuadraticModule} (f : Isometry A B) (p : ℕ) :
    Isometry (A.restrict (AddCommGroup.primaryComponent A p))
      (B.restrict (AddCommGroup.primaryComponent B p)) :=
  f.restrict fun x ↦ by
    simp only [AddCommGroup.mem_primaryComponent, ← map_nsmul, EmbeddingLike.map_eq_zero_iff]

variable {A} in
/-- The restriction of an isometry to primary components acts as the isometry. -/
@[simp]
theorem Isometry.restrictHom_restrictPrimaryComponent_apply {B : FiniteQuadraticModule}
    (f : Isometry A B) (p : ℕ) (x : A.restrict (AddCommGroup.primaryComponent A p)) :
    B.restrictHom _ (f.restrictPrimaryComponent p x) = f (A.restrictHom _ x) :=
  f.restrictHom_restrict_apply _ x

/-- Restricting a quadratic isometry to `n`-primary components commutes with coercion to the
ambient module. -/
@[simp]
theorem Isometry.coe_restrictPrimaryComponent_apply {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ)
    (x : A.restrict (AddCommGroup.primaryComponent A n)) :
    (f.restrictPrimaryComponent n x).val = f x.val := by
  have h := f.restrictHom_restrictPrimaryComponent_apply n x
  let y : AddCommGroup.primaryComponent B n := f.restrictPrimaryComponent n x
  let x' : AddCommGroup.primaryComponent A n := x
  change B.restrictHom _ y = f (A.restrictHom _ x') at h
  rw [B.restrictHom_apply, A.restrictHom_apply] at h
  exact h

/-- The additive equivalence underlying a restricted quadratic isometry is the restricted additive
equivalence. -/
@[simp]
theorem Isometry.restrictPrimaryComponent_toAddEquiv {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    (f.restrictPrimaryComponent n).toAddEquiv = f.toAddEquiv.primaryComponent n :=
  AddEquiv.ext fun x ↦ Subtype.ext <|
    (f.coe_restrictPrimaryComponent_apply n x).trans
      (f.toAddEquiv.coe_primaryComponent_apply n x).symm

/-- Restricting the identity quadratic isometry to an `n`-primary component gives the identity
quadratic isometry. -/
@[simp]
theorem Isometry.refl_restrictPrimaryComponent (A : FiniteQuadraticModule.{u}) (n : ℕ) :
    Isometry.restrictPrimaryComponent (A := A) (B := A)
      (QuadraticMap.IsometryEquiv.refl A.quadratic) n =
      QuadraticMap.IsometryEquiv.refl
        (A.restrict (AddCommGroup.primaryComponent A n)).quadratic :=
  DFunLike.ext _ _ fun _ ↦ by
    apply Subtype.ext; rw [Isometry.coe_restrictPrimaryComponent_apply]; rfl

/-- Restricting the inverse quadratic isometry to `n`-primary components gives the inverse of the
restricted isometry. -/
@[simp]
theorem Isometry.symm_restrictPrimaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    Isometry.restrictPrimaryComponent f.symm n = (f.restrictPrimaryComponent n).symm :=
  DFunLike.ext _ _ fun y ↦ by
    apply EquivLike.injective (f.restrictPrimaryComponent n)
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply]; exact Subtype.ext (by simp)

/-- Restricting a composite quadratic isometry to `n`-primary components gives the composite of the
restricted isometries. -/
@[simp]
theorem Isometry.trans_restrictPrimaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} {C : FiniteQuadraticModule.{w}}
    (f : Isometry A B) (g : Isometry B C) (n : ℕ) :
    Isometry.restrictPrimaryComponent (A := A) (B := C) (f.trans g) n =
      (f.restrictPrimaryComponent n).trans (g.restrictPrimaryComponent n) :=
  DFunLike.ext _ _ fun _ ↦ by apply Subtype.ext; simp

/-- Forgetting the quadratic structure of a restricted quadratic isometry gives the restricted
polar bilinear isometry. -/
@[simp]
theorem Isometry.restrictPrimaryComponent_toFiniteBilinearModule {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    (f.restrictPrimaryComponent n).toFiniteBilinearModule =
      f.toFiniteBilinearModule.restrictPrimaryComponent n := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [Isometry.toFiniteBilinearModule_toAddEquiv, Isometry.restrictPrimaryComponent_toAddEquiv,
    FiniteBilinearModule.Isometry.restrictPrimaryComponent_toAddEquiv,
    Isometry.toFiniteBilinearModule_toAddEquiv]

/-- **The `p`-primary component of an orthogonal product** is the orthogonal product of the
`p`-primary components (`AddCommGroup.primaryComponent_prod`). -/
def restrictPrimaryComponentProdIsometry (B : FiniteQuadraticModule) (p : ℕ) :
    Isometry ((A.prod B).restrict (AddCommGroup.primaryComponent (A.prod B) p))
      ((A.restrict (AddCommGroup.primaryComponent A p)).prod
        (B.restrict (AddCommGroup.primaryComponent B p))) :=
  ((A.prod B).restrictCongr (AddCommGroup.primaryComponent_prod A B p)).trans
    (A.restrictProdIsometry _ _)

/-- The first component of `restrictPrimaryComponentProdIsometry` is the first coordinate. -/
@[simp]
theorem restrictHom_restrictPrimaryComponentProdIsometry_apply_fst (B : FiniteQuadraticModule)
    (p : ℕ) (x : (A.prod B).restrict (AddCommGroup.primaryComponent (A.prod B) p)) :
    A.restrictHom _ (A.restrictPrimaryComponentProdIsometry B p x).1 =
      ((A.prod B).restrictHom _ x).1 := by
  rw [restrictPrimaryComponentProdIsometry, Isometry.trans_apply,
    restrictHom_restrictProdIsometry_apply_fst, restrictHom_restrictCongr_apply]

/-- The second component of `restrictPrimaryComponentProdIsometry` is the second coordinate. -/
@[simp]
theorem restrictHom_restrictPrimaryComponentProdIsometry_apply_snd (B : FiniteQuadraticModule)
    (p : ℕ) (x : (A.prod B).restrict (AddCommGroup.primaryComponent (A.prod B) p)) :
    B.restrictHom _ (A.restrictPrimaryComponentProdIsometry B p x).2 =
      ((A.prod B).restrictHom _ x).2 := by
  rw [restrictPrimaryComponentProdIsometry, Isometry.trans_apply,
    restrictHom_restrictProdIsometry_apply_snd, restrictHom_restrictCongr_apply]

end FiniteQuadraticModule

end TauCeti
