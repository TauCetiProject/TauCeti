/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Torsion
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.Algebra.Group.Primary.Rank

/-!
# Primary components of finite bilinear and quadratic modules

The primary components of a finite abelian group are already defined by Mathlib as
`AddCommGroup.primaryComponent`. This file bundles the restricted forms as
`TauCeti.FiniteBilinearModule.primaryComponent` and
`TauCeti.FiniteQuadraticModule.primaryComponent`, proves their compatibility with isometries and
orthogonal products, and establishes the form-theoretic fact needed to decompose finite bilinear and
quadratic modules: components belonging to distinct primes are orthogonal.

For a bilinear module, orthogonality follows because the value of the pairing on a `p`-primary and
a `q`-primary element is annihilated by powers of both `p` and `q`. Those powers are coprime when
the primes are distinct. The quadratic statements then follow from the polar identity. Finite-sum
versions record that both raw forms split as sums of their restrictions whenever the summands lie
in pairwise distinct primary components.

## Main definitions and results

* `TauCeti.FiniteBilinearModule.primaryComponent`,
  `TauCeti.FiniteQuadraticModule.primaryComponent`: the restricted bilinear and quadratic modules on
  `AddCommGroup.primaryComponent A p`.
* `TauCeti.FiniteBilinearModule.Isometry.primaryComponent`,
  `TauCeti.FiniteQuadraticModule.Isometry.primaryComponent`,
  `TauCeti.FiniteBilinearModule.primaryComponentProdIsometry`,
  `TauCeti.FiniteQuadraticModule.primaryComponentProdIsometry`: functoriality under isometries and
  orthogonal direct sums.
* `TauCeti.FiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent`: distinct primary
  components are orthogonal elementwise.
* `TauCeti.FiniteBilinearModule.primaryComponent_le_orthogonalComplement_primaryComponent`: the
  corresponding inclusion of additive subgroups.
* `TauCeti.FiniteBilinearModule.isNondegenerate_restrict_primaryComponent`: a nondegenerate
  pairing restricts nondegenerately to each prime-primary component.
* `TauCeti.FiniteBilinearModule.pairing_sum_eq_sum_pairing_of_mem_primaryComponent`: a bilinear
  pairing of primary decompositions is the sum of the component pairings.
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

/-! ## Bundled primary components -/

/-- The `p`-primary component of a finite bilinear module: the restriction of the pairing to
`AddCommGroup.primaryComponent A p`. -/
abbrev primaryComponent (A : FiniteBilinearModule.{u}) (p : ℕ) : FiniteBilinearModule.{u} :=
  A.restrict (AddCommGroup.primaryComponent A p)

/-- The `n`-primary component of a finite bilinear module is an additive `n`-group. -/
theorem isAddPGroup_primaryComponent (A : FiniteBilinearModule.{u}) (n : ℕ) :
    IsAddPGroup n (A.primaryComponent n) :=
  AddCommGroup.primaryComponent.isAddPGroup A n

/-- An isometry of finite bilinear modules restricts to an isometry between their `n`-primary
components. -/
def Isometry.primaryComponent {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
    (f : A.Isometry B) (n : ℕ) : (A.primaryComponent n).Isometry (B.primaryComponent n) where
  toAddEquiv :=
    { toFun := fun x ↦ ⟨f x.1, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      invFun := fun y ↦ ⟨f.symm y.1, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      left_inv := fun x ↦ Subtype.ext (f.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (f.apply_symm_apply y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add f x.1 y.1) }
  map_pairing' x y := f.map_pairing x.1 y.1

@[simp]
theorem Isometry.coe_primaryComponent_apply {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : A.Isometry B) (n : ℕ) (x : A.primaryComponent n) :
    (f.primaryComponent n x : B) = f x.1 := by
  rfl

@[simp]
theorem Isometry.coe_primaryComponent_symm_apply {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : A.Isometry B) (n : ℕ) (y : B.primaryComponent n) :
    ((f.primaryComponent n).symm y : A) = f.symm y.1 := by
  rw [← coe_toAddEquiv, symm_toAddEquiv]
  rfl

/-- The `n`-primary component of an orthogonal direct sum of finite bilinear modules splits as the
orthogonal direct sum of their `n`-primary components. -/
def primaryComponentProdIsometry (A : FiniteBilinearModule.{u}) (B : FiniteBilinearModule.{v})
    (n : ℕ) :
    ((A.prod B).primaryComponent n).Isometry
      ((A.primaryComponent n).prod (B.primaryComponent n)) where
  toAddEquiv := AddCommGroup.primaryComponentProdAddEquiv A B n
  map_pairing' x y := by
    rw [prod_pairing, restrict_pairing, restrict_pairing, restrict_pairing,
      AddCommGroup.primaryComponentProdAddEquiv_apply_fst,
      AddCommGroup.primaryComponentProdAddEquiv_apply_fst,
      AddCommGroup.primaryComponentProdAddEquiv_apply_snd,
      AddCommGroup.primaryComponentProdAddEquiv_apply_snd, prod_pairing]

@[simp]
theorem coe_primaryComponentProdIsometry_apply_fst (A : FiniteBilinearModule.{u})
    (B : FiniteBilinearModule.{v}) (n : ℕ) (x : (A.prod B).primaryComponent n) :
    ((primaryComponentProdIsometry A B n x).1 : A) = x.1.1 :=
  AddCommGroup.primaryComponentProdAddEquiv_apply_fst A.carrier B.carrier n x

@[simp]
theorem coe_primaryComponentProdIsometry_apply_snd (A : FiniteBilinearModule.{u})
    (B : FiniteBilinearModule.{v}) (n : ℕ) (x : (A.prod B).primaryComponent n) :
    ((primaryComponentProdIsometry A B n x).2 : B) = x.1.2 :=
  AddCommGroup.primaryComponentProdAddEquiv_apply_snd A.carrier B.carrier n x

@[simp]
theorem coe_primaryComponentProdIsometry_symm_apply (A : FiniteBilinearModule.{u})
    (B : FiniteBilinearModule.{v}) (n : ℕ) (x : A.primaryComponent n) (y : B.primaryComponent n) :
    ((primaryComponentProdIsometry A B n).symm (x, y) : A.carrier × B.carrier) = (x.1, y.1) := by
  rw [← Isometry.coe_toAddEquiv, Isometry.symm_toAddEquiv]
  exact AddCommGroup.coe_primaryComponentProdAddEquiv_symm_apply A B n x y

/-- If the underlying group of `A` is already `n`-primary torsion, its `n`-primary component is
canonically isometric to `A`. -/
def primaryComponentIsometrySelfOfIsAddPGroup {A : FiniteBilinearModule.{u}} {n : ℕ}
    (hA : IsAddPGroup n A) : (A.primaryComponent n).Isometry A where
  toAddEquiv :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, AddCommGroup.mem_primaryComponent.mpr (hA x)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  map_pairing' _ _ := rfl

@[simp]
theorem primaryComponentIsometrySelfOfIsAddPGroup_apply {A : FiniteBilinearModule.{u}} {n : ℕ}
    (hA : IsAddPGroup n A) (x : A.primaryComponent n) :
    primaryComponentIsometrySelfOfIsAddPGroup hA x = x.1 := by
  rfl

@[simp]
theorem coe_primaryComponentIsometrySelfOfIsAddPGroup_symm_apply {A : FiniteBilinearModule.{u}}
    {n : ℕ} (hA : IsAddPGroup n A) (x : A) :
    ((primaryComponentIsometrySelfOfIsAddPGroup hA).symm x : A) = x := by
  rw [← Isometry.coe_toAddEquiv, Isometry.symm_toAddEquiv]
  rfl

/-- For distinct primes `p ≠ q`, the `p`-primary component of a `q`-primary finite bilinear module
is trivial. -/
theorem subsingleton_primaryComponent_of_isAddPGroup_of_ne {A : FiniteBilinearModule.{u}}
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hA : IsAddPGroup q A) :
    Subsingleton (A.primaryComponent p) := by
  refine subsingleton_of_forall_eq 0 fun ⟨x, hx⟩ ↦ Subtype.ext ?_
  obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.mp hx
  obtain ⟨n, hn⟩ := hA x
  exact eq_zero_of_coprime_nsmul_eq_zero (Nat.coprime_pow_primes m n hp hq hpq) hm hn

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- The `p`-primary component of a finite quadratic module: the restriction of the quadratic map
and polar pairing to `AddCommGroup.primaryComponent A p`. -/
abbrev primaryComponent (A : FiniteQuadraticModule.{u}) (p : ℕ) : FiniteQuadraticModule.{u} :=
  A.restrict (AddCommGroup.primaryComponent A p)

/-- The `n`-primary component of a finite quadratic module is an additive `n`-group. -/
theorem isAddPGroup_primaryComponent (A : FiniteQuadraticModule.{u}) (n : ℕ) :
    IsAddPGroup n (A.primaryComponent n) :=
  AddCommGroup.primaryComponent.isAddPGroup A n

/-- An isometry of finite quadratic modules restricts to an isometry between their `n`-primary
components. -/
def Isometry.primaryComponent {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : A.Isometry B) (n : ℕ) : (A.primaryComponent n).Isometry (B.primaryComponent n) where
  toLinearEquiv :=
    ({ toFun := fun x : AddCommGroup.primaryComponent A n ↦
        (⟨f x.1, by
          obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
          exact AddCommGroup.mem_primaryComponent.mpr
            ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩ : AddCommGroup.primaryComponent B n)
       invFun := fun y : AddCommGroup.primaryComponent B n ↦
        (⟨f.symm y.1, by
          obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.2
          exact AddCommGroup.mem_primaryComponent.mpr
            ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩ : AddCommGroup.primaryComponent A n)
       left_inv := fun x ↦ Subtype.ext (f.symm_apply_apply x.1)
       right_inv := fun y ↦ Subtype.ext (f.apply_symm_apply y.1)
       map_add' := fun x y ↦ Subtype.ext (map_add f x.1 y.1) } :
      AddCommGroup.primaryComponent A n ≃+ AddCommGroup.primaryComponent B n).toIntLinearEquiv
  map_app' x := f.map_app x.1

@[simp]
theorem Isometry.val_primaryComponent_apply {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : A.Isometry B) (n : ℕ) (x : A.primaryComponent n) :
    (f.primaryComponent n x).1 = f x.1 := by
  rfl

@[simp]
theorem Isometry.val_primaryComponent_symm_apply {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : A.Isometry B) (n : ℕ) (y : B.primaryComponent n) :
    ((f.primaryComponent n).symm y).1 = f.symm y.1 := by
  rfl

/-- The `n`-primary component of an orthogonal direct sum of finite quadratic modules splits as the
orthogonal direct sum of their `n`-primary components. -/
def primaryComponentProdIsometry (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v})
    (n : ℕ) :
    ((A.prod B).primaryComponent n).Isometry
      ((A.primaryComponent n).prod (B.primaryComponent n)) where
  toLinearEquiv := (AddCommGroup.primaryComponentProdAddEquiv A B n).toIntLinearEquiv
  map_app' x :=
    let x' : AddCommGroup.primaryComponent (A.carrier × B.carrier) n := x
    congrArg₂ (· + ·)
      (congrArg A.quadratic
        (AddCommGroup.primaryComponentProdAddEquiv_apply_fst A.carrier B.carrier n x'))
      (congrArg B.quadratic
        (AddCommGroup.primaryComponentProdAddEquiv_apply_snd A.carrier B.carrier n x'))

@[simp]
theorem val_primaryComponentProdIsometry_apply_fst (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) (n : ℕ) (x : (A.prod B).primaryComponent n) :
    ((primaryComponentProdIsometry A B n x).1).1 = x.1.1 :=
  AddCommGroup.primaryComponentProdAddEquiv_apply_fst A.carrier B.carrier n x

@[simp]
theorem val_primaryComponentProdIsometry_apply_snd (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) (n : ℕ) (x : (A.prod B).primaryComponent n) :
    ((primaryComponentProdIsometry A B n x).2).1 = x.1.2 :=
  AddCommGroup.primaryComponentProdAddEquiv_apply_snd A.carrier B.carrier n x

@[simp]
theorem val_primaryComponentProdIsometry_symm_apply (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) (n : ℕ) (x : A.primaryComponent n) (y : B.primaryComponent n) :
    ((primaryComponentProdIsometry A B n).symm (x, y)).1 = (x.1, y.1) := by
  exact AddCommGroup.coe_primaryComponentProdAddEquiv_symm_apply A B n x y

/-- If the underlying group of `A` is already `n`-primary torsion, its `n`-primary component is
canonically isometric to `A`. -/
def primaryComponentIsometrySelfOfIsAddPGroup {A : FiniteQuadraticModule.{u}} {n : ℕ}
    (hA : IsAddPGroup n A) : (A.primaryComponent n).Isometry A where
  toLinearEquiv :=
    ({ toFun := Subtype.val
       invFun := fun x ↦ ⟨x, AddCommGroup.mem_primaryComponent.mpr (hA x)⟩
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl
       map_add' := fun _ _ ↦ rfl } :
      AddCommGroup.primaryComponent A n ≃+ A).toIntLinearEquiv
  map_app' _ := rfl

@[simp]
theorem primaryComponentIsometrySelfOfIsAddPGroup_apply {A : FiniteQuadraticModule.{u}} {n : ℕ}
    (hA : IsAddPGroup n A) (x : A.primaryComponent n) :
    primaryComponentIsometrySelfOfIsAddPGroup hA x = x.1 := by
  rfl

@[simp]
theorem val_primaryComponentIsometrySelfOfIsAddPGroup_symm_apply {A : FiniteQuadraticModule.{u}}
    {n : ℕ} (hA : IsAddPGroup n A) (x : A) :
    ((primaryComponentIsometrySelfOfIsAddPGroup hA).symm x).1 = x := by
  rfl

/-- For distinct primes `p ≠ q`, the `p`-primary component of a `q`-primary finite quadratic module
is trivial. -/
theorem subsingleton_primaryComponent_of_isAddPGroup_of_ne {A : FiniteQuadraticModule.{u}}
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hA : IsAddPGroup q A) :
    Subsingleton (A.primaryComponent p) :=
  A.toFiniteBilinearModule.subsingleton_primaryComponent_of_isAddPGroup_of_ne hp hq hpq hA

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
