/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Subalgebra
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.Restricted.Jacobson
import TauCeti.Algebra.Lie.AdjointAction.Frobenius

/-!
# Restricted Lie algebras

A *restricted Lie algebra* (Jacobson 1941), or *`p`-Lie algebra*, is a Lie algebra `L` over a
commutative ring `R` together with a `p`-map `x ↦ x^[p]` which behaves like the `p`-th power in an
associative algebra of characteristic `p`:

* it is `p`-homogeneous, `(c • x)^[p] = c ^ p • x^[p]`;
* its adjoint action is the `p`-th power of that of `x`, `ad (x^[p]) = (ad x) ^ p`;
* it satisfies Jacobson's formula, `(x + y)^[p] = x^[p] + y^[p] + Λ_p(x, y)`, where `Λ_p` is
  Jacobson's Lie polynomial `TauCeti.LieAlgebra.jacobson`.

Additivity is not the right axiom: in `2 × 2` matrices over `ZMod p` for an odd prime `p`, the
Frobenius is not additive (`TauCeti.LieAlgebra.jacobson_single_single`), and the Lie term `Λ_p` is
what corrects it. Moreover, the `p`-map is genuine data rather than a property: on an abelian Lie
algebra `R` of prime characteristic `p` with `1 ≠ 0`, `pMap = 0` (`ofAbelianZero`) and
`pMap x = x ^ p` (`ofAssociativeAlgebra`) are two distinct restricted structures on the same Lie
algebra.

The basic example is an associative `R`-algebra `A` of exponential characteristic `p` with
`x^[p] = x ^ p` (`TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra`), in particular
`Module.End R M` whenever `[ExpChar (Module.End R M) p]` holds. Separately, for any `R`-module
`M` (including trivial modules and modules over mixed-characteristic base rings `R`) annihilated
pointwise by a prime `p`, `TauCeti.RestrictedLieAlgebra.ofModuleEnd` constructs the restricted
structure `f ↦ f ^ p` on `Module.End R M`, agreeing with `ofAssociativeAlgebra` when
`[ExpChar (Module.End R M) p]` holds (`ofModuleEnd_eq_ofAssociativeAlgebra`). Since the
commutator Lie ring of `A` is only a local instance, these structures are definitions rather than
instances. A Lie subalgebra of a restricted Lie algebra which is closed under the `p`-map
inherits a restricted structure (`LieSubalgebra.restrictedLieAlgebra`, bundled as
`TauCeti.RestrictedLieSubalgebra`), and so does the source of any injective Lie algebra morphism
compatible with given `p`-maps (`Function.Injective.restrictedLieAlgebra`). The derivations of a
commutative algebra of exponential characteristic `p` form a restricted Lie algebra under
`D ↦ D^[p]`; that instance is in `TauCeti.RingTheory.Derivation.PPow`.

## Main definitions

* `TauCeti.RestrictedLieAlgebra R L p`: a Lie algebra with a `p`-map `RestrictedLieAlgebra.pMap`.
* `TauCeti.RestrictedLieHom R L L' p`: a Lie algebra morphism commuting with the `p`-maps.
* `TauCeti.RestrictedLieHom.id`, `TauCeti.RestrictedLieHom.comp`: identity and composition.
* `TauCeti.RestrictedLieHom.ad`: `LieAlgebra.ad R L` as a restricted morphism into
  `ofAssociativeAlgebra`, assuming `[ExpChar (Module.End R L) p]`.
* `TauCeti.RestrictedLieSubalgebra R L p`: a bundled Lie subalgebra closed under `pMap`, with
  induced restricted structure, partial order with `⊤`, `⊥`, and `⊓`, `RestrictedLieHom.range`,
  and `RestrictedLieHom.rangeRestrict`.
* `TauCeti.RestrictedLieIdeal R L p`: a bundled Lie ideal closed under `pMap`, with induced
  restricted structure, partial order with `⊤`, `⊥`, and `⊓`, and `RestrictedLieHom.ker`.
* `TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra`: the restricted structure `a ↦ a ^ p` on an
  associative algebra of exponential characteristic `p`.
* `TauCeti.RestrictedLieAlgebra.ofModuleEnd`: the restricted structure `f ↦ f ^ p` on
  `Module.End R M` when prime `p` annihilates `M` pointwise.
* `TauCeti.RestrictedLieAlgebra.ofAbelianZero`: the zero `p`-map on an abelian Lie algebra for
  `p ≠ 0`.
* `AlgHom.toRestrictedLieHom`: an algebra morphism is a morphism of these restricted structures.
* `Function.Injective.restrictedLieAlgebra`: the restricted structure pulled back along an
  injective Lie algebra morphism.
* `LieSubalgebra.restrictedLieAlgebra`: the restricted structure on a Lie subalgebra closed under
  the `p`-map.

## Main statements

* `TauCeti.RestrictedLieAlgebra.subsingleton_of_eq_zero`: for `p = 0` the axioms force `L` to be
  trivial.
* `TauCeti.RestrictedLieAlgebra.pMap_add_of_lie_eq_zero`: the `p`-map is additive on commuting
  elements.
* `TauCeti.RestrictedLieAlgebra.pMap_sum_of_lie_eq_zero`: the `p`-map commutes with finite sums of
  pairwise commuting elements.
* `TauCeti.RestrictedLieHom.pMap_mem_ker`, `TauCeti.RestrictedLieHom.ker_eq_bot`: the kernel of
  a restricted morphism is a restricted ideal, and is trivial iff the morphism is injective.

## References

* N. Jacobson, *Restricted Lie algebras of characteristic p*, Trans. Amer. Math. Soc. **50**
  (1941), 15–25.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V, §7.
* H. Strade, R. Farnsteiner, *Modular Lie Algebras and their Representations*, Marcel Dekker
  (1988), Chapter 2.
-/

public section

open TauCeti.LieAlgebra

namespace TauCeti

/-- A **restricted Lie algebra** (Jacobson): a Lie algebra `L` over `R` with a `p`-map
`pMap R p : L → L` which is `p`-homogeneous, whose adjoint action is the `p`-th power of the adjoint
action, and which satisfies Jacobson's formula
`pMap R p (x + y) = pMap R p x + pMap R p y + Λ_p(x, y)`. -/
class RestrictedLieAlgebra (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ) where
  /-- The `p`-map `x ↦ x^[p]`. -/
  pMap : L → L
  /-- The `p`-map is `p`-homogeneous. -/
  pMap_smul (c : R) (x : L) : pMap (c • x) = c ^ p • pMap x
  /-- The adjoint action of `x^[p]` is the `p`-th power of the adjoint action of `x`. -/
  ad_pMap (x : L) : LieAlgebra.ad R L (pMap x) = LieAlgebra.ad R L x ^ p
  /-- **Jacobson's formula** for the `p`-map. -/
  pMap_add (x y : L) : pMap (x + y) = pMap x + pMap y + jacobson p x y

namespace RestrictedLieAlgebra

/-- Two restricted Lie algebra structures on the same Lie algebra are equal if and only if their
`p`-maps agree pointwise. -/
@[ext]
theorem ext {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
    {i j : RestrictedLieAlgebra R L p} (h : ∀ x, i.pMap x = j.pMap x) : i = j := by
  cases i
  cases j
  congr
  exact funext h

section Basic

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
  [RestrictedLieAlgebra R L p]

/-- The bracket with `x^[p]` is the `p`-fold iterated bracket with `x`. -/
theorem pMap_lie (x y : L) : ⁅pMap R p x, y⁆ = (LieAlgebra.ad R L x ^ p) y := by
  rw [← ad_pMap, LieAlgebra.ad_apply]

/-- For `p = 0` the axioms force `L` to be trivial: `ad (x^[0]) = 1`, so `⁅x^[0], y⁆ = y` for all
`y`, which for `y = x^[0]` gives `x^[0] = 0` and then `y = ⁅0, y⁆ = 0`. -/
theorem subsingleton_of_eq_zero (R : Type*) [CommRing R] [LieAlgebra R L]
    [RestrictedLieAlgebra R L p] (hp : p = 0) : Subsingleton L := by
  subst hp
  have h (x y : L) : ⁅pMap R 0 x, y⁆ = y := by simp [pMap_lie]
  have h0 : pMap R 0 (0 : L) = 0 := by simpa using (h 0 (pMap R 0 0)).symm
  exact ⟨fun y z ↦ by rw [← h 0 y, ← h 0 z, h0, zero_lie, zero_lie]⟩

/-- The `p`-map sends `0` to `0`. -/
@[simp]
theorem pMap_zero : pMap R p (0 : L) = 0 := by
  rcases eq_or_ne p 0 with hp | hp
  · have := subsingleton_of_eq_zero (L := L) R hp
    exact Subsingleton.elim _ _
  · simpa [zero_pow hp] using pMap_smul (R := R) (p := p) (0 : R) (0 : L)

/-- `x^[p]` commutes with `x`. -/
@[simp]
theorem pMap_lie_self (x : L) : ⁅pMap R p x, x⁆ = 0 := by
  rcases eq_or_ne p 0 with hp | hp
  · have := subsingleton_of_eq_zero (L := L) R hp
    exact Subsingleton.elim _ _
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    simp [pMap_lie, pow_succ]

/-- `(-x)^[p] = (-1) ^ p • x^[p]`. -/
theorem pMap_neg (x : L) : pMap R p (-x) = (-1 : R) ^ p • pMap R p x := by
  rw [← pMap_smul, neg_one_smul]

/-- For odd `p`, `(-x)^[p] = -x^[p]`. -/
theorem pMap_neg_of_odd (hp : Odd p) (x : L) : pMap R p (-x) = -pMap R p x := by
  rw [pMap_neg, hp.neg_one_pow, neg_one_smul]

/-- For even `p`, `(-x)^[p] = x^[p]`. -/
theorem pMap_neg_of_even (hp : Even p) (x : L) : pMap R p (-x) = pMap R p x := by
  rw [pMap_neg, hp.neg_one_pow, one_smul]

/-- The `p`-map is additive on commuting elements, where Jacobson's correction term vanishes. -/
theorem pMap_add_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap R p (x + y) = pMap R p x + pMap R p y := by
  rw [pMap_add, jacobson_eq_zero_of_lie_eq_zero p h, add_zero]

/-- On commuting elements `x, y`, `(x - y)^[p] = x^[p] + (-1) ^ p • y^[p]`. -/
theorem pMap_sub_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap R p (x - y) = pMap R p x + (-1 : R) ^ p • pMap R p y := by
  rw [sub_eq_add_neg, pMap_add_of_lie_eq_zero (by rw [lie_neg, h, neg_zero]), pMap_neg]

/-- In an abelian restricted Lie algebra, `pMap` is additive. -/
theorem pMap_add_of_isLieAbelian [IsLieAbelian L] (x y : L) :
    pMap R p (x + y) = pMap R p x + pMap R p y :=
  pMap_add_of_lie_eq_zero (trivial_lie_zero L L x y)

/-- On a finite family of pairwise commuting elements, `pMap` commutes with the finite sum. -/
theorem pMap_sum_of_lie_eq_zero {ι : Type*} {s : Finset ι} {f : ι → L}
    (h : (s : Set ι).Pairwise fun i j ↦ ⁅f i, f j⁆ = 0) :
    pMap R p (∑ i ∈ s, f i) = ∑ i ∈ s, pMap R p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert] at h
    have h' := Set.pairwise_insert.mp h
    have hcomm : ⁅f a, ∑ i ∈ s, f i⁆ = 0 := by
      rw [lie_sum]
      exact Finset.sum_eq_zero fun i hi ↦ (h'.2 i hi (ne_of_mem_of_not_mem hi ha).symm).1
    rw [Finset.sum_insert ha, pMap_add_of_lie_eq_zero hcomm, ih h'.1, Finset.sum_insert ha]

/-- In an abelian restricted Lie algebra, `pMap` commutes with finite sums. -/
theorem pMap_sum_of_isLieAbelian [IsLieAbelian L] {ι : Type*} (s : Finset ι) (f : ι → L) :
    pMap R p (∑ i ∈ s, f i) = ∑ i ∈ s, pMap R p (f i) :=
  pMap_sum_of_lie_eq_zero fun _ _ _ _ _ ↦ trivial_lie_zero L L _ _

end Basic

/-- The trivial (zero) restricted Lie algebra structure on an abelian Lie algebra for `p ≠ 0`. -/
@[instance_reducible]
def ofAbelianZero (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [IsLieAbelian L] (p : ℕ) (hp : p ≠ 0) : RestrictedLieAlgebra R L p where
  pMap _ := 0
  pMap_smul _ _ := (smul_zero _).symm
  ad_pMap x := by
    have h0 : LieAlgebra.ad R L x = 0 := by
      ext y
      exact trivial_lie_zero L L x y
    rw [map_zero, h0, zero_pow hp]
  pMap_add x y := by
    rw [add_zero, jacobson_eq_zero_of_lie_eq_zero p (trivial_lie_zero L L x y), add_zero]

/-- The `p`-map of `ofAbelianZero` is the zero map. -/
@[simp]
theorem ofAbelianZero_pMap (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [IsLieAbelian L] (p : ℕ) (hp : p ≠ 0) (x : L) :
    (ofAbelianZero R L p hp).pMap x = 0 :=
  (rfl)

/-! ### The restricted structure of an associative algebra -/

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] (p : ℕ) [ExpChar A p]

/-- An associative `R`-algebra `A` of exponential characteristic `p`, with the commutator bracket,
is a restricted Lie algebra under `a ↦ a ^ p`: the adjoint action is compatible by
`TauCeti.LieAlgebra.ad_pow_expChar_pow` and Jacobson's formula is
`TauCeti.LieAlgebra.add_pow_eq_jacobson`. This applies in particular to `Module.End R M`. It is
not an instance because the commutator Lie ring `LieRing.ofAssociativeRing` is not one. -/
abbrev ofAssociativeAlgebra : RestrictedLieAlgebra R A p where
  pMap a := a ^ p
  pMap_smul c a := smul_pow c a p
  ad_pMap a := by simpa using ad_pow_expChar_pow (R := R) p a 1
  pMap_add a b := add_pow_eq_jacobson p a b

variable {R A p}

/-- The `p`-map of `ofAssociativeAlgebra` is the `p`-th power. -/
@[simp]
theorem pMap_ofAssociativeAlgebra (a : A) :
    letI := ofAssociativeAlgebra R A p
    pMap R p a = a ^ p :=
  (rfl)

/-- The restricted Lie algebra structure `f ↦ f ^ p` on `Module.End R M` for prime `p`, whenever
`p` annihilates `M` pointwise (`∀ m : M, p • m = 0`). Valid for every such `R`-module `M`,
including trivial modules and modules over mixed-characteristic base rings `R`. -/
@[instance_reducible]
def ofModuleEnd (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) :
    RestrictedLieAlgebra R (Module.End R M) p :=
  have hfields :
      (∀ f : Module.End R M,
        LieAlgebra.ad R (Module.End R M) (f ^ p) = LieAlgebra.ad R (Module.End R M) f ^ p) ∧
      (∀ f g : Module.End R M, (f + g) ^ p = f ^ p + g ^ p + jacobson p f g) := by
    rcases subsingleton_or_nontrivial M with _ | _
    · exact ⟨fun _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
    · have : CharP (Module.End R M) p :=
        (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by ext m; simp [hM m])
      have : ExpChar (Module.End R M) p := ExpChar.prime Fact.out
      exact
        ⟨fun f ↦ (ofAssociativeAlgebra R (Module.End R M) p).ad_pMap f,
         fun f g ↦ (ofAssociativeAlgebra R (Module.End R M) p).pMap_add f g⟩
  { pMap f := f ^ p
    pMap_smul c f := smul_pow c f p
    ad_pMap := hfields.1
    pMap_add := hfields.2 }

/-- The `p`-map of `ofModuleEnd` is the ordinary `p`-th power `f ↦ f ^ p`. -/
@[simp]
theorem ofModuleEnd_pMap (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) (f : Module.End R M) :
    (ofModuleEnd R M p hM).pMap f = f ^ p :=
  (rfl)

/-- When `Module.End R M` has exponential characteristic `p`, `ofModuleEnd` agrees with
`ofAssociativeAlgebra`. -/
theorem ofModuleEnd_eq_ofAssociativeAlgebra (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0)
    [ExpChar (Module.End R M) p] :
    ofModuleEnd R M p hM = ofAssociativeAlgebra R (Module.End R M) p :=
  ext fun _ ↦ rfl

end Associative

end RestrictedLieAlgebra

open RestrictedLieAlgebra

/-! ### Morphisms -/

/-- A **morphism of restricted Lie algebras**: a Lie algebra morphism commuting with the
`p`-maps. -/
structure RestrictedLieHom (R L L' : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] (p : ℕ) [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] extends L →ₗ⁅R⁆ L' where
  /-- The morphism commutes with the `p`-maps. -/
  map_pMap' (x : L) : toFun (pMap R p x) = pMap R p (toFun x)

namespace RestrictedLieHom

variable {R L L' L'' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L''] {p : ℕ} [RestrictedLieAlgebra R L p]
  [RestrictedLieAlgebra R L' p] [RestrictedLieAlgebra R L'' p]

instance : FunLike (RestrictedLieHom R L L' p) L L' where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨f, _⟩ := f
    obtain ⟨g, _⟩ := g
    congr
    exact LieHom.coe_injective h

instance : LinearMapClass (RestrictedLieHom R L L' p) R L L' where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'

/-- The underlying function of the underlying Lie algebra morphism. -/
@[simp]
theorem coe_toLieHom (f : RestrictedLieHom R L L' p) : ⇑f.toLieHom = f :=
  (rfl)

/-- Evaluating the underlying Lie algebra morphism agrees with evaluating `f`. -/
@[simp]
theorem toLieHom_apply (f : RestrictedLieHom R L L' p) (x : L) : f.toLieHom x = f x :=
  (rfl)

/-- The underlying function of a restricted morphism built from a Lie algebra morphism. -/
@[simp]
theorem coe_mk (f : L →ₗ⁅R⁆ L') (h) : ⇑(⟨f, h⟩ : RestrictedLieHom R L L' p) = f :=
  (rfl)

/-- The underlying Lie algebra morphism of `⟨f, h⟩` is `f`. -/
@[simp]
theorem toLieHom_mk (f : L →ₗ⁅R⁆ L') (h) :
    (⟨f, h⟩ : RestrictedLieHom R L L' p).toLieHom = f :=
  (rfl)

/-- Rebuilding a restricted morphism from its underlying Lie algebra morphism gives it back. -/
@[simp]
theorem mk_coe (f : RestrictedLieHom R L L' p) (h) :
    (⟨f.toLieHom, h⟩ : RestrictedLieHom R L L' p) = f :=
  (rfl)

/-- A restricted morphism preserves brackets. -/
@[simp]
theorem map_lie (f : RestrictedLieHom R L L' p) (x y : L) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  f.toLieHom.map_lie x y

/-- A restricted morphism commutes with the `p`-maps. -/
@[simp]
theorem map_pMap (f : RestrictedLieHom R L L' p) (x : L) : f (pMap R p x) = pMap R p (f x) :=
  f.map_pMap' x

@[ext]
theorem ext {f g : RestrictedLieHom R L L' p} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- A restricted morphism is determined by its underlying Lie algebra morphism. -/
theorem toLieHom_injective :
    Function.Injective (toLieHom : RestrictedLieHom R L L' p → L →ₗ⁅R⁆ L') :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

variable (R L p) in
/-- The identity of a restricted Lie algebra, as a restricted morphism. -/
def id : RestrictedLieHom R L L p where
  __ := LieHom.id
  map_pMap' _ := rfl

@[simp]
theorem coe_id : ⇑(RestrictedLieHom.id R L p) = _root_.id :=
  (rfl)

@[simp]
theorem id_apply (x : L) : RestrictedLieHom.id R L p x = x :=
  (rfl)

@[simp]
theorem toLieHom_id : (RestrictedLieHom.id R L p).toLieHom = LieHom.id :=
  (rfl)

/-- The composition of restricted morphisms. -/
def comp (g : RestrictedLieHom R L' L'' p) (f : RestrictedLieHom R L L' p) :
    RestrictedLieHom R L L'' p where
  __ := g.toLieHom.comp f.toLieHom
  map_pMap' x := by simp

@[simp]
theorem coe_comp (g : RestrictedLieHom R L' L'' p) (f : RestrictedLieHom R L L' p) :
    ⇑(g.comp f) = g ∘ f :=
  (rfl)

@[simp]
theorem comp_apply (g : RestrictedLieHom R L' L'' p) (f : RestrictedLieHom R L L' p) (x : L) :
    g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem toLieHom_comp (g : RestrictedLieHom R L' L'' p) (f : RestrictedLieHom R L L' p) :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom :=
  (rfl)

@[simp]
theorem comp_id (f : RestrictedLieHom R L L' p) : f.comp (.id R L p) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem id_comp (f : RestrictedLieHom R L L' p) : (RestrictedLieHom.id R L' p).comp f = f :=
  ext fun _ ↦ rfl

theorem comp_assoc {L''' : Type*} [LieRing L'''] [LieAlgebra R L''']
    [RestrictedLieAlgebra R L''' p] (h : RestrictedLieHom R L'' L''' p)
    (g : RestrictedLieHom R L' L'' p) (f : RestrictedLieHom R L L' p) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ ↦ rfl

/-- The kernel of a restricted morphism, a Lie ideal, is closed under the `p`-map: it is a
restricted ideal. -/
theorem pMap_mem_ker (f : RestrictedLieHom R L L' p) {x : L} (hx : x ∈ f.toLieHom.ker) :
    pMap R p x ∈ f.toLieHom.ker := by
  simp_all [LieHom.mem_ker]

section Adjoint

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint representation `LieAlgebra.ad R L : L →ₗ⁅R⁆ Module.End R L` of a restricted Lie
algebra, as a morphism of restricted Lie algebras into `ofAssociativeAlgebra`, assuming
`[ExpChar (Module.End R L) p]`. -/
def ad (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [RestrictedLieAlgebra R L p] [ExpChar (Module.End R L) p] :
    letI := ofAssociativeAlgebra R (Module.End R L) p
    RestrictedLieHom R L (Module.End R L) p :=
  letI := ofAssociativeAlgebra R (Module.End R L) p
  { LieAlgebra.ad R L with map_pMap' x := ad_pMap x }

@[simp]
theorem ad_apply (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [RestrictedLieAlgebra R L p] [ExpChar (Module.End R L) p] (x : L) :
    letI := ofAssociativeAlgebra R (Module.End R L) p
    ad R L p x = LieAlgebra.ad R L x :=
  (rfl)

@[simp]
theorem toLieHom_ad (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [RestrictedLieAlgebra R L p] [ExpChar (Module.End R L) p] :
    letI := ofAssociativeAlgebra R (Module.End R L) p
    (ad R L p).toLieHom = LieAlgebra.ad R L :=
  (rfl)

end Adjoint

end RestrictedLieHom

end TauCeti

open TauCeti TauCeti.RestrictedLieAlgebra

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- An algebra morphism preserves `p`-th powers, so it is a morphism of the restricted Lie
algebras `RestrictedLieAlgebra.ofAssociativeAlgebra`. -/
def AlgHom.toRestrictedLieHom (f : A →ₐ[R] B) (p : ℕ) [ExpChar A p] [ExpChar B p] :
    letI := ofAssociativeAlgebra R A p
    letI := ofAssociativeAlgebra R B p
    RestrictedLieHom R A B p :=
  letI := ofAssociativeAlgebra R A p
  letI := ofAssociativeAlgebra R B p
  { f.toLieHom with map_pMap' a := map_pow f a p }

@[simp]
theorem AlgHom.toRestrictedLieHom_apply (f : A →ₐ[R] B) (p : ℕ) [ExpChar A p] [ExpChar B p]
    (a : A) :
    letI := ofAssociativeAlgebra R A p
    letI := ofAssociativeAlgebra R B p
    f.toRestrictedLieHom p a = f a :=
  (rfl)

end Associative

section Injective

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]

/-- **Pulling back a restricted structure.** If `f : L' → L` is an injective Lie algebra morphism
into a restricted Lie algebra and `q : L' → L'` satisfies `f (q x) = pMap R p (f x)`, then `q` is
a `p`-map on `L'`. -/
protected abbrev Function.Injective.restrictedLieAlgebra {f : L' →ₗ⁅R⁆ L}
    (hf : Function.Injective f) (q : L' → L') (hq : ∀ x, f (q x) = pMap R p (f x)) :
    RestrictedLieAlgebra R L' p where
  pMap := q
  pMap_smul c x := hf <| by simp [hq, pMap_smul]
  ad_pMap x := LinearMap.ext fun y ↦ hf <| by simp [hq, pMap_lie, LieHom.map_ad_pow]
  pMap_add x y := hf <| by simp [hq, pMap_add, LieHom.map_jacobson]

/-- The `p`-map pulled back along `f` is `q`. -/
@[simp]
theorem Function.Injective.pMap_restrictedLieAlgebra {f : L' →ₗ⁅R⁆ L}
    (hf : Function.Injective f) (q : L' → L') (hq : ∀ x, f (q x) = pMap R p (f x)) (x : L') :
    letI := hf.restrictedLieAlgebra q hq
    pMap R p x = q x :=
  (rfl)

/-- `f` is a restricted morphism for the restricted structure pulled back along it. -/
def Function.Injective.restrictedLieHom {f : L' →ₗ⁅R⁆ L} (hf : Function.Injective f) (q : L' → L')
    (hq : ∀ x, f (q x) = pMap R p (f x)) :
    letI := hf.restrictedLieAlgebra q hq
    RestrictedLieHom R L' L p :=
  letI := hf.restrictedLieAlgebra q hq
  { f with map_pMap' := hq }

@[simp]
theorem Function.Injective.restrictedLieHom_apply {f : L' →ₗ⁅R⁆ L} (hf : Function.Injective f)
    (q : L' → L') (hq : ∀ x, f (q x) = pMap R p (f x)) (x : L') :
    letI := hf.restrictedLieAlgebra q hq
    hf.restrictedLieHom q hq x = f x :=
  (rfl)

end Injective

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
  [RestrictedLieAlgebra R L p]

/-- A Lie subalgebra closed under the `p`-map is a restricted Lie algebra, with the induced
`p`-map. -/
abbrev restrictedLieAlgebra (K : LieSubalgebra R L) (hK : ∀ x ∈ K, pMap R p x ∈ K) :
    RestrictedLieAlgebra R K p :=
  (K.coe_incl ▸ Subtype.val_injective : Function.Injective K.incl).restrictedLieAlgebra
    (fun x ↦ ⟨pMap R p x, hK x x.property⟩) fun _ ↦ rfl

/-- The induced `p`-map on a Lie subalgebra is the restriction of the `p`-map. -/
@[simp]
theorem coe_pMap (K : LieSubalgebra R L) (hK : ∀ x ∈ K, pMap R p x ∈ K) (x : K) :
    letI := K.restrictedLieAlgebra hK
    ((pMap R p x : K) : L) = pMap R p (x : L) :=
  (rfl)

end LieSubalgebra

namespace TauCeti

section Subalgebra

/-- A restricted Lie subalgebra of a restricted Lie algebra `L`: a Lie subalgebra closed under
the `p`-map `RestrictedLieAlgebra.pMap`. -/
structure RestrictedLieSubalgebra (R L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] (p : ℕ) [RestrictedLieAlgebra R L p] extends LieSubalgebra R L where
  /-- Closure under `pMap`. -/
  pMap_mem' {x : L} : x ∈ carrier → RestrictedLieAlgebra.pMap R p x ∈ carrier

namespace RestrictedLieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
  [RestrictedLieAlgebra R L p]

instance : SetLike (RestrictedLieSubalgebra R L p) L where
  coe S := S.carrier
  coe_injective S T h := by cases S; cases T; congr; exact SetLike.coe_injective h

instance : AddSubgroupClass (RestrictedLieSubalgebra R L p) L where
  add_mem {S} := S.toLieSubalgebra.add_mem
  zero_mem S := S.toLieSubalgebra.zero_mem
  neg_mem {S} := S.toLieSubalgebra.neg_mem

instance : SMulMemClass (RestrictedLieSubalgebra R L p) R L where
  smul_mem {S} := S.toLieSubalgebra.smul_mem

theorem toLieSubalgebra_injective :
    Function.Injective (toLieSubalgebra : RestrictedLieSubalgebra R L p → LieSubalgebra R L) := by
  intro S T h; cases S; cases T; cases h; rfl

@[ext]
theorem ext {S T : RestrictedLieSubalgebra R L p} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_toLieSubalgebra {S : RestrictedLieSubalgebra R L p} {x : L} :
    x ∈ S.toLieSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toLieSubalgebra (S : RestrictedLieSubalgebra R L p) :
    (S.toLieSubalgebra : Set L) = S :=
  (rfl)

/-- A restricted Lie subalgebra is closed under `RestrictedLieAlgebra.pMap`. -/
theorem pMap_mem (S : RestrictedLieSubalgebra R L p) {x : L} (hx : x ∈ S) :
    RestrictedLieAlgebra.pMap R p x ∈ S :=
  S.pMap_mem' hx

theorem zero_mem (S : RestrictedLieSubalgebra R L p) : (0 : L) ∈ S :=
  S.toLieSubalgebra.zero_mem

theorem add_mem (S : RestrictedLieSubalgebra R L p) {x y : L} (hx : x ∈ S) (hy : y ∈ S) :
    x + y ∈ S :=
  S.toLieSubalgebra.add_mem hx hy

theorem neg_mem (S : RestrictedLieSubalgebra R L p) {x : L} (hx : x ∈ S) : -x ∈ S :=
  S.toLieSubalgebra.neg_mem hx

theorem sub_mem (S : RestrictedLieSubalgebra R L p) {x y : L} (hx : x ∈ S) (hy : y ∈ S) :
    x - y ∈ S :=
  S.toLieSubalgebra.sub_mem hx hy

theorem smul_mem (S : RestrictedLieSubalgebra R L p) (c : R) {x : L} (hx : x ∈ S) :
    c • x ∈ S :=
  S.toLieSubalgebra.smul_mem c hx

theorem lie_mem (S : RestrictedLieSubalgebra R L p) {x y : L} (hx : x ∈ S) (hy : y ∈ S) :
    ⁅x, y⁆ ∈ S :=
  S.toLieSubalgebra.lie_mem hx hy

instance instLieRing (S : RestrictedLieSubalgebra R L p) : LieRing S :=
  S.toLieSubalgebra.lieRing

instance instLieAlgebra (S : RestrictedLieSubalgebra R L p) : LieAlgebra R S :=
  S.toLieSubalgebra.lieAlgebra

@[simp]
theorem coe_zero (S : RestrictedLieSubalgebra R L p) : ((0 : S) : L) = 0 :=
  (rfl)

@[simp]
theorem coe_add (S : RestrictedLieSubalgebra R L p) (x y : S) : ((x + y : S) : L) = x + y :=
  (rfl)

@[simp]
theorem coe_neg (S : RestrictedLieSubalgebra R L p) (x : S) : ((-x : S) : L) = -x :=
  (rfl)

@[simp]
theorem coe_sub (S : RestrictedLieSubalgebra R L p) (x y : S) : ((x - y : S) : L) = x - y :=
  (rfl)

@[simp]
theorem coe_smul (S : RestrictedLieSubalgebra R L p) (c : R) (x : S) : ((c • x : S) : L) = c • x :=
  (rfl)

@[simp]
theorem coe_lie (S : RestrictedLieSubalgebra R L p) (x y : S) :
    ((⁅x, y⁆ : S) : L) = ⁅(x : L), (y : L)⁆ :=
  (rfl)

/-- A restricted Lie subalgebra inherits a restricted Lie algebra structure from the ambient
restricted Lie algebra. -/
instance instRestrictedLieAlgebra (S : RestrictedLieSubalgebra R L p) :
    RestrictedLieAlgebra R S p :=
  S.toLieSubalgebra.restrictedLieAlgebra fun _ hx ↦ S.pMap_mem hx

/-- The `p`-map on a restricted Lie subalgebra coerces to the ambient `p`-map. -/
@[simp]
theorem coe_pMap (S : RestrictedLieSubalgebra R L p) (x : S) :
    ((RestrictedLieAlgebra.pMap R p x : S) : L) = RestrictedLieAlgebra.pMap R p (x : L) :=
  (rfl)

/-- The canonical inclusion `S → L` of a restricted Lie subalgebra as a restricted morphism. -/
def incl (S : RestrictedLieSubalgebra R L p) : RestrictedLieHom R S L p where
  toLieHom := S.toLieSubalgebra.incl
  map_pMap' _ := rfl

@[simp]
theorem incl_apply (S : RestrictedLieSubalgebra R L p) (x : S) : S.incl x = x :=
  (rfl)

@[simp]
theorem toLieHom_incl (S : RestrictedLieSubalgebra R L p) :
    S.incl.toLieHom = S.toLieSubalgebra.incl :=
  (rfl)

theorem incl_injective (S : RestrictedLieSubalgebra R L p) : Function.Injective S.incl :=
  Subtype.val_injective

instance : PartialOrder (RestrictedLieSubalgebra R L p) :=
  .ofSetLike (RestrictedLieSubalgebra R L p)

theorem le_def {S T : RestrictedLieSubalgebra R L p} : S ≤ T ↔ (S : Set L) ⊆ T :=
  Iff.rfl

@[simp]
theorem toLieSubalgebra_le_toLieSubalgebra {S T : RestrictedLieSubalgebra R L p} :
    S.toLieSubalgebra ≤ T.toLieSubalgebra ↔ S ≤ T :=
  Iff.rfl

@[simp]
theorem toLieSubalgebra_inj {S T : RestrictedLieSubalgebra R L p} :
    S.toLieSubalgebra = T.toLieSubalgebra ↔ S = T :=
  toLieSubalgebra_injective.eq_iff

instance : OrderTop (RestrictedLieSubalgebra R L p) where
  top :=
    { toLieSubalgebra := ⊤
      pMap_mem' := fun _ ↦ Set.mem_univ _ }
  le_top _ _ _ := Set.mem_univ _

@[simp]
theorem toLieSubalgebra_top :
    ((⊤ : RestrictedLieSubalgebra R L p).toLieSubalgebra) = ⊤ :=
  (rfl)

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : RestrictedLieSubalgebra R L p) :=
  Set.mem_univ x

instance : OrderBot (RestrictedLieSubalgebra R L p) where
  bot :=
    { toLieSubalgebra := ⊥
      pMap_mem' := fun {x} hx ↦ by
        have hx0 : x = 0 := (LieSubalgebra.mem_bot (R := R) x).mp hx
        exact (LieSubalgebra.mem_bot (R := R) _).mpr <| by
          rw [hx0, RestrictedLieAlgebra.pMap_zero] }
  bot_le S x hx := by
    have hx0 : x = 0 := (LieSubalgebra.mem_bot (R := R) x).mp hx
    rw [hx0]
    exact S.zero_mem

@[simp]
theorem toLieSubalgebra_bot :
    ((⊥ : RestrictedLieSubalgebra R L p).toLieSubalgebra) = ⊥ :=
  (rfl)

@[simp]
theorem mem_bot {x : L} : x ∈ (⊥ : RestrictedLieSubalgebra R L p) ↔ x = 0 :=
  LieSubalgebra.mem_bot x

instance : SemilatticeInf (RestrictedLieSubalgebra R L p) where
  inf S T :=
    { toLieSubalgebra := S.toLieSubalgebra ⊓ T.toLieSubalgebra
      pMap_mem' := fun ⟨hxS, hxT⟩ ↦ ⟨S.pMap_mem hxS, T.pMap_mem hxT⟩ }
  inf_le_left _ _ _ := And.left
  inf_le_right _ _ _ := And.right
  le_inf _ _ _ h₁₂ h₁₃ _ hx := ⟨h₁₂ hx, h₁₃ hx⟩

@[simp]
theorem toLieSubalgebra_inf (S T : RestrictedLieSubalgebra R L p) :
    (S ⊓ T).toLieSubalgebra = S.toLieSubalgebra ⊓ T.toLieSubalgebra :=
  (rfl)

@[simp]
theorem mem_inf {S T : RestrictedLieSubalgebra R L p} {x : L} :
    x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

end RestrictedLieSubalgebra

/-- The image of a restricted Lie algebra morphism, as a restricted Lie subalgebra. -/
def RestrictedLieHom.range {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    RestrictedLieSubalgebra R L' p where
  toLieSubalgebra := f.toLieHom.range
  pMap_mem' := by
    rintro y ⟨x, rfl⟩
    exact ⟨RestrictedLieAlgebra.pMap R p x, f.map_pMap x⟩

@[simp]
theorem RestrictedLieHom.toLieSubalgebra_range {R L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    f.range.toLieSubalgebra = f.toLieHom.range :=
  (rfl)

@[simp]
theorem RestrictedLieHom.mem_range {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) {y : L'} :
    y ∈ f.range ↔ ∃ x : L, f x = y :=
  Iff.rfl

/-- Any image `f x` lies in `f.range`. -/
theorem RestrictedLieHom.mem_range_self {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) (x : L) :
    f x ∈ f.range :=
  ⟨x, rfl⟩

/-- Restrict a restricted Lie algebra morphism to a surjective morphism onto its range. -/
def RestrictedLieHom.rangeRestrict {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    RestrictedLieHom R L f.range p where
  toLieHom := f.toLieHom.rangeRestrict
  map_pMap' x := Subtype.ext (f.map_pMap x)

/-- The underlying Lie algebra morphism of `f.rangeRestrict` composes with the range inclusion
to give `f.toLieHom`. -/
theorem RestrictedLieHom.incl_toLieHom_comp_rangeRestrict {R L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {p : ℕ}
    [RestrictedLieAlgebra R L p] [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    f.range.incl.toLieHom.comp f.rangeRestrict.toLieHom = f.toLieHom := by
  rw [← toLieHom_comp]
  ext x
  rfl

@[simp]
theorem RestrictedLieHom.rangeRestrict_apply {R L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) (x : L) :
    f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩ :=
  (rfl)

@[simp]
theorem RestrictedLieHom.incl_comp_rangeRestrict {R L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    f.range.incl.comp f.rangeRestrict = f := by
  ext x
  rfl

/-- The range restriction of a restricted Lie algebra morphism is surjective. -/
theorem RestrictedLieHom.surjective_rangeRestrict {R L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    Function.Surjective f.rangeRestrict := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := f.toLieHom.surjective_rangeRestrict ⟨y, hy⟩
  exact ⟨x, Subtype.ext (congrArg Subtype.val hx)⟩

end Subalgebra

section Ideal

/-- A restricted Lie ideal of a restricted Lie algebra `L`: a Lie ideal closed under the `p`-map
`RestrictedLieAlgebra.pMap`. -/
structure RestrictedLieIdeal (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : ℕ) [RestrictedLieAlgebra R L p] where
  /-- The underlying Lie ideal. -/
  toLieIdeal : LieIdeal R L
  /-- Closure under `pMap`. -/
  pMap_mem' {x : L} : x ∈ toLieIdeal → RestrictedLieAlgebra.pMap R p x ∈ toLieIdeal

namespace RestrictedLieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
  [RestrictedLieAlgebra R L p]

instance : SetLike (RestrictedLieIdeal R L p) L where
  coe I := (I.toLieIdeal : Set L)
  coe_injective I J h := by cases I; cases J; congr; exact SetLike.coe_injective h

instance : AddSubgroupClass (RestrictedLieIdeal R L p) L where
  add_mem {I} := I.toLieIdeal.add_mem
  zero_mem I := I.toLieIdeal.zero_mem
  neg_mem {I} := I.toLieIdeal.neg_mem

instance : SMulMemClass (RestrictedLieIdeal R L p) R L where
  smul_mem {I} c _ hx := I.toLieIdeal.smul_mem c hx

theorem toLieIdeal_injective :
    Function.Injective (toLieIdeal : RestrictedLieIdeal R L p → LieIdeal R L) := by
  intro I J h; cases I; cases J; cases h; rfl

@[ext]
theorem ext {I J : RestrictedLieIdeal R L p} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

@[simp]
theorem mem_toLieIdeal {I : RestrictedLieIdeal R L p} {x : L} :
    x ∈ I.toLieIdeal ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem coe_toLieIdeal (I : RestrictedLieIdeal R L p) : (I.toLieIdeal : Set L) = I :=
  (rfl)

/-- A restricted Lie ideal is closed under `RestrictedLieAlgebra.pMap`. -/
theorem pMap_mem (I : RestrictedLieIdeal R L p) {x : L} (hx : x ∈ I) :
    RestrictedLieAlgebra.pMap R p x ∈ I :=
  I.pMap_mem' hx

theorem zero_mem (I : RestrictedLieIdeal R L p) : (0 : L) ∈ I :=
  I.toLieIdeal.zero_mem

theorem add_mem (I : RestrictedLieIdeal R L p) {x y : L} (hx : x ∈ I) (hy : y ∈ I) :
    x + y ∈ I :=
  I.toLieIdeal.add_mem hx hy

theorem neg_mem (I : RestrictedLieIdeal R L p) {x : L} (hx : x ∈ I) : -x ∈ I :=
  I.toLieIdeal.neg_mem hx

theorem sub_mem (I : RestrictedLieIdeal R L p) {x y : L} (hx : x ∈ I) (hy : y ∈ I) :
    x - y ∈ I :=
  I.toLieIdeal.sub_mem hx hy

theorem smul_mem (I : RestrictedLieIdeal R L p) (c : R) {x : L} (hx : x ∈ I) : c • x ∈ I :=
  I.toLieIdeal.smul_mem c hx

theorem lie_mem_right (I : RestrictedLieIdeal R L p) (x : L) {y : L} (hy : y ∈ I) :
    ⁅x, y⁆ ∈ I :=
  _root_.lie_mem_right R L I.toLieIdeal x y hy

theorem lie_mem_left (I : RestrictedLieIdeal R L p) {x : L} (y : L) (hx : x ∈ I) :
    ⁅x, y⁆ ∈ I :=
  _root_.lie_mem_left R L I.toLieIdeal x y hx

/-- View a restricted Lie ideal as a restricted Lie subalgebra. -/
def toRestrictedLieSubalgebra (I : RestrictedLieIdeal R L p) :
    RestrictedLieSubalgebra R L p where
  toLieSubalgebra := I.toLieIdeal.toLieSubalgebra
  pMap_mem' := I.pMap_mem'

@[simp]
theorem mem_toRestrictedLieSubalgebra (I : RestrictedLieIdeal R L p) {x : L} :
    x ∈ I.toRestrictedLieSubalgebra ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem toLieSubalgebra_toRestrictedLieSubalgebra (I : RestrictedLieIdeal R L p) :
    I.toRestrictedLieSubalgebra.toLieSubalgebra = I.toLieIdeal.toLieSubalgebra :=
  (rfl)

instance instLieRing (I : RestrictedLieIdeal R L p) : LieRing I :=
  I.toLieIdeal.lieRing

instance instLieAlgebra (I : RestrictedLieIdeal R L p) : LieAlgebra R I :=
  I.toLieIdeal.lieAlgebra

@[simp]
theorem coe_zero (I : RestrictedLieIdeal R L p) : ((0 : I) : L) = 0 :=
  (rfl)

@[simp]
theorem coe_add (I : RestrictedLieIdeal R L p) (x y : I) : ((x + y : I) : L) = x + y :=
  (rfl)

@[simp]
theorem coe_neg (I : RestrictedLieIdeal R L p) (x : I) : ((-x : I) : L) = -x :=
  (rfl)

@[simp]
theorem coe_sub (I : RestrictedLieIdeal R L p) (x y : I) : ((x - y : I) : L) = x - y :=
  (rfl)

@[simp]
theorem coe_smul (I : RestrictedLieIdeal R L p) (c : R) (x : I) : ((c • x : I) : L) = c • x :=
  (rfl)

@[simp]
theorem coe_lie (I : RestrictedLieIdeal R L p) (x y : I) :
    ((⁅x, y⁆ : I) : L) = ⁅(x : L), (y : L)⁆ :=
  (rfl)

/-- A restricted Lie ideal inherits a restricted Lie algebra structure from the ambient
restricted Lie algebra. -/
instance instRestrictedLieAlgebra (I : RestrictedLieIdeal R L p) :
    RestrictedLieAlgebra R I p :=
  I.toLieIdeal.toLieSubalgebra.restrictedLieAlgebra fun _ hx ↦ I.pMap_mem hx

/-- The `p`-map on a restricted Lie ideal coerces to the ambient `p`-map. -/
@[simp]
theorem coe_pMap (I : RestrictedLieIdeal R L p) (x : I) :
    ((RestrictedLieAlgebra.pMap R p x : I) : L) = RestrictedLieAlgebra.pMap R p (x : L) :=
  (rfl)

/-- The canonical inclusion `I → L` of a restricted Lie ideal as a restricted morphism. -/
def incl (I : RestrictedLieIdeal R L p) : RestrictedLieHom R I L p where
  toLieHom := I.toLieIdeal.incl
  map_pMap' _ := rfl

@[simp]
theorem incl_apply (I : RestrictedLieIdeal R L p) (x : I) : I.incl x = x :=
  (rfl)

@[simp]
theorem toLieHom_incl (I : RestrictedLieIdeal R L p) : I.incl.toLieHom = I.toLieIdeal.incl :=
  (rfl)

theorem incl_injective (I : RestrictedLieIdeal R L p) : Function.Injective I.incl :=
  Subtype.val_injective

instance : PartialOrder (RestrictedLieIdeal R L p) :=
  .ofSetLike (RestrictedLieIdeal R L p)

theorem le_def {I J : RestrictedLieIdeal R L p} : I ≤ J ↔ (I : Set L) ⊆ J :=
  Iff.rfl

@[simp]
theorem toLieIdeal_le_toLieIdeal {I J : RestrictedLieIdeal R L p} :
    I.toLieIdeal ≤ J.toLieIdeal ↔ I ≤ J :=
  Iff.rfl

@[simp]
theorem toLieIdeal_inj {I J : RestrictedLieIdeal R L p} :
    I.toLieIdeal = J.toLieIdeal ↔ I = J :=
  toLieIdeal_injective.eq_iff

instance : OrderTop (RestrictedLieIdeal R L p) where
  top :=
    { toLieIdeal := ⊤
      pMap_mem' := fun _ ↦ trivial }
  le_top _ _ _ := trivial

@[simp]
theorem toLieIdeal_top : ((⊤ : RestrictedLieIdeal R L p).toLieIdeal) = ⊤ :=
  (rfl)

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : RestrictedLieIdeal R L p) :=
  trivial

instance : OrderBot (RestrictedLieIdeal R L p) where
  bot :=
    { toLieIdeal := ⊥
      pMap_mem' := fun hx ↦ by
        rw [LieSubmodule.mem_bot] at hx ⊢
        rw [hx, RestrictedLieAlgebra.pMap_zero] }
  bot_le I x hx := by
    have hx0 : x = 0 := (LieSubmodule.mem_bot x).mp hx
    rw [hx0]
    exact I.zero_mem

@[simp]
theorem toLieIdeal_bot : ((⊥ : RestrictedLieIdeal R L p).toLieIdeal) = ⊥ :=
  (rfl)

@[simp]
theorem mem_bot {x : L} : x ∈ (⊥ : RestrictedLieIdeal R L p) ↔ x = 0 :=
  LieSubmodule.mem_bot x

instance : SemilatticeInf (RestrictedLieIdeal R L p) where
  inf I J :=
    { toLieIdeal := I.toLieIdeal ⊓ J.toLieIdeal
      pMap_mem' := fun ⟨hxI, hxJ⟩ ↦ ⟨I.pMap_mem hxI, J.pMap_mem hxJ⟩ }
  inf_le_left _ _ _ := And.left
  inf_le_right _ _ _ := And.right
  le_inf _ _ _ h₁₂ h₁₃ _ hx := ⟨h₁₂ hx, h₁₃ hx⟩

@[simp]
theorem toLieIdeal_inf (I J : RestrictedLieIdeal R L p) :
    (I ⊓ J).toLieIdeal = I.toLieIdeal ⊓ J.toLieIdeal :=
  (rfl)

@[simp]
theorem mem_inf {I J : RestrictedLieIdeal R L p} {x : L} :
    x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

end RestrictedLieIdeal

/-- The kernel of a restricted Lie algebra morphism, as a restricted Lie ideal. -/
def RestrictedLieHom.ker {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    RestrictedLieIdeal R L p where
  toLieIdeal := f.toLieHom.ker
  pMap_mem' hx := f.pMap_mem_ker hx

@[simp]
theorem RestrictedLieHom.toLieIdeal_ker {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    f.ker.toLieIdeal = f.toLieHom.ker :=
  (rfl)

@[simp]
theorem RestrictedLieHom.mem_ker {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) {x : L} :
    x ∈ f.ker ↔ f x = 0 :=
  LieHom.mem_ker (f := f.toLieHom)

/-- A restricted Lie algebra morphism has trivial kernel if and only if it is injective. -/
theorem RestrictedLieHom.ker_eq_bot {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] {p : ℕ} [RestrictedLieAlgebra R L p]
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R L L' p) :
    f.ker = ⊥ ↔ Function.Injective f := by
  rw [← RestrictedLieIdeal.toLieIdeal_inj, toLieIdeal_ker, RestrictedLieIdeal.toLieIdeal_bot,
    LieHom.ker_eq_bot, coe_toLieHom]

end Ideal

end TauCeti

section Examples

attribute [local instance 100] LieRing.ofAssociativeRing

-- Witness: on a commutative associative algebra `A` of exponential characteristic `p`,
-- `pMap a = a ^ p` is additive (`Λ_p = 0`).
example (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (p : ℕ) [ExpChar A p] (a b : A) :
    letI := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R A p
    TauCeti.RestrictedLieAlgebra.pMap R p (a + b) =
      TauCeti.RestrictedLieAlgebra.pMap R p a + TauCeti.RestrictedLieAlgebra.pMap R p b := by
  let _ := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R A p
  exact TauCeti.RestrictedLieAlgebra.pMap_add_of_lie_eq_zero
    (by rw [Ring.lie_def, mul_comm, sub_self])

-- Witness: on a nontrivial commutative ring `R` of prime characteristic `p`, `ofAbelianZero` and
-- `ofAssociativeAlgebra` are two distinct restricted Lie algebra structures on the same Lie
-- algebra (they differ at `1 : R`).
example (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    let _ : IsLieAbelian R := ⟨fun x y ↦ by rw [Ring.lie_def, mul_comm, sub_self]⟩
    TauCeti.RestrictedLieAlgebra.ofAbelianZero R R p (Fact.out : p.Prime).ne_zero ≠
      TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R R p := by
  intro _ h
  have h1 := (TauCeti.RestrictedLieAlgebra.ext_iff.mp h) (1 : R)
  simp only [TauCeti.RestrictedLieAlgebra.ofAbelianZero_pMap,
    TauCeti.RestrictedLieAlgebra.pMap_ofAssociativeAlgebra, one_pow] at h1
  exact zero_ne_one h1

end Examples
