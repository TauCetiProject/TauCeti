/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

Additivity is not the right axiom: in `2 × 2` matrices over `ZMod p`, `p` odd, the Frobenius is not
additive (`TauCeti.LieAlgebra.jacobson_single_single`), and the Lie term `Λ_p` is what corrects it.

The basic example is an associative `R`-algebra `A` of exponential characteristic `p` with
`x^[p] = x ^ p` (`TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra`), in particular
`Module.End R M`. Since the commutator Lie ring of `A` is only a local instance, this structure is
a definition rather than an instance. A Lie subalgebra of a restricted Lie algebra which is closed
under the `p`-map inherits a restricted structure (`LieSubalgebra.restrictedLieAlgebra`), and so
does the source of any injective Lie algebra morphism compatible with given `p`-maps
(`Function.Injective.restrictedLieAlgebra`). The derivations of a commutative algebra of
characteristic `p` form a restricted Lie algebra under `D ↦ D^[p]`; that instance is in
`TauCeti.RingTheory.Derivation.PPow`.

## Main definitions

* `TauCeti.RestrictedLieAlgebra R L p`: a Lie algebra with a `p`-map `RestrictedLieAlgebra.pMap`.
* `TauCeti.RestrictedLieHom R L L' p`: a Lie algebra morphism commuting with the `p`-maps.
* `TauCeti.RestrictedLieHom.id`, `TauCeti.RestrictedLieHom.comp`: identity and composition.
* `TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra`: the restricted structure `a ↦ a ^ p` on an
  associative algebra of exponential characteristic `p`.
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
* `TauCeti.RestrictedLieHom.pMap_mem_ker`: the kernel of a restricted morphism, a Lie ideal, is
  closed under the `p`-map, so it is a restricted ideal.

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

/-- The `p`-map is additive on commuting elements, where Jacobson's correction term vanishes. -/
theorem pMap_add_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap R p (x + y) = pMap R p x + pMap R p y := by
  rw [pMap_add, jacobson_eq_zero_of_lie_eq_zero p h, add_zero]

end Basic

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
  pMap_add a b := by
    obtain _ | ⟨hp⟩ := ‹ExpChar A p›
    · simp [jacobson_def]
    · have : Fact p.Prime := ⟨hp⟩
      exact add_pow_eq_jacobson p a b

variable {R A p}

/-- The `p`-map of `ofAssociativeAlgebra` is the `p`-th power. -/
@[simp]
theorem pMap_ofAssociativeAlgebra (a : A) :
    letI := ofAssociativeAlgebra R A p
    pMap R p a = a ^ p :=
  (rfl)

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

/-- The underlying function of a restricted morphism built from a Lie algebra morphism. -/
@[simp]
theorem coe_mk (f : L →ₗ⁅R⁆ L') (h) : ⇑(⟨f, h⟩ : RestrictedLieHom R L L' p) = f :=
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
