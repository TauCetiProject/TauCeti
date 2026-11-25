/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Algebra.Equiv

/-!
# Basic facts about module endomorphisms

A nontrivial endomorphism semiring forces the underlying module to be nontrivial. Together with
Mathlib's converse instance, this identifies nontriviality on the two sides without assumptions on
the endomorphism semiring beyond nontriviality itself.

A vector on which every endomorphism of a list acts by the same scalar `z` is acted on by their
product through `z ^ l.length` (`Module.End.list_prod_apply_eq_pow_smul`).

An endomorphism of a torsion-free module over a domain some power of which is a scalar other than
one has no nonzero fixed vectors (`TauCeti.injective_one_sub_of_pow_eq_smul_one`).

Rescaling an involution by a scalar `μ` with `μ * μ = 1` gives an endomorphism squaring to `1`
(`Module.End.smul_mul_smul_self_eq_one`).

A finite nontrivial module has more than one endomorphism (`Module.End.one_lt_natCard`).

Of two endomorphisms conjugate by a linear equivalence, one squares to `κ • 1` exactly when the
other does (`Module.End.mul_self_eq_smul_one_iff_of_forall_apply_eq`).

Scalar restriction of endomorphisms is packaged as a ring homomorphism, with identity, product,
power and nilpotence compatibility (`Module.End.restrictScalarsRingHom`).

An endomorphism acting as a scalar `a` from a monoid acting on the module has `k`-th power acting
as `a ^ k` (`Module.End.pow_apply_eq_pow_smul`), so it is `1` once `a ^ k = 1`
(`Module.End.pow_eq_one_of_apply_eq_smul`).

Iterates of endomorphisms intertwined by a semilinear map are intertwined
(`Module.End.pow_apply_of_comp_eq`).

A submodule fixed pointwise by an endomorphism `f` is invariant under `f`
(`Submodule.le_comap_of_fixed`). If `f` maps `p` into `p ⊔ q` and leaves `q` invariant, then so
does each power of `f` (`Submodule.le_comap_pow_of_le_comap_sup`). A submodule invariant under
two endomorphisms is invariant under their difference
(`Module.End.invtSubmodule_inf_invtSubmodule_le_invtSubmodule_sub`).

An endomorphism squaring to `-1` is bijective, with inverse `-f`
(`Module.End.bijective_of_comp_self_eq_neg_one`).
-/

public section

namespace TauCeti

/-- A module with nontrivial endomorphism semiring is nontrivial. -/
theorem nontrivial_of_nontrivial_end {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial (Module.End R M)] : Nontrivial M := by
  have : Nontrivial (M → M) := (DFunLike.coe_injective (F := Module.End R M)).nontrivial
  exact Function.nontrivial_of_nontrivial M M

/-- **`1 - φ` is injective when a power of `φ` is a scalar other than one**, for an endomorphism
of a torsion-free module over a domain. If `φ v = v` then `m • v = φ ^ n v = v`, so
`(1 - m) • v = 0` and `v = 0`. For the character map `φ` of a Steinberg endomorphism some power of
`φ` is `q • 1` with `q` a power of the characteristic. The hypothesis `m ≠ 1` cannot be dropped:
`φ = 1` satisfies `φ ^ 1 = 1 • 1`. -/
theorem injective_one_sub_of_pow_eq_smul_one {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M] {φ : Module.End A M} {n : ℕ} {m : A}
    (h : φ ^ n = m • 1) (hm : m ≠ 1) : Function.Injective ⇑(1 - φ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  -- `1 - φ ^ n = (∑ i < n, φ ^ i) * (1 - φ)` kills `v`, and it is multiplication by `1 - m`.
  have hn : (1 - φ ^ n) v = 0 := by
    rw [← geom_sum_mul_neg, _root_.mul_apply_eq_comp, hv, map_zero]
  have hmv : (1 - m) • v = 0 := by
    rw [sub_smul, one_smul]
    simpa [h] using hn
  exact (smul_eq_zero.mp hmv).resolve_left (sub_ne_zero.mpr hm.symm)

end TauCeti

namespace Module.End

section RestrictScalars

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
  [Module R M] [Module S M] [LinearMap.CompatibleSMul M M R S]

/-- Scalar restriction of endomorphisms as a ring homomorphism. -/
def restrictScalarsRingHom (R S M : Type*) [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module S M] [LinearMap.CompatibleSMul M M R S] :
    Module.End S M →+* Module.End R M where
  toFun := LinearMap.restrictScalars R
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Restricting the scalars of the identity endomorphism gives the identity. -/
@[simp]
theorem restrictScalars_one : (1 : Module.End S M).restrictScalars R = 1 :=
  (restrictScalarsRingHom R S M).map_one

/-- Restricting the scalars of endomorphisms preserves their products. -/
@[simp]
theorem restrictScalars_mul (D E : Module.End S M) :
    (D * E).restrictScalars R = D.restrictScalars R * E.restrictScalars R :=
  (restrictScalarsRingHom R S M).map_mul D E

/-- Restricting the scalars of an endomorphism preserves its powers. -/
@[simp]
theorem restrictScalars_pow (D : Module.End S M) (n : ℕ) :
    (D ^ n).restrictScalars R = (D.restrictScalars R) ^ n :=
  (restrictScalarsRingHom R S M).map_pow D n

/-- Restricting the scalars of an endomorphism preserves and reflects nilpotence. -/
@[simp]
theorem isNilpotent_restrictScalars_iff {D : Module.End S M} :
    IsNilpotent (D.restrictScalars R) ↔ IsNilpotent D :=
  IsNilpotent.map_iff (f := restrictScalarsRingHom R S M) (LinearMap.restrictScalars_injective R)

/-- The scalar-restriction ring homomorphism is the underlying scalar-restriction map. It has
`low` priority so that the generic morphism lemmas such as `map_mul` fire first; see Mathlib's
library note on hom simp lemma priority. -/
@[simp low]
theorem restrictScalarsRingHom_apply (R S M : Type*) [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module S M] [LinearMap.CompatibleSMul M M R S] (D : Module.End S M) :
    restrictScalarsRingHom R S M D = D.restrictScalars R := (rfl)

end RestrictScalars

/-- A product of endomorphisms each of which acts on `s` by the scalar `z` acts on `s` by
`z ^ l.length`. -/
theorem list_prod_apply_eq_pow_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {l : List (Module.End R M)} {z : R} {s : M} (h : ∀ a ∈ l, a s = z • s) :
    l.prod s = z ^ l.length • s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, _root_.mul_apply_eq_comp, ih fun a ha ↦ h a (List.mem_cons_of_mem _ ha),
      map_smul, h a List.mem_cons_self, smul_smul, List.length_cons, pow_succ]

/-- `μ • g` squares to `1` for an involution `g` and `μ * μ = 1`. -/
theorem smul_mul_smul_self_eq_one {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {g : Module.End R M} (hg : Function.Involutive g) {μ : R} (hμ : μ * μ = 1) :
    (μ • g) * (μ • g) = 1 := by
  rw [smul_mul_smul_comm, hμ, one_smul]
  exact LinearMap.ext hg

/-- An endomorphism squaring to `-1` is bijective, with inverse `-f`. -/
theorem bijective_of_comp_self_eq_neg_one {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} (hf : f ∘ₗ f = -1) : Function.Bijective f :=
  ⟨fun _ _ hxy ↦ by simpa [← LinearMap.comp_apply, hf] using congrArg (-f) hxy,
   fun y ↦ ⟨-f y, by simp [← LinearMap.comp_apply, hf]⟩⟩

/-- A finite nontrivial module has more than one endomorphism: `0` and `1` differ. -/
theorem one_lt_natCard {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial M]
    [Finite M] : 1 < Nat.card (Module.End R M) := by
  have : Finite (Module.End R M) := Finite.of_injective _ DFunLike.coe_injective
  exact Finite.one_lt_card

/-- If `e` conjugates `A` to `B`, then `A` squares to `κ • 1` exactly when `B` does. -/
theorem mul_self_eq_smul_one_iff_of_forall_apply_eq {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {A : Module.End R M}
    {B : Module.End R N} {e : M ≃ₗ[R] N} (hAB : ∀ v, e (A v) = B (e v)) (κ : R) :
    A * A = κ • 1 ↔ B * B = κ • 1 := by
  have hB : B = e.conjAlgEquiv R A := LinearMap.ext fun w ↦ by
    simp [LinearEquiv.conjAlgEquiv_apply, hAB]
  rw [hB, ← map_mul, ← map_one (e.conjAlgEquiv R), ← map_smul, EmbeddingLike.apply_eq_iff_eq]

/-- The `k`-th power of an endomorphism acting as the scalar `a` acts as `a ^ k`. -/
theorem pow_apply_eq_pow_smul {R M X : Type*} [Semiring R] [AddCommMonoid X] [Module R X]
    [Monoid M] [MulAction M X] {a : M} (S : Module.End R X) (hS : ∀ x, S x = a • x) (k : ℕ)
    (x : X) : (S ^ k) x = a ^ k • x := by
  rw [pow_apply_eq_iterate, show ⇑S = fun x ↦ a • x from funext hS, smul_iterate_apply]

/-- An endomorphism acting as the scalar `a` satisfies `S ^ k = 1` whenever `a ^ k = 1`. -/
theorem pow_eq_one_of_apply_eq_smul {R M X : Type*} [Semiring R] [AddCommMonoid X] [Module R X]
    [Monoid M] [MulAction M X] {a : M} (S : Module.End R X) (hS : ∀ x, S x = a • x) {k : ℕ}
    (hk : a ^ k = 1) : S ^ k = 1 :=
  LinearMap.ext fun x ↦ by rw [pow_apply_eq_pow_smul S hS, hk, one_smul, one_apply_eq_self]

/-- Iterates of intertwined endomorphisms are intertwined: if `f ∘ g = g₂ ∘ f`, then
`(g₂ ^ k) (f m) = f ((g ^ k) m)`. This is the pointwise form of `commute_pow_left_of_commute`. -/
theorem pow_apply_of_comp_eq {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M]
    [Module R M] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R →+* R₂} {f : M →ₛₗ[σ₁₂] M₂}
    {g : Module.End R M} {g₂ : Module.End R₂ M₂} (h : f.comp g = g₂.comp f) (k : ℕ) (m : M) :
    (g₂ ^ k) (f m) = f ((g ^ k) m) :=
  LinearMap.congr_fun (commute_pow_left_of_commute h.symm k) m

end Module.End

namespace Submodule

/-- A submodule fixed pointwise by an endomorphism is invariant under it. -/
theorem le_comap_of_fixed {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (p : Submodule R V) (f : Module.End R V)
    (hfix : ∀ y ∈ p, f y = y) : p ≤ p.comap f :=
  fun y hy ↦ by rw [Submodule.mem_comap, hfix y hy]; exact hy

/-- If an endomorphism maps `p` into `p ⊔ q` and leaves `q` invariant, so does each of its powers.
This is the relative form of `Submodule.le_comap_pow_of_le_comap`. -/
theorem le_comap_pow_of_le_comap_sup {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (p : Submodule R V) {q : Submodule R V} {f : Module.End R V} (hp : p ≤ (p ⊔ q).comap f)
    (hq : q ≤ q.comap f) (k : ℕ) : p ≤ (p ⊔ q).comap (f ^ k) :=
  le_sup_left.trans <|
    (p ⊔ q).le_comap_pow_of_le_comap (sup_le hp (hq.trans (comap_mono le_sup_right))) k

end Submodule

namespace Module.End

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (f g : End R V)

/-- A submodule invariant under two endomorphisms is invariant under their difference. This is the
analogue of `Module.End.invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add`. -/
theorem invtSubmodule_inf_invtSubmodule_le_invtSubmodule_sub :
    f.invtSubmodule ⊓ g.invtSubmodule ≤ (f - g).invtSubmodule :=
  fun p ⟨hfp, hgp⟩ _ hx ↦ p.sub_mem (hfp hx) (hgp hx)

end Module.End
