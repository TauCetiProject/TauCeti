/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor.Basic
import TauCeti.Algebra.Category.ModuleCat.Quotient

/-!
# Complete flatness of modules

Let `A` be a commutative ring and `I` an ideal of `A`. A module `M` is `I`-*completely flat* when
its derived reduction `M ⊗^L_A A/I` is a flat `A/I`-module in degree zero: the higher groups
`Tor_n^A(M, A/I)` vanish and `A/I ⊗_A M = M/IM` is flat over `A/I`. It is `I`-*completely
faithfully flat* when moreover `M/IM` is faithfully flat over `A/I`. Neither predicate asks `M` to
be `I`-adically or derived `I`-complete, and no finiteness is asked of `I`.

Every flat module is `I`-completely flat for every ideal `I`, as its higher `Tor` vanishes and flat
modules base change to flat modules; likewise every faithfully flat module is `I`-completely
faithfully flat. The converse fails: `F_p` is not `p`-completely flat over `ℤ`, since
`Tor_1^ℤ(F_p, F_p) ≠ 0` (`TauCeti.DerivedDeRham.not_isCompletelyFlatModule_quotient_self`), while
`ℤ` is `p`-completely flat without being derived `p`-complete.

## Main definitions

* `TauCeti.DerivedDeRham.IsCompletelyFlatModule A I M`: `M` is `I`-completely flat.
* `TauCeti.DerivedDeRham.IsCompletelyFaithfullyFlatModule A I M`: `M` is `I`-completely faithfully
  flat.

## Main results

* `TauCeti.DerivedDeRham.isCompletelyFlatModule_of_flat`: flat modules are `I`-completely flat.
* `TauCeti.DerivedDeRham.isCompletelyFaithfullyFlatModule_of_faithfullyFlat`: faithfully flat
  modules are `I`-completely faithfully flat.
* `TauCeti.DerivedDeRham.IsCompletelyFlatModule.of_iso`: complete flatness is invariant under
  isomorphism of modules.
* `TauCeti.DerivedDeRham.not_isCompletelyFlatModule_quotient_self`: for a nonzerodivisor `a` that
  is not a unit, `A/(a)` is not `(a)`-completely flat, as `Tor_1^A(A/(a), A/(a)) ≠ 0`.

## References

* B. Bhatt, M. Morrow and P. Scholze, *Topological Hochschild homology and integral `p`-adic
  Hodge theory*, Publ. Math. IHÉS 129 (2019), Definition 4.1.
* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022), §1.2.
-/

public section

open CategoryTheory Limits TensorProduct

universe u

namespace TauCeti.DerivedDeRham

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- **Complete flatness of a module.** A module `M` is `I`-completely flat when its derived
reduction `M ⊗^L_A A/I` is a flat `A/I`-module in degree zero: the higher `Tor_n^A(M, A/I)` vanish
and `A/I ⊗_A M` is flat over `A/I`. The predicate does not require `M` to be complete (Bhatt,
Morrow and Scholze, *Topological Hochschild homology and integral `p`-adic Hodge theory*,
Definition 4.1, for `I = (p)`; the same definition applies to any ideal). -/
def IsCompletelyFlatModule (M : ModuleCat.{u} A) : Prop :=
  (∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat.{u} A) n).obj M).obj (ModuleCat.of A (A ⧸ I)))) ∧
    Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M)

/-- **Complete faithful flatness of a module.** A module `M` is `I`-completely faithfully flat when
it is `I`-completely flat and `A/I ⊗_A M` is faithfully flat over `A/I`. -/
def IsCompletelyFaithfullyFlatModule (M : ModuleCat.{u} A) : Prop :=
  IsCompletelyFlatModule A I M ∧ Module.FaithfullyFlat (A ⧸ I) ((A ⧸ I) ⊗[A] M)

variable {A I}

/-- Unfolding lemma for `IsCompletelyFlatModule`. -/
theorem isCompletelyFlatModule_iff {M : ModuleCat.{u} A} :
    IsCompletelyFlatModule A I M ↔
      (∀ n : ℕ, 0 < n →
        IsZero (((Tor (ModuleCat.{u} A) n).obj M).obj (ModuleCat.of A (A ⧸ I)))) ∧
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) :=
  Iff.rfl

/-- Unfolding lemma for `IsCompletelyFaithfullyFlatModule`. -/
theorem isCompletelyFaithfullyFlatModule_iff {M : ModuleCat.{u} A} :
    IsCompletelyFaithfullyFlatModule A I M ↔
      IsCompletelyFlatModule A I M ∧ Module.FaithfullyFlat (A ⧸ I) ((A ⧸ I) ⊗[A] M) :=
  Iff.rfl

/-- A completely faithfully flat module is completely flat. -/
theorem IsCompletelyFaithfullyFlatModule.isCompletelyFlatModule {M : ModuleCat.{u} A}
    (h : IsCompletelyFaithfullyFlatModule A I M) : IsCompletelyFlatModule A I M :=
  h.1

/-- **Flat modules are completely flat**, for every ideal: their higher `Tor` vanishes
(`ModuleCat.isZero_Tor_succ_of_flat`), and their base change to `A/I` is flat. -/
theorem isCompletelyFlatModule_of_flat (M : ModuleCat.{u} A) [Module.Flat A M] :
    IsCompletelyFlatModule A I M := by
  refine ⟨fun n hn => ?_, inferInstance⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simpa using ModuleCat.isZero_Tor_succ_of_flat M (ModuleCat.of A (A ⧸ I)) k

/-- **Faithfully flat modules are completely faithfully flat**, for every ideal. -/
theorem isCompletelyFaithfullyFlatModule_of_faithfullyFlat (M : ModuleCat.{u} A)
    [Module.FaithfullyFlat A M] : IsCompletelyFaithfullyFlatModule A I M :=
  ⟨isCompletelyFlatModule_of_flat M, inferInstance⟩

/-- Complete flatness is invariant under isomorphism of modules. -/
theorem IsCompletelyFlatModule.of_iso {M N : ModuleCat.{u} A} (h : IsCompletelyFlatModule A I M)
    (e : M ≅ N) : IsCompletelyFlatModule A I N := by
  refine ⟨fun n hn => (h.1 n hn).of_iso (((Tor (ModuleCat.{u} A) n).mapIso e).app _).symm, ?_⟩
  have := h.2
  exact Module.Flat.of_linearEquiv
    (AlgebraTensorModule.congr (LinearEquiv.refl (A ⧸ I) (A ⧸ I)) e.toLinearEquiv).symm

/-- Complete faithful flatness is invariant under isomorphism of modules. -/
theorem IsCompletelyFaithfullyFlatModule.of_iso {M N : ModuleCat.{u} A}
    (h : IsCompletelyFaithfullyFlatModule A I M) (e : M ≅ N) :
    IsCompletelyFaithfullyFlatModule A I N := by
  refine ⟨h.1.of_iso e, ?_⟩
  have := h.2
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (AlgebraTensorModule.congr (LinearEquiv.refl (A ⧸ I) (A ⧸ I)) e.toLinearEquiv).symm

/-- **A quotient by a nonzerodivisor is not completely flat for its own ideal.** If `a` is a
nonzerodivisor and not a unit, then `A/(a)` is not `(a)`-completely flat: the short exact sequence
`0 → A → A → A/(a) → 0` of multiplication by `a` shows that `Tor_1^A(A/(a), A/(a)) = 0` would make
multiplication by `a` injective on `A ⊗_A A/(a) = A/(a)`, where it is zero. For instance `F_p` is
not `p`-completely flat over `ℤ`. -/
theorem not_isCompletelyFlatModule_quotient_self {a : A} (ha : IsRegular a) (hu : ¬ IsUnit a) :
    ¬ IsCompletelyFlatModule A (Ideal.span {a}) (ModuleCat.of A (A ⧸ Ideal.span {a})) := by
  intro h
  let J := Ideal.span {a}
  let S := mulQuotientSpanSingletonShortComplex a
  have hS : S.ShortExact := ha.left.mulQuotientSpanSingletonShortComplex_shortExact
  have hinj := hS.rTensor_injective_of_isZero_Tor_one (ModuleCat.of A (A ⧸ J)) (h.1 1 one_pos)
  have ha0 : ∀ z : A ⧸ J, a • z = 0 := fun z => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [J, Algebra.smul_def]
  have hzero : S.f.hom.rTensor (A ⧸ J) = 0 := by
    refine TensorProduct.ext' fun x z => ?_
    simp only [S, ModuleCat.hom_ofHom, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply,
      LinearMap.zero_apply, ← smul_eq_mul, TensorProduct.smul_tmul, ha0, TensorProduct.tmul_zero]
  have : Subsingleton (A ⊗[A] (A ⧸ J)) :=
    ⟨fun x y => hinj (by simp only [hzero, LinearMap.zero_apply])⟩
  have : Subsingleton (A ⧸ J) := (TensorProduct.lid A (A ⧸ J)).symm.injective.subsingleton
  exact hu (Ideal.span_singleton_eq_top.1 (Ideal.Quotient.subsingleton_iff.1 this))

end TauCeti.DerivedDeRham
