/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RingTheory.LocalRing.Basic

/-!
# Indecomposable modules and Fitting's lemma

A module is *indecomposable* when it is nonzero and is not the internal direct sum of two nonzero
submodules. This file introduces the predicate, records its idempotent reformulation, and proves
**Fitting's lemma**: an endomorphism of an indecomposable module of finite length is either
nilpotent or bijective, so the endomorphism ring of such a module is local.

Mathlib has the Fitting *decomposition* of an endomorphism of a Noetherian and Artinian module
(`LinearMap.eventually_isCompl_ker_pow_range_pow`) and `CategoryTheory.Indecomposable` for objects
of a category with binary biproducts, but no module-level indecomposability predicate and no
local-endomorphism-ring theorem. Both are supplied here.

## Main definitions

* `TauCeti.IsIndecomposableModule A M`: `M` is a nonzero `A`-module admitting no decomposition
  `M = N ⊕ P` with `N` and `P` both nonzero.

## Main results

* `TauCeti.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem`: indecomposability
  says exactly that `M` is nontrivial and `0` and `1` are the only idempotents of `Module.End A M`.
* `TauCeti.isIndecomposableModule_iff_isIndecomposableModule_of_algebraMap_surjective`:
  indecomposability is unchanged by restricting scalars along a surjective algebra map.
* `TauCeti.IsIndecomposableModule.bijective_of_bijective_comp`: a split injection into an
  indecomposable module is an isomorphism, that is, if `g ∘ₗ f` is bijective and the module `f`
  lands in is indecomposable, then `f` is bijective.
* `TauCeti.IsIndecomposableModule.isNilpotent_or_bijective`: **Fitting's lemma**, for a module that
  is Noetherian and Artinian, together with
  `TauCeti.IsIndecomposableModule.isNilpotent_iff_not_isUnit`, which reads it as an identification
  of the non-units of the endomorphism ring with its nilpotents.
* `TauCeti.isLocalRing_end_of_isIndecomposable`: the endomorphism ring of an indecomposable module
  of finite length is local, and `TauCeti.nontrivial_of_isLocalRing_end` for the converse direction
  that a local endomorphism ring forces the module to be nonzero.
* `TauCeti.isIndecomposableModule_iff_isLocalRing_end`: for a module of finite length the converse
  holds too, so indecomposability is *equivalent* to having a local endomorphism ring.
* `TauCeti.isIndecomposableModule_self`: a local ring is indecomposable over itself, and
  `TauCeti.isLocalRing_of_isIndecomposableModule_self` the converse for a ring of finite length
  over itself; `TauCeti.isIndecomposableModule_self_iff` reads indecomposability of a ring over
  itself off its idempotents.
* `TauCeti.IsIndecomposableModule.nonempty_linearEquiv_of_free`: an indecomposable free module is
  isomorphic to the scalar semiring.

## Implementation notes

`IsIndecomposableModule`, its two projections, and its transport along a semilinear equivalence are
stated for a semimodule over a semiring, since the submodule lattice and the order isomorphism it
inherits from a semilinear equivalence need no subtraction; so is `nontrivial_of_isLocalRing_end`,
which only reads `0 ≠ 1` off the endomorphism semiring. The free-module theorem also works over
a semiring. The idempotent, splitting, and Fitting results are stated over a ring, where Mathlib
puts the tools they use:
`LinearMap.IsIdempotentElem.isCompl` and `Submodule.projection` build a projection by subtracting,
and `IsSimpleModule` is itself only defined for modules over a ring.

The finiteness hypothesis is carried as the pair of instances `[IsNoetherian A M] [IsArtinian A M]`
on the lemmas that consume it, which is what Mathlib's Fitting decomposition asks for. The
`IsFiniteLength A M` spelling appears on the headline statements
`isLocalRing_end_of_isIndecomposable` and `isIndecomposableModule_iff_isLocalRing_end`, which
unpack it through `isFiniteLength_iff_isNoetherian_isArtinian`.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v w

section Semiring

variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]

/-- A module is **indecomposable** when it is nonzero and is not the internal direct sum of two
nonzero submodules. -/
def IsIndecomposableModule : Prop :=
  Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥

variable {A M}

/-- `IsIndecomposableModule` restated as the conjunction defining it, so that clients can
establish and consume it without unfolding the definition. -/
theorem isIndecomposableModule_iff_nontrivial_and_forall_isCompl :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥ :=
  Iff.rfl

/-- A nontrivial module along none of whose decompositions `M = N ⊕ P` both summands are nonzero is
indecomposable. -/
theorem isIndecomposableModule_of_forall_isCompl [Nontrivial M]
    (h : ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥) : IsIndecomposableModule A M :=
  ⟨‹_›, h⟩

theorem IsIndecomposableModule.nontrivial (h : IsIndecomposableModule A M) : Nontrivial M := h.1

theorem IsIndecomposableModule.eq_bot_or_eq_bot (h : IsIndecomposableModule A M)
    {N P : Submodule A M} (hNP : IsCompl N P) : N = ⊥ ∨ P = ⊥ :=
  h.2 N P hNP

/-- Indecomposability transfers along a semilinear equivalence over mutually inverse scalar
homomorphisms. -/
theorem IsIndecomposableModule.of_linearEquiv {B : Type*} [Semiring B]
    {σ : A →+* B} {τ : B →+* A} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    {N : Type w} [AddCommMonoid N] [Module B N]
    (h : IsIndecomposableModule A M) (e : M ≃ₛₗ[σ] N) : IsIndecomposableModule B N := by
  have := h.nontrivial
  refine ⟨e.symm.toEquiv.nontrivial, fun P Q hPQ ↦ ?_⟩
  simpa using h.eq_bot_or_eq_bot ((Submodule.orderIsoMapComap e.symm).isCompl hPQ)

/-- A module with local endomorphism ring is nonzero: over the zero module the endomorphism ring is
the zero ring, which is not local. -/
theorem nontrivial_of_isLocalRing_end [IsLocalRing (Module.End A M)] : Nontrivial M := by
  rcases subsingleton_or_nontrivial M with _ | h
  · exact absurd (LinearMap.ext fun _ ↦ Subsingleton.elim _ _ : (0 : Module.End A M) = 1)
      zero_ne_one
  · exact h

end Semiring

section Ring

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

/-! ### Restriction of scalars along a surjection -/

/-- **Indecomposability is insensitive to restriction of scalars along a surjection**: when
`algebraMap R A` is surjective, the `R`-submodules and the `A`-submodules of `M` are the same, so
`M` is indecomposable over `R` exactly when it is over `A`. -/
theorem isIndecomposableModule_iff_isIndecomposableModule_of_algebraMap_surjective
    {R : Type*} [CommRing R] [Algebra R A] [Module R M] [IsScalarTower R A M]
    (h : Function.Surjective (algebraMap R A)) :
    IsIndecomposableModule R M ↔ IsIndecomposableModule A M := by
  let e := Submodule.orderIsoOfAlgebraMapSurjective (M := M) h
  refine and_congr_right fun _ ↦ ⟨fun hR N P hNP ↦ ?_, fun hA N P hNP ↦ ?_⟩
  · simpa using hR (e N) (e P) (e.isCompl hNP)
  · simpa using hA (e.symm N) (e.symm P) (e.symm.isCompl hNP)

/-! ### Indecomposability through idempotent endomorphisms -/

/-- The idempotent endomorphisms of an indecomposable module are `0` and `1`: an idempotent splits
the module as the direct sum of its range and its kernel, and one of the two must vanish. -/
theorem IsIndecomposableModule.eq_zero_or_eq_one_of_isIdempotentElem
    (h : IsIndecomposableModule A M) {f : Module.End A M} (hf : IsIdempotentElem f) :
    f = 0 ∨ f = 1 := by
  rcases h.eq_bot_or_eq_bot (LinearMap.IsIdempotentElem.isCompl hf) with hrange | hker
  · exact Or.inl (LinearMap.range_eq_bot.mp hrange)
  · refine Or.inr (LinearMap.ext fun x ↦ ?_)
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have hx : f (f x) = f x := DFunLike.congr_fun hf x
    simpa using hinj hx

/-- A nonzero module whose only idempotent endomorphisms are `0` and `1` is indecomposable: a
decomposition `M = N ⊕ P` is witnessed by the projection onto `N` along `P`. -/
theorem isIndecomposableModule_of_forall_isIdempotentElem [Nontrivial M]
    (h : ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1) :
    IsIndecomposableModule A M := by
  refine isIndecomposableModule_of_forall_isCompl fun N P hNP ↦ ?_
  rcases h (N.projection P hNP) (Submodule.isIdempotentElem_projection hNP) with h₀ | h₁
  · exact Or.inl (by simpa [h₀] using (Submodule.range_projection hNP).symm)
  · exact Or.inr (by simpa [h₁, Module.End.one_eq_id] using (Submodule.ker_projection hNP).symm)

/-- Indecomposability of a module is exactly the statement that it is nontrivial and its
endomorphism ring has no idempotents besides `0` and `1`. -/
theorem isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1 :=
  ⟨fun h ↦ ⟨h.nontrivial, fun _ hf ↦ h.eq_zero_or_eq_one_of_isIdempotentElem hf⟩,
    fun ⟨_, h⟩ ↦ isIndecomposableModule_of_forall_isIdempotentElem h⟩

/-- A simple module is indecomposable: it has no proper nonzero submodule to decompose along. -/
theorem IsSimpleModule.isIndecomposableModule [IsSimpleModule A M] :
    IsIndecomposableModule A M := by
  refine ⟨IsSimpleModule.nontrivial A M, fun N P hNP ↦ ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · exact Or.inl hN
  · refine Or.inr ?_
    have hdisj : Disjoint (⊤ : Submodule A M) P := hN ▸ hNP.disjoint
    simpa using hdisj

/-- An indecomposable semisimple module is simple. -/
theorem IsIndecomposableModule.isSimpleModule [IsSemisimpleModule A M]
    (h : IsIndecomposableModule A M) : IsSimpleModule A M := by
  have := h.nontrivial
  refine (isSimpleModule_iff A M).mpr ⟨fun N ↦ ?_⟩
  obtain ⟨P, hNP⟩ := exists_isCompl N
  rcases h.eq_bot_or_eq_bot hNP with hN | hP
  · exact Or.inl hN
  · exact Or.inr (by simpa [hP] using hNP.sup_eq_top)

/-! ### Splitting off an indecomposable module -/

/-- **A split injection into an indecomposable module is an isomorphism.** If `g ∘ₗ f` is bijective
then `f ∘ₗ (g ∘ₗ f)⁻¹ ∘ₗ g` is an idempotent endomorphism of the indecomposable module `f` lands
in, hence is `0` or `1`; it cannot be `0`, because that would force `f` to vanish on a nontrivial
module, so it is the identity and `f` is surjective. -/
theorem IsIndecomposableModule.bijective_of_bijective_comp {N P : Type*}
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] [Nontrivial N]
    (hP : IsIndecomposableModule A P) {f : N →ₗ[A] P} {g : P →ₗ[A] N}
    (h : Function.Bijective (g ∘ₗ f)) : Function.Bijective f := by
  set u : N ≃ₗ[A] N := LinearEquiv.ofBijective (g ∘ₗ f) h with _
  have hgf : ∀ x : N, u.symm (g (f x)) = x := fun x ↦ u.symm_apply_apply x
  set e : Module.End A P := f ∘ₗ (u.symm : N →ₗ[A] N) ∘ₗ g with he
  have hidem : IsIdempotentElem e := by
    ext x
    simp only [he, Module.End.mul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
    rw [hgf]
  have hinjf : Function.Injective f := fun x y hxy ↦ h.1 (by
    simp only [LinearMap.coe_comp, Function.comp_apply, hxy])
  rcases hP.eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · exfalso
    have hzero : ∀ x : N, f x = 0 := fun x ↦ by
      have hx := congrArg (fun t : Module.End A P ↦ t (f x)) h0
      simpa [he, hgf] using hx
    obtain ⟨x, y, hxy⟩ := exists_pair_ne N
    exact hxy (hinjf (by rw [hzero x, hzero y]))
  · refine ⟨hinjf, fun y ↦ ⟨u.symm (g y), ?_⟩⟩
    have hy := congrArg (fun t : Module.End A P ↦ t y) h1
    simpa [he] using hy

/-! ### Fitting's lemma -/

section Fitting

variable [IsNoetherian A M] [IsArtinian A M]

/-- **Fitting's lemma**: an endomorphism of an indecomposable module that is both Noetherian and
Artinian is either nilpotent or bijective.

For a large enough exponent `m`, Mathlib's Fitting decomposition splits `M` as
`ker (f ^ m) ⊕ range (f ^ m)`. Indecomposability collapses one of the two summands: if the range
vanishes then `f ^ m = 0`, and if the kernel vanishes then `f` is injective while the range, being
everything, forces `f` to be surjective. -/
theorem IsIndecomposableModule.isNilpotent_or_bijective (h : IsIndecomposableModule A M)
    (f : Module.End A M) : IsNilpotent f ∨ Function.Bijective f := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  -- The exponent `n + 1` is positive, so `f` itself inherits injectivity and surjectivity from
  -- `f ^ (n + 1)`; the threshold `n` alone could be `0`, where the decomposition says nothing.
  have hcompl := hn (n + 1) (Nat.le_succ n)
  rcases h.eq_bot_or_eq_bot hcompl with hker | hrange
  · apply Or.inr
    rw [← Module.End.isUnit_iff, ← isUnit_pow_succ_iff (n := n), Module.End.isUnit_iff]
    refine ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp ?_⟩
    simpa [hker] using hcompl.sup_eq_top
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩

/-- **Fitting's lemma**, restated: an endomorphism of an indecomposable module that is both
Noetherian and Artinian is either nilpotent or a unit of the endomorphism ring. -/
theorem IsIndecomposableModule.isNilpotent_or_isUnit (h : IsIndecomposableModule A M)
    (f : Module.End A M) : IsNilpotent f ∨ IsUnit f :=
  (h.isNilpotent_or_bijective f).imp id (Module.End.isUnit_iff f).mpr

/-- On an indecomposable module that is Noetherian and Artinian, the non-units of the endomorphism
ring are exactly the nilpotent endomorphisms. This identifies the maximal ideal produced by
`TauCeti.isLocalRing_end_of_isIndecomposable`. -/
theorem IsIndecomposableModule.isNilpotent_iff_not_isUnit (h : IsIndecomposableModule A M)
    (f : Module.End A M) : IsNilpotent f ↔ ¬ IsUnit f := by
  have := h.nontrivial
  exact ⟨IsNilpotent.not_isUnit, (h.isNilpotent_or_isUnit f).resolve_right⟩

end Fitting

/-! ### Local endomorphism rings -/

/-- The endomorphism ring of an indecomposable module of finite length is **local**.

This is the form of Fitting's lemma that drives the Krull-Schmidt theorem: a non-unit endomorphism
is nilpotent, and `1 - f` is then a unit. -/
theorem isLocalRing_end_of_isIndecomposable (hM : IsFiniteLength A M)
    (h : IsIndecomposableModule A M) : IsLocalRing (Module.End A M) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have := h.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  exact (h.isNilpotent_or_isUnit f).symm.imp id IsNilpotent.isUnit_one_sub

/-- A module with local endomorphism ring is indecomposable. This is the converse of
`TauCeti.isLocalRing_end_of_isIndecomposable`, and needs no finiteness hypothesis; nontriviality
comes for free, by `TauCeti.nontrivial_of_isLocalRing_end`. -/
theorem isIndecomposableModule_of_isLocalRing_end [IsLocalRing (Module.End A M)] :
    IsIndecomposableModule A M :=
  have := nontrivial_of_isLocalRing_end (A := A) (M := M)
  isIndecomposableModule_of_forall_isIdempotentElem fun _ hf ↦
    IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hf

/-- For a module of finite length, indecomposability is **equivalent** to having a local
endomorphism ring. -/
theorem isIndecomposableModule_iff_isLocalRing_end (hM : IsFiniteLength A M) :
    IsIndecomposableModule A M ↔ IsLocalRing (Module.End A M) := by
  refine ⟨isLocalRing_end_of_isIndecomposable hM, fun h ↦ ?_⟩
  have := h
  exact isIndecomposableModule_of_isLocalRing_end

variable (A) in
/-- **A local ring is indecomposable as a left module over itself**: its endomorphism ring is the
opposite ring, which is again local. -/
theorem isIndecomposableModule_self [IsLocalRing A] : IsIndecomposableModule A A := by
  have : IsLocalRing (Module.End A A) :=
    .of_surjective' (RingEquiv.moduleEndSelf A).toRingHom (RingEquiv.moduleEndSelf A).surjective
  exact isIndecomposableModule_of_isLocalRing_end

variable (A) in
/-- **A ring is indecomposable as a left module over itself exactly when it is nontrivial and `0`
and `1` are its only idempotents.** An endomorphism of the left module `A` is right multiplication
by an element, and it is idempotent exactly when that element is. -/
theorem isIndecomposableModule_self_iff :
    IsIndecomposableModule A A ↔ Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine and_congr_right fun _ ↦ ⟨fun h e he ↦ ?_, fun h f hf ↦ ?_⟩
  · have hop : IsIdempotentElem (MulOpposite.op e) := by
      rw [IsIdempotentElem, ← MulOpposite.op_mul, he.eq]
    have hf := h (RingEquiv.moduleEndSelf A (MulOpposite.op e))
      (hop.map (RingEquiv.moduleEndSelf A))
    rw [map_eq_zero_iff _ (RingEquiv.moduleEndSelf A).injective,
      map_eq_one_iff _ (RingEquiv.moduleEndSelf A).injective, MulOpposite.op_eq_zero_iff,
      MulOpposite.op_eq_one_iff] at hf
    exact hf
  · obtain ⟨e, rfl⟩ := (RingEquiv.moduleEndSelf A).surjective f
    have he : IsIdempotentElem e.unop := by
      have hee : e * e = e := (RingEquiv.moduleEndSelf A).injective (by rw [map_mul, hf.eq])
      rw [IsIdempotentElem, ← MulOpposite.unop_mul, hee]
    rcases h e.unop he with h0 | h1
    · exact Or.inl (by rw [← MulOpposite.op_unop e, h0, MulOpposite.op_zero, map_zero])
    · exact Or.inr (by rw [← MulOpposite.op_unop e, h1, MulOpposite.op_one, map_one])

/-- **A ring of finite length over itself which is indecomposable over itself is local**, the
converse of `TauCeti.isIndecomposableModule_self` under finite length: by Fitting's lemma the
endomorphism ring of the left module `A`, which is the opposite ring, is local. -/
theorem isLocalRing_of_isIndecomposableModule_self (hA : IsFiniteLength A A)
    (h : IsIndecomposableModule A A) : IsLocalRing A := by
  have := h.nontrivial
  have := isLocalRing_end_of_isIndecomposable hA h
  have : IsLocalRing Aᵐᵒᵖ := .of_surjective' (RingEquiv.moduleEndSelf A).symm.toRingHom
    (RingEquiv.moduleEndSelf A).symm.surjective
  exact .of_surjective' (RingEquiv.opOp A).symm.toRingHom (RingEquiv.opOp A).symm.surjective

end Ring

/-! ### Indecomposable free modules -/

section Free

variable {A : Type u} {M : Type v} [Semiring A] [AddCommMonoid M] [Module A M]

/-- **An indecomposable free module is isomorphic to the scalar semiring.** For a basis vector
`b i`, its span and the span of the remaining basis vectors are complementary, so the latter span
is zero and `i` is the only index. -/
theorem IsIndecomposableModule.nonempty_linearEquiv_of_free [Module.Free A M]
    (h : IsIndecomposableModule A M) : Nonempty (M ≃ₗ[A] A) := by
  have := h.nontrivial
  have := Module.nontrivial A M
  let b := Module.Free.chooseBasis A M
  obtain ⟨i⟩ := b.index_nonempty
  have hi (j : Module.Free.ChooseBasisIndex A M) : j = i := by
    by_contra hji
    rcases h.eq_bot_or_eq_bot (b.linearIndependent.isCompl_span_image b.span_eq
      (isCompl_compl (x := {i}))) with hbot | hbot
    · exact b.ne_zero i (Submodule.span_eq_bot.mp hbot _ ⟨i, rfl, rfl⟩)
    · exact b.ne_zero j (Submodule.span_eq_bot.mp hbot _ ⟨j, hji, rfl⟩)
  have : Subsingleton (Module.Free.ChooseBasisIndex A M) :=
    ⟨fun j j' ↦ (hi j).trans (hi j').symm⟩
  exact ⟨b.repr.trans (Finsupp.uniqueLinearEquiv A A i)⟩

end Free

end TauCeti
