/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.SplitAlgebra.Basic

/-!
# Splinters

A commutative ring `R` is a *splinter* if it is noetherian and reduced and every finite
`R`-algebra `S` with injective structure map `R → S` is split: the unit map has an `R`-linear
retraction `S → R` (`TauCeti.SplitAlgebra`). The direct summand theorem asserts that every
noetherian regular ring is a splinter.

Reducedness is part of the definition. Without it the self-injective ring `k[ε]/(ε²)` would
qualify, since every injective map out of a self-injective ring splits. Bhatt's
scheme-theoretic definition (splitting of `𝒪 → f_* 𝒪` for every finite surjective `f`) forces
reducedness by applying it to `Spec R_red → Spec R`.

The definition tests algebras in the universe of `R`. Since a finite algebra is small over its
base, `TauCeti.Splinter.splitAlgebra` removes this restriction, and with it being a splinter is
invariant under ring isomorphisms between different universes.

## Main definitions

* `TauCeti.Splinter R`: `R` is noetherian, reduced, and every finite injective `R`-algebra is
  split.

## Main results

* `TauCeti.Splinter.splitAlgebra`: over a splinter, every finite injective algebra, in any
  universe, is split.
* `TauCeti.Splinter.iff_forall_splitAlgebra`: the defining condition, with test algebras in any
  universe containing that of `R`.
* `TauCeti.Splinter.iff_of_ringEquiv`: being a splinter is invariant under ring isomorphism.
* `TauCeti.Splinter.comap_map_eq_self`: for an injective integral algebra `S` over a
  splinter `R`, every ideal `I` of `R` is contracted from `S`, i.e. `I S ∩ R = I`.
* `TauCeti.Splinter.isIntegrallyClosed`: a splinter is integrally closed in its total ring of
  fractions; in particular a splinter domain is integrally closed.
* `TauCeti.Splinter.of_isPrincipalIdealRing`: every principal ideal domain, in particular every
  field and `ℤ`, is a splinter.

## References

* B. Bhatt, L. Ma, Zs. Patakfalvi, K. Schwede, K. Tucker, J. Waldron, J. Witaszek,
  *Globally `+`-regular varieties and the minimal model program for threefolds in mixed
  characteristic*, Publ. Math. IHÉS 138 (2023), Definition 2.12.
* B. Bhatt, *Derived splinters in positive characteristic*, Compos. Math. 148 (2012),
  Definition 0.1 and Example 1.1.
* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), §0.1.
-/

public section

namespace TauCeti

universe u v

/-- A commutative ring `R` is a *splinter* if it is noetherian and reduced and every finite
`R`-algebra with injective structure map is split: its unit map has an `R`-linear retraction.
The defining condition tests algebras in the universe of `R`; `TauCeti.Splinter.splitAlgebra`
gives it in every universe. -/
structure Splinter (R : Type u) [CommRing R] : Prop where
  /-- A splinter is noetherian. -/
  isNoetherianRing : IsNoetherianRing R
  /-- A splinter is reduced. -/
  isReduced : IsReduced R
  /-- Every finite injective `R`-algebra in the universe of `R` is split. Use
  `TauCeti.Splinter.splitAlgebra` for algebras in an arbitrary universe. -/
  splitAlgebra_of_injective : ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
    Function.Injective (algebraMap R S) → SplitAlgebra R S

namespace Splinter

variable {R : Type u} [CommRing R]

/-- A finite injective `R`-algebra `S` is split if an isomorphic copy `T` is split whenever it is
finite and injective. -/
private theorem splitAlgebra_of_algEquiv {S T : Type*} [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Module.Finite R S] (e : T ≃ₐ[R] S)
    (hinj : Function.Injective (algebraMap R S))
    (hT : ∀ [Module.Finite R T], Function.Injective (algebraMap R T) → SplitAlgebra R T) :
    SplitAlgebra R S := by
  have : Module.Finite R T := .equiv e.symm.toLinearEquiv
  refine (SplitAlgebra.iff_of_equiv e).1 (hT ?_)
  rw [← e.symm.toAlgHom.comp_algebraMap]
  exact e.symm.injective.comp hinj

/-- Over a splinter `R`, every finite `R`-algebra `S` with injective structure map is split,
whatever the universe of `S`. -/
theorem splitAlgebra (h : Splinter R) {S : Type v} [CommRing S] [Algebra R S]
    [Module.Finite R S] (hinj : Function.Injective (algebraMap R S)) : SplitAlgebra R S := by
  have : Small.{u} S := Module.Finite.small R S
  exact splitAlgebra_of_algEquiv (Shrink.algEquiv R S) hinj (h.splitAlgebra_of_injective _)

/-- A ring is a splinter exactly when it is noetherian and reduced and every finite injective
algebra in a given universe containing that of `R` is split. -/
theorem iff_forall_splitAlgebra :
    Splinter R ↔ IsNoetherianRing R ∧ IsReduced R ∧
      ∀ (S : Type max u v) [CommRing S] [Algebra R S] [Module.Finite R S],
        Function.Injective (algebraMap R S) → SplitAlgebra R S := by
  refine ⟨fun h ↦ ⟨h.isNoetherianRing, h.isReduced, fun S _ _ _ hinj ↦ h.splitAlgebra hinj⟩,
    fun ⟨hN, hR, hS⟩ ↦ ⟨hN, hR, fun S _ _ _ hinj ↦ ?_⟩⟩
  exact splitAlgebra_of_algEquiv (ULift.algEquiv : ULift.{v} S ≃ₐ[R] S) hinj (hS _)

/-- Being a splinter transfers along a ring isomorphism, possibly between different
universes. -/
theorem of_ringEquiv {R' : Type v} [CommRing R'] (h : Splinter R) (e : R ≃+* R') :
    Splinter R' := by
  have := h.isNoetherianRing
  have := h.isReduced
  refine ⟨isNoetherianRing_of_ringEquiv R e, isReduced_of_injective e.symm.toRingHom
    e.symm.injective, fun S _ _ _ hinj ↦ ?_⟩
  let : Algebra R R' := e.toRingHom.toAlgebra
  let : Algebra R S := ((algebraMap R' S).comp e.toRingHom).toAlgebra
  have : IsScalarTower R R' S := .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap R R') := e.surjective
  have : Module.Finite R R' := .of_surjective (Algebra.linearMap R R') hsurj
  have : Module.Finite R S := .trans R' S
  obtain ⟨ρ, hρ⟩ := splitAlgebra_iff_exists_linearMap.1 <|
    h.splitAlgebra (S := S) (hinj.comp e.injective)
  let ρ' : S →ₗ[R] R' := (Algebra.linearMap R R').comp ρ
  exact .of_map_one (ρ'.extendScalarsOfSurjective hsurj) (by simp [ρ', hρ])

/-- Being a splinter is invariant under ring isomorphism. -/
theorem iff_of_ringEquiv {R' : Type v} [CommRing R'] (e : R ≃+* R') :
    Splinter R ↔ Splinter R' :=
  ⟨fun h ↦ h.of_ringEquiv e, fun h ↦ h.of_ringEquiv e.symm⟩

/-- Over a splinter `R`, every ideal `I` is contracted from each injective integral `R`-algebra
`S`: `I S ∩ R = I`. -/
theorem comap_map_eq_self (h : Splinter R) {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) (I : Ideal R) :
    (I.map (algebraMap R S)).comap (algebraMap R S) = I := by
  -- An element of `I S ∩ R` lies in `I S'` for the finite subalgebra `S'` generated by the
  -- coefficients of an expression in generators of `I`, and `S'` is split over `R`.
  refine le_antisymm (fun x hx ↦ ?_) Ideal.le_comap_map
  have := h.isNoetherianRing
  obtain ⟨n, g, hg⟩ : ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = I :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  rw [← hg] at hx ⊢
  rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp,
    Ideal.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  let S' : Subalgebra R S := Algebra.adjoin R (Set.range c)
  have : Module.Finite R S' :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range c)
      fun s _ ↦ Algebra.IsIntegral.isIntegral s
  have hinj' : Function.Injective (algebraMap R S') := fun a b hab ↦
    hinj (by simpa using congrArg Subtype.val hab)
  rw [← (h.splitAlgebra hinj').comap_map_eq_self (Ideal.span (Set.range g)), Ideal.mem_comap]
  have hx : algebraMap R S' x =
      ∑ i, ⟨c i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ * algebraMap R S' (g i) :=
    Subtype.ext (by simpa using hc.symm)
  rw [hx]
  exact sum_mem fun i _ ↦
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Submodule.subset_span ⟨i, rfl⟩))

/-- A splinter is integrally closed in its total ring of fractions; in particular a splinter
domain is integrally closed. -/
theorem isIntegrallyClosed (h : Splinter R) : IsIntegrallyClosed R := by
  -- For `x = a / b` integral over `R`, split `R → R[x]` by `ρ`; then `b ρ(x) = ρ(b x) = a`.
  refine (isIntegrallyClosed_iff (FractionRing R)).2 fun {x} hx ↦ ?_
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R {x}
  have : Module.Finite R S := Algebra.finite_adjoin_simple_of_isIntegral hx
  have hinj : Function.Injective (algebraMap R S) := fun a b hab ↦
    IsFractionRing.injective R (FractionRing R) (by simpa using congrArg Subtype.val hab)
  obtain ⟨ρ, hρ⟩ := splitAlgebra_iff_exists_linearMap.1 (h.splitAlgebra hinj)
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  let y : S := ⟨_, Algebra.self_mem_adjoin_singleton R _⟩
  have key : (b : R) • y = algebraMap R S a :=
    Subtype.ext (by simp [y, Algebra.smul_def])
  have hab : (b : R) * ρ y = a := by
    simpa [Algebra.algebraMap_eq_smul_one, hρ] using congrArg ρ key
  refine ⟨ρ y, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_comm, hab]

variable (R) in
/-- Every principal ideal domain is a splinter; in particular every field and `ℤ` are. A finite
injective algebra `S` has a prime `q` lying over `0`, and `S ⧸ q` is a finite torsion-free module
over the principal ideal domain, hence free, hence split. -/
theorem of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R] : Splinter R := by
  refine ⟨inferInstance, inferInstance, fun S _ _ _ hinj ↦ ?_⟩
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  obtain ⟨q, -, hq, hqR⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R)
    (⊥ : Ideal S) (Ideal.under_bot R S).le
  refine SplitAlgebra.of_algHom (Ideal.Quotient.mkₐ R q) ?_
  have hinj' : Function.Injective (algebraMap R (S ⧸ q)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.under R :=
      (Ideal.mem_under R q).2 ((Ideal.Quotient.eq_zero_iff_mem (a := algebraMap R S a)).1 ha)
    simpa [hqR] using this
  have : Module.IsTorsionFree R (S ⧸ q) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj'
  have : Nontrivial (S ⧸ q) := Ideal.Quotient.nontrivial_iff.2 hq.ne_top
  exact splitAlgebra_of_free

end Splinter

end TauCeti
