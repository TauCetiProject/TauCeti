/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.LocallyFree.ClassGroup
public import TauCeti.RingTheory.FractionalIdeal.Projective
import TauCeti.RingTheory.DedekindDomain.ModuleDecomposition
import TauCeti.RingTheory.FractionalIdeal.LinearEquiv

/-!
# From ideal classes to locally free classes

For a Dedekind domain `A`, the assignment `I ↦ [I] - [A]` defines a homomorphism from
`Additive (ClassGroup A)` to projective `K₀(A)`. The product identity `I ⊕ J ≅ A ⊕ IJ`
makes it additive, and scaling an ideal by a nonzero element preserves its module class,
so it descends through the quotient by principal ideals.

If `A` is not a field, its image lies in the locally free class group: every nonzero
integral ideal is locally free of rank one. `TauCeti.LocallyFree.ofIdealClass` is the
resulting homomorphism. Its computation on nonzero integral ideals identifies it with
the assignment `[I] ↦ [I] - [A]`. The map is surjective: a pseudo-basis expresses every
finite projective module as a product of nonzero ideals, so its reduced class comes from the
product of their ideal classes. This includes the zero module, represented by the empty
product. Injectivity is the remaining direction of the ideal-class comparison.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter II,
  Proposition 2.6 and Corollary 2.6.3, and Chapter I, Proposition 3.4.
-/

public section

open scoped nonZeroDivisors TensorProduct

namespace TauCeti

universe u

variable {A : Type u} [CommRing A]

namespace FiniteProjectiveModules

section SameUniverse

variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]

section FractionalIdeal

variable [IsDomain A]

/-- The product of ideal classes corresponds to addition of reduced projective classes. -/
theorem classOf_mul [IsNoetherianRing A] [Ring.DimensionLEOne A] (I J : (FractionalIdeal A⁰ K)ˣ) :
    classOf A ((I * J : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) 1 =
      classOf A (I : FractionalIdeal A⁰ K) 1 + classOf A (J : FractionalIdeal A⁰ K) 1 := by
  let : Module.Finite A (↑I * ↑J : FractionalIdeal A⁰ K) :=
    inferInstanceAs (Module.Finite A ((I * J : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
  let : Module.Projective A (↑I * ↑J : FractionalIdeal A⁰ K) :=
    inferInstanceAs (Module.Projective A ((I * J : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
  obtain ⟨e⟩ := FractionalIdeal.nonempty_prod_linearEquiv_prod_mul I.isUnit J.ne_zero
  have h := classOf_congr e 2
  rw [classOf_prod 1 1, classOf_prod 1 1] at h
  have hA : classOf A A 1 = 0 := by simp [classOf_def]
  simpa [hA] using h.symm

/-- A principal fractional ideal has zero reduced projective class. -/
@[simp]
theorem classOf_toPrincipalIdeal (x : Kˣ) :
    classOf A (toPrincipalIdeal A K x : FractionalIdeal A⁰ K) 1 = 0 := by
  let e : (1 : FractionalIdeal A⁰ K) ≃ₗ[A] A :=
    (FractionalIdeal.coeIdealEquiv (⊤ : Ideal A)).trans Submodule.topEquiv
  let s := FractionalIdeal.spanSingletonMulEquiv (IsRegular.of_ne_zero x.ne_zero).left
    (1 : FractionalIdeal A⁰ K)
  have hs : FractionalIdeal.spanSingleton A⁰ (x : K) * 1 =
      (toPrincipalIdeal A K x : FractionalIdeal A⁰ K) := by simp
  let e' := LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule hs)
  have h := classOf_congr ((s.trans e').symm.trans e) 1
  simpa [classOf_def] using h

end FractionalIdeal

variable [IsDedekindDomain A]

variable (A K) in
/-- The reduced class of an invertible fractional ideal, as a multiplicative homomorphism
with values in the multiplicative type tag of projective `K₀`. -/
private noncomputable def fractionalIdealClassHom :
    (FractionalIdeal A⁰ K)ˣ →*
      Multiplicative (SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) where
  toFun I := Multiplicative.ofAdd (classOf A (I : FractionalIdeal A⁰ K) 1)
  map_one' := by
    let : Module.Finite A (1 : FractionalIdeal A⁰ K) :=
      inferInstanceAs (Module.Finite A ((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
    let : Module.Projective A (1 : FractionalIdeal A⁰ K) :=
      inferInstanceAs (Module.Projective A ((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
    let e : (1 : FractionalIdeal A⁰ K) ≃ₗ[A] A :=
      (FractionalIdeal.coeIdealEquiv (⊤ : Ideal A)).trans Submodule.topEquiv
    exact congrArg Multiplicative.ofAdd ((classOf_congr e 1).trans (by simp [classOf_def]))
  map_mul' I J := congrArg Multiplicative.ofAdd (classOf_mul I J)

end SameUniverse

variable [IsDedekindDomain A]

variable (A) in
/-- The homomorphism `[I] ↦ [I] - [A]` from the ideal class group to projective `K₀(A)`. -/
noncomputable def idealClassHom :
    Additive (ClassGroup A) →+ SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  (QuotientGroup.lift (toPrincipalIdeal A (FractionRing A)).range
    (fractionalIdealClassHom A (FractionRing A)) (by
      rintro _ ⟨x, rfl⟩
      exact congrArg Multiplicative.ofAdd (classOf_toPrincipalIdeal x))).toAdditiveLeft

/-- The ideal-class homomorphism evaluated on a fractional ideal in the canonical fraction field. -/
@[simp]
theorem idealClassHom_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    idealClassHom A (Additive.ofMul (ClassGroup.mk (FractionRing A) I)) =
      classOf A (I : FractionalIdeal A⁰ (FractionRing A)) 1 := by
  rw [← ClassGroup.Quot_mk_eq_mk]
  exact congrArg Multiplicative.toAdd
    (QuotientGroup.lift_quot_mk _ _ I)

/-- On a nonzero integral ideal the homomorphism is its reduced projective class.
The projectivity instance is required to express the right-hand side using `classOf`. -/
@[simp]
theorem idealClassHom_mk0 (I : (Ideal A)⁰) [Module.Projective A (I : Ideal A)] :
    idealClassHom A (Additive.ofMul (ClassGroup.mk0 I)) = classOf A (I : Ideal A) 1 := by
  rw [← ClassGroup.mk_mk0 (FractionRing A), idealClassHom_mk]
  exact classOf_congr (FractionalIdeal.coeIdealEquiv (I : Ideal A)) 1

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

variable (A K) in
/-- Every reduced class of a finite projective module over a Dedekind domain comes from an
ideal class. The reduction uses the dimension over the fraction field. -/
theorem exists_idealClassHom_eq_classOf (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ c : Additive (ClassGroup A), idealClassHom A c =
      classOf A M (Module.finrank K (K ⊗[A] M)) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := Module.exists_linearEquiv_pi_ideal A K M
  have hP i : Module.Projective A (J i) := by
    let I : (FractionalIdeal A⁰ (FractionRing A))ˣ :=
      Units.mk0 (J i : FractionalIdeal A⁰ (FractionRing A))
        (FractionalIdeal.coeIdeal_ne_zero.mpr (hJ i))
    let : Module.Projective A (J i : FractionalIdeal A⁰ (FractionRing A)) :=
      inferInstanceAs (Module.Projective A (I : FractionalIdeal A⁰ (FractionRing A)))
    exact Module.Projective.of_equiv
      (FractionalIdeal.coeIdealEquiv (P := FractionRing A) (S := A⁰) (J i))
  have : ∀ i, Module.Projective A (J i) := hP
  refine ⟨∑ i, Additive.ofMul (ClassGroup.mk0 ⟨J i, mem_nonZeroDivisors_of_ne_zero (hJ i)⟩), ?_⟩
  rw [map_sum]
  simp only [idealClassHom_mk0]
  simpa using (classOf_eq_sum_of_linearEquiv_pi (fun i ↦ J i) e (fun _ ↦ 1)).symm

end FiniteProjectiveModules

namespace LocallyFree

variable [IsDedekindDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

open FiniteProjectiveModules

/-- Ideal classes give locally free classes over a nonfield Dedekind domain. -/
theorem idealClassHom_mem_classGroup (hA : ¬IsField A) (c : Additive (ClassGroup A)) :
    idealClassHom A c ∈ classGroup A K A := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c.toMul
  have h := isLocallyFreeOfRank_one_of_ne_bot (K := K)
    (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  have : Module.Projective A (I : Ideal A) := h.projective hA
  have hc : Additive.ofMul (ClassGroup.mk0 I) = c := congrArg Additive.ofMul hI
  rw [← hc, idealClassHom_mk0]
  exact classOf_mem_classGroup hA h

variable (A K) in
/-- The homomorphism from ideal classes to locally free classes, sending `[I]` to `[I] - [A]`.
It is defined for a nonfield Dedekind base, where nonzero ideals are locally free of rank one. -/
noncomputable def ofIdealClass (hA : ¬IsField A) :
    Additive (ClassGroup A) →+ classGroup A K A :=
  (idealClassHom A).codRestrict (classGroup A K A) (idealClassHom_mem_classGroup hA)

/-- Forgetting membership in the locally free class group recovers the projective class. -/
@[simp]
theorem coe_ofIdealClass (hA : ¬IsField A) (c : Additive (ClassGroup A)) :
    (ofIdealClass A K hA c : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) =
      idealClassHom A c :=
  (rfl)

/-- Every class in the locally free class group of the base Dedekind domain is the reduced
class of an ideal. This is the surjective direction of the ideal-class comparison. -/
theorem ofIdealClass_surjective (hA : ¬IsField A) : Function.Surjective (ofIdealClass A K hA) := by
  have hle : classGroup A K A ≤ (idealClassHom A).range := by
    rw [classGroup_le_iff hA]
    intro M _ mA mΛ ht _ _ n h
    -- At `Λ = A` the generator predicate carries two compatible `A`-actions.
    -- Identify them before comparing the generic dimension with the reduced class.
    have heq : mA = mΛ := Module.ext' mA mΛ fun a m ↦ by
      have hassoc := ht.smul_assoc a (1 : A) m
      simpa only [smul_eq_mul, mul_one, one_smul] using hassoc.symm
    cases heq
    have hn : Module.finrank K (K ⊗[A] M) = n := by
      simpa only [(TensorProduct.AlgebraTensorModule.rid A K K).finrank_eq,
        Module.finrank_self, mul_one] using h.finrank hA
    obtain ⟨c, hc⟩ := exists_idealClassHom_eq_classOf A K M
    exact ⟨c, hn ▸ hc⟩
  intro x
  obtain ⟨c, hc⟩ := hle x.property
  exact ⟨c, Subtype.ext hc⟩

end LocallyFree

end TauCeti
