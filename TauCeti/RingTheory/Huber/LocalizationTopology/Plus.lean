/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.Pair

/-!
# The plus ring `A_U⁺` of a rational localisation

For a rational subset `U = R(T/s)` of `Spa(A, A⁺)`, Wedhorn (§8.1) completes the affinoid ring
`(Aₛ, C)`, where `C` is the integral closure of `A⁺[T/s]` in `Aₛ` — a ring of integral elements of
the localised topology. The plus ring of `A_U = A⟨T/s⟩` is therefore `A_U⁺`, the closure in
`A⟨T/s⟩` of the image of `C`. This file defines it and proves that it is a ring of integral
elements of `A_U`, so that `(A_U, A_U⁺)` is a Huber pair.

## The layers

```text
Algebra.adjoin A⁺ {t/s}     A⁺[t₁/s, …, tₙ/s]  (Mathlib's, unwrapped)  ⊆ Aₛ
integralClosure A⁺[T/s] Aₛ  C, a ring of integral elements of Aₛ        ⊆ Aₛ
completedPlusSubring        the closure of the image of C               ⊆ A⟨T/s⟩
```

## Why not the integral closure of the image

An alternative definition of `A_U⁺` is the integral closure in `A_U` of the image of `A⁺[T/s]`.
That subring need not be open, so `(A_U, A_U⁺)` would not be a Huber pair: for
`A = ℚ` with the `p`-adic topology, `A⁺ = ℤ_(p)`, `T = {1}` and `s = 1`, the completion is `ℚ_p`,
and the integral closure of `ℤ_(p)` in `ℚ_p` consists of elements algebraic over `ℚ`, a countable
set, whereas every nonempty open subset of `ℚ_p` is uncountable. The closure of the image of `C`
is open because `C` is, and it is integrally closed by Huber's Lemma 2.4.3(iv)
(`UniformSpace.Completion.isIntegrallyClosedIn_topologicalClosure_map_coeRingHom`), the half of
Wedhorn's Lemma 7.47(4) that this file needs.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.completedPlusSubring`: **`A_U⁺`**.

## Main results

* `TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_completedPlusSubring`: when `A⁺`
  consists of power-bounded elements and contains the image of the ideal of definition, `A_U⁺` is
  a ring of integral elements of `A⟨T/s⟩`.
* `TauCeti.Huber.PairOfDefinition.coeRingHom_mem_completedPlusSubring`: the completion map
  carries `C` into `A_U⁺`, making it a morphism of pairs `(A(T/s), C) → (A⟨T/s⟩, A_U⁺)`.
* `TauCeti.Huber.PairOfDefinition.toCompletionLoc_mem_completedPlusSubring` and
  `TauCeti.Huber.PairOfDefinition.divBy_mem_completedPlusSubring`: the image of `A⁺` and each
  fraction `t/s` lie in `A_U⁺`.
* `TauCeti.Huber.PairOfDefinition.isPowerBounded_of_mem_adjoin_plus`: when every element of `A⁺`
  is power-bounded in `A`, so is every element of `A⁺[T/s]` in `Aₛ`.
* `TauCeti.Huber.PairOfDefinition.locSubring_mul_idealOfDefinition_mem_adjoin_plus`: the
  absorption itself — inside `Aₛ`, an element of `D = A₀[T/s]` times an element of the ideal
  of definition `I` lies in `A⁺[T/s]`.
* `TauCeti.Huber.PairOfDefinition.locIdealImage_one_le_adjoin_plus`: inside `Aₛ`, `A⁺[T/s]`
  absorbs the first basic neighbourhood of zero, which makes it open.
* `TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_integralClosure_adjoin_plus`: under the
  same hypotheses, `C` is a ring of integral elements of `Aₛ`.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, branch `dev/adic-spaces` at `37bbdaeb9`)
carries a version of this construction in `projects/AdicSpaces/Adic spaces/Presheaf.lean` as
`RationalLocData.locPlusSubring`, `completedPlusSubringBase` and `completedPlusSubring`; its
`completedPlusSubringBase` is the closure of the image of `(A⁺[T/s])^int`, the object defined here.

The absorption results are adapted from the same AINTLIB file:
`locSubring_mul_idealOfDefinition_mem_adjoin_plus` and `locIdealImage_one_le_adjoin_plus` follow
`RationalLocData.locNhd_one_subset_locPlusSubring` and the neighbourhood step of
`RationalLocData.completedPlusSubringBase_isOpen`. `isPowerBounded_of_mem_adjoin_plus` and the
power-boundedness half of `isRingOfIntegralElements_integralClosure_adjoin_plus` follow
`RationalLocData.locPlusSubring_le_powerBounded` and
`RationalLocData.integralClosure_locPlusSubring_le_powerBounded`. Integral closedness of `A_U⁺`
comes instead from this repository's Huber 2.4.3(iv). No proof text was copied.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §8.1, §8.2, 8.16, 7.19, 7.20 and 7.47(4).
-/

public section

open Pointwise Topology TauCeti.Localization

namespace TauCeti.Huber

namespace PairOfDefinition

section Topological

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **`A_U⁺`**, Wedhorn's plus ring of `A⟨T/s⟩`: the closure in `A⟨T/s⟩` of the image of `C`, the
integral closure of `A⁺[T/s]` in `Aₛ`. It needs no hypothesis on `Aplus`; under the hypotheses of
`isRingOfIntegralElements_completedPlusSubring` it is a ring of integral elements of `A⟨T/s⟩`.

Under the same hypotheses `C` is a ring of integral elements of `Aₛ`
(`isRingOfIntegralElements_integralClosure_adjoin_plus`), and `A_U⁺` is its completed counterpart.
It is not the integral closure in `A⟨T/s⟩` of the image of `A⁺[T/s]`, a subring that need not be
open. The body is not exposed: `coe_completedPlusSubring` describes it as a set, and
`toCompletionLoc_mem_completedPlusSubring` and `divBy_mem_completedPlusSubring` show that it
contains the image of `A⁺` and each `t/s`. -/
noncomputable def completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Subring (UniformSpace.Completion S) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  ((integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
    S).toSubring.map UniformSpace.Completion.coeRingHom).topologicalClosure

/-- **As a set, `A_U⁺` is the closure in `A⟨T/s⟩` of the image of `C`**, the integral closure of
`A⁺[T/s]` in `Aₛ`. The body of `completedPlusSubring` is not exposed, so this is how a consumer
unfolds it; `UniformSpace.Completion.coe_topologicalClosure_map_coeRingHom` is the same equation
for the closure of the image of an arbitrary subring. Here `Aₛ` carries `locUniformSpace`, so a
fact about `Aₛ` stated at `locTopology`, such as the openness of `C`, must first be moved across
`locUniformSpace_toTopologicalSpace`. -/
theorem coe_completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completedPlusSubring P Aplus T s S hden : Set (UniformSpace.Completion S)) =
      closure (((↑) : S → UniformSpace.Completion S) ''
        (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
          S : Set S)) := (rfl)

/-- **Membership in `A_U⁺`**: an element of `A⟨T/s⟩` lies in `A_U⁺` exactly when it lies in the
closure of the image of `C`, the integral closure of `A⁺[T/s]` in `Aₛ`. This is the membership
form of `coe_completedPlusSubring`. -/
@[simp]
theorem mem_completedPlusSubring_iff (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ x : UniformSpace.Completion S, x ∈ completedPlusSubring P Aplus T s S hden ↔
      x ∈ closure (((↑) : S → UniformSpace.Completion S) ''
        (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
          S : Set S)) := by
  intro x
  rw [← SetLike.mem_coe, coe_completedPlusSubring]

/-- **`A_U⁺` is the smallest closed subring containing the image of `C`**, the integral closure
of `A⁺[T/s]` in `Aₛ`: a closed subring of `A⟨T/s⟩` contains `A_U⁺` exactly when it contains the
image of every element of `C`. -/
theorem completedPlusSubring_le_iff (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {R : Subring (UniformSpace.Completion S)}, IsClosed (R : Set (UniformSpace.Completion S)) →
      (completedPlusSubring P Aplus T s S hden ≤ R ↔
        ∀ x ∈ integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
          S, (x : UniformSpace.Completion S) ∈ R) := by
  intro R hR
  rw [← SetLike.coe_subset_coe, coe_completedPlusSubring, hR.closure_subset_iff,
    Set.image_subset_iff]
  rfl

/-- **`A_U⁺` is closed** in `A⟨T/s⟩`, with no hypothesis on `Aplus`. -/
theorem isClosed_completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsClosed (completedPlusSubring P Aplus T s S hden : Set (UniformSpace.Completion S)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [coe_completedPlusSubring]
  exact isClosed_closure

/-- **The image of `C` lies in `A_U⁺`.** The completion map `A(T/s) → A⟨T/s⟩` carries the
integral closure `C` of `A⁺[T/s]` in `A(T/s)` into the plus ring of the completed localization,
which is by definition the closure of that image. Together with
`UniformSpace.Completion.continuous_coeRingHom` this makes the completion map a morphism of pairs
`(A(T/s), C) → (A⟨T/s⟩, A_U⁺)`, the second factor of the structure map `ρ : A → A⟨T/s⟩`; the
first factor is covered by `algebraMap_mem_integralClosure_adjoin_plus`. -/
theorem coeRingHom_mem_completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {x : S}
    (hx : x ∈ (integralClosure ↥(Algebra.adjoin Aplus
      (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    UniformSpace.Completion.coeRingHom x ∈ completedPlusSubring P Aplus T s S hden := by
  -- `A_U⁺` is the closure of the image of `C`, so the image itself is inside it
  rw [mem_completedPlusSubring_iff]
  exact subset_closure ⟨x, hx, rfl⟩

/-- **The structure map `A → A⟨T/s⟩` carries `A⁺` into `A_U⁺`**, with no hypothesis on `Aplus`.
Together with `continuous_toCompletionLoc`, this makes the structure map a morphism of pairs
`(A, A⁺) → (A⟨T/s⟩, A_U⁺)`. The companion `divBy_mem_completedPlusSubring` puts each fraction `t/s`
in `A_U⁺` as well. -/
theorem toCompletionLoc_mem_completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {a : A} (ha : a ∈ Aplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    toCompletionLoc P T s S hden a ∈ completedPlusSubring P Aplus T s S hden := by
  -- `a` already lies in `A⁺[T/s] ⊆ C`, and the image of `C` lies in its closure
  rw [mem_completedPlusSubring_iff, toCompletionLoc_apply]
  exact subset_closure ⟨_, Subalgebra.algebraMap_mem _ (algebraMap Aplus _ ⟨a, ha⟩), rfl⟩

/-- **Each fraction `t/s` with `t ∈ T` lies in `A_U⁺`**, with no hypothesis on `Aplus`. Here
`t/s` is `divBy t s` in `Aₛ`, carried into `A⟨T/s⟩` by the completion map. The companion
`toCompletionLoc_mem_completedPlusSubring` puts the image of `A⁺` in `A_U⁺`; together they give
the plus-ring conditions of the universal property of the rational localisation. A goal phrased
as the image of `t` times the inverse of the image of `s` is first rewritten into this form by
`toCompletionLoc_mul_unit_inv_eq_divBy`. -/
theorem divBy_mem_completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {t : A} (ht : t ∈ T) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ((divBy t s : S) : UniformSpace.Completion S) ∈ completedPlusSubring P Aplus T s S hden := by
  -- `t/s` already lies in `A⁺[T/s] ⊆ C`, and the image of `C` lies in its closure
  rw [mem_completedPlusSubring_iff]
  exact subset_closure ⟨_, algebraMap_mem _ ⟨_, Algebra.subset_adjoin ⟨⟨t, ht⟩, rfl⟩⟩, rfl⟩

/-- **When every element of `A⁺` is power-bounded, so is every element of `A⁺[T/s]`**, inside `Aₛ`
and before any completion. This is the pre-completion half of the power-boundedness of `A_U⁺` in
`TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_completedPlusSubring`. -/
theorem isPowerBounded_of_mem_adjoin_plus (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {x : S}
    (hx : x ∈ Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))) :
    letI := locTopology P T s S hden
    IsPowerBounded x := by
  let _ := locTopology P T s S hden
  have _ := nonarchimedeanRing_locTopology P T s S hden
  -- `(Aₛ)°` is a subring, so it is enough that the two families generating `A⁺[T/s]` are
  -- power-bounded: the image of `A⁺` because power-boundedness transfers along `A → Aₛ`, and
  -- each `t/s` because it lies in the bounded ring of definition `D`.
  have hle : (Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))).toSubring
      ≤ powerBoundedSubring S := by
    rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro w (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · exact mem_powerBoundedSubring.mpr
        (isPowerBounded_algebraMap_of_isPowerBounded P T s S hden (hAplus ha))
    · exact mem_powerBoundedSubring.mpr (isPowerBounded_divBy P T s S hden ht)
  exact mem_powerBoundedSubring.mp (hle hx)

omit [IsTopologicalRing A] in
/-- **`A⁺[T/s]` absorbs the ideal of definition**, inside `Aₛ` and before any completion: for `c`
in the ring of definition `D = A₀[T/s]` of the localised topology and `i` in the ideal of
definition `I`, the product `c · i` already lies in the subring `A⁺[T/s]` whose integral closure
`C` underlies `A_U⁺`. This is the absorption itself; `locIdealImage_one_le_adjoin_plus`
packages it as a statement about the first basic neighbourhood of zero. The strategy is
Wedhorn's, in the proofs of Proposition 7.19 and Lemma 7.20.

Two facts carry it. The image of `I` lies in `Aplus`, which is the hypothesis `hIplus`; and `I`
is an ideal *of `A₀`*, so a coefficient contributed by `A₀` can be pushed onto the numerator
instead. Only the containment is needed, not power-boundedness or a nonarchimedean topology: for a
ring of integral elements `A⁺` it is discharged by
`TauCeti.Huber.IsRingOfIntegralElements.mem_of_isTopologicallyNilpotent` applied to
`TauCeti.Huber.PairOfDefinition.isTopologicallyNilpotent_of_mem_idealOfDefinition`. -/
theorem locSubring_mul_idealOfDefinition_mem_adjoin_plus
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    {c : S} (hc : c ∈ locSubring P T s S) {i : P.ringOfDefinition}
    (hi : i ∈ P.idealOfDefinition) :
    c * algebraMap A S (i : A) ∈
      Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)) := by
  -- Running over `D` with the predicate `c · I ⊆ A⁺[T/s]` breaks at the multiplicative step:
  -- `A₀ ⊄ A⁺` leaves `c` itself outside `A⁺[T/s]`. So run instead over the transporter of
  -- `W = {z | z · I ⊆ A⁺[T/s]}` into itself — unlike `W`, that is a subring, so `locSubring_le_iff`
  -- decides it on the generators of `D`. Multiplying by `1` recovers `W`.
  have hdiv : ∀ t ∈ T,
      (divBy t s : S) ∈ Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)) :=
    fun t ht ↦ Algebra.subset_adjoin ⟨⟨t, ht⟩, rfl⟩
  have hplus : ∀ a ∈ Aplus,
      algebraMap A S a ∈ Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)) :=
    fun a ha ↦ Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : Aplus)
  set E := Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))
  -- The ideal of definition lands in `A⁺` by hypothesis, hence in `A⁺[T/s]`.
  have hI : ∀ j ∈ P.idealOfDefinition, algebraMap A S (j : A) ∈ E := fun j hj ↦
    hplus _ (hIplus j hj)
  -- `W`: the elements of `Aₛ` carrying the image of `I` into `A⁺[T/s]`. It is an additive
  -- subgroup, but not a subring.
  let W : AddSubgroup S :=
    { carrier := {z | ∀ j ∈ P.idealOfDefinition, z * algebraMap A S (j : A) ∈ E}
      add_mem' := fun hx hy j hj ↦ by rw [add_mul]; exact add_mem (hx j hj) (hy j hj)
      zero_mem' := fun j _ ↦ by rw [zero_mul]; exact zero_mem E
      neg_mem' := fun hx j hj ↦ by rw [neg_mul]; exact neg_mem (hx j hj) }
  -- `R`: the transporter of `W` into itself, which is a subring, so `D ≤ R` is decided by the
  -- generators of `D`.
  let R : Subring S :=
    { carrier := {x | ∀ z ∈ W, x * z ∈ W}
      one_mem' := fun z hz ↦ by rwa [one_mul]
      mul_mem' := fun hx hy z hz ↦ by rw [mul_assoc]; exact hx _ (hy z hz)
      zero_mem' := fun z _ ↦ by rw [zero_mul]; exact zero_mem W
      add_mem' := fun hx hy z hz ↦ by rw [add_mul]; exact add_mem (hx z hz) (hy z hz)
      neg_mem' := fun hx z hz ↦ by rw [neg_mul]; exact neg_mem (hx z hz) }
  have hDR : locSubring P T s S ≤ R := by
    refine (locSubring_le_iff P T s S).mpr ⟨fun a ha z hz j hj ↦ ?_, fun t ht z hz j hj ↦ ?_⟩
    · -- a coefficient from `A₀` moves onto the numerator, where `I` absorbs it
      have h := hz (⟨a, ha⟩ * j) (Ideal.mul_mem_left _ _ hj)
      rw [MulMemClass.coe_mul, map_mul] at h
      rw [mul_comm (algebraMap A S a) z, mul_assoc]
      exact h
    · -- a fraction is already in `A⁺[T/s]`
      rw [mul_assoc]
      exact mul_mem (hdiv t ht) (hz j hj)
  -- `1 ∈ W` by `hI`, and multiplying by it turns `c ∈ R` back into `c ∈ W`
  have h := hDR hc 1 (fun j hj ↦ by rw [one_mul]; exact hI j hj) i hi
  rwa [mul_one] at h

omit [IsTopologicalRing A] in
/-- **`A⁺[T/s]` absorbs the first basic neighbourhood of zero**, inside `Aₛ` and before any
completion: the image in `Aₛ` of `J = I · D`, for `D = A₀[T/s]` the ring of definition of the
localised topology, lies in the subring `A⁺[T/s]`.

This is the openness step for `A_U⁺`. Once `Aₛ` carries the localised topology — which needs
`TauCeti.Huber.PairOfDefinition.HasDenominatorPower` — the sets `locIdealImage P T s S n` are a
neighbourhood basis of zero, so absorbing the first of them is what makes `A⁺[T/s]` an open
subgroup of `Aₛ`. Its integral closure `C`, and then the closure of the image of `C` in
`A⟨T/s⟩`, inherit the openness.

Only the packaging is here. `J` is spanned over `D` by the image of `I`, so a span induction
reduces the containment to the absorption itself,
`TauCeti.Huber.PairOfDefinition.locSubring_mul_idealOfDefinition_mem_adjoin_plus`. -/
theorem locIdealImage_one_le_adjoin_plus (P : PairOfDefinition A) (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    locIdealImage P T s S 1 ≤
      (Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))).toSubring.toAddSubgroup := by
  set E := Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))
  -- The span induction carries a `D`-coefficient `c` along, so that the `smul` step can move a
  -- fresh coefficient into it; every generator is absorbed by the previous theorem.
  have hJ : ∀ d ∈ locIdeal P T s S ^ 1, ∀ c : locSubring P T s S,
      ((c * d : locSubring P T s S) : S) ∈ E := by
    intro d hd
    rw [locIdeal_pow_eq_span, pow_one] at hd
    induction hd using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      intro c
      rw [MulMemClass.coe_mul, toLocSubring_apply]
      exact locSubring_mul_idealOfDefinition_mem_adjoin_plus P Aplus hIplus T s S c.2 hi
    | zero =>
      intro c
      rw [mul_zero, ZeroMemClass.coe_zero]
      exact zero_mem E
    | add y z _ _ hy hz =>
      intro c
      rw [mul_add, AddMemClass.coe_add]
      exact add_mem (hy c) (hz c)
    | smul r y _ hy =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (c * r)
  intro x hx
  obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T s S 1).mp hx
  exact Subring.mem_toAddSubgroup.mpr (Subalgebra.mem_toSubring.mpr (one_mul d ▸ hJ d hd 1))

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- **`A⁺` maps into `C`**, the integral closure of `A⁺[T/s]` in `Aₛ`: an element of `A⁺` lands in
the adjoined subring already, hence in its integral closure. No topology is involved. -/
lemma algebraMap_mem_integralClosure_adjoin_plus (Aplus : Subring A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (a : A) (ha : a ∈ Aplus) :
    algebraMap A S a ∈ (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦
      (divBy (t : A) s : S))) S).toSubring :=
  Subalgebra.algebraMap_mem _ (⟨_, Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : Aplus)⟩ :
    ↥(Algebra.adjoin Aplus _))

/-- **When `A⁺` consists of power-bounded elements and contains the image of the ideal of
definition, the integral closure of `A⁺[T/s]` in `Aₛ` is a ring of integral elements** of the
localised topology: it is open, integrally closed in `Aₛ`, and contained in `(Aₛ)°`. Those are the
three conditions a Huber pair asks of its plus ring.

The integral closure is taken here in `Aₛ`, not in `A⟨T/s⟩`;
`isRingOfIntegralElements_completedPlusSubring` carries the three conditions to the closure of its
image in `A⟨T/s⟩`, which is `A_U⁺`. -/
theorem isRingOfIntegralElements_integralClosure_adjoin_plus (P : PairOfDefinition A)
    (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    letI := nonarchimedeanRing_locTopology P T s S hden
    IsRingOfIntegralElements
      (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
        S).toSubring := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  have _ := nonarchimedeanRing_locTopology P T s S hden
  set E := Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))
  -- `A⁺[T/s]` absorbs the first basic neighbourhood of zero, so it is itself open.
  have hopen : IsOpen (E.toSubring : Set S) := by
    rw [← Subring.coe_toAddSubgroup]
    exact AddSubgroup.isOpen_mono (locIdealImage_one_le_adjoin_plus P Aplus hIplus T s S)
      (isOpen_locIdealImage P T s S hden 1)
  -- Power-boundedness is decided by `A⁺[T/s]` alone.
  have hpb : E.toSubring ≤ powerBoundedSubring S := fun _ hx ↦
    mem_powerBoundedSubring.mpr (isPowerBounded_of_mem_adjoin_plus P Aplus hAplus T s S hden hx)
  exact Pair.isRingOfIntegralElements_integralClosure (R := E.toSubring) hopen hpb

-- `C` lies in `(Aₛ)°` for the uniformity's topology: `A⁺[T/s]` does, and `(Aₛ)°` is integrally
-- closed; the fact about `A⁺[T/s]` is stated at `locTopology`, hence moved across
-- `locUniformSpace_toTopologicalSpace`.
private theorem integralClosure_adjoin_plus_le_powerBoundedSubring (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
      S).toSubring ≤ powerBoundedSubring S := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  exact Subring.integralClosure_subring_le_iff.mpr fun z hz ↦ mem_powerBoundedSubring.mpr <|
    locUniformSpace_toTopologicalSpace P T s S hden ▸
      isPowerBounded_of_mem_adjoin_plus P Aplus hAplus T s S hden hz

/-- **`A_U⁺` lies in `(A⟨T/s⟩)°`** as soon as every element of `A⁺` is power-bounded. This is the
power-boundedness condition of `isRingOfIntegralElements_completedPlusSubring`, and unlike that
theorem it needs no hypothesis on the ideal of definition: enlarging a plus ring of `A⟨T/s⟩` from
`A_U⁺` to `(A⟨T/s⟩)°` along it only shrinks the adic spectrum. -/
theorem completedPlusSubring_le_powerBoundedSubring (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    completedPlusSubring P Aplus T s S hden ≤ powerBoundedSubring (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  exact topologicalClosure_map_coeRingHom_le_powerBoundedSubring
    (integralClosure_adjoin_plus_le_powerBoundedSubring P Aplus hAplus T s S hden)

/-- **`(A⟨T/s⟩, A_U⁺)` is a Huber pair**: when `A⁺` consists of power-bounded elements and contains
the image of the ideal of definition, `A_U⁺` is a ring of integral elements of `A⟨T/s⟩`.

This is `TauCeti.Huber.IsRingOfIntegralElements.completion` applied to `C`, which
`isRingOfIntegralElements_integralClosure_adjoin_plus` makes a ring of integral elements of `Aₛ`.
Every ring of integral elements `A⁺` of `A` satisfies both hypotheses: `hAplus` is
`TauCeti.Huber.IsRingOfIntegralElements.le_powerBoundedSubring`, and `hIplus` follows from
`TauCeti.Huber.IsRingOfIntegralElements.mem_of_isTopologicallyNilpotent` applied to
`TauCeti.Huber.PairOfDefinition.isTopologicallyNilpotent_of_mem_idealOfDefinition`. -/
theorem isRingOfIntegralElements_completedPlusSubring (P : PairOfDefinition A) (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    IsRingOfIntegralElements (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  -- `C` is a ring of integral elements of `Aₛ` for the uniformity's topology: its openness is
  -- stated at `locTopology`, so it is moved across `locUniformSpace_toTopologicalSpace`
  have hopen := @IsRingOfIntegralElements.isOpen S _ (locTopology P T s S hden)
    (nonarchimedeanRing_locTopology P T s S hden) _
    (isRingOfIntegralElements_integralClosure_adjoin_plus P Aplus hIplus hAplus T s S hden)
  rw [← locUniformSpace_toTopologicalSpace P T s S hden] at hopen
  exact IsRingOfIntegralElements.completion ⟨hopen, inferInstance,
    integralClosure_adjoin_plus_le_powerBoundedSubring P Aplus hAplus T s S hden⟩

end Topological

end PairOfDefinition

end TauCeti.Huber
