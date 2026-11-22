/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure
public import TauCeti.RepresentationTheory.Irreducible
-- Private: `IsSimpleModule.toSpanSingleton_surjective` is used only inside proofs.
import Mathlib.RingTheory.SimpleModule.Basic
-- Private: the span theorem is used only to pass from group invariance to even-Clifford invariance.
import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift
-- Private: the generation of the exterior endomorphism algebra by creation and contraction, the
-- naturality of contraction, and the exterior algebras of finite subspaces are used only inside
-- proofs.
import TauCeti.LinearAlgebra.ExteriorAlgebra.End
import TauCeti.LinearAlgebra.ExteriorAlgebra.Subspace

/-!
# Invariant subspaces and intertwiners for the spinor and half-spin actions

The Fock model makes the exterior algebra `S = ⋀·W` of the isotropic summand of a polarization a
module over `CliffordAlgebra Q` (`TauCeti.spinAction`). **The spinor module is simple**, in every
dimension, without any nondegeneracy hypothesis, and for an arbitrary isotropic summand `W`:
`TauCeti.exists_spinAction_eq` says that a nonzero spinor is carried to every other one, and
`TauCeti.eq_bot_or_eq_top_of_map_spinAction_le` that an invariant subspace is `⊥` or everything.
Neither goes through the surjectivity of the action onto the full endomorphism algebra
(`TauCeti.spinAction_surjective`), which needs `W` finite-dimensional. A nonzero spinor lies in the
exterior algebra of a finite-dimensional subspace of `W`, where creation and contraction operators
generate every endomorphism and so carry it to `1`, and left multiplication by any spinor is a
Fock operator.

That is not yet the irreducibility the spin representation is named for, because in even dimension
`S` visibly splits, into the two half-spin summands `S⁺` and `S⁻` of `TauCeti.spinPlus` and
`TauCeti.spinMinus`. The splitting is invariant not under the whole Clifford algebra but under its
even subalgebra, and the theorem the splitting deserves is that the even subalgebra sees exactly
those two pieces and nothing finer:

`TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd :`
`  even Q ≃ₐ[K] Module.End K S⁺ × Module.End K S⁻`.

The proof of that structure theorem does not count dimensions a second time. Surjectivity onto the
*product* comes from the full structure theorem `TauCeti.spinAction_bijective` together with the
parity bookkeeping of `TauCeti/RepresentationTheory/Spin/HalfSpin/Basic.lean`. This file records its
representation-theoretic consequences: each half-spin summand has no proper nonzero invariant
subspace because its factor is a full endomorphism algebra, and the two even-Clifford actions are
**inequivalent**
(`TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`) because the
element of `even Q` acting as the identity on `S⁺` and as zero on `S⁻` kills any map that
intertwines them.

The invariant-subspace conclusions for the even Clifford algebra are stated in lattice form, as
"an invariant subspace is `⊥` or everything", rather than as `IsSimpleModule`: `S⁺` and `S⁻`
carry no `Module (even Q)` instance, and manufacturing one would mean a type synonym for a
statement that reads no better through it. Over a separably closed field, the Spin group linearly
spans the even Clifford algebra when the quadratic form is nondegenerate and the characteristic
is not two. The same dichotomies therefore prove that the even half-spin subrepresentation is
irreducible, that the odd half is irreducible when `P.W ≠ ⊥`, and that the two are inequivalent.

The actions themselves — `TauCeti.spinPlusAction`, `TauCeti.spinMinusAction` and their pair
`TauCeti.evenSpinActionProd` — are defined in
`TauCeti/RepresentationTheory/Spin/HalfSpin/Basic.lean`, beside the bundling of the same two
summands as subrepresentations of `spinRep` that the same invariance gives; this file only proves
theorems about them.

The hypothesis `P.line = ⊥` is the even-dimensional case, and it is exactly what makes the parity
splitting a splitting of modules at all;
`TauCeti.SpinPolarizationData.even_finrank_of_line_eq_bot` turns it into the evenness the structure
theorem is stated with, so no separate parity hypothesis is carried. The lattice dichotomy for
`S⁻` needs no further hypothesis, since it also holds vacuously when `S⁻ = 0`. To conclude that
`S⁻` is simple, combine it with `TauCeti.nontrivial_spinMinus`, whose hypothesis `W ≠ ⊥` rules out
only the zero-dimensional quadratic space: there `S = K` is entirely even and `S⁻` is zero. `S⁺`
always contains the scalars, so it needs no such hypothesis, and neither does the inequivalence.

The odd-dimensional case is the opposite of all this, and the last section records it. There, over
a field with `2 ≠ 0`, the even subalgebra is a *single* block rather than a product, so the Fock
action already carries it onto all of `Module.End K S` (`TauCeti.evenSpinAction_surjective`, which
assumes `2 ≠ 0`), and the whole spinor module —
not a half of it — is the irreducible object: `TauCeti.spinRep_isIrreducible_of_odd`.
As soon as `P.W ≠ ⊥`, exterior parity still splits `S` as a vector space but no longer as a
representation, which `TauCeti.not_forall_map_spinRep_spinPlus_le` and
`TauCeti.not_forall_map_spinRep_spinMinus_le` record: neither half is `⊥` or everything, so
irreducibility alone forbids either from being invariant. The `P.line = ⊥` carried by every
statement of the even-dimensional half is precisely what fails. Dimension one is the exception:
there `W = ⊥` and `S = K` is entirely even, so `S⁺ = S` and `S⁻ = 0` are both invariant, for want
of anything to split.

The two parities are separated by exactly one hypothesis, the surjectivity of
`TauCeti.evenSpinAction`, and `TauCeti.isIrreducible_spinRep_comp_of_span_of_surjective` is stated
against it rather than against a dimension, so the dichotomy is visible in the statement and the
criterion itself holds in every characteristic. It holds in odd dimension over a field with
`2 ≠ 0`, and fails in even dimension except for the zero-dimensional quadratic space, where
`S = K` is one-dimensional and there is no room for it to fail.

What is not proved here is the odd-dimensional splitting of `CliffordAlgebra Q` into its two
central summands, for which the results here are the even-dimensional half; it is
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one`.

## Main results

* `TauCeti.exists_spinAction_eq` and `TauCeti.eq_bot_or_eq_top_of_map_spinAction_le`: **the spinor
  module is a simple Clifford module**, with no finiteness assumption on `W`.
* `TauCeti.mem_even_of_map_spinPlus_le_of_map_spinMinus_le`: a Clifford element whose action
  preserves both half-spin summands is even.
* `TauCeti.eq_bot_or_eq_top_of_map_spinPlusAction_le` and
  `TauCeti.eq_bot_or_eq_top_of_map_spinMinusAction_le`: the two half-spin summands have no proper
  nonzero invariant subspace. Together with `TauCeti.nontrivial_spinPlus` and
  `TauCeti.nontrivial_spinMinus`, respectively, these say that the summands are simple.
* `TauCeti.eq_zero_of_intertwines_spinPlusAction_spinMinusAction` and
  `TauCeti.eq_zero_of_intertwines_spinMinusAction_spinPlusAction`: there is no nonzero map either
  way intertwining the two actions, and hence
  `TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`: **the half-spin summands
  are inequivalent.**
* `TauCeti.isIrreducible_spinPlusSubrep_comp_of_span` and
  `TauCeti.isIrreducible_spinMinusSubrep_comp_of_span`: **the two half-spin group representations
  are irreducible** on restriction along any monoid homomorphism `φ : H →* spinGroup Q` whose image
  spans the even Clifford algebra, such as the Spin group itself (`φ = MonoidHom.id`) or the
  inclusion of a real Spin group in its complexification. Both require `P.line = ⊥`, and the odd
  half also `P.W ≠ ⊥`. The `_of_isSquare` and suffix-free versions for the Spin group itself give
  progressively stronger sufficient hypotheses.
* `TauCeti.isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_comp_of_span`: **the two half-spin group
  representations are inequivalent** under the same spanning hypothesis, with analogous
  corollaries.
* `TauCeti.isIrreducible_spinRep_comp_of_span_of_surjective`: the spin representation is
  irreducible on restriction along such a `φ`, once the even subalgebra exhausts the endomorphisms
  of the spinor module.
* `TauCeti.isIrreducible_spinRep_of_isSquare` and `TauCeti.spinRep_isIrreducible_of_odd`: **the
  spin representation is irreducible in odd dimension**, the type `Bₗ` case, under the square
  normalization and over a separably closed field respectively.
* `TauCeti.not_forall_map_spinRep_spinPlus_le_of_isIrreducible` and
  `TauCeti.not_forall_map_spinRep_spinMinus_le_of_isIrreducible`: **an irreducible spinor module
  does not split along exterior parity**, provided `P.W ≠ ⊥`, which rules out only dimension one;
  `TauCeti.not_forall_map_spinRep_spinPlus_le` and
  `TauCeti.not_forall_map_spinRep_spinMinus_le` are their odd-dimensional specializations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9 and
  Proposition 20.15: the Clifford algebra of an even-dimensional space is the endomorphism algebra
  of `⋀·W`, its even subalgebra is the product of the endomorphism algebras of the two halves, and
  the two half-spin modules are irreducible and inequivalent; §20.2 for the odd-dimensional spin
  representation, which does not split.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter I, §5: the complex spinor representations and their irreducibility in both parities.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

private theorem eq_bot_or_eq_top_of_surjective_action {K : Type u} [Field K]
    {A M : Type*} [AddCommGroup M] [Module K M] (F : A → Module.End K M)
    (hF : Function.Surjective F) (N : Submodule K M)
    (hN : ∀ a : A, N.map (F a) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨s, hs, hs0⟩ := N.exists_mem_ne_zero_of_ne_bot hbot
  let _ : Nontrivial M := ⟨s, 0, hs0⟩
  obtain ⟨g, hg⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End K M) hs0 t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hg
  obtain ⟨a, rfl⟩ := hF g
  exact hg ▸ hN a ⟨s, hs, rfl⟩

/-- The spanning hypothesis for the Spin group itself, in the form taken by the restriction along
the identity homomorphism. -/
private theorem span_range_id_of_span {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule) :
    Submodule.span K (Set.range fun g : spinGroup Q ↦ (MonoidHom.id _ g : CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule :=
  (congrArg (Submodule.span K) Subtype.range_coe).trans hspan

/-- An even-Clifford action exhausting the endomorphisms stays irreducible on restriction to the
Spin group along `spinGroupToEven` and then along any `φ` whose image spans the even algebra. -/
private theorem isIrreducible_toMonoidHom_comp_spinGroupToEven_comp {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {H : Type*} [Monoid H] {φ : H →* spinGroup Q}
    (hspan : Submodule.span K (Set.range fun h : H ↦ (φ h : CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    {M : Type*} [AddCommGroup M] [Module K M] [Nontrivial M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M)
    (hF : Function.Surjective F) :
    Representation.IsIrreducible ((F.toMonoidHom.comp (spinGroupToEven Q)).comp φ) := by
  rw [MonoidHom.comp_assoc]
  exact F.isIrreducible_toMonoidHom_comp_of_span_eq_top hF ((spinGroupToEven Q).comp φ)
    ((span_range_spinGroupToEven_comp_eq_top_iff φ).2 hspan)

/-! ### The spinor module is a simple Clifford module

Nothing here needs an even dimension, a nondegenerate form, an invertible `2`, or a
finite-dimensional isotropic summand. A nonzero spinor lies in the exterior algebra of a
finite-dimensional subspace `W₀ ≤ W`, where creation and contraction operators generate every
endomorphism and so carry it to `1`; these operators extend from `W₀` to `W`, and left
multiplication by any spinor is again a Fock operator (`TauCeti.exists_spinAction_eq_mul`). Only the
stronger statement that the Fock action is onto `Module.End K S`, `TauCeti.spinAction_surjective`,
needs `W` to be finite-dimensional. -/

section Simple

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-- A nonzero spinor is carried to `1` by some Clifford element, with no finiteness assumption on
`W`: it lies in the exterior algebra of a finite-dimensional `W₀`, where creation and contraction
operators generate every endomorphism, and these operators extend from `W₀` to `W`. -/
private theorem exists_spinAction_eq_one (s : ExteriorAlgebra K P.W) (hs : s ≠ 0) :
    ∃ x : CliffordAlgebra Q, spinAction Q P x s = 1 := by
  obtain ⟨W₀, hW₀, hsW₀⟩ := ExteriorAlgebra.exists_finite_submodule_mem_range_map_subtype s
  obtain ⟨s₀, rfl⟩ := (AlgHom.mem_range _).mp hsW₀
  have hs₀ : s₀ ≠ 0 := by rintro rfl; exact hs (map_zero _)
  obtain ⟨g, hg⟩ := IsSimpleModule.toSpanSingleton_surjective
    (Module.End K (ExteriorAlgebra K W₀)) hs₀ 1
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hg
  have key : ∀ g ∈ Algebra.adjoin K
      (Set.range (fun x : W₀ ↦
        (LinearMap.mulLeft K (ExteriorAlgebra.ι K x) : Module.End K (ExteriorAlgebra K W₀))) ∪
       Set.range (fun d : Module.Dual K W₀ ↦
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W₀)) d :
          Module.End K (ExteriorAlgebra K W₀)))),
      ∃ x : CliffordAlgebra Q, ∀ t, spinAction Q P x (ExteriorAlgebra.map W₀.subtype t) =
      ExteriorAlgebra.map W₀.subtype (g t) := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem g hg =>
      rcases hg with ⟨y, rfl⟩ | ⟨d, rfl⟩
      · refine ⟨CliffordAlgebra.ι Q ((W₀.subtype y : P.W) : V), fun t => ?_⟩
        rw [spinAction_ι_wedge]
        simp [map_mul]
      · obtain ⟨d', hd'⟩ := LinearMap.exists_extend (p := W₀) d
        obtain ⟨y, hy⟩ := P.pairingEquiv.surjective d'
        refine ⟨CliffordAlgebra.ι Q (y : V), fun t => ?_⟩
        rw [spinAction_ι_contract, hy, ExteriorAlgebra.contractLeft_map]
        simp [hd']
    | algebraMap r => exact ⟨algebraMap K _ r, fun t => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, fun t => by simp [hx, hy]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x * y, fun t => by simp [hx, hy]⟩
  obtain ⟨x, hx⟩ := key g (by rw [ExteriorAlgebra.creation_contraction_adjoin_eq_top]; trivial)
  exact ⟨x, by rw [hx, hg, map_one]⟩

/-- **A nonzero spinor generates the spinor module**: some Clifford element carries it to any
prescribed spinor. No finiteness of `W` is needed: some Clifford element carries the nonzero spinor
to `1`, and left multiplication by the target is the Fock action of another. -/
theorem exists_spinAction_eq {s : ExteriorAlgebra K P.W} (hs : s ≠ 0)
    (t : ExteriorAlgebra K P.W) : ∃ x : CliffordAlgebra Q, spinAction Q P x s = t := by
  obtain ⟨x, hx⟩ := exists_spinAction_eq_one P s hs
  obtain ⟨y, hy⟩ := exists_spinAction_eq_mul P t
  exact ⟨y * x, by rw [map_mul, mul_apply_eq_comp, hx, hy, mul_one]⟩

/-- **The invariant-subspace dichotomy for the spinor module**: a submodule of `S = ⋀·W`
invariant under every Clifford element is `⊥` or the whole of `S`. The spinor module is nonzero,
so this is its simplicity statement for the Clifford action. No finiteness of `W` is needed. -/
theorem eq_bot_or_eq_top_of_map_spinAction_le (N : Submodule K (ExteriorAlgebra K P.W))
    (hN : ∀ x : CliffordAlgebra Q, N.map (spinAction Q P x) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  refine or_iff_not_imp_left.mpr fun h0 => Submodule.eq_top_iff'.mpr fun t => ?_
  obtain ⟨s, hsN, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨x, rfl⟩ := exists_spinAction_eq P hs t
  exact hN x (Submodule.mem_map_of_mem hsN)

end Simple

/-! ### Consequences of the even structure theorem -/

section Even

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [FiniteDimensional K V]


/-! ### Invariant-subspace dichotomies and inequivalence of the two half-spin actions -/

/-- **The invariant-subspace dichotomy for the even half-spin summand**: every subspace of `S⁺`
invariant under the even Clifford subalgebra is `⊥` or all of `S⁺`. Combine this with
`TauCeti.nontrivial_spinPlus` to obtain simplicity. -/
theorem eq_bot_or_eq_top_of_map_spinPlusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinPlus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinPlusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  eq_bot_or_eq_top_of_surjective_action (spinPlusAction Q P hline)
    (spinPlusAction_surjective P hline) N hN

/-- **The invariant-subspace dichotomy for the odd half-spin summand**: every subspace of `S⁻`
invariant under the even Clifford subalgebra is `⊥` or all of `S⁻`. This remains true when `S⁻` is
zero; combine it with `TauCeti.nontrivial_spinMinus` to obtain simplicity when `P.W ≠ ⊥`. -/
theorem eq_bot_or_eq_top_of_map_spinMinusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinMinus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinMinusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  eq_bot_or_eq_top_of_surjective_action (spinMinusAction Q P hline)
    (spinMinusAction_surjective P hline) N hN

/-- **A map intertwining the two half-spin actions is zero.** The even subalgebra contains an
element acting as the identity on `S⁺` and as zero on `S⁻`, and an intertwiner turns the first
statement into the second. -/
theorem eq_zero_of_intertwines_spinPlusAction_spinMinusAction (hline : P.line = ⊥)
    (φ : spinPlus Q P →ₗ[K] spinMinus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
      φ (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (1, 0)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **A map intertwining the odd and even half-spin actions is zero.** -/
theorem eq_zero_of_intertwines_spinMinusAction_spinPlusAction (hline : P.line = ⊥)
    (φ : spinMinus Q P →ₗ[K] spinPlus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinMinus Q P),
      φ (spinMinusAction Q P hline x s) = spinPlusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (0, 1)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **The two half-spin summands are inequivalent.** There is no linear equivalence intertwining
the two actions of the even Clifford subalgebra. -/
theorem not_exists_equiv_intertwines_spinPlusAction_spinMinusAction (hline : P.line = ⊥) :
    ¬ ∃ e : spinPlus Q P ≃ₗ[K] spinMinus Q P,
      ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
        e (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (e s) := by
  rintro ⟨e, he⟩
  have hzero : (e : spinPlus Q P →ₗ[K] spinMinus Q P) = 0 :=
    eq_zero_of_intertwines_spinPlusAction_spinMinusAction P hline _ he
  have := nontrivial_spinPlus P
  obtain ⟨s, hs⟩ := exists_ne (0 : spinPlus Q P)
  have hes : e s = 0 := by simpa using LinearMap.congr_fun hzero s
  exact hs (e.injective (hes.trans (map_zero e).symm))

end Even

/-! ### Irreducibility of the half-spin group representations -/

section SpinGroup

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [FiniteDimensional K V] (P : SpinPolarizationData Q)
  {H : Type*} [Monoid H]

/-- **The even half-spin representation stays irreducible on restriction along a monoid
homomorphism into the Spin group whose image spans the even Clifford algebra.** For polarization
data without a line remainder (`P.line = ⊥`) and `φ : H →* spinGroup Q`, the restriction of the
even half-spin representation along `φ` is irreducible as soon as the elements `φ h` linearly span
the even Clifford algebra; for instance, a real Spin group acting on complex spinors. The Spin
group itself is the case `φ = MonoidHom.id`. -/
theorem isIrreducible_spinPlusSubrep_comp_of_span (φ : H →* spinGroup Q)
    (hspan : Submodule.span K (Set.range fun h : H ↦ (φ h : CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hline : P.line = ⊥) :
    Representation.IsIrreducible ((spinPlusSubrep P hline).toRepresentation.comp φ) :=
  let _ : Nontrivial (spinPlus Q P) := nontrivial_spinPlus P
  ((spinPlusSubrepEquiv P hline).res φ).isIrreducible <|
    isIrreducible_toMonoidHom_comp_spinGroupToEven_comp hspan (spinPlusAction Q P hline)
      (spinPlusAction_surjective P hline)

/-- **The odd half-spin representation stays irreducible on restriction along a monoid
homomorphism into the Spin group whose image spans the even Clifford algebra**, for polarization
data without a line remainder (`P.line = ⊥`) whose odd summand is nonzero (`P.W ≠ ⊥`). -/
theorem isIrreducible_spinMinusSubrep_comp_of_span (φ : H →* spinGroup Q)
    (hspan : Submodule.span K (Set.range fun h : H ↦ (φ h : CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hline : P.line = ⊥) (hW : P.W ≠ ⊥) :
    Representation.IsIrreducible ((spinMinusSubrep P hline).toRepresentation.comp φ) :=
  let _ : Nontrivial (spinMinus Q P) := nontrivial_spinMinus P hW
  ((spinMinusSubrepEquiv P hline).res φ).isIrreducible <|
    isIrreducible_toMonoidHom_comp_spinGroupToEven_comp hspan (spinMinusAction Q P hline)
      (spinMinusAction_surjective P hline)

/-- **The two half-spin representations stay inequivalent on restriction along a monoid
homomorphism into the Spin group whose image spans the even Clifford algebra**, for polarization
data without a line remainder (`P.line = ⊥`). An equivalence of the restrictions along `φ` would
intertwine the whole even Clifford algebra, which separates the two summands. -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_comp_of_span (φ : H →* spinGroup Q)
    (hspan : Submodule.span K (Set.range fun h : H ↦ (φ h : CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hline : P.line = ⊥) :
    IsEmpty (Representation.Equiv ((spinPlusSubrep P hline).toRepresentation.comp φ)
      ((spinMinusSubrep P hline).toRepresentation.comp φ)) := by
  refine ⟨fun e => ?_⟩
  let f := (((spinPlusSubrepEquiv P hline).res φ).trans e).trans
    ((spinMinusSubrepEquiv P hline).res φ).symm
  have hf' : Representation.IsIntertwiningMap
      ((spinPlusAction Q P hline).toMonoidHom.comp ((spinGroupToEven Q).comp φ))
      ((spinMinusAction Q P hline).toMonoidHom.comp ((spinGroupToEven Q).comp φ))
      f.toLinearMap := by
    rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc]
    exact ⟨Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap⟩
  -- `f` intertwines the restrictions along `(spinGroupToEven Q).comp φ`, hence the whole even
  -- Clifford algebra.
  have hf := ((spinPlusAction Q P hline).isIntertwiningMap_toMonoidHom_comp_iff_of_span_eq_top
    (spinMinusAction Q P hline) ((spinGroupToEven Q).comp φ)
    ((span_range_spinGroupToEven_comp_eq_top_iff φ).2 hspan) f.toLinearMap).1 hf'
  exact not_exists_equiv_intertwines_spinPlusAction_spinMinusAction P hline ⟨f.toLinearEquiv, hf⟩

variable [Invertible (2 : K)]

/-- **The even half-spin representation of the Spin group is irreducible** when anisotropic pairs
admit the square normalization needed to span the even Clifford algebra. -/
theorem isIrreducible_spinPlusSubrep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hline : P.line = ⊥) :
    (spinPlusSubrep P hline).toRepresentation.IsIrreducible :=
  by simpa only [MonoidHom.comp_id] using
    isIrreducible_spinPlusSubrep_comp_of_span P (MonoidHom.id _) (span_range_id_of_span
      (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
        (P.nondegenerate_of_line_eq_bot hline) hsq)) hline

/-- **The odd half-spin representation of the Spin group is irreducible** when the odd summand is
nonzero and anisotropic pairs admit the required square normalization. -/
theorem isIrreducible_spinMinusSubrep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hline : P.line = ⊥)
    (hW : P.W ≠ ⊥) : (spinMinusSubrep P hline).toRepresentation.IsIrreducible :=
  by simpa only [MonoidHom.comp_id] using
    isIrreducible_spinMinusSubrep_comp_of_span P (MonoidHom.id _) (span_range_id_of_span
      (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
        (P.nondegenerate_of_line_eq_bot hline) hsq)) hline hW

/-- **The two half-spin representations of the Spin group are inequivalent** when anisotropic
pairs admit the square normalization needed to span the even Clifford algebra. -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hline : P.line = ⊥) :
    IsEmpty ((spinPlusSubrep P hline).toRepresentation.Equiv
      (spinMinusSubrep P hline).toRepresentation) :=
  by simpa only [MonoidHom.comp_id] using
    isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_comp_of_span P (MonoidHom.id _)
      (span_range_id_of_span (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
        (P.nondegenerate_of_line_eq_bot hline) hsq)) hline

/-- **The even half-spin representation of the Spin group is irreducible** over a separably
closed field for polarization data without a line remainder. -/
theorem isIrreducible_spinPlusSubrep [IsSepClosed K] (hline : P.line = ⊥) :
    (spinPlusSubrep P hline).toRepresentation.IsIrreducible :=
  isIrreducible_spinPlusSubrep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.isSquare ((Q v)⁻¹ * (Q w)⁻¹)) hline

/-- **The odd half-spin representation of the Spin group is irreducible** over a separably closed
field when the odd summand is nonzero. -/
theorem isIrreducible_spinMinusSubrep [IsSepClosed K] (hline : P.line = ⊥)
    (hW : P.W ≠ ⊥) : (spinMinusSubrep P hline).toRepresentation.IsIrreducible :=
  isIrreducible_spinMinusSubrep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.isSquare ((Q v)⁻¹ * (Q w)⁻¹)) hline hW

/-- **The two half-spin representations of the Spin group are inequivalent** over a separably
closed field. -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep [IsSepClosed K]
    (hline : P.line = ⊥) :
    IsEmpty ((spinPlusSubrep P hline).toRepresentation.Equiv
      (spinMinusSubrep P hline).toRepresentation) :=
  isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.isSquare ((Q v)⁻¹ * (Q w)⁻¹)) hline

end SpinGroup

/-! ### Irreducibility of the spin representation in odd dimension -/

section Odd

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q)

/-- **The whole spin representation stays irreducible on restriction along a monoid homomorphism
into the Spin group whose image spans the even Clifford algebra**, as soon as that subalgebra
exhausts the endomorphisms of the spinor module. The Spin group itself is the case
`φ = MonoidHom.id`.

The second hypothesis is exactly what separates the two parities of `finrank K V`. In *positive*
even dimension it fails — the even subalgebra is the *product* of the two half-spin endomorphism
algebras, by `TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`, and `S` visibly splits — and
in odd dimension over a field with `2 ≠ 0` it holds, by `TauCeti.evenSpinAction_surjective`. The
criterion itself needs no hypothesis on the characteristic. Dimension zero is the exception
on the even side: there `W = ⊥`, the odd block is zero, `S = K` is one-dimensional and the even
subalgebra is already all of `Module.End K S`. -/
theorem isIrreducible_spinRep_comp_of_span_of_surjective {H : Type*} [Monoid H]
    (φ : H →* spinGroup Q)
    (hspan : Submodule.span K (Set.range fun h : H ↦ (φ h : CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hsurj : Function.Surjective (evenSpinAction Q P)) :
    Representation.IsIrreducible ((spinRep Q P).comp φ) := by
  rw [spinRep_eq_evenSpinAction_comp]
  exact isIrreducible_toMonoidHom_comp_spinGroupToEven_comp hspan (evenSpinAction Q P) hsurj

/-- A subspace of the spinor module that is neither zero nor everything is not invariant under the
Spin group once the spin representation is irreducible, since invariance would make it a
subrepresentation. -/
private theorem not_forall_map_spinRep_le (hirr : (spinRep Q P).IsIrreducible)
    {N : Submodule K (ExteriorAlgebra K P.W)} (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    ¬ ∀ g : spinGroup Q, N.map (spinRep Q P g) ≤ N := by
  intro hinv
  have _ : (spinRep Q P).IsIrreducible := hirr
  let σ : Subrepresentation (spinRep Q P) :=
    { toSubmodule := N
      apply_mem_toSubmodule := fun g _ hv => hinv g ⟨_, hv, rfl⟩ }
  rcases IsSimpleOrder.eq_bot_or_eq_top σ with h | h
  · exact hbot (congrArg Subrepresentation.toSubmodule h)
  · exact htop (congrArg Subrepresentation.toSubmodule h)

/-- **An irreducible spinor module does not split along exterior parity.** The even part `S⁺` is
not invariant under the Spin group, so it is not a subrepresentation of `spinRep`.

Nothing about the anisotropic remainder is computed: the proof is by irreducibility, `S⁺` being
neither `⊥` (it contains the scalars) nor everything (it misses the nonzero `S⁻`). The hypothesis
`P.W ≠ ⊥` is what excludes `finrank K V = 1`, where `S = K` is entirely even, `S⁺ = S` is trivially
invariant and there is nothing to split. In even dimension the same subspace *is* invariant, by
`TauCeti.spinPlus_invariant`, and `spinRep` is correspondingly reducible. -/
theorem not_forall_map_spinRep_spinPlus_le_of_isIrreducible (hirr : (spinRep Q P).IsIrreducible)
    (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinPlus Q P).map (spinRep Q P g) ≤ spinPlus Q P :=
  not_forall_map_spinRep_le P hirr
    (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinPlus P))
    ((isCompl_spinPlus_spinMinus P).symm.disjoint.ne_top_of_ne_bot
      (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinMinus P hW)))

/-- **The odd half of an irreducible spinor module is not invariant either.** The companion of
`TauCeti.not_forall_map_spinRep_spinPlus_le_of_isIrreducible` for the other parity: `S⁻` is nonzero
when `P.W ≠ ⊥` and is not everything, `S⁺` containing the scalars, so irreducibility forbids it
from being a subrepresentation of `spinRep`. -/
theorem not_forall_map_spinRep_spinMinus_le_of_isIrreducible (hirr : (spinRep Q P).IsIrreducible)
    (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinMinus Q P).map (spinRep Q P g) ≤ spinMinus Q P :=
  not_forall_map_spinRep_le P hirr
    (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinMinus P hW))
    ((isCompl_spinPlus_spinMinus P).disjoint.ne_top_of_ne_bot
      (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinPlus P)))

variable [NeZero (2 : K)]

/-- **The spin representation is irreducible in odd dimension** when anisotropic pairs admit the
square normalization needed to span the even Clifford algebra.

This is the generality of the even-dimensional `TauCeti.isIrreducible_spinPlusSubrep_of_isSquare`:
no separably closed field, and no nondegeneracy hypothesis, the polarization data already carrying
it by `TauCeti.SpinPolarizationData.nondegenerate`. The square normalization is only what lifts a
product of two reflections to the Spin group, and it is the sole remaining hypothesis of this
argument. -/
theorem isIrreducible_spinRep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hodd : Odd (finrank K V)) : (spinRep Q P).IsIrreducible := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos hodd.pos
  have _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  simpa only [MonoidHom.comp_id] using
    isIrreducible_spinRep_comp_of_span_of_surjective P (MonoidHom.id _)
      (span_range_id_of_span (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
        (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)) hsq))
      (evenSpinAction_surjective P hodd)

variable [IsSepClosed K]

/-- **The spin representation is irreducible in odd dimension.** For a polarized quadratic space of
dimension `2 * l + 1` over a separably closed field of characteristic not two, the Spin group acts
irreducibly on the whole spinor module `S = ⋀·W`.

Nondegeneracy of `Q` is not assumed: the polarization data already carries it, by
`TauCeti.SpinPolarizationData.nondegenerate`. Except in dimension one, where `W = ⊥` and `S = K` is
entirely even, the exterior parity splitting `S = S⁺ ⊕ S⁻` is *not* a splitting of representations
here: see `TauCeti.not_forall_map_spinRep_spinPlus_le`. The even-dimensional counterpart is the
pair `TauCeti.isIrreducible_spinPlusSubrep`, `TauCeti.isIrreducible_spinMinusSubrep`, where `S`
itself is reducible unless it is the zero-dimensional quadratic space. -/
theorem spinRep_isIrreducible_of_odd (l : ℕ) (hV : finrank K V = 2 * l + 1) :
    (spinRep Q P).IsIrreducible :=
  isIrreducible_spinRep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.isSquare ((Q v)⁻¹ * (Q w)⁻¹)) ⟨l, hV⟩

/-- **In odd dimension the spinor module does not split along exterior parity.** The
separably closed specialization of
`TauCeti.not_forall_map_spinRep_spinPlus_le_of_isIrreducible`, where
`TauCeti.spinRep_isIrreducible_of_odd` supplies the irreducibility. Unlike in positive even
dimension, `S⁺` is not a subrepresentation of `spinRep`; the hypothesis `P.line = ⊥` carried by
`TauCeti.spinPlus_invariant` is what an odd-dimensional polarization cannot satisfy. -/
theorem not_forall_map_spinRep_spinPlus_le (l : ℕ) (hV : finrank K V = 2 * l + 1) (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinPlus Q P).map (spinRep Q P g) ≤ spinPlus Q P :=
  not_forall_map_spinRep_spinPlus_le_of_isIrreducible P (spinRep_isIrreducible_of_odd P l hV) hW

/-- **In odd dimension the odd half of the spinor module is not invariant either.** The companion
of `TauCeti.not_forall_map_spinRep_spinPlus_le` for the other parity, the separably closed
specialization of `TauCeti.not_forall_map_spinRep_spinMinus_le_of_isIrreducible`. -/
theorem not_forall_map_spinRep_spinMinus_le (l : ℕ) (hV : finrank K V = 2 * l + 1) (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinMinus Q P).map (spinRep Q P g) ≤ spinMinus Q P :=
  not_forall_map_spinRep_spinMinus_le_of_isIrreducible P (spinRep_isIrreducible_of_odd P l hV) hW

end Odd

end TauCeti
