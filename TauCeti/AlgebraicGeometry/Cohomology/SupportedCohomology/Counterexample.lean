/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Non-Noetherian counterexample for geometric vs. algebraic local cohomology

Without finite generation of the ideal `I`, geometric supported cohomology `H⁰_{V(I)}(Spec A, M~)`
can differ from algebraic local cohomology `H⁰_I(M)`. For any nontrivial commutative ring `k`, let
`A = k[X₀, X₁, …] ⧸ (X₀², X₁³, …, X_j^{j+2}, …)`
(`TauCeti.AlgebraicGeometry.NonNoetherianExampleRing`) and `I = (x₀, x₁, …)`
(`TauCeti.AlgebraicGeometry.nonNoetherianVarIdeal`). Every generator `x_j` is nilpotent, so
`V(I) = Spec A` and the unit global section `1` gives a nontrivial element of
`H⁰_{V(I)}(Spec A, 𝒪_{Spec A})`. On the other hand, no nonzero element of `A` is annihilated by a
uniform power `I ^ n`, so `I.primaryComponent A = ⊥` and `H⁰_I(A) = 0`.

## Main definitions

* `TauCeti.AlgebraicGeometry.nonNoetherianRelIdeal`: the monomial relation ideal
  `(X₀², X₁³, …, X_j^{j+2}, …)` in `k[X₀, X₁, …]`.
* `TauCeti.AlgebraicGeometry.NonNoetherianExampleRing` and
  `TauCeti.AlgebraicGeometry.nonNoetherianExampleRingCat`: the quotient ring `A`.
* `TauCeti.AlgebraicGeometry.nonNoetherianVarIdeal`: the variable ideal `I = (x₀, x₁, …)` in `A`.

## Main results

* `TauCeti.AlgebraicGeometry.zeroLocusClosed_nonNoetherianVarIdeal`: `V(I) = Spec A`.
* `TauCeti.AlgebraicGeometry.nontrivial_supportedModuleH_zero_nonNoetherianExampleRing`:
  `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})` is nontrivial.
* `TauCeti.AlgebraicGeometry.primaryComponent_nonNoetherianVarIdeal_eq_bot` and
  `TauCeti.AlgebraicGeometry.isZero_localCohomology_zero_nonNoetherianExampleRing`:
  `I.primaryComponent A = ⊥` and `H⁰_I(A) = 0`.
* `TauCeti.AlgebraicGeometry.not_fg_nonNoetherianVarIdeal` and
  `TauCeti.AlgebraicGeometry.not_isNoetherianRing_nonNoetherianExampleRing`: `I` is not finitely
  generated and `A` is not Noetherian.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

section NonNoetherianCounterexample

variable (k : Type u) [CommRing k] [Nontrivial k]

/-- The monomial relation ideal `(X₀², X₁³, …, X_j^{j+2}, …)` in `k[X₀, X₁, …]`. -/
def nonNoetherianRelIdeal : Ideal (MvPolynomial ℕ k) :=
  Ideal.span { MvPolynomial.X j ^ (j + 2) | j : ℕ }

/-- The non-Noetherian ring `A = k[X₀, X₁, …] ⧸ (X₀², X₁³, …)` on which geometric and algebraic
degree-zero local cohomology disagree at the variable ideal `(x₀, x₁, …)`. -/
abbrev NonNoetherianExampleRing : Type u :=
  MvPolynomial ℕ k ⧸ nonNoetherianRelIdeal k

/-- `NonNoetherianExampleRing k` bundled as an object of `CommRingCat.{u}`. -/
abbrev nonNoetherianExampleRingCat : CommRingCat.{u} :=
  CommRingCat.of (NonNoetherianExampleRing k)

/-- The ideal `I = (x₀, x₁, …)` in `nonNoetherianExampleRingCat k`. -/
def nonNoetherianVarIdeal : Ideal (nonNoetherianExampleRingCat k) :=
  Ideal.map (Ideal.Quotient.mk (nonNoetherianRelIdeal k))
    (Ideal.span (Set.range MvPolynomial.X))

omit [Nontrivial k] in
/-- A polynomial lies in `(X_j^{j+2} | j : ℕ)` if and only if all of its coefficients at
multi-indices `d` satisfying `∀ j, d j < j + 2` vanish. -/
private lemma mem_nonNoetherianRelIdeal_iff (p : MvPolynomial ℕ k) :
    p ∈ nonNoetherianRelIdeal k ↔ ∀ d : ℕ →₀ ℕ, (∀ j, d j < j + 2) → p.coeff d = 0 := by
  have hspan : nonNoetherianRelIdeal k =
      Ideal.span ((fun s ↦ MvPolynomial.monomial s (1 : k)) ''
        Set.range fun j : ℕ ↦ Finsupp.single j (j + 2)) := by
    unfold nonNoetherianRelIdeal
    congr 1
    ext x
    simp [MvPolynomial.X_pow_eq_monomial]
  rw [hspan, MvPolynomial.mem_ideal_span_monomial_image]
  simp only [MvPolynomial.mem_support_iff, Set.mem_range, exists_exists_eq_and,
    Finsupp.single_le_iff]
  constructor
  · intro hp d hd
    by_contra hne
    obtain ⟨j, hj⟩ := hp d hne
    exact (hd j).not_ge hj
  · intro hp d hne
    by_contra! hlt
    exact hne (hp d hlt)

instance instNontrivialNonNoetherianExampleRing : Nontrivial (NonNoetherianExampleRing k) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun htop ↦ ?_
  have h1 : (1 : MvPolynomial ℕ k) ∈ nonNoetherianRelIdeal k := htop ▸ Submodule.mem_top
  exact one_ne_zero (α := k) <| by
    simpa using (mem_nonNoetherianRelIdeal_iff k 1).mp h1 0 (fun j ↦ Nat.zero_lt_succ (j + 1))

omit [Nontrivial k] in
private lemma mk_X_pow_eq_zero (j : ℕ) :
    Ideal.Quotient.mk (nonNoetherianRelIdeal k) (MvPolynomial.X j) ^ (j + 2) = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

omit [Nontrivial k] in
/-- Every generator of `nonNoetherianVarIdeal k` is nilpotent, so `V(I) = Spec A`. -/
theorem zeroLocusClosed_nonNoetherianVarIdeal :
    Spec.zeroLocusClosed (R := nonNoetherianExampleRingCat k)
      (nonNoetherianVarIdeal k : Set (nonNoetherianExampleRingCat k)) = ⊤ := by
  rw [nonNoetherianVarIdeal, Ideal.map_span, Spec.zeroLocusClosed_span,
    ← Closeds.coe_eq_univ, Spec.coe_zeroLocusClosed]
  refine (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr ?_
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact mem_nilradical.mpr ⟨j + 2, mk_X_pow_eq_zero k j⟩

/-- On `A = nonNoetherianExampleRingCat k`, geometric `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})` is nontrivial
because the unit global section `1` is killed locally on `Spec A \ V(I) = ∅`. -/
theorem nontrivial_supportedModuleH_zero_nonNoetherianExampleRing :
    Nontrivial ((modulesSpecToSheaf.obj
      (tilde (.of (nonNoetherianExampleRingCat k)
        (nonNoetherianExampleRingCat k)))).supportedModuleH
      (Spec.zeroLocusClosed (R := nonNoetherianExampleRingCat k)
        (nonNoetherianVarIdeal k : Set (nonNoetherianExampleRingCat k))) ⊤ 0) := by
  let A := nonNoetherianExampleRingCat k
  let F := modulesSpecToSheaf.obj (tilde (.of A A))
  let Z : Closeds (Spec A) := Spec.zeroLocusClosed (nonNoetherianVarIdeal k : Set A)
  have h1 : tilde.toOpen (.of A A) ⊤ (1 : A) ∈ F.supportedSubmodule Z ⊤ := by
    have hZ : Z = Spec.zeroLocusClosed (R := A)
        ((Ideal.Quotient.mk (nonNoetherianRelIdeal k)) '' Set.range MvPolynomial.X) := by
      dsimp only [Z]
      rw [nonNoetherianVarIdeal, Ideal.map_span, Spec.zeroLocusClosed_span]
    rw [hZ, tilde_toOpen_top_mem_supportedSubmodule_iff]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨j + 2, ?_⟩
    rw [smul_eq_mul, mul_one]
    exact mk_X_pow_eq_zero k j
  have hne : (⟨tilde.toOpen (.of A A) ⊤ (1 : A), h1⟩ : F.supportedSubmodule Z ⊤) ≠
      0 := fun h0 ↦ one_ne_zero (α := A) <| by
    have hval : tilde.toOpen (.of A A) ⊤ (1 : A) = 0 := congr(Subtype.val $h0)
    have hinv := ConcreteCategory.congr_hom (tilde.isoTop (.of A A)).hom_inv_id (1 : A)
    simpa [hval] using hinv.symm
  have : Nontrivial (F.supportedSubmodule Z ⊤) := ⟨⟨_, h1⟩, 0, hne⟩
  exact (F.supportedModuleHZeroEquiv Z ⊤).toEquiv.nontrivial

omit [Nontrivial k] in
/-- In `A = nonNoetherianExampleRingCat k`, no nonzero element is annihilated by a uniform power
`I ^ n` of `I = (x₀, x₁, …)`, so `I.primaryComponent A = ⊥`. -/
theorem primaryComponent_nonNoetherianVarIdeal_eq_bot :
    (nonNoetherianVarIdeal k).primaryComponent (nonNoetherianExampleRingCat k) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_contra hp0
  have hpJ : p ∉ nonNoetherianRelIdeal k := fun h ↦ hp0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hnot := mt (mem_nonNoetherianRelIdeal_iff k p).mpr hpJ
  push Not at hnot
  obtain ⟨d₀, hd₀, hp₀⟩ := hnot
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (nonNoetherianExampleRingCat k)
    (nonNoetherianVarIdeal k) _).mp ha
  let N : ℕ := max n (d₀.support.sup id + 1)
  have hxN : Ideal.Quotient.mk (nonNoetherianRelIdeal k) (MvPolynomial.X N) ^ n ∈
      nonNoetherianVarIdeal k ^ n :=
    Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self N))) n
  have hprod : MvPolynomial.X N ^ n * p ∈ nonNoetherianRelIdeal k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [map_mul, map_pow] using (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨_, hxN⟩
  have hd' : ∀ j, (Finsupp.single N n + d₀) j < j + 2 := fun j ↦ by
    by_cases hj : j = N
    · subst hj
      have hdN : d₀ N = 0 := Finsupp.notMem_support_iff.mp fun hmem ↦
        not_le_of_gt (Nat.lt_succ_self (d₀.support.sup id))
          ((le_max_right n _).trans (Finset.le_sup (f := id) hmem) |>.trans_eq rfl)
      simpa [hdN] using lt_of_le_of_lt (le_max_left n _) (Nat.lt_add_of_pos_right two_pos)
    · simpa [hj] using hd₀ j
  have hzero := (mem_nonNoetherianRelIdeal_iff k _).mp hprod (Finsupp.single N n + d₀) hd'
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul, one_mul] at hzero
  exact hp₀ hzero

omit [Nontrivial k] in
/-- Algebraic degree-zero local cohomology `H⁰_I(A)` vanishes on `nonNoetherianExampleRingCat k`,
disagreeing with geometric `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})`. -/
theorem isZero_localCohomology_zero_nonNoetherianExampleRing :
    IsZero ((localCohomology (nonNoetherianVarIdeal k) 0).obj
      (.of (nonNoetherianExampleRingCat k) (nonNoetherianExampleRingCat k))) := by
  have : Subsingleton ((nonNoetherianVarIdeal k).primaryComponent
      (nonNoetherianExampleRingCat k)) :=
    primaryComponent_nonNoetherianVarIdeal_eq_bot k ▸ inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (localCohomology.degreeZeroEquivPrimaryComponent (nonNoetherianVarIdeal k)
      (.of (nonNoetherianExampleRingCat k) (nonNoetherianExampleRingCat k))).toModuleIso

/-- `nonNoetherianVarIdeal k` is not finitely generated; otherwise degree-zero geometric and
algebraic local cohomology would agree. -/
theorem not_fg_nonNoetherianVarIdeal : ¬ (nonNoetherianVarIdeal k).FG := fun hfg ↦ by
  let A := nonNoetherianExampleRingCat k
  have : Subsingleton ((nonNoetherianVarIdeal k).primaryComponent A) :=
    primaryComponent_nonNoetherianVarIdeal_eq_bot k ▸ inferInstance
  have : Subsingleton ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleH
      (Spec.zeroLocusClosed (R := A) (nonNoetherianVarIdeal k : Set A)) ⊤ 0) :=
    ((primaryComponentEquivSupportedSubmoduleTop hfg (.of A A)).trans
      ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleHZeroEquiv
        _ ⊤).symm).toEquiv.symm.subsingleton
  have := nontrivial_supportedModuleH_zero_nonNoetherianExampleRing k
  exact false_of_nontrivial_of_subsingleton
    ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleH
      (Spec.zeroLocusClosed (R := A) (nonNoetherianVarIdeal k : Set A)) ⊤ 0)

/-- `NonNoetherianExampleRing k` is not Noetherian. -/
theorem not_isNoetherianRing_nonNoetherianExampleRing :
    ¬ IsNoetherianRing (NonNoetherianExampleRing k) :=
  fun _ ↦ not_fg_nonNoetherianVarIdeal k (IsNoetherian.noetherian _)

end NonNoetherianCounterexample

end TauCeti.AlgebraicGeometry
