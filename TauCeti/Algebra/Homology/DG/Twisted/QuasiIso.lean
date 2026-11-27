/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.ActionSequence
import Mathlib.Data.Fintype.Lattice
import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Continuation maps with homotopy-invertible diagonal are quasi-isomorphisms

Let `ν` be a continuation cocycle between two twisting cocycles `m₁` and `m₂` on the same
generators `(P, ind)`, over a differential graded algebra `(𝒜, d)`. Suppose that `ν` vanishes
between distinct generators `x ≠ y` with `ind x ≤ ind y`, and that each diagonal entry `ν x x`,
a cycle of degree `0`, is invertible up to homotopy: there is a cycle `μ` of degree `0` with
`ν x x * μ - 1` and `μ * ν x x - 1` boundaries of elements of degree `-1`. Then for every
differential graded right module `ℳ` the continuation map `ℳ ⊗ ⟨P⟩ → ℳ ⊗ ⟨P⟩` of `ν` is a
quasi-isomorphism (`TauCeti.ContinuationCocycle.quasiIso_continuationHom`), so the two twisted
complexes have the same cohomology.

This is the situation of a gauge transformation between Barraud–Cornea cocycles over the chains
`C_*(ΩX)` on a based loop space whose diagonal entries are point chains of loops. Such a loop is
invertible in `H₀(ΩX)` but, when it has positive length, not in the chain algebra of Moore loops,
whose unit is the constant loop of length zero. So the continuation cocycle need not be invertible
as a matrix (compare `TauCeti.ContinuationCocycle.isUnit_of_eq_one_of_le`), but its continuation
map is a quasi-isomorphism. Over an algebra concentrated in cohomological degrees `≤ 0`, such as
`C_*(ΩX)`, the entries with `ind x < ind y` vanish for degree reasons, and it suffices that `ν`
vanishes between distinct generators of equal index
(`TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_nonpos`).

The proof is an induction on the number of generators. A generator `x` of maximal index spans a
quotient complex of the twisted complex, with the twisted complex of the other generators as
subcomplex (`TauCeti.TwistingCocycle.restrictShortComplex_shortExact`), and `ν` maps this short
exact sequence to the one of `m₂` (`TauCeti.ContinuationCocycle.restrictShortComplexMap`). On the
subcomplex the continuation map is a quasi-isomorphism by induction. On the quotient, which has the
single generator `x`, the twisting cocycles vanish and the continuation map is right
multiplication by `ν x x`; a homotopy inverse `μ` and the two homotopies make the two quotients
homologous (`TauCeti.Homologous`), so the map is a homotopy equivalence. The two out of three
property for the middle map of a morphism of short exact sequences
(`HomologicalComplex.HomologySequence.quasiIso_τ₂`) concludes.

## Main results

* `TauCeti.ContinuationCocycle.quasiIso_continuationHom`: a continuation cocycle on one set of
  generators, vanishing between distinct generators `x, y` with `ind x ≤ ind y` and with diagonal
  entries invertible up to homotopy, induces quasi-isomorphisms of twisted complexes.
* `TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_nonpos`: over a nonpositively graded
  algebra, it suffices that the cocycle vanishes between distinct generators of equal index.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3, 4 and 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}

namespace ContinuationCocycle

/-! ### At most one generator -/

section Subsingleton

variable {P : Type uP} [Fintype P] [DecidableEq P] [Subsingleton P] {ind : P → ℤ}
  {m₁ m₂ : TwistingCocycle 𝒜 d P ind}

omit [GradedAlgebra 𝒜] [DecidableEq P] in
/-- On at most one generator a twisting cocycle vanishes, by one-sidedness. -/
private theorem m_eq_zero_of_subsingleton (m : TwistingCocycle 𝒜 d P ind) (x y : P) :
    m.m x y = 0 :=
  m.one_sided x y (congrArg ind (Subsingleton.elim x y)).le

/-- On at most one generator, the continuation cocycle `m₂ → m₁` whose entry at `x` is a cycle
`μ x` of degree `0`. -/
private def ofSubsingleton (μ : P → A) (hμ : ∀ x, μ x ∈ 𝒜 0) (hdμ : ∀ x, d (μ x) = 0) :
    ContinuationCocycle m₂ m₁ where
  ν x _ := μ x
  mem_graded x y := by
    obtain rfl := Subsingleton.elim x y
    simpa using hμ x
  continuation x y := by
    simp [hdμ, m_eq_zero_of_subsingleton]

/-- On at most one generator, a continuation cocycle whose entries are invertible up to homotopy
makes its two ends homologous: the inverse is `ofSubsingleton μ`, and the homotopies between the
two composites and the identities are the given elements `k` and `k'`. -/
private def homologousOfSubsingleton (ν : ContinuationCocycle m₁ m₂) (μ : P → A)
    (hμ : ∀ x, μ x ∈ 𝒜 0) (hdμ : ∀ x, d (μ x) = 0) (k k' : P → A) (hk : ∀ x, k x ∈ 𝒜 (-1))
    (hk' : ∀ x, k' x ∈ 𝒜 (-1)) (hdk : ∀ x, d (k x) = ν.ν x x * μ x - 1)
    (hdk' : ∀ x, d (k' x) = μ x * ν.ν x x - 1) : Homologous h m₁ m₂ where
  ν := ν
  ν' := ofSubsingleton μ hμ hdμ
  homP :=
    { h := fun x _ ↦ k x
      mem_graded := fun x y ↦ by
        obtain rfl := Subsingleton.elim x y
        simpa using hk x
      parametrized := fun x y ↦ by
        obtain rfl := Subsingleton.elim x y
        simp [comp_ν, Matrix.mul_apply, Fintype.sum_subsingleton _ x, ofSubsingleton, hdk,
          m_eq_zero_of_subsingleton] }
  homQ :=
    { h := fun x _ ↦ k' x
      mem_graded := fun x y ↦ by
        obtain rfl := Subsingleton.elim x y
        simpa using hk' x
      parametrized := fun x y ↦ by
        obtain rfl := Subsingleton.elim x y
        simp [comp_ν, Matrix.mul_apply, Fintype.sum_subsingleton _ x, ofSubsingleton, hdk',
          m_eq_zero_of_subsingleton] }

omit [DecidableEq P] in
/-- On at most one generator, a continuation cocycle whose entries are invertible up to homotopy
induces quasi-isomorphisms, indeed homotopy equivalences, of twisted complexes. -/
private theorem quasiIso_continuationHom_of_subsingleton (ν : ContinuationCocycle m₁ m₂)
    (μ : P → A) (hμ : ∀ x, μ x ∈ 𝒜 0) (hdμ : ∀ x, d (μ x) = 0) (k k' : P → A)
    (hk : ∀ x, k x ∈ 𝒜 (-1)) (hk' : ∀ x, k' x ∈ 𝒜 (-1)) (hdk : ∀ x, d (k x) = ν.ν x x * μ x - 1)
    (hdk' : ∀ x, d (k' x) = μ x * ν.ν x x - 1) (hM : IsDGRightModule h ℳ dM) :
    QuasiIso (ν.continuationHom hM) := by
  classical
  have := ((homologousOfSubsingleton ν μ hμ hdμ k k' hk hk' hdk hdk').homotopyEquiv hM).quasiIso_hom
  rwa [Homologous.homotopyEquiv_hom] at this

end Subsingleton

/-! ### The induction on the number of generators -/

/-- The induction behind `TauCeti.ContinuationCocycle.quasiIso_continuationHom`, on the number `n`
of generators: a generator of maximal index spans a quotient complex, on which the continuation map
is a homotopy equivalence, and the other generators span a subcomplex, on which it is a
quasi-isomorphism by induction. -/
private theorem quasiIso_continuationHom_of_card_eq (hM : IsDGRightModule h ℳ dM) (n : ℕ) :
    ∀ {P : Type uP} [Fintype P] {ind : P → ℤ}
      {m₁ m₂ : TwistingCocycle 𝒜 d P ind} (ν : ContinuationCocycle m₁ m₂), Fintype.card P = n →
      (∀ x y, ind x ≤ ind y → x ≠ y → ν.ν x y = 0) →
      (∀ x, ∃ μ ∈ 𝒜 0, d μ = 0 ∧ (∃ k ∈ 𝒜 (-1), d k = ν.ν x x * μ - 1) ∧
        ∃ k ∈ 𝒜 (-1), d k = μ * ν.ν x x - 1) →
      QuasiIso (ν.continuationHom hM) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ ind m₁ m₂ ν hn hν hunit
  classical
  choose μ hμ hdμ hk hk' using hunit
  choose k hk hdk using hk
  choose k' hk' hdk' using hk'
  cases isEmpty_or_nonempty P with
  | inl _ =>
    -- With no generators the two ends are homologous, so `ν` induces a homotopy equivalence.
    exact quasiIso_continuationHom_of_subsingleton ν μ hμ hdμ k k' hk hk' hdk hdk' hM
  | inr _ =>
    -- Split off a generator `x` of maximal index: the others span a subcomplex `S`, and `x`
    -- spans the quotient complex `T`.
    obtain ⟨x, hx⟩ := Finite.exists_max ind
    let S : Set P := {y | y ≠ x}
    let T : Set P := {y | y = x}
    have hST : ∀ y, y ∈ T ↔ y ∉ S := fun y ↦ by simp [S, T]
    have hS : ∀ (m : TwistingCocycle 𝒜 d P ind) (a b : P), a ∈ S → b ∉ S → m.m a b = 0 :=
      fun m a b _ hb ↦ m.one_sided a b (by rw [not_not.1 hb]; exact hx a)
    have hνS : ∀ a b, a ∈ S → b ∉ S → ν.ν a b = 0 := fun a b ha hb ↦
      hν a b (by rw [not_not.1 hb]; exact hx a) (by rw [not_not.1 hb]; exact ha)
    let φ := ν.restrictShortComplexMap h hM S T (hS m₁) hST S T (hS m₂) hST hνS
    -- On the subcomplex of `S` the continuation map is a quasi-isomorphism by induction.
    have h₁ : QuasiIso φ.τ₁ := by
      rw [restrictShortComplexMap_τ₁]
      refine ih _ (hn ▸ Fintype.card_subtype_lt (x := x) (by simp [S])) _ rfl
        (fun a b hab hne ↦ by simpa using hν a b hab (Subtype.coe_injective.ne hne))
        fun a ↦ ⟨μ a, hμ a, hdμ a, ⟨k a, hk a, by simpa using hdk a⟩, k' a, hk' a,
          by simpa using hdk' a⟩
    -- On the quotient complex of `T = {x}` it is a homotopy equivalence.
    have : Subsingleton T := ⟨fun a b ↦ Subtype.ext (a.property.trans b.property.symm)⟩
    have h₃ : QuasiIso φ.τ₃ := by
      rw [restrictShortComplexMap_τ₃]
      exact quasiIso_continuationHom_of_subsingleton _ (fun a : T ↦ μ a) (fun a ↦ hμ a)
        (fun a ↦ hdμ a) (fun a : T ↦ k a) (fun a : T ↦ k' a) (fun a ↦ hk a) (fun a ↦ hk' a)
        (fun a ↦ by simpa using hdk a) (fun a ↦ by simpa using hdk' a) hM
    -- So it is a quasi-isomorphism on the whole complex, by two out of three.
    have := HomologicalComplex.HomologySequence.quasiIso_τ₂ φ
      (m₁.restrictShortComplex_shortExact hM S T (hS m₁) hST)
      (m₂.restrictShortComplex_shortExact hM S T (hS m₂) hST) h₁ h₃
    rwa [restrictShortComplexMap_τ₂] at this

variable {P : Type uP} [Fintype P] {ind : P → ℤ} {m₁ m₂ : TwistingCocycle 𝒜 d P ind}

/-- **A continuation cocycle with homotopy-invertible diagonal induces quasi-isomorphisms.** Let
`ν` be a continuation cocycle between twisting cocycles on the same generators `(P, ind)` which
vanishes between distinct generators `x ≠ y` with `ind x ≤ ind y`, and whose diagonal entries are
invertible up to homotopy: for each `x` there is a cycle `μ` of degree `0` such that
`ν x x * μ - 1` and `μ * ν x x - 1` are boundaries of elements of degree `-1`. Then for every
differential graded right module the continuation map of `ν` is a quasi-isomorphism of twisted
complexes. -/
theorem quasiIso_continuationHom (ν : ContinuationCocycle m₁ m₂)
    (hν : ∀ x y, ind x ≤ ind y → x ≠ y → ν.ν x y = 0)
    (hunit : ∀ x, ∃ μ ∈ 𝒜 0, d μ = 0 ∧ (∃ k ∈ 𝒜 (-1), d k = ν.ν x x * μ - 1) ∧
      ∃ k ∈ 𝒜 (-1), d k = μ * ν.ν x x - 1)
    (hM : IsDGRightModule h ℳ dM) : QuasiIso (ν.continuationHom hM) :=
  quasiIso_continuationHom_of_card_eq hM _ ν rfl hν hunit

/-- **A continuation cocycle over a nonpositively graded algebra induces quasi-isomorphisms when it
vanishes between distinct generators of equal index and its diagonal is invertible up to
homotopy.** Over an algebra concentrated in cohomological degrees `≤ 0`, such as the chains on a
based loop space, the entries `ν x y` with `ind x < ind y` vanish for degree reasons. -/
theorem quasiIso_continuationHom_of_nonpos (ν : ContinuationCocycle m₁ m₂)
    (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥) (hν : ∀ x y, ind x = ind y → x ≠ y → ν.ν x y = 0)
    (hunit : ∀ x, ∃ μ ∈ 𝒜 0, d μ = 0 ∧ (∃ k ∈ 𝒜 (-1), d k = ν.ν x x * μ - 1) ∧
      ∃ k ∈ 𝒜 (-1), d k = μ * ν.ν x x - 1)
    (hM : IsDGRightModule h ℳ dM) : QuasiIso (ν.continuationHom hM) :=
  ν.quasiIso_continuationHom (fun x y hxy hne ↦ hxy.lt_or_eq.elim
    (fun hlt ↦ ν.ν_eq_zero_of_lt_of_nonpos h𝒜 hlt) (fun heq ↦ hν x y heq hne)) hunit hM

end ContinuationCocycle

end TauCeti
