/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Reduced
public import TauCeti.LinearAlgebra.Charpoly.Pi
public import TauCeti.LinearAlgebra.Charpoly.Trace
public import TauCeti.RingTheory.Semisimple.Burnside
public import TauCeti.RingTheory.Semisimple.Trace.Basic

/-!
# Brauer–Nesbitt: semisimple modules are determined by characteristic polynomials

Let `A` be an algebra over an algebraically closed field `k`, of any characteristic. This file
proves that two finite-dimensional semisimple `A`-modules on which the elements of a spanning set
of `A` act with the same characteristic polynomials are isomorphic
(`IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq`). For the monoid algebra `k[G]` and the
spanning set `G`, this is the Brauer–Nesbitt theorem: the characteristic polynomials at the
elements of `G` determine a semisimple representation. In characteristic zero the traces already
suffice (`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`); in characteristic `p` they only
determine the multiplicities modulo `p`
(`IsSemisimpleModule.natCast_jordanHolderMultiplicity_eq_of_trace_eq`).

The proof is the classical one. By Burnside's theorem and the isotypic projections, `A` maps
onto `∏ j, End_k(T_j)` for a finite family of pairwise non-isomorphic finite-dimensional simple
modules `T_j` (`IsSemisimpleModule.exists_forall_lsmul_eq`, in
`TauCeti.RingTheory.Semisimple.Burnside`). An element acting on one `T_j` by an endomorphism of
trace `1` and by zero on the others therefore reads off the multiplicity of `T_j`, cast into `k`,
from the trace. If two semisimple modules have equal characteristic polynomials, cancel their
common simple summands. Their remaining multiplicities have disjoint supports and agree in `k`, so
they are all divisible by `p`. The characteristic polynomials are then `p`-th powers of those of
modules with multiplicities divided by `p`, which again agree because Frobenius is injective on
`k[X]`. Since the total multiplicity drops, induction shows that nothing remains.

## Main results

* `IsSemisimpleModule.natCast_jordanHolderMultiplicity_eq_of_trace_eq`: semisimple modules with
  the same trace on the elements of a spanning set have the same multiplicities of every simple
  module, cast into `k`.
* `IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq`: **Brauer–Nesbitt.** Semisimple
  modules with the same characteristic polynomials on a spanning set of `A` are isomorphic.

## References

* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 30.16.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, proof of Proposition 2.6.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, arXiv:0809.0415v2, end of the proof of
  Theorem 2.12.
-/

public section

open Module Polynomial TauCeti

namespace IsSemisimpleModule

section Exponents

variable {k ι Γ : Type*} [Field k] [Fintype ι] (P : ι → Γ → k[X]) (hP : ∀ i γ, (P i γ).Monic)
variable (hsep : ∀ c d : ι → ℕ, (∀ γ, ∏ i, P i γ ^ c i = ∏ i, P i γ ^ d i) → ∀ i, (c i : k) = d i)
include hsep

/-- **Exponent vectors with disjoint supports.** Let `P i γ` be polynomials over a field `k` such
that exponent vectors `c, d` giving the same products `∏ i, P i γ ^ c i` for every `γ` agree after
casting into `k`. If such `c, d` have disjoint supports, they vanish. Their entries vanish in `k`,
so in characteristic `p` they are divisible by `p`; since Frobenius is injective on `k[X]`, the
quotients by `p` again give equal products, and induction on the total exponent applies. -/
private theorem eq_zero_of_forall_prod_pow_eq :
    ∀ c d : ι → ℕ, (∀ i, c i = 0 ∨ d i = 0) → (∀ γ, ∏ i, P i γ ^ c i = ∏ i, P i γ ^ d i) →
      c = 0 ∧ d = 0 := by
  intro c d
  induction hn : ∑ i, (c i + d i) using Nat.strong_induction_on generalizing c d with
  | _ n ih =>
  intro hdisj h
  have hcast (i : ι) : (c i : k) = 0 ∧ (d i : k) = 0 := by
    have := hsep c d h i
    rcases hdisj i with hi | hi <;> simp_all
  by_contra h0
  obtain ⟨p, hchar⟩ := CharP.exists k
  have hdvd (i : ι) : p ∣ c i ∧ p ∣ d i :=
    ⟨(CharP.cast_eq_zero_iff k p _).mp (hcast i).1, (CharP.cast_eq_zero_iff k p _).mp (hcast i).2⟩
  rcases CharP.char_is_prime_or_zero k p with hp | rfl
  swap
  · exact h0 ⟨funext fun i => Nat.eq_zero_of_zero_dvd (hdvd i).1,
      funext fun i => Nat.eq_zero_of_zero_dvd (hdvd i).2⟩
  have := Fact.mk hp
  choose u hu using fun i => (hdvd i).1
  choose v hv using fun i => (hdvd i).2
  have hpow (e : ι → ℕ) (γ : Γ) : ∏ i, P i γ ^ (p * e i) = (∏ i, P i γ ^ e i) ^ p := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  have h2 := hp.two_le
  obtain ⟨hu0, hv0⟩ : u = 0 ∧ v = 0 := by
    refine ih (∑ i, (u i + v i)) ?_ u v rfl (fun i => ?_) fun γ => frobenius_inj k[X] p ?_
    · rw [← hn]
      obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 ∨ v i ≠ 0 := by
        by_contra! hall
        exact h0 ⟨funext fun i => by simp [hu i, (hall i).1],
          funext fun i => by simp [hv i, (hall i).2]⟩
      refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · nlinarith [hu i, hv i]
      · rcases hi with hi | hi <;> nlinarith [hu i, hv i, Nat.pos_of_ne_zero hi]
    · rcases hdisj i with hi | hi
      · exact Or.inl (by simpa [hu i, hp.ne_zero] using hi)
      · exact Or.inr (by simpa [hv i, hp.ne_zero] using hi)
    · simp only [frobenius_def, ← hpow]
      simpa only [← hu, ← hv] using h γ
  exact h0 ⟨funext fun i => by simp [hu i, hu0], funext fun i => by simp [hv i, hv0]⟩

include hP in
/-- **Cancelling exponents against a separating family.** Let `P i γ` be monic polynomials over a
field `k` such that exponent vectors `c, d` giving the same products `∏ i, P i γ ^ c i` for every
`γ` agree after casting into `k`. Then such exponent vectors agree: cancelling their common part
`min (c i) (d i)` leaves exponent vectors with disjoint supports, which vanish by
`eq_zero_of_forall_prod_pow_eq`. -/
private theorem eq_of_forall_prod_pow_eq (c d : ι → ℕ)
    (h : ∀ γ, ∏ i, P i γ ^ c i = ∏ i, P i γ ^ d i) : c = d := by
  have key (e : ι → ℕ) (he : ∀ i, min (c i) (d i) ≤ e i) (γ : Γ) : ∏ i, P i γ ^ e i =
      (∏ i, P i γ ^ min (c i) (d i)) * ∏ i, P i γ ^ (e i - min (c i) (d i)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_sub_cancel' (he i)]
  obtain ⟨hc, hd⟩ := eq_zero_of_forall_prod_pow_eq P hsep (fun i => c i - min (c i) (d i))
    (fun i => d i - min (c i) (d i)) (fun i => by omega) fun γ => by
      have := h γ
      rw [key c (fun i => min_le_left _ _), key d (fun i => min_le_right _ _)] at this
      exact mul_left_cancel₀ (monic_prod_of_monic _ _ fun i _ => (hP i γ).pow _).ne_zero this
  funext i
  have := congrFun hc i
  have := congrFun hd i
  simp only [Pi.zero_apply] at *
  omega

end Exponents

section Generic

variable {A : Type*} [Ring A]

/-- Finitely many pairwise non-isomorphic simple submodules of `M × N` to which every simple
submodule of `M` and of `N` is isomorphic. -/
private theorem exists_simple_family (M N : Type*) [AddCommGroup M] [Module A M]
    [IsSemisimpleModule A M] [Module.Finite A M] [AddCommGroup N] [Module A N]
    [IsSemisimpleModule A N] [Module.Finite A N] :
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → Submodule A (M × N)),
      (∀ i, IsSimpleModule A (T i)) ∧ (Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j)) ∧
      (∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i)) ∧
      ∀ P : Submodule A N, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i) := by
  classical
  obtain ⟨r, Q, hQ, ⟨e⟩⟩ := exists_linearEquiv_pi_submodule (R := A) (M × N)
  let s : Setoid (Fin r) :=
    { r x y := Nonempty (Q x ≃ₗ[A] Q y)
      iseqv := ⟨fun _ => ⟨.refl A _⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩ }
  -- A simple module embedded in `M × N` is isomorphic to a factor of the decomposition.
  have hcover (P : Submodule A (M × N)) [IsSimpleModule A P] :
      ∃ i : Quotient s, Nonempty (P ≃ₗ[A] Q i.out) := by
    have hle := jordanHolderMultiplicity_le_of_injective (S := P) P.subtype Subtype.val_injective
    rw [jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv P (.refl A P),
      jordanHolderMultiplicity_eq_of_linearEquiv e, jordanHolderMultiplicity_pi_eq_natCard] at hle
    obtain ⟨⟨x, ⟨g⟩⟩⟩ := (Nat.card_pos_iff.mp hle).1
    obtain ⟨h⟩ := Quotient.mk_out (s := s) x
    exact ⟨⟦x⟧, ⟨g.trans h.symm⟩⟩
  refine ⟨Quotient s, Fintype.ofFinite _, fun i => Q i.out, fun i => hQ _,
    fun i j hij => ⟨fun f => ?_⟩, fun P _ => ?_, fun P _ => ?_⟩
  · exact hij (by rw [← Quotient.out_eq i, ← Quotient.out_eq j]; exact Quotient.sound ⟨f⟩)
  · let e' := P.equivMapOfInjective _ (LinearMap.inl_injective (R := A) (M := M) (M₂ := N))
    have := IsSimpleModule.congr e'.symm
    obtain ⟨i, ⟨f⟩⟩ := hcover (P.map (LinearMap.inl A M N))
    exact ⟨i, ⟨e'.trans f⟩⟩
  · let e' := P.equivMapOfInjective _ (LinearMap.inr_injective (R := A) (M := M) (M₂ := N))
    have := IsSimpleModule.congr e'.symm
    obtain ⟨i, ⟨f⟩⟩ := hcover (P.map (LinearMap.inr A M N))
    exact ⟨i, ⟨e'.trans f⟩⟩

/-- If every simple submodule of `M` is isomorphic to some `T i`, then a module isomorphic to no
`T i` does not occur in `M`. -/
private theorem jordanHolderMultiplicity_eq_zero_of_forall_isEmpty {ι : Type*} {T : ι → Type*}
    [∀ i, AddCommGroup (T i)] [∀ i, Module A (T i)] {M : Type*} [AddCommGroup M] [Module A M]
    [IsSemisimpleModule A M] [Module.Finite A M]
    (hM : ∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i))
    (S : Type*) [AddCommGroup S] [Module A S] (hS : ∀ i, IsEmpty (S ≃ₗ[A] T i)) :
    jordanHolderMultiplicity A M S = 0 := by
  obtain ⟨n, Q, hQ, ⟨eM⟩⟩ := exists_linearEquiv_pi_submodule (R := A) M
  rw [jordanHolderMultiplicity_eq_of_linearEquiv eM, jordanHolderMultiplicity_pi_eq_natCard,
    Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨x, ⟨e⟩⟩ => ?_⟩
  obtain ⟨i, ⟨f⟩⟩ := hM (Q x) (hQ x)
  exact (hS i).false (e.trans f)

/-- Under the covering hypotheses, a function of the multiplicities that agrees on every `T i`
agrees on every module: a module isomorphic to no `T i` occurs in neither `M` nor `N`. -/
private theorem forall_jordanHolderMultiplicity_eq {α : Type*} (φ : ℕ → α) {ι : Type*}
    {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module A (T i)] {M N : Type*}
    [AddCommGroup M] [Module A M] [IsSemisimpleModule A M] [Module.Finite A M] [AddCommGroup N]
    [Module A N] [IsSemisimpleModule A N] [Module.Finite A N]
    (hM : ∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i))
    (hN : ∀ P : Submodule A N, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i))
    (h : ∀ i, φ (jordanHolderMultiplicity A M (T i)) = φ (jordanHolderMultiplicity A N (T i)))
    (S : Type*) [AddCommGroup S] [Module A S] :
    φ (jordanHolderMultiplicity A M S) = φ (jordanHolderMultiplicity A N S) := by
  by_cases hS : ∃ i, Nonempty (S ≃ₗ[A] T i)
  · obtain ⟨i, ⟨f⟩⟩ := hS
    rw [jordanHolderMultiplicity_congr f, jordanHolderMultiplicity_congr f]
    exact h i
  · simp only [not_exists, not_nonempty_iff] at hS
    rw [jordanHolderMultiplicity_eq_zero_of_forall_isEmpty hM S hS,
      jordanHolderMultiplicity_eq_zero_of_forall_isEmpty hN S hS]

end Generic

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The trace combination `∑ i, c i • tr(a | T i)` is minus the next coefficient of
`∏ i, charpoly(a | T i) ^ c i`. -/
private theorem sum_smul_trace_eq {ι : Type*} [Fintype ι] {T : ι → Type*}
    [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)] [∀ i, Module A (T i)]
    [∀ i, IsScalarTower k A (T i)] [∀ i, FiniteDimensional k (T i)] (c : ι → ℕ) (a : A) :
    -(∏ i, (Algebra.lsmul k k (T i) a).charpoly ^ c i).nextCoeff =
      ∑ i, c i • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) a) := by
  rw [Monic.nextCoeff_prod _ _ fun i _ => (LinearMap.charpoly_monic _).pow _,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(LinearMap.charpoly_monic _).nextCoeff_pow, LinearMap.trace_eq_neg_charpoly_nextCoeff,
    smul_neg]

section Decomposition

variable {ι : Type*} [Fintype ι] {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)]
  [∀ i, Module A (T i)] [∀ i, IsScalarTower k A (T i)] [∀ i, FiniteDimensional k (T i)]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [IsSemisimpleModule A M] [Module.Finite A M]

/-- **The characteristic polynomial of a semisimple module.** If every simple submodule of `M` is
isomorphic to one of the pairwise non-isomorphic simple modules `T i`, then the characteristic
polynomial of `a` on `M` is `∏ i, charpoly(a | T i) ^ [M : T i]`. -/
private theorem charpoly_lsmul_eq_prod (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j))
    (hM : ∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i)) (a : A) :
    (Algebra.lsmul k k M a).charpoly =
      ∏ i, (Algebra.lsmul k k (T i) a).charpoly ^ jordanHolderMultiplicity A M (T i) := by
  classical
  obtain ⟨n, Q, hQ, ⟨eM⟩⟩ := exists_linearEquiv_pi_submodule (R := A) M
  have (x : Fin n) : FiniteDimensional k (Q x) :=
    .of_injective ((Q x).subtype.restrictScalars k) Subtype.val_injective
  have hprod : (Algebra.lsmul k k M a).charpoly = ∏ x, (Algebra.lsmul k k (Q x) a).charpoly := by
    rw [← (eM.restrictScalars k).charpoly_conj, ← LinearMap.charpoly_piMap]
    congr 1
    refine LinearMap.ext fun y => funext fun x => ?_
    simp [LinearEquiv.conj_apply]
  choose σ hσ using fun x => hM (Q x) (hQ x)
  have hx (x : Fin n) : (Algebra.lsmul k k (Q x) a).charpoly =
      (Algebra.lsmul k k (T (σ x)) a).charpoly := by
    rw [← ((hσ x).some.restrictScalars k).charpoly_conj]
    congr 1
    ext y
    simp [LinearEquiv.conj_apply]
  rw [hprod, Finset.prod_congr rfl fun x _ => hx x,
    ← Finset.prod_fiberwise Finset.univ σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.prod_const,
    jordanHolderMultiplicity_eq_of_linearEquiv eM, jordanHolderMultiplicity_pi_eq_natCard,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => h ▸ ⟨(hσ x).some.symm⟩, fun ⟨e⟩ => ?_⟩
  by_contra hne
  exact (hT hne).false ((hσ x).some.symm.trans e.symm)

/-- The trace of `a` on `M` is `∑ i, [M : T i] • tr(a | T i)`, under the hypotheses of
`charpoly_lsmul_eq_prod`. -/
private theorem trace_lsmul_eq_sum (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j))
    (hM : ∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i)) (a : A) :
    LinearMap.trace k M (Algebra.lsmul k k M a) =
      ∑ i, jordanHolderMultiplicity A M (T i) • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) a)
    := by
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff, charpoly_lsmul_eq_prod hT hM, sum_smul_trace_eq]

end Decomposition

variable [IsAlgClosed k]

section Family

variable {ι : Type*} [Finite ι] {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)]
  [∀ i, Module A (T i)] [∀ i, IsScalarTower k A (T i)] [∀ i, IsSimpleModule A (T i)]
  [∀ i, FiniteDimensional k (T i)]

/-- **Traces separate multiplicities.** Over an algebraically closed field, if the trace
combinations `∑ i, c i • tr(a | T i)` and `∑ i, d i • tr(a | T i)` agree on a spanning set of `A`,
for pairwise non-isomorphic simple `T i`, then `c i` and `d i` agree in `k`. -/
private theorem natCast_eq_of_sum_trace_eq [Fintype ι]
    (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j)) {Γ : Type*} {g : Γ → A}
    (hg : Submodule.span k (Set.range g) = ⊤) (c d : ι → ℕ)
    (h : ∀ γ, ∑ i, c i • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) (g γ)) =
      ∑ i, d i • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) (g γ))) (i : ι) :
    (c i : k) = d i := by
  classical
  let φ (e : ι → ℕ) : A →ₗ[k] k :=
    ∑ j, e j • (LinearMap.trace k (T j)).comp (Algebra.lsmul k k (T j)).toLinearMap
  have hφ : φ c = φ d := LinearMap.ext_on_range hg fun γ => by simpa [φ] using h γ
  -- An element acting on `T i` by a rank-one idempotent and by zero on the other `T j`.
  have : Nontrivial (T i) := IsSimpleModule.nontrivial A (T i)
  let B := Module.finBasis k (T i)
  let j₀ : Fin (finrank k (T i)) := ⟨0, finrank_pos⟩
  obtain ⟨a, ha⟩ := exists_forall_lsmul_eq hT
    (Pi.single i ((B.coord j₀).smulRight (B j₀)) : ∀ j, Module.End k (T j))
  have hφa (e : ι → ℕ) : φ e a = e i := by
    simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, ha]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp [B, LinearMap.trace_smulRight]
  rw [← hφa c, ← hφa d, hφ]

end Family

variable {M N : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [IsSemisimpleModule A M] [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N] [FiniteDimensional k N] [IsSemisimpleModule A N]

/-- **Traces determine multiplicities modulo the characteristic.** Over an algebraically closed
field, finite-dimensional semisimple modules on which every element of `A` acts with the same
trace contain every simple module the same number of times, counted in `k`. In characteristic `p`
the multiplicities are thus congruent modulo `p`, and need not be equal: over an algebraic closure
of `𝔽₃`, three copies
of the trivial representation of `ℤ/2` and three copies of its sign representation have the same
trace everywhere, and contain the trivial representation `3` and `0` times. -/
theorem natCast_jordanHolderMultiplicity_eq_of_trace_eq [Module.Finite A M] [Module.Finite A N]
    {Γ : Type*} {g : Γ → A} (hg : Submodule.span k (Set.range g) = ⊤)
    (h : ∀ γ, LinearMap.trace k M (Algebra.lsmul k k M (g γ)) =
      LinearMap.trace k N (Algebra.lsmul k k N (g γ)))
    (S : Type*) [AddCommGroup S] [Module A S] :
    (jordanHolderMultiplicity A M S : k) = jordanHolderMultiplicity A N S := by
  obtain ⟨ι, _, T, hTs, hT, hM, hN⟩ := exists_simple_family (A := A) M N
  have (i : ι) : FiniteDimensional k (T i) :=
    .of_injective ((T i).subtype.restrictScalars k) Subtype.val_injective
  have (i : ι) : IsSimpleModule A (T i) := hTs i
  have hmult := natCast_eq_of_sum_trace_eq hT hg
    (fun i => jordanHolderMultiplicity A M (T i)) (fun i => jordanHolderMultiplicity A N (T i))
    fun γ => by
      rw [← trace_lsmul_eq_sum (k := k) hT hM, ← trace_lsmul_eq_sum (k := k) hT hN]
      exact h γ
  exact forall_jordanHolderMultiplicity_eq (Nat.cast : ℕ → k) hM hN hmult S

/-- **Brauer–Nesbitt.** Over an algebraically closed field `k` of any characteristic, two
finite-dimensional semisimple modules over a `k`-algebra `A` are isomorphic if the elements of a
spanning set `Set.range g` of `A` act on them with the same characteristic polynomials.

Traces alone do not suffice in characteristic `p`: over an algebraic closure of `𝔽₃`, three copies
of the trivial representation of `ℤ/2` and three copies of the sign representation have equal
traces. -/
theorem nonempty_linearEquiv_of_charpoly_eq {Γ : Type*} {g : Γ → A}
    (hg : Submodule.span k (Set.range g) = ⊤)
    (h : ∀ γ, (Algebra.lsmul k k M (g γ)).charpoly = (Algebra.lsmul k k N (g γ)).charpoly) :
    Nonempty (M ≃ₗ[A] N) := by
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨ι, _, T, hTs, hT, hM, hN⟩ := exists_simple_family (A := A) M N
  have (i : ι) : FiniteDimensional k (T i) :=
    .of_injective ((T i).subtype.restrictScalars k) Subtype.val_injective
  have (i : ι) : IsSimpleModule A (T i) := hTs i
  have hmult := eq_of_forall_prod_pow_eq (fun i γ => (Algebra.lsmul k k (T i) (g γ)).charpoly)
    (fun _ _ => LinearMap.charpoly_monic _)
    (fun c d hcd => natCast_eq_of_sum_trace_eq hT hg c d fun γ => by
      rw [← sum_smul_trace_eq, ← sum_smul_trace_eq, hcd γ])
    (fun i => jordanHolderMultiplicity A M (T i)) (fun i => jordanHolderMultiplicity A N (T i))
    fun γ => by rw [← charpoly_lsmul_eq_prod hT hM, ← charpoly_lsmul_eq_prod hT hN, h γ]
  exact nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N fun S _ _ _ =>
    forall_jordanHolderMultiplicity_eq id hM hN (congrFun hmult) S

end IsSemisimpleModule
