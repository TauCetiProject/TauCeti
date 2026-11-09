/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import TauCeti.LinearAlgebra.Span.Basic

/-!
# Pseudo-bases of lattices over a Dedekind domain

Let `R` be a Dedekind domain with fraction field `K` and let `V` be a `K`-vector space. A
finitely generated `R`-submodule `Λ` of `V` that spans `V` over `K` need not be free, but it is
always a direct sum of rank-one pieces: there are a `K`-basis `b` of `V` and nonzero ideals
`J i` of `R` with `Λ = ⊕ i, J i • b i`, that is, `x ∈ Λ` exactly when the `i`-th coordinate of
`x` in `b` lies in `J i` for every `i`. Such a pair `(b, J)` is a *pseudo-basis* of `Λ`. This is
the structure theorem for finitely generated torsion-free modules over a Dedekind domain, in the
form a covolume or index computation consumes: the change of variables `b.equivFun` carries `Λ`
onto the product of the ideals `J i`.

## Main results

* `Submodule.exists_apply_eq_one_forall_smul_mem`: an `R`-submodule `Λ` splits off its image
  `I` under a `K`-linear functional `f` when `I` is finitely generated and nonzero: some `v`
  has `f v = 1` and `x • v ∈ Λ` for all `x ∈ I`.
* `Submodule.exists_pseudoBasis`: a finitely generated `R`-submodule spanning `V` has a
  pseudo-basis indexed by any finite type of cardinality `finrank K V`.

## Implementation notes

The pseudo-basis is built one coordinate at a time. A nonzero `K`-linear functional `f` maps `Λ`
onto a nonzero finitely generated fractional ideal `I`, and since `I` is invertible there is a
vector `v` with `f v = 1` and `I • v ⊆ Λ`; then `Λ` is the direct sum of `Λ ∩ ker f` and `I • v`,
and the first summand spans a smaller subspace.

## References

* H. Cohen, *Advanced Topics in Computational Number Theory*, Graduate Texts in Mathematics 193,
  Springer, 2000, Section 1.2 (pseudo-bases and the structure of finitely generated torsion-free
  modules over a Dedekind domain).
-/

public section

open Module Submodule
open scoped nonZeroDivisors

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

namespace Submodule

/-- An `R`-submodule `Λ` of a `K`-vector space splits off its image under a `K`-linear functional
`f` when that image is finitely generated and nonzero: there is a vector `v` with `f v = 1` such
that `x • v ∈ Λ` for every `x` in the image `f '' Λ`, a nonzero fractional ideal of `R`. -/
theorem exists_apply_eq_one_forall_smul_mem (Λ : Submodule R V) (f : V →ₗ[K] K)
    (hI : (Λ.map (f.restrictScalars R)).FG) (hf : Λ.map (f.restrictScalars R) ≠ ⊥) :
    ∃ v : V, f v = 1 ∧ ∀ x ∈ Λ.map (f.restrictScalars R), x • v ∈ Λ := by
  set I := Λ.map (f.restrictScalars R)
  let I' : FractionalIdeal R⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hcoe : (I' : Submodule R K) = I := rfl
  have hI' : I' ≠ 0 := fun h ↦ hf <| by rw [← hcoe, h, FractionalIdeal.coe_zero]
  have hmul : I * (I'⁻¹ : FractionalIdeal R⁰ K) = 1 := by
    rw [← hcoe, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI', FractionalIdeal.coe_one]
  -- The vectors `v` with `I • v ⊆ Λ` form an `R`-submodule `N`; we show `1 ∈ f(N)`.
  let N : Submodule R V :=
    { carrier := {v | ∀ x ∈ I, x • v ∈ Λ}
      add_mem' := fun ha hb x hx ↦ by simpa [smul_add] using Λ.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ ↦ by simp
      smul_mem' := fun r v hv x hx ↦ by
        rw [smul_comm]
        exact Λ.smul_mem r (hv x hx) }
  have hle : I * (I'⁻¹ : FractionalIdeal R⁰ K) ≤ N.map (f.restrictScalars R) := by
    refine Submodule.mul_le.2 fun m hm n hn ↦ ?_
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hm
    refine ⟨n • l, fun x hx ↦ ?_, by simp [mul_comm]⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hmul ▸ Submodule.mul_mem_mul hx hn)
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Λ.smul_mem r hl
  obtain ⟨v, hv, hv1⟩ := Submodule.mem_map.1 (hle (hmul ▸ Submodule.mem_one.2 ⟨1, map_one _⟩))
  exact ⟨v, hv1, hv⟩

/-- The induction behind `Submodule.exists_pseudoBasis`: a finitely generated `R`-submodule of a
finite-dimensional `K`-vector space is `⊕ i, J i • y i` for a `K`-linearly independent family `y`
and nonzero ideals `J i`. -/
private theorem exists_linearIndependent_forall_mem_iff [FiniteDimensional K V]
    (Λ : Submodule R V) (hΛ : Λ.FG) :
    ∃ (m : ℕ) (y : Fin m → V) (J : Fin m → Ideal R), (∀ i, J i ≠ ⊥) ∧ LinearIndependent K y ∧
      ∀ x, x ∈ Λ ↔ ∃ c : Fin m → R, (∀ i, c i ∈ J i) ∧ ∑ i, c i • y i = x := by
  obtain ⟨n, hn⟩ : ∃ n, finrank K (span K (Λ : Set V)) = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing Λ with | _ n ih => ?_
  rcases eq_or_ne Λ ⊥ with rfl | hne
  · exact ⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, linearIndependent_empty_type,
      fun x ↦ by simp [eq_comm]⟩
  -- Split off the image `I` of `Λ` under a functional `f` with `f l₀ = 1` for some `l₀ ∈ Λ`.
  obtain ⟨l₀, hl₀, hl₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hl₀ne
  set I := Λ.map (f.restrictScalars R)
  have hI : I ≠ ⊥ := fun h ↦ by
    simpa [hf] using (Submodule.eq_bot_iff _).1 h _ (mem_map_of_mem (f := f.restrictScalars R) hl₀)
  obtain ⟨v, hv1, hv⟩ := Λ.exists_apply_eq_one_forall_smul_mem f (hΛ.map _) hI
  -- The kernel part `Λ'` has a smaller span, so the induction hypothesis applies to it.
  set Λ' := Λ ⊓ (LinearMap.ker f).restrictScalars R
  have hΛ' : Λ'.FG :=
    have := isNoetherian_of_fg_of_noetherian Λ hΛ
    Submodule.FG.of_le_of_isNoetherian inf_le_left
  have hker : span K (Λ' : Set V) ≤ LinearMap.ker f := span_le.2 fun x hx ↦ hx.2
  have hlt : finrank K (span K (Λ' : Set V)) < n := hn ▸ Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne (span_mono inf_le_left) fun h ↦ by
      exact one_ne_zero (hf.symm.trans (LinearMap.mem_ker.1 (hker (h ▸ subset_span hl₀)))))
  obtain ⟨m, y', J', hJ', hli', hmem'⟩ := ih _ hlt Λ' hΛ' rfl
  -- Write `I` as `a⁻¹ J₀` for an integral ideal `J₀`.
  let I' : FractionalIdeal R⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg (hΛ.map _)⟩
  have hcoe : (I' : Submodule R K) = I := rfl
  obtain ⟨a, J₀, ha, hIeq⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I'
  have hmemI : ∀ t, t ∈ I ↔ ∃ j ∈ J₀, (algebraMap R K a)⁻¹ * algebraMap R K j = t := fun t ↦ by
    rw [← hcoe, FractionalIdeal.mem_coe, hIeq, FractionalIdeal.mem_singleton_mul]
    simp only [FractionalIdeal.mem_coeIdeal]
    grind
  have ha' : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha
  have hJ₀ : J₀ ≠ ⊥ := fun h ↦ hI <| eq_bot_iff.2 fun t ht ↦ by
    obtain ⟨j, hj, rfl⟩ := (hmemI t).1 ht
    rw [h, Ideal.mem_bot] at hj
    simp [hj]
  have hsmul : ∀ j : R, j • (algebraMap R K a)⁻¹ • v =
      ((algebraMap R K a)⁻¹ * algebraMap R K j) • v := fun j ↦ by
    rw [← algebraMap_smul K j, smul_smul, mul_comm]
  -- The new family puts `a⁻¹ v` in front of `y'`.
  refine ⟨m + 1, Fin.cons ((algebraMap R K a)⁻¹ • v) y', Fin.cons J₀ J',
    Fin.cases hJ₀ hJ', hli'.finCons fun hmem ↦ ?_, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · -- `f` vanishes on the span of `y'` but not on `a⁻¹ v`.
    have := ((span_range_eq_span_of_forall_mem_iff hJ' hmem').trans_le hker) hmem
    simp [hv1, ha'] at this
  · -- Decompose `x = (f x) • v + (x - (f x) • v)` with the second summand in `Λ'`.
    have ht : f x ∈ I := Submodule.mem_map_of_mem (f := f.restrictScalars R) hx
    obtain ⟨j, hj, hjt⟩ := (hmemI _).1 ht
    obtain ⟨c', hc', hc'x⟩ := (hmem' (x - f x • v)).1
      ⟨Λ.sub_mem hx (hv _ ht), by simp [hv1]⟩
    refine ⟨Fin.cons j c', Fin.cases hj hc', ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hc'x, hsmul, hjt]
    abel
  · rintro ⟨c, hc, rfl⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    refine Λ.add_mem ?_ ((hmem' _).2 ⟨fun i ↦ c i.succ, fun i ↦ hc i.succ, rfl⟩).1
    rw [hsmul]
    exact hv _ ((hmemI _).2 ⟨c 0, hc 0, rfl⟩)

/-- **Pseudo-bases** over a Dedekind domain. Let `R` be a Dedekind domain with fraction field
`K`. A finitely generated `R`-submodule `Λ` of a `K`-vector space `V` spanning `V` is
`⊕ i, J i • b i` for a `K`-basis `b` of `V` and nonzero ideals `J i` of `R`: a vector lies in `Λ`
exactly when its `i`-th coordinate in `b` lies in `J i` for every `i`. The basis may be indexed by
any finite type of cardinality `finrank K V`. -/
theorem exists_pseudoBasis {ι : Type*} [Finite ι] (Λ : Submodule R V) (hΛ : Λ.FG)
    (hspan : span K (Λ : Set V) = ⊤) (hι : Nat.card ι = finrank K V) :
    ∃ (b : Basis ι K V) (J : ι → Ideal R), (∀ i, J i ≠ ⊥) ∧
      ∀ x, x ∈ Λ ↔ ∀ i, b.repr x i ∈ IsLocalization.coeSubmodule K (J i) := by
  have : FiniteDimensional K V := by
    obtain ⟨s, hs⟩ := hΛ
    exact Module.finite_def.2 ⟨s, by rw [← span_span_of_tower R, hs, hspan]⟩
  obtain ⟨m, y, J, hJ, hli, hmem⟩ := exists_linearIndependent_forall_mem_iff (K := K) Λ hΛ
  have hy : ⊤ ≤ span K (Set.range y) :=
    ((span_range_eq_span_of_forall_mem_iff hJ hmem).trans hspan).ge
  let B := Basis.mk hli hy
  have hBy : ∀ i, B i = y i := Basis.mk_apply hli hy
  have hB : ∀ x, x ∈ Λ ↔ ∀ j, B.repr x j ∈ IsLocalization.coeSubmodule K (J j) := fun x ↦ by
    refine (hmem x).trans ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨c, hc, rfl⟩ j
      have : ∑ i, c i • y i = ∑ i, (algebraMap R K ∘ c) i • B i := by
        simp [hBy, algebraMap_smul]
      rw [this, B.repr_sum_self]
      exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨c j, hc j, rfl⟩
    · choose c hc hcx using fun j ↦ (IsLocalization.mem_coeSubmodule _ _).1 (h j)
      refine ⟨c, hc, ?_⟩
      conv_rhs => rw [← B.sum_repr x]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [← hcx i, algebraMap_smul, hBy]
  have hm : Nat.card ι = m := hι.trans (by simp [finrank_eq_card_basis B])
  let e := Finite.equivFinOfCardEq hm
  refine ⟨B.reindex e.symm, J ∘ e, fun i ↦ hJ _, fun x ↦ ?_⟩
  simp only [Basis.repr_reindex_apply, Equiv.symm_symm, Function.comp_apply, hB x]
  exact e.surjective.forall

end Submodule
