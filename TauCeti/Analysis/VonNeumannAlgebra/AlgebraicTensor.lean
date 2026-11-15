/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.Star.Subalgebra
public import TauCeti.Analysis.VonNeumannAlgebra.Density
public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import TauCeti.Analysis.InnerProductSpace.RankOne

/-!
# Algebraic tensor products of a factor and its commutant

When a concrete von Neumann algebra `M` on `H` has trivial center (`M ⊓ M.commutant = ⊥`, as holds
for every factor), `M` and `M.commutant` are algebraically linearly disjoint inside `H →L[ℂ] H`:

* **Orbit projections** (`VonNeumannAlgebra.starProjection_topologicalClosure_span_mem_commutant`,
  `VonNeumannAlgebra.starProjection_topologicalClosure_span_mem`): for any `S : Set H`, the
  orthogonal projection onto the closed span of `{x v | x ∈ M, v ∈ S}` lies in `M.commutant`, and
  also in `M` whenever `S` is `M.commutant`-invariant.
* **Nonzero product theorem**
  (`VonNeumannAlgebra.eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant`): if `a ∈ M`
  and `b ∈ M.commutant` satisfy `a * b = 0`, then `a = 0` or `b = 0`. The closed subspace spanned
  by `{x (a ξ) | x ∈ M, ξ ∈ H}` is invariant under both `M` and `M.commutant`, so its orthogonal
  projection lies in `M ⊓ M.commutant = ⊥` and is therefore `0` (forcing `a = 0`) or `1` (forcing
  `b = 0` by density).
* **Linear independence of commuting products** (`VonNeumannAlgebra.eq_zero_of_sum_mul_eq_zero`):
  if `w i ∈ M.commutant` are `ℂ`-linearly independent and `v i ∈ M` satisfy `∑ i, v i * w i = 0`,
  then every `v i` is `0`. Induction on the support reduces to the sandwich identity
  `u * x * v = v * x * u` for all `x ∈ M`, which extends by strong-operator density of
  `M ⊔ M.commutant = ⊤` (`VonNeumannAlgebra.eq_of_mem_adjoin`) to all bounded operators
  `T : H →L[ℂ] H`; evaluating against normalized rank-one operators (`TauCeti.rankOneDivNormSq`)
  forces `v` to be a scalar multiple of `u`.
* **Multiplication equivalences** (`VonNeumannAlgebra.mulLinearEquiv`,
  `VonNeumannAlgebra.mulStarAlgEquiv`): for arbitrary `ℂ`-linear subspaces `V ≤ M` and
  `W ≤ M.commutant` (with no finite-dimensionality assumption), multiplication induces a linear
  equivalence `V ⊗[ℂ] W ≃ₗ[ℂ] ↥(V * W)` onto the linear span `V * W`; when `A ≤ M` and
  `B ≤ M.commutant` are unital `⋆`-subalgebras, multiplication induces a unital `⋆`-algebra
  equivalence `A ⊗[ℂ] B ≃⋆ₐ[ℂ] ↥(A ⊔ B)`, where
  `(A ⊔ B).toSubmodule = A.toSubmodule * B.toSubmodule`.

## References

* F. J. Murray and J. von Neumann, *On rings of operators*, Ann. of Math. (2) **37** (1936),
  116–229, Lemma 3.1.1 and Theorem III.
* J. Dixmier, *Von Neumann Algebras*, North-Holland, 1981, Part I, Chapter 2, §2, Proposition 4,
  Corollary 2.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Academic
  Press, 1983, Proposition 5.5.4.
-/

public section

open scoped InnerProductSpace TensorProduct

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Orbit projections -/

/-- For any set of vectors `S`, the orthogonal projection onto the closed span of the `M`-orbit
`{x v | x ∈ M, v ∈ S}` lies in `M.commutant`. -/
theorem starProjection_topologicalClosure_span_mem_commutant (M : VonNeumannAlgebra H)
    (S : Set H) :
    (Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}).topologicalClosure.starProjection ∈
      M.commutant := by
  set L₀ := Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}
  set L := L₀.topologicalClosure
  rw [IsStarProjection.mem_iff (isStarProjection_starProjection (U := L)) M.commutant,
    M.commutant_commutant, L.range_starProjection]
  intro z hz
  rw [Module.End.mem_invtSubmodule]
  refine Submodule.topologicalClosure_minimal _ ?_
    (L₀.isClosed_topologicalClosure.preimage z.continuous)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  refine Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨z * x, M.mul_mem hz hx, v, hv, ?_⟩)
  exact mul_apply_eq_comp z x v

/-- If `S : Set H` is invariant under every operator in `M.commutant`, then the orthogonal
projection onto the closed span of `{x v | x ∈ M, v ∈ S}` lies in `M`. -/
theorem starProjection_topologicalClosure_span_mem (M : VonNeumannAlgebra H) {S : Set H}
    (hS : ∀ y ∈ M.commutant, Set.MapsTo y S S) :
    (Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}).topologicalClosure.starProjection ∈
      M := by
  set L₀ := Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ S, x v = w}
  set L := L₀.topologicalClosure
  rw [IsStarProjection.mem_iff (isStarProjection_starProjection (U := L)) M,
    L.range_starProjection]
  intro y hy
  rw [Module.End.mem_invtSubmodule]
  refine Submodule.topologicalClosure_minimal _ ?_
    (L₀.isClosed_topologicalClosure.preimage y.continuous)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  have hcomm : x * y = y * x := mem_commutant_iff.mp hy x hx
  refine Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨x, hx, y v, hS y hy hv, ?_⟩)
  calc
    x (y v) = (x * y) v := (mul_apply_eq_comp x y v).symm
    _ = (y * x) v := by rw [hcomm]
    _ = y (x v) := mul_apply_eq_comp y x v

/-! ### Nonzero products between `M` and `M.commutant` -/

/-- **Nonzero product theorem.** If `M` has trivial center (`M ⊓ M.commutant = ⊥`), `a ∈ M`, and
`b ∈ M.commutant` satisfy `a * b = 0`, then `a = 0` or `b = 0`. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant {M : VonNeumannAlgebra H}
    (hM : M ⊓ M.commutant = ⊥) {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M.commutant)
    (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  -- The closed span `L` of `{x v | x ∈ M, v ∈ range a}` reduces both `M` and `M.commutant`.
  set L₀ : Submodule ℂ H := Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ Set.range a, x v = w}
  set L : Submodule ℂ H := L₀.topologicalClosure
  have hrange : ∀ w ∈ M.commutant, Set.MapsTo w (Set.range a) (Set.range a) := by
    rintro w hw _ ⟨ξ, rfl⟩
    have hcomm : a * w = w * a := mem_commutant_iff.mp hw a ha
    exact ⟨w ξ, (mul_apply_eq_comp a w ξ).symm.trans
      ((DFunLike.congr_fun hcomm ξ).trans (mul_apply_eq_comp w a ξ))⟩
  have hp_bot : L.starProjection ∈ (⊥ : VonNeumannAlgebra H) :=
    hM ▸ mem_inf.mpr
      ⟨M.starProjection_topologicalClosure_span_mem hrange,
        M.starProjection_topologicalClosure_span_mem_commutant (Set.range a)⟩
  -- Since `L.starProjection` is an idempotent in `⊥`, it is `0` or `1`.
  rcases eq_zero_or_eq_one_of_isIdempotentElem_of_mem_bot L.isIdempotentElem_starProjection
      hp_bot with hp0 | hp1
  · left
    ext ξ
    have hξ : a ξ ∈ L := Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨1, M.one_mem, a ξ, ⟨ξ, rfl⟩, one_apply_eq_self _⟩)
    rw [← L.starProjection_eq_self_iff.mpr hξ, hp0, zero_apply, zero_apply]
  · right
    have hker : L ≤ LinearMap.ker b.toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage b.continuous)
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, _, ⟨ξ, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      have hxb : x * b = b * x := mem_commutant_iff.mp hb x hx
      have hab' : b * a = 0 := (mem_commutant_iff.mp hb a ha).symm.trans hab
      calc
        b (x (a ξ)) = ((b * x) * a) ξ := by simp [mul_assoc]
        _ = (x * (b * a)) ξ := by rw [← hxb, mul_assoc]
        _ = 0 := by simp [hab']
    ext v
    have hvL : v ∈ L := by
      rw [← L.starProjection_eq_self_iff, hp1, one_apply_eq_self]
    exact hker hvL

/-- In a von Neumann algebra with trivial center, a product `a * b` with `a ∈ M` and
`b ∈ M.commutant` vanishes if and only if `a = 0` or `b = 0`. -/
theorem mul_eq_zero_iff_of_mem_commutant {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M.commutant) :
    a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM ha hb, by rintro (rfl | rfl) <;> simp⟩

/-- In a von Neumann algebra with trivial center, the product of nonzero `a ∈ M` and
`b ∈ M.commutant` is nonzero. -/
theorem mul_ne_zero_of_mem_commutant {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M.commutant) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    a * b ≠ 0 :=
  fun hab => (eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM ha hb hab).elim ha0 hb0

/-! ### Linear disjointness of `M` and `M.commutant` -/

/-- If `M ⊓ M.commutant = ⊥` and `u, v ∈ M` satisfy `u * x * v = v * x * u` for all `x ∈ M` with
`u ≠ 0`, then `v` is a complex scalar multiple of `u`. -/
private theorem exists_smul_eq_of_forall_mul_mul_eq {M : VonNeumannAlgebra H}
    (hM : M ⊓ M.commutant = ⊥) {u v : H →L[ℂ] H} (hu : u ∈ M) (hv : v ∈ M) (hu0 : u ≠ 0)
    (huv : ∀ x ∈ M, u * x * v = v * x * u) : ∃ c : ℂ, v = c • u := by
  -- Extend `u * s * v = v * s * u` from `x ∈ M` to the `⋆`-algebra generated by `M ∪ M.commutant`.
  have hcomm : ∀ a ∈ M.toStarSubalgebra, ∀ b ∈ M.commutant.toStarSubalgebra, Commute a b :=
    fun a ha b hb => mem_commutant_iff.mp hb a ha
  have hP : ∀ p ∈ M.toStarSubalgebra.toSubmodule * M.commutant.toStarSubalgebra.toSubmodule,
      u * p * v = v * p * u := fun p hp =>
    Submodule.mul_induction_on hp
      (fun x hx y hy => by
        have hyu : y * u = u * y := (mem_commutant_iff.mp hy u hu).symm
        have hyv : y * v = v * y := (mem_commutant_iff.mp hy v hv).symm
        calc
          u * (x * y) * v = u * x * (y * v) := by simp only [mul_assoc]
          _ = (u * x * v) * y := by rw [hyv]; simp only [mul_assoc]
          _ = (v * x * u) * y := by rw [huv x hx]
          _ = v * x * (u * y) := by simp only [mul_assoc]
          _ = v * x * (y * u) := by rw [← hyu]
          _ = v * (x * y) * u := by simp only [mul_assoc])
      fun p₁ p₂ hp₁ hp₂ => by rw [mul_add, add_mul, hp₁, hp₂, mul_add, add_mul]
  let s : Set (H →L[ℂ] H) := (M : Set (H →L[ℂ] H)) ∪ M.commutant
  have hadj_le : StarAlgebra.adjoin ℂ s ≤ M.toStarSubalgebra ⊔ M.commutant.toStarSubalgebra := by
    refine StarAlgebra.adjoin_le ?_
    rintro z (hz | hz)
    · exact StarSubalgebra.mem_sup_left hz
    · exact StarSubalgebra.mem_sup_right hz
  have hadj_top : adjoin s = ⊤ := by
    rw [← sup_eq_adjoin, sup_commutant_eq_top_iff]
    exact hM
  -- By strong-operator density (`eq_of_mem_adjoin`), the sandwich identity holds for all `T`.
  have hB (T : H →L[ℂ] H) (ξ : H) : (u * T * v) ξ = (v * T * u) ξ :=
    eq_of_mem_adjoin (hadj_top ▸ mem_top : T ∈ adjoin s) ![v ξ, u ξ]
      (u.continuous.comp (continuous_apply 0)) (v.continuous.comp (continuous_apply 1))
      fun t ht => by
        have htP : t ∈ M.toStarSubalgebra.toSubmodule *
            M.commutant.toStarSubalgebra.toSubmodule := by
          rw [← StarSubalgebra.toSubmodule_sup_of_commute hcomm]
          exact hadj_le ht
        simpa using DFunLike.congr_fun (hP t htP) ξ
  -- Evaluate on normalized rank-one operators sending `u ξ₀ ↦ ξ`.
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : H, u ξ₀ ≠ 0 := by
    by_contra! hall
    exact hu0 (ContinuousLinearMap.ext hall)
  refine ⟨((‖u ξ₀‖ : ℂ) ^ 2)⁻¹ * ⟪u ξ₀, v ξ₀⟫_ℂ, ContinuousLinearMap.ext fun ξ => ?_⟩
  have hT := hB (TauCeti.rankOneDivNormSq ℂ ξ (u ξ₀)) ξ₀
  simpa [mul_apply_eq_comp, TauCeti.rankOneDivNormSq_apply_self ξ hξ₀,
    TauCeti.rankOneDivNormSq_apply] using hT.symm

/-- Finite-tuple form of linear disjointness: if `w : Fin n → H →L[ℂ] H` is a linearly independent
tuple in `M.commutant` and `v : Fin n → H →L[ℂ] H` is a tuple in `M` with `∑ i, v i * w i = 0`,
then every `v i = 0`. -/
private theorem eq_zero_of_sum_fin_mul_eq_zero {M : VonNeumannAlgebra H}
    (hM : M ⊓ M.commutant = ⊥) :
    ∀ {n : ℕ} {v w : Fin n → H →L[ℂ] H}, (∀ i, v i ∈ M) → (∀ i, w i ∈ M.commutant) →
      LinearIndependent ℂ w → ∑ i, v i * w i = 0 → ∀ i, v i = 0
  | 0, _, _, _, _, _, _, i => i.elim0
  | n + 1, v, w, hv, hw, hli, hsum, i => by
    by_cases hv0 : v 0 = 0
    · have hsum' : ∑ j : Fin n, v j.succ * w j.succ = 0 := by
        simpa [Fin.sum_univ_succ, hv0] using hsum
      have hall : ∀ j : Fin n, v j.succ = 0 :=
        eq_zero_of_sum_fin_mul_eq_zero hM (fun j => hv j.succ) (fun j => hw j.succ)
          (hli.comp Fin.succ (Fin.succ_injective n)) hsum'
      exact Fin.cases hv0 hall i
    · -- Eliminate the `0`-th term to deduce `v 0 * x * v j.succ = v j.succ * x * v 0` for `x ∈ M`.
      have hprop : ∀ j : Fin n, ∃ c : ℂ, v j.succ = c • v 0 := by
        have hsand : ∀ (x : H →L[ℂ] H), x ∈ M →
            ∀ j : Fin n, v 0 * x * v j.succ = v j.succ * x * v 0 := by
          intro x hx
          have hleft : ∑ k : Fin (n + 1), (v 0 * x * v k) * w k = 0 := by
            have := congrArg ((v 0 * x) * ·) hsum
            simpa only [Finset.mul_sum, mul_zero, mul_assoc] using this
          have hright : ∑ k : Fin (n + 1), (v k * x * v 0) * w k = 0 := by
            have := congrArg (· * (x * v 0)) hsum
            rw [Finset.sum_mul, zero_mul] at this
            refine (Finset.sum_congr rfl fun k _ => ?_).trans this
            have hcomm : (x * v 0) * w k = w k * (x * v 0) :=
              mem_commutant_iff.mp (hw k) (x * v 0) (M.mul_mem hx (hv 0))
            calc
              (v k * x * v 0) * w k = v k * ((x * v 0) * w k) := by simp only [mul_assoc]
              _ = v k * (w k * (x * v 0)) := by rw [hcomm]
              _ = v k * w k * (x * v 0) := by simp only [mul_assoc]
          have hdiff : ∑ j : Fin n, (v 0 * x * v j.succ - v j.succ * x * v 0) * w j.succ = 0 := by
            have hsub := sub_eq_zero.mpr (hleft.trans hright.symm)
            rw [← Finset.sum_sub_distrib] at hsub
            simpa only [Fin.sum_univ_succ, sub_mul, sub_self, zero_add] using hsub
          have hzero := eq_zero_of_sum_fin_mul_eq_zero hM
            (fun j => sub_mem (M.mul_mem (M.mul_mem (hv 0) hx) (hv j.succ))
              (M.mul_mem (M.mul_mem (hv j.succ) hx) (hv 0)))
            (fun j => hw j.succ) (hli.comp Fin.succ (Fin.succ_injective n)) hdiff
          exact fun j => sub_eq_zero.mp (hzero j)
        exact fun j => exists_smul_eq_of_forall_mul_mul_eq hM (hv 0) (hv j.succ) hv0
          (fun x hx => hsand x hx j)
      choose c hc using hprop
      have hw_comb : w 0 + ∑ j : Fin n, c j • w j.succ ∈ M.commutant :=
        add_mem (hw 0) (sum_mem fun j _ => SMulMemClass.smul_mem (c j) (hw j.succ))
      have hprod : v 0 * (w 0 + ∑ j : Fin n, c j • w j.succ) = 0 := by
        calc
          v 0 * (w 0 + ∑ j : Fin n, c j • w j.succ)
              = v 0 * w 0 + ∑ j : Fin n, (c j • v 0) * w j.succ := by
                rw [mul_add, Finset.mul_sum]
                congr 1
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [mul_smul_comm, smul_mul_assoc]
          _ = v 0 * w 0 + ∑ j : Fin n, v j.succ * w j.succ := by
                simp_rw [← hc]
          _ = ∑ k : Fin (n + 1), v k * w k := (Fin.sum_univ_succ fun k => v k * w k).symm
          _ = 0 := hsum
      have hw0 : w 0 + ∑ j : Fin n, c j • w j.succ = 0 :=
        (eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM (hv 0) hw_comb hprod).resolve_left
          hv0
      let coeff : Fin (n + 1) → ℂ := @Fin.cons n (fun _ => ℂ) 1 c
      have hdep : ∑ k : Fin (n + 1), coeff k • w k = 0 := by
        simpa [coeff, Fin.sum_univ_succ] using hw0
      exact False.elim (one_ne_zero (Fintype.linearIndependent_iff.mp hli coeff hdep 0))

/-- **Linear independence of commuting products.** If `M ⊓ M.commutant = ⊥`, `w` is `ℂ`-linearly
independent on `s` with values in `M.commutant`, and `v` takes values in `M` with
`∑ i ∈ s, v i * w i = 0`, then `v i = 0` for all `i ∈ s`. -/
theorem eq_zero_of_sum_mul_eq_zero {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {ι : Type*} {s : Finset ι} {v w : ι → H →L[ℂ] H} (hv : ∀ i ∈ s, v i ∈ M)
    (hw : ∀ i ∈ s, w i ∈ M.commutant) (hli : LinearIndependent ℂ (fun i : s => w i))
    (hsum : ∑ i ∈ s, v i * w i = 0) : ∀ i ∈ s, v i = 0 := by
  let e : Fin s.card ≃ s := s.equivFin.symm
  have hsum' : ∑ k : Fin s.card, v (e k) * w (e k) = 0 := by
    calc
      ∑ k : Fin s.card, v (e k) * w (e k) = ∑ x : s, v x * w x :=
        e.sum_comp (fun x : s => v x * w x)
      _ = ∑ i ∈ s, v i * w i := Finset.sum_coe_sort s (fun i => v i * w i)
      _ = 0 := hsum
  have hall := eq_zero_of_sum_fin_mul_eq_zero hM (fun k => hv (e k) (e k).2)
    (fun k => hw (e k) (e k).2) (hli.comp e e.injective) hsum'
  intro i hi
  simpa using hall (e.symm ⟨i, hi⟩)

/-! ### Algebraic tensor product multiplication equivalences -/

/-- If `M ⊓ M.commutant = ⊥` and `V ≤ M`, `W ≤ M.commutant` are `ℂ`-linear subspaces of operators,
then the multiplication map `V ⊗[ℂ] W →ₗ[ℂ] (H →L[ℂ] H)` is injective. -/
theorem mul_tensorProduct_injective {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {V W : Submodule ℂ (H →L[ℂ] H)} (hV : (V : Set (H →L[ℂ] H)) ⊆ M)
    (hW : (W : Set (H →L[ℂ] H)) ⊆ M.commutant) :
    Function.Injective ((LinearMap.mul' ℂ (H →L[ℂ] H)).comp
      (TensorProduct.map V.subtype W.subtype)) := by
  refine injective_iff_map_eq_zero _ |>.mpr fun t ht => ?_
  let ℬ := Module.Basis.ofVectorSpace ℂ W
  obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ t
  have hsum : ∑ i ∈ b.support, ((b i : V) : H →L[ℂ] H) * ((ℬ i : W) : H →L[ℂ] H) = 0 := by
    simpa [Finsupp.sum] using ht
  have hliW : LinearIndependent ℂ (fun i => ((ℬ i : W) : H →L[ℂ] H)) :=
    ℬ.linearIndependent.map' W.subtype W.ker_subtype
  have hzero := eq_zero_of_sum_mul_eq_zero hM (fun i _ => hV (b i).2) (fun i _ => hW (ℬ i).2)
    (hliW.comp Subtype.val Subtype.val_injective) hsum
  have hb0 : b = 0 := Finsupp.ext fun i => by
    by_cases hi : i ∈ b.support
    · exact Subtype.ext (hzero i hi)
    · exact Finsupp.notMem_support_iff.mp hi
  simp [hb0]

/-- **Subspace multiplication equivalence.** When `M ⊓ M.commutant = ⊥`, multiplication induces a
`ℂ`-linear isomorphism from the algebraic tensor product `V ⊗[ℂ] W` of any subspaces `V ≤ M` and
`W ≤ M.commutant` onto the product submodule `V * W` (the linear span of `{v * w | v ∈ V, w ∈ W}`).
No finite-dimensionality assumption on `V` or `W` is required. -/
noncomputable def mulLinearEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {V W : Submodule ℂ (H →L[ℂ] H)} (hV : (V : Set (H →L[ℂ] H)) ⊆ M)
    (hW : (W : Set (H →L[ℂ] H)) ⊆ M.commutant) :
    V ⊗[ℂ] W ≃ₗ[ℂ] ↥(V * W) :=
  let μ := ((LinearMap.mul' ℂ (H →L[ℂ] H)).comp (TensorProduct.map V.subtype W.subtype)).codRestrict
    (V * W) fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul v w => exact Submodule.mul_mem_mul v.2 w.2
      | add x y hx hy => rw [map_add]; exact (V * W).add_mem hx hy
  LinearEquiv.ofBijective μ
    (⟨fun _ _ hxy => mul_tensorProduct_injective hM hV hW (congrArg Subtype.val hxy),
      fun ⟨z, hz⟩ =>
        Submodule.mul_induction_on' (C := fun z hz => ∃ t : V ⊗[ℂ] W, μ t = ⟨z, hz⟩)
          (fun v hv w hw => ⟨(⟨v, hv⟩ : V) ⊗ₜ[ℂ] (⟨w, hw⟩ : W), Subtype.ext (by simp [μ])⟩)
          (fun _ _ _ _ ⟨tx, htx⟩ ⟨ty, hty⟩ =>
            ⟨tx + ty, Subtype.ext (by simp [map_add, congrArg Subtype.val htx,
              congrArg Subtype.val hty])⟩) hz⟩ : Function.Bijective μ)

/-- `mulLinearEquiv` sends a pure tensor `v ⊗ₜ w` to the operator product `v * w`. -/
@[simp]
theorem coe_mulLinearEquiv_tmul {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {V W : Submodule ℂ (H →L[ℂ] H)} (hV : (V : Set (H →L[ℂ] H)) ⊆ M)
    (hW : (W : Set (H →L[ℂ] H)) ⊆ M.commutant) (v : V) (w : W) :
    (mulLinearEquiv hM hV hW (v ⊗ₜ[ℂ] w) : H →L[ℂ] H) = (v : H →L[ℂ] H) * w := by
  rw [mulLinearEquiv]
  exact (congrArg Subtype.val (LinearEquiv.ofBijective_apply _ (v ⊗ₜ[ℂ] w))).trans (by simp)

/-- For unital `⋆`-subalgebras `A ≤ M` and `B ≤ M.commutant`, the `⋆`-subalgebra `A ⊔ B` they
generate has underlying submodule `A.toSubmodule * B.toSubmodule` (the linear span `AB`). -/
theorem toSubmodule_sup_eq_mul {M : VonNeumannAlgebra H}
    {A B : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : (A : Set (H →L[ℂ] H)) ⊆ M)
    (hB : (B : Set (H →L[ℂ] H)) ⊆ M.commutant) :
    (A ⊔ B).toSubmodule = A.toSubmodule * B.toSubmodule :=
  StarSubalgebra.toSubmodule_sup_of_commute fun a ha _ hb =>
    mem_commutant_iff.mp (hB hb) a (hA ha)

/-- **Star-subalgebra multiplication equivalence.** When `M ⊓ M.commutant = ⊥`, multiplication
induces a unital `⋆`-algebra isomorphism from the algebraic tensor product `A ⊗[ℂ] B` of any unital
`⋆`-subalgebras `A ≤ M` and `B ≤ M.commutant` onto `A ⊔ B` (whose underlying vector space is the
linear span `A.toSubmodule * B.toSubmodule` by `VonNeumannAlgebra.toSubmodule_sup_eq_mul`). -/
noncomputable def mulStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {A B : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : (A : Set (H →L[ℂ] H)) ⊆ M)
    (hB : (B : Set (H →L[ℂ] H)) ⊆ M.commutant) :
    A ⊗[ℂ] B ≃⋆ₐ[ℂ] ↥(A ⊔ B) :=
  let lin : A ⊗[ℂ] B ≃ₗ[ℂ] ↥(A ⊔ B) :=
    (mulLinearEquiv hM (V := A.toSubmodule) (W := B.toSubmodule) hA hB).trans
      (LinearEquiv.ofEq _ _ (toSubmodule_sup_eq_mul hA hB).symm)
  have hlin (a : A) (b : B) : ((lin (a ⊗ₜ[ℂ] b) : ↥(A ⊔ B)) : H →L[ℂ] H) =
      (a : H →L[ℂ] H) * b := by
    rw [LinearEquiv.trans_apply]
    exact (LinearEquiv.coe_ofEq_apply _ _).trans
      (coe_mulLinearEquiv_tmul hM hA hB ⟨a.1, a.2⟩ ⟨b.1, b.2⟩)
  let alg : A ⊗[ℂ] B ≃ₐ[ℂ] ↥(A ⊔ B) :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct lin
      (fun a₁ a₂ b₁ b₂ => Subtype.ext <| by
        have hba : (b₁ : H →L[ℂ] H) * a₂ = (a₂ : H →L[ℂ] H) * b₁ :=
          (mem_commutant_iff.mp (hB b₁.2) a₂ (hA a₂.2)).symm
        rw [MulMemClass.coe_mul, hlin, hlin, hlin, MulMemClass.coe_mul, MulMemClass.coe_mul]
        calc
          ((a₁ : H →L[ℂ] H) * a₂) * ((b₁ : H →L[ℂ] H) * b₂)
              = (a₁ : H →L[ℂ] H) * (a₂ * b₁) * b₂ := by simp only [mul_assoc]
          _ = (a₁ : H →L[ℂ] H) * (b₁ * a₂) * b₂ := by rw [← hba]
          _ = ((a₁ : H →L[ℂ] H) * b₁) * ((a₂ : H →L[ℂ] H) * b₂) := by simp only [mul_assoc])
      (Subtype.ext <| by
        rw [hlin, OneMemClass.coe_one, OneMemClass.coe_one, OneMemClass.coe_one, mul_one])
  StarAlgEquiv.ofAlgEquiv alg fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      apply Subtype.ext
      have hcomm : (star a : H →L[ℂ] H) * (star b : H →L[ℂ] H) =
          (star b : H →L[ℂ] H) * (star a : H →L[ℂ] H) :=
        mem_commutant_iff.mp (hB (star b).2) (star a) (hA (star a).2)
      rw [TensorProduct.star_tmul,
        Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply,
        StarMemClass.coe_star, Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply,
        hlin, hlin, StarMemClass.coe_star, StarMemClass.coe_star, star_mul, ← hcomm]
    | add x y hx hy =>
      rw [star_add, map_add, hx, hy, map_add, star_add]

/-- `mulStarAlgEquiv` sends a pure tensor `a ⊗ₜ b` to the operator product `a * b`. -/
@[simp]
theorem coe_mulStarAlgEquiv_tmul {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {A B : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : (A : Set (H →L[ℂ] H)) ⊆ M)
    (hB : (B : Set (H →L[ℂ] H)) ⊆ M.commutant) (a : A) (b : B) :
    (mulStarAlgEquiv hM hA hB (a ⊗ₜ[ℂ] b) : H →L[ℂ] H) = (a : H →L[ℂ] H) * b := by
  rw [mulStarAlgEquiv, StarAlgEquiv.ofAlgEquiv_apply,
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply, LinearEquiv.trans_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans
    (coe_mulLinearEquiv_tmul hM hA hB ⟨a.1, a.2⟩ ⟨b.1, b.2⟩)

/-- When `M ⊓ M.commutant = ⊥`, multiplication gives a unital `⋆`-algebra equivalence from
`M ⊗[ℂ] M.commutant` onto `M.toStarSubalgebra ⊔ M.commutant.toStarSubalgebra`. -/
noncomputable def commutantMulStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥) :
    M.toStarSubalgebra ⊗[ℂ] M.commutant.toStarSubalgebra ≃⋆ₐ[ℂ]
      ↥(M.toStarSubalgebra ⊔ M.commutant.toStarSubalgebra) :=
  mulStarAlgEquiv hM Set.Subset.rfl Set.Subset.rfl

/-- `commutantMulStarAlgEquiv` sends a pure tensor `x ⊗ₜ y` to the operator product `x * y`. -/
@[simp]
theorem coe_commutantMulStarAlgEquiv_tmul {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (x : M.toStarSubalgebra) (y : M.commutant.toStarSubalgebra) :
    (commutantMulStarAlgEquiv hM (x ⊗ₜ[ℂ] y) : H →L[ℂ] H) = (x : H →L[ℂ] H) * y :=
  coe_mulStarAlgEquiv_tmul hM Set.Subset.rfl Set.Subset.rfl x y

end VonNeumannAlgebra
