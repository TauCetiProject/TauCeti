/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Period
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Colouring
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.Matrix.Trace.Pow
import TauCeti.LinearAlgebra.PiTensorProduct.Basis.Basic
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Traces of endomorphisms on indexed tensor products

This file computes the trace of diagonal and permutation-twisted endomorphisms on finite indexed
tensor products `⨂[R] i : ι, M i` and `⨂[R] _ : ι, M` of free modules over a commutative semiring
`R`, without requiring finite-rank hypotheses on the factors.

For the pure permutation of tensor factors of a free module of rank `N`, the trace is `N ^ c(σ)`,
where `c(σ) = Multiset.card σ.fullCycleType` is the number of cycles of `σ`, fixed points
included. In the basis of pure tensors `e_p = ⨂ᵢ e_{p i}`, indexed by the functions `p` from `ι` to
the `N` indices of a basis of `M`, the permutation sends `e_p` to `e_{p ∘ σ⁻¹}`, so its trace is the
number of `p` constant on the cycles of `σ` (`Equiv.Perm.card_invariantColouring`).

## Main results

* `LinearMap.trace_piTensorProduct_map`: the trace of `PiTensorProduct.map f` is the product of the
  traces of the factor endomorphisms `f i`.
* `LinearMap.sum_prod_coords_eq_sum_prod_orbit_coords`: splits the cyclic coordinate sum of
  matrices over the orbits of a permutation into a product of orbit-wise cyclic path traces.
* `LinearMap.trace_piTensorProduct_map_comp_reindex_eq_prod_trace_inv_orbits`: the trace of
  `(PiTensorProduct.map f).comp (PiTensorProduct.reindex R (fun _ ↦ M) σ⁻¹).toLinearMap` as a
  product over `⟨σ⟩`-orbits.
* `LinearMap.trace_piTensorProduct_map_comp_reindex`: the trace of
  `(PiTensorProduct.map f).comp (PiTensorProduct.reindex R (fun _ ↦ M) σ).toLinearMap` as a
  product over `⟨σ⟩`-orbits using inverse powers `σ⁻¹ ^ (t : ℕ) • ω.out`.
* `PiTensorProduct.trace_reindex`: **the trace of a permutation of tensor factors** of a free
  module of finite rank `N` is `N ^ c(σ)`.
-/

public section

namespace LinearMap

open PiTensorProduct Module
open scoped TensorProduct

section TraceMap

private theorem trace_eq_zero_of_subsingleton {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Subsingleton M] (f : M →ₗ[R] M) : LinearMap.trace R M f = 0 := by
  rw [Subsingleton.elim f 0, map_zero]

private theorem not_finite_piTensorProduct_of_infinite {R ι : Type*} [CommSemiring R]
    [Finite ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {I : ι → Type*} (b : ∀ i, Basis (I i) R (M i)) [Nontrivial R] (hinf : Infinite (∀ i, I i)) :
    ¬Module.Finite R (⨂[R] i, M i) := fun h ↦
  hinf.not_finite ((Module.finite_finsupp_self_iff.mp
    ((Module.Finite.equiv_iff (Basis.piTensorProduct b).repr).mp h)).resolve_left
      (not_subsingleton R))

private theorem infinite_basisIndex_of_not_finite {R I M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (b : Basis I R M)
    (hfin : ¬Module.Finite R M) : Infinite I :=
  not_finite_iff_infinite.mp fun _ ↦
    hfin ((Module.Finite.equiv_iff b.repr).mpr (Module.finite_finsupp_self_iff.mpr (Or.inr ‹_›)))

private theorem trace_piTensorProduct_map_eq_zero_of_not_finite {R ι : Type*} [CommSemiring R]
    [Fintype ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] (f : ∀ i, M i →ₗ[R] M i) {i₀ : ι}
    (hfin : ¬Module.Finite R (M i₀)) :
    LinearMap.trace R (⨂[R] i, M i) (PiTensorProduct.map f) =
      ∏ i, LinearMap.trace R (M i) (f i) := by
  classical
  rcases subsingleton_or_nontrivial R with _hR | _hR
  · exact Subsingleton.elim _ _
  let b := fun i ↦ Module.Free.chooseBasis R (M i)
  let I := fun i ↦ Module.Free.ChooseBasisIndex R (M i)
  by_cases hemp : ∃ i₁, IsEmpty (I i₁)
  · obtain ⟨i₁, hi₁⟩ := hemp
    have : Subsingleton (M i₁) := ((b i₁).repr.toEquiv.subsingleton_congr).mpr inferInstance
    have : IsEmpty (∀ i, I i) := ⟨fun g ↦ hi₁.false (g i₁)⟩
    have : Subsingleton (⨂[R] i, M i) :=
      ((Basis.piTensorProduct b).repr.toEquiv.subsingleton_congr).mpr inferInstance
    rw [trace_eq_zero_of_subsingleton,
      Finset.prod_eq_zero (Finset.mem_univ i₁) (trace_eq_zero_of_subsingleton (f i₁))]
  push Not at hemp
  have hInf0 : Infinite (I i₀) := infinite_basisIndex_of_not_finite (b i₀) hfin
  have hNotFinPi : ¬Module.Finite R (⨂[R] i, M i) :=
    have := hemp
    not_finite_piTensorProduct_of_infinite b (Pi.infinite_of_exists_right i₀)
  rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hNotFinPi, LinearMap.zero_apply,
    Finset.prod_eq_zero (Finset.mem_univ i₀)
      (by simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin])]

open scoped Classical in
/-- **Trace of an indexed tensor product of endomorphisms.** Over any commutative semiring `R`,
the trace of `PiTensorProduct.map f` on a finite tensor product of free `R`-modules equals the
product of the traces of the factor endomorphisms `f i`. -/
theorem trace_piTensorProduct_map {R ι : Type*} [CommSemiring R] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    LinearMap.trace R (⨂[R] i, M i) (PiTensorProduct.map f) =
      ∏ i, LinearMap.trace R (M i) (f i) := by
  by_cases hfin : ∀ i, Module.Finite R (M i); swap
  · push Not at hfin
    obtain ⟨i₀, hi₀⟩ := hfin
    exact trace_piTensorProduct_map_eq_zero_of_not_finite f hi₀
  rcases subsingleton_or_nontrivial R with _hR | _hR
  · exact Subsingleton.elim _ _
  let b := fun i ↦ Module.Free.chooseBasis R (M i)
  have hFinI : ∀ i, Finite (Module.Free.ChooseBasisIndex R (M i)) :=
    fun i ↦ have := hfin i; Module.Finite.finite_basis (b i)
  let _ := fun i ↦ Fintype.ofFinite (Module.Free.ChooseBasisIndex R (M i))
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace R B]
  simp_rw [LinearMap.trace_eq_matrix_trace R (b _)]
  simp only [Matrix.trace, Matrix.diag]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp [B, LinearMap.toMatrix_apply]

end TraceMap

section ReindexTrace

/-- A point lies in the `⟨σ⟩`-orbit `ω` exactly when it lies on the cycle of `ω.out`. -/
private theorem sameCycle_out_iff {α : Type*} (σ : Equiv.Perm α) {x : α}
    {ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α} :
    σ.SameCycle ω.out x ↔
      (Quotient.mk'' x : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α) = ω := by
  rw [σ.sameCycle_iff_mem_orbit_zpowers, ← MulAction.orbitRel_apply, ← Quotient.eq'',
    Quotient.out_eq']

private theorem existsUnique_sameCycle_orbitRel_out {α : Type*} (σ : Equiv.Perm α) (x : α) :
    ∃! ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α, σ.SameCycle ω.out x :=
  ⟨Quotient.mk'' x, (sameCycle_out_iff σ).mpr rfl, fun _ h ↦ ((sameCycle_out_iff σ).mp h).symm⟩

/-- The enumeration `⟨ω, t⟩ ↦ (σ ^ t) ω.out` of `ι` along the `⟨σ⟩`-orbits, obtained from
`Equiv.Perm.sigmaCycleEquiv` with the representatives `Quotient.out`. -/
private noncomputable def orbitElemEquiv {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) :
    (Σ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
      Fin (Function.minimalPeriod (σ • ·) ω.out)) ≃ ι :=
  (Equiv.sigmaCongrRight fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι ↦
      finCongr (σ.minimalPeriod_sub_one_add_one ω.out).symm).trans
    (σ.sigmaCycleEquiv Quotient.out (existsUnique_sameCycle_orbitRel_out σ))

private theorem orbitElemEquiv_apply {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    (ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι)
    (t : Fin (Function.minimalPeriod (σ • ·) ω.out)) :
    orbitElemEquiv σ ⟨ω, t⟩ = (σ ^ (t : ℕ)) ω.out :=
  σ.sigmaCycleEquiv_apply _ _ ω _

private theorem finCongr_finRotate {a b : ℕ} (h : a = b) (t : Fin a) :
    finCongr h (finRotate a t) = finRotate b (finCongr h t) := by
  subst h
  rfl

private theorem orbitElemEquiv_succ {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    (ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι)
    (t : Fin (Function.minimalPeriod (σ • ·) ω.out)) :
    σ (orbitElemEquiv σ ⟨ω, t⟩) =
      orbitElemEquiv σ ⟨ω, finRotate (Function.minimalPeriod (σ • ·) ω.out) t⟩ :=
  (σ.sigmaCycleEquiv_finRotate _ _ ω _).symm.trans
    (congrArg (fun i ↦ σ.sigmaCycleEquiv _ (existsUnique_sameCycle_orbitRel_out σ) ⟨ω, i⟩)
      (finCongr_finRotate (σ.minimalPeriod_sub_one_add_one ω.out).symm t).symm)

/-- Along a cycle of length `m + 1`, the cyclic shift `finRotate` on exponents is the successor. -/
private theorem pow_finRotate_apply {α : Type*} (σ : Equiv.Perm α) (x : α)
    {m : ℕ} (hm : Function.minimalPeriod (σ • ·) x = m + 1) (t : Fin (m + 1)) :
    (σ ^ ((finRotate (m + 1) t : ℕ))) x = (σ ^ ((t : ℕ) + 1)) x := by
  have hm' : Function.minimalPeriod σ x = m + 1 := hm
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow, ← Function.iterate_mod_minimalPeriod_eq (n := _ + 1),
    hm']
  congr 1
  rw [coe_finRotate]
  split_ifs with h
  · simp [h]
  · rw [Nat.mod_eq_of_lt (by have := Fin.val_lt_last h; omega)]

private theorem trace_list_ofFn_rot {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {k : ℕ} (A : Fin (k + 1) → M →ₗ[R] M) :
    LinearMap.trace R M (List.ofFn fun t ↦ A (finRotate (k + 1) t)).prod =
      LinearMap.trace R M (List.ofFn A).prod := by
  have hlist :
      List.ofFn (fun t : Fin (k + 1) ↦ A (finRotate (k + 1) t)) =
        List.ofFn (fun i : Fin k ↦ A i.succ) ++ [A 0] := by
    rw [List.ofFn_succ']
    simp
  rw [hlist, List.prod_append, List.prod_singleton, LinearMap.trace_mul_comm,
    ← List.prod_cons, ← List.ofFn_succ]

private theorem trace_list_ofFn_add_shift_succ {R ι M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (σ : Equiv.Perm ι) (f : ι → M →ₗ[R] M) (x : ι)
    {m : ℕ} (hm : Function.minimalPeriod (σ • ·) x = m + 1) (d : ℕ) :
    LinearMap.trace R M (List.ofFn fun t : Fin (m + 1) ↦
        f ((σ ^ ((t : ℕ) + d)) x)).prod =
      LinearMap.trace R M (List.ofFn fun t : Fin (m + 1) ↦ f ((σ ^ (t : ℕ)) x)).prod := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hfun : (fun t : Fin (m + 1) ↦ f ((σ ^ ((t : ℕ) + (d + 1))) x)) =
        fun t : Fin (m + 1) ↦ f ((σ ^ (((finRotate (m + 1) t : ℕ)) + d)) x) := by
      funext t
      congr 1
      rw [show (t : ℕ) + (d + 1) = d + ((t : ℕ) + 1) by omega, pow_add, Equiv.Perm.mul_apply,
        ← pow_finRotate_apply σ x hm t, ← Equiv.Perm.mul_apply, ← pow_add, add_comm d _]
    rw [hfun]
    exact (trace_list_ofFn_rot fun s : Fin (m + 1) ↦ f ((σ ^ ((s : ℕ) + d)) x)).trans ih

private theorem trace_orbit_change_rep {R ι M : Type*} [CommSemiring R] [Finite ι]
    [AddCommMonoid M] [Module R M] (σ : Equiv.Perm ι) (f : ι → M →ₗ[R] M) {x y : ι}
    (h : MulAction.orbitRel (Subgroup.zpowers σ) ι y x) :
    LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) y) ↦
        f ((σ ^ (t : ℕ)) y)).prod =
      LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) x) ↦
        f ((σ ^ (t : ℕ)) x)).prod := by
  obtain ⟨d, rfl⟩ :=
    (σ.sameCycle_iff_mem_orbit_zpowers.mpr (MulAction.orbitRel_apply.mp h)).exists_nat_pow_eq
  have hper : Function.minimalPeriod (σ • ·) ((σ ^ d) x) = Function.minimalPeriod (σ • ·) x := by
    rw [Equiv.Perm.coe_pow]
    exact Function.minimalPeriod_apply_iterate (σ.injective.mem_periodicPts x) d
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)).ne'
  have hm' : Function.minimalPeriod (σ • ·) x = m + 1 := hm
  have h1 :
      List.ofFn (fun t : Fin (Function.minimalPeriod (σ • ·) ((σ ^ d) x)) ↦
          f ((σ ^ (t : ℕ)) ((σ ^ d) x))) =
        List.ofFn fun t : Fin (m + 1) ↦ f ((σ ^ ((t : ℕ) + d)) x) := by
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_ofFn, hper, hm'])
      fun i _ _ ↦ ?_
    simp only [List.getElem_ofFn]
    rw [← Equiv.Perm.mul_apply, ← pow_add]
  have h2 :
      List.ofFn (fun t : Fin (m + 1) ↦ f ((σ ^ (t : ℕ)) x)) =
        List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) x) ↦ f ((σ ^ (t : ℕ)) x) :=
    List.ext_getElem (by rw [List.length_ofFn, List.length_ofFn, hm'])
      fun i _ _ ↦ by simp only [List.getElem_ofFn]
  rw [h1, ← h2]
  exact trace_list_ofFn_add_shift_succ σ f x hm d

open scoped Classical in
/-- Splits a cyclic coordinate sum of matrix products over the orbits of a permutation into a
product of cyclic path matrix traces along each orbit. -/
theorem sum_prod_coords_eq_sum_prod_orbit_coords {R ι κ : Type*} [CommSemiring R] [Fintype ι]
    [Fintype κ] [DecidableEq κ] (σ : Equiv.Perm ι) (A : ι → Matrix κ κ R) :
    (∑ p : ι → κ, ∏ i : ι, A i (p i) (p (σ i))) =
      ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          A ((σ ^ (t : ℕ)) ω.out)).prod.trace := by
  let e := orbitElemEquiv σ
  let fEquiv :
      (∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          Fin (Function.minimalPeriod (σ • ·) ω.out) → κ) ≃ (ι → κ) :=
    (Equiv.piCurry (fun ω _ ↦ κ)).symm.trans (Equiv.piCongrLeft' (fun _ ↦ κ) e)
  rw [← fEquiv.sum_comp]
  have hstep :
      (∑ c : ∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ i : ι, A i (fEquiv c i) (fEquiv c (σ i))) =
        ∑ c : ∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
            ∏ t : Fin (Function.minimalPeriod (σ • ·) ω.out),
              A ((σ ^ (t : ℕ)) ω.out) (c ω t) (c ω (finRotate _ t)) := by
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [← Fintype.prod_equiv e _ _ fun _ ↦ rfl, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ω _ ↦ Finset.prod_congr rfl fun t _ ↦ ?_
    have hnext : σ (e ⟨ω, t⟩) =
        e ⟨ω, finRotate (Function.minimalPeriod (σ • ·) ω.out) t⟩ :=
      orbitElemEquiv_succ σ ω t
    have hp1 : fEquiv c (e ⟨ω, t⟩) = c ω t := by simp [fEquiv]; rfl
    have hp2 : fEquiv c (σ (e ⟨ω, t⟩)) =
        c ω (finRotate (Function.minimalPeriod (σ • ·) ω.out) t) := by
      rw [hnext]
      simp [fEquiv]
      rfl
    simp only [hp1, hp2]
    rw [show e ⟨ω, t⟩ = _ from orbitElemEquiv_apply σ ω t]
  rw [hstep]
  have hrhs :
      (∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
            A ((σ ^ (t : ℕ)) ω.out)).prod.trace) =
        ∑ c : ∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
            Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
            ∏ t : Fin (Function.minimalPeriod (σ • ·) ω.out),
              A ((σ ^ (t : ℕ)) ω.out) (c ω t) (c ω (finRotate _ t)) := by
    trans (∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        ∑ c_ω : Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ t : Fin (Function.minimalPeriod (σ • ·) ω.out),
            A ((σ ^ (t : ℕ)) ω.out) (c_ω t) (c_ω (finRotate _ t)))
    · refine Finset.prod_congr rfl fun ω _ ↦ ?_
      have : NeZero (Function.minimalPeriod (σ • ·) ω.out) :=
        ⟨(Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts ω.out)).ne'⟩
      rw [Matrix.trace_list_ofFn_prod]
    · rw [Fintype.prod_sum]
  rw [hrhs]

private theorem trace_piTensorProduct_map_comp_reindex_inv_zero {R ι M : Type*} [CommSemiring R]
    [Finite ι] [Nonempty ι] [AddCommMonoid M] [Module R M] [Module.Free R M]
    (hfin : ¬Module.Finite R M) (f : ι → M →ₗ[R] M) (σ : Equiv.Perm ι)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι)] :
    LinearMap.trace R (⨂[R] _ : ι, M)
        ((PiTensorProduct.map f).comp (PiTensorProduct.reindex R (fun _ ↦ M) σ⁻¹).toLinearMap) =
      ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          f ((σ ^ (t : ℕ)) ω.out)).prod := by
  classical
  rcases subsingleton_or_nontrivial R with _hR | _hR
  · exact Subsingleton.elim _ _
  let b := Module.Free.chooseBasis R M
  have hInfI : Infinite (Module.Free.ChooseBasisIndex R M) :=
    infinite_basisIndex_of_not_finite b hfin
  have hNotFinPi : ¬Module.Finite R (⨂[R] _ : ι, M) :=
    not_finite_piTensorProduct_of_infinite (fun _ ↦ b)
      Pi.infinite_of_right
  rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hNotFinPi, LinearMap.zero_apply]
  let ω₀ : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι :=
    Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) ι) (Classical.arbitrary ι)
  refine (Finset.prod_eq_zero (Finset.mem_univ ω₀) ?_).symm
  simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin]

open scoped Classical in
/-- **Trace of a permutation-twisted tensor-product endomorphism (inverse reindex form).**
For a free `R`-module `M`, a finite index type `ι`, factor endomorphisms `f i`, and a permutation
`σ`, the trace of `(PiTensorProduct.map f).comp (PiTensorProduct.reindex R _ σ⁻¹)` equals the
product over `⟨σ⟩`-orbits of the traces of the orbit cyclic compositions. -/
theorem trace_piTensorProduct_map_comp_reindex_eq_prod_trace_inv_orbits {R ι M : Type*}
    [CommSemiring R] [Fintype ι] [AddCommMonoid M] [Module R M] [Module.Free R M]
    (f : ι → M →ₗ[R] M) (σ : Equiv.Perm ι) :
    LinearMap.trace R (⨂[R] _ : ι, M)
        ((PiTensorProduct.map f).comp (PiTensorProduct.reindex R (fun _ ↦ M) σ⁻¹).toLinearMap) =
      ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          f ((σ ^ (t : ℕ)) ω.out)).prod := by
  by_cases hne : IsEmpty ι
  · rcases subsingleton_or_nontrivial R with _hR | _hR
    · exact Subsingleton.elim _ _
    let b := Module.Free.chooseBasis R M
    let B := Basis.piTensorProduct fun _ : ι ↦ b
    rw [LinearMap.trace_eq_matrix_trace R B]
    simp only [Matrix.trace, Matrix.diag]
    simp [B, LinearMap.toMatrix_apply, PiTensorProduct.reindex_tprod,
      Basis.piTensorProduct_repr_tprod_apply]
  rw [not_isEmpty_iff] at hne
  by_cases hfin : Module.Finite R M; swap
  · exact trace_piTensorProduct_map_comp_reindex_inv_zero hfin f σ
  rcases subsingleton_or_nontrivial R with _hR | _hR
  · exact Subsingleton.elim _ _
  let b := Module.Free.chooseBasis R M
  have hFinI : Finite (Module.Free.ChooseBasisIndex R M) := Module.Finite.finite_basis b
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex R M)
  let B := Basis.piTensorProduct fun _ : ι ↦ b
  rw [LinearMap.trace_eq_matrix_trace R B]
  simp only [Matrix.trace, Matrix.diag]
  have hdiag :
      (∑ p : ι → Module.Free.ChooseBasisIndex R M,
          (LinearMap.toMatrix B B ((PiTensorProduct.map f).comp
            (PiTensorProduct.reindex R (fun _ ↦ M) σ⁻¹).toLinearMap)) p p) =
        ∑ p : ι → Module.Free.ChooseBasisIndex R M,
          ∏ i : ι, (LinearMap.toMatrixAlgEquiv b (f i)) (p i) (p (σ i)) := by
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [B, LinearMap.toMatrix_apply, LinearMap.toMatrixAlgEquiv_apply,
      PiTensorProduct.reindex_tprod, Basis.piTensorProduct_repr_tprod_apply,
      show σ⁻¹.symm = σ from inv_inv σ]
  rw [hdiag,
    sum_prod_coords_eq_sum_prod_orbit_coords σ (fun i ↦ LinearMap.toMatrixAlgEquiv b (f i))]
  refine Finset.prod_congr rfl fun ω _ ↦ ?_
  have hmap :
      List.ofFn (fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          LinearMap.toMatrixAlgEquiv b (f ((σ ^ (t : ℕ)) ω.out))) =
        (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          f ((σ ^ (t : ℕ)) ω.out)).map (LinearMap.toMatrixAlgEquiv b) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, ← map_list_prod (LinearMap.toMatrixAlgEquiv b), LinearMap.trace_eq_matrix_trace R b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

open scoped Classical in
/-- **Trace of a permutation-twisted tensor-product endomorphism.** For a free `R`-module `M`, a
finite index type `ι`, factor endomorphisms `f i`, and a permutation `σ`, the trace of
`(PiTensorProduct.map f).comp (PiTensorProduct.reindex R _ σ)` equals the product over
`⟨σ⟩`-orbits of `LinearMap.trace R M (List.ofFn fun t ↦ f ((σ⁻¹ ^ (t : ℕ)) ω.out)).prod`. -/
theorem trace_piTensorProduct_map_comp_reindex {R ι M : Type*} [CommSemiring R] [Fintype ι]
    [AddCommMonoid M] [Module R M] [Module.Free R M] (f : ι → M →ₗ[R] M) (σ : Equiv.Perm ι) :
    LinearMap.trace R (⨂[R] _ : ι, M)
        ((PiTensorProduct.map f).comp (PiTensorProduct.reindex R (fun _ ↦ M) σ).toLinearMap) =
      ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          f ((σ⁻¹ ^ (t : ℕ)) ω.out)).prod := by
  have h := trace_piTensorProduct_map_comp_reindex_eq_prod_trace_inv_orbits f σ⁻¹
  rw [inv_inv] at h
  rw [h]
  let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι :=
    Quotient.congrRight fun _ _ ↦ by rw [Subgroup.zpowers_inv]
  refine Fintype.prod_equiv qEquiv _ _ fun ω ↦ ?_
  have horb : MulAction.orbitRel (Subgroup.zpowers σ⁻¹) ι ω.out (qEquiv ω).out := by
    have hq : qEquiv ω = Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) ι) ω.out := by
      conv_lhs => rw [← Quotient.out_eq ω]
      rfl
    have heq : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) ι) ω.out =
        Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) ι) (qEquiv ω).out :=
      hq.symm.trans (Quotient.out_eq (qEquiv ω)).symm
    have hs := Quotient.exact' heq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hs ⊢
    obtain ⟨⟨g, hg⟩, hgx⟩ := hs
    rw [← Subgroup.zpowers_inv (g := σ)] at hg
    exact ⟨⟨g, hg⟩, hgx⟩
  refine (trace_orbit_change_rep σ⁻¹ f horb).trans ?_
  have hper : Function.minimalPeriod (σ⁻¹ • ·) (qEquiv ω).out =
      Function.minimalPeriod (σ • ·) (qEquiv ω).out := by
    simpa only [MulAction.period_eq_minimalPeriod] using MulAction.period_inv σ (qEquiv ω).out
  have hlist :
      (List.ofFn fun t : Fin (Function.minimalPeriod (σ⁻¹ • ·) (qEquiv ω).out) ↦
          f ((σ⁻¹ ^ (t : ℕ)) (qEquiv ω).out)) =
        List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) (qEquiv ω).out) ↦
          f ((σ⁻¹ ^ (t : ℕ)) (qEquiv ω).out) :=
    List.ext_getElem (by simpa [List.length_ofFn] using hper)
      fun i _ _ ↦ by simp only [List.getElem_ofFn]
  rw [hlist]

end ReindexTrace

end LinearMap

namespace PiTensorProduct

open Module

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- **The trace of a permutation of tensor factors.** On the tensor power of a free module of
finite rank `N`, reindexing the factors by `σ` has trace `N ^ c(σ)`, where `c(σ)` is the number of
cycles of `σ`, fixed points included. -/
@[simp]
theorem trace_reindex [Module.Free R M] [Module.Finite R M] (σ : Equiv.Perm ι) :
    LinearMap.trace R _ (reindex R (fun _ : ι => M) σ).toLinearMap =
      (finrank R M : R) ^ Multiset.card σ.fullCycleType := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  set b := Module.Free.chooseBasis R M
  set B := Basis.piTensorProduct fun _ : ι => b
  -- `σ` sends the basis tensor of `p` to that of `p ∘ σ⁻¹`
  have hB : ∀ p : ι → Free.ChooseBasisIndex R M,
      reindex R (fun _ : ι => M) σ (B p) = B (p ∘ σ.symm) := fun p => by
    simp only [B, Basis.piTensorProduct_apply, reindex_tprod, Function.comp_apply]
  have hfix : ∀ p : ι → Free.ChooseBasisIndex R M, p ∘ σ.symm = p ↔ p ∘ σ = p := fun p =>
    (σ.comp_symm_eq p p).trans eq_comm
  rw [LinearMap.trace_eq_matrix_trace R B, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hB,
    Basis.repr_self, Finsupp.single_apply, hfix, Finset.sum_boole]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Equiv.Perm.card_invariantColouring,
    Nat.card_eq_fintype_card, ← finrank_eq_card_chooseBasisIndex, Nat.cast_pow]

end PiTensorProduct
