/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.RingTheory.Finiteness.Cardinality
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
* `Matrix.sum_prod_apply_perm_eq_prod_trace_list_ofFn_orbit`: splits the cyclic coordinate sum of
  matrices over the orbits of a permutation into a product, over the orbits, of traces of the
  ordered matrix products along each orbit.
* `LinearMap.trace_piTensorProduct_map_comp_reindex_inv`: the trace of
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
    rw [LinearMap.trace_eq_zero_of_subsingleton, Finset.prod_eq_zero (Finset.mem_univ i₁)
      (LinearMap.trace_eq_zero_of_subsingleton (f i₁))]
  push Not at hemp
  have : Infinite (I i₀) := not_finite_iff_infinite.mp fun _ ↦ hfin (.of_basis (b i₀))
  have : Infinite (∀ i, I i) := have := hemp; Pi.infinite_of_exists_right i₀
  have hNotFinPi : ¬Module.Finite R (⨂[R] i, M i) :=
    Module.not_finite_of_infinite_basis (Basis.piTensorProduct b)
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

/-- The enumeration `⟨ω, t⟩ ↦ (σ ^ t) ω.out` of `ι` along the `⟨σ⟩`-orbits, obtained from
`Equiv.Perm.sigmaCycleEquiv` with the representatives `Quotient.out`. -/
private noncomputable def orbitElemEquiv {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) :
    (Σ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
      Fin (Function.minimalPeriod (σ • ·) ω.out)) ≃ ι :=
  (Equiv.sigmaCongrRight fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι ↦
      finCongr (σ.minimalPeriod_sub_one_add_one ω.out).symm).trans
    (σ.sigmaCycleEquiv Quotient.out σ.existsUnique_sameCycle_orbitRel_out)

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
    (congrArg (fun i ↦ σ.sigmaCycleEquiv _ σ.existsUnique_sameCycle_orbitRel_out ⟨ω, i⟩)
      (finCongr_finRotate (σ.minimalPeriod_sub_one_add_one ω.out).symm t).symm)

/-- The trace of the ordered product of `f` along a `⟨σ⟩`-orbit does not depend on the starting
point: starting at `(σ ^ d) x` instead of `x` rotates the list of factors by `d`. -/
private theorem trace_orbit_change_rep {R ι M : Type*} [CommSemiring R] [Finite ι]
    [AddCommMonoid M] [Module R M] (σ : Equiv.Perm ι) (f : ι → M →ₗ[R] M) {x y : ι}
    (h : MulAction.orbitRel (Subgroup.zpowers σ) ι y x) :
    LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) y) ↦
        f ((σ ^ (t : ℕ)) y)).prod =
      LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) x) ↦
        f ((σ ^ (t : ℕ)) x)).prod := by
  obtain ⟨d, rfl⟩ :=
    (σ.sameCycle_iff_mem_orbit_zpowers.mpr (MulAction.orbitRel_apply.mp h)).exists_nat_pow_eq
  have hx : x ∈ Function.periodicPts σ := σ.injective.mem_periodicPts x
  have hper : Function.minimalPeriod (σ • ·) ((σ ^ d) x) = Function.minimalPeriod (σ • ·) x := by
    rw [Equiv.Perm.coe_pow]
    exact Function.minimalPeriod_apply_iterate hx d
  refine (LinearMap.trace_list_prod_of_isRotated
    ⟨d, List.ext_getElem (by simpa using hper.symm) fun m h₁ h₂ ↦ ?_⟩).symm
  simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
  rw [← Equiv.Perm.mul_apply, ← pow_add, Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact congrArg f (Function.iterate_mod_minimalPeriod_eq (f := σ))

end ReindexTrace

end LinearMap

namespace Matrix

open scoped Classical in
/-- Splits a cyclic coordinate sum of matrix products over the orbits of a permutation into a
product, over the orbits, of the traces of the ordered matrix products along each orbit. -/
theorem sum_prod_apply_perm_eq_prod_trace_list_ofFn_orbit {R ι κ : Type*} [CommSemiring R]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (σ : Equiv.Perm ι) (A : ι → Matrix κ κ R) :
    (∑ p : ι → κ, ∏ i : ι, A i (p i) (p (σ i))) =
      ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          A ((σ ^ (t : ℕ)) ω.out)).prod.trace := by
  let e := LinearMap.orbitElemEquiv σ
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
      LinearMap.orbitElemEquiv_succ σ ω t
    have hp : ∀ p, fEquiv c (e p) = c p.1 p.2 := fun p ↦ by
      simp only [fEquiv, Equiv.trans_apply, Equiv.piCongrLeft'_apply, Equiv.piCurry_symm_apply,
        Sigma.uncurry]
      rw [Equiv.symm_apply_apply]
    rw [hp, hnext, hp, show e ⟨ω, t⟩ = _ from LinearMap.orbitElemEquiv_apply σ ω t]
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

end Matrix

namespace LinearMap

open PiTensorProduct Module
open scoped TensorProduct

section ReindexTrace

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
  have : Infinite (Module.Free.ChooseBasisIndex R M) :=
    not_finite_iff_infinite.mp fun _ ↦ hfin (.of_basis b)
  have hNotFinPi : ¬Module.Finite R (⨂[R] _ : ι, M) :=
    Module.not_finite_of_infinite_basis (Basis.piTensorProduct fun _ : ι ↦ b)
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
theorem trace_piTensorProduct_map_comp_reindex_inv {R ι M : Type*}
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
    Matrix.sum_prod_apply_perm_eq_prod_trace_list_ofFn_orbit σ
      (fun i ↦ LinearMap.toMatrixAlgEquiv b (f i))]
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
  have h := trace_piTensorProduct_map_comp_reindex_inv f σ⁻¹
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
