/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.Tensor.Induction.Basic

import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import TauCeti.GroupTheory.GroupAction.Orbit.Card

/-!
# Traces and characters of tensor-induced representations

A monomial endomorphism of a tensor power acts by linear maps on the individual factors followed by
a permutation of the index set. Its trace decomposes over the cycles of that permutation: on each
cycle of length `k`, the diagonal basis terms multiply entrywise around the loop and contract to the
trace of the `k`-fold composition of the factor maps along the cycle.

Applying this to `Representation.wreathTensor` expresses the character of a wreath tensor
representation as a product over the cycles of the underlying permutation. Pulling back along
`Subgroup.monomialHom` and telescoping the transversal words `TauCeti.lWord` along each coset
cycle gives the character formula for `Subgroup.tensorInducedRepresentation`: for any finite-index
subgroup `U ≤ G`, any left transversal `s`, and any `U`-representation `ρ`, the trace at `g ∈ G` is
the product over the `⟨g⟩`-orbits on `G ⧸ U` of the trace of `ρ` at the cycle monodromy
`r⁻¹ * g ^ m * r ∈ U`. Because `u ↦ tr (ρ u)` is invariant under `U`-conjugation, this product is
independent of the transversal `s` and defines a canonical conjugation-invariant function
`Subgroup.tensorIndClassFun U f`.

For a normal subgroup `H ≤ G`, conjugation invariance allows evaluating `Subgroup.tensorIndClassFun`
at elements of `H` as the product of `H`-conjugate values over `G ⧸ H`.

## Main definitions

* `Subgroup.tensorIndClassFun`: canonical tensor-induced function on `G` attached to a function
  `U → R` for a finite-index subgroup `U ≤ G`.

## Main results

* `LinearMap.trace_piTensorProduct_map`: trace of `PiTensorProduct.map` as a product of traces.
* `LinearMap.trace_piTensorProduct_map_comp_reindex`: cycle-product trace formula for a diagonal map
  composed with a factor permutation.
* `Representation.trace_wreathTensor`: trace formula for `Representation.wreathTensor`.
* `Subgroup.trace_tensorInducedRepresentation` and `Subgroup.character_tensorInducedRepresentation`:
  transversal-independent orbit-product trace and character formulas for
  `Subgroup.tensorInducedRepresentation`.
* `Subgroup.tensorIndClassFun_conj` and `Subgroup.tensorIndClassFun_mem_classFunction`: conjugation
  invariance of `Subgroup.tensorIndClassFun`.
* `Subgroup.tensorIndClassFun_apply_of_mem_of_normal`: evaluation on a normal subgroup.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–5.
* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.
-/

public section

open scoped TensorProduct

namespace Matrix

private def finConsEquiv (n : ℕ) (κ : Type*) : κ × (Fin n → κ) ≃ (Fin (n + 1) → κ) where
  toFun p := Fin.cons p.1 p.2
  invFun d := (d 0, fun i ↦ d i.succ)
  left_inv p := by ext <;> simp
  right_inv d := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl

private theorem finSnoc_cons {n : ℕ} {κ : Type*} (z : κ) (c : Fin n → κ) (y : κ)
    (j : Fin (n + 1)) :
    Fin.snoc (α := fun _ ↦ κ) (Fin.cons z c) y j.succ = Fin.snoc (α := fun _ ↦ κ) c y j := by
  cases j using Fin.lastCases with
  | cast k =>
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.cons_succ]
  | last =>
    rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]

private theorem finSnoc_succ_first {n : ℕ} {κ : Type*} (d : Fin (n + 1) → κ)
    (i : Fin (n + 1)) :
    Fin.snoc (α := fun _ ↦ κ) (fun j : Fin n ↦ d j.succ) (d 0) i = d (i + 1) := by
  cases i using Fin.lastCases with
  | cast j =>
    have hj : j.castSucc + 1 = j.succ := by
      ext
      simp
    rw [Fin.snoc_castSucc, hj]
  | last =>
    have hlast : Fin.last n + 1 = (0 : Fin (n + 1)) := by
      ext
      simp
    rw [Fin.snoc_last, hlast]

private theorem finCases_succ_first {n : ℕ} {κ : Type*} (d : Fin (n + 1) → κ)
    (j : Fin (n + 1)) :
    Fin.cases (motive := fun _ ↦ κ) (d 0) (fun i ↦ d i.succ) j = d j := by
  cases j using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem list_ofFn_prod_apply {R κ : Type*} [CommSemiring R] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (B : Fin (n + 1) → Matrix κ κ R) (x y : κ) :
    (List.ofFn B).prod x y =
      ∑ c : Fin n → κ, ∏ i : Fin (n + 1),
        B i (Fin.cases (motive := fun _ ↦ κ) x c i) (Fin.snoc (α := fun _ ↦ κ) c y i) := by
  induction n generalizing x with
  | zero =>
    rw [List.ofFn_succ, List.ofFn_zero, List.prod_singleton, Fintype.sum_unique, Fin.prod_univ_one,
      show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
    rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih _ _]
    have hsum :
        ∑ d : Fin (n + 1) → κ, ∏ i : Fin (n + 2),
            B i (Fin.cases (motive := fun _ ↦ κ) x d i) (Fin.snoc (α := fun _ ↦ κ) d y i) =
          ∑ p : κ × (Fin n → κ), B 0 x p.1 * ∏ j : Fin (n + 1),
            B j.succ (Fin.cases (motive := fun _ ↦ κ) p.1 p.2 j)
              (Fin.snoc (α := fun _ ↦ κ) p.2 y j) := by
      refine Fintype.sum_equiv (finConsEquiv n κ).symm _ _ fun d ↦ ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cases_zero, finConsEquiv, Equiv.coe_fn_symm_mk]
      -- Match `Fin.cases` at `0` against `p.1` and `Fin.snoc` at `n` against `p.2`.
      change B 0 x (d 0) * _ = B 0 x (d 0) * _
      congr 1
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hd : Fin.cons (d 0) (fun i ↦ d i.succ) = d := (finConsEquiv n κ).apply_symm_apply d
      rw [Fin.cases_succ, ← finSnoc_cons (d 0) (fun i ↦ d i.succ) y j, hd, finCases_succ_first]
    rw [hsum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.mul_sum]

/-- **Cyclic matrix trace identity.** For a nonempty tuple of square matrices indexed by `Fin k`,
the trace of their ordered product equals the sum over closed loops `d : Fin k → κ` of the product
of entries `A i (d i) (d (i + 1))`. -/
theorem trace_list_ofFn_prod {R κ : Type*} [CommSemiring R] [Fintype κ] [DecidableEq κ]
    {k : ℕ} [NeZero k] (A : Fin k → Matrix κ κ R) :
    (List.ofFn A).prod.trace =
      ∑ d : Fin k → κ, ∏ i : Fin k, A i (d i) (d (i + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  -- Unfold `Matrix.trace` as the diagonal sum so `list_ofFn_prod_apply` matches.
  change ∑ c₀ : κ, (List.ofFn A).prod c₀ c₀ = _
  simp_rw [list_ofFn_prod_apply]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (finConsEquiv n κ) _ _ fun p ↦ ?_
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h1 : Fin.cases (motive := fun _ ↦ κ) p.1 p.2 i = finConsEquiv n κ p i := rfl
  have h2 : Fin.snoc (α := fun _ ↦ κ) p.2 p.1 i = finConsEquiv n κ p (i + 1) := by
    simpa [finConsEquiv] using finSnoc_succ_first (finConsEquiv n κ p) i
  rw [h1, h2]

end Matrix

namespace LinearMap

private theorem trace_eq_zero_of_infinite_basis {R M ι : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) [Infinite ι] (f : M →ₗ[R] M) :
    trace R M f = 0 := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · have hno : ¬ ∃ s : Finset M, Nonempty (Module.Basis s R M) := by
      rintro ⟨s, ⟨c⟩⟩
      let supp : Finset ι := Finset.univ.biUnion fun v : s ↦ (b.repr (c v)).support
      obtain ⟨i₀, hi₀⟩ := Infinite.exists_notMem_finset supp
      have hsum : ∑ v : s, c.repr (b i₀) v • c v = b i₀ := c.sum_repr (b i₀)
      have hcoord := congrArg
        (fun m ↦ (Finsupp.lapply i₀ : (ι →₀ R) →ₗ[R] R) (b.repr m)) hsum
      simp only [map_sum, map_smul, Finsupp.lapply_apply, smul_eq_mul, b.repr_self,
        Finsupp.single_eq_same] at hcoord
      have hzero : ∀ v ∈ Finset.univ, c.repr (b i₀) v * b.repr (c v) i₀ = 0 := fun v _ ↦ by
        have hnot : i₀ ∉ (b.repr (c v)).support := fun hm ↦
          hi₀ (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hm⟩)
        rw [Finsupp.notMem_support_iff.mp hnot, mul_zero]
      rw [Finset.sum_eq_zero hzero] at hcoord
      exact zero_ne_one hcoord
    rw [trace, dite_eq_right hno, LinearMap.zero_apply]

private theorem trace_eq_zero_of_not_finite_of_free {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
    (h : ¬ Module.Finite R M) (f : M →ₗ[R] M) :
    trace R M f = 0 := by
  have : Infinite (Module.Free.ChooseBasisIndex R M) :=
    not_finite_iff_infinite.mp fun _ ↦ h (Module.Finite.of_basis (Module.Free.chooseBasis R M))
  exact trace_eq_zero_of_infinite_basis (Module.Free.chooseBasis R M) f

/-- **Trace of a tensor product of endomorphisms.** Over any commutative semiring, the trace of
`PiTensorProduct.map f` on an indexed tensor power of free modules equals the product of the
traces of the factors. If any factor is not finitely generated, both sides evaluate to `0`. -/
theorem trace_piTensorProduct_map {R ι : Type*} {M : ι → Type*}
    [CommSemiring R] [Fintype ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    trace R (⨂[R] i, M i) (PiTensorProduct.map f) =
      ∏ i : ι, trace R (M i) (f i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  let B := Basis.piTensorProduct b
  by_cases hfin : ∀ i, Module.Finite R (M i)
  · rw [trace_eq_matrix_trace R B]
    simp_rw [trace_eq_matrix_trace R (b _), Matrix.trace, Matrix.diag_apply, toMatrix_apply,
      B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
      Basis.piTensorProduct_repr_tprod_apply]
    exact (Fintype.prod_sum fun i k ↦ (b i).repr (f i (b i k)) k).symm
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hfin
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (trace_eq_zero_of_not_finite_of_free hi₀ (f i₀))]
    by_cases hempty : ∃ j : ι, IsEmpty (Module.Free.ChooseBasisIndex R (M j))
    · obtain ⟨j, hj⟩ := hempty
      have : IsEmpty (∀ i, Module.Free.ChooseBasisIndex R (M i)) := ⟨fun p ↦ hj.false (p j)⟩
      let := Fintype.ofIsEmpty (α := ∀ i, Module.Free.ChooseBasisIndex R (M i))
      rw [trace_eq_matrix_trace R B, Matrix.trace, Fintype.sum_empty]
    · have hne : ∀ j : ι, Nonempty (Module.Free.ChooseBasisIndex R (M j)) := fun j ↦
        not_isEmpty_iff.mp fun hj ↦ hempty ⟨j, hj⟩
      have : Infinite (Module.Free.ChooseBasisIndex R (M i₀)) :=
        not_finite_iff_infinite.mp fun _ ↦ hi₀ (Module.Finite.of_basis (b i₀))
      let g : ∀ i, Module.Free.ChooseBasisIndex R (M i) := fun i ↦ Classical.choice (hne i)
      have hinj : Function.Injective (Function.update g i₀) := fun a₁ a₂ h ↦ by
        simpa [Function.update_self] using congrFun h i₀
      have : Infinite (∀ i, Module.Free.ChooseBasisIndex R (M i)) :=
        Infinite.of_injective (Function.update g i₀) hinj
      exact trace_eq_zero_of_infinite_basis B _

private theorem minimalPeriod_pos_of_finite {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) (x : ι) :
    0 < Function.minimalPeriod (σ • ·) x := by
  rw [← MulAction.natCard_orbit_zpowers σ x, Nat.pos_iff_ne_zero]
  exact MulAction.orbitRel.Quotient.card_orbit_ne_zero (Quotient.mk'' x)

private theorem minimalPeriod_inv_perm {ι : Type*} (σ : Equiv.Perm ι) (x : ι) :
    Function.minimalPeriod (σ⁻¹ • ·) x = Function.minimalPeriod (σ • ·) x := by
  rw [← MulAction.natCard_orbit_zpowers σ⁻¹ x, ← MulAction.natCard_orbit_zpowers σ x,
    Subgroup.zpowers_inv]

private theorem minimalPeriod_eq_of_orbitRel {ι : Type*} (σ : Equiv.Perm ι) {x y : ι}
    (h : MulAction.orbitRel (Subgroup.zpowers σ) ι x y) :
    Function.minimalPeriod (σ • ·) x = Function.minimalPeriod (σ • ·) y := by
  rw [← MulAction.natCard_orbit_zpowers σ x, ← MulAction.natCard_orbit_zpowers σ y]
  exact congrArg (fun S : Set ι ↦ Nat.card S) (MulAction.orbit_eq_iff.mpr h)

private noncomputable def orbitFinEquiv {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) :
    ι ≃ Σ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι,
      Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out) :=
  (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers σ⁻¹) ι).trans
    (Equiv.sigmaCongrRight fun q ↦
      haveI : NeZero (Function.minimalPeriod (σ⁻¹ • ·) q.out) :=
        ⟨(minimalPeriod_pos_of_finite σ⁻¹ q.out).ne'⟩
      (MulAction.orbitZPowersEquiv σ⁻¹ q.out).trans (ZMod.finEquiv _).symm.toEquiv)

private theorem zmod_cast_finEquiv (n : ℕ) [NeZero n] (t : Fin n) :
    (ZMod.cast ((ZMod.finEquiv n) t) : ℤ) = t.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
    rw [ZMod.cast_eq_val (R := ℤ)]
    rfl

private theorem selfEquivSigmaOrbits_symm_coe {G α : Type*} [Group G] [MulAction G α]
    (q : MulAction.orbitRel.Quotient G α) (x : MulAction.orbit G q.out) :
    (MulAction.selfEquivSigmaOrbits G α).symm ⟨q, x⟩ = (x : α) := by
  rw [Equiv.symm_apply_eq]
  have hfst : q = (MulAction.selfEquivSigmaOrbits G α (x : α)).fst :=
    ((Quotient.sound' x.property).trans (Quotient.out_eq q)).symm
  refine Sigma.ext hfst ?_
  have horb : ∀ z, z ∈ MulAction.orbit G q.out ↔
      z ∈ MulAction.orbit G (MulAction.selfEquivSigmaOrbits G α (x : α)).fst.out := fun z ↦ by
    rw [← hfst]
  exact (Subtype.heq_iff_coe_eq horb).mpr rfl

private theorem orbitFinEquiv_symm_apply {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    (q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι)
    (t : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out)) :
    ((orbitFinEquiv σ).symm ⟨q, t⟩ : ι) = (σ⁻¹ ^ (t : ℕ)) q.out := by
  have : NeZero (Function.minimalPeriod (σ⁻¹ • ·) q.out) :=
    ⟨(minimalPeriod_pos_of_finite σ⁻¹ q.out).ne'⟩
  rw [orbitFinEquiv, Equiv.symm_trans_apply, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply, selfEquivSigmaOrbits_symm_coe, Equiv.symm_trans_apply]
  have hz : ((ZMod.finEquiv (Function.minimalPeriod (σ⁻¹ • ·) q.out)).symm.toEquiv).symm t =
      (ZMod.finEquiv (Function.minimalPeriod (σ⁻¹ • ·) q.out)) t := rfl
  rw [hz, MulAction.orbitZPowersEquiv_symm_apply, zmod_cast_finEquiv, zpow_natCast]
  rfl

private theorem iterate_perm_smul {ι : Type*} (σ : Equiv.Perm ι) (n : ℕ) (x : ι) :
    (σ • ·)^[n] x = (σ ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Equiv.Perm.smul_def, ← Equiv.Perm.mul_apply, ← pow_succ']

private theorem perm_pow_mod_minimalPeriod {ι : Type*} (σ : Equiv.Perm ι) (x : ι) (n : ℕ) :
    (σ ^ (n % Function.minimalPeriod (σ • ·) x)) x = (σ ^ n) x := by
  simpa only [← iterate_perm_smul] using Function.iterate_mod_minimalPeriod_eq (f := (σ • ·))

private theorem perm_inv_orbitFinEquiv_symm {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    (q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι)
    (t : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out)) :
    σ⁻¹ ((orbitFinEquiv σ).symm ⟨q, t⟩) = (orbitFinEquiv σ).symm ⟨q, t + 1⟩ := by
  rw [orbitFinEquiv_symm_apply, orbitFinEquiv_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ']
  have hval : (t + 1).val = (t.val + 1) % Function.minimalPeriod (σ⁻¹ • ·) q.out := by
    simp [Fin.val_add, Nat.add_mod_mod]
  rw [hval, perm_pow_mod_minimalPeriod]

private theorem trace_toMatrix_list_ofFn {R κ M : Type*} [CommSemiring R] [Fintype κ]
    [DecidableEq κ] [AddCommMonoid M] [Module R M] (b : Module.Basis κ R M)
    (L : List (M →ₗ[R] M)) :
    (L.map (fun g ↦ toMatrix b b g)).prod.trace = trace R M L.prod := by
  rw [trace_eq_matrix_trace R b]
  congr 1
  induction L with
  | nil => simp
  | cons g gs ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp, toMatrix_comp b b b,
      ih]

private theorem trace_list_ofFn_shift {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {k : ℕ} [NeZero k] (g : Fin k → M →ₗ[R] M) (r : ℕ) :
    trace R M (List.ofFn g).prod =
      trace R M (List.ofFn fun t : Fin k ↦
        g ⟨(t.val + r) % k, Nat.mod_lt _ (NeZero.pos k)⟩).prod := by
  induction r with
  | zero =>
    congr 2
    refine List.ext_get (by simp) fun i hi _ ↦ ?_
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, List.get_eq_getElem]
    congr 1; ext; simp [Nat.mod_eq_of_lt hi]
  | succ r ih =>
    rw [ih]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
    let h (t : Fin (n + 1)) : M →ₗ[R] M :=
      g ⟨(t.val + r) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
    have hlist :
        (List.ofFn fun t : Fin (n + 1) ↦
            g ⟨(t.val + (r + 1)) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩) =
          List.ofFn (fun t : Fin n ↦ h t.succ) ++ [h 0] := by
      refine List.ext_get (by simp) fun i hi₁ _ ↦ ?_
      simp only [List.length_ofFn] at hi₁
      simp only [List.get_eq_getElem]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi₁) with hlt | heq
      · have hlen : i < (List.ofFn fun t : Fin n ↦ h t.succ).length := by simpa using hlt
        rw [List.getElem_append_left hlen]
        simp only [List.getElem_ofFn, h]
        congr 1; ext; simp only [Fin.val_succ]; rw [Nat.add_assoc, Nat.add_comm 1 r]
      · have hle : (List.ofFn fun t : Fin n ↦ h t.succ).length ≤ i := by simp [heq]
        rw [List.getElem_append_right hle]
        simp only [List.length_ofFn, heq, Nat.sub_self, List.getElem_singleton,
          List.getElem_ofFn, h, Fin.val_zero, zero_add]
        congr 1; ext; simp only; rw [Nat.add_left_comm, Nat.add_mod_right]
    rw [hlist, List.prod_append, List.prod_singleton, trace_mul_comm, ← List.prod_cons,
      ← List.ofFn_succ]

private theorem trace_piTensorProduct_map_comp_reindex_inv_sum {R ι M : Type*}
    [CommSemiring R] [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module R M]
    [Module.Free R M] [Fintype (Module.Free.ChooseBasisIndex R M)]
    (f : ι → (M →ₗ[R] M)) (σ : Equiv.Perm ι)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι)]
    [DecidableEq (MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι)] :
    let b := Module.Free.chooseBasis R M
    (∑ p : ι → Module.Free.ChooseBasisIndex R M,
        ∏ i : ι, b.repr (f i (b (p (Equiv.symm σ i)))) (p i)) =
      ∑ d : (∀ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι,
          Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out) → Module.Free.ChooseBasisIndex R M),
        ∏ q, ∏ t : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out),
          (toMatrix b b (f ((σ⁻¹ ^ (t : ℕ)) q.out))) (d q t) (d q (t + 1)) := by
  classical
  let ePi : (∀ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι,
      Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out) →
        Module.Free.ChooseBasisIndex R M) ≃
      (ι → Module.Free.ChooseBasisIndex R M) :=
    (Equiv.piCurry _).symm.trans
      (Equiv.piCongrLeft' (fun _ ↦ Module.Free.ChooseBasisIndex R M) (orbitFinEquiv σ).symm)
  refine (Fintype.sum_equiv ePi _ _ fun d ↦ ?_).symm
  rw [← (Fintype.prod_equiv (orbitFinEquiv σ).symm _ _ fun _ ↦ rfl), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun q _ ↦ Finset.prod_congr rfl fun t _ ↦ ?_
  have hs : ePi d ((orbitFinEquiv σ).symm ⟨q, t⟩) = d q t := by
    simp only [ePi, Equiv.trans_apply, Equiv.piCongrLeft'_apply, Equiv.piCurry_symm_apply,
      Sigma.uncurry]
    rw [Equiv.symm_symm, (orbitFinEquiv σ).apply_symm_apply]
  have hs1 : ePi d (Equiv.symm σ ((orbitFinEquiv σ).symm ⟨q, t⟩)) = d q (t + 1) := by
    -- Identify `Equiv.symm σ` on `Equiv.Perm ι` with `σ⁻¹` for `perm_inv_orbitFinEquiv_symm`.
    change ePi d (σ⁻¹ ((orbitFinEquiv σ).symm ⟨q, t⟩)) = d q (t + 1)
    rw [perm_inv_orbitFinEquiv_symm]
    simp only [ePi, Equiv.trans_apply, Equiv.piCongrLeft'_apply, Equiv.piCurry_symm_apply,
      Sigma.uncurry]
    rw [Equiv.symm_symm, (orbitFinEquiv σ).apply_symm_apply]
  rw [orbitFinEquiv_symm_apply] at hs hs1 ⊢
  rw [hs, hs1, toMatrix_apply]

private theorem trace_piTensorProduct_map_comp_reindex_inv {R ι M : Type*}
    [CommSemiring R] [Finite ι] [AddCommMonoid M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (f : ι → (M →ₗ[R] M)) (σ : Equiv.Perm ι)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι)] :
    trace R (⨂[R] _ : ι, M)
        (PiTensorProduct.map f ∘ₗ (PiTensorProduct.reindex R (fun _ : ι ↦ M) σ).toLinearMap) =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι,
        trace R M
          (List.ofFn fun t : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out) ↦
            f ((σ⁻¹ ^ (t : ℕ)) q.out)).prod := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex R M)
  let b := Module.Free.chooseBasis R M
  let B := Basis.piTensorProduct fun _ : ι ↦ b
  rw [trace_eq_matrix_trace R B, Matrix.trace]
  simp_rw [Matrix.diag_apply, toMatrix_apply, comp_apply, LinearEquiv.coe_coe,
    B, Basis.piTensorProduct_apply, PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  rw [trace_piTensorProduct_map_comp_reindex_inv_sum f σ]
  have hps :
      (∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι,
          ∑ dq : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out) → Module.Free.ChooseBasisIndex R M,
            ∏ t : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out),
              (toMatrix b b (f ((σ⁻¹ ^ (t : ℕ)) q.out))) (dq t) (dq (t + 1))) =
        ∑ d : (∀ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι,
            Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out) → Module.Free.ChooseBasisIndex R M),
          ∏ q, ∏ t : Fin (Function.minimalPeriod (σ⁻¹ • ·) q.out),
            (toMatrix b b (f ((σ⁻¹ ^ (t : ℕ)) q.out))) (d q t) (d q (t + 1)) :=
    Fintype.prod_sum _
  rw [← hps]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  have : NeZero (Function.minimalPeriod (σ⁻¹ • ·) q.out) :=
    ⟨(minimalPeriod_pos_of_finite σ⁻¹ q.out).ne'⟩
  rw [← Matrix.trace_list_ofFn_prod, ← trace_toMatrix_list_ofFn b, List.map_ofFn]
  rfl

private theorem orbitRel_zpowers_inv_iff {ι : Type*} (σ : Equiv.Perm ι) (x y : ι) :
    MulAction.orbitRel (Subgroup.zpowers σ⁻¹) ι x y ↔
      MulAction.orbitRel (Subgroup.zpowers σ) ι x y := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor <;> rintro ⟨⟨_, k, rfl⟩, hy⟩
  · refine ⟨⟨σ ^ (-k), -k, rfl⟩, ?_⟩
    -- Unfold the `zpowers` subtype action into permutation powers.
    change (σ ^ (-k)) • y = x
    change ((σ⁻¹) ^ k) • y = x at hy
    simpa [Equiv.Perm.smul_def, inv_zpow, zpow_neg] using hy
  · refine ⟨⟨(σ⁻¹) ^ (-k), -k, rfl⟩, ?_⟩
    -- Unfold the `zpowers` subtype action into permutation powers.
    change ((σ⁻¹) ^ (-k)) • y = x
    change (σ ^ k) • y = x at hy
    simpa [Equiv.Perm.smul_def, inv_zpow, zpow_neg] using hy

private theorem exists_pow_eq_of_orbitRel {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    {x y : ι} (h : MulAction.orbitRel (Subgroup.zpowers σ⁻¹) ι x y) :
    ∃ r : ℕ, (σ⁻¹ ^ r) x = y := by
  obtain ⟨⟨_, k, rfl⟩, hy⟩ := MulAction.mem_orbit_iff.mp h
  let m := Function.minimalPeriod (σ⁻¹ • ·) x
  have hm : 0 < m := minimalPeriod_pos_of_finite σ⁻¹ x
  have hnonneg : (0 : ℤ) ≤ (-k) % (m : ℤ) := Int.emod_nonneg (-k) (by exact_mod_cast hm.ne')
  refine ⟨((-k) % (m : ℤ)).toNat, ?_⟩
  have hy' : (σ⁻¹ ^ k) • y = x := hy
  have hx : (σ⁻¹ ^ (-k)) • x = y := by
    rw [← hy', ← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul]
  rw [← Equiv.Perm.smul_def, ← zpow_natCast, Int.toNat_of_nonneg hnonneg,
    MulAction.zpow_smul_mod_minimalPeriod, hx]

private theorem trace_orbit_change_rep {R ι M : Type*} [CommSemiring R] [Finite ι]
    [AddCommMonoid M] [Module R M] (f : ι → M →ₗ[R] M) (σ : Equiv.Perm ι) {x y : ι}
    (horb : MulAction.orbitRel (Subgroup.zpowers σ⁻¹) ι x y) :
    trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ⁻¹ • ·) x) ↦
        f ((σ⁻¹ ^ (t : ℕ)) x)).prod =
      trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) y) ↦
        f ((σ⁻¹ ^ (t : ℕ)) y)).prod := by
  have hper : Function.minimalPeriod (σ⁻¹ • ·) x = Function.minimalPeriod (σ • ·) y :=
    (minimalPeriod_inv_perm σ x).trans
      (minimalPeriod_eq_of_orbitRel σ ((orbitRel_zpowers_inv_iff σ x y).mp horb))
  obtain ⟨r, hr⟩ := exists_pow_eq_of_orbitRel σ horb
  have : NeZero (Function.minimalPeriod (σ⁻¹ • ·) x) := ⟨(minimalPeriod_pos_of_finite σ⁻¹ x).ne'⟩
  rw [trace_list_ofFn_shift _ r]
  refine congrArg (trace R M) (congrArg List.prod ?_)
  have hlen : (List.ofFn fun t : Fin (Function.minimalPeriod (σ⁻¹ • ·) x) ↦
        f ((σ⁻¹ ^ ((t.val + r) % Function.minimalPeriod (σ⁻¹ • ·) x)) x)).length =
      (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) y) ↦
        f ((σ⁻¹ ^ (t : ℕ)) y)).length := by
    simp only [List.length_ofFn, hper]
  refine List.ext_get hlen fun i _ _ ↦ ?_
  simp only [List.getElem_ofFn, List.get_eq_getElem]
  rw [← hr]
  congr 1
  rw [← Equiv.Perm.mul_apply, ← pow_add, perm_pow_mod_minimalPeriod, ← perm_pow_mod_minimalPeriod,
    Nat.add_comm i r]

/-- **Cycle-product trace formula for a monomial endomorphism.** On an indexed tensor power
`⨂[R] _ : ι, M`, composing a permutation `σ` of the factors with a family of factor
endomorphisms `f : ι → M →ₗ[R] M` has trace equal to the product over the cycles of `σ` of the
trace of the ordered composition of the factor maps along each cycle. If `ι` is nonempty and `M`
is not finitely generated, both sides evaluate to `0`. -/
theorem trace_piTensorProduct_map_comp_reindex {R ι M : Type*}
    [CommSemiring R] [Finite ι] [AddCommMonoid M] [Module R M]
    [Module.Free R M]
    (f : ι → (M →ₗ[R] M)) (σ : Equiv.Perm ι)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι)] :
    trace R (⨂[R] _ : ι, M)
        (PiTensorProduct.map f ∘ₗ (PiTensorProduct.reindex R (fun _ : ι ↦ M) σ).toLinearMap) =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        trace R M
          (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) q.out) ↦
            f ((σ⁻¹ ^ (t : ℕ)) q.out)).prod := by
  classical
  by_cases hfin : Module.Finite R M
  · let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι)
    rw [trace_piTensorProduct_map_comp_reindex_inv]
    let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers σ⁻¹) ι ≃
        MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι :=
      Quotient.congrRight (orbitRel_zpowers_inv_iff σ)
    refine Fintype.prod_equiv qEquiv _ _ fun q ↦ trace_orbit_change_rep f σ ?_
    have hq : Quotient.mk'' q.out = qEquiv q := by
      conv_rhs => rw [← Quotient.out_eq q]
      rfl
    have hmk : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι) =
        Quotient.mk'' (qEquiv q).out :=
      hq.trans (Quotient.out_eq (qEquiv q)).symm
    exact (orbitRel_zpowers_inv_iff σ q.out (qEquiv q).out).mpr (Quotient.exact' hmk)
  · by_cases hempty : IsEmpty ι
    · let b := Module.Free.chooseBasis R M
      let B := Basis.piTensorProduct fun _ : ι ↦ b
      have : Unique (ι → Module.Free.ChooseBasisIndex R M) := Pi.uniqueOfIsEmpty _
      have : IsEmpty (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι) :=
        ⟨fun q ↦ hempty.false q.out⟩
      let := Fintype.ofFinite (ι → Module.Free.ChooseBasisIndex R M)
      let := Fintype.ofIsEmpty (α := ι)
      rw [trace_eq_matrix_trace R B, Matrix.trace, Fintype.sum_unique, Fintype.prod_empty]
      simp [Matrix.diag_apply, toMatrix_apply, B, Basis.piTensorProduct_apply,
        PiTensorProduct.reindex_tprod, Basis.piTensorProduct_repr_tprod_apply]
    · obtain ⟨i₀⟩ := not_isEmpty_iff.mp hempty
      have : Infinite (Module.Free.ChooseBasisIndex R M) :=
        not_finite_iff_infinite.mp fun _ ↦
          hfin (Module.Finite.of_basis (Module.Free.chooseBasis R M))
      have hinj : Function.Injective (fun (x : Module.Free.ChooseBasisIndex R M) (_ : ι) ↦ x) :=
        fun _ _ h ↦ congrFun h i₀
      have : Infinite (ι → Module.Free.ChooseBasisIndex R M) :=
        Infinite.of_injective _ hinj
      rw [trace_eq_zero_of_infinite_basis (Basis.piTensorProduct fun _ : ι ↦
          Module.Free.chooseBasis R M) _,
        Finset.prod_eq_zero (Finset.mem_univ (Quotient.mk'' i₀))
          (trace_eq_zero_of_not_finite_of_free hfin _)]

end LinearMap

namespace Representation

/-- **Trace of a wreath tensor product representation.** At `(a, σ)` in the permutation wreath
product `(ι → D) ⋊ Perm ι`, the trace on `⨂[R] _ : ι, M` equals the product over the cycles of `σ`
of the trace of `ρ` at the ordered cycle product of `a`. -/
theorem trace_wreathTensor {R D M : Type*} [CommSemiring R] [Group D]
    [AddCommMonoid M] [Module R M] [Module.Free R M]
    (ρ : Representation R D M) (ι : Type*) [Finite ι] (a : TauCeti.WreathProduct D ι)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers a.right) ι)] :
    LinearMap.trace R (⨂[R] _ : ι, M) (ρ.wreathTensor ι a) =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers a.right) ι,
        LinearMap.trace R M
          (ρ (List.ofFn fun t : Fin (Function.minimalPeriod (a.right • ·) q.out) ↦
            a.left ((a.right⁻¹ ^ (t : ℕ)) q.out)).prod) := by
  rw [wreathTensor_apply, LinearMap.trace_piTensorProduct_map_comp_reindex]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  congr 1
  rw [map_list_prod, List.map_ofFn]
  rfl

end Representation

namespace Subgroup

private theorem lWord_list_ofFn_prod {G : Type*} [Group G] (U : Subgroup G) (r : G ⧸ U → G)
    (q : G ⧸ U) (g : G) (m : ℕ) :
    (List.ofFn fun t : Fin m ↦ TauCeti.lWord U r ((g⁻¹ ^ (t : ℕ)) • q) g).prod =
      TauCeti.lWord U r q (g ^ m) := by
  induction m generalizing q with
  | zero => simp [TauCeti.lWord_one]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have hstep : (fun t : Fin m ↦ TauCeti.lWord U r ((g⁻¹ ^ (t.succ : ℕ)) • q) g) =
        fun t : Fin m ↦ TauCeti.lWord U r ((g⁻¹ ^ (t : ℕ)) • (g⁻¹ • q)) g := by
      funext t
      rw [Fin.val_succ, pow_succ, mul_smul]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rw [hstep, ih (g⁻¹ • q), TauCeti.lWord_mul_lWord, ← pow_succ']

private theorem smul_pow_minimalPeriod {G α : Type*} [Group G] [MulAction G α] (g : G) (q : α) :
    g ^ Function.minimalPeriod (g • ·) q • q = q := by
  have hiter : ∀ n : ℕ, (g • ·)^[n] q = g ^ n • q := fun n ↦ by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  rw [← hiter, Function.iterate_minimalPeriod]

private theorem inv_smul_pow_minimalPeriod {G α : Type*} [Group G] [MulAction G α]
    (g : G) (q : α) :
    (g ^ Function.minimalPeriod (g • ·) q)⁻¹ • q = q :=
  inv_smul_eq_iff.mpr (smul_pow_minimalPeriod g q).symm

/-- For any coset representative `r` of `q : G ⧸ U`, conjugating `g ^ minimalPeriod (g • ·) q`
by `r` stays inside `U`. -/
theorem conj_pow_minimalPeriod_mem {G : Type*} [Group G] (U : Subgroup G) (g : G)
    {q : G ⧸ U} {r : G} (hr : (QuotientGroup.mk r : G ⧸ U) = q) :
    r⁻¹ * g ^ Function.minimalPeriod (g • ·) q * r ∈ U := by
  have hq : (QuotientGroup.mk r : G ⧸ U) =
      QuotientGroup.mk (g ^ Function.minimalPeriod (g • ·) q * r) := by
    rw [hr]
    -- Rewrite multiplication on cosets as the group action so `smul_pow_minimalPeriod` applies.
    change q = (g ^ Function.minimalPeriod (g • ·) q) • (QuotientGroup.mk r : G ⧸ U)
    rw [hr, smul_pow_minimalPeriod]
  simpa [mul_assoc] using QuotientGroup.leftRel_apply.mp (Quotient.exact' hq)

private theorem minimalPeriod_smul_eq_of_orbitRel {G : Type*} [Group G] (U : Subgroup G) (g : G)
    {x y : G ⧸ U} (h : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U) x y) :
    Function.minimalPeriod (g • ·) x = Function.minimalPeriod (g • ·) y := by
  rw [← MulAction.natCard_orbit_zpowers g x, ← MulAction.natCard_orbit_zpowers g y]
  exact congrArg (fun S : Set (G ⧸ U) ↦ Nat.card S) (MulAction.orbit_eq_iff.mpr h)

/-- **Orbit-representative invariance of cycle monodromy.** When `f : U → R` is invariant under
`U`-conjugation, `f` takes the same value on the cycle monodromy `r⁻¹ * g ^ m * r` for any two
coset representatives of points in the same `⟨g⟩`-orbit of `G ⧸ U`. -/
theorem apply_conj_pow_minimalPeriod_eq_of_orbitRel {R G : Type*} [Group G] {U : Subgroup G}
    {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u) (g : G) {x y : G ⧸ U}
    (h : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U) x y) {rx ry : G}
    (hrx : (QuotientGroup.mk rx : G ⧸ U) = x) (hry : (QuotientGroup.mk ry : G ⧸ U) = y) :
    f ⟨ry⁻¹ * g ^ Function.minimalPeriod (g • ·) y * ry,
        conj_pow_minimalPeriod_mem U g hry⟩ =
      f ⟨rx⁻¹ * g ^ Function.minimalPeriod (g • ·) x * rx,
        conj_pow_minimalPeriod_mem U g hrx⟩ := by
  obtain ⟨⟨_, k, rfl⟩, hxy⟩ := MulAction.mem_orbit_iff.mp h
  let m := Function.minimalPeriod (g • ·) x
  have hm : Function.minimalPeriod (g • ·) y = m :=
    (minimalPeriod_smul_eq_of_orbitRel U g h).symm
  have hxy' : g ^ (-k) • x = y := by
    have hxy0 : g ^ k • y = x := hxy
    rw [← hxy0, ← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul]
  have hmk : (QuotientGroup.mk (g ^ (-k) * rx) : G ⧸ U) = QuotientGroup.mk ry := by
    rw [hry, ← hxy']
    -- Rewrite left multiplication on cosets as the group action on `G ⧸ U`.
    change (g ^ (-k)) • (QuotientGroup.mk rx : G ⧸ U) = g ^ (-k) • x
    rw [hrx]
  let v : U := ⟨(g ^ (-k) * rx)⁻¹ * ry, QuotientGroup.leftRel_apply.mp (Quotient.exact' hmk)⟩
  have hcomm : g ^ (-k) * g ^ m * (g ^ (-k))⁻¹ = g ^ m := by
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1; omega
  have hconj : (⟨ry⁻¹ * g ^ Function.minimalPeriod (g • ·) y * ry,
      conj_pow_minimalPeriod_mem U g hry⟩ : U) =
      v⁻¹ * ⟨rx⁻¹ * g ^ m * rx, conj_pow_minimalPeriod_mem U g hrx⟩ * (v⁻¹)⁻¹ := by
    ext
    simp only [hm, v, inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv]
    calc
      ry⁻¹ * g ^ m * ry = ry⁻¹ * (g ^ (-k) * g ^ m * (g ^ (-k))⁻¹) * ry := by rw [hcomm]
      _ = ((g ^ (-k) * rx)⁻¹ * ry)⁻¹ * (rx⁻¹ * g ^ m * rx) * ((g ^ (-k) * rx)⁻¹ * ry) := by
        simp [mul_assoc]
  rw [hconj, hf]

/-- **The canonical tensor-induced function of a finite-index subgroup.** For a finite-index
subgroup `U ≤ G` and a function `f : U → R` into a commutative monoid, `U.tensorIndClassFun f g`
is the product over the `⟨g⟩`-orbits on `G ⧸ U` of `f` evaluated at the cycle monodromy
`q.out.out⁻¹ * g ^ m * q.out.out ∈ U`. When `f` is invariant under `U`-conjugation, this agrees
with `LinearMap.trace R M (U.tensorInducedRepresentation s ρ g)` for every left transversal `s`
(`Subgroup.trace_tensorInducedRepresentation`) and is invariant under `G`-conjugation. -/
noncomputable def tensorIndClassFun {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] (f : U → R) (g : G) : R :=
  letI := U.fintypeQuotientOfFiniteIndex
  letI : Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U)) := Fintype.ofFinite _
  ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U),
    f ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem U g q.out⟩

/-- The defining orbit-product formula for `Subgroup.tensorIndClassFun` using any `Fintype`
instance on the `⟨g⟩`-orbits of `G ⧸ U`. -/
theorem tensorIndClassFun_def {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] (f : U → R) (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    U.tensorIndClassFun f g =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U),
        f ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem U g q.out⟩ := by
  rw [tensorIndClassFun]
  convert rfl

/-- When `f : U → R` is invariant under `U`-conjugation, `Subgroup.tensorIndClassFun U f g` can be
evaluated using any choice of coset representatives `r : G ⧸ U → G`. -/
theorem tensorIndClassFun_eq_prod_of_rep {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u)
    (r : G ⧸ U → G) (hr : ∀ q, (QuotientGroup.mk (r q) : G ⧸ U) = q) (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    U.tensorIndClassFun f g =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U),
        f ⟨(r q.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * r q.out,
          conj_pow_minimalPeriod_mem U g (hr q.out)⟩ := by
  rw [tensorIndClassFun_def]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  exact apply_conj_pow_minimalPeriod_eq_of_orbitRel hf g (MulAction.mem_orbit_self q.out)
    (hr q.out) (QuotientGroup.out_eq' q.out)

private theorem trace_rep_conj_invariant {R U M : Type*} [CommSemiring R] [Group U]
    [AddCommMonoid M] [Module R M] (ρ : Representation R U M) (u v : U) :
    LinearMap.trace R M (ρ (v * u * v⁻¹)) = LinearMap.trace R M (ρ u) := by
  rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, inv_mul_cancel,
    map_one, one_mul]

private theorem monomialHom_right_zpow_smul {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) (g : G) (n : ℤ) (z : G ⧸ U) :
    ((U.monomialHom s g).right ^ n) • z = (g ^ n) • z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_comm, zpow_one_add, mul_smul, ih, Equiv.Perm.smul_def, Subgroup.monomialHom_right,
      ← mul_smul, ← zpow_one_add, add_comm]
  | pred n ih =>
    rw [sub_eq_add_neg, add_comm, zpow_add, mul_smul, ih, zpow_neg_one, Equiv.Perm.smul_def,
      Subgroup.monomialHom_right_inv, ← mul_smul, ← zpow_neg_one, ← zpow_add, add_comm,
      ← sub_eq_add_neg]

/-- **Cycle monodromy of `Subgroup.monomialHom`.** Along a coset cycle generated by `g`, the
ordered product of the base coordinates of `U.monomialHom s g` equals the cycle monodromy
`r⁻¹ * g ^ m * r ∈ U` attached to the transversal representative `r = U.leftTransversalRep s q₀`. -/
theorem monomialHom_orbit_prod {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) (g : G) (q₀ : G ⧸ U) :
    ((List.ofFn fun t : Fin (Function.minimalPeriod ((U.monomialHom s g).right • ·) q₀) ↦
        (U.monomialHom s g).left
          (((U.monomialHom s g).right⁻¹ ^ (t : ℕ)) q₀)).prod : U) =
      ⟨(U.leftTransversalRep s q₀)⁻¹ *
          g ^ Function.minimalPeriod (g • ·) q₀ * U.leftTransversalRep s q₀,
        conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s q₀)⟩ := by
  have hper : Function.minimalPeriod ((U.monomialHom s g).right • ·) q₀ =
      Function.minimalPeriod (g • ·) q₀ := by
    congr 1; ext x; exact Subgroup.monomialHom_right U s g x
  have hact : ∀ (t : ℕ) (z : G ⧸ U),
      ((U.monomialHom s g).right⁻¹ ^ t) z = (g⁻¹ ^ t) • z := fun t z ↦ by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', Equiv.Perm.mul_apply, Subgroup.monomialHom_right_inv, ih,
        ← mul_smul, ← pow_succ']
  ext
  rw [Subgroup.val_list_prod, List.map_ofFn]
  have hlist :
      (List.ofFn (Subtype.val ∘ fun t :
          Fin (Function.minimalPeriod ((U.monomialHom s g).right • ·) q₀) ↦
          (U.monomialHom s g).left (((U.monomialHom s g).right⁻¹ ^ (t : ℕ)) q₀))) =
        List.ofFn fun t : Fin (Function.minimalPeriod (g • ·) q₀) ↦
          TauCeti.lWord U (U.leftTransversalRep s) ((g⁻¹ ^ (t : ℕ)) • q₀) g :=
    List.ext_get (by simp only [List.length_ofFn, hper]) fun i _ _ ↦ by
      simp only [List.getElem_ofFn, List.get_eq_getElem, Function.comp_apply,
        Subgroup.monomialHom_left]
      rw [hact]
  rw [hlist, lWord_list_ofFn_prod, TauCeti.lWord_def, inv_smul_pow_minimalPeriod]

/-- **Trace of a tensor-induced representation.** For any finite-index subgroup `U ≤ G`, any left
transversal `s`, and any representation `ρ` of `U` on a free `R`-module `M`, the trace of
`U.tensorInducedRepresentation s ρ g` equals `U.tensorIndClassFun (fun u ↦ trace R M (ρ u)) g`
and in particular does not depend on `s`. -/
theorem trace_tensorInducedRepresentation {R G M : Type*} [CommSemiring R] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (s : U.LeftTransversal)
    [AddCommMonoid M] [Module R M] [Module.Free R M]
    (ρ : Representation R U M) (g : G) :
    LinearMap.trace R (⨂[R] _ : G ⧸ U, M) (U.tensorInducedRepresentation s ρ g) =
      U.tensorIndClassFun (fun u ↦ LinearMap.trace R M (ρ u)) g := by
  let := U.fintypeQuotientOfFiniteIndex
  let := Fintype.ofFinite
    (MulAction.orbitRel.Quotient (Subgroup.zpowers (U.monomialHom s g).right) (G ⧸ U))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
  have hdef : U.tensorInducedRepresentation s ρ g = ρ.wreathTensor (G ⧸ U) (U.monomialHom s g) :=
    LinearMap.ext fun z ↦ Subgroup.tensorInducedRepresentation_apply U s ρ g z
  rw [hdef, Representation.trace_wreathTensor, tensorIndClassFun_eq_prod_of_rep U
    (trace_rep_conj_invariant ρ) (U.leftTransversalRep s) (U.leftTransversalRep_mk s)]
  let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers (U.monomialHom s g).right) (G ⧸ U) ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) :=
    Quotient.congrRight fun x y ↦ by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      constructor <;> rintro ⟨⟨_, k, rfl⟩, hy⟩
      · refine ⟨⟨g ^ k, k, rfl⟩, ?_⟩
        -- Unfold the `zpowers` subtype action into group powers.
        change g ^ k • y = x
        change ((U.monomialHom s g).right ^ k) • y = x at hy
        rwa [monomialHom_right_zpow_smul] at hy
      · refine ⟨⟨(U.monomialHom s g).right ^ k, k, rfl⟩, ?_⟩
        -- Unfold the `zpowers` subtype action into permutation powers.
        change ((U.monomialHom s g).right ^ k) • y = x
        change g ^ k • y = x at hy
        rwa [monomialHom_right_zpow_smul]
  refine Fintype.prod_equiv qEquiv _ _ fun q ↦ ?_
  rw [monomialHom_orbit_prod]
  refine apply_conj_pow_minimalPeriod_eq_of_orbitRel
    (f := fun u ↦ LinearMap.trace R M (ρ u)) (trace_rep_conj_invariant ρ) g ?_
    (U.leftTransversalRep_mk s (qEquiv q).out) (U.leftTransversalRep_mk s q.out)
  have hq : Quotient.mk'' q.out = qEquiv q := by
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  exact Quotient.exact' ((Quotient.out_eq (qEquiv q)).trans hq.symm)

/-- **Character of a tensor-induced representation.** Over any field `k`, the character of
`U.tensorInducedRepresentation s ρ` equals `U.tensorIndClassFun ρ.character`. -/
theorem character_tensorInducedRepresentation {k G V : Type*} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (s : U.LeftTransversal)
    [AddCommGroup V] [Module k V]
    (ρ : Representation k U V) :
    (U.tensorInducedRepresentation s ρ).character = U.tensorIndClassFun ρ.character := by
  ext g
  exact trace_tensorInducedRepresentation U s ρ g

private theorem minimalPeriod_conj_smul {G α : Type*} [Group G] [MulAction G α] (g c : G) (x : α) :
    Function.minimalPeriod ((c * g * c⁻¹) • ·) (c • x) = Function.minimalPeriod (g • ·) x := by
  refine Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ ?_
  have hiter : ∀ (m : ℕ) (z : α), ((c * g * c⁻¹) • ·)^[m] (c • z) = c • ((g • ·)^[m] z) := by
    intro m z
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [← mul_smul, mul_assoc]
  simp [Function.IsPeriodicPt, Function.IsFixedPt, hiter]

/-- **Conjugation invariance of `Subgroup.tensorIndClassFun`.** If `f : U → R` is invariant under
`U`-conjugation, then `U.tensorIndClassFun f` is invariant under `G`-conjugation. -/
theorem tensorIndClassFun_conj {R G : Type*} [CommMonoid R] [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → R}
    (hf : ∀ u v : U, f (v * u * v⁻¹) = f u) (g c : G) :
    U.tensorIndClassFun f (c * g * c⁻¹) = U.tensorIndClassFun f g := by
  let := U.fintypeQuotientOfFiniteIndex
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers (c * g * c⁻¹)) (G ⧸ U))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
  rw [tensorIndClassFun_def, tensorIndClassFun_def]
  have heq : ∀ (n : ℤ) (q : G ⧸ U), (c * g * c⁻¹) ^ n • (c • q) = c • (g ^ n • q) := by
    intro n q
    rw [conj_zpow, ← mul_smul, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul]
  let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers (c * g * c⁻¹)) (G ⧸ U) :=
    Quotient.congr (MulAction.toPerm c) fun x y ↦ by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
      constructor
      · rintro ⟨⟨_, k, rfl⟩, rfl⟩
        refine ⟨⟨(c * g * c⁻¹) ^ k, k, rfl⟩, ?_⟩
        -- Unfold the `zpowers` subtype action into group powers.
        change (c * g * c⁻¹) ^ k • (c • y) = c • (g ^ k • y)
        exact heq k y
      · rintro ⟨⟨_, k, rfl⟩, h⟩
        refine ⟨⟨g ^ k, k, rfl⟩, (MulAction.toPerm c).injective ?_⟩
        -- Expose the `zpowers` subtype action as group-power multiplication.
        change (c * g * c⁻¹) ^ k • (c • y) = c • x at h
        rw [MulAction.toPerm_apply]
        -- Expose the `zpowers` subtype action so `heq` rewrites the LHS.
        change c • (g ^ k • y) = c • x
        rwa [← heq]
  refine (Fintype.prod_equiv qEquiv _ _ fun q ↦ ?_).symm
  have hrep : (QuotientGroup.mk (c * q.out.out) : G ⧸ U) = c • q.out := by
    -- Rewrite left multiplication on cosets as the left action of `G` on `G ⧸ U`.
    change c • (QuotientGroup.mk q.out.out : G ⧸ U) = c • q.out
    rw [QuotientGroup.out_eq']
  have hq : qEquiv q = Quotient.mk'' (c • q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have horb : MulAction.orbitRel (Subgroup.zpowers (c * g * c⁻¹)) (G ⧸ U)
      (qEquiv q).out (c • q.out) :=
    Quotient.exact' ((Quotient.out_eq (qEquiv q)).trans hq)
  rw [← apply_conj_pow_minimalPeriod_eq_of_orbitRel hf (c * g * c⁻¹) horb
    (QuotientGroup.out_eq' (qEquiv q).out) hrep]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [minimalPeriod_conj_smul, conj_pow]
  simp [mul_assoc]

/-- If `f` is a class function on a finite-index subgroup `U ≤ G`, then `U.tensorIndClassFun f`
is a class function on `G`. -/
theorem tensorIndClassFun_mem_classFunction {k G : Type*} [CommSemiring k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → k} (hf : f ∈ TauCeti.ClassFunction k U) :
    U.tensorIndClassFun f ∈ TauCeti.ClassFunction k G := by
  refine TauCeti.ClassFunction.mem_iff.mpr fun g c ↦ ?_
  exact tensorIndClassFun_conj U (fun u v ↦ TauCeti.ClassFunction.mem_iff.mp hf u v) g c

private theorem mem_normal_smul_quotient {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (h : H) (q : G ⧸ H) : (h : G) • q = q := by
  induction q using Quotient.inductionOn' with | h y =>
  refine Quotient.sound' (QuotientGroup.leftRel_apply.mpr ?_)
  simpa [mul_assoc] using ‹H.Normal›.conj_mem _ (H.inv_mem h.property) y⁻¹

private theorem zpow_smul_quotient_of_normal {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (h : H) (k : ℤ) (y : G ⧸ H) : ((h : G) ^ k) • y = y := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, mem_normal_smul_quotient, ih]
  | pred n ih =>
    rw [zpow_sub_one, mul_smul, inv_smul_eq_iff.mpr (mem_normal_smul_quotient H h _).symm, ih]

/-- **Normal-subgroup evaluation on `H`.** For a finite-index normal subgroup `H ≤ G` and any
function `f : H → R`, evaluating `H.tensorIndClassFun f` at `h : H` gives the product of `f` over
all coset conjugates `q.out⁻¹ * h * q.out`. -/
theorem tensorIndClassFun_apply_of_mem_of_normal {R G : Type*} [CommMonoid R] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] (f : H → R) (h : H) :
    H.tensorIndClassFun f h =
      letI := H.fintypeQuotientOfFiniteIndex
      ∏ q : G ⧸ H, f (MulAut.conjNormal q.out⁻¹ h) := by
  let := H.fintypeQuotientOfFiniteIndex
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers (h : G)) (G ⧸ H))
  rw [tensorIndClassFun_def]
  let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers (h : G)) (G ⧸ H) ≃ G ⧸ H :=
    { toFun := Quotient.lift id fun x y hxy ↦ by
        obtain ⟨⟨_, k, rfl⟩, rfl⟩ := MulAction.mem_orbit_iff.mp hxy
        exact zpow_smul_quotient_of_normal H h k y
      invFun := Quotient.mk''
      left_inv := fun q ↦ Quotient.inductionOn' q fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine Fintype.prod_equiv qEquiv _ _ fun q ↦ ?_
  have hper : Function.minimalPeriod (fun x : G ⧸ H ↦ (h : G) • x) q.out = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (mem_normal_smul_quotient H h q.out)
  have hmk : q.out = qEquiv q := by
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  have helem :
      (⟨q.out.out⁻¹ * (h : G) ^ Function.minimalPeriod (fun x : G ⧸ H ↦ (h : G) • x) q.out *
          q.out.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H (h : G) q.out⟩ : H) =
        MulAut.conjNormal q.out.out⁻¹ h := by
    apply Subtype.ext
    dsimp only
    rw [hper, pow_one, MulAut.conjNormal_apply, inv_inv]
  rw [helem, ← hmk]

end Subgroup
