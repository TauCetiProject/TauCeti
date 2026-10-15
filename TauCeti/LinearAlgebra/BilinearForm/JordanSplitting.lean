/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Modular
import TauCeti.Algebra.Module.Submodule.Finite
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Nakayama
import TauCeti.LinearAlgebra.BilinearForm.Ideals
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Jordan splittings over a discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `π`. A **Jordan splitting** of a bilinear
form `B` on an `R`-module `M` is a decomposition `M = ⊕_i N_i` into pairwise orthogonal
submodules such that the restriction of `B` to `N_i` is `π ^ i`-modular: `π ^ i` times a perfect
pairing (`LinearMap.BilinForm.IsJordanSplitting`). Thus each `N_i` carries the form `π ^ i • C_i`
for a perfect pairing `C_i`; this is the Jordan decomposition of O'Meara 91C.

The main result is that every nondegenerate symmetric bilinear form on a finite module has
a Jordan splitting (`LinearMap.BilinForm.IsSymm.exists_isJordanSplitting`). The constituents
separate the form into its valuation scales, reducing its analysis to perfect pairings at each
scale. This decomposition supports the local analysis and classification of integral forms,
including the dyadic case, for instance `R = ℤ_2`, where constituents need not be diagonalizable.

A Jordan splitting is not unique, but the ranks of its constituents are invariants of the form
(`LinearMap.BilinForm.IsJordanSplitting.finrank_eq`), and hence of its isometry class
(`LinearMap.BilinForm.IsJordanSplitting.finrank_eq_of_equivalent`). This holds over every local
domain `R` and every nonzero non-unit `π`, in particular at the dyadic prime. The vectors `x` with
`π ^ j ∣ B x y` for all `y` are, modulo `π M`, exactly the sums of vectors of the constituents of
index at least `j`. By Nakayama's lemma the sum of these constituents therefore has the same rank
for any two splittings, and the rank of the `j`-th constituent is a difference of two such ranks.

## Main definitions

* `LinearMap.BilinForm.IsJordanSplitting`: a family `N : ℕ → Submodule R M` is a Jordan splitting
  of `B` with respect to `π`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.hasFiniteSupport`: a finitely generated module has only
  finitely many nonzero Jordan constituents.
* `LinearMap.BilinForm.IsSymm.exists_isJordanSplitting`: Jordan splittings exist.
* `LinearMap.BilinForm.IsJordanSplitting.finrank_eq`: any two Jordan splittings have constituents
  of equal rank.
* `LinearMap.BilinForm.IsJordanSplitting.finrank_eq_of_equivalent`: the ranks of the constituents
  are invariants of the isometry class of the form.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C, for Jordan splittings, and 91:9, for
  the invariance of the ranks of their constituents.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, Lemma 4.1 and Theorem 4.1.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

section Basic

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {B : BilinForm R M}

/-- A family `N` of submodules is a **Jordan splitting** of `B` with respect to `π` when `M` is
the internal direct sum of the `N i`, these are pairwise orthogonal, and the restriction of `B`
to `N i` is `π ^ i`-modular. -/
structure IsJordanSplitting (B : BilinForm R M) (π : R) (N : ℕ → Submodule R M) : Prop where
  /-- The module is the internal direct sum of the constituents. -/
  isInternal : DirectSum.IsInternal N
  /-- Distinct constituents are orthogonal. -/
  apply_eq_zero : ∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0
  /-- The `i`-th constituent is `π ^ i`-modular. -/
  isModular : ∀ i, (B.restrict (N i)).IsModular (π ^ i)

/-- A Jordan splitting is transported by a linear equivalence, mapping every constituent. -/
theorem IsJordanSplitting.congr {M' : Type*} [AddCommMonoid M'] [Module R M'] {π : R}
    {N : ℕ → Submodule R M} (h : B.IsJordanSplitting π N) (e : M ≃ₗ[R] M') :
    (congr e B).IsJordanSplitting π (fun i ↦ (N i).map e.toLinearMap) := by
  let eN (i : ℕ) := e.submoduleMap (N i)
  let E := DirectSum.congrLinearEquiv eN
  have hcoe : (DirectSum.coeLinearMap (fun i ↦ (N i).map e.toLinearMap)).comp E.toLinearMap =
      e.toLinearMap.comp (DirectSum.coeLinearMap N) := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simp [E, eN, DirectSum.coe_congrLinearEquiv]
  have hcomm (x : DirectSum ℕ (fun i ↦ N i)) :
      DirectSum.coeLinearMap (fun i ↦ (N i).map e.toLinearMap) (E x) =
        e (DirectSum.coeLinearMap N x) := LinearMap.congr_fun hcoe x
  have hInternal := h.isInternal
  change Function.Bijective (DirectSum.coeLinearMap N) at hInternal
  refine ⟨?_, ?_, ?_⟩
  · -- IsInternal is bijectivity of additive recomposition; coeLinearMap has the same function.
    -- The lattice characterization requires rings and groups, while this API allows semirings.
    change Function.Bijective (DirectSum.coeLinearMap (fun i ↦ (N i).map e.toLinearMap))
    constructor
    · intro x y hxy
      obtain ⟨x, rfl⟩ := E.surjective x
      obtain ⟨y, rfl⟩ := E.surjective y
      exact congrArg E (hInternal.1 (e.injective (by simpa only [hcomm] using hxy)))
    · intro y
      obtain ⟨x, hx⟩ := hInternal.2 (e.symm y)
      refine ⟨E x, ?_⟩
      rw [hcomm, hx, e.apply_symm_apply]
  · intro i j hij x hx y hy
    obtain ⟨x, hxN, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y, hyN, rfl⟩ := Submodule.mem_map.mp hy
    simpa using h.apply_eq_zero i j hij x hxN y hyN
  · intro i
    have hi : LinearMap.BilinForm.congr (eN i) (B.restrict (N i)) =
        (LinearMap.BilinForm.congr e B).restrict ((N i).map e.toLinearMap) := by
      ext x y
      obtain ⟨x, rfl⟩ := (eN i).surjective x
      obtain ⟨y, rfl⟩ := (eN i).surjective y
      simp [eN]
    rw [← hi]
    exact (h.isModular i).congr (eN i)

/-- Jordan splitting is invariant under a linear equivalence of the underlying module. -/
@[simp]
theorem isJordanSplitting_congr_iff {M' : Type*} [AddCommMonoid M'] [Module R M'] {π : R}
    {N : ℕ → Submodule R M} (e : M ≃ₗ[R] M') :
    (congr e B).IsJordanSplitting π (fun i ↦ (N i).map e.toLinearMap) ↔
      B.IsJordanSplitting π N :=
  ⟨fun h ↦ by
    simpa only [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply,
      ← Submodule.map_comp, e.symm_comp, Submodule.map_id] using h.congr e.symm,
    fun h ↦ h.congr e⟩

/-- Every value of `B` at a vector of the constituent `N i` of a Jordan splitting is divisible by
`π ^ i`. -/
theorem IsJordanSplitting.pow_dvd_apply {π : R} {N : ℕ → Submodule R M}
    (h : B.IsJordanSplitting π N) {i : ℕ} {x : M} (hx : x ∈ N i) (y : M) : π ^ i ∣ B x y := by
  refine Submodule.iSup_induction N (motive := fun y ↦ π ^ i ∣ B x y)
    (h.isInternal.submodule_iSup_eq_top ▸ Submodule.mem_top) (fun k y hy ↦ ?_) (by simp)
    fun y z hy hz ↦ by simpa only [map_add] using dvd_add hy hz
  by_cases hik : i = k
  · subst hik
    simpa using (h.isModular i).dvd ⟨x, hx⟩ ⟨y, hy⟩
  · rw [h.apply_eq_zero i k hik x hx y hy]
    exact dvd_zero _

/-- A Jordan splitting of a finitely generated module has finitely many nonzero constituents. -/
theorem IsJordanSplitting.hasFiniteSupport [Module.Finite R M] {π : R}
    {N : ℕ → Submodule R M} (h : B.IsJordanSplitting π N) : {i | N i ≠ ⊥}.Finite := by
  exact h.isInternal.submodule_iSupIndep.finite_ne_bot_of_fg
    (by rw [h.isInternal.submodule_iSup_eq_top]; exact Module.Finite.fg_top)

end Basic

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **Jordan splittings exist.** Over a discrete valuation ring with uniformizer `π`, every
nondegenerate symmetric bilinear form on a finite free module is an orthogonal direct sum of
submodules `N i` on which the form is `π ^ i`-modular. -/
private theorem exists_isJordanSplitting_of_free [Free R M] [Module.Finite R M] (hB : B.IsSymm)
    (hnd : B.Nondegenerate) {π : R} (hπ : Irreducible π) :
    ∃ N : ℕ → Submodule R M, B.IsJordanSplitting π N := by
  have hπ0 : ∀ i, π ^ i ∈ nonZeroDivisors R := fun i ↦
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i hπ.ne_zero)
  suffices h : ∃ N : ℕ → Submodule R M, iSup N = ⊤ ∧
      (∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0) ∧
      ∀ i, (B.restrict (N i)).IsModular (π ^ i) by
    obtain ⟨N, htop, horth, hmod⟩ := h
    refine ⟨N, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).mpr
      ⟨B.iSupIndep_of_restrict_separatingRight horth fun i ↦ ((hmod i).nondegenerate (hπ0 i)).2,
        htop⟩, horth, hmod⟩
  induction hn : finrank R M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  rcases subsingleton_or_nontrivial M with hM | hM
  · refine ⟨fun _ ↦ ⊥, Subsingleton.elim _ _, fun _ _ _ x hx _ _ ↦ ?_,
      fun _ ↦ isModular_of_subsingleton⟩
    rw [(Submodule.mem_bot R).mp hx, map_zero, LinearMap.zero_apply]
  -- A Gram entry of minimal valuation divides every value of the form.
  let b := Free.chooseBasis R M
  have : Nonempty (Free.ChooseBasisIndex R M) := b.index_nonempty
  obtain ⟨⟨i₀, j₀⟩, hij⟩ :=
    TauCeti.PreValuationRing.exists_forall_dvd fun q : _ × _ ↦ B (b q.1) (b q.2)
  have hdvd : ∀ x y, B (b i₀) (b j₀) ∣ B x y :=
    dvd_apply_of_forall_dvd_basis b fun k l ↦ hij (k, l)
  have hd0 : B (b i₀) (b j₀) ≠ 0 := fun h ↦
    hnd.ne_zero (LinearMap.ext₂ fun x y ↦ zero_dvd_iff.mp (h ▸ hdvd x y))
  -- Split off a modular summand `S` of minimal scale `π ^ k`.
  obtain ⟨S, hS0, -, hSmod, hSc⟩ := hB.exists_isModular_restrict_isCompl_orthogonal
    (mem_nonZeroDivisors_of_ne_zero hd0) hdvd
  obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hπ
  have hSk : (B.restrict S).IsModular (π ^ k) :=
    hSmod.of_associated ⟨u⁻¹, by rw [hku, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  -- Its orthogonal complement `N'` is finite free of smaller rank, with a nondegenerate form.
  let N' := B.orthogonal S
  have hrank : finrank R (B.orthogonal S) < n := by
    have h := S.finrank_quotient_add_finrank
    rw [(Submodule.quotientEquivOfIsCompl _ _ hSc).finrank_eq, hn] at h
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS0
    have : 0 < finrank R S := Module.finrank_pos
    omega
  have hSN : ∀ x ∈ S, ∀ y ∈ N', B x y = 0 := fun x hx y hy ↦ hy x hx
  have hNS : ∀ x ∈ N', ∀ y ∈ S, B x y = 0 := fun x hx y hy ↦ by rw [hB.eq, hSN y hy x hx]
  have hnd' : (B.restrict N').Nondegenerate := by
    refine B.nondegenerate_restrict_of_disjoint_orthogonal hB.isRefl
      (Submodule.disjoint_def.mpr fun x hx hx' ↦ hnd.2 x fun m ↦ ?_)
    obtain ⟨s, hs, y, hy, rfl⟩ :=
      Submodule.mem_sup.mp (hSc.sup_eq_top ▸ Submodule.mem_top (x := m))
    rw [map_add, LinearMap.add_apply, hSN s hs x hx, hx' y hy, add_zero]
  obtain ⟨N'', htop', horth', hmod'⟩ := ih _ hrank (hB.restrict N') hnd' rfl
  -- Put `S` into the constituent of index `k` of the splitting of `N'`.
  let N : ℕ → Submodule R M := fun i ↦ (N'' i).map N'.subtype
  have hNle : ∀ i, N i ≤ N' := fun i ↦ by simp [N, Submodule.map_subtype_le]
  have horthN : ∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0 := by
    rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact horth' i j hij x hx y hy
  refine ⟨fun i ↦ if i = k then S ⊔ N i else N i, ?_, ?_, fun i ↦ ?_⟩
  · refine eq_top_iff.mpr (hSc.sup_eq_top ▸ sup_le (le_iSup_of_le k (by simp)) ?_)
    have : N' = ⨆ i, N i := by
      rw [← Submodule.map_iSup, htop', Submodule.map_top, Submodule.range_subtype]
    exact this.trans_le (iSup_mono fun i ↦ by split_ifs <;> simp)
  · intro i j hij x hx y hy
    dsimp only at hx hy
    split_ifs at hx hy with hi hj hj
    · exact absurd (hi.trans hj.symm) hij
    · obtain ⟨s, hs, x', hx', rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, LinearMap.add_apply, hSN s hs y (hNle j hy), horthN i j hij x' hx' y hy,
        add_zero]
    · obtain ⟨s, hs, y', hy', rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, hNS x (hNle i hx) s hs, horthN i j hij x hx y' hy', add_zero]
    · exact horthN i j hij x hx y hy
  · have hNi : (B.restrict (N i)).IsModular (π ^ i) :=
      isModular_restrict_map_subtype_iff.mpr (hmod' i)
    by_cases hi : i = k
    · subst hi
      beta_reduce
      rw [ite_eq_left rfl]
      exact hSk.restrict_sup hB (hπ0 i) hNi fun x hx y hy ↦ hSN x hx y (hNle i hy)
    · beta_reduce
      rw [ite_eq_right hi]
      exact hNi

/-- **Jordan splittings exist.** Over a discrete valuation ring with uniformizer `π`, every
nondegenerate symmetric bilinear form on a finite module is an orthogonal direct sum of submodules
`N i` on which the form is `π ^ i`-modular. Nondegeneracy forces the module to be torsion-free. -/
theorem IsSymm.exists_isJordanSplitting [Module.Finite R M] (hB : B.IsSymm)
    (hnd : B.Nondegenerate) {π : R} (hπ : Irreducible π) :
    ∃ N : ℕ → Submodule R M, B.IsJordanSplitting π N := by
  let : IsTorsionFree R M := Module.isTorsionFree_iff_smul_eq_zero.mpr fun r m h ↦ by
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr (hnd.1 m fun y ↦ ?_)
      have hb : r * B m y = 0 := by
        simpa only [LinearMap.map_smul₂, smul_eq_mul, map_zero, LinearMap.zero_apply] using
          congrArg (fun x ↦ B x y) h
      exact (mul_eq_zero.mp hb).resolve_left hr
  let : Free R M := inferInstance
  exact exists_isJordanSplitting_of_free hB hnd hπ

section Uniqueness

/-! ### Uniqueness of the ranks of the constituents -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M} {π : R}
  {N : ℕ → Submodule R M}

/-- The vectors of the constituents of index at least `j` of a Jordan splitting pair into
`π ^ j R`. -/
theorem IsJordanSplitting.pow_dvd_apply_of_mem_biSup (h : B.IsJordanSplitting π N) {j : ℕ}
    {x : M} (hx : x ∈ ⨆ i ∈ Set.Ici j, N i) (y : M) : π ^ j ∣ B x y := by
  have hle : ⨆ i ∈ Set.Ici j, N i ≤ ⨅ y, Submodule.comap (B.flip y) (Ideal.span {π ^ j}) :=
    iSup₂_le fun i hi x hx ↦ Submodule.mem_iInf _ |>.mpr fun y ↦ by
      simpa [Ideal.mem_span_singleton] using (pow_dvd_pow π hi).trans (h.pow_dvd_apply hx y)
  simpa [Ideal.mem_span_singleton] using Submodule.mem_iInf _ |>.mp (hle hx) y

/-- **A vector pairing into `π ^ j R` lies in the constituents of index at least `j`, modulo `π`.**
If `π` is a non-zero-divisor and every value `B x y` is divisible by `π ^ j`, then `x` is the sum
of a vector of the constituents of index at least `j` of a Jordan splitting and a vector of `π M`.
-/
theorem IsJordanSplitting.mem_biSup_sup_smul_top (h : B.IsJordanSplitting π N)
    (hπ : π ∈ nonZeroDivisors R) {j : ℕ} {x : M} (hx : ∀ y, π ^ j ∣ B x y) :
    x ∈ (⨆ i ∈ Set.Ici j, N i) ⊔ Ideal.span {π} • ⊤ := by
  classical
  obtain ⟨f, rfl⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' N x).mp
    (h.isInternal.submodule_iSup_eq_top ▸ Submodule.mem_top)
  refine Submodule.dfinsuppSum_mem _ _ _ fun i _ ↦ ?_
  by_cases hi : j ≤ i
  · exact Submodule.mem_sup_left
      (le_iSup₂ (f := fun i (_ : i ∈ Set.Ici j) ↦ N i) i (Set.mem_Ici.mpr hi) (f i).2)
  refine Submodule.mem_sup_right ?_
  -- The components of index `i < j` are divisible by `π`: against `N i`, the vector pairs as its
  -- `i`-th component does, so these values are divisible by `π ^ (i + 1)`.
  have hcomp : ∀ y ∈ N i, B (f.sum fun _ z ↦ (z : M)) y = B (f i) y := fun y hy ↦ by
    rw [DFinsupp.sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_single i (fun k _ hki ↦ h.apply_eq_zero k i hki _ (f k).2 y hy) ?_
    intro hi
    rw [DFinsupp.notMem_support_iff.mp hi, ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply]
  obtain ⟨z, hz⟩ :=
    (h.isModular i).exists_eq_smul_of_forall_dvd (pow_mem hπ i) hπ (x := f i) fun y ↦ by
      rw [← pow_succ, restrict_apply, domRestrict_apply, ← hcomp y y.2]
      exact (pow_dvd_pow π (by omega)).trans (hx y)
  rw [hz, Submodule.coe_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top

/-- The constituents of index at least `j` of a Jordan splitting have rank at most that of the
constituents of index at least `j` of any other Jordan splitting. By Nakayama's lemma, the second
family and the constituents of index below `j` of the first one span the module, since they
already span it modulo `π`. -/
private theorem IsJordanSplitting.rank_biSup_le [IsDomain R] [IsLocalRing R] [Module.Finite R M]
    {N' : ℕ → Submodule R M} (h : B.IsJordanSplitting π N) (h' : B.IsJordanSplitting π N')
    (hπ : π ≠ 0) (hπ' : ¬IsUnit π) (j : ℕ) :
    Module.rank R ↥(⨆ i ∈ Set.Ici j, N i) ≤ Module.rank R ↥(⨆ i ∈ Set.Ici j, N' i) := by
  set A := ⨆ i ∈ Set.Ici j, N i
  set A' := ⨆ i ∈ Set.Ici j, N' i
  set C := ⨆ i ∈ Set.Iio j, N i
  have hAC : A ⊔ C = ⊤ := by
    rw [← iSup_union, Set.Ici_union_Iio, iSup_univ, h.isInternal.submodule_iSup_eq_top]
  have hAC' : A ⊓ C = ⊥ := (h.isInternal.submodule_iSupIndep.disjoint_biSup_biSup
    (Set.disjoint_left.mpr fun i hi hi' ↦ (Set.mem_Iio.mp hi').not_ge hi)).eq_bot
  have hle : A ≤ A' ⊔ Ideal.span {π} • ⊤ := fun x hx ↦
    h'.mem_biSup_sup_smul_top (mem_nonZeroDivisors_of_ne_zero hπ)
      (h.pow_dvd_apply_of_mem_biSup hx)
  have htop : A' ⊔ C = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := Ideal.span {π}) Module.Finite.fg_top ?_ ?_)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_singleton_le_iff_mem]
      exact (IsLocalRing.mem_maximalIdeal π).mpr hπ'
    · exact hAC.ge.trans
        (sup_le (hle.trans (sup_le_sup_right le_sup_left _)) (le_sup_right.trans le_sup_left))
  have hrank := Submodule.rank_sup_add_rank_inf_eq A C
  have hrank' := Submodule.rank_add_le_rank_add_rank A' C
  rw [hAC, hAC', rank_bot, add_zero] at hrank
  rw [htop, hrank] at hrank'
  exact (Cardinal.add_le_add_iff_of_lt_aleph0
    ((Submodule.rank_le C).trans_lt (rank_lt_aleph0 R M))).mp hrank'

/-- In a Jordan splitting, the constituents of index at least `j` are the `j`-th constituent and
those of index at least `j + 1`. -/
private theorem IsJordanSplitting.rank_biSup_Ici [IsDomain R] (h : B.IsJordanSplitting π N)
    (j : ℕ) : Module.rank R ↥(⨆ i ∈ Set.Ici j, N i) =
      Module.rank R (N j) + Module.rank R ↥(⨆ i ∈ Set.Ici (j + 1), N i) := by
  have hdisj : N j ⊓ ⨆ i ∈ Set.Ici (j + 1), N i = ⊥ :=
    (h.isInternal.submodule_iSupIndep.disjoint_biSup (by simp)).eq_bot
  have hIci : Set.Ici j = insert j (Set.Ici (j + 1)) := by
    ext i
    simp only [Set.mem_Ici, Set.mem_insert_iff]
    omega
  rw [hIci, iSup_insert, ← Submodule.rank_sup_add_rank_inf_eq, hdisj, rank_bot, add_zero]

/-- **The ranks of the constituents of a Jordan splitting are invariants of the form.** Over a
local domain, any two Jordan splittings of a bilinear form on a finite module with respect to the
same nonzero non-unit `π` have constituents of equal rank at every index. -/
theorem IsJordanSplitting.finrank_eq [IsDomain R] [IsLocalRing R] [Module.Finite R M]
    {N' : ℕ → Submodule R M} (h : B.IsJordanSplitting π N) (h' : B.IsJordanSplitting π N')
    (hπ : π ≠ 0) (hπ' : ¬IsUnit π) (j : ℕ) : finrank R (N j) = finrank R (N' j) := by
  have hA : ∀ j,
      Module.rank R ↥(⨆ i ∈ Set.Ici j, N i) = Module.rank R ↥(⨆ i ∈ Set.Ici j, N' i) :=
    fun j ↦ (h.rank_biSup_le h' hπ hπ' j).antisymm (h'.rank_biSup_le h hπ hπ' j)
  have hj := hA j
  rw [h.rank_biSup_Ici, h'.rank_biSup_Ici, ← hA (j + 1),
    Cardinal.add_right_inj_of_lt_aleph0 ((Submodule.rank_le _).trans_lt (rank_lt_aleph0 R M))]
    at hj
  rw [finrank, finrank, hj]

/-- **The ranks of the Jordan constituents are isometry invariants.** Over a local domain, if a
bilinear form is isometric to a bilinear form on a finite module, then Jordan splittings of the
two forms with respect to the same nonzero non-unit `π` have constituents of equal rank at every
index. -/
theorem IsJordanSplitting.finrank_eq_of_equivalent [IsDomain R] [IsLocalRing R] {M' : Type*}
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] {B' : BilinForm R M'}
    {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N) (h' : B'.IsJordanSplitting π N')
    (hB : B.Equivalent B') (hπ : π ≠ 0) (hπ' : ¬IsUnit π) (j : ℕ) :
    finrank R (N j) = finrank R (N' j) := by
  obtain ⟨e⟩ := hB
  have he : LinearMap.BilinForm.congr e.toLinearEquiv B = B' := LinearMap.ext₂ fun x y ↦ by
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective y
    rw [congr_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact (e.map_app y x).symm
  rw [← (e.toLinearEquiv).finrank_map_eq (N j)]
  exact (he ▸ h.congr e.toLinearEquiv).finrank_eq h' hπ hπ' j

end Uniqueness

end LinearMap.BilinForm
