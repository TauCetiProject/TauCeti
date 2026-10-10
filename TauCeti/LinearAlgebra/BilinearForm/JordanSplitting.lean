/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Modular
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Jordan splittings over a discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `π`. A **Jordan splitting** of a bilinear
form `B` on an `R`-module `M` is a decomposition `M = ⊕_i N_i` into pairwise orthogonal
submodules such that the restriction of `B` to `N_i` is `π ^ i`-modular: `π ^ i` times a perfect
pairing (`LinearMap.BilinForm.IsJordanSplitting`). Thus each `N_i` carries the form `π ^ i • C_i`
for a perfect pairing `C_i`; this is the Jordan decomposition of O'Meara 91C.

The main result is that every nondegenerate symmetric bilinear form on a finite free module has
a Jordan splitting (`LinearMap.BilinForm.IsSymm.exists_isJordanSplitting`). The proof splits off
a modular summand of minimal scale, of rank one or two
(`LinearMap.BilinForm.IsSymm.exists_isModular_restrict_isCompl_orthogonal`), and recurses on its
orthogonal complement. No inverse of `2` is used, so the theorem covers the dyadic case, for
instance `R = ℤ_2`, where Jordan constituents need not be diagonalizable.

## Main definitions

* `LinearMap.BilinForm.IsJordanSplitting`: a family `N : ℕ → Submodule R M` is a Jordan splitting
  of `B` with respect to `π`.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_isJordanSplitting`: Jordan splittings exist.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 91:9.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, Lemma 4.1 and Theorem 4.1.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

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

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **Jordan splittings exist.** Over a discrete valuation ring with uniformizer `π`, every
nondegenerate symmetric bilinear form on a finite free module is an orthogonal direct sum of
submodules `N i` on which the form is `π ^ i`-modular. -/
theorem IsSymm.exists_isJordanSplitting [Free R M] [Module.Finite R M] (hB : B.IsSymm)
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

end LinearMap.BilinForm
