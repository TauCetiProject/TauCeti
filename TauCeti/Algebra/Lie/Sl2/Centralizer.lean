/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.EigenspaceMap
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# The centralizer of the raising element of an `sl₂` triple

Let `t : IsSl2Triple h e f` be an `sl₂` triple in a Lie algebra `L` over a field `K` of
characteristic zero, and let `M` be a finite-dimensional `L`-module. Write `M(μ)` for the
`μ`-eigenspace of `h`. This file describes the kernel of the raising operator `e` through the
grading of `M` by `h`.

* The kernel of `e` is spanned by the vectors it contains of weight `n`, `n : ℕ`
  (`IsSl2Triple.ker_toEnd_e_eq_iSup_inf_eigenspace`).
* Its weight-`n` part has dimension `dim M(n) - dim M(n + 2)`, because `e` maps `M(n)` onto
  `M(n + 2)` (`IsSl2Triple.finrank_ker_toEnd_e_inf_eigenspace_add_finrank_eigenspace_add_two`).
  Summing over `n` telescopes, so `dim ker e = dim M(0) + dim M(1)`
  (`IsSl2Triple.finrank_ker_toEnd_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one`).
* A vector killed by `h` and by `e` is killed by `f`
  (`IsSl2Triple.ker_toEnd_h_inf_ker_toEnd_e_le_ker_toEnd_f`): its image under `f` would be
  a vector of weight `-2` killed by `e`. So the weight-zero part of the kernel of `e` consists of
  the invariants of the triple, and the kernel of `e` is the sum of these invariants and of its
  part of positive weight (`IsSl2Triple.ker_toEnd_e_eq_sup`).

In a decomposition of `M` into irreducible modules `V(n)`, the kernel of `e` is spanned by the
highest weight vectors, one for each summand, and a summand has a weight `0` or a weight `1`
according to the parity of `n`. The proofs here use no such decomposition.

For the adjoint module, write `𝔤(j)` for the eigenspaces of `ad h`. The centralizer `𝔤ᵉ` of `e`
then lies in the sum of the `𝔤(n)` with `n : ℕ`, which is the Lie algebra of the parabolic
subgroup attached to the triple. It satisfies `dim 𝔤ᵉ = dim 𝔤(0) + dim 𝔤(1)`, so the adjoint orbit
of `e` has dimension `dim 𝔤 - dim 𝔤(0) - dim 𝔤(1)`, which is read off the grading
(`IsSl2Triple.finrank_range_ad_e_add_finrank_eigenspace_zero_add_finrank_eigenspace_one`).
Finally `𝔤ᵉ` is the sum of the centralizer `𝔤ʰ ∩ 𝔤ᵉ ∩ 𝔤ᶠ` of the whole triple, which is its
grade-zero part, and of its part of positive grade (`IsSl2Triple.ker_ad_e_eq_sup`). For an
algebraic group this sum is the Lie algebra counterpart of writing the centralizer of `e` as the
centralizer of the triple times a unipotent normal subgroup; only the Lie algebra statement is
proved here.

The statement that a vector killed by `h` and `e` is killed by `f` needs no field: it holds in a
Noetherian torsion-free module over a domain of characteristic zero.

## Main results

* `IsSl2Triple.ker_toEnd_e_eq_iSup_inf_eigenspace`: the kernel of `e` is graded by `ℕ`.
* `IsSl2Triple.finrank_ker_toEnd_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one`:
  `dim ker e = dim M(0) + dim M(1)`.
* `IsSl2Triple.ker_toEnd_h_inf_ker_toEnd_e_le_ker_toEnd_f`: a vector killed by `h` and `e` is
  killed by `f`.
* `IsSl2Triple.ker_toEnd_e_eq_sup`: the kernel of `e` is the sum of the invariants of the triple
  and of its part of positive weight.
* `IsSl2Triple.finrank_ker_ad_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one` and
  `IsSl2Triple.finrank_range_ad_e_add_finrank_eigenspace_zero_add_finrank_eigenspace_one`: the
  dimensions of the centralizer of `e` and of the tangent space `[𝔤, e]` to its orbit.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.4 and §3.7.
-/

public section

open LieModule LieAlgebra Module

namespace IsSl2Triple

/-! ### The invariants of the triple -/

section Domain

variable {K L M : Type*} [CommRing K] [IsDomain K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [IsNoetherian K M] [IsTorsionFree K M] {h e f : L}

/-- **A vector killed by `h` and `e` is killed by `f`.** This holds in a Noetherian torsion-free
module over a domain of characteristic zero. So the vectors of weight zero killed by `e` are
exactly the invariants of the triple. -/
theorem ker_toEnd_h_inf_ker_toEnd_e_le_ker_toEnd_f (t : IsSl2Triple h e f) :
    LinearMap.ker (toEnd K L M h) ⊓ LinearMap.ker (toEnd K L M e) ≤
      LinearMap.ker (toEnd K L M f) := by
  intro m hm
  obtain ⟨hh, he⟩ := Submodule.mem_inf.1 hm
  rw [LinearMap.mem_ker, toEnd_apply_apply] at hh he
  have hm : m ∈ (toEnd K L M h).eigenspace 0 := by simpa using hh
  have hfm : ⁅f, m⁆ ∈ (toEnd K L M h).eigenspace (0 - 2) := TauCeti.lie_mem_eigenspace_sub_two t hm
  have hefm : ⁅f, m⁆ ∈ LinearMap.ker (toEnd K L M e) := by
    rw [LinearMap.mem_ker, toEnd_apply_apply, leibniz_lie, t.lie_e_f, hh, he, lie_zero, add_zero]
  refine Submodule.disjoint_def.1 (t.disjoint_ker_toEnd_e_eigenspace (μ := 0 - 2) fun n hn ↦ ?_)
    _ hefm hfm
  have : (n : ℤ) = -2 := by exact_mod_cast hn.symm.trans (zero_sub (2 : K))
  omega

/-- **A vector killed by `h` and `f` is killed by `e`.** This is
`IsSl2Triple.ker_toEnd_h_inf_ker_toEnd_e_le_ker_toEnd_f` for the triple `(-h, f, e)`. -/
theorem ker_toEnd_h_inf_ker_toEnd_f_le_ker_toEnd_e (t : IsSl2Triple h e f) :
    LinearMap.ker (toEnd K L M h) ⊓ LinearMap.ker (toEnd K L M f) ≤
      LinearMap.ker (toEnd K L M e) := by
  simpa using t.symm.ker_toEnd_h_inf_ker_toEnd_e_le_ker_toEnd_f (K := K) (M := M)

end Domain

/-! ### The weights of `h` on the kernel of the raising operator -/

section Field

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {h e f : L}

/-- **The kernel of the raising operator is graded by `ℕ`.** In a finite-dimensional module over a
field of characteristic zero, the kernel of `e` is spanned by the vectors it contains of weight `n`
for `h`, `n : ℕ`. This is `IsSl2Triple.ker_toEnd_f_eq_iSup_inf_eigenspace` for the triple
`(-h, f, e)`. -/
theorem ker_toEnd_e_eq_iSup_inf_eigenspace (t : IsSl2Triple h e f) :
    LinearMap.ker (toEnd K L M e) =
      ⨆ n : ℕ, LinearMap.ker (toEnd K L M e) ⊓ (toEnd K L M h).eigenspace (n : K) := by
  simpa using t.symm.ker_toEnd_f_eq_iSup_inf_eigenspace (K := K) (M := M)

/-- **The weight-`μ` part of the kernel of `e`.** When `e` maps `M(μ)` onto `M(μ + 2)`, which is
the case unless `μ + 2` is of the form `-n` with `n : ℕ`, the vectors of weight `μ` killed by `e`
form a subspace of dimension `dim M(μ) - dim M(μ + 2)`. -/
theorem finrank_ker_toEnd_e_inf_eigenspace_add_finrank_eigenspace_add_two
    (t : IsSl2Triple h e f) {μ : K} (hμ : ∀ n : ℕ, μ + 2 ≠ -n) :
    finrank K (LinearMap.ker (toEnd K L M e) ⊓ (toEnd K L M h).eigenspace μ : Submodule K M) +
        finrank K ((toEnd K L M h).eigenspace (μ + 2)) =
      finrank K ((toEnd K L M h).eigenspace μ) := by
  set p := (toEnd K L M h).eigenspace μ
  have hrange : LinearMap.range ((toEnd K L M e).domRestrict p) =
      (toEnd K L M h).eigenspace (μ + 2) := by
    rw [LinearMap.range_domRestrict, t.map_toEnd_e_eigenspace hμ]
  have hker : finrank K (LinearMap.ker ((toEnd K L M e).domRestrict p)) =
      finrank K (LinearMap.ker (toEnd K L M e) ⊓ p : Submodule K M) := by
    rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
      Submodule.map_comap_subtype, inf_comm]
  rw [← hker, ← hrange, add_comm]
  exact LinearMap.finrank_range_add_finrank_ker _

/-- **The dimension of the kernel of the raising operator.** For an `sl₂` triple `(h, e, f)` acting
on a finite-dimensional module `M` over a field of characteristic zero,
`dim ker e = dim M(0) + dim M(1)`. In a decomposition of `M` into irreducible modules both sides
count the summands. -/
theorem finrank_ker_toEnd_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one
    (t : IsSl2Triple h e f) :
    finrank K (LinearMap.ker (toEnd K L M e)) =
      finrank K ((toEnd K L M h).eigenspace 0) + finrank K ((toEnd K L M h).eigenspace 1) := by
  -- Only finitely many natural numbers are weights of `h`; let `N` exceed them all.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n, N ≤ n → (toEnd K L M h).eigenspace (n : K) = ⊥ := by
    obtain ⟨N, hN⟩ := ((toEnd K L M h).finite_hasEigenvalue.preimage
      (Nat.cast_injective (R := K)).injOn).bddAbove
    refine ⟨N + 1, fun n hn ↦ ?_⟩
    by_contra hne
    have : n ≤ N := hN (Module.End.hasEigenvalue_iff.2 hne)
    omega
  set d : ℕ → ℕ := fun n ↦ finrank K ((toEnd K L M h).eigenspace (n : K))
  set k : ℕ → Submodule K M :=
    fun n ↦ LinearMap.ker (toEnd K L M e) ⊓ (toEnd K L M h).eigenspace (n : K)
  -- Only the weights below `N` contribute to the kernel.
  have hker : LinearMap.ker (toEnd K L M e) = ⨆ n : Fin N, k n := by
    refine (t.ker_toEnd_e_eq_iSup_inf_eigenspace).trans (le_antisymm (iSup_le fun n ↦ ?_)
      (iSup_le fun n ↦ le_iSup k (n : ℕ)))
    by_cases hn : n < N
    · exact le_iSup_of_le ⟨n, hn⟩ le_rfl
    · simp [k, hN n (not_lt.1 hn)]
  have hindep : iSupIndep fun n : Fin N ↦ k n :=
    (((toEnd K L M h).eigenspaces_iSupIndep.comp
      (Nat.cast_injective.comp Fin.val_injective)).mono fun _ ↦ inf_le_right)
  -- On weight `n`, the raising operator is onto weight `n + 2`.
  have hstep (n : ℕ) : finrank K (k n) + d (n + 2) = d n := by
    have := t.finrank_ker_toEnd_e_inf_eigenspace_add_finrank_eigenspace_add_two (M := M)
      (μ := (n : K)) fun m hm ↦ by
        have : ((n + 2 : ℕ) : ℤ) = -m := by exact_mod_cast hm
        omega
    rwa [← Nat.cast_two, ← Nat.cast_add] at this
  have hsum :
      finrank K (LinearMap.ker (toEnd K L M e)) = ∑ n ∈ Finset.range N, finrank K (k n) := by
    rw [hker, TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hindep,
      Finset.sum_range (fun n ↦ finrank K (k n))]
  -- Telescope `∑ₙ (d n - d (n + 2))` over `n < N`, using `d N = d (N + 1) = 0`.
  have htel : ∑ n ∈ Finset.range N, finrank K (k n) + ∑ n ∈ Finset.range N, d (n + 2) =
      ∑ n ∈ Finset.range N, d n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ hstep n
  have hshift : ∑ n ∈ Finset.range (N + 2), d n = ∑ n ∈ Finset.range N, d (n + 2) + d 1 + d 0 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have htop : ∑ n ∈ Finset.range (N + 2), d n = ∑ n ∈ Finset.range N, d n := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [d]
    rw [hN N le_rfl, hN (N + 1) (Nat.le_succ N)]
    simp
  have h0 : d 0 = finrank K ((toEnd K L M h).eigenspace 0) := by
    simp only [d]
    rw [Nat.cast_zero]
  have h1 : d 1 = finrank K ((toEnd K L M h).eigenspace 1) := by
    simp only [d]
    rw [Nat.cast_one]
  omega

/-- **The kernel of `e` is spanned by invariants and positive weights.** The kernel of the raising
operator is the sum of the vectors killed by the whole triple, which form its weight-zero part, and
of its part of positive weight. -/
theorem ker_toEnd_e_eq_sup (t : IsSl2Triple h e f) :
    LinearMap.ker (toEnd K L M e) =
      (LinearMap.ker (toEnd K L M h) ⊓ LinearMap.ker (toEnd K L M e) ⊓
          LinearMap.ker (toEnd K L M f)) ⊔
        LinearMap.ker (toEnd K L M e) ⊓ ⨆ n : ℕ, (toEnd K L M h).eigenspace ((n + 1 : ℕ) : K) := by
  have hker := t.ker_toEnd_e_eq_iSup_inf_eigenspace (K := K) (M := M)
  rw [← sup_iSup_nat_succ] at hker
  refine le_antisymm (hker.le.trans (sup_le_sup (fun m hm ↦ ?_) (iSup_le fun n ↦ ?_)))
    (sup_le (inf_le_left.trans inf_le_right) inf_le_left)
  · obtain ⟨hme, hmh⟩ := Submodule.mem_inf.1 hm
    have hmh' : m ∈ LinearMap.ker (toEnd K L M h) := by simpa using hmh
    exact ⟨⟨hmh', hme⟩, t.ker_toEnd_h_inf_ker_toEnd_e_le_ker_toEnd_f ⟨hmh', hme⟩⟩
  · exact inf_le_inf_left _ (le_iSup (fun n : ℕ ↦ (toEnd K L M h).eigenspace ((n + 1 : ℕ) : K)) n)

/-! ### The adjoint action -/

variable [FiniteDimensional K L]

/-- **The dimension of the centralizer of `e`.** For an `sl₂` triple `(h, e, f)` in a
finite-dimensional Lie algebra `𝔤` over a field of characteristic zero,
`dim 𝔤ᵉ = dim 𝔤(0) + dim 𝔤(1)`, where `𝔤(j)` is the `j`-eigenspace of `ad h`. -/
theorem finrank_ker_ad_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one
    (t : IsSl2Triple h e f) :
    finrank K (LinearMap.ker (ad K L e)) =
      finrank K ((ad K L h).eigenspace 0) + finrank K ((ad K L h).eigenspace 1) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.finrank_ker_toEnd_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one (M := L)

/-- **The dimension of the adjoint orbit of `e`.** For an `sl₂` triple `(h, e, f)` in a
finite-dimensional Lie algebra `𝔤` over a field of characteristic zero, the tangent space `[𝔤, e]`
to the orbit of `e` has dimension `dim 𝔤 - dim 𝔤(0) - dim 𝔤(1)`. -/
theorem finrank_range_ad_e_add_finrank_eigenspace_zero_add_finrank_eigenspace_one
    (t : IsSl2Triple h e f) :
    finrank K (LinearMap.range (ad K L e)) + finrank K ((ad K L h).eigenspace 0) +
        finrank K ((ad K L h).eigenspace 1) = finrank K L := by
  rw [add_assoc, ← t.finrank_ker_ad_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one]
  exact LinearMap.finrank_range_add_finrank_ker _

/-- **The centralizer of `e` and the centralizer of the triple.** For an `sl₂` triple `(h, e, f)` in
a finite-dimensional Lie algebra over a field of characteristic zero, the centralizer of `e` is the
sum of the centralizer of the whole triple, which is its grade-zero part, and of its part of
positive grade for `ad h`. -/
theorem ker_ad_e_eq_sup (t : IsSl2Triple h e f) :
    LinearMap.ker (ad K L e) =
      (LinearMap.ker (ad K L h) ⊓ LinearMap.ker (ad K L e) ⊓ LinearMap.ker (ad K L f)) ⊔
        LinearMap.ker (ad K L e) ⊓ ⨆ n : ℕ, (ad K L h).eigenspace ((n + 1 : ℕ) : K) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.ker_toEnd_e_eq_sup (M := L)

end Field

end IsSl2Triple
