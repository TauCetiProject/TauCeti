/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Finite
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Eventual joint eigenspaces along a filter

Let `T : W → ι → Module.End R M` be a family of endomorphisms indexed by "places" `w : W` and
"indices" `j : ι`, and let `L` be a filter on `W`. For a system of scalars `χ : W → ι → R`, the
*eventual eigenspace* `Filter.eventualEigenspace L T χ` consists of the vectors `v` with
`T w j v = χ w j • v` for all `j`, for `L`-eventually all `w`. For `L = Filter.cofinite` these are
the vectors that are joint eigenvectors with eigenvalues `χ w j` at all but finitely many `w`.

The space only depends on the germs of `T` and `χ` along `L` (`Filter.eventualEigenspace_congr`),
it is antitone in `L` (`Filter.eventualEigenspace_anti`), and along a principal filter `𝓟 s` it is
the joint eigenspace of the `T w j`, `w ∈ s` (`Filter.eventualEigenspace_principal`).
Over a domain acting torsion-freely, eventual eigenspaces of systems that pairwise differ
`L`-frequently are supremum-independent (`Filter.iSupIndep_eventualEigenspace`); equivalently,
any family of distinct eventual eigenspaces is independent
(`Filter.iSupIndep_eventualEigenspace_of_injective`). No commutation between the `T w j` is
needed: finitely many vectors of such spaces are all joint eigenvectors on one common member of
`L`, where their systems are still pairwise distinct, and joint eigenspaces of any family of
endomorphisms for distinct eigenvalue functions are independent (`iSupIndep_iInf_eigenspace`).

## Main results

* `Filter.eventualEigenspace`: the eventual joint eigenspace of a system `χ` along `L`.
* `Filter.mem_eventualEigenspace`: its membership criterion.
* `Filter.eventualEigenspace_congr`: families and systems that agree eventually give the same
  space.
* `Filter.eventualEigenspace_anti`: a finer filter gives a larger space.
* `Filter.eventualEigenspace_principal`: along a principal filter, a joint eigenspace.
* `Filter.mapsTo_eventualEigenspace_of_comm`: an endomorphism commuting eventually with the
  family preserves every eventual eigenspace.
* `Filter.iSupIndep_eventualEigenspace`: independence for systems pairwise differing
  frequently along `L`.
* `Filter.iSupIndep_eventualEigenspace_of_injective`: independence of distinct eventual
  eigenspaces.

## References

* The statements follow the independence of isotypic spaces in the formal proof in the folder
  `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.Patching.Isotypic`,
  `New.Patching.Isotypic.iSupIndep_val`).
-/

public section

open Module.End

namespace Filter

section CommSemiring

variable {R M W ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The *eventual eigenspace* of a system of scalars `χ : W → ι → R` for a family of
endomorphisms `T : W → ι → Module.End R M` along a filter `L` on `W`: the vectors `v` such that,
for `L`-eventually all `w`, `T w j v = χ w j • v` for every `j`. -/
def eventualEigenspace (L : Filter W) (T : W → ι → Module.End R M) (χ : W → ι → R) :
    Submodule R M where
  carrier := {v | ∀ᶠ w in L, ∀ j, T w j v = χ w j • v}
  zero_mem' := by simp
  add_mem' {u v} hu hv := (Filter.Eventually.and hu hv).mono fun w h j ↦ by
    rw [map_add, h.1 j, h.2 j, smul_add]
  smul_mem' c v hv := Filter.Eventually.mono hv fun w h j ↦ by
    rw [map_smul, h j, smul_comm]

variable {L L' : Filter W} {T T' : W → ι → Module.End R M} {χ χ' : W → ι → R} {v : M}

@[simp]
theorem mem_eventualEigenspace :
    v ∈ eventualEigenspace L T χ ↔ ∀ᶠ w in L, ∀ j, T w j v = χ w j • v :=
  Iff.rfl

/-- The eventual eigenspace only depends on the family `T` and the system `χ` along `L`. -/
theorem eventualEigenspace_congr (hT : ∀ᶠ w in L, ∀ j, T w j = T' w j)
    (hχ : ∀ᶠ w in L, ∀ j, χ w j = χ' w j) :
    eventualEigenspace L T χ = eventualEigenspace L T' χ' := by
  ext v
  simp only [mem_eventualEigenspace]
  exact eventually_congr ((hT.and hχ).mono fun w h ↦ by simp only [h.1, h.2])

/-- The eventual eigenspace is antitone in the filter: a finer filter gives a larger space. -/
theorem eventualEigenspace_anti (h : L ≤ L') :
    eventualEigenspace L' T χ ≤ eventualEigenspace L T χ :=
  fun _ hv ↦ h hv

/-- An endomorphism commuting with every `T w j` for `L`-eventually all `w` maps each eventual
eigenspace into itself. -/
theorem mapsTo_eventualEigenspace_of_comm {A : Module.End R M}
    (hA : ∀ᶠ w in L, ∀ j, Commute A (T w j)) :
    Set.MapsTo A (eventualEigenspace L T χ) (eventualEigenspace L T χ) :=
  fun v hv ↦ (Filter.Eventually.and hv hA).mono fun w h j ↦ by
    rw [← mul_apply_eq_comp, ← (h.2 j).eq, mul_apply_eq_comp, h.1 j, map_smul]

end CommSemiring

section CommRing

variable {R M W ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Along the principal filter of a set `s`, the eventual eigenspace is the joint eigenspace of
the operators `T w j`, `w ∈ s`, for the eigenvalues `χ w j`. -/
theorem eventualEigenspace_principal (s : Set W) (T : W → ι → Module.End R M)
    (χ : W → ι → R) :
    eventualEigenspace (𝓟 s) T χ = ⨅ w ∈ s, ⨅ j, (T w j).eigenspace (χ w j) := by
  ext v
  simp [eventually_principal, Submodule.mem_iInf]

end CommRing

section Domain

variable {R M W ι κ : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.IsTorsionFree R M] {L : Filter W} {T : W → ι → Module.End R M}

/-- **Independence of eventual eigenspaces.** If the systems `χ a` pairwise differ at
`L`-frequently many `w` (for `L = Filter.cofinite`: at infinitely many `w`), then their eventual
eigenspaces are supremum-independent. No commutation between the `T w j` is needed. -/
theorem iSupIndep_eventualEigenspace {χ : κ → W → ι → R}
    (hχ : Pairwise fun a b ↦ ∃ᶠ w in L, ∃ j, χ a w j ≠ χ b w j) :
    iSupIndep fun a ↦ eventualEigenspace L T (χ a) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum
  -- a common member `U` of `L` on which every `v a`, `a ∈ s`, is a joint eigenvector
  let U := {w | ∀ a ∈ s, ∀ j, T w j (v a) = χ a w j • v a}
  have hU : ∀ᶠ w in L, w ∈ U := (eventually_all_finset s).2 fun a ha ↦ hv a ha
  -- the systems restricted to `U` are still distinct on `s`
  let g : s → U × ι → R := fun a p ↦ χ a p.1 p.2
  have hg : Function.Injective g := by
    intro a b hab
    by_contra hne
    obtain ⟨w, ⟨j, hj⟩, hwU⟩ := ((hχ (Subtype.coe_ne_coe.mpr hne)).and_eventually hU).exists
    exact hj (congrFun hab (⟨w, hwU⟩, j))
  have hind := (TauCeti.iSupIndep_iInf_eigenspace fun p : U × ι ↦ T p.1 p.2).comp hg
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hind
  intro a ha
  refine hind Finset.univ (fun b ↦ v b) (fun b _ ↦ ?_) ?_ ⟨a, ha⟩ (Finset.mem_univ _)
  · exact Submodule.mem_iInf _ |>.mpr fun p ↦ mem_eigenspace_iff.mpr (p.1.property b b.property p.2)
  · rwa [Finset.sum_coe_sort s v]

/-- **Distinct eventual eigenspaces are independent.** Any injective family of eventual
eigenspaces is supremum-independent. -/
theorem iSupIndep_eventualEigenspace_of_injective {χ : κ → W → ι → R}
    (hχ : Function.Injective fun a ↦ eventualEigenspace L T (χ a)) :
    iSupIndep fun a ↦ eventualEigenspace L T (χ a) := by
  refine iSupIndep_eventualEigenspace fun a b hab h ↦ ?_
  refine hab (hχ (eventualEigenspace_congr (.of_forall fun _ _ ↦ rfl) (h.mono fun w hw j ↦ ?_)))
  by_contra hj
  exact hw ⟨j, hj⟩

end Domain

end Filter
