/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
import TauCeti.GroupTheory.TransversalWord

/-!
# The index-two coefficient sequence in characteristic two

For an open subgroup `U` of index two and a discrete `G`-module `M` killed by two,
the coinduction unit and trace form the short exact sequence

```text
0 → M → Coind_U^G M → M → 0.
```

For trivial coefficients the unit is the inclusion of constant functions and the trace
is the sum of the two coordinates. This is the coefficient sequence whose long exact
sequence, under Shapiro's isomorphism, alternates restriction, corestriction and cup
product with the character of `G/U`.

`indexTwoShortExact_explicitDelta0` fixes the connecting-map normalization: an invariant
`m` maps to the class of the cocycle that is zero on `U` and `m` off `U`. In particular,
for trivial `𝔽₂` coefficients, the boundary of `1` is the nonzero character with kernel `U`.
The coefficient sequence works for nontrivial actions as well.

## References

* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*,
  Proc. Amer. Math. Soc. **91** (1984), Lemma 2.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.3.2), for the connecting-map convention.
-/

public section

namespace TauCeti.DiscreteCoind

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {U : Subgroup G} [U.FiniteIndex] {M : Type v} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The trace at index two has the two terms at `1` and at an arbitrary outside representative.
The action on the second term is retained even when the coefficients are nontrivial. -/
theorem trace_eq_add_of_index_two (hU : U.index = 2) {s : G} (hs : s ∉ U)
    (f : DiscreteCoind G U M) : trace G U M f = f 1 + s • f s⁻¹ := by
  rw [trace_eq_sum_transversal (U.indexTwoTransversal s)
    (Subgroup.indexTwoTransversal_mk hU hs), sum_quotient_eq_add_of_index_two hU hs]
  simp [Subgroup.indexTwoTransversal_of_ne s (mk_ne_mk_one_of_notMem hs)]

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- At index two, for coefficients killed by two, the kernel of the trace is the image
of the coinduction unit. No triviality of the action is assumed. -/
theorem trace_eq_zero_iff_exists_unit_of_index_two (hU : U.index = 2)
    (hM : ∀ m : M, 2 • m = 0) (f : DiscreteCoind G U M) :
    trace G U M f = 0 ↔ ∃ m : M, unit G U M m = f := by
  constructor
  · intro hf
    obtain ⟨s, hs, _⟩ := U.index_eq_two_iff_exists_notMem_and.mp hU
    have hfs : s • f s⁻¹ = f 1 := by
      have ht := trace_eq_add_of_index_two hU hs f
      have hm := hM (f 1)
      rw [two_nsmul] at hm
      rw [hf] at ht
      exact add_left_cancel (ht.symm.trans hm.symm)
    refine ⟨f 1, ext fun g => ?_⟩
    rw [unit_apply]
    by_cases hg : g ∈ U
    · exact (apply_coe f ⟨g, hg⟩).symm
    · have hgs : g * s ∈ U :=
        (Subgroup.mul_mem_iff_of_index_two hU).2 (iff_of_false hg hs)
      have h := apply_mul f ⟨g * s, hgs⟩ s⁻¹
      simpa [mul_smul, hfs] using h.symm
  · rintro ⟨m, rfl⟩
    rw [trace_unit, hU, hM]

variable (G U M)

/-- The short exact sequence `0 → M → Coind_U^G M → M → 0` for an open subgroup of
index two and discrete coefficients killed by two. Its maps are the unit and trace. -/
noncomputable def indexTwoShortExact (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (hM : ∀ m : M, 2 • m = 0) :
    ContCohomology.DiscreteShortExact G M (DiscreteCoind G U M) M where
  incl := (unit G U M).toAddMonoidHom
  proj := (trace G U M).toAddMonoidHom
  incl_equivariant g m := _root_.map_smul (unit G U M) g m
  proj_equivariant g f := _root_.map_smul (trace G U M) g f
  incl_injective := unit_injective
  proj_surjective := trace_surjective hUo
  exact := trace_eq_zero_iff_exists_unit_of_index_two hU hM

/-- The first map of the index-two sequence is the coinduction unit. -/
@[simp]
theorem indexTwoShortExact_incl (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (hM : ∀ m : M, 2 • m = 0) :
    (indexTwoShortExact G U M hU hUo hM).incl = (unit G U M).toAddMonoidHom := (rfl)

/-- The second map of the index-two sequence is the trace. -/
@[simp]
theorem indexTwoShortExact_proj (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (hM : ∀ m : M, 2 • m = 0) :
    (indexTwoShortExact G U M hU hUo hM).proj = (trace G U M).toAddMonoidHom := (rfl)

end TauCeti.DiscreteCoind

namespace TauCeti.ContCohomology

open DiscreteCoind

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]
  {U : Subgroup G} [U.FiniteIndex] {M : Type v} [AddCommGroup M]
  [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

variable [ContinuousMul G] in
omit [U.FiniteIndex] in
open Classical in
/-- The boundary of a single supported on `U`, for an invariant coefficient killed by two,
is the unit applied to the function which is zero on `U` and that coefficient off `U`. -/
private theorem unit_indicator_eq_smul_single_sub (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (hM : ∀ m : M, 2 • m = 0) (c : H0 G M) (g : G) :
    unit G U M (if g ∈ U then 0 else (c : M)) =
      g • single G U M hUo 1 (c : M) - single G U M hUo 1 (c : M) := by
  have hc : ∀ g : G, g • (c : M) = (c : M) :=
    (FixedPoints.mem_addSubgroup G M c).1 c.2
  have hneg : -(c : M) = (c : M) := by
    have h := hM (c : M)
    rw [two_nsmul, ← eq_neg_iff_add_eq_zero] at h
    exact h.symm
  have hs : ∀ x : G, single G U M hUo 1 (c : M) x = if x ∈ U then (c : M) else 0 := by
    intro x
    by_cases hx : x ∈ U
    · simpa [hx, hc, Subgroup.smul_def] using single_apply_mul hUo 1 (c : M) ⟨x, hx⟩
    · rw [single_apply_of_notMem hUo (c : M) (g := 1) (x := x) (by simpa using hx)]
      simp [hx]
  ext x
  simp only [unit_apply, coe_sub, Pi.sub_apply, coe_smul, hs]
  by_cases hg : g ∈ U <;> by_cases hx : x ∈ U <;>
    simp [hg, hx, Subgroup.mul_mem_iff_of_index_two hU, hc, hneg]

variable [ContinuousMul G] [IsTopologicalAddGroup M] in
omit [U.FiniteIndex] [DiscreteTopology M] [ContinuousSMul G M] in
open Classical in
/-- The index-two connecting cocycle of an invariant `c`: zero on the subgroup, `c` off it. -/
noncomputable def indexTwoConnectingCocycle (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (c : H0 G M) (hc2 : 2 • (c : M) = 0) : Z1 G M := by
  refine ⟨fun g => if g ∈ U then 0 else (c : M), mem_Z1_iff.2 ⟨?_, ?_⟩⟩
  · exact continuous_const.if
      (by simp [IsClopen.frontier_eq ⟨U.isClosed_of_isOpen hUo, hUo⟩]) continuous_const
  · have hc := (FixedPoints.mem_addSubgroup G M c).1 c.2
    intro g h
    by_cases hg : g ∈ U <;> by_cases hh : h ∈ U <;>
      simp [hg, hh, Subgroup.mul_mem_iff_of_index_two hU, hc, ← two_nsmul, hc2]

variable [ContinuousMul G] [IsTopologicalAddGroup M] in
omit [U.FiniteIndex] [DiscreteTopology M] [ContinuousSMul G M] in
open Classical in
/-- The value formula of the connecting cocycle. -/
@[simp]
theorem indexTwoConnectingCocycle_apply (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (c : H0 G M) (hc2 : 2 • (c : M) = 0) (g : G) :
    (indexTwoConnectingCocycle hU hUo c hc2 : G → M) g =
      if g ∈ U then 0 else (c : M) := (rfl)

variable [IsTopologicalGroup G] [CompactSpace G]

/-- The degree-zero connecting map of the index-two coefficient sequence is the class
of the cocycle equal to `c` outside the subgroup and zero inside. -/
theorem indexTwoShortExact_explicitDelta0 (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (hM : ∀ m : M, 2 • m = 0) (c : H0 G M) :
    (indexTwoShortExact G U M hU hUo hM).explicitDelta0 c =
      (indexTwoConnectingCocycle hU hUo c (hM c) : H1 G M) := by
  exact (indexTwoShortExact G U M hU hUo hM).explicitDelta0_apply c
    (b := single G U M hUo 1 (c : M))
    (by rw [indexTwoShortExact_proj]; exact (trace_single hUo 1 (c : M)).trans (by simp))
    (unit_indicator_eq_smul_single_sub hU hUo hM c)

/-- For a trivial action the connecting map is injective: an invariant coefficient has
zero boundary exactly when it is zero. Thus the boundary of `1` for trivial `𝔽₂`
coefficients is nonzero, as required for the index-two character. -/
theorem indexTwoShortExact_explicitDelta0_eq_zero_iff (hU : U.index = 2)
    (hUo : IsOpen (U : Set G)) (hM : ∀ m : M, 2 • m = 0)
    (htriv : ∀ (g : G) (m : M), g • m = m) (c : H0 G M) :
    (indexTwoShortExact G U M hU hUo hM).explicitDelta0 c = 0 ↔ c = 0 := by
  constructor
  · intro hc
    rw [indexTwoShortExact_explicitDelta0, H1pi_eq_zero_iff, mem_B1_iff] at hc
    obtain ⟨m, hm⟩ := hc
    obtain ⟨s, hs, _⟩ := U.index_eq_two_iff_exists_notMem_and.mp hU
    have h := hm s
    simp only [indexTwoConnectingCocycle_apply, ite_eq_right hs, htriv, sub_self] at h
    exact Subtype.ext h.symm
  · rintro rfl
    exact map_zero _

end TauCeti.ContCohomology
