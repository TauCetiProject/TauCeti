/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Basic

/-!
# Fixed subalgebras of finite étale torsors

If `B` is a finite étale `G`-torsor over `A` and `N ≤ G`, then `B` is an `N`-torsor over the
fixed subalgebra `Bᴺ`. For normal `N`, the quotient group `G ⧸ N` acts on `Bᴺ` and makes it a
finite étale torsor over `A`. Over a field this gives the normal-subgroup quotient of a Galois
algebra, including disconnected algebras and positive characteristic.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), Theorem 2.3.
-/

public section

namespace TauCeti.Algebra.IsFiniteEtaleTorsor

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- Restricting a finite étale torsor to a subgroup makes the algebra a torsor over the
subgroup's fixed subalgebra. -/
theorem over_fixedPoints (h : IsFiniteEtaleTorsor G A B) (N : Subgroup G) :
    IsFiniteEtaleTorsor N (FixedPoints.subalgebra A B N) B := by
  refine isFiniteEtaleTorsor_iff.mpr ⟨?_, inferInstance, fun n hn ↦ ?_⟩
  · exact (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  exact (isFiniteEtaleTorsor_iff.mp h).2.2 (n : G) (by simpa using hn)

private theorem span_range_quotient_smul_sub (h : IsFiniteEtaleTorsor G A B) (N : Subgroup G)
    [N.Normal] (g : G) (hg : g ∉ N) :
    Ideal.span (Set.range fun x : FixedPoints.subalgebra A B N ↦ (g : G ⧸ N) • x - x) = ⊤ := by
  classical
  let _ := Fintype.ofFinite N
  let C := FixedPoints.subalgebra A B N
  let I : Ideal C := Ideal.span (Set.range fun x : C ↦ (g : G ⧸ N) • x - x)
  have := (h.over_fixedPoints N).finite
  apply (Ideal.map_eq_top_iff (algebraMap C B) Subtype.val_injective
    (IsIntegral.of_finite C)).mp
  -- Start with the Galois coordinate vector for the identity. Summing over the subgroup on
  -- its second factor gives the indicator of the identity coset.
  obtain ⟨u, hu⟩ := h.bijective_tensorToPi.2 (Pi.single 1 1)
  obtain ⟨s, hs⟩ := MulSemiringAction.exists_finset_sum_mul_smul hu
  let trace (b : B) : C := ⟨∑ n : N, n • b, fun n ↦ smul_sum_smul n b⟩
  have hsum (k : G) :
      ∑ p ∈ s, p.1 * k • (trace p.2 : B) = ∑ n : N, (Pi.single 1 1 : G → B) (k * n) := by
    simp only [trace, Finset.smul_sum, Finset.mul_sum, Subgroup.smul_def, ← mul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ ↦ hs (k * n)
  have hone : ∑ p ∈ s, p.1 * (trace p.2 : B) = 1 := by
    simpa [Pi.single_apply] using hsum (1 : G)
  have hzero : ∑ p ∈ s, p.1 * g • (trace p.2 : B) = 0 := by
    rw [hsum]
    refine Finset.sum_eq_zero fun n _ ↦ Pi.single_eq_of_ne (fun hn ↦ hg ?_) _
    rw [eq_inv_of_mul_eq_one_left hn]
    exact N.inv_mem n.property
  -- The differences at these two cosets therefore generate the unit ideal after extension
  -- to B. Integrality detects the unit ideal downstairs.
  have hmem : (∑ p ∈ s, p.1 * (g • (trace p.2 : B) - (trace p.2 : B))) ∈
      I.map (algebraMap C B) := by
    refine Ideal.sum_mem _ fun p _ ↦ Ideal.mul_mem_left _ _ ?_
    have hx : (g : G ⧸ N) • trace p.2 - trace p.2 ∈ I :=
      Ideal.subset_span ⟨trace p.2, rfl⟩
    have hsmul : (((g : G ⧸ N) • trace p.2 : C) : B) = g • (trace p.2 : B) :=
      Subgroup.coe_mk_smul N g (trace p.2)
    simpa only [map_sub, Subalgebra.algebraMap_apply, hsmul]
      using Ideal.mem_map_of_mem (algebraMap C B) hx
  rw [Ideal.eq_top_iff_one]
  simpa only [mul_sub, Finset.sum_sub_distrib, hone, hzero, zero_sub, neg_neg]
    using (I.map (algebraMap C B)).neg_mem hmem

/-- The fixed subalgebra of a normal subgroup of a finite étale torsor is a finite étale
torsor under the quotient group, with its canonical action on the fixed subalgebra. -/
theorem quotient (h : IsFiniteEtaleTorsor G A B) (N : Subgroup G) [N.Normal] :
    IsFiniteEtaleTorsor (G ⧸ N) A (FixedPoints.subalgebra A B N) := by
  have := IsFiniteEtaleTorsor.isInvariant (h := h)
  have := h.faithfullyFlat
  refine isFiniteEtaleTorsor_iff.mpr ⟨?_, inferInstance, fun q hq ↦ ?_⟩
  · refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y hxy ↦ ?_
    exact FaithfulSMul.algebraMap_injective A B (congrArg Subtype.val hxy)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact span_range_quotient_smul_sub h N g (fun hg ↦ hq ((QuotientGroup.eq_one_iff g).mpr hg))

end TauCeti.Algebra.IsFiniteEtaleTorsor
