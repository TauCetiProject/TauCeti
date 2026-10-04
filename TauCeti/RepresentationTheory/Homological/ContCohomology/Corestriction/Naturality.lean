/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# Coefficient naturality of degree-two corestriction

For an open finite-index subgroup `U` of a topological group `G`, degree-two corestriction
commutes with every continuous `G`-equivariant additive coefficient map. This lets coefficient
identifications and changes of coefficients pass through the explicit transversal construction,
including when the coefficients are topological rather than discrete.

`explicitCor2Transversal_explicitMap2_id` gives the identity for any transversal;
`explicitCor2_explicitMap2_id` gives it for the canonical corestriction. Together with
`map_explicitCor0` and `explicitCor1_explicitMap1_id` in `Corestriction.Basic`, this supplies
coefficient naturality in all three explicit degrees.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I,
  §5, for corestriction and its functoriality.
-/

public section

namespace TauCeti.ContCohomology

universe u v w

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (U : Subgroup G) [U.FiniteIndex]
  {N : Type w} [AddCommGroup N] [DistribMulAction G N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul G N]

/-- Degree-two corestriction for any transversal commutes with a continuous equivariant
coefficient map. No continuity of the transversal or discreteness of the coefficients is needed. -/
theorem explicitCor2Transversal_explicitMap2_id
    (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (hU : IsOpen (U : Set G)) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (g : G) (m : M), f (g • m) = g • f m) (x : H2 U M) :
    explicitCor2Transversal G N U t ht hU
        (explicitMap2 U M U N (ContinuousMonoidHom.id U) f hf
          (fun u m => by simpa [Subgroup.smul_def] using hequiv u m) x) =
      explicitMap2 G M G N (ContinuousMonoidHom.id G) f hf
        (fun g m => by simpa using hequiv g m)
        (explicitCor2Transversal G M U t ht hU x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitMap2_mk, explicitCor2Transversal_mk, explicitCor2Transversal_mk,
      explicitMap2_mk]
    apply congrArg (fun z : Z2 G N => (z : H2 G N))
    apply Subtype.ext
    ext ⟨γ, η⟩
    simp only [coe_cocyclesCor2, cocyclesMap2_coe, cochainsMap2_apply]
    have hmap : cochainsMap2 (ContinuousMonoidHom.id U : U →* U) f c =
        fun q => f ((c : U × U → M) q) := by
      ext ⟨a, b⟩
      simp [cochainsMap2_apply]
    rw [hmap]
    simpa using (map_cochainsCor2 G M U t ht f hequiv c γ η).symm

/-- Degree-two corestriction commutes with continuous equivariant coefficient maps, completing
coefficient naturality for the explicit low-degree cohomology groups. -/
theorem explicitCor2_explicitMap2_id (hU : IsOpen (U : Set G))
    (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (g : G) (m : M), f (g • m) = g • f m) (x : H2 U M) :
    explicitCor2 G N U hU
        (explicitMap2 U M U N (ContinuousMonoidHom.id U) f hf
          (fun u m => by simpa [Subgroup.smul_def] using hequiv u m) x) =
      explicitMap2 G M G N (ContinuousMonoidHom.id G) f hf
        (fun g m => by simpa using hequiv g m) (explicitCor2 G M U hU x) := by
  rw [explicitCor2_eq_transversal G N U Quotient.out Quotient.out_eq,
    explicitCor2_eq_transversal G M U Quotient.out Quotient.out_eq]
  exact explicitCor2Transversal_explicitMap2_id G M U Quotient.out Quotient.out_eq hU
    f hf hequiv x

end TauCeti.ContCohomology
