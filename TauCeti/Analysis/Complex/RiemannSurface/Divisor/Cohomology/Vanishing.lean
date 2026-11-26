/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.MittagLeffler
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Map
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch

/-!
# Vanishing of `H¹(X, 𝒪_E)` for large `E` and surjectivity of the Mittag-Leffler map

Let `X` be a compact connected Hausdorff Riemann surface. For every divisor `D` there is a divisor
`E ≥ D` with `H¹(X, 𝒪_E) = 0` (`exists_le_subsingleton_divisorCechCohomology_one`). Consequently
every class of `H¹(X, 𝒪_D)` dies in some `H¹(X, 𝒪_E)`, and the Mittag-Leffler connecting map
`PrincipalParts D → H¹(X, 𝒪_D)` is surjective (`mittagLefflerConnecting_surjective`, Forster,
Theorem 17.3).

## Proof

The numbers `h¹(E)` for `E ≥ D` are bounded below, and they decrease along inclusions, which are
surjective on `H¹` (`divisorCechCohomologyMapOfLE_one_surjective`). At a divisor `E` where `h¹`
is least, every inclusion `H¹(𝒪_E) → H¹(𝒪_{E'})`, `E ≤ E'`, is an isomorphism. Suppose
`H¹(𝒪_E) ≠ 0`. Choose a nonconstant meromorphic function `f`
(`exists_meromorphicFunction_notMem_range_algebraMap`) and `E₁ ≥ E` with `(f) ≥ E - E₁`.
Multiplication by `f` maps `H¹(𝒪_E)` to `H¹(𝒪_{E₁}) ≅ H¹(𝒪_E)`; over `ℂ` this endomorphism
has an eigenvalue `c` with eigenvector `v ≠ 0`. Multiplication by `g = f - c`, the difference of
multiplication by `f` and `c` times the inclusion, kills `v`. Since `g ≠ 0`, multiplication by
`g⁻¹` maps `𝒪_{E₁}` to `𝒪_{E₂}` with `E₂ = E₁ + (g) ≥ E`, and the composite is the inclusion
`𝒪_E → 𝒪_{E₂}`, which is injective on `H¹`. So `v = 0`, a contradiction.

This avoids the quotient `H¹(𝒪_D) / ⋃_{E ≥ D} ker (H¹(𝒪_D) → H¹(𝒪_E))` of Forster's proof:
choosing `E` with least `h¹` makes that quotient `H¹(𝒪_E)` itself.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §17, Theorem 17.3 and its proof.
-/

public noncomputable section

open CategoryTheory Opposite
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- At a divisor `E ≥ D` where `h¹` is least, every inclusion `H¹(𝒪_E) → H¹(𝒪_{E'})` is
injective. -/
private theorem exists_le_forall_injective (D : WeilDivisor X) :
    ∃ E, D ≤ E ∧ ∀ ⦃E' : WeilDivisor X⦄ (h : E ≤ E'),
      Function.Injective (divisorCechCohomologyMapOfLE h 1) := by
  classical
  have hex : ∃ n, ∃ E, D ≤ E ∧ Module.finrank ℂ (divisorCechCohomology E 1) = n :=
    ⟨_, D, le_rfl, rfl⟩
  obtain ⟨E, hDE, hE⟩ := Nat.find_spec hex
  refine ⟨E, hDE, fun E' h ↦ ?_⟩
  have hle := finrank_divisorCechCohomology_one_le_of_le h
  have hge := Nat.find_min' hex ⟨E', hDE.trans h, rfl⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).2
    (divisorCechCohomologyMapOfLE_one_surjective h)

omit [T2Space X] in
/-- Multiplication by a meromorphic function which kills a class `v` of `H¹(𝒪_E)` and is not `0`
forces `v = 0` when all inclusions out of `E` are injective on `H¹`. -/
private theorem eq_zero_of_divisorCechCohomologyMeromorphicMul {E E₁ : WeilDivisor X}
    (hE : ∀ ⦃E' : WeilDivisor X⦄ (h : E ≤ E'),
      Function.Injective (divisorCechCohomologyMapOfLE h 1))
    {g : MeromorphicFunction X} (hg0 : g ≠ 0)
    (hg : ∀ x, ((E x - E₁ x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g)
    {v : divisorCechCohomology E 1}
    (hv : divisorCechCohomologyMeromorphicMul g hg 1 v = 0) : v = 0 := by
  -- Multiplying further by `g⁻¹` into `𝒪_{E₁ + (g)}` gives the inclusion of `𝒪_E`.
  let E₂ := E₁ + (MeromorphicFunction.orderSystem X).principalDivisor
    (Additive.ofMul (Units.mk0 g hg0))
  have hEE₂ : E ≤ E₂ := fun x ↦ by
    have := MeromorphicFunction.order_eq_principalDivisor_mk0 hg0 x ▸ hg x
    simp only [E₂, Finsupp.add_apply]
    norm_cast at this
    omega
  have hginv (x : X) : ((E₁ x - E₂ x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g⁻¹ := by
    rw [(MeromorphicFunction.order x).map_inv,
      MeromorphicFunction.order_eq_principalDivisor_mk0 hg0]
    simp [E₂, sub_add_cancel_left]
  apply hE hEE₂
  have hcomp := divisorCechCohomologyMeromorphicMul_comp_apply g g⁻¹ hg hginv 1 v
  simp only [hv, map_zero, mul_inv_cancel₀ hg0, divisorCechCohomologyMeromorphicMul_one hEE₂]
    at hcomp
  rw [map_zero, ← hcomp]

/-- At a divisor `E` from which all inclusions are injective on `H¹`, the group `H¹(𝒪_E)`
vanishes. -/
private theorem subsingleton_of_forall_injective {E : WeilDivisor X}
    (hE : ∀ ⦃E' : WeilDivisor X⦄ (h : E ≤ E'),
      Function.Injective (divisorCechCohomologyMapOfLE h 1)) :
    Subsingleton (divisorCechCohomology E 1) := by
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨f, hf⟩ := exists_meromorphicFunction_notMem_range_algebraMap X
  have hf0 : f ≠ 0 := fun h ↦ hf ⟨0, by rw [h, map_zero]⟩
  set F := (MeromorphicFunction.orderSystem X).principalDivisor (Additive.ofMul (Units.mk0 f hf0))
    with hF
  have hEE₁ : E ≤ E ⊔ (E - F) := le_sup_left
  have hfo (x : X) : ((E x - (E ⊔ (E - F)) x : ℤ) : WithTop ℤ) ≤
      MeromorphicFunction.order x f := by
    have : E x - F x ≤ (E ⊔ (E - F)) x := (le_sup_right : E - F ≤ _) x
    rw [MeromorphicFunction.order_eq_principalDivisor_mk0 hf0, ← hF]
    exact_mod_cast (by omega)
  -- Multiplication by `f`, read on `H¹(𝒪_E)` through the isomorphism `H¹(𝒪_E) ≅ H¹(𝒪_{E₁})`.
  let e := LinearEquiv.ofBijective (divisorCechCohomologyMapOfLE hEE₁ 1)
    ⟨hE hEE₁, divisorCechCohomologyMapOfLE_one_surjective hEE₁⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue
    (e.symm.toLinearMap ∘ₗ divisorCechCohomologyMeromorphicMul f hfo 1)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hMv := hv.apply_eq_smul
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, map_smul] at hMv
  -- Multiplication by `f - c` kills the eigenvector.
  have hcb := sub_le_order_algebraMap hEE₁ c
  refine hv.2 (eq_zero_of_divisorCechCohomologyMeromorphicMul hE
    (sub_ne_zero.2 fun h ↦ hf ⟨c, h.symm⟩)
    (fun x ↦ (le_min (hfo x) (hcb x)).trans ((MeromorphicFunction.order x).map_sub _ _)) ?_)
  rw [divisorCechCohomologyMeromorphicMul_sub f _ hfo hcb,
    divisorCechCohomologyMeromorphicMul_algebraMap, LinearMap.sub_apply, LinearMap.smul_apply,
    sub_eq_zero]
  exact hMv

/-- **`H¹(X, 𝒪_E)` vanishes for large `E`.** On a compact connected Hausdorff Riemann surface,
every divisor `D` lies below a divisor `E` with `H¹(X, 𝒪_E) = 0`. -/
theorem exists_le_subsingleton_divisorCechCohomology_one (D : WeilDivisor X) :
    ∃ E, D ≤ E ∧ Subsingleton (divisorCechCohomology E 1) := by
  obtain ⟨E, hDE, hE⟩ := exists_le_forall_injective D
  exact ⟨E, hDE, subsingleton_of_forall_injective hE⟩

/-- **Forster, Theorem 17.3.** On a compact connected Hausdorff Riemann surface, the
Mittag-Leffler connecting map `PrincipalParts D → H¹(X, 𝒪_D)` is surjective: every class of
`H¹(X, 𝒪_D)` is the obstruction of a Mittag-Leffler distribution. -/
theorem mittagLefflerConnecting_surjective (D : WeilDivisor X) :
    Function.Surjective (mittagLefflerConnecting D) := by
  obtain ⟨E, hDE, hE⟩ := exists_le_subsingleton_divisorCechCohomology_one D
  rw [← LinearMap.range_eq_top, range_mittagLefflerConnecting, eq_top_iff]
  exact fun v _ ↦ Submodule.mem_iSup_of_mem E <| Submodule.mem_iSup_of_mem hDE <|
    Subsingleton.elim _ _

end TauCeti.RiemannSurface
