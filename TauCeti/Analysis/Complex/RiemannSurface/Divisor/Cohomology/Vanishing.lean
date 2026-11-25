/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.MittagLeffler
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.LinearEquivalence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.PointSeparation

/-!
# Vanishing of `H¹(X, 𝒪_D)` for large divisors and the Mittag-Leffler sequence

Let `X` be a compact connected Hausdorff Riemann surface. This file proves that the first Čech
cohomology of the divisor sheaf `𝒪_E` vanishes for all sufficiently large divisors `E`
(`TauCeti.RiemannSurface.exists_forall_le_subsingleton_divisorCechCohomology_one`), and deduces
Forster's Theorem 17.3: every class of `H¹(X, 𝒪_D)` is the obstruction of a Mittag-Leffler
distribution (`TauCeti.RiemannSurface.mittagLefflerConnecting_surjective`), so that

`0 → H⁰(X, 𝒪_D) → 𝓜(X) → PrincipalParts D → H¹(X, 𝒪_D) → 0`

is exact. So `H¹(X, 𝒪_D)` is the space of Mittag-Leffler distributions relative to `D` modulo the
principal parts of meromorphic functions, which is the form of `H¹` on which the residue pairing
of Serre duality is defined.

The proof uses no estimate beyond the finite-dimensionality of `H¹(X, 𝒪_D)`. The maps
`H¹(𝒪_D) → H¹(𝒪_E)` induced by inclusions `D ≤ E` are surjective, so `h¹` is antitone in the
divisor. Let `E` be a divisor at which `h¹` takes its least value. Then every inclusion `E ≤ G`
induces an isomorphism on `H¹`, and so does every inclusion out of a divisor linearly equivalent
to `E`. Take a meromorphic function `f` whose only pole is a pole of order `k ≥ 1` at a point
`x`, and let `P = k[x]`. Multiplication by `f` and the inclusion give two maps
`H¹(𝒪_E) → H¹(𝒪_{E+P})`, the second an isomorphism. If `H¹(𝒪_E)` were nonzero, the
endomorphism `ι⁻¹ ∘ f` would have an eigenvalue `c`, so multiplication by `f - c` would fail to be
injective on `H¹(𝒪_E)`. But `f - c` is a nonzero meromorphic function, and multiplication by it
is the isomorphism `𝒪_E ≅ 𝒪_{E - (f - c)}` followed by an inclusion out of a divisor linearly
equivalent to `E`, which is injective on `H¹`.

## Main results

* `TauCeti.RiemannSurface.exists_forall_le_subsingleton_divisorCechCohomology_one`: there is a
  divisor `E` with `H¹(X, 𝒪_F) = 0` for every `F ≥ E`.
* `TauCeti.RiemannSurface.mittagLefflerConnecting_surjective`: the Mittag-Leffler connecting map
  `PrincipalParts D → H¹(X, 𝒪_D)` is surjective (Forster, Theorem 17.3).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 17.3 (the exactness of the Mittag-Leffler sequence).
-/

public noncomputable section

open CategoryTheory Filter
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- If `h¹` takes its least value at `E`, then every inclusion `E ≤ G` induces an injective map
`H¹(𝒪_E) → H¹(𝒪_G)`: the map is surjective between spaces of the same dimension. -/
private theorem divisorCechCohomologyMapOfLE_one_injective_of_le_finrank {E G : WeilDivisor X}
    (hE : ∀ F : WeilDivisor X, Module.finrank ℂ (divisorCechCohomology E 1) ≤
      Module.finrank ℂ (divisorCechCohomology F 1)) (hEG : E ≤ G) :
    Function.Injective (divisorCechCohomologyMapOfLE hEG 1) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_divisorCechCohomology_one_le_of_le hEG).antisymm (hE G)).symm).2
    (divisorCechCohomologyMapOfLE_one_surjective hEG)

/-- If `h¹` takes its least value at `E`, multiplication by a nonzero meromorphic function `g`
of order at least `E - G` is injective on `H¹(𝒪_E)`. It is the isomorphism
`H¹(𝒪_E) ≅ H¹(𝒪_{E - (g)})` followed by the map of an inclusion out of `E - (g)`, at which `h¹`
takes the same least value. -/
private theorem divisorCechCohomologyMeromorphicMul_one_injective_of_le_finrank
    {E G : WeilDivisor X}
    (hE : ∀ F : WeilDivisor X, Module.finrank ℂ (divisorCechCohomology E 1) ≤
      Module.finrank ℂ (divisorCechCohomology F 1))
    {g : MeromorphicFunction X} (hg₀ : g ≠ 0)
    (hg : ∀ y, ((E y - G y : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order y g) :
    Function.Injective (divisorCechCohomologyMeromorphicMul g hg 1) := by
  let u : Additive (MeromorphicFunction X)ˣ := Additive.ofMul (Units.mk0 g hg₀)
  have hval : ((u.toMul : (MeromorphicFunction X)ˣ) : MeromorphicFunction X) = g := by
    simp [u]
  have hu : (MeromorphicFunction.orderSystem X).principalDivisor u =
      E - (E - (MeromorphicFunction.orderSystem X).principalDivisor u) :=
    (sub_sub_cancel _ _).symm
  have hFG : E - (MeromorphicFunction.orderSystem X).principalDivisor u ≤ G := fun y ↦ by
    have := hg y
    rw [← hval, ← MeromorphicFunction.coe_coeff_principalDivisor_orderSystem u y] at this
    have := WithTop.coe_le_coe.1 this
    simp only [WeilDivisor.coeff] at this
    simp only [Finsupp.sub_apply]
    omega
  let iso := divisorCechCohomologyIsoOfPrincipalDivisorEq u hu 1
  have hF (F : WeilDivisor X) : Module.finrank ℂ (divisorCechCohomology
      (E - (MeromorphicFunction.orderSystem X).principalDivisor u) 1) ≤
        Module.finrank ℂ (divisorCechCohomology F 1) :=
    iso.toLinearEquiv.finrank_eq ▸ hE F
  have hmul : divisorCechCohomologyMeromorphicMul g hg 1 =
      divisorCechCohomologyMapOfLE hFG 1 ∘ₗ iso.hom.hom := by
    rw [divisorCechCohomologyMapOfLE_comp_divisorCechCohomologyIsoOfPrincipalDivisorEq_hom]
    simp only [hval]
  rw [hmul, LinearMap.coe_comp]
  exact (divisorCechCohomologyMapOfLE_one_injective_of_le_finrank hF hFG).comp
    iso.toLinearEquiv.injective

/-- A meromorphic function `f` which differs from every constant, with an effective divisor `P`
bounding its poles: `ord f ≥ -P`. Any meromorphic function with a pole will do. -/
private theorem exists_meromorphicFunction_ne_algebraMap :
    ∃ (f : MeromorphicFunction X) (P : WeilDivisor X), 0 ≤ P ∧
      (∀ c : ℂ, f - algebraMap ℂ _ c ≠ 0) ∧
        ∀ y, ((-P y : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order y f := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := X)
  obtain ⟨k, ⟨f, hfx, hf⟩, hk⟩ :=
    ((MeromorphicFunction.eventually_exists_order_eq_neg x).and (eventually_ge_atTop 1)).exists
  refine ⟨f, k • WeilDivisor.ofPoint x, nsmul_nonneg (WeilDivisor.ofPoint_nonneg x) k,
    fun c ↦ ?_, fun y ↦ ?_⟩
  · -- `f` has a pole at `x`, and no constant has.
    rw [sub_ne_zero]
    rintro rfl
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, (MeromorphicFunction.order x).map_zero] at hfx
      exact WithTop.top_ne_coe hfx
    · rw [MeromorphicFunction.order_algebraMap hc] at hfx
      exact absurd (WithTop.coe_eq_zero.1 hfx.symm) (by omega)
  · rw [Finsupp.smul_apply, nsmul_eq_mul]
    rcases eq_or_ne y x with rfl | hyx
    · rw [show WeilDivisor.ofPoint y y = 1 from WeilDivisor.coeff_ofPoint_self y, mul_one, hfx]
    · rw [show WeilDivisor.ofPoint x y = 0 from WeilDivisor.coeff_ofPoint_of_ne hyx, mul_zero,
        neg_zero, WithTop.coe_zero]
      exact hf y hyx

/-- If `h¹` takes its least value at `E`, then `H¹(X, 𝒪_E) = 0`. -/
private theorem subsingleton_divisorCechCohomology_one_of_le_finrank {E : WeilDivisor X}
    (hE : ∀ F : WeilDivisor X, Module.finrank ℂ (divisorCechCohomology E 1) ≤
      Module.finrank ℂ (divisorCechCohomology F 1)) :
    Subsingleton (divisorCechCohomology E 1) := by
  obtain ⟨f, P, hP, hf₀, hf⟩ := exists_meromorphicFunction_ne_algebraMap (X := X)
  have hEP : E ≤ E + P := le_add_of_nonneg_right hP
  have hfP (y : X) : ((E y - (E + P) y : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order y f := by
    rw [Finsupp.add_apply, sub_add_cancel_left]
    exact hf y
  -- The inclusion `ι : H¹(𝒪_E) → H¹(𝒪_{E+P})` is an isomorphism, so if `H¹(𝒪_E) ≠ 0` then
  -- `ι⁻¹ ∘ f` has an eigenvector `ξ`, with eigenvalue `c`.
  let ι := LinearEquiv.ofBijective (divisorCechCohomologyMapOfLE hEP 1)
    ⟨divisorCechCohomologyMapOfLE_one_injective_of_le_finrank hE hEP,
      divisorCechCohomologyMapOfLE_one_surjective hEP⟩
  rw [← not_nontrivial_iff_subsingleton]
  intro
  obtain ⟨c, hc⟩ :=
    Module.End.exists_eigenvalue (ι.symm.toLinearMap ∘ₗ divisorCechCohomologyMeromorphicMul f hfP 1)
  obtain ⟨ξ, hξ⟩ := hc.exists_hasEigenvector
  -- Then multiplication by the nonzero function `f - c` kills `ξ`, so it is not injective.
  have hfcP (y : X) : ((E y - (E + P) y : ℤ) : WithTop ℤ) ≤
      MeromorphicFunction.order y (f - algebraMap ℂ _ c) :=
    (le_min (hfP y) (sub_le_order_algebraMap hEP c y)).trans
      ((MeromorphicFunction.order y).map_sub _ _)
  have hξ₀ : divisorCechCohomologyMeromorphicMul (f - algebraMap ℂ _ c) hfcP 1 ξ = 0 := by
    rw [divisorCechCohomologyMeromorphicMul_sub f _ hfP (sub_le_order_algebraMap hEP c),
      divisorCechCohomologyMeromorphicMul_algebraMap hEP c,
      LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, ← ι.apply_symm_apply
        (divisorCechCohomologyMeromorphicMul f hfP 1 ξ)]
    exact congrArg ι hξ.apply_eq_smul |>.trans (ι.map_smul c ξ)
  exact hξ.2 (divisorCechCohomologyMeromorphicMul_one_injective_of_le_finrank hE (hf₀ c) hfcP
    (hξ₀.trans (map_zero _).symm))

/-- **Vanishing of `H¹` for large divisors.** On a compact connected Hausdorff Riemann surface
there is a divisor `E` such that `H¹(X, 𝒪_F) = 0` for every divisor `F ≥ E`. -/
theorem exists_forall_le_subsingleton_divisorCechCohomology_one :
    ∃ E : WeilDivisor X, ∀ F, E ≤ F → Subsingleton (divisorCechCohomology F 1) := by
  let h₁ (F : WeilDivisor X) : ℕ := Module.finrank ℂ (divisorCechCohomology F 1)
  have := subsingleton_divisorCechCohomology_one_of_le_finrank (Function.argmin_le h₁ ·)
  exact ⟨Function.argmin h₁, fun F hF ↦
    (divisorCechCohomologyMapOfLE_one_surjective hF).subsingleton⟩

/-- **Forster, Theorem 17.3.** On a compact connected Hausdorff Riemann surface every class of
`H¹(X, 𝒪_D)` is the Mittag-Leffler obstruction of a Mittag-Leffler distribution relative to
`D`. -/
theorem mittagLefflerConnecting_surjective (D : WeilDivisor X) :
    Function.Surjective (mittagLefflerConnecting D) := by
  obtain ⟨E, hE⟩ := exists_forall_le_subsingleton_divisorCechCohomology_one (X := X)
  have := hE (D ⊔ E) le_sup_right
  rw [← LinearMap.range_eq_top, range_mittagLefflerConnecting, eq_top_iff]
  exact fun ξ _ ↦ Submodule.mem_iSup_of_mem (D ⊔ E) <| Submodule.mem_iSup_of_mem le_sup_left <|
    LinearMap.mem_ker.2 (Subsingleton.elim _ _)

end TauCeti.RiemannSurface
