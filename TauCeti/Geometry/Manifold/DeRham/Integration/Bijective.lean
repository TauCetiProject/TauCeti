/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.DeRham.Euclidean
import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective

/-!
# Top compactly supported cohomology of a connected oriented manifold

On a connected, oriented, boundaryless, Hausdorff, σ-compact smooth manifold `M` of finite
dimension `n`, integration `∫_M : H^n_c(M) → ℝ` is a linear isomorphism
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral`). Equivalently, a compactly
supported top form is the exterior derivative of a compactly supported form exactly when its
integral vanishes (`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`), and
`H^n_c(M)` is a line. This is the base case of Poincaré duality in the top degree.

Surjectivity holds without connectedness
(`TauCeti.compactlySupportedDeRhamCohomology.surjective_integral`). For injectivity, every point
has an open neighbourhood `U` diffeomorphic to `ℝⁿ`
(`TauCeti.exists_opens_diffeomorph_euclideanSpace`), on which integration `H^n_c(U) → ℝ` is
injective because `H^n_c(ℝⁿ)` is a line
(`TauCeti.finrank_compactlySupportedDeRhamCohomology_normedSpace`). Hence two compactly supported
top forms supported in `U` with the same integral have the same class in `H^n_c(M)`. Fix a class
`e₀` of integral one. The points having an open neighbourhood all of whose compactly supported
classes `y` satisfy `y = (∫_M y) • e₀` form an open set; its complement is open too, since two such
Euclidean neighbourhoods that meet share a localized class of integral one. By connectedness every
point has such a neighbourhood, and a partition of unity splits every compactly supported top form
into finitely many forms supported in them. So every class is `(∫_M y) • e₀`.

The connectedness hypothesis cannot be dropped: on a disjoint union of two copies of `ℝⁿ`,
`H^n_c` is two-dimensional.

## Main results

* `TauCeti.compactlySupportedDeRhamCohomology.injective_integral`,
  `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral`: integration on `H^n_c(M)` is
  injective, hence bijective, on a connected manifold.
* `TauCeti.compactlySupportedDeRhamCohomologyIntegralEquiv`: integration as a linear isomorphism
  `H^n_c(M) ≃ₗ[ℝ] ℝ`.
* `TauCeti.finrank_compactlySupportedDeRhamCohomology_top`: `H^n_c(M)` is one-dimensional.
* `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`: a compactly supported
  top form has a compactly supported primitive exactly when its integral vanishes.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Cohomology with
  Compact Support, the integration isomorphism on top compactly supported cohomology.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5.
-/

public noncomputable section

open Set Function Module TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] {n : ℕ}

namespace compactlySupportedDeRhamCohomology

/-- If integration is injective on `H^n_c(U)` and `e` is a class from `U` of integral one, then
every class `y` from `U` is `(∫_M y) • e`. -/
private theorem range_extendByZeroTop_le_eqLocus (o : Manifold.Orientation I M (Fin n))
    (U : Opens M) [SigmaCompactSpace U] (hU : Injective (integral (o.restrict U)))
    {e : compactlySupportedDeRhamCohomology I M n}
    (he : e ∈ LinearMap.range (extendByZeroTop U n)) (he₁ : integral o e = 1) :
    LinearMap.range (extendByZeroTop U n) ≤
      LinearMap.eqLocus LinearMap.id ((integral o).smulRight e) := by
  obtain ⟨a, rfl⟩ := he
  rintro _ ⟨b, rfl⟩
  have h : b - integral o (extendByZeroTop U n b) • a = 0 := hU <| by
    rw [map_sub, map_smul, ← integral_extendByZeroTop o, ← integral_extendByZeroTop o, he₁,
      smul_eq_mul, mul_one, sub_self, map_zero]
  rw [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.smulRight_apply, ← map_smul,
    ← sub_eq_zero, ← map_sub, h, map_zero]

/-- Let `V` be an open subset all of whose classes are their integrals times `e`, and let `U` be
an open subset meeting `V` on which integration is injective. Then all classes from `U` are their
integrals times `e`: a class of integral one supported in `U ∩ V` comes from both. -/
private theorem range_extendByZeroTop_le_eqLocus_of_inter_nonempty
    (o : Manifold.Orientation I M (Fin n)) {e : compactlySupportedDeRhamCohomology I M n}
    (U : Opens M) [SigmaCompactSpace U] (hU : Injective (integral (o.restrict U))) {V : Opens M}
    (hV : LinearMap.range (extendByZeroTop V n) ≤
      LinearMap.eqLocus LinearMap.id ((integral o).smulRight e))
    (hUV : ((U : Set M) ∩ V).Nonempty) :
    LinearMap.range (extendByZeroTop U n) ≤
      LinearMap.eqLocus LinearMap.id ((integral o).smulRight e) := by
  obtain ⟨p, hpU, hpV⟩ := hUV
  obtain ⟨τ, hτ, hτ₁⟩ := exists_compactlySupportedClosedForms_integralTopForm_eq_one o p
    (Filter.inter_mem (U.isOpen.mem_nhds hpU) (V.isOpen.mem_nhds hpV))
  have h₁ : integral o (mk I n τ) = 1 := by rw [integral_mk, hτ₁]
  have he : mk I n τ = e := by
    have := hV (mk_mem_range_extendByZeroTop V τ (hτ.trans inter_subset_right))
    rwa [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.smulRight_apply, h₁, one_smul] at this
  exact he ▸ range_extendByZeroTop_le_eqLocus o U hU
    (mk_mem_range_extendByZeroTop U τ (hτ.trans inter_subset_left)) h₁

omit [SigmaCompactSpace M] in
/-- Every point has an open neighbourhood `U` on which integration `H^n_c(U) → ℝ` is injective:
a neighbourhood diffeomorphic to `ℝⁿ`. -/
private theorem exists_opens_injective_integral (o : Manifold.Orientation I M (Fin n)) (x : M) :
    ∃ U : Opens M, x ∈ U ∧
      ∃ _ : SigmaCompactSpace U, Injective (integral (o.restrict U)) := by
  obtain ⟨U, hxU, ⟨Ψ⟩⟩ := exists_opens_diffeomorph_euclideanSpace (n := ⊤)
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  have : SigmaCompactSpace U := Ψ.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hfin : finrank ℝ (compactlySupportedDeRhamCohomology I U n) = finrank ℝ ℝ := by
    rw [← (equivOfDiffeomorph Ψ n).finrank_eq, finrank_self]
    exact finrank_compactlySupportedDeRhamCohomology_normedSpace _
      (by rw [finrank_euclideanSpace_fin, ← o.card_eq, Fintype.card_fin])
  have : FiniteDimensional ℝ (compactlySupportedDeRhamCohomology I U n) :=
    Module.finite_of_finrank_eq_succ (hfin.trans (finrank_self ℝ))
  exact ⟨U, hxU, ‹_›,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr (surjective_integral _)⟩

/-- **The top compactly supported cohomology of a connected manifold.** On a connected, oriented,
boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold, integration
`H^n_c(M) → ℝ` is injective. -/
theorem injective_integral [ConnectedSpace M] (o : Manifold.Orientation I M (Fin n)) :
    Injective (integral o) := by
  have hn : finrank ℝ E ≤ n := by simpa using o.card_eq.ge
  -- A class `e₀` of integral one, supported in a neighbourhood `U₀` on which integration is
  -- injective; `K` consists of the classes which are their integrals times `e₀`.
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨U₀, hx₀, _, hU₀⟩ := exists_opens_injective_integral o x₀
  obtain ⟨τ₀, hτ₀U, hτ₀⟩ :=
    exists_compactlySupportedClosedForms_integralTopForm_eq_one o x₀ (U₀.isOpen.mem_nhds hx₀)
  have he₀ : integral o (mk I n τ₀) = 1 := by rw [integral_mk, hτ₀]
  let K := LinearMap.eqLocus LinearMap.id ((integral o).smulRight (mk I n τ₀))
  -- By connectedness, every point has a neighbourhood all of whose classes lie in `K`.
  let S : Set M := {x | ∃ V : Opens M, x ∈ V ∧ LinearMap.range (extendByZeroTop V n) ≤ K}
  have hS : S = univ := by
    refine IsClopen.eq_univ ⟨?_, ?_⟩ ⟨x₀, U₀, hx₀,
      range_extendByZeroTop_le_eqLocus o U₀ hU₀ (mk_mem_range_extendByZeroTop U₀ τ₀ hτ₀U) he₀⟩
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨U, hxU, _, hU⟩ := exists_opens_injective_integral o x
      exact ⟨U, fun y hyU ⟨V, hyV, hV⟩ ↦ hx ⟨U, hxU,
        range_extendByZeroTop_le_eqLocus_of_inter_nonempty o U hU hV ⟨y, hyU, hyV⟩⟩, U.isOpen, hxU⟩
    · rw [isOpen_iff_forall_mem_open]
      rintro x ⟨V, hxV, hV⟩
      exact ⟨V, fun y hy ↦ ⟨V, hy, hV⟩, V.isOpen, hxV⟩
  choose V hxV hV using fun x ↦ (hS ▸ mem_univ x : x ∈ S)
  have hK : K = ⊤ := eq_top_of_forall_range_extendByZeroTop_le hn V hxV hV
  intro a b hab
  have key (y) : y = integral o y • mk I n τ₀ := LinearMap.mem_eqLocus.mp (hK ▸ Submodule.mem_top)
  rw [key a, key b, hab]

/-- **The top compactly supported cohomology of a connected manifold.** On a connected, oriented,
boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold, integration
`H^n_c(M) → ℝ` is bijective. -/
theorem bijective_integral [ConnectedSpace M] (o : Manifold.Orientation I M (Fin n)) :
    Bijective (integral o) :=
  ⟨injective_integral o, surjective_integral o⟩

end compactlySupportedDeRhamCohomology

/-- **The top compactly supported cohomology of a connected manifold**: integration as a linear
isomorphism `H^n_c(M) ≃ₗ[ℝ] ℝ`, for a connected, oriented, boundaryless, Hausdorff, σ-compact
finite-dimensional smooth manifold. -/
def compactlySupportedDeRhamCohomologyIntegralEquiv [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedDeRhamCohomology I M n ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral o)

/-- The isomorphism `H^n_c(M) ≃ₗ[ℝ] ℝ` is integration. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyIntegralEquiv_apply [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) (x : compactlySupportedDeRhamCohomology I M n) :
    compactlySupportedDeRhamCohomologyIntegralEquiv o x =
      compactlySupportedDeRhamCohomology.integral o x :=
  LinearEquiv.ofBijective_apply _ _

/-- On a connected, oriented, boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold
of dimension `n`, the top compactly supported cohomology `H^n_c(M)` is one-dimensional. -/
theorem finrank_compactlySupportedDeRhamCohomology_top [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) :
    finrank ℝ (compactlySupportedDeRhamCohomology I M n) = 1 :=
  (compactlySupportedDeRhamCohomologyIntegralEquiv o).finrank_eq.trans (finrank_self ℝ)

/-- **The compactly supported Poincaré lemma in top degree, on a connected manifold.** On a
connected, oriented, boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold of
dimension `n`, a compactly supported smooth `n`-form is the exterior derivative of a compactly
supported form if and only if its integral vanishes. -/
theorem mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) {φ : SmoothForm I M ℝ n}
    (hφ : φ ∈ compactlySupportedForms I M n) :
    φ ∈ exactCompactlySupportedForms I M n ↔ integralTopForm o φ.1 = 0 := by
  refine ⟨integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o, fun h ↦ ?_⟩
  let ψ : compactlySupportedClosedForms I M n :=
    ⟨φ, (mem_compactlySupportedClosedForms I).mpr
      ⟨hφ, mem_closedForms_of_finrank_le I (by simpa using o.card_eq.ge) φ⟩⟩
  refine (compactlySupportedDeRhamCohomology.mk_eq_zero_iff I n ψ).mp
    ((injective_iff_map_eq_zero _).mp
      (compactlySupportedDeRhamCohomology.injective_integral o) _ ?_)
  rw [compactlySupportedDeRhamCohomology.integral_mk]
  exact h

end TauCeti
