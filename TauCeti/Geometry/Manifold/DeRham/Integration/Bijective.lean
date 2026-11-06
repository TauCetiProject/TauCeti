/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.DeRham.Euclidean
import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset

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

/-! Extension by zero is defined between open subsets of `M`. To extend from an open subset `U` to
`M` itself, extend to the open subset `⊤` and identify `⊤` with `M` through a diffeomorphism `Φ`
whose underlying map is the inclusion, such as `Diffeomorph.ofTop`. The helpers below take `Φ` as an
argument, so that only its underlying map, and not its construction, enters the proofs. -/

/-- Extension by zero from an open subset `U` to `M`, on compactly supported cohomology: extend to
the open subset `⊤` and identify it with `M` through `Φ`. -/
private def ofOpens (Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M) (U : Opens M) (n : ℕ) :
    compactlySupportedDeRhamCohomology I U n →ₗ[ℝ] compactlySupportedDeRhamCohomology I M n :=
  (equivOfDiffeomorph Φ n).symm.toLinearMap ∘ₗ extendByZero (le_top : U ≤ ⊤) n

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- The pullback along `Φ` of a compactly supported closed form, as a rough form. -/
private theorem coe_mpullback_ofTop (Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M)
    (φ : compactlySupportedClosedForms I M n) :
    ((compactlySupportedClosedForms.mpullback Φ Φ.contMDiff Φ.toHomeomorph.isProperMap n φ :
      SmoothForm I (⊤ : Opens M) ℝ n) : RoughForm I (⊤ : Opens M) ℝ n) =
      mpullback I I Φ φ.1.1 :=
  (congrArg Subtype.val (compactlySupportedClosedForms.coe_mpullback _ _ _ n φ)).trans
    (SmoothForm.coe_mpullback _ _ _)

/-- Extension by zero from an open subset `U` preserves integrals. -/
private theorem integral_ofOpens (o : Manifold.Orientation I M (Fin n))
    {Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M} (hΦ : ⇑Φ = Subtype.val) (U : Opens M) [SigmaCompactSpace U]
    (z : compactlySupportedDeRhamCohomology I U n) :
    integral o (ofOpens Φ U n z) = integral (o.restrict U) z := by
  have : SigmaCompactSpace (⊤ : Opens M) := Φ.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  rw [← integral_extendByZero o (le_top : U ≤ ⊤)]
  obtain ⟨φ, hφ⟩ := mk_surjective I n (ofOpens Φ U n z)
  have hz : extendByZero (le_top : U ≤ ⊤) n z = equivOfDiffeomorph Φ n (mk I n φ) := by
    rw [hφ, ofOpens, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have h : integralTopForm (o.restrict ⊤) (mpullback I I Φ φ.1.1) = integralTopForm o φ.1.1 := by
    rw [hΦ]
    exact integralTopForm_mpullback_subtypeVal o ⊤ (by simp)
  rw [hz, ← hφ, equivOfDiffeomorph_mk, integral_mk, integral_mk, ← h, coe_mpullback_ofTop]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
/-- The class of a compactly supported top form supported in an open subset `U` comes from
`H^n_c(U)`. -/
private theorem mk_mem_range_ofOpens (hn : finrank ℝ E ≤ n) {Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M}
    (hΦ : ⇑Φ = Subtype.val) (U : Opens M) (φ : compactlySupportedClosedForms I M n)
    (hφ : _root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) φ.1.1 ⊆ U) :
    mk I n φ ∈ LinearMap.range (ofOpens Φ U n) := by
  let ψ := compactlySupportedClosedForms.mpullback Φ Φ.contMDiff Φ.toHomeomorph.isProperMap n φ
  -- The pullback of `φ` to `⊤` is supported in `U`, so it is an extension by zero from `U`.
  obtain ⟨χ, hχ⟩ := (compactlySupportedForms.mem_range_extendByZero_iff (le_top : U ≤ ⊤)
    (φ := ⟨ψ.1, compactlySupportedClosedForms_le_compactlySupportedForms I n ψ.2⟩)).mpr <| by
    dsimp only
    rw [coe_mpullback_ofTop]
    refine (RoughForm.tsupport_mpullback_subset_preimage Φ.continuous _).trans fun x hx ↦ ?_
    simpa [hΦ] using hφ hx
  refine ⟨mk I n ⟨χ.1, (mem_compactlySupportedClosedForms I).mpr
    ⟨χ.2, mem_closedForms_of_finrank_le I hn _⟩⟩, ?_⟩
  rw [ofOpens, LinearMap.comp_apply, extendByZero_mk, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_eq, equivOfDiffeomorph_mk]
  refine congrArg (mk I n) (Subtype.ext (Subtype.ext ?_))
  rw [compactlySupportedClosedForms.coe_extendByZero, coe_mpullback_ofTop,
    ← compactlySupportedForms.coe_extendByZero (le_top : U ≤ ⊤), hχ]
  exact coe_mpullback_ofTop Φ φ

/-- If integration is injective on `H^n_c(U)` and `e` is a class from `U` of integral one, then
every class `y` from `U` is `(∫_M y) • e`. -/
private theorem range_ofOpens_le_eqLocus (o : Manifold.Orientation I M (Fin n))
    {Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M} (hΦ : ⇑Φ = Subtype.val) (U : Opens M) [SigmaCompactSpace U]
    (hU : Injective (integral (o.restrict U))) {e : compactlySupportedDeRhamCohomology I M n}
    (he : e ∈ LinearMap.range (ofOpens Φ U n)) (he₁ : integral o e = 1) :
    LinearMap.range (ofOpens Φ U n) ≤
      LinearMap.eqLocus LinearMap.id ((integral o).smulRight e) := by
  obtain ⟨a, rfl⟩ := he
  rintro _ ⟨b, rfl⟩
  have h : b - integral o (ofOpens Φ U n b) • a = 0 := hU <| by
    rw [map_sub, map_smul, ← integral_ofOpens o hΦ, ← integral_ofOpens o hΦ, he₁, smul_eq_mul,
      mul_one, sub_self, map_zero]
  rw [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.smulRight_apply, ← map_smul,
    ← sub_eq_zero, ← map_sub, h, map_zero]

/-- Let `V` be an open subset all of whose classes are their integrals times `e`, and let `U` be
an open subset meeting `V` on which integration is injective. Then all classes from `U` are their
integrals times `e`: a class of integral one supported in `U ∩ V` comes from both. -/
private theorem range_ofOpens_le_eqLocus_of_inter_nonempty (hn : finrank ℝ E ≤ n)
    (o : Manifold.Orientation I M (Fin n)) {Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M}
    (hΦ : ⇑Φ = Subtype.val) {e : compactlySupportedDeRhamCohomology I M n} (U : Opens M)
    [SigmaCompactSpace U] (hU : Injective (integral (o.restrict U))) {V : Opens M}
    (hV : LinearMap.range (ofOpens Φ V n) ≤
      LinearMap.eqLocus LinearMap.id ((integral o).smulRight e))
    (hUV : ((U : Set M) ∩ V).Nonempty) :
    LinearMap.range (ofOpens Φ U n) ≤
      LinearMap.eqLocus LinearMap.id ((integral o).smulRight e) := by
  obtain ⟨p, hpU, hpV⟩ := hUV
  obtain ⟨τ, hτ, hτ₁⟩ := exists_compactlySupportedClosedForms_integralTopForm_eq_one o p
    (Filter.inter_mem (U.isOpen.mem_nhds hpU) (V.isOpen.mem_nhds hpV))
  have h₁ : integral o (mk I n τ) = 1 := by rw [integral_mk, hτ₁]
  have he : mk I n τ = e := by
    have := hV (mk_mem_range_ofOpens hn hΦ V τ (hτ.trans inter_subset_right))
    rwa [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.smulRight_apply, h₁, one_smul] at this
  exact he ▸ range_ofOpens_le_eqLocus o hΦ U hU
    (mk_mem_range_ofOpens hn hΦ U τ (hτ.trans inter_subset_left)) h₁

omit [BoundarylessManifold I M] in
/-- A submodule of `H^n_c(M)` containing the classes from every member of a family of open subsets
covering `M` is everything: a partition of unity splits every compactly supported top form into
finitely many forms supported in members of the family. -/
private theorem eq_top_of_forall_range_ofOpens_le (hn : finrank ℝ E ≤ n)
    {Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M} (hΦ : ⇑Φ = Subtype.val)
    {K : Submodule ℝ (compactlySupportedDeRhamCohomology I M n)} (V : M → Opens M)
    (hxV : ∀ x, x ∈ V x) (hK : ∀ x, LinearMap.range (ofOpens Φ (V x) n) ≤ K) : K = ⊤ := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun x ↦ (V x : Set M)) (fun x ↦ (V x).isOpen) fun x _ ↦ mem_iUnion.mpr ⟨x, hxV x⟩
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective I n y
  have hc := (mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp φ.2).1
  obtain ⟨s, hs, -⟩ := RoughForm.exists_finset_partition_eq φ.1.1 hc ρ.toPartitionOfUnity
  -- The pieces `ρ i • φ` of `φ`, each supported in `V i`.
  let ψ (i : M) : compactlySupportedClosedForms I M n :=
    ⟨⟨fun x ↦ ρ i x • φ.1.1 x, (φ.1.isSmoothForm.fun_smul (ρ i).contMDiff).mem_smoothBundleForms⟩,
      (mem_compactlySupportedClosedForms I).mpr
        ⟨(mem_compactlySupportedForms I).mpr (hc.of_isClosed_subset (isClosed_tsupport _)
          (_root_.tsupport_smul_subset_right (ρ i) (show M → E [⋀^Fin n]→L[ℝ] ℝ from φ.1.1))),
          mem_closedForms_of_finrank_le I hn _⟩⟩
  have hφ : φ = ∑ i ∈ s, ψ i := Subtype.ext <| Subtype.ext <| by
    rw [Submodule.coe_sum, Submodule.coe_sum]
    refine hs.trans (funext fun x ↦ ?_)
    simp only [ψ, Finset.sum_apply]
    -- The partition of unity and its underlying continuous partition agree pointwise.
    rfl
  rw [hφ, map_sum]
  exact K.sum_mem fun i _ ↦ hK i (mk_mem_range_ofOpens hn hΦ (V i) (ψ i)
    ((_root_.tsupport_smul_subset_left (ρ i) (show M → E [⋀^Fin n]→L[ℝ] ℝ from φ.1.1)).trans
      (hρ i)))

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
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M, ⇑Φ = Subtype.val :=
    ⟨Diffeomorph.ofTop ⊤ rfl, funext Diffeomorph.ofTop_apply⟩
  -- A class `e₀` of integral one, supported in a neighbourhood `U₀` on which integration is
  -- injective; `K` consists of the classes which are their integrals times `e₀`.
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨U₀, hx₀, _, hU₀⟩ := exists_opens_injective_integral o x₀
  obtain ⟨τ₀, hτ₀U, hτ₀⟩ :=
    exists_compactlySupportedClosedForms_integralTopForm_eq_one o x₀ (U₀.isOpen.mem_nhds hx₀)
  have he₀ : integral o (mk I n τ₀) = 1 := by rw [integral_mk, hτ₀]
  let K := LinearMap.eqLocus LinearMap.id ((integral o).smulRight (mk I n τ₀))
  -- By connectedness, every point has a neighbourhood all of whose classes lie in `K`.
  let S : Set M := {x | ∃ V : Opens M, x ∈ V ∧ LinearMap.range (ofOpens Φ V n) ≤ K}
  have hS : S = univ := by
    refine IsClopen.eq_univ ⟨?_, ?_⟩ ⟨x₀, U₀, hx₀,
      range_ofOpens_le_eqLocus o hΦ U₀ hU₀ (mk_mem_range_ofOpens hn hΦ U₀ τ₀ hτ₀U) he₀⟩
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨U, hxU, _, hU⟩ := exists_opens_injective_integral o x
      exact ⟨U, fun y hyU ⟨V, hyV, hV⟩ ↦ hx ⟨U, hxU,
        range_ofOpens_le_eqLocus_of_inter_nonempty hn o hΦ U hU hV ⟨y, hyU, hyV⟩⟩, U.isOpen, hxU⟩
    · rw [isOpen_iff_forall_mem_open]
      rintro x ⟨V, hxV, hV⟩
      exact ⟨V, fun y hy ↦ ⟨V, hy, hV⟩, V.isOpen, hxV⟩
  choose V hxV hV using fun x ↦ (hS ▸ mem_univ x : x ∈ S)
  have hK : K = ⊤ := eq_top_of_forall_range_ofOpens_le hn hΦ V hxV hV
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
