/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Gluing distributions and currents on an open cover

Let `Ω` be an open subset of a finite-dimensional real normed space `E`, covered by open sets
`U i`. Suppose that for every `i` a continuous linear map `T i : 𝓓^{n}(U i, F) →L[ℝ] V` is given,
with values in a locally convex space `V`, and that these maps are compatible: `T i` and `T j`
agree on tests supported in `U i ∩ U j`. Then there is a unique continuous linear map
`S : 𝓓^{n}(Ω, F) →L[ℝ] V` whose restriction to each `U i` is `T i`
(`Distribution.existsUnique_gluing`). Restriction to an open subset is precomposition with the
extension by zero `TestFunction.monoCLM`.

With `F = ℝ` this glues distributions; with `F = E [⋀^Fin k]→L[ℝ] ℝ` and `V = ℝ` it glues
`k`-currents. The cover is arbitrary: it need not be locally finite or countable.

The glued map is `S φ = ∑ i ∈ s, T i (χ i • φ)` for finitely many smooth cutoffs `χ i`, supported in
`U i`, whose sum is one on the support of `φ`. Compatibility shows that this value does not depend
on the cutoffs: for a second family `χ'`, both sums equal `∑ i, ∑ j, T (χ i • χ' j • φ)`. Using one
family of cutoffs for all tests supported in a fixed compact set gives continuity for the LF
topology. Uniqueness is the localization principle
`AddMonoidHom.eq_zero_of_locally_vanishing`.

## Main declarations

* `Distribution.eq_of_forall_comp_monoCLM_eq`: continuous linear maps on tests on `Ω` which agree
  after restriction to every member of an open cover are equal.
* `Distribution.existsUnique_gluing`: compatible continuous linear maps on the members of an open
  cover glue to a unique continuous linear map on the union.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2 (Localization),
  Theorem 2.2.4.
-/

public section

open Set TopologicalSpace TestFunction
open scoped Distributions ContDiff Manifold

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {Ω : Opens E} {n : ℕ∞} {ι : Type*} {U : ι → Opens E} {T : ∀ i, 𝓓^{n}(U i, F) →L[ℝ] V}

/-- Compatible local maps take the same value on tests on `U i` and `U j` that coincide as
functions. -/
private theorem apply_eq_apply_of_coe_eq
    (hT : ∀ i j (φ : 𝓓^{n}(U i ⊓ U j, F)), T i (monoCLM ℝ φ) = T j (monoCLM ℝ φ))
    {i j : ι} {φ : 𝓓^{n}(U i, F)} {ψ : 𝓓^{n}(U j, F)} (h : ⇑φ = ⇑ψ) : T i φ = T j ψ := by
  let θ : 𝓓^{n}(U i ⊓ U j, F) := ⟨φ, φ.contDiff, φ.hasCompactSupport,
    subset_inter φ.tsupport_subset (h ▸ ψ.tsupport_subset)⟩
  have hφ : monoCLM ℝ θ = φ := TestFunction.ext fun x ↦ by simp [θ]
  have hψ : monoCLM ℝ θ = ψ := TestFunction.ext fun x ↦ by simp [θ, h]
  rw [← hφ, ← hψ, hT]

/-- The value `∑ i ∈ s, T i (χ i • φ)` does not depend on the family of cutoffs `χ i`, supported
in `U i`, as long as they sum to one on the support of `φ`. -/
private theorem sum_cutoffCLM_eq
    (hT : ∀ i j (φ : 𝓓^{n}(U i ⊓ U j, F)), T i (monoCLM ℝ φ) = T j (monoCLM ℝ φ))
    {s s' : Finset ι} {χ χ' : ι → E → ℝ} (hχ : ∀ i, ContDiff ℝ n (χ i))
    (hχ' : ∀ i, ContDiff ℝ n (χ' i)) (hχU : ∀ i, tsupport (χ i) ∩ Ω ⊆ U i)
    (hχ'U : ∀ i, tsupport (χ' i) ∩ Ω ⊆ U i) (φ : 𝓓^{n}(Ω, F))
    (hs : ∀ x ∈ tsupport φ, ∑ i ∈ s, χ i x = 1) (hs' : ∀ x ∈ tsupport φ, ∑ j ∈ s', χ' j x = 1) :
    ∑ i ∈ s, T i (cutoffCLM (hχ i) (hχU i) φ) = ∑ j ∈ s', T j (cutoffCLM (hχ' j) (hχ'U j) φ) := by
  -- Both sides equal the double sum of `T (χ i • χ' j • φ)`, evaluated on `U i` or on `U j`.
  have hprod (i j : ι) : ContDiff ℝ n (χ i * χ' j) := (hχ i).mul (hχ' j)
  have hprodl (i j : ι) : tsupport (χ i * χ' j) ∩ Ω ⊆ U i :=
    (inter_subset_inter_left _ (tsupport_mul_subset_left)).trans (hχU i)
  have hprodr (i j : ι) : tsupport (χ i * χ' j) ∩ Ω ⊆ U j :=
    (inter_subset_inter_left _ (tsupport_mul_subset_right)).trans (hχ'U j)
  -- A cutoff `g` equals the sum of its products with a family summing to one near `tsupport φ`.
  have hsplit {W : Opens E} {g : E → ℝ} {t : Finset ι} {c : ι → E → ℝ} (hg : ContDiff ℝ n g)
      (hgW : tsupport g ∩ Ω ⊆ W) (hc : ∀ i, ContDiff ℝ n (c i * g))
      (hcW : ∀ i, tsupport (c i * g) ∩ Ω ⊆ W) (ht : ∀ x ∈ tsupport φ, ∑ i ∈ t, c i x = 1) :
      cutoffCLM hg hgW φ = ∑ i ∈ t, cutoffCLM (hc i) (hcW i) φ := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · simp [← Finset.sum_smul, ht x hx, mul_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  calc ∑ i ∈ s, T i (cutoffCLM (hχ i) (hχU i) φ)
      = ∑ i ∈ s, ∑ j ∈ s', T i (cutoffCLM (hprod i j) (hprodl i j) φ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hsplit (hχ i) (hχU i) (c := χ') (fun j ↦ (hχ' j).mul (hχ i))
          (fun j ↦ by simpa only [mul_comm] using hprodl i j) hs', map_sum]
        exact Finset.sum_congr rfl fun j _ ↦ congrArg (T i) (TestFunction.ext fun x ↦ by
          simp [mul_comm])
    _ = ∑ i ∈ s, ∑ j ∈ s', T j (cutoffCLM (hprod i j) (hprodr i j) φ) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
          apply_eq_apply_of_coe_eq hT (by ext x; simp)
    _ = ∑ j ∈ s', T j (cutoffCLM (hχ' j) (hχ'U j) φ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hsplit (hχ' j) (hχ'U j) (c := χ) (fun i ↦ hprod i j) (fun i ↦ hprodr i j) hs, map_sum]

variable [FiniteDimensional ℝ E]

/-- **Locality.** Two continuous linear maps on tests on `Ω` are equal if their restrictions to
every member of an open cover `U` of `Ω` are equal. -/
theorem eq_of_forall_comp_monoCLM_eq (hU : ⨆ i, U i = Ω) {S S' : 𝓓^{n}(Ω, F) →L[ℝ] V}
    (h : ∀ i, S ∘L (monoCLM ℝ : 𝓓^{n}(U i, F) →L[ℝ] 𝓓^{n}(Ω, F)) = S' ∘L monoCLM ℝ) :
    S = S' := by
  have hzero := AddMonoidHom.eq_zero_of_locally_vanishing
    ((S : 𝓓^{n}(Ω, F) →+ V) - (S' : 𝓓^{n}(Ω, F) →+ V)) fun x hx ↦ ?_
  · ext φ
    simpa [sub_eq_zero] using DFunLike.congr_fun hzero φ
  · obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
      simpa [← SetLike.mem_coe, ← hU, Opens.coe_iSup] using hx
    refine ⟨U i, (U i).isOpen, hi, fun φ hφ ↦ ?_⟩
    -- A test on `Ω` supported in `U i` is the extension of a test on `U i`.
    let ψ : 𝓓^{n}(U i, F) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    have hψ : monoCLM ℝ ψ = φ := TestFunction.ext fun y ↦ by simp [ψ, hU ▸ le_iSup U i]
    simpa [hψ, sub_eq_zero] using DFunLike.congr_fun (h i) ψ

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]

/-- **Gluing of distributions and currents.** Let the open sets `U i` cover `Ω`. Continuous linear
maps `T i` on tests on `U i` which agree on tests on every overlap `U i ⊓ U j` are the
restrictions of a unique continuous linear map on tests on `Ω`. -/
theorem existsUnique_gluing (hU : ⨆ i, U i = Ω)
    (hT : ∀ i j (φ : 𝓓^{n}(U i ⊓ U j, F)), T i (monoCLM ℝ φ) = T j (monoCLM ℝ φ)) :
    ∃! S : 𝓓^{n}(Ω, F) →L[ℝ] V, ∀ i, S ∘L monoCLM ℝ = T i := by
  classical
  have hUΩ (i : ι) : U i ≤ Ω := hU ▸ le_iSup U i
  -- Every compact subset of `Ω` carries finitely many smooth cutoffs subordinate to the cover and
  -- summing to one on it.
  have hcut (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ (s : Finset ι) (χ : ι → E → ℝ)
      (hχ : ∀ i, ContDiff ℝ n (χ i)), (∀ i, tsupport (χ i) ∩ Ω ⊆ U i) ∧
        ∀ x ∈ K, ∑ i ∈ s, χ i x = 1 := by
    have hKU : K ⊆ ⋃ i, (U i : Set E) := by rwa [← Opens.coe_iSup, hU]
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK.isClosed
      (fun i ↦ (U i : Set E)) (fun i ↦ (U i).isOpen) hKU
    have hfin := ρ.locallyFinite.finite_nonempty_inter_compact hK
    refine ⟨hfin.toFinset, fun i ↦ ρ i, fun i ↦ (ρ i).contMDiff.contDiff.of_le (by simp),
      fun i ↦ inter_subset_left.trans (hρ i), fun x hx ↦ ?_⟩
    refine ρ.toPartitionOfUnity.sum_finsupport' hx fun i hi ↦ ?_
    rw [PartitionOfUnity.mem_finsupport] at hi
    exact hfin.mem_toFinset.2 ⟨x, hi, hx⟩
  choose s χ hχ hχU hsum using hcut
  -- The glued value on `φ`, computed with the cutoffs chosen for `tsupport φ`.
  let S₀ : 𝓓^{n}(Ω, F) → V := fun φ ↦
    ∑ i ∈ s _ φ.hasCompactSupport φ.tsupport_subset,
      T i (cutoffCLM (hχ _ φ.hasCompactSupport φ.tsupport_subset i)
        (hχU _ φ.hasCompactSupport φ.tsupport_subset i) φ)
  -- With cutoffs summing to one on `tsupport φ`, the sum computes `S₀ φ`.
  have hS₀ (φ : 𝓓^{n}(Ω, F)) (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
      (hφK : tsupport φ ⊆ K) :
      S₀ φ = ∑ i ∈ s K hK hKΩ, T i (cutoffCLM (hχ K hK hKΩ i) (hχU K hK hKΩ i) φ) :=
    sum_cutoffCLM_eq hT _ _ _ _ φ (hsum _ _ _) fun x hx ↦ hsum K hK hKΩ x (hφK hx)
  let S : 𝓓^{n}(Ω, F) →L[ℝ] V := TestFunction.limitCLM ℝ S₀
    (fun K hKΩ ↦ ∑ i ∈ s K K.isCompact hKΩ,
      T i ∘L cutoffCLM (hχ K K.isCompact hKΩ i) (hχU K K.isCompact hKΩ i) ∘L
        ofSupportedInCLM ℝ hKΩ)
    (fun K hKΩ f ↦ by
      simpa using hS₀ (ofSupportedIn hKΩ f) K K.isCompact hKΩ f.tsupport_subset)
  have hSapply (φ : 𝓓^{n}(Ω, F)) : S φ = S₀ φ := TestFunction.limitCLM_apply ..
  have hglue (i : ι) : S ∘L monoCLM ℝ = T i := by
    -- On a test `ψ` on `U i`, replace each cutoff on `U j` by the same cutoff on `U i`.
    ext ψ
    have hψΩ : ⇑(monoCLM ℝ ψ : 𝓓^{n}(Ω, F)) = ψ := by simp [hUΩ i]
    have hK : IsCompact (tsupport ψ) := ψ.hasCompactSupport
    have hKΩ : tsupport ψ ⊆ Ω := ψ.tsupport_subset.trans (hUΩ i)
    have hloc (j : ι) : tsupport (χ _ hK hKΩ j) ∩ U i ⊆ U i := inter_subset_right
    rw [ContinuousLinearMap.comp_apply, hSapply, hS₀ _ _ hK hKΩ (by rw [hψΩ])]
    calc ∑ j ∈ s _ hK hKΩ, T j (cutoffCLM (hχ _ hK hKΩ j) (hχU _ hK hKΩ j) (monoCLM ℝ ψ))
        = ∑ j ∈ s _ hK hKΩ, T i (cutoffCLM (hχ _ hK hKΩ j) (hloc j) ψ) :=
          Finset.sum_congr rfl fun j _ ↦
            apply_eq_apply_of_coe_eq hT (by ext x; simp [hψΩ])
      _ = T i ψ := by
          rw [← map_sum]
          congr 1
          ext x
          by_cases hx : x ∈ tsupport ψ
          · simp [← Finset.sum_smul, hsum _ hK hKΩ x hx]
          · simp [image_eq_zero_of_notMem_tsupport hx]
  exact ⟨S, hglue, fun S' hS' ↦
    eq_of_forall_comp_monoCLM_eq hU fun i ↦ (hS' i).trans (hglue i).symm⟩

end Distribution
