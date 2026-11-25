/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
public import TauCeti.Algebra.Homology.ModuleCat.Biprod
import TauCeti.Geometry.Manifold.Metrizable
import TauCeti.Algebra.Homology.HomologySequenceBiprod

/-!
# The Mayer–Vietoris sequence of compactly supported de Rham complexes

For open subsets `U` and `V` of a Hausdorff manifold, extension by zero of compactly supported
smooth forms gives the compactly supported Mayer–Vietoris short complex
`0 ⟶ Ω_c^•(U ⊓ V) ⟶ Ω_c^•(U) ⊞ Ω_c^•(V) ⟶ Ω_c^•(U ⊔ V) ⟶ 0`,
whose first map is `(ext, -ext)` and whose second map is the sum `ext + ext` of the two extensions
by zero to `U ⊔ V`. Its arrows run opposite to those of the Mayer–Vietoris sequence of de Rham
complexes, `TauCeti.mayerVietorisShortComplex`, which is built from restrictions.

In each degree, the first map is injective and the sequence is exact in the middle on every
Hausdorff manifold: if compactly supported forms on `U` and `V` have extensions by zero summing to
zero, their common support lies in `U ⊓ V`, so they are the extensions of one compactly supported
form on `U ⊓ V`. The second map is surjective on a Hausdorff σ-compact manifold modelled on a
finite-dimensional space: a smooth partition of unity on `U ⊔ V` subordinate to the cover by `U`
and `V` splits a compactly supported form on `U ⊔ V` into a sum of compactly supported forms
supported in `U` and in `V`. Hence the compactly supported Mayer–Vietoris short complex is short
exact (`TauCeti.compactlySupportedMayerVietorisShortComplex_shortExact`), and Mathlib's
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂` and `homology_exact₃`
give the Mayer–Vietoris long exact sequence of compactly supported de Rham cohomology.

Its connecting map `H^k_c(U ⊔ V) → H^{k+1}_c(U ⊓ V)`
(`TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ`) is computed on representatives
(`TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ_mk`): write a compactly supported
closed form `τ` on `U ⊔ V` as `ext α + ext β` with `α` and `β` compactly supported on `U` and on
`V`; then `dα` and `-dβ` are the extensions by zero of one compactly supported closed form `σ` on
`U ⊓ V` (`TauCeti.compactlySupportedForms.exists_extendByZero_eq_mextDerivₗ`), and the class of
`τ` goes to the class of `σ`. This is the compactly supported counterpart of
`TauCeti.deRhamCohomology.mayerVietorisδ_mk`.

## Main definitions and results

* `TauCeti.compactlySupportedForms.extendByZero_add_extendByZero_eq_zero_iff`: exactness in the
  middle of the Mayer–Vietoris sequence of compactly supported smooth forms in a fixed degree.
* `TauCeti.compactlySupportedForms.surjective_coprod_extendByZero`: surjectivity of its second
  map. Injectivity of its first map is `TauCeti.compactlySupportedForms.extendByZero_injective`.
* `TauCeti.compactlySupportedMayerVietorisShortComplex`: the compactly supported Mayer–Vietoris
  short complex of compactly supported de Rham complexes.
* `TauCeti.compactlySupportedMayerVietorisShortComplex_shortExact`: it is short exact.
* `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ`: its connecting map
  `H^k_c(U ⊔ V) → H^{k+1}_c(U ⊓ V)`, computed on classes by
  `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ_mk`.
* `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisToProd` and
  `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisFromProd`: the maps
  `H^k_c(U ⊓ V) → H^k_c(U) × H^k_c(V) → H^k_c(U ⊔ V)` of extension by zero, `(ext, -ext)` and
  `ext + ext`, as linear maps to and from the product module.
* `TauCeti.compactlySupportedDeRhamCohomology.exact_mayerVietorisToProd_fromProd`,
  `TauCeti.compactlySupportedDeRhamCohomology.exact_mayerVietorisFromProd_δ` and
  `TauCeti.compactlySupportedDeRhamCohomology.exact_mayerVietorisδ_toProd`: the compactly supported
  Mayer–Vietoris long exact sequence, as exactness (`Function.Exact`) of linear maps;
  `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisFromProd_surjective`: it ends with a
  surjection in degrees at least the dimension.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, "Cohomology with Compact
  Support", the compactly supported Mayer–Vietoris theorem.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §2.
-/

public section

noncomputable section

open CategoryTheory Limits Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {k : ℕ}

namespace compactlySupportedForms

section Exactness

variable [IsManifold I 1 M]

/-- Compactly supported forms on `U` and `V` have extensions by zero to `U ⊔ V` summing to zero
exactly when they are the extensions by zero of a compactly supported form on `U ⊓ V` and of its
negative. -/
theorem extendByZero_add_extendByZero_eq_zero_iff {U V : Opens M}
    {α : compactlySupportedForms I U k} {β : compactlySupportedForms I V k} :
    extendByZero (le_sup_left : U ≤ U ⊔ V) k α + extendByZero (le_sup_right : V ≤ U ⊔ V) k β = 0 ↔
      ∃ θ : compactlySupportedForms I (U ⊓ V : Opens M) k,
        extendByZero inf_le_left k θ = α ∧ extendByZero inf_le_right k θ = -β := by
  refine ⟨fun hαβ ↦ ?_, ?_⟩
  · -- The common extension by zero of `α` and `-β` is supported in `U` and in `V`, hence it is
    -- the extension by zero of a compactly supported form `θ` on `U ⊓ V`.
    have hω : extendByZero le_sup_left k α = extendByZero le_sup_right k (-β) :=
      (eq_neg_of_add_eq_zero_left hαβ).trans
        (map_neg (extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k) β).symm
    obtain ⟨θ, hθ⟩ := (mem_range_extendByZero_iff (inf_le_left.trans le_sup_left)).mpr
      fun x hx ↦ ⟨(mem_range_extendByZero_iff le_sup_left).mp ⟨α, rfl⟩ hx,
        (mem_range_extendByZero_iff le_sup_right).mp ⟨-β, hω.symm⟩ hx⟩
    refine ⟨θ, extendByZero_injective (le_sup_left : U ≤ U ⊔ V) k ?_,
      extendByZero_injective (le_sup_right : V ≤ U ⊔ V) k ?_⟩
    · rw [extendByZero_extendByZero, hθ]
    · rw [extendByZero_extendByZero, hθ, hω]
  · rintro ⟨θ, rfl, hθ⟩
    -- Both composites of inclusions are the inclusion of `U ⊓ V` in `U ⊔ V`.
    have h : extendByZero (inf_le_left.trans le_sup_left) k θ =
        -extendByZero (le_sup_right : V ≤ U ⊔ V) k β :=
      ((extendByZero_extendByZero inf_le_right le_sup_right k θ).symm.trans
        (congrArg _ hθ)).trans (map_neg (extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k) β)
    rw [extendByZero_extendByZero, h]
    exact neg_add_cancel (extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k β)

end Exactness

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, every compactly
supported form on `U ⊔ V` is the sum of the extensions by zero of compactly supported forms on `U`
and on `V`. -/
theorem surjective_coprod_extendByZero [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [SigmaCompactSpace M] (U V : Opens M) :
    Function.Surjective
      ((extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V) k).coprod
        (extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k)) := by
  classical
  intro φ
  have := Manifold.sigmaCompactSpace_opens I (U ⊔ V)
  let W : Bool → Opens M := fun b ↦ cond b V U
  have hW (b : Bool) : W b ≤ U ⊔ V := by
    cases b
    exacts [le_sup_left, le_sup_right]
  have hcover : U ⊔ V ≤ iSup W := by
    simp [W, iSup_bool_eq, sup_comm]
  obtain ⟨s, ψ, hψ⟩ := exists_sum_extendByZero W hW hcover k φ
  let θ (b : Bool) : compactlySupportedForms I (W b) k := if b ∈ s then ψ b else 0
  have hsum : φ = ∑ b : Bool, extendByZero (hW b) k (θ b) := by
    simpa only [θ, apply_ite, map_zero, Finset.sum_ite_mem_eq] using hψ
  rw [Fintype.sum_bool, add_comm] at hsum
  exact ⟨(θ false, θ true), hsum.symm⟩

end compactlySupportedForms

section Complex

variable [IsManifold I 2 M]

variable (I) in
/-- The compactly supported Mayer–Vietoris short complex
`Ω_c^•(U ⊓ V) ⟶ Ω_c^•(U) ⊞ Ω_c^•(V) ⟶ Ω_c^•(U ⊔ V)` of compactly supported de Rham complexes, with
first map the pair `(ext, -ext)` of extensions by zero and second map the sum of the extensions by
zero. -/
@[expose] def compactlySupportedMayerVietorisShortComplex (U V : Opens M) :
    ShortComplex (CochainComplex (ModuleCat ℝ) ℕ) :=
  ShortComplex.mk
    (biprod.lift
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U))
      (-compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V)))
    (biprod.desc
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V))
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V)))
    (by
      rw [biprod.lift_desc, Preadditive.neg_comp,
        compactlySupportedDeRhamComplex.extendByZero_comp_extendByZero,
        compactlySupportedDeRhamComplex.extendByZero_comp_extendByZero]
      -- Both composites of inclusions are the inclusion of `U ⊓ V` in `U ⊔ V`.
      exact add_neg_cancel _)

/-- The first term of the compactly supported Mayer–Vietoris short complex is the compactly
supported de Rham complex of `U ⊓ V`. -/
@[simp]
theorem compactlySupportedMayerVietorisShortComplex_X₁ (U V : Opens M) :
    (compactlySupportedMayerVietorisShortComplex I U V).X₁ =
      compactlySupportedDeRhamComplex I (U ⊓ V : Opens M) :=
  (rfl)

/-- The middle term of the compactly supported Mayer–Vietoris short complex is the biproduct of the
compactly supported de Rham complexes of `U` and `V`. -/
@[simp]
theorem compactlySupportedMayerVietorisShortComplex_X₂ (U V : Opens M) :
    (compactlySupportedMayerVietorisShortComplex I U V).X₂ =
      (compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V) :=
  (rfl)

/-- The last term of the compactly supported Mayer–Vietoris short complex is the compactly
supported de Rham complex of `U ⊔ V`. -/
@[simp]
theorem compactlySupportedMayerVietorisShortComplex_X₃ (U V : Opens M) :
    (compactlySupportedMayerVietorisShortComplex I U V).X₃ =
      compactlySupportedDeRhamComplex I (U ⊔ V : Opens M) :=
  (rfl)

/-- The first map of the compactly supported Mayer–Vietoris short complex is the pair of the
extension by zero to `U` and the negative of the extension by zero to `V`. -/
@[simp]
theorem compactlySupportedMayerVietorisShortComplex_f (U V : Opens M) :
    (compactlySupportedMayerVietorisShortComplex I U V).f =
      biprod.lift
        (compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U))
        (-compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V)) :=
  (rfl)

/-- The second map of the compactly supported Mayer–Vietoris short complex is the sum of the
extensions by zero from `U` and from `V` to `U ⊔ V`. -/
@[simp]
theorem compactlySupportedMayerVietorisShortComplex_g (U V : Opens M) :
    (compactlySupportedMayerVietorisShortComplex I U V).g =
      biprod.desc
        (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V))
        (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V)) :=
  (rfl)

/-- **The compactly supported Mayer–Vietoris short exact sequence.** On a Hausdorff σ-compact
manifold modelled on a finite-dimensional space, the compactly supported Mayer–Vietoris short
complex of two open subsets is short exact. -/
theorem compactlySupportedMayerVietorisShortComplex_shortExact [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [SigmaCompactSpace M] (U V : Opens M) :
    (compactlySupportedMayerVietorisShortComplex I U V).ShortExact := by
  -- In each degree, transport the exactness of extension by zero of compactly supported forms
  -- along the identification of `(Ω_c^•(U) ⊞ Ω_c^•(V))^k` with the product module
  -- `Ω_cᵏ(U) × Ω_cᵏ(V)`.
  unfold compactlySupportedMayerVietorisShortComplex
  -- The sign is written as a scalar `-1`: synthesizing negation of linear maps between these
  -- submodules of smooth forms times out.
  let f (k : ℕ) := (compactlySupportedForms.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U) k).prod
    ((-1 : ℝ) • compactlySupportedForms.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V) k)
  let g (k : ℕ) :=
    (compactlySupportedForms.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V) k).coprod
      (compactlySupportedForms.extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k)
  have hexact (k : ℕ) : Function.Exact (f k) (g k) := by
    rintro ⟨α, β⟩
    simp only [f, g, LinearMap.coprod_apply, Set.mem_range, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.smul_apply, Prod.mk.injEq,
      compactlySupportedForms.extendByZero_add_extendByZero_eq_zero_iff]
    refine exists_congr fun θ ↦ and_congr_right' ?_
    rw [neg_one_smul ℝ
      (compactlySupportedForms.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V) k θ)]
    exact (neg_eq_iff_eq_neg (G := compactlySupportedForms I V k)).symm
  have hinj (k : ℕ) : Function.Injective (f k) := fun _ _ h ↦
    compactlySupportedForms.extendByZero_injective (I := I) (inf_le_left : U ⊓ V ≤ U) k
      (congrArg Prod.fst h)
  exact HomologicalComplex.moduleCat_shortExact_biprod _
    (fun k ↦ compactlySupportedDeRhamComplexXIso I k)
    (fun k ↦ compactlySupportedDeRhamComplexXIso I k)
    (fun k ↦ compactlySupportedDeRhamComplexXIso I k)
    (fun k ↦ compactlySupportedDeRhamComplexXIso I k) _
    (fun k ↦ (-1 : ℝ) • compactlySupportedForms.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V) k)
    _ _ (fun k ↦ compactlySupportedDeRhamComplex.extendByZero_f _ k)
    (fun k ↦ by
      rw [HomologicalComplex.neg_f_apply, Preadditive.neg_comp,
        compactlySupportedDeRhamComplex.extendByZero_f, ← Preadditive.comp_neg]
      congr 1
      ext : 1
      rw [ModuleCat.hom_neg, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
      exact (neg_one_smul ℝ _).symm)
    (fun k ↦ compactlySupportedDeRhamComplex.extendByZero_f _ k)
    (fun k ↦ compactlySupportedDeRhamComplex.extendByZero_f _ k) hexact hinj
    fun _ ↦ compactlySupportedForms.surjective_coprod_extendByZero U V

/-- Let `α` and `β` be compactly supported forms on `U` and on `V` whose extensions by zero to
`U ⊔ V` have closed sum. Then `dα` and `-dβ` are the extensions by zero of one compactly supported
closed form on `U ⊓ V`. This is the form that represents the image of the class of that sum under
the compactly supported Mayer–Vietoris connecting map
(`TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ_mk`). -/
theorem compactlySupportedForms.exists_extendByZero_eq_mextDerivₗ {U V : Opens M}
    (α : compactlySupportedForms I U k) (β : compactlySupportedForms I V k)
    (hαβ : (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) k α +
      compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) k β).val ∈
        closedForms I (U ⊔ V : Opens M) k) :
    ∃ σ : compactlySupportedClosedForms I (U ⊓ V : Opens M) (k + 1),
      compactlySupportedForms.extendByZero (inf_le_left : U ⊓ V ≤ U) (k + 1)
          ⟨σ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1) σ.property⟩ =
        compactlySupportedForms.mextDerivₗ I U k α ∧
      compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (k + 1)
          ⟨σ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1) σ.property⟩ =
        -compactlySupportedForms.mextDerivₗ I V k β := by
  -- The extensions by zero of `dα` and `dβ` sum to the exterior derivative of a closed form.
  obtain ⟨σ, hσU, hσV⟩ := compactlySupportedForms.extendByZero_add_extendByZero_eq_zero_iff.mp
    (by
      rw [← compactlySupportedForms.mextDerivₗ_extendByZero,
        ← compactlySupportedForms.mextDerivₗ_extendByZero, ← map_add]
      exact Subtype.ext (by
        rw [compactlySupportedForms.coe_mextDerivₗ]
        exact (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp hαβ) :
      compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) (k + 1)
          (compactlySupportedForms.mextDerivₗ I U k α) +
        compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) (k + 1)
          (compactlySupportedForms.mextDerivₗ I V k β) = 0)
  -- It is closed, since its extension by zero to `U` is exact.
  have hdσ : compactlySupportedForms.mextDerivₗ I (U ⊓ V : Opens M) (k + 1) σ = 0 :=
    compactlySupportedForms.extendByZero_injective (inf_le_left : U ⊓ V ≤ U) (k + 1 + 1) <| by
      rw [← compactlySupportedForms.mextDerivₗ_extendByZero, hσU, map_zero]
      exact LinearMap.congr_fun (compactlySupportedForms.mextDerivₗ_comp_mextDerivₗ I k) α
  refine ⟨⟨σ.val, (mem_compactlySupportedClosedForms I).mpr ⟨σ.property,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr ?_⟩⟩, hσU, hσV⟩
  simpa using congrArg Subtype.val hdσ

end Complex

section Connecting

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M]

namespace compactlySupportedDeRhamCohomology

variable (I) in
/-- The **compactly supported Mayer–Vietoris connecting map** `H^k_c(U ⊔ V) → H^{k+1}_c(U ⊓ V)`:
the connecting map of the long exact cohomology sequence of the compactly supported
Mayer–Vietoris short exact sequence. -/
def mayerVietorisδ (U V : Opens M) (k : ℕ) :
    compactlySupportedDeRhamCohomology I (U ⊔ V : Opens M) k →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I (U ⊓ V : Opens M) (k + 1) :=
  ((compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).δ k (k + 1) rfl).hom

/-- The compactly supported Mayer–Vietoris connecting map is the connecting morphism of the
homology sequence of the compactly supported Mayer–Vietoris short exact sequence, so Mathlib's
exactness results for that sequence apply. -/
theorem ofHom_mayerVietorisδ (U V : Opens M) (k : ℕ) :
    ModuleCat.ofHom (mayerVietorisδ I U V k) =
      (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).δ k (k + 1) rfl :=
  (rfl)

/-- **The compactly supported Mayer–Vietoris connecting map on classes.** Let `τ` be a compactly
supported closed form on `U ⊔ V`, written as the sum of the extensions by zero of compactly
supported forms `α` on `U` and `β` on `V`. If `σ` is a compactly supported closed form on
`U ⊓ V` whose extensions by zero are `dα` on `U` and `-dβ` on `V`, then the connecting map sends
the class of `τ` to the class of `σ`. -/
theorem mayerVietorisδ_mk (U V : Opens M) (τ : compactlySupportedClosedForms I (U ⊔ V : Opens M) k)
    (α : compactlySupportedForms I U k) (β : compactlySupportedForms I V k)
    (hαβ : compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) k α +
      compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) k β =
        ⟨τ.val, compactlySupportedClosedForms_le_compactlySupportedForms I k τ.property⟩)
    (σ : compactlySupportedClosedForms I (U ⊓ V : Opens M) (k + 1))
    (hσU : compactlySupportedForms.extendByZero (inf_le_left : U ⊓ V ≤ U) (k + 1)
      ⟨σ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1) σ.property⟩ =
        compactlySupportedForms.mextDerivₗ I U k α)
    (hσV : compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (k + 1)
      ⟨σ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1) σ.property⟩ =
        -compactlySupportedForms.mextDerivₗ I V k β) :
    mayerVietorisδ I U V k (mk I k τ) = mk I (k + 1) σ := by
  -- The lift of `τ` to `Ω_c^•(U) ⊞ Ω_c^•(V)` is the pair `(α, β)`.
  let x₂ : (compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).X k :=
    (biprod.inl : compactlySupportedDeRhamComplex I U ⟶ _).f k
        ((compactlySupportedDeRhamComplexXIso I k).inv α) +
      (biprod.inr : compactlySupportedDeRhamComplex I V ⟶ _).f k
        ((compactlySupportedDeRhamComplexXIso I k).inv β)
  have hx₂ : (biprod.desc
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V))
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V))).f k x₂ =
      (compactlySupportedDeRhamComplexXIso I k).inv
        ⟨τ.val, compactlySupportedClosedForms_le_compactlySupportedForms I k τ.property⟩ := by
    rw [← hαβ]
    simp only [map_add]
    rw [← compactlySupportedDeRhamComplex.extendByZero_f_inv_apply,
      ← compactlySupportedDeRhamComplex.extendByZero_f_inv_apply]
    simp [x₂, ← ModuleCat.comp_apply]
  -- The image of `σ` in `Ω_c^•(U) ⊞ Ω_c^•(V)` is the differential of the lift.
  have hσ : (biprod.lift
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U))
      (-compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V))).f
        (k + 1) ((compactlySupportedDeRhamComplexXIso I (k + 1)).inv
          ⟨σ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1) σ.property⟩) =
      (compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).d k (k + 1)
        x₂ := by
    simp [x₂, biprod.lift_eq,
      compactlySupportedDeRhamComplex.extendByZero_f_inv_apply _ (k + 1)
        ⟨σ.val, compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1) σ.property⟩, hσU,
            hσV,
      HomologicalComplex.Hom.comm_apply, compactlySupportedDeRhamComplex_d_apply]
    -- The identification of the objects is linear, so it commutes with negation.
    have hneg := map_neg (compactlySupportedDeRhamComplexXIso I (M := V) (k + 1)).inv.hom
      (compactlySupportedForms.mextDerivₗ I V k β)
    simp only [hneg, map_neg, neg_neg]
  rw [mayerVietorisδ, mk_eq_moduleCatHomologyClass, mk_eq_moduleCatHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_apply,
    HomologicalComplex.moduleCatHomologyClass_apply]
  -- The terms and maps of the compactly supported Mayer–Vietoris short complex are, by
  -- definition, those above.
  exact (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).moduleCat_δ_homologyπ
    k (k + 1) rfl _ x₂ (hx₂.trans (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm)
    _ ((congrArg _ (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _)).trans hσ)

end compactlySupportedDeRhamCohomology

end Connecting


section LongExact

/-! ### The compactly supported Mayer–Vietoris long exact sequence as linear maps -/

namespace compactlySupportedDeRhamCohomology

section Maps

variable [IsManifold I 2 M]

variable (I) in
/-- The map `H^k_c(U ⊓ V) → H^k_c(U) × H^k_c(V)` of the compactly supported Mayer–Vietoris
sequence: the extension by zero to `U` and the negative of the extension by zero to `V`. -/
def mayerVietorisToProd (U V : Opens M) (k : ℕ) :
    compactlySupportedDeRhamCohomology I (U ⊓ V : Opens M) k →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I U k × compactlySupportedDeRhamCohomology I V k :=
  (extendByZero (inf_le_left : U ⊓ V ≤ U) k).prod (-extendByZero (inf_le_right : U ⊓ V ≤ V) k)

@[simp]
theorem mayerVietorisToProd_apply (U V : Opens M) (k : ℕ)
    (x : compactlySupportedDeRhamCohomology I (U ⊓ V : Opens M) k) :
    mayerVietorisToProd I U V k x =
      (extendByZero (inf_le_left : U ⊓ V ≤ U) k x, -extendByZero (inf_le_right : U ⊓ V ≤ V) k x) :=
  (rfl)

variable (I) in
/-- The map `H^k_c(U) × H^k_c(V) → H^k_c(U ⊔ V)` of the compactly supported Mayer–Vietoris
sequence: the sum of the extensions by zero to `U ⊔ V`. -/
def mayerVietorisFromProd (U V : Opens M) (k : ℕ) :
    compactlySupportedDeRhamCohomology I U k × compactlySupportedDeRhamCohomology I V k →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I (U ⊔ V : Opens M) k :=
  (extendByZero (le_sup_left : U ≤ U ⊔ V) k).coprod (extendByZero (le_sup_right : V ≤ U ⊔ V) k)

@[simp]
theorem mayerVietorisFromProd_apply (U V : Opens M) (k : ℕ)
    (x : compactlySupportedDeRhamCohomology I U k × compactlySupportedDeRhamCohomology I V k) :
    mayerVietorisFromProd I U V k x =
      extendByZero (le_sup_left : U ≤ U ⊔ V) k x.1 +
        extendByZero (le_sup_right : V ≤ U ⊔ V) k x.2 :=
  (rfl)

/-- The pair of maps induced on cohomology by the first map of the compactly supported
Mayer–Vietoris short complex is `mayerVietorisToProd`. -/
private theorem prod_homologyMap (U V : Opens M) (k : ℕ) :
    (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.extendByZero (I := I)
        (inf_le_left : U ⊓ V ≤ U)) k).hom.prod
      (HomologicalComplex.homologyMap (-compactlySupportedDeRhamComplex.extendByZero (I := I)
        (inf_le_right : U ⊓ V ≤ V)) k).hom =
      mayerVietorisToProd I U V k := by
  simp [mayerVietorisToProd, HomologicalComplex.homologyMap_neg,
    compactlySupportedDeRhamComplex.homologyMap_extendByZero]

/-- The sum of the maps induced on cohomology by the second map of the compactly supported
Mayer–Vietoris short complex is `mayerVietorisFromProd`. -/
private theorem coprod_homologyMap (U V : Opens M) (k : ℕ) :
    (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.extendByZero (I := I)
        (le_sup_left : U ≤ U ⊔ V)) k).hom.coprod
      (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.extendByZero (I := I)
        (le_sup_right : V ≤ U ⊔ V)) k).hom =
      mayerVietorisFromProd I U V k := by
  simp [mayerVietorisFromProd, compactlySupportedDeRhamComplex.homologyMap_extendByZero]

end Maps

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- **Exactness of the compactly supported Mayer–Vietoris sequence at `H^k_c(U) × H^k_c(V)`.** -/
theorem exact_mayerVietorisToProd_fromProd (U V : Opens M) (k : ℕ) :
    Function.Exact (mayerVietorisToProd I U V k) (mayerVietorisFromProd I U V k) := by
  rw [← prod_homologyMap, ← coprod_homologyMap]
  exact (ShortComplex.moduleCat_exact_biprod_lift_desc_iff _).1
    ((compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).biprod_homology_exact₂
      k)

/-- **Exactness of the compactly supported Mayer–Vietoris sequence at `H^k_c(U ⊔ V)`.** -/
theorem exact_mayerVietorisFromProd_δ (U V : Opens M) (k : ℕ) :
    Function.Exact (mayerVietorisFromProd I U V k) (mayerVietorisδ I U V k) := by
  rw [← coprod_homologyMap]
  exact (ShortComplex.moduleCat_exact_biprod_desc_iff _).1
    ((compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).biprod_homology_exact₃
      k (k + 1) rfl)

/-- **Exactness of the compactly supported Mayer–Vietoris sequence at `H^{k+1}_c(U ⊓ V)`.** -/
theorem exact_mayerVietorisδ_toProd (U V : Opens M) (k : ℕ) :
    Function.Exact (mayerVietorisδ I U V k) (mayerVietorisToProd I U V (k + 1)) := by
  rw [← prod_homologyMap]
  exact (ShortComplex.moduleCat_exact_biprod_lift_iff _).1
    ((compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).biprod_homology_exact₁
      k (k + 1) rfl)

/-- In degrees at least the dimension, every compactly supported class on `U ⊔ V` is a sum of
classes extended by zero from `U` and from `V`: the next term `H^{k+1}_c(U ⊓ V)` of the compactly
supported Mayer–Vietoris sequence vanishes. -/
theorem mayerVietorisFromProd_surjective (U V : Opens M) (hk : Module.finrank ℝ E ≤ k) :
    Function.Surjective (mayerVietorisFromProd I U V k) := fun x ↦
  (exact_mayerVietorisFromProd_δ U V k x).mp
    (Subsingleton.elim (h := subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt I
      (U ⊓ V : Opens M) (Nat.lt_succ_of_le hk)) _ _)

end compactlySupportedDeRhamCohomology

end LongExact

end TauCeti
