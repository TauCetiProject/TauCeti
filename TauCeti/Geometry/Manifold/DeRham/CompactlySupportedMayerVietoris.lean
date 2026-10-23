/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
public import TauCeti.Algebra.Homology.ModuleCat.Biprod
import Mathlib.Geometry.Manifold.PartitionOfUnity

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

## Main definitions and results

* `TauCeti.compactlySupportedForms.extendByZero_add_extendByZero_eq_zero_iff`: exactness in the
  middle of the Mayer–Vietoris sequence of compactly supported smooth forms in a fixed degree.
* `TauCeti.compactlySupportedForms.surjective_coprod_extendByZero`: surjectivity of its second
  map. Injectivity of its first map is `TauCeti.compactlySupportedForms.extendByZero_injective`.
* `TauCeti.compactlySupportedMayerVietorisShortComplex`: the compactly supported Mayer–Vietoris
  short complex of compactly supported de Rham complexes.
* `TauCeti.compactlySupportedMayerVietorisShortComplex_shortExact`: it is short exact.

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
  intro φ
  -- The open subset `U ⊔ V` is again a Hausdorff σ-compact manifold.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace (U ⊔ V : Opens M) := ChartedSpace.locallyCompactSpace H _
  -- A smooth partition of unity on `U ⊔ V` subordinate to the cover by `V` and `U`.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun b : Bool ↦ cond b {x : (U ⊔ V : Opens M) | (x : M) ∈ V} {x | (x : M) ∈ U})
    (fun b ↦ by
      cases b
      exacts [U.isOpen.preimage continuous_subtype_val, V.isOpen.preimage continuous_subtype_val])
    fun x _ ↦ by
      rcases Opens.mem_sup.mp x.2 with hx | hx
      exacts [mem_iUnion.mpr ⟨false, hx⟩, mem_iUnion.mpr ⟨true, hx⟩]
  -- The cut-off forms `ρ b φ` are compactly supported, with support in `V` or `U`. The
  -- supports are computed for the model-fibre view of `φ`, for the function support lemmas.
  let ρφ (b : Bool) : compactlySupportedForms I (U ⊔ V : Opens M) k :=
    ⟨⟨fun x ↦ ρ b x • φ.1.1 x, (φ.1.isSmoothForm.fun_smul (ρ b).contMDiff).mem_smoothForms⟩,
      (mem_compactlySupportedForms I).mpr <|
        ((mem_compactlySupportedForms I).mp φ.2).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_smul_subset_right (ρ b)
            (show (U ⊔ V : Opens M) → E [⋀^Fin k]→L[ℝ] ℝ from φ.1.1))⟩
  have hρφ (b : Bool) : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (ρφ b).1.1 ⊆
      cond b {x : (U ⊔ V : Opens M) | (x : M) ∈ V} {x | (x : M) ∈ U} :=
    (tsupport_smul_subset_left (ρ b)
      (show (U ⊔ V : Opens M) → E [⋀^Fin k]→L[ℝ] ℝ from φ.1.1)).trans (hρ b)
  obtain ⟨α, hα⟩ := (mem_range_extendByZero_iff le_sup_left).mpr (hρφ false)
  obtain ⟨β, hβ⟩ := (mem_range_extendByZero_iff le_sup_right).mpr (hρφ true)
  refine ⟨(α, β), ?_⟩
  rw [LinearMap.coprod_apply, hα, hβ]
  refine Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_
  -- `ρ false + ρ true = 1`, so the two cut-off forms sum to `φ`.
  have hsum := ρ.sum_eq_one (mem_univ x)
  rw [finsum_eq_sum_of_fintype, Fintype.sum_bool] at hsum
  -- Sums of compactly supported forms, and the cut-off forms, are computed pointwise.
  simp only [Submodule.coe_add, Pi.add_apply, ρφ]
  rw [← add_smul, add_comm, hsum, one_smul]

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

end Complex

end TauCeti
