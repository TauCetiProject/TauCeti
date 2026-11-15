/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
public import TauCeti.Algebra.Homology.ModuleCat.Biprod

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
* `TauCeti.exists_compactlySupportedClosedForms_extendByZero_eq_mextDerivₗ`: the closed compactly
  supported form on `U ⊓ V` whose extensions to `U` and `V` are `dγ` and `-dδ`.
* `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ` and
  `TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ_mk`: the connecting map of the
  compactly supported Mayer–Vietoris sequence and its description on classes.
* `TauCeti.compactlySupportedDeRhamCohomology.exact_mayerVietoris₁`,
  `TauCeti.compactlySupportedDeRhamCohomology.exact_mayerVietoris₂`,
  `TauCeti.compactlySupportedDeRhamCohomology.exact_mayerVietoris₃`, and
  `TauCeti.compactlySupportedDeRhamCohomology.injective_mayerVietoris_zero`: exactness of the
  compactly supported Mayer–Vietoris long exact sequence in unbundled `Function.Exact` form.

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
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace (U ⊔ V : Opens M) := ChartedSpace.locallyCompactSpace H _
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

/-- Let `γ` and `δ` be compactly supported forms on `U` and `V` whose extensions by zero to
`U ⊔ V` have closed sum. Then `dγ` and `-dδ` are the extensions by zero of a compactly supported
closed form on `U ⊓ V`. This is the form that represents the image of the class of that sum under
the compactly supported Mayer–Vietoris connecting map
(`TauCeti.compactlySupportedDeRhamCohomology.mayerVietorisδ_mk`). -/
theorem exists_compactlySupportedClosedForms_extendByZero_eq_mextDerivₗ {U V : Opens M}
    (γ : compactlySupportedForms I U k) (δ : compactlySupportedForms I V k)
    (hγδ : (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) k γ +
      compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) k δ).1 ∈
        closedForms I (U ⊔ V : Opens M) k) :
    ∃ τ : compactlySupportedClosedForms I (U ⊓ V : Opens M) (k + 1),
      (compactlySupportedClosedForms.extendByZero inf_le_left (k + 1) τ).1 =
          (compactlySupportedForms.mextDerivₗ I U k γ).1 ∧
        (compactlySupportedClosedForms.extendByZero inf_le_right (k + 1) τ).1 =
          -(compactlySupportedForms.mextDerivₗ I V k δ).1 := by
  have hd0 : compactlySupportedForms.mextDerivₗ I (U ⊔ V : Opens M) k
      (compactlySupportedForms.extendByZero le_sup_left k γ +
        compactlySupportedForms.extendByZero le_sup_right k δ) = 0 :=
    Subtype.ext <| by
      rw [compactlySupportedForms.coe_mextDerivₗ, Submodule.coe_zero]
      exact (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp hγδ
  rw [map_add, compactlySupportedForms.mextDerivₗ_extendByZero,
    compactlySupportedForms.mextDerivₗ_extendByZero] at hd0
  obtain ⟨θ, hθU, hθV⟩ := compactlySupportedForms.extendByZero_add_extendByZero_eq_zero_iff.mp hd0
  have hθd : compactlySupportedForms.mextDerivₗ I (U ⊓ V : Opens M) (k + 1) θ = 0 :=
    compactlySupportedForms.extendByZero_injective (inf_le_left : U ⊓ V ≤ U) (k + 2) <| by
      rw [map_zero, ← compactlySupportedForms.mextDerivₗ_extendByZero, hθU]
      exact LinearMap.congr_fun (compactlySupportedForms.mextDerivₗ_comp_mextDerivₗ I k) γ
  refine ⟨⟨θ.1, (mem_compactlySupportedClosedForms I).mpr ⟨θ.2,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr ?_⟩⟩, ?_, ?_⟩
  · simpa only [compactlySupportedForms.coe_mextDerivₗ, Submodule.coe_zero] using
      congrArg Subtype.val hθd
  · exact Subtype.ext (by
      simpa only [compactlySupportedClosedForms.coe_extendByZero,
        compactlySupportedForms.coe_extendByZero] using
        congrArg (fun ξ : compactlySupportedForms I U (k + 1) ↦ ξ.1.1) hθU)
  · exact Subtype.ext (by
      simpa only [compactlySupportedClosedForms.coe_extendByZero,
        compactlySupportedForms.coe_extendByZero, Submodule.coe_neg] using
        congrArg (fun ξ : compactlySupportedForms I V (k + 1) ↦ ξ.1.1) hθV)

private theorem extendByZero_f_inv_apply (I : ModelWithCorners ℝ E H) [IsManifold I 2 M]
    {U W : Opens M} (h : U ≤ W) (k : ℕ) (φ : compactlySupportedForms I U k) :
    (compactlySupportedDeRhamComplex.extendByZero (I := I) h).f k
        ((compactlySupportedDeRhamComplexXIso I k).inv φ) =
      (compactlySupportedDeRhamComplexXIso I k).inv
        (compactlySupportedForms.extendByZero h k φ) := by
  rw [(Iso.eq_comp_inv _).mpr (compactlySupportedDeRhamComplex.extendByZero_f h k)]
  simp

end Complex

section Connecting

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M]

namespace compactlySupportedDeRhamCohomology

variable (I) in
/-- The **compactly supported Mayer–Vietoris connecting map** `H_c^k(U ⊔ V) → H_c^{k+1}(U ⊓ V)` of
compactly supported de Rham cohomology: the connecting map of the long exact cohomology sequence of
the compactly supported Mayer–Vietoris short exact sequence. -/
def mayerVietorisδ (U V : Opens M) (k : ℕ) :
    compactlySupportedDeRhamCohomology I (U ⊔ V : Opens M) k →ₗ[ℝ]
      compactlySupportedDeRhamCohomology I (U ⊓ V : Opens M) (k + 1) :=
  ((compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).δ k (k + 1) rfl).hom

/-- The compactly supported Mayer–Vietoris connecting map is the connecting morphism of the
homology sequence of the compactly supported Mayer–Vietoris short exact sequence. -/
theorem ofHom_mayerVietorisδ (U V : Opens M) (k : ℕ) :
    ModuleCat.ofHom (mayerVietorisδ I U V k) =
      (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).δ k (k + 1) rfl :=
  (rfl)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
private theorem mayerVietoris_biprod_lift_eq_d (U V : Opens M) {k : ℕ}
    (γ : compactlySupportedForms I U k) (δ : compactlySupportedForms I V k)
    (τ : compactlySupportedClosedForms I (U ⊓ V : Opens M) (k + 1))
    (hτU : (compactlySupportedClosedForms.extendByZero inf_le_left (k + 1) τ).1 =
      (compactlySupportedForms.mextDerivₗ I U k γ).1)
    (hτV : (compactlySupportedClosedForms.extendByZero inf_le_right (k + 1) τ).1 =
      -(compactlySupportedForms.mextDerivₗ I V k δ).1) :
    (biprod.lift
        (compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U))
        (-compactlySupportedDeRhamComplex.extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V))).f
        (k + 1)
        ((compactlySupportedDeRhamComplexXIso I (k + 1)).inv
          (Submodule.inclusion
            (compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1)) τ)) =
      (compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).d k (k + 1)
        ((biprod.inl : compactlySupportedDeRhamComplex I U ⟶
            compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f k
            ((compactlySupportedDeRhamComplexXIso I k).inv γ) +
          (biprod.inr : compactlySupportedDeRhamComplex I V ⟶
            compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f k
            ((compactlySupportedDeRhamComplexXIso I k).inv δ)) := by
  have hτUc : compactlySupportedForms.extendByZero (inf_le_left : U ⊓ V ≤ U) (k + 1)
      (Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1)) τ) =
      compactlySupportedForms.mextDerivₗ I U k γ :=
    Subtype.ext <| Subtype.ext <| by
      simpa only [compactlySupportedForms.coe_extendByZero,
        compactlySupportedClosedForms.coe_extendByZero, Submodule.coe_inclusion] using
        congrArg Subtype.val hτU
  have hτVc : compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (k + 1)
      (Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I (k + 1)) τ) =
      -compactlySupportedForms.mextDerivₗ I V k δ :=
    Subtype.ext <| Subtype.ext <| by
      simpa only [compactlySupportedForms.coe_extendByZero,
        compactlySupportedClosedForms.coe_extendByZero, Submodule.coe_inclusion,
        Submodule.coe_neg] using congrArg Subtype.val hτV
  have hneg : -(biprod.inr : compactlySupportedDeRhamComplex I V ⟶
        compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f (k + 1)
        ((compactlySupportedDeRhamComplexXIso I (k + 1)).inv
          (-compactlySupportedForms.mextDerivₗ I V k δ)) =
      (biprod.inr : compactlySupportedDeRhamComplex I V ⟶
        compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f (k + 1)
        ((compactlySupportedDeRhamComplexXIso I (k + 1)).inv
          (compactlySupportedForms.mextDerivₗ I V k δ)) :=
    (congrArg
      (fun z ↦ -(biprod.inr : compactlySupportedDeRhamComplex I V ⟶
        compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f (k + 1) z)
      (map_neg (compactlySupportedDeRhamComplexXIso I (k + 1)).inv.hom _)).trans
      ((congrArg Neg.neg (map_neg ((biprod.inr : compactlySupportedDeRhamComplex I V ⟶
        compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f (k + 1)).hom
        _)).trans (neg_neg _))
  simp [biprod.lift_eq, extendByZero_f_inv_apply I _ (k + 1), hτUc, hτVc,
    HomologicalComplex.Hom.comm_apply, compactlySupportedDeRhamComplex_d_apply, hneg]

/-- **Witness formula for `compactlySupportedDeRhamCohomology.mayerVietorisδ`.** Let `ψ` be a
compactly supported closed form on `U ⊔ V`, written as the sum of the extensions by zero of
compactly supported forms `γ` on `U` and `δ` on `V`. If `τ` is a compactly supported closed form on
`U ⊓ V` whose extensions by zero to `U` and to `V` are `dγ` and `-dδ`, then the connecting map sends
the class of `ψ` to the class of `τ`. -/
theorem mayerVietorisδ_mk (U V : Opens M) {k : ℕ}
    (ψ : compactlySupportedClosedForms I (U ⊔ V : Opens M) k)
    (γ : compactlySupportedForms I U k) (δ : compactlySupportedForms I V k)
    (hγδ : (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) k γ +
      compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) k δ).1 = ψ.1)
    (τ : compactlySupportedClosedForms I (U ⊓ V : Opens M) (k + 1))
    (hτU : (compactlySupportedClosedForms.extendByZero inf_le_left (k + 1) τ).1 =
      (compactlySupportedForms.mextDerivₗ I U k γ).1)
    (hτV : (compactlySupportedClosedForms.extendByZero inf_le_right (k + 1) τ).1 =
      -(compactlySupportedForms.mextDerivₗ I V k δ).1) :
    mayerVietorisδ I U V k (mk I k ψ) = mk I (k + 1) τ := by
  let x₂ : (compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).X k :=
    (biprod.inl : compactlySupportedDeRhamComplex I U ⟶
        compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f k
        ((compactlySupportedDeRhamComplexXIso I k).inv γ) +
      (biprod.inr : compactlySupportedDeRhamComplex I V ⟶
        compactlySupportedDeRhamComplex I U ⊞ compactlySupportedDeRhamComplex I V).f k
        ((compactlySupportedDeRhamComplexXIso I k).inv δ)
  have hψc : compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) k γ +
      compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) k δ =
      Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I k) ψ :=
    Subtype.ext hγδ
  have hx₂ : (biprod.desc
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V))
      (compactlySupportedDeRhamComplex.extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V))).f k x₂ =
      (compactlySupportedDeRhamComplexXIso I k).inv
        (Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I k) ψ) := by
    simp only [x₂, ← hψc, map_add, ← extendByZero_f_inv_apply I le_sup_left k γ,
      ← extendByZero_f_inv_apply I le_sup_right k δ, ← ModuleCat.comp_apply,
      ← HomologicalComplex.comp_f, biprod.inl_desc, biprod.inr_desc]
  have hτ := mayerVietoris_biprod_lift_eq_d U V γ δ τ hτU hτV
  rw [mayerVietorisδ, mk_eq_moduleCatHomologyClass, mk_eq_moduleCatHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_apply,
    HomologicalComplex.moduleCatHomologyClass_apply]
  refine (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V).moduleCat_δ_homologyπ
    k (k + 1) rfl _ x₂ (hx₂.trans (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm) _
    ((congrArg _ (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _)).trans hτ)

/-- Exactness of the compactly supported Mayer–Vietoris sequence at `H_c^{k+1}(U ⊓ V)`. -/
theorem exact_mayerVietoris₁ (U V : Opens M) (k : ℕ) :
    Function.Exact (mayerVietorisδ I U V k)
      ((extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U) (k + 1)).prod
        (-extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V) (k + 1))) := by
  have h := HomologicalComplex.moduleCat_biprod_homology_exact₁
    (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V) k (k + 1) rfl
  rwa [compactlySupportedDeRhamComplex.homologyMap_extendByZero,
    HomologicalComplex.homologyMap_neg,
    compactlySupportedDeRhamComplex.homologyMap_extendByZero, ModuleCat.hom_neg,
    ModuleCat.hom_ofHom, ModuleCat.hom_ofHom] at h

/-- Exactness of the compactly supported Mayer–Vietoris sequence at `H_c^k(U) × H_c^k(V)`. -/
theorem exact_mayerVietoris₂ (U V : Opens M) (k : ℕ) :
    Function.Exact
      ((extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U) k).prod
        (-extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V) k))
      ((extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V) k).coprod
        (extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k)) := by
  simpa only [compactlySupportedDeRhamComplex.homologyMap_extendByZero,
    HomologicalComplex.homologyMap_neg, ModuleCat.hom_neg, ModuleCat.hom_ofHom] using
    HomologicalComplex.moduleCat_biprod_homology_exact₂
      (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V) k

/-- Exactness of the compactly supported Mayer–Vietoris sequence at `H_c^k(U ⊔ V)`. -/
theorem exact_mayerVietoris₃ (U V : Opens M) (k : ℕ) :
    Function.Exact
      ((extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V) k).coprod
        (extendByZero (I := I) (le_sup_right : V ≤ U ⊔ V) k))
      (mayerVietorisδ I U V k) := by
  have h := HomologicalComplex.moduleCat_biprod_homology_exact₃
    (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V) k (k + 1) rfl
  rwa [compactlySupportedDeRhamComplex.homologyMap_extendByZero,
    compactlySupportedDeRhamComplex.homologyMap_extendByZero, ModuleCat.hom_ofHom,
    ModuleCat.hom_ofHom] at h

/-- Injectivity of `H_c⁰(U ⊓ V) → H_c⁰(U) × H_c⁰(V)` in the compactly supported Mayer–Vietoris
sequence. -/
theorem injective_mayerVietoris_zero (U V : Opens M) :
    Function.Injective
      ((extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U) 0).prod
        (-extendByZero (I := I) (inf_le_right : U ⊓ V ≤ V) 0)) := by
  simpa only [compactlySupportedDeRhamComplex.homologyMap_extendByZero,
    HomologicalComplex.homologyMap_neg, ModuleCat.hom_neg, ModuleCat.hom_ofHom] using
    HomologicalComplex.moduleCat_biprod_homology_injective_of_not_rel
      (compactlySupportedMayerVietorisShortComplex_shortExact (I := I) U V) 0
      fun i (h : i + 1 = 0) ↦ Nat.succ_ne_zero i h

end compactlySupportedDeRhamCohomology

end Connecting

end TauCeti
