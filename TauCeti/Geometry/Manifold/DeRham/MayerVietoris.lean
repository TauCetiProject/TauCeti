/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The Mayer–Vietoris sequence of de Rham complexes

For open subsets `U` and `V` of a manifold, restriction of smooth forms gives the Mayer–Vietoris
short complex of de Rham complexes
`0 ⟶ Ω^•(U ⊔ V) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V) ⟶ 0`,
whose first map is `(res, res)` and whose second map is the difference `res - res` of the two
restrictions to `U ⊓ V`.

In each degree, the first map is injective and the sequence is exact in the middle on every
manifold: forms on `U` and `V` that agree on `U ⊓ V` glue to a form on `U ⊔ V`. The second map is
surjective on a Hausdorff σ-compact manifold modelled on a finite-dimensional space: a smooth
function on `U ⊔ V` vanishing near the points outside `V` and equal to one near the points outside
`U` splits a form on `U ⊓ V` into a difference of forms extended by zero. Hence the Mayer–Vietoris
short complex is short exact (`TauCeti.mayerVietorisShortComplex_shortExact`), and Mathlib's
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂` and `homology_exact₃`
give the Mayer–Vietoris long exact sequence of de Rham cohomology.

## Main definitions and results

* `TauCeti.SmoothForm.injective_mayerVietoris`, `TauCeti.SmoothForm.exact_mayerVietoris` and
  `TauCeti.SmoothForm.surjective_mayerVietoris`: exactness of the Mayer–Vietoris sequence of
  smooth forms in a fixed degree.
* `TauCeti.mayerVietorisShortComplex`: the Mayer–Vietoris short complex of de Rham complexes.
* `TauCeti.mayerVietorisShortComplex_shortExact`: it is short exact.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, the Mayer–Vietoris
  theorem.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace SmoothForm

section Exactness

variable [IsManifold I 1 M]

/-- A smooth form on `U ⊔ V` whose restrictions to `U` and to `V` vanish is zero. -/
theorem injective_mayerVietoris (U V : Opens M) :
    Function.Injective
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _)).prod
        (mpullback (I := I) (I' := I)
          (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _))) := by
  refine (injective_iff_map_eq_zero _).mpr fun φ hφ ↦ ?_
  rw [LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero] at hφ
  apply Subtype.ext
  funext x
  rcases Opens.mem_sup.mp x.2 with hx | hx
  · have h := congrFun (congrArg Subtype.val hφ.1) ⟨x, hx⟩
    rw [coe_mpullback, mpullback_inclusion_apply] at h
    exact h
  · have h := congrFun (congrArg Subtype.val hφ.2) ⟨x, hx⟩
    rw [coe_mpullback, mpullback_inclusion_apply] at h
    exact h

/-- Smooth forms on `U` and `V` with the same restriction to `U ⊓ V` are the restrictions of a
smooth form on `U ⊔ V`. -/
theorem exact_mayerVietoris (U V : Opens M) :
    Function.Exact
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _)).prod
        (mpullback (I := I) (I' := I)
          (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)))
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _)).coprod
        (-mpullback (I := I) (I' := I)
          (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _))) := by
  classical
  rintro ⟨α, β⟩
  simp only [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, sub_eq_zero,
    Set.mem_range, LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq]
  refine ⟨fun hαβ ↦ ?_, ?_⟩
  · -- Pointwise, `α` and `β` agree on `U ⊓ V`.
    have hagree : ∀ (y : M) (hU : y ∈ U) (hV : y ∈ V),
        (α.1 ⟨y, hU⟩ : E [⋀^Fin k]→L[ℝ] F) = β.1 ⟨y, hV⟩ := fun y hU hV ↦ by
      have h := congrFun (congrArg Subtype.val hαβ) ⟨y, hU, hV⟩
      rw [coe_mpullback, coe_mpullback, mpullback_inclusion_apply,
        mpullback_inclusion_apply] at h
      exact h
    let γ : RoughForm I (U ⊔ V : Opens M) F k := fun x ↦
      if hx : (x : M) ∈ U then (α.1 ⟨x, hx⟩ : E [⋀^Fin k]→L[ℝ] F)
      else β.1 ⟨x, (Opens.mem_sup.mp x.2).resolve_left hx⟩
    have hγU : TauCeti.mpullback I I (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) γ = α.1 := by
      funext y
      rw [mpullback_inclusion_apply]
      exact dite_eq_left y.2
    have hγV : TauCeti.mpullback I I (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) γ = β.1 := by
      funext y
      rw [mpullback_inclusion_apply]
      by_cases hy : (y : M) ∈ U
      · exact (dite_eq_left hy).trans (hagree y hy y.2)
      · exact dite_eq_right hy
    have hγ : IsSmoothForm I ∞ γ := by
      refine IsSmoothForm.of_mpullback_inclusion (U := fun b : Bool ↦ cond b U V)
        (fun b ↦ by cases b <;> simp) (fun x ↦ ?_) fun b ↦ ?_
      · rcases Opens.mem_sup.mp x.2 with hx | hx
        exacts [⟨true, hx⟩, ⟨false, hx⟩]
      · cases b
        · exact hγV ▸ β.isSmoothForm
        · exact hγU ▸ α.isSmoothForm
    exact ⟨⟨γ, mem_smoothForms.mpr ((isSmoothBundleForm_def ∞ _).mpr
      ((isSmoothForm_def ∞ _).mp hγ))⟩, Subtype.ext ((coe_mpullback _ _ _).trans hγU),
      Subtype.ext ((coe_mpullback _ _ _).trans hγV)⟩
  · rintro ⟨φ, rfl, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← mpullback_comp, ← mpullback_comp]
    -- Both composites of inclusions are, by definition, the inclusion of `U ⊓ V` in `U ⊔ V`.
    rfl

end Exactness

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, every smooth form
on `U ⊓ V` is the difference of the restrictions of smooth forms on `U` and on `V`. -/
theorem surjective_mayerVietoris [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] (U V : Opens M) :
    Function.Surjective
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _)).coprod
        (-mpullback (I := I) (I' := I)
          (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _))) := by
  classical
  intro θ
  -- The open subset `U ⊔ V` is again a Hausdorff σ-compact manifold, hence normal.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace (U ⊔ V : Opens M) := ChartedSpace.locallyCompactSpace H _
  have : NormalSpace (U ⊔ V : Opens M) :=
    have := Manifold.metrizableSpace I (U ⊔ V : Opens M)
    inferInstance
  -- A cut-off function vanishing near the points outside `V` and equal to one near the points
  -- outside `U`.
  have hA : IsClosed {x : (U ⊔ V : Opens M) | (x : M) ∉ V} :=
    (V.isOpen.preimage continuous_subtype_val).isClosed_compl
  have hB : IsClosed {x : (U ⊔ V : Opens M) | (x : M) ∉ U} :=
    (U.isOpen.preimage continuous_subtype_val).isClosed_compl
  have hAB : Disjoint {x : (U ⊔ V : Opens M) | (x : M) ∉ V} {x | (x : M) ∉ U} :=
    disjoint_left.mpr fun x hxV hxU ↦ (Opens.mem_sup.mp x.2).elim hxU hxV
  obtain ⟨ρ, hρ0, hρ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤) hA hB hAB
  have hU : ∀ x : U, (x : M) ∉ U ⊓ V →
      ∀ᶠ y in 𝓝 x, ρ (Opens.inclusion (le_sup_left : U ≤ U ⊔ V) y) = 0 := fun x hx ↦
    (contMDiff_inclusion (I := I) (n := 0) le_sup_left).continuous.continuousAt.eventually
      (hρ0.filter_mono (nhds_le_nhdsSet fun hxV ↦ hx ⟨x.2, hxV⟩))
  have hV : ∀ x : V, (x : M) ∉ U ⊓ V →
      ∀ᶠ y in 𝓝 x, ρ (Opens.inclusion (le_sup_right : V ≤ U ⊔ V) y) - 1 = 0 := fun x hx ↦
    ((contMDiff_inclusion (I := I) (n := 0) le_sup_right).continuous.continuousAt.eventually
      (hρ1.filter_mono (nhds_le_nhdsSet fun hxU ↦ hx ⟨hxU, x.2⟩))).mono
        fun _ hy ↦ sub_eq_zero.mpr hy
  -- `θ = ρ θ - (ρ - 1) θ`, where `ρ θ` extends by zero to `U` and `(ρ - 1) θ` to `V`.
  have haU := θ.isSmoothForm.extendByZero_smul inf_le_left
    (ρ.contMDiff.comp (contMDiff_inclusion le_sup_left)) hU
  have hbV := θ.isSmoothForm.extendByZero_smul inf_le_right
    ((ρ.contMDiff.comp (contMDiff_inclusion le_sup_right)).sub contMDiff_const) hV
  refine ⟨(⟨_, mem_smoothForms.mpr ((isSmoothBundleForm_def ∞ _).mpr
    ((isSmoothForm_def ∞ _).mp haU))⟩, ⟨_, mem_smoothForms.mpr ((isSmoothBundleForm_def ∞ _).mpr
    ((isSmoothForm_def ∞ _).mp hbV))⟩), Subtype.ext ?_⟩
  rw [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, Submodule.coe_sub,
    coe_mpullback, coe_mpullback, RoughForm.mpullback_inclusion_extendByZero,
    RoughForm.mpullback_inclusion_extendByZero]
  funext y
  simp only [Pi.sub_apply, sub_smul, one_smul]
  -- The two cut-off factors are the same function, read through the two inclusions of `U ⊓ V`.
  exact sub_sub_cancel _ _

end SmoothForm

section Complex

variable [IsManifold I 2 M]

variable (I) in
/-- The Mayer–Vietoris short complex `Ω^•(U ⊔ V) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V)` of de Rham
complexes, with first map the pair of restrictions and second map the difference of the
restrictions. -/
@[expose] def mayerVietorisShortComplex (U V : Opens M) :
    ShortComplex (CochainComplex (ModuleCat ℝ) ℕ) :=
  ShortComplex.mk
    (biprod.lift
      (deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _))
      (deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)))
    (biprod.desc
      (deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _))
      (-deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _)))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← deRhamComplex.map_comp,
        ← deRhamComplex.map_comp]
      -- Both composites of inclusions are, by definition, the inclusion of `U ⊓ V` in `U ⊔ V`.
      exact add_neg_cancel _)

/-- The first term of the Mayer–Vietoris short complex is the de Rham complex of `U ⊔ V`. -/
theorem mayerVietorisShortComplex_X₁ (U V : Opens M) :
    (mayerVietorisShortComplex I U V).X₁ = deRhamComplex I (U ⊔ V : Opens M) := (rfl)

/-- The first map of the Mayer–Vietoris short complex is the pair of restrictions to `U` and
to `V`. -/
theorem mayerVietorisShortComplex_f (U V : Opens M) :
    (mayerVietorisShortComplex I U V).f =
      biprod.lift
        (deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _))
        (deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)) := (rfl)

/-- The second map of the Mayer–Vietoris short complex is the difference of the restrictions to
`U ⊓ V` from `U` and from `V`. -/
theorem mayerVietorisShortComplex_g (U V : Opens M) :
    (mayerVietorisShortComplex I U V).g =
      biprod.desc
        (deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _))
        (-deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _)) := (rfl)

/-- The middle term of the Mayer–Vietoris short complex is the biproduct of the de Rham complexes
of `U` and `V`. -/
theorem mayerVietorisShortComplex_X₂ (U V : Opens M) :
    (mayerVietorisShortComplex I U V).X₂ = (deRhamComplex I U ⊞ deRhamComplex I V) := (rfl)

/-- The last term of the Mayer–Vietoris short complex is the de Rham complex of `U ⊓ V`. -/
theorem mayerVietorisShortComplex_X₃ (U V : Opens M) :
    (mayerVietorisShortComplex I U V).X₃ = deRhamComplex I (U ⊓ V : Opens M) := (rfl)

/-- **The Mayer–Vietoris short exact sequence of de Rham complexes.** On a Hausdorff σ-compact
manifold modelled on a finite-dimensional space, the Mayer–Vietoris short complex of two open
subsets is short exact. -/
theorem mayerVietorisShortComplex_shortExact [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U V : Opens M) :
    (mayerVietorisShortComplex I U V).ShortExact := by
  -- In each degree, transport the exactness of the restriction maps of smooth forms along the
  -- identification of `(Ω^•(U) ⊞ Ω^•(V))^k` with the product module `Ωᵏ(U) × Ωᵏ(V)`.
  unfold mayerVietorisShortComplex
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k ↦ ?_
  have hinl : biprod.inl ≫ (ModuleCat.biprodIsoProd (.of ℝ (SmoothForm I U ℝ k))
      (.of ℝ (SmoothForm I V ℝ k))).hom = ModuleCat.ofHom (LinearMap.inl ℝ _ _) := by
    rw [← Iso.eq_comp_inv]
    apply biprod.hom_ext <;> ext x <;> simp
  have hinr : biprod.inr ≫ (ModuleCat.biprodIsoProd (.of ℝ (SmoothForm I U ℝ k))
      (.of ℝ (SmoothForm I V ℝ k))).hom = ModuleCat.ofHom (LinearMap.inr ℝ _ _) := by
    rw [← Iso.eq_comp_inv]
    apply biprod.hom_ext <;> ext x <;> simp
  have hmap {U₁ U₂ : Opens M} (h : U₁ ≤ U₂) :
      (deRhamComplex.map (I := I) (I' := I) (Opens.inclusion h) (contMDiff_inclusion _)).f k =
        (deRhamComplexXIso I k).hom ≫
          ModuleCat.ofHom (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion _)) ≫
            (deRhamComplexXIso I k).inv := by
    rw [← deRhamComplex.map_f_assoc, Iso.hom_inv_id, Category.comp_id]
  let e₂ := HomologicalComplex.biprodXIso (deRhamComplex I U) (deRhamComplex I V) k ≪≫
    biprod.mapIso (deRhamComplexXIso I k) (deRhamComplexXIso I k) ≪≫ ModuleCat.biprodIsoProd _ _
  have hexact := SmoothForm.exact_mayerVietoris (I := I) (F := ℝ) (k := k) U V
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk (deRhamComplexXIso I k).symm e₂.symm
      (deRhamComplexXIso I k).symm ?_ ?_)
    (ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero _ _ hexact.linearMap_comp_eq_zero) hexact
      (SmoothForm.injective_mayerVietoris U V) (SmoothForm.surjective_mayerVietoris U V))
  -- The two squares commute: compare components of the biproducts.
  · rw [← cancel_mono (HomologicalComplex.biprodXIso (deRhamComplex I U) (deRhamComplex I V) k).hom]
    apply biprod.hom_ext
    · ext x
      simp [e₂, hmap, reassoc_of% ModuleCat.biprodIsoProd_inv_comp_fst]
    · ext x
      simp [e₂, hmap, reassoc_of% ModuleCat.biprodIsoProd_inv_comp_snd]
  · refine (cancel_epi (ModuleCat.biprodIsoProd (.of ℝ (SmoothForm I U ℝ k))
      (.of ℝ (SmoothForm I V ℝ k))).hom).mp ?_
    apply biprod.hom_ext'
    · ext x
      simp [e₂, hmap, reassoc_of% hinl]
    · ext x
      simp [e₂, hmap, reassoc_of% hinr]

end Complex

end TauCeti
