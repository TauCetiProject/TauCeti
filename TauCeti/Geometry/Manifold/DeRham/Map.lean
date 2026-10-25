/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Functoriality of de Rham cohomology

A smooth map pulls smooth forms back and commutes with the exterior derivative. Consequently it
induces a contravariant map on the de Rham complex and on de Rham cohomology. The induced map sends
the class of a closed form to the class of its pullback, preserves identity maps, and reverses
composition.

Pullback also defines a cochain map of de Rham complexes, `TauCeti.deRhamComplex.map`, which
induces the map on cohomology (`TauCeti.deRhamComplex.homologyMap_map`). It is stated for
manifolds whose model vector spaces share one universe and whose underlying types share another,
so that their de Rham complexes live in the same category of complexes of modules.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

section Pullback

variable {E H E' H' E'' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {I'' : ModelWithCorners ℝ E'' H''}
  {M M' M'' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']
  [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' 2 M'']

namespace closedForms

/-- Pullback of closed smooth forms along a smooth map. -/
def mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    closedForms I' M' ℝ k →ₗ[ℝ] closedForms I M ℝ k :=
  ((SmoothForm.mpullback f hf).domRestrict (closedForms I' M' ℝ k)).codRestrict
    (closedForms I M ℝ k) fun φ ↦ by
      rw [mem_closedForms_iff_mextDerivₗ_eq_zero, LinearMap.domRestrict_apply,
        SmoothForm.mextDerivₗ_mpullback,
        (mem_closedForms_iff_mextDerivₗ_eq_zero I' φ.1).mp φ.2, map_zero]

/-- The underlying smooth form of a pullback of a closed form is the usual smooth pullback. -/
@[simp]
theorem coe_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : closedForms I' M' ℝ k) :
    (mpullback f hf k φ).1 = SmoothForm.mpullback f hf φ.1 := by
  rw [mpullback]
  rfl

/-- Pullback of closed forms by the identity is the identity linear map. -/
@[simp]
theorem mpullback_id (k : ℕ) :
    mpullback (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id k = LinearMap.id := by
  ext φ : 1
  apply Subtype.ext
  simp

/-- Pullback of closed forms reverses composition. -/
theorem mpullback_comp (f : M → M') (g : M' → M'')
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I' I'' ∞ g) (k : ℕ) :
    mpullback (g ∘ f) (hg.comp hf) k = (mpullback f hf k).comp (mpullback g hg k) := by
  ext φ : 1
  apply Subtype.ext
  rw [coe_mpullback, LinearMap.comp_apply, coe_mpullback]
  exact LinearMap.congr_fun (SmoothForm.mpullback_comp f g hf hg) φ.1

/-- Pullback preserves exact forms. -/
theorem mpullback_mem_exactForms (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : closedForms I' M' ℝ k) (hφ : φ.1 ∈ exactForms I' M' ℝ k) :
    (mpullback f hf k φ).1 ∈ exactForms I M ℝ k := by
  cases k with
  | zero =>
      rw [exactForms_zero, Submodule.mem_bot] at hφ ⊢
      rw [coe_mpullback, hφ]
      exact LinearMap.map_zero _
  | succ k =>
      rw [exactForms_succ, SmoothForm.mextDerivLinearMap_real, LinearMap.mem_range] at hφ ⊢
      obtain ⟨ψ, hψ⟩ := hφ
      exact ⟨SmoothForm.mpullback f hf ψ, by
        rw [SmoothForm.mextDerivₗ_mpullback, hψ, coe_mpullback]⟩

end closedForms

namespace deRhamCohomology

/-- The map from closed forms on the target to cohomology on the source obtained by pulling back
and taking the cohomology class. -/
private def pullbackClass (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    closedForms I' M' ℝ k →ₗ[ℝ] deRhamCohomology I M ℝ k :=
  (mk I k).comp (closedForms.mpullback f hf k)

/-- Exact target forms lie in the kernel of pullback followed by the cycle-class map. -/
private theorem ker_mk_le_ker_pullbackClass (f : M → M')
    (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    LinearMap.ker (mk I' (M := M') k) ≤ LinearMap.ker (pullbackClass f hf k) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker, pullbackClass, LinearMap.comp_apply, mk_eq_zero_iff]
  exact closedForms.mpullback_mem_exactForms f hf k φ hφ

/-- The contravariant map on de Rham cohomology induced by a smooth map. -/
def map (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    deRhamCohomology I' M' ℝ k →ₗ[ℝ] deRhamCohomology I M ℝ k := by
  let q := mk (𝕜 := ℝ) I' (M := M') k
  exact (LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I' M' ℝ k)
    (M₂ := deRhamCohomology I' M' ℝ k) (M₃ := deRhamCohomology I M ℝ k) (f := q)
    (mk_surjective I' (M := M') k))
      (⟨pullbackClass f hf k, ker_mk_le_ker_pullbackClass f hf k⟩ :
        {g : closedForms I' M' ℝ k →ₗ[ℝ] deRhamCohomology I M ℝ k //
          LinearMap.ker q ≤ LinearMap.ker g})

/-- The induced map sends the class of a closed form to the class of its pullback. -/
@[simp]
theorem map_mk (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : closedForms I' M' ℝ k) :
    map f hf k (mk I' k φ) = mk I k (closedForms.mpullback f hf k φ) := by
  rw [map, LinearMap.equivOfSurjective_apply]
  rfl

/-- The map on de Rham cohomology induced by the identity is the identity. -/
@[simp]
theorem map_id (k : ℕ) :
    map (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id k = LinearMap.id := by
  apply LinearMap.ext
  intro c
  obtain ⟨φ, rfl⟩ := mk_surjective I (M := M) k c
  rw [map_mk, closedForms.mpullback_id]
  rfl

/-- Pullback on de Rham cohomology reverses composition of smooth maps. -/
theorem map_comp (f : M → M') (g : M' → M'')
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I' I'' ∞ g) (k : ℕ) :
    map (g ∘ f) (hg.comp hf) k = (map f hf k).comp (map g hg k) := by
  apply LinearMap.ext
  intro c
  obtain ⟨φ, rfl⟩ := mk_surjective I'' (M := M'') k c
  rw [LinearMap.comp_apply,
    map_mk (I := I) (I' := I'') (M := M) (M' := M'') (g ∘ f) (hg.comp hf) k φ,
    map_mk (I := I') (I' := I'') (M := M') (M' := M'') g hg k φ,
    map_mk (I := I) (I' := I') (M := M) (M' := M') f hf k,
    closedForms.mpullback_comp (I := I) (I' := I') (I'' := I'')
      (M := M) (M' := M') (M'' := M'') f g hf hg k]
  rfl

end deRhamCohomology

end Pullback

section Complex

/-! The induced cochain maps compare complexes in one universe, so the model spaces share a
universe, as do the manifolds. -/

open CategoryTheory

universe u v

variable {E E' E'' : Type u} {H H' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {I'' : ModelWithCorners ℝ E'' H''}
  {M M' M'' : Type v}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']
  [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' 2 M'']

namespace deRhamComplex

/-- The cochain map of de Rham complexes induced by a smooth map, given in each degree by pullback
of smooth forms. -/
def map (f : M → M') (hf : ContMDiff I I' ∞ f) : deRhamComplex I' M' ℝ ⟶ deRhamComplex I M ℝ :=
  CochainComplex.ofHom (fun k ↦ (deRhamComplexXIso (𝕜 := ℝ) I' k).hom ≫
      ModuleCat.ofHom (SmoothForm.mpullback f hf) ≫ (deRhamComplexXIso (𝕜 := ℝ) I k).inv)
    fun k ↦ by
      have hcomm : ModuleCat.ofHom (SmoothForm.mpullback (F := ℝ) (k := k) f hf) ≫
          ModuleCat.ofHom (mextDerivₗ I (F := ℝ) k) =
            ModuleCat.ofHom (mextDerivₗ I' (F := ℝ) k) ≫
              ModuleCat.ofHom (SmoothForm.mpullback f hf) := by
        ext φ : 2
        exact SmoothForm.mextDerivₗ_mpullback f hf k φ
      rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d I (M := M) k),
        (Iso.eq_comp_inv _).mpr (deRhamComplex_d I' (M := M') k)]
      simp only [SmoothForm.mextDerivLinearMap_real, Category.assoc,
        Iso.inv_hom_id_assoc, reassoc_of% hcomm]

/-- Under the canonical identifications of the objects, the induced cochain map is pullback of
smooth forms. -/
@[reassoc]
theorem map_f (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    (map f hf).f k ≫ (deRhamComplexXIso (𝕜 := ℝ) I k).hom =
      (deRhamComplexXIso (𝕜 := ℝ) I' k).hom ≫ ModuleCat.ofHom (SmoothForm.mpullback f hf) := by
  simp [map]

/-- The induced cochain map, on a form read through the canonical identification of the
degree-`k` object, is pullback of that form. -/
theorem map_f_inv_apply (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : SmoothForm I' M' ℝ k) :
    (map f hf).f k ((deRhamComplexXIso (𝕜 := ℝ) I' k).inv φ) =
      (deRhamComplexXIso (𝕜 := ℝ) I k).inv (SmoothForm.mpullback f hf φ) := by
  rw [(Iso.eq_comp_inv _).mpr (map_f f hf k)]
  simp

/-- The identity map induces the identity cochain map. -/
@[simp]
theorem map_id : map (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id = 𝟙 _ := by
  ext k : 2
  simp [map]

/-- The induced cochain maps reverse composition of smooth maps. -/
theorem map_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) : map (g ∘ f) (hg.comp hf) = map g hg ≫ map f hf := by
  ext k : 2
  simp only [map, HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc,
    SmoothForm.mpullback_comp f g hf hg, ModuleCat.ofHom_comp]

/-- The map induced on cohomology by the cochain map of a smooth map is pullback on de Rham
cohomology. -/
theorem homologyMap_map (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    HomologicalComplex.homologyMap (map f hf) k =
      ModuleCat.ofHom (deRhamCohomology.map f hf k) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I' k c
  rw [ModuleCat.hom_ofHom, deRhamCohomology.map_mk, deRhamCohomology.mk_eq_moduleCatHomologyClass,
    deRhamCohomology.mk_eq_moduleCatHomologyClass]
  refine HomologicalComplex.homologyMap_moduleCatHomologyClass (Z' := closedForms I M ℝ k) _ _ _
    (map f hf) _ _ (closedForms.mpullback f hf k) (fun φ ↦ ?_) φ
  have h := ConcreteCategory.congr_hom ((Iso.eq_comp_inv _).mpr (map_f f hf k))
    ((deRhamComplexXIso (𝕜 := ℝ) I' k).inv φ.1)
  simp only [Category.assoc, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, Iso.inv_hom_id_apply] at h
  exact h.trans (congrArg (deRhamComplexXIso (𝕜 := ℝ) I k).inv.hom
    (closedForms.coe_mpullback f hf k φ).symm)

end deRhamComplex

end Complex

end TauCeti
