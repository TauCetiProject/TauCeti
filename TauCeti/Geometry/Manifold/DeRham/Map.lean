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

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

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
    closedForms I' M' k →ₗ[ℝ] closedForms I M k :=
  ((SmoothForm.mpullback f hf).domRestrict (closedForms I' M' k)).codRestrict
    (closedForms I M k) fun φ ↦ by
      rw [mem_closedForms]
      have hclosed := (mem_closedForms (I := I') (M := M') φ.1).mp φ.2
      have hreg : IsSmoothBundleForm (I := I') (F := ℝ)
          (V := Bundle.Trivial M' ℝ) 1 φ.1.1 := by
        rw [isSmoothBundleForm_def]
        exact ((isSmoothBundleForm_def ∞ φ.1.1).mp
          (mem_smoothForms.mp φ.1.2)).of_le (by simp)
      -- The codomain restriction hides the underlying smooth form from the naturality theorem.
      change mextDeriv (SmoothForm.mpullback f hf φ.1).1 = 0
      rw [SmoothForm.coe_mpullback, ← mpullback_mextDeriv (hf.of_le (by simp)) hreg,
        hclosed, TauCeti.mpullback_zero]

/-- The underlying smooth form of a pullback of a closed form is the usual smooth pullback. -/
@[simp]
theorem coe_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : closedForms I' M' k) :
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
    (φ : closedForms I' M' k) (hφ : φ.1 ∈ exactForms I' M' k) :
    (mpullback f hf k φ).1 ∈ exactForms I M k := by
  cases k with
  | zero =>
      rw [exactForms_zero, Submodule.mem_bot] at hφ ⊢
      rw [coe_mpullback, hφ]
      exact LinearMap.map_zero _
  | succ k =>
      rw [exactForms_succ, LinearMap.mem_range] at hφ ⊢
      obtain ⟨ψ, hψ⟩ := hφ
      refine ⟨SmoothForm.mpullback f hf ψ, ?_⟩
      apply Subtype.ext
      have hψ' := congrArg Subtype.val hψ
      simp only [mextDerivₗ_apply] at hψ' ⊢
      have hreg : IsSmoothBundleForm (I := I') (F := ℝ)
          (V := Bundle.Trivial M' ℝ) 1 ψ.1 := by
        rw [isSmoothBundleForm_def]
        exact ((isSmoothBundleForm_def ∞ ψ.1).mp
          (mem_smoothForms.mp ψ.2)).of_le (by simp)
      -- Subtype extensionality leaves smooth-form coercions that naturality cannot match directly.
      change mextDeriv (SmoothForm.mpullback f hf ψ).1 =
        (SmoothForm.mpullback f hf φ.1).1
      rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
        ← mpullback_mextDeriv (hf.of_le (by simp)) hreg, hψ']

end closedForms

namespace deRhamCohomology

/-- The map from closed forms on the target to cohomology on the source obtained by pulling back
and taking the cohomology class. -/
private def pullbackClass (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ) :
    closedForms I' M' k →ₗ[ℝ] deRhamCohomology I M k :=
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
    deRhamCohomology I' M' k →ₗ[ℝ] deRhamCohomology I M k := by
  let q := mk I' (M := M') k
  exact (LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I' M' k)
    (M₂ := deRhamCohomology I' M' k) (M₃ := deRhamCohomology I M k) (f := q)
    (mk_surjective I' (M := M') k))
      (⟨pullbackClass f hf k, ker_mk_le_ker_pullbackClass f hf k⟩ :
        {g : closedForms I' M' k →ₗ[ℝ] deRhamCohomology I M k //
          LinearMap.ker q ≤ LinearMap.ker g})

/-- The induced map sends the class of a closed form to the class of its pullback. -/
@[simp]
theorem map_mk (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : closedForms I' M' k) :
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

end TauCeti
