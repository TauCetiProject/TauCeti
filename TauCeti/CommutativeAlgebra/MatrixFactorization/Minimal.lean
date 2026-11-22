/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Biproduct
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Minimal matrix factorizations

A finite-projective matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` of `w : S` is *minimal*
(`TauCeti.MatrixFactorization.IsMinimal`) if both differentials land in `Ring.jacobson S • ⊤`. Over
a local ring `(S, 𝔪)`, this means both differentials have image in `𝔪 • ⊤`
(`isMinimal_iff_range_le_maximalIdeal_smul`).

Minimality is invariant under isomorphism (`IsMinimal.of_iso`, `isMinimal_iff_of_iso`) and
parity shift (`isMinimal_parityShift_iff`), holds for the zero factorization (`isMinimal_zero`),
and splits across direct sums (`isMinimal_biprod_iff`). Results relating minimality to reduction
modulo `w` and projective retracts of the cokernel live in
`TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Minimal`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits IsLocalRing

variable {S : Type u} [CommRing S] {w : S}

/-- A matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` over `S` is *minimal* if both
differentials have image in `Ring.jacobson S • ⊤`. -/
def IsMinimal (X : MatrixFactorization S w) : Prop :=
  LinearMap.range X.obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤ ∧
    LinearMap.range X.obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤

/-- Unfolds `TauCeti.MatrixFactorization.IsMinimal`. -/
theorem isMinimal_iff (X : MatrixFactorization S w) :
    X.IsMinimal ↔ LinearMap.range X.obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤ ∧
      LinearMap.range X.obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤ := Iff.rfl

/-- Over a local ring, minimality means both differentials map into `maximalIdeal S • ⊤`. -/
theorem isMinimal_iff_range_le_maximalIdeal_smul [IsLocalRing S] (X : MatrixFactorization S w) :
    X.IsMinimal ↔ LinearMap.range X.obj.d₀.hom.hom ≤ maximalIdeal S • ⊤ ∧
      LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤ := by
  rw [isMinimal_iff, ringJacobson_eq_maximalIdeal]

/-- Minimality is preserved along isomorphisms of matrix factorizations. -/
theorem IsMinimal.of_iso {X Y : MatrixFactorization S w} (hX : X.IsMinimal) (e : X ≅ Y) :
    Y.IsMinimal := by
  have hf₀ : e.inv.hom.f₀.hom ≫ e.hom.hom.f₀.hom = 𝟙 Y.obj.X₀.obj :=
    congrArg (fun k : Y ⟶ Y ↦ k.hom.f₀.hom) e.inv_hom_id
  have hf₁ : e.inv.hom.f₁.hom ≫ e.hom.hom.f₁.hom = 𝟙 Y.obj.X₁.obj :=
    congrArg (fun k : Y ⟶ Y ↦ k.hom.f₁.hom) e.inv_hom_id
  have comm₀ : e.inv.hom.f₀.hom ≫ X.obj.d₀.hom ≫ e.hom.hom.f₁.hom = Y.obj.d₀.hom := by
    simpa [CategoryTheory.Category.assoc, hf₁] using
      congrArg (fun m ↦ m.hom ≫ e.hom.hom.f₁.hom) e.inv.hom.comm₀
  have comm₁ : e.inv.hom.f₁.hom ≫ X.obj.d₁.hom ≫ e.hom.hom.f₀.hom = Y.obj.d₁.hom := by
    simpa [CategoryTheory.Category.assoc, hf₀] using
      congrArg (fun m ↦ m.hom ≫ e.hom.hom.f₀.hom) e.inv.hom.comm₁
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩; rw [← comm₀]
    exact Submodule.smul_top_le_comap_smul_top _ e.hom.hom.f₁.hom.hom (hX.1 ⟨_, rfl⟩)
  · rintro _ ⟨y, rfl⟩; rw [← comm₁]
    exact Submodule.smul_top_le_comap_smul_top _ e.hom.hom.f₀.hom.hom (hX.2 ⟨_, rfl⟩)

/-- Isomorphic matrix factorizations are simultaneously minimal. -/
theorem isMinimal_iff_of_iso {X Y : MatrixFactorization S w} (e : X ≅ Y) :
    X.IsMinimal ↔ Y.IsMinimal := ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Parity shift preserves and reflects minimality. -/
@[simp]
theorem isMinimal_parityShift_iff (X : MatrixFactorization S w) :
    (parityShift.obj X).IsMinimal ↔ X.IsMinimal := by
  have hd₀ : (-X.obj.d₁).hom.hom = -X.obj.d₁.hom.hom := rfl
  have hd₁ : (-X.obj.d₀).hom.hom = -X.obj.d₀.hom.hom := rfl
  rw [isMinimal_iff, isMinimal_iff, parityShift_obj_d₀, parityShift_obj_d₁, hd₀, hd₁,
    LinearMap.range_neg, LinearMap.range_neg, and_comm]

/-- The zero matrix factorization is minimal. -/
@[simp]
theorem isMinimal_zero : (zero (S := S) (w := w)).IsMinimal := by
  simp [isMinimal_iff]

private theorem range_biprod_map_le_smul_iff {P₁ Q₁ P₂ Q₂ : FGModuleCat.{u} S}
    (f₁ : P₁ ⟶ Q₁) (f₂ : P₂ ⟶ Q₂) :
    LinearMap.range (CategoryTheory.Limits.biprod.map f₁ f₂).hom.hom ≤ Ring.jacobson S • ⊤ ↔
      LinearMap.range f₁.hom.hom ≤ Ring.jacobson S • ⊤ ∧
        LinearMap.range f₂.hom.hom ≤ Ring.jacobson S • ⊤ := by
  let inlP : P₁ ⟶ P₁ ⊞ P₂ := CategoryTheory.Limits.biprod.inl
  let inrP : P₂ ⟶ P₁ ⊞ P₂ := CategoryTheory.Limits.biprod.inr
  let fstP : P₁ ⊞ P₂ ⟶ P₁ := CategoryTheory.Limits.biprod.fst
  let sndP : P₁ ⊞ P₂ ⟶ P₂ := CategoryTheory.Limits.biprod.snd
  let inlQ : Q₁ ⟶ Q₁ ⊞ Q₂ := CategoryTheory.Limits.biprod.inl
  let inrQ : Q₂ ⟶ Q₁ ⊞ Q₂ := CategoryTheory.Limits.biprod.inr
  let fstQ : Q₁ ⊞ Q₂ ⟶ Q₁ := CategoryTheory.Limits.biprod.fst
  let sndQ : Q₁ ⊞ Q₂ ⟶ Q₂ := CategoryTheory.Limits.biprod.snd
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro _ ⟨x, rfl⟩
    have hf₁ : f₁ = inlP ≫ CategoryTheory.Limits.biprod.map f₁ f₂ ≫ fstQ := by
      simp [inlP, fstQ]
    rw [hf₁]
    exact Submodule.smul_top_le_comap_smul_top _ fstQ.hom.hom (h ⟨inlP.hom.hom x, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    have hf₂ : f₂ = inrP ≫ CategoryTheory.Limits.biprod.map f₁ f₂ ≫ sndQ := by
      simp [inrP, sndQ]
    rw [hf₂]
    exact Submodule.smul_top_le_comap_smul_top _ sndQ.hom.hom (h ⟨inrP.hom.hom x, rfl⟩)
  · rintro _ ⟨z, rfl⟩
    have hmap : CategoryTheory.Limits.biprod.map f₁ f₂ =
        fstP ≫ f₁ ≫ inlQ + sndP ≫ f₂ ≫ inrQ := by
      calc
        CategoryTheory.Limits.biprod.map f₁ f₂
          = (fstP ≫ inlP + sndP ≫ inrP) ≫ CategoryTheory.Limits.biprod.map f₁ f₂ := by
            rw [CategoryTheory.Limits.biprod.total, Category.id_comp]
        _ = fstP ≫ (inlP ≫ CategoryTheory.Limits.biprod.map f₁ f₂) +
              sndP ≫ (inrP ≫ CategoryTheory.Limits.biprod.map f₁ f₂) := by
            rw [Preadditive.add_comp, Category.assoc, Category.assoc]
        _ = fstP ≫ f₁ ≫ inlQ + sndP ≫ f₂ ≫ inrQ := by
            simp [inlP, inrP, inlQ, inrQ]
    rw [hmap]
    exact Submodule.add_mem _
      (Submodule.smul_top_le_comap_smul_top _ inlQ.hom.hom (h₁ ⟨fstP.hom.hom z, rfl⟩))
      (Submodule.smul_top_le_comap_smul_top _ inrQ.hom.hom (h₂ ⟨sndP.hom.hom z, rfl⟩))

/-- A direct sum of matrix factorizations is minimal if and only if both summands are minimal. -/
@[simp]
theorem isMinimal_biprod_iff (X Y : MatrixFactorization S w) :
    (biprod X Y).IsMinimal ↔ X.IsMinimal ∧ Y.IsMinimal := by
  rw [isMinimal_iff, isMinimal_iff, isMinimal_iff]
  have hd₀ : (LinearMap.range (biprod X Y).obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤) =
      (LinearMap.range (CategoryTheory.Limits.biprod.map X.obj.d₀ Y.obj.d₀).hom.hom ≤
        Ring.jacobson S • ⊤) := rfl
  have hd₁ : (LinearMap.range (biprod X Y).obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤) =
      (LinearMap.range (CategoryTheory.Limits.biprod.map X.obj.d₁ Y.obj.d₁).hom.hom ≤
        Ring.jacobson S • ⊤) := rfl
  rw [hd₀, hd₁, range_biprod_map_le_smul_iff, range_biprod_map_le_smul_iff]
  tauto

end TauCeti.MatrixFactorization
