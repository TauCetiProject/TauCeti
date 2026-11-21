/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Minimal matrix factorizations

A finite-projective matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` of `w : S` is *minimal*
(`TauCeti.MatrixFactorization.IsMinimal`) if both differentials land in `Ring.jacobson S • ⊤`. Over
a local ring `(S, 𝔪)`, this means both differentials have image in `𝔪 • ⊤`
(`isMinimal_iff_range_le_maximalIdeal_smul`).

Minimality is invariant under isomorphism (`IsMinimal.of_iso`, `isMinimal_iff_of_iso`) and
parity shift (`isMinimal_parityShift_iff`). Results relating minimality to reduction modulo `w`
and projective retracts of the cokernel live in
`TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Minimal`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory IsLocalRing

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

end TauCeti.MatrixFactorization
