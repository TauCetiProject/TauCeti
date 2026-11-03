/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Tactic.Ring

/-!
# Translation of cochain indices and the signed shift

Restriction along `i ↦ i + k` translates the terms of a cochain complex without changing its
differential. The native shift by `k` also multiplies the differential by `(-1)^k`.
`CochainComplex.restrictionAddIsoShift` compares these functors by multiplication by
`(-1)^(i * k)` in degree `i`. This comparison allows state-indexed complexes with unchanged
edge signs to use native cochain shifts.
-/

public section

open CategoryTheory HomologicalComplex

namespace CochainComplex

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] (k : ℤ)

/-- Translating cochain indices without changing the differential agrees with the native
signed shift, through the degreewise sign `(-1)^(i * k)`. -/
noncomputable def restrictionAddIsoShift :
    (ComplexShape.embeddingUp'Add (1 : ℤ) k).restrictionFunctor C ≅
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) k :=
  NatIso.ofComponents
    (fun K ↦ Hom.isoOfComponents (fun i ↦ (i * k).negOnePow • Iso.refl (K.X (i + k)))
      (fun i j hij ↦ by
        obtain rfl : j = i + 1 := hij.symm
        -- Mathlib's restriction uses `up' 1` whereas the native shift uses `up ℤ`.
        -- Their definitional shape equality prevents simp from rewriting this mixed goal;
        -- expose the component identities and the formulas of `restriction_d` and
        -- `shiftFunctor_obj_d'` before applying preadditivity.
        change ((i * k).negOnePow • 𝟙 (K.X (i + k))) ≫
              (k.negOnePow • K.d (i + k) (i + 1 + k)) =
            K.d (i + k) (i + 1 + k) ≫
              (((i + 1) * k).negOnePow • 𝟙 (K.X (i + 1 + k)))
        simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
          Category.id_comp, Category.comp_id, smul_smul,
          ← Units.val_mul, ← Int.negOnePow_add]
        have hsign : k + i * k = (i + 1) * k := by ring
        rw [hsign]))
    (fun {K L} f ↦ by
      ext i
      -- As above, the mixed shape goal needs its component identities exposed before
      -- simp can use preadditivity. Both functors preserve the component `f.f (i + k)`.
      change f.f (i + k) ≫ ((i * k).negOnePow • 𝟙 (L.X (i + k))) =
          ((i * k).negOnePow • 𝟙 (K.X (i + k))) ≫ f.f (i + k)
      simp [Units.smul_def])

/-- The forward comparison multiplies degree `i` by `(-1)^(i * k)`. -/
@[simp]
theorem restrictionAddIsoShift_hom_app_f (K : CochainComplex C ℤ) (i : ℤ) :
    ((restrictionAddIsoShift C k).hom.app K).f i =
      (i * k).negOnePow • 𝟙 (K.X (i + k)) := (rfl)

/-- The inverse comparison has the same degreewise sign. -/
@[simp]
theorem restrictionAddIsoShift_inv_app_f (K : CochainComplex C ℤ) (i : ℤ) :
    ((restrictionAddIsoShift C k).inv.app K).f i =
      (i * k).negOnePow • 𝟙 (K.X (i + k)) := by
  rw [← Int.units_inv_eq_self (i * k).negOnePow]
  rfl

end CochainComplex
