/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Fintype.Prod
public import TauCeti.CategoryTheory.Linear.LinearTensor.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Biproducts in the tensor product of linear categories

`TauCeti.LinearTensor.biconeTmul` forms a bicone on pairs of objects from bicones in each
factor. Its projections and inclusions are pure tensors. If both bicones are bilimits over
finite index types, `TauCeti.LinearTensor.isBilimitBiconeTmul` shows that their tensor is a
bilimit as well: the pair of two biproducts is the biproduct of the pairs.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TensorProduct

universe w v₁ v₂ u₁ u₂

namespace TauCeti.LinearTensor

section Biproduct

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]
  {J : Type*} {J' : Type*} {f : J → C} {g : J' → D}

/-- The bicone on the family of pairs `(f j, g j')` with cone point `(b.pt, c.pt)`, built from
bicones `b` on `f` and `c` on `g`: its projections and inclusions are the pure tensors of those of
`b` and `c`. -/
@[simps π ι]
def biconeTmul (b : Bicone f) (c : Bicone g) :
    Bicone (fun p : J × J' ↦ (⟨f p.1, g p.2⟩ : LinearTensor k C D)) where
  pt := ⟨b.pt, c.pt⟩
  π p := tmul (b.π p.1) (c.π p.2)
  ι p := tmul (b.ι p.1) (c.ι p.2)
  ι_π p q := by
    obtain ⟨p₁, p₂⟩ := p
    obtain ⟨q₁, q₂⟩ := q
    by_cases h₁ : p₁ = q₁
    · subst h₁
      by_cases h₂ : p₂ = q₂
      · subst h₂
        simp
      · simp [bicone_ι_π_ne _ h₂, h₂]
    · simp [bicone_ι_π_ne _ h₁, h₁]

@[simp]
theorem biconeTmul_pt (b : Bicone f) (c : Bicone g) :
    (biconeTmul (k := k) b c).pt = ⟨b.pt, c.pt⟩ :=
  rfl

/-- **The pair of two biproducts is the biproduct of the pairs**: if `b` and `c` are bilimit
bicones over finite index types, so is `biconeTmul b c`. -/
def isBilimitBiconeTmul [Fintype J] [Fintype J'] {b : Bicone f} {c : Bicone g} (hb : b.IsBilimit)
    (hc : c.IsBilimit) : (biconeTmul (k := k) b c).IsBilimit :=
  isBilimitOfTotal _ <| by
    simp only [biconeTmul_π, biconeTmul_ι]
    -- Restate the goal with the cone point `(biconeTmul b c).pt` written as `⟨b.pt, c.pt⟩`
    -- (`biconeTmul_pt`).
    change ∑ p : J × J', tmul (k := k) (b.π p.1) (c.π p.2) ≫ tmul (b.ι p.1) (c.ι p.2) =
      𝟙 (⟨b.pt, c.pt⟩ : LinearTensor k C D)
    rw [← tmul_id_id, ← IsBilimit.total hb, ← IsBilimit.total hc, sum_tmul, Fintype.sum_prod_type]
    simp only [tmul_sum, tmul_comp_tmul]

end Biproduct

end TauCeti.LinearTensor
