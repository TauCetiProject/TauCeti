/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FlatLine

/-!
# The flat line of the trivial character

The flat line `TauCeti.FlatLine ψ` over the torus `ℂ / L` is the orbit space of `ℂ × ℂ` under
`γ +ᵥ (z, v) = (z + γ, ψ γ v)`. For the trivial character `ψ = 1` the lattice acts on the first
factor only, so the flat line is the product line `(ℂ / L) × ℂ`, by `[(z, v)] ↦ ([z], v)`
(`TauCeti.FlatLine.prodDiffeomorph`).

## Main definitions

* `TauCeti.FlatLine.prodDiffeomorph`: the flat line of the trivial character is `(ℂ / L) × ℂ`.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace FlatLine

variable {L : Submodule ℤ ℂ}

/-- The map `([z], v) ↦ [(z, v)]` from the product line to the flat line of the trivial
character. -/
private def ofProd (x : AddAction.orbitRel.Quotient L ℂ × ℂ) : FlatLine (1 : AddChar L Circle) :=
  Quotient.lift (fun z ↦ (Quotient.mk _ (z, x.2) : FlatLine (1 : AddChar L Circle)))
    (fun z z' hzz' ↦ mk_eq_mk_iff.2 ⟨⟨_, L.orbitRelQuotient_mk_eq_mk_iff.1 (Quotient.sound hzz')⟩,
      by simp, by simp⟩) x.1

private theorem ofProd_mk (z w : ℂ) :
    ofProd (L := L) (Quotient.mk _ z, w) = Quotient.mk _ (z, w) :=
  rfl

variable [DiscreteTopology L] {n : WithTop ℕ∞}

/-- **The flat line of the trivial character is the product line** `(ℂ / L) × ℂ`, by
`[(z, v)] ↦ ([z], v)`. -/
def prodDiffeomorph :
    FlatLine (1 : AddChar L Circle) ≃ₘ^n⟮𝓘(ℝ, ℂ × ℂ), 𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)⟯
      AddAction.orbitRel.Quotient L ℂ × ℂ where
  toFun := Quotient.lift (fun p ↦ (Quotient.mk _ p.1, p.2)) fun p q hpq ↦ by
    obtain ⟨γ, h₁, h₂⟩ := mk_eq_mk_iff.1 (Quotient.sound hpq :
      (Quotient.mk _ p : FlatLine (1 : AddChar L Circle)) = Quotient.mk _ q)
    refine Prod.ext (L.orbitRelQuotient_mk_eq_mk_iff.2 (by simp [h₁])) ?_
    simpa using h₂
  invFun := ofProd
  left_inv x := by
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
    rfl
  right_inv x := by
    obtain ⟨y, w⟩ := x
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective y
    rfl
  contMDiff_toFun := by
    rw [← (isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice (1 : AddChar L Circle))
      (I := 𝓘(ℝ, ℂ × ℂ)) (n := n)).contMDiff_comp_iff Quotient.mk_surjective le_rfl]
    exact ((isLocalDiffeomorph_addQuotientMk (G := L) (I := 𝓘(ℝ, ℂ)) (n := n)).contMDiff.comp
      contDiff_fst.contMDiff).prodMk contDiff_snd.contMDiff
  contMDiff_invFun := by
    -- Precomposed with the swap and the orbit projection of the torus, the inverse is the orbit
    -- projection of the flat line, read on `ℂ × ℂ` with the coordinates swapped.
    have hswap : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) n
        ((ofProd ∘ Prod.swap) ∘ Prod.map id (Quotient.mk (AddAction.orbitRel L ℂ))) := by
      have : (ofProd ∘ Prod.swap) ∘ Prod.map id (Quotient.mk (AddAction.orbitRel L ℂ)) =
          Quotient.mk _ ∘ fun q : ℂ × ℂ ↦ (q.2, q.1) :=
        funext fun q ↦ ofProd_mk q.2 q.1
      rw [this]
      exact isLocalDiffeomorph_addQuotientMk.contMDiff.comp
        (contMDiff_snd.prodMk_space contMDiff_fst)
    have h := ((isLocalDiffeomorph_addQuotientMk (G := L) (I := 𝓘(ℝ, ℂ))
      (n := n)).contMDiff_comp_prodMap_iff (I' := 𝓘(ℝ, ℂ)) Quotient.mk_surjective le_rfl).1 hswap
    exact h.comp (contMDiff_snd.prodMk contMDiff_fst)

/-- The identification of the flat line of the trivial character with the product line sends
`[(z, v)]` to `([z], v)`. -/
@[simp]
theorem prodDiffeomorph_mk (p : ℂ × ℂ) :
    prodDiffeomorph (n := n) (Quotient.mk _ p : FlatLine (1 : AddChar L Circle)) =
      (Quotient.mk _ p.1, p.2) :=
  (rfl)

/-- The inverse identification sends `([z], w)` to `[(z, w)]`. -/
@[simp]
theorem prodDiffeomorph_symm_mk (z w : ℂ) :
    (prodDiffeomorph (n := n) (L := L)).symm (Quotient.mk _ z, w) = Quotient.mk _ (z, w) :=
  ofProd_mk z w

end FlatLine

end TauCeti
