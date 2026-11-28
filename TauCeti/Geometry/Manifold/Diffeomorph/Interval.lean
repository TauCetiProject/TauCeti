/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.OpenSubset

/-!
# Diffeomorphisms of product strips

An increasing real diffeomorphism taking one pair of endpoints to another restricts to a
product-strip diffeomorphism. Its forward and inverse maps keep the manifold coordinate and
apply the real coordinate change in the interval direction. `TauCeti.prodIooOpens` records the
open strip, and `Diffeomorph.prodIoo` restricts the coordinate change to it.

The interval coordinate changes used for sphere collars in
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture) and
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) are
expressed here using native diffeomorphism restriction.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

open Set TopologicalSpace

/-- The product of a space with an open real interval, as an open subset of the product. -/
def prodIooOpens (M : Type*) [TopologicalSpace M] (a b : ℝ) : Opens (M × ℝ) :=
  ⟨univ ×ˢ Ioo a b, isOpen_univ.prod isOpen_Ioo⟩

/-- Membership in a product strip depends only on the real coordinate. -/
@[simp]
theorem mem_prodIooOpens {M : Type*} [TopologicalSpace M] {a b : ℝ} {p : M × ℝ} :
    p ∈ prodIooOpens M a b ↔ a < p.2 ∧ p.2 < b := by
  simp [prodIooOpens]

end TauCeti

namespace Diffeomorph

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- Restrict an increasing real diffeomorphism to the product strips determined by two
corresponding pairs of endpoints. -/
noncomputable def prodIoo (Ψ : ℝ ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (hmono : StrictMono Ψ)
    {a b c d : ℝ} (ha : Ψ a = c) (hb : Ψ b = d) :
    TauCeti.prodIooOpens M a b ≃ₘ^n⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯
      TauCeti.prodIooOpens M c d :=
  ((Diffeomorph.refl I M n).prodCongr Ψ).subtype fun p ↦ by
    simp only [TauCeti.mem_prodIooOpens, Diffeomorph.coe_prodCongr, Prod.map_snd]
    rw [← ha, ← hb, hmono.lt_iff_lt, hmono.lt_iff_lt]

/-- The product-strip restriction keeps the first coordinate and applies the real
coordinate change to the second. -/
@[simp]
theorem prodIoo_apply_coe (Ψ : ℝ ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (hmono : StrictMono Ψ)
    {a b c d : ℝ} (ha : Ψ a = c) (hb : Ψ b = d)
    (p : TauCeti.prodIooOpens M a b) :
    (Ψ.prodIoo (I := I) hmono ha hb p : M × ℝ) = (p.val.1, Ψ p.val.2) := by
  simp only [prodIoo, Diffeomorph.subtype_apply_coe, Diffeomorph.coe_prodCongr,
    Diffeomorph.coe_refl, Prod.map_apply', id_eq]

/-- The inverse product-strip restriction keeps the first coordinate and applies the inverse
real coordinate change to the second. -/
@[simp]
theorem prodIoo_symm_apply_coe (Ψ : ℝ ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (hmono : StrictMono Ψ)
    {a b c d : ℝ} (ha : Ψ a = c) (hb : Ψ b = d)
    (p : TauCeti.prodIooOpens M c d) :
    ((Ψ.prodIoo (I := I) hmono ha hb).symm p : M × ℝ) = (p.val.1, Ψ.symm p.val.2) := by
  simp only [prodIoo, Diffeomorph.subtype_symm_apply_coe, Diffeomorph.prodCongr_symm,
    Diffeomorph.coe_prodCongr, Diffeomorph.symm_refl, Diffeomorph.coe_refl,
    Prod.map_apply', id_eq]

end Diffeomorph
