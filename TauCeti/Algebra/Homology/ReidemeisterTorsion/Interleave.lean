/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Reidemeister torsion of interleaved chain complexes

Let `X₁`, `X₂`, `X₃` be three `ℤ`-indexed families of finite-dimensional vector spaces over a field
`F` with maps `f q : X₁ q ⟶ X₂ q`, `g q : X₂ q ⟶ X₃ q`, and `δ q : X₃ (q + 1) ⟶ X₁ q` forming an
interleaved chain complex `ChainComplex.interleave X₁ X₂ X₃ f g δ hfg hgδ hδf` with `X₁ q`, `X₂ q`
and `X₃ q` in degrees `3q + 2`, `3q + 1` and `3q`, based by
`ChainComplex.interleave.basis hfg hgδ hδf b₁ b₂ b₃`.

Replacing the bases `(b₁, b₂, b₃)` by `(b₁', b₂', b₃')` multiplies the Reidemeister torsion of the
interleaved complex by the alternating product of the three families of basis-change determinants
(`ChainComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det`). When the interleaved complex is
bounded and acyclic, and each basis `b₁ q`, `b₂ q`, `b₃ (q + 1)` is assembled from a basis of the
image of the incoming differential followed by lifts of a basis of the image of the outgoing
differential, the Reidemeister torsion equals `1`
(`ChainComplex.reidemeisterTorsion_interleave_eq_one_of_exact`).

## Main declarations

* `ChainComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det`: the basis-change formula for
  the torsion of an interleaved chain complex.
* `ChainComplex.reidemeisterTorsion_interleave_eq_one_of_exact`: an acyclic bounded interleaved
  complex based by boundary bases followed by their lifts has torsion `1`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex

section Interleave

variable {F : Type*} [Field F] {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)

/-- Replacing the bases `(b₁, b₂, b₃)` of an interleaved chain complex `ChainComplex.interleave` by
`(b₁', b₂', b₃')` multiplies its Reidemeister torsion by the alternating determinants of the three
families, with `X₁ q`, `X₂ q` and `X₃ q` carrying the signs of degrees `3q + 2`, `3q + 1` and `3q`
respectively. Both sides vanish when the interleaved complex is unbounded or not acyclic. -/
theorem reidemeisterTorsion_interleave_eq_mul_finprod_det {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (interleave.basis hfg hgδ hδf b₁' b₂' b₃') =
      (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
          (interleave.basis hfg hgδ hδf b₁ b₂ b₃) *
        ((∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ))) := by
  by_cases hrank : {n | interleave.rank m₁ m₂ m₃ n ≠ 0}.Finite
  swap
  · simp [HomologicalComplex.reidemeisterTorsion_of_not_finite _ _ hrank]
  rw [HomologicalComplex.reidemeisterTorsion_eq_mul_finprod_det _
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (interleave.basis hfg hgδ hδf b₁' b₂' b₃')]
  congr 1
  -- Regroup the product over `n : ℤ` according to `n % 3` via `Int.divModEquiv 3`.
  set gF : ℤ → F := fun n ↦
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃ n).det
      (interleave.basis hfg hgδ hδf b₁' b₂' b₃' n) ^ (n.negOnePow : ℤ)
  have hgF : Function.HasFiniteMulSupport gF :=
    hrank.subset <| Function.mulSupport_subset_iff'.2 fun n hn ↦ by
      have hn₀ : interleave.rank m₁ m₂ m₃ n = 0 := by simpa using hn
      have : IsEmpty (Fin (interleave.rank m₁ m₂ m₃ n)) := by rw [hn₀]; infer_instance
      simp [gF]
  let e : Fin 3 × ℤ ≃ ℤ := (Equiv.prodComm (Fin 3) ℤ).trans (Int.divModEquiv 3).symm
  rw [← finprod_comp_equiv e, finprod_curry _ (hgF.preimage e.injective.injOn),
    finprod_eq_prod_of_fintype, Fin.prod_univ_three]
  have h₀ : (∏ᶠ q : ℤ, gF (e (0, q))) = ∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      have he₀ : e (0, q) = q * 3 := by simp [e]
      rw [he₀]
      dsimp only [gF]
      rw [interleave.det_basis_of_eq_three_mul hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' (q := q)
        (by omega), (Int.negOnePow_eq_iff _ q).2 ⟨q, by omega⟩]
  have h₁ : (∏ᶠ q : ℤ, gF (e (1, q))) = ∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      have he₁ : e (1, q) = q * 3 + 1 := by simp [e]
      rw [he₁]
      dsimp only [gF]
      rw [interleave.det_basis_of_eq_three_mul_add_one hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' (q := q)
        (by omega), (Int.negOnePow_eq_iff _ (q + 1)).2 ⟨q, by omega⟩]
  have h₂ : (∏ᶠ q : ℤ, gF (e (2, q))) = ∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      have he₂ : e (2, q) = q * 3 + 2 := by simp [e]
      rw [he₂]
      dsimp only [gF]
      rw [interleave.det_basis_of_eq_three_mul_add_two hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' (q := q)
        (by omega), (Int.negOnePow_eq_iff _ q).2 ⟨q + 1, by omega⟩]
  rw [h₀, h₁, h₂]
  ring

/-- In a degree `n + 1` where `ChainComplex.interleave` is exact and identified via `e` with a
module `Y`, if a family `b'` is the casted concatenation of `u'` and `s'`, and the images under `e`
of `interleave.basis`, `interleave.boundaryBasis`, and `interleave.boundaryLift` agree with `b'`,
`u'`, and `s'` up to `Fin.cast`, then the torsion bracket in degree `n + 1` equals `1`. -/
private theorem interleave_bracket_eq_one {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ} {n : ℤ}
    {hL : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).ExactAt (n + 1)}
    {b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q)}
    {b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q)}
    {b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)}
    {u₁ : ∀ q, Basis (Fin (r₁ q)) F (LinearMap.range (δ q).hom)}
    {u₂ : ∀ q, Basis (Fin (r₂ q)) F (LinearMap.range (f q).hom)}
    {u₃ : ∀ q, Basis (Fin (r₃ q)) F (LinearMap.range (g q).hom)}
    {s₁ : ∀ q, Fin (r₂ q) → X₁ q} {s₂ : ∀ q, Fin (r₃ q) → X₂ q}
    {s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)}
    (hspec : ∀ k, ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom
      (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n k) =
      interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n k)
    {Y : ModuleCat F} (e : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (n + 1) ≅ Y)
    {m' p' q' : ℕ} {b' : Fin m' → Y} {u' : Fin p' → Y} {s' : Fin q' → Y}
    (hm : interleave.rank m₁ m₂ m₃ (n + 1) = m')
    (hp : interleave.rank r₁ r₂ r₃ (n + 1) = p')
    (hq : interleave.rank r₁ r₂ r₃ n = q')
    (hm' : m' = p' + q')
    (hb : ∀ k, e.hom (interleave.basis hfg hgδ hδf b₁ b₂ b₃ (n + 1) k) = b' (Fin.cast hm k))
    (hu : ∀ k, e.hom (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1) k) =
      u' (Fin.cast hp k))
    (hs : ∀ k, e.hom (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n k) =
      s' (Fin.cast hq k))
    (hb' : b' = Fin.append u' s' ∘ Fin.cast hm') :
    HomologicalComplex.torsionBracket (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
      hL (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1))
      (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n)
      (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n) hspec = 1 := by
  subst hm hp hq
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hm']
  convert Basis.det_self (interleave.basis hfg hgδ hδf b₁ b₂ b₃ (n + 1))
  apply e.toLinearEquiv.injective.comp_left
  dsimp only
  have hb_fn : ⇑e.toLinearEquiv ∘ ⇑(interleave.basis hfg hgδ hδf b₁ b₂ b₃ (n + 1)) = b' :=
    funext fun k ↦ by simp only [Function.comp_apply, Iso.toLinearEquiv_apply, hb, Fin.cast_refl,
      id_eq]
  have hu_fn :
      ⇑e.toLinearEquiv ∘ (fun k ↦ (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1) k : _)) =
      u' :=
    funext fun k ↦ by simp only [Function.comp_apply, Iso.toLinearEquiv_apply, hu, Fin.cast_refl,
      id_eq]
  have hs_fn :
      ⇑e.toLinearEquiv ∘ interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n = s' :=
    funext fun k ↦ by simp only [Function.comp_apply, Iso.toLinearEquiv_apply, hs, Fin.cast_refl,
      id_eq]
  rw [Fin.comp_append_comp_cast, hu_fn, hs_fn, ← hb', hb_fn]

/-- An acyclic bounded interleaved chain complex whose bases `(b₁, b₂, b₃)` are formed in each
degree from bases `(u₁, u₂, u₃)` of the images of `(δ, f, g)` followed by lifts `(s₁, s₂, s₃)` of
those bases through `(f, g, δ)` has Reidemeister torsion `1`. -/
theorem reidemeisterTorsion_interleave_eq_one_of_exact {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
    (hrank : {n | interleave.rank m₁ m₂ m₃ n ≠ 0}.Finite)
    (hL : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))
    (u₁ : ∀ q, Basis (Fin (r₁ q)) F (LinearMap.range (δ q).hom))
    (u₂ : ∀ q, Basis (Fin (r₂ q)) F (LinearMap.range (f q).hom))
    (u₃ : ∀ q, Basis (Fin (r₃ q)) F (LinearMap.range (g q).hom))
    {s₁ : ∀ q, Fin (r₂ q) → X₁ q} {s₂ : ∀ q, Fin (r₃ q) → X₂ q}
    {s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)}
    (hs₁ : ∀ q k, (f q).hom (s₁ q k) = u₂ q k)
    (hs₂ : ∀ q k, (g q).hom (s₂ q k) = u₃ q k)
    (hs₃ : ∀ q k, (δ q).hom (s₃ q k) = u₁ q k)
    (hm₁ : ∀ q, m₁ q = r₁ q + r₂ q)
    (hm₂ : ∀ q, m₂ q = r₂ q + r₃ q)
    (hm₃ : ∀ q, m₃ (q + 1) = r₃ (q + 1) + r₁ q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (u₁ q k : X₁ q)) (s₁ q) ∘ Fin.cast (hm₁ q))
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (u₂ q k : X₂ q)) (s₂ q) ∘ Fin.cast (hm₂ q))
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (u₃ (q + 1) k : X₃ (q + 1))) (s₃ q) ∘ Fin.cast (hm₃ q)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
      (interleave.basis hfg hgδ hδf b₁ b₂ b₃) = 1 := by
  rw [HomologicalComplex.reidemeisterTorsion_eq_finprod hrank hL
    (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃)
    (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃)
    (interleave.boundaryLift_spec hfg hgδ hδf u₁ u₂ u₃ hs₁ hs₂ hs₃)]
  refine finprod_eq_one_of_forall_eq_one fun n ↦ ?_
  have hspec := interleave.boundaryLift_spec hfg hgδ hδf u₁ u₂ u₃ hs₁ hs₂ hs₃ n
  suffices HomologicalComplex.torsionBracket (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (by simp)
      (by simp) (hL (n + 1)) (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1))
      (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n)
      (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n) hspec = 1 by
    rw [this, one_zpow]
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q := ⟨n / 3, by omega⟩
  · exact interleave_bracket_eq_one hfg hgδ hδf hspec
      (interleave.XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega))
      (interleave.rank_of_eq_three_mul (by omega))
      (interleave.rank_of_eq_three_mul (by omega))
      (interleave.rank_of_eq_three_mul_add_two hq) (hm₃ q)
      (interleave.XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by omega))
      (interleave.XIso₃_hom_boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (by omega))
      (interleave.XIso₃_hom_boundaryLift hfg hgδ hδf s₁ s₂ s₃ (by omega)) (hb₃ q)
  · exact interleave_bracket_eq_one hfg hgδ hδf hspec
      (interleave.XIso₁ hfg hgδ hδf (n + 1) q (by omega))
      (interleave.rank_of_eq_three_mul_add_two (by omega))
      (interleave.rank_of_eq_three_mul_add_two (by omega))
      (interleave.rank_of_eq_three_mul_add_one hq) (hm₁ q)
      (interleave.XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by omega))
      (interleave.XIso₁_hom_boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (by omega))
      (interleave.XIso₁_hom_boundaryLift hfg hgδ hδf s₁ s₂ s₃ (by omega)) (hb₁ q)
  · exact interleave_bracket_eq_one hfg hgδ hδf hspec
      (interleave.XIso₂ hfg hgδ hδf (n + 1) q (by omega))
      (interleave.rank_of_eq_three_mul_add_one (by omega))
      (interleave.rank_of_eq_three_mul_add_one (by omega))
      (interleave.rank_of_eq_three_mul hq) (hm₂ q)
      (interleave.XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by omega))
      (interleave.XIso₂_hom_boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (by omega))
      (interleave.XIso₂_hom_boundaryLift hfg hgδ hδf s₁ s₂ s₃ (by omega)) (hb₂ q)

end Interleave

end ChainComplex
