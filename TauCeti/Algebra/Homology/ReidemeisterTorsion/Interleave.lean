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

private theorem interleave_bracket_eq_one_add_two {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
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
    (hm₃ : ∀ q, m₃ (q + 1) = r₃ (q + 1) + r₁ q)
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (u₃ (q + 1) k : X₃ (q + 1))) (s₃ q) ∘ Fin.cast (hm₃ q))
    {n q : ℤ} (hq : n = 3 * q + 2) :
    HomologicalComplex.torsionBracket (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
      (hL (n + 1)) (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1))
      (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n)
      (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n)
      (interleave.boundaryLift_spec hfg hgδ hδf u₁ u₂ u₃ hs₁ hs₂ hs₃ n) = 1 := by
  have hm_rk : interleave.rank m₁ m₂ m₃ (n + 1) = m₃ (q + 1) :=
    interleave.rank_of_eq_three_mul (by omega)
  have hr₁ : interleave.rank r₁ r₂ r₃ (n + 1) = r₃ (q + 1) :=
    interleave.rank_of_eq_three_mul (by omega)
  have hr₀ : interleave.rank r₁ r₂ r₃ n = r₁ q :=
    interleave.rank_of_eq_three_mul_add_two hq
  have hlen : interleave.rank m₁ m₂ m₃ (n + 1) =
      interleave.rank r₁ r₂ r₃ (n + 1) + interleave.rank r₁ r₂ r₃ n := by
    rw [hm_rk, hm₃, hr₁, hr₀]
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hlen]
  convert Basis.det_self (interleave.basis hfg hgδ hδf b₁ b₂ b₃ (n + 1))
  ext k
  apply (interleave.XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).toLinearEquiv.injective
  simp only [Iso.toLinearEquiv_apply, interleave.XIso₃_hom_basis, hb₃ q, Function.comp_apply]
  obtain ⟨m, rfl⟩ := (finCongr hlen.symm).surjective k
  have hm₀ : Fin.cast hlen (finCongr hlen.symm m) = m := Fin.ext rfl
  rw [hm₀]
  induction m using Fin.addCases with
  | left m =>
    have hm : Fin.cast (hm₃ q) (Fin.cast hm_rk (finCongr hlen.symm (Fin.castAdd _ m))) =
        Fin.castAdd (r₁ q) (Fin.cast hr₁ m) := Fin.ext rfl
    rw [hm]
    simp
  | right m =>
    have hm : Fin.cast (hm₃ q) (Fin.cast hm_rk (finCongr hlen.symm (Fin.natAdd _ m))) =
        Fin.natAdd (r₃ (q + 1)) (Fin.cast hr₀ m) := Fin.ext (by simp [hr₁])
    rw [hm]
    simp

private theorem interleave_bracket_eq_one_add_one {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
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
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (u₁ q k : X₁ q)) (s₁ q) ∘ Fin.cast (hm₁ q))
    {n q : ℤ} (hq : n = 3 * q + 1) :
    HomologicalComplex.torsionBracket (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
      (hL (n + 1)) (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1))
      (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n)
      (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n)
      (interleave.boundaryLift_spec hfg hgδ hδf u₁ u₂ u₃ hs₁ hs₂ hs₃ n) = 1 := by
  have hm_rk : interleave.rank m₁ m₂ m₃ (n + 1) = m₁ q :=
    interleave.rank_of_eq_three_mul_add_two (by omega)
  have hr₁ : interleave.rank r₁ r₂ r₃ (n + 1) = r₁ q :=
    interleave.rank_of_eq_three_mul_add_two (by omega)
  have hr₀ : interleave.rank r₁ r₂ r₃ n = r₂ q :=
    interleave.rank_of_eq_three_mul_add_one hq
  have hlen : interleave.rank m₁ m₂ m₃ (n + 1) =
      interleave.rank r₁ r₂ r₃ (n + 1) + interleave.rank r₁ r₂ r₃ n := by
    rw [hm_rk, hm₁, hr₁, hr₀]
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hlen]
  convert Basis.det_self (interleave.basis hfg hgδ hδf b₁ b₂ b₃ (n + 1))
  ext k
  apply (interleave.XIso₁ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv.injective
  simp only [Iso.toLinearEquiv_apply, interleave.XIso₁_hom_basis, hb₁ q, Function.comp_apply]
  obtain ⟨m, rfl⟩ := (finCongr hlen.symm).surjective k
  have hm₀ : Fin.cast hlen (finCongr hlen.symm m) = m := Fin.ext rfl
  rw [hm₀]
  induction m using Fin.addCases with
  | left m =>
    have hm : Fin.cast (hm₁ q) (Fin.cast hm_rk (finCongr hlen.symm (Fin.castAdd _ m))) =
        Fin.castAdd (r₂ q) (Fin.cast hr₁ m) := Fin.ext rfl
    rw [hm]
    simp
  | right m =>
    have hm : Fin.cast (hm₁ q) (Fin.cast hm_rk (finCongr hlen.symm (Fin.natAdd _ m))) =
        Fin.natAdd (r₁ q) (Fin.cast hr₀ m) := Fin.ext (by simp [hr₁])
    rw [hm]
    simp

private theorem interleave_bracket_eq_one_mul {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
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
    (hm₂ : ∀ q, m₂ q = r₂ q + r₃ q)
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (u₂ q k : X₂ q)) (s₂ q) ∘ Fin.cast (hm₂ q))
    {n q : ℤ} (hq : n = 3 * q) :
    HomologicalComplex.torsionBracket (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
      (hL (n + 1)) (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ (n + 1))
      (interleave.boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n)
      (interleave.boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n)
      (interleave.boundaryLift_spec hfg hgδ hδf u₁ u₂ u₃ hs₁ hs₂ hs₃ n) = 1 := by
  have hm_rk : interleave.rank m₁ m₂ m₃ (n + 1) = m₂ q :=
    interleave.rank_of_eq_three_mul_add_one (by omega)
  have hr₁ : interleave.rank r₁ r₂ r₃ (n + 1) = r₂ q :=
    interleave.rank_of_eq_three_mul_add_one (by omega)
  have hr₀ : interleave.rank r₁ r₂ r₃ n = r₃ q :=
    interleave.rank_of_eq_three_mul hq
  have hlen : interleave.rank m₁ m₂ m₃ (n + 1) =
      interleave.rank r₁ r₂ r₃ (n + 1) + interleave.rank r₁ r₂ r₃ n := by
    rw [hm_rk, hm₂, hr₁, hr₀]
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hlen]
  convert Basis.det_self (interleave.basis hfg hgδ hδf b₁ b₂ b₃ (n + 1))
  ext k
  apply (interleave.XIso₂ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv.injective
  simp only [Iso.toLinearEquiv_apply, interleave.XIso₂_hom_basis, hb₂ q, Function.comp_apply]
  obtain ⟨m, rfl⟩ := (finCongr hlen.symm).surjective k
  have hm₀ : Fin.cast hlen (finCongr hlen.symm m) = m := Fin.ext rfl
  rw [hm₀]
  induction m using Fin.addCases with
  | left m =>
    have hm : Fin.cast (hm₂ q) (Fin.cast hm_rk (finCongr hlen.symm (Fin.castAdd _ m))) =
        Fin.castAdd (r₃ q) (Fin.cast hr₁ m) := Fin.ext rfl
    rw [hm]
    simp
  | right m =>
    have hm : Fin.cast (hm₂ q) (Fin.cast hm_rk (finCongr hlen.symm (Fin.natAdd _ m))) =
        Fin.natAdd (r₂ q) (Fin.cast hr₀ m) := Fin.ext (by simp [hr₁])
    rw [hm]
    simp

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
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q := ⟨n / 3, by omega⟩
  · rw [interleave_bracket_eq_one_add_two hfg hgδ hδf hL b₁ b₂ b₃ u₁ u₂ u₃ hs₁ hs₂ hs₃ hm₃ hb₃
      hq, one_zpow]
  · rw [interleave_bracket_eq_one_add_one hfg hgδ hδf hL b₁ b₂ b₃ u₁ u₂ u₃ hs₁ hs₂ hs₃ hm₁ hb₁
      hq, one_zpow]
  · rw [interleave_bracket_eq_one_mul hfg hgδ hδf hL b₁ b₂ b₃ u₁ u₂ u₃ hs₁ hs₂ hs₃ hm₂ hb₂ hq,
      one_zpow]

end Interleave

end ChainComplex
