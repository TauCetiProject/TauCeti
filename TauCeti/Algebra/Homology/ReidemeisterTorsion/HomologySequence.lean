/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ModuleCat.ShortExact
import TauCeti.Algebra.Homology.ShortComplex.Splitting
import TauCeti.LinearAlgebra.Alternating.Append
import TauCeti.LinearAlgebra.Exact

/-!
# Multiplicativity of Reidemeister torsion with homology bases

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`, with compatible chain bases `(c₁, c₃, c₂)` and chosen homology
bases `(h₁, h₂, h₃)`. Its long exact homology sequence is the acyclic chain complex
`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and
`Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`, based by
`ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃`.

This file proves Milnor's multiplicativity formula
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`):

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H, (h₁, h₂, h₃))`,

where `H` is the based long exact homology sequence and `ε` is the Koszul sign recording the block
exchanges between the boundaries of `S.X₃` and `S.X₁` and the images of the induced maps on
homology: in degree `j + 1`, the exponent of `-1` is
`dim B₃,ⱼ₊₁ · dim im Hⱼ₊₁(S.f) + (dim B₃,ⱼ₊₁ + dim im Hⱼ₊₁(S.g)) · dim B₁,ⱼ`.

The proof chooses bases of the images of the maps in `H` and lifts them simultaneously on homology
and on chains via `CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_d_eq_of_δ_eq`. For the
resulting adapted homology bases `(h₁', h₂', h₃')`, the torsion of `H` is `1`
(`ChainComplex.reidemeisterTorsion_interleave_eq_one_of_exact`), while the boundaries of `S.X₂`
decompose through the two short exact sequences of `TauCeti.Algebra.Homology.ModuleCat.ShortExact`
so that the bracket of `S.X₂` factors into the brackets of `S.X₁` and `S.X₃` up to the six-block
Koszul sign (`AlternatingMap.map_append_append_append_comm`). Passing from `(h₁', h₂', h₃')` back
to `(h₁, h₂, h₃)` by the basis-change formulas on homology and on `ChainComplex.interleave`
(`ChainComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det`) introduces the factor
`τ(H, (h₁, h₂, h₃))`.

When the homology bases `(h₁, h₃, h₂)` are compatible in every degree, the connecting morphisms
vanish, `τ(H) = 1`
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_eq_one`), and
the torsion of `S.X₂` is `ε · τ(S.X₁) · τ(S.X₃)`
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homology`). This
specializes further to short exact sequences with one acyclic outer term
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₃`,
`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₁`) and to
biproducts `C₁ ⊞ C₃` (`HomologicalComplex.reidemeisterTorsionWithHomology_biprod`).

## Main declarations

* `ChainComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det`: the basis-change formula for
  the torsion of an interleaved chain complex.
* `ChainComplex.reidemeisterTorsion_interleave_eq_one_of_exact`: an acyclic bounded interleaved
  complex based by boundary bases followed by their lifts has torsion `1`.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`,
  `reidemeisterTorsion_homologySequenceComplex_eq_mul_finprod_det`, and
  `reidemeisterTorsion_homologySequenceComplex_eq_one`: nonvanishing, basis change, and triviality
  (for compatible homology bases) of the torsion of the based long exact homology sequence.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`: Milnor's
  multiplicativity formula for torsion with homology bases in a short exact sequence.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homology`: the case
  of compatible homology bases.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₃` and
  `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₁`: the
  cases where one outer complex is acyclic.
* `HomologicalComplex.reidemeisterTorsionWithHomology_biprod`: the torsion with homology bases of a
  direct sum `C₁ ⊞ C₃`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Appendix A, Proposition A.2.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace ChainComplex

section Interleave

variable {F : Type*} [Field F] {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)

private theorem det_interleave_basis_of_eq_three_mul_add_two {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) {n q : ℤ} (h : n = 3 * q + 2) :
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃ n).det (interleave.basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₁ q).det (b₁' q) := by
  have hb (c₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q)) (c₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
      (c₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) :
      interleave.basis hfg hgδ hδf c₁ c₂ c₃ n =
        ((c₁ q).reindex (finCongr (interleave.rank_of_eq_three_mul_add_two h).symm)).map
          (interleave.XIso₁ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun k ↦
      (interleave.XIso₁ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb b₁ b₂ b₃, hb b₁' b₂' b₃', Basis.det_map, Basis.det_reindex]
  congr 1
  ext k
  simp

private theorem det_interleave_basis_of_eq_three_mul_add_one {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) {n q : ℤ} (h : n = 3 * q + 1) :
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃ n).det (interleave.basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₂ q).det (b₂' q) := by
  have hb (c₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q)) (c₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
      (c₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) :
      interleave.basis hfg hgδ hδf c₁ c₂ c₃ n =
        ((c₂ q).reindex (finCongr (interleave.rank_of_eq_three_mul_add_one h).symm)).map
          (interleave.XIso₂ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun k ↦
      (interleave.XIso₂ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb b₁ b₂ b₃, hb b₁' b₂' b₃', Basis.det_map, Basis.det_reindex]
  congr 1
  ext k
  simp

private theorem det_interleave_basis_of_eq_three_mul {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) {n q : ℤ} (h : n = 3 * q) :
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃ n).det (interleave.basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₃ q).det (b₃' q) := by
  have hb (c₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q)) (c₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
      (c₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) :
      interleave.basis hfg hgδ hδf c₁ c₂ c₃ n =
        ((c₃ q).reindex (finCongr (interleave.rank_of_eq_three_mul h).symm)).map
          (interleave.XIso₃ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun k ↦
      (interleave.XIso₃ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb b₁ b₂ b₃, hb b₁' b₂' b₃', Basis.det_map, Basis.det_reindex]
  congr 1
  ext k
  simp

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
      rw [det_interleave_basis_of_eq_three_mul hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' (q := q)
        (by omega), (Int.negOnePow_eq_iff _ q).2 ⟨q, by omega⟩]
  have h₁ : (∏ᶠ q : ℤ, gF (e (1, q))) = ∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      have he₁ : e (1, q) = q * 3 + 1 := by simp [e]
      rw [he₁]
      dsimp only [gF]
      rw [det_interleave_basis_of_eq_three_mul_add_one hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' (q := q)
        (by omega), (Int.negOnePow_eq_iff _ (q + 1)).2 ⟨q, by omega⟩]
  have h₂ : (∏ᶠ q : ℤ, gF (e (2, q))) = ∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      have he₂ : e (2, q) = q * 3 + 2 := by simp [e]
      rw [he₂]
      dsimp only [gF]
      rw [det_interleave_basis_of_eq_three_mul_add_two hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' (q := q)
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

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact)

/-- The long exact homology sequence, based by ordered bases of the homology groups of which only
finitely many are nonempty, has nonzero Reidemeister torsion. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (h₁ : {i | m₁ i ≠ 0}.Finite) (h₂ : {i | m₂ i ≠ 0}.Finite) (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  HomologicalComplex.reidemeisterTorsion_ne_zero _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
    hS.acyclic_homologySequenceComplex

/-- Replacing the homology bases `(b₁, b₂, b₃)` in the based long exact homology sequence by
`(b₁', b₂', b₃')` multiplies its Reidemeister torsion by the alternating determinants of the three
families. -/
theorem reidemeisterTorsion_homologySequenceComplex_eq_mul_finprod_det {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ b₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₂ b₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (b₃ b₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    hS.homologySequenceComplex.reidemeisterTorsion
        (ChainComplex.interleave.basis _ _ _ b₁' b₂' b₃') =
      hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) *
        ((∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ))) :=
  ChainComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det
    (f := fun i ↦ HomologicalComplex.homologyMap S.f i)
    (g := fun i ↦ HomologicalComplex.homologyMap S.g i)
    (δ := fun i ↦ hS.δ (i + 1) i rfl) _ _ _ b₁ b₁' b₂ b₂' b₃ b₃'

include hS in
/-- If the homology bases `b₃` and `b₂` satisfy `(homologyMap S.g i) (b₂ i (natAdd _ k)) = b₃ i k`
in every degree, then `Hᵢ(S.g)` is surjective, the connecting morphisms vanish, and `Hᵢ(S.f)` is
injective. -/
private theorem surjective_and_injective_of_compatible_homology {m₁ m₃ : ℤ → ℕ}
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (b₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hb₃ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom
      (b₂ i (Fin.natAdd (m₁ i) k)) = b₃ i k) :
    (∀ i, Function.Surjective (HomologicalComplex.homologyMap S.g i).hom) ∧
      (∀ i, hS.δ (i + 1) i rfl = 0) ∧
      ∀ i, Function.Injective (HomologicalComplex.homologyMap S.f i).hom := by
  have hg (i : ℤ) : Function.Surjective (HomologicalComplex.homologyMap S.g i).hom := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (b₃ i).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨b₂ i (Fin.natAdd (m₁ i) k), hb₃ i k⟩
  have hδ (i : ℤ) : hS.δ (i + 1) i rfl = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := hg (i + 1) x
    simpa using ConcreteCategory.congr_hom (hS.comp_δ (i + 1) i rfl) y
  have hf (i : ℤ) : Function.Injective (HomologicalComplex.homologyMap S.f i).hom := by
    have hex : LinearMap.range (hS.δ (i + 1) i rfl).hom =
        LinearMap.ker (HomologicalComplex.homologyMap S.f i).hom :=
      (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₁ (i + 1) i rfl)
    rw [← LinearMap.ker_eq_bot, ← hex, hδ i, ModuleCat.hom_zero, LinearMap.range_zero]
  exact ⟨hg, hδ, hf⟩

/-- When the homology bases `(b₁, b₃, b₂)` of a bounded short exact sequence of chain complexes are
compatible in every degree, so that `b₂ i` consists of the images under `Hᵢ(S.f)` of `b₁ i`
followed by lifts through `Hᵢ(S.g)` of `b₃ i`, the based long exact homology sequence has
Reidemeister torsion `1`. -/
theorem reidemeisterTorsion_homologySequenceComplex_eq_one {m₁ m₃ : ℤ → ℕ}
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (b₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hb₁ : ∀ i k, b₂ i (Fin.castAdd (m₃ i) k) =
      (HomologicalComplex.homologyMap S.f i).hom (b₁ i k))
    (hb₃ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom
      (b₂ i (Fin.natAdd (m₁ i) k)) = b₃ i k)
    (hm : {i | m₁ i + m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) = 1 := by
  obtain ⟨hg, hδ, hf⟩ := hS.surjective_and_injective_of_compatible_homology b₃ b₂ hb₃
  have hm₁ : {i | m₁ i ≠ 0}.Finite :=
    hm.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hm₃ : {i | m₃ i ≠ 0}.Finite :=
    hm.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hsub (i : ℤ) : Subsingleton (LinearMap.range (hS.δ (i + 1) i rfl).hom) := by
    rw [hδ i, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  let u₁ (i : ℤ) : Basis (Fin 0) F (LinearMap.range (hS.δ (i + 1) i rfl).hom) := Basis.empty _
  let u₂ (i : ℤ) : Basis (Fin (m₁ i)) F
      (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom) :=
    (b₁ i).map (LinearEquiv.ofInjective _ (hf i))
  let u₃ (i : ℤ) : Basis (Fin (m₃ i)) F
      (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom) :=
    (b₃ i).map (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 (hg i))).symm
  refine ChainComplex.reidemeisterTorsion_interleave_eq_one_of_exact
    (f := fun i ↦ HomologicalComplex.homologyMap S.f i)
    (g := fun i ↦ HomologicalComplex.homologyMap S.g i)
    (δ := fun i ↦ hS.δ (i + 1) i rfl) _ _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero hm₁ hm hm₃)
    hS.acyclic_homologySequenceComplex b₁ b₂ b₃ u₁ u₂ u₃
    (s₁ := fun i ↦ b₁ i) (s₂ := fun i k ↦ b₂ i (Fin.natAdd (m₁ i) k)) (s₃ := fun _ ↦ Fin.elim0)
    (fun i k ↦ by simp [u₂]) (fun i k ↦ by simp [u₃, hb₃]) (fun _ k ↦ k.elim0)
    (fun i ↦ (Nat.zero_add (m₁ i)).symm) (fun _ ↦ rfl) (fun i ↦ (Nat.add_zero (m₃ (i + 1))).symm)
    (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_)
  · ext k
    simp [Fin.append_left_nil _ _ rfl]
  · ext k
    induction k using Fin.addCases <;> simp [u₂, hb₁]
  · ext k
    simp [u₃]

end CategoryTheory.ShortComplex.ShortExact

namespace HomologicalComplex

variable {F : Type*} [Field F]

section ShortExact

section BoundaryBasis

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {j : ℤ}
  {p₁ r₁ p₃ : ℕ}

/-- The basis of the boundaries `B₂,ⱼ ⊆ S.X₂.X j` assembled from a basis `b₁` of `B₁,ⱼ`, cycles
`z₁` of `S.X₁` whose classes form a basis `u₁` of `im δⱼ` and whose images in `S.X₂` are the
boundaries of `w`, and lifts `t` to `S.X₂.X (j + 1)` of lifts of a basis `b₃` of `B₃,ⱼ`. -/
private def shortExactBoundaryBasisWithHomology
    (hf : Function.Injective (S.f.f j).hom) (hfg : Function.Exact (S.f.f j).hom (S.g.f j).hom)
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (u₁ : Basis (Fin r₁) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (w : Fin r₁ → S.X₂.X (j + 1)) (z₁ : Fin r₁ → S.X₁.cycles j)
    (hw : ∀ k, (S.X₂.d (j + 1) j).hom (w k) = (S.f.f j).hom ((S.X₁.iCycles j).hom (z₁ k)))
    (hz₁ : ∀ k, (S.X₁.homologyπ j).hom (z₁ k) = u₁ k)
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p₃ → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b₃ k) :
    Basis (Fin ((p₁ + r₁) + p₃)) F (LinearMap.range (S.X₂.d (j + 1) j).hom) := by
  let β₁₂ :
      Basis (Fin (p₁ + r₁)) F ((LinearMap.range (S.X₂.d (j + 1) j).hom).comap (S.f.f j).hom) :=
    (Basis.ofExactLift (Submodule.inclusion_injective _)
      (hS.exact_inclusion_comapRangeHomologyClass (i := j + 1) (j := j) rfl) b₁ u₁
      (fun k ↦ ⟨(S.X₁.iCycles j).hom (z₁ k), w k, hw k⟩) fun k ↦
        Subtype.ext ((hS.coe_comapRangeHomologyClass_iCycles rfl (z₁ k) _).trans (hz₁ k))).reindex
      finSumFinEquiv
  exact (Basis.ofExactLift (S.f.comapBoundaryMap_injective (j + 1) hf)
    (Hom.exact_comapBoundaryMap_boundaryMap (j + 1) hfg) β₁₂ b₃
    (fun k ↦ ⟨(S.X₂.d (j + 1) j).hom (t k), t k, rfl⟩) fun k ↦
      Subtype.ext ((S.g.coe_boundaryMap _ _ _).trans
        ((S.g.comm_apply _ _ _).symm.trans (ht k)))).reindex finSumFinEquiv

private theorem coe_shortExactBoundaryBasisWithHomology_f
    (hf : Function.Injective (S.f.f j).hom) (hfg : Function.Exact (S.f.f j).hom (S.g.f j).hom)
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (u₁ : Basis (Fin r₁) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (w : Fin r₁ → S.X₂.X (j + 1)) (z₁ : Fin r₁ → S.X₁.cycles j)
    (hw : ∀ k, (S.X₂.d (j + 1) j).hom (w k) = (S.f.f j).hom ((S.X₁.iCycles j).hom (z₁ k)))
    (hz₁ : ∀ k, (S.X₁.homologyπ j).hom (z₁ k) = u₁ k)
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p₃ → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b₃ k) :
    (fun k ↦ (shortExactBoundaryBasisWithHomology hS hf hfg b₁ u₁ w z₁ hw hz₁ b₃ t ht k :
        S.X₂.X j)) =
      Fin.append (Fin.append (fun k ↦ (S.f.f j).hom (b₁ k))
        (fun k ↦ (S.f.f j).hom ((S.X₁.iCycles j).hom (z₁ k))))
        (fun k ↦ (S.X₂.d (j + 1) j).hom (t k)) := by
  ext k
  induction k using Fin.addCases with
  | left k => induction k using Fin.addCases <;> simp [shortExactBoundaryBasisWithHomology]
  | right k => simp [shortExactBoundaryBasisWithHomology]

private theorem coe_shortExactBoundaryBasisWithHomology_d
    (hf : Function.Injective (S.f.f j).hom) (hfg : Function.Exact (S.f.f j).hom (S.g.f j).hom)
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (u₁ : Basis (Fin r₁) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (w : Fin r₁ → S.X₂.X (j + 1)) (z₁ : Fin r₁ → S.X₁.cycles j)
    (hw : ∀ k, (S.X₂.d (j + 1) j).hom (w k) = (S.f.f j).hom ((S.X₁.iCycles j).hom (z₁ k)))
    (hz₁ : ∀ k, (S.X₁.homologyπ j).hom (z₁ k) = u₁ k)
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p₃ → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b₃ k) :
    (fun k ↦ (shortExactBoundaryBasisWithHomology hS hf hfg b₁ u₁ w z₁ hw hz₁ b₃ t ht k :
        S.X₂.X j)) =
      Fin.append (Fin.append (fun k ↦ (S.f.f j).hom (b₁ k))
        (fun k ↦ (S.X₂.d (j + 1) j).hom (w k)))
        (fun k ↦ (S.X₂.d (j + 1) j).hom (t k)) := by
  rw [coe_shortExactBoundaryBasisWithHomology_f]
  simp only [hw]

end BoundaryBasis

/-- The bracket of `S.X₂` in degree `j + 1`, computed with `shortExactBoundaryBasisWithHomology`
and homology representatives adapted to the long exact homology sequence, equals the product of the
corresponding brackets of `S.X₁` and `S.X₃` up to the six-block Koszul sign
`(-1) ^ (p₃₁ * r₂₁ + (p₃₁ + r₃₁) * p₁₀)`. -/
private theorem torsionBracketWithHomology_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ : ℤ → ℕ}
    {c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)}
    {c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i)}
    {c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i)}
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hf : ∀ i, Function.Injective (S.f.f i).hom)
    (hfg : ∀ i, Function.Exact (S.f.f i).hom (S.g.f i).hom)
    {j : ℤ} {p₁₁ p₁₀ p₃₁ p₃₀ r₁₁ r₁₀ r₂₁ r₃₁ m₁₁ m₂₁ m₃₁ : ℕ}
    (hm₁₁ : r₁₁ + r₂₁ = m₁₁) (hm₂₁ : r₂₁ + r₃₁ = m₂₁) (hm₃₁ : r₃₁ + r₁₀ = m₃₁)
    (b₁₁ : Basis (Fin p₁₁) F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom))
    (b₁₀ : Basis (Fin p₁₀) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (s₁₀ : Fin p₁₀ → S.X₁.X (j + 1)) (hs₁₀ : ∀ k, (S.X₁.d (j + 1) j).hom (s₁₀ k) = b₁₀ k)
    (b₃₁ : Basis (Fin p₃₁) F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom))
    (t₁ : Fin p₃₁ → S.X₂.X (j + 1 + 1))
    (ht₁ : ∀ k, (S.X₃.d (j + 1 + 1) (j + 1)).hom ((S.g.f (j + 1 + 1)).hom (t₁ k)) = b₃₁ k)
    (b₃₀ : Basis (Fin p₃₀) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t₀ : Fin p₃₀ → S.X₂.X (j + 1))
    (ht₀ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₀ k)) = b₃₀ k)
    (u₁₁ : Basis (Fin r₁₁) F (LinearMap.range (hS.δ (j + 1 + 1) (j + 1) rfl).hom))
    (w₁ : Fin r₁₁ → S.X₂.X (j + 1 + 1)) (z₁₁₁ : Fin r₁₁ → S.X₁.cycles (j + 1))
    (hw₁ : ∀ k, (S.X₂.d (j + 1 + 1) (j + 1)).hom (w₁ k) =
      (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₁₁ k)))
    (hz₁₁₁ : ∀ k, (S.X₁.homologyπ (j + 1)).hom (z₁₁₁ k) = u₁₁ k)
    (u₁₀ : Basis (Fin r₁₀) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (w₀ : Fin r₁₀ → S.X₂.X (j + 1)) (z₁₁₀ : Fin r₁₀ → S.X₁.cycles j)
    (z₃₂₀ : Fin r₁₀ → S.X₃.cycles (j + 1))
    (hw₀ : ∀ k, (S.X₂.d (j + 1) j).hom (w₀ k) = (S.f.f j).hom ((S.X₁.iCycles j).hom (z₁₁₀ k)))
    (hz₁₁₀ : ∀ k, (S.X₁.homologyπ j).hom (z₁₁₀ k) = u₁₀ k)
    (hgz₀ : ∀ k, (S.g.f (j + 1)).hom (w₀ k) = (S.X₃.iCycles (j + 1)).hom (z₃₂₀ k))
    (z₁₂₁ : Fin r₂₁ → S.X₁.cycles (j + 1)) (z₂₂₁ : Fin r₃₁ → S.X₂.cycles (j + 1))
    (h₁' : Basis (Fin m₁₁) F (S.X₁.homology (j + 1)))
    (hy₁' : ∀ k, S.X₁.homologyπ (j + 1)
      ((Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) k) = h₁' k)
    (h₂' : Basis (Fin m₂₁) F (S.X₂.homology (j + 1)))
    (hy₂' : ∀ k, S.X₂.homologyπ (j + 1)
      ((Fin.append (cyclesMap S.f (j + 1) ∘ z₁₂₁) z₂₂₁ ∘ Fin.cast hm₂₁.symm) k) = h₂' k)
    (h₃' : Basis (Fin m₃₁) F (S.X₃.homology (j + 1)))
    (hy₃' : ∀ k, S.X₃.homologyπ (j + 1)
      ((Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) k) = h₃' k)
    (hs₂₀ : ∀ k, (S.X₂.d (j + 1) j).hom
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁₀ k)) w₀) t₀ k) =
        shortExactBoundaryBasisWithHomology hS (hf j) (hfg j) b₁₀ u₁₀ w₀ z₁₁₀ hw₀ hz₁₁₀ b₃₀ t₀
          ht₀ k) :
    torsionBracketWithHomology c₂
        (shortExactBoundaryBasisWithHomology hS (hf (j + 1)) (hfg (j + 1)) b₁₁ u₁₁ w₁ z₁₁₁ hw₁
          hz₁₁₁ b₃₁ t₁ ht₁)
        h₂' (Fin.append (cyclesMap S.f (j + 1) ∘ z₁₂₁) z₂₂₁ ∘ Fin.cast hm₂₁.symm) hy₂'
        (shortExactBoundaryBasisWithHomology hS (hf j) (hfg j) b₁₀ u₁₀ w₀ z₁₁₀ hw₀ hz₁₁₀ b₃₀ t₀
          ht₀)
        (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁₀ k)) w₀) t₀) hs₂₀ =
      (-1 : F) ^ (p₃₁ * r₂₁ + (p₃₁ + r₃₁) * p₁₀) *
        (torsionBracketWithHomology c₁ b₁₁ h₁' (Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) hy₁'
            b₁₀ s₁₀ hs₁₀ *
          torsionBracketWithHomology c₃ b₃₁ h₃'
            (Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) hy₃'
            b₃₀ (fun k ↦ (S.g.f (j + 1)).hom (t₀ k)) ht₀) := by
  -- Express all three brackets as determinants of concatenated families.
  have hn₁ := eq_add_add_of_homology c₁ b₁₁ h₁' (Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) hy₁'
    b₁₀ s₁₀ hs₁₀
  have hn₃ := eq_add_add_of_homology c₃ b₃₁ h₃'
    (Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) hy₃' b₃₀ _ ht₀
  have hN : n₁ (j + 1) + n₃ (j + 1) =
      (p₁₁ + r₁₁) + r₂₁ + p₁₀ + (p₃₁ + r₃₁ + (r₁₀ + p₃₀)) := by omega
  have hlen₂ : n₁ (j + 1) + n₃ (j + 1) =
      ((p₁₁ + r₁₁) + p₃₁) + m₂₁ + ((p₁₀ + r₁₀) + p₃₀) := by omega
  rw [torsionBracketWithHomology_eq_det_append c₂ _ _
      (Fin.append (cyclesMap S.f (j + 1) ∘ z₁₂₁) z₂₂₁ ∘ Fin.cast hm₂₁.symm) hy₂' _ _ hs₂₀ hlen₂,
    coe_shortExactBoundaryBasisWithHomology_f,
    torsionBracketWithHomology_eq_det_append c₁ b₁₁ h₁'
      (Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) hy₁' b₁₀ s₁₀ hs₁₀ hn₁,
    torsionBracketWithHomology_eq_det_append c₃ b₃₁ h₃'
      (Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) hy₃' b₃₀ _ ht₀ hn₃]
  -- Reorder the six blocks of the `S.X₂` family into the `S.X₁` blocks followed by the `S.X₃`
  -- blocks, extracting the Koszul sign via `AlternatingMap.map_append_append_append_comm`.
  have comp_append {A B : ModuleCat F} (φ : A ⟶ B) {m n : ℕ} (u : Fin m → A) (v : Fin n → A) :
      φ.hom ∘ Fin.append u v = Fin.append (φ.hom ∘ u) (φ.hom ∘ v) := by
    ext k
    induction k using Fin.addCases <;> simp
  have hy₂_vec : (fun k ↦ S.X₂.iCycles (j + 1)
      ((Fin.append (cyclesMap S.f (j + 1) ∘ z₁₂₁) z₂₂₁ ∘ Fin.cast hm₂₁.symm) k)) =
      Fin.append (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₂₁ k)))
        (fun k ↦ (S.X₂.iCycles (j + 1)).hom (z₂₂₁ k)) ∘ Fin.cast hm₂₁.symm := by
    ext k
    obtain ⟨l, rfl⟩ := (finCongr hm₂₁).surjective k
    induction l using Fin.addCases <;> simp
  have hsw := ((c₂ (j + 1)).reindex (finCongr hN)).det.map_append_append_append_comm
    (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁₁ k))
      (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₁₁ k))))
    (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₂₁ k)))
    (fun k ↦ (S.f.f (j + 1)).hom (s₁₀ k))
    (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
    (fun k ↦ (S.X₂.iCycles (j + 1)).hom (z₂₂₁ k))
    (Fin.append w₀ t₀)
  rw [Basis.det_reindex, Basis.det_reindex] at hsw
  have harg :
      Fin.append (Fin.append
          (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁₁ k))
            (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₁₁ k))))
            (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k)))
          (fun k ↦ S.X₂.iCycles (j + 1)
            ((Fin.append (cyclesMap S.f (j + 1) ∘ z₁₂₁) z₂₂₁ ∘ Fin.cast hm₂₁.symm) k)))
        (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁₀ k)) w₀) t₀) ∘
        Fin.cast hlen₂ =
      (Fin.append (Fin.append
          (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁₁ k))
            (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₁₁ k))))
            (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k)))
          (Fin.append (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₂₁ k)))
            (fun k ↦ (S.X₂.iCycles (j + 1)).hom (z₂₂₁ k))))
        (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁₀ k)) (Fin.append w₀ t₀)) ∘
        Fin.cast (by omega)) ∘ (finCongr hN : Fin (n₁ (j + 1) + n₃ (j + 1)) → _) := by
    rw [hy₂_vec, Fin.append_cast_right, Fin.append_assoc _ w₀ t₀, Fin.append_cast_left,
      Fin.append_cast_right]
    rfl
  -- Factor the reordered determinant along `Basis.ofExactLift` and identify the `S.X₁` and `S.X₃`
  -- families block by block.
  rw [harg, hsw,
    Basis.eq_reindex_ofExactLift (hf (j + 1)) (hfg (j + 1)) (c₁ (j + 1)) (c₃ (j + 1))
      (c₂ (j + 1)) (hc₁ (j + 1)) (hc₃ (j + 1)), Basis.det_reindex,
    Basis.ofExactLift_det_eq_mul _ _ _ _ _ _
      (Fin.append (Fin.append (fun k ↦ (b₁₁ k : S.X₁.X (j + 1)))
        (fun k ↦ S.X₁.iCycles (j + 1) ((Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) k))) s₁₀ ∘
        Fin.cast hn₁)
      (Fin.append (Fin.append (fun k ↦ (b₃₁ k : S.X₃.X (j + 1)))
        (fun k ↦ S.X₃.iCycles (j + 1)
          ((Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) k)))
        (fun k ↦ (S.g.f (j + 1)).hom (t₀ k)) ∘ Fin.cast hn₃)
      _ ?_ ?_]
  · simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  · intro i
    have hl : finCongr hN (finSumFinEquiv (.inl i)) =
        Fin.castAdd (p₃₁ + r₃₁ + (r₁₀ + p₃₀)) (Fin.cast (by omega) i) := Fin.ext (by simp)
    have hy₁_vec : (fun k ↦ S.X₁.iCycles (j + 1)
        ((Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) k)) =
        Fin.append ((S.X₁.iCycles (j + 1)).hom ∘ z₁₁₁) ((S.X₁.iCycles (j + 1)).hom ∘ z₁₂₁) ∘
          Fin.cast hm₁₁.symm := by
      ext k
      obtain ⟨l, rfl⟩ := (finCongr hm₁₁).surjective k
      induction l using Fin.addCases <;> simp
    have hf_eq :
        Fin.append
          (Fin.append
            (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁₁ k))
              (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₁₁ k))))
            (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (z₁₂₁ k))))
          (fun k ↦ (S.f.f (j + 1)).hom (s₁₀ k)) ∘ Fin.cast (by omega) =
        ((S.f.f (j + 1)).hom ∘
          Fin.append (Fin.append (fun k ↦ (b₁₁ k : S.X₁.X (j + 1)))
            (fun k ↦ S.X₁.iCycles (j + 1) ((Fin.append z₁₁₁ z₁₂₁ ∘ Fin.cast hm₁₁.symm) k))) s₁₀) ∘
          Fin.cast hn₁ := by
      rw [hy₁_vec, Fin.append_cast_right, Fin.append_cast_left, ← Function.comp_assoc,
        comp_append (S.f.f (j + 1)), comp_append (S.f.f (j + 1)), comp_append (S.f.f (j + 1)),
        Fin.append_assoc (fun k ↦ (S.f.f (j + 1)).hom (b₁₁ k)), Fin.append_cast_left]
      rfl
    simpa only [Function.comp_apply, hl, Fin.append_left] using congrFun hf_eq i
  · intro i
    have hr : finCongr hN (finSumFinEquiv (.inr i)) =
        Fin.natAdd ((p₁₁ + r₁₁) + r₂₁ + p₁₀) (Fin.cast (by omega) i) := Fin.ext (by simp; omega)
    have hy₃_vec : (fun k ↦ S.X₃.iCycles (j + 1)
        ((Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) k)) =
        Fin.append (fun k ↦ (S.X₃.iCycles (j + 1)).hom (cyclesMap S.g (j + 1) (z₂₂₁ k)))
          ((S.X₃.iCycles (j + 1)).hom ∘ z₃₂₀) ∘ Fin.cast hm₃₁.symm := by
      ext k
      obtain ⟨l, rfl⟩ := (finCongr hm₃₁).surjective k
      induction l using Fin.addCases <;> simp
    have hg₁ : (S.g.f (j + 1)).hom ∘ (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k)) =
        fun k ↦ (b₃₁ k : S.X₃.X (j + 1)) :=
      funext fun k ↦ (S.g.comm_apply _ _ _).symm.trans (ht₁ k)
    have hg₂ : (S.g.f (j + 1)).hom ∘ (fun k ↦ (S.X₂.iCycles (j + 1)).hom (z₂₂₁ k)) =
        fun k ↦ (S.X₃.iCycles (j + 1)).hom (cyclesMap S.g (j + 1) (z₂₂₁ k)) :=
      funext fun k ↦ (S.X₂.moduleCat_iCycles_cyclesMap_apply (j + 1) S.g (z₂₂₁ k)).symm
    have hg₃ : (S.g.f (j + 1)).hom ∘ w₀ = (S.X₃.iCycles (j + 1)).hom ∘ z₃₂₀ := funext hgz₀
    have hg_eq :
        ((S.g.f (j + 1)).hom ∘
          Fin.append
            (Fin.append (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
              (fun k ↦ (S.X₂.iCycles (j + 1)).hom (z₂₂₁ k)))
            (Fin.append w₀ t₀)) ∘ Fin.cast (by omega) =
        Fin.append (Fin.append (fun k ↦ (b₃₁ k : S.X₃.X (j + 1)))
          (fun k ↦ S.X₃.iCycles (j + 1)
            ((Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂₁) z₃₂₀ ∘ Fin.cast hm₃₁.symm) k)))
          (fun k ↦ (S.g.f (j + 1)).hom (t₀ k)) ∘ Fin.cast hn₃ := by
      rw [hy₃_vec, comp_append (S.g.f (j + 1)), comp_append (S.g.f (j + 1)),
        comp_append (S.g.f (j + 1)), hg₁, hg₂, hg₃, Fin.append_assoc,
        Fin.append_cast_right, Fin.append_cast_left, Fin.append_assoc, Fin.append_assoc,
        Fin.append_cast_right]
      rfl
    simpa only [Function.comp_apply, hr, Fin.append_right] using congrFun hg_eq i

/-- If the middle term of a short exact sequence of based complexes is unbounded, so is one of the
outer terms, and both sides of Milnor's multiplicativity formula vanish. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_not_finite
    {C₁ C₂ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (C₂.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (C₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i))
    (hn : ¬{i | n₁ i + n₃ i ≠ 0}.Finite) (ε τH : F) :
    C₂.reidemeisterTorsionWithHomology c₂ h₂ =
      ε * (C₁.reidemeisterTorsionWithHomology c₁ h₁ *
        C₃.reidemeisterTorsionWithHomology c₃ h₃ * τH) := by
  rw [reidemeisterTorsionWithHomology_of_not_finite C₂ c₂ h₂ hn]
  by_cases hn₁ : {i | n₁ i ≠ 0}.Finite
  · have hn₃ : ¬{i | n₃ i ≠ 0}.Finite := fun hn₃ ↦
      hn ((hn₁.union hn₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega)
    simp [reidemeisterTorsionWithHomology_of_not_finite C₃ c₃ h₃ hn₃]
  · simp [reidemeisterTorsionWithHomology_of_not_finite C₁ c₁ h₁ hn₁]

/-- Multiplying the six-block bracket identity over `j : ℤ` relates `τ(S.X₂, c₂, h₂')` to
`τ(S.X₁, c₁, h₁') · τ(S.X₃, c₃, h₃')` for homology bases `(h₁', h₂', h₃')` represented by
simultaneously lifted cycles. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_adapted_cycles
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    (hm₁_eq : ∀ i, r₁ i + r₂ i = m₁ i)
    (hm₂_eq : ∀ i, r₂ i + r₃ i = m₂ i)
    (hm₃_eq : ∀ j, r₃ (j + 1) + r₁ j = m₃ (j + 1))
    (u₁ : ∀ i, Basis (Fin (r₁ i)) F (LinearMap.range (hS.δ (i + 1) i rfl).hom))
    (w₂ : ∀ i, Fin (r₁ i) → S.X₂.X (i + 1))
    (z₁₁ : ∀ i, Fin (r₁ i) → S.X₁.cycles i)
    (z₁₂ : ∀ i, Fin (r₂ i) → S.X₁.cycles i)
    (z₂₂ : ∀ i, Fin (r₃ i) → S.X₂.cycles i)
    (z₃₂ : ∀ i, Fin (r₁ i) → S.X₃.cycles (i + 1))
    (hw₂ : ∀ i k, (S.X₂.d (i + 1) i).hom (w₂ i k) =
      (S.f.f i).hom ((S.X₁.iCycles i).hom (z₁₁ i k)))
    (hz₁₁ : ∀ i k, (S.X₁.homologyπ i).hom (z₁₁ i k) = u₁ i k)
    (hgz₃₂ : ∀ i k, (S.g.f (i + 1)).hom (w₂ i k) = (S.X₃.iCycles (i + 1)).hom (z₃₂ i k))
    (h₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (hy₁ : ∀ i k, S.X₁.homologyπ i
      ((Fin.append (z₁₁ i) (z₁₂ i) ∘ Fin.cast (hm₁_eq i).symm) k) = h₁' i k)
    (h₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (hy₂ : ∀ i k, S.X₂.homologyπ i
      ((Fin.append (cyclesMap S.f i ∘ z₁₂ i) (z₂₂ i) ∘ Fin.cast (hm₂_eq i).symm) k) = h₂' i k)
    (h₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (hy₃Aux : ∀ j k, S.X₃.homologyπ (j + 1)
      ((Fin.append (cyclesMap S.g (j + 1) ∘ z₂₂ (j + 1)) (z₃₂ j) ∘ Fin.cast (hm₃_eq j).symm) k) =
        h₃' (j + 1) k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂' =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          r₂ (j + 1) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + r₃ (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃') := by
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hS' := (shortExact_iff_degreewise_shortExact S).1 hS
  have hf (i : ℤ) : Function.Injective (S.f.f i).hom := (hS' i).moduleCat_injective_f
  have hfg (i : ℤ) : Function.Exact (S.f.f i).hom (S.g.f i).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS' i).exact
  have hg (i : ℤ) : Function.Surjective (S.g.f i).hom := (hS' i).moduleCat_surjective_g
  -- Assemble boundary bases `β₂` and lifts `s₂` for `S.X₂` from chosen boundary bases and lifts of
  -- `S.X₁` and `S.X₃` together with the connecting-map lifts `(w₂, z₁₁)`.
  let t (j : ℤ) (k : Fin (finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom))) : S.X₂.X (j + 1) :=
    Function.surjInv (hg (j + 1)) (chosenBoundaryLift S.X₃ c₃ (j + 1) j k)
  have ht (j : ℤ) (k) : (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t j k)) =
      chosenBoundaryBasis S.X₃ c₃ (j + 1) j k := by
    rw [Function.surjInv_eq (hg (j + 1)), chosenBoundaryLift_spec]
  let β₂ (j : ℤ) := shortExactBoundaryBasisWithHomology hS (hf j) (hfg j)
    (chosenBoundaryBasis S.X₁ c₁ (j + 1) j) (u₁ j) (w₂ j) (z₁₁ j) (hw₂ j) (hz₁₁ j)
    (chosenBoundaryBasis S.X₃ c₃ (j + 1) j) (t j) (ht j)
  let s₂ (j : ℤ) := Fin.append
    (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (chosenBoundaryLift S.X₁ c₁ (j + 1) j k)) (w₂ j))
    (t j)
  have hs₂ (j : ℤ) (k) : (S.X₂.d (j + 1) j).hom (s₂ j k) = β₂ j k := by
    rw [congrFun (coe_shortExactBoundaryBasisWithHomology_d hS (hf j) (hfg j) _ _ _ _ (hw₂ j)
      (hz₁₁ j) _ _ (ht j)) k]
    induction k using Fin.addCases with
    | left k =>
      induction k using Fin.addCases <;> simp [s₂, Hom.comm_apply, chosenBoundaryLift_spec]
    | right k => simp [s₂]
  let y₃ (i : ℤ) : Fin (m₃ i) → S.X₃.cycles i :=
    Function.surjInv (S.X₃.moduleCat_homologyπ_surjective i) ∘ h₃' i
  have hy₃ (i : ℤ) (k : Fin (m₃ i)) : S.X₃.homologyπ i (y₃ i k) = h₃' i k :=
    Function.surjInv_eq (S.X₃.moduleCat_homologyπ_surjective i) _
  -- Split the alternating product into the Koszul sign and the brackets of `S.X₁` and `S.X₃`.
  have hsupp₁ := hasFiniteMulSupport_torsionBracketWithHomology (c := c₁) (h := h₁') hn₁
    (fun j ↦ chosenBoundaryBasis S.X₁ c₁ (j + 1) j) _ hy₁
    (fun j ↦ chosenBoundaryLift S.X₁ c₁ (j + 1) j)
    (fun j ↦ chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j)
  have hsupp₃ := hasFiniteMulSupport_torsionBracketWithHomology (c := c₃) (h := h₃') hn₃
    (fun j ↦ chosenBoundaryBasis S.X₃ c₃ (j + 1) j) y₃ hy₃
    (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht
  have hε : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * r₂ (j + 1) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + r₃ (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) := by
    have hε₁ : Function.HasFiniteMulSupport fun j : ℤ ↦
        (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * r₂ (j + 1)) :=
      (hasFiniteMulSupport_neg_one_pow_finrank_mul S.X₃ c₃ hn₃ r₂).preimage
        (add_left_injective (1 : ℤ)).injOn
    have hε₂ : Function.HasFiniteMulSupport fun j : ℤ ↦
        (-1 : F) ^ ((finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + r₃ (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) := by
      simpa only [Nat.mul_comm] using hasFiniteMulSupport_neg_one_pow_finrank_mul S.X₁ c₁ hn₁
        fun j ↦ finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + r₃ (j + 1)
    simpa only [pow_add] using hε₁.fun_mul hε₂
  rw [reidemeisterTorsionWithHomology_eq_finprod hn β₂ _ hy₂ s₂ hs₂,
    reidemeisterTorsionWithHomology_eq_finprod hn₁
      (fun j ↦ chosenBoundaryBasis S.X₁ c₁ (j + 1) j) _ hy₁
      (fun j ↦ chosenBoundaryLift S.X₁ c₁ (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j),
    reidemeisterTorsionWithHomology_eq_finprod hn₃
      (fun j ↦ chosenBoundaryBasis S.X₃ c₃ (j + 1) j) y₃ hy₃
      (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht,
    ← finprod_mul_distrib hsupp₁ hsupp₃, ← finprod_mul_distrib hε (hsupp₁.fun_mul hsupp₃)]
  -- Apply the six-block bracket identity in each degree `j + 1`.
  refine finprod_congr fun j ↦ ?_
  have hy₃_eq : torsionBracketWithHomology c₃ (chosenBoundaryBasis S.X₃ c₃ (j + 1 + 1) (j + 1))
      (h₃' (j + 1)) _ (hy₃Aux j) (chosenBoundaryBasis S.X₃ c₃ (j + 1) j)
      (fun k ↦ (S.g.f (j + 1)).hom (t j k)) (ht j) =
      torsionBracketWithHomology c₃ (chosenBoundaryBasis S.X₃ c₃ (j + 1 + 1) (j + 1))
      (h₃' (j + 1)) (y₃ (j + 1)) (hy₃ (j + 1)) (chosenBoundaryBasis S.X₃ c₃ (j + 1) j)
      (fun k ↦ (S.g.f (j + 1)).hom (t j k)) (ht j) := by
    rw [torsionBracketWithHomology_eq_mul c₃ (chosenBoundaryBasis S.X₃ c₃ (j + 1 + 1) (j + 1))
      (h₃' (j + 1)) (y₃ (j + 1)) (hy₃ (j + 1)) (chosenBoundaryBasis S.X₃ c₃ (j + 1) j) _ (ht j)]
    simp [Basis.det_self]
  rw [torsionBracketWithHomology_shortExact hS hc₁ hc₃ hf hfg (hm₁_eq (j + 1)) (hm₂_eq (j + 1))
    (hm₃_eq j) _ _ _ (chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j) _ (t (j + 1)) (ht (j + 1)) _
    (t j) (ht j) (u₁ (j + 1)) (w₂ (j + 1)) (z₁₁ (j + 1)) (hw₂ (j + 1)) (hz₁₁ (j + 1)) (u₁ j)
    (w₂ j) (z₁₁ j) (z₃₂ j) (hw₂ j) (hz₁₁ j) (hgz₃₂ j) (z₁₂ (j + 1)) (z₂₂ (j + 1))
    (h₁' (j + 1)) (hy₁ (j + 1)) (h₂' (j + 1)) (hy₂ (j + 1)) (h₃' (j + 1)) (hy₃Aux j) (hs₂ j),
    hy₃_eq, mul_zpow, mul_zpow]
  congr 1
  rcases Int.units_eq_one_or j.negOnePow with hj | hj <;> simp [hj, ← inv_pow]

/-- For a bounded short exact sequence of chain complexes with compatible chain bases `(c₁, c₃, c₂)`
and given bases `(u₁, u₂, u₃)` of the images of the maps in the long exact homology sequence, there
exist adapted homology bases `(h₁', h₂', h₃')` for which `τ(H, (h₁', h₂', h₃')) = 1` and
`τ(S.X₂, c₂, h₂') = ε · (τ(S.X₁, c₁, h₁') · τ(S.X₃, c₃, h₃'))`. -/
private theorem exists_adapted_homology_bases
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (u₁ : ∀ i, Basis (Fin (r₁ i)) F (LinearMap.range (hS.δ (i + 1) i rfl).hom))
    (u₂ : ∀ i, Basis (Fin (r₂ i)) F (LinearMap.range (homologyMap S.f i).hom))
    (u₃ : ∀ i, Basis (Fin (r₃ i)) F (LinearMap.range (homologyMap S.g i).hom)) :
    ∃ (h₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
      (h₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
      (h₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)),
      hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ h₁' h₂' h₃') = 1 ∧
        S.X₂.reidemeisterTorsionWithHomology c₂ h₂' =
          (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
              r₂ (j + 1) +
            (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + r₃ (j + 1)) *
              finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
          (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
            S.X₃.reidemeisterTorsionWithHomology c₃ h₃') := by
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  -- Lift `(u₁, u₂, u₃)` along the maps of the long exact homology sequence and choose cycle
  -- representatives, using `moduleCat_exists_d_eq_of_δ_eq` to lift `u₁` simultaneously on chains.
  let s₁ (i : ℤ) (k : Fin (r₂ i)) : S.X₁.homology i :=
    Function.surjInv (homologyMap S.f i).hom.surjective_rangeRestrict (u₂ i k)
  have hs₁ (i : ℤ) (k : Fin (r₂ i)) : (homologyMap S.f i).hom (s₁ i k) = u₂ i k :=
    congrArg Subtype.val (Function.surjInv_eq (homologyMap S.f i).hom.surjective_rangeRestrict _)
  let s₂_hom (i : ℤ) (k : Fin (r₃ i)) : S.X₂.homology i :=
    Function.surjInv (homologyMap S.g i).hom.surjective_rangeRestrict (u₃ i k)
  have hs₂_hom (i : ℤ) (k : Fin (r₃ i)) : (homologyMap S.g i).hom (s₂_hom i k) = u₃ i k :=
    congrArg Subtype.val (Function.surjInv_eq (homologyMap S.g i).hom.surjective_rangeRestrict _)
  let s₃ (i : ℤ) (k : Fin (r₁ i)) : S.X₃.homology (i + 1) :=
    Function.surjInv (hS.δ (i + 1) i rfl).hom.surjective_rangeRestrict (u₁ i k)
  have hs₃ (i : ℤ) (k : Fin (r₁ i)) : (hS.δ (i + 1) i rfl).hom (s₃ i k) = u₁ i k :=
    congrArg Subtype.val (Function.surjInv_eq (hS.δ (i + 1) i rfl).hom.surjective_rangeRestrict _)
  let z₁₁ (i : ℤ) (k : Fin (r₁ i)) : S.X₁.cycles i :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective i) (u₁ i k)
  have hz₁₁ (i : ℤ) (k : Fin (r₁ i)) : (S.X₁.homologyπ i).hom (z₁₁ i k) = u₁ i k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective i) _
  let z₁₂ (i : ℤ) (k : Fin (r₂ i)) : S.X₁.cycles i :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective i) (s₁ i k)
  have hz₁₂ (i : ℤ) (k : Fin (r₂ i)) : (S.X₁.homologyπ i).hom (z₁₂ i k) = s₁ i k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective i) _
  let z₂₂ (i : ℤ) (k : Fin (r₃ i)) : S.X₂.cycles i :=
    Function.surjInv (S.X₂.moduleCat_homologyπ_surjective i) (s₂_hom i k)
  have hz₂₂ (i : ℤ) (k : Fin (r₃ i)) : (S.X₂.homologyπ i).hom (z₂₂ i k) = s₂_hom i k :=
    Function.surjInv_eq (S.X₂.moduleCat_homologyπ_surjective i) _
  choose w₂ z₃₂ hw₂ hgz₃₂ hz₃₂ using fun i k ↦
    hS.moduleCat_exists_d_eq_of_δ_eq (i + 1) i rfl (s₃ i k) (z₁₁ i k)
      ((hs₃ i k).trans (hz₁₁ i k).symm)
  -- Assemble adapted homology bases `(h₁', h₂', h₃')` from the short exact pieces of `H`.
  let h₁Raw (i : ℤ) : Basis (Fin (r₁ i + r₂ i)) F (S.X₁.homology i) :=
    (Basis.ofExactLift (Submodule.injective_subtype _)
      (((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
        (hS.homology_exact₁ (i + 1) i rfl)).symm ▸ LinearMap.exact_subtype_rangeRestrict _)
      (u₁ i) (u₂ i) (s₁ i) fun k ↦ Subtype.ext (hs₁ i k)).reindex finSumFinEquiv
  let h₂Raw (i : ℤ) : Basis (Fin (r₂ i + r₃ i)) F (S.X₂.homology i) :=
    (Basis.ofExactLift (Submodule.injective_subtype _)
      (((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₂ i)).symm ▸
        LinearMap.exact_subtype_rangeRestrict _)
      (u₂ i) (u₃ i) (s₂_hom i) fun k ↦ Subtype.ext (hs₂_hom i k)).reindex finSumFinEquiv
  let h₃Raw (j : ℤ) : Basis (Fin (r₃ (j + 1) + r₁ j)) F (S.X₃.homology (j + 1)) :=
    (Basis.ofExactLift (Submodule.injective_subtype _)
      (((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
        (hS.homology_exact₃ (j + 1) j rfl)).symm ▸ LinearMap.exact_subtype_rangeRestrict _)
      (u₃ (j + 1)) (u₁ j) (s₃ j) fun k ↦ Subtype.ext (hs₃ j k)).reindex finSumFinEquiv
  have hm₁_eq (i : ℤ) : r₁ i + r₂ i = m₁ i := by
    simpa using Fintype.card_congr ((h₁Raw i).indexEquiv (h₁ i))
  have hm₂_eq (i : ℤ) : r₂ i + r₃ i = m₂ i := by
    simpa using Fintype.card_congr ((h₂Raw i).indexEquiv (h₂ i))
  have hm₃_eq (j : ℤ) : r₃ (j + 1) + r₁ j = m₃ (j + 1) := by
    simpa using Fintype.card_congr ((h₃Raw j).indexEquiv (h₃ (j + 1)))
  let h₁' (i : ℤ) : Basis (Fin (m₁ i)) F (S.X₁.homology i) :=
    (h₁Raw i).reindex (finCongr (hm₁_eq i))
  let h₂' (i : ℤ) : Basis (Fin (m₂ i)) F (S.X₂.homology i) :=
    (h₂Raw i).reindex (finCongr (hm₂_eq i))
  let h₃Aux (j : ℤ) : Basis (Fin (m₃ (j + 1))) F (S.X₃.homology (j + 1)) :=
    (h₃Raw j).reindex (finCongr (hm₃_eq j))
  let castH₃ {a b : ℤ} (h : a = b) (e : Basis (Fin (m₃ a)) F (S.X₃.homology a)) :
      Basis (Fin (m₃ b)) F (S.X₃.homology b) := h ▸ e
  let h₃' (i : ℤ) : Basis (Fin (m₃ i)) F (S.X₃.homology i) :=
    castH₃ (Int.sub_add_cancel i 1) (h₃Aux (i - 1))
  have h₃'_add_one (j : ℤ) : h₃' (j + 1) = h₃Aux j := by
    dsimp only [h₃']
    generalize Int.sub_add_cancel (j + 1) 1 = hp
    revert hp
    rw [Int.add_sub_cancel]
    intro hp
    rfl
  -- In `(h₁', h₂', h₃')`, the homology sequence has torsion `1` and the chain complexes satisfy
  -- the adapted-cycles product formula.
  refine ⟨h₁', h₂', h₃', ?_, ?_⟩
  · exact ChainComplex.reidemeisterTorsion_interleave_eq_one_of_exact
      (f := fun i ↦ homologyMap S.f i) (g := fun i ↦ homologyMap S.g i)
      (δ := fun i ↦ hS.δ (i + 1) i rfl) _ _ _
      (ChainComplex.interleave.finite_setOf_rank_ne_zero
        (finite_homology_of_finite c₁ h₁ hn₁) (finite_homology_of_finite c₂ h₂ hn)
        (finite_homology_of_finite c₃ h₃ hn₃))
      hS.acyclic_homologySequenceComplex h₁' h₂' h₃' u₁ u₂ u₃ hs₁ hs₂_hom hs₃
      (fun i ↦ (hm₁_eq i).symm) (fun i ↦ (hm₂_eq i).symm) (fun j ↦ (hm₃_eq j).symm)
      (fun i ↦ by
        ext k; obtain ⟨l, rfl⟩ := (finCongr (hm₁_eq i)).surjective k
        induction l using Fin.addCases <;> simp [h₁', h₁Raw])
      (fun i ↦ by
        ext k; obtain ⟨l, rfl⟩ := (finCongr (hm₂_eq i)).surjective k
        induction l using Fin.addCases <;> simp [h₂', h₂Raw])
      (fun j ↦ by
        rw [h₃'_add_one j]; ext k; obtain ⟨l, rfl⟩ := (finCongr (hm₃_eq j)).surjective k
        induction l using Fin.addCases <;> simp [h₃Aux, h₃Raw])
  · exact reidemeisterTorsionWithHomology_eq_mul_of_adapted_cycles hS c₁ c₃ c₂ hc₁ hc₃ hn
      hm₁_eq hm₂_eq hm₃_eq u₁ w₂ z₁₁ z₁₂ z₂₂ z₃₂ hw₂ hz₁₁ hgz₃₂
      h₁' (fun i k ↦ by
        obtain ⟨l, rfl⟩ := (finCongr (hm₁_eq i)).surjective k
        induction l using Fin.addCases <;> simp [h₁', h₁Raw, hz₁₁, hz₁₂])
      h₂' (fun i k ↦ by
        obtain ⟨l, rfl⟩ := (finCongr (hm₂_eq i)).surjective k
        induction l using Fin.addCases <;>
          simp [h₂', h₂Raw, ← moduleCat_homologyMap_homologyπ, hz₁₂, hs₁, hz₂₂])
      h₃' (fun j k ↦ by
        rw [h₃'_add_one j]; obtain ⟨l, rfl⟩ := (finCongr (hm₃_eq j)).surjective k
        induction l using Fin.addCases <;>
          simp [h₃Aux, h₃Raw, ← moduleCat_homologyMap_homologyπ, hz₂₂, hs₂_hom, hz₃₂])

/-- **Milnor's multiplicativity theorem for Reidemeister torsion with homology bases.**
Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over `F` with compatible chain bases `(c₁, c₃, c₂)` and homology bases
`(h₁, h₂, h₃)`. Then

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H, (h₁, h₂, h₃))`,

where `H = hS.homologySequenceComplex` is the based long exact homology sequence and `ε` is the
product over `j : ℤ` of
`(-1) ^ (dim B₃,ⱼ₊₁ · dim im Hⱼ₊₁(S.f) + (dim B₃,ⱼ₊₁ + dim im Hⱼ₊₁(S.g)) · dim B₁,ⱼ)`.
Both sides vanish when `S.X₂` is unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
          (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃)) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂ h₃ hn _ _
  have (i : ℤ) : Module.Finite F (S.X₁.homology i) := .of_basis (h₁ i)
  have (i : ℤ) : Module.Finite F (S.X₂.homology i) := .of_basis (h₂ i)
  have (i : ℤ) : Module.Finite F (S.X₃.homology i) := .of_basis (h₃ i)
  let u₁ (i : ℤ) := finBasis F (LinearMap.range (hS.δ (i + 1) i rfl).hom)
  let u₂ (i : ℤ) := finBasis F (LinearMap.range (homologyMap S.f i).hom)
  let u₃ (i : ℤ) := finBasis F (LinearMap.range (homologyMap S.g i).hom)
  obtain ⟨h₁', h₂', h₃', hH₁, hadapt⟩ :=
    exists_adapted_homology_bases hS c₁ c₃ c₂ hc₁ hc₃ hn h₁ h₂ h₃ u₁ u₂ u₃
  -- Change homology bases from `(h₁', h₂', h₃')` back to `(h₁, h₂, h₃)` in all four torsions.
  have det_zpow {V : ModuleCat F} {k : ℕ}
      (e e' : Basis (Fin k) F V) (q : ℤ) :
      e.det e' ^ ((q + 1).negOnePow : ℤ) = e'.det e ^ (q.negOnePow : ℤ) := by
    have hinv : e.det e' = (e'.det e)⁻¹ :=
      eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
    rw [hinv, Int.negOnePow_succ, Units.val_neg, zpow_neg, inv_zpow, inv_inv]
  have hH := hS.reidemeisterTorsion_homologySequenceComplex_eq_mul_finprod_det h₁' h₁ h₂' h₂ h₃' h₃
  rw [hH₁, one_mul] at hH
  have hX₂ := S.X₂.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology
    (c := c₂) (h := h₂') h₂
  have hX₁ : S.X₁.reidemeisterTorsionWithHomology c₁ h₁' =
      S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        ∏ᶠ q : ℤ, (h₁' q).det (h₁ q) ^ (q.negOnePow : ℤ) := by
    rw [S.X₁.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₁) (h := h₁) h₁']
    exact congrArg _ (finprod_congr fun q ↦ det_zpow (h₁ q) (h₁' q) q)
  have hX₃ : S.X₃.reidemeisterTorsionWithHomology c₃ h₃' =
      S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        ∏ᶠ q : ℤ, (h₃' q).det (h₃ q) ^ (q.negOnePow : ℤ) := by
    rw [S.X₃.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₃) (h := h₃) h₃']
    exact congrArg _ (finprod_congr fun q ↦ det_zpow (h₃ q) (h₃' q) q)
  rw [hX₂, hadapt, hX₁, hX₃, hH]
  ring

/-- **Multiplicativity of torsion with compatible homology bases.**
Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of chain complexes with compatible
chain bases `(c₁, c₃, c₂)` and compatible homology bases `(h₁, h₃, h₂)`, so that `h₂ i` lists the
images under `Hᵢ(S.f)` of `h₁ i` followed by lifts through `Hᵢ(S.g)` of `h₃ i`. Then `τ(H) = 1` and
`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃)`, with the sign `ε` given by the
dimensions of the boundaries and homology groups of `S.X₁` and `S.X₃`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homology
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (h₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hh₁ : ∀ i k, h₂ i (Fin.castAdd (m₃ i) k) = (homologyMap S.f i).hom (h₁ i k))
    (hh₃ : ∀ i k, (homologyMap S.g i).hom (h₂ i (Fin.natAdd (m₁ i) k)) = h₃ i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (S.X₁.homology (j + 1)) +
          (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (S.X₃.homology (j + 1))) *
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · simpa only [mul_one] using
      reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂ h₃ hn _ 1
  obtain ⟨hg, -, hf⟩ := hS.surjective_and_injective_of_compatible_homology h₃ h₂ hh₃
  have hrk_f (i : ℤ) :
      finrank F (LinearMap.range (homologyMap S.f i).hom) = finrank F (S.X₁.homology i) :=
    (LinearEquiv.ofInjective _ (hf i)).finrank_eq.symm
  have hrk_g (i : ℤ) :
      finrank F (LinearMap.range (homologyMap S.g i).hom) = finrank F (S.X₃.homology i) := by
    rw [LinearMap.range_eq_top.2 (hg i), finrank_top]
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ h₁ h₂ h₃,
    hS.reidemeisterTorsion_homologySequenceComplex_eq_one h₁ h₃ h₂ hh₁ hh₃
      (finite_homology_of_finite c₂ h₂ hn), mul_one]
  simp only [hrk_f, hrk_g]

/-- **Multiplicativity of torsion when the quotient complex is acyclic.**
Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of chain complexes with `S.X₃` acyclic,
compatible chain bases `(c₁, c₃, c₂)`, and homology bases `h₁` of `S.X₁` and `h₂` of `S.X₂` matched
by the isomorphism `Hᵢ(S.f)`. Then
`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃)`, where
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · (dim Hⱼ₊₁(S.X₁) + dim B₁,ⱼ))`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₃
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) (hX₃ : S.X₃.Acyclic)
    {n₁ n₃ m : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m i)) F (S.X₂.homology i))
    (hh : ∀ i k, h₂ i k = (homologyMap S.f i).hom (h₁ i k)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          (finrank F (S.X₁.homology (j + 1)) +
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ * S.X₃.reidemeisterTorsion c₃) := by
  have hsub (i : ℤ) : Subsingleton (S.X₃.homology i) :=
    ModuleCat.subsingleton_of_isZero (hX₃ i).isZero_homology
  let h₃ (i : ℤ) : Basis (Fin 0) F (S.X₃.homology i) := Basis.empty _
  rw [← reidemeisterTorsionWithHomology_reindex_homology c₂ h₂
      (fun i ↦ (Nat.add_zero (m i)).symm),
    reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homology hS c₁ c₃ c₂ hc₁ hc₃
      h₁ h₃ _ (fun i k ↦ by simpa using hh i k) (fun _ k ↦ k.elim0),
    reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₃) (h := h₃) hX₃]
  congr 1
  refine finprod_congr fun j ↦ ?_
  have hrk₃ : finrank F (S.X₃.homology (j + 1)) = 0 := finrank_zero_of_subsingleton
  rw [hrk₃, add_zero, Nat.mul_add]

/-- **Multiplicativity of torsion when the subcomplex is acyclic.**
Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of chain complexes with `S.X₁` acyclic,
compatible chain bases `(c₁, c₃, c₂)`, and homology bases `h₂` of `S.X₂` and `h₃` of `S.X₃` matched
by the isomorphism `Hᵢ(S.g)`. Then
`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁) · τ(S.X₃, c₃, h₃)`, where
`ε = ∏ⱼ (-1) ^ ((dim B₃,ⱼ₊₁ + dim Hⱼ₊₁(S.X₃)) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_acyclic_X₁
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) (hX₁ : S.X₁.Acyclic)
    {n₁ n₃ m : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₂ : ∀ i, Basis (Fin (m i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m i)) F (S.X₃.homology i))
    (hh : ∀ i k, (homologyMap S.g i).hom (h₂ i k) = h₃ i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        ((finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (S.X₃.homology (j + 1))) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsion c₁ * S.X₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  have hsub (i : ℤ) : Subsingleton (S.X₁.homology i) :=
    ModuleCat.subsingleton_of_isZero (hX₁ i).isZero_homology
  let h₁ (i : ℤ) : Basis (Fin 0) F (S.X₁.homology i) := Basis.empty _
  rw [← reidemeisterTorsionWithHomology_reindex_homology c₂ h₂
      (fun i ↦ (Nat.zero_add (m i)).symm),
    reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homology hS c₁ c₃ c₂ hc₁ hc₃
      h₁ h₃ _ (fun _ k ↦ k.elim0) (fun i k ↦ by simpa using hh i k),
    reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₁) (h := h₁) hX₁]
  congr 1
  refine finprod_congr fun j ↦ ?_
  have hrk₁ : finrank F (S.X₁.homology (j + 1)) = 0 := finrank_zero_of_subsingleton
  rw [hrk₁, mul_zero, zero_add]

/-- **Torsion with homology bases of a direct sum.**
For two chain complexes `C₁` and `C₃` of vector spaces over `F` with chain bases `c₁`, `c₃` and
homology bases `h₁`, `h₃`, the biproduct `C₁ ⊞ C₃`, based on chains by `biprodXBasis` and on
homology by `biprodHomologyBasis`, has torsion
`τ(C₁ ⊞ C₃) = ε · τ(C₁, c₁, h₁) · τ(C₃, c₃, h₃)`, where `ε` is the product over `j : ℤ` of
`(-1) ^ (dim B₃,ⱼ₊₁ · dim Hⱼ₊₁(C₁) + (dim B₃,ⱼ₊₁ + dim Hⱼ₊₁(C₃)) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_biprod {C₁ C₃ : ChainComplex (ModuleCat F) ℤ}
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i)) :
    (C₁ ⊞ C₃).reidemeisterTorsionWithHomology
        (fun i ↦ (biprodXBasis (c₁ i) (c₃ i)).reindex finSumFinEquiv)
        (fun i ↦ (biprodHomologyBasis (h₁ i) (h₃ i)).reindex finSumFinEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (C₁.homology (j + 1)) +
          (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (C₃.homology (j + 1))) *
            finrank F (LinearMap.range (C₁.d (j + 1) j).hom))) *
      (C₁.reidemeisterTorsionWithHomology c₁ h₁ *
        C₃.reidemeisterTorsionWithHomology c₃ h₃) :=
  reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homology
    (ShortComplex.Splitting.ofHasBinaryBiproduct C₁ C₃).shortExact c₁ c₃ _
    (by simp) (by simp [← ModuleCat.comp_apply]) h₁ h₃ _
    (by simp) (by simp [← ModuleCat.comp_apply, ← homologyMap_comp])

end ShortExact

end HomologicalComplex
