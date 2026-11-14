/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.BigOperators.Finprod

/-!
# The Reidemeister torsion of an interleaved chain complex

Let `X₁`, `X₂`, `X₃` be three `ℤ`-indexed families of finite-dimensional vector spaces over a
field `F`, with ordered bases `b₁ q`, `b₂ q`, `b₃ q` of sizes `m₁ q`, `m₂ q`, `m₃ q`, and linear
maps

`⋯ ⟶ X₃ (q + 1) ⟶ X₁ q ⟶ X₂ q ⟶ X₃ q ⟶ X₁ (q - 1) ⟶ ⋯`

whose consecutive composites vanish (`f q ≫ g q = 0`, `g (q + 1) ≫ δ q = 0`, `δ q ≫ f q = 0`).
Regarded as the single `ℤ`-graded chain complex `ChainComplex.interleave` with `X₁ q`, `X₂ q`,
`X₃ q` in degrees `3q + 2`, `3q + 1`, `3q` and equipped with the degreewise basis
`ChainComplex.interleave.basis`, its Reidemeister torsion regroups by triples of consecutive
degrees into an alternating product over `ℤ` of the three bracket determinants at `X₁ (j + 1)`,
`X₂ (j + 1)` and `X₃ (j + 1)` (`ChainComplex.interleave.reidemeisterTorsion_eq_finprod`).

When one of the three families vanishes (`m₂ = 0`, `m₃ = 0` or `m₁ = 0`) and the interleaved
complex is acyclic, the remaining map in each period (`δ q`, `f q` or `g q`) is an isomorphism,
and the torsion collapses to the alternating product of its determinants in the given bases
(`ChainComplex.interleave.reidemeisterTorsion_of_eq_zero₂`,
`reidemeisterTorsion_of_eq_zero₃`, `reidemeisterTorsion_of_eq_zero₁`).

The main consumer is `TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence`, where the
interleaved complex is the based long exact homology sequence of a short exact sequence of chain
complexes.

## Main declarations

* `ChainComplex.interleave.card_eq_add_of_acyclic₁`, `card_eq_add_of_acyclic₂`,
  `card_eq_add_of_acyclic₃`: in an acyclic interleaved complex, the rank of each term is the sum of
  the ranks of the incoming and outgoing images.
* `ChainComplex.interleave.reidemeisterTorsion_eq_finprod`: the torsion of a bounded acyclic
  interleaved complex as a `finprod` over `j : ℤ` of three bracket determinants.
* `ChainComplex.interleave.card_eq_of_eq_zero₂`, `reidemeisterTorsion_of_eq_zero₂` and their
  companions for `m₃ = 0` and `m₁ = 0`: rank equalities and determinant formulas when one of the
  three families vanishes.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex.interleave

variable {F : Type*} [Field F] {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} {hfg : ∀ q, f q ≫ g q = 0}
  {hgδ : ∀ q, g (q + 1) ≫ δ q = 0} {hδf : ∀ q, δ q ≫ f q = 0} {m₁ m₂ m₃ : ℤ → ℕ}
  (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q)) (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
  (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))

/-- Transport the image of a morphism `φ : A ⟶ B` to the image of `d = e₁.hom ≫ φ ≫ e₀.inv`
along the target isomorphism `e₀`. -/
private def rangeEquiv {A B A' B' : ModuleCat F} {d : A' ⟶ B'} {φ : A ⟶ B} (e₁ : A' ≅ A)
    (e₀ : B' ≅ B) (hd : d = e₁.hom ≫ φ ≫ e₀.inv) :
    LinearMap.range φ.hom ≃ₗ[F] LinearMap.range d.hom where
  toFun y := ⟨e₀.inv y.1, by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨e₁.inv x, by simp [hd, ← hx]⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  invFun y := ⟨e₀.hom y.1, by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨e₁.hom x, by simp [← hx, hd]⟩⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

@[simp]
private theorem coe_rangeEquiv {A B A' B' : ModuleCat F} {d : A' ⟶ B'} {φ : A ⟶ B} (e₁ : A' ≅ A)
    (e₀ : B' ≅ B) (hd : d = e₁.hom ≫ φ ≫ e₀.inv) (y : LinearMap.range φ.hom) :
    (rangeEquiv e₁ e₀ hd y : B') = e₀.inv y.1 :=
  rfl

/-- Transport a determinant along a linear equivalence carrying one basis to another. -/
private theorem det_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {m m' : ℕ} (c : Basis (Fin m) F M) (b : Basis (Fin m') F N)
    (e : M ≃ₗ[F] N) (hm : m = m') (hc : ∀ i, e (c i) = b (Fin.cast hm i)) (v : Fin m → M) :
    c.det v = b.det (e ∘ v ∘ Fin.cast hm.symm) := by
  subst hm
  have hb : b = c.map e := Basis.eq_of_apply_eq fun i ↦ (hc i).symm.trans (c.map_apply e i).symm
  rw [hb, Basis.det_apply, Basis.det_apply]
  congr 1
  ext i j
  simp [Function.comp_def]

section Boundary

variable {u v w : ℤ → ℕ}
  (α : ∀ q, Basis (Fin (u q)) F (LinearMap.range (δ q).hom))
  (β : ∀ q, Basis (Fin (v q)) F (LinearMap.range (f q).hom))
  (γ : ∀ q, Basis (Fin (w q)) F (LinearMap.range (g q).hom))

/-- The basis of the image of `d : I.X (k + 1) ⟶ I.X k` assembled from `α`, `β` and `γ`. -/
private def boundaryBasis (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
    (hδf : ∀ q, δ q ≫ f q = 0) (k : ℤ) :
    Basis (Fin (rank u v w k)) F
      (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (k + 1) k).hom) :=
  if _ : k % 3 = 0 then
    ((γ (k / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (rangeEquiv (XIso₂ hfg hgδ hδf (k + 1) (k / 3) (by omega))
        (XIso₃ hfg hgδ hδf k (k / 3) (by omega))
        (interleave_d_eq_of_eq_three_mul hfg hgδ hδf (by omega)))
  else if _ : k % 3 = 1 then
    ((β (k / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (rangeEquiv (XIso₁ hfg hgδ hδf (k + 1) (k / 3) (by omega))
        (XIso₂ hfg hgδ hδf k (k / 3) (by omega))
        (interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf (by omega)))
  else
    ((α (k / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (rangeEquiv (XIso₃ hfg hgδ hδf (k + 1) (k / 3 + 1) (by omega))
        (XIso₁ hfg hgδ hδf k (k / 3) (by omega))
        (interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf (by omega)))

private theorem XIso₃_hom_coe_boundaryBasis {k q : ℤ} (hk : k = 3 * q) (l : Fin (rank u v w k)) :
    (XIso₃ hfg hgδ hδf k q hk).hom (boundaryBasis α β γ hfg hgδ hδf k l) =
      γ q (Fin.cast (rank_of_eq_three_mul hk) l) := by
  obtain rfl : k / 3 = q := by omega
  rw [boundaryBasis, dite_eq_left (by omega)]
  simp

private theorem XIso₂_hom_coe_boundaryBasis {k q : ℤ} (hk : k = 3 * q + 1)
    (l : Fin (rank u v w k)) :
    (XIso₂ hfg hgδ hδf k q hk).hom (boundaryBasis α β γ hfg hgδ hδf k l) =
      β q (Fin.cast (rank_of_eq_three_mul_add_one hk) l) := by
  obtain rfl : k / 3 = q := by omega
  rw [boundaryBasis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

private theorem XIso₁_hom_coe_boundaryBasis {k q : ℤ} (hk : k = 3 * q + 2)
    (l : Fin (rank u v w k)) :
    (XIso₁ hfg hgδ hδf k q hk).hom (boundaryBasis α β γ hfg hgδ hδf k l) =
      α q (Fin.cast (rank_of_eq_three_mul_add_two hk) l) := by
  obtain rfl : k / 3 = q := by omega
  rw [boundaryBasis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- Lifts of `boundaryBasis` through the differentials of `ChainComplex.interleave`. -/
private def boundaryLift (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
    (hδf : ∀ q, δ q ≫ f q = 0) (α' : ∀ q, Fin (u q) → X₃ (q + 1))
    (β' : ∀ q, Fin (v q) → X₁ q) (γ' : ∀ q, Fin (w q) → X₂ q) (k : ℤ) (l : Fin (rank u v w k)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (k + 1) :=
  if _ : k % 3 = 0 then
    (XIso₂ hfg hgδ hδf (k + 1) (k / 3) (by omega)).inv
      (γ' (k / 3) (Fin.cast (rank_of_eq_three_mul (by omega)) l))
  else if _ : k % 3 = 1 then
    (XIso₁ hfg hgδ hδf (k + 1) (k / 3) (by omega)).inv
      (β' (k / 3) (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) l))
  else
    (XIso₃ hfg hgδ hδf (k + 1) (k / 3 + 1) (by omega)).inv
      (α' (k / 3) (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) l))

private theorem XIso₂_hom_boundaryLift {α' : ∀ q, Fin (u q) → X₃ (q + 1)}
    {β' : ∀ q, Fin (v q) → X₁ q} {γ' : ∀ q, Fin (w q) → X₂ q} {k q : ℤ} (hk : k = 3 * q)
    (l : Fin (rank u v w k)) :
    (XIso₂ hfg hgδ hδf (k + 1) q (by omega)).hom (boundaryLift hfg hgδ hδf α' β' γ' k l) =
      γ' q (Fin.cast (rank_of_eq_three_mul hk) l) := by
  obtain rfl : k / 3 = q := by omega
  rw [boundaryLift, dite_eq_left (by omega)]
  simp

private theorem XIso₁_hom_boundaryLift {α' : ∀ q, Fin (u q) → X₃ (q + 1)}
    {β' : ∀ q, Fin (v q) → X₁ q} {γ' : ∀ q, Fin (w q) → X₂ q} {k q : ℤ} (hk : k = 3 * q + 1)
    (l : Fin (rank u v w k)) :
    (XIso₁ hfg hgδ hδf (k + 1) q (by omega)).hom (boundaryLift hfg hgδ hδf α' β' γ' k l) =
      β' q (Fin.cast (rank_of_eq_three_mul_add_one hk) l) := by
  obtain rfl : k / 3 = q := by omega
  rw [boundaryLift, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

private theorem XIso₃_hom_boundaryLift {α' : ∀ q, Fin (u q) → X₃ (q + 1)}
    {β' : ∀ q, Fin (v q) → X₁ q} {γ' : ∀ q, Fin (w q) → X₂ q} {k q : ℤ} (hk : k = 3 * q + 2)
    (l : Fin (rank u v w k)) :
    (XIso₃ hfg hgδ hδf (k + 1) (q + 1) (by omega)).hom (boundaryLift hfg hgδ hδf α' β' γ' k l) =
      α' q (Fin.cast (rank_of_eq_three_mul_add_two hk) l) := by
  obtain rfl : k / 3 = q := by omega
  rw [boundaryLift, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

private theorem boundaryLift_spec {α' : ∀ q, Fin (u q) → X₃ (q + 1)}
    (hα' : ∀ q l, (δ q).hom (α' q l) = α q l) {β' : ∀ q, Fin (v q) → X₁ q}
    (hβ' : ∀ q l, (f q).hom (β' q l) = β q l) {γ' : ∀ q, Fin (w q) → X₂ q}
    (hγ' : ∀ q l, (g q).hom (γ' q l) = γ q l) (k : ℤ) (l : Fin (rank u v w k)) :
    ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (k + 1) k).hom
      (boundaryLift hfg hgδ hδf α' β' γ' k l) = boundaryBasis α β γ hfg hgδ hδf k l := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, k = 3 * q ∨ k = 3 * q + 1 ∨ k = 3 * q + 2 := ⟨k / 3, by omega⟩
  · apply (XIso₃ hfg hgδ hδf k q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul hfg hgδ hδf hq, XIso₂_hom_boundaryLift hq,
      XIso₃_hom_coe_boundaryBasis α β γ hq, hγ']
  · apply (XIso₂ hfg hgδ hδf k q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf hq, XIso₁_hom_boundaryLift hq,
      XIso₂_hom_coe_boundaryBasis α β γ hq, hβ']
  · apply (XIso₁ hfg hgδ hδf k q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf hq, XIso₃_hom_boundaryLift hq,
      XIso₁_hom_coe_boundaryBasis α β γ hq, hα']

include b₁ α β in
/-- In an acyclic interleaved complex, the rank `m₁ q` of `X₁ q` is the sum of the ranks of the
images of `δ q` and `f q`. -/
theorem card_eq_add_of_acyclic₁ (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    m₁ q = u q + v q := by
  have := Module.Finite.of_basis (b₁ q)
  have ⟨h₁, _, _⟩ := (acyclic_interleave_iff hfg hgδ hδf).1 hI
  have h := LinearMap.finrank_range_add_finrank_ker (f q).hom
  rw [← (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (h₁ q),
    finrank_eq_card_basis (b₁ q), finrank_eq_card_basis (α q), finrank_eq_card_basis (β q)] at h
  simp only [Fintype.card_fin] at h
  omega

include b₂ β γ in
/-- In an acyclic interleaved complex, the rank `m₂ q` of `X₂ q` is the sum of the ranks of the
images of `f q` and `g q`. -/
theorem card_eq_add_of_acyclic₂ (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    m₂ q = v q + w q := by
  have := Module.Finite.of_basis (b₂ q)
  have ⟨_, h₂, _⟩ := (acyclic_interleave_iff hfg hgδ hδf).1 hI
  have h := LinearMap.finrank_range_add_finrank_ker (g q).hom
  rw [← (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (h₂ q),
    finrank_eq_card_basis (b₂ q), finrank_eq_card_basis (β q), finrank_eq_card_basis (γ q)] at h
  simp only [Fintype.card_fin] at h
  omega

include b₃ α γ in
/-- In an acyclic interleaved complex, the rank `m₃ (q + 1)` of `X₃ (q + 1)` is the sum of the
ranks of the images of `g (q + 1)` and `δ q`. -/
theorem card_eq_add_of_acyclic₃ (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    m₃ (q + 1) = w (q + 1) + u q := by
  have := Module.Finite.of_basis (b₃ (q + 1))
  have ⟨_, _, h₃⟩ := (acyclic_interleave_iff hfg hgδ hδf).1 hI
  have h := LinearMap.finrank_range_add_finrank_ker (δ q).hom
  rw [← (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (h₃ q),
    finrank_eq_card_basis (b₃ (q + 1)), finrank_eq_card_basis (α q),
    finrank_eq_card_basis (γ (q + 1))] at h
  simp only [Fintype.card_fin] at h
  omega

private theorem torsionBracket_three_mul_add_two
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    {α' : ∀ q, Fin (u q) → X₃ (q + 1)} (hα' : ∀ q l, (δ q).hom (α' q l) = α q l)
    {β' : ∀ q, Fin (v q) → X₁ q} (hβ' : ∀ q l, (f q).hom (β' q l) = β q l)
    {γ' : ∀ q, Fin (w q) → X₂ q} (hγ' : ∀ q l, (g q).hom (γ' q l) = γ q l) (j : ℤ) :
    HomologicalComplex.torsionBracket (basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
        (hI (3 * j + 2 + 1)) (boundaryBasis α β γ hfg hgδ hδf (3 * j + 2 + 1))
        (boundaryBasis α β γ hfg hgδ hδf (3 * j + 2))
        (boundaryLift hfg hgδ hδf α' β' γ' (3 * j + 2))
        (boundaryLift_spec α β γ hα' hβ' hγ' (3 * j + 2)) =
      (b₃ (j + 1)).det (Fin.append (fun l ↦ (γ (j + 1) l : X₃ (j + 1))) (α' j) ∘
        Fin.cast (card_eq_add_of_acyclic₃ b₃ α γ hI j)) := by
  have hm := card_eq_add_of_acyclic₃ b₃ α γ hI j
  have hk₁ : 3 * j + 2 + 1 = 3 * (j + 1) := by omega
  have hrk : rank m₁ m₂ m₃ (3 * j + 2 + 1) =
      rank u v w (3 * j + 2 + 1) + rank u v w (3 * j + 2) := by
    rw [rank_of_eq_three_mul hk₁, rank_of_eq_three_mul hk₁, rank_of_eq_three_mul_add_two rfl, hm]
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hrk,
    det_eq_of_linearEquiv _ (b₃ (j + 1))
      (XIso₃ hfg hgδ hδf (3 * j + 2 + 1) (j + 1) hk₁).toLinearEquiv
      (rank_of_eq_three_mul hk₁) (XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ hk₁)]
  congr 1
  ext l
  obtain ⟨m, rfl⟩ := (finCongr hm.symm).surjective l
  simp only [Function.comp_apply, Iso.toLinearEquiv_apply]
  induction m using Fin.addCases with
  | left m =>
    have hc : Fin.cast hrk (Fin.cast (rank_of_eq_three_mul hk₁).symm
        (finCongr hm.symm (Fin.castAdd (u j) m))) =
        Fin.castAdd (rank u v w (3 * j + 2)) (Fin.cast (rank_of_eq_three_mul hk₁).symm m) :=
      Fin.ext (by simp)
    rw [hc, Fin.append_left, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]
    simpa using XIso₃_hom_coe_boundaryBasis α β γ (hfg := hfg) (hgδ := hgδ) (hδf := hδf) hk₁
      (Fin.cast (rank_of_eq_three_mul hk₁).symm m)
  | right m =>
    have hc : Fin.cast hrk (Fin.cast (rank_of_eq_three_mul hk₁).symm
        (finCongr hm.symm (Fin.natAdd (w (j + 1)) m))) =
        Fin.natAdd (rank u v w (3 * j + 2 + 1))
          (Fin.cast (rank_of_eq_three_mul_add_two rfl).symm m) :=
      Fin.ext (by simp [rank_of_eq_three_mul hk₁])
    rw [hc, Fin.append_right, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
    simpa using XIso₃_hom_boundaryLift (hfg := hfg) (hgδ := hgδ) (hδf := hδf)
      (α' := α') (β' := β') (γ' := γ') (q := j) rfl
      (Fin.cast (rank_of_eq_three_mul_add_two rfl).symm m)

private theorem torsionBracket_three_mul_add_three
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    {α' : ∀ q, Fin (u q) → X₃ (q + 1)} (hα' : ∀ q l, (δ q).hom (α' q l) = α q l)
    {β' : ∀ q, Fin (v q) → X₁ q} (hβ' : ∀ q l, (f q).hom (β' q l) = β q l)
    {γ' : ∀ q, Fin (w q) → X₂ q} (hγ' : ∀ q l, (g q).hom (γ' q l) = γ q l) (j : ℤ) :
    HomologicalComplex.torsionBracket (basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
        (hI (3 * j + 3 + 1)) (boundaryBasis α β γ hfg hgδ hδf (3 * j + 3 + 1))
        (boundaryBasis α β γ hfg hgδ hδf (3 * j + 3))
        (boundaryLift hfg hgδ hδf α' β' γ' (3 * j + 3))
        (boundaryLift_spec α β γ hα' hβ' hγ' (3 * j + 3)) =
      (b₂ (j + 1)).det (Fin.append (fun l ↦ (β (j + 1) l : X₂ (j + 1))) (γ' (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₂ b₂ β γ hI (j + 1))) := by
  have hm := card_eq_add_of_acyclic₂ b₂ β γ hI (j + 1)
  have hk₀ : 3 * j + 3 = 3 * (j + 1) := by omega
  have hk₁ : 3 * j + 3 + 1 = 3 * (j + 1) + 1 := by omega
  have hrk : rank m₁ m₂ m₃ (3 * j + 3 + 1) =
      rank u v w (3 * j + 3 + 1) + rank u v w (3 * j + 3) := by
    rw [rank_of_eq_three_mul_add_one hk₁, rank_of_eq_three_mul_add_one hk₁,
      rank_of_eq_three_mul hk₀, hm]
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hrk,
    det_eq_of_linearEquiv _ (b₂ (j + 1))
      (XIso₂ hfg hgδ hδf (3 * j + 3 + 1) (j + 1) hk₁).toLinearEquiv
      (rank_of_eq_three_mul_add_one hk₁) (XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ hk₁)]
  congr 1
  ext l
  obtain ⟨m, rfl⟩ := (finCongr hm.symm).surjective l
  simp only [Function.comp_apply, Iso.toLinearEquiv_apply]
  induction m using Fin.addCases with
  | left m =>
    have hc : Fin.cast hrk (Fin.cast (rank_of_eq_three_mul_add_one hk₁).symm
        (finCongr hm.symm (Fin.castAdd (w (j + 1)) m))) =
        Fin.castAdd (rank u v w (3 * j + 3))
          (Fin.cast (rank_of_eq_three_mul_add_one hk₁).symm m) :=
      Fin.ext (by simp)
    rw [hc, Fin.append_left, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]
    simpa using XIso₂_hom_coe_boundaryBasis α β γ (hfg := hfg) (hgδ := hgδ) (hδf := hδf) hk₁
      (Fin.cast (rank_of_eq_three_mul_add_one hk₁).symm m)
  | right m =>
    have hc : Fin.cast hrk (Fin.cast (rank_of_eq_three_mul_add_one hk₁).symm
        (finCongr hm.symm (Fin.natAdd (v (j + 1)) m))) =
        Fin.natAdd (rank u v w (3 * j + 3 + 1)) (Fin.cast (rank_of_eq_three_mul hk₀).symm m) :=
      Fin.ext (by simp [rank_of_eq_three_mul_add_one hk₁])
    rw [hc, Fin.append_right, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
    simpa using XIso₂_hom_boundaryLift (hfg := hfg) (hgδ := hgδ) (hδf := hδf)
      (α' := α') (β' := β') (γ' := γ') hk₀ (Fin.cast (rank_of_eq_three_mul hk₀).symm m)

private theorem torsionBracket_three_mul_add_four
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    {α' : ∀ q, Fin (u q) → X₃ (q + 1)} (hα' : ∀ q l, (δ q).hom (α' q l) = α q l)
    {β' : ∀ q, Fin (v q) → X₁ q} (hβ' : ∀ q l, (f q).hom (β' q l) = β q l)
    {γ' : ∀ q, Fin (w q) → X₂ q} (hγ' : ∀ q l, (g q).hom (γ' q l) = γ q l) (j : ℤ) :
    HomologicalComplex.torsionBracket (basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
        (hI (3 * j + 4 + 1)) (boundaryBasis α β γ hfg hgδ hδf (3 * j + 4 + 1))
        (boundaryBasis α β γ hfg hgδ hδf (3 * j + 4))
        (boundaryLift hfg hgδ hδf α' β' γ' (3 * j + 4))
        (boundaryLift_spec α β γ hα' hβ' hγ' (3 * j + 4)) =
      (b₁ (j + 1)).det (Fin.append (fun l ↦ (α (j + 1) l : X₁ (j + 1))) (β' (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₁ b₁ α β hI (j + 1))) := by
  have hm := card_eq_add_of_acyclic₁ b₁ α β hI (j + 1)
  have hk₀ : 3 * j + 4 = 3 * (j + 1) + 1 := by omega
  have hk₁ : 3 * j + 4 + 1 = 3 * (j + 1) + 2 := by omega
  have hrk : rank m₁ m₂ m₃ (3 * j + 4 + 1) =
      rank u v w (3 * j + 4 + 1) + rank u v w (3 * j + 4) := by
    rw [rank_of_eq_three_mul_add_two hk₁, rank_of_eq_three_mul_add_two hk₁,
      rank_of_eq_three_mul_add_one hk₀, hm]
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hrk,
    det_eq_of_linearEquiv _ (b₁ (j + 1))
      (XIso₁ hfg hgδ hδf (3 * j + 4 + 1) (j + 1) hk₁).toLinearEquiv
      (rank_of_eq_three_mul_add_two hk₁) (XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ hk₁)]
  congr 1
  ext l
  obtain ⟨m, rfl⟩ := (finCongr hm.symm).surjective l
  simp only [Function.comp_apply, Iso.toLinearEquiv_apply]
  induction m using Fin.addCases with
  | left m =>
    have hc : Fin.cast hrk (Fin.cast (rank_of_eq_three_mul_add_two hk₁).symm
        (finCongr hm.symm (Fin.castAdd (v (j + 1)) m))) =
        Fin.castAdd (rank u v w (3 * j + 4))
          (Fin.cast (rank_of_eq_three_mul_add_two hk₁).symm m) :=
      Fin.ext (by simp)
    rw [hc, Fin.append_left, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]
    simpa using XIso₁_hom_coe_boundaryBasis α β γ (hfg := hfg) (hgδ := hgδ) (hδf := hδf) hk₁
      (Fin.cast (rank_of_eq_three_mul_add_two hk₁).symm m)
  | right m =>
    have hc : Fin.cast hrk (Fin.cast (rank_of_eq_three_mul_add_two hk₁).symm
        (finCongr hm.symm (Fin.natAdd (u (j + 1)) m))) =
        Fin.natAdd (rank u v w (3 * j + 4 + 1))
          (Fin.cast (rank_of_eq_three_mul_add_one hk₀).symm m) :=
      Fin.ext (by simp [rank_of_eq_three_mul_add_two hk₁])
    rw [hc, Fin.append_right, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
    simpa using XIso₁_hom_boundaryLift (hfg := hfg) (hgδ := hgδ) (hδf := hδf)
      (α' := α') (β' := β') (γ' := γ') hk₀ (Fin.cast (rank_of_eq_three_mul_add_one hk₀).symm m)

/-- The three indices `3j + 2`, `3j + 3`, `3j + 4` forming the fiber `(k - 2) / 3 = j`. -/
private def fiberEquiv (j : ℤ) : Fin 3 ≃ {k : ℤ // (k - 2) / 3 = j} where
  toFun i := ⟨3 * j + 2 + i.1, by omega⟩
  invFun k := ⟨(k.1 - (3 * j + 2)).toNat, by have := k.2; omega⟩
  left_inv i := by ext; dsimp; omega
  right_inv k := by ext; dsimp; have := k.2; omega

/-- **Reidemeister torsion of a bounded acyclic interleaved complex.** Given bases `α q`, `β q`,
`γ q` of the images of `δ q`, `f q`, `g q` and lifts `α' q`, `β' q`, `γ' q`, the torsion of
`ChainComplex.interleave` is the product over `j : ℤ` of the three bracket determinants at
`X₁ (j + 1)`, `X₂ (j + 1)` and `X₃ (j + 1)`, with exponents `(-1) ^ j`, `(-1) ^ (j + 1)` and
`(-1) ^ j`. -/
theorem reidemeisterTorsion_eq_finprod (h₁ : {q | m₁ q ≠ 0}.Finite) (h₂ : {q | m₂ q ≠ 0}.Finite)
    (h₃ : {q | m₃ q ≠ 0}.Finite) (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    (α' : ∀ q, Fin (u q) → X₃ (q + 1)) (hα' : ∀ q l, (δ q).hom (α' q l) = α q l)
    (β' : ∀ q, Fin (v q) → X₁ q) (hβ' : ∀ q l, (f q).hom (β' q l) = β q l)
    (γ' : ∀ q, Fin (w q) → X₂ q) (hγ' : ∀ q l, (g q).hom (γ' q l) = γ q l) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁ b₂ b₃) =
      ∏ᶠ j : ℤ,
        ((b₁ (j + 1)).det (Fin.append (fun l ↦ (α (j + 1) l : X₁ (j + 1))) (β' (j + 1)) ∘
            Fin.cast (card_eq_add_of_acyclic₁ b₁ α β hI (j + 1)))) ^ (j.negOnePow : ℤ) *
        ((b₂ (j + 1)).det (Fin.append (fun l ↦ (β (j + 1) l : X₂ (j + 1))) (γ' (j + 1)) ∘
            Fin.cast (card_eq_add_of_acyclic₂ b₂ β γ hI (j + 1)))) ^
          ((j + 1).negOnePow : ℤ) *
        ((b₃ (j + 1)).det (Fin.append (fun l ↦ (γ (j + 1) l : X₃ (j + 1))) (α' j) ∘
            Fin.cast (card_eq_add_of_acyclic₃ b₃ α γ hI j))) ^ (j.negOnePow : ℤ) := by
  let F₀ (k : ℤ) : F :=
    HomologicalComplex.torsionBracket (basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
      (hI (k + 1)) (boundaryBasis α β γ hfg hgδ hδf (k + 1))
      (boundaryBasis α β γ hfg hgδ hδf k) (boundaryLift hfg hgδ hδf α' β' γ' k)
      (boundaryLift_spec α β γ hα' hβ' hγ' k) ^ (k.negOnePow : ℤ)
  have hfin := finite_setOf_rank_ne_zero h₁ h₂ h₃
  have hsupp : Function.HasFiniteMulSupport F₀ :=
    (hfin.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun k hk ↦ by
        dsimp [F₀]
        rw [HomologicalComplex.torsionBracket_eq_one _ _ _ _ _ _ _ _ (by simpa using hk), one_zpow]
  -- Regroup the degreewise product by the fibers `(k - 2) / 3 = j`, each of size `3`.
  rw [HomologicalComplex.reidemeisterTorsion_eq_finprod hfin hI
      (boundaryBasis α β γ hfg hgδ hδf) (boundaryLift hfg hgδ hδf α' β' γ')
      (boundaryLift_spec α β γ hα' hβ' hγ'),
    ← TauCeti.finprod_fiberwise (fun k : ℤ ↦ (k - 2) / 3) F₀ hsupp]
  refine finprod_congr fun j ↦ ?_
  rw [← finprod_comp_equiv (fiberEquiv j), finprod_eq_prod_of_fintype, Fin.prod_univ_three]
  have hf₀ : F₀ (fiberEquiv j 0).1 =
      ((b₃ (j + 1)).det (Fin.append (fun l ↦ (γ (j + 1) l : X₃ (j + 1))) (α' j) ∘
        Fin.cast (card_eq_add_of_acyclic₃ b₃ α γ hI j))) ^ (j.negOnePow : ℤ) := by
    have hk : (fiberEquiv j 0).1 = 3 * j + 2 := by simp [fiberEquiv]
    rw [hk]
    dsimp [F₀]
    rw [torsionBracket_three_mul_add_two b₁ b₂ b₃ α β γ hI hα' hβ' hγ' j,
      (Int.negOnePow_eq_iff _ _).2 ⟨j + 1, by ring⟩]
  have hf₁ : F₀ (fiberEquiv j 1).1 =
      ((b₂ (j + 1)).det (Fin.append (fun l ↦ (β (j + 1) l : X₂ (j + 1))) (γ' (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₂ b₂ β γ hI (j + 1)))) ^
          ((j + 1).negOnePow : ℤ) := by
    have hk : (fiberEquiv j 1).1 = 3 * j + 3 := by dsimp [fiberEquiv]; omega
    rw [hk]
    dsimp [F₀]
    rw [torsionBracket_three_mul_add_three b₁ b₂ b₃ α β γ hI hα' hβ' hγ' j,
      (Int.negOnePow_eq_iff (3 * j + 3) (j + 1)).2 ⟨j + 1, by ring⟩]
  have hf₂ : F₀ (fiberEquiv j 2).1 =
      ((b₁ (j + 1)).det (Fin.append (fun l ↦ (α (j + 1) l : X₁ (j + 1))) (β' (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₁ b₁ α β hI (j + 1)))) ^ (j.negOnePow : ℤ) := by
    have hk : (fiberEquiv j 2).1 = 3 * j + 4 := by dsimp [fiberEquiv]; omega
    rw [hk]
    dsimp [F₀]
    rw [torsionBracket_three_mul_add_four b₁ b₂ b₃ α β γ hI hα' hβ' hγ' j,
      (Int.negOnePow_eq_iff (3 * j + 4) j).2 ⟨j + 2, by ring⟩]
  rw [hf₀, hf₁, hf₂]
  ring

end Boundary

section Specializations

private theorem subsingleton_of_eq_zero {M : Type*} [AddCommGroup M] [Module F M] {m : ℕ}
    (b : Basis (Fin m) F M) (hm : m = 0) : Subsingleton M := by
  have : IsEmpty (Fin m) := hm ▸ inferInstance
  exact b.repr.toEquiv.subsingleton

private theorem subsingleton_range_of_domain {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [Subsingleton M] (φ : M →ₗ[F] N) :
    Subsingleton (LinearMap.range φ) :=
  ⟨fun ⟨_, x, hx⟩ ⟨_, y, hy⟩ ↦
    Subtype.ext (hx.symm.trans ((congrArg φ (Subsingleton.elim x y)).trans hy))⟩

private theorem bijective_of_subsingleton {A B C D : ModuleCat F} {φ : A ⟶ B} {ψ : B ⟶ C}
    {θ : C ⟶ D} (hφψ : φ ≫ ψ = 0) (hψθ : ψ ≫ θ = 0) [Subsingleton A] [Subsingleton D]
    (h₁ : (ShortComplex.mk φ ψ hφψ).Exact) (h₂ : (ShortComplex.mk ψ θ hψθ).Exact) :
    Function.Bijective ψ.hom := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := (ShortComplex.moduleCat_exact_iff (ShortComplex.mk φ ψ hφψ)).1 h₁ x hx
    simp [Subsingleton.elim z 0]
  · exact (ShortComplex.moduleCat_exact_iff (ShortComplex.mk ψ θ hψθ)).1 h₂ y
      (Subsingleton.elim _ _)

include b₂ in
private theorem bijective_δ_of_eq_zero₂ (hm₂ : ∀ q, m₂ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    Function.Bijective (δ q).hom := by
  have := subsingleton_of_eq_zero (b₂ (q + 1)) (hm₂ (q + 1))
  have := subsingleton_of_eq_zero (b₂ q) (hm₂ q)
  have ⟨h₁, _, h₃⟩ := (acyclic_interleave_iff hfg hgδ hδf).1 hI
  exact bijective_of_subsingleton (hgδ q) (hδf q) (h₃ q) (h₁ q)

include b₁ b₂ b₃ in
/-- When `X₂` vanishes in an acyclic interleaved complex, `δ q : X₃ (q + 1) ⟶ X₁ q` is an
isomorphism, so `m₃ (q + 1) = m₁ q`. -/
theorem card_eq_of_eq_zero₂ (hm₂ : ∀ q, m₂ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    m₃ (q + 1) = m₁ q := by
  simpa using (finrank_eq_card_basis ((b₃ (q + 1)).map
    (LinearEquiv.ofBijective _ (bijective_δ_of_eq_zero₂ b₂ hm₂ hI q)))).symm.trans
      (finrank_eq_card_basis (b₁ q))

/-- When `X₂` vanishes in a bounded acyclic interleaved complex, the torsion is the alternating
product `∏ᶠ q, det(δ q) ^ ((-1) ^ (q + 1))` of the determinants of `δ q` in the bases `b₃ (q + 1)`
and `b₁ q`. -/
theorem reidemeisterTorsion_of_eq_zero₂ (h₁ : {q | m₁ q ≠ 0}.Finite) (hm₂ : ∀ q, m₂ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁ b₂ b₃) =
      ∏ᶠ q : ℤ, ((b₁ q).det fun k ↦ (δ q).hom (b₃ (q + 1)
        (Fin.cast (card_eq_of_eq_zero₂ b₁ b₂ b₃ hm₂ hI q).symm k))) ^ ((q + 1).negOnePow : ℤ) := by
  have h₂ : {q | m₂ q ≠ 0}.Finite := by simp [hm₂]
  have h₃ : {q | m₃ q ≠ 0}.Finite :=
    (h₁.image (· + 1)).subset fun q hq ↦ ⟨q - 1, by
      have hcard := card_eq_of_eq_zero₂ b₁ b₂ b₃ hm₂ hI (q - 1)
      rw [sub_add_cancel] at hcard
      exact fun h0 ↦ hq (hcard.trans h0), sub_add_cancel q 1⟩
  have hSub₂ (q : ℤ) : Subsingleton (X₂ q) := subsingleton_of_eq_zero (b₂ q) (hm₂ q)
  have hSubg (q : ℤ) : Subsingleton (LinearMap.range (g q).hom) :=
    subsingleton_range_of_domain (g q).hom
  let α (q : ℤ) := (b₃ (q + 1)).map
    (LinearEquiv.ofInjective (δ q).hom (bijective_δ_of_eq_zero₂ b₂ hm₂ hI q).1)
  let β (q : ℤ) : Basis (Fin 0) F (LinearMap.range (f q).hom) := Basis.empty _
  let γ (q : ℤ) : Basis (Fin 0) F (LinearMap.range (g q).hom) := Basis.empty _
  have hshift : (∏ᶠ q : ℤ, ((b₁ q).det fun k ↦ (δ q).hom (b₃ (q + 1)
      (Fin.cast (card_eq_of_eq_zero₂ b₁ b₂ b₃ hm₂ hI q).symm k))) ^
        ((q + 1).negOnePow : ℤ)) =
    ∏ᶠ j : ℤ, ((b₁ (j + 1)).det fun k ↦ (δ (j + 1)).hom (b₃ (j + 1 + 1)
      (Fin.cast (card_eq_of_eq_zero₂ b₁ b₂ b₃ hm₂ hI (j + 1)).symm k))) ^
        ((j + 1 + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight (1 : ℤ))).symm
  rw [hshift, reidemeisterTorsion_eq_finprod b₁ b₂ b₃ α β γ h₁ h₂ h₃ hI
    (fun q ↦ b₃ (q + 1)) (fun q l ↦ by simp [α]) (fun _ ↦ Fin.elim0) (fun _ l ↦ l.elim0)
    (fun _ ↦ Fin.elim0) (fun _ l ↦ l.elim0)]
  refine finprod_congr fun j ↦ ?_
  have : IsEmpty (Fin (m₂ (j + 1))) := hm₂ (j + 1) ▸ inferInstance
  have hd₂ : (b₂ (j + 1)).det
      (Fin.append (fun l : Fin 0 ↦ (β (j + 1) l : X₂ (j + 1))) Fin.elim0 ∘
        Fin.cast (card_eq_add_of_acyclic₂ b₂ β γ hI (j + 1))) = 1 := by simp
  have hd₃ : (b₃ (j + 1)).det
      (Fin.append (fun l : Fin 0 ↦ (γ (j + 1) l : X₃ (j + 1))) (b₃ (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₃ b₃ α γ hI j)) = 1 := by
    convert (b₃ (j + 1)).det_self
    ext k
    simp [Fin.append_left_nil _ _ rfl]
  rw [hd₂, one_zpow, mul_one, hd₃, one_zpow, mul_one,
    (Int.negOnePow_eq_iff (j + 1 + 1) j).2 ⟨1, by ring⟩]
  congr 2
  ext k
  simp [α, Fin.append_right_nil _ _ rfl]

include b₃ in
private theorem bijective_f_of_eq_zero₃ (hm₃ : ∀ q, m₃ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    Function.Bijective (f q).hom := by
  have := subsingleton_of_eq_zero (b₃ (q + 1)) (hm₃ (q + 1))
  have := subsingleton_of_eq_zero (b₃ q) (hm₃ q)
  have ⟨h₁, h₂, _⟩ := (acyclic_interleave_iff hfg hgδ hδf).1 hI
  exact bijective_of_subsingleton (hδf q) (hfg q) (h₁ q) (h₂ q)

include b₁ b₂ b₃ in
/-- When `X₃` vanishes in an acyclic interleaved complex, `f q : X₁ q ⟶ X₂ q` is an isomorphism,
so `m₁ q = m₂ q`. -/
theorem card_eq_of_eq_zero₃ (hm₃ : ∀ q, m₃ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    m₁ q = m₂ q := by
  simpa using (finrank_eq_card_basis ((b₁ q).map
    (LinearEquiv.ofBijective _ (bijective_f_of_eq_zero₃ b₃ hm₃ hI q)))).symm.trans
      (finrank_eq_card_basis (b₂ q))

/-- When `X₃` vanishes in a bounded acyclic interleaved complex, the torsion is the alternating
product `∏ᶠ q, det(f q) ^ ((-1) ^ q)` of the determinants of `f q` in the bases `b₁ q` and
`b₂ q`. -/
theorem reidemeisterTorsion_of_eq_zero₃ (h₁ : {q | m₁ q ≠ 0}.Finite) (hm₃ : ∀ q, m₃ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁ b₂ b₃) =
      ∏ᶠ q : ℤ, ((b₂ q).det fun k ↦ (f q).hom (b₁ q
        (Fin.cast (card_eq_of_eq_zero₃ b₁ b₂ b₃ hm₃ hI q).symm k))) ^ (q.negOnePow : ℤ) := by
  have h₂ : {q | m₂ q ≠ 0}.Finite :=
    h₁.subset fun q hq h0 ↦ hq ((card_eq_of_eq_zero₃ b₁ b₂ b₃ hm₃ hI q).symm.trans h0)
  have h₃ : {q | m₃ q ≠ 0}.Finite := by simp [hm₃]
  have hSub₃ (q : ℤ) : Subsingleton (X₃ q) := subsingleton_of_eq_zero (b₃ q) (hm₃ q)
  have hSubδ (q : ℤ) : Subsingleton (LinearMap.range (δ q).hom) :=
    subsingleton_range_of_domain (δ q).hom
  let α (q : ℤ) : Basis (Fin 0) F (LinearMap.range (δ q).hom) := Basis.empty _
  let β (q : ℤ) := (b₁ q).map
    (LinearEquiv.ofInjective (f q).hom (bijective_f_of_eq_zero₃ b₃ hm₃ hI q).1)
  let γ (q : ℤ) : Basis (Fin 0) F (LinearMap.range (g q).hom) := Basis.empty _
  have hshift : (∏ᶠ q : ℤ, ((b₂ q).det fun k ↦ (f q).hom (b₁ q
      (Fin.cast (card_eq_of_eq_zero₃ b₁ b₂ b₃ hm₃ hI q).symm k))) ^ (q.negOnePow : ℤ)) =
    ∏ᶠ j : ℤ, ((b₂ (j + 1)).det fun k ↦ (f (j + 1)).hom (b₁ (j + 1)
      (Fin.cast (card_eq_of_eq_zero₃ b₁ b₂ b₃ hm₃ hI (j + 1)).symm k))) ^
        ((j + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight (1 : ℤ))).symm
  rw [hshift, reidemeisterTorsion_eq_finprod b₁ b₂ b₃ α β γ h₁ h₂ h₃ hI
    (fun _ ↦ Fin.elim0) (fun _ l ↦ l.elim0) (fun q ↦ b₁ q) (fun q l ↦ by simp [β])
    (fun _ ↦ Fin.elim0) (fun _ l ↦ l.elim0)]
  refine finprod_congr fun j ↦ ?_
  have : IsEmpty (Fin (m₃ (j + 1))) := hm₃ (j + 1) ▸ inferInstance
  have hd₁ : (b₁ (j + 1)).det
      (Fin.append (fun l : Fin 0 ↦ (α (j + 1) l : X₁ (j + 1))) (b₁ (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₁ b₁ α β hI (j + 1))) = 1 := by
    convert (b₁ (j + 1)).det_self
    ext k
    simp [Fin.append_left_nil _ _ rfl]
  have hd₃ : (b₃ (j + 1)).det
      (Fin.append (fun l : Fin 0 ↦ (γ (j + 1) l : X₃ (j + 1))) Fin.elim0 ∘
        Fin.cast (card_eq_add_of_acyclic₃ b₃ α γ hI j)) = 1 := by simp
  rw [hd₁, one_zpow, one_mul, hd₃, one_zpow, mul_one]
  congr 2
  ext k
  simp [β, Fin.append_right_nil _ _ rfl]

include b₁ in
private theorem bijective_g_of_eq_zero₁ (hm₁ : ∀ q, m₁ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    Function.Bijective (g q).hom := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have := subsingleton_of_eq_zero (b₁ (p + 1)) (hm₁ (p + 1))
  have := subsingleton_of_eq_zero (b₁ p) (hm₁ p)
  have ⟨_, h₂, h₃⟩ := (acyclic_interleave_iff hfg hgδ hδf).1 hI
  exact bijective_of_subsingleton (hfg (p + 1)) (hgδ p) (h₂ (p + 1)) (h₃ p)

include b₁ b₂ b₃ in
/-- When `X₁` vanishes in an acyclic interleaved complex, `g q : X₂ q ⟶ X₃ q` is an isomorphism,
so `m₂ q = m₃ q`. -/
theorem card_eq_of_eq_zero₁ (hm₁ : ∀ q, m₁ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) (q : ℤ) :
    m₂ q = m₃ q := by
  simpa using (finrank_eq_card_basis ((b₂ q).map
    (LinearEquiv.ofBijective _ (bijective_g_of_eq_zero₁ b₁ hm₁ hI q)))).symm.trans
      (finrank_eq_card_basis (b₃ q))

/-- When `X₁` vanishes in a bounded acyclic interleaved complex, the torsion is the alternating
product `∏ᶠ q, det(g q) ^ ((-1) ^ (q + 1))` of the determinants of `g q` in the bases `b₂ q` and
`b₃ q`. -/
theorem reidemeisterTorsion_of_eq_zero₁ (h₂ : {q | m₂ q ≠ 0}.Finite) (hm₁ : ∀ q, m₁ q = 0)
    (hI : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁ b₂ b₃) =
      ∏ᶠ q : ℤ, ((b₃ q).det fun k ↦ (g q).hom (b₂ q
        (Fin.cast (card_eq_of_eq_zero₁ b₁ b₂ b₃ hm₁ hI q).symm k))) ^ ((q + 1).negOnePow : ℤ) := by
  have h₁ : {q | m₁ q ≠ 0}.Finite := by simp [hm₁]
  have h₃ : {q | m₃ q ≠ 0}.Finite :=
    h₂.subset fun q hq h0 ↦ hq ((card_eq_of_eq_zero₁ b₁ b₂ b₃ hm₁ hI q).symm.trans h0)
  have hSub₁ (q : ℤ) : Subsingleton (X₁ q) := subsingleton_of_eq_zero (b₁ q) (hm₁ q)
  have hSubf (q : ℤ) : Subsingleton (LinearMap.range (f q).hom) :=
    subsingleton_range_of_domain (f q).hom
  let α (q : ℤ) : Basis (Fin 0) F (LinearMap.range (δ q).hom) := Basis.empty _
  let β (q : ℤ) : Basis (Fin 0) F (LinearMap.range (f q).hom) := Basis.empty _
  let γ (q : ℤ) := (b₂ q).map
    (LinearEquiv.ofInjective (g q).hom (bijective_g_of_eq_zero₁ b₁ hm₁ hI q).1)
  have hshift : (∏ᶠ q : ℤ, ((b₃ q).det fun k ↦ (g q).hom (b₂ q
      (Fin.cast (card_eq_of_eq_zero₁ b₁ b₂ b₃ hm₁ hI q).symm k))) ^
        ((q + 1).negOnePow : ℤ)) =
    ∏ᶠ j : ℤ, ((b₃ (j + 1)).det fun k ↦ (g (j + 1)).hom (b₂ (j + 1)
      (Fin.cast (card_eq_of_eq_zero₁ b₁ b₂ b₃ hm₁ hI (j + 1)).symm k))) ^
        ((j + 1 + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight (1 : ℤ))).symm
  rw [hshift, reidemeisterTorsion_eq_finprod b₁ b₂ b₃ α β γ h₁ h₂ h₃ hI
    (fun _ ↦ Fin.elim0) (fun _ l ↦ l.elim0) (fun _ ↦ Fin.elim0) (fun _ l ↦ l.elim0)
    (fun q ↦ b₂ q) (fun q l ↦ by simp [γ])]
  refine finprod_congr fun j ↦ ?_
  have : IsEmpty (Fin (m₁ (j + 1))) := hm₁ (j + 1) ▸ inferInstance
  have hd₁ : (b₁ (j + 1)).det
      (Fin.append (fun l : Fin 0 ↦ (α (j + 1) l : X₁ (j + 1))) Fin.elim0 ∘
        Fin.cast (card_eq_add_of_acyclic₁ b₁ α β hI (j + 1))) = 1 := by simp
  have hd₂ : (b₂ (j + 1)).det
      (Fin.append (fun l : Fin 0 ↦ (β (j + 1) l : X₂ (j + 1))) (b₂ (j + 1)) ∘
        Fin.cast (card_eq_add_of_acyclic₂ b₂ β γ hI (j + 1))) = 1 := by
    convert (b₂ (j + 1)).det_self
    ext k
    simp [Fin.append_left_nil _ _ rfl]
  rw [hd₁, one_zpow, one_mul, hd₂, one_zpow, one_mul,
    (Int.negOnePow_eq_iff (j + 1 + 1) j).2 ⟨1, by ring⟩]
  congr 2
  ext k
  simp [γ, Fin.append_right_nil _ _ rfl]

end Specializations

end ChainComplex.interleave
