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
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Noetherian.Orzech
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ShortComplex.Splitting
import TauCeti.LinearAlgebra.Alternating.Append

/-!
# Multiplicativity of Reidemeister torsion through the long exact homology sequence

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`, with compatible chain bases `(c₁, c₂, c₃)` and arbitrary homology
bases `(h₁, h₂, h₃)`. Its long exact homology sequence is the acyclic chain complex
`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and
`Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`, based by `ChainComplex.interleave.basis`.

This file proves Milnor's multiplicativity theorem (*Whitehead torsion*, Theorem 3.2; Turaev,
Theorem 1.14):

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H, h₁, h₂, h₃)`

(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`), with the Koszul sign

`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im f_*,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim im g_*,ⱼ₊₁) · dim B₁,ⱼ)`

coming from reordering the six blocks of boundaries, homology representatives and boundary lifts in
`S.X₂.X (j + 1)` into those coming from `S.X₁` followed by lifts of those of `S.X₃`.

To prove it, we first choose homology bases `(h₁', h₂', h₃')` adapted to the images of the maps in
the long exact homology sequence. For those bases, the torsion of the interleaved homology sequence
is `1` (`HomologicalComplex.reidemeisterTorsion_interleave_eq_one`), and lifting the connecting
homomorphisms on the nose via `CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_d_eq_of_δ_eq`
produces boundary bases of `S.X₂` for which the bracket in degree `j + 1` factors as the Koszul
sign times the brackets of `S.X₁` and `S.X₃`. Changing from `(h₁', h₂', h₃')` back to `(h₁, h₂, h₃)`
multiplies `τ(S.X₁) · τ(S.X₃)` and `τ(S.X₂)` by the exact determinant factors that make up
`τ(H, h₁, h₂, h₃)` (`HomologicalComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det`).

When `S.X₂` is acyclic, `im f_*` and `im g_*` vanish and `τ(S.X₂, c₂, h₂) = τ(S.X₂, c₂)`
(`HomologicalComplex.reidemeisterTorsion_eq_mul_of_shortExact_acyclic_X₂`). When the sequence
splits with compatible homology bases, the connecting map vanishes and `τ(H) = 1`, giving
`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_splitting` and the biproduct formula
`HomologicalComplex.reidemeisterTorsionWithHomology_biprod`.

## Main declarations

* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`: the
  based long exact homology sequence has nonzero torsion.
* `HomologicalComplex.reidemeisterTorsion_interleave_eq_mul_finprod_det`: basis change for the
  torsion of an interleaved complex.
* `HomologicalComplex.reidemeisterTorsion_interleave_eq_one`: an acyclic bounded interleaved
  complex based by bases adapted to the images of its differentials has torsion `1`.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`: Milnor's
  multiplicativity formula for a short exact sequence of chain complexes with based homology.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_of_shortExact_acyclic_X₂`: specialization to an
  acyclic middle term.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_splitting` and
  `HomologicalComplex.reidemeisterTorsionWithHomology_biprod`: split short exact sequences and
  direct sums with compatible homology bases.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact) {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The long exact homology sequence, based by ordered bases of the homology groups of which only
finitely many are nonempty, has nonzero Reidemeister torsion. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero (h₁ : {i | m₁ i ≠ 0}.Finite)
    (h₂ : {i | m₂ i ≠ 0}.Finite) (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  HomologicalComplex.reidemeisterTorsion_ne_zero _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
    hS.acyclic_homologySequenceComplex

end CategoryTheory.ShortComplex.ShortExact

namespace HomologicalComplex

variable {F : Type*} [Field F]

section Interleave

/-! ### Torsion of interleaved complexes -/

private theorem det_eq_of_iso {M N : ModuleCat F} {r m : ℕ} (e : M ≅ N)
    (c c' : Basis (Fin r) F M) (d d' : Basis (Fin m) F N) (hr : r = m)
    (hc : ∀ i, e.hom (c i) = d (Fin.cast hr i))
    (hc' : ∀ i, e.hom (c' i) = d' (Fin.cast hr i)) :
    c.det c' = d.det d' := by
  have hce : c = (d.map e.symm.toLinearEquiv).reindex (finCongr hr.symm) :=
    Basis.eq_of_apply_eq fun i ↦ e.toLinearEquiv.injective (by
      simpa [Iso.toLinearEquiv_apply] using hc i)
  rw [hce, Basis.det_reindex, Basis.det_map]
  congr 1
  ext j
  simpa [Iso.toLinearEquiv_apply] using hc' (Fin.cast hr.symm j)

private theorem hasFiniteMulSupport_det_zpow_fin {m : ℤ → ℕ} {M : ℤ → ModuleCat F}
    (b b' : ∀ q, Basis (Fin (m q)) F (M q)) (hm : {q | m q ≠ 0}.Finite) (e : ℤ → ℤ) :
    Function.HasFiniteMulSupport fun q : ℤ ↦ (b q).det (b' q) ^ e q :=
  hm.subset <| Function.mulSupport_subset_iff'.2 fun q hq ↦ by
    have : IsEmpty (Fin (m q)) := by rw [show m q = 0 by simpa using hq]; infer_instance
    simp

section BasisChange

variable {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q} {g : ∀ q, X₂ q ⟶ X₃ q}
  {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
  (hδf : ∀ q, δ q ≫ f q = 0) {m₁ m₂ m₃ : ℤ → ℕ}
  (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
  (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
  (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))

/-- Replacing the three families of bases `(b₁, b₂, b₃)` of an interleaved complex by
`(b₁', b₂', b₃')` multiplies its torsion by
`(∏ᶠ q, [b₁' q / b₁ q] ^ ((-1) ^ q)) * (∏ᶠ q, [b₂' q / b₂ q] ^ ((-1) ^ (q + 1))) *
  (∏ᶠ q, [b₃' q / b₃ q] ^ ((-1) ^ q))`. -/
theorem reidemeisterTorsion_interleave_eq_mul_finprod_det :
    (ChainComplex.interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (ChainComplex.interleave.basis hfg hgδ hδf b₁' b₂' b₃') =
      (ChainComplex.interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (ChainComplex.interleave.basis hfg hgδ hδf b₁ b₂ b₃) *
      ((∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ)) *
        (∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ)) *
        (∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ))) := by
  let B := ChainComplex.interleave.basis hfg hgδ hδf b₁ b₂ b₃
  let B' := ChainComplex.interleave.basis hfg hgδ hδf b₁' b₂' b₃'
  by_cases hfin : {n | ChainComplex.interleave.rank m₁ m₂ m₃ n ≠ 0}.Finite
  swap
  · simp [reidemeisterTorsion_of_not_finite _ _ hfin]
  obtain ⟨hfin₁, hfin₂, hfin₃⟩ := ChainComplex.interleave.finite_setOf_rank_ne_zero_iff.1 hfin
  have hsupp := hasFiniteMulSupport_det_zpow_fin B B' hfin fun n ↦ (n.negOnePow : ℤ)
  have h₁ := hasFiniteMulSupport_det_zpow_fin b₁ b₁' hfin₁ fun q ↦ (q.negOnePow : ℤ)
  have h₂ := hasFiniteMulSupport_det_zpow_fin b₂ b₂' hfin₂ fun q ↦ ((q + 1).negOnePow : ℤ)
  have h₃ := hasFiniteMulSupport_det_zpow_fin b₃ b₃' hfin₃ fun q ↦ (q.negOnePow : ℤ)
  rw [reidemeisterTorsion_eq_mul_finprod_det _ B B', ← TauCeti.finprod_int_mul_add 3 hsupp,
    ← finprod_mul_distrib h₁ h₂, ← finprod_mul_distrib (h₁.fun_mul h₂) h₃]
  congr 1
  refine finprod_congr fun q ↦ ?_
  rw [Fin.prod_univ_three]
  have hd₀ : (B ((3 : ℕ) * q + (0 : Fin 3))).det (B' ((3 : ℕ) * q + (0 : Fin 3))) =
      (b₃ q).det (b₃' q) :=
    det_eq_of_iso (ChainComplex.interleave.XIso₃ hfg hgδ hδf _ q (by simp)) _ _ _ _
      (ChainComplex.interleave.rank_of_eq_three_mul (by simp))
      (ChainComplex.interleave.XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by simp))
      (ChainComplex.interleave.XIso₃_hom_basis hfg hgδ hδf b₁' b₂' b₃' (by simp))
  have hd₁ : (B ((3 : ℕ) * q + (1 : Fin 3))).det (B' ((3 : ℕ) * q + (1 : Fin 3))) =
      (b₂ q).det (b₂' q) :=
    det_eq_of_iso (ChainComplex.interleave.XIso₂ hfg hgδ hδf _ q (by simp)) _ _ _ _
      (ChainComplex.interleave.rank_of_eq_three_mul_add_one (by simp))
      (ChainComplex.interleave.XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by simp))
      (ChainComplex.interleave.XIso₂_hom_basis hfg hgδ hδf b₁' b₂' b₃' (by simp))
  have h2 : ((3 : ℕ) : ℤ) * q + ((2 : Fin 3) : ℕ) = 3 * q + 2 := by simp
  have hd₂ : (B ((3 : ℕ) * q + (2 : Fin 3))).det (B' ((3 : ℕ) * q + (2 : Fin 3))) =
      (b₁ q).det (b₁' q) :=
    det_eq_of_iso (ChainComplex.interleave.XIso₁ hfg hgδ hδf _ q h2) _ _ _ _
      (ChainComplex.interleave.rank_of_eq_three_mul_add_two h2)
      (ChainComplex.interleave.XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ h2)
      (ChainComplex.interleave.XIso₁_hom_basis hfg hgδ hδf b₁' b₂' b₃' h2)
  have he₀ : (((3 : ℕ) : ℤ) * q + ((0 : Fin 3) : ℕ)).negOnePow = q.negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨q, by simp; omega⟩
  have he₁ : (((3 : ℕ) : ℤ) * q + ((1 : Fin 3) : ℕ)).negOnePow = (q + 1).negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨q, by simp; omega⟩
  have he₂ : (((3 : ℕ) : ℤ) * q + ((2 : Fin 3) : ℕ)).negOnePow = q.negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨q + 1, by simp; omega⟩
  rw [hd₀, hd₁, hd₂, he₀, he₁, he₂]
  ring

end BasisChange

section Adapted

private theorem map_range_of_iso {M₁ M₂ N₁ N₂ : ModuleCat F} {d : M₁ ⟶ M₂} {φ : N₁ ⟶ N₂}
    (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (hd : d = e₁.hom ≫ φ ≫ e₂.inv) :
    (LinearMap.range φ.hom).map (e₂.symm.toLinearEquiv : N₂ →ₗ[F] M₂) = LinearMap.range d.hom := by
  have h : (e₂.symm.toLinearEquiv : N₂ →ₗ[F] M₂) ∘ₗ φ.hom =
      d.hom ∘ₗ (e₁.symm.toLinearEquiv : N₁ →ₗ[F] M₁) := by
    ext x
    simp [hd]
  rw [← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

private def rangeBasisOfIso {M₁ M₂ N₁ N₂ : ModuleCat F} {d : M₁ ⟶ M₂} {φ : N₁ ⟶ N₂}
    (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (hd : d = e₁.hom ≫ φ ≫ e₂.inv) {R r : ℕ}
    (α₀ : Basis (Fin r) F (LinearMap.range φ.hom)) (hr : R = r) :
    Basis (Fin R) F (LinearMap.range d.hom) :=
  (α₀.reindex (finCongr hr.symm)).map
    ((e₂.symm.toLinearEquiv.submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (map_range_of_iso e₁ e₂ hd)))

private theorem hom_rangeBasisOfIso {M₁ M₂ N₁ N₂ : ModuleCat F} {d : M₁ ⟶ M₂} {φ : N₁ ⟶ N₂}
    (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (hd : d = e₁.hom ≫ φ ≫ e₂.inv) {R r : ℕ}
    (α₀ : Basis (Fin r) F (LinearMap.range φ.hom)) (hr : R = r) (k : Fin R) :
    e₂.hom (rangeBasisOfIso e₁ e₂ hd α₀ hr k : M₂) = α₀ (Fin.cast hr k) := by
  simp only [rangeBasisOfIso, Basis.map_apply, Basis.reindex_apply, finCongr_symm, finCongr_apply,
    LinearEquiv.trans_apply]
  exact e₂.inv_hom_id_apply _

private theorem d_inv_lift_of_iso {M₁ M₂ N₁ N₂ : ModuleCat F} {d : M₁ ⟶ M₂} {φ : N₁ ⟶ N₂}
    (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (hd : d = e₁.hom ≫ φ ≫ e₂.inv) {R r : ℕ}
    (α₀ : Basis (Fin r) F (LinearMap.range φ.hom)) (s₀ : Fin r → N₁)
    (hs₀ : ∀ k, φ.hom (s₀ k) = α₀ k) (hr : R = r) (k : Fin R) :
    d.hom (e₁.inv (s₀ (Fin.cast hr k))) = rangeBasisOfIso e₁ e₂ hd α₀ hr k := by
  apply e₂.toLinearEquiv.injective
  simpa [Iso.toLinearEquiv_apply, hd, hom_rangeBasisOfIso] using
    congrArg e₂.hom (congrArg e₂.inv (hs₀ (Fin.cast hr k)))

private theorem torsionBracket_eq_one_of_iso {C : ChainComplex (ModuleCat F) ℤ} {n : ℤ → ℕ}
    (B : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} (hC : C.ExactAt (j + 1)) {p q m p' q' : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : Fin q → C.X (j + 1)) (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k)
    {M : ModuleCat F} (e : C.X (j + 1) ≅ M) (bM : Basis (Fin m) F M)
    (v₁ : Fin p' → M) (v₀ : Fin q' → M)
    (hn : n (j + 1) = m) (hp : p = p') (hq : q = q') (hm : m = p' + q')
    (hB : ∀ k, e.hom (B (j + 1) k) = bM (Fin.cast hn k))
    (hbM : ⇑bM = Fin.append v₁ v₀ ∘ Fin.cast hm)
    (hb₁ : ∀ k, e.hom (b₁ k : C.X (j + 1)) = v₁ (Fin.cast hp k))
    (hs₀ : ∀ k, e.hom (s k) = v₀ (Fin.cast hq k)) :
    torsionBracket B (by simp) (by simp) hC b₁ b₀ s hs = 1 := by
  have hBe : B (j + 1) = (bM.map e.symm.toLinearEquiv).reindex (finCongr hn.symm) :=
    Basis.eq_of_apply_eq fun k ↦ e.toLinearEquiv.injective (by
      simpa [Iso.toLinearEquiv_apply] using hB k)
  rw [torsionBracket_eq_det_append B _ _ hC b₁ b₀ s hs (by omega), hBe,
    Basis.det_reindex, Basis.det_map]
  suffices ∀ k, e.hom ((Fin.append (fun k ↦ (b₁ k : C.X (j + 1))) s
      (Fin.cast (by omega) ((finCongr hn.symm) k)))) = bM k by
    have hfun : e.symm.toLinearEquiv.symm ∘
        (Fin.append (fun k ↦ (b₁ k : C.X (j + 1))) s ∘ Fin.cast (by omega)) ∘
          ⇑(finCongr hn.symm) = ⇑bM := funext this
    rw [hfun, Basis.det_self]
  subst hp hq
  intro k
  rw [hbM, Function.comp_apply]
  have hcast : Fin.cast (by omega) ((finCongr hn.symm) k) = Fin.cast hm k := Fin.ext (by simp)
  rw [hcast]
  induction Fin.cast hm k using Fin.addCases with
  | left l => simpa using hb₁ l
  | right l => simpa using hs₀ l

/-- An acyclic bounded interleaved complex `ChainComplex.interleave`, based in each degree by a
basis of the image of the incoming map followed by lifts of a basis of the image of the outgoing
map, has Reidemeister torsion `1`. -/
theorem reidemeisterTorsion_interleave_eq_one
    {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q} {g : ∀ q, X₂ q ⟶ X₃ q}
    {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
    (hδf : ∀ q, δ q ≫ f q = 0)
    (hK : (ChainComplex.interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    {m₁ m₂ m₃ u v w : ℤ → ℕ}
    (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))
    (hfin₁ : {q | m₁ q ≠ 0}.Finite) (hfin₂ : {q | m₂ q ≠ 0}.Finite) (hfin₃ : {q | m₃ q ≠ 0}.Finite)
    (α : ∀ q, Basis (Fin (u q)) F (LinearMap.range (δ q).hom))
    (β : ∀ q, Basis (Fin (v q)) F (LinearMap.range (f q).hom))
    (γ : ∀ q, Basis (Fin (w q)) F (LinearMap.range (g q).hom))
    (sα : ∀ q, Fin (u q) → X₃ (q + 1)) (hsα : ∀ q k, (δ q).hom (sα q k) = α q k)
    (sβ : ∀ q, Fin (v q) → X₁ q) (hsβ : ∀ q k, (f q).hom (sβ q k) = β q k)
    (sγ : ∀ q, Fin (w q) → X₂ q) (hsγ : ∀ q k, (g q).hom (sγ q k) = γ q k)
    (hm₁ : ∀ q, m₁ q = u q + v q) (hm₂ : ∀ q, m₂ q = v q + w q)
    (hm₃ : ∀ q, m₃ (q + 1) = w (q + 1) + u q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (α q k : X₁ q)) (sβ q) ∘ Fin.cast (hm₁ q))
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (β q k : X₂ q)) (sγ q) ∘ Fin.cast (hm₂ q))
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (γ (q + 1) k : X₃ (q + 1))) (sα q) ∘ Fin.cast (hm₃ q)) :
    (ChainComplex.interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (ChainComplex.interleave.basis hfg hgδ hδf b₁ b₂ b₃) = 1 := by
  let K := ChainComplex.interleave X₁ X₂ X₃ f g δ hfg hgδ hδf
  let B := ChainComplex.interleave.basis hfg hgδ hδf b₁ b₂ b₃
  -- Assemble the boundary bases and lifts of `K` in each residue class mod `3`.
  let bK (n : ℤ) : Basis (Fin (ChainComplex.interleave.rank u v w n)) F
      (LinearMap.range (K.d (n + 1) n).hom) :=
    if h₀ : n % 3 = 0 then
      rangeBasisOfIso (ChainComplex.interleave.XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega))
        (ChainComplex.interleave.XIso₃ hfg hgδ hδf n (n / 3) (by omega))
        (ChainComplex.interleave_d_eq_of_eq_three_mul hfg hgδ hδf (by omega)) (γ (n / 3))
        (ChainComplex.interleave.rank_of_eq_three_mul (by omega))
    else if h₁ : n % 3 = 1 then
      rangeBasisOfIso (ChainComplex.interleave.XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega))
        (ChainComplex.interleave.XIso₂ hfg hgδ hδf n (n / 3) (by omega))
        (ChainComplex.interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf (by omega)) (β (n / 3))
        (ChainComplex.interleave.rank_of_eq_three_mul_add_one (by omega))
    else
      rangeBasisOfIso (ChainComplex.interleave.XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega))
        (ChainComplex.interleave.XIso₁ hfg hgδ hδf n (n / 3) (by omega))
        (ChainComplex.interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf (by omega)) (α (n / 3))
        (ChainComplex.interleave.rank_of_eq_three_mul_add_two (by omega))
  let sK (n : ℤ) (k : Fin (ChainComplex.interleave.rank u v w n)) : K.X (n + 1) :=
    if h₀ : n % 3 = 0 then
      (ChainComplex.interleave.XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
        (sγ (n / 3) (Fin.cast (ChainComplex.interleave.rank_of_eq_three_mul (by omega)) k))
    else if h₁ : n % 3 = 1 then
      (ChainComplex.interleave.XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
        (sβ (n / 3) (Fin.cast (ChainComplex.interleave.rank_of_eq_three_mul_add_one (by omega)) k))
    else
      (ChainComplex.interleave.XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega)).inv
        (sα (n / 3) (Fin.cast (ChainComplex.interleave.rank_of_eq_three_mul_add_two (by omega)) k))
  have hsK (n : ℤ) (k) : (K.d (n + 1) n).hom (sK n k) = bK n k := by
    dsimp only [bK, sK]
    split_ifs with h₀ h₁
    · exact d_inv_lift_of_iso _ _ _ _ _ (hsγ (n / 3)) _ k
    · exact d_inv_lift_of_iso _ _ _ _ _ (hsβ (n / 3)) _ k
    · exact d_inv_lift_of_iso _ _ _ _ _ (hsα (n / 3)) _ k
  have hbK₀ (n p : ℤ) (hn : n = 3 * p) (k) :
      (ChainComplex.interleave.XIso₃ hfg hgδ hδf n p hn).hom (bK n k) =
        γ p (Fin.cast (ChainComplex.interleave.rank_of_eq_three_mul hn) k) := by
    dsimp only [bK]; split_ifs <;> try omega
    obtain rfl : p = n / 3 := (by omega); exact hom_rangeBasisOfIso _ _ _ _ _ k
  rw [reidemeisterTorsion_eq_finprod
    (ChainComplex.interleave.finite_setOf_rank_ne_zero hfin₁ hfin₂ hfin₃) hK bK sK hsK]
  refine finprod_eq_one_of_forall_eq_one fun j ↦ ?_
  suffices torsionBracket B (by simp) (by simp) (hK (j + 1)) (bK (j + 1)) (bK j) (sK j) (hsK j) =
      1 by rw [this, one_zpow]
  -- Each degree `j + 1` falls in one of the three residue classes `3q + 2`, `3q + 1`, `3(q + 1)`.
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, j + 1 = 3 * q + 2 ∨ j + 1 = 3 * q + 1 ∨ j + 1 = 3 * (q + 1) :=
    ⟨j / 3, by omega⟩
  · exact torsionBracket_eq_one_of_iso B (hK (j + 1)) (bK (j + 1)) (bK j) (sK j) (hsK j)
      (ChainComplex.interleave.XIso₁ hfg hgδ hδf (j + 1) q hq) (b₁ q)
      (fun k ↦ (α q k : X₁ q)) (sβ q)
      (ChainComplex.interleave.rank_of_eq_three_mul_add_two hq)
      (ChainComplex.interleave.rank_of_eq_three_mul_add_two hq)
      (ChainComplex.interleave.rank_of_eq_three_mul_add_one (by omega)) (hm₁ q)
      (ChainComplex.interleave.XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ hq) (hb₁ q)
      (fun k ↦ by
        dsimp only [bK]; split_ifs <;> try omega
        obtain rfl : q = (j + 1) / 3 := (by omega); exact hom_rangeBasisOfIso _ _ _ _ _ k)
      (fun k ↦ by
        dsimp only [sK]; split_ifs <;> try omega
        obtain rfl : q = j / 3 := (by omega); exact Iso.inv_hom_id_apply _ _)
  · exact torsionBracket_eq_one_of_iso B (hK (j + 1)) (bK (j + 1)) (bK j) (sK j) (hsK j)
      (ChainComplex.interleave.XIso₂ hfg hgδ hδf (j + 1) q hq) (b₂ q)
      (fun k ↦ (β q k : X₂ q)) (sγ q)
      (ChainComplex.interleave.rank_of_eq_three_mul_add_one hq)
      (ChainComplex.interleave.rank_of_eq_three_mul_add_one hq)
      (ChainComplex.interleave.rank_of_eq_three_mul (by omega)) (hm₂ q)
      (ChainComplex.interleave.XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ hq) (hb₂ q)
      (fun k ↦ by
        dsimp only [bK]; split_ifs <;> try omega
        obtain rfl : q = (j + 1) / 3 := (by omega); exact hom_rangeBasisOfIso _ _ _ _ _ k)
      (fun k ↦ by
        dsimp only [sK]; split_ifs <;> try omega
        obtain rfl : q = j / 3 := (by omega); exact Iso.inv_hom_id_apply _ _)
  · exact torsionBracket_eq_one_of_iso B (hK (j + 1)) (bK (j + 1)) (bK j) (sK j) (hsK j)
      (ChainComplex.interleave.XIso₃ hfg hgδ hδf (j + 1) (q + 1) hq) (b₃ (q + 1))
      (fun k ↦ (γ (q + 1) k : X₃ (q + 1))) (sα q)
      (ChainComplex.interleave.rank_of_eq_three_mul hq)
      (ChainComplex.interleave.rank_of_eq_three_mul hq)
      (ChainComplex.interleave.rank_of_eq_three_mul_add_two (by omega)) (hm₃ q)
      (ChainComplex.interleave.XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ hq) (hb₃ q)
      (hbK₀ (j + 1) (q + 1) hq)
      (fun k ↦ by
        dsimp only [sK]; split_ifs <;> try omega
        obtain rfl : q = j / 3 := (by omega); exact Iso.inv_hom_id_apply _ _)

end Adapted

end Interleave

section ShortExact

/-! ### Multiplicativity of the torsion with homology bases -/

/-- Exactness of `(ShortComplex.mk φ ψ w)` in `ModuleCat F` makes `0 → range φ → B → range ψ → 0`
exact, so bases of `range φ` and `range ψ` with lifts in `B` assemble into a basis of `B`. -/
private theorem exact_subtype_rangeRestrict_of_exact {A B C : ModuleCat F}
    {φ : A ⟶ B} {ψ : B ⟶ C} {w : φ ≫ ψ = 0} (hex : (ShortComplex.mk φ ψ w).Exact) :
    Function.Exact (LinearMap.range φ.hom).subtype ψ.hom.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hex).symm

private theorem rank_eq_add_of_exact {A B C : ModuleCat F}
    {φ : A ⟶ B} {ψ : B ⟶ C} {w : φ ≫ ψ = 0} (hex : (ShortComplex.mk φ ψ w).Exact)
    {m u v : ℕ} (bB : Basis (Fin m) F B)
    (α : Basis (Fin u) F (LinearMap.range φ.hom))
    (β : Basis (Fin v) F (LinearMap.range ψ.hom))
    (s : Fin v → B) (hs : ∀ k, ψ.hom (s k) = β k) : m = u + v := by
  simpa using Fintype.card_congr (bB.indexEquiv
    ((Basis.ofExactLift (Submodule.injective_subtype _)
      (exact_subtype_rangeRestrict_of_exact hex) α β s
      fun k ↦ Subtype.ext (hs k)).reindex finSumFinEquiv))

private def adaptedFinBasis {A B C : ModuleCat F}
    {φ : A ⟶ B} {ψ : B ⟶ C} {w : φ ≫ ψ = 0} (hex : (ShortComplex.mk φ ψ w).Exact)
    {m u v : ℕ} (bB : Basis (Fin m) F B)
    (α : Basis (Fin u) F (LinearMap.range φ.hom))
    (β : Basis (Fin v) F (LinearMap.range ψ.hom))
    (s : Fin v → B) (hs : ∀ k, ψ.hom (s k) = β k) : Basis (Fin m) F B :=
  ((Basis.ofExactLift (Submodule.injective_subtype _)
    (exact_subtype_rangeRestrict_of_exact hex) α β s
    fun k ↦ Subtype.ext (hs k)).reindex finSumFinEquiv).reindex
    (finCongr (rank_eq_add_of_exact hex bB α β s hs).symm)

private theorem coe_adaptedFinBasis {A B C : ModuleCat F}
    {φ : A ⟶ B} {ψ : B ⟶ C} {w : φ ≫ ψ = 0} (hex : (ShortComplex.mk φ ψ w).Exact)
    {m u v : ℕ} (bB : Basis (Fin m) F B)
    (α : Basis (Fin u) F (LinearMap.range φ.hom))
    (β : Basis (Fin v) F (LinearMap.range ψ.hom))
    (s : Fin v → B) (hs : ∀ k, ψ.hom (s k) = β k) :
    ⇑(adaptedFinBasis hex bB α β s hs) =
      Fin.append (fun k ↦ (α k : B)) s ∘ Fin.cast (rank_eq_add_of_exact hex bB α β s hs) := by
  ext k
  rw [adaptedFinBasis, Basis.reindex_apply, Function.comp_apply,
    Basis.coe_reindex_ofExactLift _ _ α β s (fun k ↦ Subtype.ext (hs k))]
  rfl

private theorem finAppend_comp {α β : Type*} {m n : ℕ} (f : α → β) (u : Fin m → α)
    (v : Fin n → α) :
    Fin.append (fun k ↦ f (u k)) (fun k ↦ f (v k)) = fun k ↦ f (Fin.append u v k) := by
  ext k
  induction k using Fin.addCases <;> simp

private theorem apply_finAppend {α β : Type*} {m n : ℕ} (f : α → β) (u : Fin m → α)
    (v : Fin n → α) (k : Fin (m + n)) :
    f (Fin.append u v k) = Fin.append (fun i ↦ f (u i)) (fun i ↦ f (v i)) k := by
  induction k using Fin.addCases <;> simp

private theorem fun_apply_finAppend_cast {α β : Type*} {m m' n : ℕ} (f : α → β)
    (u : Fin m' → α) (v : Fin n → α) (h : m = m' + n) :
    (fun k ↦ f (Fin.append u v (Fin.cast h k))) =
      Fin.append (fun k ↦ f (u k)) (fun k ↦ f (v k)) ∘ Fin.cast h := by
  ext k
  rw [Function.comp_apply]
  generalize Fin.cast h k = l
  induction l using Fin.addCases <;> simp

private theorem finAppend_fun_cast_left {α : Type*} {a a' b : ℕ} (h : a = a')
    (u : Fin a' → α) (v : Fin b → α) :
    Fin.append (fun k ↦ u (Fin.cast h k)) v =
      fun k ↦ Fin.append u v (Fin.cast (by omega) k) := by
  subst h
  simp

private theorem shift_basis_aux {M : ℤ → ModuleCat F} {m : ℤ → ℕ}
    (b : ∀ q, Basis (Fin (m (q + 1))) F (M (q + 1))) {p q : ℤ} (hp : p = q)
    (hp1 : p + 1 = q + 1) :
    ((b p).reindex (finCongr (congrArg m hp1))).map
      (eqToIso (congrArg M hp1)).toLinearEquiv = b q := by
  subst hp
  have : hp1 = rfl := Subsingleton.elim _ _
  subst this
  ext k
  simp

/-- In degree `j + 1` of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the determinant with
respect to `c₂ (j + 1)` of the six-block family `((x₁, y₁), (x₂, y₂), (x₃, y₃))` made of the
candidate boundaries `(x₁, y₁)`, adapted homology representatives `(x₂, y₂)` and lifts `(x₃, y₃)` is
the Koszul sign `(-1) ^ (p₃' * v' + (p₃' + w') * p₁)` times the product of the brackets of `X₁` and
`X₃`. -/
private theorem det_shortExactWithHomology {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
    {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    {j : ℤ}
    (hf : Function.Injective (S.f.f (j + 1)).hom)
    (hfg : Function.Exact (S.f.f (j + 1)).hom (S.g.f (j + 1)).hom)
    {p₁' u' v' p₁ p₃' w' u p₃ m₁' m₃' : ℕ}
    (b₁_hi : Basis (Fin p₁') F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom))
    (b₁_lo : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (s₁ : Fin p₁ → S.X₁.X (j + 1)) (hs₁ : ∀ k, (S.X₁.d (j + 1) j).hom (s₁ k) = b₁_lo k)
    (h₁_hi : Basis (Fin m₁') F (S.X₁.homology (j + 1))) (hm₁' : m₁' = u' + v')
    (zα_hi : Fin u' → S.X₁.cycles (j + 1)) (zsβ_hi : Fin v' → S.X₁.cycles (j + 1))
    (hy₁ : ∀ k, (S.X₁.homologyπ (j + 1)).hom
      ((Fin.append zα_hi zsβ_hi ∘ Fin.cast hm₁') k) = h₁_hi k)
    (b₃_hi : Basis (Fin p₃') F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom))
    (t_hi : Fin p₃' → S.X₂.X (j + 1 + 1))
    (ht_hi : ∀ k, (S.X₃.d (j + 1 + 1) (j + 1)).hom ((S.g.f (j + 1 + 1)).hom (t_hi k)) = b₃_hi k)
    (b₃_lo : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t_lo : Fin p₃ → S.X₂.X (j + 1))
    (ht_lo : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t_lo k)) = b₃_lo k)
    (h₃_hi : Basis (Fin m₃') F (S.X₃.homology (j + 1))) (hm₃' : m₃' = w' + u)
    (zsγ_hi : Fin w' → S.X₂.cycles (j + 1))
    (r_lo : Fin u → S.X₂.X (j + 1)) (zsα_lo : Fin u → S.X₃.cycles (j + 1))
    (hgr_lo : ∀ k, (S.g.f (j + 1)).hom (r_lo k) = (S.X₃.iCycles (j + 1)).hom (zsα_lo k))
    (hy₃ : ∀ k, (S.X₃.homologyπ (j + 1)).hom
      ((Fin.append (fun k ↦ (cyclesMap S.g (j + 1)).hom (zsγ_hi k)) zsα_lo ∘
        Fin.cast hm₃') k) = h₃_hi k)
    (hN_lhs : n₁ (j + 1) + n₃ (j + 1) =
      (p₁' + u') + p₃' + (v' + w') + (p₁ + (u + p₃))) :
    (c₂ (j + 1)).det
      (Fin.append
        (Fin.append
          (Fin.append
            (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁_hi k))
              (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (zα_hi k))))
            (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t_hi k)))
          (Fin.append
            (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (zsβ_hi k)))
            (fun k ↦ (S.X₂.iCycles (j + 1)).hom (zsγ_hi k))))
        (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁ k)) (Fin.append r_lo t_lo)) ∘
        Fin.cast hN_lhs) =
      (-1 : F) ^ (p₃' * v' + (p₃' + w') * p₁) *
        (torsionBracketWithHomology c₁ b₁_hi h₁_hi _ hy₁ b₁_lo s₁ hs₁ *
          torsionBracketWithHomology c₃ b₃_hi h₃_hi _ hy₃ b₃_lo
            (fun k ↦ (S.g.f (j + 1)).hom (t_lo k)) ht_lo) := by
  have hn₁' := eq_add_add c₁ b₁_hi h₁_hi _ hy₁ b₁_lo s₁ hs₁
  have hn₃' := eq_add_add c₃ b₃_hi h₃_hi _ hy₃ b₃_lo (fun k ↦ (S.g.f (j + 1)).hom (t_lo k)) ht_lo
  have hN : n₁ (j + 1) + n₃ (j + 1) = (p₁' + u') + v' + p₁ + (p₃' + w' + (u + p₃)) := by omega
  rw [torsionBracketWithHomology_eq_det_append c₁ _ _ _ hy₁ _ _ hs₁ hn₁',
    torsionBracketWithHomology_eq_det_append c₃ _ _ _ hy₃ _ _ ht_lo hn₃']
  -- Reorder `((x₁, y₁), (x₂, y₂), (x₃, y₃))` into `((x₁, x₂, x₃), (y₁, y₂, y₃))`.
  have hsw := ((c₂ (j + 1)).reindex (finCongr hN)).det.map_append_append_append_comm
    (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁_hi k))
      (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (zα_hi k))))
    (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (zsβ_hi k)))
    (fun k ↦ (S.f.f (j + 1)).hom (s₁ k))
    (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t_hi k))
    (fun k ↦ (S.X₂.iCycles (j + 1)).hom (zsγ_hi k))
    (Fin.append r_lo t_lo)
  let x₁ := Fin.append (Fin.append (fun k ↦ (b₁_hi k : S.X₁.X (j + 1)))
      (fun k ↦ (S.X₁.iCycles (j + 1)).hom ((Fin.append zα_hi zsβ_hi ∘ Fin.cast hm₁') k))) s₁ ∘
    Fin.cast hn₁'
  let x₃ := Fin.append (Fin.append (fun k ↦ (b₃_hi k : S.X₃.X (j + 1)))
      (fun k ↦ (S.X₃.iCycles (j + 1)).hom
        ((Fin.append (fun k ↦ (cyclesMap S.g (j + 1)).hom (zsγ_hi k)) zsα_lo ∘
          Fin.cast hm₃') k)))
      (fun k ↦ (S.g.f (j + 1)).hom (t_lo k)) ∘ Fin.cast hn₃'
  rw [Basis.det_reindex, Basis.det_reindex] at hsw
  rw [show Fin.cast hN_lhs = Fin.cast (by omega) ∘ finCongr hN from funext fun _ ↦ by simp,
    ← Function.comp_assoc, hsw,
    Basis.eq_reindex_ofExactLift hf hfg (c₁ (j + 1)) (c₃ (j + 1)) (c₂ (j + 1))
      (hc₁ (j + 1)) (hc₃ (j + 1)), Basis.det_reindex,
    Basis.ofExactLift_det_eq_mul _ _ _ _ _ _ x₁ x₃ _ ?_ ?_]
  · simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rfl
  · intro i
    have hl : finCongr hN (finSumFinEquiv (.inl i)) =
        Fin.castAdd (p₃' + w' + (u + p₃)) (Fin.cast (by omega) i) := Fin.ext (by simp)
    rw [Function.comp_apply, Function.comp_apply, hl, Fin.append_left]
    dsimp only [x₁, Function.comp_apply]
    simp only [finAppend_comp (S.f.f (j + 1)).hom,
      fun_apply_finAppend_cast (S.X₁.iCycles (j + 1)).hom, Function.comp_apply,
      Fin.append_assoc, Fin.append_cast_left, Fin.append_cast_right, finAppend_fun_cast_left]
    exact congrArg _ (congrArg _ (Fin.ext rfl))
  · intro i
    have hr : finCongr hN (finSumFinEquiv (.inr i)) =
        Fin.natAdd ((p₁' + u') + v' + p₁) (Fin.cast (by omega) i) := Fin.ext (by simp; omega)
    have hy₁' : (fun k ↦ (S.g.f (j + 1)).hom ((S.X₂.d (j + 1 + 1) (j + 1)).hom (t_hi k))) =
        fun k ↦ (b₃_hi k : S.X₃.X (j + 1)) :=
      funext fun k ↦ (Hom.comm_apply S.g _ _ (t_hi k)).symm.trans (ht_hi k)
    have hy₂' : (fun k ↦ (S.g.f (j + 1)).hom ((S.X₂.iCycles (j + 1)).hom (zsγ_hi k))) =
        fun k ↦ (S.X₃.iCycles (j + 1)).hom ((cyclesMap S.g (j + 1)).hom (zsγ_hi k)) :=
      funext fun k ↦ (S.X₂.moduleCat_iCycles_cyclesMap_apply (j + 1) S.g (zsγ_hi k)).symm
    have hr' : (fun k ↦ (S.g.f (j + 1)).hom (r_lo k)) =
        fun k ↦ (S.X₃.iCycles (j + 1)).hom (zsα_lo k) :=
      funext hgr_lo
    rw [Function.comp_apply, Function.comp_apply, hr, Fin.append_right]
    dsimp only [x₃, Function.comp_apply]
    simp only [apply_finAppend (S.g.f (j + 1)).hom, hy₁', hy₂', hr',
      fun_apply_finAppend_cast (S.X₃.iCycles (j + 1)).hom, Function.comp_apply,
      Fin.append_assoc, Fin.append_cast_left, Fin.append_cast_right]
    exact congrArg _ (Fin.ext (by simp))

/-- If a three-block family `(vB₁, z₂, s₂)` spans `C.X (j + 1)`, where `vB₁` consists of boundaries,
`z₂` of cycles, and `s₂` lifts a boundary family `vB₀`, then `vB₀` spans the boundaries of `C` in
degree `j`. -/
private theorem top_le_span_range_of_span_append {C : ChainComplex (ModuleCat F) ℤ} {j : ℤ}
    {r₁ m r₀ : ℕ}
    (vB₁ : Fin r₁ → LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom)
    (z₂ : Fin m → C.cycles (j + 1))
    (vB₀ : Fin r₀ → LinearMap.range (C.d (j + 1) j).hom)
    (s₂ : Fin r₀ → C.X (j + 1)) (hs₂ : ∀ k, (C.d (j + 1) j).hom (s₂ k) = vB₀ k)
    (hspan : Submodule.span F (Set.range
      (Fin.append (Fin.append (fun k ↦ (vB₁ k : C.X (j + 1)))
        (fun k ↦ (C.iCycles (j + 1)).hom (z₂ k))) s₂)) = ⊤) :
    ⊤ ≤ Submodule.span F (Set.range vB₀) := by
  rintro b -
  obtain ⟨x, rfl⟩ := (C.d (j + 1) j).hom.surjective_rangeRestrict b
  have hx : x ∈ Submodule.span F (Set.range
      (Fin.append (Fin.append (fun k ↦ (vB₁ k : C.X (j + 1)))
        (fun k ↦ (C.iCycles (j + 1)).hom (z₂ k))) s₂)) := hspan.symm ▸ Submodule.mem_top
  have hx' : (C.d (j + 1) j).hom.rangeRestrict x ∈
      Submodule.span F ((C.d (j + 1) j).hom.rangeRestrict '' Set.range
        (Fin.append (Fin.append (fun k ↦ (vB₁ k : C.X (j + 1)))
          (fun k ↦ (C.iCycles (j + 1)).hom (z₂ k))) s₂)) := by
    rw [← LinearMap.map_span]
    exact Submodule.mem_map_of_mem hx
  refine Submodule.span_le.2 ?_ hx'
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  induction k using Fin.addCases with
  | left k =>
    induction k using Fin.addCases with
    | left k =>
      obtain ⟨w, hw⟩ := (vB₁ k).2
      have h0 : (C.d (j + 1) j).hom.rangeRestrict (vB₁ k : C.X (j + 1)) = 0 :=
        Subtype.ext ((congrArg (C.d (j + 1) j).hom hw.symm).trans (C.d_comp_d_apply _ _ _ w))
      simp [h0]
    | right k =>
      have h0 : (C.d (j + 1) j).hom.rangeRestrict ((C.iCycles (j + 1)).hom (z₂ k)) = 0 :=
        Subtype.ext (C.moduleCat_d_iCycles_apply (j + 1) j (z₂ k))
      simp [h0]
  | right k =>
    have hs : (C.d (j + 1) j).hom.rangeRestrict (s₂ k) = vB₀ k := Subtype.ext (hs₂ k)
    simpa [hs] using Submodule.subset_span (s := Set.range vB₀) ⟨k, rfl⟩

/-- If families `vB j` of boundaries, `y i` of cycle representatives of `h i`, and lifts `s j` of
`vB j` satisfy `n (j + 1) = R (j + 1) + m (j + 1) + R j` and have nonzero concatenated determinant
against `c (j + 1)` in every degree, then `vB j` is automatically a basis of the boundaries in
degree `j` and `τ(C, c, h)` is the alternating product of those determinants. -/
private theorem reidemeisterTorsionWithHomology_eq_finprod_det_of_ne_zero
    {C : ChainComplex (ModuleCat F) ℤ} {n m R : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i))
    (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
    (hn : {i | n i ≠ 0}.Finite)
    (vB : ∀ j, Fin (R j) → LinearMap.range (C.d (j + 1) j).hom)
    (y : ∀ i, Fin (m i) → C.cycles i)
    (hy : ∀ i k, (C.homologyπ i).hom (y i k) = h i k)
    (s : ∀ j, Fin (R j) → C.X (j + 1))
    (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = vB j k)
    (hN : ∀ j, n (j + 1) = R (j + 1) + m (j + 1) + R j)
    (hne : ∀ j, (c (j + 1)).det
      (Fin.append (Fin.append (fun k ↦ (vB (j + 1) k : C.X (j + 1)))
        (fun k ↦ (C.iCycles (j + 1)).hom (y (j + 1) k))) (s j) ∘ Fin.cast (hN j)) ≠ 0) :
    C.reidemeisterTorsionWithHomology c h =
      ∏ᶠ j : ℤ, (c (j + 1)).det
        (Fin.append (Fin.append (fun k ↦ (vB (j + 1) k : C.X (j + 1)))
          (fun k ↦ (C.iCycles (j + 1)).hom (y (j + 1) k))) (s j) ∘
          Fin.cast (hN j)) ^ (j.negOnePow : ℤ) := by
  have hspan (j : ℤ) : ⊤ ≤ Submodule.span F (Set.range (vB j)) := by
    have htop := ((c (j + 1)).is_basis_iff_det.mpr (IsUnit.mk0 _ (hne j))).2
    have hsurj : Function.Surjective (Fin.cast (hN j)) := (finCongr (hN j)).surjective
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ] at htop
    exact top_le_span_range_of_span_append (vB (j + 1)) (y (j + 1)) (vB j) (s j) (hs j) htop
  have hle (j : ℤ) : finrank F (LinearMap.range (C.d (j + 1) j).hom) ≤ R j := by
    rw [← finrank_top F (LinearMap.range (C.d (j + 1) j).hom), ← top_le_iff.mp (hspan j)]
    exact (finrank_range_le_card (vB j)).trans_eq (Fintype.card_fin _)
  have hcard (j : ℤ) :
      Fintype.card (Fin (R j)) = finrank F (LinearMap.range (C.d (j + 1) j).hom) := by
    have := hle j; have := hle (j + 1)
    have := finrank_eq_add_add (c := c) (h := h) j; have := hN j
    simp only [Fintype.card_fin]; omega
  let b (j : ℤ) := basisOfTopLeSpanOfCardEqFinrank (vB j) (hspan j) (hcard j)
  have hs' (j : ℤ) (k) : (C.d (j + 1) j).hom (s j k) = b j k := by simp [b, hs]
  rw [reidemeisterTorsionWithHomology_eq_finprod (c := c) (h := h) hn b y hy s hs']
  refine finprod_congr fun j ↦ ?_
  rw [torsionBracketWithHomology_eq_det_append c _ _ _ (hy (j + 1)) _ _ (hs' j) (hN j)]
  simp [b]

/-- If the middle term of a sequence of based complexes is unbounded, then so is one of the outer
terms, so both sides of Milnor's multiplicativity formula vanish. -/
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

/-- For a bounded short exact sequence `S` of complexes, Milnor's multiplicativity formula holds
for the homology bases `(h₁', h₂', h₃')` adapted to the images of the maps in the long exact
homology sequence, where `τ(H, h₁', h₂', h₃') = 1`. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_adapted
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    {u v w : ℤ → ℕ}
    (α : ∀ q, Basis (Fin (u q)) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (β : ∀ q, Basis (Fin (v q)) F (LinearMap.range (homologyMap S.f q).hom))
    (γ : ∀ q, Basis (Fin (w q)) F (LinearMap.range (homologyMap S.g q).hom))
    (sα : ∀ q, Fin (u q) → S.X₃.homology (q + 1))
    (hsα : ∀ q k, (hS.δ (q + 1) q rfl).hom (sα q k) = α q k)
    (sβ : ∀ q, Fin (v q) → S.X₁.homology q)
    (hsβ : ∀ q k, (homologyMap S.f q).hom (sβ q k) = β q k)
    (sγ : ∀ q, Fin (w q) → S.X₂.homology q)
    (hsγ : ∀ q k, (homologyMap S.g q).hom (sγ q k) = γ q k)
    (h₁' : ∀ q, Basis (Fin (m₁ q)) F (S.X₁.homology q))
    (h₂' : ∀ q, Basis (Fin (m₂ q)) F (S.X₂.homology q))
    (h₃' : ∀ q, Basis (Fin (m₃ q)) F (S.X₃.homology q))
    (hm₁ : ∀ q, m₁ q = u q + v q) (hm₂ : ∀ q, m₂ q = v q + w q)
    (hm₃ : ∀ q, m₃ (q + 1) = w (q + 1) + u q)
    (hh₁' : ∀ q, ⇑(h₁' q) =
      Fin.append (fun k ↦ (α q k : S.X₁.homology q)) (sβ q) ∘ Fin.cast (hm₁ q))
    (hh₂' : ∀ q, ⇑(h₂' q) =
      Fin.append (fun k ↦ (β q k : S.X₂.homology q)) (sγ q) ∘ Fin.cast (hm₂ q))
    (hh₃' : ∀ q, ⇑(h₃' (q + 1)) =
      Fin.append (fun k ↦ (γ (q + 1) k : S.X₃.homology (q + 1))) (sα q) ∘ Fin.cast (hm₃ q)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂' =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        v (j + 1) + (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + w (j + 1)) *
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
  -- Choose cycle representatives of `α`, `sβ`, `sγ` and lifts `r` along `δ` and `t` of `B₃`.
  let zα (q : ℤ) (k : Fin (u q)) : S.X₁.cycles q :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective q) (α q k)
  have hzα (q : ℤ) (k) : (S.X₁.homologyπ q).hom (zα q k) = α q k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective q) _
  let zsβ (q : ℤ) (k : Fin (v q)) : S.X₁.cycles q :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective q) (sβ q k)
  have hzsβ (q : ℤ) (k) : (S.X₁.homologyπ q).hom (zsβ q k) = sβ q k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective q) _
  let zsγ (q : ℤ) (k : Fin (w q)) : S.X₂.cycles q :=
    Function.surjInv (S.X₂.moduleCat_homologyπ_surjective q) (sγ q k)
  have hzsγ (q : ℤ) (k) : (S.X₂.homologyπ q).hom (zsγ q k) = sγ q k :=
    Function.surjInv_eq (S.X₂.moduleCat_homologyπ_surjective q) _
  choose r zsα hr hgr hzsα using fun (q : ℤ) (k : Fin (u q)) ↦
    hS.moduleCat_exists_d_eq_of_δ_eq (q + 1) q rfl (sα q k) (zα q k)
      ((hsα q k).trans (hzα q k).symm)
  let b₁ (j : ℤ) := chosenBoundaryBasis S.X₁ c₁ (j + 1) j
  let s₁ (j : ℤ) := chosenBoundaryLift S.X₁ c₁ (j + 1) j
  have hs₁ (j : ℤ) := chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j
  let b₃ (j : ℤ) := chosenBoundaryBasis S.X₃ c₃ (j + 1) j
  let t (j : ℤ) (k : Fin (finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom))) : S.X₂.X (j + 1) :=
    Function.surjInv (hg (j + 1)) (chosenBoundaryLift S.X₃ c₃ (j + 1) j k)
  have ht (j : ℤ) (k) : (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t j k)) = b₃ j k := by
    rw [Function.surjInv_eq (hg (j + 1)), chosenBoundaryLift_spec]
  -- Cycle families representing `h₁'`, `h₂'`, `h₃'`.
  let y₁ (q : ℤ) := Fin.append (zα q) (zsβ q) ∘ Fin.cast (hm₁ q)
  have hy₁ (q : ℤ) (k) : (S.X₁.homologyπ q).hom (y₁ q k) = h₁' q k := by
    dsimp only [y₁, Function.comp_apply]
    rw [congrFun (hh₁' q) k, Function.comp_apply]
    generalize Fin.cast (hm₁ q) k = l
    induction l using Fin.addCases with
    | left l => simpa using hzα q l
    | right l => simpa using hzsβ q l
  let y₂ (q : ℤ) :=
    Fin.append (fun k ↦ (cyclesMap S.f q).hom (zsβ q k)) (zsγ q) ∘ Fin.cast (hm₂ q)
  have hy₂ (q : ℤ) (k) : (S.X₂.homologyπ q).hom (y₂ q k) = h₂' q k := by
    dsimp only [y₂, Function.comp_apply]
    rw [congrFun (hh₂' q) k, Function.comp_apply]
    generalize Fin.cast (hm₂ q) k = l
    induction l using Fin.addCases with
    | left l =>
      simpa using (moduleCat_homologyMap_homologyπ S.f q (zsβ q l)).symm.trans
        ((congrArg (homologyMap S.f q).hom (hzsβ q l)).trans (hsβ q l))
    | right l => simpa using hzsγ q l
  let y₃_succ (q : ℤ) :=
    Fin.append (fun k ↦ (cyclesMap S.g (q + 1)).hom (zsγ (q + 1) k)) (zsα q) ∘ Fin.cast (hm₃ q)
  have hy₃_succ (q : ℤ) (k) : (S.X₃.homologyπ (q + 1)).hom (y₃_succ q k) = h₃' (q + 1) k := by
    dsimp only [y₃_succ, Function.comp_apply]
    rw [congrFun (hh₃' q) k, Function.comp_apply]
    generalize Fin.cast (hm₃ q) k = l
    induction l using Fin.addCases with
    | left l =>
      simpa using (moduleCat_homologyMap_homologyπ S.g (q + 1) (zsγ (q + 1) l)).symm.trans
        ((congrArg (homologyMap S.g (q + 1)).hom (hzsγ (q + 1) l)).trans (hsγ (q + 1) l))
    | right l => simp [hzsα]
  let y₃ (i : ℤ) : Fin (m₃ i) → S.X₃.cycles i := fun k ↦
    Function.surjInv (S.X₃.moduleCat_homologyπ_surjective i) (h₃' i k)
  have hy₃ (i : ℤ) (k) : (S.X₃.homologyπ i).hom (y₃ i k) = h₃' i k :=
    Function.surjInv_eq (S.X₃.moduleCat_homologyπ_surjective i) _
  -- Candidate boundary family `vB j` and lifts `s₂ j` in `S.X₂`.
  let vB (j : ℤ) : Fin ((finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom) + u j) +
      finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom)) →
      LinearMap.range (S.X₂.d (j + 1) j).hom :=
    Fin.append
      (Fin.append
        (fun k ↦ ⟨(S.f.f j).hom (b₁ j k), (S.f.f (j + 1)).hom (s₁ j k),
          by rw [Hom.comm_apply, hs₁]⟩)
        (fun k ↦ ⟨(S.f.f j).hom ((S.X₁.iCycles j).hom (zα j k)), r j k, hr j k⟩))
      (fun k ↦ ⟨(S.X₂.d (j + 1) j).hom (t j k), t j k, rfl⟩)
  let s₂ (j : ℤ) : Fin ((finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom) + u j) +
      finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom)) → S.X₂.X (j + 1) :=
    Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁ j k)) (Fin.append (r j) (t j)) ∘
      Fin.cast (by omega)
  have hs₂ (j : ℤ) (k) : (S.X₂.d (j + 1) j).hom (s₂ j k) = vB j k := by
    have hlen : finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom) +
        (u j + finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom)) =
        (finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom) + u j) +
          finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom) := by omega
    obtain ⟨l, rfl⟩ := (finCongr hlen).surjective k
    dsimp only [s₂, vB, Function.comp_apply]
    have hc : Fin.cast (by omega) (finCongr hlen l) = l := Fin.ext (by simp)
    rw [hc]
    induction l using Fin.addCases with
    | left l =>
      rw [Fin.append_left]
      exact (Hom.comm_apply S.f (j + 1) j (s₁ j l)).trans
        ((congrArg (S.f.f j).hom (hs₁ j l)).trans (by simp [b₁, Fin.append_assoc]))
    | right l =>
      rw [Fin.append_right]
      induction l using Fin.addCases with
      | left l => simpa [Fin.append_assoc] using hr j l
      | right l => simp [Fin.append_assoc]
  -- Evaluate the determinant of `(vB (j + 1), y₂ (j + 1), s₂ j)` against `c₂ (j + 1)`.
  have hN_lhs (j : ℤ) : n₁ (j + 1) + n₃ (j + 1) =
      ((finrank F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom) + u (j + 1)) +
        finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom)) +
        m₂ (j + 1) +
        ((finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom) + u j) +
          finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom)) := by
    have := finrank_eq_add_add (c := c₁) (h := h₁') j
    have := finrank_eq_add_add (c := c₃) (h := h₃') j
    have := hm₁ (j + 1); have := hm₂ (j + 1); have := hm₃ j; omega
  have hdet (j : ℤ) : (c₂ (j + 1)).det
      (Fin.append (Fin.append (fun k ↦ (vB (j + 1) k : S.X₂.X (j + 1)))
        (fun k ↦ (S.X₂.iCycles (j + 1)).hom (y₂ (j + 1) k))) (s₂ j) ∘ Fin.cast (hN_lhs j)) =
      (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * v (j + 1) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + w (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) *
        (torsionBracketWithHomology c₁ (b₁ (j + 1)) (h₁' (j + 1)) (y₁ (j + 1)) (hy₁ (j + 1))
          (b₁ j) (s₁ j) (hs₁ j) *
          torsionBracketWithHomology c₃ (b₃ (j + 1)) (h₃' (j + 1)) (y₃ (j + 1)) (hy₃ (j + 1))
            (b₃ j) (fun k ↦ (S.g.f (j + 1)).hom (t j k)) (ht j)) := by
    have hbr₃ : torsionBracketWithHomology c₃ (b₃ (j + 1)) (h₃' (j + 1)) (y₃_succ j) (hy₃_succ j)
        (b₃ j) (fun k ↦ (S.g.f (j + 1)).hom (t j k)) (ht j) =
        torsionBracketWithHomology c₃ (b₃ (j + 1)) (h₃' (j + 1)) (y₃ (j + 1)) (hy₃ (j + 1))
          (b₃ j) (fun k ↦ (S.g.f (j + 1)).hom (t j k)) (ht j) := by
      rw [torsionBracketWithHomology_eq_mul c₃ (b₃ (j + 1)) (h₃' (j + 1)) (y₃ (j + 1))
        (hy₃ (j + 1)) (b₃ j) _ (ht j)]
      simp [Basis.det_self]
    rw [← hbr₃]
    dsimp only [y₁, y₃_succ]
    rw [← det_shortExactWithHomology c₁ c₃ c₂ hc₁ hc₃ (hf (j + 1)) (hfg (j + 1))
      (b₁ (j + 1)) (b₁ j) (s₁ j) (hs₁ j) (h₁' (j + 1)) (hm₁ (j + 1)) (zα (j + 1)) (zsβ (j + 1))
      (hy₁ (j + 1)) (b₃ (j + 1)) (t (j + 1)) (ht (j + 1)) (b₃ j) (t j) (ht j) (h₃' (j + 1))
      (hm₃ j) (zsγ (j + 1)) (r j) (zsα j) (hgr j) (hy₃_succ j)
      (by have := hm₂ (j + 1); have := hN_lhs j; omega)]
    have hvB : (fun k ↦ (vB (j + 1) k : S.X₂.X (j + 1))) =
        Fin.append
          (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁ (j + 1) k))
            (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (zα (j + 1) k))))
          (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t (j + 1) k)) := by
      dsimp only [vB]
      rw [← finAppend_comp Subtype.val, ← finAppend_comp Subtype.val]
    have hy₂' : (fun k ↦ (S.X₂.iCycles (j + 1)).hom (y₂ (j + 1) k)) =
        Fin.append
          (fun k ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (zsβ (j + 1) k)))
          (fun k ↦ (S.X₂.iCycles (j + 1)).hom (zsγ (j + 1) k)) ∘ Fin.cast (hm₂ (j + 1)) := by
      dsimp only [y₂, Function.comp_apply]
      rw [fun_apply_finAppend_cast (S.X₂.iCycles (j + 1)).hom]
      simp only [S.X₁.moduleCat_iCycles_cyclesMap_apply (j + 1) S.f]
    congr 1
    rw [hvB, hy₂']
    dsimp only [s₂]
    ext k
    simp only [Fin.append_cast_left, Fin.append_cast_right, Function.comp_apply]
    exact congrArg _ (Fin.ext (by simp))
  have hne (j : ℤ) : (c₂ (j + 1)).det
      (Fin.append (Fin.append (fun k ↦ (vB (j + 1) k : S.X₂.X (j + 1)))
        (fun k ↦ (S.X₂.iCycles (j + 1)).hom (y₂ (j + 1) k))) (s₂ j) ∘ Fin.cast (hN_lhs j)) ≠ 0 := by
    rw [hdet j]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (torsionBracketWithHomology_ne_zero c₁ _ _ _ _ _ _ _)
        (torsionBracketWithHomology_ne_zero c₃ _ _ _ _ _ _ _))
  have hτ₁ := hasFiniteMulSupport_torsionBracketWithHomology (c := c₁) (h := h₁') hn₁
    b₁ y₁ hy₁ s₁ hs₁
  have hτ₃ := hasFiniteMulSupport_torsionBracketWithHomology (c := c₃) (h := h₃') hn₃
    b₃ y₃ hy₃ (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht
  have hε₁ : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * v (j + 1)) :=
    (hasFiniteMulSupport_neg_one_pow_finrank_mul S.X₃ c₃ hn₃ v).preimage
      (add_left_injective 1).injOn
  have hε₂ : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ ((finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + w (j + 1)) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) := by
    simpa only [Nat.mul_comm] using hasFiniteMulSupport_neg_one_pow_finrank_mul S.X₁ c₁ hn₁
      fun j ↦ finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + w (j + 1)
  have hε : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * v (j + 1) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + w (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) := by
    simpa only [pow_add] using hε₁.fun_mul hε₂
  rw [reidemeisterTorsionWithHomology_eq_finprod_det_of_ne_zero c₂ h₂' hn vB y₂ hy₂ s₂ hs₂
      hN_lhs hne,
    reidemeisterTorsionWithHomology_eq_finprod (c := c₁) (h := h₁') hn₁ b₁ y₁ hy₁ s₁ hs₁,
    reidemeisterTorsionWithHomology_eq_finprod (c := c₃) (h := h₃') hn₃ b₃ y₃ hy₃
      (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht,
    ← finprod_mul_distrib hτ₁ hτ₃, ← finprod_mul_distrib hε (hτ₁.fun_mul hτ₃)]
  refine finprod_congr fun j ↦ ?_
  rw [hdet j, mul_zpow, mul_zpow]
  congr 1
  rcases Int.units_eq_one_or j.negOnePow with hj | hj <;> simp [hj, ← inv_pow]

/-- **Milnor's multiplicativity theorem for Reidemeister torsion.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over a field `F`, with compatible chain bases `(c₁, c₂, c₃)` and arbitrary homology bases
`(h₁, h₂, h₃)`. Then

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H, h₁, h₂, h₃)`,

where `H` is the acyclic long exact homology sequence `hS.homologySequenceComplex`, based by
`(h₁, h₂, h₃)`, and

`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im f_*,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim im g_*,ⱼ₊₁) · dim B₁,ⱼ)`.

This holds unconditionally: when `S.X₂` is unbounded, so is `S.X₁` or `S.X₃`, and both sides
are `0`. -/
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
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hfin₁ := finite_setOf_homology_ne_zero (c := c₁) (h := h₁) hn₁
  have hfin₂ := finite_setOf_homology_ne_zero (c := c₂) (h := h₂) hn
  have hfin₃ := finite_setOf_homology_ne_zero (c := c₃) (h := h₃) hn₃
  have : ∀ i, Module.Finite F (S.X₁.homology i) := fun i ↦ .of_basis (h₁ i)
  have : ∀ i, Module.Finite F (S.X₂.homology i) := fun i ↦ .of_basis (h₂ i)
  have : ∀ i, Module.Finite F (S.X₃.homology i) := fun i ↦ .of_basis (h₃ i)
  -- Build bases `(h₁', h₂', h₃')` adapted to the images in the long exact homology sequence.
  let α (q : ℤ) := finBasis F (LinearMap.range (hS.δ (q + 1) q rfl).hom)
  let β (q : ℤ) := finBasis F (LinearMap.range (homologyMap S.f q).hom)
  let γ (q : ℤ) := finBasis F (LinearMap.range (homologyMap S.g q).hom)
  let sα (q : ℤ) (k) : S.X₃.homology (q + 1) :=
    Function.surjInv (hS.δ (q + 1) q rfl).hom.surjective_rangeRestrict (α q k)
  have hsα (q : ℤ) (k) : (hS.δ (q + 1) q rfl).hom (sα q k) = α q k :=
    congrArg Subtype.val (Function.surjInv_eq (hS.δ (q + 1) q rfl).hom.surjective_rangeRestrict _)
  let sβ (q : ℤ) (k) : S.X₁.homology q :=
    Function.surjInv (homologyMap S.f q).hom.surjective_rangeRestrict (β q k)
  have hsβ (q : ℤ) (k) : (homologyMap S.f q).hom (sβ q k) = β q k :=
    congrArg Subtype.val (Function.surjInv_eq (homologyMap S.f q).hom.surjective_rangeRestrict _)
  let sγ (q : ℤ) (k) : S.X₂.homology q :=
    Function.surjInv (homologyMap S.g q).hom.surjective_rangeRestrict (γ q k)
  have hsγ (q : ℤ) (k) : (homologyMap S.g q).hom (sγ q k) = γ q k :=
    congrArg Subtype.val (Function.surjInv_eq (homologyMap S.g q).hom.surjective_rangeRestrict _)
  let h₁' (q : ℤ) := adaptedFinBasis (hS.homology_exact₁ (q + 1) q rfl) (h₁ q) (α q) (β q)
    (sβ q) (hsβ q)
  let h₂' (q : ℤ) := adaptedFinBasis (hS.homology_exact₂ q) (h₂ q) (β q) (γ q) (sγ q) (hsγ q)
  let h₃'_succ (q : ℤ) := adaptedFinBasis (hS.homology_exact₃ (q + 1) q rfl) (h₃ (q + 1))
    (γ (q + 1)) (α q) (sα q) (hsα q)
  let h₃' (i : ℤ) : Basis (Fin (m₃ i)) F (S.X₃.homology i) :=
    ((h₃'_succ (i - 1)).reindex (finCongr (congrArg m₃ (sub_add_cancel i 1)))).map
      (eqToIso (congrArg (fun k ↦ S.X₃.homology k) (sub_add_cancel i 1)) :
        S.X₃.homology (i - 1 + 1) ≅ S.X₃.homology i).toLinearEquiv
  have hh₃'_eq (q : ℤ) : h₃' (q + 1) = h₃'_succ q :=
    shift_basis_aux (M := fun k ↦ S.X₃.homology k) h₃'_succ
      (add_sub_cancel_right q 1) (sub_add_cancel (q + 1) 1)
  have hm₁ (q : ℤ) := rank_eq_add_of_exact (hS.homology_exact₁ (q + 1) q rfl) (h₁ q) (α q) (β q)
    (sβ q) (hsβ q)
  have hm₂ (q : ℤ) := rank_eq_add_of_exact (hS.homology_exact₂ q) (h₂ q) (β q) (γ q)
    (sγ q) (hsγ q)
  have hm₃ (q : ℤ) := rank_eq_add_of_exact (hS.homology_exact₃ (q + 1) q rfl) (h₃ (q + 1))
    (γ (q + 1)) (α q) (sα q) (hsα q)
  have hh₁' (q : ℤ) := coe_adaptedFinBasis (hS.homology_exact₁ (q + 1) q rfl) (h₁ q) (α q) (β q)
    (sβ q) (hsβ q)
  have hh₂' (q : ℤ) := coe_adaptedFinBasis (hS.homology_exact₂ q) (h₂ q) (β q) (γ q)
    (sγ q) (hsγ q)
  have hh₃' (q : ℤ) : ⇑(h₃' (q + 1)) =
      Fin.append (fun k ↦ (γ (q + 1) k : S.X₃.homology (q + 1))) (sα q) ∘ Fin.cast (hm₃ q) := by
    rw [hh₃'_eq]
    exact coe_adaptedFinBasis (hS.homology_exact₃ (q + 1) q rfl) (h₃ (q + 1)) (γ (q + 1)) (α q)
      (sα q) (hsα q)
  -- For `(h₁', h₂', h₃')` the homology sequence has torsion `1`; change back to `(h₁, h₂, h₃)`.
  have hH₁ : hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ h₁' h₂' h₃') = 1 :=
    reidemeisterTorsion_interleave_eq_one _ _ _ hS.acyclic_homologySequenceComplex h₁' h₂' h₃'
      hfin₁ hfin₂ hfin₃ α β γ sα hsα sβ hsβ sγ hsγ hm₁ hm₂ hm₃ hh₁' hh₂' hh₃'
  have hcng {m : ℤ → ℕ} {M : ℤ → ModuleCat F} (b b' : ∀ q, Basis (Fin (m q)) F (M q)) :
      ∏ᶠ q : ℤ, (b q).det (b' q) ^ ((q + 1).negOnePow : ℤ) =
        ∏ᶠ q : ℤ, (b' q).det (b q) ^ (q.negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      have hinv : (b q).det (b' q) = ((b' q).det (b q))⁻¹ :=
        eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
      rw [hinv, Int.negOnePow_succ, Units.val_neg, zpow_neg, inv_zpow, inv_inv]
  rw [reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₂) (h := h₂') h₂,
    reidemeisterTorsionWithHomology_eq_mul_adapted hS c₁ c₃ c₂ hc₁ hc₃ hn α β γ sα hsα sβ hsβ
      sγ hsγ h₁' h₂' h₃' hm₁ hm₂ hm₃ hh₁' hh₂' hh₃',
    reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₁) (h := h₁) h₁',
    reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₃) (h := h₃) h₃',
    hcng h₁ h₁', hcng h₃ h₃',
    reidemeisterTorsion_interleave_eq_mul_finprod_det _ _ _ h₁' h₁ h₂' h₂ h₃' h₃, hH₁, one_mul]
  ring

/-- Specialization of Milnor's multiplicativity formula when the middle complex `S.X₂` is acyclic:
`τ(S.X₂, c₂) = (∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim B₁,ⱼ)) · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H)`. -/
theorem reidemeisterTorsion_eq_mul_of_shortExact_acyclic_X₂
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) (h₂_ac : S.X₂.Acyclic)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsion c₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃)) := by
  rw [← reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₂) (h := h₂) h₂_ac,
    reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ h₁ h₂ h₃]
  congr 1
  refine finprod_congr fun j ↦ ?_
  have : Subsingleton (S.X₂.homology (j + 1)) :=
    ModuleCat.subsingleton_of_isZero (h₂_ac (j + 1)).isZero_homology
  have : Subsingleton (LinearMap.range (homologyMap S.g (j + 1)).hom) :=
    (homologyMap S.g (j + 1)).hom.surjective_rangeRestrict.subsingleton
  have hv : finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) = 0 :=
    finrank_zero_of_subsingleton
  have hw : finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) = 0 :=
    finrank_zero_of_subsingleton
  simp [hv, hw]

end ShortExact

section Splitting

/-! ### Split short exact sequences and direct sums with based homology -/

/-- **Torsion with homology bases of a split short exact sequence.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a split short exact sequence of chain complexes of vector spaces,
with compatible chain bases `(c₁, c₂, c₃)` and compatible homology bases `(h₁, h₂, h₃)`. Then the
connecting map vanishes and `τ(H) = 1`, so

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃)`

with `ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · m₁(j + 1) + (dim B₃,ⱼ₊₁ + m₃(j + 1)) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_splitting
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (σ : S.Splitting)
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
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * m₁ (j + 1) +
          (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + m₃ (j + 1)) *
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · simpa using reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂ h₃ hn _ 1
  have hinj (q : ℤ) : Function.Injective (homologyMap S.f q).hom :=
    Function.LeftInverse.injective (g := (homologyMap σ.r q).hom) fun x ↦ by
      rw [← ModuleCat.comp_apply, ← homologyMap_comp, σ.f_r, homologyMap_id, ModuleCat.id_apply]
  have hsurj (q : ℤ) : Function.Surjective (homologyMap S.g q).hom :=
    Function.RightInverse.surjective (g := (homologyMap σ.s q).hom) fun x ↦ by
      rw [← ModuleCat.comp_apply, ← homologyMap_comp, σ.s_g, homologyMap_id, ModuleCat.id_apply]
  have hδ (q : ℤ) : LinearMap.range (σ.shortExact.δ (q + 1) q rfl).hom = ⊥ :=
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
      (σ.shortExact.homology_exact₁ (q + 1) q rfl)).trans (LinearMap.ker_eq_bot.2 (hinj q))
  have hsub (q : ℤ) : Subsingleton ↑(LinearMap.range (σ.shortExact.δ (q + 1) q rfl).hom) := by
    rw [hδ q]; infer_instance
  let α (q : ℤ) : Basis (Fin 0) F (LinearMap.range (σ.shortExact.δ (q + 1) q rfl).hom) :=
    Basis.empty _
  let β (q : ℤ) : Basis (Fin (m₁ q)) F (LinearMap.range (homologyMap S.f q).hom) :=
    (h₁ q).map (LinearEquiv.ofInjective (homologyMap S.f q).hom (hinj q))
  let γ (q : ℤ) : Basis (Fin (m₃ q)) F (LinearMap.range (homologyMap S.g q).hom) :=
    (h₃ q).map (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 (hsurj q))).symm
  have hm₁ (q : ℤ) : m₁ q = 0 + m₁ q := (Nat.zero_add _).symm
  have hm₃ (q : ℤ) : m₃ (q + 1) = m₃ (q + 1) + 0 := (Nat.add_zero _).symm
  refine reidemeisterTorsionWithHomology_eq_mul_adapted σ.shortExact c₁ c₃ c₂ hc₁ hc₃ hn α β γ
    (fun _ ↦ Fin.elim0) (fun _ k ↦ k.elim0) (fun q ↦ ⇑(h₁ q)) (fun q k ↦ by simp [β])
    (fun q k ↦ h₂ q (Fin.natAdd (m₁ q) k)) (fun q k ↦ by simp [γ, hh₃])
    h₁ h₂ h₃ hm₁ (fun _ ↦ rfl) hm₃ (fun q ↦ ?_) (fun q ↦ ?_) (fun q ↦ ?_)
  · ext k
    rw [Function.comp_apply, show Fin.cast (hm₁ q) k = Fin.natAdd 0 k from Fin.ext (by simp),
      Fin.append_right]
  · ext k
    induction k using Fin.addCases <;> simp [β, hh₁]
  · ext k
    rw [Function.comp_apply, show Fin.cast (hm₃ q) k = Fin.castAdd 0 k from Fin.ext (by simp),
      Fin.append_left]
    simp [γ]

/-- **Torsion with homology bases of a direct sum.** The torsion of the biproduct `C₁ ⊞ C₃` of two
based complexes with based homology, based by `biprodXBasis` on chains and `biprodHomologyBasis` on
homology, is `ε · τ(C₁, c₁, h₁) · τ(C₃, c₃, h₃)` with
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · m₁(j + 1) + (dim B₃,ⱼ₊₁ + m₃(j + 1)) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_biprod
    {C₁ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i)) :
    (C₁ ⊞ C₃).reidemeisterTorsionWithHomology
        (fun i ↦ (biprodXBasis (c₁ i) (c₃ i)).reindex finSumFinEquiv)
        (fun i ↦ (biprodHomologyBasis (h₁ i) (h₃ i)).reindex finSumFinEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) * m₁ (j + 1) +
          (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) + m₃ (j + 1)) *
            finrank F (LinearMap.range (C₁.d (j + 1) j).hom))) *
      (C₁.reidemeisterTorsionWithHomology c₁ h₁ *
        C₃.reidemeisterTorsionWithHomology c₃ h₃) :=
  reidemeisterTorsionWithHomology_eq_mul_of_splitting
    (ShortComplex.Splitting.ofHasBinaryBiproduct C₁ C₃) c₁ c₃ _
    (by simp) (by simp [← ModuleCat.comp_apply]) h₁ h₃ _
    (by simp) (by simp [← ModuleCat.comp_apply, ← homologyMap_comp])

end Splitting

end HomologicalComplex
