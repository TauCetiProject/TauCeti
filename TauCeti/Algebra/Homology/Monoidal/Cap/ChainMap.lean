/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Embedding.HomEquiv
public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic
import TauCeti.CategoryTheory.Preadditive.NSMul

/-!
# Capping with a cocycle as a chain map

Let `D : E ⟶ A ⊗ B` be a diagonal and `a : M ⊗ B ⟶ B'` an action, as in
`TauCeti.ChainComplex.capChain`, and let `φ` be a cocycle of degree `p` of `Hom(A, M)`. By the
boundary formula `∂(x ⌢ φ) = (-1)^p ∂x ⌢ φ` (`TauCeti.ChainComplex.capChain_comp_d_of_cycles`),
capping with `φ` commutes with the differentials up to the sign `(-1)^p`. Correcting the cap
product `E_{q + p} ⟶ B'_q` by the sign `(-1)^(p q)` therefore gives a chain map from `E` to the
complex `B'` placed `p` degrees higher, with zero objects in the degrees below `p`: the extension
of `B'` along the embedding `q ↦ q + p` of `ComplexShape.down ℕ`
(`TauCeti.ChainComplex.capChainMap`).

On homology this chain map is the cap product with the class of `φ`, up to the same sign
(`TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom`). So it is a
quasi-isomorphism exactly when capping with the class of `φ` is an isomorphism
`H_{p + q}(E) ≅ H_q(B')` in every degree and the homology of `E` vanishes below `p`
(`TauCeti.ChainComplex.quasiIso_capChainMap_iff`). For the singular chains of the Thom pair of a
vector bundle and a cocycle representing a Thom class, this is the chain-level form of the Thom
isomorphism in homology; at the chain level it can be made equivariant for a group acting on the
bundle, which is what computes homology with local coefficients through a covering.

## Main definitions

* `TauCeti.ChainComplex.capChainMap`: capping with a cocycle of degree `p`, with the sign
  `(-1)^(p q)` in degree `q + p`, as a chain map from `E` to `B'` shifted up by `p`.

## Main results

* `TauCeti.ChainComplex.capChainMap_f`: its component in degree `q + p`.
* `TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom`: on homology it is
  `(-1)^(p q)` times the cap product with the class of the cocycle.
* `TauCeti.ChainComplex.quasiIso_capChainMap_iff`: it is a quasi-isomorphism if and only if the
  homology of `E` vanishes below `p` and capping with the class of the cocycle is an isomorphism
  in every degree.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product and its boundary formula.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  {A B B' E : ChainComplex C ℕ} [A.HasTensor B] {M : C} {k : Type*} [Ring k] [Linear k C]
  [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B')

/-- The boundary formula for the cap product with a cocycle `φ` of degree `p`, corrected by the
signs `(-1)^(p q)`: these sign-corrected cap products commute with the differentials. -/
private theorem zsmul_capChain_comp_d (p q n n' : ℕ) (h : p + q = n) (h' : p + (q + 1) = n')
    (φ : (A.linearYonedaObj k M).cycles p) :
    (((-1 : ℤ) ^ (p * (q + 1))) •
        capChain k D a p (q + 1) n' h' ((A.linearYonedaObj k M).iCycles p φ)) ≫ B'.d (q + 1) q =
      E.d n' n ≫ (((-1 : ℤ) ^ (p * q)) •
        capChain k D a p q n h ((A.linearYonedaObj k M).iCycles p φ)) := by
  obtain rfl : n' = n + 1 := by omega
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, capChain_comp_d_of_cycles D a p q n h φ,
    smul_smul, ← pow_add, show p * (q + 1) + p = p * q + 2 * p by ring, pow_add,
    (even_two_mul p).neg_one_pow, mul_one]

variable (k) in
/-- The sign-corrected cap products with a cocycle `φ` of degree `p`, as a chain map from the
restriction of `E` to the degrees at least `p` to `B'`. -/
private def capRestrictionHom (p : ℕ) (φ : (A.linearYonedaObj k M).cycles p) :
    E.restriction (ComplexShape.embeddingDownNatAdd p) ⟶ B' where
  f q := (E.restrictionXIso _ (ComplexShape.embeddingDownNatAdd_f p q)).hom ≫
    (((-1 : ℤ) ^ (p * q)) • capChain k D a p q (q + p) (by omega)
      ((A.linearYonedaObj k M).iCycles p φ))
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [E.restriction_d_eq _ (ComplexShape.embeddingDownNatAdd_f p (j + 1))
      (ComplexShape.embeddingDownNatAdd_f p j)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [zsmul_capChain_comp_d D a p j _ _ _ _ φ]

variable (k) in
/-- **Capping with a cocycle as a chain map.** For a cocycle `φ` of degree `p` of `Hom(A, M)`,
capping with `φ` along the diagonal `D` and the action `a`, with the sign `(-1)^(p q)` in degree
`q + p`, is a chain map from `E` to the complex `B'` placed `p` degrees higher, the extension of
`B'` along the embedding `q ↦ q + p` of `ComplexShape.down ℕ`. It vanishes in the degrees below
`p`, where the extension is zero. -/
def capChainMap (p : ℕ) (φ : (A.linearYonedaObj k M).cycles p) :
    E ⟶ B'.extend (ComplexShape.embeddingDownNatAdd p) :=
  (ComplexShape.embeddingDownNatAdd p).liftExtend (capRestrictionHom k D a p φ)
    ((ComplexShape.embeddingDownNatAdd p).hasLift _)

/-- In degree `n = q + p`, the chain map `capChainMap` is `(-1)^(p q)` times the cap product with
the cocycle, followed by the identification of the extension of `B'` in degree `n` with `B'_q`. -/
theorem capChainMap_f (p q n : ℕ) (h : q + p = n) (φ : (A.linearYonedaObj k M).cycles p) :
    (capChainMap k D a p φ).f n =
      (((-1 : ℤ) ^ (p * q)) • capChain k D a p q n (by omega)
        ((A.linearYonedaObj k M).iCycles p φ)) ≫
        (B'.extendXIso (ComplexShape.embeddingDownNatAdd p) (by simpa using h)).inv := by
  subst h
  rw [capChainMap, ComplexShape.Embedding.liftExtend_f _ _ _ (i := q) (by simp)]
  simp only [capRestrictionHom, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The chain map `capChainMap` is the cap product on homology**, up to sign: in degree
`n = q + p`, followed by the identification of the homology of the extension of `B'` with that of
`B'`, it is `(-1)^(p q)` times the cap product with the class of the cocycle. -/
theorem homologyMap_capChainMap_comp_extendHomologyIso_hom (p q n : ℕ) (h : q + p = n)
    (φ : (A.linearYonedaObj k M).cycles p) :
    homologyMap (capChainMap k D a p φ) n ≫
        (B'.extendHomologyIso (ComplexShape.embeddingDownNatAdd p) (by simpa using h)).hom =
      ((-1 : ℤ) ^ (p * q)) • cap k D a p q n (by omega)
        ((A.linearYonedaObj k M).homologyπ p φ) := by
  rw [← cancel_epi (E.homologyπ n), homologyπ_naturality_assoc,
    homologyπ_extendHomologyIso_hom, Preadditive.comp_zsmul, cap_homologyπ,
    ← Preadditive.zsmul_comp, ← Category.assoc]
  congr 1
  rw [← cancel_mono (B'.iCycles q), Category.assoc, extendCyclesIso_hom_iCycles,
    cyclesMap_i_assoc, capChainMap_f D a p q n h, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Preadditive.zsmul_comp, capCycles_i, Preadditive.comp_zsmul]

/-- **When capping with a cocycle is a quasi-isomorphism.** The chain map `capChainMap` of a cocycle
`φ` of degree `p` is a quasi-isomorphism if and only if the homology of `E` vanishes in the degrees
below `p` and capping with the class of `φ` is an isomorphism `H_{p + q}(E) ≅ H_q(B')` for every
`q`. -/
theorem quasiIso_capChainMap_iff (p : ℕ) (φ : (A.linearYonedaObj k M).cycles p) :
    QuasiIso (capChainMap k D a p φ) ↔ (∀ n < p, IsZero (E.homology n)) ∧
      ∀ q, IsIso (cap k D a p q (p + q) rfl ((A.linearYonedaObj k M).homologyπ p φ)) := by
  have hlow (n : ℕ) (hn : n < p) :
      QuasiIsoAt (capChainMap k D a p φ) n ↔ IsZero (E.homology n) := by
    -- below `p` the extension of `B'` is zero, so its homology vanishes
    have hz : IsZero ((B'.extend (ComplexShape.embeddingDownNatAdd p)).homology n) :=
      (exactAt_iff_isZero_homology _ _).1 (B'.extend_exactAt _ n fun q ↦ by simp; omega)
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ⟨fun _ ↦ hz.of_iso (asIso (homologyMap (capChainMap k D a p φ) n)), fun hE ↦
      isIso_of_source_target_iso_zero _ hE.isoZero hz.isoZero⟩
  have hhigh (q : ℕ) : QuasiIsoAt (capChainMap k D a p φ) (p + q) ↔
      IsIso (cap k D a p q (p + q) rfl ((A.linearYonedaObj k M).homologyπ p φ)) := by
    rw [quasiIsoAt_iff_isIso_homologyMap, ← isIso_comp_right_iff _
      (B'.extendHomologyIso (ComplexShape.embeddingDownNatAdd p) (j := q) (by simp; omega)).hom,
      homologyMap_capChainMap_comp_extendHomologyIso_hom D a p q _ (add_comm q p) φ,
      isIso_zsmul_iff_of_isUnit ((isUnit_one.neg).pow _)]
  refine (quasiIso_iff _).trans ⟨fun h ↦ ⟨fun n hn ↦ (hlow n hn).1 (h n), fun q ↦
    (hhigh q).1 (h (p + q))⟩, fun ⟨h₁, h₂⟩ n ↦ ?_⟩
  rcases lt_or_ge n p with hn | hn
  · exact (hlow n hn).2 (h₁ n hn)
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hhigh q).2 (h₂ q)

end TauCeti.ChainComplex
