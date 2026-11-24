/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic

/-!
# Capping with a cocycle as a chain map

Let `D : E ⟶ A ⊗ B` be a diagonal and `a : M ⊗ B ⟶ B'` an action, as for the cap product of
chains and cochains `TauCeti.ChainComplex.capChain`, and let `φ : A_p ⟶ M` be a cocycle of degree
`p`, that is `φ ∘ ∂ = 0`. By the boundary formula `∂(x ⌢ φ) = (-1)^p ∂x ⌢ φ`, capping with `φ`
lowers degrees by `p` and commutes with the differentials up to the sign `(-1)^p`. With the signs
`(-1)^(p q)` on the chains of degree `p + q`, it is therefore a chain map

`E ⟶ B'[p]`,  `x ↦ (-1)^(p q) x ⌢ φ`  for `x ∈ E_{p + q}`,

where `B'[p]` is `B'` placed `p` degrees higher, with zero objects in the degrees below `p`
(Mathlib's `HomologicalComplex.extend` along `ComplexShape.embeddingDownNatAdd p`). This file
constructs it (`TauCeti.ChainComplex.capChainMap`), as the extension
`ComplexShape.Embedding.liftExtend` of the chain map from the degrees `≥ p` of `E` to `B'`.

On homology it is, up to the sign `(-1)^(p q)`, the cap product with the class of `φ`
(`TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom`). So it is a
quasi-isomorphism as soon as `E` is exact below `p` and capping with the class of `φ` is an
isomorphism `H_{p + q}(E) ≅ H_q(B')` in every degree
(`TauCeti.ChainComplex.quasiIso_capChainMap`). This is how a cohomological statement such as the
Thom isomorphism in homology, capping with a Thom class, is promoted to the chain level, where
chain maps can be made equivariant and compared after tensoring with coefficients.

## Main definitions and results

* `TauCeti.ChainComplex.capChainMap`: capping with a cocycle of degree `p`, as a chain map from
  `E` to `B'` shifted up by `p`.
* `TauCeti.ChainComplex.capChainMap_f`: its component in degree `n = p + q`.
* `TauCeti.ChainComplex.capChainMap_naturality`: naturality along maps of diagonals and actions.
* `TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom`: on homology, it is
  the cap product with the class of the cocycle, up to sign.
* `TauCeti.ChainComplex.quasiIso_capChainMap`: it is a quasi-isomorphism when `E` is exact below
  `p` and capping with the class is an isomorphism in every degree.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product and its boundary formula.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Chain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {A B B' E : ChainComplex C ℕ} [A.HasTensor B] {M : C} {k : Type*} [Semiring k] [Linear k C]
  [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') {p : ℕ} {φ : A.X p ⟶ M}

/-- The boundary formula for capping with a cocycle, `∂(x ⌢ φ) = (-1)^p ∂x ⌢ φ`, with the degree
`n'` of the source given as any number equal to `n + 1`. -/
private lemma capChain_comp_d_of_d_comp_eq_zero (hφ : A.d (p + 1) p ≫ φ = 0) (q n n' : ℕ)
    (h : p + q = n) (h' : p + (q + 1) = n') :
    capChain k D a p (q + 1) n' h' φ ≫ B'.d (q + 1) q =
      ((-1 : ℤ) ^ p) • (E.d n' n ≫ capChain k D a p q n h φ) := by
  obtain rfl : n' = n + 1 := by omega
  rw [capChain_comp_d D a p q n h φ, hφ, map_zero, sub_zero]

/-- The cap product does not depend on how its source degree is written: transporting along an
equality of degrees `n = n'` does not change it. -/
@[reassoc]
private lemma eqToHom_comp_capChain (q n n' : ℕ) (h : p + q = n) (h' : p + q = n')
    (hn : E.X n = E.X n') :
    eqToHom hn ≫ capChain k D a p q n' h' φ = capChain k D a p q n h φ := by
  obtain rfl : n = n' := by omega
  rw [eqToHom_refl, Category.id_comp]

variable [HasZeroObject C]

variable (k) in
/-- Capping with a cocycle `φ` of degree `p`, as a chain map from the degrees `≥ p` of `E`,
reindexed from `0`, to `B'`: in degree `q` it is `(-1)^(p q)` times capping with `φ`. -/
private def capChainMapRestriction (hφ : A.d (p + 1) p ≫ φ = 0) :
    E.restriction (embeddingDownNatAdd p) ⟶ B' where
  f q := (E.restrictionXIso (embeddingDownNatAdd p) (embeddingDownNatAdd_f p q)).hom ≫
    (((-1 : ℤ) ^ (p * q)) • capChain k D a p q (q + p) (by omega) φ)
  comm' := by
    rintro _ q rfl
    rw [restriction_d_eq _ _ (embeddingDownNatAdd_f p (q + 1)) (embeddingDownNatAdd_f p q)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Linear.smul_comp,
      capChain_comp_d_of_d_comp_eq_zero D a hφ q (q + p) (q + 1 + p) (by omega) (by omega),
      smul_smul]
    -- the signs: `(-1)^(p (q + 1)) (-1)^p = (-1)^(p q)`
    rw [← pow_add, show p * (q + 1) + p = p * q + 2 * p by ring, pow_add,
      (even_two_mul p).neg_one_pow, mul_one]
    simp only [Preadditive.comp_zsmul]

variable (k) in
/-- **Capping with a cocycle as a chain map.** For a cochain `φ : A_p ⟶ M` with `φ ∘ ∂ = 0`, the
chain map from `E` to `B'` placed `p` degrees higher which sends a chain `x` of degree `p + q` to
`(-1)^(p q) x ⌢ φ` (`TauCeti.ChainComplex.capChainMap_f`); it vanishes in the degrees below `p`,
where the target is zero. -/
def capChainMap (p : ℕ) (φ : A.X p ⟶ M) (hφ : A.d (p + 1) p ≫ φ = 0) :
    E ⟶ B'.extend (embeddingDownNatAdd p) :=
  (embeddingDownNatAdd p).liftExtend (capChainMapRestriction k D a hφ)
    fun _ hj ↦ hj.false_of_isTruncLE.elim

/-- In degree `n = p + q`, capping with a cocycle `φ` of degree `p` as a chain map is
`(-1)^(p q)` times capping with `φ`, followed by the identification of the degree `n` of the
shifted complex with `B'_q`. -/
lemma capChainMap_f (hφ : A.d (p + 1) p ≫ φ = 0) (q n : ℕ) (h : p + q = n) :
    (capChainMap k D a p φ hφ).f n =
      ((-1 : ℤ) ^ (p * q)) • capChain k D a p q n h φ ≫
        (B'.extendXIso (embeddingDownNatAdd p) (by rw [embeddingDownNatAdd_f]; omega)).inv := by
  refine ((embeddingDownNatAdd p).liftExtend_f (capChainMapRestriction k D a hφ)
    (fun _ hj ↦ hj.false_of_isTruncLE.elim)
    (by rw [embeddingDownNatAdd_f]; omega : (embeddingDownNatAdd p).f q = n)).trans ?_
  simp only [capChainMapRestriction, restrictionXIso, eqToIso.inv, eqToIso.hom, Linear.comp_smul,
    Linear.smul_comp, Category.assoc, eqToHom_trans_assoc]
  rw [eqToHom_comp_capChain_assoc D a q n (q + p) h (by omega)]

/-- In degree `n = p + q`, capping with a cocycle `φ` of degree `p` as a chain map, read in
`B'_q`, is `(-1)^(p q)` times capping with `φ`. -/
@[reassoc (attr := simp)]
lemma capChainMap_f_comp_extendXIso_hom (hφ : A.d (p + 1) p ≫ φ = 0) (q n : ℕ) (h : p + q = n) :
    (capChainMap k D a p φ hφ).f n ≫
        (B'.extendXIso (embeddingDownNatAdd p) (by rw [embeddingDownNatAdd_f]; omega)).hom =
      ((-1 : ℤ) ^ (p * q)) • capChain k D a p q n h φ := by
  rw [capChainMap_f D a hφ q n h, Linear.smul_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Naturality of capping with a cocycle as a chain map**, along maps of diagonals and actions:
if chain maps `e : E' ⟶ E`, `f : A' ⟶ A`, `g : B₁ ⟶ B` and `g' : B₁' ⟶ B'` satisfy
`e ≫ D = D' ≫ (f ⊗ g)` and `a' ≫ g' = (M ◁ g) ≫ a`, then capping with a cocycle `φ` after `e` is
capping with its pull-back `φ ∘ f` followed by `g'` on the shifted complexes. -/
lemma capChainMap_naturality {A' B₁ B₁' E' : ChainComplex C ℕ} [A'.HasTensor B₁]
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B₁)
    (a' : ((tensorLeft M).mapHomologicalComplex _).obj B₁ ⟶ B₁') (e : E' ⟶ E) (f : A' ⟶ A)
    (g : B₁ ⟶ B) (g' : B₁' ⟶ B') (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g)
    (ha : a' ≫ g' = ((tensorLeft M).mapHomologicalComplex _).map g ≫ a)
    (hφ : A.d (p + 1) p ≫ φ = 0) :
    e ≫ capChainMap k D a p φ hφ =
      capChainMap k D' a' p (f.f p ≫ φ) (by rw [← f.comm_assoc, hφ, comp_zero]) ≫
        extendMap g' (embeddingDownNatAdd p) := by
  ext n : 1
  by_cases hn : p ≤ n
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [comp_f, comp_f, capChainMap_f D a hφ q _ rfl, capChainMap_f D' a' _ q _ rfl,
      extendMap_f g' (embeddingDownNatAdd p) (i := q) (by rw [embeddingDownNatAdd_f]; omega)]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (capChain k D' a' p q (p + q) rfl (f.f p ≫ φ)),
      capChain_naturality D a D' a' e f g g' hD ha p q (p + q) rfl φ, Category.assoc]
  · -- Below `p` the shifted complex is zero.
    exact (B'.isZero_extend_embeddingDownNatAdd_X (by omega)).eq_of_tgt _ _

end Chain

section Homology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M : C} {k : Type*} [Ring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') {p : ℕ}

/-- **Capping with a cocycle as a chain map computes the cap product on homology**: in degree
`n = p + q`, the map induced on homology by capping with a cocycle `φ` of degree `p`, read in
`H_q(B')`, is `(-1)^(p q)` times the cap product with the class of `φ`. -/
theorem homologyMap_capChainMap_comp_extendHomologyIso_hom (q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) :
    homologyMap (capChainMap k D a p ((A.linearYonedaObj k M).iCycles p φ)
          (d_comp_linearYonedaObj_iCycles p (p + 1) φ)) n ≫
        (B'.extendHomologyIso (embeddingDownNatAdd p)
          (by rw [embeddingDownNatAdd_f]; omega)).hom =
      ((-1 : ℤ) ^ (p * q)) • cap k D a p q n h ((A.linearYonedaObj k M).homologyπ p φ) := by
  have hc : cyclesMap (capChainMap k D a p ((A.linearYonedaObj k M).iCycles p φ)
        (d_comp_linearYonedaObj_iCycles p (p + 1) φ)) n ≫
        (B'.extendCyclesIso (embeddingDownNatAdd p) (by rw [embeddingDownNatAdd_f]; omega)).hom =
      ((-1 : ℤ) ^ (p * q)) • capCycles k D a p q n h φ := by
    rw [← cancel_mono (B'.iCycles q), Category.assoc, extendCyclesIso_hom_iCycles,
      cyclesMap_i_assoc]
    -- The cocycle is an element of the module of cochains, so the component lemma is applied up
    -- to unfolding that module rather than by rewriting.
    refine (congrArg (E.iCycles n ≫ ·) (capChainMap_f_comp_extendXIso_hom D a _ q n h)).trans ?_
    rw [Linear.smul_comp, capCycles_i, Linear.comp_smul]
  rw [← cancel_epi (E.homologyπ n), homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom,
    reassoc_of% hc, Linear.comp_smul, cap_homologyπ, Linear.smul_comp]

/-- **Capping with a cocycle is a quasi-isomorphism** onto the shifted complex when `E` is exact in
the degrees below `p` and capping with the class of the cocycle is an isomorphism
`Hₙ(E) ≅ H_q(B')` whenever `p + q = n`. -/
theorem quasiIso_capChainMap (φ : (A.linearYonedaObj k M).cycles p)
    (hE : ∀ n < p, E.ExactAt n)
    (hcap : ∀ q n (h : p + q = n),
      IsIso (cap k D a p q n h ((A.linearYonedaObj k M).homologyπ p φ))) :
    QuasiIso (capChainMap k D a p ((A.linearYonedaObj k M).iCycles p φ)
      (d_comp_linearYonedaObj_iCycles p (p + 1) φ)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : p ≤ n
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
    -- The sign `(-1)^(p q)` times the cap product is an isomorphism, with the same sign times the
    -- inverse as its inverse.
    have hm : ((-1 : ℤ) ^ (p * q)) * (-1) ^ (p * q) = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have : IsIso (((-1 : ℤ) ^ (p * q)) •
        cap k D a p q (p + q) rfl ((A.linearYonedaObj k M).homologyπ p φ)) :=
      ⟨((-1 : ℤ) ^ (p * q)) • inv (cap k D a p q (p + q) rfl
        ((A.linearYonedaObj k M).homologyπ p φ)), by simp [smul_smul, hm],
        by simp [smul_smul, hm]⟩
    rw [← homologyMap_capChainMap_comp_extendHomologyIso_hom D a q (p + q) rfl φ] at this
    exact IsIso.of_isIso_comp_right _ (B'.extendHomologyIso (embeddingDownNatAdd p)
      ((embeddingDownNatAdd_f p q).trans (add_comm q p))).hom
  · -- Below `p` both homologies vanish: `E` is exact there and the shifted complex is zero.
    exact isIso_of_source_target_iso_zero _
      ((hE n (by omega)).isZero_homology.isoZero)
      ((B'.extend_exactAt (embeddingDownNatAdd p) n fun j ↦ by
        rw [embeddingDownNatAdd_f]; omega).isZero_homology.isoZero)

end Homology

end TauCeti.ChainComplex
