/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.ModuleCat
public import TauCeti.Algebra.Homology.Monoidal.TensorCochain

/-!
# Cap products of chains and cochains along a diagonal

Let `C` be a `k`-linear preadditive monoidal category, let `A`, `B`, `B'` and `E` be chain
complexes in `C` indexed by `ℕ` such that the tensor product `A ⊗ B` exists, let
`D : E ⟶ A ⊗ B` be a chain map (a
*diagonal*), and let `a : M ⊗ B ⟶ B'` be a chain map from the complex `B` tensored on the left by
an object `M` (an *action* of the coefficient object `M` on `B`).  A cochain `φ : A_p ⟶ M` then
caps a chain of `E` of degree `n = p + q` to a chain of `B'` of degree `q`: the cap product
`E_n ⟶ B'_q` is the degree-`n` component of `D`, followed by the projection of `(A ⊗ B)_n` onto
its summand `A_p ⊗ B_q`, by `φ ▷ B_q` and by `a`.  In terms of the tensor product of cochains
`TauCeti.ChainComplex.tensorCochain`, it is `D ≫ tensorCochain a φ (𝟙 B_q)`.

Since `D` and `a` are chain maps and the tensor product carries the Koszul signs, the cap product
satisfies the boundary formula `∂(x ⌢ φ) = (-1)^p (∂x ⌢ φ - x ⌢ δφ)`, where `δφ = φ ∘ ∂`.  When `C`
is moreover abelian, capping with a cocycle sends cycles to cycles and boundaries to boundaries,
capping with a coboundary is zero on homology, and the cap product descends to a `k`-linear map
`Hᵖ(Hom(A, M)) ⟶ (Hₙ(E) ⟶ H_q(B'))` from the cohomology of `ChainComplex.linearYonedaObj`.  It is
natural along maps of diagonals and actions.

The singular cap product is the case where `D` is the Alexander–Whitney map precomposed with the
diagonal of a space, and `a` lets a coefficient pairing act on singular chains; there `x ⌢ φ`
evaluates `φ` on the front `p`-face of a singular simplex and keeps its back `q`-face.

## Main definitions and results

* `TauCeti.ChainComplex.capChain`: the cap product of a chain and a cochain.
* `TauCeti.ChainComplex.capChain_comp_d`: the boundary formula.
* `TauCeti.ChainComplex.capChain_naturality`: naturality along maps of diagonals and actions.
* `TauCeti.ChainComplex.capCycles`: the cap product of a cycle and a cocycle.
* `TauCeti.ChainComplex.cap`: the cap product on homology, with
  `TauCeti.ChainComplex.cap_homologyπ` computing it on classes of cycles and cocycles and
  `TauCeti.ChainComplex.cap_naturality` its naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product and its boundary formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Chain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M : C} {k : Type*} [Semiring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B')

variable (k) in
/-- **The cap product of chains and cochains** along the diagonal `D : E ⟶ A ⊗ B` and the action
`a : M ⊗ B ⟶ B'`: for `p + q = n`, the `k`-linear map sending a cochain `φ : A_p ⟶ M` to the
morphism `E_n ⟶ (A ⊗ B)_n ⟶ B'_q`, the component of `D` followed by the projection onto the summand
`A_p ⊗ B_q`, by `φ ▷ B_q` and by the component of `a`. -/
def capChain (p q n : ℕ) (_ : p + q = n) : (A.X p ⟶ M) →ₗ[k] (E.X n ⟶ B'.X q) where
  toFun φ := D.f n ≫ tensorCochain (a.f q) φ (𝟙 (B.X q)) n
  map_add' φ φ' := by rw [tensorCochain_add_left, Preadditive.comp_add]
  map_smul' r φ := by rw [tensorCochain_smul_left, Linear.comp_smul, RingHom.id_apply]

/-- The cap product is the component of the diagonal followed by the tensor product of cochains of
`φ` and the identity of `B_q`, along the action `a`. -/
@[simp]
lemma capChain_apply (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) :
    capChain k D a p q n h φ = D.f n ≫ tensorCochain (a.f q) φ (𝟙 (B.X q)) n :=
  (rfl)

/-- **The boundary formula for the cap product**: `∂(x ⌢ φ) = (-1)^p (∂x ⌢ φ - x ⌢ (φ ∘ ∂))` for a
cochain `φ` of degree `p`. -/
lemma capChain_comp_d (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) :
    capChain k D a p (q + 1) (n + 1) (by omega) φ ≫ B'.d (q + 1) q =
      ((-1 : ℤ) ^ p) • (E.d (n + 1) n ≫ capChain k D a p q n h φ -
        capChain k D a (p + 1) q (n + 1) (by omega) (A.d (p + 1) p ≫ φ)) := by
  -- since `a` is a chain map, `∂(x ⌢ φ)` is the tensor product of `φ` and `∂` on `B`
  have hd : capChain k D a p (q + 1) (n + 1) (by omega) φ ≫ B'.d (q + 1) q =
      D.f (n + 1) ≫ tensorCochain (a.f q) φ (B.d (q + 1) q) (n + 1) := by
    have ha : a.f (q + 1) ≫ B'.d (q + 1) q = (M ◁ B.d (q + 1) q) ≫ a.f q := by simp
    rw [capChain_apply, Category.assoc, tensorCochain_comp, ha, tensorCochain_whiskerLeft_comp,
      Category.id_comp]
  -- the Leibniz rule for the tensor product of `φ` and `𝟙 B_q`, transported along `D`
  have hL : E.d (n + 1) n ≫ capChain k D a p q n h φ =
      capChain k D a (p + 1) q (n + 1) (by omega) (A.d (p + 1) p ≫ φ) +
        ((-1 : ℤ) ^ p) • (D.f (n + 1) ≫ tensorCochain (a.f q) φ (B.d (q + 1) q) (n + 1)) := by
    rw [capChain_apply, capChain_apply, ← D.comm_assoc, d_comp_tensorCochain, Category.comp_id,
      Preadditive.comp_add, Preadditive.comp_zsmul]
  rw [hd, hL, add_sub_cancel_left]
  simp [smul_smul, ← mul_pow]

/-- **Naturality of the cap product of chains and cochains** along maps of diagonals and actions:
if chain maps `e : E' ⟶ E`, `f : A' ⟶ A`, `g : B₁ ⟶ B` and `g' : B₁' ⟶ B'` satisfy
`e ≫ D = D' ≫ (f ⊗ g)` and `a' ≫ g' = (M ◁ g) ≫ a`, then pushing forward along `g'` the cap
product along `D'` and `a'` with the pulled-back cochain is the cap product along `D` and `a` of
the pushed-forward chain. -/
lemma capChain_naturality {A' B₁ B₁' E' : ChainComplex C ℕ} [A'.HasTensor B₁]
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B₁)
    (a' : ((tensorLeft M).mapHomologicalComplex _).obj B₁ ⟶ B₁') (e : E' ⟶ E) (f : A' ⟶ A)
    (g : B₁ ⟶ B) (g' : B₁' ⟶ B') (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g)
    (ha : a' ≫ g' = ((tensorLeft M).mapHomologicalComplex _).map g ≫ a) (p q n : ℕ)
    (h : p + q = n) (φ : A.X p ⟶ M) :
    capChain k D' a' p q n h (f.f p ≫ φ) ≫ g'.f q = e.f n ≫ capChain k D a p q n h φ := by
  -- move `g'` through the action `a'` onto the second factor
  have hg : tensorCochain (a'.f q) (f.f p ≫ φ) (𝟙 (B₁.X q)) n ≫ g'.f q =
      tensorCochain (a.f q) (f.f p ≫ φ) (g.f q ≫ 𝟙 (B.X q)) n := by
    have ha' : a'.f q ≫ g'.f q = (M ◁ g.f q) ≫ a.f q := by
      simpa using congrArg (fun F ↦ F.f q) ha
    rw [tensorCochain_comp, ha', tensorCochain_whiskerLeft_comp, Category.id_comp,
      Category.comp_id]
  -- then move `f ⊗ g` through the diagonal
  have hD' : D'.f n ≫ (HomologicalComplex.tensorHom f g).f n = e.f n ≫ D.f n := by
    simpa using congrArg (fun F ↦ F.f n) hD.symm
  rw [capChain_apply, capChain_apply, Category.assoc, hg, ← tensorHom_f_comp_tensorCochain,
    reassoc_of% hD']

end Chain

section Homology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M : C} {k : Type*} [Ring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B')

/-- The boundary formula for the cap product with a cocycle: `∂(x ⌢ φ) = (-1)^p ∂x ⌢ φ`. -/
private lemma capChain_comp_d_of_cycles (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) :
    capChain k D a p (q + 1) (n + 1) (by omega) ((A.linearYonedaObj k M).iCycles p φ) ≫
        B'.d (q + 1) q =
      ((-1 : ℤ) ^ p) • (E.d (n + 1) n ≫
        capChain k D a p q n h ((A.linearYonedaObj k M).iCycles p φ)) := by
  -- a cocycle vanishes on boundaries
  have hφ : A.d (p + 1) p ≫ (A.linearYonedaObj k M).iCycles p φ = 0 :=
    d_comp_linearYonedaObj_iCycles p (p + 1) φ
  rw [capChain_comp_d D a p q n h ((A.linearYonedaObj k M).iCycles p φ), hφ, map_zero, sub_zero]

/-- Capping a cycle with a fixed cocycle `φ`, as a map of cycles. -/
private def capCyclesOf (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p) :
    E.cycles n ⟶ B'.cycles q :=
  B'.liftCycles (E.iCycles n ≫ capChain k D a p q n h ((A.linearYonedaObj k M).iCycles p φ))
    ((ComplexShape.down ℕ).next q) rfl (by
      cases q with
      | zero => rw [B'.shape _ _ (by simp), comp_zero]
      | succ q =>
        obtain rfl : n = p + q + 1 := by omega
        rw [ChainComplex.next_nat_succ, Category.assoc,
          capChain_comp_d_of_cycles D a p q _ rfl, Preadditive.comp_zsmul, iCycles_d_assoc,
          zero_comp, smul_zero])

@[reassoc]
private lemma capCyclesOf_i (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p) :
    capCyclesOf D a p q n h φ ≫ B'.iCycles q =
      E.iCycles n ≫ capChain k D a p q n h ((A.linearYonedaObj k M).iCycles p φ) :=
  B'.liftCycles_i _ _ _ _

variable (k) in
/-- **The cap product of a cycle and a cocycle**: capping with a cocycle of degree `p` sends the
cycles of `E` of degree `n = p + q` to cycles of `B'` of degree `q`, by the boundary formula
`TauCeti.ChainComplex.capChain_comp_d`; this is `k`-linear in the cocycle. -/
def capCycles (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).cycles p →ₗ[k] (E.cycles n ⟶ B'.cycles q) where
  toFun φ := capCyclesOf D a p q n h φ
  map_add' φ φ' := by
    rw [← cancel_mono (B'.iCycles q), Preadditive.add_comp, capCyclesOf_i, capCyclesOf_i,
      capCyclesOf_i, map_add, ← Preadditive.comp_add]
    exact congrArg (E.iCycles n ≫ ·) ((capChain k D a p q n h).map_add _ _)
  map_smul' r φ := by
    rw [← cancel_mono (B'.iCycles q), Linear.smul_comp, capCyclesOf_i, capCyclesOf_i, map_smul,
      RingHom.id_apply, ← Linear.comp_smul]
    exact congrArg (E.iCycles n ≫ ·) ((capChain k D a p q n h).map_smul r _)

/-- On underlying chains, the cap product of a cycle and a cocycle is the cap product of the chain
and the cochain. -/
@[reassoc (attr := simp)]
lemma capCycles_i (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p) :
    capCycles k D a p q n h φ ≫ B'.iCycles q =
      E.iCycles n ≫ capChain k D a p q n h ((A.linearYonedaObj k M).iCycles p φ) :=
  capCyclesOf_i D a p q n h φ

/-- The cap product of a boundary and a cocycle is a boundary. -/
private lemma toCycles_capCycles (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) :
    E.toCycles (n + 1) n ≫ capCycles k D a p q n h φ =
      (((-1 : ℤ) ^ p) • capChain k D a p (q + 1) (n + 1) (by omega)
        ((A.linearYonedaObj k M).iCycles p φ)) ≫ B'.toCycles (q + 1) q := by
  rw [← cancel_mono (B'.iCycles q), Category.assoc, capCycles_i, toCycles_i_assoc,
    Category.assoc, toCycles_i, Preadditive.zsmul_comp, capChain_comp_d_of_cycles D a p q n h]
  simp [smul_smul, ← mul_pow]

/-- The cap product of a cycle and a coboundary is a boundary. -/
private lemma capCycles_toCycles (i q n : ℕ) (h : i + 1 + q = n)
    (x : (A.linearYonedaObj k M).X i) :
    capCycles k D a (i + 1) q n h ((A.linearYonedaObj k M).toCycles i (i + 1) x) =
      (-((-1 : ℤ) ^ i) • (E.iCycles n ≫ capChain k D a i (q + 1) n (by omega) x)) ≫
        B'.toCycles (q + 1) q := by
  obtain rfl : n = i + q + 1 := by omega
  have hd := capChain_comp_d (k := k) D a i q (i + q) rfl x
  rw [← cancel_mono (B'.iCycles q), Category.assoc, capCycles_i, toCycles_i,
    linearYonedaObj_iCycles_toCycles_apply, Preadditive.zsmul_comp, Category.assoc, hd]
  -- the term `∂x ⌢ φ` vanishes on cycles, leaving the sign algebra
  simp [smul_smul, ← mul_pow]

variable (k) in
/-- Capping with a fixed cocycle, on homology. -/
private def capHomologyOfCycles (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) : E.homology n ⟶ B'.homology q :=
  (CokernelCofork.IsColimit.desc' (E.homologyIsCokernel (n + 1) n (by simp))
    (capCycles k D a p q n h φ ≫ B'.homologyπ q)
    (by rw [← Category.assoc, toCycles_capCycles, Category.assoc, toCycles_comp_homologyπ,
      comp_zero])).1

private lemma homologyπ_capHomologyOfCycles (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) :
    E.homologyπ n ≫ capHomologyOfCycles k D a p q n h φ =
      capCycles k D a p q n h φ ≫ B'.homologyπ q :=
  (CokernelCofork.IsColimit.desc' (E.homologyIsCokernel (n + 1) n (by simp)) _ _).2

/-- Capping with a coboundary is zero on homology. -/
private lemma capHomologyOfCycles_toCycles (p q n : ℕ) (h : p + q = n) (i : ℕ)
    (x : (A.linearYonedaObj k M).X i) :
    capHomologyOfCycles k D a p q n h ((A.linearYonedaObj k M).toCycles i p x) = 0 := by
  rw [← cancel_epi (E.homologyπ n), homologyπ_capHomologyOfCycles, comp_zero]
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := hip
    rw [capCycles_toCycles, Category.assoc, toCycles_comp_homologyπ, comp_zero]
  · rw [(A.linearYonedaObj k M).toCycles_eq_zero hip]
    simp

variable (k) in
/-- Capping with a cocycle on homology, as a `k`-linear function of the cocycle. -/
private def capCyclesHomology (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).cycles p ⟶ ModuleCat.of k (E.homology n ⟶ B'.homology q) :=
  ModuleCat.ofHom (X := (A.linearYonedaObj k M).cycles p)
    { toFun φ := capHomologyOfCycles k D a p q n h φ
      map_add' φ φ' := by
        rw [← cancel_epi (E.homologyπ n), Preadditive.comp_add, homologyπ_capHomologyOfCycles,
          homologyπ_capHomologyOfCycles, homologyπ_capHomologyOfCycles, map_add,
          Preadditive.add_comp]
      map_smul' r φ := by
        rw [← cancel_epi (E.homologyπ n), RingHom.id_apply, Linear.comp_smul,
          homologyπ_capHomologyOfCycles, homologyπ_capHomologyOfCycles, map_smul,
          Linear.smul_comp] }

/-- Capping with a coboundary is zero on homology. -/
private lemma toCycles_comp_capCyclesHomology (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).toCycles ((ComplexShape.up ℕ).prev p) p ≫
      capCyclesHomology k D a p q n h = 0 := by
  ext x : 2
  exact capHomologyOfCycles_toCycles D a p q n h _ x

variable (k) in
/-- **The cap product on homology**, `Hᵖ(Hom(A, M)) ⟶ (Hₙ(E) ⟶ H_q(B'))` for `p + q = n`, along
the diagonal `D : E ⟶ A ⊗ B` and the action `a : M ⊗ B ⟶ B'`: on the classes of a cocycle `φ` and
a cycle `x`, the class of `x ⌢ φ` (`TauCeti.ChainComplex.cap_homologyπ`). -/
def cap (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).homology p →ₗ[k] (E.homology n ⟶ B'.homology q) :=
  (CokernelCofork.IsColimit.desc' ((A.linearYonedaObj k M).homologyIsCokernel _ p rfl)
    (capCyclesHomology k D a p q n h) (toCycles_comp_capCyclesHomology D a p q n h)).1.hom

/-- **The cap product on classes**: capping the class of a cycle with the class of a cocycle `φ`
is the class of the cap product of the cycle with `φ`. -/
@[reassoc (attr := simp)]
lemma cap_homologyπ (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p) :
    E.homologyπ n ≫ cap k D a p q n h ((A.linearYonedaObj k M).homologyπ p φ) =
      capCycles k D a p q n h φ ≫ B'.homologyπ q := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    ((A.linearYonedaObj k M).homologyIsCokernel _ p rfl) (capCyclesHomology k D a p q n h)
    (toCycles_comp_capCyclesHomology D a p q n h)).2 φ
  rw [cap]
  exact (congrArg (E.homologyπ n ≫ ·) hfac).trans (homologyπ_capHomologyOfCycles D a p q n h φ)

/-- **Naturality of the cap product on homology** along maps of diagonals and actions: if chain
maps `e : E' ⟶ E`, `f : A' ⟶ A`, `g : B₁ ⟶ B` and `g' : B₁' ⟶ B'` satisfy
`e ≫ D = D' ≫ (f ⊗ g)` and `a' ≫ g' = (M ◁ g) ≫ a`, then capping with the pulled-back class and
pushing forward along `g'` is pushing forward along `e` and capping with the class. -/
lemma cap_naturality {A' B₁ B₁' E' : ChainComplex C ℕ} [A'.HasTensor B₁]
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B₁)
    (a' : ((tensorLeft M).mapHomologicalComplex _).obj B₁ ⟶ B₁') (e : E' ⟶ E) (f : A' ⟶ A)
    (g : B₁ ⟶ B) (g' : B₁' ⟶ B') (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g)
    (ha : a' ≫ g' = ((tensorLeft M).mapHomologicalComplex _).map g ≫ a) (p q n : ℕ)
    (h : p + q = n) (α : (A.linearYonedaObj k M).homology p) :
    cap k D' a' p q n h
        (homologyMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) p α) ≫ homologyMap g' q =
      homologyMap e n ≫ cap k D a p q n h α := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply, ← cancel_epi (E'.homologyπ n),
    cap_homologyπ_assoc, homologyπ_naturality_assoc, cap_homologyπ, homologyπ_naturality,
    ← Category.assoc, ← Category.assoc]
  -- both sides are classes of cycles, compared on underlying chains by `capChain_naturality`
  congr 1
  rw [← cancel_mono (B'.iCycles q), Category.assoc, cyclesMap_i, capCycles_i_assoc,
    Category.assoc, capCycles_i, cyclesMap_i_assoc, iCycles_cyclesMap_linearYonedaFunctor_map_apply]
  exact congrArg (E'.iCycles n ≫ ·) (capChain_naturality D a D' a' e f g g' hD ha p q n h _)

end Homology

end TauCeti.ChainComplex
