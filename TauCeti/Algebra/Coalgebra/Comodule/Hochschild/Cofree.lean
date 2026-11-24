/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Hochschild.Complex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Acyclicity of cofree Hochschild coefficients

For a bialgebra `H` over a commutative ring `R` and any `R`-module `N`, the Hochschild
complex with coefficients in the cofree comodule `N ⊗ H` is exact in positive degrees.
The contraction applies the counit to the first `H` factor, retaining all subsequent
factors in their original order. In degree zero its homotopy identity is the identity
minus the projection `n ⊗ h ↦ ε(h) • (n ⊗ 1)`.

This gives explicit primitives for all positive-degree cocycles. Moreover the Hochschild complex
of `N ⊗ H` is homotopy equivalent to `N` placed in degree zero, so `H⁰(H, N ⊗ H) ≅ N`, the
identification being induced by the counit `n ⊗ h ↦ ε(h) n`. Neither `H` nor `N` needs to be
flat, finite or injective; the result concerns the Hochschild complex itself.

For a flat Hopf algebra `H = O(G)`, the cofree comodules are the terms of the standard resolution
`M → M ⊗ H → M ⊗ H ⊗ H → ⋯` of a comodule `M`, and every comodule embeds into a cofree comodule
`I ⊗ H` with `I` an injective module. Their acyclicity is the input that identifies Hochschild
cohomology with the right derived functors of the invariants `M ↦ Mᴴ`, the rational cohomology
`Hⁿ(G, M)`.

## Main declarations

* `TauCeti.Comodule.hochschildCofreeContraction`: the contraction (extra codegeneracy) of the
  Hochschild cochains of `N ⊗ H`.
* `TauCeti.Comodule.hochschildCofreeContraction_comp_differential`: it is a contracting
  homotopy in positive degrees.
* `TauCeti.Comodule.exactAt_hochschildComplex_cofree`: the positive degree Hochschild
  cohomology of `N ⊗ H` vanishes.
* `TauCeti.Comodule.hochschildComplexCofreeHomotopyEquiv`: the Hochschild complex of `N ⊗ H` is
  homotopy equivalent to `N` in degree zero.
* `TauCeti.Comodule.hochschildComplexCofreeHomologyZeroIso`: the degree zero Hochschild
  cohomology of `N ⊗ H` is `N`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, §§3.7, 4.14–4.16.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) [CommRing R] (H : Type v)

section Acyclic

variable (N : Type w) [AddCommGroup N] [Module R N]

attribute [local instance] cofree

section Coalgebra

variable [AddCommMonoid H] [Module R H] [Coalgebra R H]

/-- The contraction of the Hochschild complex of the cofree comodule `N ⊗ H`.
It applies the counit to its first `H` factor, leaving the remaining factors in order. -/
noncomputable def hochschildCofreeContraction : (n : ℕ) →
    (hochschildCochains R H (N ⊗[R] H) (n + 1) →ₗ[R]
      hochschildCochains R H (N ⊗[R] H) n)
  | 0 => (cofreeCounit R H N).rTensor H
  | n + 1 => (hochschildCofreeContraction n).rTensor H

/-- In degree zero, the contraction applies the counit projection to the factor `N ⊗ H`. -/
theorem hochschildCofreeContraction_zero :
    hochschildCofreeContraction R H N 0 = (cofreeCounit R H N).rTensor H :=
  (rfl)

/-- In degree one, the contraction evaluates the first coalgebra factor by the counit. -/
@[simp]
theorem hochschildCofreeContraction_zero_tmul (n : N) (a b : H) :
    hochschildCofreeContraction R H N 0 ((n ⊗ₜ[R] a) ⊗ₜ[R] b) =
      Coalgebra.counit (R := R) a • (n ⊗ₜ[R] b) := by
  simp [hochschildCofreeContraction_zero, TensorProduct.smul_tmul']

/-- In higher degrees, the contraction leaves the last tensor factor untouched. -/
theorem hochschildCofreeContraction_succ (n : ℕ) :
    hochschildCofreeContraction R H N (n + 1) =
      (hochschildCofreeContraction R H N n).rTensor H :=
  (rfl)

/-- In higher degrees, the contraction acts on all but the last factor. -/
@[simp]
theorem hochschildCofreeContraction_succ_tmul (n : ℕ)
    (x : hochschildCochains R H (N ⊗[R] H) (n + 1)) (h : H) :
    hochschildCofreeContraction R H N (n + 1) (x ⊗ₜ[R] h) =
      (hochschildCofreeContraction R H N n x ⊗ₜ[R] h :
        hochschildCochains R H (N ⊗[R] H) (n + 1)) := by
  rw [hochschildCofreeContraction_succ, LinearMap.rTensor_tmul]

end Coalgebra

variable [Semiring H] [Bialgebra R H]

/-- The contraction cancels the first coface. -/
@[simp]
theorem hochschildCofreeContraction_comp_coface_zero (n : ℕ) :
    hochschildCofreeContraction R H N n ∘ₗ
        hochschildCoface R H (N ⊗[R] H) n 0 = LinearMap.id := by
  induction n with
  | zero =>
    -- Present the first index as a cast so the recursive coface formula applies.
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      hochschildCoface_zero_castSucc, hochschildCofreeContraction_zero]
    exact rTensor_cofreeCounit_comp_cofreeCoact
  | succ n ih =>
    -- Two casts select precisely the recursively tensored cofaces.
    rw [show (0 : Fin (n + 3)) = (0 : Fin (n + 1)).castSucc.castSucc from rfl,
      hochschildCoface_succ_castSucc_castSucc, hochschildCofreeContraction_succ,
      ← LinearMap.rTensor_comp, Fin.castSucc_zero, ih, LinearMap.rTensor_id]

/-- The contraction commutes with every later coface, shifting its index down by one. -/
@[simp]
theorem hochschildCofreeContraction_comp_coface_succ (n : ℕ) (i : Fin (n + 2)) :
    hochschildCofreeContraction R H N (n + 1) ∘ₗ
        hochschildCoface R H (N ⊗[R] H) (n + 1) i.succ =
      hochschildCoface R H (N ⊗[R] H) n i ∘ₗ
        hochschildCofreeContraction R H N n := by
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildCoface_last, hochschildCoface_last,
      hochschildCofreeContraction_succ]
    ext x
    simp
  | cast i =>
    rw [Fin.succ_castSucc, hochschildCofreeContraction_succ]
    induction n with
    | zero =>
      have hi : i = Fin.last 0 := Fin.ext (by omega)
      subst i
      rw [Fin.succ_last, hochschildCoface_succ_castSucc_last,
        hochschildCoface_zero_castSucc]
      exact (cofreeCoact_comp_rTensor _).symm
    | succ n ih =>
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, hochschildCoface_succ_castSucc_last,
          hochschildCoface_succ_castSucc_last, hochschildCofreeContraction_succ]
        exact (cofreeCoact_comp_rTensor _).symm
      | cast i =>
        rw [Fin.succ_castSucc, hochschildCoface_succ_castSucc_castSucc,
          hochschildCoface_succ_castSucc_castSucc, hochschildCofreeContraction_succ,
          ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
        exact congrArg (LinearMap.rTensor H) (ih i)

/-- The contracting homotopy identity in positive degrees, with no sign change in the
contraction: `s d + d s = id`. -/
theorem hochschildCofreeContraction_comp_differential (n : ℕ) :
    hochschildCofreeContraction R H N (n + 1) ∘ₗ
        hochschildDifferential R H (N ⊗[R] H) (n + 1) +
      hochschildDifferential R H (N ⊗[R] H) n ∘ₗ
        hochschildCofreeContraction R H N n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [hochschildDifferential_apply R H (N ⊗[R] H),
    hochschildDifferential_apply R H (N ⊗[R] H)]
  simp only [map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  have hzero := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_coface_zero R H N (n + 1)) x
  have hsucc (i : Fin (n + 2)) := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_coface_succ R H N n i) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hzero hsucc
  rw [hzero]
  simp_rw [hsucc]
  simp only [Fin.val_zero, pow_zero, one_zsmul, LinearMap.id_apply, Fin.val_succ,
    pow_succ, mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  abel

/-- In degree zero, the homotopy retracts onto the counit projection followed by
`n ↦ n ⊗ 1`. -/
theorem hochschildCofreeContraction_zero_comp_differential (x : N ⊗[R] H) :
    hochschildCofreeContraction R H N 0
        (hochschildDifferential R H (N ⊗[R] H) 0 x) =
      x - cofreeCounit R H N x ⊗ₜ[R] (1 : H) := by
  rw [hochschildDifferential_zero_apply, map_sub]
  have h := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_coface_zero R H N 0) x
  -- The first index must be a cast for the degree-zero coface formula to match.
  rw [LinearMap.comp_apply,
    show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
    hochschildCoface_zero_castSucc, LinearMap.id_apply] at h
  rw [h]
  rfl

/-- Every positive-degree Hochschild cocycle with cofree coefficients has the explicit
primitive given by the contraction. -/
theorem hochschildDifferential_contraction_of_cocycle (n : ℕ)
    (x : hochschildCochains R H (N ⊗[R] H) (n + 1))
    (hx : hochschildDifferential R H (N ⊗[R] H) (n + 1) x = 0) :
    hochschildDifferential R H (N ⊗[R] H) n
      (hochschildCofreeContraction R H N n x) = x := by
  have h := LinearMap.congr_fun (hochschildCofreeContraction_comp_differential R H N n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero, zero_add,
    LinearMap.id_apply] using h

/-- The Hochschild complex of a cofree comodule is exact in every positive degree. -/
theorem exactAt_hochschildComplex_cofree (n : ℕ) :
    (hochschildComplex R H (N ⊗[R] H)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [hochschildComplex_d]
  intro x hx
  refine ⟨hochschildCofreeContraction R H N n x, ?_⟩
  exact hochschildDifferential_contraction_of_cocycle R H N n x hx

/-- All positive-degree Hochschild cohomology objects of a cofree comodule vanish. -/
theorem isZero_homology_hochschildComplex_cofree (n : ℕ) :
    Limits.IsZero ((hochschildComplex R H (N ⊗[R] H)).homology (n + 1)) :=
  (exactAt_hochschildComplex_cofree R H N n).isZero_homology

/-- The map `N → N ⊗ H`, `x ↦ x ⊗ 1`, lands in the cocycles of degree zero of the Hochschild
complex of `N ⊗ H`. -/
theorem hochschildDifferential_zero_comp_mk_flip_one :
    hochschildDifferential R H (N ⊗[R] H) 0 ∘ₗ (TensorProduct.mk R N H).flip 1 = 0 := by
  ext x
  rw [LinearMap.comp_apply, hochschildDifferential_zero_apply]
  simp [Algebra.TensorProduct.one_def]

end Acyclic

section HomotopyEquiv

/-! The homotopy equivalence with `N` in degree zero compares the Hochschild complex with a
complex of `R`-modules in the same universe, so here `N` lives in `Type (max v w)`. -/

variable (N : Type (max v w)) [AddCommGroup N] [Module R N] [Semiring H] [Bialgebra R H]

attribute [local instance] cofree

/-- The homotopy condition in degree zero, on cochains. -/
private theorem homotopy_comm_zero_apply
    (x : hochschildCochains.{u, v, max v w} R H (N ⊗[R] H) 0) :
    ((TensorProduct.mk R N H).flip 1 ∘ₗ cofreeCounit R H N) x =
      (-hochschildCofreeContraction R H N 0)
          (hochschildDifferential.{u, v, max v w} R H (N ⊗[R] H) 0 x) + x := by
  rw [LinearMap.neg_apply, hochschildCofreeContraction_zero_comp_differential]
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.flip_apply]
  abel

/-- The homotopy condition in positive degrees, on cochains. -/
private theorem homotopy_comm_succ_apply (n : ℕ)
    (x : hochschildCochains.{u, v, max v w} R H (N ⊗[R] H) (n + 1)) :
    (0 : hochschildCochains.{u, v, max v w} R H (N ⊗[R] H) (n + 1)) =
      (-hochschildCofreeContraction R H N (n + 1))
          (hochschildDifferential.{u, v, max v w} R H (N ⊗[R] H) (n + 1) x) +
        hochschildDifferential.{u, v, max v w} R H (N ⊗[R] H) n
          ((-hochschildCofreeContraction R H N n) x) + x := by
  have h := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_differential R H N n) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
  simp only [LinearMap.neg_apply, map_neg]
  exact (sub_eq_zero.mpr h.symm).symm.trans (by abel)

/-- The Hochschild complex of the cofree comodule `N ⊗ H` is homotopy equivalent to `N` placed in
degree zero. The map to `N` applies the counit, `x ⊗ h ↦ ε(h) x`, and the map from `N` is
`x ↦ x ⊗ 1`; the homotopy is given by the contraction. -/
noncomputable def hochschildComplexCofreeHomotopyEquiv :
    HomotopyEquiv (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H))
      ((CochainComplex.single₀ (ModuleCat.{max v w} R)).obj (ModuleCat.of R N)) where
  hom := (CochainComplex.toSingle₀Equiv _ _).symm
    (ConcreteCategory.ofHom (C := ModuleCat R)
      (X := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X 0) (cofreeCounit R H N))
  inv := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨ConcreteCategory.ofHom (C := ModuleCat R)
      (Y := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X 0)
      ((TensorProduct.mk R N H).flip 1), by
      rw [hochschildComplex_d]
      exact ModuleCat.hom_ext (hochschildDifferential_zero_comp_mk_flip_one R H N)⟩
  homotopyHomInvId :=
    { hom i j := if h : j + 1 = i then
        eqToHom (congrArg (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X h.symm) ≫
          ConcreteCategory.ofHom (C := ModuleCat R)
            (X := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X (j + 1))
            (Y := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X j)
            (-hochschildCofreeContraction R H N j)
        else 0
      zero i j hij := dite_eq_right_iff.mpr fun h ↦ absurd h hij
      comm i := by
        cases i with
        | zero =>
          simp only [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
            hochschildComplex_d, add_zero, HomologicalComplex.comp_f, HomologicalComplex.id_f,
            CochainComplex.toSingle₀Equiv_symm_apply_f_zero,
            CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, dite_true, eqToHom_refl,
            Category.id_comp]
          -- The terms of the complex are the Hochschild cochains only by unfolding
          -- `hochschildComplex_X`, so the goal is closed by its form on cochains.
          exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ homotopy_comm_zero_apply R H N x)
        | succ i =>
          simp only [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
            hochschildComplex_d, HomologicalComplex.comp_f, HomologicalComplex.id_f,
            CochainComplex.toSingle₀Equiv_symm_apply_f_succ, dite_true, eqToHom_refl,
            Category.id_comp, Limits.zero_comp]
          -- As in degree zero, the goal is its form on cochains up to `hochschildComplex_X`.
          exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ homotopy_comm_succ_apply R H N i x) }
  homotopyInvHomId := Homotopy.ofEq (by
    ext : 1
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
      CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
    -- In degree zero, this is the counit law of `x ↦ x ⊗ 1`.
    exact ModuleCat.hom_ext (cofreeCounit_comp_mk_flip_one R N H))

/-- In degree zero, the map from the Hochschild complex of `N ⊗ H` to `N` applies the counit. -/
@[simp]
theorem hochschildComplexCofreeHomotopyEquiv_hom_f_zero :
    (hochschildComplexCofreeHomotopyEquiv R H N).hom.f 0 =
      ConcreteCategory.ofHom (C := ModuleCat R)
        (X := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X 0) (cofreeCounit R H N) :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero _

/-- In degree zero, the map from `N` to the Hochschild complex of `N ⊗ H` is `x ↦ x ⊗ 1`. -/
@[simp]
theorem hochschildComplexCofreeHomotopyEquiv_inv_f_zero :
    (hochschildComplexCofreeHomotopyEquiv R H N).inv.f 0 =
      ConcreteCategory.ofHom (C := ModuleCat R)
        (Y := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X 0)
        ((TensorProduct.mk R N H).flip 1) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The Hochschild cohomology of the cofree comodule `N ⊗ H` in degree zero is `N`, by the map
induced by the counit `x ⊗ h ↦ ε(h) x`. -/
noncomputable def hochschildComplexCofreeHomologyZeroIso :
    (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).homology 0 ≅ ModuleCat.of R N :=
  (hochschildComplexCofreeHomotopyEquiv R H N).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

/-- The identification of the degree zero Hochschild cohomology of `N ⊗ H` with `N` sends the
class of a cocycle `x` to `(id ⊗ ε) x`. -/
@[reassoc (attr := simp)]
theorem homologyπ_hochschildComplexCofreeHomologyZeroIso_hom :
    (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).homologyπ 0 ≫
        (hochschildComplexCofreeHomologyZeroIso R H N).hom =
      (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).iCycles 0 ≫
        ConcreteCategory.ofHom (C := ModuleCat R)
          (X := (hochschildComplex.{u, v, max v w} R H (N ⊗[R] H)).X 0)
          (Y := ModuleCat.of R N) (cofreeCounit R H N) := by
  simp only [hochschildComplexCofreeHomologyZeroIso, HomotopyEquiv.toHomologyIso,
    Iso.trans_hom, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc]
  simp [hochschildComplexCofreeHomotopyEquiv_hom_f_zero, CochainComplex.single₀ObjXSelf]

end HomotopyEquiv

end TauCeti.Comodule
