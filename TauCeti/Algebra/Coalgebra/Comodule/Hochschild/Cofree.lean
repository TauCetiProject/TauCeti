/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.Algebra.Coalgebra.Comodule.Hochschild.Complex

/-!
# Hochschild cohomology of cofree comodules

Let `H` be a bialgebra over a commutative ring `R` and `N` an `R`-module. This file proves that
the cofree comodule `N ⊗ H` is acyclic for Hochschild cohomology: its Hochschild complex is
homotopy equivalent to `N` placed in degree zero. Consequently `H⁰(H, N ⊗ H) ≅ N`, the
identification being induced by the counit `n ⊗ h ↦ ε(h) n`, and `Hⁿ(H, N ⊗ H) = 0` for `n > 0`.
No flatness or finiteness is assumed of `N` or `H`.

The Hochschild cochains of `N ⊗ H` are `N ⊗ H ⊗ H^⊗n`, and the homotopy is the extra
codegeneracy `n ⊗ h₀ ⊗ h₁ ⊗ ⋯ ⊗ hₙ ↦ ε(h₀) n ⊗ h₁ ⊗ ⋯ ⊗ hₙ`, which applies the counit to the
factor `H` of the cofree comodule. It is a left inverse of the coface applying the coaction, and
it commutes with the remaining cofaces after a shift of index.

For a flat Hopf algebra `H = O(G)`, the cofree comodules are the terms of the standard resolution
`M → M ⊗ H → M ⊗ H ⊗ H → ⋯` of a comodule `M`, and every comodule embeds into a cofree comodule
`I ⊗ H` with `I` an injective module. Their acyclicity is the input that identifies Hochschild
cohomology with the right derived functors of the invariants `M ↦ Mᴴ`, the rational cohomology
`Hⁿ(G, M)`.

## Main declarations

* `TauCeti.Comodule.hochschildExtraCodegeneracy`: the extra codegeneracy of the Hochschild
  cochains of `N ⊗ H`.
* `TauCeti.Comodule.hochschildExtraCodegeneracy_comp_hochschildDifferential_succ`: it is a
  contracting homotopy in positive degrees.
* `TauCeti.Comodule.hochschildComplexCofreeHomotopyEquiv`: the Hochschild complex of `N ⊗ H` is
  homotopy equivalent to `N` in degree zero.
* `TauCeti.Comodule.exactAt_hochschildComplex_cofree_succ`: the positive degree Hochschild
  cohomology of `N ⊗ H` vanishes.
* `TauCeti.Comodule.hochschildComplexCofreeHomologyZeroIso`: the degree zero Hochschild
  cohomology of `N ⊗ H` is `N`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, §§3.7, 4.15–4.16.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (H : Type v) (N : Type (max v w))
variable [CommRing R] [AddCommGroup N] [Module R N]

section ExtraCodegeneracy

variable [AddCommMonoid H] [Module R H] [Coalgebra R H]

/-- The extra codegeneracy of the Hochschild cochains of the cofree comodule `N ⊗ H`: it applies
the counit to the factor `H` of `N ⊗ H`, sending `n ⊗ h₀ ⊗ h₁ ⊗ ⋯ ⊗ hₙ₊₁` to
`ε(h₀) n ⊗ h₁ ⊗ ⋯ ⊗ hₙ₊₁`. -/
noncomputable def hochschildExtraCodegeneracy :
    ∀ n, hochschildCochains R H (N ⊗[R] H) (n + 1) →ₗ[R] hochschildCochains R H (N ⊗[R] H) n
  | 0 => (cofreeCounit R H N).rTensor H
  | n + 1 => (hochschildExtraCodegeneracy n).rTensor H

/-- In degree zero, the extra codegeneracy applies the counit to the factor `H` of `N ⊗ H`. -/
theorem hochschildExtraCodegeneracy_zero :
    hochschildExtraCodegeneracy R H N 0 = (cofreeCounit R H N).rTensor H :=
  (rfl)

/-- In degree `n + 1`, the extra codegeneracy is the one of degree `n` tensored with `H`. -/
theorem hochschildExtraCodegeneracy_succ (n : ℕ) :
    hochschildExtraCodegeneracy R H N (n + 1) = (hochschildExtraCodegeneracy R H N n).rTensor H :=
  (rfl)

/-- The extra codegeneracy of degree zero sends `(x ⊗ h₀) ⊗ h₁` to `ε(h₀) x ⊗ h₁`. -/
@[simp]
theorem hochschildExtraCodegeneracy_zero_tmul (x : N) (h₀ h₁ : H) :
    hochschildExtraCodegeneracy R H N 0 ((x ⊗ₜ[R] h₀) ⊗ₜ[R] h₁) =
      (Coalgebra.counit (R := R) h₀ • x) ⊗ₜ[R] h₁ := by
  simp [hochschildExtraCodegeneracy_zero]

/-- The extra codegeneracy of degree `n + 1` acts on all but the last factor. -/
@[simp]
theorem hochschildExtraCodegeneracy_succ_tmul (n : ℕ)
    (x : hochschildCochains R H (N ⊗[R] H) (n + 1)) (h : H) :
    hochschildExtraCodegeneracy R H N (n + 1) (x ⊗ₜ[R] h) =
      (hochschildExtraCodegeneracy R H N n x ⊗ₜ[R] h :
        hochschildCochains R H (N ⊗[R] H) (n + 1)) := by
  rw [hochschildExtraCodegeneracy_succ, LinearMap.rTensor_tmul]

end ExtraCodegeneracy

variable [Semiring H] [Bialgebra R H]

-- The Hochschild complex in this file is that of the cofree comodule `N ⊗ H`.
attribute [local instance] cofree

/-- The extra codegeneracy is a left inverse of the coface applying the coaction. -/
theorem hochschildExtraCodegeneracy_comp_hochschildCoface_zero (n : ℕ) :
    hochschildExtraCodegeneracy R H N n ∘ₗ hochschildCoface R H (N ⊗[R] H) n 0 =
      LinearMap.id := by
  induction n with
  | zero =>
    -- The coaction of the cofree comodule is `cofreeCoact`, and the identity is its counit law.
    rw [← Fin.castSucc_zero, hochschildCoface_zero_castSucc, hochschildExtraCodegeneracy_zero]
    exact rTensor_cofreeCounit_comp_cofreeCoact
  | succ n ih =>
    -- The coface `0` acts on all but the last factor `H`.
    have h := hochschildCoface_succ_castSucc_castSucc R H (N ⊗[R] H) n 0
    simp only [Fin.castSucc_zero] at h
    simp [h, hochschildExtraCodegeneracy_succ, ← LinearMap.rTensor_comp, ih]

/-- The extra codegeneracy commutes with the last coface, which appends the unit. -/
private theorem hochschildExtraCodegeneracy_comp_hochschildCoface_last (n : ℕ) :
    hochschildExtraCodegeneracy R H N (n + 1) ∘ₗ
        hochschildCoface R H (N ⊗[R] H) (n + 1) (Fin.last (n + 2)) =
      hochschildCoface R H (N ⊗[R] H) n (Fin.last (n + 1)) ∘ₗ
        hochschildExtraCodegeneracy R H N n := by
  rw [hochschildCoface_last R H (N ⊗[R] H) (n + 1), hochschildCoface_last,
    hochschildExtraCodegeneracy_succ]
  refine LinearMap.ext fun x ↦ ?_
  simp

/-- The extra codegeneracy commutes with the coface comultiplying the last factor `H`: both are
cofree coactions, and the extra codegeneracy acts on the other factors. -/
private theorem hochschildExtraCodegeneracy_comp_hochschildCoface_castSucc_last (n : ℕ) :
    hochschildExtraCodegeneracy R H N (n + 1) ∘ₗ
        hochschildCoface R H (N ⊗[R] H) (n + 1) (Fin.last (n + 1)).castSucc =
      hochschildCoface R H (N ⊗[R] H) n (Fin.last n).castSucc ∘ₗ
        hochschildExtraCodegeneracy R H N n := by
  rw [hochschildCoface_succ_castSucc_last, hochschildExtraCodegeneracy_succ]
  cases n with
  | zero =>
    -- The coaction of the cofree comodule `N ⊗ H` is `cofreeCoact`.
    rw [Fin.last_zero, hochschildCoface_zero_castSucc, hochschildExtraCodegeneracy_zero]
    exact (cofreeCoact_comp_rTensor _).symm
  | succ n =>
    rw [hochschildCoface_succ_castSucc_last, hochschildExtraCodegeneracy_succ]
    exact (cofreeCoact_comp_rTensor _).symm

/-- The extra codegeneracy commutes with the cofaces other than the coaction, after shifting
their index down by one. -/
theorem hochschildExtraCodegeneracy_comp_hochschildCoface_succ (n : ℕ) (i : Fin (n + 2)) :
    hochschildExtraCodegeneracy R H N (n + 1) ∘ₗ hochschildCoface R H (N ⊗[R] H) (n + 1) i.succ =
      hochschildCoface R H (N ⊗[R] H) n i ∘ₗ hochschildExtraCodegeneracy R H N n := by
  induction i using Fin.lastCases with
  | last => exact hochschildExtraCodegeneracy_comp_hochschildCoface_last R H N n
  | cast j =>
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.succ_castSucc, Fin.succ_last]
      exact hochschildExtraCodegeneracy_comp_hochschildCoface_castSucc_last R H N n
    | cast k =>
      -- Both sides act on all but the last factor `H`, where this is the statement one degree
      -- lower.
      cases n with
      | zero => exact k.elim0
      | succ n =>
        simpa only [Fin.succ_castSucc, hochschildCoface_succ_castSucc_castSucc,
          hochschildExtraCodegeneracy_succ, LinearMap.rTensor_comp] using
          congrArg (LinearMap.rTensor H)
            (hochschildExtraCodegeneracy_comp_hochschildCoface_succ n k.castSucc)

/-- In degree zero, the extra codegeneracy sends the last coface `x ↦ x ⊗ 1` to the map
`x ↦ (id ⊗ ε) x ⊗ 1`. -/
private theorem hochschildExtraCodegeneracy_zero_comp_hochschildCoface_last :
    hochschildExtraCodegeneracy R H N 0 ∘ₗ hochschildCoface R H (N ⊗[R] H) 0 (Fin.last 1) =
      (TensorProduct.mk R N H).flip 1 ∘ₗ cofreeCounit R H N := by
  rw [hochschildCoface_last, hochschildExtraCodegeneracy_zero]
  refine LinearMap.ext fun x ↦ ?_
  simp

/-- In degree zero, the extra codegeneracy is a left inverse of the Hochschild differential up
to the projection `x ↦ (id ⊗ ε) x ⊗ 1` onto the invariants. -/
theorem hochschildExtraCodegeneracy_comp_hochschildDifferential_zero :
    hochschildExtraCodegeneracy R H N 0 ∘ₗ hochschildDifferential R H (N ⊗[R] H) 0 =
      LinearMap.id - (TensorProduct.mk R N H).flip 1 ∘ₗ cofreeCounit R H N := by
  refine LinearMap.ext fun x ↦ ?_
  have h₀ := LinearMap.congr_fun
    (hochschildExtraCodegeneracy_comp_hochschildCoface_zero R H N 0) x
  -- The last coface out of degree zero is the coface `1 = Fin.last 1`.
  have h₁ : hochschildExtraCodegeneracy R H N 0 (hochschildCoface R H (N ⊗[R] H) 0 1 x) =
      ((TensorProduct.mk R N H).flip 1 ∘ₗ cofreeCounit R H N) x :=
    LinearMap.congr_fun (hochschildExtraCodegeneracy_zero_comp_hochschildCoface_last R H N) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h₀
  -- `simp` does not apply `hochschildDifferential_apply` to the `ModuleCat` carriers of cochains.
  rw [LinearMap.comp_apply, hochschildDifferential_apply]
  simp [Fin.sum_univ_two, h₀, h₁, sub_eq_add_neg]

/-- In positive degrees, the extra codegeneracy is a contracting homotopy of the Hochschild
complex of the cofree comodule `N ⊗ H`. -/
theorem hochschildExtraCodegeneracy_comp_hochschildDifferential_succ (n : ℕ) :
    hochschildExtraCodegeneracy R H N (n + 1) ∘ₗ hochschildDifferential R H (N ⊗[R] H) (n + 1) +
        hochschildDifferential R H (N ⊗[R] H) n ∘ₗ hochschildExtraCodegeneracy R H N n =
      LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  have h₀ := LinearMap.congr_fun
    (hochschildExtraCodegeneracy_comp_hochschildCoface_zero R H N (n + 1)) x
  have h := fun i ↦ LinearMap.congr_fun
    (hochschildExtraCodegeneracy_comp_hochschildCoface_succ R H N n i) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h₀ h
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  -- As in degree zero, the differentials are unfolded by rewriting.
  rw [hochschildDifferential_apply, hochschildDifferential_apply]
  -- Split off only the coface `0` of degree `n + 1`, the coaction undone by `h₀`.
  simp [Fin.sum_univ_succ (n := n + 2), h₀, h, pow_succ]

/-- The map `N → N ⊗ H`, `x ↦ x ⊗ 1`, lands in the cocycles of degree zero of the Hochschild
complex of `N ⊗ H`. -/
theorem hochschildDifferential_zero_comp_mk_flip_one :
    hochschildDifferential R H (N ⊗[R] H) 0 ∘ₗ (TensorProduct.mk R N H).flip 1 = 0 := by
  ext x
  rw [LinearMap.comp_apply, hochschildDifferential_zero_apply]
  simp [Algebra.TensorProduct.one_def]

/-- The homotopy condition in degree zero, on cochains. -/
private theorem homotopy_comm_zero_apply (x : hochschildCochains R H (N ⊗[R] H) 0) :
    ((TensorProduct.mk R N H).flip 1 ∘ₗ cofreeCounit R H N) x =
      (-hochschildExtraCodegeneracy R H N 0) (hochschildDifferential R H (N ⊗[R] H) 0 x) + x := by
  have h := LinearMap.congr_fun
    (hochschildExtraCodegeneracy_comp_hochschildDifferential_zero R H N) x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h
  simp only [LinearMap.neg_apply, h]
  abel

/-- The homotopy condition in positive degrees, on cochains. -/
private theorem homotopy_comm_succ_apply (n : ℕ) (x : hochschildCochains R H (N ⊗[R] H) (n + 1)) :
    (0 : hochschildCochains R H (N ⊗[R] H) (n + 1)) =
      (-hochschildExtraCodegeneracy R H N (n + 1))
          (hochschildDifferential R H (N ⊗[R] H) (n + 1) x) +
        hochschildDifferential R H (N ⊗[R] H) n ((-hochschildExtraCodegeneracy R H N n) x) + x := by
  have h := LinearMap.congr_fun
    (hochschildExtraCodegeneracy_comp_hochschildDifferential_succ R H N n) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
  simp only [LinearMap.neg_apply, map_neg]
  exact (sub_eq_zero.mpr h.symm).symm.trans (by abel)

/-- The Hochschild complex of the cofree comodule `N ⊗ H` is homotopy equivalent to `N` placed in
degree zero. The map to `N` applies the counit, `x ⊗ h ↦ ε(h) x`, and the map from `N` is
`x ↦ x ⊗ 1`; the homotopy is given by the extra codegeneracy. -/
noncomputable def hochschildComplexCofreeHomotopyEquiv :
    HomotopyEquiv (hochschildComplex R H (N ⊗[R] H))
      ((CochainComplex.single₀ (ModuleCat.{max v w} R)).obj (ModuleCat.of R N)) where
  hom := (CochainComplex.toSingle₀Equiv _ _).symm
    (ConcreteCategory.ofHom (C := ModuleCat R) (X := (hochschildComplex R H (N ⊗[R] H)).X 0)
      (cofreeCounit R H N))
  inv := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨ConcreteCategory.ofHom (C := ModuleCat R) (Y := (hochschildComplex R H (N ⊗[R] H)).X 0)
      ((TensorProduct.mk R N H).flip 1), by
      rw [hochschildComplex_d]
      exact ModuleCat.hom_ext (hochschildDifferential_zero_comp_mk_flip_one R H N)⟩
  homotopyHomInvId :=
    { hom i j := if h : j + 1 = i then
        eqToHom (congrArg (hochschildComplex R H (N ⊗[R] H)).X h.symm) ≫
          ConcreteCategory.ofHom (C := ModuleCat R)
            (X := (hochschildComplex R H (N ⊗[R] H)).X (j + 1))
            (Y := (hochschildComplex R H (N ⊗[R] H)).X j) (-hochschildExtraCodegeneracy R H N j)
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
      ConcreteCategory.ofHom (C := ModuleCat R) (X := (hochschildComplex R H (N ⊗[R] H)).X 0)
        (cofreeCounit R H N) :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero _

/-- In degree zero, the map from `N` to the Hochschild complex of `N ⊗ H` is `x ↦ x ⊗ 1`. -/
@[simp]
theorem hochschildComplexCofreeHomotopyEquiv_inv_f_zero :
    (hochschildComplexCofreeHomotopyEquiv R H N).inv.f 0 =
      ConcreteCategory.ofHom (C := ModuleCat R) (Y := (hochschildComplex R H (N ⊗[R] H)).X 0)
        ((TensorProduct.mk R N H).flip 1) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The Hochschild cohomology of the cofree comodule `N ⊗ H` vanishes in positive degrees. -/
theorem exactAt_hochschildComplex_cofree_succ (n : ℕ) :
    (hochschildComplex R H (N ⊗[R] H)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (HomologicalComplex.isZero_single_obj_homology _ _ _ _ n.succ_ne_zero).of_iso
    ((hochschildComplexCofreeHomotopyEquiv R H N).toHomologyIso (n + 1))

/-- The Hochschild cohomology of the cofree comodule `N ⊗ H` in degree zero is `N`, by the map
induced by the counit `x ⊗ h ↦ ε(h) x`. -/
noncomputable def hochschildComplexCofreeHomologyZeroIso :
    (hochschildComplex R H (N ⊗[R] H)).homology 0 ≅ ModuleCat.of R N :=
  (hochschildComplexCofreeHomotopyEquiv R H N).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

/-- The identification of the degree zero Hochschild cohomology of `N ⊗ H` with `N` sends the
class of a cocycle `x` to `(id ⊗ ε) x`. -/
@[reassoc (attr := simp)]
theorem homologyπ_hochschildComplexCofreeHomologyZeroIso_hom :
    (hochschildComplex R H (N ⊗[R] H)).homologyπ 0 ≫
        (hochschildComplexCofreeHomologyZeroIso R H N).hom =
      (hochschildComplex R H (N ⊗[R] H)).iCycles 0 ≫
        ConcreteCategory.ofHom (C := ModuleCat R) (X := (hochschildComplex R H (N ⊗[R] H)).X 0)
          (Y := ModuleCat.of R N) (cofreeCounit R H N) := by
  simp only [hochschildComplexCofreeHomologyZeroIso, HomotopyEquiv.toHomologyIso,
    Iso.trans_hom, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc]
  simp [hochschildComplexCofreeHomotopyEquiv_hom_f_zero, CochainComplex.single₀ObjXSelf]

end TauCeti.Comodule
