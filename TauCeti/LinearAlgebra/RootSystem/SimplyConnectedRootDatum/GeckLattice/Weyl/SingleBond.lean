/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond

/-!
# The parameter sign at a single bond of the Geck carrier

For two simple roots joined by a single bond, the Weyl presentations `([i], j)` and
`([j], i)` represent the same sum root. Their root-subgroup parameters have opposite signs.
The equality here holds over every commutative ring, including nonreduced rings and rings of
characteristic two. It is a comparison of the actual transported subgroups, not merely of
their root labels or torus characters.

The sign is determined by the ordered bracket: the pinned Weyl element at `i` carries the
raising operator at `j` to their bracket. Interchanging `i` and `j` negates that bracket.
Integral divided-power exponentials then transport this identity to arbitrary value rings.
No independence for longer Weyl presentations, reductivity, or identification with an
independently pinned simply connected group scheme is asserted.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.

The integral transport uses `TauCeti.baseChange_integralUnitRestrict_conj_baseChangeExp`,
the same construction underlying the Kostant Weyl conjugation API.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

local notation "ρ" => t.geckRepresentation ht
local notation "E" => LieAlgebra.Basis.rootGenerator (t.lieBasis ht)
local notation "H" => LieAlgebra.Basis.h (t.lieBasis ht)
local notation "M" => Submodule.toAddSubgroup (t.geckCoordinateLattice ht)
local notation "hM" => t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht
local notation "hnil" => t.isNilpotent_geckRepresentation_rootGenerator ht
local notation "X" => (fun i => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (E (Sum.inl i))))
local notation "N" => (fun i => weylUnit (hnil (Sum.inl i)) (hnil (Sum.inr i)))

private theorem kostantWeyl_conj_raising_singleBond (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type v) [CommRing A] (u : A) :
    kostantWeylGL E H ρ M hM (hnil (.inl i)) (hnil (.inr i)) A *
        kostantRootSubgroupParam E H ρ M hM (.inl j) (hnil (.inl j))
          (CommAlgCat.of ℤ A) (Multiplicative.ofAdd u) *
        (kostantWeylGL E H ρ M hM (hnil (.inl i)) (hnil (.inr i)) A)⁻¹ =
      kostantWeylGL E H ρ M hM (hnil (.inl j)) (hnil (.inr j)) A *
        kostantRootSubgroupParam E H ρ M hM (.inl i) (hnil (.inl i))
          (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (-u)) *
        (kostantWeylGL E H ρ M hM (hnil (.inl j)) (hnil (.inr j)) A)⁻¹ := by
  -- First compare the rational conjugated operators and their stable divided powers.
  let C := fun i j => (N i : Module.End ℚ (t.GeckIndex ht → ℚ)) * X j * ↑(N i)⁻¹
  let hX : ∀ i n, ∀ v ∈ M, Associative.dividedPower n (X i) • v ∈ M :=
    fun i n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem E H ρ hM (.inl i) n hv
  let hN : ∀ i, ∀ v ∈ M, (N i : Module.End ℚ (t.GeckIndex ht → ℚ)) • v ∈ M :=
    fun i _ hv => weylUnit_smul_mem E H ρ M hM (hnil (.inl i)) (hnil (.inr i)) hv
  let hNinv : ∀ i, ∀ v ∈ M,
      (((N i)⁻¹ : (Module.End ℚ (t.GeckIndex ht → ℚ))ˣ) :
        Module.End ℚ (t.GeckIndex ht → ℚ)) • v ∈ M :=
    fun i _ hv => inv_weylUnit_smul_mem E H ρ M hM (hnil (.inl i)) (hnil (.inr i)) hv
  let hC : ∀ i j n, ∀ v ∈ M, Associative.dividedPower n (C i j) • v ∈ M :=
    fun i j n => Associative.dividedPower_conj_smul_mem (X j)
      (M : Set (t.GeckIndex ht → ℚ)) (N i) (hN i) (hNinv i) n (hX j n)
  let φ := (ρ).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  have hs := (t.isSerreSystem_lieBasis ht).map φ
  have hE (k : Fin t.rank) : IsNilpotent (φ ((t.lieBasis ht).e k)) := by
    simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inl] using hnil (.inl k)
  have hF (k : Fin t.rank) : IsNilpotent (φ ((t.lieBasis ht).f k)) := by
    simpa only [φ, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inr] using hnil (.inr k)
  have hCeq (k l : Fin t.rank) (hkl : t.cartanMatrix l k = -1) :
      C k l = ⁅X k, X l⁆ := by
    simpa only [C, φ, Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply,
      LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
      hs.weylUnit_conj_E_of_cartan_eq_neg_one (by simp) hkl (hE k) (hF k)
  have hsign : C i j = -C j i := by rw [hCeq i j hji, hCeq j i hij, lie_skew]
  have hneg : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (-C j i) • v ∈ M :=
    fun n => Associative.dividedPower_neg_smul_mem _ M (hC j i n)
  -- Base change conjugation on the lattice, then negate the exponential's parameter.
  have hpoint (i j : Fin t.rank) (u : A) :
      (kostantWeylPoints E H ρ M hM (hnil (.inl i)) (hnil (.inr i)) A).toLinearMap *
          baseChangeExp (X j) M (hX j) u *
          (kostantWeylPoints E H ρ M hM (hnil (.inl i)) (hnil (.inr i)) A).symm.toLinearMap =
        baseChangeExp (C i j) M (hC i j) u := by
    rw [kostantWeylPoints_toLinearMap, kostantWeylPoints_symm_toLinearMap,
      kostantWeylRestrict_eq_integralUnitRestrict]
    exact baseChange_integralUnitRestrict_conj_baseChangeExp (X j) M (N i)
      (hN i) (hNinv i) (hX j) u
  have hexp := (hpoint i j u).trans
    ((baseChangeExp_congr hsign M (hC i j) hneg u).trans
      ((baseChangeExp_neg (C j i) M hneg (hC j i) u).trans
        (hpoint j i (-u)).symm))
  -- Read the root parameters before passing to underlying endomorphisms.
  rw [kostantRootSubgroupParam_apply, kostantRootSubgroupParam_apply]
  apply Units.ext
  simpa only [Units.val_mul, kostantWeylGL_val, kostantWeylGL_inv_val,
    kostantRootSubgroupPoints_val, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hexp

/-- The two one-step Weyl presentations of the sum root at a single bond have opposite
parameters, over every commutative value ring. -/
theorem geckWeylRootSubgroupPoints_singleton_eq_singleton_neg (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type v) [CommRing A] (u : A) :
    t.geckWeylRootSubgroupPoints ht [i] j A (Multiplicative.ofAdd u) =
      t.geckWeylRootSubgroupPoints ht [j] i A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.coe_injective
  simp only [geckWeylRootSubgroupPoints_apply, geckWeylWordPoint_cons,
    geckWeylWordPoint_nil, mul_one, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_geckSimpleWeylPoint, coe_geckRootSubgroupPoints]
  let f := Units.map ((LinearMap.toMatrixAlgEquiv
    ((t.geckCoordinateBasisFin ht).baseChange A)).toMulEquiv.toMonoidHom)
  have hmatrix (k : Fin t.rank) (v : A) :
      f (kostantRootSubgroupParam E H ρ M hM (.inl k) (hnil (.inl k))
        (CommAlgCat.of ℤ A) (Multiplicative.ofAdd v)) =
      t.geckRootSubgroupMatrix ht (.inl k)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
          (Multiplicative.ofAdd v)) :=
    basisMatrix_kostantRootSubgroupParam E H ρ M hM hnil
      (t.geckCoordinateBasisFin ht) A (.inl k) (Multiplicative.ofAdd v)
  have h := congrArg f (t.kostantWeyl_conj_raising_singleBond ht i j hij hji A u)
  simp only [map_mul, map_inv] at h
  rw [hmatrix j u, hmatrix i (-u)] at h
  simpa only [f, MulEquiv.toMonoidHom_eq_coe] using h

end

end TauCeti.DynkinType
