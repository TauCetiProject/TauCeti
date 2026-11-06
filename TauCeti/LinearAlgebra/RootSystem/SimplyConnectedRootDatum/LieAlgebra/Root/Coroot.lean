/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.System
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CartanLattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Coroot

/-!
# Coroot coordinates and rank-one words at every root

The Killing coroot at every numbered root is the integral combination of the simple Cartan
vectors specified by the simply connected root datum. Consequently its binomial coefficients
belong to the simple-generator Kostant form. These are the Cartan inputs for the rank-one
root-word identities at nonsimple roots.

`TauCeti.DynkinType.chevalleyRootSubgroup_mul_mul_eq_torus_mul` identifies
`x_α(s) x_{-α}(-s⁻¹) x_α(s)` with the coroot value times the same word at `s = 1`,
for every root on a Kostant-stable weight lattice over every commutative value ring.
It requires that the coroot act nontrivially on the rational representation, as holds for a
faithful Chevalley datum. The torus used here is the full-weight parametrization; the theorem
identifies its coroot values and does not assert that this parametrization reaches the entire
torus of an arbitrary datum.

The coordinate transport follows the existing type-F₄ calculation
`TauCeti.DynkinType.f4KillingCoroot_eq_sum_simple`. The root-word identity applies the generic
`kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL`
from `TauCeti.UniversalEnvelopingAlgebra` to the single Cartan vector of the chosen coroot;
the integral-coordinate calculation supplies its admissibility and weight equations.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 1–3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling

variable (t : DynkinType) (ht : t.Valid)

attribute [local instance] TauCeti.moduleNNRat

/-- Every Killing coroot has the simple-coroot coordinates of the pinned integral datum. -/
theorem coroot_rootEquiv_eq_sum (α : Fin t.numRoots) :
    ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
        (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht) =
      ∑ i, (t.simplyConnectedRootDatum ht).coroot α i • (t.lieBasis ht).h i := by
  let E := t.rationalRootSystemEquiv ht
  have hcoroot : E.coweightEquiv.symm ((t.rationalRootSystem ht).coroot α) =
      (rootSystem (t.cartanSubalgebra ht)).coroot (t.rootEquiv ht α) := by
    apply E.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply, RootPairing.Equiv.coweightEquiv_apply]
    simpa only [rootEquiv_eq_indexEquiv, Equiv.symm_apply_apply] using
      (RootPairing.Hom.coroot_coweightMap_apply _ _ (E.indexEquiv α) E.toHom).symm
  have hsimple (i : Fin t.rank) :
      E.coweightEquiv.symm (Pi.single i 1) = t.cartanBasis ht i := by
    have hs : (t.rationalRootSystem ht).coroot (t.simpleIndex ht i) = Pi.single i 1 := by
      ext j
      simp only [coroot_rationalRootSystem, coroot_simpleIndex]
      by_cases hij : i = j <;> simp [hij]
    rw [← hs, rationalRootSystemEquiv_coweightEquiv_symm_coroot_simpleIndex]
    -- The Cartan basis and the simple Killing coroot have the same underlying Lie vector.
    apply Subtype.ext
    rw [rootSystem_coroot_apply, (t.lieBasis ht).coroot_eq_h', coe_cartanBasis]
    rfl
  have hexp := congrArg E.coweightEquiv.symm
    (pi_eq_sum_univ' ((t.rationalRootSystem ht).coroot α))
  rw [map_sum] at hexp
  simp only [map_smul, hsimple, coroot_rationalRootSystem] at hexp
  rw [hcoroot] at hexp
  simpa [rootSystem_coroot_apply, coe_cartanBasis, Int.cast_smul_eq_zsmul ℚ] using
    congrArg Subtype.val hexp

/-- The binomial coefficients of every numbered Killing coroot belong to the Kostant form
presented using only the simple root and Cartan generators. -/
theorem ringChoose_coroot_rootEquiv_mem_kostantForm (α : Fin t.numRoots) (n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
        (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)) n ∈
      UniversalEnvelopingAlgebra.kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h := by
  apply UniversalEnvelopingAlgebra.ringChoose_mem_kostantForm_of_mem_span
  · intro i j
    exact (t.lieBasis ht).lie_h_h i j
  · rw [coroot_rootEquiv_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))

section Representation

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

variable {t ht} {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

include hM hnil in
/-- Admissibility for all root vectors and the single Cartan vector of any chosen coroot follows
from admissibility for the simple-generator Kostant form. -/
theorem kostantForm_chevalleySystem_coroot_apply_mem (α : Fin t.numRoots)
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)}
    (hu : u ∈ kostantForm (t.chevalleySystem ht)
      (fun _ : Unit => ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ
        (t.cartanSubalgebra ht) (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)))
    {v : V} (hv : v ∈ M) : ρ u v ∈ M := by
  apply kostantForm_apply_mem _ _ ρ M.toIntSubmodule _ _ u hu hv
  · intro γ n w hw
    rw [Associative.map_dividedPower]
    exact dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ n w hw
  · intro _ n w hw
    exact hM _ (t.ringChoose_coroot_rootEquiv_mem_kostantForm ht α n) w hw

/-- An integral Cartan weight evaluates on a numbered coroot by the native coroot coordinates. -/
theorem apply_ι_coroot_rootEquiv_of_isCartanWeightVector {μ : Fin t.rank → ℤ} {v : V}
    (hv : IsCartanWeightVector (t.lieBasis ht).h ρ μ v) (α : Fin t.numRoots) :
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
        (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)) v =
      ((∑ i, (t.simplyConnectedRootDatum ht).coroot α i * μ i : ℤ) : ℚ) • v := by
  rw [t.coroot_rootEquiv_eq_sum ht]
  rw [isCartanWeightVector_iff] at hv
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, hv,
    Int.cast_sum, Int.cast_mul, Finset.sum_smul, mul_smul, Int.cast_smul_eq_zsmul ℚ]

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem rootSubgroupParam_coroot_eq (α γ : Fin t.numRoots) (A : CommAlgCat ℤ)
    (u : Multiplicative A) :
    kostantRootSubgroupParam (t.chevalleySystem ht)
      (fun _ : Unit => ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ
        (t.cartanSubalgebra ht) (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht))
      ρ M (fun _ hu _ hv => kostantForm_chevalleySystem_coroot_apply_mem ρ M hM hnil α hu hv)
      γ (isNilpotent_apply_ι_chevalleySystem ρ hnil γ) A u =
      chevalleyRootSubgroup ρ M hM hnil γ A u := by
  refine Units.ext (LinearMap.ext fun z => ?_)
  rw [kostantRootSubgroupParam_val_apply, chevalleyRootSubgroup_val]

variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → Fin t.rank → ℤ)
variable (hwt : ∀ j, IsCartanWeightVector (t.lieBasis ht).h ρ (wt j) (b j : V))

include hwt in
/-- Chevalley's rank-one identity at every numbered root. The torus parameter is the native
coroot, including at nonsimple roots. The only nondegeneracy assumption is that this coroot acts
nontrivially on the rational representation; in particular a faithful Chevalley datum qualifies.
The coefficient ring may have arbitrary characteristic and may be nonreduced. -/
theorem chevalleyRootSubgroup_mul_mul_eq_torus_mul (α : Fin t.numRoots)
    (hH : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
        (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)) ≠ 0)
    (A : CommAlgCat ℤ) (s : Aˣ) :
    chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd (s : A)) *
        chevalleyRootSubgroup ρ M hM hnil
          ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A
          (Multiplicative.ofAdd (-((s⁻¹ : Aˣ) : A))) *
        chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd (s : A)) =
      kostantTorusPoints M b wt A (fun i => s ^ (t.simplyConnectedRootDatum ht).coroot α i) *
        (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd 1) *
          chevalleyRootSubgroup ρ M hM hnil
            ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A (Multiplicative.ofAdd (-1)) *
          chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd 1)) := by
  let H : Unit → t.lieAlgebra ht := fun _ =>
    ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
      (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)
  let W : η → Unit → ℤ := fun j _ => ∑ i, (t.simplyConnectedRootDatum ht).coroot α i * wt j i
  let hM' := fun u hu v hv => kostantForm_chevalleySystem_coroot_apply_mem ρ M hM hnil α
    (u := u) hu (v := v) hv
  have hw j : IsCartanWeightVector H ρ (W j) (b j : V) := by
    rw [isCartanWeightVector_iff]
    exact fun _ => apply_ι_coroot_rootEquiv_of_isCartanWeightVector ρ (hwt j) α
  have hT := (t.isSl2Triple_chevalleySystem ht α).map
    (ρ.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) hH
  have hα : ∀ j, ⁅H j, t.chevalleySystem ht α⁆ = ((fun _ : Unit => 2) j : ℚ) •
      t.chevalleySystem ht α := fun _ => (t.isSl2Triple_chevalleySystem ht α).lie_h_e_smul ℚ
  have hneg : ∀ j, ⁅H j, t.chevalleySystem ht
      ((t.simplyConnectedRootDatum ht).reflectionPerm α α)⁆ =
      -(((fun _ : Unit => 2) j : ℚ) • t.chevalleySystem ht
        ((t.simplyConnectedRootDatum ht).reflectionPerm α α)) := fun _ =>
    (t.isSl2Triple_chevalleySystem ht α).lie_lie_smul_f ℚ
  have htorus : kostantCoordinateCocharacter M b W A () s =
      kostantTorusPoints M b wt A (fun i => s ^ (t.simplyConnectedRootDatum ht).coroot α i) := by
    refine Units.ext (Module.Basis.ext (b.baseChange A) fun j => ?_)
    simp only [Module.Basis.baseChange_apply, kostantCoordinateCocharacter_tmul_basis,
      kostantTorusPoints_tmul_basis, W, torusCharacter_def, ← zpow_mul,
      Finset.prod_zpow_eq_zpow_sum]
  have h := kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL
    (t.chevalleySystem ht) H ρ M hM' b W hw (c := ()) hT
    (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil _) hα hneg A s
  rw [kostantWeylGL_eq_kostantRootSubgroupParam_mul] at h
  -- Expose the local Cartan family so that the change-of-presentation lemma matches it.
  dsimp only [H] at h
  simpa only [rootSubgroupParam_coroot_eq ρ M hM hnil α _ A, htorus] using h

end Representation

end TauCeti.DynkinType
