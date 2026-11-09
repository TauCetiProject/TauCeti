/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Exact
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.FiniteFree
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Quotient
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FiniteModuleTopology
import Mathlib.Analysis.Matrix.Normed

/-!
# Presentations of module-valued restricted series

For a coefficient submodule `N ≤ Rⁱ`, the coefficient quotient induces a map from a finite free
module over the restricted-series ring to restricted series valued in `Rⁱ/N`. It is a quotient
map for the Gauss topologies when `N` is closed.

If `R` is itself a Tate algebra over a complete ultrametric field, a matrix presenting `N`
presents all relations among these series: the matrix is unchanged, with its entries included
as constant series. The crucial input is the uniform bound on preimages on the range of a
linear map into a finite free Tate module. Thus coefficient lifts still tend to zero with the
prescribed weights. No spherical completeness or discrete valuation is needed, and the new
variables and their positive radii are arbitrary.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollaries 8–10.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §§3.7.2–3.7.3, 5.1.1.
-/

public section

noncomputable section

open TauCeti.MvPowerSeries.IsRestrictedFamily (Gauss)
open TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss

namespace Submodule

open _root_.MvPowerSeries

variable {σ ι κ R : Type*} [Fintype ι] [Fintype κ]
  [NormedCommRing R] [IsUltrametricDist R]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- The finite free presentation map to series with coefficients in a quotient module.
It assembles the coefficient vectors and then applies the coefficient quotient. -/
def restrictedFamilyPresentation (N : Submodule R (ι → R)) :
    (ι → IsRestricted.subring (R := R) c) →ₗ[IsRestricted.subring (R := R) c]
      Gauss c ((ι → R) ⧸ N) where
  toFun a := N.gaussFamilyMkQ ((piRingLinearIsometryEquiv R c).symm a)
  map_add' a b := by simp
  map_smul' f a := by
    simp only [RingHom.id_apply, LinearIsometryEquiv.map_smul]
    exact N.gaussFamilyMkQ_isRestrictedSubring_smul f _

/-- Each coefficient is the class of the vector of coefficients in the free coordinates. -/
@[simp]
theorem restrictedFamilyPresentation_apply (N : Submodule R (ι → R))
    (a : ι → IsRestricted.subring (R := R) c) (t : σ →₀ ℕ) :
    N.restrictedFamilyPresentation a t =
      Submodule.Quotient.mk
        (fun i ↦ _root_.MvPowerSeries.coeff t (a i : MvPowerSeries σ R)) := by
  dsimp only [Submodule.restrictedFamilyPresentation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Submodule.gaussFamilyMkQ_apply]
  congr 1
  funext i
  exact piRingLinearIsometryEquiv_symm_apply a t i

/-- Passing to quotient coefficients does not increase the maximum Gauss norm. -/
theorem norm_restrictedFamilyPresentation_le (N : Submodule R (ι → R))
    (a : ι → IsRestricted.subring (R := R) c) :
    ‖N.restrictedFamilyPresentation a‖ ≤ ‖a‖ := by
  exact (N.norm_gaussFamilyMkQ_le _).trans_eq
    ((piRingLinearIsometryEquiv R c).symm.norm_map a)

/-- The presentation map is continuous for the Gauss topologies. -/
theorem continuous_restrictedFamilyPresentation (N : Submodule R (ι → R)) :
    Continuous (Submodule.restrictedFamilyPresentation (c := c) N) :=
  (AddMonoidHomClass.uniformContinuous_of_bound (N.restrictedFamilyPresentation (c := c)) 1
    (fun a ↦ by simpa using N.norm_restrictedFamilyPresentation_le a)).continuous

/-- The kernel consists of tuples whose coefficient vectors lie in the relation submodule. -/
@[simp]
theorem restrictedFamilyPresentation_eq_zero_iff (N : Submodule R (ι → R))
    (a : ι → IsRestricted.subring (R := R) c) :
    N.restrictedFamilyPresentation a = 0 ↔
      ∀ t, (fun i ↦ _root_.MvPowerSeries.coeff t (a i : MvPowerSeries σ R)) ∈ N := by
  constructor
  · intro ha t
    exact (Submodule.Quotient.mk_eq_zero N).mp
      (by simpa using congrArg (fun b : Gauss c ((ι → R) ⧸ N) ↦ b t) ha)
  · intro ha
    ext t
    simpa using (Submodule.Quotient.mk_eq_zero N).mpr (ha t)

/-- Closed coefficient quotients give surjective presentation maps. -/
theorem restrictedFamilyPresentation_surjective (N : Submodule R (ι → R))
    [IsClosed (N : Set (ι → R))] :
    Function.Surjective (Submodule.restrictedFamilyPresentation (c := c) N) := by
  intro b
  obtain ⟨a, ha⟩ := N.gaussFamilyMkQ_surjective (c := c) b
  exact ⟨piRingLinearIsometryEquiv R c a, by simpa [restrictedFamilyPresentation] using ha⟩

/-- The finite free presentation induces precisely the Gauss topology on quotient-valued
restricted series. -/
theorem isQuotientMap_restrictedFamilyPresentation (N : Submodule R (ι → R))
    [IsClosed (N : Set (ι → R))] :
    Topology.IsQuotientMap (Submodule.restrictedFamilyPresentation (c := c) N) :=
  (N.isQuotientMap_gaussFamilyMkQ (c := c)).comp
    (piRingLinearIsometryEquiv R c).symm.toHomeomorph.isQuotientMap

end Submodule

namespace Matrix

open _root_.MvPowerSeries

variable {σ ι κ R : Type*} [Fintype ι] [Fintype κ]
  [NormedCommRing R] [IsUltrametricDist R]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- A coefficient relation matrix remains the relation matrix after adjoining restricted
variables, provided its range admits uniformly bounded coefficient lifts. -/
theorem range_map_mulVecLin_eq_ker_restrictedFamilyPresentation (A : Matrix ι κ R) {L : ℝ}
    (hlift : ∀ y ∈ LinearMap.range A.mulVecLin,
      ∃ x, A.mulVecLin x = y ∧ ‖x‖ ≤ L * ‖y‖) :
    LinearMap.range (A.map (algebraMap R (IsRestricted.subring (R := R) c))).mulVecLin =
      LinearMap.ker ((LinearMap.range A.mulVecLin).restrictedFamilyPresentation (c := c)) := by
  have hA := A.linfty_opNorm_mulVec
  ext b
  rw [LinearMap.mem_ker, Submodule.restrictedFamilyPresentation_eq_zero_iff]
  have hcoeff (t : σ →₀ ℕ) :
      (fun i ↦ _root_.MvPowerSeries.coeff t (b i : MvPowerSeries σ R)) =
        (piRingLinearIsometryEquiv R c).symm b t := by
    ext i
    exact (piRingLinearIsometryEquiv_symm_apply b t i).symm
  simp_rw [hcoeff]
  rw [← LinearMap.mem_range_gaussFamilyMap_iff A.mulVecLin hA hlift]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(piRingLinearIsometryEquiv R c).symm a, ?_⟩
    apply (piRingLinearIsometryEquiv R c).injective
    rw [A.piRingLinearIsometryEquiv_mapLinearMap hA]
    simp
  · rintro ⟨a, ha⟩
    refine ⟨piRingLinearIsometryEquiv R c a, ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [← A.piRingLinearIsometryEquiv_mapLinearMap hA, ha]
    exact (piRingLinearIsometryEquiv R c).apply_symm_apply b

section TateCoefficients

variable {τ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite τ]
  {d : τ → ℝ} [∀ j, Fact (0 < d j)]

local notation "T" => IsRestricted.subring (R := K) d

/-- **Exactness of finite presentations after adjoining restricted variables.** Every relation
matrix over a Tate algebra presents the quotient-valued restricted series through the same
matrix of constant series. Uniformly bounded lifts follow from strict finite-module theory. -/
theorem range_map_mulVecLin_eq_ker_restrictedFamilyPresentation_isRestricted_subring
    (A : Matrix ι κ T) :
    LinearMap.range (A.map (algebraMap T (IsRestricted.subring (R := T) c))).mulVecLin =
      LinearMap.ker ((LinearMap.range A.mulVecLin).restrictedFamilyPresentation (c := c)) := by
  obtain ⟨L, -, hlift⟩ := A.mulVecLin.exists_preimage_norm_le_pi_isRestricted_subring
  exact range_map_mulVecLin_eq_ker_restrictedFamilyPresentation A hlift

/-- The coefficient quotient in a finite Tate-module presentation remains a topological
quotient after adjoining restricted variables. -/
theorem isQuotientMap_restrictedFamilyPresentation_isRestricted_subring (A : Matrix ι κ T) :
    Topology.IsQuotientMap
      (Submodule.restrictedFamilyPresentation (c := c) (LinearMap.range A.mulVecLin)) := by
  have : IsClosed (LinearMap.range A.mulVecLin : Set (ι → T)) :=
    A.mulVecLin.isClosed_range_of_isRestricted_subring
  exact Submodule.isQuotientMap_restrictedFamilyPresentation _

/-- The cokernel of the unchanged relation matrix is topologically the restricted series
with coefficients in the presented finite Tate module. The source has its quotient topology. -/
def restrictedFamilyPresentationEquiv (A : Matrix ι κ T) :
    ((ι → IsRestricted.subring (R := T) c) ⧸
      LinearMap.range (A.map (algebraMap T (IsRestricted.subring (R := T) c))).mulVecLin) ≃L[
        IsRestricted.subring (R := T) c] Gauss c ((ι → T) ⧸ LinearMap.range A.mulVecLin) := by
  have : IsClosed (LinearMap.range A.mulVecLin : Set (ι → T)) :=
    A.mulVecLin.isClosed_range_of_isRestricted_subring
  let q := Submodule.restrictedFamilyPresentation (c := c) (LinearMap.range A.mulVecLin)
  let e := (Submodule.quotEquivOfEq _ _
    (range_map_mulVecLin_eq_ker_restrictedFamilyPresentation_isRestricted_subring (c := c) A)).trans
      (q.quotKerEquivOfSurjective (Submodule.restrictedFamilyPresentation_surjective _))
  have he (a : ι → IsRestricted.subring (R := T) c) :
      e (Submodule.Quotient.mk a) = q a := by
    simp [e]
  have hi (a : ι → IsRestricted.subring (R := T) c) :
      e.symm (q a) = Submodule.Quotient.mk a := by
    rw [← he]
    exact e.symm_apply_apply _
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (Submodule.isQuotientMap_mkQ _).continuous_iff.mpr
    exact ((LinearMap.range A.mulVecLin).continuous_restrictedFamilyPresentation (c := c)).congr
      (fun a ↦ (he a).symm)
  · apply ((LinearMap.range A.mulVecLin).isQuotientMap_restrictedFamilyPresentation
      (c := c)).continuous_iff.mpr
    exact continuous_quot_mk.congr (fun a ↦ (hi a).symm)

/-- The cokernel comparison takes a free tuple to the series of its coefficient classes. -/
@[simp]
theorem restrictedFamilyPresentationEquiv_mk (A : Matrix ι κ T)
    (a : ι → IsRestricted.subring (R := T) c) :
    restrictedFamilyPresentationEquiv A (Submodule.Quotient.mk a) =
      Submodule.restrictedFamilyPresentation (LinearMap.range A.mulVecLin) a := by
  simp [restrictedFamilyPresentationEquiv]

/-- The inverse cokernel comparison recovers the class of any free representative. -/
@[simp]
theorem restrictedFamilyPresentationEquiv_symm_restrictedFamilyPresentation
    (A : Matrix ι κ T)
    (a : ι → IsRestricted.subring (R := T) c) :
    (restrictedFamilyPresentationEquiv A).symm
      ((LinearMap.range A.mulVecLin).restrictedFamilyPresentation a) =
        Submodule.Quotient.mk a := by
  rw [← restrictedFamilyPresentationEquiv_mk]
  exact (restrictedFamilyPresentationEquiv A).symm_apply_apply _

end TateCoefficients

end Matrix
