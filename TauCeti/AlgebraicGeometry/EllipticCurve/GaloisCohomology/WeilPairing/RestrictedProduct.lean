/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
public import TauCeti.Topology.Algebra.RestrictedProduct.Pairing

/-!
# The restricted-product local isogeny pairing

Sum the normalized local Tate pairings over a family of nonarchimedean local fields.
The reference subgroups are the kernels defining the isogeny Selmer local conditions;
for a separable isogeny these are its Kummer images. Orthogonality of these subgroups
makes the sum finite on the restricted products, not just on finitely supported families.
The sum is biadditive, separates the first argument, and vanishes on the full products
of the two local conditions.

For a number field, apply this to its finite completions and the base changes of one
isogeny. This gives the finite-place part of the adelic pairing used in global duality.
No exact-annihilator or global duality assertion is assumed here, and archimedean factors
are not included.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve ContCohomology Hom
open scoped RestrictedProduct

variable {ι : Type*} {K : ι → Type} [∀ i, Field (K i)]
  [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)]
  [∀ i, IsNonarchimedeanLocalField (K i)]
  {W₁ W₂ : ∀ i, WeierstrassCurve (K i)} [∀ i, (W₁ i).IsElliptic]
  [∀ i, (W₂ i).IsElliptic]
  (φ : ∀ i, Isogeny (W₁ i).toAffine (W₂ i).toAffine)
  (hn : ∀ i, IsUnit ((φ i).degree : K i))

/-- The restricted product of local kernel cohomology with respect to the Selmer local
conditions. The parameter is a family of isogenies, so it also applies to the family of
local duals without identifying a dual with a base-changed global dual. -/
abbrev RestrictedLocalH1 :=
  Πʳ i, [H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i)).KerCoeff,
    (explicitCoeff1 _ _ (ofIsogeny (φ i)).kerCoeffIncl continuous_of_discreteTopology).ker]

/-- The local Tate pairing at an index, composed with the normalization into `ℚ/ℤ`. -/
private def normalizedLocalTateKerWeilPairing (i : ι) :
    H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i)).KerCoeff →+
      H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i).dual).KerCoeff →+ AddCircle (1 : ℚ) :=
  (AddMonoidHom.compHom (ZMod.toRatAddCircle (φ i).degree)).comp
    ((φ i).localTateKerWeilPairing (hn i))

@[simp]
private theorem normalizedLocalTateKerWeilPairing_apply (i : ι)
    (a : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i)).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i).dual).KerCoeff) :
    normalizedLocalTateKerWeilPairing φ hn i a b =
      ZMod.toRatAddCircle (φ i).degree ((φ i).localTateKerWeilPairing (hn i) a b) := by
  simp only [normalizedLocalTateKerWeilPairing, AddMonoidHom.comp_apply,
    AddMonoidHom.compHom_apply_apply]

private theorem normalizedLocalTateKerWeilPairing_eq_zero_of_mem_ker (i : ι)
    (a : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i)).KerCoeff)
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny (φ i)).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (b : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i).dual).KerCoeff)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny (φ i).dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    normalizedLocalTateKerWeilPairing φ hn i a b = 0 := by
  simp only [normalizedLocalTateKerWeilPairing_apply, localTateKerWeilPairing_apply,
    (φ i).kerH1WeilPairing_eq_zero_of_mem_ker (hn i) ha hb, map_zero]

/-- The normalized local isogeny pairings have finite support on restricted cohomology
families. The isogeny degree may be divisible by the residue characteristic. -/
theorem hasFiniteSupport_localTateKerWeilPairing
    (x : RestrictedLocalH1 φ) (y : RestrictedLocalH1 fun i ↦ (φ i).dual) :
    (fun i ↦ ZMod.toRatAddCircle (φ i).degree
      ((φ i).localTateKerWeilPairing (hn i) (x i) (y i))).HasFiniteSupport := by
  simpa only [normalizedLocalTateKerWeilPairing_apply] using
    RestrictedProduct.hasFiniteSupport_pairing _ _ (normalizedLocalTateKerWeilPairing φ hn)
      (normalizedLocalTateKerWeilPairing_eq_zero_of_mem_ker φ hn) x y

/-- Sum of the local isogeny pairings, normalized in `ℚ/ℤ`, on restricted cohomology
families. The sum is finite because the Selmer local conditions are orthogonal. -/
def restrictedLocalTateKerWeilPairing :
    RestrictedLocalH1 φ →+ RestrictedLocalH1 (fun i ↦ (φ i).dual) →+ AddCircle (1 : ℚ) :=
  RestrictedProduct.sumPairing _ _ (normalizedLocalTateKerWeilPairing φ hn)
    (normalizedLocalTateKerWeilPairing_eq_zero_of_mem_ker φ hn)

/-- The restricted pairing is the sum of normalized local values. -/
theorem restrictedLocalTateKerWeilPairing_apply
    (x : RestrictedLocalH1 φ) (y : RestrictedLocalH1 fun i ↦ (φ i).dual) :
    restrictedLocalTateKerWeilPairing φ hn x y =
      ∑ᶠ i, ZMod.toRatAddCircle (φ i).degree
        ((φ i).localTateKerWeilPairing (hn i) (x i) (y i)) := by
  simp only [restrictedLocalTateKerWeilPairing, RestrictedProduct.sumPairing_apply,
    normalizedLocalTateKerWeilPairing_apply]

/-- Pairing with a family supported at one place recovers the normalized local pairing. -/
@[simp]
theorem restrictedLocalTateKerWeilPairing_single_right [DecidableEq ι]
    (x : RestrictedLocalH1 φ) (i : ι)
    (b : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i).dual).KerCoeff) :
    restrictedLocalTateKerWeilPairing φ hn x (RestrictedProduct.single _ i b) =
      ZMod.toRatAddCircle (φ i).degree ((φ i).localTateKerWeilPairing (hn i) (x i) b) := by
  simp only [restrictedLocalTateKerWeilPairing, RestrictedProduct.sumPairing_single_right,
    normalizedLocalTateKerWeilPairing_apply]

/-- A family supported at one place in the first argument also recovers the local pairing. -/
@[simp]
theorem restrictedLocalTateKerWeilPairing_single_left [DecidableEq ι]
    (i : ι) (a : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i)).KerCoeff)
    (y : RestrictedLocalH1 fun i ↦ (φ i).dual) :
    restrictedLocalTateKerWeilPairing φ hn (RestrictedProduct.single _ i a) y =
      ZMod.toRatAddCircle (φ i).degree ((φ i).localTateKerWeilPairing (hn i) a (y i)) := by
  simp only [restrictedLocalTateKerWeilPairing, RestrictedProduct.sumPairing_single_left,
    normalizedLocalTateKerWeilPairing_apply]

/-- The restricted pairing detects every nonzero first argument by local Tate duality. -/
theorem restrictedLocalTateKerWeilPairing_injective :
    Function.Injective (restrictedLocalTateKerWeilPairing φ hn) := by
  apply RestrictedProduct.sumPairing_injective
  intro i a b hab
  apply (φ i).localTateKerWeilPairing_bijective (hn i) |>.injective
  apply AddMonoidHom.ext
  intro c
  apply ZMod.toRatAddCircle_injective (φ i).degree
  simpa only [normalizedLocalTateKerWeilPairing_apply] using DFunLike.congr_fun hab c

/-- Families satisfying the Selmer local conditions everywhere are orthogonal, even if
they are nonzero at infinitely many indices. -/
theorem restrictedLocalTateKerWeilPairing_eq_zero_of_forall_mem_ker
    (x : RestrictedLocalH1 φ) (y : RestrictedLocalH1 fun i ↦ (φ i).dual)
    (hx : ∀ i, x i ∈ (explicitCoeff1 _ _ (ofIsogeny (φ i)).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hy : ∀ i, y i ∈ (explicitCoeff1 _ _ (ofIsogeny (φ i).dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    restrictedLocalTateKerWeilPairing φ hn x y = 0 := by
  unfold restrictedLocalTateKerWeilPairing
  exact RestrictedProduct.sumPairing_eq_zero_of_forall _ _ _ _ x y fun i ↦
    normalizedLocalTateKerWeilPairing_eq_zero_of_mem_ker φ hn i _ (hx i) _ (hy i)

end TauCeti.Isogeny
