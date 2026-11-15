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

/-- The normalized local isogeny pairings have finite support on restricted cohomology
families. The isogeny degree may be divisible by the residue characteristic. -/
theorem hasFiniteSupport_localTateKerWeilPairing
    (x : RestrictedLocalH1 φ) (y : RestrictedLocalH1 fun i ↦ (φ i).dual) :
    (fun i ↦ ZMod.toRatAddCircle (φ i).degree
      ((φ i).localTateKerWeilPairing (hn i) (x i) (y i))).HasFiniteSupport := by
  apply RestrictedProduct.hasFiniteSupport_pairing
    (p := fun i ↦ (AddMonoidHom.compHom (ZMod.toRatAddCircle (φ i).degree)).comp
      ((φ i).localTateKerWeilPairing (hn i)))
  intro i a ha b hb
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    (φ i).localTateKerWeilPairing_eq_zero_of_mem_ker (hn i) ha hb, map_zero]

/-- Sum of the local isogeny pairings, normalized in `ℚ/ℤ`, on restricted cohomology
families. The sum is finite because the Selmer local conditions are orthogonal. -/
def restrictedLocalTateKerWeilPairing :
    RestrictedLocalH1 φ →+ RestrictedLocalH1 (fun i ↦ (φ i).dual) →+ AddCircle (1 : ℚ) :=
  RestrictedProduct.sumPairing _ _
    (fun i ↦ (AddMonoidHom.compHom (ZMod.toRatAddCircle (φ i).degree)).comp
      ((φ i).localTateKerWeilPairing (hn i)))
    (fun i a ha b hb ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
        (φ i).localTateKerWeilPairing_eq_zero_of_mem_ker (hn i) ha hb, map_zero])

/-- The restricted pairing is the sum of normalized local values. -/
theorem restrictedLocalTateKerWeilPairing_apply
    (x : RestrictedLocalH1 φ) (y : RestrictedLocalH1 fun i ↦ (φ i).dual) :
    restrictedLocalTateKerWeilPairing φ hn x y =
      ∑ᶠ i, ZMod.toRatAddCircle (φ i).degree
        ((φ i).localTateKerWeilPairing (hn i) (x i) (y i)) := by
  unfold restrictedLocalTateKerWeilPairing
  rw [RestrictedProduct.sumPairing_apply]
  rfl

/-- Pairing with a family supported at one place recovers the normalized local pairing. -/
@[simp]
theorem restrictedLocalTateKerWeilPairing_single_right [DecidableEq ι]
    (x : RestrictedLocalH1 φ) (i : ι)
    (b : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i).dual).KerCoeff) :
    restrictedLocalTateKerWeilPairing φ hn x (RestrictedProduct.single _ i b) =
      ZMod.toRatAddCircle (φ i).degree ((φ i).localTateKerWeilPairing (hn i) (x i) b) := by
  unfold restrictedLocalTateKerWeilPairing
  rw [RestrictedProduct.sumPairing_single_right]
  rfl

/-- A family supported at one place in the first argument also recovers the local pairing. -/
@[simp]
theorem restrictedLocalTateKerWeilPairing_single_left [DecidableEq ι]
    (i : ι) (a : H1 (AbsoluteGaloisGroup (K i)) (ofIsogeny (φ i)).KerCoeff)
    (y : RestrictedLocalH1 fun i ↦ (φ i).dual) :
    restrictedLocalTateKerWeilPairing φ hn (RestrictedProduct.single _ i a) y =
      ZMod.toRatAddCircle (φ i).degree ((φ i).localTateKerWeilPairing (hn i) a (y i)) := by
  unfold restrictedLocalTateKerWeilPairing
  rw [RestrictedProduct.sumPairing_single_left]
  rfl

/-- The restricted pairing detects every nonzero first argument by local Tate duality. -/
theorem restrictedLocalTateKerWeilPairing_injective :
    Function.Injective (restrictedLocalTateKerWeilPairing φ hn) := by
  apply RestrictedProduct.sumPairing_injective
  intro i a b hab
  apply (φ i).localTateKerWeilPairing_bijective (hn i) |>.injective
  apply AddMonoidHom.ext
  intro c
  have := (hn i).neZero_natCast
  apply ZMod.toRatAddCircle_injective (φ i).degree
  exact DFunLike.congr_fun hab c

/-- Families satisfying the Selmer local conditions everywhere are orthogonal, even if
they are nonzero at infinitely many indices. -/
theorem restrictedLocalTateKerWeilPairing_eq_zero_of_forall_mem_ker
    (x : RestrictedLocalH1 φ) (y : RestrictedLocalH1 fun i ↦ (φ i).dual)
    (hx : ∀ i, x i ∈ (explicitCoeff1 _ _ (ofIsogeny (φ i)).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hy : ∀ i, y i ∈ (explicitCoeff1 _ _ (ofIsogeny (φ i).dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    restrictedLocalTateKerWeilPairing φ hn x y = 0 := by
  rw [restrictedLocalTateKerWeilPairing_apply]
  exact finsum_eq_zero_of_forall_eq_zero fun i ↦ by
    rw [(φ i).localTateKerWeilPairing_eq_zero_of_mem_ker (hn i) (hx i) (hy i), map_zero]

end TauCeti.Isogeny
