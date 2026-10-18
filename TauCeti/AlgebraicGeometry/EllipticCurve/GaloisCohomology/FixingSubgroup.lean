/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.DivisionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Tower
-- Proof-only: the identification of `G_L` with the subgroup of `G_K` fixing `σ(L)`.
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# Restriction to an embedded extension as restriction to a fixing subgroup

Let `W` be a Weierstrass curve over a field `K` and `L/K` an extension embedded in `Kˢ` by
`σ : L →ₐ[K] Kˢ`. Then `Kˢ` is a separable closure of `L`, and `G_L` is identified with the
subgroup `Gal(Kˢ/σ(L))` of `G_K` fixing `σ(L)` pointwise
(`TauCeti.absoluteGaloisGroupEquivFixingSubgroup`). Restriction of the Galois cohomology of `W`
to `L`, defined along an embedding of separable closures `τ : Kˢ → Lˢ`
(`WeierstrassCurve.pointRes`, `WeierstrassCurve.torsionRes`), is therefore the group-theoretic
restriction to `Gal(Kˢ/σ(L))` followed by an isomorphism. In particular the two restrictions have
the same kernel (`WeierstrassCurve.ker_pointRes`, `WeierstrassCurve.ker_torsionRes`), by
`TauCeti.ContCohomology.explicitMap1_eq_zero_iff_explicitRes1_eq_zero` applied to the bijective
coordinate maps `WeierstrassCurve.pointCoeffBaseChange_bijective` and
`WeierstrassCurve.torsionCoeffBaseChange_bijective`.

For the `m`-division field `L = K(E[m])` of an elliptic curve and `m ≠ 0`, the kernel of
group-theoretic restriction is finite by inflation-restriction
(`WeierstrassCurve.finite_ker_explicitRes1_divisionField`), so the restriction
`H¹(G_K, E[m]) → H¹(G_L, E[m])` has finite kernel
(`WeierstrassCurve.finite_ker_torsionRes_divisionField`). Since restriction also maps
`Sel_m(E/K)` into `Sel_m(E/K(E[m]))`, the finiteness of `Sel_m(E/K)` follows from that of
`Sel_m(E/K(E[m]))` (`WeierstrassCurve.finite_selmerGroup_of_finite_selmerGroup_divisionField`).
This is the step of the proof of the finiteness of the `m`-Selmer group (Silverman X.4.2) that
replaces `K` by `K(E[m])`, over which `E[m]` is rational.

## Main results

* `WeierstrassCurve.pointRes_eq_zero_iff`, `WeierstrassCurve.torsionRes_eq_zero_iff`: a class
  restricts to zero over `L` exactly when it restricts to zero on `Gal(Kˢ/σ(L))`.
* `WeierstrassCurve.ker_pointRes`, `WeierstrassCurve.ker_torsionRes`: the same statement for the
  kernels.
* `WeierstrassCurve.forall_smul_eq_torsionCoeff_divisionField`: over the `m`-division field, every
  point of `E[m]` is rational.
* `WeierstrassCurve.finite_ker_torsionRes_divisionField`: for `W` elliptic and `m ≠ 0`, restriction
  of `H¹(G_K, E[m])` to the `m`-division field has finite kernel.
* `WeierstrassCurve.finite_selmerGroup_of_finite_selmerGroup_divisionField`: hence `Sel_m(E/K)` is
  finite once `Sel_m(E/K(E[m]))` is.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (W : WeierstrassCurve K)
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-! ### Restriction to the fixing subgroup -/

variable (σ : L →ₐ[K] SeparableClosure K)

/-- **A class of `H¹(G_K, E(Kˢ))` restricts to zero over `L` exactly when it restricts to zero on
the subgroup `Gal(Kˢ/σ(L))` of `G_K`.** -/
theorem pointRes_eq_zero_iff {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff} :
    W.pointRes τ c = 0 ↔
      explicitRes1 (AbsoluteGaloisGroup K) W.PointCoeff σ.fieldRange.fixingSubgroup c = 0 := by
  rw [W.pointRes_eq_pointRes τ (separableClosureAlgEquiv K L σ), pointRes_eq_explicitMap1]
  exact explicitMap1_eq_zero_iff_explicitRes1_eq_zero _
    (absoluteGaloisGroupMap_separableClosureAlgEquiv K L σ)
    (W.pointCoeffBaseChange_bijective (separableClosureAlgEquiv K L σ).bijective) _

/-- **A class of `H¹(G_K, E(Kˢ)[m])` restricts to zero over `L` exactly when it restricts to zero
on the subgroup `Gal(Kˢ/σ(L))` of `G_K`.** -/
theorem torsionRes_eq_zero_iff {m : ℕ} {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    W.torsionRes τ m c = 0 ↔
      explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) σ.fieldRange.fixingSubgroup c =
        0 := by
  rw [W.torsionRes_eq_torsionRes τ (separableClosureAlgEquiv K L σ), torsionRes_eq_explicitMap1]
  exact explicitMap1_eq_zero_iff_explicitRes1_eq_zero _
    (absoluteGaloisGroupMap_separableClosureAlgEquiv K L σ)
    (W.torsionCoeffBaseChange_bijective m (separableClosureAlgEquiv K L σ).bijective) _

/-- **Restriction of `H¹(G_K, E(Kˢ))` to `L` has the kernel of restriction to `Gal(Kˢ/σ(L))`.** -/
theorem ker_pointRes :
    (W.pointRes τ).ker =
      (explicitRes1 (AbsoluteGaloisGroup K) W.PointCoeff σ.fieldRange.fixingSubgroup).ker := by
  ext c
  exact W.pointRes_eq_zero_iff τ σ

/-- **Restriction of `H¹(G_K, E(Kˢ)[m])` to `L` has the kernel of restriction to
`Gal(Kˢ/σ(L))`.** -/
theorem ker_torsionRes (m : ℕ) :
    (W.torsionRes τ m).ker =
      (explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
        σ.fieldRange.fixingSubgroup).ker := by
  ext c
  exact W.torsionRes_eq_zero_iff τ σ

/-! ### Restriction to the division field -/

/-- **Over the `m`-division field `K(E[m])`, every geometric `m`-torsion point is rational**: `G_L`
acts trivially on `E(Lˢ)[m]` for `L = K(E[m])`. -/
theorem forall_smul_eq_torsionCoeff_divisionField (m : ℕ)
    (g : AbsoluteGaloisGroup (W.divisionField m)) (P : (W⁄(W.divisionField m)).TorsionCoeff m) :
    g • P = P := by
  let e := separableClosureAlgEquiv K (W.divisionField m) (W.divisionField m).val
  refine W.forall_smul_eq_torsionCoeff_baseChange m (τ := e) e.bijective (fun g Q ↦ ?_) g P
  refine (W.mem_fixingSubgroup_divisionField_iff (m := m)).1 ?_ Q
  rw [absoluteGaloisGroupMap_separableClosureAlgEquiv, ContinuousMonoidHom.comp_toFun,
    ContinuousMonoidHom.coe_coe, ContinuousMonoidHom.subgroupSubtype_apply]
  simpa only [IntermediateField.fieldRange_val] using
    (absoluteGaloisGroupEquivFixingSubgroup K (W.divisionField m) (W.divisionField m).val g).2

/-- **Restriction of `H¹(G_K, E[m])` to the `m`-division field `K(E[m])` has finite kernel**, for
`W` elliptic and `m ≠ 0`, along any embedding of separable closures. -/
theorem finite_ker_torsionRes_divisionField [W.IsElliptic] (m : ℕ) [NeZero m]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (W.divisionField m)) :
    Finite (W.torsionRes τ m).ker := by
  rw [W.ker_torsionRes τ (W.divisionField m).val, IntermediateField.fieldRange_val]
  exact W.finite_ker_explicitRes1_divisionField m

/-- **The finiteness of `Sel_m(E/K)` reduces to the finiteness of `Sel_m(E/K(E[m]))`**, for `W`
elliptic and `m ≠ 0`: if each field `L' j` defining the Selmer group over the `m`-division field
`K(E[m])` is an extension of the field `K' (σ j)` defining that over `K`, compatibly with
`K → K(E[m]) → L' j`, and `Sel_m(E/K(E[m]))` is finite, then so is `Sel_m(E/K)`. -/
theorem finite_selmerGroup_of_finite_selmerGroup_divisionField [W.IsElliptic] (m : ℕ) [NeZero m]
    {ι : Type*} {K' : ι → Type*} [∀ i, Field (K' i)] [∀ i, Algebra K (K' i)]
    (τK : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (K' i))
    {J : Type*} {L' : J → Type*} [∀ j, Field (L' j)] [∀ j, Algebra (W.divisionField m) (L' j)]
    (τL : ∀ j, SeparableClosure (W.divisionField m) →ₐ[W.divisionField m] SeparableClosure (L' j))
    (σ : J → ι) [∀ j, Algebra K (L' j)] [∀ j, IsScalarTower K (W.divisionField m) (L' j)]
    [∀ j, Algebra (K' (σ j)) (L' j)] [∀ j, IsScalarTower K (K' (σ j)) (L' j)]
    (h : Finite ((W⁄(W.divisionField m)).selmerGroup τL m)) :
    Finite (W.selmerGroup τK m) :=
  W.finite_selmerGroup_of_finite_ker_torsionRes IsSepClosed.lift τK τL σ
    (W.finite_ker_torsionRes_divisionField m _) h

end WeierstrassCurve
