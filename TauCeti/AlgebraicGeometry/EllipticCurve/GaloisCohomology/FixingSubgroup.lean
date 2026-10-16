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
the same kernel (`WeierstrassCurve.ker_pointRes`, `WeierstrassCurve.ker_torsionRes`).

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

* `WeierstrassCurve.pointCoeffBaseChange_bijective`,
  `WeierstrassCurve.torsionCoeffBaseChange_bijective`: the coordinate maps along a bijective
  embedding of separable closures are bijective.
* `WeierstrassCurve.pointRes_eq_zero_iff`, `WeierstrassCurve.torsionRes_eq_zero_iff`: a class
  restricts to zero over `L` exactly when it restricts to zero on `Gal(Kˢ/σ(L))`.
* `WeierstrassCurve.ker_pointRes`, `WeierstrassCurve.ker_torsionRes`: the same statement for the
  kernels.
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

/-! ### Bijectivity of the coordinate maps -/

variable {τ} in
open scoped Classical in
/-- **Along a bijective embedding of separable closures, `E(Kˢ) → E(Lˢ)` is bijective.** -/
theorem pointCoeffBaseChange_bijective (hτ : Function.Bijective τ) :
    Function.Bijective (W.pointCoeffBaseChange τ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun P hP ↦ ?_, fun Q ↦ ?_⟩
  · -- The image of an affine point is affine, so only the point at infinity maps to zero.
    obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
    rcases P with _ | ⟨x, y, h⟩
    · rw [← Affine.Point.zero_def, map_zero]
    · rw [pointCoeffBaseChange_pointCoeffEquiv_some, AddEquivClass.map_eq_zero_iff] at hP
      cases hP
  · -- An affine point of `W⁄L` over `Lˢ` is the image of its coordinates pulled back along `τ`.
    let e : SeparableClosure K ≃ₐ[K] SeparableClosure L := AlgEquiv.ofBijective τ hτ
    obtain ⟨Q, rfl⟩ := (W⁄L).pointCoeffEquiv.surjective Q
    rcases Q with _ | ⟨x, y, h⟩
    · exact ⟨0, by rw [map_zero, ← Affine.Point.zero_def, map_zero]⟩
    have h' : (W⁄(SeparableClosure L)).toAffine.Nonsingular (τ (e.symm x)) (τ (e.symm y)) := by
      convert (show (W⁄L)⁄(SeparableClosure L) = W⁄(SeparableClosure L) from
        W.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))) ▸ h <;>
      exact e.apply_symm_apply _
    refine ⟨W.pointCoeffEquiv (.some _ _
      ((W.toAffine.baseChange_nonsingular (S := K) (f := τ) τ.injective _ _).1 h')), ?_⟩
    rw [pointCoeffBaseChange_pointCoeffEquiv_some]
    congr 2 <;> exact e.apply_symm_apply _

variable {τ} in
/-- **Along a bijective embedding of separable closures, `E(Kˢ)[m] → E(Lˢ)[m]` is bijective.** -/
theorem torsionCoeffBaseChange_bijective (hτ : Function.Bijective τ) (m : ℕ) :
    Function.Bijective (W.torsionCoeffBaseChange τ m) := by
  have h := W.pointCoeffBaseChange_bijective hτ
  refine ⟨fun P Q hPQ ↦ Subtype.ext <| h.1 <| by
    rw [← coe_torsionCoeffBaseChange, hPQ, coe_torsionCoeffBaseChange], fun Q ↦ ?_⟩
  obtain ⟨P, hP⟩ := h.2 Q
  -- The preimage of an `m`-torsion point is `m`-torsion, by injectivity.
  have hPm : P ∈ AddSubgroup.torsionBy W.PointCoeff m := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    refine h.1 ?_
    rw [map_nsmul, hP, map_zero, AddSubgroup.torsionBy.nsmul_iff.1 Q.2]
  exact ⟨⟨P, hPm⟩, Subtype.ext <| by rw [coe_torsionCoeffBaseChange, hP]⟩

/-! ### Restriction to the fixing subgroup -/

variable (σ : L →ₐ[K] SeparableClosure K)

/-- **A class of `H¹(G_K, E(Kˢ))` restricts to zero over `L` exactly when it restricts to zero on
the subgroup `Gal(Kˢ/σ(L))` of `G_K`.** -/
theorem pointRes_eq_zero_iff {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff} :
    W.pointRes τ c = 0 ↔
      explicitRes1 (AbsoluteGaloisGroup K) W.PointCoeff σ.fieldRange.fixingSubgroup c = 0 := by
  let ψ : SeparableClosure K →ₐ[K] SeparableClosure L := separableClosureAlgEquiv K L σ
  let f := AddEquiv.ofBijective (W.pointCoeffBaseChange ψ)
    (W.pointCoeffBaseChange_bijective (separableClosureAlgEquiv K L σ).bijective)
  have hf : ∀ (g : AbsoluteGaloisGroup L) (P : W.PointCoeff),
      f (absoluteGaloisGroupEquivFixingSubgroup K L σ g • P) = g • f P := fun g P ↦ by
    have h := W.pointCoeffBaseChange_smul ψ g P
    rw [absoluteGaloisGroupMap_separableClosureAlgEquiv] at h
    exact h
  -- Restriction along `ψ` is restriction to the fixing subgroup followed by the isomorphism
  -- induced by `(absoluteGaloisGroupEquivFixingSubgroup K L σ, f)`.
  have h : W.pointRes ψ c = explicitMap1Equiv _ _ _ _ (absoluteGaloisGroupEquivFixingSubgroup K L σ)
      f continuous_of_discreteTopology continuous_of_discreteTopology hf
      (explicitRes1 _ _ σ.fieldRange.fixingSubgroup c) := by
    rw [explicitMap1Equiv_apply, explicitRes1_eq_explicitMap1, pointRes_eq_explicitMap1]
    refine Eq.trans ?_ (DFunLike.congr_fun (explicitMap1_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _) c)
    exact DFunLike.congr_fun (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _
      (absoluteGaloisGroupMap_separableClosureAlgEquiv K L σ) rfl) c
  rw [W.pointRes_eq_pointRes τ ψ, h, AddEquivClass.map_eq_zero_iff]

/-- **A class of `H¹(G_K, E(Kˢ)[m])` restricts to zero over `L` exactly when it restricts to zero
on the subgroup `Gal(Kˢ/σ(L))` of `G_K`.** -/
theorem torsionRes_eq_zero_iff {m : ℕ} {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    W.torsionRes τ m c = 0 ↔
      explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) σ.fieldRange.fixingSubgroup c =
        0 := by
  let ψ : SeparableClosure K →ₐ[K] SeparableClosure L := separableClosureAlgEquiv K L σ
  let f := AddEquiv.ofBijective (W.torsionCoeffBaseChange ψ m)
    (W.torsionCoeffBaseChange_bijective (separableClosureAlgEquiv K L σ).bijective m)
  have hf : ∀ (g : AbsoluteGaloisGroup L) (P : W.TorsionCoeff m),
      f (absoluteGaloisGroupEquivFixingSubgroup K L σ g • P) = g • f P := fun g P ↦ by
    have h := W.torsionCoeffBaseChange_smul ψ m g P
    rw [absoluteGaloisGroupMap_separableClosureAlgEquiv] at h
    exact h
  -- Restriction along `ψ` is restriction to the fixing subgroup followed by the isomorphism
  -- induced by `(absoluteGaloisGroupEquivFixingSubgroup K L σ, f)`.
  have h : W.torsionRes ψ m c =
      explicitMap1Equiv _ _ _ _ (absoluteGaloisGroupEquivFixingSubgroup K L σ)
        f continuous_of_discreteTopology continuous_of_discreteTopology hf
        (explicitRes1 _ _ σ.fieldRange.fixingSubgroup c) := by
    rw [explicitMap1Equiv_apply, explicitRes1_eq_explicitMap1, torsionRes_eq_explicitMap1]
    refine Eq.trans ?_ (DFunLike.congr_fun (explicitMap1_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _) c)
    exact DFunLike.congr_fun (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _
      (absoluteGaloisGroupMap_separableClosureAlgEquiv K L σ) rfl) c
  rw [W.torsionRes_eq_torsionRes τ ψ, h, AddEquivClass.map_eq_zero_iff]

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
