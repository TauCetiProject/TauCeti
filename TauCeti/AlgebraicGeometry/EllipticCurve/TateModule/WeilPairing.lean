/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
public import TauCeti.RingTheory.RootsOfUnity.PadicTateTwist
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Compatibility
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois

/-!
# The ℓ-adic Weil pairing

Over a separably closed field in which the prime `ℓ` is invertible, the finite Weil pairings
assemble into a continuous, alternating, nondegenerate `ℤ_ℓ`-bilinear pairing

`T_ℓ E × T_ℓ E → ℤ_ℓ(1)`.

The codomain is `TauCeti.PadicTateTwist`, not a chosen copy of `ℤ_ℓ`: keeping the roots of unity
makes the Galois equivariance canonical. The pairing is characterized by its projections to
`μ_{ℓ^n}`. Its Galois equivariance is the input for identifying the determinant of the Tate-module
representation with the cyclotomic character.

## Main results

* `WeierstrassCurve.tateModuleWeilPairing`: the `ℤ_ℓ`-bilinear pairing.
* `WeierstrassCurve.proj_tateModuleWeilPairing`: its finite components are the Weil pairings.
* `WeierstrassCurve.tateModuleWeilPairing_self`: alternation.
* `WeierstrassCurve.tateModuleWeilPairing_nondegenerate`: nondegeneracy.
* `WeierstrassCurve.continuous_tateModuleWeilPairing`: joint continuity.
* `WeierstrassCurve.tateModuleWeilPairing_galoisRepresentation`: Galois equivariance.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7–8.
-/

public section

noncomputable section

open TauCeti
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {K : Type*} [Field K] [IsSepClosed K]
  (W : WeierstrassCurve K) [W.IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)

local instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

-- Both torsion carriers are Mathlib's integer torsion subgroup; the equivalence puts the
-- roots-of-unity value in the finite level of the Tate twist.
open scoped Classical in
private def tateWeilLevel (n : ℕ) :
    TateModuleLevel ℓ W.toAffine.Point n →+
      TateModuleLevel ℓ W.toAffine.Point n →+ TateModuleLevel ℓ (Additive Kˣ) n where
  toFun S := (PadicTateTwist.levelAddEquivRootsOfUnity n).symm.toAddMonoidHom.comp
    (Isogeny.weilPairing W (ℓ ^ n) (by simpa using pow_ne_zero n hℓ) S)
  map_zero' := by ext T; simp
  map_add' S T := by ext U; simp

open scoped Classical in
private theorem tateWeilLevel_transition (x y : TateModule ℓ W.toAffine.Point) (n : ℕ) :
    tateModuleTransition ℓ (Additive Kˣ) n
        (tateWeilLevel W hℓ (n + 1) (TateModule.proj (n + 1) x) (TateModule.proj (n + 1) y)) =
      tateWeilLevel W hℓ n (TateModule.proj n x) (TateModule.proj n y) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  simp only [tateModuleTransition_apply, tateWeilLevel, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    PadicTateTwist.coe_levelAddEquivRootsOfUnity_symm, toMul_nsmul, toMul_ofMul]
  exact Isogeny.coe_weilPairing_pow_eq_coe_weilPairing_nsmul W
    (N := ℓ ^ (n + 1)) (m := ℓ ^ n)
    (by simpa using pow_ne_zero (n + 1) hℓ) (by simpa using pow_ne_zero n hℓ) (pow_succ ℓ n)
    (S := TateModule.proj (n + 1) x) (T := TateModule.proj (n + 1) y)
    (S' := TateModule.proj n x) (T' := TateModule.proj n y)
    (by simpa only [tateModuleTransition_apply] using
      (congrArg Subtype.val (TateModule.proj_succ x n)).symm)
    (by simpa only [tateModuleTransition_apply] using
      (congrArg Subtype.val (TateModule.proj_succ y n)).symm)

open scoped Classical in
private def tateWeilAdd : TateModule ℓ W.toAffine.Point →+
    TateModule ℓ W.toAffine.Point →+ PadicTateTwist ℓ K where
  toFun x := TateModule.lift
    (fun n ↦ (tateWeilLevel W hℓ n (TateModule.proj n x)).comp (TateModule.proj n))
    (fun n ↦ AddMonoidHom.ext fun y ↦ tateWeilLevel_transition W hℓ x y n)
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    apply TateModule.ext
    intro n
    simp only [map_zero, ← AddMonoidHom.comp_apply, TateModule.proj_lift]
    simp
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    apply TateModule.ext
    intro n
    simp only [AddMonoidHom.add_apply, map_add, ← AddMonoidHom.comp_apply, TateModule.proj_lift]
    simp

open scoped Classical in
private theorem proj_tateWeilAdd (x y : TateModule ℓ W.toAffine.Point) (n : ℕ) :
    TateModule.proj n (tateWeilAdd W hℓ x y) =
      tateWeilLevel W hℓ n (TateModule.proj n x) (TateModule.proj n y) :=
  DFunLike.congr_fun (TateModule.proj_lift _ _ n) y

open scoped Classical in
/-- **The ℓ-adic Weil pairing**, with values in the Tate twist `ℤ_ℓ(1)`, obtained from the
compatible finite Weil pairings over a separably closed field in which `ℓ` is invertible. -/
def tateModuleWeilPairing : TateModule ℓ W.toAffine.Point →ₗ[ℤ_[ℓ]]
    TateModule ℓ W.toAffine.Point →ₗ[ℤ_[ℓ]] PadicTateTwist ℓ K where
  toFun x :=
    { toFun := fun y ↦ tateWeilAdd W hℓ x y
      map_add' y z := map_add (tateWeilAdd W hℓ x) y z
      map_smul' a y := by
        apply TateModule.ext
        intro n
        simp only [proj_tateWeilAdd, TateModule.proj_smul, RingHom.id_apply]
        exact ZMod.map_smul (tateWeilLevel W hℓ n (TateModule.proj n x))
          (PadicInt.toZModPow n a) (TateModule.proj n y) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact DFunLike.congr_fun (map_add (tateWeilAdd W hℓ) x y) z
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply TateModule.ext
    intro n
    simp only [LinearMap.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
      proj_tateWeilAdd, TateModule.proj_smul]
    exact ZMod.map_smul ((tateWeilLevel W hℓ n).flip (TateModule.proj n y))
      (PadicInt.toZModPow n a) (TateModule.proj n x)

open scoped Classical in
private theorem tateModuleProj_tateModuleWeilPairing (x y : TateModule ℓ W.toAffine.Point)
    (n : ℕ) : TateModule.proj n (W.tateModuleWeilPairing hℓ x y) =
      tateWeilLevel W hℓ n (TateModule.proj n x) (TateModule.proj n y) :=
  proj_tateWeilAdd W hℓ x y n

open scoped Classical in
/-- The finite components of the ℓ-adic pairing are the ordinary Weil pairings. -/
@[simp]
theorem proj_tateModuleWeilPairing (x y : TateModule ℓ W.toAffine.Point) (n : ℕ) :
    PadicTateTwist.proj n (W.tateModuleWeilPairing hℓ x y) =
      Isogeny.weilPairing W (ℓ ^ n) (by simpa using pow_ne_zero n hℓ) (TateModule.proj n x)
        (TateModule.proj n y) := by
  rw [PadicTateTwist.proj_def, tateModuleProj_tateModuleWeilPairing]
  simp [tateWeilLevel]

open scoped Classical in
/-- The ℓ-adic Weil pairing is alternating. -/
@[simp]
theorem tateModuleWeilPairing_self (x : TateModule ℓ W.toAffine.Point) :
    W.tateModuleWeilPairing hℓ x x = 0 := by
  apply PadicTateTwist.ext
  intro n
  rw [proj_tateModuleWeilPairing, map_zero]
  exact Isogeny.weilPairing_self W (ℓ ^ n) _ _

open scoped Classical in
/-- The ℓ-adic Weil pairing is skew-symmetric, in additive notation on the Tate twist. -/
theorem neg_tateModuleWeilPairing (x y : TateModule ℓ W.toAffine.Point) :
    -(W.tateModuleWeilPairing hℓ x y) = W.tateModuleWeilPairing hℓ y x := by
  apply PadicTateTwist.ext
  intro n
  rw [map_neg, proj_tateModuleWeilPairing, proj_tateModuleWeilPairing]
  exact Isogeny.neg_weilPairing W (ℓ ^ n) _ _ _

open scoped Classical in
/-- The ℓ-adic Weil pairing is nondegenerate in its first variable. -/
theorem tateModuleWeilPairing_nondegenerate {x : TateModule ℓ W.toAffine.Point}
    (hx : ∀ y, W.tateModuleWeilPairing hℓ x y = 0) : x = 0 := by
  apply TateModule.ext
  intro n
  rw [map_zero]
  apply Isogeny.weilPairing_nondegenerate W (ℓ ^ n) (by simpa using pow_ne_zero n hℓ)
  intro T
  obtain ⟨y, rfl⟩ := TateModule.proj_surjective
    (TateModule.tateModuleTransition_surjective_of_natCard (Fact.out : ℓ.Prime).ne_zero
      (W.natCard_tateModuleLevel hℓ)) n T
  simpa using congrArg (PadicTateTwist.proj n) (hx y)

open scoped Classical in
/-- The ℓ-adic Weil pairing is nondegenerate in its second variable. -/
theorem eq_zero_of_forall_tateModuleWeilPairing_eq_zero {y : TateModule ℓ W.toAffine.Point}
    (hy : ∀ x, W.tateModuleWeilPairing hℓ x y = 0) : y = 0 := by
  apply W.tateModuleWeilPairing_nondegenerate hℓ
  intro x
  rw [← W.neg_tateModuleWeilPairing hℓ, hy x, neg_zero]

open scoped Classical in
/-- The ℓ-adic Weil pairing is jointly continuous for the inverse-limit topologies. -/
theorem continuous_tateModuleWeilPairing :
    Continuous fun q : TateModule ℓ W.toAffine.Point × TateModule ℓ W.toAffine.Point ↦
      W.tateModuleWeilPairing hℓ q.1 q.2 := by
  apply TateModule.continuous_iff.mpr
  intro n
  have hx := (TateModule.isLocallyConstant_proj (p := ℓ) (A := W.toAffine.Point) n).comp_continuous
    (continuous_fst (Y := TateModule ℓ W.toAffine.Point))
  have hy := (TateModule.isLocallyConstant_proj (p := ℓ) (A := W.toAffine.Point) n).comp_continuous
    (continuous_snd (X := TateModule ℓ W.toAffine.Point))
  simpa only [tateModuleProj_tateModuleWeilPairing, Function.comp_apply] using
    hx.comp₂ hy (fun x y ↦ tateWeilLevel W hℓ n x y)

section Galois

variable {F : Type*} [Field F] [Algebra F K] (E : WeierstrassCurve F) [E.IsElliptic]

open scoped Classical in
/-- The ℓ-adic Weil pairing intertwines the elliptic Galois representation with the action on
`ℤ_ℓ(1)`. Thus its equivariance does not require choosing a generator of the Tate twist. -/
theorem tateModuleWeilPairing_galoisRepresentation (σ : K ≃ₐ[F] K)
    (x y : TateModule ℓ (E⁄K).toAffine.Point) :
    (E⁄K).tateModuleWeilPairing hℓ (E.tateModuleGaloisRepresentation ℓ σ x)
        (E.tateModuleGaloisRepresentation ℓ σ y) =
      PadicTateTwist.galoisRepresentation (F := F) σ ((E⁄K).tateModuleWeilPairing hℓ x y) := by
  apply PadicTateTwist.ext
  intro n
  rw [proj_tateModuleWeilPairing]
  have hσ (z : TateModule ℓ (E⁄K).toAffine.Point) :
      TateModule.proj n (E.tateModuleGaloisRepresentation ℓ σ z) =
        Multiplicative.toAdd (E.torsionGaloisAction ((ℓ ^ n : ℕ) : ℤ) σ) (TateModule.proj n z) := by
    apply Subtype.ext
    rw [E.coe_proj_tateModuleGaloisRepresentation, E.torsionGaloisAction_apply_coe,
      E.pointGaloisAction_apply]
  rw [hσ x, hσ y, E.weilPairing_torsionGaloisAction]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [toMul_ofMul, restrictRootsOfUnity_coe_apply, PadicTateTwist.coe_proj,
    PadicTateTwist.coe_tateModuleProj_galoisRepresentation]
  have h := congrArg (fun z : Additive (rootsOfUnity (ℓ ^ n) K) ↦ σ ((z.toMul : Kˣ) : K))
    (proj_tateModuleWeilPairing (E⁄K) hℓ x y n).symm
  simpa only [PadicTateTwist.coe_proj] using h

end Galois

end WeierstrassCurve

end
