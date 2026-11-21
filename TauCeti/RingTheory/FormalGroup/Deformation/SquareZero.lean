/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import TauCeti.RingTheory.FormalGroup.Deformation.Basic
public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.LubinTate
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AdicCompletion.Noetherian
import TauCeti.Algebra.Module.Torsion.Finite
import TauCeti.Algebra.Module.Torsion.ScalarAction
import TauCeti.RingTheory.FormalGroup.Deformation.Lifting
import TauCeti.RingTheory.FormalGroup.Rigidity
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height
import TauCeti.RingTheory.LocalRing.RingHom
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Square-zero fibres of finite-height formal group deformations

Let `F₀` be a commutative formal group law over a field `k` of characteristic `p`, and let
`q : A →+* B` be a surjective ring homomorphism compatible with `π_A : A →+* k` and `π_B : B →+* k`
(`π_B.comp q = π_A`). Building on `TauCeti.RingTheory.FormalGroup.SymmetricCocycle.LubinTate`, this
file classifies framed lifts (`TauCeti.FormalGroupLift`) and coordinate-equivalence classes of
deformations (`TauCeti.FormalGroupDeformation`) across square-zero extensions.

## Main definitions and results

* `TauCeti.FormalGroupLift.deformByCocycle`, `TauCeti.FormalGroupLift.deformationCocycleEquiv`:
  identifies the square-zero fibre of `FormalGroupLift.map q hq` with symmetric 2-cocycles without
  constant term with coefficients in `RingHom.ker q`.
* `TauCeti.FormalGroupDeformation.deformByLubinTate`,
  `TauCeti.FormalGroupDeformation.squareZeroFiberEquiv`: at finite height `h`, identifies
  `Fin (h - 1) → RingHom.ker q` with the fibre of `FormalGroupDeformation.map q hq` over
  `⟦F.map q hq⟧` when `B` is an `𝔪`-adically Hausdorff local ring, `π_B` is surjective,
  `RingHom.ker q` is finitely generated, and `RingHom.ker π_A * RingHom.ker q = ⊥`.
* `TauCeti.FormalGroupDeformation.bijective_map_of_height_eq_one`: rigidity at height `1`.
* `TauCeti.FormalGroupDeformation.dualNumberEquiv`: identifies the tangent space over
  `DualNumber k` with `Fin (h - 1) → k`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1–§2.
* M. Hazewinkel, *Formal Groups and Applications*, Academic Press (1978), §22.
-/

public section

noncomputable section

open MvPowerSeries FormalGroup

namespace TauCeti.FormalGroupLift

variable {A B k : Type*} [CommRing A] [CommRing B] [CommRing k]
  {π_A : A →+* k} {π_B : B →+* k} {F₀ : FormalGroup k}

private theorem coeff_sub_mem_ker_of_map_eq {F G : FormalGroupLift π_A F₀} {q : A →+* B}
    {hq : π_B.comp q = π_A} (h : G.map q hq = F.map q hq) (d : Fin 2 →₀ ℕ) :
    coeff d (G.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) ∈ RingHom.ker q := by
  simpa [FormalGroup.map_toPowerSeries, RingHom.mem_ker, sub_eq_zero] using
    congrArg (fun H : FormalGroupLift π_B F₀ ↦ coeff d H.formalGroup.toPowerSeries) h

/-- Deforming a lift `F : FormalGroupLift π_A F₀` by a symmetric 2-cocycle whose coefficients lie in
a square-zero ideal `I ≤ RingHom.ker π_A` gives a lift of `F₀` to `A`. -/
noncomputable def deformByCocycle (F : FormalGroupLift π_A F₀) {I : Ideal A} (hI : I * I = ⊥)
    (hIπ : I ≤ RingHom.ker π_A) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) : FormalGroupLift π_A F₀ where
  formalGroup := F.formalGroup.deformByCocycle hI hΦ hΦ₀ hΦI
  isComm := inferInstance
  map_eq := (F.formalGroup.map_deformByCocycle_eq hI π_A hIπ hΦ hΦ₀ hΦI).trans F.map_eq

/-- The underlying formal group law of `F.deformByCocycle`. -/
@[simp]
theorem formalGroup_deformByCocycle (F : FormalGroupLift π_A F₀) {I : Ideal A} (hI : I * I = ⊥)
    (hIπ : I ≤ RingHom.ker π_A) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hIπ hΦ hΦ₀ hΦI).formalGroup =
      F.formalGroup.deformByCocycle hI hΦ hΦ₀ hΦI := (rfl)

/-- **Framed square-zero lifts as symmetric 2-cocycles.** Given `hq : π_B.comp q = π_A` with
`RingHom.ker q * RingHom.ker q = ⊥` and a reference lift `F : FormalGroupLift π_A F₀`, the lifts
`G : FormalGroupLift π_A F₀` with `G.map q hq = F.map q hq` correspond bijectively to symmetric
2-cocycles of `F.formalGroup` without constant term and with coefficients in `RingHom.ker q`. -/
noncomputable def deformationCocycleEquiv (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥) :
    {G : FormalGroupLift π_A F₀ // G.map q hq = F.map q hq} ≃
      {Φ : MvPowerSeries (Fin 2) A //
        F.formalGroup.IsSymmetricCocycle Φ ∧ constantCoeff Φ = 0 ∧
          ∀ d, coeff d Φ ∈ RingHom.ker q} where
  toFun G :=
    let hFG := coeff_sub_mem_ker_of_map_eq G.property
    ⟨F.formalGroup.deformationCocycle G.val.formalGroup,
      F.formalGroup.isSymmetricCocycle_deformationCocycle G.val.formalGroup hker hFG,
      F.formalGroup.constantCoeff_deformationCocycle G.val.formalGroup,
      FormalGroup.coeff_deformationCocycle_mem_iff.mpr hFG⟩
  invFun Φ :=
    have hle : RingHom.ker q ≤ RingHom.ker π_A := fun x hx ↦ by
      rw [RingHom.mem_ker] at hx ⊢; rw [← hq, RingHom.comp_apply, hx, map_zero]
    ⟨F.deformByCocycle hker hle Φ.property.1 Φ.property.2.1 Φ.property.2.2,
      FormalGroupLift.ext <| by
        rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
          FormalGroupLift.formalGroup_deformByCocycle]
        exact F.formalGroup.map_deformByCocycle_eq hker q le_rfl
          Φ.property.1 Φ.property.2.1 Φ.property.2.2⟩
  left_inv G := Subtype.ext <| FormalGroupLift.ext <|
    F.formalGroup.deformByCocycle_deformationCocycle G.val.formalGroup hker
      (coeff_sub_mem_ker_of_map_eq G.property)
  right_inv Φ := Subtype.ext <|
    F.formalGroup.deformationCocycle_deformByCocycle hker
      Φ.property.1 Φ.property.2.1 Φ.property.2.2

/-- Evaluating `FormalGroupLift.deformationCocycleEquiv` computes `deformationCocycle`. -/
@[simp]
theorem deformationCocycleEquiv_apply_coe (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (G : {G : FormalGroupLift π_A F₀ // G.map q hq = F.map q hq}) :
    (F.deformationCocycleEquiv hq hker G).val =
      F.formalGroup.deformationCocycle G.val.formalGroup := (rfl)

end TauCeti.FormalGroupLift

namespace TauCeti.FormalGroupDeformation

section SquareZeroFiber

open _root_.IsLocalRing

variable {A B k : Type*} [CommRing A] [CommRing B] [Field k]
  {π_A : A →+* k} {π_B : B →+* k} {F₀ : FormalGroup k}

private def primePowPred (p : ℕ) [hp : Fact p.Prime] (j : ℕ) : ℕ+ :=
  ⟨p ^ (j + 1) - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow j.succ_ne_zero hp.out.one_lt)⟩

@[simp]
private theorem coe_primePowPred_add_one (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
    (primePowPred p j : ℕ) + 1 = p ^ (j + 1) :=
  Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos)

private theorem ker_le_ker_of_comp_eq {q : A →+* B} (hq : π_B.comp q = π_A) :
    RingHom.ker q ≤ RingHom.ker π_A := fun x hx ↦ by
  rw [RingHom.mem_ker] at hx ⊢; rw [← hq, RingHom.comp_apply, hx, map_zero]

/-- If `π_B.comp q = π_A` and `RingHom.ker π_A * RingHom.ker q = ⊥`, then `RingHom.ker q` has
square zero. -/
theorem ker_mul_self_eq_bot_of_ker_mul_eq_bot {q : A →+* B} (hq : π_B.comp q = π_A)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) :
    RingHom.ker q * RingHom.ker q = ⊥ :=
  eq_bot_iff.mpr ((Ideal.mul_mono_left (ker_le_ker_of_comp_eq hq)).trans hker.le)

/-- The framed lift underlying `deformByLubinTate`. -/
private noncomputable def lubinTateLift (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupLift π_A F₀ :=
  F.deformByCocycle hker (ker_le_ker_of_comp_eq hq)
    (FormalGroup.IsSymmetricCocycle.sum Finset.univ fun j _ ↦
      (F.formalGroup.isSymmetricCocycle_lubinTateCocycle (primePowPred p j.val)).smul (m j : A))
    (by rw [map_sum]; exact Finset.sum_eq_zero fun j _ ↦ by simp)
    (fun d ↦ by
      rw [map_sum]
      exact Ideal.sum_mem _ fun j _ ↦ by
        rw [coeff_smul]; exact (RingHom.ker q).mul_mem_right _ (m j).property)

private theorem deformationCocycle_lubinTateLift (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    F.formalGroup.deformationCocycle (lubinTateLift F hq hker p h m).formalGroup =
      ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.val) := by
  rw [lubinTateLift, FormalGroupLift.formalGroup_deformByCocycle,
    FormalGroup.deformationCocycle_deformByCocycle]

private theorem coeff_lubinTateLift_sub_mem (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) (d : Fin 2 →₀ ℕ) :
    coeff d ((lubinTateLift F hq hker p h m).formalGroup.toPowerSeries -
      F.formalGroup.toPowerSeries) ∈ RingHom.ker q :=
  FormalGroup.coeff_deformationCocycle_mem_iff.mp (fun e ↦ by
    rw [deformationCocycle_lubinTateLift, map_sum]
    exact Ideal.sum_mem _ fun j _ ↦ by
      rw [coeff_smul]; exact (RingHom.ker q).mul_mem_right _ (m j).property) d

private theorem map_lubinTateLift (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    (lubinTateLift F hq hker p h m).map q hq = F.map q hq :=
  FormalGroupLift.ext <| by
    rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map, lubinTateLift,
      FormalGroupLift.formalGroup_deformByCocycle]
    exact F.formalGroup.map_deformByCocycle_eq hker q le_rfl _ _ _

/-- Deforming a reference lift `F : FormalGroupLift π_A F₀` along a tuple
`m : Fin (h - 1) → RingHom.ker q` using the canonical Lubin–Tate symmetric 2-cocycles in degrees
`p, p², …, p^(h - 1)`. -/
noncomputable def deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupDeformation π_A F₀ :=
  ⟦lubinTateLift F hq hker p h m⟧

/-- Deforming `F` by `0` gives the deformation class `⟦F⟧`. -/
@[simp]
theorem deformByLubinTate_zero (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] :
    deformByLubinTate F hq hker p h 0 = ⟦F⟧ :=
  congrArg Quotient.mk'' (FormalGroupLift.ext (by ext d; simp [lubinTateLift]))

/-- Every Lubin–Tate deformation along `m : Fin (h - 1) → RingHom.ker q` maps to `⟦F.map q hq⟧`
over `B`. -/
@[simp]
theorem map_deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupDeformation.map q hq (deformByLubinTate F hq hker p h m) = ⟦F.map q hq⟧ := by
  rw [deformByLubinTate, map_mk, map_lubinTateLift]

private theorem eq_one_of_smul_eq_of_map_eq_one [IsLocalRing B]
    [IsHausdorff (maximalIdeal B) B] (hπ_B : Function.Surjective π_B) {p h : ℕ}
    [Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h) (H : FormalGroupLift π_B F₀)
    {ψ : FormalCoordinate B} (hψ₁ : FormalCoordinate.map π_B ψ = 1)
    (hψH : ψ • H.formalGroup = H.formalGroup) : ψ = 1 := by
  have hker_max : RingHom.ker π_B = maximalIdeal B :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π_B hπ_B)
  let e_res : ResidueField B ≃+* k :=
    (Ideal.quotEquivOfEq hker_max.symm).trans (RingHom.quotientKerEquivOfSurjective hπ_B)
  have he_comp : e_res.toRingHom.comp (residue B) = π_B := RingHom.ext fun x ↦
    (congrArg _ (Ideal.quotEquivOfEq_mk hker_max.symm x)).trans
      (RingHom.quotientKerEquivOfSurjective_apply_mk hπ_B x)
  have : CharP (ResidueField B) p := (e_res.toRingHom.charP_iff_charP p).mpr ‹_›
  have hheight : (H.formalGroup.map (residue B)).height p = h := by
    rw [← FormalGroup.height_map _ e_res.toRingHom p, FormalGroup.map_comp, he_comp, H.map_eq, hF₀]
  let f₁ : FormalGroupHom H.formalGroup H.formalGroup :=
    ⟨ψ.toPowerSeries, ψ.constantCoeff_toPowerSeries, by
      have hhom := (FormalGroup.smulIso ψ H.formalGroup).toHom.hom
      rwa [FormalGroup.smulIso_toHom_toPowerSeries, hψH] at hhom⟩
  have heq := f₁.eq_of_map_residue_eq (.id H.formalGroup) hheight <|
    PowerSeries.map_injective e_res.toRingHom e_res.injective <| by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← PowerSeries.map_comp, he_comp,
        FormalGroupHom.id_toPowerSeries, PowerSeries.map_X,
        ← FormalCoordinate.toPowerSeries_map, hψ₁, FormalCoordinate.toPowerSeries_one]
  ext n; simpa [f₁] using congrArg (fun u : FormalGroupHom H.formalGroup H.formalGroup ↦
    PowerSeries.coeff n u.toPowerSeries) heq

section IdealBasis

variable {I : Ideal A} [Module k I]

private theorem sum_smul_lubinTate_eq (hπ_A : Function.Surjective π_A)
    (hsmul : ∀ (a : A) (y : I), ((π_A a • y : I) : A) = a * y.val)
    {n : ℕ} (b : Fin n → I) (F : FormalGroupLift π_A F₀) (p h : ℕ) [Fact p.Prime]
    (c : Fin n → Fin (h - 1) → k) (m : Fin (h - 1) → I) (hm : ∀ j, m j = ∑ i, c i j • b i) :
    ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.val) =
      ∑ i, (b i : A) • ∑ j : Fin (h - 1),
        Function.surjInv hπ_A (c i j) • F.formalGroup.lubinTateCocycle (primePowPred p j.val) := by
  trans ∑ j, ∑ i, (Function.surjInv hπ_A (c i j) * (b i : A)) •
      F.formalGroup.lubinTateCocycle (primePowPred p j.val)
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [congrArg Subtype.val (hm j), Submodule.coe_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← hsmul, Function.surjInv_eq hπ_A]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm (Function.surjInv _ _), mul_smul]

private theorem isSymmetricCocycle_basisComp (hπ_A : Function.Surjective π_A)
    (hsmul : ∀ (a : A) (y : I), ((π_A a • y : I) : A) = a * y.val)
    {n : ℕ} (b : Module.Basis (Fin n) k I) (F : FormalGroupLift π_A F₀)
    {Φ : MvPowerSeries (Fin 2) A} (hΦ : F.formalGroup.IsSymmetricCocycle Φ)
    (hΦI : ∀ d, coeff d Φ ∈ I) (i : Fin n) :
    F₀.IsSymmetricCocycle (basisComp b hΦI i) := by
  have hpair {τ : Type} (u v : MvPowerSeries τ A) :
      (fun s ↦ MvPowerSeries.map π_A (![u, v] s)) =
        ![MvPowerSeries.map π_A u, MvPowerSeries.map π_A v] := by
    funext s; fin_cases s <;> rfl
  refine ⟨?_, ?_⟩
  · have esw := hpair (X 1 : MvPowerSeries (Fin 2) A) (X 0)
    simp only [map_X] at esw
    rw [← esw, ← basisComp_subst hπ_A hsmul b hΦI HasSubst.X_X i]
    exact basisComp_congr b hΦ.subst_swap i
  · have hX (s : Fin 3) := PowerSeries.HasSubst.X (S := A) s
    have hs1 := hasSubst_finTwo (hX 0) (hX 1); have hs4 := hasSubst_finTwo (hX 1) (hX 2)
    have hs2 := hasSubst_finTwo (F.formalGroup.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2)
    have hs3 := hasSubst_finTwo (hX 0) (F.formalGroup.hasSubst_subst_pair (hX 1) (hX 2))
    have e1 := hpair (X 0 : MvPowerSeries (Fin 3) A) (X 1)
    have e4 := hpair (X 1 : MvPowerSeries (Fin 3) A) (X 2)
    have e2 := hpair (F.formalGroup.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1])
      (X 2)
    have e3 := hpair (X 0)
      (F.formalGroup.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2])
    simp only [map_X, map_subst hs1, map_subst hs4, ← FormalGroup.map_toPowerSeries, F.map_eq]
      at e1 e2 e3 e4
    rw [e1] at e2; rw [e4] at e3
    rw [← e2, ← e3, ← e1, ← e4, ← basisComp_subst hπ_A hsmul b hΦI hs1 i,
      ← basisComp_subst hπ_A hsmul b hΦI hs2 i, ← basisComp_subst hπ_A hsmul b hΦI hs3 i,
      ← basisComp_subst hπ_A hsmul b hΦI hs4 i, ← basisComp_add, ← basisComp_add]
    exact basisComp_congr b hΦ.subst_add_subst_eq i

end IdealBasis

private theorem deformationCocycle_lubinTateLift_sub {F G : FormalGroupLift π_A F₀} {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥) (p h : ℕ) [Fact p.Prime]
    (m : Fin (h - 1) → RingHom.ker q)
    (hFG : ∀ d, coeff d (G.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) ∈
      RingHom.ker q) :
    (lubinTateLift F hq hker p h m).formalGroup.deformationCocycle G.formalGroup =
      F.formalGroup.deformationCocycle G.formalGroup -
        ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.val) := by
  have hFm := coeff_lubinTateLift_sub_mem F hq hker p h m
  have htrans := FormalGroup.deformationCocycle_trans hker hFm fun d ↦ by
    rw [← sub_sub_sub_cancel_right _ _ F.formalGroup.toPowerSeries, map_sub]
    exact (RingHom.ker q).sub_mem (hFG d) (hFm d)
  rw [deformationCocycle_lubinTateLift] at htrans
  linear_combination -htrans

variable [F₀.IsComm]

private theorem map_lubinTateCocycle_lift (F : FormalGroupLift π_A F₀) (m : ℕ+) :
    MvPowerSeries.map π_A (F.formalGroup.lubinTateCocycle m) = F₀.lubinTateCocycle m := by
  have h : ∀ {G : FormalGroup k} [G.IsComm],
      G = F₀ → G.lubinTateCocycle m = F₀.lubinTateCocycle m := by
    rintro _ _ rfl; rfl
  exact (FormalGroup.map_lubinTateCocycle π_A F.formalGroup m).trans (h F.map_eq)

private theorem map_sum_smul_lubinTateCocycle (hπ_A : Function.Surjective π_A)
    (F : FormalGroupLift π_A F₀) (p h : ℕ) [Fact p.Prime] (c : Fin (h - 1) → k) :
    MvPowerSeries.map π_A (∑ j : Fin (h - 1),
      Function.surjInv hπ_A (c j) • F.formalGroup.lubinTateCocycle (primePowPred p j.val)) =
      ∑ j : Fin (h - 1), c j • F₀.lubinTateCocycle (primePowPred p j.val) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [smul_eq_C_mul, map_mul, map_C, Function.surjInv_eq hπ_A, map_lubinTateCocycle_lift,
      ← smul_eq_C_mul]

private theorem eq_zero_of_sum_lubinTateCocycle_eq_homDefect (hπ_A : Function.Surjective π_A)
    {q : A →+* B} (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥)
    {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h)
    (F : FormalGroupLift π_A F₀) {m : Fin (h - 1) → RingHom.ker q} {g : PowerSeries A}
    (hgI : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker q)
    (hsum : ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.val) =
      F.formalGroup.homDefect 𝔾ₐ g) : m = 0 := by
  have htor := Ideal.isTorsionBySet_of_mul_eq_bot hker
  let _ := htor.moduleOfSurjective hπ_A
  have hsmul := fun a y ↦ congrArg Subtype.val (htor.moduleOfSurjective_smul hπ_A a y)
  have : Module.Finite A (RingHom.ker q) := Module.Finite.iff_fg.mpr hFG
  have : Module.Finite k (RingHom.ker q) := htor.finite_of_surjective hπ_A
  let b := Module.finBasis k (RingHom.ker q)
  have hgI' (d : Unit →₀ ℕ) : coeff d g ∈ RingHom.ker q := by
    rw [← PowerSeries.coeff_def rfl]; exact hgI (d ())
  let gA (i : Fin _) : PowerSeries A := liftOfSurjective hπ_A (basisComp b hgI' i)
  have heq : ∑ i, (b i : A) • ∑ j : Fin (h - 1),
        Function.surjInv hπ_A (b.repr (m j) i) •
          F.formalGroup.lubinTateCocycle (primePowPred p j.val) =
      ∑ i, (b i : A) • F.formalGroup.homDefect 𝔾ₐ (gA i) := by
    rw [← sum_smul_lubinTate_eq hπ_A hsmul b F p h _ m fun j ↦ (b.sum_repr (m j)).symm, hsum,
      ← FormalGroup.homDefect_𝔾ₐ_sum_smul, ← eq_sum_smul_liftOfSurjective hπ_A hsmul b hgI']
  have hF₀_ord : ((p ^ h : ℕ) : ℕ∞) = (F₀.nsmulSeries p).order :=
    (F₀.height_eq_natCast_iff.mp hF₀).symm
  have hc0 (i : Fin _) : (fun j : Fin (h - 1) ↦ b.repr (m j) i) = 0 := by
    have hmap := map_eq_of_sum_smul_eq hsmul b heq i
    rw [map_sum_smul_lubinTateCocycle, FormalGroup.map_homDefect_𝔾ₐ, F.map_eq] at hmap
    exact (F₀.sum_smul_eq_homDefect_𝔾ₐ_iff hp.out hF₀_ord.le (u := fun _ ↦ 1)
      (fun j ↦ by simpa using F₀.le_order_lubinTateCocycle (primePowPred p j.val))
      (fun j ↦ by
        have := F₀.homogeneousComponent_lubinTateCocycle (primePowPred p j.val)
        rwa [coe_primePowPred_add_one, ← one_smul k (TauCeti.lazardCocycle _ k)] at this)
      (fun _ ↦ isUnit_one)).mp ⟨PowerSeries.map π_A (gA i), hmap⟩
  funext j
  exact b.repr.injective (Finsupp.ext fun i ↦ by
    rw [Pi.zero_apply, map_zero, Finsupp.zero_apply]; exact congrFun (hc0 i) j)

private theorem deformByLubinTate_injective [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    (hπ_B : Function.Surjective π_B) {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀) :
    Function.Injective
      (deformByLubinTate F hq (ker_mul_self_eq_bot_of_ker_mul_eq_bot hq hker) p h) := by
  set hker_sq := ker_mul_self_eq_bot_of_ker_mul_eq_bot hq hker
  have hπ_A : Function.Surjective π_A := hq ▸ hπ_B.comp hq_surj
  intro m₁ m₂ hm
  obtain ⟨φ, hφ_π, hφ_eq⟩ := (mk_eq_mk_iff _ _).mp hm
  have hψ1 : FormalCoordinate.map q φ = 1 :=
    eq_one_of_smul_eq_of_map_eq_one hπ_B hF₀ (F.map q hq)
      (by rw [← FormalCoordinate.map_comp, hq, hφ_π]) (by
        have h1 := congrArg (FormalGroup.map · q) hφ_eq
        rwa [FormalGroup.map_smul, ← FormalGroupLift.formalGroup_map _ q hq,
          ← FormalGroupLift.formalGroup_map _ q hq, map_lubinTateLift, map_lubinTateLift] at h1)
  have hφI (n : ℕ) : PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ RingHom.ker q := by
    rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, ← PowerSeries.coeff_map,
      ← PowerSeries.coeff_map, PowerSeries.map_X, ← FormalCoordinate.toPowerSeries_map, hψ1,
      FormalCoordinate.toPowerSeries_one]
  set G₁ := lubinTateLift F hq hker_sq p h m₁
  set G₂ := lubinTateLift F hq hker_sq p h m₂
  obtain ⟨g, -, hgI, hcoc⟩ :=
    (G₁.formalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
      G₂.formalGroup hker_sq).mp ⟨φ, hφI, hφ_eq⟩
  rw [FormalGroup.homDefect_𝔾ₐ_eq_of_coeff_mem hker_sq
        (coeff_lubinTateLift_sub_mem F hq hker_sq p h m₁) hgI,
      deformationCocycle_lubinTateLift_sub hq hker_sq p h m₁
        (coeff_lubinTateLift_sub_mem F hq hker_sq p h m₂),
      deformationCocycle_lubinTateLift] at hcoc
  have hdiff : ∑ j : Fin (h - 1), ((m₂ j - m₁ j : RingHom.ker q) : A) •
      F.formalGroup.lubinTateCocycle (primePowPred p j.val) = F.formalGroup.homDefect 𝔾ₐ g := by
    simpa [AddSubgroupClass.coe_sub, sub_smul, Finset.sum_sub_distrib] using hcoc
  exact (sub_eq_zero.mp (eq_zero_of_sum_lubinTateCocycle_eq_homDefect hπ_A hFG hker hF₀ F
    hgI hdiff)).symm

private theorem exists_lubinTate_decomp_of_coeff_mem (hπ_A : Function.Surjective π_A)
    {q : A →+* B} (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥)
    {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h)
    (F : FormalGroupLift π_A F₀) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ_coc : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ RingHom.ker q) :
    ∃ (m : Fin (h - 1) → RingHom.ker q) (g : PowerSeries A),
      PowerSeries.constantCoeff g = 0 ∧ (∀ n, PowerSeries.coeff n g ∈ RingHom.ker q) ∧
      Φ = ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.val) +
        F.formalGroup.homDefect 𝔾ₐ g := by
  have htor := Ideal.isTorsionBySet_of_mul_eq_bot hker
  let _ := htor.moduleOfSurjective hπ_A
  have hsmul := fun a y ↦ congrArg Subtype.val (htor.moduleOfSurjective_smul hπ_A a y)
  have : Module.Finite A (RingHom.ker q) := Module.Finite.iff_fg.mpr hFG
  have : Module.Finite k (RingHom.ker q) := htor.finite_of_surjective hπ_A
  let b := Module.finBasis k (RingHom.ker q)
  have hF₀_ord : ((p ^ h : ℕ) : ℕ∞) = (F₀.nsmulSeries p).order :=
    (F₀.height_eq_natCast_iff.mp hF₀).symm
  have hex (i : Fin _) : ∃ (c : Fin (h - 1) → k) (gk : PowerSeries k),
      PowerSeries.constantCoeff gk = 0 ∧
        basisComp b hΦI i = ∑ j : Fin (h - 1), c j • F₀.lubinTateCocycle (primePowPred p j.val) +
          F₀.homDefect 𝔾ₐ gk := by
    have h0 : constantCoeff (basisComp b hΦI i) = 0 := by
      have hΦ0' : (⟨coeff 0 Φ, hΦI 0⟩ : RingHom.ker q) = 0 :=
        Subtype.ext (by simp [coeff_zero_eq_constantCoeff_apply, hΦ₀])
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_basisComp, hΦ0', map_zero]
    obtain ⟨c, ⟨gk, hgk₀, hgk⟩, -⟩ :=
      (isSymmetricCocycle_basisComp hπ_A hsmul b F hΦ_coc hΦI
        i).existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ hp.out
        (CharP.cast_eq_zero k p) hF₀_ord.le
        (F₀.coeff_nsmulSeries_ne_zero_of_height_eq hF₀).isUnit h0
    exact ⟨c, gk, hgk₀, hgk⟩
  choose ck gk hgk₀ hΦk_eq using hex
  let gA (i : Fin _) : PowerSeries A :=
    PowerSeries.mk fun n ↦ if n = 0 then 0 else Function.surjInv hπ_A (PowerSeries.coeff n (gk i))
  have hgA_map (i : Fin _) : PowerSeries.map π_A (gA i) = gk i := by
    ext n; rcases n with _ | n
    · simp [gA, PowerSeries.coeff_zero_eq_constantCoeff_apply, hgk₀ i]
    · simp [gA, Function.surjInv_eq]
  refine ⟨fun j ↦ ∑ i, ck i j • b i, ∑ i, (b i : A) • gA i,
    by rw [map_sum]; exact Finset.sum_eq_zero fun i _ ↦ by simp [gA],
    fun n ↦ by
      rw [map_sum]; exact Ideal.sum_mem _ fun i _ ↦ by
        rw [PowerSeries.coeff_smul, smul_eq_mul]
        exact (RingHom.ker q).mul_mem_right _ (b i).property,
    ?_⟩
  rw [sum_smul_lubinTate_eq hπ_A hsmul b F p h ck _ (fun _ ↦ rfl),
    FormalGroup.homDefect_𝔾ₐ_sum_smul, ← Finset.sum_add_distrib]
  conv_lhs => rw [eq_sum_smul_liftOfSurjective hπ_A hsmul b hΦI]
  simp_rw [← smul_add]
  refine sum_smul_eq_of_map_eq hsmul b fun i ↦ ?_
  rw [map_liftOfSurjective, map_add, map_sum_smul_lubinTateCocycle, FormalGroup.map_homDefect_𝔾ₐ,
    F.map_eq, hgA_map, hΦk_eq]

/-- **Lubin–Tate square-zero fibre theorem.** Let `F₀` be a commutative formal group law of finite
height `h` over a field `k` of characteristic `p`. Let `q : A →+* B` be a surjective ring
homomorphism compatible with reductions `π_A : A →+* k` and `π_B : B →+* k` (`π_B` surjective),
where `B` is an `𝔪`-adically Hausdorff local ring, `RingHom.ker q` is finitely generated, and
`RingHom.ker π_A * RingHom.ker q = ⊥`. Then for every lift `F : FormalGroupLift π_A F₀`,
`deformByLubinTate` gives an equivalence from `Fin (h - 1) → RingHom.ker q` onto the fibre of
`FormalGroupDeformation.map q hq` over `⟦F.map q hq⟧`. -/
noncomputable def squareZeroFiberEquiv [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    (hπ_B : Function.Surjective π_B) {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀) :
    (Fin (h - 1) → RingHom.ker q) ≃
      {x : FormalGroupDeformation π_A F₀ //
        FormalGroupDeformation.map q hq x = ⟦F.map q hq⟧} := by
  set hker_sq := ker_mul_self_eq_bot_of_ker_mul_eq_bot hq hker
  have hπ_A : Function.Surjective π_A := hq ▸ hπ_B.comp hq_surj
  refine Equiv.ofBijective
    (fun m ↦ ⟨deformByLubinTate F hq hker_sq p h m, map_deformByLubinTate F hq hker_sq p h m⟩)
    ⟨fun m₁ m₂ hm ↦ deformByLubinTate_injective hπ_B hq hq_surj hFG hker hF₀ F
      (congrArg Subtype.val hm), ?_⟩
  rintro ⟨x, hx⟩
  induction x using Quotient.inductionOn with | _ G₀ =>
  rw [map_mk] at hx
  obtain ⟨ψ, hψ_π, hψ_eq⟩ := (mk_eq_mk_iff _ _).mp hx
  have : IsLocalHom q := q.isLocalHom_of_surjective_of_isNilpotent_ker hq_surj fun y hy ↦
    ⟨2, by rw [pow_two, ← Ideal.mem_bot, ← hker_sq]; exact Ideal.mul_mem_mul hy hy⟩
  obtain ⟨φ₀, hφ₀_q⟩ := FormalCoordinate.map_surjective_of_isLocalHom q hq_surj ψ
  have hφ₀_π : FormalCoordinate.map π_A φ₀ = 1 := by
    rw [← hq, FormalCoordinate.map_comp, hφ₀_q, hψ_π]
  let G : FormalGroupLift π_A F₀ :=
    (⟨φ₀, MonoidHom.mem_ker.mpr hφ₀_π⟩ : (FormalCoordinate.map π_A).ker) • G₀
  have hGq : G.map q hq = F.map q hq := FormalGroupLift.ext <| by
    rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_smul, FormalGroup.map_smul,
      hφ₀_q, ← FormalGroupLift.formalGroup_map G₀ q hq, hψ_eq]
  have hFG_mem := FormalGroupLift.coeff_sub_mem_ker_of_map_eq hGq
  obtain ⟨m, g, hg₀, hgI, hΦ_decomp⟩ :=
    exists_lubinTate_decomp_of_coeff_mem hπ_A hFG hker hF₀ F
      (F.formalGroup.isSymmetricCocycle_deformationCocycle G.formalGroup hker_sq hFG_mem)
      (F.formalGroup.constantCoeff_deformationCocycle G.formalGroup)
      (FormalGroup.coeff_deformationCocycle_mem_iff.mpr hFG_mem)
  set Fm := lubinTateLift F hq hker_sq p h m
  have hFmG_coc : Fm.formalGroup.deformationCocycle G.formalGroup =
      Fm.formalGroup.homDefect 𝔾ₐ g := by
    rw [FormalGroup.homDefect_𝔾ₐ_eq_of_coeff_mem hker_sq
          (coeff_lubinTateLift_sub_mem F hq hker_sq p h m) hgI,
        deformationCocycle_lubinTateLift_sub hq hker_sq p h m hFG_mem, hΦ_decomp,
        add_sub_cancel_left]
  obtain ⟨φ, hφI, hφ_smul⟩ :=
    (Fm.formalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
      G.formalGroup hker_sq).mpr ⟨g, hg₀, hgI, hFmG_coc⟩
  have hφ_π : FormalCoordinate.map π_A φ = 1 := by
    ext n
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one,
      PowerSeries.coeff_map, ← PowerSeries.map_X π_A, PowerSeries.coeff_map, ← sub_eq_zero,
      ← map_sub, ← map_sub]
    exact RingHom.mem_ker.mp (ker_le_ker_of_comp_eq hq (hφI n))
  exact ⟨m, Subtype.ext (((mk_eq_mk_iff Fm G).mpr ⟨φ, hφ_π, hφ_smul⟩).trans
    ((mk_eq_mk_iff G₀ G).mpr ⟨φ₀, hφ₀_π, rfl⟩).symm)⟩

/-- `squareZeroFiberEquiv` acts by `deformByLubinTate`. -/
@[simp]
theorem squareZeroFiberEquiv_apply_coe [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    (hπ_B : Function.Surjective π_B) {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀)
    (m : Fin (h - 1) → RingHom.ker q) :
    (squareZeroFiberEquiv hπ_B hq hq_surj hFG hker hF₀ F m).val =
      deformByLubinTate F hq (ker_mul_self_eq_bot_of_ker_mul_eq_bot hq hker) p h m := by
  rw [squareZeroFiberEquiv]; rfl

/-- **Height-one rigidity across square-zero extensions.** If `F₀` has height `1` over a field `k`
of characteristic `p`, then base change of deformations along any surjective `q : A →+* B` onto an
`𝔪`-adically Hausdorff local ring `B` with finitely generated kernel annihilated by `ker π_A` is
bijective. -/
theorem bijective_map_of_height_eq_one [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    (hπ_B : Function.Surjective π_B) {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = 1) :
    Function.Bijective
      (FormalGroupDeformation.map q hq :
        FormalGroupDeformation π_A F₀ → FormalGroupDeformation π_B F₀) := by
  refine ⟨fun x₁ x₂ hx ↦ ?_, map_surjective hq hq_surj⟩
  induction x₂ using Quotient.inductionOn with | _ F =>
  rw [map_mk] at hx
  have : IsEmpty (Fin (1 - 1)) := inferInstanceAs (IsEmpty (Fin 0))
  have hsub := (squareZeroFiberEquiv hπ_B hq hq_surj hFG hker hF₀ F).symm.injective.subsingleton
  exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨x₁, hx⟩ ⟨⟦F⟧, map_mk q hq F⟩)

/-- **The Lubin–Tate tangent space.** For a commutative formal group law `F₀` of finite height `h`
over a field `k` of characteristic `p`, the set of deformations of `F₀` over the dual numbers
`DualNumber k = k[ε]` (`ε² = 0`) is canonically equivalent to `Fin (h - 1) → k`. -/
noncomputable def dualNumberEquiv {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) :
    (Fin (h - 1) → k) ≃
      FormalGroupDeformation (TrivSqZeroExt.fstHom k k k).toRingHom F₀ := by
  let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hFG : (RingHom.ker π).FG := ⟨{DualNumber.eps}, by
    rw [Finset.coe_singleton]; ext z
    simp only [RingHom.mem_ker, Ideal.mem_span_singleton, π, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply]
    exact ⟨fun ⟨w, hw⟩ ↦ by simp [hw], fun hz ↦ ⟨algebraMap k (DualNumber k) z.snd,
      by ext <;> simp [hz, TrivSqZeroExt.algebraMap_eq_inl]⟩⟩⟩
  let eKer : k ≃ RingHom.ker π :=
    ⟨fun c ↦ ⟨TrivSqZeroExt.inr c, by simp [RingHom.mem_ker, π]⟩, fun z ↦ z.val.snd,
      fun _ ↦ by simp, fun z ↦ Subtype.ext <| by
        have hz : z.val.fst = 0 := by simpa [π] using RingHom.mem_ker.mp z.property
        ext <;> simp [hz]⟩
  exact (Equiv.piCongrRight fun _ ↦ eKer).trans <|
    (squareZeroFiberEquiv (B := k) (π_B := RingHom.id k) Function.surjective_id
      (RingHom.id_comp π) (fun c ↦ ⟨algebraMap k (DualNumber k) c, by simp [π]⟩)
      hFG ((pow_two (TrivSqZeroExt.kerIdeal k k)).symm.trans (TrivSqZeroExt.kerIdeal_sq k k)) hF₀
      (FormalGroupLift.ofSection F₀ π (algebraMap k (DualNumber k))
        (RingHom.ext fun _ ↦ by simp [π]))).trans
      (Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ _)

/-- Evaluating `dualNumberEquiv` deforms the trivial lift along `ε • cⱼ`. -/
theorem dualNumberEquiv_apply {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (c : Fin (h - 1) → k) :
    dualNumberEquiv hF₀ c =
      deformByLubinTate
        (FormalGroupLift.ofSection F₀ (TrivSqZeroExt.fstHom k k k).toRingHom
          (algebraMap k (DualNumber k)) (RingHom.ext fun x ↦ by simp))
        (RingHom.id_comp _)
        ((pow_two (TrivSqZeroExt.kerIdeal k k)).symm.trans (TrivSqZeroExt.kerIdeal_sq k k))
        p h (fun j ↦ ⟨TrivSqZeroExt.inr (c j), by simp [RingHom.mem_ker]⟩) := by
  rw [dualNumberEquiv]; rfl

end SquareZeroFiber

end TauCeti.FormalGroupDeformation
