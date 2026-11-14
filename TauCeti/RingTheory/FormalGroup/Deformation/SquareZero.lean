/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import TauCeti.RingTheory.FormalGroup.Deformation.Basic
public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.LubinTate
import Mathlib.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial
import TauCeti.RingTheory.FormalGroup.Rigidity
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height
import TauCeti.RingTheory.LocalRing.RingHom
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Square-zero fibres of finite-height formal group deformations

Let `F₀` be a commutative formal group law over a field `k` of characteristic `p`, and let
`q : A →+* B` be a surjective homomorphism of commutative rings compatible with reductions
`π_A : A →+* k` and `π_B : B →+* k` (`π_B.comp q = π_A`). Building on the linearised deformation
cocycle and canonical Lubin–Tate cocycles in
`TauCeti.RingTheory.FormalGroup.SymmetricCocycle.LubinTate`, this file classifies both framed lifts
(`TauCeti.FormalGroupLift`) and coordinate-equivalence classes of deformations
(`TauCeti.FormalGroupDeformation`) across square-zero extensions.

## Main definitions

* `TauCeti.FormalGroupLift.deformByCocycle`: deforms a framed lift `F : FormalGroupLift π_A F₀` by a
  symmetric 2-cocycle of `F.formalGroup` without constant term whose coefficients lie in a
  square-zero ideal `I ≤ RingHom.ker π_A`.
* `TauCeti.FormalGroupLift.deformationCocycleEquiv`: identifies the fibre of
  `FormalGroupLift.map q hq` over `F.map q hq` when `RingHom.ker q * RingHom.ker q = ⊥` with
  symmetric 2-cocycles of `F.formalGroup` without constant term and with coefficients in
  `RingHom.ker q`.
* `TauCeti.FormalGroupDeformation.deformByLubinTate`: deforms `F` along a parameter tuple
  `m : Fin (h - 1) → RingHom.ker q` using the Lubin–Tate symmetric 2-cocycles in degrees
  `p, p², …, p^(h - 1)`.
* `TauCeti.FormalGroupDeformation.squareZeroFiberEquiv`: when `F₀` has finite height `h`, `B` is an
  `𝔪`-adically Hausdorff local ring with `π_B` surjective, `RingHom.ker q` is finitely generated,
  and `RingHom.ker π_A * RingHom.ker q = ⊥`, identifies `Fin (h - 1) → RingHom.ker q` with the
  fibre of `FormalGroupDeformation.map q hq` over `⟦F.map q hq⟧`.
* `TauCeti.FormalGroupDeformation.dualNumberEquiv`: identifies the tangent space
  `FormalGroupDeformation π F₀` over `DualNumber k` with `Fin (h - 1) → k`.

## Main results

* `TauCeti.FormalGroupLift.map_surjective` and `TauCeti.FormalGroupDeformation.map_surjective`:
  framed lifts and deformation classes lift along every surjective coefficient homomorphism.
* `TauCeti.FormalGroupDeformation.bijective_map_of_height_eq_one`: at height `1`,
  `FormalGroupDeformation.map q hq` is bijective across every small extension of an `𝔪`-adically
  Hausdorff local ring.

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

private theorem coeff_mul_mem_of_right {I : Ideal A} (P : MvPowerSeries (Fin 2) A)
    {f : MvPowerSeries (Fin 2) A} (hf : ∀ d, coeff d f ∈ I) (d : Fin 2 →₀ ℕ) :
    coeff d (P * f) ∈ I := by
  classical
  rw [coeff_mul]
  exact Ideal.sum_mem I fun pq _ ↦ I.mul_mem_left _ (hf pq.2)

/-- Every commutative formal group lift over `B` lifts along any surjective ring homomorphism
`q : A →+* B` compatible with the reductions to `k`. -/
theorem map_surjective {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) :
    Function.Surjective (fun F : FormalGroupLift π_A F₀ ↦ F.map q hq) := by
  intro G
  obtain ⟨H, hH_comm, hHq⟩ := FormalGroup.exists_map_eq_of_surjective G.formalGroup hq_surj
  refine ⟨⟨H, hH_comm, ?_⟩, FormalGroupLift.ext (by simpa using hHq)⟩
  rw [← hq, ← FormalGroup.map_comp, hHq, G.map_eq]

/-- Deforming a lift `F : FormalGroupLift π_A F₀` by a symmetric 2-cocycle whose coefficients lie in
a square-zero ideal `I ≤ RingHom.ker π_A` gives a lift of `F₀` to `A`. -/
noncomputable def deformByCocycle (F : FormalGroupLift π_A F₀) {I : Ideal A} (hI : I * I = ⊥)
    (hIπ : I ≤ RingHom.ker π_A) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) : FormalGroupLift π_A F₀ where
  formalGroup := F.formalGroup.deformByCocycle hI hΦ hΦ₀ hΦI
  isComm := inferInstance
  map_eq := by
    ext d
    have hmem : π_A (coeff d
        (PowerSeries.subst F.formalGroup.toPowerSeries
          (subst ![(0 : PowerSeries A), PowerSeries.X] (pderiv 0 F.formalGroup.toPowerSeries)) *
          Φ)) = 0 :=
      RingHom.mem_ker.mp (hIπ (coeff_mul_mem_of_right _ hΦI d))
    rw [FormalGroup.map_toPowerSeries, FormalGroup.toPowerSeries_deformByCocycle, map_add,
      map_add, coeff_map, coeff_map, hmem, _root_.add_zero, ← coeff_map,
      ← FormalGroup.map_toPowerSeries, F.map_eq]

/-- The underlying formal group law of `F.deformByCocycle`. -/
@[simp]
theorem formalGroup_deformByCocycle (F : FormalGroupLift π_A F₀) {I : Ideal A} (hI : I * I = ⊥)
    (hIπ : I ≤ RingHom.ker π_A) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hIπ hΦ hΦ₀ hΦI).formalGroup =
      F.formalGroup.deformByCocycle hI hΦ hΦ₀ hΦI :=
  (rfl)

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
    have hFG : ∀ d, coeff d (G.1.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) ∈
        RingHom.ker q := fun d ↦ by
      have hd := congrArg (fun H : FormalGroupLift π_B F₀ ↦ coeff d H.formalGroup.toPowerSeries) G.2
      simpa [FormalGroup.map_toPowerSeries, RingHom.mem_ker, sub_eq_zero] using hd
    ⟨F.formalGroup.deformationCocycle G.1.formalGroup,
      F.formalGroup.isSymmetricCocycle_deformationCocycle G.1.formalGroup hker hFG,
      F.formalGroup.constantCoeff_deformationCocycle G.1.formalGroup,
      FormalGroup.coeff_deformationCocycle_mem_iff.mpr hFG⟩
  invFun Φ :=
    have hle : RingHom.ker q ≤ RingHom.ker π_A := fun x hx ↦ by
      rw [RingHom.mem_ker] at hx ⊢
      rw [← hq, RingHom.comp_apply, hx, map_zero]
    ⟨F.deformByCocycle hker hle Φ.2.1 Φ.2.2.1 Φ.2.2.2, by
      ext d
      have hd : q (coeff d
          (PowerSeries.subst F.formalGroup.toPowerSeries
            (subst ![(0 : PowerSeries A), PowerSeries.X] (pderiv 0 F.formalGroup.toPowerSeries)) *
            Φ.1)) = 0 :=
        RingHom.mem_ker.mp (coeff_mul_mem_of_right _ Φ.2.2.2 d)
      rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
        FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries,
        FormalGroupLift.formalGroup_deformByCocycle, FormalGroup.toPowerSeries_deformByCocycle,
        map_add, map_add, coeff_map, coeff_map, hd, _root_.add_zero]⟩
  left_inv G := by
    apply Subtype.ext
    apply FormalGroupLift.ext
    refine F.formalGroup.deformByCocycle_deformationCocycle G.1.formalGroup hker fun d ↦ ?_
    have hd := congrArg (fun H : FormalGroupLift π_B F₀ ↦ coeff d H.formalGroup.toPowerSeries) G.2
    simpa [FormalGroup.map_toPowerSeries, RingHom.mem_ker, sub_eq_zero] using hd
  right_inv Φ :=
    Subtype.ext (F.formalGroup.deformationCocycle_deformByCocycle hker Φ.2.1 Φ.2.2.1 Φ.2.2.2)

/-- Evaluating `FormalGroupLift.deformationCocycleEquiv` computes `deformationCocycle`. -/
@[simp]
theorem deformationCocycleEquiv_apply_coe (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (G : {G : FormalGroupLift π_A F₀ // G.map q hq = F.map q hq}) :
    (F.deformationCocycleEquiv hq hker G).val =
      F.formalGroup.deformationCocycle G.val.formalGroup :=
  (rfl)

end TauCeti.FormalGroupLift

namespace TauCeti.FormalGroupDeformation

section General

variable {A B k : Type*} [CommRing A] [CommRing B] [CommRing k]
  {π_A : A →+* k} {π_B : B →+* k} {F₀ : FormalGroup k}

/-- Base change of formal group deformations along any surjective ring homomorphism is surjective,
by Lazard's theorem that commutative formal group laws lift along surjections. -/
theorem map_surjective {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) :
    Function.Surjective
      (FormalGroupDeformation.map q hq :
        FormalGroupDeformation π_A F₀ → FormalGroupDeformation π_B F₀) := by
  intro y
  induction y using Quotient.inductionOn with | _ G =>
  obtain ⟨F, rfl⟩ := FormalGroupLift.map_surjective hq hq_surj G
  exact ⟨⟦F⟧, map_mk q hq F⟩

end General

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
  rw [RingHom.mem_ker] at hx ⊢
  rw [← hq, RingHom.comp_apply, hx, map_zero]

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
      (F.formalGroup.isSymmetricCocycle_lubinTateCocycle (primePowPred p j.1)).smul (m j : A))
    (by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j _ ↦ by
        rw [constantCoeff_smul, FormalGroup.constantCoeff_lubinTateCocycle, smul_zero])
    (fun d ↦ by
      rw [map_sum]
      exact Ideal.sum_mem _ fun j _ ↦ by
        rw [coeff_smul]
        exact (RingHom.ker q).mul_mem_right _ (m j).2)

private theorem coeff_lubinTateLift_sub_mem (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) (d : Fin 2 →₀ ℕ) :
    coeff d ((lubinTateLift F hq hker p h m).formalGroup.toPowerSeries -
      F.formalGroup.toPowerSeries) ∈ RingHom.ker q := by
  classical
  rw [lubinTateLift, FormalGroupLift.formalGroup_deformByCocycle,
    FormalGroup.toPowerSeries_deformByCocycle, add_sub_cancel_left, coeff_mul]
  refine Ideal.sum_mem _ fun pq _ ↦ (RingHom.ker q).mul_mem_left _ ?_
  rw [map_sum]
  exact Ideal.sum_mem _ fun j _ ↦ by
    rw [coeff_smul]
    exact (RingHom.ker q).mul_mem_right _ (m j).2

private theorem map_lubinTateLift (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    (lubinTateLift F hq hker p h m).map q hq = F.map q hq := by
  ext d
  have hd := RingHom.mem_ker.mp (coeff_lubinTateLift_sub_mem F hq hker p h m d)
  rw [map_sub, map_sub, sub_eq_zero] at hd
  simpa [FormalGroup.map_toPowerSeries] using hd

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
    deformByLubinTate F hq hker p h 0 = ⟦F⟧ := by
  refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
  ext d
  simp [lubinTateLift]

/-- Every Lubin–Tate deformation along `m : Fin (h - 1) → RingHom.ker q` maps to `⟦F.map q hq⟧`
over `B`. -/
@[simp]
theorem map_deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupDeformation.map q hq (deformByLubinTate F hq hker p h m) = ⟦F.map q hq⟧ := by
  rw [deformByLubinTate, map_mk, map_lubinTateLift]

/-- Rigidity of ⋆-automorphisms on `B` along a surjective reduction `π_B : B →+* k` onto a field of
characteristic `p`. -/
private theorem eq_one_of_smul_eq_of_map_eq_one [IsLocalRing B]
    [IsHausdorff (maximalIdeal B) B] (hπ_B : Function.Surjective π_B) {p h : ℕ}
    [Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h) (H : FormalGroupLift π_B F₀)
    {ψ : FormalCoordinate B} (hψ₁ : FormalCoordinate.map π_B ψ = 1)
    (hψH : ψ • H.formalGroup = H.formalGroup) : ψ = 1 := by
  have hker_max : RingHom.ker π_B = maximalIdeal B :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π_B hπ_B)
  let e_res : ResidueField B ≃+* k :=
    (Ideal.quotEquivOfEq hker_max.symm).trans (RingHom.quotientKerEquivOfSurjective hπ_B)
  have he_comp : e_res.toRingHom.comp (residue B) = π_B := by
    ext x
    rw [RingHom.comp_apply]
    exact (congrArg (RingHom.quotientKerEquivOfSurjective hπ_B)
      (Ideal.quotEquivOfEq_mk hker_max.symm x)).trans
      (RingHom.quotientKerEquivOfSurjective_apply_mk hπ_B x)
  have : CharP (ResidueField B) p := (e_res.toRingHom.charP_iff_charP p).mpr ‹_›
  have hheight : (H.formalGroup.map (residue B)).height p = h := by
    rw [← FormalGroup.height_map _ e_res.toRingHom p, FormalGroup.map_comp, he_comp, H.map_eq, hF₀]
  let f₁ : FormalGroupHom H.formalGroup H.formalGroup :=
    { toPowerSeries := ψ.toPowerSeries
      zero_constantCoeff := ψ.constantCoeff_toPowerSeries
      hom := by
        have hhom := (FormalGroup.smulIso ψ H.formalGroup).toHom.hom
        rwa [FormalGroup.smulIso_toHom_toPowerSeries, hψH] at hhom }
  have hres_eq : f₁.toPowerSeries.map (residue B) =
      (FormalGroupHom.id H.formalGroup).toPowerSeries.map (residue B) := by
    apply PowerSeries.map_injective e_res.toRingHom e_res.injective
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← PowerSeries.map_comp, he_comp,
      FormalGroupHom.id_toPowerSeries, PowerSeries.map_X,
      ← FormalCoordinate.toPowerSeries_map, hψ₁, FormalCoordinate.toPowerSeries_one]
  have heq := f₁.eq_of_map_residue_eq (.id H.formalGroup) hheight hres_eq
  ext n
  have := congrArg (fun u : FormalGroupHom H.formalGroup H.formalGroup ↦
    PowerSeries.coeff n u.toPowerSeries) heq
  simpa [f₁] using this

variable [F₀.IsComm]

private theorem map_lubinTateCocycle_lift (F : FormalGroupLift π_A F₀) (m : ℕ+) :
    MvPowerSeries.map π_A (F.formalGroup.lubinTateCocycle m) = F₀.lubinTateCocycle m := by
  rw [FormalGroup.map_lubinTateCocycle]
  exact @Eq.ndrec _ F₀ (fun G ↦ ∀ [G.IsComm], G.lubinTateCocycle m = F₀.lubinTateCocycle m)
    (fun [_] ↦ rfl) (F.formalGroup.map π_A) F.map_eq.symm _

private theorem homDefect_𝔾ₐ_sum_smul {ι : Type*} (G : FormalGroup A) (s : Finset ι)
    (b : ι → A) (g : ι → PowerSeries A) :
    G.homDefect 𝔾ₐ (∑ i ∈ s, b i • g i) = ∑ i ∈ s, b i • G.homDefect 𝔾ₐ (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, G.homDefect_𝔾ₐ_add, G.homDefect_𝔾ₐ_smul, ih]

private theorem mul_eq_of_ker_mul_eq_bot {I : Ideal A} (hker : RingHom.ker π_A * I = ⊥)
    {a₁ a₂ y : A} (ha : π_A a₁ = π_A a₂) (hy : y ∈ I) : a₁ * y = a₂ * y := by
  rw [← sub_eq_zero, ← sub_mul, ← Ideal.mem_bot, ← hker]
  exact Ideal.mul_mem_mul (by rw [RingHom.mem_ker, map_sub, ha, sub_self]) hy

/-- Extracting a `k`-linearly independent subset with the same `k`-span inside an ideal `I`
annihilated by `RingHom.ker π_A`. -/
private theorem exists_subset_basis_of_ker_mul_eq_bot {I : Ideal A} (hker : RingHom.ker π_A * I = ⊥)
    {sec : k → A} (hsec : ∀ c, π_A (sec c) = c) (s : Finset A) (hs : ∀ x ∈ s, x ∈ I) :
    ∃ t ⊆ s, (∀ x ∈ s, ∃ c : A → k, x = ∑ b ∈ t, sec (c b) * b) ∧
      (∀ c : A → k, ∑ b ∈ t, sec (c b) * b = 0 → ∀ b ∈ t, c b = 0) := by
  classical
  have hsec_zero {y : A} (hy : y ∈ I) : sec 0 * y = 0 :=
    (mul_eq_of_ker_mul_eq_bot (a₂ := 0) hker (by simp [hsec]) hy).trans (zero_mul y)
  have hsec_one {y : A} (hy : y ∈ I) : sec 1 * y = y :=
    (mul_eq_of_ker_mul_eq_bot (a₂ := 1) hker (by simp [hsec]) hy).trans (one_mul y)
  have hsec_mul (u v : k) {y : A} (hy : y ∈ I) : sec u * (sec v * y) = sec (u * v) * y := by
    rw [← mul_assoc]
    exact mul_eq_of_ker_mul_eq_bot hker (by simp [hsec]) hy
  induction s using Finset.induction with
  | empty =>
    exact ⟨∅, Finset.Subset.refl _, fun _ h ↦ absurd h (Finset.notMem_empty _),
      fun _ _ _ h ↦ absurd h (Finset.notMem_empty _)⟩
  | insert a s ha ih =>
    have haI : a ∈ I := hs a (Finset.mem_insert_self a s)
    have hsI : ∀ x ∈ s, x ∈ I := fun x hx ↦ hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨t, hts, hspan, hind⟩ := ih hsI
    have hat : a ∉ t := fun h ↦ ha (hts h)
    by_cases hrel : ∃ d : A → k, d a ≠ 0 ∧ sec (d a) * a + ∑ b ∈ t, sec (d b) * b = 0
    · -- `a` is a `k`-linear combination of `t`, so `t` already spans `insert a s`.
      obtain ⟨d, hda, hd0⟩ := hrel
      refine ⟨t, hts.trans (Finset.subset_insert a s), fun x hx ↦ ?_, hind⟩
      rcases Finset.mem_insert.mp hx with hx_eq | hxs
      · rw [hx_eq]
        refine ⟨fun b ↦ -(d a)⁻¹ * d b, ?_⟩
        have h1 := congrArg (sec (d a)⁻¹ * ·) hd0
        rw [mul_zero, mul_add, hsec_mul _ _ haI, inv_mul_cancel₀ hda, hsec_one haI,
          Finset.mul_sum] at h1
        have h2 : ∑ b ∈ t, sec (d a)⁻¹ * (sec (d b) * b) =
            ∑ b ∈ t, sec ((d a)⁻¹ * d b) * b :=
          Finset.sum_congr rfl fun b hb ↦ hsec_mul _ _ (hsI b (hts hb))
        rw [h2] at h1
        nth_rw 1 [eq_neg_of_add_eq_zero_left h1]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b hb ↦ ?_
        rw [← neg_mul]
        exact mul_eq_of_ker_mul_eq_bot hker (by simp [hsec]) (hsI b (hts hb))
      · exact hspan x hxs
    · -- `a` is independent of `t`, so `insert a t` is a `k`-linearly independent spanning subset.
      push Not at hrel
      refine ⟨insert a t, Finset.insert_subset_insert a hts, fun x hx ↦ ?_, fun c hc b hb ↦ ?_⟩
      · rcases Finset.mem_insert.mp hx with hx_eq | hxs
        · rw [hx_eq]
          refine ⟨fun b ↦ if b = a then 1 else 0, ?_⟩
          rw [Finset.sum_insert hat]
          dsimp only
          rw [ite_eq_left rfl, hsec_one haI, Finset.sum_eq_zero fun b hb ↦ by
            rw [ite_eq_right (fun hba : b = a ↦ hat (hba ▸ hb))]
            exact hsec_zero (hsI b (hts hb)), _root_.add_zero]
        · obtain ⟨c, rfl⟩ := hspan x hxs
          refine ⟨fun b ↦ if b = a then 0 else c b, ?_⟩
          rw [Finset.sum_insert hat]
          dsimp only
          rw [ite_eq_left rfl, hsec_zero haI, _root_.zero_add]
          exact Finset.sum_congr rfl fun b hb ↦ by
            rw [ite_eq_right (fun hba : b = a ↦ hat (hba ▸ hb))]
      · rw [Finset.sum_insert hat] at hc
        have hca : c a = 0 := by
          by_contra hne
          exact hrel c hne hc
        rcases Finset.mem_insert.mp hb with rfl | hbt
        · exact hca
        · rw [hca, hsec_zero haI, _root_.zero_add] at hc
          exact hind c hc b hbt

/-- Extracting a `k`-basis from a finitely generated ideal `I` annihilated by `RingHom.ker π_A`. -/
private theorem exists_finset_basis_of_fg {I : Ideal A} (hFG : I.FG)
    (hπ_A : Function.Surjective π_A) (hker : RingHom.ker π_A * I = ⊥) :
    ∃ (B₀ : Finset A) (sec : k → A), (∀ c, π_A (sec c) = c) ∧
      (∀ b ∈ B₀, b ∈ I) ∧
      (∀ y ∈ I, ∃ c : A → k, y = ∑ b ∈ B₀, sec (c b) * b) ∧
      (∀ c : A → k, ∑ b ∈ B₀, sec (c b) * b = 0 → ∀ b ∈ B₀, c b = 0) := by
  classical
  let sec : k → A := Function.surjInv hπ_A
  have hsec (c : k) : π_A (sec c) = c := Function.surjInv_eq hπ_A c
  obtain ⟨s₀, hs₀⟩ := hFG
  have hs₀I : ∀ x ∈ s₀, x ∈ I := fun x hx ↦ hs₀ ▸ Ideal.subset_span hx
  obtain ⟨B₀, hB₀s, hspan, hind⟩ := exists_subset_basis_of_ker_mul_eq_bot hker hsec s₀ hs₀I
  have hB₀I : ∀ b ∈ B₀, b ∈ I := fun b hb ↦ hs₀I b (hB₀s hb)
  refine ⟨B₀, sec, hsec, hB₀I, fun y hy ↦ ?_, hind⟩
  rw [← hs₀, Submodule.mem_span_finset] at hy
  obtain ⟨f, -, rfl⟩ := hy
  choose! g hg using hspan
  refine ⟨fun b ↦ ∑ x ∈ s₀, π_A (f x) * g x b, ?_⟩
  calc ∑ x ∈ s₀, f x • x
      = ∑ x ∈ s₀, ∑ b ∈ B₀, sec (π_A (f x) * g x b) * b := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hfx : f x • x = f x * ∑ b ∈ B₀, sec (g x b) * b := by
          rw [smul_eq_mul]
          exact congrArg (f x * ·) (hg x hx)
        rw [hfx, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b hb ↦ ?_
        rw [← mul_assoc]
        exact mul_eq_of_ker_mul_eq_bot hker (by simp [hsec]) (hB₀I b hb)
    _ = ∑ b ∈ B₀, ∑ x ∈ s₀, sec (π_A (f x) * g x b) * b := Finset.sum_comm
    _ = ∑ b ∈ B₀, sec (∑ x ∈ s₀, π_A (f x) * g x b) * b := by
        refine Finset.sum_congr rfl fun b hb ↦ ?_
        rw [← Finset.sum_mul]
        exact mul_eq_of_ker_mul_eq_bot hker (by simp [hsec]) (hB₀I b hb)

/-- If a `RingHom.ker q`-linear combination of Lubin–Tate cocycles is a coboundary of a series with
coefficients in `RingHom.ker q`, then all coefficients vanish. -/
private theorem eq_zero_of_sum_lubinTateCocycle_eq_homDefect (hπ_A : Function.Surjective π_A)
    {q : A →+* B} (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥)
    {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h)
    (F : FormalGroupLift π_A F₀) {m : Fin (h - 1) → RingHom.ker q} {g : PowerSeries A}
    (hgI : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker q)
    (hsum : ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) =
      F.formalGroup.homDefect 𝔾ₐ g) : m = 0 := by
  -- Expand `m j` and the coefficients of `g` along a `k`-basis `B₀` of `RingHom.ker q`.
  obtain ⟨B₀, sec, hsec, hB₀I, hspan, hind⟩ := exists_finset_basis_of_fg hFG hπ_A hker
  choose cm hcm using fun j ↦ hspan _ (m j).2
  choose cg hcg using fun n ↦ hspan (PowerSeries.coeff n g) (hgI n)
  let gk (b : A) : PowerSeries k := PowerSeries.mk fun n ↦ cg n b
  let gA (b : A) : PowerSeries A := PowerSeries.mk fun n ↦ sec (cg n b)
  have hg_sum : g = ∑ b' ∈ B₀, b' • gA b' := by
    ext n
    rw [hcg n, map_sum]
    exact Finset.sum_congr rfl fun b' _ ↦ by
      simp [gA, smul_eq_mul, mul_comm b']
  have hlt_sum : ∑ j : Fin (h - 1),
        (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) =
      ∑ b' ∈ B₀, b' • ∑ j : Fin (h - 1),
        sec (cm j b') • F.formalGroup.lubinTateCocycle (primePowPred p j.1) := by
    calc _ = ∑ j : Fin (h - 1), ∑ b' ∈ B₀,
          (sec (cm j b') * b') • F.formalGroup.lubinTateCocycle (primePowPred p j.1) :=
          Finset.sum_congr rfl fun j _ ↦ by rw [hcm j, Finset.sum_smul]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b' _ ↦ ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm (sec _), mul_smul]
  -- Projecting onto each basis element `b ∈ B₀` yields a coboundary relation for `F₀` over `k`.
  have hcoeff_eq (d : Fin 2 →₀ ℕ) (b : A) (hb : b ∈ B₀) :
      coeff d (∑ j : Fin (h - 1), cm j b • F₀.lubinTateCocycle (primePowPred p j.1) -
        F₀.homDefect 𝔾ₐ (gk b)) = 0 := by
    refine hind (fun b' ↦ coeff d (∑ j : Fin (h - 1),
      cm j b' • F₀.lubinTateCocycle (primePowPred p j.1) - F₀.homDefect 𝔾ₐ (gk b'))) ?_ b hb
    have hlhs : ∑ b' ∈ B₀, sec (coeff d (∑ j : Fin (h - 1),
          cm j b' • F₀.lubinTateCocycle (primePowPred p j.1) - F₀.homDefect 𝔾ₐ (gk b'))) * b' =
        coeff d (∑ j : Fin (h - 1),
          (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) -
          F.formalGroup.homDefect 𝔾ₐ g) := by
      rw [hlt_sum, hg_sum, homDefect_𝔾ₐ_sum_smul, ← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun b' hb' ↦ ?_
      rw [← smul_sub, coeff_smul, mul_comm b']
      refine mul_eq_of_ker_mul_eq_bot hker ?_ (hB₀I b' hb')
      have hgA_map : PowerSeries.map π_A (gA b') = gk b' := by ext n; simp [gA, gk, hsec]
      have hmap_rhs : MvPowerSeries.map π_A
          (∑ j : Fin (h - 1),
              sec (cm j b') • F.formalGroup.lubinTateCocycle (primePowPred p j.1) -
            F.formalGroup.homDefect 𝔾ₐ (gA b')) =
          ∑ j : Fin (h - 1), cm j b' • F₀.lubinTateCocycle (primePowPred p j.1) -
            F₀.homDefect 𝔾ₐ (gk b') := by
        rw [map_sub, map_sum, FormalGroup.homDefect_𝔾ₐ, FormalGroup.homDefect_𝔾ₐ,
          map_sub, map_sub,
          PowerSeries.map_subst (.of_constantCoeff_zero F.formalGroup.zero_constantCoeff),
          PowerSeries.map_subst (PowerSeries.HasSubst.X 0),
          PowerSeries.map_subst (PowerSeries.HasSubst.X 1), hgA_map,
          ← FormalGroup.map_toPowerSeries, F.map_eq, map_X, map_X]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [smul_eq_C_mul, map_mul, map_C, hsec, map_lubinTateCocycle_lift, ← smul_eq_C_mul]
      rw [hsec, ← hmap_rhs, coeff_map]
    rw [hlhs, hsum, sub_self, map_zero]
  -- Independence of Lubin–Tate cocycles modulo coboundaries over `k` forces `cm j b = 0`.
  have hF₀_ord : ((p ^ h : ℕ) : ℕ∞) = (F₀.nsmulSeries p).order :=
    (F₀.height_eq_natCast_iff.mp hF₀).symm
  funext j
  apply Subtype.ext
  rw [Pi.zero_apply, Submodule.coe_zero, hcm j]
  refine Finset.sum_eq_zero fun b hb ↦ ?_
  have hbeq : ∑ i : Fin (h - 1), cm i b • F₀.lubinTateCocycle (primePowPred p i.1) =
      F₀.homDefect 𝔾ₐ (gk b) := sub_eq_zero.mp (MvPowerSeries.ext fun d ↦ hcoeff_eq d b hb)
  have hc0 := (F₀.sum_smul_eq_homDefect_𝔾ₐ_iff hp.out hF₀_ord.le (u := fun _ ↦ 1)
    (fun i ↦ by simpa using F₀.le_order_lubinTateCocycle (primePowPred p i.1))
    (fun i ↦ by
      have := F₀.homogeneousComponent_lubinTateCocycle (primePowPred p i.1)
      rwa [coe_primePowPred_add_one, ← one_smul k (TauCeti.lazardCocycle _ k)] at this)
    (fun _ ↦ isUnit_one)).mp ⟨gk b, hbeq⟩
  rw [congrFun hc0 j]
  exact (mul_eq_of_ker_mul_eq_bot hker (by simp [hsec]) (hB₀I b hb)).trans (zero_mul b)

/-- Injectivity of `deformByLubinTate` over a square-zero extension at finite height. -/
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
  -- Any ⋆-equivalence `φ` between the two lifts reduces to `1` over `B` by height-`h` rigidity.
  obtain ⟨φ, hφ_π, hφ_eq⟩ := (mk_eq_mk_iff _ _).mp hm
  have hψ1 : FormalCoordinate.map q φ = 1 := by
    refine eq_one_of_smul_eq_of_map_eq_one hπ_B hF₀ (F.map q hq) ?_ ?_
    · rw [← FormalCoordinate.map_comp, hq, hφ_π]
    · have h1 := congrArg (FormalGroup.map · q) hφ_eq
      rw [FormalGroup.map_smul, ← FormalGroupLift.formalGroup_map _ q hq,
        ← FormalGroupLift.formalGroup_map _ q hq, map_lubinTateLift, map_lubinTateLift] at h1
      exact h1
  have hφI : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ RingHom.ker q :=
    fun n ↦ by
      rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, ← PowerSeries.coeff_map,
        ← PowerSeries.coeff_map, PowerSeries.map_X, ← FormalCoordinate.toPowerSeries_map, hψ1,
        FormalCoordinate.toPowerSeries_one]
  -- Hence `φ ≡ X (mod RingHom.ker q)`, so the difference of parameter sums is a coboundary.
  set G₁ := (lubinTateLift F hq hker_sq p h m₁).formalGroup
  set G₂ := (lubinTateLift F hq hker_sq p h m₂).formalGroup
  obtain ⟨g, -, hgI, hcoc⟩ :=
    (G₁.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ G₂ hker_sq).mp
      ⟨φ, hφI, hφ_eq⟩
  have hFG₁ := coeff_lubinTateLift_sub_mem F hq hker_sq p h m₁
  have hFG₂ := coeff_lubinTateLift_sub_mem F hq hker_sq p h m₂
  have hG₁G₂ : ∀ d, coeff d (G₂.toPowerSeries - G₁.toPowerSeries) ∈ RingHom.ker q := fun d ↦ by
    have hsub : G₂.toPowerSeries - G₁.toPowerSeries =
        (G₂.toPowerSeries - F.formalGroup.toPowerSeries) -
          (G₁.toPowerSeries - F.formalGroup.toPowerSeries) := by ring
    rw [hsub, map_sub]
    exact (RingHom.ker q).sub_mem (hFG₂ d) (hFG₁ d)
  have htrans := FormalGroup.deformationCocycle_trans hker_sq hFG₁ hG₁G₂
  rw [FormalGroup.homDefect_𝔾ₐ_eq_of_coeff_mem hker_sq hFG₁ hgI] at hcoc
  dsimp only [G₁, G₂, lubinTateLift] at htrans hcoc
  rw [FormalGroupLift.formalGroup_deformByCocycle,
    FormalGroupLift.formalGroup_deformByCocycle] at htrans
  rw [FormalGroupLift.formalGroup_deformByCocycle,
    FormalGroupLift.formalGroup_deformByCocycle] at hcoc
  rw [FormalGroup.deformationCocycle_deformByCocycle,
    FormalGroup.deformationCocycle_deformByCocycle, hcoc] at htrans
  have hdiff : ∑ j : Fin (h - 1), ((m₂ j - m₁ j : RingHom.ker q) : A) •
      F.formalGroup.lubinTateCocycle (primePowPred p j.1) = F.formalGroup.homDefect 𝔾ₐ g := by
    simp only [AddSubgroupClass.coe_sub, sub_smul, Finset.sum_sub_distrib]
    linear_combination htrans
  exact (sub_eq_zero.mp (eq_zero_of_sum_lubinTateCocycle_eq_homDefect hπ_A hFG hker hF₀ F
    hgI hdiff)).symm

omit [F₀.IsComm] in
/-- Symmetry of each `k`-basis component of a symmetric series with coefficients in `I`. -/
private theorem subst_swap_component {I : Ideal A} (hker : RingHom.ker π_A * I = ⊥)
    {B₀ : Finset A} {sec : k → A} (hsec : ∀ c, π_A (sec c) = c) (hB₀I : ∀ b ∈ B₀, b ∈ I)
    (hind : ∀ c : A → k, ∑ b ∈ B₀, sec (c b) * b = 0 → ∀ b ∈ B₀, c b = 0)
    {Φ : MvPowerSeries (Fin 2) A}
    (hswap : Φ.subst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) A) = Φ)
    {cΦ : (Fin 2 →₀ ℕ) → A → k} (hcΦ : ∀ d, coeff d Φ = ∑ b ∈ B₀, sec (cΦ d b) * b)
    {b : A} (hb : b ∈ B₀) :
    MvPowerSeries.subst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) k) (fun d ↦ cΦ d b) =
      (fun d ↦ cΦ d b) := by
  let Φk (b' : A) : MvPowerSeries (Fin 2) k := fun d ↦ cΦ d b'
  let ΦA (b' : A) : MvPowerSeries (Fin 2) A := fun d ↦ sec (cΦ d b')
  have hΦA_map (b' : A) : MvPowerSeries.map π_A (ΦA b') = Φk b' := by
    ext d
    rw [coeff_map, coeff_apply, coeff_apply, hsec]
  have hΦ_sum : Φ = ∑ b' ∈ B₀, b' • ΦA b' := by
    ext d
    rw [hcΦ d, map_sum]
    exact Finset.sum_congr rfl fun b' _ ↦ by rw [coeff_smul, coeff_apply, mul_comm]
  have hsub_sw : Φ.subst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) A) =
      ∑ b' ∈ B₀, b' • (ΦA b').subst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) A) := by
    rw [hΦ_sum, ← coe_substAlgHom HasSubst.X_X, map_sum]
    exact Finset.sum_congr rfl fun b' _ ↦ map_smul (substAlgHom HasSubst.X_X) b' (ΦA b')
  ext d
  have h0 : coeff d ((Φk b).subst ![X 1, X 0] - Φk b) = 0 := by
    refine hind (fun b' ↦ coeff d ((Φk b').subst ![X 1, X 0] - Φk b')) ?_ b hb
    have htot : ∑ b' ∈ B₀, sec (coeff d ((Φk b').subst ![X 1, X 0] - Φk b')) * b' =
        coeff d (Φ.subst ![X 1, X 0] - Φ) := by
      rw [hsub_sw, hΦ_sum, ← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun b' hb' ↦ ?_
      rw [← smul_sub, coeff_smul, mul_comm b']
      refine mul_eq_of_ker_mul_eq_bot hker ?_ (hB₀I b' hb')
      have esw : (fun i ↦ MvPowerSeries.map π_A (![X 1, X 0] i)) =
          (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) k) := by funext i; fin_cases i <;> simp
      have hmap_sw : MvPowerSeries.map π_A ((ΦA b').subst ![X 1, X 0] - ΦA b') =
          (Φk b').subst ![X 1, X 0] - Φk b' := by
        rw [map_sub, map_subst HasSubst.X_X, hΦA_map, esw]
      rw [hsec, ← hmap_sw, coeff_map]
    rw [htot, hswap, sub_self, map_zero]
  rw [map_sub, sub_eq_zero] at h0
  exact h0

omit [F₀.IsComm] in
/-- Each `k`-component series of a symmetric 2-cocycle with coefficients in `RingHom.ker q` is a
symmetric 2-cocycle of `F₀` over `k`. -/
private theorem isSymmetricCocycle_component {I : Ideal A} (hker : RingHom.ker π_A * I = ⊥)
    {B₀ : Finset A} {sec : k → A} (hsec : ∀ c, π_A (sec c) = c) (hB₀I : ∀ b ∈ B₀, b ∈ I)
    (hind : ∀ c : A → k, ∑ b ∈ B₀, sec (c b) * b = 0 → ∀ b ∈ B₀, c b = 0)
    (F : FormalGroupLift π_A F₀) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ_coc : F.formalGroup.IsSymmetricCocycle Φ) {cΦ : (Fin 2 →₀ ℕ) → A → k}
    (hcΦ : ∀ d, coeff d Φ = ∑ b ∈ B₀, sec (cΦ d b) * b) {b : A} (hb : b ∈ B₀) :
    F₀.IsSymmetricCocycle (fun d ↦ cΦ d b) := by
  let Φk (b' : A) : MvPowerSeries (Fin 2) k := fun d ↦ cΦ d b'
  let ΦA (b' : A) : MvPowerSeries (Fin 2) A := fun d ↦ sec (cΦ d b')
  have hΦA_map (b' : A) : MvPowerSeries.map π_A (ΦA b') = Φk b' := by
    ext d
    rw [coeff_map, coeff_apply, coeff_apply, hsec]
  have hΦ_sum : Φ = ∑ b' ∈ B₀, b' • ΦA b' := by
    ext d
    rw [hcΦ d, map_sum]
    exact Finset.sum_congr rfl fun b' _ ↦ by rw [coeff_smul, coeff_apply, mul_comm]
  have hsub_sum {τ : Type} {b_sub : Fin 2 → MvPowerSeries τ A} (hb_sub : HasSubst b_sub) :
      Φ.subst b_sub = ∑ b' ∈ B₀, b' • (ΦA b').subst b_sub := by
    rw [hΦ_sum, ← coe_substAlgHom hb_sub, map_sum]
    exact Finset.sum_congr rfl fun b' _ ↦ map_smul (substAlgHom hb_sub) b' (ΦA b')
  refine { subst_swap := subst_swap_component hker hsec hB₀I hind hΦ_coc.subst_swap hcΦ hb
           subst_add_subst_eq := ?_ }
  -- Expand the 3-variable cocycle defect of `Φ` along `B₀` and read off the `b`-component.
  ext d
  have h0 : coeff d ((Φk b).subst ![(X 0 : MvPowerSeries (Fin 3) k), X 1] +
      (Φk b).subst ![F₀.toPowerSeries.subst ![X 0, X 1], X 2] -
      (Φk b).subst ![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] -
      (Φk b).subst ![X 1, X 2]) = 0 := by
    refine hind (fun b' ↦ coeff d ((Φk b').subst ![(X 0 : MvPowerSeries (Fin 3) k), X 1] +
        (Φk b').subst ![F₀.toPowerSeries.subst ![X 0, X 1], X 2] -
        (Φk b').subst ![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] -
        (Φk b').subst ![X 1, X 2])) ?_ b hb
    have hX0 := PowerSeries.HasSubst.X (S := A) (0 : Fin 3)
    have hX1 := PowerSeries.HasSubst.X (S := A) (1 : Fin 3)
    have hX2 := PowerSeries.HasSubst.X (S := A) (2 : Fin 3)
    have hs1 := hasSubst_finTwo hX0 hX1
    have hs2 := hasSubst_finTwo (F.formalGroup.hasSubst_subst_pair hX0 hX1) hX2
    have hs3 := hasSubst_finTwo hX0 (F.formalGroup.hasSubst_subst_pair hX1 hX2)
    have hs4 := hasSubst_finTwo hX1 hX2
    -- Identify the `B₀`-combination of reduced cocycle defects with the cocycle defect of `Φ`.
    have htot : ∑ b' ∈ B₀, sec (coeff d
          ((Φk b').subst ![(X 0 : MvPowerSeries (Fin 3) k), X 1] +
          (Φk b').subst ![F₀.toPowerSeries.subst ![X 0, X 1], X 2] -
          (Φk b').subst ![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] -
          (Φk b').subst ![X 1, X 2])) * b' =
        coeff d (Φ.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1] +
          Φ.subst ![F.formalGroup.toPowerSeries.subst ![X 0, X 1], X 2] -
          Φ.subst ![X 0, F.formalGroup.toPowerSeries.subst ![X 1, X 2]] -
          Φ.subst ![X 1, X 2]) := by
      rw [hsub_sum hs1, hsub_sum hs2, hsub_sum hs3, hsub_sum hs4, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun b' hb' ↦ ?_
      simp only [← smul_add, ← smul_sub, coeff_smul, mul_comm b']
      refine mul_eq_of_ker_mul_eq_bot hker ?_ (hB₀I b' hb')
      have e1 : (fun i ↦ MvPowerSeries.map π_A (![(X 0 : MvPowerSeries (Fin 3) A), X 1] i)) =
          ![X 0, X 1] := by funext i; fin_cases i <;> simp
      have e4 : (fun i ↦ MvPowerSeries.map π_A (![(X 1 : MvPowerSeries (Fin 3) A), X 2] i)) =
          ![X 1, X 2] := by funext i; fin_cases i <;> simp
      have e2 : (fun i ↦ MvPowerSeries.map π_A
          (![F.formalGroup.toPowerSeries.subst
            ![(X 0 : MvPowerSeries (Fin 3) A), X 1], X 2] i)) =
          ![F₀.toPowerSeries.subst ![X 0, X 1], X 2] := by
        refine funext <| Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · simp [map_subst HasSubst.X_X, e1, ← FormalGroup.map_toPowerSeries, F.map_eq]
        · simp
      have e3 : (fun i ↦ MvPowerSeries.map π_A
          (![X 0, F.formalGroup.toPowerSeries.subst
            ![(X 1 : MvPowerSeries (Fin 3) A), X 2]] i)) =
          ![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] := by
        refine funext <| Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · simp
        · simp [map_subst HasSubst.X_X, e4, ← FormalGroup.map_toPowerSeries, F.map_eq]
      have hmap_4 : MvPowerSeries.map π_A
          ((ΦA b').subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1] +
            (ΦA b').subst ![F.formalGroup.toPowerSeries.subst ![X 0, X 1], X 2] -
            (ΦA b').subst ![X 0, F.formalGroup.toPowerSeries.subst ![X 1, X 2]] -
            (ΦA b').subst ![X 1, X 2]) =
          (Φk b').subst ![(X 0 : MvPowerSeries (Fin 3) k), X 1] +
            (Φk b').subst ![F₀.toPowerSeries.subst ![X 0, X 1], X 2] -
            (Φk b').subst ![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] -
            (Φk b').subst ![X 1, X 2] := by
        rw [map_sub, map_sub, map_add, map_subst hs1, map_subst hs2, map_subst hs3,
          map_subst hs4, hΦA_map, e1, e2, e3, e4]
      rw [hsec, ← hmap_4, coeff_map]
    have hcoc0 : Φ.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1] +
        Φ.subst
          ![F.formalGroup.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1], X 2] -
        Φ.subst ![X 0, F.formalGroup.toPowerSeries.subst ![X 1, X 2]] -
        Φ.subst ![X 1, X 2] = 0 := by
      rw [hΦ_coc.subst_add_subst_eq]
      abel
    rw [htot, hcoc0, map_zero]
  rw [sub_sub, map_sub, sub_eq_zero] at h0
  exact h0

/-- Decomposing a symmetric 2-cocycle `Φ` of `F.formalGroup` with coefficients in `RingHom.ker q`
into a `RingHom.ker q`-linear combination of Lubin–Tate cocycles plus a coboundary. -/
private theorem exists_lubinTate_decomp_of_coeff_mem (hπ_A : Function.Surjective π_A)
    {q : A →+* B} (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥)
    {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h)
    (F : FormalGroupLift π_A F₀) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ_coc : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ RingHom.ker q) :
    ∃ (m : Fin (h - 1) → RingHom.ker q) (g : PowerSeries A),
      PowerSeries.constantCoeff g = 0 ∧ (∀ n, PowerSeries.coeff n g ∈ RingHom.ker q) ∧
      Φ = ∑ j : Fin (h - 1), (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) +
        F.formalGroup.homDefect 𝔾ₐ g := by
  -- Decompose `Φ` along a `k`-basis `B₀` of `RingHom.ker q` into symmetric 2-cocycles over `k`.
  obtain ⟨B₀, sec, hsec, hB₀I, hspan, hind⟩ := exists_finset_basis_of_fg hFG hπ_A hker
  choose cΦ hcΦ using fun d ↦ hspan (coeff d Φ) (hΦI d)
  let Φk (b : A) : MvPowerSeries (Fin 2) k := fun d ↦ cΦ d b
  let ΦA (b : A) : MvPowerSeries (Fin 2) A := fun d ↦ sec (cΦ d b)
  have hΦ_sum : Φ = ∑ b ∈ B₀, b • ΦA b := by
    ext d
    rw [hcΦ d, map_sum]
    exact Finset.sum_congr rfl fun b _ ↦ by rw [coeff_smul, coeff_apply, mul_comm]
  have hΦk_zero (b : A) (hb : b ∈ B₀) : constantCoeff (Φk b) = 0 :=
    hind (fun b' ↦ cΦ 0 b') (by rw [← hcΦ 0, coeff_zero_eq_constantCoeff_apply, hΦ₀]) b hb
  -- Expand each `k`-component `Φk b` in the Lubin–Tate cocycle basis of `F₀` modulo coboundaries.
  have hF₀_ord : ((p ^ h : ℕ) : ℕ∞) = (F₀.nsmulSeries p).order :=
    (F₀.height_eq_natCast_iff.mp hF₀).symm
  have hF₀_unit : IsUnit (PowerSeries.coeff (p ^ h) (F₀.nsmulSeries p)) :=
    (F₀.coeff_nsmulSeries_ne_zero_of_height_eq hF₀).isUnit
  have hex (b : A) (hb : b ∈ B₀) : ∃ (c : Fin (h - 1) → k) (gk : PowerSeries k),
      PowerSeries.constantCoeff gk = 0 ∧
        Φk b = ∑ j : Fin (h - 1), c j • F₀.lubinTateCocycle (primePowPred p j.1) +
          F₀.homDefect 𝔾ₐ gk := by
    have hcomp_coc := isSymmetricCocycle_component hker hsec hB₀I hind F hΦ_coc hcΦ hb
    obtain ⟨c, ⟨gk, hgk₀, hgk⟩, -⟩ :=
      hcomp_coc.existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ
        hp.out (CharP.cast_eq_zero k p) hF₀_ord.le hF₀_unit (hΦk_zero b hb)
    exact ⟨c, gk, hgk₀, hgk⟩
  choose! ck gk hgk₀ hΦk_eq using hex
  -- Lift the coefficients `ck b j` and coboundary series `gk b` back to `A` via `sec`.
  let gA (b : A) : PowerSeries A :=
    PowerSeries.mk fun n ↦ if n = 0 then 0 else sec (PowerSeries.coeff n (gk b))
  have hgA_map (b : A) (hb : b ∈ B₀) : PowerSeries.map π_A (gA b) = gk b := by
    ext n
    rcases n with _ | n
    · simp [gA, PowerSeries.coeff_zero_eq_constantCoeff_apply, hgk₀ b hb]
    · simp [gA, hsec]
  let m : Fin (h - 1) → RingHom.ker q := fun j ↦
    ⟨∑ b ∈ B₀, sec (ck b j) * b,
      Ideal.sum_mem _ fun b hb ↦ (RingHom.ker q).mul_mem_left _ (hB₀I b hb)⟩
  refine ⟨m, ∑ b ∈ B₀, b • gA b, ?_, fun n ↦ ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero fun b _ ↦ by simp [gA]
  · rw [map_sum]
    exact Ideal.sum_mem _ fun b hb ↦ by
      rw [PowerSeries.coeff_smul, smul_eq_mul]
      exact (RingHom.ker q).mul_mem_right _ (hB₀I b hb)
  · have hsum_m : ∑ j : Fin (h - 1),
          (m j : A) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) =
        ∑ b ∈ B₀, b • ∑ j : Fin (h - 1),
          sec (ck b j) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) := by
      calc _ = ∑ j : Fin (h - 1), ∑ b ∈ B₀,
            (sec (ck b j) * b) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) :=
            Finset.sum_congr rfl fun j _ ↦ by rw [Finset.sum_smul]
        _ = _ := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ ↦ ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm (sec _), mul_smul]
    rw [hΦ_sum, hsum_m, homDefect_𝔾ₐ_sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    ext d
    rw [← smul_add, coeff_smul, coeff_smul, mul_comm b, mul_comm b]
    refine mul_eq_of_ker_mul_eq_bot hker ?_ (hB₀I b hb)
    have hΦA_d : π_A (coeff d (ΦA b)) = coeff d (Φk b) := by
      rw [coeff_apply, coeff_apply, hsec]
    have hmap_rhs : MvPowerSeries.map π_A
        (∑ j : Fin (h - 1), sec (ck b j) • F.formalGroup.lubinTateCocycle (primePowPred p j.1) +
          F.formalGroup.homDefect 𝔾ₐ (gA b)) = Φk b := by
      rw [hΦk_eq b hb, map_add, map_sum, FormalGroup.homDefect_𝔾ₐ, FormalGroup.homDefect_𝔾ₐ,
        map_sub, map_sub,
        PowerSeries.map_subst (.of_constantCoeff_zero F.formalGroup.zero_constantCoeff),
        PowerSeries.map_subst (PowerSeries.HasSubst.X 0),
        PowerSeries.map_subst (PowerSeries.HasSubst.X 1),
        hgA_map b hb, ← FormalGroup.map_toPowerSeries, F.map_eq, map_X, map_X]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_eq_C_mul, map_mul, map_C, hsec, map_lubinTateCocycle_lift, ← smul_eq_C_mul]
    rw [hΦA_d, ← hmap_rhs, coeff_map]

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
  let toFiber (m : Fin (h - 1) → RingHom.ker q) :
      {x : FormalGroupDeformation π_A F₀ //
        FormalGroupDeformation.map q hq x = ⟦F.map q hq⟧} :=
    ⟨deformByLubinTate F hq hker_sq p h m, map_deformByLubinTate F hq hker_sq p h m⟩
  refine Equiv.ofBijective toFiber
    ⟨fun m₁ m₂ hm ↦ deformByLubinTate_injective hπ_B hq hq_surj hFG hker hF₀ F
      (congrArg Subtype.val hm), ?_⟩
  rintro ⟨x, hx⟩
  induction x using Quotient.inductionOn with | _ G₀ =>
  -- Lift the ⋆-equivalence `ψ` over `B` along the nilpotent-kernel surjection `q` to replace `G₀`
  -- by a representative `G` in the same deformation class with `G.map q hq = F.map q hq`.
  rw [map_mk] at hx
  obtain ⟨ψ, hψ_π, hψ_eq⟩ := (mk_eq_mk_iff _ _).mp hx
  have : IsLocalHom q := q.isLocalHom_of_surjective_of_isNilpotent_ker hq_surj fun y hy ↦
    ⟨2, by
      rw [pow_two, ← Ideal.mem_bot, ← hker_sq]
      exact Ideal.mul_mem_mul hy hy⟩
  obtain ⟨φ₀, hφ₀_q⟩ := FormalCoordinate.map_surjective_of_isLocalHom q hq_surj ψ
  have hφ₀_π : FormalCoordinate.map π_A φ₀ = 1 := by
    rw [← hq, FormalCoordinate.map_comp, hφ₀_q, hψ_π]
  let G : FormalGroupLift π_A F₀ :=
    (⟨φ₀, MonoidHom.mem_ker.mpr hφ₀_π⟩ : (FormalCoordinate.map π_A).ker) • G₀
  have hG_class : (⟦G⟧ : FormalGroupDeformation π_A F₀) = ⟦G₀⟧ :=
    ((mk_eq_mk_iff G₀ G).mpr ⟨φ₀, hφ₀_π, rfl⟩).symm
  have hGq : G.map q hq = F.map q hq := by
    apply FormalGroupLift.ext
    rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_smul, FormalGroup.map_smul,
      hφ₀_q, ← FormalGroupLift.formalGroup_map G₀ q hq, hψ_eq]
  -- Decompose the deformation cocycle from `F` to `G` into Lubin–Tate cocycles + coboundary.
  have hFG_mem : ∀ d, coeff d (G.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) ∈
      RingHom.ker q := fun d ↦ by
    have hd := congrArg (fun H : FormalGroupLift π_B F₀ ↦ coeff d H.formalGroup.toPowerSeries) hGq
    simpa [FormalGroup.map_toPowerSeries, RingHom.mem_ker, sub_eq_zero] using hd
  obtain ⟨m, g, hg₀, hgI, hΦ_decomp⟩ :=
    exists_lubinTate_decomp_of_coeff_mem hπ_A hFG hker hF₀ F
      (F.formalGroup.isSymmetricCocycle_deformationCocycle G.formalGroup hker_sq hFG_mem)
      (F.formalGroup.constantCoeff_deformationCocycle G.formalGroup)
      (FormalGroup.coeff_deformationCocycle_mem_iff.mpr hFG_mem)
  -- Convert the remaining coboundary `homDefect 𝔾ₐ g` into an infinitesimal coordinate `φ`.
  set Fm := lubinTateLift F hq hker_sq p h m
  have hFm_mem := coeff_lubinTateLift_sub_mem F hq hker_sq p h m
  have hFmG_mem : ∀ d, coeff d (G.formalGroup.toPowerSeries - Fm.formalGroup.toPowerSeries) ∈
      RingHom.ker q := fun d ↦ by
    have hsub : G.formalGroup.toPowerSeries - Fm.formalGroup.toPowerSeries =
        (G.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) -
          (Fm.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) := by ring
    rw [hsub, map_sub]
    exact (RingHom.ker q).sub_mem (hFG_mem d) (hFm_mem d)
  have htrans := FormalGroup.deformationCocycle_trans hker_sq hFm_mem hFmG_mem
  have hFmG_coc : Fm.formalGroup.deformationCocycle G.formalGroup =
      Fm.formalGroup.homDefect 𝔾ₐ g := by
    rw [FormalGroup.homDefect_𝔾ₐ_eq_of_coeff_mem hker_sq hFm_mem hgI]
    dsimp only [Fm, lubinTateLift] at htrans ⊢
    rw [FormalGroupLift.formalGroup_deformByCocycle] at htrans ⊢
    rw [FormalGroup.deformationCocycle_deformByCocycle] at htrans
    linear_combination hΦ_decomp - htrans
  obtain ⟨φ, hφI, hφ_smul⟩ :=
    (Fm.formalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
      G.formalGroup hker_sq).mpr ⟨g, hg₀, hgI, hFmG_coc⟩
  have hφ_π : FormalCoordinate.map π_A φ = 1 := by
    ext n
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one,
      PowerSeries.coeff_map, ← PowerSeries.map_X π_A, PowerSeries.coeff_map, ← sub_eq_zero,
      ← map_sub, ← map_sub]
    exact RingHom.mem_ker.mp (ker_le_ker_of_comp_eq hq (hφI n))
  exact ⟨m, Subtype.ext (((mk_eq_mk_iff Fm G).mpr ⟨φ, hφ_π, hφ_smul⟩).trans hG_class)⟩

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
  rw [squareZeroFiberEquiv]
  rfl

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
  let e := squareZeroFiberEquiv hπ_B hq hq_surj hFG hker hF₀ F
  have hsub : Subsingleton {x : FormalGroupDeformation π_A F₀ //
      FormalGroupDeformation.map q hq x = ⟦F.map q hq⟧} := e.symm.injective.subsingleton
  exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨x₁, hx⟩ ⟨⟦F⟧, map_mk q hq F⟩)

/-- The kernel of the projection `DualNumber R →+* R` has square zero. -/
theorem ker_fstHom_mul_self_eq_bot (R : Type*) [CommRing R] :
    RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom *
      RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom = ⊥ := by
  rw [eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx0 : x.fst = 0 := hx
  have hy0 : y.fst = 0 := hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx0, hy0]

/-- **The Lubin–Tate tangent space.** For a commutative formal group law `F₀` of finite height `h`
over a field `k` of characteristic `p`, the set of deformations of `F₀` over the dual numbers
`DualNumber k = k[ε]` (`ε² = 0`) is canonically equivalent to `Fin (h - 1) → k`. -/
noncomputable def dualNumberEquiv {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) :
    (Fin (h - 1) → k) ≃
      FormalGroupDeformation (TrivSqZeroExt.fstHom k k k).toRingHom F₀ := by
  let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hcomp : (RingHom.id k).comp π = π := RingHom.id_comp π
  let F_triv : FormalGroupLift π F₀ :=
    FormalGroupLift.ofSection F₀ π (algebraMap k (DualNumber k))
      (RingHom.ext fun c ↦ by simp [π])
  have hker_span : RingHom.ker π = Ideal.span {DualNumber.eps} := by
    ext z
    simp only [RingHom.mem_ker, Ideal.mem_span_singleton, π, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply]
    constructor
    · intro hz
      refine ⟨algebraMap k (DualNumber k) z.snd, ?_⟩
      ext <;> simp [hz, TrivSqZeroExt.algebraMap_eq_inl]
    · rintro ⟨w, rfl⟩
      simp
  have hFG : (RingHom.ker π).FG := ⟨{DualNumber.eps}, by simpa using hker_span.symm⟩
  let eKer : k ≃ RingHom.ker π :=
    { toFun c := ⟨TrivSqZeroExt.inr c, by simp [RingHom.mem_ker, π]⟩
      invFun z := z.val.snd
      left_inv c := by simp
      right_inv z := by
        apply Subtype.ext
        have hz : z.val.fst = 0 := z.2
        ext <;> simp [hz] }
  let eFib := squareZeroFiberEquiv (B := k) (π_B := RingHom.id k) Function.surjective_id
    hcomp (fun c ↦ ⟨algebraMap k (DualNumber k) c, by simp [π]⟩)
    hFG (ker_fstHom_mul_self_eq_bot k) hF₀ F_triv
  let eDrop : {x : FormalGroupDeformation π F₀ //
      FormalGroupDeformation.map π hcomp x = ⟦F_triv.map π hcomp⟧} ≃
      FormalGroupDeformation π F₀ :=
    { toFun x := x.val
      invFun x := ⟨x, Subsingleton.elim _ _⟩
      left_inv x := Subtype.ext rfl
      right_inv _ := rfl }
  exact (Equiv.piCongrRight fun _ ↦ eKer).trans (eFib.trans eDrop)

/-- Evaluating `dualNumberEquiv` deforms the trivial lift along `ε • cⱼ`. -/
theorem dualNumberEquiv_apply {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (c : Fin (h - 1) → k) :
    dualNumberEquiv hF₀ c =
      deformByLubinTate
        (FormalGroupLift.ofSection F₀ (TrivSqZeroExt.fstHom k k k).toRingHom
          (algebraMap k (DualNumber k)) (RingHom.ext fun x ↦ by simp))
        (RingHom.id_comp _)
        (ker_fstHom_mul_self_eq_bot k)
        p h (fun j ↦ ⟨TrivSqZeroExt.inr (c j), by simp [RingHom.mem_ker]⟩) := by
  rw [dualNumberEquiv]
  rfl

end SquareZeroFiber

end TauCeti.FormalGroupDeformation
