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
public import TauCeti.RingTheory.Ideal.Maps
public import TauCeti.RingTheory.Ideal.Operations
public import TauCeti.RingTheory.TrivSqZeroExt
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.DualNumber
import TauCeti.Algebra.Module.Torsion.Finite
import TauCeti.Algebra.Module.Torsion.ScalarAction
import TauCeti.RingTheory.FormalGroup.Deformation.Lifting
import TauCeti.RingTheory.FormalGroup.Rigidity
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height
import TauCeti.RingTheory.LocalRing.RingHom
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Basic
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Square-zero fibres of finite-height formal group deformations

Let `F₀` be a commutative formal group law over a field `k` of characteristic `p`, and let
`q : A →+* B` be a surjective ring homomorphism compatible with `π_A : A →+* k` and `π_B : B →+* k`
(`π_B.comp q = π_A`). Building on `TauCeti.RingTheory.FormalGroup.SymmetricCocycle.LubinTate`, this
file classifies framed lifts (`TauCeti.FormalGroupLift`) and coordinate-equivalence classes of
deformations (`TauCeti.FormalGroupDeformation`) across square-zero extensions.

## Main definitions and results

* `TauCeti.FormalGroupLift.deformByCocycle`, `TauCeti.FormalGroupLift.map_deformByCocycle`,
  `TauCeti.FormalGroupLift.deformationCocycleEquiv`: identifies the square-zero fibre of
  `FormalGroupLift.map q hq` with symmetric 2-cocycles without constant term with coefficients in
  `RingHom.ker q`.
* `TauCeti.FormalGroupLift.deformByLubinTate`,
  `TauCeti.FormalGroupLift.deformationCocycle_deformByLubinTate`,
  `TauCeti.FormalGroupLift.map_deformByLubinTate`: explicit framed lifts deformed by the canonical
  Lubin–Tate cocycles.
* `TauCeti.FormalGroupDeformation.deformByLubinTate`,
  `TauCeti.FormalGroupDeformation.map_deformByLubinTate_of_map_ker_le`,
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

namespace TauCeti

namespace FormalGroupLift

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

/-- Base change along `f : A →+* B'` compatible with reductions transports
`F.deformByCocycle` to `(F.map f hf).deformByCocycle` for any square-zero ideal
`J ≤ RingHom.ker π_B'` containing `I.map f`. -/
theorem map_deformByCocycle (F : FormalGroupLift π_A F₀) {I : Ideal A} (hI : I * I = ⊥)
    (hIπ : I ≤ RingHom.ker π_A) {B' : Type*} [CommRing B'] {π_B' : B' →+* k}
    (f : A →+* B') (hf : π_B'.comp f = π_A) {J : Ideal B'} (hJ : J * J = ⊥)
    (hJπ : J ≤ RingHom.ker π_B') (hIJ : I.map f ≤ J) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) :
    (F.deformByCocycle hI hIπ hΦ hΦ₀ hΦI).map f hf =
      (F.map f hf).deformByCocycle hJ hJπ (Φ := MvPowerSeries.map f Φ)
        (by rw [formalGroup_map]; exact hΦ.map f)
        (by rw [MvPowerSeries.constantCoeff_map, hΦ₀, map_zero])
        (fun d ↦ hIJ (Ideal.mem_map_of_mem f (hΦI d))) :=
  FormalGroupLift.ext <| by
    rw [formalGroup_map, formalGroup_deformByCocycle, formalGroup_deformByCocycle,
      F.formalGroup.map_deformByCocycle hI f hJ hIJ hΦ hΦ₀ hΦI]
    ext d
    simp only [FormalGroup.toPowerSeries_deformByCocycle, FormalGroupLift.formalGroup_map]

private noncomputable def fiberToFormalGroupEquiv (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) :
    {G : FormalGroupLift π_A F₀ // G.map q hq = F.map q hq} ≃
      {G : FormalGroup A //
        G.IsComm ∧
          ∀ d, coeff d (G.toPowerSeries - F.formalGroup.toPowerSeries) ∈ RingHom.ker q} where
  toFun G := ⟨G.val.formalGroup, G.val.isComm, coeff_sub_mem_ker_of_map_eq G.property⟩
  invFun G :=
    have hmap : G.val.map q = F.formalGroup.map q := by
      ext d
      simpa [FormalGroup.map_toPowerSeries, RingHom.mem_ker, sub_eq_zero] using G.property.2 d
    ⟨{ formalGroup := G.val
       isComm := G.property.1
       map_eq :=
         have h1 : G.val.map (π_B.comp q) = F.formalGroup.map (π_B.comp q) := by
           rw [← FormalGroup.map_comp, hmap, FormalGroup.map_comp]
         (congrArg (FormalGroup.map G.val) hq.symm).trans
           (h1.trans ((congrArg (FormalGroup.map F.formalGroup) hq).trans F.map_eq)) },
      FormalGroupLift.ext <| by rw [formalGroup_map, formalGroup_map, hmap]⟩
  left_inv _ := Subtype.ext (FormalGroupLift.ext rfl)
  right_inv _ := Subtype.ext rfl

@[simp]
private theorem fiberToFormalGroupEquiv_apply_coe (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (G : {G : FormalGroupLift π_A F₀ // G.map q hq = F.map q hq}) :
    (F.fiberToFormalGroupEquiv hq G).val = G.val.formalGroup :=
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
          ∀ d, coeff d Φ ∈ RingHom.ker q} :=
  (F.fiberToFormalGroupEquiv hq).trans (F.formalGroup.deformationCocycleEquiv hker)

/-- Evaluating `FormalGroupLift.deformationCocycleEquiv` computes `deformationCocycle`. -/
@[simp]
theorem deformationCocycleEquiv_apply_coe (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (G : {G : FormalGroupLift π_A F₀ // G.map q hq = F.map q hq}) :
    (F.deformationCocycleEquiv hq hker G).val =
      F.formalGroup.deformationCocycle G.val.formalGroup := by
  rw [deformationCocycleEquiv, Equiv.trans_apply, FormalGroup.deformationCocycleEquiv_apply_coe,
    fiberToFormalGroupEquiv_apply_coe]

/-- Evaluating the inverse of `FormalGroupLift.deformationCocycleEquiv` constructs
`FormalGroupLift.deformByCocycle`. -/
@[simp]
theorem deformationCocycleEquiv_symm_apply_coe (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (Φ : {Φ : MvPowerSeries (Fin 2) A //
      F.formalGroup.IsSymmetricCocycle Φ ∧ constantCoeff Φ = 0 ∧
        ∀ d, coeff d Φ ∈ RingHom.ker q}) :
    ((F.deformationCocycleEquiv hq hker).symm Φ).val =
      F.deformByCocycle hker (RingHom.ker_le_ker_of_comp_eq hq)
        Φ.property.1 Φ.property.2.1 Φ.property.2.2 := by
  refine FormalGroupLift.ext ?_
  rw [deformationCocycleEquiv, Equiv.symm_trans_apply]
  exact FormalGroup.deformationCocycleEquiv_symm_apply_coe F.formalGroup hker Φ

/-- Deforming a reference lift `F : FormalGroupLift π_A F₀` along a tuple
`m : Fin (h - 1) → RingHom.ker q` using the canonical Lubin–Tate symmetric 2-cocycles in degrees
`p, p², …, p^(h - 1)`. -/
noncomputable def deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [hp : Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupLift π_A F₀ :=
  F.deformByCocycle hker (RingHom.ker_le_ker_of_comp_eq hq)
    (FormalGroup.IsSymmetricCocycle.sum (s := Finset.univ) fun j _ ↦
      (F.formalGroup.isSymmetricCocycle_lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val)).smul
        (m j : A))
    (by rw [map_sum]; exact Finset.sum_eq_zero fun j _ ↦ by simp)
    (fun d ↦ by
      rw [map_sum]
      exact Ideal.sum_mem _ fun j _ ↦ by
        rw [coeff_smul]; exact (RingHom.ker q).mul_mem_right _ (m j).property)

/-- The deformation cocycle of `F.deformByLubinTate` relative to `F` is the linear combination of
the canonical Lubin–Tate cocycles. -/
@[simp]
theorem deformationCocycle_deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [hp : Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    F.formalGroup.deformationCocycle (F.deformByLubinTate hq hker p h m).formalGroup =
      ∑ j : Fin (h - 1),
        (m j : A) • F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) := by
  rw [deformByLubinTate, formalGroup_deformByCocycle,
    FormalGroup.deformationCocycle_deformByCocycle]

/-- Deforming a framed lift by `0` leaves it unchanged. -/
@[simp]
theorem deformByLubinTate_zero (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] :
    F.deformByLubinTate hq hker p h 0 = F :=
  FormalGroupLift.ext (by ext d; simp [deformByLubinTate])

/-- Every Lubin–Tate deformation of `F` along `m : Fin (h - 1) → RingHom.ker q` maps to `F.map q hq`
over `B`. -/
@[simp]
theorem map_deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    (F.deformByLubinTate hq hker p h m).map q hq = F.map q hq :=
  FormalGroupLift.ext <| by
    rw [formalGroup_map, formalGroup_map, deformByLubinTate, formalGroup_deformByCocycle]
    exact F.formalGroup.map_deformByCocycle_eq hker q le_rfl _ _ _

/-- Base change along a compatible homomorphism `f : A →+* A'` carrying `RingHom.ker q` into
`RingHom.ker q'` transports `F.deformByLubinTate` to `(F.map f hf).deformByLubinTate` with
coefficients mapped by `f`. -/
theorem map_deformByLubinTate_of_map_ker_le {A' B' : Type*} [CommRing A'] [CommRing B']
    {π_A' : A' →+* k} {π_B' : B' →+* k} (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    {q' : A' →+* B'} (hq' : π_B'.comp q' = π_A') (hker' : RingHom.ker q' * RingHom.ker q' = ⊥)
    (f : A →+* A') (hf : π_A'.comp f = π_A) (hfq : (RingHom.ker q).map f ≤ RingHom.ker q')
    {p h : ℕ} [hp : Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    (F.deformByLubinTate hq hker p h m).map f hf =
      (F.map f hf).deformByLubinTate hq' hker' p h
        (fun j ↦ ⟨f (m j), hfq (Ideal.mem_map_of_mem f (m j).property)⟩) := by
  rw [deformByLubinTate, deformByLubinTate,
    F.map_deformByCocycle hker (RingHom.ker_le_ker_of_comp_eq hq) f hf hker'
      (RingHom.ker_le_ker_of_comp_eq hq') hfq]
  refine FormalGroupLift.ext ?_
  have hsum :
      MvPowerSeries.map f
          (∑ i : Fin (h - 1),
            (m i : A) • F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt i.val)) =
        ∑ i : Fin (h - 1),
          (⟨f (m i), hfq (Ideal.mem_map_of_mem f (m i).property)⟩ : RingHom.ker q').val •
            (F.map f hf).formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt i.val) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_eq_C_mul, map_mul, map_C, FormalGroup.map_lubinTateCocycle, ← smul_eq_C_mul,
      FormalGroup.lubinTateCocycle_congr (FormalGroupLift.formalGroup_map F f hf).symm]
  ext d
  simp only [formalGroup_deformByCocycle, FormalGroup.toPowerSeries_deformByCocycle,
    formalGroup_map, hsum]

end FormalGroupLift

namespace FormalGroupDeformation

section SquareZeroFiber

open _root_.IsLocalRing

variable {A B k : Type*} [CommRing A] [CommRing B] [Field k]
  {π_A : A →+* k} {π_B : B →+* k} {F₀ : FormalGroup k}

private theorem coeff_deformByLubinTate_sub_mem (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) (d : Fin 2 →₀ ℕ) :
    coeff d ((F.deformByLubinTate hq hker p h m).formalGroup.toPowerSeries -
      F.formalGroup.toPowerSeries) ∈ RingHom.ker q :=
  FormalGroupLift.coeff_sub_mem_ker_of_map_eq (F.map_deformByLubinTate hq hker p h m) d

/-- Deforming a reference lift `F : FormalGroupLift π_A F₀` along a tuple
`m : Fin (h - 1) → RingHom.ker q` using the canonical Lubin–Tate symmetric 2-cocycles in degrees
`p, p², …, p^(h - 1)`. -/
noncomputable def deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupDeformation π_A F₀ :=
  ⟦F.deformByLubinTate hq hker p h m⟧

/-- Unfolding `FormalGroupDeformation.deformByLubinTate` as the class of
`FormalGroupLift.deformByLubinTate`. -/
theorem deformByLubinTate_def (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    deformByLubinTate F hq hker p h m = ⟦F.deformByLubinTate hq hker p h m⟧ := (rfl)

/-- Deforming `F` by `0` gives the deformation class `⟦F⟧`. -/
@[simp]
theorem deformByLubinTate_zero (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] :
    deformByLubinTate F hq hker p h 0 = ⟦F⟧ :=
  congrArg Quotient.mk'' (F.deformByLubinTate_zero hq hker p h)

/-- Every Lubin–Tate deformation along `m : Fin (h - 1) → RingHom.ker q` maps to `⟦F.map q hq⟧`
over `B`. -/
@[simp]
theorem map_deformByLubinTate (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    (p h : ℕ) [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupDeformation.map q hq (deformByLubinTate F hq hker p h m) = ⟦F.map q hq⟧ := by
  rw [deformByLubinTate, map_mk, FormalGroupLift.map_deformByLubinTate]

/-- Base change along a compatible homomorphism `f : A →+* A'` carrying `RingHom.ker q` into
`RingHom.ker q'` transports `deformByLubinTate` to `deformByLubinTate` of `F.map f hf` with
coefficients mapped by `f`. -/
theorem map_deformByLubinTate_of_map_ker_le {A' B' : Type*} [CommRing A'] [CommRing B']
    {π_A' : A' →+* k} {π_B' : B' →+* k} (F : FormalGroupLift π_A F₀) {q : A →+* B}
    (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥)
    {q' : A' →+* B'} (hq' : π_B'.comp q' = π_A') (hker' : RingHom.ker q' * RingHom.ker q' = ⊥)
    (f : A →+* A') (hf : π_A'.comp f = π_A) (hfq : (RingHom.ker q).map f ≤ RingHom.ker q')
    {p h : ℕ} [Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q) :
    FormalGroupDeformation.map f hf (deformByLubinTate F hq hker p h m) =
      deformByLubinTate (F.map f hf) hq' hker' p h
        (fun j ↦ ⟨f (m j), hfq (Ideal.mem_map_of_mem f (m j).property)⟩) := by
  rw [deformByLubinTate, deformByLubinTate, map_mk]
  exact congrArg Quotient.mk'' (F.map_deformByLubinTate_of_map_ker_le hq hker hq' hker' f hf hfq m)

section IdealBasis

variable {I : Ideal A} [Module k I]

private theorem sum_smul_lubinTate_eq (hπ_A : Function.Surjective π_A)
    (hsmul : ∀ (a : A) (y : I), ((π_A a • y : I) : A) = a * y.val)
    {n : ℕ} (b : Fin n → I) (F : FormalGroupLift π_A F₀) (p h : ℕ) [hp : Fact p.Prime]
    (c : Fin n → Fin (h - 1) → k) (m : Fin (h - 1) → I) (hm : ∀ j, m j = ∑ i, c i j • b i) :
    ∑ j : Fin (h - 1),
        (m j : A) • F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) =
      ∑ i, (b i : A) • ∑ j : Fin (h - 1),
        Function.surjInv hπ_A (c i j) •
          F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) := by
  trans ∑ j, ∑ i, (Function.surjInv hπ_A (c i j) * (b i : A)) •
      F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val)
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
  refine ⟨?_, ?_⟩
  · have h := basisComp_congr b (hf₁ := coeff_subst_mem_of_coeff_mem .X_X hΦI) (hf₂ := hΦI)
      hΦ.subst_swap i
    simpa only [basisComp_subst_finTwo hπ_A hsmul b hΦI .X_X i, map_X] using h
  · have hs1 : HasSubst ![(X 0 : MvPowerSeries (Fin 3) A), X 1] := .X_X
    have hs2 : HasSubst ![F.formalGroup.toPowerSeries.subst
        ![(X 0 : MvPowerSeries (Fin 3) A), X 1], X 2] :=
      .cons_subst_zero_left 0 1 2 F.formalGroup.zero_constantCoeff
    have hs3 : HasSubst ![(X 0 : MvPowerSeries (Fin 3) A),
        F.formalGroup.toPowerSeries.subst ![X 1, X 2]] :=
      .cons_subst_zero_right 0 1 2 F.formalGroup.zero_constantCoeff
    have hs4 : HasSubst ![(X 1 : MvPowerSeries (Fin 3) A), X 2] := .X_X
    have hsub {b : Fin 2 → MvPowerSeries (Fin 3) A} (hb : HasSubst b) :=
      coeff_subst_mem_of_coeff_mem hb hΦI
    have hadd {b₁ b₂ : Fin 2 → MvPowerSeries (Fin 3) A} (hb₁ : HasSubst b₁) (hb₂ : HasSubst b₂)
        (d : Fin 3 →₀ ℕ) : coeff d (Φ.subst b₁ + Φ.subst b₂) ∈ I := by
      rw [map_add]; exact I.add_mem (hsub hb₁ d) (hsub hb₂ d)
    have h := basisComp_congr b (hf₁ := hadd hs1 hs2) (hf₂ := hadd hs3 hs4)
      hΦ.subst_add_subst_eq i
    rw [basisComp_add b (hsub hs1) (hsub hs2), basisComp_add b (hsub hs3) (hsub hs4),
      basisComp_subst_finTwo hπ_A hsmul b hΦI hs1 i,
      basisComp_subst_finTwo hπ_A hsmul b hΦI hs2 i,
      basisComp_subst_finTwo hπ_A hsmul b hΦI hs3 i,
      basisComp_subst_finTwo hπ_A hsmul b hΦI hs4 i] at h
    simpa only [map_subst_finTwo π_A hs1, map_subst_finTwo π_A hs4, map_X,
      ← FormalGroup.map_toPowerSeries, F.map_eq] using h

end IdealBasis

private theorem deformationCocycle_deformByLubinTate_sub {F G : FormalGroupLift π_A F₀}
    {q : A →+* B} (hq : π_B.comp q = π_A) (hker : RingHom.ker q * RingHom.ker q = ⊥) (p h : ℕ)
    [hp : Fact p.Prime] (m : Fin (h - 1) → RingHom.ker q)
    (hFG : ∀ d, coeff d (G.formalGroup.toPowerSeries - F.formalGroup.toPowerSeries) ∈
      RingHom.ker q) :
    (F.deformByLubinTate hq hker p h m).formalGroup.deformationCocycle G.formalGroup =
      F.formalGroup.deformationCocycle G.formalGroup -
        ∑ j : Fin (h - 1),
          (m j : A) • F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) := by
  have hFm := coeff_deformByLubinTate_sub_mem F hq hker p h m
  have htrans := FormalGroup.deformationCocycle_trans hker hFm fun d ↦ by
    rw [← sub_sub_sub_cancel_right _ _ F.formalGroup.toPowerSeries, map_sub]
    exact (RingHom.ker q).sub_mem (hFG d) (hFm d)
  rw [FormalGroupLift.deformationCocycle_deformByLubinTate] at htrans
  linear_combination -htrans

variable [F₀.IsComm]

private theorem map_lubinTateCocycle_lift (F : FormalGroupLift π_A F₀) (m : ℕ+) :
    MvPowerSeries.map π_A (F.formalGroup.lubinTateCocycle m) = F₀.lubinTateCocycle m :=
  (FormalGroup.map_lubinTateCocycle π_A F.formalGroup m).trans
    (FormalGroup.lubinTateCocycle_congr F.map_eq m)

private theorem map_sum_smul_lubinTateCocycle (hπ_A : Function.Surjective π_A)
    (F : FormalGroupLift π_A F₀) (p h : ℕ) [hp : Fact p.Prime] (c : Fin (h - 1) → k) :
    MvPowerSeries.map π_A (∑ j : Fin (h - 1),
      Function.surjInv hπ_A (c j) •
        F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val)) =
      ∑ j : Fin (h - 1), c j • F₀.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [smul_eq_C_mul, map_mul, map_C, Function.surjInv_eq hπ_A, map_lubinTateCocycle_lift,
      ← smul_eq_C_mul]

/-- Provides the descended `k`-module structure, scalar compatibility, and a finite `k`-basis on
`RingHom.ker q` when `RingHom.ker π_A * RingHom.ker q = ⊥` and `RingHom.ker q` is finitely
generated. -/
private theorem exists_ker_basis (hπ_A : Function.Surjective π_A) {q : A →+* B}
    (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥) :
    ∃ (_ : Module k (RingHom.ker q)) (n : ℕ) (_ : Module.Basis (Fin n) k (RingHom.ker q)),
      ∀ (a : A) (y : RingHom.ker q), ((π_A a • y : RingHom.ker q) : A) = a * y.val := by
  have htor := Ideal.isTorsionBySet_of_mul_eq_bot hker
  let _ := htor.moduleOfSurjective hπ_A
  have : Module.Finite A (RingHom.ker q) := Module.Finite.iff_fg.mpr hFG
  have : Module.Finite k (RingHom.ker q) := (htor.finite_iff_of_surjective hπ_A).mp inferInstance
  exact ⟨inferInstance, _, Module.finBasis k (RingHom.ker q),
    fun a y ↦ congrArg Subtype.val (htor.moduleOfSurjective_smul hπ_A a y)⟩

private theorem ker_mul_ker_eq_bot {q : A →+* B} (hq : π_B.comp q = π_A)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) :
    RingHom.ker q * RingHom.ker q = ⊥ :=
  Ideal.mul_self_eq_bot_of_le_of_mul_eq_bot (RingHom.ker_le_ker_of_comp_eq hq) hker

private theorem eq_zero_of_sum_lubinTateCocycle_eq_homDefect (hπ_A : Function.Surjective π_A)
    {q : A →+* B} (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥)
    {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h)
    (F : FormalGroupLift π_A F₀) {m : Fin (h - 1) → RingHom.ker q} {g : PowerSeries A}
    (hgI : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker q)
    (hsum : ∑ j : Fin (h - 1),
        (m j : A) • F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) =
      F.formalGroup.homDefect 𝔾ₐ g) : m = 0 := by
  obtain ⟨inst, _, b, hsmul⟩ := exists_ker_basis hπ_A hFG hker
  let _ := inst
  have hgI' := PowerSeries.mvCoeff_mem_of_coeff_mem hgI
  let gA (i : Fin _) : PowerSeries A := liftOfSurjective hπ_A (basisComp b hgI' i)
  have heq : ∑ i, (b i : A) • ∑ j : Fin (h - 1),
        Function.surjInv hπ_A (b.repr (m j) i) •
          F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) =
      ∑ i, (b i : A) • F.formalGroup.homDefect 𝔾ₐ (gA i) := by
    rw [← sum_smul_lubinTate_eq hπ_A hsmul b F p h _ m fun j ↦ (b.sum_repr (m j)).symm, hsum,
      ← FormalGroup.homDefect_𝔾ₐ_sum_smul, ← eq_sum_smul_liftOfSurjective hπ_A hsmul b hgI']
  have hc0 (i : Fin _) : (fun j : Fin (h - 1) ↦ b.repr (m j) i) = 0 := by
    have hmap := map_eq_of_sum_smul_eq hsmul b heq i
    rw [map_sum_smul_lubinTateCocycle, FormalGroup.map_homDefect_𝔾ₐ, F.map_eq] at hmap
    exact (F₀.sum_smul_lubinTateCocycle_eq_homDefect_𝔾ₐ_iff hp.out
      (F₀.height_eq_natCast_iff.mp hF₀).ge).mp ⟨PowerSeries.map π_A (gA i), hmap⟩
  funext j
  exact b.repr.injective (Finsupp.ext fun i ↦ by
    rw [Pi.zero_apply, map_zero, Finsupp.zero_apply]; exact congrFun (hc0 i) j)

private theorem deformByLubinTate_injective [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    (hπ_B : Function.Surjective π_B) {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀) :
    Function.Injective
      (deformByLubinTate F hq (ker_mul_ker_eq_bot hq hker) p h) := by
  set hker_sq := ker_mul_ker_eq_bot hq hker
  have hπ_A : Function.Surjective π_A := hq ▸ hπ_B.comp hq_surj
  intro m₁ m₂ hm
  obtain ⟨φ, hφ_π, hφ_eq⟩ := (mk_eq_mk_iff _ _).mp hm
  have hψ1 : FormalCoordinate.map q φ = 1 :=
    FormalCoordinate.eq_one_of_smul_eq_of_map_eq_one hπ_B
      (by rw [(F.map q hq).map_eq, hF₀])
      (by rw [← FormalCoordinate.map_comp, hq, hφ_π]) (by
        have h1 := congrArg (FormalGroup.map · q) hφ_eq
        rwa [FormalGroup.map_smul, ← FormalGroupLift.formalGroup_map _ q hq,
          ← FormalGroupLift.formalGroup_map _ q hq,
          FormalGroupLift.map_deformByLubinTate, FormalGroupLift.map_deformByLubinTate] at h1)
  have hφI := (FormalCoordinate.map_eq_one_iff q φ).mp hψ1
  set G₁ := F.deformByLubinTate hq hker_sq p h m₁
  set G₂ := F.deformByLubinTate hq hker_sq p h m₂
  obtain ⟨g, -, hgI, hcoc⟩ :=
    (G₁.formalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
      G₂.formalGroup hker_sq).mp ⟨φ, hφI, hφ_eq⟩
  rw [FormalGroup.homDefect_𝔾ₐ_eq_of_coeff_mem hker_sq
        (coeff_deformByLubinTate_sub_mem F hq hker_sq p h m₁) hgI,
      deformationCocycle_deformByLubinTate_sub hq hker_sq p h m₁
        (coeff_deformByLubinTate_sub_mem F hq hker_sq p h m₂),
      FormalGroupLift.deformationCocycle_deformByLubinTate] at hcoc
  have hdiff : ∑ j : Fin (h - 1), ((m₂ j - m₁ j : RingHom.ker q) : A) •
      F.formalGroup.lubinTateCocycle (lubinTateIndex ‹Fact p.Prime›.out.one_lt j.val) =
      F.formalGroup.homDefect 𝔾ₐ g := by
    simpa [AddSubgroupClass.coe_sub, sub_smul, Finset.sum_sub_distrib] using hcoc
  exact (sub_eq_zero.mp (eq_zero_of_sum_lubinTateCocycle_eq_homDefect hπ_A hFG hker hF₀ F
    hgI hdiff)).symm

/-- Decomposes the `i`-th `k`-basis component of an `I`-valued symmetric 2-cocycle `Φ` over `k`
into a linear combination of Lubin–Tate cocycles and a coboundary. -/
private theorem exists_lubinTate_decomp_basisComp (hπ_A : Function.Surjective π_A)
    {I : Ideal A} [Module k I]
    (hsmul : ∀ (a : A) (y : I), ((π_A a • y : I) : A) = a * y.val)
    {n : ℕ} (b : Module.Basis (Fin n) k I) {p h : ℕ} [hp : Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ_coc : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ I) (i : Fin n) :
    ∃ (c : Fin (h - 1) → k) (gk : PowerSeries k),
      PowerSeries.constantCoeff gk = 0 ∧
        basisComp b hΦI i =
          ∑ j : Fin (h - 1), c j • F₀.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) +
          F₀.homDefect 𝔾ₐ gk := by
  have h0 : constantCoeff (basisComp b hΦI i) = 0 := by
    have hΦ0' : (⟨coeff 0 Φ, hΦI 0⟩ : I) = 0 :=
      Subtype.ext (by simp [coeff_zero_eq_constantCoeff_apply, hΦ₀])
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_basisComp, hΦ0', map_zero]
  obtain ⟨c, ⟨gk, hgk₀, hgk⟩, -⟩ :=
    (isSymmetricCocycle_basisComp hπ_A hsmul b F hΦ_coc hΦI
      i).existsUnique_sum_smul_lubinTateCocycle_add_homDefect_𝔾ₐ hp.out
      (CharP.cast_eq_zero k p) (F₀.height_eq_natCast_iff.mp hF₀).ge
      (F₀.coeff_nsmulSeries_ne_zero_of_height_eq hF₀).isUnit h0
  exact ⟨c, gk, hgk₀, hgk⟩

private theorem exists_lubinTate_decomp_of_coeff_mem (hπ_A : Function.Surjective π_A)
    {q : A →+* B} (hFG : (RingHom.ker q).FG) (hker : RingHom.ker π_A * RingHom.ker q = ⊥)
    {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (hF₀ : F₀.height p = h)
    (F : FormalGroupLift π_A F₀) {Φ : MvPowerSeries (Fin 2) A}
    (hΦ_coc : F.formalGroup.IsSymmetricCocycle Φ) (hΦ₀ : constantCoeff Φ = 0)
    (hΦI : ∀ d, coeff d Φ ∈ RingHom.ker q) :
    ∃ (m : Fin (h - 1) → RingHom.ker q) (g : PowerSeries A),
      PowerSeries.constantCoeff g = 0 ∧ (∀ n, PowerSeries.coeff n g ∈ RingHom.ker q) ∧
      Φ = ∑ j : Fin (h - 1),
          (m j : A) • F.formalGroup.lubinTateCocycle (lubinTateIndex hp.out.one_lt j.val) +
        F.formalGroup.homDefect 𝔾ₐ g := by
  -- 1. Equip `RingHom.ker q` with a finite `k`-basis `b`.
  obtain ⟨inst, _, b, hsmul⟩ := exists_ker_basis hπ_A hFG hker
  let _ := inst
  -- 2. Decompose each basis component over `k` and lift the coboundary series to `A`.
  choose ck gk hgk₀ hΦk_eq using fun i ↦
    exists_lubinTate_decomp_basisComp hπ_A hsmul b hF₀ F hΦ_coc hΦ₀ hΦI i
  let gA (i : Fin _) : PowerSeries A :=
    liftOfSurjective hπ_A (gk i) -
      PowerSeries.C (PowerSeries.constantCoeff (liftOfSurjective hπ_A (gk i)))
  -- 3. Reassemble the `RingHom.ker q`-valued combination and verify it componentwise along `b`.
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
  have hgA : PowerSeries.map π_A (gA i) = gk i := by
    dsimp only [gA]
    rw [map_sub, PowerSeries.map_C, ← PowerSeries.constantCoeff_map,
      PowerSeries.map_liftOfSurjective, hgk₀ i, map_zero, sub_zero]
  rw [map_liftOfSurjective, map_add, map_sum_smul_lubinTateCocycle, FormalGroup.map_homDefect_𝔾ₐ,
    F.map_eq, hgA, hΦk_eq]

private theorem deformByLubinTate_surjective {q : A →+* B} (hπ_B : Function.Surjective π_B)
    (hq : π_B.comp q = π_A) (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀) :
    Function.Surjective (fun m : Fin (h - 1) → RingHom.ker q ↦
      (⟨deformByLubinTate F hq (ker_mul_ker_eq_bot hq hker) p h m,
        map_deformByLubinTate F hq _ p h m⟩ :
        {x : FormalGroupDeformation π_A F₀ //
          FormalGroupDeformation.map q hq x = ⟦F.map q hq⟧})) := by
  have hle : RingHom.ker q ≤ RingHom.ker π_A := RingHom.ker_le_ker_of_comp_eq hq
  set hker_sq := ker_mul_ker_eq_bot hq hker
  have hπ_A : Function.Surjective π_A := hq ▸ hπ_B.comp hq_surj
  have : IsLocalHom q := q.isLocalHom_of_surjective_of_isNilpotent_ker hq_surj fun y hy ↦
    ⟨2, by rw [pow_two, ← Ideal.mem_bot, ← hker_sq]; exact Ideal.mul_mem_mul hy hy⟩
  rintro ⟨x, hx⟩
  induction x using Quotient.inductionOn with | _ G₀ =>
  -- Normalize the representative `G₀` so that `G.map q hq = F.map q hq`, then decompose
  -- `F.deformationCocycle G` into Lubin–Tate cocycles plus a coboundary `homDefect 𝔾ₐ g`.
  obtain ⟨G, hG_eq, hGq⟩ :=
    exists_mk_eq_and_map_eq hq (FormalCoordinate.map_surjective_of_isLocalHom q hq_surj) hx
  have hFG_mem := FormalGroupLift.coeff_sub_mem_ker_of_map_eq hGq
  obtain ⟨m, g, hg₀, hgI, hΦ_decomp⟩ :=
    exists_lubinTate_decomp_of_coeff_mem hπ_A hFG hker hF₀ F
      (F.formalGroup.isSymmetricCocycle_deformationCocycle G.formalGroup hker_sq hFG_mem)
      (F.formalGroup.constantCoeff_deformationCocycle G.formalGroup)
      (FormalGroup.coeff_deformationCocycle_mem_iff.mpr hFG_mem)
  set Fm := F.deformByLubinTate hq hker_sq p h m
  have hFmG_coc : Fm.formalGroup.deformationCocycle G.formalGroup =
      Fm.formalGroup.homDefect 𝔾ₐ g := by
    rw [FormalGroup.homDefect_𝔾ₐ_eq_of_coeff_mem hker_sq
          (coeff_deformByLubinTate_sub_mem F hq hker_sq p h m) hgI,
        deformationCocycle_deformByLubinTate_sub hq hker_sq p h m hFG_mem, hΦ_decomp,
        add_sub_cancel_left]
  obtain ⟨φ, hφI, hφ_smul⟩ :=
    (Fm.formalGroup.exists_smul_eq_iff_exists_deformationCocycle_eq_homDefect_𝔾ₐ
      G.formalGroup hker_sq).mpr ⟨g, hg₀, hgI, hFmG_coc⟩
  have hφ_π : FormalCoordinate.map π_A φ = 1 :=
    (FormalCoordinate.map_eq_one_iff π_A φ).mpr fun n ↦ hle (hφI n)
  exact ⟨m, Subtype.ext (((mk_eq_mk_iff Fm G).mpr ⟨φ, hφ_π, hφ_smul⟩).trans hG_eq)⟩

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
        FormalGroupDeformation.map q hq x = ⟦F.map q hq⟧} :=
  Equiv.ofBijective
    (fun m ↦ ⟨deformByLubinTate F hq (ker_mul_ker_eq_bot hq hker) p h m,
      map_deformByLubinTate F hq _ p h m⟩)
    ⟨fun _ _ hm ↦ deformByLubinTate_injective hπ_B hq hq_surj hFG hker hF₀ F
      (congrArg Subtype.val hm),
    deformByLubinTate_surjective hπ_B hq hq_surj hFG hker hF₀ F⟩

/-- `squareZeroFiberEquiv` acts by `deformByLubinTate`. -/
@[simp]
theorem squareZeroFiberEquiv_apply_coe [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    (hπ_B : Function.Surjective π_B) {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) (hFG : (RingHom.ker q).FG)
    (hker : RingHom.ker π_A * RingHom.ker q = ⊥) {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (F : FormalGroupLift π_A F₀)
    (m : Fin (h - 1) → RingHom.ker q) :
    (squareZeroFiberEquiv hπ_B hq hq_surj hFG hker hF₀ F m).val =
      deformByLubinTate F hq
        (Ideal.mul_self_eq_bot_of_le_of_mul_eq_bot (RingHom.ker_le_ker_of_comp_eq hq) hker)
        p h m := by
  rw [squareZeroFiberEquiv]
  exact congrArg Subtype.val (congrFun (Equiv.coe_ofBijective _ _) m)

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

private theorem mem_kerIdeal_iff_mem_ker_fstHom (k : Type*) [CommRing k] (x : TrivSqZeroExt k k) :
    x ∈ TrivSqZeroExt.kerIdeal k k ↔ x ∈ RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom :=
  Iff.rfl

private theorem fg_ker_fstHom (k : Type*) [CommRing k] :
    (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom).FG :=
  TrivSqZeroExt.fg_kerIdeal

private noncomputable def piKerFstEquiv (k : Type*) [CommRing k] (n : ℕ) :
    (Fin n → k) ≃ (Fin n → RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) :=
  Equiv.piCongrRight fun _ ↦
    (TrivSqZeroExt.kerIdealLinearEquiv k k).toEquiv.trans
      (Equiv.subtypeEquivRight (mem_kerIdeal_iff_mem_ker_fstHom k))

private theorem piKerFstEquiv_apply (k : Type*) [CommRing k] {n : ℕ} (c : Fin n → k) :
    piKerFstEquiv k n c = fun j ↦ ⟨TrivSqZeroExt.inr (c j), by simp [RingHom.mem_ker]⟩ := by
  funext j
  exact Subtype.ext <| by
    rw [piKerFstEquiv, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.trans_apply,
      Equiv.subtypeEquivRight_apply, LinearEquiv.coe_toEquiv, TrivSqZeroExt.coe_kerIdealLinearEquiv]

private theorem fstHom_surjective (k : Type*) [CommRing k] :
    Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
  TrivSqZeroExt.fst_surjective

private noncomputable def dualNumberTrivialLift (F₀ : FormalGroup k) [F₀.IsComm] :
    FormalGroupLift (TrivSqZeroExt.fstHom k k k).toRingHom F₀ :=
  FormalGroupLift.ofSection F₀ (TrivSqZeroExt.fstHom k k k).toRingHom
    (algebraMap k (DualNumber k)) (RingHom.ext fun _ ↦ by simp)

/-- **The Lubin–Tate tangent space.** For a commutative formal group law `F₀` of finite height `h`
over a field `k` of characteristic `p`, the set of deformations of `F₀` over the dual numbers
`DualNumber k = k[ε]` (`ε² = 0`) is canonically equivalent to `Fin (h - 1) → k`. -/
noncomputable def dualNumberEquiv {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) :
    (Fin (h - 1) → k) ≃
      FormalGroupDeformation (TrivSqZeroExt.fstHom k k k).toRingHom F₀ :=
  (piKerFstEquiv k (h - 1)).trans <|
    (squareZeroFiberEquiv (B := k) (π_B := RingHom.id k) Function.surjective_id
      (RingHom.id_comp _) (fstHom_surjective k) (fg_ker_fstHom k)
      ((pow_two _).symm.trans (TrivSqZeroExt.kerIdeal_sq k k))
      hF₀ (dualNumberTrivialLift F₀)).trans
      (Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ _)

/-- Evaluating `dualNumberEquiv` deforms the trivial lift along `ε • cⱼ`. -/
theorem dualNumberEquiv_apply {p h : ℕ} [Fact p.Prime] [CharP k p]
    (hF₀ : F₀.height p = h) (c : Fin (h - 1) → k) :
    dualNumberEquiv hF₀ c =
      deformByLubinTate
        (FormalGroupLift.ofSection F₀ (TrivSqZeroExt.fstHom k k k).toRingHom
          (algebraMap k (DualNumber k)) (RingHom.ext fun x ↦ by simp))
        (RingHom.id_comp _) ((pow_two _).symm.trans (TrivSqZeroExt.kerIdeal_sq k k))
        p h (fun j ↦ ⟨TrivSqZeroExt.inr (c j), by simp [RingHom.mem_ker]⟩) := by
  rw [dualNumberEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply,
    squareZeroFiberEquiv_apply_coe, piKerFstEquiv_apply, dualNumberTrivialLift]

end SquareZeroFiber

end FormalGroupDeformation

end TauCeti
