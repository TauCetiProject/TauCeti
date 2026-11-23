/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Span
import TauCeti.Algebra.Category.GradedModuleCat.Retract.PID
import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Range

/-!
# Homogeneous splittings and bases of degree-zero idempotents over a PID

Let `A` be a connected nonnegatively `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`) over a
principal ideal domain `k`, and view the finite function module `I → A` (`[Finite I]`) as the
shifted free graded `A`-module with `j`th summand in shift `s j : ℤ`.

By translating a degree-zero idempotent `p : (I → A) →ₗ[A] (I → A)` into a graded retract of
`GradedModuleCat.free 𝒜 s` via `TauCeti.GradedModuleCat.retractRangeOfPiIdempotent` and applying
`TauCeti.GradedModuleCat.exists_iso_free_of_retract` and
`TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`, this file proves:

* `TauCeti.exists_homogeneous_splitting_of_idempotent_of_connected`: `p` splits homogeneously
  through some `Fin n → A` with shifts `d : Fin n → ℤ` via maps `ι` and `π` satisfying
  `π ∘ₗ ι = id` and `ι ∘ₗ π = p`.
* `TauCeti.exists_homogeneous_basis_range_idempotent_of_connected`: `LinearMap.range p` admits a
  finite homogeneous `A`-basis `b : Module.Basis (Fin n) A (LinearMap.range p)` with
  `(b i).val j ∈ 𝒜 (d i - s j)`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Chapter II, §4.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti

universe uk uA uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- **Homogeneous splitting of a degree-zero idempotent on a finite shifted free module `I → A`.**
Over a connected nonnegatively graded algebra `A` over a PID `k`, any degree-zero idempotent
`p : (I → A) →ₗ[A] (I → A)` (`[Finite I]`) splits homogeneously through a finite shifted free
module `Fin n → A` via maps `ι` and `π` satisfying `π ∘ₗ ι = id` and `ι ∘ₗ π = p`. -/
theorem exists_homogeneous_splitting_of_idempotent_of_connected
    [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A),
      (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → A) →ₗ[A] (I → A))
      (π : (I → A) →ₗ[A] (Fin n → A)),
      π.comp ι = LinearMap.id ∧
      ι.comp π = p ∧
      (∀ (q : ℤ) (u : Fin n → A), (∀ i, u i ∈ 𝒜 (q - d i)) → ∀ j, ι u j ∈ 𝒜 (q - s j)) ∧
      (∀ (q : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ i, π v i ∈ 𝒜 (q - d i)) := by
  cases nonempty_fintype I
  let eF : GradedModuleCat.free 𝒜 s ≃ₗ[A] (I → A) :=
    DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let rR := GradedModuleCat.retractRangeOfPiIdempotent s p hp hhom
  obtain ⟨n, d, ⟨Φ⟩⟩ := GradedModuleCat.exists_iso_free_of_retract hneg hzero rR
  let eD : GradedModuleCat.free 𝒜 (d ∘ ULift.down) ≃ₗ[A] (Fin n → A) :=
    (DirectSum.linearEquivFunOnFintype A (ULift.{uI} (Fin n)) (fun _ ↦ A)).trans
      (LinearEquiv.piCongrLeft A (fun _ ↦ A) Equiv.ulift)
  have heD_symm : ∀ (q : ℤ) (u : Fin n → A),
      eD.symm u ∈ (GradedModuleCat.free 𝒜 (d ∘ ULift.down)).grading.piece q ↔
        ∀ i, u i ∈ 𝒜 (q - d i) := fun q u ↦ by
    dsimp only [eD]
    rw [LinearEquiv.symm_trans_apply,
      GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff]
    exact ⟨fun h i ↦ h (ULift.up i), fun h j ↦ h j.down⟩
  let rD := (Retract.ofIso Φ).trans rR
  let ι : (Fin n → A) →ₗ[A] (I → A) :=
    eF.toLinearMap ∘ₗ rD.i.hom ∘ₗ eD.symm.toLinearMap
  let π : (I → A) →ₗ[A] (Fin n → A) :=
    eD.toLinearMap ∘ₗ rD.r.hom ∘ₗ eF.symm.toLinearMap
  refine ⟨n, d, ι, π, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun u ↦ ?_
    have hret : rD.r.hom (rD.i.hom (eD.symm u)) = eD.symm u :=
      LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom rD.retract) _
    simp [ι, π, hret]
  · have hri : rD.r ≫ rD.i = GradedModuleCat.freeEndOfPiEnd s p hhom := by
      calc rD.r ≫ rD.i = (rR.r ≫ Φ.inv) ≫ (Φ.hom ≫ rR.i) := rfl
        _ = rR.r ≫ (Φ.inv ≫ Φ.hom) ≫ rR.i := by simp only [Category.assoc]
        _ = rR.r ≫ rR.i := by rw [Φ.inv_hom_id, Category.id_comp]
        _ = GradedModuleCat.freeEndOfPiEnd s p hhom :=
          GradedModuleCat.retractRangeOfPiIdempotent_r_comp_i s p hp hhom
    refine LinearMap.ext fun v ↦ ?_
    have hv : rD.i.hom (rD.r.hom (eF.symm v)) =
        (GradedModuleCat.freeEndOfPiEnd s p hhom).hom (eF.symm v) :=
      LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom hri) (eF.symm v)
    simp only [ι, π, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    rw [hv]
    dsimp only [eF]
    rw [GradedModuleCat.hom_freeEndOfPiEnd_apply, LinearEquiv.apply_symm_apply]
  · exact fun q u hu ↦ (GradedModuleCat.mem_free_piece_iff 𝒜 s q _).mp
      (GradedModuleCat.map_mem rD.i ((heD_symm q u).mpr hu))
  · exact fun q v hv ↦ (heD_symm q (π v)).mp <| by
      simpa [π] using GradedModuleCat.map_mem rD.r
        ((GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s q v).mpr hv)

/-- **Homogeneous basis of the image of a degree-zero idempotent on `I → A`.**
Over a connected nonnegatively graded algebra `A` over a PID `k`, the range of any degree-zero
idempotent `p : (I → A) →ₗ[A] (I → A)` (`[Finite I]`, shifts `s : I → ℤ`) admits a finite
`A`-basis `b : Module.Basis (Fin n) A (LinearMap.range p)` whose `i`th vector has `j`th coordinate
in `𝒜 (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent_of_connected
    [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A),
      (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ 𝒜 (d i - s j) := by
  cases nonempty_fintype I
  obtain ⟨n, b, d, hb⟩ :=
    GradedModuleCat.exists_homogeneous_basis_of_retract hneg hzero
      (GradedModuleCat.retractRangeOfPiIdempotent s p hp hhom)
  let equivRange := GradedModuleCat.rangeEquivRangeObj s p hhom
  refine ⟨n, b.map equivRange.symm, d, fun i ↦ ?_⟩
  have hval : (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm
      (b.map equivRange.symm i).val = (b i).val := by
    rw [Module.Basis.map_apply,
      ← GradedModuleCat.coe_rangeEquivRangeObj_apply s p hhom (equivRange.symm (b i)),
      equivRange.apply_symm_apply]
  exact (GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s (d i) _).mp
    (hval ▸ (GradedModuleCat.mem_rangeObjOfPiEnd_piece_iff s p hhom).mp (hb i))

end TauCeti
