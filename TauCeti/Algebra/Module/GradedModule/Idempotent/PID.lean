/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Idempotent.Basic
import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.Category.GradedModuleCat.Retract.PID

/-!
# Homogeneous splittings and bases of degree-zero idempotents over a PID

Let `A` be a connected nonnegatively `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`) over a
principal ideal domain `k`, and view the finite function module `I → A` (`[Finite I]`) as the
shifted free graded `A`-module with `j`th summand in shift `s j : ℤ`.

By translating a degree-zero idempotent `p : (I → A) →ₗ[A] (I → A)` into a graded retract of
`GradedModuleCat.free 𝒜 s` and applying `TauCeti.GradedModuleCat.exists_iso_free_of_retract`, this
file proves:

* `TauCeti.exists_homogeneous_splitting_of_idempotent_of_connected`: `p` splits homogeneously
  through some `Fin n → A` with shifts `d : Fin n → ℤ` via maps `ι` and `π` satisfying
  `π ∘ₗ ι = id` and `ι ∘ₗ π = p`.
* `TauCeti.exists_homogeneous_basis_range_idempotent_of_connected`: `LinearMap.range p` admits a
  finite homogeneous `A`-basis `b : Module.Basis (Fin n) A (LinearMap.range p)` with
  `(b i).val j ∈ 𝒜 (d i - s j)`.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), 573–651, Lemma 3.30.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti

universe uk uA uI

section ConnectedPID

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- A degree-zero idempotent `p` on `I → A` exhibits `rangeObjOfPiEnd s p hhom` as a graded retract
of `GradedModuleCat.free 𝒜 s`. -/
private noncomputable def retractRangeOfPiIdempotent {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    Retract (rangeObjOfPiEnd s p hhom) (GradedModuleCat.free 𝒜 s) :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  have hp' : IsIdempotentElem p'.hom :=
    IsIdempotentElem.map (show IsIdempotentElem (p : Module.End A (I → A)) from hp)
      eF.symm.conjRingEquiv
  { i := GradedModuleCat.ofHom (LinearMap.range p'.hom).subtype
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (InternalGrading.mem_submodule_piece _ _ _).mp hx)
    r := GradedModuleCat.ofHom p'.hom.rangeRestrict
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (InternalGrading.mem_submodule_piece _ _ _).mpr (GradedModuleCat.map_mem p' hx))
    retract := GradedModuleCat.hom_ext <| LinearMap.ext fun z ↦
      Subtype.ext ((LinearMap.IsIdempotentElem.mem_range_iff hp').mp z.property) }

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
  let rR := retractRangeOfPiIdempotent s p hp hhom
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
  let ι : (Fin n → A) →ₗ[A] (I → A) :=
    eF.toLinearMap ∘ₗ rR.i.hom ∘ₗ Φ.hom.hom ∘ₗ eD.symm.toLinearMap
  let π : (I → A) →ₗ[A] (Fin n → A) :=
    eD.toLinearMap ∘ₗ Φ.inv.hom ∘ₗ rR.r.hom ∘ₗ eF.symm.toLinearMap
  refine ⟨n, d, ι, π, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun u ↦ ?_
    have h1 : rR.r.hom (rR.i.hom (Φ.hom.hom (eD.symm u))) = Φ.hom.hom (eD.symm u) :=
      LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom rR.retract) _
    have h2 : Φ.inv.hom (Φ.hom.hom (eD.symm u)) = eD.symm u :=
      LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom Φ.hom_inv_id) _
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_coe, eF.symm_apply_apply, h1, h2,
      eD.apply_symm_apply, LinearMap.id_apply]
  · refine LinearMap.ext fun v ↦ ?_
    have h1 : Φ.hom.hom (Φ.inv.hom (rR.r.hom (eF.symm v))) = rR.r.hom (eF.symm v) :=
      LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom Φ.inv_hom_id) _
    have h2 : rR.i.hom (rR.r.hom (eF.symm v)) = (freeEndOfPiEnd s p hhom).hom (eF.symm v) :=
      LinearMap.congr_fun (LinearMap.subtype_comp_rangeRestrict _) _
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_coe, eD.symm_apply_apply, h1, h2]
    dsimp [freeEndOfPiEnd, GradedModuleCat.ofHom]
    simp [eF]
  · exact fun q u hu ↦ (GradedModuleCat.mem_free_piece_iff 𝒜 s q _).mp
      (GradedModuleCat.map_mem rR.i (GradedModuleCat.map_mem Φ.hom ((heD_symm q u).mpr hu)))
  · exact fun q v hv ↦ (heD_symm q (π v)).mp <| by
      simpa [π] using GradedModuleCat.map_mem Φ.inv
        (GradedModuleCat.map_mem rR.r
          ((GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s q v).mpr hv))

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
  classical
  obtain ⟨n, d, ι, π, hπι, hιπ, hι_hom, -⟩ :=
    exists_homogeneous_splitting_of_idempotent_of_connected hneg hzero s p hp hhom
  have hrange : LinearMap.range ι = LinearMap.range p := by
    rw [← hιπ, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (Function.LeftInverse.surjective (f := π) (g := ι)
        (LinearMap.congr_fun hπι)))]
  let equivRange : (Fin n → A) ≃ₗ[A] LinearMap.range p :=
    (LinearEquiv.ofLeftInverse (LinearMap.congr_fun hπι)).trans (LinearEquiv.ofEq _ _ hrange)
  let b : Module.Basis (Fin n) A (LinearMap.range p) :=
    (Pi.basisFun A (Fin n)).map equivRange
  refine ⟨n, b, d, fun i j ↦ ?_⟩
  have hb_eq : (b i).val = ι (Pi.single i 1) := by
    simp only [b, equivRange, Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  rw [hb_eq]
  refine hι_hom (d i) (Pi.single i 1) (fun t ↦ ?_) j
  by_cases hti : t = i
  · subst hti
    simpa using SetLike.GradedOne.one_mem (A := 𝒜)
  · simp [Pi.single_eq_of_ne hti]

end ConnectedPID

end TauCeti
