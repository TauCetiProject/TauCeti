/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Span
import TauCeti.Algebra.Category.GradedModuleCat.Retract

/-!
# Homogeneous splittings and bases of degree-zero idempotents on shifted free modules

Let `A` be a connected nonnegatively `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`), and view the
finite function module `I → A` (`[Finite I]`) as the shifted free graded `A`-module with `j`th
summand in shift `s j : ℤ`, so its homogeneous elements of degree `d` are the tuples `v : I → A`
satisfying `∀ j, v j ∈ 𝒜 (d - s j)`.

Transporting `I → A` to `GradedModuleCat.free 𝒜 s` via `DirectSum.linearEquivFunOnFintype` deduces
concrete module-level consequences from `TauCeti.Algebra.Category.GradedModuleCat.Retract`:

1. Over a principal ideal domain `k`, every degree-zero idempotent `p : (I → A) →ₗ[A] (I → A)`
   splits homogeneously through some `Fin n → A` with shifts `d : Fin n → ℤ` via linear maps `ι`
   and `π` satisfying `π ∘ₗ ι = id` and `ι ∘ₗ π = p`
   (`TauCeti.exists_homogeneous_splitting_of_idempotent_of_connected`), and `LinearMap.range p`
   admits a finite homogeneous `A`-basis
   (`TauCeti.exists_homogeneous_basis_range_idempotent_of_connected`).
2. Over any nontrivial commutative base ring `k`, the multiset of degrees `d` of a finite
   homogeneous `A`-basis of `LinearMap.range p` is uniquely determined
   (`TauCeti.multiset_map_eq_of_homogeneous_basis_range_idempotent`).
3. In particular, the zero idempotent has only the empty basis, and any rank-one homogeneous
   projection `p v = v i₀ • w` (`w i₀ = 1`, `∀ j, w j ∈ 𝒜 (s i₀ - s j)`) has unique basis degree
   multiset `{s i₀}`.

## Main results

* `TauCeti.exists_homogeneous_splitting_of_idempotent_of_connected`: homogeneous splitting
  `π ∘ₗ ι = id`, `ι ∘ₗ π = p` of a degree-zero idempotent on `I → A` over a PID.
* `TauCeti.exists_homogeneous_basis_range_idempotent_of_connected`: finite homogeneous `A`-basis of
  `LinearMap.range p` over a PID.
* `TauCeti.multiset_map_eq_of_homogeneous_basis_range_idempotent`: uniqueness of the multiset of
  basis shifts of `LinearMap.range p`.
* `TauCeti.eq_zero_of_basis_range_zero`,
  `TauCeti.multiset_map_eq_singleton_of_homogeneous_basis_range`:
  rank and degree-multiset formulas for the zero idempotent and rank-one homogeneous projections.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), 573–651, Lemma 3.30.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti

universe uk uA uI

section ConnectedRing

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Transporting `free 𝒜 s` (`[Fintype I]`) along `DirectSum.linearEquivFunOnFintype` identifies
its homogeneous pieces with functions `v : I → A` satisfying `∀ j, v j ∈ 𝒜 (q - s j)`. -/
private theorem mem_free_piece_symm_iff {I : Type uI} [Fintype I] (s : I → ℤ) (q : ℤ)
    (v : I → A) :
    (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v ∈
      (GradedModuleCat.free 𝒜 s).grading.piece q ↔ ∀ j, v j ∈ 𝒜 (q - s j) := by
  rw [GradedModuleCat.mem_free_piece_iff]
  refine forall_congr' fun j ↦ ?_
  rw [← DirectSum.linearEquivFunOnFintype_apply A, LinearEquiv.apply_symm_apply]

omit [GradedAlgebra 𝒜] in
/-- Transporting a degree-zero endomorphism of `I → A` to `GradedModuleCat.free 𝒜 s`. -/
private noncomputable def freeEndOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    GradedModuleCat.free 𝒜 s ⟶ GradedModuleCat.free 𝒜 s :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  GradedModuleCat.ofHom (eF.symm.toLinearMap ∘ₗ p ∘ₗ eF.toLinearMap) <|
    LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
      rw [add_zero]
      exact (mem_free_piece_symm_iff s q _).mpr
        (hhom q (eF x) ((GradedModuleCat.mem_free_piece_iff 𝒜 s q x).mp hx))

/-- The graded range object in `GradedModuleCat 𝒜` of a degree-zero endomorphism of `I → A`. -/
private noncomputable def rangeObjOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    GradedModuleCat.{max uA uI} 𝒜 :=
  let _ := (GradedModuleCat.free 𝒜 s).gradedSMul
  let p' := freeEndOfPiEnd s p hhom
  { carrier := LinearMap.range p'.hom
    isAddCommGroup := Submodule.addCommGroup _
    isModule := Submodule.module _
    isModuleBase := Submodule.module' _
    grading := (GradedModuleCat.free 𝒜 s).grading.submodule (LinearMap.range p'.hom)
      p'.isHomogeneous.isHomogeneous_range
    gradedSMul := ⟨fun {_ _} _ _ ha hx ↦ by
      rw [InternalGrading.mem_submodule_piece] at hx ⊢
      exact SetLike.GradedSMul.smul_mem (B := (GradedModuleCat.free 𝒜 s).grading.piece) ha hx⟩ }

/-- `A`-linear identification `LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom`. -/
private noncomputable def rangeEquivRangeObj {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  LinearEquiv.ofLinearMap
    (LinearMap.codRestrict (LinearMap.range p'.hom)
      (eF.symm.toLinearMap.comp (LinearMap.range p).subtype) fun y ↦ by
        obtain ⟨v, hv⟩ := y.2
        refine ⟨eF.symm v, ?_⟩
        dsimp [p', freeEndOfPiEnd, eF]
        rw [LinearEquiv.apply_symm_apply, hv])
    (LinearMap.codRestrict (LinearMap.range p)
      (eF.toLinearMap.comp (LinearMap.range p'.hom).subtype) fun z ↦ by
        obtain ⟨x, hx⟩ := z.2
        have h := congrArg eF hx
        dsimp [p', freeEndOfPiEnd] at h
        exact ⟨eF x, by rwa [eF.apply_symm_apply] at h⟩)
    (LinearMap.ext fun z ↦ Subtype.ext (eF.symm_apply_apply z.1))
    (LinearMap.ext fun y ↦ Subtype.ext (eF.apply_symm_apply y.1))

/-- A degree-zero idempotent `p` on `I → A` exhibits `rangeObjOfPiEnd s p hhom` as a graded retract
of `GradedModuleCat.free 𝒜 s`. -/
private noncomputable def retractRangeOfPiIdempotent {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    Retract (rangeObjOfPiEnd s p hhom) (GradedModuleCat.free 𝒜 s) :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  have hp' : ∀ x, p'.hom (p'.hom x) = p'.hom x := fun x ↦ by
    dsimp [p', freeEndOfPiEnd, GradedModuleCat.ofHom]
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg eF.symm (LinearMap.congr_fun hp (eF x))
  { i := GradedModuleCat.ofHom (LinearMap.range p'.hom).subtype
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (InternalGrading.mem_submodule_piece _ _ _).mp hx)
    r := GradedModuleCat.ofHom (LinearMap.codRestrict (LinearMap.range p'.hom) p'.hom
        (LinearMap.mem_range_self p'.hom))
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (InternalGrading.mem_submodule_piece _ _ _).mpr (GradedModuleCat.map_mem p' hx))
    retract := GradedModuleCat.hom_ext <| LinearMap.ext fun z ↦ Subtype.ext <| by
      obtain ⟨x, hx⟩ := z.2
      exact (congrArg p'.hom hx.symm).trans ((hp' x).trans hx) }

private theorem apply_retractRangeOfPiIdempotent_i_r_symm {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    (v : I → A) :
    DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
      ((retractRangeOfPiIdempotent s p hp hhom).i.hom
        ((retractRangeOfPiIdempotent s p hp hhom).r.hom
          ((DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v))) = p v := by
  have h : (retractRangeOfPiIdempotent s p hp hhom).i.hom
      ((retractRangeOfPiIdempotent s p hp hhom).r.hom
        ((DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v)) =
      (freeEndOfPiEnd s p hhom).hom
        ((DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v) := rfl
  rw [h]
  dsimp [freeEndOfPiEnd, GradedModuleCat.ofHom]
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

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
    rw [LinearEquiv.symm_trans_apply, mem_free_piece_symm_iff]
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
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_coe, eD.symm_apply_apply, h1]
    exact apply_retractRangeOfPiIdempotent_i_r_symm s p hp hhom v
  · exact fun q u hu ↦ (GradedModuleCat.mem_free_piece_iff 𝒜 s q _).mp
      (GradedModuleCat.map_mem rR.i (GradedModuleCat.map_mem Φ.hom ((heD_symm q u).mpr hu)))
  · exact fun q v hv ↦ (heD_symm q (π v)).mp <| by
      simpa [π] using GradedModuleCat.map_mem Φ.inv
        (GradedModuleCat.map_mem rR.r ((mem_free_piece_symm_iff s q v).mpr hv))

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
  let equivRange : (Fin n → A) ≃ₗ[A] LinearMap.range p :=
    LinearEquiv.ofLinearMap
      (LinearMap.codRestrict (LinearMap.range p) ι fun u ↦
        ⟨ι u, (LinearMap.congr_fun hιπ (ι u)).symm.trans
          (congrArg ι (LinearMap.congr_fun hπι u))⟩)
      (π.comp (LinearMap.range p).subtype)
      (LinearMap.ext fun y ↦ Subtype.ext <| by
        obtain ⟨v, hv⟩ := y.2
        exact (LinearMap.congr_fun hιπ y.1).trans (hv ▸ LinearMap.congr_fun hp v))
      (LinearMap.ext fun u ↦ LinearMap.congr_fun hπι u)
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

/-- Over a nontrivial commutative ring `k`, any two finite homogeneous bases of the range of a
degree-zero endomorphism `p : (I → A) →ₗ[A] (I → A)` (`[Finite I]`) have the same multiset of
degrees. -/
theorem multiset_map_eq_of_homogeneous_basis_range_idempotent
    [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A),
      (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) A (LinearMap.range p)) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ 𝒜 (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) A (LinearMap.range p)) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ 𝒜 (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val := by
  cases nonempty_fintype I
  let equivRange := rangeEquivRangeObj s p hhom
  let mkIso : ∀ {n : ℕ} (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      (∀ i j, (b i).val j ∈ 𝒜 (d i - s j)) →
        (GradedModuleCat.free 𝒜 (d ∘ ULift.down) ≅ rangeObjOfPiEnd s p hhom) :=
    fun b d hb ↦ GradedModuleCat.isoFreeOfHomogeneousBasis
      ((b.reindex Equiv.ulift.symm).map equivRange) fun i ↦
        (InternalGrading.mem_submodule_piece _ _ _).mpr <| by
          have hval : (((b.reindex Equiv.ulift.symm).map equivRange) i).1 =
              (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm (b i.down).val := by
            simp only [equivRange, rangeEquivRangeObj, Module.Basis.map_apply,
              Module.Basis.reindex_apply]
            rfl
          rw [hval]
          exact (mem_free_piece_symm_iff s (d i.down) (b i.down).val).mpr (hb i.down)
  have hU := GradedModuleCat.multiset_map_eq_of_iso_free hneg hzero
    ((mkIso b₁ d₁ hb₁).trans (mkIso b₂ d₂ hb₂).symm)
  have huniv : ∀ {n : ℕ} (d : Fin n → ℤ),
      Multiset.map (d ∘ ULift.down) (Finset.univ : Finset (ULift.{uI} (Fin n))).val =
        Multiset.map d Finset.univ.val := fun d ↦ by
    rw [← Multiset.map_map]
    exact congrArg (Multiset.map d)
      (congrArg Finset.val (Finset.map_univ_equiv (Equiv.ulift (α := Fin _))))
  rwa [huniv d₁, huniv d₂] at hU

omit [CommRing k] [Algebra k A] [GradedAlgebra 𝒜] in
/-- Over a nontrivial ring `A`, every `Fin n`-indexed basis of the range of the zero endomorphism
on `I → A` has `n = 0`. -/
theorem eq_zero_of_basis_range_zero [Nontrivial A] {I : Type uI} {n : ℕ}
    (b : Module.Basis (Fin n) A (LinearMap.range (0 : (I → A) →ₗ[A] (I → A)))) :
    n = 0 := by
  by_contra hn
  have hsub : Subsingleton (LinearMap.range (0 : (I → A) →ₗ[A] (I → A))) := by
    rw [LinearMap.range_zero]
    infer_instance
  exact b.ne_zero ⟨0, Nat.pos_of_ne_zero hn⟩ (Subsingleton.elim _ _)

omit [CommRing k] [Algebra k A] [GradedAlgebra 𝒜] in
/-- Any `A`-linear endomorphism `p : (I → A) →ₗ[A] (I → A)` of the form `p v = v i₀ • w` with
`w i₀ = 1` is idempotent. -/
theorem idempotent_of_apply_eq_smul {I : Type uI} {p : (I → A) →ₗ[A] (I → A)} (i₀ : I)
    {w : I → A} (hp : ∀ v, p v = v i₀ • w) (hw₀ : w i₀ = 1) : p.comp p = p := by
  ext v j
  simp [hp, hw₀]

/-- If `p v = v i₀ • w` and `∀ j, w j ∈ 𝒜 (s i₀ - s j)`, then `p` is homogeneous of degree zero on
the shifted module `I → A` with shifts `s`. -/
theorem homogeneous_of_apply_eq_smul {I : Type uI} (s : I → ℤ) {p : (I → A) →ₗ[A] (I → A)}
    (i₀ : I) {w : I → A} (hp : ∀ v, p v = v i₀ • w) (hw : ∀ j, w j ∈ 𝒜 (s i₀ - s j))
    (d : ℤ) (v : I → A) (hv : ∀ j, v j ∈ 𝒜 (d - s j)) (j : I) :
    p v j ∈ 𝒜 (d - s j) := by
  rw [hp, Pi.smul_apply, smul_eq_mul]
  simpa [sub_add_sub_cancel] using SetLike.mul_mem_graded (hv i₀) (hw j)

/-- Over a connected nonnegatively graded `k`-algebra (`Nontrivial k`), any finite homogeneous basis
of the range of a rank-one homogeneous projection `p v = v i₀ • w` (`w i₀ = 1`,
`∀ j, w j ∈ 𝒜 (s i₀ - s j)`) has degree multiset `{s i₀}`. -/
theorem multiset_map_eq_singleton_of_homogeneous_basis_range
    [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] (s : I → ℤ)
    {p : (I → A) →ₗ[A] (I → A)} (i₀ : I) {w : I → A}
    (hp : ∀ v, p v = v i₀ • w) (hw₀ : w i₀ = 1) (hw : ∀ j, w j ∈ 𝒜 (s i₀ - s j))
    {n : ℕ} (b : Module.Basis (Fin n) A (LinearMap.range p))
    (d : Fin n → ℤ) (hb : ∀ i j, (b i).val j ∈ 𝒜 (d i - s j)) :
    Multiset.map d Finset.univ.val = {s i₀} := by
  let e₁ : (Fin 1 → A) ≃ₗ[A] LinearMap.range p :=
    { toFun := fun u ↦ ⟨u 0 • w, Function.const I (u 0), by rw [hp]; rfl⟩
      map_add' := fun u₁ u₂ ↦ Subtype.ext (add_smul (u₁ 0) (u₂ 0) w)
      map_smul' := fun a u ↦ Subtype.ext (mul_smul a (u 0) w)
      invFun := fun y _ ↦ y.1 i₀
      left_inv := fun u ↦ funext fun t ↦ by
        rw [Fin.eq_zero t]
        dsimp only
        rw [Pi.smul_apply, smul_eq_mul, hw₀, mul_one]
      right_inv := fun y ↦ Subtype.ext <| by
        obtain ⟨v, hv⟩ := y.2
        dsimp only
        rw [← hv, hp v, Pi.smul_apply, smul_eq_mul, hw₀, mul_one] }
  let b₀ : Module.Basis (Fin 1) A (LinearMap.range p) := (Pi.basisFun A (Fin 1)).map e₁
  have hb₀ : ∀ (i : Fin 1) (j : I), (b₀ i).val j ∈ 𝒜 (s i₀ - s j) := fun i j ↦ by
    rw [Fin.eq_zero i]
    have hval : (b₀ 0).val = w := by
      dsimp only [b₀]
      rw [Module.Basis.map_apply, Pi.basisFun_apply]
      dsimp [e₁]
      rw [Pi.single_eq_same, one_smul]
    rw [hval]
    exact hw j
  have h := multiset_map_eq_of_homogeneous_basis_range_idempotent hneg hzero s p
    (homogeneous_of_apply_eq_smul s i₀ hp hw) b d hb b₀ (fun _ ↦ s i₀) hb₀
  simpa using h

end ConnectedRing

end TauCeti
