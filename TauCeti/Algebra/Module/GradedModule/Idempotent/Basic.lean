/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Free.Head

/-!
# Graded endomorphism ranges and degree-multiset uniqueness on shifted free modules

Let `A` be a connected nonnegatively `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`), and view
the finite function module `I → A` (`[Finite I]`) as the shifted free graded `A`-module with `j`th
summand in shift `s j : ℤ`, so its homogeneous elements of degree `d` are the tuples `v : I → A`
satisfying `∀ j, v j ∈ 𝒜 (d - s j)`.

Transporting `I → A` to `GradedModuleCat.free 𝒜 s` via `DirectSum.linearEquivFunOnFintype` yields
the shared graded-range infrastructure and PID-free basis degree-uniqueness results:

* `TauCeti.freeEndOfPiEnd`, `TauCeti.rangeObjOfPiEnd`, `TauCeti.rangeEquivRangeObj`: graded
  endomorphism and graded range object in `GradedModuleCat 𝒜` associated to a degree-zero
  endomorphism of `I → A`.
* `TauCeti.multiset_map_eq_of_homogeneous_basis_range_idempotent`: over a nontrivial commutative
  base ring `k`, any two finite homogeneous `A`-bases of `LinearMap.range p` have the same
  multiset of shifts.
* `TauCeti.homogeneous_of_apply_eq_smul`,
  `TauCeti.multiset_map_eq_singleton_of_homogeneous_basis_range`: any rank-one homogeneous
  projection `p v = v i₀ • w` (`w i₀ = 1`, `∀ j, w j ∈ 𝒜 (s i₀ - s j)`) has unique basis degree
  multiset `{s i₀}`.

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

omit [GradedAlgebra 𝒜] in
/-- Transporting a degree-zero endomorphism of `I → A` to `GradedModuleCat.free 𝒜 s`. -/
@[expose]
noncomputable def freeEndOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    GradedModuleCat.free 𝒜 s ⟶ GradedModuleCat.free 𝒜 s :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  GradedModuleCat.ofHom (eF.symm.conjRingEquiv p) <|
    LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
      rw [add_zero]
      exact (GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s q _).mpr
        (hhom q (eF x) ((GradedModuleCat.mem_free_piece_iff 𝒜 s q x).mp hx))

/-- The graded range object in `GradedModuleCat 𝒜` of a degree-zero endomorphism of `I → A`. -/
@[expose]
noncomputable def rangeObjOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
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
noncomputable def rangeEquivRangeObj {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  eF.symm.ofSubmodules (LinearMap.range p) (LinearMap.range p'.hom) <| by
    dsimp [p', freeEndOfPiEnd]
    change Submodule.map eF.symm.toLinearMap (LinearMap.range p) =
      LinearMap.range (eF.symm.toLinearMap ∘ₗ p ∘ₗ eF.toLinearMap)
    rw [← LinearMap.range_comp, ← LinearMap.comp_assoc, LinearEquiv.range_comp]

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
    fun b d hb ↦ ((b.reindex Equiv.ulift.symm).map equivRange).isoGradedFree fun i ↦
      (InternalGrading.mem_submodule_piece _ _ _).mpr <| by
        have hval : (((b.reindex Equiv.ulift.symm).map equivRange) i).val =
            (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm (b i.down).val := by
          rw [Module.Basis.map_apply, Module.Basis.reindex_apply]
          exact LinearEquiv.ofSubmodules_apply _ _ (b i.down)
        rw [hval]
        exact (GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff
          𝒜 s (d i.down) (b i.down).val).mpr (hb i.down)
  have hU := GradedModuleCat.multiset_map_eq_of_iso_free hneg hzero
    ((mkIso b₁ d₁ hb₁).trans (mkIso b₂ d₂ hb₂).symm)
  have huniv : ∀ {n : ℕ} (d : Fin n → ℤ),
      Multiset.map (d ∘ ULift.down) (Finset.univ : Finset (ULift.{uI} (Fin n))).val =
        Multiset.map d Finset.univ.val := fun d ↦ by
    rw [← Multiset.map_map]
    exact congrArg (Multiset.map d)
      (congrArg Finset.val (Finset.map_univ_equiv (Equiv.ulift (α := Fin _))))
  rwa [huniv d₁, huniv d₂] at hU

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
  let ι : (Fin 1 → A) →ₗ[A] (I → A) :=
    (LinearMap.proj (R := A) (φ := fun _ : Fin 1 ↦ A) 0).smulRight w
  have hleft : Function.LeftInverse (fun (v : I → A) (_ : Fin 1) ↦ v i₀) ι := fun u ↦
    funext fun t ↦ by
      rw [Fin.eq_zero t]
      simp [ι, hw₀]
  have hrange : LinearMap.range ι = LinearMap.range p := by
    ext x
    simp only [LinearMap.mem_range, ι, LinearMap.smulRight_apply, LinearMap.proj_apply, hp]
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨Function.const I (u 0), hu⟩, fun ⟨v, hv⟩ ↦ ⟨fun _ ↦ v i₀, hv⟩⟩
  let e₁ : (Fin 1 → A) ≃ₗ[A] LinearMap.range p :=
    (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ hrange)
  let b₀ : Module.Basis (Fin 1) A (LinearMap.range p) := (Pi.basisFun A (Fin 1)).map e₁
  have hb₀ : ∀ (i : Fin 1) (j : I), (b₀ i).val j ∈ 𝒜 (s i₀ - s j) := fun i j ↦ by
    rw [Fin.eq_zero i]
    have hval : (b₀ 0).val = w := by
      dsimp only [b₀]
      rw [Module.Basis.map_apply, Pi.basisFun_apply]
      change ι (Pi.single 0 1) = w
      simp [ι]
    rw [hval]
    exact hw j
  have h := multiset_map_eq_of_homogeneous_basis_range_idempotent hneg hzero s p
    (homogeneous_of_apply_eq_smul s i₀ hp hw) b d hb b₀ (fun _ ↦ s i₀) hb₀
  simpa using h

end ConnectedRing

end TauCeti
