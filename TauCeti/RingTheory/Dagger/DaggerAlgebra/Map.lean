/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Completion
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.MaximalSpectrum
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm

import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.Restricted
import TauCeti.RingTheory.Dagger.AlgHomExt

/-!
# Universal property and functoriality of dagger completion

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra. This file
establishes three structural properties of the completion `τ : A → completion K A`:

1. **Metric completion** (`TauCeti.Dagger.uniformCompletionAlgEquiv`): equipping `A` with the
   residue norm `TauCeti.Dagger.residueNormedCommRing` of its chosen minimal presentation, `τ` is
   an isometry with dense image, identifying `UniformSpace.Completion A` isometrically with
   `completion K A` as a `K`-algebra.
2. **Universal property in affinoid algebras** (`TauCeti.Dagger.completion.lift`,
   `TauCeti.Dagger.completion.existsUnique_algHom`): every `K`-algebra homomorphism `A →ₐ[K] C` into
   a completely normed affinoid algebra extends uniquely along `τ` to a (necessarily continuous)
   `K`-algebra homomorphism `completion K A →ₐ[K] C`. Thus `completion K` is left adjoint to the
   forgetful functor from `K`-affinoid algebras to `K`-dagger algebras.
3. **Functoriality and presentation-independence** (`TauCeti.Dagger.completion.map`,
   `TauCeti.Dagger.completion.presentationAlgEquiv`,
   `TauCeti.Dagger.completion.washnitzerAlgEquiv`): every `K`-algebra map `A →ₐ[K] B` of dagger
   algebras induces a unique `K`-algebra map `completion K A →ₐ[K] completion K B` compatible with
   `toCompletion`, surjective maps induce surjections on completions, and for any surjective
   overconvergent presentation `π : W_σ ↠ A` the completion `completion K A` is canonically
   isomorphic to `T_σ ⧸ (ker π) T_σ`.

Topological upgrades of these isomorphisms (`ContinuousAlgEquiv`) are provided in
`TauCeti.RingTheory.Dagger.DaggerAlgebra.Continuity`.

## Main definitions

* `TauCeti.Dagger.uniformCompletionAlgEquiv`: isometric `K`-algebra isomorphism
  `UniformSpace.Completion A ≃ₐ[K] completion K A` for the residue norm on `A`.
* `TauCeti.Dagger.washnitzerAlgebra.liftTate`: extension of `W_σ →ₐ[K] C` to `T_σ →ₐ[K] C` for any
  completely normed affinoid algebra `C`.
* `TauCeti.Dagger.completion.lift`: universal extension `(A →ₐ[K] C) → (completion K A →ₐ[K] C)`
  into any completely normed affinoid algebra `C`.
* `TauCeti.Dagger.completion.map` and `TauCeti.Dagger.completion.mapEquiv`: functorial action of
  `completion K` on `K`-algebra homomorphisms and isomorphisms of dagger algebras.
* `TauCeti.Dagger.completion.presentationAlgEquiv`: canonical isomorphism
  `completion K A ≃ₐ[K] T_σ ⧸ (ker π) T_σ` for an arbitrary presentation `π : W_σ ↠ A`.
* `TauCeti.Dagger.completion.washnitzerAlgEquiv` and
  `TauCeti.Dagger.completion.restrictedMvPowerSeriesCompletionAlgEquiv`: identification of
  `completion K (washnitzerAlgebra _ K)` with the Gauss-normed and Huber Tate algebras.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 and Theorem 1.7(1).
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section UniformCompletion

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **Metric completion comparison for dagger algebras.** Equipping `A` with the residue norm of
its chosen minimal presentation, `UniformSpace.Completion A` is isometrically isomorphic as a
`K`-algebra to `completion K A`. -/
noncomputable def uniformCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    UniformSpace.Completion A ≃ₐ[K] completion K A :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  AlgHom.completionAlgEquiv (R := K) (A := A) (B := completion K A)
    (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion

/-- `uniformCompletionAlgEquiv` extends `toCompletion` on elements of `A`. -/
@[simp↓]
theorem uniformCompletionAlgEquiv_coe (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    uniformCompletionAlgEquiv K A (a : UniformSpace.Completion A) = toCompletion K A a :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    have h : uniformCompletionAlgEquiv K A =
        AlgHom.completionAlgEquiv (R := K) (A := A) (B := completion K A)
          (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion := rfl
    rw [h]
    exact AlgHom.completionAlgEquiv_coe _ _ _ a

/-- The inverse metric completion comparison sends `toCompletion K A a` to `(a : Completion A)`. -/
@[simp↓]
theorem uniformCompletionAlgEquiv_symm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    (uniformCompletionAlgEquiv K A).symm (toCompletion K A a) =
      (a : UniformSpace.Completion A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by rw [← uniformCompletionAlgEquiv_coe K A a, AlgEquiv.symm_apply_apply]

/-- `uniformCompletionAlgEquiv` is an isometry for the completed residue norm and the quotient
Gauss norm on `completion K A`. -/
theorem isometry_uniformCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Isometry (uniformCompletionAlgEquiv K A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    have h : uniformCompletionAlgEquiv K A =
        AlgHom.completionAlgEquiv (R := K) (A := A) (B := completion K A)
          (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion := rfl
    rw [h]
    exact AlgHom.isometry_completionAlgEquiv _ _ _

/-- `uniformCompletionAlgEquiv` preserves norms. -/
@[simp↓]
theorem norm_uniformCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    ∀ x : UniformSpace.Completion A, ‖uniformCompletionAlgEquiv K A x‖ = ‖x‖ :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  fun x ↦ (AddMonoidHomClass.isometry_iff_norm (E := UniformSpace.Completion A)
    (F := completion K A) (uniformCompletionAlgEquiv K A)).mp
      (isometry_uniformCompletionAlgEquiv K A) x

end UniformCompletion

section LiftTate

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C]
  [CompleteSpace C]

namespace washnitzerAlgebra

/-- Two `K`-algebra homomorphisms out of `K⟨X₁, …, Xₙ⟩` into a completely normed affinoid algebra
agree as soon as their restrictions to `K⟨X₁, …, Xₙ⟩†` agree. No continuity hypothesis is needed. -/
theorem algHom_ext_toTate (hC : IsAffinoidAlgebra K C)
    {f g : IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) →ₐ[K] C}
    (h : f.comp (toTate σ K) = g.comp (toTate σ K)) : f = g := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  have hf : Continuous f :=
    hC.continuous_algHom (B := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))) f
  have hg : Continuous g :=
    hC.continuous_algHom (B := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))) g
  exact DFunLike.coe_injective <| denseRange_toTate.equalizer hf hg (congrArg DFunLike.coe h)

/-- Every `K`-algebra homomorphism from `K⟨X₁, …, Xₙ⟩†` into a completely normed affinoid algebra
extends along `toTate` to the unit-radius Tate algebra `K⟨X₁, …, Xₙ⟩`. -/
noncomputable def liftTate (hC : IsAffinoidAlgebra K C) (ψ : washnitzerAlgebra σ K →ₐ[K] C) :
    IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) →ₐ[K] C := by
  let _ := Fintype.ofFinite σ
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hb : ∀ j : Fin (Fintype.card σ), Huber.IsPowerBounded (ψ (X σ K (e.symm j))) := fun j ↦
    hC.isPowerBounded_iff_supSeminorm_le_one.mpr <|
      (IsDaggerAlgebra.supSeminorm_map_le_of_isAffinoidAlgebra hC ψ _).trans_eq
        ((supSeminorm_eq_norm _).trans (norm_X _))
  exact (isAffinoidAlgebra_self.restrictedLift hC (Algebra.ofId K C) hb).comp
    (IsRestricted.renameAlgEquiv e (fun _ : Fin (Fintype.card σ) ↦ (1 : ℝ))).toAlgHom

@[simp]
theorem liftTate_comp_toTate (hC : IsAffinoidAlgebra K C) (ψ : washnitzerAlgebra σ K →ₐ[K] C) :
    (liftTate hC ψ).comp (toTate σ K) = ψ := by
  refine hC.algHom_ext_washnitzerAlgebra fun i ↦ ?_
  dsimp [liftTate]
  rw [toTate_X, IsRestricted.renameAlgEquiv_X, IsAffinoidAlgebra.restrictedLift_X,
    Equiv.symm_apply_apply]

@[simp]
theorem liftTate_toTate (hC : IsAffinoidAlgebra K C) (ψ : washnitzerAlgebra σ K →ₐ[K] C)
    (f : washnitzerAlgebra σ K) : liftTate hC ψ (toTate σ K f) = ψ f :=
  AlgHom.congr_fun (liftTate_comp_toTate hC ψ) f

end washnitzerAlgebra

end LiftTate

namespace completion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  {B : Type*} [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  {D : Type*} [CommRing D] [Algebra K D] [IsDaggerAlgebra K D]
  {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- **Uniqueness of extensions to the completion.** Two `K`-algebra homomorphisms from
`completion K A` into a completely normed affinoid algebra agree as soon as they agree on `A`. No
continuity hypothesis is needed. -/
theorem algHom_ext (hC : IsAffinoidAlgebra K C) {f g : completion K A →ₐ[K] C}
    (h : f.comp (toCompletion K A) = g.comp (toCompletion K A)) : f = g := by
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  have hf : Continuous f := hC.continuous_algHom (B := completion K A) f
  have hg : Continuous g := hC.continuous_algHom (B := completion K A) g
  exact DFunLike.coe_injective <| denseRange_toCompletion.equalizer hf hg (congrArg DFunLike.coe h)

/-- **Universal extension to the completion.** Every `K`-algebra homomorphism `ψ : A →ₐ[K] C` from
a dagger algebra into a completely normed affinoid algebra extends along `toCompletion K A` to
`completion K A →ₐ[K] C`. -/
noncomputable def lift (hC : IsAffinoidAlgebra K C) (ψ : A →ₐ[K] C) : completion K A →ₐ[K] C :=
  have hker : (RingHom.ker (presentation K A)).map (washnitzerAlgebra.toTate _ K) ≤
      RingHom.ker (washnitzerAlgebra.liftTate hC (ψ.comp (presentation K A))) :=
    Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by
      simp [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker.mp hf]
  Ideal.Quotient.liftₐ _ (washnitzerAlgebra.liftTate hC (ψ.comp (presentation K A)))
    fun a ha ↦ RingHom.mem_ker.mp (hker ha)

@[simp]
theorem lift_toCompletion (hC : IsAffinoidAlgebra K C) (ψ : A →ₐ[K] C) (a : A) :
    lift hC ψ (toCompletion K A a) = ψ a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [toCompletion_presentation]
  exact washnitzerAlgebra.liftTate_toTate hC (ψ.comp (presentation K A)) f

@[simp]
theorem lift_comp_toCompletion (hC : IsAffinoidAlgebra K C) (ψ : A →ₐ[K] C) :
    (lift hC ψ).comp (toCompletion K A) = ψ :=
  AlgHom.ext (lift_toCompletion hC ψ)

/-- The universal extension `completion.lift hC ψ` is continuous for the quotient Gauss norm on
`completion K A`. -/
theorem continuous_lift (hC : IsAffinoidAlgebra K C) (ψ : A →ₐ[K] C) :
    Continuous (lift hC ψ) := by
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  exact hC.continuous_algHom (B := completion K A) (lift hC ψ)

/-- **Left-adjointness of `completion`.** Every `K`-algebra homomorphism from a dagger algebra `A`
into a completely normed affinoid algebra `C` factors uniquely through `toCompletion K A`. -/
theorem existsUnique_algHom (hC : IsAffinoidAlgebra K C) (ψ : A →ₐ[K] C) :
    ∃! Φ : completion K A →ₐ[K] C, Φ.comp (toCompletion K A) = ψ :=
  ⟨lift hC ψ, lift_comp_toCompletion hC ψ,
    fun _ hΦ ↦ algHom_ext hC (hΦ.trans (lift_comp_toCompletion hC ψ).symm)⟩

/-- **Functoriality of `completion`.** A `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras
induces a unique `K`-algebra homomorphism `completion.map φ : completion K A →ₐ[K] completion K B`
compatible with `toCompletion`. -/
noncomputable def map (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  lift (K := K) (A := A) (C := completion K B) isAffinoidAlgebra_completion
    ((toCompletion K B).comp φ)

@[simp]
theorem map_toCompletion (φ : A →ₐ[K] B) (a : A) :
    map φ (toCompletion K A a) = toCompletion K B (φ a) := by
  rw [map]
  exact lift_toCompletion _ _ a

@[simp]
theorem map_comp_toCompletion (φ : A →ₐ[K] B) :
    (map φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  AlgHom.ext (map_toCompletion φ)

/-- The induced map `completion.map φ` on completions is continuous. -/
theorem continuous_map (φ : A →ₐ[K] B) : Continuous (map φ) := by
  rw [map]
  exact continuous_lift _ _

@[simp]
theorem map_id : map (AlgHom.id K A) = AlgHom.id K (completion K A) :=
  algHom_ext (K := K) (A := A) (C := completion K A) isAffinoidAlgebra_completion
    (AlgHom.ext fun a ↦ by simp)

/-- `completion.map (AlgHom.id K A)` acts as the identity on elements. -/
theorem map_id_apply (x : completion K A) : map (AlgHom.id K A) x = x := by
  rw [map_id, AlgHom.id_apply]

/-- `completion.map` preserves composition of `K`-algebra homomorphisms. -/
theorem map_comp (φ : A →ₐ[K] B) (ψ : B →ₐ[K] D) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  algHom_ext (K := K) (A := A) (C := completion K D) isAffinoidAlgebra_completion
    (AlgHom.ext fun a ↦ by simp)

@[simp]
theorem map_map (φ : A →ₐ[K] B) (ψ : B →ₐ[K] D) (x : completion K A) :
    map ψ (map φ x) = map (ψ.comp φ) x :=
  (AlgHom.congr_fun (map_comp φ ψ) x).symm

/-- A `K`-algebra isomorphism of dagger algebras induces a `K`-algebra isomorphism of their
completions. -/
noncomputable def mapEquiv (e : A ≃ₐ[K] B) : completion K A ≃ₐ[K] completion K B :=
  AlgEquiv.ofAlgHom (map e.toAlgHom) (map e.symm.toAlgHom)
    (by
      rw [← map_comp]
      convert map_id (K := K) (A := B)
      ext
      simp)
    (by
      rw [← map_comp]
      convert map_id (K := K) (A := A)
      ext
      simp)

@[simp]
theorem coe_mapEquiv (e : A ≃ₐ[K] B) : ⇑(mapEquiv e) = map e.toAlgHom := (rfl)

@[simp]
theorem mapEquiv_symm (e : A ≃ₐ[K] B) : (mapEquiv e).symm = mapEquiv e.symm :=
  AlgEquiv.ext fun _ ↦ rfl

@[simp]
theorem mapEquiv_toCompletion (e : A ≃ₐ[K] B) (a : A) :
    mapEquiv e (toCompletion K A a) = toCompletion K B (e a) :=
  map_toCompletion e.toAlgHom a

@[simp]
theorem mapEquiv_refl : mapEquiv (AlgEquiv.refl : A ≃ₐ[K] A) = AlgEquiv.refl :=
  AlgEquiv.ext map_id_apply

@[simp]
theorem mapEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] D) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
  AlgEquiv.ext fun x ↦ (map_map e₁.toAlgHom e₂.toAlgHom x).symm

/-- Auxiliary map `T_σ ⧸ (ker π) T_σ →ₐ[K] completion K A` induced by an overconvergent
presentation `π : W_σ →ₐ[K] A`. -/
private noncomputable def presentationInv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) :
    IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸
      (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) →ₐ[K] completion K A :=
  let F := washnitzerAlgebra.liftTate (K := K) (σ := σ) (C := completion K A)
    isAffinoidAlgebra_completion ((toCompletion K A).comp π)
  Ideal.Quotient.liftₐ ((RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) F fun a ha ↦
    RingHom.mem_ker.mp <|
      (Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by
        simp [F, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker.mp hf]) ha

private theorem presentationInv_mk_toTate {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (f : washnitzerAlgebra σ K) :
    presentationInv π (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K A (π f) :=
  washnitzerAlgebra.liftTate_toTate _ _ f

/-- **Presentation-independence of `completion`.** For any surjective overconvergent presentation
`π : W_σ ↠ A`, `completion K A` is canonically isomorphic as a `K`-algebra to
`T_σ ⧸ (ker π) T_σ`. -/
noncomputable def presentationAlgEquiv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    completion K A ≃ₐ[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸
        (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  let J := (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)
  let hQ : IsAffinoidAlgebra K
      (IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸ J) :=
    isAffinoidAlgebra_tate.quotient J
  let τ : A →ₐ[K] IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸ J :=
    (Ideal.quotientMapₐ J (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  let fwd := lift (K := K) (A := A)
    (C := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸ J) hQ τ
  have hτ : ∀ f, τ (π f) = Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f) := fun f ↦ by
    rw [← Ideal.quotientKerAlgEquivOfSurjective_mk hπ f]
    dsimp only [τ, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [AlgEquiv.symm_apply_apply]
    rfl
  AlgEquiv.ofAlgHom fwd (presentationInv π)
    (by
      have hcomp := washnitzerAlgebra.algHom_ext_toTate (K := K) (σ := σ)
        (C := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸ J) hQ
        (f := (fwd.comp (presentationInv π)).comp (Ideal.Quotient.mkₐ K J))
        (g := Ideal.Quotient.mkₐ K J) <| AlgHom.ext fun f ↦ by
          dsimp only [fwd, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
          rw [presentationInv_mk_toTate, lift_toCompletion, hτ]
      refine AlgHom.ext fun x ↦ ?_
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact AlgHom.congr_fun hcomp g)
    (algHom_ext (K := K) (A := A) (C := completion K A) isAffinoidAlgebra_completion <|
      AlgHom.ext fun a ↦ by
        obtain ⟨f, rfl⟩ := hπ a
        dsimp only [fwd, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
        rw [lift_toCompletion, hτ, presentationInv_mk_toTate])

@[simp]
theorem presentationAlgEquiv_toCompletion_apply {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    presentationAlgEquiv π hπ (toCompletion K A (π f)) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) := by
  dsimp only [presentationAlgEquiv]
  rw [AlgEquiv.ofAlgHom_apply, lift_toCompletion, ← Ideal.quotientKerAlgEquivOfSurjective_mk hπ f]
  dsimp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [AlgEquiv.symm_apply_apply]
  rfl

@[simp]
theorem presentationAlgEquiv_symm_mk_toTate {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    (presentationAlgEquiv π hπ).symm (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K A (π f) :=
  (AlgEquiv.symm_apply_eq _).mpr (presentationAlgEquiv_toCompletion_apply π hπ f).symm

/-- A surjective `K`-algebra homomorphism of dagger algebras induces a surjective map on
completions. -/
theorem map_surjective {φ : A →ₐ[K] B} (hφ : Function.Surjective φ) :
    Function.Surjective (map φ) := by
  let πB := φ.comp (presentation K A)
  have hπB : Function.Surjective πB := hφ.comp (presentation_surjective K A)
  let JB := (RingHom.ker πB).map (washnitzerAlgebra.toTate _ K)
  have hle : (RingHom.ker (presentation K A)).map (washnitzerAlgebra.toTate _ K) ≤
      JB.comap (AlgHom.id K _) := by
    rw [Ideal.comap_idₐ]
    exact Ideal.map_mono fun f hf ↦ by simp [πB, RingHom.mem_ker, RingHom.mem_ker.mp hf]
  let q : completion K A →ₐ[K] _ := Ideal.quotientMapₐ JB (AlgHom.id K _) hle
  have hq : (presentationAlgEquiv πB hπB).toAlgHom.comp (map φ) = q :=
    algHom_ext (K := K) (A := A)
      (C := IsRestricted.subring (R := K)
        (fun _ : Fin (presentationDim K A) ↦ (1 : ℝ)) ⧸ JB)
      (isAffinoidAlgebra_tate.quotient _) <| AlgHom.ext fun a ↦ by
        obtain ⟨f, rfl⟩ := presentation_surjective K A a
        dsimp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom]
        rw [map_toCompletion]
        change presentationAlgEquiv πB hπB (toCompletion K B (πB f)) =
          q (toCompletion K A (presentation K A f))
        rw [presentationAlgEquiv_toCompletion_apply, toCompletion_presentation]
        rfl
  intro y
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (presentationAlgEquiv πB hπB y)
  refine ⟨Ideal.Quotient.mk _ g, (presentationAlgEquiv πB hπB).injective ?_⟩
  exact (AlgHom.congr_fun hq (Ideal.Quotient.mk _ g)).trans hg

variable (K) in
/-- **The completion of the Monsky–Washnitzer algebra is the unit-radius Tate algebra.** -/
noncomputable def washnitzerAlgEquiv (σ : Type*) [Finite σ] :
    completion K (washnitzerAlgebra σ K) ≃ₐ[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) :=
  let T := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))
  let fwd := lift (K := K) (A := washnitzerAlgebra σ K) (C := T)
    isAffinoidAlgebra_tate (washnitzerAlgebra.toTate σ K)
  let inv := washnitzerAlgebra.liftTate (K := K) (σ := σ)
    (C := completion K (washnitzerAlgebra σ K))
    isAffinoidAlgebra_completion (toCompletion K (washnitzerAlgebra σ K))
  AlgEquiv.ofAlgHom fwd inv
    (washnitzerAlgebra.algHom_ext_toTate (K := K) (σ := σ) (C := T) isAffinoidAlgebra_tate <|
      AlgHom.ext fun f ↦ by
        dsimp only [fwd, inv, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
        rw [washnitzerAlgebra.liftTate_toTate, lift_toCompletion])
    (algHom_ext (K := K) (A := washnitzerAlgebra σ K)
      (C := completion K (washnitzerAlgebra σ K)) isAffinoidAlgebra_completion <|
      AlgHom.ext fun f ↦ by
        dsimp only [fwd, inv, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
        rw [lift_toCompletion, washnitzerAlgebra.liftTate_toTate])

@[simp]
theorem washnitzerAlgEquiv_toCompletion {σ : Type*} [Finite σ] (f : washnitzerAlgebra σ K) :
    washnitzerAlgEquiv K σ (toCompletion K (washnitzerAlgebra σ K) f) =
      washnitzerAlgebra.toTate σ K f := by
  dsimp only [washnitzerAlgEquiv, AlgEquiv.ofAlgHom_apply]
  exact lift_toCompletion _ _ f

@[simp]
theorem washnitzerAlgEquiv_symm_toTate {σ : Type*} [Finite σ] (f : washnitzerAlgebra σ K) :
    (washnitzerAlgEquiv K σ).symm (washnitzerAlgebra.toTate σ K f) =
      toCompletion K (washnitzerAlgebra σ K) f := by
  dsimp only [washnitzerAlgEquiv, AlgEquiv.ofAlgHom_symm_apply]
  exact washnitzerAlgebra.liftTate_toTate _ _ f

variable (K) in
/-- **Comparison of `completion K (washnitzerAlgebra (Fin n) K)` with Huber's completed Tate
algebra** `Huber.restrictedMvPowerSeriesCompletion n K`, as a `K`-algebra isomorphism. -/
noncomputable def restrictedMvPowerSeriesCompletionAlgEquiv (n : ℕ) :
    completion K (washnitzerAlgebra (Fin n) K) ≃ₐ[K]
      Huber.restrictedMvPowerSeriesCompletion n K :=
  (washnitzerAlgEquiv K (Fin n)).trans
    (Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)).symm

@[simp]
theorem restrictedMvPowerSeriesCompletionAlgEquiv_apply (n : ℕ)
    (x : completion K (washnitzerAlgebra (Fin n) K)) :
    restrictedMvPowerSeriesCompletionAlgEquiv K n x =
      (Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)).symm
        (washnitzerAlgEquiv K (Fin n) x) := by rfl

@[simp]
theorem restrictedMvPowerSeriesCompletionAlgEquiv_symm_apply (n : ℕ)
    (y : Huber.restrictedMvPowerSeriesCompletion n K) :
    (restrictedMvPowerSeriesCompletionAlgEquiv K n).symm y =
      (washnitzerAlgEquiv K (Fin n)).symm
        (Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K) y) := by rfl

end completion

end TauCeti.Dagger
