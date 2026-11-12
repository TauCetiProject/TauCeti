/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Transporting quadratic forms along semilinear equivalences

Let `σ : R →+* S` be a ring isomorphism with inverse `σ'`, and let `f : M ≃ₛₗ[σ] M'` be a
`σ`-semilinear equivalence from an `R`-module to an `S`-module. A quadratic form `Q` over `R` on
`M` transports to the quadratic form `Q.transport f` over `S` on `M'`, given by
`x ↦ σ (Q (f.symm x))`; thus `Q.transport f (f x) = σ (Q x)`.

When `σ` comes from an isomorphism of fields `K ≃+* K'`, taking for `M'` the group `M` itself with
`K'` acting through `σ⁻¹` recovers the form `σ ∘ Q`. The transported form has the same arithmetic
as `Q`: it is nondegenerate, anisotropic, or represents `σ a` exactly when `Q` is nondegenerate,
anisotropic, or represents `a`, and two transported forms are isometric, or one injectively
represented by the other, exactly when the original forms are. This is what carries statements
about quadratic forms over one field to statements over an isomorphic copy of it, for instance to a
copy in another universe.

## Main definitions

* `QuadraticForm.transport`: the quadratic form `x ↦ σ (Q (f.symm x))` over `S` on `M'`.
* `QuadraticMap.IsometryEquiv.transport`: an isometry equivalence of forms over `R`, transported
  to an isometry equivalence of the transported forms over `S`.

## Main results

* `QuadraticForm.transport_symm_transport`, `QuadraticForm.transport_transport_symm`: transporting
  along `f` and then along `f.symm` is the identity, in both orders.
* `QuadraticForm.radical_transport`: the radical of the transported form is the image of the
  radical.
* `QuadraticForm.nondegenerate_transport_iff`, `QuadraticForm.anisotropic_transport_iff`,
  `QuadraticForm.represents_transport_iff`: nondegeneracy, anisotropy, and representation of
  scalars are invariant under transport.
* `QuadraticForm.equivalent_transport_iff`, `QuadraticForm.isRepresentedBy_transport_iff`: the
  transported forms are isometric, or one is injectively represented by the other, exactly when
  the original forms are.
-/

public section

open QuadraticMap

universe u v

namespace QuadraticForm

variable {R S : Type*} [CommRing R] [CommRing S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M : Type u} {M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module S M']

/-- A ring homomorphism with a two-sided inverse is injective. -/
private theorem injective_of_invPair {σ : R →+* S} (σ' : S →+* R) [RingHomInvPair σ σ'] :
    Function.Injective σ :=
  Function.LeftInverse.injective fun _ ↦ RingHomInvPair.comp_apply_eq (σ' := σ')

/-- The polar of `x ↦ σ (Q (f.symm x))` is the transport of the polar of `Q`. -/
private theorem polar_comp_symm (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x y : M') :
    polar (fun x ↦ σ (Q (f.symm x))) x y = σ (polar Q (f.symm x) (f.symm y)) := by
  simp only [polar, map_add, map_sub]

/-- The transport of a quadratic form `Q` over `R` on `M` along a `σ`-semilinear equivalence
`f : M ≃ₛₗ[σ] M'`: the quadratic form `x ↦ σ (Q (f.symm x))` over `S` on `M'`. -/
def transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) : QuadraticForm S M' :=
  QuadraticMap.ofPolar (fun x ↦ σ (Q (f.symm x)))
    (fun a x ↦ by
      rw [map_smulₛₗ, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        RingHomInvPair.comp_apply_eq₂])
    (fun x x' y ↦ by
      simp only [polar_comp_symm, map_add, QuadraticMap.polar_add_left])
    (fun a x y ↦ by
      rw [polar_comp_symm, polar_comp_symm, map_smulₛₗ, QuadraticMap.polar_smul_left, smul_eq_mul,
        smul_eq_mul, map_mul, RingHomInvPair.comp_apply_eq₂])

/-- The transported form is `x ↦ σ (Q (f.symm x))`. -/
@[simp]
theorem transport_apply (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x : M') :
    Q.transport f x = σ (Q (f.symm x)) :=
  (rfl)

/-- The transported form takes the value `σ (Q x)` at the image `f x`. -/
theorem transport_apply_apply (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x : M) :
    Q.transport f (f x) = σ (Q x) := by
  simp

/-- The polar of the transported form is the transport of the polar. -/
@[simp]
theorem polar_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x y : M') :
    polar (Q.transport f) x y = σ (polar Q (f.symm x) (f.symm y)) :=
  polar_comp_symm f Q x y

/-- Transporting along the identity does nothing. -/
@[simp]
theorem transport_refl (Q : QuadraticForm R M) : Q.transport (LinearEquiv.refl R M) = Q := by
  ext
  simp

/-- Transporting along `f` and then back along `f.symm` recovers the original form. -/
@[simp]
theorem transport_symm_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).transport f.symm = Q := by
  ext
  simp

/-- Transporting along `f.symm` and then along `f` recovers the original form. -/
@[simp]
theorem transport_transport_symm (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm S M') :
    (Q.transport f.symm).transport f = Q := by
  simpa using transport_symm_transport f.symm Q

/-- The transported form represents `σ a` exactly when the original form represents `a`. -/
@[simp]
theorem represents_transport_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (a : R) :
    (Q.transport f).Represents (σ a) ↔ Q.Represents a := by
  rw [represents_iff, represents_iff]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨f.symm x, injective_of_invPair σ' hx⟩, fun ⟨x, hx⟩ ↦ ⟨f x, by simp [hx]⟩⟩

/-- The transported form is anisotropic exactly when the original form is. -/
@[simp]
theorem anisotropic_transport_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).Anisotropic ↔ Q.Anisotropic := by
  simp only [Anisotropic, transport_apply, f.symm.surjective.forall,
    map_eq_zero_iff _ (injective_of_invPair σ'), LinearEquiv.map_eq_zero_iff]

/-- The radical of the transported form is the image of the radical of the original form. -/
theorem radical_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).radical = Q.radical.map (f : M →ₛₗ[σ] M') := by
  ext x
  rw [Submodule.mem_map_equiv, mem_radical_iff', mem_radical_iff']
  simp only [transport_apply, f.symm.surjective.forall, ← map_add,
    map_eq_zero_iff _ (injective_of_invPair σ'), (injective_of_invPair σ').eq_iff]

/-- The kernel of the polar bilinear map of the transported form is the image of the kernel of
the polar bilinear map of the original form. -/
theorem ker_polarBilin_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    LinearMap.ker (Q.transport f).polarBilin =
      (LinearMap.ker Q.polarBilin).map (f : M →ₛₗ[σ] M') := by
  ext x
  simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.ext_iff,
    polarBilin_apply_apply, LinearMap.zero_apply, polar_transport, f.symm.surjective.forall,
    map_eq_zero_iff _ (injective_of_invPair σ')]

/-- The transported form is nondegenerate exactly when the original form is. -/
@[simp]
theorem nondegenerate_transport_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).Nondegenerate ↔ Q.Nondegenerate := by
  have hrank : Cardinal.lift.{u} (Module.rank S (LinearMap.ker (Q.transport f).polarBilin)) =
      Cardinal.lift.{v} (Module.rank R (LinearMap.ker Q.polarBilin)) := by
    rw [ker_polarBilin_transport]
    exact (lift_rank_eq_of_equiv_equiv σ
      ((f.submoduleMap (LinearMap.ker Q.polarBilin)).toAddEquiv)
      ⟨injective_of_invPair σ', RingHomSurjective.is_surjective⟩
      fun r m ↦ (f.submoduleMap _).map_smulₛₗ r m).symm
  have hrad : (Q.transport f).radical = ⊥ ↔ Q.radical = ⊥ := by
    rw [radical_transport, Submodule.map_eq_bot_iff]
  have hle : Module.rank S (LinearMap.ker (Q.transport f).polarBilin) ≤ 1 ↔
      Module.rank R (LinearMap.ker Q.polarBilin) ≤ 1 := by
    rw [← Cardinal.lift_le_one_iff, hrank, Cardinal.lift_le_one_iff]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨hrad.mp h₁, hle.mp h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨hrad.mpr h₁, hle.mpr h₂⟩⟩

section Isometry

variable {M₁ M₂ M₁' M₂' : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₁'] [Module S M₁'] [AddCommGroup M₂'] [Module S M₂']
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- An isometry equivalence `e` between quadratic forms over `R` transports, along
`σ`-semilinear equivalences `f₁` and `f₂`, to the isometry equivalence `f₂ ∘ e ∘ f₁.symm` between
the transported forms over `S`. -/
def _root_.QuadraticMap.IsometryEquiv.transport (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).IsometryEquiv (Q₂.transport f₂) where
  toLinearEquiv := (f₁.symm.trans e.toLinearEquiv).trans f₂
  map_app' x := by simp

@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.transport_apply (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') (x : M₁') :
    e.transport f₁ f₂ x = f₂ (e (f₁.symm x)) :=
  (rfl)

/-- Isometric forms over `R` have isometric transports over `S`. -/
theorem _root_.QuadraticMap.Equivalent.transport (h : Q₁.Equivalent Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).Equivalent (Q₂.transport f₂) :=
  h.map (·.transport f₁ f₂)

/-- Two transported forms are isometric exactly when the original forms are. -/
@[simp]
theorem equivalent_transport_iff (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).Equivalent (Q₂.transport f₂) ↔ Q₁.Equivalent Q₂ :=
  ⟨fun h ↦ by simpa using h.transport f₁.symm f₂.symm, fun h ↦ h.transport f₁ f₂⟩

/-- If `Q₁` is injectively represented by `Q₂` over `R`, then the transport of `Q₁` is injectively
represented by the transport of `Q₂` over `S`. -/
theorem _root_.QuadraticMap.IsRepresentedBy.transport (h : Q₁.IsRepresentedBy Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).IsRepresentedBy (Q₂.transport f₂) := by
  obtain ⟨g, hg, hQ⟩ := (isRepresentedBy_iff Q₁ Q₂).mp h
  refine (isRepresentedBy_iff _ _).mpr
    ⟨(f₂ : M₂ →ₛₗ[σ] M₂').comp (g.comp (f₁.symm : M₁' →ₛₗ[σ'] M₁)), ?_, fun x ↦ ?_⟩
  · exact f₂.injective.comp (hg.comp f₁.symm.injective)
  · simp [hQ]

/-- The transport of `Q₁` is injectively represented by the transport of `Q₂` exactly when `Q₁` is
injectively represented by `Q₂`. -/
@[simp]
theorem isRepresentedBy_transport_iff (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).IsRepresentedBy (Q₂.transport f₂) ↔ Q₁.IsRepresentedBy Q₂ :=
  ⟨fun h ↦ by simpa using h.transport f₁.symm f₂.symm, fun h ↦ h.transport f₁ f₂⟩

end Isometry

end QuadraticForm
