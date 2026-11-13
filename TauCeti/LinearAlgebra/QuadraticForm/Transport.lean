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

* `QuadraticMap.transport`: the quadratic form `x ↦ σ (Q (f.symm x))` over `S` on `M'`.
* `QuadraticMap.Isometry.transport`: transport of form-preserving linear maps.
* `QuadraticMap.IsometryEquiv.transport`: an isometry equivalence of forms over `R`, transported
  to an isometry equivalence of the transported forms over `S`.

## Main results

* `QuadraticMap.transport_symm_transport`, `QuadraticMap.transport_transport_symm`: transporting
  along `f` and then along `f.symm` is the identity, in both orders.
* `QuadraticMap.radical_transport`: the radical of the transported form is the image of the
  radical.
* `QuadraticMap.nondegenerate_transport_iff`, `QuadraticMap.anisotropic_transport_iff`,
  `QuadraticMap.represents_transport_iff`: nondegeneracy, anisotropy, and representation of
  scalars are invariant under transport.
* `QuadraticMap.equivalent_transport_iff`, `QuadraticMap.isRepresentedBy_transport_iff`: the
  transported forms are isometric, or one is injectively represented by the other, exactly when
  the original forms are.
-/

public section

universe u v

namespace QuadraticMap

section Semiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M : Type u} {M' : Type v} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module S M']

/-- The transport of a quadratic form `Q` over `R` on `M` along a `σ`-semilinear equivalence
`f : M ≃ₛₗ[σ] M'`: the quadratic form `x ↦ σ (Q (f.symm x))` over `S` on `M'`. -/
def transport (Q : QuadraticForm R M) (f : M ≃ₛₗ[σ] M') : QuadraticForm S M' where
  toFun x := σ (Q (f.symm x))
  toFun_smul a x := by
    rw [map_smulₛₗ, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      RingHomInvPair.comp_apply_eq₂]
  exists_companion' := by
    obtain ⟨B, hB⟩ := Q.exists_companion
    refine ⟨LinearMap.mk₂ S (fun x y ↦ σ (B (f.symm x) (f.symm y)))
      (fun x y z ↦ ?_) (fun a x y ↦ ?_) (fun x y z ↦ ?_) (fun a x y ↦ ?_), ?_⟩
    · simp
    · simp [map_smulₛₗ, smul_eq_mul]
    · simp
    · simp [map_smulₛₗ, smul_eq_mul]
    · intro x y
      simpa using congrArg σ (hB (f.symm x) (f.symm y))

/-- The transported form is `x ↦ σ (Q (f.symm x))`. -/
@[simp]
theorem transport_apply (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x : M') :
    Q.transport f x = σ (Q (f.symm x)) :=
  (rfl)

/-- The transported form takes the value `σ (Q x)` at the image `f x`. -/
theorem transport_apply_apply (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x : M) :
    Q.transport f (f x) = σ (Q x) := by
  simp

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

@[simp]
theorem transport_zero (f : M ≃ₛₗ[σ] M') : (0 : QuadraticForm R M).transport f = 0 := by
  ext
  simp

@[simp]
theorem transport_add (f : M ≃ₛₗ[σ] M') (Q P : QuadraticForm R M) :
    (Q + P).transport f = Q.transport f + P.transport f := by
  ext
  simp

@[simp]
theorem transport_smul (f : M ≃ₛₗ[σ] M') (a : R) (Q : QuadraticForm R M) :
    (a • Q).transport f = σ a • Q.transport f := by
  ext
  simp [smul_eq_mul]

/-- Transport along a fixed semilinear equivalence reflects equality of forms. -/
@[simp]
theorem transport_inj (f : M ≃ₛₗ[σ] M') (Q P : QuadraticForm R M) :
    Q.transport f = P.transport f ↔ Q = P := by
  constructor
  · intro h
    simpa using congrArg (fun T ↦ T.transport f.symm) h
  · rintro rfl
    rfl

@[simp]
theorem transport_eq_zero (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    Q.transport f = 0 ↔ Q = 0 := by
  rw [← transport_zero f, transport_inj]

/-- Successive transports agree with transport along the composite semilinear equivalence. -/
theorem transport_trans {T : Type*} [CommSemiring T]
    {τ : S →+* T} {τ' : T →+* S} [RingHomInvPair τ τ'] [RingHomInvPair τ' τ]
    {ρ : R →+* T} {ρ' : T →+* R} [RingHomInvPair ρ ρ'] [RingHomInvPair ρ' ρ]
    [RingHomCompTriple σ τ ρ] [RingHomCompTriple τ' σ' ρ']
    {M'' : Type*} [AddCommMonoid M''] [Module T M'']
    (Q : QuadraticForm R M) (f : M ≃ₛₗ[σ] M') (g : M' ≃ₛₗ[τ] M'') :
    (Q.transport f).transport g = Q.transport (f.trans g) := by
  ext
  simp [RingHomCompTriple.comp_apply]

/-- The transported form represents a scalar exactly when the original form represents its
image under the inverse ring homomorphism. -/
@[simp]
theorem represents_transport_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (b : S) :
    (Q.transport f).Represents b ↔ Q.Represents (σ' b) := by
  rw [represents_iff, represents_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨f.symm x, by simpa using congrArg σ' hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨f x, by simp [hx]⟩

/-- The transported form represents `σ a` exactly when the original form represents `a`. -/
theorem represents_transport_map_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (a : R) :
    (Q.transport f).Represents (σ a) ↔ Q.Represents a := by
  simp

/-- The transported form is anisotropic exactly when the original form is. -/
@[simp]
theorem anisotropic_transport_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).Anisotropic ↔ Q.Anisotropic := by
  simp only [Anisotropic, transport_apply, f.symm.surjective.forall,
    map_eq_zero_iff σ (RingHomInvPair.toRingEquiv σ σ').injective, LinearEquiv.map_eq_zero_iff]

end Semiring

section Ring

variable {R S : Type*} [CommRing R] [CommRing S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M : Type u} {M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module S M']

@[simp]
theorem transport_neg (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (-Q).transport f = -Q.transport f := by
  ext
  simp

@[simp]
theorem transport_sub (f : M ≃ₛₗ[σ] M') (Q P : QuadraticForm R M) :
    (Q - P).transport f = Q.transport f - P.transport f := by
  ext
  simp

/-- The polar of the transported form is the transport of the polar. -/
@[simp]
theorem polar_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) (x y : M') :
    polar (Q.transport f) x y = σ (polar Q (f.symm x) (f.symm y)) := by
  simp [polar]

/-- The radical of the transported form is the image of the radical of the original form. -/
theorem radical_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).radical = Q.radical.map (f : M →ₛₗ[σ] M') := by
  ext x
  rw [Submodule.mem_map_equiv, mem_radical_iff', mem_radical_iff']
  simp only [transport_apply, f.symm.surjective.forall, ← map_add,
    map_eq_zero_iff σ (RingHomInvPair.toRingEquiv σ σ').injective,
    Function.Injective.eq_iff (f := σ) (RingHomInvPair.toRingEquiv σ σ').injective]

/-- The kernel of the polar bilinear map of the transported form is the image of the kernel of
the polar bilinear map of the original form. -/
theorem ker_polarBilin_transport (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    LinearMap.ker (Q.transport f).polarBilin =
      (LinearMap.ker Q.polarBilin).map (f : M →ₛₗ[σ] M') := by
  ext x
  simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.ext_iff,
    polarBilin_apply_apply, LinearMap.zero_apply, polar_transport, f.symm.surjective.forall,
    map_eq_zero_iff σ (RingHomInvPair.toRingEquiv σ σ').injective]

/-- The transported form is nondegenerate exactly when the original form is. -/
@[simp]
theorem nondegenerate_transport_iff (f : M ≃ₛₗ[σ] M') (Q : QuadraticForm R M) :
    (Q.transport f).Nondegenerate ↔ Q.Nondegenerate := by
  have hrank : Cardinal.lift.{u} (Module.rank S (LinearMap.ker (Q.transport f).polarBilin)) =
      Cardinal.lift.{v} (Module.rank R (LinearMap.ker Q.polarBilin)) := by
    rw [ker_polarBilin_transport]
    exact (lift_rank_eq_of_equiv_equiv σ
      ((f.submoduleMap (LinearMap.ker Q.polarBilin)).toAddEquiv)
      (RingHomInvPair.toRingEquiv σ σ').bijective
      fun r m ↦ (f.submoduleMap _).map_smulₛₗ r m).symm
  have hrad : (Q.transport f).radical = ⊥ ↔ Q.radical = ⊥ := by
    rw [radical_transport, Submodule.map_eq_bot_iff]
  have hle : Module.rank S (LinearMap.ker (Q.transport f).polarBilin) ≤ 1 ↔
      Module.rank R (LinearMap.ker Q.polarBilin) ≤ 1 := by
    rw [← Cardinal.lift_le_one_iff, hrank, Cardinal.lift_le_one_iff]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨hrad.mp h₁, hle.mp h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨hrad.mpr h₁, hle.mpr h₂⟩⟩

end Ring

section Isometry

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M₁ M₂ M₁' M₂' : Type*} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₁'] [Module S M₁'] [AddCommMonoid M₂'] [Module S M₂']
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- An isometry transports to the isometry `f₂ ∘ g ∘ f₁.symm` of the transported forms. -/
def Isometry.transport (g : Q₁ →qᵢ Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    Q₁.transport f₁ →qᵢ Q₂.transport f₂ where
  toLinearMap := (f₂ : M₂ →ₛₗ[σ] M₂').comp
    (g.toLinearMap.comp (f₁.symm : M₁' →ₛₗ[σ'] M₁))
  map_app' x := by simp

@[simp]
theorem Isometry.transport_apply (g : Q₁ →qᵢ Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') (x : M₁') :
    g.transport f₁ f₂ x = f₂ (g (f₁.symm x)) :=
  (rfl)

@[simp]
theorem Isometry.toLinearMap_transport (g : Q₁ →qᵢ Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (g.transport f₁ f₂).toLinearMap =
      (f₂ : M₂ →ₛₗ[σ] M₂').comp (g.toLinearMap.comp (f₁.symm : M₁' →ₛₗ[σ'] M₁)) :=
  (rfl)

@[simp]
theorem Isometry.id_transport (Q : QuadraticForm R M₁) (f : M₁ ≃ₛₗ[σ] M₁') :
    (Isometry.id Q).transport f f = Isometry.id (Q.transport f) := by
  ext
  simp

variable {M₃ M₃' : Type*} [AddCommMonoid M₃] [Module R M₃]
  [AddCommMonoid M₃'] [Module S M₃'] {Q₃ : QuadraticForm R M₃}

@[simp]
theorem Isometry.comp_transport (g : Q₂ →qᵢ Q₃) (h : Q₁ →qᵢ Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') (f₃ : M₃ ≃ₛₗ[σ] M₃') :
    (g.transport f₂ f₃).comp (h.transport f₁ f₂) = (g.comp h).transport f₁ f₃ := by
  ext
  simp

/-- An isometry equivalence `e` between quadratic forms over `R` transports, along
`σ`-semilinear equivalences `f₁` and `f₂`, to the isometry equivalence `f₂ ∘ e ∘ f₁.symm` between
the transported forms over `S`. -/
def IsometryEquiv.transport (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).IsometryEquiv (Q₂.transport f₂) where
  toLinearEquiv := (f₁.symm.trans e.toLinearEquiv).trans f₂
  map_app' := (e.toIsometry.transport f₁ f₂).map_app

@[simp]
theorem IsometryEquiv.transport_apply (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') (x : M₁') :
    e.transport f₁ f₂ x = f₂ (e (f₁.symm x)) :=
  (rfl)

@[simp]
theorem IsometryEquiv.toLinearEquiv_transport (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (e.transport f₁ f₂).toLinearEquiv = (f₁.symm.trans e.toLinearEquiv).trans f₂ :=
  (rfl)

@[simp]
theorem IsometryEquiv.toIsometry_transport (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (e.transport f₁ f₂).toIsometry = e.toIsometry.transport f₁ f₂ :=
  (rfl)

/-- Inverting a transported isometry equivalence exchanges the two transport maps. -/
@[simp]
theorem IsometryEquiv.symm_transport (e : Q₁.IsometryEquiv Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (e.transport f₁ f₂).symm = e.symm.transport f₂ f₁ :=
  (rfl)

@[simp]
theorem IsometryEquiv.refl_transport (Q : QuadraticForm R M₁) (f : M₁ ≃ₛₗ[σ] M₁') :
    (IsometryEquiv.refl Q).transport f f = IsometryEquiv.refl (Q.transport f) := by
  apply DFunLike.ext
  intro x
  exact f.apply_symm_apply x

@[simp]
theorem IsometryEquiv.trans_transport (e : Q₁.IsometryEquiv Q₂) (d : Q₂.IsometryEquiv Q₃)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') (f₃ : M₃ ≃ₛₗ[σ] M₃') :
    (e.transport f₁ f₂).trans (d.transport f₂ f₃) = (e.trans d).transport f₁ f₃ := by
  apply DFunLike.ext
  intro x
  exact congrArg (fun y ↦ f₃ (d y)) (f₂.symm_apply_apply (e (f₁.symm x)))

/-- Isometric forms over `R` have isometric transports over `S`. -/
theorem Equivalent.transport (h : Q₁.Equivalent Q₂)
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
theorem IsRepresentedBy.transport (h : Q₁.IsRepresentedBy Q₂)
    (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).IsRepresentedBy (Q₂.transport f₂) := by
  obtain ⟨g, hg, hQ⟩ := (isRepresentedBy_iff Q₁ Q₂).mp h
  refine (isRepresentedBy_iff _ _).mpr
    ⟨((⟨g, hQ⟩ : Q₁ →qᵢ Q₂).transport f₁ f₂).toLinearMap,
      f₂.injective.comp (hg.comp f₁.symm.injective), ?_⟩
  exact ((⟨g, hQ⟩ : Q₁ →qᵢ Q₂).transport f₁ f₂).map_app

/-- The transport of `Q₁` is injectively represented by the transport of `Q₂` exactly when `Q₁` is
injectively represented by `Q₂`. -/
@[simp]
theorem isRepresentedBy_transport_iff (f₁ : M₁ ≃ₛₗ[σ] M₁') (f₂ : M₂ ≃ₛₗ[σ] M₂') :
    (Q₁.transport f₁).IsRepresentedBy (Q₂.transport f₂) ↔ Q₁.IsRepresentedBy Q₂ :=
  ⟨fun h ↦ by simpa using h.transport f₁.symm f₂.symm, fun h ↦ h.transport f₁ f₂⟩

end Isometry

end QuadraticMap
