/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain

/-!
# `A∞` morphisms into DG algebras and the universal property of `Ω Tᶜ(sA)`

Let `A` be a nonunital `A∞` algebra, whose reduced bar construction `Tᶜ(sA)` is a noncounital
differential graded coalgebra (`TauCeti.AInfinityAlgebra.isNonCounitalDGCoalgebra_bar`), and let
`D` be a differential graded algebra, regarded as an `A∞` algebra with `m₁ = d`, `m₂` the product
and no higher operations.  The suspended Taylor components of an `A∞` morphism `f : A ⟶ D` form a
linear map `f : Tᶜ(sA) ⟶ D` raising the degree by one, and its component equation reads

`d (f z) + ∑ σ (f z') * f z'' = f (b z)`   for `Δ z = ∑ z' ⊗ z''`,

where `b` is the bar differential, `Δ` is reduced deconcatenation, and `σ : x ↦ (-1) ^ |x| x` is
the Koszul twist of `D`.  This is the twisting-cochain equation of
`TauCeti.IsTwistingCochain` after a change of sign: `τ = σ ∘ f`, that is
`τ z = (-1) ^ (|z| + 1) f z` for `z` of degree `|z|` in `Tᶜ(sA)`, satisfies
`d τ + τ b + μ (τ ⊗ τ) Δ = 0`.  The sign comes from comparing the suspension sign of `m₂`, carried
by the Koszul twist of the left factor, with the Koszul sign of the tensor product of two
degree-one maps in the twisting equation.  Hence `A∞` morphisms `A ⟶ D` are the twisting cochains
`Tᶜ(sA) ⟶ D` (`TauCeti.AInfinityAlgebra.homTwistingCochainEquiv`).

Composing with the cobar universal property
`TauCeti.IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv`, `A∞` morphisms `A ⟶ D` correspond to
DG algebra maps `Ω Tᶜ(sA) ⟶ D` (`TauCeti.AInfinityAlgebra.cobarBarHomEquiv`).  The identity of
`Ω Tᶜ(sA)` corresponds to the canonical `A∞` morphism `A ⟶ Ω Tᶜ(sA)`
(`TauCeti.AInfinityAlgebra.toCobarBar`), whose Taylor components are `z ↦ (-1) ^ |z| s⁻¹ z`, and
every `A∞` morphism from `A` to a DG algebra factors uniquely through it by a DG algebra map
(`TauCeti.AInfinityAlgebra.bijective_comp_toCobarBar`).  Since `Tᶜ(sA)` is the coaugmentation
coideal of the bar construction of the augmented algebra `R ⊕ A`, the DG algebra `Ω Tᶜ(sA)` is the
enveloping DG algebra `Ω B (R ⊕ A)`, and this is its universal property among nonunital `A∞`
morphisms out of `A`.  It holds over any commutative ring: no conilpotence, flatness or field
hypothesis is involved.

## Main definitions

* `TauCeti.AInfinityAlgebra.homTwistingCochainEquiv`: `A∞` morphisms into a DG algebra are the
  twisting cochains on the bar construction.
* `TauCeti.AInfinityAlgebra.cobarBarHomEquiv`: `A∞` morphisms into a DG algebra are the DG
  algebra maps out of the cobar construction of the bar construction.
* `TauCeti.AInfinityAlgebra.toCobarBar`: the canonical `A∞` morphism `A ⟶ Ω Tᶜ(sA)`.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_toCobarBar`: the Taylor components of the canonical morphism.
* `TauCeti.AInfinityAlgebra.cobarBarHomEquiv_symm_apply`: the `A∞` morphism of a DG algebra map
  `Ω Tᶜ(sA) ⟶ D` is that map composed with the canonical morphism.
* `TauCeti.AInfinityAlgebra.bijective_comp_toCobarBar`: **the universal property of `Ω Tᶜ(sA)`**.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for twisting cochains, the bar--cobar adjunction and the enveloping
  differential graded algebra `Ω B A` of an augmented `A∞` algebra.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for twisting morphisms and the bar--cobar adjunction.
-/

public section

open scoped TensorProduct

namespace TauCeti.AInfinityAlgebra

universe uR uA uD

variable {R : Type uR} {A : Type uA} {D : Type uD} [CommRing R] [AddCommGroup A] [Module R A]
  [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {d : D →ₗ[R] D}
  (𝒜 : AInfinityAlgebra R A) (hD : IsDGAlgebra 𝒟 d)

/-! ### `A∞` morphisms into a DG algebra as twisting cochains -/

/-- The Taylor map of a DG algebra after the Taylor expansion of `g`: the differential of `g` plus
the product of the two halves of each cut, the left one twisted. -/
private theorem taylor_coalgHom_apply (g : ReducedTensorWords R A →ₗ[R] D)
    (z : ReducedTensorWords R A) :
    hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R g z) =
      d (g z) + LinearMap.mul' R D (TensorProduct.map
        ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) g
          (ReducedTensorWords.deconcatenation R A z)) := by
  rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_taylor, LinearMap.add_apply, LinearMap.comp_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R D), ReducedTensorWords.letter_comp_coalgHom,
    LinearMap.comp_apply, LinearMap.comp_apply,
    (ReducedTensorWords.isCoalgHom_coalgHom g).deconcatenation_apply, TensorProduct.map_map,
    LinearMap.comp_assoc, ReducedTensorWords.letter_comp_coalgHom]

/-- Suspended Taylor components into a DG algebra raise the unsuspended degree by one, so they
anticommute with the Koszul twists. -/
private theorem apply_koszulTwist (g : ReducedTensorWords R A →ₗ[R] D)
    (hg : LinearMap.IsHomogeneous g (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.shift 1).piece 0)
    (z : ReducedTensorWords R A) :
    g ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1 (g z) := by
  rw [← ReducedTensorWords.grading_piece] at hg
  have h := hg.koszulTwist_apply 1 z
  rw [InternalGrading.koszulTwist_one_shift_one, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading]
    at h
  simpa using h.symm

/-- The Koszul twist of the twisting-cochain expression of `σ ∘ g` is minus the defect of the
component equation of `g`. -/
private theorem koszulTwist_twistingSum (g : ReducedTensorWords R A →ₗ[R] D)
    (hg : ∀ z, g ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1 (g z))
    (z : ReducedTensorWords R A) :
    (InternalGrading.ofDecomposition 𝒟).koszulTwist 1
        (d (((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) z) +
          ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) (𝒜.barDifferential z) +
          LinearMap.mul' R D (TensorProduct.map
            (((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) ∘ₗ
              (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1)
            ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g)
            (ReducedTensorWords.deconcatenation R A z))) =
      g (𝒜.barDifferential z) - hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.taylor
        (ReducedTensorWords.coalgHom R g z) := by
  have hq (w : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) :
      (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 (LinearMap.mul' R D (TensorProduct.map
          (((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) ∘ₗ
            (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1)
          ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) w)) =
        -LinearMap.mul' R D
          (TensorProduct.map ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) g w) := by
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply, hg,
        InternalGrading.koszulTwist_ofDecomposition_mul, InternalGrading.koszulTwist_koszulTwist,
        map_neg, neg_mul]
    | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  rw [taylor_coalgHom_apply hD, map_add, map_add, hq, LinearMap.comp_apply, LinearMap.comp_apply,
    InternalGrading.koszulTwist_koszulTwist, hD.toIsNonUnitalDGAlgebra.koszulTwist_map,
    InternalGrading.koszulTwist_koszulTwist]
  abel

private theorem koszulTwist_comp_koszulTwist_comp (g : ReducedTensorWords R A →ₗ[R] D) :
    (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ
      (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g = g := by
  rw [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self, LinearMap.id_comp]

/-- `σ ∘ g` raises the degree by one exactly when `g` has degree zero for the suspended
gradings. -/
private theorem isHomogeneous_koszulTwist_comp_iff (g : ReducedTensorWords R A →ₗ[R] D) :
    LinearMap.IsHomogeneous ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g)
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece 𝒟 1 ↔
      LinearMap.IsHomogeneous g (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
        (hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.shift 1).piece 0 := by
  have hσ {x : D} {k : ℤ} : (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 x ∈ 𝒟 k ↔ x ∈ 𝒟 k :=
    ⟨fun h ↦ by simpa using InternalGrading.koszulTwist_mem_ofDecomposition 𝒟 h 1,
      fun h ↦ InternalGrading.koszulTwist_mem_ofDecomposition 𝒟 h 1⟩
  simp only [LinearMap.isHomogeneous_def, ReducedTensorWords.grading_piece,
    InternalGrading.shift_piece, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
    InternalGrading.ofDecomposition_piece, LinearMap.comp_apply, add_zero, hσ]

/-- For suspended Taylor components `g` of degree zero, `σ ∘ g` is a twisting cochain exactly when
`g` satisfies the component equation of an `A∞` morphism. -/
private theorem isTwistingCochain_koszulTwist_comp_iff (g : ReducedTensorWords R A →ₗ[R] D)
    (hg : LinearMap.IsHomogeneous g (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.shift 1).piece 0) :
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential 𝒟 d
        ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) ↔
      hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.taylor ∘ₗ ReducedTensorWords.coalgHom R g =
        g ∘ₗ 𝒜.barDifferential := by
  have key := koszulTwist_twistingSum 𝒜 hD g (apply_koszulTwist 𝒜 hD g hg)
  constructor
  · refine fun h ↦ LinearMap.ext fun z ↦ ?_
    have hz := key z
    rw [h.equation z, map_zero, eq_comm, sub_eq_zero] at hz
    exact hz.symm
  · refine fun h ↦ ⟨(isHomogeneous_koszulTwist_comp_iff 𝒜 hD g).2 hg, fun z ↦ ?_⟩
    have hz := congrArg ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1) (key z)
    rwa [← LinearMap.comp_apply (hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.taylor), h,
      LinearMap.comp_apply g, sub_self, map_zero, InternalGrading.koszulTwist_koszulTwist] at hz

/-- **`A∞` morphisms into a DG algebra are the twisting cochains on the bar construction.**  An
`A∞` morphism `f : A ⟶ D` corresponds to the twisting cochain `σ ∘ f : Tᶜ(sA) ⟶ D`, its suspended
Taylor components followed by the Koszul twist `σ : x ↦ (-1) ^ |x| x` of `D`. -/
noncomputable def homTwistingCochainEquiv :
    AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra ≃
      {τ : ReducedTensorWords R A →ₗ[R] D // IsTwistingCochain
        (ReducedTensorWords.grading (𝒜.grading.shift 1)) (ReducedTensorWords.deconcatenation R A)
        𝒜.barDifferential 𝒟 d τ} where
  toFun f := ⟨(InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ f.taylor,
    (isTwistingCochain_koszulTwist_comp_iff 𝒜 hD _ f.isHomogeneous_taylor).2 <| by
      rw [← f.barMap_eq_coalgHom]
      exact f.taylor_comp_barMap⟩
  invFun τ :=
    have hτ := (isHomogeneous_koszulTwist_comp_iff 𝒜 hD
      ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ τ.val)).1 <| by
        rw [koszulTwist_comp_koszulTwist_comp]
        exact τ.property.isHomogeneous
    AInfinityHom.ofTaylor ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ τ.val) hτ <|
      (isTwistingCochain_koszulTwist_comp_iff 𝒜 hD _ hτ).1 <| by
        rw [koszulTwist_comp_koszulTwist_comp]
        exact τ.property
  left_inv f := AInfinityHom.ext <| by
    rw [AInfinityHom.taylor_ofTaylor, koszulTwist_comp_koszulTwist_comp]
  right_inv τ := Subtype.ext <| by
    simp only [AInfinityHom.taylor_ofTaylor, koszulTwist_comp_koszulTwist_comp]

/-- The twisting cochain of an `A∞` morphism is its Taylor map followed by the Koszul twist. -/
@[simp]
theorem homTwistingCochainEquiv_apply
    (f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) (z : ReducedTensorWords R A) :
    (homTwistingCochainEquiv 𝒜 hD f).val z =
      (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 (f.taylor z) := (rfl)

/-- The Taylor map of the `A∞` morphism of a twisting cochain is the twisting cochain followed by
the Koszul twist. -/
@[simp]
theorem taylor_homTwistingCochainEquiv_symm (τ : {τ : ReducedTensorWords R A →ₗ[R] D //
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential 𝒟 d τ}) :
    ((homTwistingCochainEquiv 𝒜 hD).symm τ).taylor =
      (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ τ.val := by
  simp only [homTwistingCochainEquiv, Equiv.coe_fn_symm_mk, AInfinityHom.taylor_ofTaylor]

/-! ### The universal property of `Ω Tᶜ(sA)` -/

/-- **`A∞` morphisms into a DG algebra are the DG algebra maps out of `Ω Tᶜ(sA)`.**  An `A∞`
morphism `f : A ⟶ D` corresponds to the DG algebra map sending the desuspended generator `s⁻¹ z`
to `-σ (f z)` (`cobarBarHomEquiv_apply_ι`). -/
noncomputable def cobarBarHomEquiv :
    AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra ≃
      DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD :=
  (homTwistingCochainEquiv 𝒜 hD).trans
    (𝒜.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hD).symm

/-- The DG algebra map of an `A∞` morphism `f` sends `s⁻¹ z` to `-σ (f z)`. -/
@[simp]
theorem cobarBarHomEquiv_apply_ι
    (f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) (z : ReducedTensorWords R A) :
    cobarBarHomEquiv 𝒜 hD f (TensorAlgebra.ι R z) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1 (f.taylor z) := by
  simp [cobarBarHomEquiv]

/-- The Taylor map of the `A∞` morphism of a DG algebra map `φ : Ω Tᶜ(sA) ⟶ D` is
`z ↦ -σ (φ (s⁻¹ z))`. -/
@[simp]
theorem taylor_cobarBarHomEquiv_symm
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD) :
    ((cobarBarHomEquiv 𝒜 hD).symm φ).taylor =
      -((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ
        (φ : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] D) ∘ₗ TensorAlgebra.ι R) := by
  ext z
  simp [cobarBarHomEquiv]

/-- The canonical `A∞` morphism `A ⟶ Ω Tᶜ(sA)`, corresponding to the identity of `Ω Tᶜ(sA)`
under `cobarBarHomEquiv`. -/
noncomputable def toCobarBar :
    AInfinityHom 𝒜 (IsDGAlgebra.toIsNonUnitalDGAlgebra
      𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential).toAInfinityAlgebra :=
  (cobarBarHomEquiv 𝒜 _).symm (DGAlgHom.id _)

/-- The canonical morphism `A ⟶ Ω Tᶜ(sA)` corresponds to the identity of `Ω Tᶜ(sA)`. -/
@[simp]
theorem cobarBarHomEquiv_toCobarBar :
    cobarBarHomEquiv 𝒜 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜.toCobarBar = DGAlgHom.id _ :=
  Equiv.apply_symm_apply _ _

/-- The Taylor components of the canonical morphism `A ⟶ Ω Tᶜ(sA)` are
`z ↦ (-1) ^ |z| s⁻¹ z`. -/
@[simp]
theorem taylor_toCobarBar :
    𝒜.toCobarBar.taylor =
      TensorAlgebra.ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 := by
  ext z
  simp [toCobarBar, InternalGrading.koszulTwist_shift]

/-- The `A∞` morphism of a DG algebra map `φ : Ω Tᶜ(sA) ⟶ D` is `φ` composed with the canonical
morphism `A ⟶ Ω Tᶜ(sA)`. -/
theorem cobarBarHomEquiv_symm_apply
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD) :
    (cobarBarHomEquiv 𝒜 hD).symm φ =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobarBar := by
  refine AInfinityHom.ext (LinearMap.ext fun z ↦ ?_)
  -- `φ` preserves degrees, so it commutes with the Koszul twists.
  have h : (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 (φ (TensorAlgebra.ι R z)) =
      -φ (TensorAlgebra.ι R
        ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z)) := by
    simpa [InternalGrading.koszulTwist_shift] using
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.isHomogeneous.koszulTwist_apply 1
        (TensorAlgebra.ι R z)
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_toCobarBar,
    taylor_cobarBarHomEquiv_symm]
  simp [h]

/-- **The universal property of `Ω Tᶜ(sA)`**: every `A∞` morphism from `A` to a DG algebra `D` is
the composite of the canonical morphism `A ⟶ Ω Tᶜ(sA)` with exactly one DG algebra map
`Ω Tᶜ(sA) ⟶ D`. -/
theorem bijective_comp_toCobarBar :
    Function.Bijective fun φ : DGAlgHom
        𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD ↦
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobarBar := by
  convert (cobarBarHomEquiv 𝒜 hD).symm.bijective using 1
  funext φ
  exact (cobarBarHomEquiv_symm_apply 𝒜 hD φ).symm

end TauCeti.AInfinityAlgebra
