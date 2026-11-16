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
`D` be a nonunital differential graded algebra, regarded as an `A∞` algebra with `m₁ = d`, `m₂` the
product and no higher operations.  The suspended Taylor components of an `A∞` morphism `f : A ⟶ D`
form a linear map `f : Tᶜ(sA) ⟶ D` raising the degree by one, and its component equation reads

`d (f z) + ∑ σ (f z') * f z'' = f (b z)`   for `Δ z = ∑ z' ⊗ z''`,

where `b` is the bar differential, `Δ` is reduced deconcatenation, and `σ : x ↦ (-1) ^ |x| x` is
the Koszul twist of `D`.  This is the twisting-cochain equation of
`TauCeti.IsTwistingCochain` after a change of sign: `τ = σ ∘ f`, that is
`τ z = (-1) ^ (|z| + 1) f z` for `z` of degree `|z|` in `Tᶜ(sA)`, satisfies
`d τ + τ b + μ (τ ⊗ τ) Δ = 0`.  The sign comes from comparing the suspension sign of `m₂`, carried
by the Koszul twist of the left factor, with the Koszul sign of the tensor product of two
degree-one maps in the twisting equation.  Hence `A∞` morphisms `A ⟶ D` into any nonunital DG
algebra are the twisting cochains `Tᶜ(sA) ⟶ D` (`TauCeti.AInfinityAlgebra.homTwistingCochainEquiv`),
naturally in both `A` and `D`.

When `D` is unital, composing with the cobar universal property
`TauCeti.IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv`, `A∞` morphisms `A ⟶ D` correspond to
DG algebra maps `Ω Tᶜ(sA) ⟶ D` (`TauCeti.AInfinityAlgebra.cobarBarHomEquiv`).  The identity of
`Ω Tᶜ(sA)` corresponds to the canonical `A∞` morphism `A ⟶ Ω Tᶜ(sA)`
(`TauCeti.AInfinityAlgebra.toCobarBar`), whose Taylor components are `z ↦ (-1) ^ |z| s⁻¹ z`, and
every `A∞` morphism from `A` to a DG algebra factors uniquely through it by a DG algebra map
(`TauCeti.AInfinityAlgebra.bijective_comp_toCobarBar`).  Applying `cobarMap` to the induced bar
coalgebra map makes `Ω Tᶜ(s-)` functorial (`TauCeti.AInfinityHom.cobarBarMap`) and renders the
adjunction natural in both variables.  Since `Tᶜ(sA)` is the coaugmentation
coideal of the bar construction of the augmented algebra `R ⊕ A`, the DG algebra `Ω Tᶜ(sA)` is the
enveloping DG algebra `Ω B (R ⊕ A)`, and this is its universal property among nonunital `A∞`
morphisms out of `A`.  It holds over any commutative ring: no conilpotence, flatness or field
hypothesis is involved.

## Main definitions

* `TauCeti.AInfinityAlgebra.homTwistingCochainEquiv`: `A∞` morphisms into a nonunital DG algebra
  are the twisting cochains on the bar construction.
* `TauCeti.AInfinityAlgebra.cobarBarHomEquiv`: `A∞` morphisms into a DG algebra are the DG
  algebra maps out of the cobar construction of the bar construction.
* `TauCeti.AInfinityAlgebra.toCobarBar`: the canonical `A∞` morphism `A ⟶ Ω Tᶜ(sA)`.
* `TauCeti.AInfinityHom.cobarBarMap`: functoriality `Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA')` along `A∞` morphisms.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_toCobarBar`: the Taylor components of the canonical morphism.
* `TauCeti.AInfinityAlgebra.cobarBarHomEquiv_symm_apply`: the `A∞` morphism of a DG algebra map
  `Ω Tᶜ(sA) ⟶ D` is that map composed with the canonical morphism.
* `TauCeti.AInfinityAlgebra.bijective_comp_toCobarBar`: **the universal property of `Ω Tᶜ(sA)`**.
* `TauCeti.AInfinityHom.cobarBarMap_comp_toCobarBar`: naturality of `toCobarBar` with respect to
  `cobarBarMap`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for twisting cochains, the bar--cobar adjunction and the enveloping
  differential graded algebra `Ω B A` of an augmented `A∞` algebra.
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology, Homotopy and
  Applications 3 (2001), Sections 3.4 and 3.6.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for twisting morphisms and the bar--cobar adjunction.
-/

public section

open scoped TensorProduct

namespace TauCeti.AInfinityAlgebra

universe uR uA uA' uA'' uD uE

section NonUnital

variable {R : Type uR} {A : Type uA} {D : Type uD} [CommRing R] [AddCommGroup A] [Module R A]
  [NonUnitalRing D] [Module R D] [IsScalarTower R D D] [SMulCommClass R D D]
  {𝒟 : ℤ → Submodule R D} [SetLike.GradedMul 𝒟] [DirectSum.Decomposition 𝒟] {d : D →ₗ[R] D}
  (𝒜 : AInfinityAlgebra R A) (hD : IsNonUnitalDGAlgebra 𝒟 d)

/-! ### `A∞` morphisms into a DG algebra as twisting cochains -/

/-- The Taylor map of a DG algebra after the Taylor expansion of `g`: the differential of `g` plus
the product of the two halves of each cut, the left one twisted. -/
private theorem taylor_coalgHom_apply (g : ReducedTensorWords R A →ₗ[R] D)
    (z : ReducedTensorWords R A) :
    hD.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R g z) =
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
      (hD.toAInfinityAlgebra.grading.shift 1).piece 0)
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
      g (𝒜.barDifferential z) - hD.toAInfinityAlgebra.taylor
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
    InternalGrading.koszulTwist_koszulTwist, hD.koszulTwist_map,
    InternalGrading.koszulTwist_koszulTwist]
  abel

/-- `σ ∘ g` raises the degree by one exactly when `g` has degree zero for the suspended
gradings. -/
private theorem isHomogeneous_koszulTwist_comp_iff (g : ReducedTensorWords R A →ₗ[R] D) :
    LinearMap.IsHomogeneous ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g)
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece 𝒟 1 ↔
      LinearMap.IsHomogeneous g (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
        (hD.toAInfinityAlgebra.grading.shift 1).piece 0 := by
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
      (hD.toAInfinityAlgebra.grading.shift 1).piece 0) :
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential 𝒟 d
        ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ g) ↔
      hD.toAInfinityAlgebra.taylor ∘ₗ ReducedTensorWords.coalgHom R g =
        g ∘ₗ 𝒜.barDifferential := by
  have key := koszulTwist_twistingSum 𝒜 hD g (apply_koszulTwist 𝒜 hD g hg)
  constructor
  · refine fun h ↦ LinearMap.ext fun z ↦ ?_
    have hz := key z
    rw [h.equation z, map_zero, eq_comm, sub_eq_zero] at hz
    exact hz.symm
  · refine fun h ↦ ⟨(isHomogeneous_koszulTwist_comp_iff 𝒜 hD g).2 hg, fun z ↦ ?_⟩
    have hz := congrArg ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1) (key z)
    rwa [← LinearMap.comp_apply (hD.toAInfinityAlgebra.taylor), h,
      LinearMap.comp_apply g, sub_self, map_zero, InternalGrading.koszulTwist_koszulTwist] at hz

/-- **`A∞` morphisms into a nonunital DG algebra are the twisting cochains on the bar
construction.**  An `A∞` morphism `f : A ⟶ D` corresponds to the twisting cochain
`σ ∘ f : Tᶜ(sA) ⟶ D`, its suspended Taylor components followed by the Koszul twist
`σ : x ↦ (-1) ^ |x| x` of `D`. -/
noncomputable def homTwistingCochainEquiv :
    AInfinityHom 𝒜 hD.toAInfinityAlgebra ≃
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
        rw [InternalGrading.koszulTwist_comp_koszulTwist_comp]
        exact τ.property.isHomogeneous
    AInfinityHom.ofTaylor ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ τ.val) hτ <|
      (isTwistingCochain_koszulTwist_comp_iff 𝒜 hD _ hτ).1 <| by
        rw [InternalGrading.koszulTwist_comp_koszulTwist_comp]
        exact τ.property
  left_inv f := AInfinityHom.ext <| by
    rw [AInfinityHom.taylor_ofTaylor, InternalGrading.koszulTwist_comp_koszulTwist_comp]
  right_inv τ := Subtype.ext <| by
    simp only [AInfinityHom.taylor_ofTaylor, InternalGrading.koszulTwist_comp_koszulTwist_comp]

/-- The twisting cochain of an `A∞` morphism is its Taylor map followed by the Koszul twist. -/
@[simp]
theorem homTwistingCochainEquiv_apply
    (f : AInfinityHom 𝒜 hD.toAInfinityAlgebra) (z : ReducedTensorWords R A) :
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

/-- The linear part of `(homTwistingCochainEquiv 𝒜 hD).symm` restricts the twisted cochain to
`A`. -/
@[simp]
theorem linearPart_homTwistingCochainEquiv_symm (τ : {τ : ReducedTensorWords R A →ₗ[R] D //
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential 𝒟 d τ}) :
    ((homTwistingCochainEquiv 𝒜 hD).symm τ).linearPart =
      (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ τ.val ∘ₗ
        ReducedTensorWords.ofLetter R A :=
  LinearMap.ext fun _ ↦ by simp

/-- Precomposing an `A∞` morphism with `k : A' ⟶ A` pulls back its bar twisting cochain along
`k.barMap`. -/
theorem homTwistingCochainEquiv_comp_right {A' : Type uA'} [AddCommGroup A'] [Module R A']
    {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'} (hD : IsNonUnitalDGAlgebra 𝒟 d)
    (g : AInfinityHom 𝒜 hD.toAInfinityAlgebra) (k : AInfinityHom 𝒜' 𝒜) :
    (homTwistingCochainEquiv 𝒜' hD (g.comp k)).val =
      (homTwistingCochainEquiv 𝒜 hD g).val ∘ₗ k.barMap :=
  LinearMap.ext fun _ ↦ by simp [AInfinityHom.taylor_comp]

/-- Postcomposing an `A∞` morphism with a nonunital DG algebra morphism `ψ : D ⟶ E` pushes forward
its bar twisting cochain by `ψ`. -/
theorem homTwistingCochainEquiv_comp_left {E : Type uE} [NonUnitalRing E] [Module R E]
    [IsScalarTower R E E] [SMulCommClass R E E] {ℰ : ℤ → Submodule R E} [SetLike.GradedMul ℰ]
    [DirectSum.Decomposition ℰ] {dE : E →ₗ[R] E} {hD : IsNonUnitalDGAlgebra 𝒟 d}
    {hE : IsNonUnitalDGAlgebra ℰ dE} (ψ : NonUnitalDGAlgHom hD hE)
    (g : AInfinityHom 𝒜 hD.toAInfinityAlgebra) :
    (homTwistingCochainEquiv 𝒜 hE (ψ.toAInfinityStrictHom.toAInfinityHom.comp g)).val =
      ψ.toAInfinityStrictHom.toLinearMap ∘ₗ (homTwistingCochainEquiv 𝒜 hD g).val := by
  have hhom : LinearMap.IsHomogeneous ψ.toAInfinityStrictHom.toLinearMap
      (InternalGrading.ofDecomposition 𝒟).piece (InternalGrading.ofDecomposition ℰ).piece 0 := by
    simpa only [hD.toAInfinityAlgebra_grading, hE.toAInfinityAlgebra_grading] using
      ψ.toAInfinityStrictHom.isHomogeneous
  refine LinearMap.ext fun w ↦ ?_
  have htw := hhom.koszulTwist_apply 1 (g.taylor w)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at htw
  simp only [homTwistingCochainEquiv_apply, AInfinityStrictHom.taylor_toAInfinityHom_comp,
    LinearMap.comp_apply, htw]

end NonUnital

/-! ### The universal property of `Ω Tᶜ(sA)` -/

section Unital

variable {R : Type uR} {A : Type uA} {D : Type uD} [CommRing R] [AddCommGroup A] [Module R A]
  [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {d : D →ₗ[R] D}
  (𝒜 : AInfinityAlgebra R A) (hD : IsDGAlgebra 𝒟 d)

/-- **`A∞` morphisms into a DG algebra are the DG algebra maps out of `Ω Tᶜ(sA)`.**  An `A∞`
morphism `f : A ⟶ D` corresponds to the DG algebra map sending the desuspended generator `s⁻¹ z`
to `-σ (f z)` (`cobarBarHomEquiv_apply_ι`). -/
noncomputable def cobarBarHomEquiv :
    AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra ≃
      DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD :=
  (homTwistingCochainEquiv 𝒜 hD.toIsNonUnitalDGAlgebra).trans
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

/-- The linear part of `(cobarBarHomEquiv 𝒜 hD).symm φ` negates the Koszul-twisted action of `φ` on
single-letter generators. -/
@[simp]
theorem linearPart_cobarBarHomEquiv_symm
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD) :
    ((cobarBarHomEquiv 𝒜 hD).symm φ).linearPart =
      -((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 ∘ₗ
        (φ : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] D) ∘ₗ TensorAlgebra.ι R ∘ₗ
          ReducedTensorWords.ofLetter R A) :=
  LinearMap.ext fun _ ↦ by simp

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

/-- Under `(cobarBarHomEquiv 𝒜 _).symm`, the identity of `Ω Tᶜ(sA)` maps to `𝒜.toCobarBar`. -/
@[simp]
theorem cobarBarHomEquiv_symm_id :
    (cobarBarHomEquiv 𝒜 _).symm (DGAlgHom.id _) = 𝒜.toCobarBar := (rfl)

/-- The Taylor components of the canonical morphism `A ⟶ Ω Tᶜ(sA)` are
`z ↦ (-1) ^ |z| s⁻¹ z`. -/
@[simp]
theorem taylor_toCobarBar :
    𝒜.toCobarBar.taylor =
      TensorAlgebra.ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 := by
  rw [toCobarBar, taylor_cobarBarHomEquiv_symm]
  ext z
  simp [InternalGrading.koszulTwist_shift]

/-- The linear part of `𝒜.toCobarBar` sends `a : A` to `-ι (ofLetter (koszulTwist 1 a))`. -/
@[simp]
theorem linearPart_toCobarBar :
    𝒜.toCobarBar.linearPart =
      -(TensorAlgebra.ι R ∘ₗ ReducedTensorWords.ofLetter R A ∘ₗ 𝒜.grading.koszulTwist 1) :=
  LinearMap.ext fun _ ↦ by
    simp [ReducedTensorWords.koszulTwist_grading, InternalGrading.koszulTwist_one_shift_one]

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

/-- Universal factorization characterization: `φ : Ω Tᶜ(sA) ⟶ D` is the DG algebra lift of
`g : A ⟶ D` if and only if `φ ∘ 𝒜.toCobarBar = g`. -/
theorem eq_cobarBarHomEquiv_iff
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD)
    (g : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    φ = cobarBarHomEquiv 𝒜 hD g ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobarBar = g := by
  rw [← Equiv.symm_apply_eq, cobarBarHomEquiv_symm_apply]

variable {E : Type uE} [Ring E] [Algebra R E] {ℰ : ℤ → Submodule R E} [GradedAlgebra ℰ]
  {dE : E →ₗ[R] E}

/-- The bar--cobar correspondence commutes with postcomposition by a DG algebra morphism. -/
@[simp] theorem cobarBarHomEquiv_comp_left {hD : IsDGAlgebra 𝒟 d} {hE : IsDGAlgebra ℰ dE}
    (ψ : DGAlgHom hD hE) (g : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    cobarBarHomEquiv 𝒜 hE (ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp g) =
      ψ.comp (cobarBarHomEquiv 𝒜 hD g) := by
  refine (𝒜.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hE).injective (Subtype.ext ?_)
  rw [IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp]
  simp only [cobarBarHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [homTwistingCochainEquiv_comp_left]; exact LinearMap.ext fun _ ↦ by simp

/-- The inverse bar--cobar correspondence is natural in its target DG algebra. -/
@[simp] theorem cobarBarHomEquiv_symm_comp {hD : IsDGAlgebra 𝒟 d} {hE : IsDGAlgebra ℰ dE}
    (ψ : DGAlgHom hD hE)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD) :
    (cobarBarHomEquiv 𝒜 hE).symm (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ((cobarBarHomEquiv 𝒜 hD).symm φ) :=
  (Equiv.symm_apply_eq _).2 (by simp)

end Unital

end TauCeti.AInfinityAlgebra

namespace TauCeti

section Functoriality

universe uR uA uA' uA'' uD

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {D : Type uD}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A''] [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D}
  [GradedAlgebra 𝒟] {d : D →ₗ[R] D}
  {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'} {𝒜'' : AInfinityAlgebra R A''}

namespace AInfinityHom

/-- An `A∞` morphism `k : A ⟶ A'` induces a DG algebra morphism `Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA')` on
cobar-bar constructions, sending `ι w` to `ι (k.barMap w)`. -/
noncomputable def cobarBarMap (k : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar k.barMap
    (by simpa only [ReducedTensorWords.grading_piece] using k.isHomogeneous_barMap)
    (ReducedTensorWords.isCoalgHom_iff.1 k.isCoalgHom_barMap) k.barDifferential_comp_barMap

/-- `cobarBarMap` sends a desuspended bar generator `ι w` to `ι (k.barMap w)`. -/
@[simp] theorem cobarBarMap_ι (k : AInfinityHom 𝒜 𝒜') (w : ReducedTensorWords R A) :
    k.cobarBarMap (TensorAlgebra.ι R w) = TensorAlgebra.ι R (k.barMap w) :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap_ι _ _ _ _ _ w

/-- The identity `A∞` morphism induces the identity DG algebra morphism on `Ω Tᶜ(sA)`. -/
@[simp] theorem cobarBarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarBarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

/-- `cobarBarMap` preserves composition of `A∞` morphisms. -/
@[simp] theorem cobarBarMap_comp (k₂ : AInfinityHom 𝒜' 𝒜'') (k₁ : AInfinityHom 𝒜 𝒜') :
    (k₂.comp k₁).cobarBarMap = k₂.cobarBarMap.comp k₁.cobarBarMap :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

end AInfinityHom

namespace AInfinityAlgebra

/-- Precomposing `g : A ⟶ D` with `k : A' ⟶ A` precomposes its cobar lift with `k.cobarBarMap`. -/
theorem cobarBarHomEquiv_comp_right (hD : IsDGAlgebra 𝒟 d)
    (g : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) (k : AInfinityHom 𝒜' 𝒜) :
    𝒜'.cobarBarHomEquiv hD (g.comp k) = (𝒜.cobarBarHomEquiv hD g).comp k.cobarBarMap := by
  refine (𝒜'.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hD).injective (Subtype.ext ?_)
  simp only [cobarBarHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply, AInfinityHom.cobarBarMap,
    IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp_cobarMap]
  exact homTwistingCochainEquiv_comp_right hD.toIsNonUnitalDGAlgebra g k

/-- The inverse bar--cobar correspondence is natural in its source `A∞` algebra along
`cobarBarMap`. -/
theorem cobarBarHomEquiv_symm_comp_cobarBarMap (hD : IsDGAlgebra 𝒟 d) (k : AInfinityHom 𝒜' 𝒜)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hD) :
    (𝒜'.cobarBarHomEquiv hD).symm (φ.comp k.cobarBarMap) =
      ((𝒜.cobarBarHomEquiv hD).symm φ).comp k :=
  (Equiv.symm_apply_eq _).2 (by simp [cobarBarHomEquiv_comp_right])

end AInfinityAlgebra

/-- The canonical `A∞` morphism `toCobarBar` is natural with respect to `cobarBarMap`. -/
theorem AInfinityHom.cobarBarMap_comp_toCobarBar (k : AInfinityHom 𝒜' 𝒜) :
    k.cobarBarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜'.toCobarBar =
      𝒜.toCobarBar.comp k := by
  rw [← AInfinityAlgebra.cobarBarHomEquiv_symm_apply
      (hD := 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential),
    ← DGAlgHom.id_comp k.cobarBarMap, AInfinityAlgebra.cobarBarHomEquiv_symm_comp_cobarBarMap,
    AInfinityAlgebra.cobarBarHomEquiv_symm_id]

end Functoriality

end TauCeti
