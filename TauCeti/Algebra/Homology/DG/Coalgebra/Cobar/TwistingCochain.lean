/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist

/-!
# Twisting cochains and the cobar universal property

A twisting cochain from a noncounital DG coalgebra `C` to a (possibly nonunital) DG algebra `A`
is a linear map `τ : C → A` of degree one satisfying

`d_A τ + τ d_C + μ (τ ⊗ τ) Δ = 0`,

where the tensor product of the two degree-one maps contributes the sign
`(-1) ^ |c'|` on a coproduct term `c' ⊗ c''`. The equation makes sense over any
commutative ring; it involves no division or infinite sum.

When `A` is unital, the cobar universal property identifies these cochains with DG algebra maps
`ΩC → A`. With the differential of `cobarDifferential`, the universal twisting cochain is **minus**
the inclusion of desuspended generators. Thus a twisting cochain `τ` extends uniquely to
the DG algebra map taking `s⁻¹ c` to `-τ c`. We prove the full chain-map equation on the
tensor algebra, not just its restriction to generators, along with naturality in both the
target DG algebra and the source coalgebra (`IsNonCounitalDGCoalgebra.cobarMap`). No
conilpotence hypothesis is needed for this direction of the bar--cobar adjunction.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2, for twisting morphisms
  and the cobar universal property (here written with cohomological degree-one cochains).
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uC uD uE uA uB

section NonUnital

variable {R : Type uR} {C : Type uC} {A : Type uA}
  [CommRing R] [AddCommGroup C] [Module R C]
  [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  (G : InternalGrading R C ℤ) (Δ : C →ₗ[R] C ⊗[R] C) (dC : C →ₗ[R] C)
  (𝒜 : ℤ → Submodule R A) (dA : A →ₗ[R] A)

/-- A degree-one twisting cochain, with the tensor-map Koszul sign in its quadratic term.
For a coaugmented coalgebra this definition is applied to its coaugmentation coideal and
reduced coproduct. -/
structure IsTwistingCochain (τ : C →ₗ[R] A) : Prop where
  /-- A twisting cochain raises degree by one. -/
  isHomogeneous : LinearMap.IsHomogeneous τ G.piece 𝒜 1
  /-- The twisting equation, including the sign of the tensor product of degree-one maps. -/
  equation (c : C) : dA (τ c) + τ (dC c) +
    LinearMap.mul' R A (TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ (Δ c)) = 0

/-- The zero linear map is a twisting cochain from any noncounital DG coalgebra datum to any
nonunital DG algebra datum. -/
@[simp] theorem isTwistingCochain_zero : IsTwistingCochain G Δ dC 𝒜 dA 0 :=
  ⟨LinearMap.isHomogeneous_zero G.piece 𝒜 1, fun _ ↦ by simp⟩

variable {G Δ dC 𝒜 dA}

private theorem quadratic_neg (τ : C →ₗ[R] A) (w : C ⊗[R] C) :
    LinearMap.mul' R A (TensorProduct.map ((-τ) ∘ₗ G.koszulTwist 1) (-τ) w) =
      LinearMap.mul' R A (TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

namespace IsTwistingCochain

/-- Precomposition with a degree-zero linear map intertwining coproducts and differentials
preserves twisting cochains. -/
theorem comap {D : Type uD} [AddCommGroup D] [Module R D]
    {GD : InternalGrading R D ℤ} {ΔD : D →ₗ[R] D ⊗[R] D} {dD : D →ₗ[R] D}
    {τ : C →ₗ[R] A} (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ)
    {f : D →ₗ[R] C} (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    IsTwistingCochain GD ΔD dD 𝒜 dA (τ ∘ₗ f) where
  isHomogeneous := by simpa only [zero_add] using hτ.isHomogeneous.comp hf_hom
  equation x := by
    have hftwist : f ∘ₗ GD.koszulTwist 1 = G.koszulTwist 1 ∘ₗ f :=
      LinearMap.ext fun y ↦ by simpa using (hf_hom.koszulTwist_apply 1 y).symm
    have hquad : TensorProduct.map ((τ ∘ₗ f) ∘ₗ GD.koszulTwist 1) (τ ∘ₗ f) (ΔD x) =
        TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ (Δ (f x)) := by
      rw [LinearMap.comp_assoc, hftwist, ← LinearMap.comp_assoc, TensorProduct.map_comp,
        LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map f f), ← hf_comul,
        LinearMap.comp_apply]
    have hfd : f (dD x) = dC (f x) := (LinearMap.congr_fun hf_d x).symm
    simpa only [LinearMap.comp_apply, hfd, hquad] using hτ.equation (f x)

section Map

variable {B : Type uB} [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  {ℬ : ℤ → Submodule R B} {dB : B →ₗ[R] B} {τ : C →ₗ[R] A}

/-- Postcomposition with a graded linear multiplicative map intertwining differentials preserves
twisting cochains. -/
theorem map {F : Type*} [FunLike F A B] [LinearMapClass F R A B] [MulHomClass F A B]
    [GradedFunLike F 𝒜 ℬ] (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) (f : F)
    (hf_d : ∀ a, dB (f a) = f (dA a)) :
    IsTwistingCochain G Δ dC ℬ dB ((f : A →ₗ[R] B) ∘ₗ τ) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ hc ↦
    GradedFunLike.map_mem f (hτ.isHomogeneous.map_mem hc)
  equation c := by
    have hq : LinearMap.mul' R B ∘ₗ TensorProduct.map
        (((f : A →ₗ[R] B) ∘ₗ τ) ∘ₗ G.koszulTwist 1) ((f : A →ₗ[R] B) ∘ₗ τ) =
        (f : A →ₗ[R] B) ∘ₗ LinearMap.mul' R A ∘ₗ TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ :=
      TensorProduct.ext' fun _ _ ↦ by simp
    have he := congrArg f (hτ.equation c)
    simp only [map_add, map_zero, ← hf_d] at he
    have hqc := LinearMap.congr_fun hq (Δ c)
    simp only [LinearMap.comp_apply, LinearMap.coe_ofClass] at hqc ⊢
    rwa [hqc]

end Map
end IsTwistingCochain
end NonUnital

section Unital

variable {R : Type uR} {C : Type uC} {A : Type uA}
  [CommRing R] [AddCommGroup C] [Module R C] [Ring A] [Algebra R A]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}

private theorem map_cobar_quadratic {F : Type*} [FunLike F (TensorAlgebra R C) A]
    [AlgHomClass F R (TensorAlgebra R C) A] (φ : F) (w : C ⊗[R] C) :
    φ (LinearMap.mul' R (TensorAlgebra R C)
      (TensorProduct.map (ι R ∘ₗ G.koszulTwist 1) (ι R) w)) =
    LinearMap.mul' R A (TensorProduct.map
      (((φ : TensorAlgebra R C →ₗ[R] A) ∘ₗ ι R) ∘ₗ G.koszulTwist 1)
      ((φ : TensorAlgebra R C →ₗ[R] A) ∘ₗ ι R) w) := by
  have h := LinearMap.congr_fun (AlgHom.ofClass φ).comp_mul'
    (TensorProduct.map (ι R ∘ₗ G.koszulTwist 1) (ι R) w)
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_ofClass,
    TensorProduct.map_map, LinearMap.comp_assoc, AlgHom.toLinearMap_eq_coe,
    AlgHomClass.linearMapOfClass_ofClass, LinearMap.coe_ofClass] using h

namespace IsNonCounitalDGCoalgebra

variable (hC : IsNonCounitalDGCoalgebra G Δ dC) (hA : IsDGAlgebra 𝒜 dA)

include hC hA in
/-- A graded algebra map out of the cobar construction commutes with differentials if and
only if it does so on the desuspended generators. -/
theorem map_cobarDifferential_iff (φ : tensorAlgebraPiece (G.shift (-1)) →ₐᵍ[R] 𝒜) :
    (∀ x, dA (φ x) = φ (cobarDifferential G Δ dC x)) ↔
      ∀ c, dA (φ (ι R c)) = φ (cobarDifferential G Δ dC (ι R c)) := by
  refine ⟨fun h c ↦ h _, fun h x ↦ ?_⟩
  have hφ : LinearMap.IsHomogeneous φ.toAlgHom.toLinearMap
      (InternalGrading.ofDecomposition (tensorAlgebraPiece (G.shift (-1)))).piece
      (InternalGrading.ofDecomposition 𝒜).piece 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
      simpa only [InternalGrading.ofDecomposition_piece, add_zero,
        AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
        φ.map_mem (by simpa only [InternalGrading.ofDecomposition_piece] using hx)
  have htwist (x : TensorAlgebra R C) := hφ.koszulTwist_apply 1 x
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
    AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom] at htwist
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp [hA.map_algebraMap]
  | ι c => exact h c
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy =>
    rw [map_mul, hA.toIsNonUnitalDGAlgebra.leibniz_koszulTwist,
      hC.isDGAlgebra_cobarDifferential.toIsNonUnitalDGAlgebra.leibniz_koszulTwist,
      map_add, map_mul, map_mul, hx, hy]
    rw [htwist]

/-- The unique graded algebra extension of `-τ` is a DG algebra map when `τ` is a twisting
cochain. -/
noncomputable def cobarLift (τ : C →ₗ[R] A) (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    DGAlgHom hC.isDGAlgebra_cobarDifferential hA where
  toGradedAlgHom := tensorAlgebraGradedLift (G.shift (-1)) 𝒜 (-τ)
    (LinearMap.isHomogeneous_def.mpr fun p c hc ↦ by
      rw [InternalGrading.shift_piece] at hc
      simpa [add_assoc] using hτ.isHomogeneous.neg.map_mem hc)
  map_d' := (hC.map_cobarDifferential_iff hA _).2 fun c ↦ by
    rw [coe_tensorAlgebraGradedLift, lift_ι_apply, LinearMap.neg_apply, map_neg dA,
      cobarDifferential_ι, map_sub, map_cobar_quadratic]
    simp only [← AlgHom.toLinearMap_eq_coe, ι_comp_lift, quadratic_neg, lift_ι_apply,
      LinearMap.neg_apply]
    have he := hτ.equation c
    grind

/-- The extension of a twisting cochain takes a desuspended generator to its negative. -/
@[simp]
theorem cobarLift_ι (τ : C →ₗ[R] A) (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) (c : C) :
    hC.cobarLift hA τ hτ (ι R c) = -τ c := by
  simp [cobarLift]

/-- DG algebra maps out of the cobar construction are determined by their values on generators. -/
@[ext]
theorem cobarHom_ext {φ ψ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA}
    (h : ∀ c, φ (ι R c) = ψ (ι R c)) : φ = ψ :=
  DGAlgHom.toGradedAlgHom_injective (tensorAlgebraGradedAlgHom_ext h)

/-- An extension of a twisting cochain is the cobar lift precisely when it has the prescribed
values on the generators. -/
theorem eq_cobarLift_iff (τ : C →ₗ[R] A) (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ)
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    φ = hC.cobarLift hA τ hτ ↔ ∀ c, φ (ι R c) = -τ c := by
  constructor
  · rintro rfl c
    exact hC.cobarLift_ι hA τ hτ c
  · intro h
    exact hC.cobarHom_ext hA fun c ↦ by rw [hC.cobarLift_ι]; exact h c

/-- Negating the restriction of a DG algebra map to desuspended generators gives a twisting
cochain. -/
theorem isTwistingCochain_restrict (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    IsTwistingCochain G Δ dC 𝒜 dA
      (-((φ : TensorAlgebra R C →ₗ[R] A) ∘ₗ ι R)) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun p c hc ↦ by
    have hmem := φ.map_mem (ι_mem_tensorAlgebraPiece (G.shift (-1))
      (p := p + 1) (by simpa [InternalGrading.shift_piece, add_assoc] using hc))
    exact neg_mem hmem
  equation c := by
    have he := φ.map_d (ι R c)
    rw [cobarDifferential_ι, map_sub, map_cobar_quadratic] at he
    rw [quadratic_neg]
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.coe_ofClass, map_neg]
    grind

/-- The **cobar universal property**: DG algebra maps `ΩC → A` correspond bijectively to
cohomological twisting cochains `C → A`. The forward map is negative restriction to
desuspended generators, and the inverse is the tensor-algebra extension of `-τ`. -/
noncomputable def cobarTwistingCochainEquiv :
    DGAlgHom hC.isDGAlgebra_cobarDifferential hA ≃
      {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ} where
  toFun φ := ⟨-((φ : TensorAlgebra R C →ₗ[R] A) ∘ₗ ι R),
    hC.isTwistingCochain_restrict hA φ⟩
  invFun τ := hC.cobarLift hA τ.val τ.property
  left_inv φ := hC.cobarHom_ext hA fun c ↦ by simp
  right_inv τ := Subtype.ext (LinearMap.ext fun c ↦ by simp)

/-- The universal-property correspondence is negative restriction to generators. -/
@[simp]
theorem cobarTwistingCochainEquiv_apply (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA)
    (c : C) : (hC.cobarTwistingCochainEquiv hA φ).val c = -φ (ι R c) := (rfl)

/-- The inverse correspondence extends the negative of a twisting cochain on generators. -/
@[simp]
theorem cobarTwistingCochainEquiv_symm_apply_ι
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ}) (c : C) :
    (hC.cobarTwistingCochainEquiv hA).symm τ (ι R c) = -τ.val c :=
  hC.cobarLift_ι hA τ.val τ.property c

include hC in
/-- The universal twisting cochain is minus the inclusion of desuspended generators. -/
theorem isTwistingCochain_neg_ι :
    IsTwistingCochain G Δ dC (tensorAlgebraPiece (G.shift (-1))) (cobarDifferential G Δ dC)
      (-ι R) := by
  have hid : (DGAlgHom.id hC.isDGAlgebra_cobarDifferential :
      TensorAlgebra R C →ₗ[R] TensorAlgebra R C) = LinearMap.id := by
    ext x
    simp
  simpa only [hid, LinearMap.id_comp] using
    hC.isTwistingCochain_restrict hC.isDGAlgebra_cobarDifferential
      (DGAlgHom.id hC.isDGAlgebra_cobarDifferential)

section Naturality

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
  [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}

/-- Extending a twisting cochain commutes with postcomposition by a DG algebra morphism. -/
@[simp] theorem cobarLift_map (τ : C →ₗ[R] A) (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ)
    (f : DGAlgHom hA hB) :
    hC.cobarLift hB ((f : A →ₗ[R] B) ∘ₗ τ) (hτ.map f f.map_d) = f.comp (hC.cobarLift hA τ hτ) :=
  hC.cobarHom_ext hB fun _ ↦ by simp

/-- The cobar correspondence is natural in its target DG algebra. -/
@[simp] theorem cobarTwistingCochainEquiv_comp (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA)
    (f : DGAlgHom hA hB) :
    (hC.cobarTwistingCochainEquiv hB (f.comp φ)).val =
      (f : A →ₗ[R] B) ∘ₗ (hC.cobarTwistingCochainEquiv hA φ).val :=
  LinearMap.ext fun _ ↦ by simp

end Naturality

section CoalgebraMap

variable {D : Type uD} {E : Type uE} [AddCommGroup D] [Module R D] [AddCommGroup E] [Module R E]
  {GD : InternalGrading R D ℤ} {ΔD : D →ₗ[R] D ⊗[R] D} {dD : D →ₗ[R] D}
  {GE : InternalGrading R E ℤ} {ΔE : E →ₗ[R] E ⊗[R] E} {dE : E →ₗ[R] E}

/-- A degree-zero linear map intertwining coproducts and differentials induces a DG algebra
morphism between cobar constructions, sending `ι x` to `ι (f x)`. -/
noncomputable def cobarMap (hD : IsNonCounitalDGCoalgebra GD ΔD dD)
    (hC : IsNonCounitalDGCoalgebra G Δ dC) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    DGAlgHom hD.isDGAlgebra_cobarDifferential hC.isDGAlgebra_cobarDifferential :=
  hD.cobarLift hC.isDGAlgebra_cobarDifferential ((-ι R) ∘ₗ f)
    (hC.isTwistingCochain_neg_ι.comap hf_hom hf_comul hf_d)

/-- `cobarMap` sends a desuspended generator `ι x` to `ι (f x)`. -/
@[simp] theorem cobarMap_ι (hD : IsNonCounitalDGCoalgebra GD ΔD dD)
    (hC : IsNonCounitalDGCoalgebra G Δ dC) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) (x : D) :
    hD.cobarMap hC f hf_hom hf_comul hf_d (ι R x) = ι R (f x) := by simp [cobarMap]

/-- The identity coalgebra morphism induces the identity DG algebra morphism on `ΩC`. -/
@[simp] theorem cobarMap_id :
    hC.cobarMap hC LinearMap.id (LinearMap.isHomogeneous_id _) (by simp) (by simp) =
      DGAlgHom.id hC.isDGAlgebra_cobarDifferential :=
  hC.cobarHom_ext _ fun _ ↦ by simp

/-- `cobarMap` preserves composition of coalgebra morphisms. -/
@[simp] theorem cobarMap_comp_cobarMap (hE : IsNonCounitalDGCoalgebra GE ΔE dE)
    (hD : IsNonCounitalDGCoalgebra GD ΔD dD) (hC : IsNonCounitalDGCoalgebra G Δ dC)
    (f : D →ₗ[R] C) (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD)
    (g : E →ₗ[R] D) (hg_hom : LinearMap.IsHomogeneous g GE.piece GD.piece 0)
    (hg_comul : ΔD ∘ₗ g = TensorProduct.map g g ∘ₗ ΔE) (hg_d : dD ∘ₗ g = g ∘ₗ dE) :
    (hD.cobarMap hC f hf_hom hf_comul hf_d).comp (hE.cobarMap hD g hg_hom hg_comul hg_d) =
      hE.cobarMap hC (f ∘ₗ g) (by simpa only [add_zero] using hf_hom.comp hg_hom)
        (by rw [← LinearMap.comp_assoc, hf_comul, LinearMap.comp_assoc, hg_comul,
          TensorProduct.map_comp, LinearMap.comp_assoc])
        (by rw [← LinearMap.comp_assoc, hf_d, LinearMap.comp_assoc, hg_d, LinearMap.comp_assoc]) :=
  hE.cobarHom_ext _ fun _ ↦ by simp

/-- Extending a pulled-back twisting cochain factors through `cobarMap`. -/
theorem cobarLift_comap (hD : IsNonCounitalDGCoalgebra GD ΔD dD) (τ : C →ₗ[R] A)
    (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    hD.cobarLift hA (τ ∘ₗ f) (hτ.comap hf_hom hf_comul hf_d) =
      (hC.cobarLift hA τ hτ).comp (hD.cobarMap hC f hf_hom hf_comul hf_d) :=
  hD.cobarHom_ext hA fun _ ↦ by simp

/-- The cobar correspondence is natural in its source DG coalgebra. -/
theorem cobarTwistingCochainEquiv_comp_cobarMap (hD : IsNonCounitalDGCoalgebra GD ΔD dD)
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    (hD.cobarTwistingCochainEquiv hA (φ.comp (hD.cobarMap hC f hf_hom hf_comul hf_d))).val =
      (hC.cobarTwistingCochainEquiv hA φ).val ∘ₗ f :=
  LinearMap.ext fun _ ↦ by simp

end CoalgebraMap
end IsNonCounitalDGCoalgebra
end Unital
end TauCeti
