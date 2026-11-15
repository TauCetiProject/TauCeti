/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar
public import TauCeti.Algebra.Homology.DG.Coalgebra.Hom

/-!
# Twisting cochains and the cobar universal property

A twisting cochain from a noncounital DG coalgebra `C` to a (not necessarily unital) DG algebra
`A` is a linear map `τ : C → A` of degree one satisfying

`d_A τ + τ d_C + μ (τ ⊗ τ) Δ = 0`,

where the tensor product of the two degree-one maps contributes the sign
`(-1) ^ |c'|` on a coproduct term `c' ⊗ c''`. The equation makes sense over any
commutative ring and for any nonunital `R`-algebra; it involves no division or infinite sum.

For a unital DG algebra `A`, the cobar universal property identifies these cochains with DG
algebra maps `ΩC → A`. With the differential of `cobarDifferential`, the universal twisting
cochain is **minus** the inclusion of desuspended generators. Thus a twisting cochain `τ` extends
uniquely to the DG algebra map taking `s⁻¹ c` to `-τ c`. Pulling back the universal twisting
cochain along a morphism `C → D` of noncounital DG coalgebras makes the cobar construction
functorial (`TauCeti.NonCounitalDGCoalgHom.cobarMap`), and lifting the zero twisting cochain to the
ground ring equips every cobar algebra with its canonical augmentation
(`TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`).

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

variable {G Δ dC 𝒜 dA}

private theorem quadratic_neg (τ : C →ₗ[R] A) (w : C ⊗[R] C) :
    LinearMap.mul' R A (TensorProduct.map ((-τ) ∘ₗ G.koszulTwist 1) (-τ) w) =
      LinearMap.mul' R A (TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

namespace IsTwistingCochain

/-- The zero linear map is always a twisting cochain. -/
theorem zero : IsTwistingCochain G Δ dC 𝒜 dA 0 where
  isHomogeneous := LinearMap.isHomogeneous_zero G.piece 𝒜 1
  equation _ := by simp

/-- Postcomposition with a nonunital DG algebra morphism preserves twisting cochains. -/
theorem map_nonUnital {B : Type uB}
    [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
    {ℬ : ℤ → Submodule R B} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
    [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ] {dB : B →ₗ[R] B}
    {hA : IsNonUnitalDGAlgebra 𝒜 dA} {hB : IsNonUnitalDGAlgebra ℬ dB}
    {τ : C →ₗ[R] A} (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) (f : NonUnitalDGAlgHom hA hB) :
    IsTwistingCochain G Δ dC ℬ dB ((f : A →ₗ[R] B) ∘ₗ τ) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ hc ↦
    Graded.map_mem f (hτ.isHomogeneous.map_mem hc)
  equation c := by
    have hqc : LinearMap.mul' R B
        (TensorProduct.map ((((f : A →ₗ[R] B) ∘ₗ τ) ∘ₗ G.koszulTwist 1))
          ((f : A →ₗ[R] B) ∘ₗ τ) (Δ c)) =
        f (LinearMap.mul' R A (TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ (Δ c))) := by
      induction Δ c using TensorProduct.inductionOn with
      | tmul x y => simp [map_mul]
      | add x y hx hy => simp only [map_add, hx, hy]
    have he := congrArg f (hτ.equation c)
    simp only [map_add, map_zero, ← f.map_d] at he
    simp only [LinearMap.comp_apply, LinearMap.coe_ofClass] at hqc ⊢
    rw [hqc]
    exact he

/-- Precomposition with a morphism of noncounital DG coalgebras pulls back twisting cochains. -/
theorem comap {D : Type uD} [AddCommGroup D] [Module R D]
    {GD : InternalGrading R D ℤ} {ΔD : D →ₗ[R] D ⊗[R] D} {dD : D →ₗ[R] D}
    {hC : IsNonCounitalDGCoalgebra G Δ dC} {hD : IsNonCounitalDGCoalgebra GD ΔD dD}
    {τ : D →ₗ[R] A} (hτ : IsTwistingCochain GD ΔD dD 𝒜 dA τ)
    (g : NonCounitalDGCoalgHom hC hD) :
    IsTwistingCochain G Δ dC 𝒜 dA (τ ∘ₗ (g : C →ₗ[R] D)) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ hc ↦
    hτ.isHomogeneous.map_mem (Graded.map_mem g hc)
  equation c := by
    have htwist : (τ ∘ₗ (g : C →ₗ[R] D)) ∘ₗ G.koszulTwist 1 =
        (τ ∘ₗ GD.koszulTwist 1) ∘ₗ (g : C →ₗ[R] D) := by
      rw [LinearMap.comp_assoc, ← g.koszulTwist_comp 1, ← LinearMap.comp_assoc]
    rw [htwist, ← TensorProduct.map_map, ← g.map_comul, LinearMap.comp_apply,
      LinearMap.comp_apply, NonCounitalDGCoalgHom.coe_toLinearMap, ← g.map_d]
    exact hτ.equation (g c)

end IsTwistingCochain

end NonUnital

section Unital

variable {R : Type uR} {C : Type uC} {A : Type uA}
  [CommRing R] [AddCommGroup C] [Module R C] [Ring A] [Algebra R A]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}
  {𝒜 : ℤ → Submodule R A} {dA : A →ₗ[R] A}

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

variable [GradedAlgebra 𝒜]

namespace IsTwistingCochain

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
  [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hA : IsDGAlgebra 𝒜 dA}
  {hB : IsDGAlgebra ℬ dB} {τ : C →ₗ[R] A}

/-- Postcomposition with a DG algebra morphism preserves twisting cochains. -/
theorem map (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) (f : DGAlgHom hA hB) :
    IsTwistingCochain G Δ dC ℬ dB ((f : A →ₗ[R] B) ∘ₗ τ) := by
  have hf : (f.toNonUnitalDGAlgHom : A →ₗ[R] B) = (f : A →ₗ[R] B) := by
    ext a
    simp
  rw [← hf]
  exact hτ.map_nonUnital f.toNonUnitalDGAlgHom

end IsTwistingCochain

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

/-- The canonical augmentation of a cobar construction, sending every desuspended generator to
zero. -/
noncomputable def cobarAugmentation :
    DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0 IsTwistingCochain.zero

@[simp]
theorem cobarAugmentation_ι (c : C) :
    hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

/-- A DG algebra morphism out of the cobar construction preserves the canonical augmentation
precisely when it sends every desuspended generator into the target augmentation ideal. -/
theorem comp_eq_cobarAugmentation_iff (εA : DGAlgAugmentation hA)
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    εA.comp φ = hC.cobarAugmentation ↔ ∀ c, φ (ι R c) ∈ εA.augmentationIdeal := by
  constructor
  · intro h c
    rw [DGAlgAugmentation.mem_augmentationIdeal, ← DGAlgHom.comp_apply, h, cobarAugmentation_ι]
  · intro h
    refine hC.cobarHom_ext (isDGAlgebra_trivialGrading R) fun c ↦ ?_
    rw [DGAlgHom.comp_apply, cobarAugmentation_ι]
    exact (DGAlgAugmentation.mem_augmentationIdeal εA).mp (h c)

section Naturality

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
  [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}

/-- Extending a twisting cochain commutes with postcomposition by a DG algebra morphism. -/
@[simp]
theorem cobarLift_map (τ : C →ₗ[R] A) (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ)
    (f : DGAlgHom hA hB) :
    hC.cobarLift hB ((f : A →ₗ[R] B) ∘ₗ τ) (hτ.map f) = f.comp (hC.cobarLift hA τ hτ) := by
  apply hC.cobarHom_ext hB
  intro c
  simp

/-- The cobar correspondence is natural in its target DG algebra. -/
@[simp]
theorem cobarTwistingCochainEquiv_comp (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA)
    (f : DGAlgHom hA hB) :
    (hC.cobarTwistingCochainEquiv hB (f.comp φ)).val =
      (f : A →ₗ[R] B) ∘ₗ (hC.cobarTwistingCochainEquiv hA φ).val := by
  ext c
  simp

end Naturality

end IsNonCounitalDGCoalgebra

end Unital

/-! ### Functoriality of the cobar construction -/

namespace NonCounitalDGCoalgHom

variable {R : Type uR} {C : Type uC} {D : Type uD} {E : Type uE} {A : Type uA}
  [CommRing R]
  [AddCommGroup C] [Module R C]
  [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]
  [Ring A] [Algebra R A]
  {GC : InternalGrading R C ℤ} {GD : InternalGrading R D ℤ} {GE : InternalGrading R E ℤ}
  {ΔC : C →ₗ[R] C ⊗[R] C} {ΔD : D →ₗ[R] D ⊗[R] D} {ΔE : E →ₗ[R] E ⊗[R] E}
  {dC : C →ₗ[R] C} {dD : D →ₗ[R] D} {dE : E →ₗ[R] E}
  {hC : IsNonCounitalDGCoalgebra GC ΔC dC}
  {hD : IsNonCounitalDGCoalgebra GD ΔD dD}
  {hE : IsNonCounitalDGCoalgebra GE ΔE dE}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}

/-- The morphism of cobar DG algebras `ΩC → ΩD` induced by a morphism of noncounital DG coalgebras
`C → D`, sending each desuspended generator `s⁻¹ c` to `s⁻¹ (g c)`. -/
noncomputable def cobarMap (g : NonCounitalDGCoalgHom hC hD) :
    DGAlgHom hC.isDGAlgebra_cobarDifferential hD.isDGAlgebra_cobarDifferential :=
  hC.cobarLift hD.isDGAlgebra_cobarDifferential ((-ι R) ∘ₗ (g : C →ₗ[R] D))
    (hD.isTwistingCochain_neg_ι.comap g)

@[simp]
theorem cobarMap_ι (g : NonCounitalDGCoalgHom hC hD) (c : C) :
    g.cobarMap (ι R c) = ι R (g c) := by
  simp [cobarMap]

@[simp]
theorem cobarMap_id (hC : IsNonCounitalDGCoalgebra GC ΔC dC) :
    (NonCounitalDGCoalgHom.id hC).cobarMap = DGAlgHom.id hC.isDGAlgebra_cobarDifferential :=
  hC.cobarHom_ext _ fun c ↦ by simp

@[simp]
theorem cobarMap_comp (k : NonCounitalDGCoalgHom hD hE) (g : NonCounitalDGCoalgHom hC hD) :
    (k.comp g).cobarMap = k.cobarMap.comp g.cobarMap :=
  hC.cobarHom_ext _ fun c ↦ by simp

/-- Extending a pulled-back twisting cochain factors through the induced cobar morphism. -/
@[simp]
theorem cobarLift_comap (g : NonCounitalDGCoalgHom hC hD) (τ : D →ₗ[R] A)
    (hτ : IsTwistingCochain GD ΔD dD 𝒜 dA τ) :
    hC.cobarLift hA (τ ∘ₗ (g : C →ₗ[R] D)) (hτ.comap g) =
      (hD.cobarLift hA τ hτ).comp g.cobarMap :=
  hC.cobarHom_ext hA fun c ↦ by simp

/-- The twisting cochain corresponding to `g.cobarMap` is `-ι ∘ g`. -/
@[simp]
theorem cobarTwistingCochainEquiv_cobarMap (g : NonCounitalDGCoalgHom hC hD) :
    (hC.cobarTwistingCochainEquiv hD.isDGAlgebra_cobarDifferential g.cobarMap).val =
      (-ι R) ∘ₗ (g : C →ₗ[R] D) := by
  ext c
  simp

/-- The cobar correspondence is contravariantly natural in its source DG coalgebra. -/
theorem cobarTwistingCochainEquiv_comp_cobarMap (g : NonCounitalDGCoalgHom hC hD)
    (φ : DGAlgHom hD.isDGAlgebra_cobarDifferential hA) :
    (hC.cobarTwistingCochainEquiv hA (φ.comp g.cobarMap)).val =
      (hD.cobarTwistingCochainEquiv hA φ).val ∘ₗ (g : C →ₗ[R] D) := by
  ext c
  simp

/-- Every induced cobar morphism commutes with the canonical cobar augmentations. -/
@[simp]
theorem cobarAugmentation_comp_cobarMap (g : NonCounitalDGCoalgHom hC hD) :
    hD.cobarAugmentation.comp g.cobarMap = hC.cobarAugmentation :=
  hC.cobarHom_ext _ fun c ↦ by simp

end NonCounitalDGCoalgHom

end TauCeti
