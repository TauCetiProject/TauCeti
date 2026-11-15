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
# Twisting cochains and the bar--cobar adjunction for `A∞` algebras

For a nonunital `A∞` algebra `A` and a nonunital differential graded algebra `B`, an `A∞` morphism
`f : A ⟶ B` is determined by its suspended Taylor map `Tᶜ(sA) ⟶ sB`, which has degree `+1` into
`B` and satisfies `taylor_B ∘ coalgHom f = f ∘ b_A`.  Because the operations of `B` above arity two
vanish, `taylor_B ∘ coalgHom f` reduces to `d_B ∘ f + μ_B ∘ ((σ_B ∘ f) ⊗ f) ∘ Δ`.  Twisting on the
right by `-σ_C`, where `σ_C` is the Koszul twist of the bar grading on `Tᶜ(sA)`, turns this
component equation into the twisting-cochain equation

`d_B τ + τ b_A + μ_B ((τ ∘ σ_C) ⊗ τ) Δ = 0`.

This yields a natural bijection (`TauCeti.AInfinityAlgebra.barTwistingCochainEquiv`) between `A∞`
morphisms `A ⟶ B` and twisting cochains from the reduced bar coalgebra `Tᶜ(sA)` to `B`, valid for
every nonunital differential graded algebra `B`.

When `B` is unital, composing with the cobar universal property
`TauCeti.IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv` produces the **bar--cobar adjunction**
(`TauCeti.AInfinityAlgebra.cobarAdjunctionEquiv`): morphisms of differential graded algebras
`Ω Tᶜ(sA) ⟶ B` correspond bijectively and naturally to `A∞` morphisms `A ⟶ B`.  The two minus signs
of the cobar and bar correspondences cancel, so the adjunction sends every DG algebra morphism
`φ : Ω Tᶜ(sA) ⟶ B` to the composite `φ ∘ toCobar` with the universal `A∞` morphism
`TauCeti.AInfinityAlgebra.toCobar : A ⟶ Ω Tᶜ(sA)`.

## Main definitions

* `TauCeti.AInfinityHom.toBarCoalgHom`: the bar map of an `A∞` morphism as a morphism of
  noncounital DG coalgebras.
* `TauCeti.AInfinityHom.twistingCochain` and `TauCeti.AInfinityAlgebra.ofTwistingCochain`:
  conversion between `A∞` morphisms into a nonunital DG algebra and twisting cochains on `Tᶜ(sA)`.
* `TauCeti.AInfinityAlgebra.barTwistingCochainEquiv`: the bijection between `A∞` morphisms `A ⟶ B`
  and twisting cochains `Tᶜ(sA) ⟶ B`.
* `TauCeti.AInfinityAlgebra.toCobar`: the universal `A∞` morphism `A ⟶ Ω Tᶜ(sA)`.
* `TauCeti.AInfinityHom.cobarMap`: functoriality `Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA')` along `A∞` morphisms.
* `TauCeti.AInfinityAlgebra.cobarAdjunctionEquiv`: the bar--cobar adjunction
  `DGAlgHom (Ω Tᶜ(sA)) B ≃ AInfinityHom A B`.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra_taylor`: explicit formula for the suspended
  Taylor map of a nonunital DG algebra on all reduced tensor words.
* `TauCeti.AInfinityAlgebra.cobarAdjunctionEquiv_apply`: every DG algebra morphism
  `φ : Ω Tᶜ(sA) ⟶ B` corresponds under the adjunction to `φ ∘ toCobar`, establishing the universal
  property of `toCobar` among `A∞` morphisms into unital DG algebras.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

open ReducedTensorWords

universe uR uA uA' uA'' uB uC

/-! ### The Taylor map of a nonunital DG algebra -/

section NonUnitalTaylor

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A]
  [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  {ℬ : ℤ → Submodule R B} [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ]
  {dB : B →ₗ[R] B}

namespace IsNonUnitalDGAlgebra

/-- The suspended Taylor map of a nonunital DG algebra reads the differential on one-letter words,
the Koszul-signed product on two-letter words, and zero on longer words; deconcatenation followed by
letter projections expresses this uniformly on all reduced tensor words. -/
theorem toAInfinityAlgebra_taylor (hB : IsNonUnitalDGAlgebra ℬ dB) :
    hB.toAInfinityAlgebra.taylor =
      dB ∘ₗ letter R B +
        LinearMap.mul' R B ∘ₗ
          TensorProduct.map
            ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ letter R B) (letter R B) ∘ₗ
          deconcatenation R B := by
  refine ReducedTensorWords.linearMap_ext R B fun ⟨k, hk⟩ x ↦ ?_
  rcases k with _ | _ | _ | k
  · omega
  · have hx1 : of R B ⟨1, hk⟩ (PiTensorProduct.tprod R x) = ofLetter R B (x 0) := by
      rw [of_tprod_eq_subword R hk, subword_one R B x hk]
      rfl
    rw [hx1]
    simp [deconcatenation_ofLetter]
  · have hw : of R B ⟨0 + 1 + 1, hk⟩ (PiTensorProduct.tprod R x) =
        of R B (2 : ℕ+) (PiTensorProduct.tprod R ![x 0, x 1]) :=
      of_tprod_congr R B _ rfl fun i ↦ by fin_cases i <;> rfl
    rw [hw]
    simp [deconcatenation_of_two, hB.toAInfinityAlgebra.taylor_of_two]
  · have htay : hB.toAInfinityAlgebra.taylor (of R B ⟨k + 3, hk⟩ (PiTensorProduct.tprod R x)) =
        0 := by
      rw [AInfinityAlgebra.taylor_of_tprod, hB.toAInfinityAlgebra_m_add_three]
      rfl
    have hlet : letter R B (of R B ⟨k + 3, hk⟩ (PiTensorProduct.tprod R x)) = 0 := by
      rw [of_tprod_eq_subword R hk, letter_subword_of_ne_one R B x 0 (by omega)]
    rw [htay, LinearMap.add_apply, LinearMap.comp_apply, hlet, map_zero, zero_add,
      LinearMap.comp_apply, LinearMap.comp_apply, of_tprod_eq_subword R hk,
      deconcatenation_subword, map_sum, map_sum]
    symm
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [Finset.mem_Ioo] at hc
    simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply]
    by_cases hc1 : c = 1
    · subst hc1
      rw [letter_subword_of_ne_one R B x 1 (by omega), mul_zero]
    · rw [letter_subword_of_ne_one R B x 0 hc1, map_zero, zero_mul]

/-- Composing the suspended Taylor map of a nonunital DG algebra with the coalgebra expansion
`coalgHom R f` evaluates `d_B ∘ f + μ_B ∘ ((σ_B ∘ f) ⊗ f) ∘ Δ`. -/
theorem toAInfinityAlgebra_taylor_comp_coalgHom (hB : IsNonUnitalDGAlgebra ℬ dB)
    (f : ReducedTensorWords R A →ₗ[R] B) :
    hB.toAInfinityAlgebra.taylor ∘ₗ coalgHom R f =
      dB ∘ₗ f +
        LinearMap.mul' R B ∘ₗ
          TensorProduct.map ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f) f ∘ₗ
          deconcatenation R A := by
  have hmap :
      TensorProduct.map ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ letter R B)
          (letter R B) ∘ₗ
        TensorProduct.map (coalgHom R f) (coalgHom R f) =
      TensorProduct.map ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f) f := by
    rw [← TensorProduct.map_comp, LinearMap.comp_assoc, letter_comp_coalgHom]
  rw [hB.toAInfinityAlgebra_taylor, LinearMap.add_comp]
  congr 1
  · rw [LinearMap.comp_assoc, letter_comp_coalgHom]
  · rw [LinearMap.comp_assoc, LinearMap.comp_assoc, isCoalgHom_iff.mp (isCoalgHom_coalgHom f)]
    refine LinearMap.ext fun z ↦ ?_
    simpa only [LinearMap.comp_apply] using
      congrArg (LinearMap.mul' R B) (LinearMap.congr_fun hmap (deconcatenation R A z))

end IsNonUnitalDGAlgebra

end NonUnitalTaylor

/-! ### Bar maps as DG coalgebra morphisms -/

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A'']
  {AA : AInfinityAlgebra R A} {AA' : AInfinityAlgebra R A'} {AA'' : AInfinityAlgebra R A''}

/-- The reduced-bar map of an `A∞` morphism packaged as a morphism of noncounital differential
graded coalgebras. -/
noncomputable def toBarCoalgHom (f : AInfinityHom AA AA') :
    NonCounitalDGCoalgHom AA.isNonCounitalDGCoalgebra_bar AA'.isNonCounitalDGCoalgebra_bar where
  toLinearMap := f.barMap
  map_mem' hz := by
    rw [ReducedTensorWords.grading_piece] at hz ⊢
    simpa only [add_zero] using f.isHomogeneous_barMap.map_mem hz
  comul_comp' := isCoalgHom_iff.mp f.isCoalgHom_barMap
  map_d' := f.barDifferential_barMap

@[simp]
theorem toLinearMap_toBarCoalgHom (f : AInfinityHom AA AA') :
    (f.toBarCoalgHom : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R A') = f.barMap := (rfl)

@[simp]
theorem coe_toBarCoalgHom (f : AInfinityHom AA AA') :
    ⇑f.toBarCoalgHom = f.barMap := (rfl)

@[simp]
theorem toBarCoalgHom_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).toBarCoalgHom =
      NonCounitalDGCoalgHom.id AA.isNonCounitalDGCoalgebra_bar := by
  ext z
  simp

@[simp]
theorem toBarCoalgHom_comp (g : AInfinityHom AA' AA'') (f : AInfinityHom AA AA') :
    (g.comp f).toBarCoalgHom = g.toBarCoalgHom.comp f.toBarCoalgHom := by
  ext z
  simp

end AInfinityHom

/-! ### Twisting cochains from the bar construction -/

private theorem neg_comp_koszulTwist_involutive {R D B : Type*} [CommRing R]
    [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
    (G : InternalGrading R D ℤ) (f : D →ₗ[R] B) :
    -(-(f ∘ₗ G.koszulTwist 1) ∘ₗ G.koszulTwist 1) = f := by
  ext z
  simp [InternalGrading.koszulTwist_koszulTwist]

private theorem koszulTwist_comp_eq_neg {R D B : Type*} [CommRing R]
    [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
    {ℬ : ℤ → Submodule R B} [DirectSum.Decomposition ℬ]
    {G : InternalGrading R D ℤ} {f : D →ₗ[R] B}
    (hf : LinearMap.IsHomogeneous f G.piece ℬ 1) :
    (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f = -(f ∘ₗ G.koszulTwist 1) := by
  have hf' : LinearMap.IsHomogeneous f G.piece (InternalGrading.ofDecomposition ℬ).piece 1 := by
    rwa [InternalGrading.ofDecomposition_piece]
  ext z
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, mul_one, Int.negOnePow_one, Units.val_neg,
    Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] using hf'.koszulTwist_apply 1 z

section BarTwistingCochain

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A']
  [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  {AA : AInfinityAlgebra R A} {AA' : AInfinityAlgebra R A'}
  {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ]
  [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞]
  {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

private theorem isHomogeneous_taylor_iff (hB : IsNonUnitalDGAlgebra ℬ dB)
    (f : ReducedTensorWords R A →ₗ[R] B) :
    LinearMap.IsHomogeneous f (gradedPiece (AA.grading.shift 1))
        (hB.toAInfinityAlgebra.grading.shift 1).piece 0 ↔
      LinearMap.IsHomogeneous f (grading (AA.grading.shift 1)).piece ℬ 1 := by
  rw [LinearMap.isHomogeneous_def, LinearMap.isHomogeneous_def]
  constructor <;> intro hf p z hz
  · have hmem := hf p z (by simpa only [grading_piece] using hz)
    simpa only [hB.toAInfinityAlgebra_grading, InternalGrading.shift_piece,
      InternalGrading.ofDecomposition_piece, add_zero] using hmem
  · have hmem := hf p z (by simpa only [grading_piece] using hz)
    simpa only [hB.toAInfinityAlgebra_grading, InternalGrading.shift_piece,
      InternalGrading.ofDecomposition_piece, add_zero] using hmem

/-- A linear map `f : Tᶜ(sA) ⟶ B` is the suspended Taylor map of an `A∞` morphism into a nonunital
DG algebra `B` precisely when `-(f ∘ σ_C)` is a twisting cochain on `Tᶜ(sA)`. -/
private theorem isTwistingCochain_neg_comp_koszulTwist_iff (hB : IsNonUnitalDGAlgebra ℬ dB)
    (f : ReducedTensorWords R A →ₗ[R] B) :
    IsTwistingCochain (grading (AA.grading.shift 1)) (deconcatenation R A) AA.barDifferential
        ℬ dB (-(f ∘ₗ (grading (AA.grading.shift 1)).koszulTwist 1)) ↔
      LinearMap.IsHomogeneous f (gradedPiece (AA.grading.shift 1))
          (hB.toAInfinityAlgebra.grading.shift 1).piece 0 ∧
        hB.toAInfinityAlgebra.taylor ∘ₗ coalgHom R f = f ∘ₗ AA.barDifferential := by
  set G := grading (AA.grading.shift 1)
  set GB := InternalGrading.ofDecomposition ℬ
  have hdeg : LinearMap.IsHomogeneous (-(f ∘ₗ G.koszulTwist 1)) G.piece ℬ 1 ↔
      LinearMap.IsHomogeneous f G.piece ℬ 1 := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← neg_comp_koszulTwist_involutive G f]
      refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
      simpa only [LinearMap.neg_apply, LinearMap.comp_apply] using
        Submodule.neg_mem _ (h.map_mem (G.koszulTwist_mem_piece hz 1))
    · refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
      simpa only [LinearMap.neg_apply, LinearMap.comp_apply] using
        Submodule.neg_mem _ (h.map_mem (G.koszulTwist_mem_piece hz 1))
  rw [isHomogeneous_taylor_iff hB f]
  -- Once `f` is homogeneous of degree `1`, twisting the Maurer--Cartan expression by `σ_B` gives
  -- `f (b_A z) - (taylor_B ∘ coalgHom f) z`.
  have hkey (hf1 : LinearMap.IsHomogeneous f G.piece ℬ 1) (z : ReducedTensorWords R A) :
      GB.koszulTwist 1
          (dB ((-(f ∘ₗ G.koszulTwist 1)) z) +
            (-(f ∘ₗ G.koszulTwist 1)) (AA.barDifferential z) +
            LinearMap.mul' R B
              (TensorProduct.map
                ((-(f ∘ₗ G.koszulTwist 1)) ∘ₗ G.koszulTwist 1)
                (-(f ∘ₗ G.koszulTwist 1))
                (deconcatenation R A z))) =
        (f ∘ₗ AA.barDifferential) z - (hB.toAInfinityAlgebra.taylor ∘ₗ coalgHom R f) z := by
    have hτ : -(f ∘ₗ G.koszulTwist 1) = GB.koszulTwist 1 ∘ₗ f :=
      (koszulTwist_comp_eq_neg hf1).symm
    have hτσ : (-(f ∘ₗ G.koszulTwist 1)) ∘ₗ G.koszulTwist 1 = -f := by
      refine LinearMap.ext fun w ↦ ?_
      simp [InternalGrading.koszulTwist_koszulTwist]
    have hquad (w : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) :
        LinearMap.mul' R B (TensorProduct.map (-f) (GB.koszulTwist 1 ∘ₗ f) w) =
          -GB.koszulTwist 1
            (LinearMap.mul' R B (TensorProduct.map (GB.koszulTwist 1 ∘ₗ f) f w)) := by
      induction w using TensorProduct.inductionOn with
      | tmul x y =>
        simp [GB, InternalGrading.koszulTwist_ofDecomposition_mul,
          InternalGrading.koszulTwist_koszulTwist]
      | add x y hx hy => simp only [map_add, neg_add, hx, hy]
    have hd : GB.koszulTwist 1 (dB (GB.koszulTwist 1 (f z))) = -dB (f z) := by
      calc
        GB.koszulTwist 1 (dB (GB.koszulTwist 1 (f z)))
            = -dB (GB.koszulTwist 1 (GB.koszulTwist 1 (f z))) := by
              simpa [GB] using hB.koszulTwist_map (GB.koszulTwist 1 (f z))
        _ = -dB (f z) := by rw [InternalGrading.koszulTwist_koszulTwist]
    rw [hτσ, hτ, LinearMap.comp_apply, LinearMap.comp_apply, hquad, map_add, map_add, hd,
      InternalGrading.koszulTwist_koszulTwist, map_neg, InternalGrading.koszulTwist_koszulTwist,
      hB.toAInfinityAlgebra_taylor_comp_coalgHom, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    abel
  refine ⟨fun ⟨h1, heq⟩ ↦ ?_, fun ⟨hf1, hfeq⟩ ↦ ⟨hdeg.mpr hf1, fun z ↦ ?_⟩⟩
  · have hf1 := hdeg.mp h1
    refine ⟨hf1, LinearMap.ext fun z ↦ ?_⟩
    have hz := hkey hf1 z
    rw [heq z, map_zero] at hz
    exact (sub_eq_zero.mp hz.symm).symm
  · have hz := hkey hf1 z
    rw [hfeq, sub_self] at hz
    calc
      dB ((-(f ∘ₗ G.koszulTwist 1)) z) + (-(f ∘ₗ G.koszulTwist 1)) (AA.barDifferential z) +
          LinearMap.mul' R B
            (TensorProduct.map ((-(f ∘ₗ G.koszulTwist 1)) ∘ₗ G.koszulTwist 1)
              (-(f ∘ₗ G.koszulTwist 1)) (deconcatenation R A z))
          = GB.koszulTwist 1 (GB.koszulTwist 1 _) :=
            (InternalGrading.koszulTwist_koszulTwist GB 1 _).symm
      _ = 0 := by rw [hz, map_zero]

/-- The twisting cochain `-(f.taylor ∘ σ_C)` associated to an `A∞` morphism into a nonunital DG
algebra. -/
noncomputable def AInfinityHom.twistingCochain {hB : IsNonUnitalDGAlgebra ℬ dB}
    (f : AInfinityHom AA hB.toAInfinityAlgebra) : ReducedTensorWords R A →ₗ[R] B :=
  -(f.taylor ∘ₗ (grading (AA.grading.shift 1)).koszulTwist 1)

@[simp]
theorem AInfinityHom.twistingCochain_apply {hB : IsNonUnitalDGAlgebra ℬ dB}
    (f : AInfinityHom AA hB.toAInfinityAlgebra) (z : ReducedTensorWords R A) :
    f.twistingCochain z = -f.taylor ((grading (AA.grading.shift 1)).koszulTwist 1 z) := (rfl)

/-- The twisting cochain of an `A∞` morphism into a nonunital DG algebra satisfies the
twisting-cochain axioms. -/
theorem AInfinityHom.isTwistingCochain_twistingCochain {hB : IsNonUnitalDGAlgebra ℬ dB}
    (f : AInfinityHom AA hB.toAInfinityAlgebra) :
    IsTwistingCochain (grading (AA.grading.shift 1)) (deconcatenation R A) AA.barDifferential
      ℬ dB f.twistingCochain :=
  (isTwistingCochain_neg_comp_koszulTwist_iff hB f.taylor).mpr
    ⟨f.isHomogeneous_taylor, by rw [← f.barMap_eq_coalgHom]; exact f.taylor_comp_barMap⟩

namespace AInfinityAlgebra

/-- The `A∞` morphism `A ⟶ B` constructed from a twisting cochain `τ : Tᶜ(sA) ⟶ B`, with suspended
Taylor map `-(τ ∘ σ_C)`. -/
noncomputable def ofTwistingCochain (AA : AInfinityAlgebra R A) (hB : IsNonUnitalDGAlgebra ℬ dB)
    (τ : ReducedTensorWords R A →ₗ[R] B)
    (hτ : IsTwistingCochain (ReducedTensorWords.grading (AA.grading.shift 1))
      (deconcatenation R A) AA.barDifferential ℬ dB τ) :
    AInfinityHom AA hB.toAInfinityAlgebra :=
  have hinv : -(-(τ ∘ₗ (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1) ∘ₗ
      (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1) = τ :=
    LinearMap.ext fun z ↦ by simp [InternalGrading.koszulTwist_koszulTwist]
  have h := (isTwistingCochain_neg_comp_koszulTwist_iff (AA := AA) hB
    (-(τ ∘ₗ (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1))).mp (hinv.symm ▸ hτ)
  AInfinityHom.ofTaylor
    (-(τ ∘ₗ (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1)) h.1 h.2

@[simp]
theorem taylor_ofTwistingCochain (AA : AInfinityAlgebra R A) (hB : IsNonUnitalDGAlgebra ℬ dB)
    (τ : ReducedTensorWords R A →ₗ[R] B) (hτ) :
    (AA.ofTwistingCochain hB τ hτ).taylor =
      -(τ ∘ₗ (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1) :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- On single letters, the `A∞` morphism of a twisting cochain `τ` evaluates `τ` after the
degree-one Koszul twist of `A`. -/
@[simp]
theorem linearPart_ofTwistingCochain (AA : AInfinityAlgebra R A) (hB : IsNonUnitalDGAlgebra ℬ dB)
    (τ : ReducedTensorWords R A →ₗ[R] B) (hτ) :
    (AA.ofTwistingCochain hB τ hτ).linearPart =
      τ ∘ₗ ofLetter R A ∘ₗ AA.grading.koszulTwist 1 := by
  ext a
  have hσ : (AA.grading.shift 1).koszulTwist 1 = -AA.grading.koszulTwist 1 := by
    rw [InternalGrading.koszulTwist_shift]
    simp
  rw [AInfinityHom.linearPart_apply, taylor_ofTwistingCochain, LinearMap.neg_apply,
    LinearMap.comp_apply, koszulTwist_grading, map_ofLetter, hσ, LinearMap.neg_apply, map_neg,
    map_neg, neg_neg, LinearMap.comp_apply, LinearMap.comp_apply]

theorem linearPart_ofTwistingCochain_apply (AA : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) (τ : ReducedTensorWords R A →ₗ[R] B) (hτ) (a : A) :
    (AA.ofTwistingCochain hB τ hτ).linearPart a =
      τ (ofLetter R A (AA.grading.koszulTwist 1 a)) :=
  LinearMap.congr_fun (AA.linearPart_ofTwistingCochain hB τ hτ) a

/-- **The bar twisting-cochain correspondence**: `A∞` morphisms from `A` to a nonunital DG algebra
`B` correspond bijectively to twisting cochains from the reduced bar coalgebra `Tᶜ(sA)` to `B`. -/
noncomputable def barTwistingCochainEquiv (AA : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) :
    AInfinityHom AA hB.toAInfinityAlgebra ≃
      {τ : ReducedTensorWords R A →ₗ[R] B //
        IsTwistingCochain (ReducedTensorWords.grading (AA.grading.shift 1)) (deconcatenation R A)
          AA.barDifferential ℬ dB τ} where
  toFun f := ⟨f.twistingCochain, f.isTwistingCochain_twistingCochain⟩
  invFun τ := AA.ofTwistingCochain hB τ.val τ.property
  left_inv f := AInfinityHom.ext <| by
    rw [taylor_ofTwistingCochain]
    exact neg_comp_koszulTwist_involutive _ f.taylor
  right_inv τ := Subtype.ext <| by
    simp only [AInfinityHom.twistingCochain, taylor_ofTwistingCochain]
    exact neg_comp_koszulTwist_involutive _ τ.val

@[simp]
theorem barTwistingCochainEquiv_apply (AA : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) (f : AInfinityHom AA hB.toAInfinityAlgebra) :
    (AA.barTwistingCochainEquiv hB f).val = f.twistingCochain := (rfl)

@[simp]
theorem barTwistingCochainEquiv_symm_apply (AA : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB)
    (τ : {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (AA.grading.shift 1)) (deconcatenation R A)
        AA.barDifferential ℬ dB τ}) :
    (AA.barTwistingCochainEquiv hB).symm τ = AA.ofTwistingCochain hB τ.val τ.property := (rfl)

/-- Postcomposing an `A∞` morphism with a nonunital DG algebra morphism postcomposes its bar
twisting cochain. -/
theorem _root_.TauCeti.AInfinityHom.twistingCochain_comp_left
    {hB : IsNonUnitalDGAlgebra ℬ dB} {hC : IsNonUnitalDGAlgebra 𝒞 dC}
    (g : NonUnitalDGAlgHom hB hC) (f : AInfinityHom AA hB.toAInfinityAlgebra) :
    (g.toAInfinityStrictHom.toAInfinityHom.comp f).twistingCochain =
      (g : B →ₗ[R] C) ∘ₗ f.twistingCochain := by
  refine LinearMap.ext fun z ↦ ?_
  rw [AInfinityHom.twistingCochain_apply, AInfinityStrictHom.taylor_toAInfinityHom_comp]
  simp

/-- Precomposing an `A∞` morphism with `g : A' ⟶ A` precomposes its bar twisting cochain with
`g.toBarCoalgHom`. -/
@[simp]
theorem _root_.TauCeti.AInfinityHom.twistingCochain_comp_right {hB : IsNonUnitalDGAlgebra ℬ dB}
    (f : AInfinityHom AA hB.toAInfinityAlgebra) (g : AInfinityHom AA' AA) :
    (f.comp g).twistingCochain = f.twistingCochain ∘ₗ (g.toBarCoalgHom : _ →ₗ[R] _) := by
  refine LinearMap.ext fun z ↦ ?_
  simp only [AInfinityHom.twistingCochain_apply, AInfinityHom.taylor_comp, LinearMap.comp_apply,
    AInfinityHom.toLinearMap_toBarCoalgHom]
  have hg := g.toBarCoalgHom.map_koszulTwist 1 z
  simp only [AInfinityHom.coe_toBarCoalgHom] at hg
  rw [hg]

/-- Naturality of the bar twisting-cochain correspondence in the target nonunital DG algebra. -/
theorem barTwistingCochainEquiv_comp_left (AA : AInfinityAlgebra R A)
    {hB : IsNonUnitalDGAlgebra ℬ dB} {hC : IsNonUnitalDGAlgebra 𝒞 dC}
    (g : NonUnitalDGAlgHom hB hC) (f : AInfinityHom AA hB.toAInfinityAlgebra) :
    (AA.barTwistingCochainEquiv hC (g.toAInfinityStrictHom.toAInfinityHom.comp f)).val =
      (g : B →ₗ[R] C) ∘ₗ (AA.barTwistingCochainEquiv hB f).val :=
  AInfinityHom.twistingCochain_comp_left g f

/-- Contravariant naturality of the bar twisting-cochain correspondence in the source `A∞`
algebra. -/
theorem barTwistingCochainEquiv_comp_right {hB : IsNonUnitalDGAlgebra ℬ dB}
    (f : AInfinityHom AA hB.toAInfinityAlgebra) (g : AInfinityHom AA' AA) :
    (AA'.barTwistingCochainEquiv hB (f.comp g)).val =
      (AA.barTwistingCochainEquiv hB f).val ∘ₗ (g.toBarCoalgHom : _ →ₗ[R] _) := by
  simp

end AInfinityAlgebra

end BarTwistingCochain

/-! ### The cobar DG algebra and the bar--cobar adjunction -/

section CobarAdjunction

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A'']
  [Ring B] [Algebra R B] [Ring C] [Algebra R C]
  {AA : AInfinityAlgebra R A} {AA' : AInfinityAlgebra R A'} {AA'' : AInfinityAlgebra R A''}
  {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace AInfinityAlgebra

/-- **The cobar construction `Ω Tᶜ(sA)` of an `A∞` algebra is a differential graded algebra.** -/
theorem isDGAlgebra_cobar (AA : AInfinityAlgebra R A) :
    IsDGAlgebra (tensorAlgebraPiece ((ReducedTensorWords.grading (AA.grading.shift 1)).shift (-1)))
      (cobarDifferential (ReducedTensorWords.grading (AA.grading.shift 1)) (deconcatenation R A)
        AA.barDifferential) :=
  AA.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential

/-- **The bar--cobar adjunction**: morphisms of differential graded algebras `Ω Tᶜ(sA) ⟶ B`
correspond bijectively to `A∞` morphisms `A ⟶ B`. -/
noncomputable def cobarAdjunctionEquiv (AA : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom AA.isDGAlgebra_cobar hB ≃
      AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  (AA.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hB).trans
    (AA.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm

/-- The Taylor map of `cobarAdjunctionEquiv φ` applies `φ ∘ ι` after the bar Koszul twist. -/
theorem taylor_cobarAdjunctionEquiv (AA : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom AA.isDGAlgebra_cobar hB) :
    (AA.cobarAdjunctionEquiv hB φ).taylor =
      (φ : _ →ₗ[R] B) ∘ₗ ι R ∘ₗ
        (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 := by
  refine LinearMap.ext fun z ↦ ?_
  simp [cobarAdjunctionEquiv]

/-- The **universal `A∞` morphism `A ⟶ Ω Tᶜ(sA)`**, corresponding to the identity DG algebra
morphism of `Ω Tᶜ(sA)` under the bar--cobar adjunction. -/
noncomputable def toCobar (AA : AInfinityAlgebra R A) :
    AInfinityHom AA AA.isDGAlgebra_cobar.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  AA.cobarAdjunctionEquiv AA.isDGAlgebra_cobar (DGAlgHom.id AA.isDGAlgebra_cobar)

@[simp]
theorem taylor_toCobar (AA : AInfinityAlgebra R A) :
    AA.toCobar.taylor =
      ι R ∘ₗ (ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 := by
  rw [toCobar, taylor_cobarAdjunctionEquiv]
  ext z
  simp

/-- On single letters, the universal `A∞` morphism `toCobar` sends `a` to
`-ι (ofLetter (σ_A a))`. -/
@[simp]
theorem linearPart_toCobar (AA : AInfinityAlgebra R A) :
    AA.toCobar.linearPart =
      -ι R ∘ₗ ofLetter R A ∘ₗ AA.grading.koszulTwist 1 := by
  ext a
  rw [toCobar, cobarAdjunctionEquiv, Equiv.trans_apply, barTwistingCochainEquiv_symm_apply,
    linearPart_ofTwistingCochain_apply]
  simp

theorem linearPart_toCobar_apply (AA : AInfinityAlgebra R A) (a : A) :
    AA.toCobar.linearPart a = -ι R (ofLetter R A (AA.grading.koszulTwist 1 a)) :=
  LinearMap.congr_fun AA.linearPart_toCobar a

/-- **Universal property of `toCobar`**: the bar--cobar adjunction sends every DG algebra morphism
`φ : Ω Tᶜ(sA) ⟶ B` to the composite `φ ∘ toCobar`. -/
@[simp]
theorem cobarAdjunctionEquiv_apply (AA : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom AA.isDGAlgebra_cobar hB) :
    AA.cobarAdjunctionEquiv hB φ =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp AA.toCobar := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_cobarAdjunctionEquiv, taylor_toCobar]
  simp

/-- On desuspended generators `s⁻¹ z`, the counit-side inverse of the bar--cobar adjunction
evaluates the Taylor map of `f` on `σ_C z`. -/
@[simp]
theorem cobarAdjunctionEquiv_symm_apply_ι (AA : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (z : ReducedTensorWords R A) :
    (AA.cobarAdjunctionEquiv hB).symm f (ι R z) =
      f.taylor ((ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 z) := by
  simp [cobarAdjunctionEquiv]

/-- Every `A∞` morphism `f : A ⟶ B` into a unital DG algebra factors uniquely through `toCobar` via
a DG algebra morphism `Ω Tᶜ(sA) ⟶ B`. -/
theorem eq_cobarAdjunctionEquiv_symm_iff (AA : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom AA.isDGAlgebra_cobar hB)
    (f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    φ = (AA.cobarAdjunctionEquiv hB).symm f ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp AA.toCobar = f := by
  rw [Equiv.eq_symm_apply, cobarAdjunctionEquiv_apply]

end AInfinityAlgebra

namespace AInfinityHom

/-- Functoriality of the cobar DG algebra along an `A∞` morphism `f : A ⟶ A'`. -/
noncomputable def cobarMap (f : AInfinityHom AA AA') :
    DGAlgHom AA.isDGAlgebra_cobar AA'.isDGAlgebra_cobar :=
  f.toBarCoalgHom.cobarMap

@[simp]
theorem cobarMap_ι (f : AInfinityHom AA AA') (z : ReducedTensorWords R A) :
    f.cobarMap (ι R z) = ι R (f.barMap z) := by
  simp [cobarMap]

@[simp]
theorem cobarMap_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).cobarMap = DGAlgHom.id AA.isDGAlgebra_cobar := by
  simp [cobarMap]

@[simp]
theorem cobarMap_comp (g : AInfinityHom AA' AA'') (f : AInfinityHom AA AA') :
    (g.comp f).cobarMap = g.cobarMap.comp f.cobarMap := by
  simp [cobarMap]

/-- Naturality of the universal `A∞` morphism `toCobar`: for every `A∞` morphism `f : A ⟶ A'`,
`(Ω B f) ∘ toCobar_A = toCobar_{A'} ∘ f`. -/
@[simp]
theorem cobarMap_comp_toCobar (f : AInfinityHom AA AA') :
    f.cobarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp AA.toCobar =
      AA'.toCobar.comp f := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_comp]
  simp only [AInfinityAlgebra.taylor_toCobar, LinearMap.comp_apply,
    AInfinityStrictHom.coe_toLinearMap, NonUnitalDGAlgHom.coe_toAInfinityStrictHom,
    DGAlgHom.toNonUnitalDGAlgHom_apply, cobarMap_ι]
  have hf := f.toBarCoalgHom.map_koszulTwist 1 z
  simp only [coe_toBarCoalgHom] at hf
  rw [← hf]

end AInfinityHom

namespace AInfinityAlgebra

/-- Naturality of the bar--cobar adjunction in the target DG algebra. -/
theorem cobarAdjunctionEquiv_comp_left (AA : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
    (ψ : DGAlgHom hB hC) (φ : DGAlgHom AA.isDGAlgebra_cobar hB) :
    AA.cobarAdjunctionEquiv hC (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (AA.cobarAdjunctionEquiv hB φ) := by
  rw [cobarAdjunctionEquiv_apply, cobarAdjunctionEquiv_apply,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc]

/-- Contravariant naturality of the bar--cobar adjunction in the source `A∞` algebra. -/
theorem cobarAdjunctionEquiv_comp_right {hB : IsDGAlgebra ℬ dB}
    (φ : DGAlgHom AA.isDGAlgebra_cobar hB) (g : AInfinityHom AA' AA) :
    AA'.cobarAdjunctionEquiv hB (φ.comp g.cobarMap) = (AA.cobarAdjunctionEquiv hB φ).comp g := by
  rw [cobarAdjunctionEquiv_apply, cobarAdjunctionEquiv_apply,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc, g.cobarMap_comp_toCobar,
    ← AInfinityHom.comp_assoc]

end AInfinityAlgebra

end CobarAdjunction

end TauCeti
