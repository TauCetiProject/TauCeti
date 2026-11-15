/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AsymptoticUnitaryEquivalence.Unitization
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate

/-!
# Asymptotic unitary equivalence with multiplier unitaries

For possibly nonunital C⋆-algebras `A` and `B`, this file defines asymptotic and strong asymptotic
unitary equivalence of `φ ψ : A →⋆ₙₐ[ℂ] B` implemented by continuous paths of unitaries in the
multiplier algebra `𝓜(ℂ, B)` (`MultiplierAsymptoticallyUnitarilyEquivalent` and
`MultiplierStronglyAsymptoticallyUnitarilyEquivalent`), phrased via composition with the canonical
isometric embedding `DoubleCentralizer.coeHom : B →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`.

Because `B` is an essential ideal in `𝓜(ℂ, B)` and `DoubleCentralizer.coe` is isometric, the
conjugates `(u t) * φ a * star (u t)` lie in `B` via `DoubleCentralizer.conjStarAlgAut` and
norm-convergence in `𝓜(ℂ, B)` coincides with norm-convergence in `B`.

## Main definitions

* `TauCeti.MultiplierAsymptoticallyUnitarilyEquivalent`: asymptotic unitary equivalence of
  `φ ψ : A →⋆ₙₐ[ℂ] B` via `C(ℝ≥0, unitary 𝓜(ℂ, B))`.
* `TauCeti.MultiplierStronglyAsymptoticallyUnitarilyEquivalent`: strong asymptotic unitary
  equivalence via `u : C(ℝ≥0, unitary 𝓜(ℂ, B))` with `u 0 = 1`.

## Main results

* `TauCeti.multiplierAsymptoticallyUnitarilyEquivalent_iff`,
  `TauCeti.multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff`, and
  `TauCeti.multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one`: intrinsic
  `B`-valued limit characterizations via `DoubleCentralizer.conjStarAlgAut`.
* Equivalence relation laws, `norm_eq`, `injective_iff`, `of_dense`, `precomp`, nondegenerate
  `postcomp` (via `NonUnitalStarAlgHom.extendToMultiplier`), `mapMatrix`, and `of_unitization` for
  both relations.
* Unital-target equivalences (`iff_asymptoticallyUnitarilyEquivalent` and
  `iff_stronglyAsymptoticallyUnitarilyEquivalent`): for a unital target `B`, the
  multiplier-unitary relations coincide with the target-unitary relations.

## References

* M. Rørdam, *Classification of nuclear, simple C*-algebras*, Encyclopaedia Math. Sci. 126,
  Springer, 2002, Definition 1.1.15 and §2.3.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra NNReal

namespace TauCeti

section NonUnitalTarget

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Asymptotic unitary equivalence of `⋆`-homomorphisms `φ ψ : A →⋆ₙₐ[ℂ] B` implemented by a
continuous path of unitaries in the multiplier algebra `𝓜(ℂ, B)`. -/
def MultiplierAsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  AsymptoticallyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
    ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ)

/-- Strong asymptotic unitary equivalence of `⋆`-homomorphisms `φ ψ : A →⋆ₙₐ[ℂ] B` implemented by
a continuous path `u : C(ℝ≥0, unitary 𝓜(ℂ, B))` starting at `u 0 = 1`. -/
def MultiplierStronglyAsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  StronglyAsymptoticallyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
    ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ)

/-- Unfolding `MultiplierAsymptoticallyUnitarilyEquivalent` as target asymptotic unitary
equivalence in `𝓜(ℂ, B)`. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ ↔
      AsymptoticallyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) :=
  Iff.rfl

/-- Unfolding `MultiplierStronglyAsymptoticallyUnitarilyEquivalent` as strong target asymptotic
unitary equivalence in `𝓜(ℂ, B)`. -/
theorem multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_coeHom (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      StronglyAsymptoticallyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) :=
  Iff.rfl

/-- Intrinsic `B`-valued limit characterization of
`MultiplierAsymptoticallyUnitarilyEquivalent`. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent_iff (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary 𝓜(ℂ, B)), ∀ a,
        Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a)) atTop (𝓝 (ψ a)) := by
  rw [multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom, asymptoticallyUnitarilyEquivalent_def]
  refine exists_congr fun u ↦ forall_congr' fun a ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
    ← DoubleCentralizer.coe_conjStarAlgAut_apply]
  exact (DoubleCentralizer.isometry_coe (𝕜 := ℂ)).isUniformInducing.isInducing
    |>.tendsto_nhds_iff.symm

/-- Intrinsic `B`-valued limit characterization of
`MultiplierStronglyAsymptoticallyUnitarilyEquivalent`. -/
theorem multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary 𝓜(ℂ, B)), u 0 = 1 ∧ ∀ a,
        Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a)) atTop (𝓝 (ψ a)) := by
  rw [multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_coeHom,
    stronglyAsymptoticallyUnitarilyEquivalent_def]
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun a ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
    ← DoubleCentralizer.coe_conjStarAlgAut_apply]
  exact (DoubleCentralizer.isometry_coe (𝕜 := ℂ)).isUniformInducing.isInducing
    |>.tendsto_nhds_iff.symm

/-- Strong multiplier asymptotic unitary equivalence holds if and only if some implementing path in
`unitary 𝓜(ℂ, B)` starts in the identity path component. -/
theorem multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary 𝓜(ℂ, B)), Joined (1 : unitary 𝓜(ℂ, B)) (u 0) ∧
        ∀ a, Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a)) atTop (𝓝 (ψ a)) := by
  rw [multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_coeHom,
    stronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one]
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun a ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
    ← DoubleCentralizer.coe_conjStarAlgAut_apply]
  exact (DoubleCentralizer.isometry_coe (𝕜 := ℂ)).isUniformInducing.isInducing
    |>.tendsto_nhds_iff.symm

/-- When `unitary 𝓜(ℂ, B)` is path-connected, strong and unconstrained multiplier asymptotic
unitary equivalence coincide. -/
theorem multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_of_pathConnectedSpace
    [PathConnectedSpace (unitary 𝓜(ℂ, B))] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      MultiplierAsymptoticallyUnitarilyEquivalent φ ψ :=
  stronglyAsymptoticallyUnitarilyEquivalent_iff_of_pathConnectedSpace

private theorem diagMultiplier_central {n : Type*} [Fintype n] (m : 𝓜(ℂ, B))
    (X Y : CStarMatrix n n B) :
    CStarMatrix.ofMatrix (Matrix.of fun i j ↦ m.snd (X i j)) * Y =
      X * CStarMatrix.ofMatrix (Matrix.of fun i j ↦ m.fst (Y i j)) := by
  ext i j
  simp [CStarMatrix.mul_apply, m.central]

/-- Entrywise diagonal embedding `𝓜(ℂ, B) →⋆ₐ[ℂ] 𝓜(ℂ, CStarMatrix n n B)`. -/
private def diagMultiplierStarAlgHom [PartialOrder B] [StarOrderedRing B]
    (n : Type*) [Fintype n] : 𝓜(ℂ, B) →⋆ₐ[ℂ] 𝓜(ℂ, CStarMatrix n n B) where
  toFun m := DoubleCentralizer.ofCentral ℂ
    (fun M ↦ CStarMatrix.ofMatrix (Matrix.of fun i j ↦ m.fst (M i j)))
    (fun M ↦ CStarMatrix.ofMatrix (Matrix.of fun i j ↦ m.snd (M i j)))
    (diagMultiplier_central m)
  map_one' := DoubleCentralizer.ext_fst_snd
    (fun M ↦ by ext i j; simp) (fun M ↦ by ext i j; simp)
  map_mul' m₁ m₂ := DoubleCentralizer.ext_fst_snd
    (fun M ↦ by ext i j; simp) (fun M ↦ by ext i j; simp)
  map_zero' := DoubleCentralizer.ext_fst_snd
    (fun M ↦ by ext i j; simp) (fun M ↦ by ext i j; simp)
  map_add' m₁ m₂ := DoubleCentralizer.ext_fst_snd
    (fun M ↦ by ext i j; simp) (fun M ↦ by ext i j; simp)
  commutes' c := DoubleCentralizer.ext_fst_snd
    (fun M ↦ by ext i j; simp [Algebra.algebraMap_eq_smul_one])
    (fun M ↦ by ext i j; simp [Algebra.algebraMap_eq_smul_one])
  map_star' m := DoubleCentralizer.ext_fst_snd
    (fun M ↦ by ext i j; simp [DoubleCentralizer.star_fst, CStarMatrix.star_apply])
    (fun M ↦ by ext i j; simp [DoubleCentralizer.star_snd, CStarMatrix.star_apply])

@[simp]
private theorem diagMultiplierStarAlgHom_fst [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (m : 𝓜(ℂ, B)) (M : CStarMatrix n n B) :
    (diagMultiplierStarAlgHom (B := B) n m).fst M =
      CStarMatrix.ofMatrix (Matrix.of fun i j ↦ m.fst (M i j)) := by
  simp [diagMultiplierStarAlgHom]

@[simp]
private theorem diagMultiplierStarAlgHom_snd [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (m : 𝓜(ℂ, B)) (M : CStarMatrix n n B) :
    (diagMultiplierStarAlgHom (B := B) n m).snd M =
      CStarMatrix.ofMatrix (Matrix.of fun i j ↦ m.snd (M i j)) := by
  simp [diagMultiplierStarAlgHom]

private theorem conjStarAlgAut_diagMultiplier [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (u : unitary 𝓜(ℂ, B)) (M : CStarMatrix n n B) :
    DoubleCentralizer.conjStarAlgAut
      (Unitary.map (StarMonoidHom.ofClass (diagMultiplierStarAlgHom (B := B) n)) u) M =
      CStarMatrix.ofMatrixL (Matrix.of fun i j ↦ DoubleCentralizer.conjStarAlgAut u (M i j)) := by
  have hentry (b : B) :
      (star (u : 𝓜(ℂ, B))).snd ((u : 𝓜(ℂ, B)).fst b) = DoubleCentralizer.conjStarAlgAut u b :=
    DoubleCentralizer.coe_injective (𝕜 := ℂ) <| by
      rw [DoubleCentralizer.coe_conjStarAlgAut_apply, DoubleCentralizer.mul_coe_eq_coe_fst,
        DoubleCentralizer.coe_mul_eq_coe_snd]
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  rw [DoubleCentralizer.coe_conjStarAlgAut_apply, DoubleCentralizer.mul_coe_eq_coe_fst,
    DoubleCentralizer.coe_mul_eq_coe_snd]
  refine congrArg (DoubleCentralizer.coe ℂ) ?_
  ext i j
  simp [StarMonoidHom.ofClass, ← map_star, hentry, ← CStarMatrix.ofMatrix_eq_ofMatrixL,
    CStarMatrix.ofMatrix_apply]

private theorem tendsto_multiplier_conj_matrix [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] {φ ψ : A →⋆ₙₐ[ℂ] B} {u : C(ℝ≥0, unitary 𝓜(ℂ, B))}
    (hu : ∀ a, Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a)) atTop (𝓝 (ψ a)))
    (M : CStarMatrix n n A) :
    Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut
      (Unitary.map (StarMonoidHom.ofClass (diagMultiplierStarAlgHom (B := B) n)) (u t))
      (CStarMatrix.mapₙₐ φ M)) atTop (𝓝 (CStarMatrix.mapₙₐ ψ M)) := by
  have htarget :
      CStarMatrix.mapₙₐ ψ M = CStarMatrix.ofMatrixL (Matrix.of fun i j ↦ ψ (M i j)) := by
    ext i j
    simp [← CStarMatrix.ofMatrix_eq_ofMatrixL, CStarMatrix.ofMatrix_apply]
  simp only [conjStarAlgAut_diagMultiplier, CStarMatrix.mapₙₐ_apply, htarget]
  exact CStarMatrix.ofMatrixL.continuous.continuousAt.tendsto.comp <|
    tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ hu (M i j)

namespace MultiplierAsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Conjugacy by a fixed unitary multiplier gives multiplier asymptotic unitary equivalence. -/
theorem of_unitary (u : unitary 𝓜(ℂ, B))
    (h : ∀ a, DoubleCentralizer.conjStarAlgAut u (φ a) = ψ a) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ :=
  (multiplierAsymptoticallyUnitarilyEquivalent_iff φ ψ).mpr
    ⟨ContinuousMap.const ℝ≥0 u, fun a ↦ by simp [h a]⟩

/-- Multiplier asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : MultiplierAsymptoticallyUnitarilyEquivalent φ φ :=
  AsymptoticallyUnitarilyEquivalent.refl _

/-- Multiplier asymptotic unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierAsymptoticallyUnitarilyEquivalent ψ φ :=
  AsymptoticallyUnitarilyEquivalent.symm h

/-- Multiplier asymptotic unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : MultiplierAsymptoticallyUnitarilyEquivalent ψ χ) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ χ :=
  AsymptoticallyUnitarilyEquivalent.trans h₁ h₂

/-- Multiplier asymptotic unitary equivalence is an equivalence relation. -/
theorem equivalence :
    Equivalence (MultiplierAsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Multiplier asymptotic unitary equivalence yields finite-set approximation in `B` by unitaries
of `𝓜(ℂ, B)`. -/
theorem exists_unitary_norm_sub_lt (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary 𝓜(ℂ, B), ∀ a ∈ F,
      ‖DoubleCentralizer.conjStarAlgAut u (φ a) - ψ a‖ < ε := by
  obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp
    (AsymptoticallyUnitarilyEquivalent.approximatelyUnitarilyEquivalent h) F ε hε
  refine ⟨u, fun a ha ↦ ?_⟩
  simpa only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
    ← DoubleCentralizer.coe_conjStarAlgAut_apply, ← DoubleCentralizer.coe_sub,
    DoubleCentralizer.norm_coe] using hu a ha

/-- Maps that are multiplier asymptotically unitarily equivalent have the same pointwise norm. -/
theorem norm_eq (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ := by
  simpa only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
    DoubleCentralizer.norm_coe] using AsymptoticallyUnitarilyEquivalent.norm_eq h a

/-- Multiplier asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ := by
  rw [injective_iff_map_eq_zero φ, injective_iff_map_eq_zero ψ]
  exact forall_congr' fun a ↦ by
    rw [← norm_eq_zero (a := φ a), ← norm_eq_zero (a := ψ a), h.norm_eq a]

/-- Pointwise convergence on a dense subset along a unitary multiplier path suffices for
multiplier asymptotic unitary equivalence. -/
theorem of_dense {s : Set A} (hs : Dense s) (u : C(ℝ≥0, unitary 𝓜(ℂ, B)))
    (hu : ∀ a ∈ s, Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a))
      atTop (𝓝 (ψ a))) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ :=
  AsymptoticallyUnitarilyEquivalent.of_dense hs u fun a ha ↦ by
    simp only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
      ← DoubleCentralizer.coe_conjStarAlgAut_apply]
    exact ((DoubleCentralizer.isometry_coe (𝕜 := ℂ)).continuous.tendsto (ψ a)).comp (hu a ha)

/-- Precomposition preserves multiplier asymptotic unitary equivalence. -/
theorem precomp [NonUnitalCStarAlgebra C]
    (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    MultiplierAsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  simpa only [MultiplierAsymptoticallyUnitarilyEquivalent, NonUnitalStarAlgHom.comp_assoc] using
    AsymptoticallyUnitarilyEquivalent.precomp h ρ

/-- Postcomposition with a nondegenerate `⋆`-homomorphism `ρ : B →⋆ₙₐ[ℂ] C` preserves multiplier
asymptotic unitary equivalence via `ρ`'s unital extension to multiplier algebras. -/
theorem postcomp [NonUnitalCStarAlgebra C]
    (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C)
    (hρ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).IsMultiplierNondegenerate) :
    MultiplierAsymptoticallyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hcomp :
      (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).extendToMultiplier
          hρ).toNonUnitalStarAlgHom.comp (DoubleCentralizer.coeHom (𝕜 := ℂ)) =
        (DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  have h' := AsymptoticallyUnitarilyEquivalent.postcomp h
    (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).extendToMultiplier hρ)
  rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc, hcomp,
    NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_assoc] at h'

/-- Finite matrix amplification preserves multiplier asymptotic unitary equivalence. -/
theorem mapMatrix [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierAsymptoticallyUnitarilyEquivalent
      (CStarMatrix.mapₙₐ φ : CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix n n B)
      (CStarMatrix.mapₙₐ ψ) := by
  rw [multiplierAsymptoticallyUnitarilyEquivalent_iff] at h ⊢
  obtain ⟨u, hu⟩ := h
  let ρ := diagMultiplierStarAlgHom (B := B) n
  refine ⟨⟨fun t ↦ Unitary.map (StarMonoidHom.ofClass ρ) (u t),
    Continuous.subtype_mk ((map_continuous ρ).comp (continuous_subtype_val.comp u.continuous)) _⟩,
    fun M ↦ ?_⟩
  simpa [ρ] using tendsto_multiplier_conj_matrix hu M

private theorem starLift_coeHom_comp_inr :
    (Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B))
        ).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ B) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) := by
  rw [← Unitization.starLift_symm_apply]
  exact Unitization.starLift.symm_apply_apply _

/-- Unitization asymptotic unitary equivalence implies multiplier asymptotic unitary equivalence via
`Unitization.starLift` applied to `B →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`. -/
theorem of_unitization (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ := by
  rw [unitizationAsymptoticallyUnitarilyEquivalent_iff_inr] at h
  have h' := AsymptoticallyUnitarilyEquivalent.postcomp h
    (Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B)))
  rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
    starLift_coeHom_comp_inr] at h'

end MultiplierAsymptoticallyUnitarilyEquivalent

namespace MultiplierStronglyAsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Strong multiplier asymptotic unitary equivalence implies unconstrained multiplier asymptotic
unitary equivalence. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent
    (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ :=
  StronglyAsymptoticallyUnitarilyEquivalent.asymptoticallyUnitarilyEquivalent h

/-- Conjugacy by a unitary multiplier in the identity path component gives strong multiplier
asymptotic unitary equivalence. -/
theorem of_joined_one (u : unitary 𝓜(ℂ, B)) (hu : Joined (1 : unitary 𝓜(ℂ, B)) u)
    (h : ∀ a, DoubleCentralizer.conjStarAlgAut u (φ a) = ψ a) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one.mpr
    ⟨ContinuousMap.const ℝ≥0 u, hu, fun a ↦ by simp [h a]⟩

/-- Conjugacy by a unitary multiplier at distance strictly less than `2` from `1` gives strong
multiplier asymptotic unitary equivalence. -/
theorem of_norm_sub_one_lt_two (u : unitary 𝓜(ℂ, B)) (hu : ‖(u : 𝓜(ℂ, B)) - 1‖ < 2)
    (h : ∀ a, DoubleCentralizer.conjStarAlgAut u (φ a) = ψ a) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  of_joined_one u (Unitary.joined 1 u hu) h

/-- Strong multiplier asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ φ :=
  StronglyAsymptoticallyUnitarilyEquivalent.refl _

/-- Strong multiplier asymptotic unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent ψ φ :=
  StronglyAsymptoticallyUnitarilyEquivalent.symm h

/-- Strong multiplier asymptotic unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : MultiplierStronglyAsymptoticallyUnitarilyEquivalent ψ χ) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ χ :=
  StronglyAsymptoticallyUnitarilyEquivalent.trans h₁ h₂

/-- Strong multiplier asymptotic unitary equivalence is an equivalence relation. -/
theorem equivalence :
    Equivalence (MultiplierStronglyAsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Maps that are strongly multiplier asymptotically unitarily equivalent have the same pointwise
norm. -/
theorem norm_eq (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ :=
  h.multiplierAsymptoticallyUnitarilyEquivalent.norm_eq a

/-- Strong multiplier asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ :=
  h.multiplierAsymptoticallyUnitarilyEquivalent.injective_iff

/-- Pointwise convergence on a dense subset along a unitary multiplier path starting at `1`
suffices for strong multiplier asymptotic unitary equivalence. -/
theorem of_dense {s : Set A} (hs : Dense s) (u : C(ℝ≥0, unitary 𝓜(ℂ, B))) (hu0 : u 0 = 1)
    (hu : ∀ a ∈ s, Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a))
      atTop (𝓝 (ψ a))) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  StronglyAsymptoticallyUnitarilyEquivalent.of_dense hs u hu0 fun a ha ↦ by
    simp only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
      ← DoubleCentralizer.coe_conjStarAlgAut_apply]
    exact ((DoubleCentralizer.isometry_coe (𝕜 := ℂ)).continuous.tendsto (ψ a)).comp (hu a ha)

/-- Precomposition preserves strong multiplier asymptotic unitary equivalence. -/
theorem precomp [NonUnitalCStarAlgebra C]
    (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  simpa only [MultiplierStronglyAsymptoticallyUnitarilyEquivalent,
    NonUnitalStarAlgHom.comp_assoc] using
    StronglyAsymptoticallyUnitarilyEquivalent.precomp h ρ

/-- Postcomposition with a nondegenerate `⋆`-homomorphism `ρ : B →⋆ₙₐ[ℂ] C` preserves strong
multiplier asymptotic unitary equivalence. -/
theorem postcomp [NonUnitalCStarAlgebra C]
    (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C)
    (hρ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).IsMultiplierNondegenerate) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hcomp :
      (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).extendToMultiplier
          hρ).toNonUnitalStarAlgHom.comp (DoubleCentralizer.coeHom (𝕜 := ℂ)) =
        (DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  have h' := StronglyAsymptoticallyUnitarilyEquivalent.postcomp h
    (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).extendToMultiplier hρ)
  rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc, hcomp,
    NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_assoc] at h'

/-- Finite matrix amplification preserves strong multiplier asymptotic unitary equivalence. -/
theorem mapMatrix [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (h : MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent
      (CStarMatrix.mapₙₐ φ : CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix n n B)
      (CStarMatrix.mapₙₐ ψ) := by
  rw [multiplierStronglyAsymptoticallyUnitarilyEquivalent_iff] at h ⊢
  obtain ⟨u, hu0, hu⟩ := h
  let ρ := diagMultiplierStarAlgHom (B := B) n
  let v : C(ℝ≥0, unitary 𝓜(ℂ, CStarMatrix n n B)) :=
    ⟨fun t ↦ Unitary.map (StarMonoidHom.ofClass ρ) (u t),
      Continuous.subtype_mk ((map_continuous ρ).comp (continuous_subtype_val.comp u.continuous)) _⟩
  refine ⟨v, ?_, fun M ↦ ?_⟩
  · exact Subtype.ext (by simp [v, ρ, hu0, StarMonoidHom.ofClass])
  · simpa [v, ρ] using tendsto_multiplier_conj_matrix hu M

/-- Strong unitization asymptotic unitary equivalence implies strong multiplier asymptotic unitary
equivalence via `Unitization.starLift` applied to `B →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`. -/
theorem of_unitization (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ := by
  rw [unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_inr] at h
  have h' := StronglyAsymptoticallyUnitarilyEquivalent.postcomp h
    (Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B)))
  rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
    MultiplierAsymptoticallyUnitarilyEquivalent.starLift_coeHom_comp_inr] at h'

end MultiplierStronglyAsymptoticallyUnitarilyEquivalent

end NonUnitalTarget

section UnitalTarget

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Evaluation of the left centralizer at `1 : B` as a unital `⋆`-homomorphism `𝓜(ℂ, B) →⋆ₐ[ℂ] B`
retracting `DoubleCentralizer.coeHom`. -/
private def evalOneStarAlgHom : 𝓜(ℂ, B) →⋆ₐ[ℂ] B where
  toFun m := m.fst 1
  map_one' := by simp
  map_mul' m n := by
    simp only [DoubleCentralizer.mul_fst, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply]
    simpa using m.fst_mul 1 (n.fst 1)
  map_zero' := by simp
  map_add' m n := by simp
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' m := by
    have hsnd : m.snd 1 = m.fst 1 := by simpa using m.central 1 1
    simp [DoubleCentralizer.star_fst, hsnd]

private theorem evalOneStarAlgHom_comp_coeHom :
    (evalOneStarAlgHom (B := B)).toNonUnitalStarAlgHom.comp
        (DoubleCentralizer.coeHom (𝕜 := ℂ)) =
      NonUnitalStarAlgHom.id ℂ B :=
  NonUnitalStarAlgHom.ext fun _ ↦ by simp [evalOneStarAlgHom]

/-- For a unital target `B`, multiplier asymptotic unitary equivalence coincides with target
asymptotic unitary equivalence. -/
theorem MultiplierAsymptoticallyUnitarilyEquivalent.iff_asymptoticallyUnitarilyEquivalent
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ ↔
      AsymptoticallyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    have h' := AsymptoticallyUnitarilyEquivalent.postcomp h (evalOneStarAlgHom (B := B))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
      evalOneStarAlgHom_comp_coeHom, NonUnitalStarAlgHom.id_comp,
      NonUnitalStarAlgHom.id_comp] at h'
  · refine fun h ↦ .of_unitization ?_
    exact UnitizationAsymptoticallyUnitarilyEquivalent.iff_asymptoticallyUnitarilyEquivalent.mpr h

namespace MultiplierStronglyAsymptoticallyUnitarilyEquivalent

/-- For a unital target `B`, strong multiplier asymptotic unitary equivalence coincides with strong
target asymptotic unitary equivalence. -/
theorem iff_stronglyAsymptoticallyUnitarilyEquivalent {φ ψ : A →⋆ₙₐ[ℂ] B} :
    MultiplierStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      StronglyAsymptoticallyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    have h' := StronglyAsymptoticallyUnitarilyEquivalent.postcomp h (evalOneStarAlgHom (B := B))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
      evalOneStarAlgHom_comp_coeHom, NonUnitalStarAlgHom.id_comp,
      NonUnitalStarAlgHom.id_comp] at h'
  · open UnitizationStronglyAsymptoticallyUnitarilyEquivalent renaming
      iff_stronglyAsymptoticallyUnitarilyEquivalent → hU in
    exact fun h ↦ .of_unitization (hU.mpr h)

end MultiplierStronglyAsymptoticallyUnitarilyEquivalent

end UnitalTarget

end TauCeti
