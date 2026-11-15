/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AsymptoticUnitaryEquivalence.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Asymptotic unitary equivalence via the minimal unitization

For star homomorphisms `φ, ψ : A →⋆ₙₐ[ℂ] B` into a possibly nonunital C⋆-algebra `B`, this file
defines asymptotic unitary equivalence and strong asymptotic unitary equivalence implemented by
continuous paths in `unitary (Unitization ℂ B)`:
* `TauCeti.UnitizationAsymptoticallyUnitarilyEquivalent`: the target-unitary relation for the
  composites with `Unitization.inrNonUnitalStarAlgHom ℂ B`, with no condition at `0`;
* `TauCeti.UnitizationStronglyAsymptoticallyUnitarilyEquivalent`: the stronger relation requiring
  `u 0 = 1`.

Because `B` sits isometrically as a two-sided ideal in `Unitization ℂ B`, conjugation by any
unitary of `Unitization ℂ B` preserves `B`, and convergence in `Unitization ℂ B` coincides with
convergence of the `B`-components (`unitizationAsymptoticallyUnitarilyEquivalent_iff` and
`unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff`). Unlike the multiplier-algebra version,
every nonunital star homomorphism `ρ : B →⋆ₙₐ[ℂ] C` lifts to a unital star homomorphism
`Unitization.starMap ρ : Unitization ℂ B →⋆ₐ[ℂ] Unitization ℂ C`, so postcomposition requires no
nondegeneracy assumption. When `B` is already unital, both relations agree with their target-unitary
counterparts (`UnitizationAsymptoticallyUnitarilyEquivalent.iff_asymptoticallyUnitarilyEquivalent`
and its `StronglyAsymptoticallyUnitarilyEquivalent` analogue).

## References

* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Encyclopaedia of Mathematical
  Sciences 126, Springer, 2002, Definition 1.1.15 and §2.1.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra NNReal

namespace TauCeti

section NonUnitalTarget

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Asymptotic unitary equivalence implemented by a continuous path of unitaries in the minimal
unitization `Unitization ℂ B`, with no condition at `0`. -/
def UnitizationAsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  AsymptoticallyUnitarilyEquivalent
    ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
    ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ)

/-- Unfolding characterization of `UnitizationAsymptoticallyUnitarilyEquivalent` via the canonical
inclusion into `Unitization ℂ B`. -/
theorem unitizationAsymptoticallyUnitarilyEquivalent_iff_inr (φ ψ : A →⋆ₙₐ[ℂ] B) :
    UnitizationAsymptoticallyUnitarilyEquivalent φ ψ ↔
      AsymptoticallyUnitarilyEquivalent
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ) :=
  Iff.rfl

/-- Strong asymptotic unitary equivalence implemented by a continuous path of unitaries in
`Unitization ℂ B` starting at `1`. -/
def UnitizationStronglyAsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  StronglyAsymptoticallyUnitarilyEquivalent
    ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
    ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ)

/-- Unfolding characterization of `UnitizationStronglyAsymptoticallyUnitarilyEquivalent` via the
canonical inclusion into `Unitization ℂ B`. -/
theorem unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_inr (φ ψ : A →⋆ₙₐ[ℂ] B) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      StronglyAsymptoticallyUnitarilyEquivalent
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ) :=
  Iff.rfl

private theorem inr_snd_conj_inr (x : Unitization ℂ B) (b : B) :
    (((x * (b : Unitization ℂ B) * star x).snd : B) : Unitization ℂ B) =
      x * (b : Unitization ℂ B) * star x :=
  Unitization.ext (by simp) (by simp)

private theorem tendsto_unitization_conj_iff {ι : Type*} {l : Filter ι}
    (u : ι → unitary (Unitization ℂ B)) (b c : B) :
    Tendsto (fun i ↦ (u i : Unitization ℂ B) * (b : Unitization ℂ B) *
        star (u i : Unitization ℂ B)) l (𝓝 (c : Unitization ℂ B)) ↔
      Tendsto (fun i ↦ ((u i : Unitization ℂ B) * (b : Unitization ℂ B) *
        star (u i : Unitization ℂ B)).snd) l (𝓝 c) := by
  conv_lhs =>
    enter [1, i]
    rw [← inr_snd_conj_inr]
  exact (Unitization.isometry_inr (𝕜 := ℂ) (A := B)).isUniformInducing.isInducing
    |>.tendsto_nhds_iff.symm

/-- Intrinsic `B`-valued limit characterization of
`UnitizationAsymptoticallyUnitarilyEquivalent`. -/
theorem unitizationAsymptoticallyUnitarilyEquivalent_iff (φ ψ : A →⋆ₙₐ[ℂ] B) :
    UnitizationAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary (Unitization ℂ B)), ∀ a,
        Tendsto (fun t ↦ ((u t : Unitization ℂ B) * (φ a : Unitization ℂ B) *
          star (u t : Unitization ℂ B)).snd) atTop (𝓝 (ψ a)) := by
  simp only [unitizationAsymptoticallyUnitarilyEquivalent_iff_inr,
    asymptoticallyUnitarilyEquivalent_def, NonUnitalStarAlgHom.comp_apply,
    Unitization.inrNonUnitalStarAlgHom_apply, tendsto_unitization_conj_iff]

/-- Intrinsic `B`-valued limit characterization of
`UnitizationStronglyAsymptoticallyUnitarilyEquivalent`. -/
theorem unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff (φ ψ : A →⋆ₙₐ[ℂ] B) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary (Unitization ℂ B)), u 0 = 1 ∧ ∀ a,
        Tendsto (fun t ↦ ((u t : Unitization ℂ B) * (φ a : Unitization ℂ B) *
          star (u t : Unitization ℂ B)).snd) atTop (𝓝 (ψ a)) := by
  simp only [unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_inr,
    stronglyAsymptoticallyUnitarilyEquivalent_def, NonUnitalStarAlgHom.comp_apply,
    Unitization.inrNonUnitalStarAlgHom_apply, tendsto_unitization_conj_iff]

/-- Strong unitization asymptotic unitary equivalence holds if and only if some implementing path in
`unitary (Unitization ℂ B)` starts in the identity path component. -/
theorem unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary (Unitization ℂ B)), Joined (1 : unitary (Unitization ℂ B)) (u 0) ∧
        ∀ a, Tendsto (fun t ↦ ((u t : Unitization ℂ B) * (φ a : Unitization ℂ B) *
          star (u t : Unitization ℂ B)).snd) atTop (𝓝 (ψ a)) := by
  simp only [unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_inr,
    stronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one,
    NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
    tendsto_unitization_conj_iff]

/-- When `unitary (Unitization ℂ B)` is path-connected, strong and unconstrained unitization
asymptotic unitary equivalence coincide. -/
theorem unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_of_pathConnectedSpace
    [PathConnectedSpace (unitary (Unitization ℂ B))] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      UnitizationAsymptoticallyUnitarilyEquivalent φ ψ :=
  stronglyAsymptoticallyUnitarilyEquivalent_iff_of_pathConnectedSpace

/-- Scalar-diagonal nonunital star homomorphism `B →⋆ₙₐ[ℂ] CStarMatrix n n B`. -/
private def diagonalMatrixNonUnitalStarAlgHom (n : Type*) [Fintype n] [DecidableEq n] :
    B →⋆ₙₐ[ℂ] CStarMatrix n n B where
  toFun b := CStarMatrix.ofMatrix (Matrix.diagonal fun _ : n ↦ b)
  map_smul' c b := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  map_zero' := by
    ext i j
    simp
  map_add' b₁ b₂ := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  map_mul' b₁ b₂ := by
    ext i j
    simp [CStarMatrix.mul_apply, Matrix.diagonal_apply]
  map_star' b := by
    ext i j
    by_cases hij : i = j <;> simp [CStarMatrix.star_apply, hij, eq_comm]

/-- Scalar-diagonal unitary conjugation in `Unitization ℂ (CStarMatrix n n B)` acts entrywise. -/
private theorem tendsto_unitization_conj_matrix [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] [DecidableEq n] {φ ψ : A →⋆ₙₐ[ℂ] B}
    {u : C(ℝ≥0, unitary (Unitization ℂ B))}
    (hu : ∀ a, Tendsto (fun t ↦ ((u t : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u t : Unitization ℂ B)).snd) atTop (𝓝 (ψ a)))
    (M : CStarMatrix n n A) :
    let ρ := Unitization.starMap (diagonalMatrixNonUnitalStarAlgHom n : B →⋆ₙₐ[ℂ] _)
    Tendsto (fun t ↦ ((ρ (u t) : Unitization ℂ (CStarMatrix n n B)) *
      (CStarMatrix.mapₙₐ φ M : Unitization ℂ (CStarMatrix n n B)) *
      star (ρ (u t) : Unitization ℂ (CStarMatrix n n B))).snd)
      atTop (𝓝 (CStarMatrix.mapₙₐ ψ M)) := by
  intro ρ
  have hentry (x : Unitization ℂ B) :
      ((ρ x * (CStarMatrix.mapₙₐ φ M : Unitization ℂ (CStarMatrix n n B)) * star (ρ x)).snd) =
        CStarMatrix.ofMatrixL (Matrix.of fun i j ↦
          (x * (φ (M i j) : Unitization ℂ B) * star x).snd) := by
    induction x using Unitization.ind with
    | inl_add_inr r b =>
      ext i j
      simp [ρ, diagonalMatrixNonUnitalStarAlgHom, Unitization.algebraMap_eq_inl,
        CStarMatrix.mul_apply, CStarMatrix.star_apply, Matrix.diagonal_apply, apply_ite star,
        ← CStarMatrix.ofMatrix_eq_ofMatrixL, CStarMatrix.ofMatrix_apply]
  have htarget :
      CStarMatrix.mapₙₐ ψ M = CStarMatrix.ofMatrixL (Matrix.of fun i j ↦ ψ (M i j)) := by
    ext i j
    simp [← CStarMatrix.ofMatrix_eq_ofMatrixL, CStarMatrix.ofMatrix_apply]
  simp only [hentry, htarget]
  exact CStarMatrix.ofMatrixL.continuous.continuousAt.tendsto.comp <|
    tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ hu (M i j)

namespace UnitizationAsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- A fixed unitary of `Unitization ℂ B` conjugating `φ` to `ψ` gives unitization asymptotic
unitary equivalence. -/
theorem of_unitary (u : unitary (Unitization ℂ B))
    (h : ∀ a, ((u : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u : Unitization ℂ B)).snd = ψ a) :
    UnitizationAsymptoticallyUnitarilyEquivalent φ ψ :=
  AsymptoticallyUnitarilyEquivalent.of_unitary u fun a ↦ by
    simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
      ← h a] using (inr_snd_conj_inr (u : Unitization ℂ B) (φ a)).symm

/-- Unitization asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : UnitizationAsymptoticallyUnitarilyEquivalent φ φ :=
  AsymptoticallyUnitarilyEquivalent.refl _

/-- Unitization asymptotic unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) :
    UnitizationAsymptoticallyUnitarilyEquivalent ψ φ :=
  AsymptoticallyUnitarilyEquivalent.symm h

/-- Unitization asymptotic unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : UnitizationAsymptoticallyUnitarilyEquivalent ψ χ) :
    UnitizationAsymptoticallyUnitarilyEquivalent φ χ :=
  AsymptoticallyUnitarilyEquivalent.trans h₁ h₂

/-- Unitization asymptotic unitary equivalence is an equivalence relation. -/
theorem equivalence :
    Equivalence (UnitizationAsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Unitization asymptotic unitary equivalence yields finite-set approximation in `B` by unitaries
of `Unitization ℂ B`. -/
theorem exists_unitary_norm_sub_lt (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Unitization ℂ B), ∀ a ∈ F,
      ‖((u : Unitization ℂ B) * (φ a : Unitization ℂ B) *
        star (u : Unitization ℂ B)).snd - ψ a‖ < ε := by
  obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp
    (AsymptoticallyUnitarilyEquivalent.approximatelyUnitarilyEquivalent h) F ε hε
  refine ⟨u, fun a ha ↦ ?_⟩
  rw [← Unitization.norm_inr (𝕜 := ℂ), Unitization.inr_sub, inr_snd_conj_inr]
  exact hu a ha

/-- Unitization asymptotically unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ := by
  simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
    Unitization.norm_inr] using AsymptoticallyUnitarilyEquivalent.norm_eq h a

/-- Unitization asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ := by
  rw [injective_iff_map_eq_zero φ, injective_iff_map_eq_zero ψ]
  exact forall_congr' fun a ↦ by
    rw [← norm_eq_zero (a := φ a), ← norm_eq_zero (a := ψ a), h.norm_eq]

/-- Pointwise convergence on a dense subset along a unitary path in `Unitization ℂ B` suffices for
unitization asymptotic unitary equivalence. -/
theorem of_dense {s : Set A} (hs : Dense s) (u : C(ℝ≥0, unitary (Unitization ℂ B)))
    (hu : ∀ a ∈ s, Tendsto (fun t ↦ ((u t : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u t : Unitization ℂ B)).snd) atTop (𝓝 (ψ a))) :
    UnitizationAsymptoticallyUnitarilyEquivalent φ ψ :=
  AsymptoticallyUnitarilyEquivalent.of_dense hs u fun a ha ↦ by
    simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
      tendsto_unitization_conj_iff] using hu a ha

/-- Precomposition preserves unitization asymptotic unitary equivalence. -/
theorem precomp [NonUnitalCStarAlgebra C]
    (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    UnitizationAsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  simpa only [UnitizationAsymptoticallyUnitarilyEquivalent, NonUnitalStarAlgHom.comp_assoc] using
    AsymptoticallyUnitarilyEquivalent.precomp h ρ

/-- Arbitrary nonunital postcomposition preserves unitization asymptotic unitary equivalence,
without any nondegeneracy assumption. -/
theorem postcomp [NonUnitalCStarAlgebra C]
    (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C) :
    UnitizationAsymptoticallyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hcomp :
      (Unitization.starMap ρ).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ B) =
        (Unitization.inrNonUnitalStarAlgHom ℂ C).comp ρ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  have h' := AsymptoticallyUnitarilyEquivalent.postcomp h (Unitization.starMap ρ)
  rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc, hcomp,
    NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_assoc] at h'

/-- Finite matrix amplification preserves unitization asymptotic unitary equivalence. -/
theorem mapMatrix [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (h : UnitizationAsymptoticallyUnitarilyEquivalent φ ψ) :
    UnitizationAsymptoticallyUnitarilyEquivalent
      (CStarMatrix.mapₙₐ φ : CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix n n B)
      (CStarMatrix.mapₙₐ ψ) := by
  classical
  rw [unitizationAsymptoticallyUnitarilyEquivalent_iff] at h ⊢
  obtain ⟨u, hu⟩ := h
  let ρ := Unitization.starMap (diagonalMatrixNonUnitalStarAlgHom n : B →⋆ₙₐ[ℂ] _)
  let v : C(ℝ≥0, unitary (Unitization ℂ (CStarMatrix n n B))) :=
    ⟨fun t ↦ Unitary.map (StarMonoidHom.ofClass ρ) (u t),
      Continuous.subtype_mk ((map_continuous ρ).comp (continuous_subtype_val.comp u.continuous)) _⟩
  refine ⟨v, fun M ↦ ?_⟩
  simpa [v, ρ, StarMonoidHom.ofClass] using tendsto_unitization_conj_matrix hu M

end UnitizationAsymptoticallyUnitarilyEquivalent

namespace UnitizationStronglyAsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Strong unitization asymptotic unitary equivalence implies unconstrained unitization asymptotic
unitary equivalence. -/
theorem unitizationAsymptoticallyUnitarilyEquivalent
    (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    UnitizationAsymptoticallyUnitarilyEquivalent φ ψ :=
  StronglyAsymptoticallyUnitarilyEquivalent.asymptoticallyUnitarilyEquivalent h

/-- Conjugate maps by a unitary in the identity path component of `unitary (Unitization ℂ B)` are
strongly asymptotically unitarily equivalent. -/
theorem of_joined_one (u : unitary (Unitization ℂ B))
    (hu : Joined (1 : unitary (Unitization ℂ B)) u)
    (h : ∀ a, ((u : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u : Unitization ℂ B)).snd = ψ a) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  StronglyAsymptoticallyUnitarilyEquivalent.of_joined_one u hu fun a ↦ by
    simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
      ← h a] using (inr_snd_conj_inr (u : Unitization ℂ B) (φ a)).symm

/-- Conjugate maps by a unitary of `Unitization ℂ B` within distance `2` of `1` are strongly
asymptotically unitarily equivalent. -/
theorem of_norm_sub_one_lt_two (u : unitary (Unitization ℂ B))
    (hu : ‖(u : Unitization ℂ B) - 1‖ < 2)
    (h : ∀ a, ((u : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u : Unitization ℂ B)).snd = ψ a) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  of_joined_one u (Unitary.joined 1 u hu) h

/-- Strong unitization asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ φ :=
  StronglyAsymptoticallyUnitarilyEquivalent.refl _

/-- Strong unitization asymptotic unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent ψ φ :=
  StronglyAsymptoticallyUnitarilyEquivalent.symm h

/-- Strong unitization asymptotic unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : UnitizationStronglyAsymptoticallyUnitarilyEquivalent ψ χ) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ χ :=
  StronglyAsymptoticallyUnitarilyEquivalent.trans h₁ h₂

/-- Strong unitization asymptotic unitary equivalence is an equivalence relation. -/
theorem equivalence :
    Equivalence (UnitizationStronglyAsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Strong unitization asymptotically unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ :=
  h.unitizationAsymptoticallyUnitarilyEquivalent.norm_eq a

/-- Strong unitization asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ :=
  h.unitizationAsymptoticallyUnitarilyEquivalent.injective_iff

/-- Pointwise convergence on a dense subset along a unitary path in `Unitization ℂ B` starting at
`1` suffices for strong unitization asymptotic unitary equivalence. -/
theorem of_dense {s : Set A} (hs : Dense s) (u : C(ℝ≥0, unitary (Unitization ℂ B)))
    (hu0 : u 0 = 1)
    (hu : ∀ a ∈ s, Tendsto (fun t ↦ ((u t : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u t : Unitization ℂ B)).snd) atTop (𝓝 (ψ a))) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  StronglyAsymptoticallyUnitarilyEquivalent.of_dense hs u hu0 fun a ha ↦ by
    simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
      tendsto_unitization_conj_iff] using hu a ha

/-- Precomposition preserves strong unitization asymptotic unitary equivalence. -/
theorem precomp [NonUnitalCStarAlgebra C]
    (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  simpa only [UnitizationStronglyAsymptoticallyUnitarilyEquivalent,
    NonUnitalStarAlgHom.comp_assoc] using
    StronglyAsymptoticallyUnitarilyEquivalent.precomp h ρ

/-- Arbitrary nonunital postcomposition preserves strong unitization asymptotic unitary equivalence,
without any nondegeneracy assumption. -/
theorem postcomp [NonUnitalCStarAlgebra C]
    (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hcomp :
      (Unitization.starMap ρ).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ B) =
        (Unitization.inrNonUnitalStarAlgHom ℂ C).comp ρ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  have h' := StronglyAsymptoticallyUnitarilyEquivalent.postcomp h (Unitization.starMap ρ)
  rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc, hcomp,
    NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_assoc] at h'

/-- Finite matrix amplification preserves strong unitization asymptotic unitary equivalence. -/
theorem mapMatrix [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] (h : UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent
      (CStarMatrix.mapₙₐ φ : CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix n n B)
      (CStarMatrix.mapₙₐ ψ) := by
  classical
  rw [unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff] at h ⊢
  obtain ⟨u, hu0, hu⟩ := h
  let ρ := Unitization.starMap (diagonalMatrixNonUnitalStarAlgHom n : B →⋆ₙₐ[ℂ] _)
  let v : C(ℝ≥0, unitary (Unitization ℂ (CStarMatrix n n B))) :=
    ⟨fun t ↦ Unitary.map (StarMonoidHom.ofClass ρ) (u t),
      Continuous.subtype_mk ((map_continuous ρ).comp (continuous_subtype_val.comp u.continuous)) _⟩
  refine ⟨v, ?_, fun M ↦ ?_⟩
  · exact Subtype.ext (by simp [v, ρ, hu0, StarMonoidHom.ofClass])
  · simpa [v, ρ, StarMonoidHom.ofClass] using tendsto_unitization_conj_matrix hu M

end UnitizationStronglyAsymptoticallyUnitarilyEquivalent

end NonUnitalTarget

section UnitalTarget

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

private theorem star_one_add_inr_sub_one (x : B) :
    star (1 + ((x - 1 : B) : Unitization ℂ B)) =
      1 + ((star x - 1 : B) : Unitization ℂ B) := by
  simp [← Unitization.inr_star, Unitization.inr_sub]

/-- Lift a unitary of a unital C⋆-algebra `B` to `1 + inr (u - 1)` in `Unitization ℂ B`. -/
private def liftUnitaryToUnitization (u : unitary B) : unitary (Unitization ℂ B) :=
  ⟨1 + (((u : B) - 1 : B) : Unitization ℂ B), by
    have hmul (x y : B) :
        (1 + ((x - 1 : B) : Unitization ℂ B)) * (1 + ((y - 1 : B) : Unitization ℂ B)) =
          1 + ((x * y - 1 : B) : Unitization ℂ B) := by
      have hring : (x - 1) + ((y - 1) + (x - 1) * (y - 1)) = x * y - 1 := by
        simp only [mul_sub, sub_mul, mul_one, one_mul]
        abel
      rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, ← Unitization.inr_mul,
        add_assoc, ← Unitization.inr_add, ← Unitization.inr_add, hring]
    rw [Unitary.mem_iff]
    obtain ⟨hu₁, hu₂⟩ := Unitary.mem_iff.mp u.prop
    rw [star_one_add_inr_sub_one, hmul, hmul, hu₁, hu₂]
    simp⟩

private theorem liftUnitaryToUnitization_conj_inr (u : unitary B) (b : B) :
    (liftUnitaryToUnitization u : Unitization ℂ B) * (b : Unitization ℂ B) *
        star (liftUnitaryToUnitization u : Unitization ℂ B) =
      (((u : B) * b * star (u : B) : B) : Unitization ℂ B) := by
  have hleft :
      (1 + (((u : B) - 1 : B) : Unitization ℂ B)) * (b : Unitization ℂ B) =
        (((u : B) * b : B) : Unitization ℂ B) := by
    rw [add_mul, one_mul, ← Unitization.inr_mul, ← Unitization.inr_add, sub_mul, one_mul,
      add_sub_cancel]
  dsimp only [liftUnitaryToUnitization]
  rw [hleft, star_one_add_inr_sub_one, mul_add, mul_one, ← Unitization.inr_mul,
    ← Unitization.inr_add, mul_sub, mul_one, add_sub_cancel]

private def liftUnitaryPathToUnitization (u : C(ℝ≥0, unitary B)) :
    C(ℝ≥0, unitary (Unitization ℂ B)) where
  toFun t := liftUnitaryToUnitization (u t)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add <|
      (Unitization.continuous_inr (𝕜 := ℂ) (A := B)).comp
        ((continuous_subtype_val.comp u.continuous).sub continuous_const)

@[simp]
private theorem liftUnitaryPathToUnitization_apply (u : C(ℝ≥0, unitary B)) (t : ℝ≥0) :
    liftUnitaryPathToUnitization u t = liftUnitaryToUnitization (u t) :=
  rfl

private theorem starLift_id_comp_inr :
    (Unitization.starLift (NonUnitalStarAlgHom.id ℂ B)).toNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ B) =
      NonUnitalStarAlgHom.id ℂ B := by
  rw [← Unitization.starLift_symm_apply]
  exact Unitization.starLift.symm_apply_apply _

/-- For a unital target `B`, unitization asymptotic unitary equivalence coincides with target
asymptotic unitary equivalence. -/
theorem UnitizationAsymptoticallyUnitarilyEquivalent.iff_asymptoticallyUnitarilyEquivalent
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    UnitizationAsymptoticallyUnitarilyEquivalent φ ψ ↔
      AsymptoticallyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    have h' := AsymptoticallyUnitarilyEquivalent.postcomp h
      (Unitization.starLift (NonUnitalStarAlgHom.id ℂ B))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc, starLift_id_comp_inr,
      NonUnitalStarAlgHom.id_comp, NonUnitalStarAlgHom.id_comp] at h'
  · rw [unitizationAsymptoticallyUnitarilyEquivalent_iff_inr,
      asymptoticallyUnitarilyEquivalent_def, asymptoticallyUnitarilyEquivalent_def]
    rintro ⟨u, hu⟩
    refine ⟨liftUnitaryPathToUnitization u, fun a ↦ ?_⟩
    have hlim := ((Unitization.continuous_inr (𝕜 := ℂ) (A := B)).tendsto (ψ a)).comp (hu a)
    simpa only [Function.comp_def, NonUnitalStarAlgHom.comp_apply,
      Unitization.inrNonUnitalStarAlgHom_apply, liftUnitaryPathToUnitization_apply,
      liftUnitaryToUnitization_conj_inr] using hlim

namespace UnitizationStronglyAsymptoticallyUnitarilyEquivalent

/-- For a unital target `B`, strong unitization asymptotic unitary equivalence coincides with
strong target asymptotic unitary equivalence. -/
theorem iff_stronglyAsymptoticallyUnitarilyEquivalent {φ ψ : A →⋆ₙₐ[ℂ] B} :
    UnitizationStronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      StronglyAsymptoticallyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    have h' := StronglyAsymptoticallyUnitarilyEquivalent.postcomp h
      (Unitization.starLift (NonUnitalStarAlgHom.id ℂ B))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc, starLift_id_comp_inr,
      NonUnitalStarAlgHom.id_comp, NonUnitalStarAlgHom.id_comp] at h'
  · rw [unitizationStronglyAsymptoticallyUnitarilyEquivalent_iff_inr,
      stronglyAsymptoticallyUnitarilyEquivalent_def, stronglyAsymptoticallyUnitarilyEquivalent_def]
    rintro ⟨u, hu0, hu⟩
    refine ⟨liftUnitaryPathToUnitization u, ?_, fun a ↦ ?_⟩
    · exact Subtype.ext (by simp [liftUnitaryToUnitization, hu0])
    · have hlim := ((Unitization.continuous_inr (𝕜 := ℂ) (A := B)).tendsto (ψ a)).comp (hu a)
      simpa only [Function.comp_def, NonUnitalStarAlgHom.comp_apply,
        Unitization.inrNonUnitalStarAlgHom_apply, liftUnitaryPathToUnitization_apply,
        liftUnitaryToUnitization_conj_inr] using hlim

end UnitizationStronglyAsymptoticallyUnitarilyEquivalent

end UnitalTarget

end TauCeti
