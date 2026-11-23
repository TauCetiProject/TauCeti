/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic properties of quadratic maps

This file records elementary consequences of the quadratic-map axioms.

## Main results

* `QuadraticMap.Anisotropic.comp`: injective pullback preserves anisotropy.
* `QuadraticMap.anisotropic_smul_iff`: scaling by a unit preserves anisotropy.
* `QuadraticMap.nontrivial_of_ne_zero`: the source of a nonzero quadratic map is nontrivial.
* `QuadraticMap.map_sum_of_pairwise_isOrtho`: a quadratic map is additive across a finite sum of
  pairwise `Q`-orthogonal vectors.
* `QuadraticMap.isRefl_polarBilin`: the polar bilinear map of any quadratic map is reflexive.
* `QuadraticMap.isSymm_polarBilin`: the polar bilinear form of a scalar-valued quadratic map is
  symmetric.
* `RingEquiv.congrPiQuadraticForm`: additive equivalence of coordinate quadratic forms induced by
  a ring isomorphism of scalars, preserving scalar multiplication and anisotropy.
-/

public section

namespace QuadraticMap

/-- The source of a nonzero quadratic map is nontrivial. -/
theorem nontrivial_of_ne_zero {S V N : Type*} [CommSemiring S] [AddCommMonoid V]
    [Module S V] [AddCommMonoid N] [Module S N] {Q : QuadraticMap S V N} (hQ : Q ≠ 0) :
    Nontrivial V := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact nontrivial_of_ne v 0 (fun h ↦ hv (by simp [h]))

/-- An injective pullback of an anisotropic quadratic map is anisotropic. -/
theorem Anisotropic.comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] {Q : QuadraticMap R M N} (hQ : Q.Anisotropic)
    (f : P →ₗ[R] M) (hf : Function.Injective f) : (Q.comp f).Anisotropic := by
  intro x hx
  apply hf
  rw [map_zero]
  exact hQ _ hx

/-- Scaling a quadratic map by a unit does not change its anisotropy. -/
@[simp]
theorem anisotropic_smul_iff {S R M N : Type*} [Monoid S] [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [DistribMulAction S N] [SMulCommClass S R N] {a : S} (ha : IsUnit a)
    (Q : QuadraticMap R M N) :
    (a • Q).Anisotropic ↔ Q.Anisotropic := by
  simp only [Anisotropic, smul_apply, ha.smul_eq_zero]

/-- For a pairwise `Q`-orthogonal family on a finite set `s`, `Q` is additive across
`∑ i ∈ s, u i`. -/
theorem map_sum_of_pairwise_isOrtho {R M P ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (Q : QuadraticMap R M P) (s : Finset ι) (u : ι → M)
    (hu : Set.Pairwise (s : Set ι) fun i j ↦ Q.IsOrtho (u i) (u j)) :
    Q (∑ i ∈ s, u i) = ∑ i ∈ s, Q (u i) := by
  classical
  have hcross : ∑ ij ∈ s.sym2 with ¬ij.IsDiag, polarSym2 Q (ij.map u) = 0 := by
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    induction ij using Sym2.ind with
    | h i j =>
      have hij_mem := Finset.mem_sym2_iff.mp (Finset.mem_filter.mp hij).1
      have hij_ne : i ≠ j := by simpa using (Finset.mem_filter.mp hij).2
      exact (hu (hij_mem i (Sym2.mem_mk_left i j)) (hij_mem j (Sym2.mem_mk_right i j))
        hij_ne).polar_eq_zero
  rw [Q.map_sum, hcross, add_zero]

/-- The polar bilinear map of any quadratic map is reflexive. -/
theorem isRefl_polarBilin {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (Q : QuadraticMap R M P) : Q.polarBilin.IsRefl :=
  fun x y ↦ (polar_comm Q y x).trans

/-- The polar bilinear form of a scalar-valued quadratic map is symmetric. -/
theorem isSymm_polarBilin {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) : LinearMap.BilinForm.IsSymm Q.polarBilin :=
  ⟨fun x y ↦ polar_comm Q x y⟩

end QuadraticMap

namespace RingEquiv

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (ι : Type*)

/-- Auxiliary pushforward of a coordinate quadratic form along a ring isomorphism. -/
private def mapPiQuadraticForm (e : R ≃+* S) (Q : QuadraticForm R (ι → R)) :
    QuadraticForm S (ι → S) where
  toFun x := e (Q (e.symm ∘ x))
  toFun_smul a x := by
    have hsmul : e.symm ∘ (a • x) = e.symm a • (e.symm ∘ x) :=
      funext fun i ↦ map_mul e.symm a (x i)
    rw [hsmul, Q.map_smul, smul_eq_mul, map_mul, map_mul, e.apply_symm_apply, smul_eq_mul]
  exists_companion' := by
    obtain ⟨B, hB⟩ := Q.exists_companion'
    simp only [QuadraticMap.toFun_eq_coe] at hB
    refine ⟨LinearMap.mk₂ S (fun x y ↦ e (B (e.symm ∘ x) (e.symm ∘ y)))
      (fun x y z ↦ ?_) (fun c x y ↦ ?_) (fun x y z ↦ ?_) (fun c x y ↦ ?_), fun x y ↦ ?_⟩
    · have h : e.symm ∘ (x + y) = e.symm ∘ x + e.symm ∘ y :=
        funext fun i ↦ map_add e.symm (x i) (y i)
      rw [h, LinearMap.map_add₂, map_add]
    · have h : e.symm ∘ (c • x) = e.symm c • (e.symm ∘ x) :=
        funext fun i ↦ map_mul e.symm c (x i)
      rw [h, LinearMap.map_smul₂, smul_eq_mul, map_mul, e.apply_symm_apply, smul_eq_mul]
    · have h : e.symm ∘ (y + z) = e.symm ∘ y + e.symm ∘ z :=
        funext fun i ↦ map_add e.symm (y i) (z i)
      rw [h, map_add, map_add]
    · have h : e.symm ∘ (c • y) = e.symm c • (e.symm ∘ y) :=
        funext fun i ↦ map_mul e.symm c (y i)
      rw [h, map_smul, smul_eq_mul, map_mul, e.apply_symm_apply, smul_eq_mul]
    · have h : e.symm ∘ (x + y) = e.symm ∘ x + e.symm ∘ y :=
        funext fun i ↦ map_add e.symm (x i) (y i)
      simp only [h, hB, map_add, LinearMap.mk₂_apply]

/-- A ring isomorphism `R ≃+* S` transports quadratic forms on `ι → R` additively to quadratic
forms on `ι → S` by acting coordinatewise on inputs via `e.symm` and on values via `e`. -/
def congrPiQuadraticForm (e : R ≃+* S) :
    QuadraticForm R (ι → R) ≃+ QuadraticForm S (ι → S) where
  toFun := mapPiQuadraticForm ι e
  invFun := mapPiQuadraticForm ι e.symm
  left_inv Q := QuadraticMap.ext fun x ↦ by simp [mapPiQuadraticForm, Function.comp_def]
  right_inv Q := QuadraticMap.ext fun x ↦ by simp [mapPiQuadraticForm, Function.comp_def]
  map_add' Q₁ Q₂ := QuadraticMap.ext fun x ↦ by simp [mapPiQuadraticForm]

/-- Evaluating the transported coordinate quadratic form applies `e.symm` to the coordinates and
`e` to the output. -/
@[simp]
theorem congrPiQuadraticForm_apply (e : R ≃+* S) (Q : QuadraticForm R (ι → R)) (x : ι → S) :
    e.congrPiQuadraticForm ι Q x = e (Q (e.symm ∘ x)) := (rfl)

/-- Transporting a scalar multiple of a coordinate quadratic form scales by the image scalar. -/
@[simp]
theorem congrPiQuadraticForm_smul (e : R ≃+* S) (a : R) (Q : QuadraticForm R (ι → R)) :
    e.congrPiQuadraticForm ι (a • Q) = e a • e.congrPiQuadraticForm ι Q :=
  QuadraticMap.ext fun x ↦ by simp

/-- The identity ring isomorphism induces the identity equivalence on coordinate quadratic forms. -/
@[simp]
theorem congrPiQuadraticForm_refl :
    (RingEquiv.refl R).congrPiQuadraticForm ι = AddEquiv.refl (QuadraticForm R (ι → R)) := by
  ext Q x
  rfl

/-- Inverting the ring isomorphism inverts the equivalence on coordinate quadratic forms. -/
@[simp]
theorem congrPiQuadraticForm_symm (e : R ≃+* S) :
    (e.congrPiQuadraticForm ι).symm = e.symm.congrPiQuadraticForm ι :=
  AddEquiv.ext fun _ ↦ QuadraticMap.ext fun _ ↦ rfl

/-- Composing ring isomorphisms composes the induced equivalences on coordinate quadratic forms. -/
@[simp]
theorem congrPiQuadraticForm_trans {T : Type*} [CommSemiring T] (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    (e₁.trans e₂).congrPiQuadraticForm ι =
      (e₁.congrPiQuadraticForm ι).trans (e₂.congrPiQuadraticForm ι) :=
  AddEquiv.ext fun _ ↦ QuadraticMap.ext fun _ ↦ rfl

private theorem anisotropic_congrPiQuadraticForm {ι : Type*} (e : R ≃+* S)
    {Q : QuadraticForm R (ι → R)} (hQ : Q.Anisotropic) :
    (e.congrPiQuadraticForm ι Q).Anisotropic := by
  intro x hx
  rw [congrPiQuadraticForm_apply] at hx
  replace hx : Q (e.symm ∘ x) = 0 := e.injective (hx.trans (map_zero e).symm)
  funext i
  exact e.symm.injective
    ((congrFun (hQ (e.symm ∘ x) hx) i).trans (map_zero e.symm).symm)

/-- Transporting a coordinate quadratic form along a ring isomorphism preserves and reflects
anisotropy. -/
@[simp]
theorem anisotropic_congrPiQuadraticForm_iff {ι : Type*} (e : R ≃+* S)
    (Q : QuadraticForm R (ι → R)) :
    (e.congrPiQuadraticForm ι Q).Anisotropic ↔ Q.Anisotropic :=
  ⟨fun h ↦ by
    simpa [← congrPiQuadraticForm_symm] using anisotropic_congrPiQuadraticForm e.symm h,
    anisotropic_congrPiQuadraticForm e⟩

end CommSemiring

end RingEquiv
