/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import TauCeti.Algebra.Lie.Symplectic.Automorphism.Extremal
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Conjugation realizes Lie equivalences of symplectic Lie algebras

Over a field of characteristic different from two, a Lie equivalence between the skew-adjoint
endomorphisms of two alternating spaces is induced by a linear similitude if either form is
nondegenerate. When every scalar is a square, the similitude can be chosen to be an isometry.
The spaces can have arbitrary dimension.

For a vector `v`, write `N(v)` for the transvection generator `x ↦ B x v • v`.
Fix a nonzero vector `e`. The Lie equivalence sends `N(e)` to a nonzero multiple of `N(d)`.
The centralizer of `N(e)` is the kernel of evaluation at `e`. Descending along evaluation
therefore gives a linear bijection `A` between the spaces. The double-bracket formula identifies
the images of all `N(v)` with the same scalar multiple of `N(A v)`, first off the orthogonal
hyperplane of `e`, then everywhere by the parallelogram identity. Polarization now identifies
the Lie equivalence with conjugation by `A`, and comparison on generators gives the multiplier.

## References

* J. S. Milne, *Lie Algebras, Algebraic Groups, and Lie Groups*, the symplectic Lie algebra
  and automorphisms of split semisimple Lie algebras.
-/

public section

namespace LinearMap.BilinForm
open LinearMap (BilinForm)
attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

private theorem evalSkew_surjective_of_eq_one (hB : B.IsAlt) {e w : M} (hw : B e w = 1) :
    Function.Surjective (fun X : skewAdjointLieSubalgebra B ↦ X.val e) := by
  intro v
  refine ⟨transvectionGenerator hB (w + v) - transvectionGenerator hB w -
    transvectionGenerator hB v - B e v • transvectionGenerator hB w, ?_⟩
  change B e (w + v) • (w + v) - B e w • w - B e v • v - B e v • B e w • w = v
  rw [map_add, hw]
  simp only [add_smul, smul_add, one_smul]
  abel

/-- The rank-one endomorphisms satisfy the parallelogram identity inside the Lie algebra. -/
private theorem transvectionGenerator_add_sub (hB : B.IsAlt) (v w : M) :
    transvectionGenerator hB (v + w) + transvectionGenerator hB (v - w) =
      (2 : R) • transvectionGenerator hB v + (2 : R) • transvectionGenerator hB w := by
  apply Subtype.ext
  ext x
  change B x (v + w) • (v + w) + B x (v - w) • (v - w) =
    (2 : R) • (B x v • v) + (2 : R) • (B x w • w)
  simp only [map_add, map_sub, add_smul, smul_add, sub_smul, smul_sub, two_smul]
  abel

private theorem smul_transvectionGenerator_mul_self (hB : B.IsAlt) (a : R) (v : M) :
    let X : skewAdjointLieSubalgebra B := a • transvectionGenerator hB v
    X.val * X.val = 0 := by
  change (a • (B.flip v).smulRight v) * (a • (B.flip v).smulRight v) = 0
  rw [smul_mul_assoc, mul_smul_comm, smulRight_flip_mul_self hB, smul_zero, smul_zero]

end CommRing

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {B : BilinForm K V} {C : BilinForm K W}

private theorem evalSkew_surjective (hB : B.IsAlt) {e : V} (he : B.flip e ≠ 0) :
    Function.Surjective (fun X : skewAdjointLieSubalgebra B ↦ X.val e) := by
  obtain ⟨w, hw⟩ : ∃ w, B e w ≠ 0 := by
    by_contra! hall
    apply he
    ext z
    change B z e = 0
    rw [← hB.neg_eq e z, hall z, neg_zero]
  exact evalSkew_surjective_of_eq_one hB (w := (B e w)⁻¹ • w) (by simp [hw])

private theorem exists_linearEquiv_eval [NeZero (2 : K)] (hB : B.IsAlt) (hC : C.IsAlt)
    {e : V} {d : W} (he : B.flip e ≠ 0) (hd : C.flip d ≠ 0)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) {c : K} (hc : c ≠ 0)
    (hED : f (transvectionGenerator hB e) = c • transvectionGenerator hC d) :
    ∃ A : V ≃ₗ[K] W, ∀ X : skewAdjointLieSubalgebra B, A (X.val e) = (f X).val d := by
  let p := (LinearMap.applyₗ e).comp (skewAdjointLieSubalgebra B).incl.toLinearMap
  let q := ((LinearMap.applyₗ d).comp (skewAdjointLieSubalgebra C).incl.toLinearMap).comp
    f.toLinearEquiv.toLinearMap
  have hp : Function.Surjective p := evalSkew_surjective hB he
  have hq : Function.Surjective q := (evalSkew_surjective hC hd).comp f.surjective
  have hker : ker p = ker q := by
    ext X
    change X.val e = 0 ↔ (f X).val d = 0
    have hs : ⁅X, transvectionGenerator hB e⁆ = 0 ↔ X.val e = 0 :=
      Subtype.ext_iff.trans (lie_smulRight_flip_eq_zero_iff he X.val X.property)
    have ht : ⁅f X, transvectionGenerator hC d⁆ = 0 ↔ (f X).val d = 0 :=
      Subtype.ext_iff.trans (lie_smulRight_flip_eq_zero_iff hd (f X).val (f X).property)
    rw [← hs, ← ht]
    have hh : f ⁅X, transvectionGenerator hB e⁆ = f 0 ↔ ⁅X, transvectionGenerator hB e⁆ = 0 :=
      f.injective.eq_iff
    rw [f.map_lie, hED, lie_smul, map_zero, smul_eq_zero, or_iff_right hc] at hh
    exact hh.symm
  refine ⟨((p.quotKerEquivOfSurjective hp).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans (q.quotKerEquivOfSurjective hq), fun X ↦ ?_⟩
  change ((p.quotKerEquivOfSurjective hp).symm.trans
    (Submodule.quotEquivOfEq _ _ hker) |>.trans (q.quotKerEquivOfSurjective hq)) (p X) = q X
  simp

/-- A linear identity on generators off the hyperplane `B e v = 0` holds on every generator.
The scalar and the linear map on the underlying vector spaces are arbitrary. -/
private theorem map_generator_eq_of_pairing_ne_zero [NeZero (2 : K)] (hB : B.IsAlt) (hC : C.IsAlt)
    {e : V} (he : B e ≠ 0)
    (F : skewAdjointLieSubalgebra B →ₗ[K] skewAdjointLieSubalgebra C)
    (A : V →ₗ[K] W) (c : K)
    (h : ∀ v, B e v ≠ 0 → F (transvectionGenerator hB v) = c • transvectionGenerator hC (A v))
    (v : V) :
    F (transvectionGenerator hB v) = c • transvectionGenerator hC (A v) := by
  by_cases hv : B e v = 0
  · obtain ⟨w, hw⟩ : ∃ w, B e w ≠ 0 := by
      by_contra! hall
      exact he (LinearMap.ext hall)
    have hp := h (v + w) (by simpa only [map_add, hv, zero_add] using hw)
    have hm := h (v - w) (by simpa only [map_sub, hv, zero_sub, neg_ne_zero] using hw)
    have H := congrArg F (transvectionGenerator_add_sub hB v w)
    simp only [map_add, map_smul, hp, hm, h w hw, map_sub] at H
    rw [← smul_add, transvectionGenerator_add_sub, smul_add, smul_comm c (2 : K),
      smul_comm c (2 : K)] at H
    exact (smul_right_injective _ (NeZero.ne (2 : K))) (add_right_cancel H.symm)
  · exact h v hv

private theorem map_generator_off_hyperplane [NeZero (2 : K)] (hB : B.IsAlt) (hC : C.IsAlt)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C)
    (A : V ≃ₗ[K] W) (e : V) (d : W) {c : K}
    (hED : f (transvectionGenerator hB e) = c • transvectionGenerator hC d)
    (hA : ∀ X : skewAdjointLieSubalgebra B,
      A (X.val e) = (f X).val d)
    (hsq : ∀ (a : K) (v : V),
      let X := f (a • transvectionGenerator hB v)
      X.val * X.val = 0) (v : V) (hv : B e v ≠ 0) :
    f (transvectionGenerator hB v) = c • transvectionGenerator hC (A v) := by
  let a := (B e v)⁻¹
  let X := a • transvectionGenerator hB v
  have hXe : X.val e = v := inv_smul_smul₀ hv v
  have hfd : (f X).val d = A v := by
    rw [← hA, hXe]
  have hs : ⁅X, ⁅X, transvectionGenerator hB e⁆⁆ = (2 : K) • transvectionGenerator hB (X.val e) :=
    Subtype.ext (lie_lie_smulRight_flip_of_apply_apply_eq_zero X.val X.property e
      (LinearMap.congr_fun (smul_transvectionGenerator_mul_self hB a v) e))
  have ht : ⁅f X, ⁅f X, transvectionGenerator hC d⁆⁆ =
      (2 : K) • transvectionGenerator hC ((f X).val d) :=
    Subtype.ext (lie_lie_smulRight_flip_of_apply_apply_eq_zero (f X).val (f X).property d
      (LinearMap.congr_fun (hsq a v) d))
  have h := congrArg f hs
  change f ⁅X, ⁅X, transvectionGenerator hB e⁆⁆ =
    f ((2 : K) • transvectionGenerator hB (X.val e)) at h
  rw [f.map_lie, f.map_lie, hED, lie_smul, lie_smul,
    ht,
    hfd, hXe, map_smul, smul_comm c (2 : K)] at h
  exact (smul_right_injective _ (NeZero.ne (2 : K))) h.symm

private theorem intertwines_of_map_transvectionGenerator [NeZero (2 : K)]
    (hB : B.IsAlt) (hC : C.IsAlt) (hmd : C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) (A : V ≃ₗ[K] W)
    {c : K} (hc : c ≠ 0)
    (hN : ∀ v, f (transvectionGenerator hB v) = c • transvectionGenerator hC (A v))
    (X : skewAdjointLieSubalgebra B) (v : V) :
    A (X.val v) = (f X).val (A v) := by
  by_cases hz : v = 0
  · simp [hz]
  have hv : A v ≠ 0 := fun h ↦ hz (A.injective (h.trans A.map_zero.symm))
  apply transvectionPolar_injective
    ((LinearMap.separatingRight_iff_linear_flip_nontrivial.mp hmd.2 _).mt hv)
  have hh : ⁅X, transvectionGenerator hB v⁆ = transvectionGenerator hB (v + X.val v) -
      transvectionGenerator hB v - transvectionGenerator hB (X.val v) :=
    Subtype.ext ((lie_smulRight_flip_eq_transvectionPolar B _ X.property v).trans
      (transvectionPolar_eq_smulRight_flip_sub B v _))
  have h := congrArg f hh
  change f ⁅X, transvectionGenerator hB v⁆ =
    f (transvectionGenerator hB _ - transvectionGenerator hB v - transvectionGenerator hB _) at h
  rw [f.map_lie, hN, map_sub, map_sub, hN, hN, hN, map_add] at h
  rw [lie_smul, ← smul_sub, ← smul_sub] at h
  have hh' := (smul_right_injective _ hc) h
  have he := congrArg (fun Z : skewAdjointLieSubalgebra C ↦ (Z : Module.End K W)) hh'
  exact (transvectionPolar_eq_smulRight_flip_sub C _ _).trans <|
    he.symm.trans (lie_smulRight_flip_eq_transvectionPolar C _ (f X).property _)

variable [NeZero (2 : K)]

private theorem form_ne_zero_of_lieEquiv [Nontrivial V]
    (hC : C.IsAlt) (hmd : C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) : B ≠ 0 := by
  rintro rfl
  let I : skewAdjointLieSubalgebra (0 : BilinForm K V) :=
    ⟨1, (mem_skewAdjointSubmodule _).mpr (by intro x y; simp)⟩
  have hcentral (Y : skewAdjointLieSubalgebra (0 : BilinForm K V)) : ⁅I, Y⁆ = 0 :=
    Subtype.ext (sub_eq_zero.mpr ((one_mul Y.val).trans (mul_one Y.val).symm))
  have hcentral' (Z : skewAdjointLieSubalgebra C) : ⁅f I, Z⁆ = 0 := by
    obtain ⟨Y, rfl⟩ := f.surjective Z
    exact (f.map_lie I Y).symm.trans ((congrArg f (hcentral Y)).trans f.map_zero)
  have hf : f I = 0 := by
    apply Subtype.ext
    ext w
    by_cases hw : w = 0
    · simp [hw]
    have hcw := (LinearMap.separatingRight_iff_linear_flip_nontrivial.mp hmd.2 w).mt hw
    exact (lie_smulRight_flip_eq_zero_iff hcw (f I).val (f I).property).mp
      (congrArg Subtype.val (hcentral' (transvectionGenerator hC w)))
  have hI : I = 0 := f.injective (hf.trans f.map_zero.symm)
  exact one_ne_zero (congrArg Subtype.val hI : (1 : Module.End K V) = 0)

private theorem exists_similitude_intertwining_of_nontrivial [Nontrivial V]
    (hB : B.IsAlt) (hC : C.IsAlt) (hmd : C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) :
    ∃ (c : Kˣ) (A : V ≃ₗ[K] W), (∀ x y, B x y = c * C (A x) (A y)) ∧
      ∀ (X : skewAdjointLieSubalgebra B) (v : V), (f X).val (A v) = A (X.val v) := by
  have hne := form_ne_zero_of_lieEquiv hC hmd f
  obtain ⟨e, w, he⟩ : ∃ e w, B e w ≠ 0 := by
    by_contra! hall
    exact hne (LinearMap.ext₂ hall)
  have heB : B e ≠ 0 := fun h ↦ he (LinearMap.congr_fun h w)
  have hef : B.flip e ≠ 0 := by
    intro h
    have hw : B w e = 0 := LinearMap.congr_fun h w
    exact he (neg_eq_zero.mp ((hB.neg_eq e w).trans hw))
  obtain ⟨c, d, hc, hd, hED⟩ := exists_map_transvectionGenerator_eq_smul hB hC hmd f hef
  have hdf := (LinearMap.separatingRight_iff_linear_flip_nontrivial.mp hmd.2 d).mt hd
  obtain ⟨A, hA⟩ := exists_linearEquiv_eval hB hC hef hdf f hc hED
  have hN : ∀ v, f (transvectionGenerator hB v) = c • transvectionGenerator hC (A v) := fun v ↦
    map_generator_eq_of_pairing_ne_zero hB hC heB f.toLinearEquiv.toLinearMap A.toLinearMap c
      (map_generator_off_hyperplane hB hC f A e d hED hA
        (map_smul_transvectionGenerator_mul_self hB hC hmd f)) v
  have hX := intertwines_of_map_transvectionGenerator hB hC hmd f A hc hN
  refine ⟨Units.mk0 c hc, A, ?_, fun X v ↦ (hX X v).symm⟩
  intro x y
  by_cases hy : y = 0
  · simp [hy]
  have h := hX (transvectionGenerator hB y) x
  rw [hN] at h
  change A (B x y • y) = c • C (A x) (A y) • A y at h
  rw [map_smul, smul_smul] at h
  exact (smul_left_injective K (fun hz ↦ hy (A.injective (hz.trans A.map_zero.symm)))) h

private theorem exists_similitude_of_nondegenerate_target (hB : B.IsAlt)
    (hC : C.IsAlt) (hmd : C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) :
    ∃ (c : Kˣ) (A : V ≃ₗ[K] W), (∀ x y, B x y = c * C (A x) (A y)) ∧
      ∀ X : skewAdjointLieSubalgebra B, (f X).val = A.lieConj X.val := by
  cases subsingleton_or_nontrivial V with
  | inl h =>
    have : Subsingleton W := by
      cases subsingleton_or_nontrivial W with
      | inl hu => exact hu
      | inr hu =>
        obtain ⟨d, hd⟩ := exists_ne (0 : W)
        have hdf := (LinearMap.separatingRight_iff_linear_flip_nontrivial.mp hmd.2 d).mt hd
        have hs : Function.Surjective (fun X : skewAdjointLieSubalgebra B ↦ (f X).val d) :=
          (evalSkew_surjective hC hdf).comp f.surjective
        exact hs.subsingleton
    refine ⟨1, LinearEquiv.ofSubsingleton (R := K) V W, ?_, fun _ ↦ Subsingleton.elim _ _⟩
    intro x y
    simp [Subsingleton.elim y 0]
  | inr h =>
    obtain ⟨c, A, hc, hA⟩ := exists_similitude_intertwining_of_nontrivial hB hC hmd f
    refine ⟨c, A, hc, fun X ↦ ?_⟩
    ext u
    obtain ⟨v, rfl⟩ := A.surjective u
    simpa [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply] using hA X v

/-- A Lie equivalence of alternating forms, at least one nondegenerate, is conjugation by a
linear similitude. In particular, the other form must then also be nondegenerate. -/
theorem exists_linearEquiv_lieConj_of_skewAdjoint (hB : B.IsAlt) (hC : C.IsAlt)
    (hnd : B.Nondegenerate ∨ C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) :
    ∃ (c : Kˣ) (A : V ≃ₗ[K] W), (∀ x y, B x y = c * C (A x) (A y)) ∧
      ∀ X : skewAdjointLieSubalgebra B, (f X).val = A.lieConj X.val := by
  rcases hnd with hBnd | hCnd
  · obtain ⟨c, A, hc, hA⟩ := exists_similitude_of_nondegenerate_target hC hB hBnd f.symm
    refine ⟨c⁻¹, A.symm, ?_, fun X ↦ ?_⟩
    · intro x y
      rw [hc, A.apply_symm_apply, A.apply_symm_apply, ← mul_assoc, Units.inv_mul, one_mul]
    · ext u
      apply A.injective
      have h := LinearMap.congr_fun (hA (f X)) (A u)
      change (f.symm (f X)).val (A u) = A ((f X).val (A.symm (A u))) at h
      rw [f.symm_apply_apply, A.symm_apply_apply] at h
      change A ((f X).val u) = A (A.symm (X.val (A u)))
      rw [A.apply_symm_apply]
      exact h.symm
  · exact exists_similitude_of_nondegenerate_target hB hC hCnd f

/-- If every scalar is a square, a symplectic Lie equivalence is conjugation by an isometry. -/
theorem exists_isometryEquiv_lieConj_of_skewAdjoint (hsq : ∀ a : K, IsSquare a)
    (hB : B.IsAlt) (hC : C.IsAlt) (hnd : B.Nondegenerate ∨ C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C) :
    ∃ h : B.IsometryEquiv C, ∀ X : skewAdjointLieSubalgebra B,
      (f X).val = h.toLinearEquiv.lieConj X.val := by
  obtain ⟨c, A, hc, hA⟩ := exists_linearEquiv_lieConj_of_skewAdjoint hB hC hnd f
  obtain ⟨b, hb⟩ := hsq (c : K)
  have hne : b ≠ 0 := by
    rintro rfl
    simp at hb
  let S := A.trans (LinearEquiv.smulOfNeZero K W b hne)
  have hS (v : V) : S v = b • A v := rfl
  have hisom (x y) : C (S x) (S y) = B x y := by
    rw [hS, hS, hc, hb]
    simp [mul_assoc]
  refine ⟨⟨S, hisom⟩, fun X ↦ ?_⟩
  ext u
  obtain ⟨v, rfl⟩ := S.surjective u
  change (f X).val (S v) = S (X.val (S.symm (S v)))
  rw [LinearEquiv.symm_apply_apply, hS, hS, map_smul, hA]
  simp [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply]

end LinearMap.BilinForm
