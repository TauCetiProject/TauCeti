/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Quotient.Basic
public import TauCeti.Topology.Algebra.Ring.MaximalIdeals

/-!
# Isometries and bounded inverses on ideal quotients

This file records two ways in which ring homomorphisms induce isometries or bi-Lipschitz
equivalences on ideal quotients of seminormed rings.

First, an isometric ring homomorphism with dense range induces an isometry on quotients by an ideal
and its extension (`RingHom.isometry_quotientMap`): the extended ideal and the image of the
original ideal have the same closure, so distances to the two ideals agree. This applies in
particular to residue norms of presentation quotients inside completed algebras.

Second, for a ring homomorphism `f : R →+* S` between possibly noncommutative seminormed rings, the
induced map `f.kerLift : R ⧸ ker f →+* S` has the same norm bound as `f`
(`RingHom.norm_kerLift_le`), and when `f` is surjective with uniformly `L`-bounded preimages the
inverse of `f.quotientKerEquivOfSurjective` has norm bound `L`
(`RingHom.norm_quotientKerEquivOfSurjective_symm_le`). Moreover `f.kerLift` is an isometry —
equivalently `‖Ideal.Quotient.mk (ker f) a‖ = ‖f a‖` for every `a` — if and only if `f` is
contractive and every image `f a` admits preimages of norm arbitrarily close to `‖f a‖`
(`RingHom.isometry_kerLift_iff`, `RingHom.isometry_quotientKerEquivOfSurjective_iff`).

## Main results

* `RingHom.isometry_quotientMap`: an isometric ring homomorphism with dense range induces an
  isometry on ideal quotients.
* `RingHom.norm_kerLift_le` and `RingHom.norm_quotientKerEquivOfSurjective_symm_le`: norm bounds on
  `RingHom.kerLift` and the inverse of `RingHom.quotientKerEquivOfSurjective`.
* `RingHom.isometry_kerLift_iff` and `RingHom.isometry_quotientKerEquivOfSurjective_iff`:
  characterisations of when `kerLift` and `quotientKerEquivOfSurjective` are isometries.
-/

public section

namespace RingHom

section QuotientMap

variable {A B : Type*} [SeminormedCommRing A] [SeminormedCommRing B]

/-- An isometric homomorphism with dense range induces an isometry on ideal quotients. -/
theorem isometry_quotientMap (f : A →+* B) (hf : Isometry f) (hd : DenseRange f)
    (I : Ideal A) :
    Isometry (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  have hclosure : closure (f '' (I : Set A)) = closure (I.map f : Set B) := by
    apply Set.Subset.antisymm
    · exact closure_mono (Set.image_subset_iff.2 Ideal.le_comap_map)
    · exact closure_minimal (Ideal.map_subset_closure_image_of_denseRange hd I)
        isClosed_closure
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk]
  -- Ideal quotient norms are the additive-group quotient norms used by Mathlib.
  have hA : ‖Ideal.Quotient.mk I a‖ = Metric.infDist a (I : Set A) :=
    QuotientAddGroup.norm_mk (S := I.toAddSubgroup) a
  have hB : ‖Ideal.Quotient.mk (I.map f) (f a)‖ =
      Metric.infDist (f a) (I.map f : Set B) :=
    QuotientAddGroup.norm_mk (S := (I.map f).toAddSubgroup) (f a)
  rw [hA, hB, ← Metric.infDist_closure (s := (I.map f : Set B)), ← hclosure,
    Metric.infDist_closure, Metric.infDist_image hf]

end QuotientMap

section Ker

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S]

/-- A ring homomorphism bounded by `C` descends to a homomorphism on `R ⧸ ker f` with the same
norm bound `C`. -/
theorem norm_kerLift_le (f : R →+* S) {C : ℝ} (hC : ∀ a, ‖f a‖ ≤ C * ‖a‖) (x : R ⧸ ker f) :
    ‖f.kerLift x‖ ≤ C * ‖x‖ := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [kerLift_mk]
  rcases le_or_gt C 0 with hC0 | hC0
  · exact (hC a).trans (mul_le_mul_of_nonpos_left (Ideal.Quotient.norm_mk_le_norm (ker f) a) hC0)
  · exact (QuotientAddGroup.norm_lift_apply_le (S := (ker f).toAddSubgroup)
      ((f : R →+ S).mkNormedAddGroupHom C hC) (fun _ ↦ mem_ker.mp)
      (Ideal.Quotient.mk (ker f) a)).trans
      (mul_le_mul_of_nonneg_right (AddMonoidHom.mkNormedAddGroupHom_norm_le _ hC0.le hC)
        (norm_nonneg _))

/-- Uniformly `L`-bounded preimages along a surjective ring homomorphism bound the inverse of the
first-isomorphism equivalence by `L`. -/
theorem norm_quotientKerEquivOfSurjective_symm_le {f : R →+* S} (hf : Function.Surjective f)
    {L : ℝ} (hlift : ∀ b, ∃ a, f a = b ∧ ‖a‖ ≤ L * ‖b‖) (b : S) :
    ‖(f.quotientKerEquivOfSurjective hf).symm b‖ ≤ L * ‖b‖ := by
  obtain ⟨a, rfl, ha⟩ := hlift b
  rw [quotientKerEquivOfSurjective_symm_apply]
  exact (Ideal.Quotient.norm_mk_le_norm (ker f) a).trans ha

/-- A bounded surjective ring homomorphism induces a Lipschitz first-isomorphism equivalence. -/
theorem lipschitzWith_quotientKerEquivOfSurjective {f : R →+* S} (hf : Function.Surjective f)
    {C : ℝ} (hC : ∀ a, ‖f a‖ ≤ C * ‖a‖) :
    LipschitzWith (Real.toNNReal C) (f.quotientKerEquivOfSurjective hf) :=
  AddMonoidHomClass.lipschitz_of_bound (f.quotientKerEquivOfSurjective hf) C (f.norm_kerLift_le hC)

/-- Uniformly bounded preimages make the inverse of `RingHom.quotientKerEquivOfSurjective`
Lipschitz. -/
theorem lipschitzWith_quotientKerEquivOfSurjective_symm {f : R →+* S} (hf : Function.Surjective f)
    {L : ℝ} (hlift : ∀ b, ∃ a, f a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    LipschitzWith (Real.toNNReal L) (f.quotientKerEquivOfSurjective hf).symm :=
  AddMonoidHomClass.lipschitz_of_bound (f.quotientKerEquivOfSurjective hf).symm L
    (f.norm_quotientKerEquivOfSurjective_symm_le hf hlift)

/-- The quotient seminorm modulo `ker f` equals `‖f ·‖` everywhere if and only if `f` is
contractive and every value `f a` admits preimages of norm arbitrarily close to `‖f a‖`. -/
theorem norm_mk_ker_eq_iff (f : R →+* S) :
    (∀ a, ‖Ideal.Quotient.mk (ker f) a‖ = ‖f a‖) ↔
      (∀ a, ‖f a‖ ≤ ‖a‖) ∧ ∀ a, ∀ ε > 0, ∃ a', f a' = f a ∧ ‖a'‖ < ‖f a‖ + ε := by
  constructor
  · intro h
    refine ⟨fun a ↦ (h a).symm.trans_le (Ideal.Quotient.norm_mk_le_norm (ker f) a),
      fun a ε hε ↦ ?_⟩
    obtain ⟨a', ha', hlt⟩ := Ideal.Quotient.exists_norm_mk_lt (Ideal.Quotient.mk (ker f) a) hε
    refine ⟨a', ?_, by rwa [h a] at hlt⟩
    simpa only [kerLift_mk] using congrArg f.kerLift ha'
  · rintro ⟨h1, h2⟩ a
    apply le_antisymm
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨a', ha', hlt⟩ := h2 a ε hε
      have hmk : Ideal.Quotient.mk (ker f) a' = Ideal.Quotient.mk (ker f) a :=
        f.kerLift_injective (by simp [ha'])
      exact (hmk ▸ Ideal.Quotient.norm_mk_le_norm (ker f) a').trans_lt hlt
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨a', ha', hlt⟩ := Ideal.Quotient.exists_norm_mk_lt (Ideal.Quotient.mk (ker f) a) hε
      have hfa : f a = f a' := by simpa only [kerLift_mk] using (congrArg f.kerLift ha').symm
      exact (hfa ▸ h1 a').trans_lt hlt

/-- **Quotient-isometry criterion for ring homomorphisms.** The induced injection
`f.kerLift : R ⧸ ker f →+* S` is an isometry if and only if `f` is contractive and every value
`f a` lifts to elements of norm arbitrarily close to `‖f a‖`. -/
theorem isometry_kerLift_iff (f : R →+* S) :
    Isometry f.kerLift ↔
      (∀ a, ‖f a‖ ≤ ‖a‖) ∧ ∀ a, ∀ ε > 0, ∃ a', f a' = f a ∧ ‖a'‖ < ‖f a‖ + ε := by
  rw [AddMonoidHomClass.isometry_iff_norm, Ideal.Quotient.mk_surjective.forall]
  simp only [kerLift_mk, eq_comm (b := ‖Ideal.Quotient.mk (ker f) _‖)]
  exact f.norm_mk_ker_eq_iff

/-- **Isometric first isomorphism theorem for seminormed rings.** For a surjective ring homomorphism
`f : R →+* S`, the equivalence `R ⧸ ker f ≃+* S` is an isometry if and only if `f` is contractive
and every `b : S` admits preimages of norm arbitrarily close to `‖b‖`. -/
theorem isometry_quotientKerEquivOfSurjective_iff {f : R →+* S} (hf : Function.Surjective f) :
    Isometry (f.quotientKerEquivOfSurjective hf) ↔
      (∀ a, ‖f a‖ ≤ ‖a‖) ∧ ∀ b, ∀ ε > 0, ∃ a, f a = b ∧ ‖a‖ < ‖b‖ + ε := by
  rw [AddMonoidHomClass.isometry_iff_norm, Ideal.Quotient.mk_surjective.forall]
  simp only [quotientKerEquivOfSurjective_apply_mk, eq_comm (b := ‖Ideal.Quotient.mk (ker f) _‖),
    f.norm_mk_ker_eq_iff, hf.forall]

/-- Non-strict approximate preimages `‖a‖ ≤ ‖b‖ + ε` suffice for the quotient seminorm modulo
`ker f` to equal `‖f ·‖`. -/
theorem norm_mk_ker_eq_of_forall_pos_exists_norm_le_add {f : R →+* S} (h1 : ∀ a, ‖f a‖ ≤ ‖a‖)
    (h2 : ∀ b, ∀ ε > 0, ∃ a, f a = b ∧ ‖a‖ ≤ ‖b‖ + ε) (a : R) :
    ‖Ideal.Quotient.mk (ker f) a‖ = ‖f a‖ := by
  refine (f.norm_mk_ker_eq_iff.mpr ⟨h1, fun x ε hε ↦ ?_⟩) a
  obtain ⟨a', ha', hle⟩ := h2 (f x) (ε / 2) (half_pos hε)
  exact ⟨a', ha', by linarith [half_lt_self hε]⟩

/-- Non-strict approximate preimages `‖a‖ ≤ ‖b‖ + ε` suffice for
`RingHom.quotientKerEquivOfSurjective` to be an isometry. -/
theorem isometry_quotientKerEquivOfSurjective_of_forall_pos_exists_norm_le_add {f : R →+* S}
    (hf : Function.Surjective f) (h1 : ∀ a, ‖f a‖ ≤ ‖a‖)
    (h2 : ∀ b, ∀ ε > 0, ∃ a, f a = b ∧ ‖a‖ ≤ ‖b‖ + ε) :
    Isometry (f.quotientKerEquivOfSurjective hf) := by
  rw [AddMonoidHomClass.isometry_iff_norm, Ideal.Quotient.mk_surjective.forall]
  intro a
  rw [quotientKerEquivOfSurjective_apply_mk, norm_mk_ker_eq_of_forall_pos_exists_norm_le_add h1 h2]

end Ker

end RingHom
