/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Content
public import TauCeti.RingTheory.Grassmannian.Basic

/-!
# Incidence conditions between Grassmannian points

For two quotient Grassmannian points `N` and `P` of the same module, the containment
`N.toSubmodule ≤ P.toSubmodule` means that the quotient map by `P` factors through the quotient
by `N`. The content of the image of `N` in the quotient by `P` defines its incidence ideal.
This ideal vanishes exactly when the containment holds, and its formation commutes with
arbitrary base change. Thus it defines a closed condition on pairs of Grassmannian points,
including consecutive members of a flag.

The construction uses the projective-module content developed in
`TauCeti.RingTheory.FittingIdeal.Content`.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {k l : ℕ}

/-- The ideal imposing containment of the submodule of `N` in that of `P`: the content of the
image of `N` in the finite projective quotient by `P`. -/
noncomputable def incidenceLocus (N : G(k, M; R)) (P : G(l, M; R)) : Ideal R :=
  (N.toSubmodule.map P.toSubmodule.mkQ).minorsIdeal 1

/-- The incidence ideal is the ideal of `1 × 1` minors of the image in the second quotient. -/
theorem incidenceLocus_def (N : G(k, M; R)) (P : G(l, M; R)) :
    N.incidenceLocus P = (N.toSubmodule.map P.toSubmodule.mkQ).minorsIdeal 1 :=
  (rfl)

/-- An ideal contains the incidence ideal exactly when it contains every functional evaluated
on the image of a vector of `N` in the quotient by `P`. -/
theorem incidenceLocus_le_iff (N : G(k, M; R)) (P : G(l, M; R)) (J : Ideal R) :
    N.incidenceLocus P ≤ J ↔
      ∀ (φ : Module.Dual R (M ⧸ P.toSubmodule)) (x : M),
        x ∈ N.toSubmodule → φ (P.toSubmodule.mkQ x) ∈ J := by
  rw [incidenceLocus_def, Submodule.minorsIdeal_one_le_iff]
  refine ⟨fun h φ x hx ↦ h φ _ ⟨x, hx, rfl⟩, ?_⟩
  rintro h φ _ ⟨x, hx, rfl⟩
  exact h φ x hx

/-- The incidence ideal vanishes precisely when the submodule of `N` is contained in that of
`P`. This holds over an arbitrary commutative ring. -/
@[simp]
theorem incidenceLocus_eq_bot_iff (N : G(k, M; R)) (P : G(l, M; R)) :
    N.incidenceLocus P = ⊥ ↔ N.toSubmodule ≤ P.toSubmodule := by
  rw [incidenceLocus_def, eq_bot_iff, Submodule.minorsIdeal_one_le_iff_le_smul_top]
  rw [Submodule.bot_smul, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
    Submodule.ker_mkQ]

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The incidence ideal commutes with simultaneous base change of both Grassmannian points
along an arbitrary algebra map. -/
@[simp]
theorem incidenceLocus_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A))
    (P : G(l, A ⊗[R] M; A)) :
    (map f N).incidenceLocus (map f P) = Ideal.map f (N.incidenceLocus P) := by
  algebraize [f.toRingHom]
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  have hP := map_toAlgHom_toSubmodule (B := B) P
  rw [hf] at hP
  let e : ((B ⊗[R] M) ⧸ (map f P).toSubmodule) ≃ₗ[B]
      B ⊗[A] ((A ⊗[R] M) ⧸ P.toSubmodule) :=
    (Submodule.quotEquivOfEq _ _ hP).trans
      ((baseChangeMkQ B P.toSubmodule).quotKerEquivOfSurjective
        (baseChangeMkQ_surjective P.toSubmodule))
  have himage : ((map f N).toSubmodule.map (map f P).toSubmodule.mkQ).map
      (e : _ →ₗ[B] _) = Submodule.span B
        (TensorProduct.mk A B _ 1 '' (N.toSubmodule.map P.toSubmodule.mkQ :
          Set ((A ⊗[R] M) ⧸ P.toSubmodule))) := by
    rw [map_toSubmodule_eq_span f N, Submodule.map_span, Submodule.map_span]
    simp only [Submodule.map_coe, Set.image_image]
    refine congrArg _ (Set.image_congr fun x _ ↦ ?_)
    simp [e, ← hf]
  rw [incidenceLocus_def, ← Submodule.minorsIdeal_map_equiv e, himage,
    (TensorProduct.isBaseChange A _ B).minorsIdeal_one_span_image, incidenceLocus_def]
  rfl

end Module.Grassmannian
