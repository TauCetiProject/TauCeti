/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.StableLocus

/-!
# Grassmannians of quotient modules

A surjection `f : M →ₗ[R] P` embeds the quotient Grassmannian of `P` in that of `M` by inverse
image of kernels. Its image consists exactly of the kernels containing `ker f`. This description
commutes with arbitrary extension of scalars, including nonflat and nonreduced test algebras.
It is the pointwise description of the closed incidence embedding of Grassmannian schemes.
For endomorphisms intertwined by `f`, `stableLocus_comap` identifies the stability ideals
before and after inverse image, retaining their full scheme structure.

## References

* The Stacks Project, Tag 089R, for the quotient convention for Grassmannians.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {P : Type*} [AddCommGroup P] [Module R P] {k : ℕ}

/-- Inverse image along a surjection preserves a finite projective quotient and its rank. -/
noncomputable def comap (N : G(k, P; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    G(k, M; R) :=
  ofSurjective (N.toSubmodule.mkQ ∘ₗ f) (N.toSubmodule.mkQ_surjective.comp hf) N.rankAtStalk_eq

/-- The kernel of the pulled-back quotient is the inverse image of the original kernel. -/
@[simp]
theorem toSubmodule_comap (N : G(k, P; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    (N.comap f hf).toSubmodule = N.toSubmodule.comap f := by
  simp [comap, LinearMap.ker_comp]

/-- Pulling back a quotient along the identity leaves it unchanged. -/
@[simp]
theorem comap_id (N : G(k, M; R)) : N.comap LinearMap.id Function.surjective_id = N := by
  apply Grassmannian.ext
  simp

/-- Pullback of quotients respects composition of surjections. -/
theorem comap_comap {Q : Type*} [AddCommGroup Q] [Module R Q] (N : G(k, Q; R))
    (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : P →ₗ[R] Q)
    (hg : Function.Surjective g) :
    (N.comap g hg).comap f hf = N.comap (g.comp f) (hg.comp hf) := by
  apply Grassmannian.ext
  simp [Submodule.comap_comp]

/-- Inverse image along a surjection is injective on quotient Grassmannian points. -/
theorem _root_.LinearMap.grassmannianComap_injective (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    Function.Injective (fun N : G(k, P; R) ↦ N.comap f hf) := by
  intro N N' h
  apply Grassmannian.ext
  apply Submodule.comap_injective_of_surjective hf
  simpa using congrArg toSubmodule h

private theorem surjective_lift_mkQ (N : G(k, M; R)) (f : M →ₗ[R] P)
    (hf : Function.Surjective f) (hN : LinearMap.ker f ≤ N.toSubmodule) :
    Function.Surjective (f.liftOfSurjective hf
      ⟨N.toSubmodule.mkQ, (Submodule.ker_mkQ N.toSubmodule).symm ▸ hN⟩) := by
  intro q
  obtain ⟨m, hm⟩ := N.toSubmodule.mkQ_surjective q
  exact ⟨f m, (LinearMap.equivOfSurjective_apply _ _).trans hm⟩

/-- A quotient of `M` whose kernel contains `ker f` descends along the surjection `f`. -/
noncomputable def descend (N : G(k, M; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f)
    (hN : LinearMap.ker f ≤ N.toSubmodule) : G(k, P; R) :=
  ofSurjective (f.liftOfSurjective hf
    ⟨N.toSubmodule.mkQ, (Submodule.ker_mkQ N.toSubmodule).symm ▸ hN⟩)
    (surjective_lift_mkQ N f hf hN) N.rankAtStalk_eq

/-- Pulling back a descended quotient recovers the original kernel. -/
@[simp]
theorem comap_descend (N : G(k, M; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f)
    (hN : LinearMap.ker f ≤ N.toSubmodule) : (N.descend f hf hN).comap f hf = N := by
  apply Grassmannian.ext
  rw [toSubmodule_comap, descend, toSubmodule_ofSurjective]
  ext m
  simp [LinearMap.equivOfSurjective_apply]

/-- The descended kernel is the image of the original kernel. -/
@[simp]
theorem toSubmodule_descend (N : G(k, M; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f)
    (hN : LinearMap.ker f ≤ N.toSubmodule) :
    (N.descend f hf hN).toSubmodule = N.toSubmodule.map f := by
  have h := congrArg (fun L : G(k, M; R) ↦ L.toSubmodule.map f) (comap_descend N f hf hN)
  simpa only [toSubmodule_comap, Submodule.map_comap_eq_of_surjective hf] using h

/-- Inverse image along a surjection contains its kernel. -/
theorem ker_le_comap (N : G(k, P; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    LinearMap.ker f ≤ (N.comap f hf).toSubmodule := by
  rw [toSubmodule_comap]
  exact fun x hx ↦ by simp [LinearMap.mem_ker.mp hx]

/-- Descending a pulled-back quotient recovers the original quotient. -/
@[simp]
theorem descend_comap (N : G(k, P; R)) (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    (N.comap f hf).descend f hf (N.ker_le_comap f hf) = N :=
  f.grassmannianComap_injective hf (comap_descend _ _ _ _)

/-- A surjection identifies the quotient Grassmannian of its target with the points whose
kernels contain its kernel. -/
noncomputable def _root_.LinearMap.grassmannianComapEquiv (f : M →ₗ[R] P)
    (hf : Function.Surjective f) :
    G(k, P; R) ≃ {N : G(k, M; R) // LinearMap.ker f ≤ N.toSubmodule} where
  toFun N := ⟨N.comap f hf, N.ker_le_comap f hf⟩
  invFun N := N.val.descend f hf N.property
  left_inv N := descend_comap N f hf
  right_inv N := Subtype.ext (comap_descend N.val f hf N.property)

/-- The forward direction of `grassmannianComapEquiv` is inverse image of the kernel. -/
@[simp]
theorem _root_.LinearMap.grassmannianComapEquiv_apply_val (f : M →ₗ[R] P)
    (hf : Function.Surjective f) (N : G(k, P; R)) :
    (f.grassmannianComapEquiv hf N).val = N.comap f hf :=
  (rfl)

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Inverse image of a quotient commutes with every change of coefficients. -/
@[simp]
theorem map_comap_baseChange (N : G(k, A ⊗[R] P; A)) (f : M →ₗ[R] P)
    (hf : Function.Surjective f) (φ : A →ₐ[R] B) :
    map φ (N.comap (f.baseChange A) (f.baseChange_surjective A hf)) =
      (map φ N).comap (f.baseChange B) (f.baseChange_surjective B hf) := by
  algebraize [φ.toRingHom]
  have hφ : IsScalarTower.toAlgHom R A B = φ := AlgHom.ext fun _ ↦ rfl
  let g := N.toSubmodule.mkQ ∘ₗ f.baseChange A
  let e := g.quotKerEquivOfSurjective
    (N.toSubmodule.mkQ_surjective.comp (f.baseChange_surjective A hf))
  have he : (e.baseChange A B _ _).toLinearMap ∘ₗ baseChangeMkQ B (LinearMap.ker g) =
      baseChangeMkQ B N.toSubmodule ∘ₗ f.baseChange B := by
    ext m
    simp [e, g]
  rw [← hφ]
  ext : 1
  rw [toSubmodule_comap, map_toAlgHom_toSubmodule (B := B),
    map_toAlgHom_toSubmodule (B := B), ← LinearMap.ker_comp, ← he,
    LinearEquiv.ker_comp]
  rw [comap, toSubmodule_ofSurjective]

/-- Inverse image along an equivariant surjection preserves the equations of stability,
including their nilpotent scheme structure. -/
@[simp]
theorem stableLocus_comap (N : G(k, A ⊗[R] P; A)) (f : M →ₗ[R] P)
    (hf : Function.Surjective f) (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) :
    (N.comap (f.baseChange A) (f.baseChange_surjective A hf)).stableLocus t = N.stableLocus u := by
  let C := N.comap (f.baseChange A) (f.baseChange_surjective A hf)
  let g := N.toSubmodule.mkQ ∘ₗ f.baseChange A
  have hC : C.toSubmodule = LinearMap.ker g := by
    dsimp only [C]
    rw [comap, toSubmodule_ofSurjective]
  let e := (Submodule.quotEquivOfEq _ _ hC).trans
    (g.quotKerEquivOfSurjective
      (N.toSubmodule.mkQ_surjective.comp (f.baseChange_surjective A hf)))
  have he (x : A ⊗[R] M) : e (C.toSubmodule.mkQ x) = g x := by simp [e]
  have ht : (f.baseChange A).comp (t.baseChange A) =
      (u.baseChange A).comp (f.baseChange A) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]
  have himage : (C.toSubmodule.map (C.toSubmodule.mkQ ∘ₗ t.baseChange A)).map
      (e : _ →ₗ[A] _) = N.toSubmodule.map (N.toSubmodule.mkQ ∘ₗ u.baseChange A) := by
    rw [← Submodule.map_comp]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨f.baseChange A x, ?_, ?_⟩
      · simpa [C] using hx
      · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, g] using
          (congrArg N.toSubmodule.mkQ (LinearMap.congr_fun ht x)).symm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := f.baseChange_surjective A hf y
      refine ⟨x, ?_, ?_⟩
      · simpa [C] using hy
      · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, g] using
          congrArg N.toSubmodule.mkQ (LinearMap.congr_fun ht x)
  rw [stableLocus_def, ← Submodule.minorsIdeal_map_equiv e, himage, stableLocus_def]

end BaseChange

end Module.Grassmannian
