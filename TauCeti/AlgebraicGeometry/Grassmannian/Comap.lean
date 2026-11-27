/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.RankLocus
public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus
public import TauCeti.RingTheory.Grassmannian.Comap

import TauCeti.LinearAlgebra.TensorProduct.Kernel
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Closed incidence embeddings from quotients of the ambient module

For a surjection `f : M →ₗ[R] P`, the Grassmannian of rank-`k` quotients of `P` is the closed
subscheme of the Grassmannian of rank-`k` quotients of `M` where the universal kernel contains
`ker f`. The equations are the rank-zero minors of the map from `ker f` to the universal
quotient. This identification holds over every `R`-algebra, without flatness or reducedness
assumptions, and does not require finiteness of `M` or `P`.

This is one of the incidence embeddings used when enlarging a finite coefficient window:
quotienting out its last degree forces that degree to lie in the universal kernel.
When `f` intertwines two endomorphisms, this embedding restricts to a closed immersion of their
stable loci. The square with the ambient Grassmannians is cartesian, and the image is defined
by the same incidence equations. The construction uses `Module.Grassmannian.homOfPoints`
and `schemeRankLocusHomEquiv` to identify the schemes on arbitrary affine points.

## Main results

* `LinearMap.grassmannianComap`: the closed immersion induced by a surjection.
* `LinearMap.isIso_grassmannianComapToRankLocus`: identification with the rank-zero locus.
* `LinearMap.grassmannianStableComap`: the closed immersion of stable loci.
* `LinearMap.ker_grassmannianStableComap`: its scheme-theoretic image ideal.
* `Module.Grassmannian.exists_comp_grassmannianComap_eq_iff`: the image on arbitrary affine
  points is exactly containment of the base change of `ker f` in the kernel.

## References

* The Stacks Project, Tag 089R, for the Grassmannian functor of locally free quotients.
* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1, for the finite Grassmannian incidence embeddings in the lattice presentation.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Module.Grassmannian

namespace LinearMap

variable {R : Type u} [CommRing R] {M P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]
  (f : M →ₗ[R] P) (hf : Function.Surjective f) (k : ℕ)

/-- The inverse-image map to the rank-zero incidence locus imposing that `ker f` maps to zero
in the universal quotient. -/
noncomputable def grassmannianComapToRankLocus :
    scheme R P k ⟶ (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subscheme :=
  homOfPoints (fun A _ _ N ↦
    (schemeRankLocusHomEquiv k (fun _ : Unit ↦ ker f) (fun _ ↦ 0) A
      ⟨N.comap (f.baseChange A) (f.baseChange_surjective A hf), fun _ ↦ by
        rw [rankLocus_zero_eq_bot_iff, ← ker_baseChange_of_surjective A f hf]
        exact N.ker_le_comap _ _⟩).val)
    fun A B _ _ _ _ φ N ↦ by
      apply (cancel_mono (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι).1
      simp only [Category.assoc, schemeRankLocusHomEquiv_apply_comp_subschemeι]
      rw [← toSchemeHom_map, map_comap_baseChange N f hf φ]

/-- The morphism of quotient Grassmannians induced by a surjection of ambient modules.
On points it takes inverse images of kernels. It is a closed immersion. -/
noncomputable def grassmannianComap : scheme R P k ⟶ scheme R M k :=
  f.grassmannianComapToRankLocus hf k ≫
    (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι

/-- The incidence factorization of the morphism induced by a surjection. -/
@[reassoc (attr := simp)]
theorem grassmannianComapToRankLocus_comp_subschemeι :
    f.grassmannianComapToRankLocus hf k ≫
      (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι =
        f.grassmannianComap hf k :=
  (rfl)

end LinearMap

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] {k : ℕ}

/-- The morphism induced by a surjection takes the kernel of a quotient to its inverse image. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_grassmannianComap {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] P; A)) (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    toSchemeHom N ≫ f.grassmannianComap hf k =
      toSchemeHom (N.comap (f.baseChange A) (f.baseChange_surjective A hf)) := by
  simp [LinearMap.grassmannianComap, LinearMap.grassmannianComapToRankLocus]

end Module.Grassmannian

namespace LinearMap

variable {R : Type u} [CommRing R] {M P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]
  (f : M →ₗ[R] P) (hf : Function.Surjective f) (k : ℕ)

/-- The morphism of Grassmannians induced by a surjection lies over the base ring. -/
@[reassoc (attr := simp)]
theorem grassmannianComap_toSpec :
    f.grassmannianComap hf k ≫ toSpec R M k = toSpec R P k :=
  scheme_hom_ext fun A _ _ N ↦ by simp [toSchemeHom_toSpec]

/-- The identity surjection induces the identity of the Grassmannian. -/
@[simp]
theorem grassmannianComap_id :
    (LinearMap.id : M →ₗ[R] M).grassmannianComap Function.surjective_id k = 𝟙 _ := by
  apply scheme_hom_ext
  intro A _ _ N
  simp

/-- The incidence embeddings compose contravariantly in surjections of ambient modules. -/
theorem grassmannianComap_comp {Q : Type u} [AddCommGroup Q] [Module R Q]
    (g : P →ₗ[R] Q) (hg : Function.Surjective g) :
    g.grassmannianComap hg k ≫ f.grassmannianComap hf k =
      (g.comp f).grassmannianComap (hg.comp hf) k := by
  apply scheme_hom_ext
  intro A _ _ N
  simp only [toSchemeHom_comp_grassmannianComap_assoc, toSchemeHom_comp_grassmannianComap,
    Module.Grassmannian.comap_comap, LinearMap.baseChange_comp]

private theorem existsUnique_comp_grassmannianComapToRankLocus {A : CommRingCat.{u}}
    (a : Spec A ⟶ (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subscheme) :
    ∃! c : Spec A ⟶ scheme R P k,
      c ≫ f.grassmannianComapToRankLocus hf k = a ∧
        c ≫ toSpec R P k = a ≫
          (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι ≫ toSpec R M k := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫
    (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι ≫ toSpec R M k)
  let _ : Algebra R A := φ.hom.toAlgebra
  have ha : a ≫ (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι ≫
      toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← hφ, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  let N := (schemeRankLocusHomEquiv k (fun _ : Unit ↦ ker f) (fun _ ↦ 0) A).symm ⟨a, ha⟩
  have hN : ker (f.baseChange A) ≤ N.val.toSubmodule := by
    rw [ker_baseChange_of_surjective A f hf, ← rankLocus_zero_eq_bot_iff]
    exact N.property ()
  let K := ((f.baseChange A).grassmannianComapEquiv
    (f.baseChange_surjective A hf)).symm ⟨N.val, hN⟩
  have hK : K.comap (f.baseChange A) (f.baseChange_surjective A hf) = N.val := by
    simpa only [grassmannianComapEquiv_apply_val] using
      congrArg Subtype.val ((f.baseChange A).grassmannianComapEquiv
        (f.baseChange_surjective A hf) |>.apply_symm_apply ⟨N.val, hN⟩)
  have hc : toSchemeHom K ≫ f.grassmannianComapToRankLocus hf k = a := by
    apply (cancel_mono (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι).1
    rw [Category.assoc, grassmannianComapToRankLocus_comp_subschemeι,
      toSchemeHom_comp_grassmannianComap, hK, toSchemeHom_schemeRankLocusHomEquiv_symm_apply]
  refine ⟨toSchemeHom K, ⟨hc, by rw [ha, toSchemeHom_toSpec]⟩, ?_⟩
  rintro c ⟨hc₁, hc₂⟩
  obtain ⟨L, rfl⟩ := exists_toSchemeHom_eq c (hc₂.trans ha)
  apply congrArg toSchemeHom
  apply (f.baseChange A).grassmannianComap_injective (f.baseChange_surjective A hf)
  apply toSchemeHom_injective
  rw [← toSchemeHom_comp_grassmannianComap L f hf,
    ← toSchemeHom_comp_grassmannianComap K f hf,
    ← grassmannianComapToRankLocus_comp_subschemeι]
  rw [← Category.assoc, ← Category.assoc, hc₁, hc]

/-- The Grassmannian of a quotient module is the closed rank-zero incidence locus, as a scheme
and over every coefficient algebra. -/
instance isIso_grassmannianComapToRankLocus : IsIso (f.grassmannianComapToRankLocus hf k) := by
  have h : IsPullback (f.grassmannianComapToRankLocus hf k) (toSpec R P k)
      ((schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).subschemeι ≫ toSpec R M k)
      (𝟙 _) :=
    Scheme.isPullback_of_forall_spec (by simp) fun A a b hab ↦ by
      rw [Category.comp_id] at hab
      subst hab
      exact existsUnique_comp_grassmannianComapToRankLocus f hf k a
  exact h.isIso_fst_of_isIso

/-- A surjection of ambient modules induces a closed immersion of quotient Grassmannians. -/
instance isClosedImmersion_grassmannianComap : IsClosedImmersion (f.grassmannianComap hf k) := by
  rw [grassmannianComap]
  infer_instance

/-- The scheme-theoretic image ideal is the rank-zero incidence ideal. -/
@[simp]
theorem ker_grassmannianComap :
    (f.grassmannianComap hf k).ker =
      schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0) := by
  rw [grassmannianComap, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- An equivariant surjection pulls back the stable locus scheme-theoretically. -/
@[simp]
theorem comap_grassmannianComap_schemeStableLocus (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) :
    (schemeStableLocus k t).comap (f.grassmannianComap hf k) = schemeStableLocus k u := by
  apply Scheme.IdealSheafData.ext_of_comap_openCover (chartOpenCover R P k)
  intro x
  dsimp only [chartOpenCover]
  rw [← Scheme.IdealSheafData.comap_comp, ← toSchemeHom_chartHomEquiv_id x,
    toSchemeHom_comp_grassmannianComap, comap_toSchemeHom_schemeStableLocus,
    comap_toSchemeHom_schemeStableLocus, stableLocus_comap _ f hf t u h]

/-- The closed immersion of stable quotient Grassmannians induced by an equivariant surjection. -/
noncomputable def grassmannianStableComap (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) :
    (schemeStableLocus k u).subscheme ⟶ (schemeStableLocus k t).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (f.grassmannianComap hf k)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (f.comap_grassmannianComap_schemeStableLocus hf k t u h).le)

/-- The map on stable loci agrees with the ambient incidence immersion. -/
@[reassoc (attr := simp)]
theorem grassmannianStableComap_comp_subschemeι (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) :
    f.grassmannianStableComap hf k t u h ≫ (schemeStableLocus k t).subschemeι =
      (schemeStableLocus k u).subschemeι ≫ f.grassmannianComap hf k :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The square of stable loci and ambient Grassmannians is cartesian. -/
theorem isPullback_grassmannianStableComap (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) :
    IsPullback (f.grassmannianStableComap hf k t u h) (schemeStableLocus k u).subschemeι
      (schemeStableLocus k t).subschemeι (f.grassmannianComap hf k) := by
  simpa only [Category.comp_id, grassmannianStableComap] using
    Scheme.IdealSheafData.isPullback_subschemeMap_of_eq
      (f.comap_grassmannianComap_schemeStableLocus hf k t u h).symm
      (IsPullback.id_vert (f.grassmannianComap hf k))

/-- Restricting the quotient incidence embedding to stable loci is a closed immersion. -/
instance isClosedImmersion_grassmannianStableComap (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) : IsClosedImmersion (f.grassmannianStableComap hf k t u h) := by
  have : IsClosedImmersion
      (f.grassmannianStableComap hf k t u h ≫ (schemeStableLocus k t).subschemeι) := by
    rw [grassmannianStableComap_comp_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (schemeStableLocus k t).subschemeι

/-- The image inside the stable locus is cut out by the same rank-zero incidence equations. -/
@[simp]
theorem ker_grassmannianStableComap (t : Module.End R M) (u : Module.End R P)
    (h : f.comp t = u.comp f) :
    (f.grassmannianStableComap hf k t u h).ker =
      (schemeRankLocus k (fun _ : Unit ↦ ker f) (fun _ ↦ 0)).comap
        (schemeStableLocus k t).subschemeι := by
  rw [← f.ker_grassmannianComap hf k]
  exact Scheme.IdealSheafData.ker_eq_comap_of_isPullback _
    (f.isPullback_grassmannianStableComap hf k t u h)

end LinearMap

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] {k : ℕ}

/-- A point lies in the scheme-theoretic image of the quotient Grassmannian exactly when its
kernel contains the base change of the kernel of the ambient surjection. -/
theorem exists_comp_grassmannianComap_eq_iff {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    (∃ c : Spec (.of A) ⟶ scheme R P k, c ≫ f.grassmannianComap hf k = toSchemeHom N) ↔
      (LinearMap.ker f).baseChange A ≤ N.toSubmodule := by
  have hiff : (f.grassmannianComap hf k).ker ≤ (toSchemeHom N).ker ↔
      (LinearMap.ker f).baseChange A ≤ N.toSubmodule := by
    simp [LinearMap.ker_grassmannianComap, schemeRankLocus_le_ker_toSchemeHom_iff]
  refine ⟨?_, fun h ↦ ⟨IsClosedImmersion.lift _ _ (hiff.mpr h),
    IsClosedImmersion.lift_fac _ _ _⟩⟩
  rintro ⟨c, hc⟩
  exact hiff.mp (hc ▸ c.le_ker_comp _)

end Module.Grassmannian

