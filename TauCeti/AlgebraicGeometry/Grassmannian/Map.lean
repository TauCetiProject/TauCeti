/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus.Basic
public import TauCeti.RingTheory.Grassmannian.Map

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Closed Grassmannian embeddings induced by injections

An injection of modules with finite projective cokernel of constant rank `d` induces a closed
immersion of quotient Grassmannians, increasing the quotient rank by `d`. Its image imposes
upper containment of the kernel in the image of the injection. The defining ideal is the
incidence ideal with the fixed quotient point given by the cokernel.

For intertwined endomorphisms, the square of stable loci is cartesian, so the induced map of
stable quotient Grassmannians is again a closed immersion. All point statements and defining
ideals use arbitrary coefficient algebras, including nonreduced ones. Only the linear sequence
splits; the complementary summand need not be invariant.

## References

* The Stacks Project, Tag 089R, for the quotient Grassmannian functor.
* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1, for closed transitions between finite lattice charts.
* [Tau Ceti, inverse-image Grassmannian embeddings]
  (https://github.com/TauCetiProject/TauCeti/pull/47414), for the affine-point isomorphism
  argument, adapted here to image kernels and changing quotient rank.

The construction uses `Module.Grassmannian.incidenceLocus`, `schemeIdealLocus` and the quotient
product decomposition of `Submodule.nonempty_quotient_map_equiv_prod`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N] {d : ℕ}

private noncomputable def upperIncidenceIdealFamily (r : ℕ) (P : G(d, N; R))
    {A : Type u} [CommRing A] [Algebra R A] (T : G(r + d, A ⊗[R] N; A)) : Ideal A :=
  T.incidenceLocus (P.baseChange A)

/-- The closed upper incidence locus: quotient kernels of rank `r + d` contained in the kernel
of a fixed rank-`d` quotient `P`. -/
noncomputable def schemeUpperIncidence (r : ℕ) (P : G(d, N; R)) :
    (scheme R N (r + d)).IdealSheafData :=
  schemeIdealLocus (upperIncidenceIdealFamily r P)
    (fun f T ↦ incidenceLocus_baseChange_map f T P)

/-- Pulling the upper incidence subscheme back to an affine point gives its incidence ideal. -/
theorem comap_toSchemeHom_schemeUpperIncidence (r : ℕ) (P : G(d, N; R))
    {A : Type u} [CommRing A] [Algebra R A] (T : G(r + d, A ⊗[R] N; A)) :
    (schemeUpperIncidence r P).comap (toSchemeHom T) =
      ofIdealTop ((T.incidenceLocus (P.baseChange A)).map (Scheme.ΓSpecIso (.of A)).inv.hom) :=
  comap_toSchemeHom_schemeIdealLocus (upperIncidenceIdealFamily r P)
    (fun f T ↦ incidenceLocus_baseChange_map f T P) T

/-- The incidence equations characterize factorization through the upper incidence locus. -/
theorem schemeUpperIncidence_le_ker_toSchemeHom_iff (r : ℕ) (P : G(d, N; R))
    {A : Type u} [CommRing A] [Algebra R A] (T : G(r + d, A ⊗[R] N; A)) :
    schemeUpperIncidence r P ≤ (toSchemeHom T).ker ↔
      T.toSubmodule ≤ (P.baseChange A).toSubmodule :=
  (schemeIdealLocus_le_ker_toSchemeHom_iff (upperIncidenceIdealFamily r P)
    (fun f T ↦ incidenceLocus_baseChange_map f T P) T).trans
    (incidenceLocus_eq_bot_iff _ _)

/-- The upper incidence closed subscheme represents the kernels contained in `P`. -/
noncomputable def schemeUpperIncidenceHomEquiv (r : ℕ) (P : G(d, N; R))
    (A : Type u) [CommRing A] [Algebra R A] :
    {T : G(r + d, A ⊗[R] N; A) // T.toSubmodule ≤ (P.baseChange A).toSubmodule} ≃
      {h : Spec (.of A) ⟶ (schemeUpperIncidence r P).subscheme //
        h ≫ (schemeUpperIncidence r P).subschemeι ≫ toSpec R N (r + d) =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  (Equiv.subtypeEquivRight fun T ↦ (incidenceLocus_eq_bot_iff T _).symm).trans
    (schemeIdealLocusHomEquiv (upperIncidenceIdealFamily r P)
      (fun f T ↦ incidenceLocus_baseChange_map f T P) A)

/-- The incidence point followed by the inclusion classifies its kernel. -/
@[reassoc (attr := simp)]
theorem schemeUpperIncidenceHomEquiv_apply_comp_subschemeι (r : ℕ) (P : G(d, N; R))
    {A : Type u} [CommRing A] [Algebra R A]
    (T : {T : G(r + d, A ⊗[R] N; A) // T.toSubmodule ≤ (P.baseChange A).toSubmodule}) :
    (schemeUpperIncidenceHomEquiv r P A T).val ≫ (schemeUpperIncidence r P).subschemeι =
      toSchemeHom T.val :=
  schemeIdealLocusHomEquiv_apply_comp_subschemeι (upperIncidenceIdealFamily r P)
    (fun f T ↦ incidenceLocus_baseChange_map f T P) _

/-- Recovering a kernel from an incidence point agrees with the ambient classifier. -/
@[simp]
theorem toSchemeHom_schemeUpperIncidenceHomEquiv_symm_apply (r : ℕ) (P : G(d, N; R))
    {A : Type u} [CommRing A] [Algebra R A]
    (h : {h : Spec (.of A) ⟶ (schemeUpperIncidence r P).subscheme //
      h ≫ (schemeUpperIncidence r P).subschemeι ≫ toSpec R N (r + d) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeUpperIncidenceHomEquiv r P A).symm h).val =
      h.val ≫ (schemeUpperIncidence r P).subschemeι :=
  toSchemeHom_schemeIdealLocusHomEquiv_symm_apply
    (upperIncidenceIdealFamily r P)
    (fun f T ↦ incidenceLocus_baseChange_map f T P) _

end Module.Grassmannian

namespace LinearMap

open Module.Grassmannian

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {d : ℕ} (i : M →ₗ[R] N) (hi : Function.Injective i)
  (P : G(d, N; R)) (hP : P.toSubmodule = range i) (r : ℕ)

/-- The injection construction, valued in its closed upper incidence locus. -/
noncomputable def grassmannianMapToUpperIncidence :
    scheme R M r ⟶ (schemeUpperIncidence r P).subscheme :=
  homOfPoints (fun A _ _ S ↦ (schemeUpperIncidenceHomEquiv r P A
    (mapEquivOfInjectiveBaseChange r i hi P hP A S)).val)
    fun A B _ _ _ _ f S ↦ by
      apply (cancel_mono (schemeUpperIncidence r P).subschemeι).1
      simp only [Category.assoc, schemeUpperIncidenceHomEquiv_apply_comp_subschemeι,
        mapEquivOfInjectiveBaseChange_apply_val]
      rw [← toSchemeHom_map, map_mapOfInjectiveBaseChange]

/-- An injection with finite projective constant-rank cokernel induces a closed immersion of
quotient Grassmannians, taking each kernel to its image. -/
noncomputable def grassmannianMap : scheme R M r ⟶ scheme R N (r + d) :=
  i.grassmannianMapToUpperIncidence hi P hP r ≫ (schemeUpperIncidence r P).subschemeι

/-- The factorization of the injection map through the upper incidence closed subscheme. -/
@[reassoc (attr := simp)]
theorem grassmannianMapToUpperIncidence_comp_subschemeι :
    i.grassmannianMapToUpperIncidence hi P hP r ≫ (schemeUpperIncidence r P).subschemeι =
      i.grassmannianMap hi P hP r := (rfl)

/-- The injection map takes images of kernels over every coefficient algebra. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_grassmannianMap {A : Type u} [CommRing A] [Algebra R A]
    (S : G(r, A ⊗[R] M; A)) :
    toSchemeHom S ≫ i.grassmannianMap hi P hP r =
      toSchemeHom (S.mapOfInjectiveBaseChange i hi P hP) := by
  simp [grassmannianMap, grassmannianMapToUpperIncidence]

/-- The injection map is a morphism over the base ring. -/
@[reassoc (attr := simp)]
theorem grassmannianMap_toSpec :
    i.grassmannianMap hi P hP r ≫ toSpec R N (r + d) = toSpec R M r :=
  scheme_hom_ext fun A _ _ S ↦ by simp [toSchemeHom_toSpec]

private theorem existsUnique_comp_grassmannianMapToUpperIncidence {A : CommRingCat.{u}}
    (a : Spec A ⟶ (schemeUpperIncidence r P).subscheme) :
    ∃! c : Spec A ⟶ scheme R M r,
      c ≫ i.grassmannianMapToUpperIncidence hi P hP r = a ∧
        c ≫ toSpec R M r = a ≫ (schemeUpperIncidence r P).subschemeι ≫
          toSpec R N (r + d) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    (a ≫ (schemeUpperIncidence r P).subschemeι ≫ toSpec R N (r + d))
  let _ : Algebra R A := φ.hom.toAlgebra
  have ha : a ≫ (schemeUpperIncidence r P).subschemeι ≫ toSpec R N (r + d) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← hφ, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  let T := (schemeUpperIncidenceHomEquiv r P A).symm ⟨a, ha⟩
  let S := (mapEquivOfInjectiveBaseChange r i hi P hP A).symm T
  have hS : S.mapOfInjectiveBaseChange i hi P hP = T.val := by
    simpa only [mapEquivOfInjectiveBaseChange_apply_val] using
      congrArg Subtype.val ((mapEquivOfInjectiveBaseChange r i hi P hP A).apply_symm_apply T)
  have hc : toSchemeHom S ≫ i.grassmannianMapToUpperIncidence hi P hP r = a := by
    apply (cancel_mono (schemeUpperIncidence r P).subschemeι).1
    rw [Category.assoc, grassmannianMapToUpperIncidence_comp_subschemeι,
      toSchemeHom_comp_grassmannianMap, hS, toSchemeHom_schemeUpperIncidenceHomEquiv_symm_apply]
  refine ⟨toSchemeHom S, ⟨hc, by rw [ha, toSchemeHom_toSpec]⟩, ?_⟩
  rintro c ⟨hc₁, hc₂⟩
  obtain ⟨L, rfl⟩ := exists_toSchemeHom_eq c (hc₂.trans ha)
  apply congrArg toSchemeHom
  apply (mapEquivOfInjectiveBaseChange r i hi P hP A).injective
  apply Subtype.ext
  apply toSchemeHom_injective
  rw [mapEquivOfInjectiveBaseChange_apply_val, mapEquivOfInjectiveBaseChange_apply_val,
    ← toSchemeHom_comp_grassmannianMap, ← toSchemeHom_comp_grassmannianMap,
    ← grassmannianMapToUpperIncidence_comp_subschemeι]
  rw [← Category.assoc, ← Category.assoc, hc₁, hc]

/-- The injection construction identifies the source Grassmannian with the upper incidence
closed subscheme, on the level of schemes. -/
instance isIso_grassmannianMapToUpperIncidence :
    IsIso (i.grassmannianMapToUpperIncidence hi P hP r) := by
  have h : IsPullback (i.grassmannianMapToUpperIncidence hi P hP r) (toSpec R M r)
      ((schemeUpperIncidence r P).subschemeι ≫ toSpec R N (r + d)) (𝟙 _) :=
    Scheme.isPullback_of_forall_spec (by simp) fun A a b hab ↦ by
      rw [Category.comp_id] at hab
      subst hab
      exact existsUnique_comp_grassmannianMapToUpperIncidence i hi P hP r a
  exact h.isIso_fst_of_isIso

/-- An injection with finite projective cokernel induces a closed immersion. -/
instance isClosedImmersion_grassmannianMap : IsClosedImmersion (i.grassmannianMap hi P hP r) := by
  rw [grassmannianMap]
  infer_instance

/-- The scheme-theoretic image is defined by the upper incidence ideal. -/
@[simp]
theorem ker_grassmannianMap :
    (i.grassmannianMap hi P hP r).ker = schemeUpperIncidence r P := by
  rw [grassmannianMap, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- The inverse image of stability is the stability locus in the source. -/
theorem comap_grassmannianMap_schemeStableLocus (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    (schemeStableLocus (r + d) u).comap (i.grassmannianMap hi P hP r) =
      schemeStableLocus r t := by
  apply Scheme.IdealSheafData.ext_of_comap_openCover (chartOpenCover R M r)
  intro x
  dsimp only [chartOpenCover]
  rw [← comap_comp, ← toSchemeHom_chartHomEquiv_id x, toSchemeHom_comp_grassmannianMap,
    comap_toSchemeHom_schemeStableLocus, comap_toSchemeHom_schemeStableLocus,
    stableLocus_mapOfInjectiveBaseChange _ i hi P hP t u htu]

/-- The closed immersion of stable quotient Grassmannians induced by an intertwined injection. -/
noncomputable def grassmannianStableMap (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    (schemeStableLocus r t).subscheme ⟶ (schemeStableLocus (r + d) u).subscheme :=
  subschemeMap _ _ (i.grassmannianMap hi P hP r)
    (le_map_iff_comap_le.mpr (i.comap_grassmannianMap_schemeStableLocus hi P hP r t u htu).le)

/-- The stable injection map lies over the ambient injection map. -/
@[reassoc (attr := simp)]
theorem grassmannianStableMap_comp_subschemeι (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    i.grassmannianStableMap hi P hP r t u htu ≫ (schemeStableLocus (r + d) u).subschemeι =
      (schemeStableLocus r t).subschemeι ≫ i.grassmannianMap hi P hP r :=
  subschemeMap_subschemeι _ _ _ _

/-- On stable points the closed immersion sends the kernel to its image under the injection. -/
@[reassoc (attr := simp)]
theorem schemeStableLocusHomEquiv_apply_comp_grassmannianStableMap
    (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) {A : Type u} [CommRing A] [Algebra R A]
    (S : {S : G(r, A ⊗[R] M; A) //
      S.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A)}) :
    (schemeStableLocusHomEquiv r t A S).val ≫ i.grassmannianStableMap hi P hP r t u htu =
      (schemeStableLocusHomEquiv (r + d) u A
        ⟨S.val.mapOfInjectiveBaseChange i hi P hP,
          (mapOfInjectiveBaseChange_mem_invtSubmodule_iff S.val i hi P hP t u htu).mpr
            S.property⟩).val := by
  apply (cancel_mono (schemeStableLocus (r + d) u).subschemeι).1
  simp only [Category.assoc, grassmannianStableMap_comp_subschemeι,
    schemeStableLocusHomEquiv_apply_comp_subschemeι_assoc,
    schemeStableLocusHomEquiv_apply_comp_subschemeι, toSchemeHom_comp_grassmannianMap]

/-- The square of stable loci and ambient Grassmannians is cartesian. -/
theorem isPullback_grassmannianStableMap (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    IsPullback (i.grassmannianStableMap hi P hP r t u htu) (schemeStableLocus r t).subschemeι
      (schemeStableLocus (r + d) u).subschemeι (i.grassmannianMap hi P hP r) := by
  simpa only [Category.comp_id, grassmannianStableMap] using
    isPullback_subschemeMap_of_eq
      (i.comap_grassmannianMap_schemeStableLocus hi P hP r t u htu).symm
      (IsPullback.id_vert (i.grassmannianMap hi P hP r))

/-- The map of stable quotient Grassmannians induced by an injection is a closed immersion. -/
instance isClosedImmersion_grassmannianStableMap (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    IsClosedImmersion (i.grassmannianStableMap hi P hP r t u htu) := by
  have : IsClosedImmersion (i.grassmannianStableMap hi P hP r t u htu ≫
      (schemeStableLocus (r + d) u).subschemeι) := by
    rw [grassmannianStableMap_comp_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (schemeStableLocus (r + d) u).subschemeι

/-- The stable injection image is cut out by the upper incidence equations inside the stable
Grassmannian, including their scheme structure over nonreduced test rings. -/
@[simp]
theorem ker_grassmannianStableMap (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    (i.grassmannianStableMap hi P hP r t u htu).ker =
      (schemeUpperIncidence r P).comap (schemeStableLocus (r + d) u).subschemeι := by
  rw [← i.ker_grassmannianMap hi P hP r]
  exact ker_eq_comap_of_isPullback _ (i.isPullback_grassmannianStableMap hi P hP r t u htu)

/-- In the ambient Grassmannian the stable injection image is defined by the sum of the
incidence and stability ideals, both compatible with arbitrary coefficient maps. -/
theorem ker_grassmannianStableMap_comp_subschemeι (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    (i.grassmannianStableMap hi P hP r t u htu ≫
      (schemeStableLocus (r + d) u).subschemeι).ker =
      schemeIdealLocus (fun {A} _ _ T ↦ T.incidenceLocus (P.baseChange A) ⊔ T.stableLocus u)
        (fun f T ↦ by rw [incidenceLocus_baseChange_map, stableLocus_map, Ideal.map_sup]) := by
  rw [Scheme.Hom.ker_comp, ker_grassmannianStableMap, map_comap_of_isClosedImmersion,
    ker_subschemeι]
  apply Scheme.IdealSheafData.ext_of_comap_openCover (chartOpenCover R N (r + d))
  intro x
  dsimp only [chartOpenCover]
  rw [← toSchemeHom_chartHomEquiv_id x, comap_sup,
    comap_toSchemeHom_schemeUpperIncidence, comap_toSchemeHom_schemeStableLocus,
    comap_toSchemeHom_schemeIdealLocus, Ideal.map_sup]
  simp only [← equivOfIsAffine_symm_apply, map_sup]

/-- Every stable point lies in the stable injection image exactly when its kernel satisfies
upper containment. -/
theorem exists_comp_grassmannianStableMap_eq_iff (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) {A : Type u} [CommRing A] [Algebra R A]
    (T : {T : G(r + d, A ⊗[R] N; A) //
      T.toSubmodule ∈ Module.End.invtSubmodule (u.baseChange A)}) :
    (∃ c : Spec (.of A) ⟶ (schemeStableLocus r t).subscheme,
      c ≫ i.grassmannianStableMap hi P hP r t u htu =
        (schemeStableLocusHomEquiv (r + d) u A T).val) ↔
      T.val.toSubmodule ≤ (P.baseChange A).toSubmodule := by
  have hiff : (i.grassmannianStableMap hi P hP r t u htu).ker ≤
      (schemeStableLocusHomEquiv (r + d) u A T).val.ker ↔
      T.val.toSubmodule ≤ (P.baseChange A).toSubmodule := by
    rw [ker_grassmannianStableMap, ← le_map_iff_comap_le, map_ker,
      schemeStableLocusHomEquiv_apply_comp_subschemeι,
      schemeUpperIncidence_le_ker_toSchemeHom_iff]
  refine ⟨?_, fun h ↦ ⟨IsClosedImmersion.lift _ _ (hiff.mpr h),
    IsClosedImmersion.lift_fac _ _ _⟩⟩
  rintro ⟨c, hc⟩
  exact hiff.mp (hc ▸ c.le_ker_comp _)

/-- The injection morphism commutes with extension of the ground ring along the canonical
Grassmannian base-change projections. -/
@[reassoc]
theorem grassmannianMap_baseChange_comp_baseChangeHom (R' : Type u) [CommRing R']
    [Algebra R R'] (hi' : Function.Injective (i.baseChange R'))
    (P' : G(d, R' ⊗[R] N; R')) (hP' : P'.toSubmodule = range (i.baseChange R')) :
    (i.baseChange R').grassmannianMap hi' P' hP' r ≫
      Module.Grassmannian.baseChangeHom R R' N (r + d) =
      Module.Grassmannian.baseChangeHom R R' M r ≫ i.grassmannianMap hi P hP r := by
  apply scheme_hom_ext
  intro A _ _ S
  let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  simp only [toSchemeHom_comp_grassmannianMap_assoc, toSchemeHom_comp_baseChangeHom,
    toSchemeHom_comp_baseChangeHom_assoc, toSchemeHom_comp_grassmannianMap]
  rw [baseChangeEquiv_mapOfInjectiveBaseChange S i hi P hP hi' P' hP']

/-- Extending the ground ring gives the base change of the closed injection morphism. -/
theorem isPullback_grassmannianMap_baseChange (R' : Type u) [CommRing R'] [Algebra R R']
    (hi' : Function.Injective (i.baseChange R')) (P' : G(d, R' ⊗[R] N; R'))
    (hP' : P'.toSubmodule = range (i.baseChange R')) :
    IsPullback ((i.baseChange R').grassmannianMap hi' P' hP' r)
      (Module.Grassmannian.baseChangeHom R R' M r)
      (Module.Grassmannian.baseChangeHom R R' N (r + d)) (i.grassmannianMap hi P hP r) := by
  have hs : IsPullback
      ((i.baseChange R').grassmannianMap hi' P' hP' r ≫ toSpec R' (R' ⊗[R] N) (r + d))
      (Module.Grassmannian.baseChangeHom R R' M r)
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (i.grassmannianMap hi P hP r ≫ toSpec R N (r + d)) := by
    simpa only [grassmannianMap_toSpec] using (isPullback_baseChangeHom R R' M r).flip
  exact hs.of_right (i.grassmannianMap_baseChange_comp_baseChangeHom hi P hP r R' hi' P' hP')
    (isPullback_baseChangeHom R R' N (r + d)).flip

/-- Successive injection morphisms agree with the composite injection after identifying
`(r + d) + d'` with `r + (d + d')`. -/
@[reassoc]
theorem grassmannianMap_comp {L : Type u} [AddCommGroup L] [Module R L] {d' : ℕ}
    (i : M →ₗ[R] N) (hi : Function.Injective i)
    (P : G(d, N; R)) (hP : P.toSubmodule = range i)
    (j : N →ₗ[R] L) (hj : Function.Injective j)
    (P' : G(d', L; R)) (hP' : P'.toSubmodule = range j)
    (Q : G(d + d', L; R)) (hQ : Q.toSubmodule = range (j ∘ₗ i)) :
    i.grassmannianMap hi P hP r ≫ j.grassmannianMap hj P' hP' (r + d) ≫
      eqToHom (congrArg (scheme R L) (Nat.add_assoc r d d')) =
      (j ∘ₗ i).grassmannianMap (hj.comp hi) Q hQ r := by
  have hcast {a b : ℕ} (h : a = b) {A : Type u} [CommRing A] [Algebra R A]
      (T : G(a, A ⊗[R] L; A)) :
      toSchemeHom T ≫ eqToHom (congrArg (scheme R L) h) =
        toSchemeHom (cast (congrArg (fun n ↦ G(n, A ⊗[R] L; A)) h) T) := by
    cases h
    simp
  apply scheme_hom_ext
  intro A _ _ S
  rw [toSchemeHom_comp_grassmannianMap_assoc, toSchemeHom_comp_grassmannianMap_assoc,
    toSchemeHom_comp_grassmannianMap, hcast (Nat.add_assoc r d d')]
  apply congrArg toSchemeHom
  exact mapOfInjectiveBaseChange_comp S i hi P hP j hj P' hP' Q hQ

/-- The identity injection gives the identity on the Grassmannian. -/
@[simp]
theorem grassmannianMap_id (P : G(0, M; R))
    (hP : P.toSubmodule = range (LinearMap.id : M →ₗ[R] M)) :
    (LinearMap.id : M →ₗ[R] M).grassmannianMap Function.injective_id P hP r = 𝟙 _ := by
  apply scheme_hom_ext
  intro A _ _ S
  rw [toSchemeHom_comp_grassmannianMap, Category.comp_id]
  apply congrArg toSchemeHom
  ext : 1
  simp [LinearMap.baseChange_id]

/-- The identity injection also induces the identity on every stable locus. -/
@[simp]
theorem grassmannianStableMap_id (P : G(0, M; R))
    (hP : P.toSubmodule = range (LinearMap.id : M →ₗ[R] M)) (t : Module.End R M) :
    (LinearMap.id : M →ₗ[R] M).grassmannianStableMap Function.injective_id P hP r t t
      (by simp) = 𝟙 _ := by
  apply (cancel_mono (schemeStableLocus r t).subschemeι).1
  simpa only [Nat.add_zero, grassmannianMap_id, Category.comp_id, Category.id_comp] using
    (LinearMap.id : M →ₗ[R] M).grassmannianStableMap_comp_subschemeι
      Function.injective_id P hP r t t (by simp)

end LinearMap
