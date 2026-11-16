/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.Algebra.Homology.ModuleCat.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.Flat
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.HomotopyEquiv

/-!
# A finite projective complex computing the cohomology of every base change

Let `R` be a Noetherian ring, `X` a scheme over `R` and `M` a quasi-coherent sheaf on `X` which
is flat over `R`, that is whose stalks are flat `R`-modules. Suppose that `X` is covered by
finitely many opens `U 0, …, U (N - 1)` whose nonempty finite intersections are affine, for
instance a finite affine open cover of a quasi-compact scheme with affine diagonal, and that the
cohomology modules `Hⁿ(X, M)` are finitely generated over `R`, as they are for a coherent sheaf
on a proper scheme. This file constructs a complex `P` of finitely generated projective
`R`-modules, concentrated in degrees `0, …, N - 1`, with a morphism `ψ` from `P` to the ordered
Čech complex of `M` which remains a quasi-isomorphism after every extension of scalars, so that for
every ring map `R → R'`, with base change `Y = X ×_R R'` and projection `g : Y ⟶ X`,

`Hⁿ(Y, g^* M) ≅ Hⁿ(R' ⊗_R P)` for every `n`

(`TauCeti.AlgebraicGeometry.exists_finite_projective_complex_cohomology_pullback`). This is the
complex of Mumford's *Abelian Varieties*, §5, and of Stacks Lemma 0B91: the cohomology of `M` on
all base changes of `X`, in particular on all its fibres `X ×_R κ(p)`, is computed by one bounded
complex of finite projective modules. It is the source of the semicontinuity theorem and of the
theorem on cohomology and base change.

The proof feeds the ordered Čech complex of `M` into the algebraic lemma of Mumford and
Grothendieck, `CochainComplex.exists_quasiIso_finite_projective`. The Čech complex `Č(U, M)` of
the `R`-modules of sections of `M` consists of flat modules
(`AlgebraicGeometry.Scheme.Modules.flat_cechComplexFunctor_obj_X_of_flat_stalk`), computes
`Hⁿ(X, M)` (`AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv`), and after
extension of scalars to `R'` computes `Hⁿ(Y, g^* M)`
(`TauCeti.AlgebraicGeometry.Cohomology.Cech.BaseChange`), but it is unbounded. Ordering the
cover, the ordered Čech complex `Čₒ(U, M)` of strictly increasing tuples vanishes in degrees
`≥ N` (`TauCeti.CategoryTheory.isZero_strictMonoCechComplexFunctor_obj_X`) and is homotopy
equivalent to `Č(U, M)` (`TauCeti.CategoryTheory.strictMonoCechComplexHomotopyEquiv`). The
homotopy equivalence survives extension of scalars, and the terms of `Čₒ(U, M)` are direct
summands of those of `Č(U, M)`, hence flat. So `Čₒ(U, M)`, extended from `ℕ` to `ℤ`, is a bounded
complex of flat modules with finitely generated cohomology which computes the cohomology of every
base change of `M`, and Mumford's lemma replaces it by a finite projective complex compatibly with
every base change.

## Main definitions

* `TauCeti.AlgebraicGeometry.orderedCechComplex`: the ordered Čech complex `Čₒ(U, M)` of
  `R`-modules, extended to `ℤ`.

## Main results

* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_homology_orderedCechComplex` and
  `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_homology_extendScalars_orderedCechComplex`:
  `Čₒ(U, M)` computes the cohomology of `M`, and after extension of scalars to `R'` the
  cohomology of its pullback to `X ×_R R'`.
* `TauCeti.AlgebraicGeometry.exists_finite_projective_complex_cohomology_pullback`: the complex
  `P` above, with the quasi-isomorphism `ψ : P ⟶ Čₒ(U, M)`.

## References

* D. Mumford, *Abelian Varieties*, Tata Institute, 1970, §5, the lemma on cohomology and base
  change and its proof.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.12.2 and
  Lemma III.12.3.
* [The Stacks Project, Lemma 0B91](https://stacks.math.columbia.edu/tag/0B91).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ComplexShape
open TauCeti.CategoryTheory AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] {ι : Type u}
  (U : ι → X.Opens) (M : X.Modules)

variable (R) in
/-- The ordered Čech complex of the `R`-modules of sections of `M` for an ordered family of opens
`U`, the complex of strictly increasing tuples of members of `U`, extended from `ℕ` to `ℤ` by zero
in negative degrees. -/
abbrev orderedCechComplex [LinearOrder ι] : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((strictMonoCechComplexFunctor U).obj ((sectionsBasePresheafFunctor R).obj M)).extend
    embeddingUpNat

/-- The ordered Čech complex of a sheaf whose stalks are flat over `R`, for a finite family of
opens with affine nonempty finite intersections, consists of flat `R`-modules: its terms are direct
summands of those of the Čech complex. -/
private lemma flat_orderedCechComplex_X [LinearOrder ι] [Finite ι] [M.IsQuasicoherent]
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))
    (hM : ∀ x : X, Module.Flat R (M.presheaf.stalk x)) (i : ℤ) :
    Module.Flat R ((orderedCechComplex R U M).X i) := by
  rcases lt_or_ge i 0 with hi | hi
  · have :=
      ModuleCat.subsingleton_of_isZero ((orderedCechComplex R U M).isZero_of_isStrictlyGE 0 i hi)
    infer_instance
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  let P := (sectionsBasePresheafFunctor R).obj M
  have := flat_cechComplexFunctor_obj_X_of_flat_stalk R U M hU (fun _ x ↦ hM x) n
  -- The restriction to strictly increasing tuples is split surjective, so the ordered term is a
  -- retract of the flat term of the Čech complex.
  have hO : Module.Flat R (((strictMonoCechComplexFunctor U).obj P).X n) :=
    Module.Flat.of_retract (section_ (((toStrictMonoCechComplex U).app P).f n)).hom
      (((toStrictMonoCechComplex U).app P).f n).hom
      (by rw [← ModuleCat.hom_comp, IsSplitEpi.id, ModuleCat.hom_id])
  exact Module.Flat.of_linearEquiv
    (HomologicalComplex.extendXIso _ embeddingUpNat (embeddingUpNat_f n)).toLinearEquiv

/-- In degrees at least the number of members of `U`, the ordered Čech complex is zero. -/
private lemma isStrictlyLE_orderedCechComplex [LinearOrder ι] [Finite ι] :
    (orderedCechComplex R U M).IsStrictlyLE (Nat.card ι - 1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact (isZero_strictMonoCechComplexFunctor_obj_X U (by omega) _).of_iso
    (HomologicalComplex.extendXIso _ embeddingUpNat (embeddingUpNat_f n))

variable [Finite ι] (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))
  (hcover : ⨆ i, U i = ⊤)

include hU hcover in
/-- The cohomology of the ordered Čech complex of a quasi-coherent sheaf, for a finite cover with
affine nonempty finite intersections, is the cohomology of the sheaf. -/
lemma nonempty_linearEquiv_homology_orderedCechComplex [LinearOrder ι]
    [M.IsQuasicoherent] (n : ℕ) :
    Nonempty ((orderedCechComplex R U M).homology n ≃ₗ[R] Cohomology M n) :=
  let P := (sectionsBasePresheafFunctor R).obj M
  ⟨(HomologicalComplex.extendHomologyIso _ embeddingUpNat (embeddingUpNat_f n) ≪≫
    ((strictMonoCechComplexHomotopyEquiv U P).toHomologyIso n).symm).toLinearEquiv ≪≫ₗ
      homologyCechComplexLinearEquiv U hU hcover M n⟩

include hU hcover in
/-- After extension of scalars along any `R → R'`, the ordered Čech complex of a quasi-coherent
sheaf, for a finite cover with affine nonempty finite intersections, computes the cohomology of
the pullback of the sheaf to the base change `Y = X ×_R R'`. -/
lemma nonempty_linearEquiv_homology_extendScalars_orderedCechComplex [LinearOrder ι]
    [M.IsQuasicoherent] {R' : Type u} [CommRing R'] [Algebra R R'] {Y : Scheme.{u}}
    [Y.Over (Spec (.of R'))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
      _).obj (orderedCechComplex R U M)).homology n ≃ₗ[R']
        Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R R')
  let P := (sectionsBasePresheafFunctor R).obj M
  obtain ⟨e⟩ :=
    nonempty_linearEquiv_homology_extendScalars_cechComplex_cohomology_pullback_of_iSup_eq_top
      H M U hU hcover n
  -- `Hⁿ(R' ⊗ Čₒ(U, M)) ≅ Hⁿ(R' ⊗ Č(U, M)) ≅ Hⁿ(Y, g^* M)`, extension of scalars preserving the
  -- homotopy equivalence `Č(U, M) ≃ Čₒ(U, M)`.
  let O := (strictMonoCechComplexFunctor U).obj P
  let e₁ : ((F.mapHomologicalComplex _).obj (orderedCechComplex R U M)).homology n ≅
      (((F.mapHomologicalComplex _).obj O).extend embeddingUpNat).homology n :=
    HomologicalComplex.homologyMapIso (HomologicalComplex.mapExtendIso F O embeddingUpNat) n
  let e₂ : (((F.mapHomologicalComplex _).obj O).extend embeddingUpNat).homology n ≅
      ((F.mapHomologicalComplex _).obj O).homology n :=
    HomologicalComplex.extendHomologyIso _ embeddingUpNat (embeddingUpNat_f n)
  let e₃ : ((F.mapHomologicalComplex _).obj O).homology n ≅
      ((F.mapHomologicalComplex _).obj ((cechComplexFunctor U).obj P)).homology n :=
    ((F.mapHomotopyEquiv (strictMonoCechComplexHomotopyEquiv U P)).toHomologyIso n).symm
  exact ⟨(e₁ ≪≫ e₂ ≪≫ e₃).toLinearEquiv ≪≫ₗ e⟩

include hU hcover in
/-- **A finite projective complex computing the cohomology of every base change.** Let `R` be
a Noetherian ring, `X` a scheme over `R` and `M` a quasi-coherent sheaf on `X` with stalks flat
over `R`. Let `U` be a finite ordered family of opens covering `X` whose nonempty finite
intersections are affine, and suppose that every cohomology module `Hⁿ(X, M)` is finitely
generated over `R`. Then there is a complex `P` of finitely generated projective `R`-modules,
concentrated in degrees `0` to `N - 1` where `N` is the number of members of `U`, with a morphism
`ψ : P ⟶ Čₒ(U, M)` to the ordered Čech complex (`TauCeti.AlgebraicGeometry.orderedCechComplex`)
which remains a quasi-isomorphism after extension of scalars along every ring map `R → R'`. In
particular, for every base change `Y = X ×_R R'` given as a pullback square, `Hⁿ(Y, g^* M)` is the
`n`-th cohomology of the complex `R' ⊗_R P` obtained by extension of scalars. -/
theorem exists_finite_projective_complex_cohomology_pullback [LinearOrder ι] [IsNoetherianRing R]
    [M.IsQuasicoherent] (hM : ∀ x : X, Module.Flat R (M.presheaf.stalk x))
    (hfin : ∀ n, Module.Finite R (Cohomology M n)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (ψ : P ⟶ orderedCechComplex R U M),
      P.IsStrictlyGE 0 ∧ P.IsStrictlyLE (Nat.card ι - 1) ∧
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧ QuasiIso ψ ∧
      (∀ (R' : Type u) [CommRing R'] (f : R →+* R'),
        QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map ψ)) ∧
      ∀ (R' : Type u) [CommRing R'] [Algebra R R'] (Y : Scheme.{u}) [Y.Over (Spec (.of R'))]
        (g : Y ⟶ X), IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) → ∀ n : ℕ,
        Nonempty ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
          _).obj P).homology n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  let K := orderedCechComplex R U M
  have := isStrictlyLE_orderedCechComplex (R := R) U M
  have hK (i : ℤ) : Module.Finite R (K.homology i) := by
    rcases lt_or_ge i 0 with hi | hi
    · have : Subsingleton (K.homology i) := ModuleCat.subsingleton_of_isZero
        ((K.sc i).isZero_homology_of_isZero_X₂ (K.isZero_of_isStrictlyGE 0 i hi))
      exact Module.Finite.of_finite
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨e⟩ := nonempty_linearEquiv_homology_orderedCechComplex (R := R) U M hU hcover n
    exact Module.Finite.equiv e.symm
  obtain ⟨P, ψ, hP₀, hP₁, hP, hψ₀, hψ⟩ := CochainComplex.exists_quasiIso_finite_projective K 0
    (Nat.card ι - 1) (flat_orderedCechComplex_X U M hU hM) hK
  refine ⟨P, ψ, hP₀, hP₁, hP, hψ₀, hψ, fun R' _ _ Y _ g H n ↦ ?_⟩
  have := hψ R' (algebraMap R R')
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_extendScalars_orderedCechComplex U M hU hcover H n
  exact ⟨(asIso (HomologicalComplex.homologyMap
    (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex _).map ψ) n)).toLinearEquiv
      ≪≫ₗ e⟩

end TauCeti.AlgebraicGeometry
