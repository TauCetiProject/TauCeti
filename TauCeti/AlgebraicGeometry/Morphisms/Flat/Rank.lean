/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
public import TauCeti.RingTheory.Length
public import TauCeti.RingTheory.Flat.Rank

/-!
# The rank of finite flat morphisms

The rank `Scheme.Hom.finrank` of a finite flat morphism is invariant under isomorphisms over its
base. This packages Mathlib's `Scheme.Hom.finrank_comp_left_of_isIso` for objects of `Over S`.
`TauCeti.finrank_eq_of_nonempty_iso_over` requires only the existence of an isomorphism over the
base, incorporating its commuting triangle. It compares an affine group scheme with the Hopf
spectrum of its coordinate algebra, and also transports rank through isomorphisms with Cartier
duals. Composing with an isomorphism of targets instead moves the point at which the rank is
evaluated (`AlgebraicGeometry.Scheme.Hom.finrank_comp_right_of_isIso`).

For finite flat morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, if `f` has constant rank `n`, then
`(f ≫ g).finrank s = n * g.finrank s` (`AlgebraicGeometry.Scheme.Hom.finrank_comp`): degrees of
finite locally free morphisms multiply in towers. The constancy hypothesis cannot be dropped,
since the points of `Y` over a given point of `S` can carry different ranks of `f`. Over an
affine base this is `TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq`, and the general case
reduces to it because the rank is computed after base change to affine opens of `S`. More
generally, it suffices that `f` have rank `n` on the fibre of `g` over `s`
(`AlgebraicGeometry.Scheme.Hom.finrank_comp_of_fiber`): after base change to the residue field
of `s`, the rank of `f` is constant.

The rank is at least `1` at the points of the image (Mathlib's `Scheme.Hom.one_le_finrank_map`)
and is `0` at every other point (`AlgebraicGeometry.Scheme.Hom.finrank_eq_zero_iff_notMem_range`).

Over the spectrum of a field `K`, a finite morphism `f : X ⟶ Spec K` has affine source, and its
rank is the `K`-dimension of `Γ(X, ⊤)` (`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`).
This dimension is computed point by point: `X` has finitely many points, each local ring `𝒪_{X,x}`
is Artinian, and the rank is the sum over the points `x` of the length of `𝒪_{X,x}` weighted by the
residue degree `[κ(x) : K]`
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finsum_residueDegree_mul_length`). For the intersection
`D ∩ C` of two curves meeting properly on a regular surface over `K`, this writes the degree
over `K` of the intersection as the sum of the local intersection multiplicities weighted by
`[κ(x) : K]`.

## Main results

* `TauCeti.finrank_eq_of_nonempty_iso_over`: isomorphic schemes over `S` have the same rank.
* `TauCeti.finiteLocallyFree_iff_of_iso`: being finite locally free of constant rank `k` over `S`
  is invariant under isomorphism over `S`.
* `AlgebraicGeometry.Scheme.Hom.finrank_comp_right_of_isIso`: the rank of `f ≫ e` at `e y` is the
  rank of `f` at `y`, for an isomorphism `e`.
* `AlgebraicGeometry.Scheme.Hom.finrank_comp`: the rank of a composite whose first factor has
  constant rank.
* `AlgebraicGeometry.Scheme.Hom.finrank_comp_of_fiber`: the rank of a composite whose first factor
  has constant rank on a fibre of the second.
* `AlgebraicGeometry.Scheme.Hom.finrank_eq_zero_iff_notMem_range`: the rank vanishes exactly at
  the points outside the image.
* `AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`: over a field, the rank is the
  dimension of the global sections.
* `AlgebraicGeometry.Scheme.Hom.finrank_eq_finsum_residueDegree_mul_length`: over a field, the rank
  is the sum over the points of the lengths of the local rings times the residue degrees.

## Usage

For `e : X ≅ Y` in `Over S`, use `TauCeti.finrank_eq_of_nonempty_iso_over ⟨e⟩` to obtain
`X.hom.finrank = Y.hom.finrank` when `Y.hom` is finite and flat.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA): the degree of a finite
  locally free morphism.
* [Stacks Project, Tag 00JA](https://stacks.math.columbia.edu/tag/00JA): an Artinian ring is the
  product of its localizations at its maximal ideals.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

namespace TauCeti

universe u

/-- Isomorphic schemes over a fixed base have the same rank function when the target
structural morphism is finite and flat. -/
theorem finrank_eq_of_nonempty_iso_over {S : Scheme.{u}} {X Y : Over S}
    (h : Nonempty (X ≅ Y))
    [Flat Y.hom] [IsFinite Y.hom] : X.hom.finrank = Y.hom.finrank := by
  obtain ⟨e⟩ := h
  rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]

/-- Being finite locally free of constant rank `k` is invariant under isomorphism over the
base. -/
theorem finiteLocallyFree_iff_of_iso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) {k : ℕ} :
    (IsFinite X.hom ∧ Flat X.hom ∧ LocallyOfFinitePresentation X.hom ∧
        ∀ s, X.hom.finrank s = k) ↔
      (IsFinite Y.hom ∧ Flat Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
        ∀ s, Y.hom.finrank s = k) := by
  rw [MorphismProperty.over_iso_iff @IsFinite e, MorphismProperty.over_iso_iff @Flat e,
    MorphismProperty.over_iso_iff @LocallyOfFinitePresentation e]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ by
    rw [finrank_eq_of_nonempty_iso_over ⟨e⟩]

end TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- Composing a finite flat morphism with an isomorphism of targets transports its rank: the
rank of `f ≫ e` at `e y` is the rank of `f` at `y`. -/
@[simp]
theorem Scheme.Hom.finrank_comp_right_of_isIso (f : X ⟶ Y) (e : Y ⟶ S) [IsIso e] [Flat f]
    [IsFinite f] (y : Y) : (f ≫ e).finrank (e y) = f.finrank y :=
  (finrank_of_isPullback (𝟙 X) f (f ≫ e) e (.of_horiz_isIso ⟨by simp⟩) y).symm

/-- **The rank vanishes exactly off the image.** A finite flat morphism `f : X ⟶ Y` has rank `0`
at `y` if and only if `y` is not in the image of `f`. -/
theorem Scheme.Hom.finrank_eq_zero_iff_notMem_range (f : X ⟶ Y) [Flat f] [IsFinite f] (y : Y) :
    f.finrank y = 0 ↔ y ∉ Set.range f := by
  refine ⟨fun h ⟨x, hx⟩ ↦ by simpa [hx, h] using f.one_le_finrank_map x, fun hy ↦ ?_⟩
  -- Reduce to an affine target, then to an affine source, as for `one_le_finrank_map`.
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · obtain ⟨R, g, _, z, rfl⟩ := Y.exists_Spec_apply_eq y
    rw [← finrank_pullback_snd]
    refine this _ z (fun ⟨w, hw⟩ ↦ hy ⟨pullback.fst f g w, ?_⟩) ⟨R, rfl⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ A, X = Spec A generalizing X with H
  · have : IsAffine X := isAffine_of_isAffineHom f
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]
    exact H _ (fun ⟨x, hx⟩ ↦ hy ⟨X.isoSpec.inv x, hx⟩) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap, ← Nat.le_zero, ← not_lt]
  exact fun h ↦ hy ((PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap _).mp h)

/-- **The rank is multiplicative in towers.** If `f : X ⟶ Y` and `g : Y ⟶ S` are finite and flat
and `f` has constant rank `n`, then the rank of `f ≫ g` is `n` times the rank of `g`. -/
theorem Scheme.Hom.finrank_comp (f : X ⟶ Y) (g : Y ⟶ S) [Flat f] [IsFinite f] [Flat g]
    [IsFinite g] {n : ℕ} (hf : ∀ y, f.finrank y = n) (s : S) :
    (f ≫ g).finrank s = n * g.finrank s := by
  -- Reduce to an affine base: base change along an affine open `Spec R ⟶ S` preserves the ranks
  -- of `g` and of `f ≫ g`, and the base change of `f` still has constant rank `n`.
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · obtain ⟨R, i, _, s, rfl⟩ := S.exists_Spec_apply_eq s
    rw [← finrank_pullback_snd, ← finrank_pullback_snd,
      ← finrank_comp_left_of_isIso (pullbackRightPullbackFstIso g i f).hom,
      pullbackRightPullbackFstIso_hom_snd]
    refine this _ _ (fun y ↦ ?_) s ⟨R, rfl⟩
    rw [finrank_pullback_snd, hf]
  obtain ⟨R, rfl⟩ := hS
  -- Over an affine base, `Y` and `X` are affine, so both may be replaced by spectra.
  wlog hY : ∃ A, Y = Spec A generalizing X Y with H
  · have : IsAffine Y := isAffine_of_isAffineHom g
    have := H (f ≫ Y.isoSpec.hom) (fun y ↦ ?_) (Y.isoSpec.inv ≫ g) ⟨_, rfl⟩
    · simpa using this
    · obtain ⟨y, rfl⟩ := Y.isoSpec.hom.surjective y
      rw [finrank_comp_right_of_isIso, hf]
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X with H
  · have : IsAffine X := isAffine_of_isAffineHom f
    have := H (X.isoSpec.inv ≫ f) (fun y ↦ by rw [finrank_comp_left_of_isIso, hf]) ⟨_, rfl⟩
    rwa [Category.assoc, finrank_comp_left_of_isIso] at this
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  -- For spectra, the ranks are the ranks at stalks of the corresponding algebras.
  have hfin : (ψ ≫ φ).hom.Finite := ‹φ.hom.Finite›.comp ‹ψ.hom.Finite›
  have hflat : (ψ ≫ φ).hom.Flat := ‹ψ.hom.Flat›.comp ‹φ.hom.Flat›
  rw [← Spec.map_comp, finrank_SpecMap_eq_finrank hfin hflat, finrank_SpecMap_eq_finrank ‹_› ‹_›]
  let := ψ.hom.toAlgebra
  let := φ.hom.toAlgebra
  let := (ψ ≫ φ).hom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : Module.Finite R A := ‹ψ.hom.Finite›
  have : Module.Flat R A := ‹ψ.hom.Flat›
  have : Module.Finite A B := ‹φ.hom.Finite›
  have : Module.Flat A B := ‹φ.hom.Flat›
  rw [← RingHom.algebraMap_toAlgebra ψ.hom, ← RingHom.algebraMap_toAlgebra (ψ ≫ φ).hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]
  refine TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq (A := A) (fun q ↦ ?_) s
  have := hf q
  rwa [finrank_SpecMap_eq_finrank ‹φ.hom.Finite› ‹φ.hom.Flat›,
    ← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap] at this

/-- **The rank is multiplicative in towers, fibrewise.** If `f : X ⟶ Y` and `g : Y ⟶ S` are finite
and flat and `f` has rank `n` at every point of the fibre of `g` over `s`, then the rank of
`f ≫ g` at `s` is `n` times the rank of `g` at `s`. -/
theorem Scheme.Hom.finrank_comp_of_fiber (f : X ⟶ Y) (g : Y ⟶ S) [Flat f] [IsFinite f] [Flat g]
    [IsFinite g] {n : ℕ} {s : S} (hf : ∀ y, g y = s → f.finrank y = n) :
    (f ≫ g).finrank s = n * g.finrank s := by
  -- Over the residue field of `s`, the base change of `f` has constant rank `n`.
  let t := S.fromSpecResidueField s
  obtain ⟨a⟩ : Nonempty (Spec (.of (S.residueField s))) := inferInstance
  rw [← S.fromSpecResidueField_apply s a, ← finrank_pullback_snd, ← finrank_pullback_snd,
    ← finrank_comp_left_of_isIso (pullbackRightPullbackFstIso g t f).hom,
    pullbackRightPullbackFstIso_hom_snd]
  refine finrank_comp _ _ (fun y ↦ ?_) a
  rw [finrank_pullback_snd]
  refine hf _ ?_
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  simp only [t, S.fromSpecResidueField_apply]

/-- **Over a field, the rank is the dimension of the global sections.** The rank of a finite
morphism `f : X ⟶ Spec K` is the `K`-dimension of `Γ(X, ⊤)`, for the `K`-algebra structure given
by the map of global sections. -/
theorem Scheme.Hom.finrank_eq_finrank_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Algebra K Γ(X, ⊤)]
    (hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    (s : Spec (.of K)) : f.finrank s = Module.finrank K Γ(X, ⊤) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have hfin : (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))).hom.Finite := by
    rwa [CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  -- `f` is the spectrum of the map of global sections, up to the isomorphism `X ≅ Spec Γ(X, ⊤)`.
  have e : f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
    rw [hf, CommRingCat.ofHom_hom, Spec.map_comp, Scheme.isoSpec_hom,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) :=
    (IsFinite.SpecMap_iff _).mpr hfin
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [e, finrank_comp_left_of_isIso, finrank_SpecMap_algebraMap K Γ(X, ⊤) s,
    Module.rankAtStalk_eq_finrank_of_free]
  -- The rank of a free module is the constant function with value its `finrank`.
  rfl

private theorem finrank_residueField_stalk {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) [Algebra K Γ(X, ⊤)]
    (hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    [Algebra K (X.presheaf.stalk x)]
    (hx : algebraMap K (X.presheaf.stalk x) =
      (X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom.comp (algebraMap K Γ(X, ⊤))) :
    Module.finrank K (IsLocalRing.ResidueField (X.presheaf.stalk x)) = f.residueDegree x := by
  let : Algebra K (X.residueField x) := Algebra.compHom (X.residueField x)
    ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
  rw [f.residueDegree_eq_finrank]
  let q := CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))
  have : IsLocalHom q.hom := inferInstanceAs
    (IsLocalHom (IsLocalRing.residue (X.presheaf.stalk x)))
  let e := X.descResidueField q
  have he : Function.Bijective e.hom := by
    refine ⟨e.hom.injective, fun a ↦ ?_⟩
    obtain ⟨t, ht⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk x) a
    refine ⟨X.residue x t, ?_⟩
    rw [← ht, ← CommRingCat.comp_apply, Scheme.residue_descResidueField]
    rfl
  have hc : X.Γevaluation x ≫ e = X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x) ≫ q := by
    exact (Category.assoc _ _ _).trans
      (congrArg (fun g ↦ X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x) ≫ g)
        (Scheme.residue_descResidueField q))
  refine (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl K)
    (RingEquiv.ofBijective e.hom he) ?_).symm
  ext c
  -- Unpack the transported algebra structures and the ring equivalence on the two residue fields.
  change algebraMap K (IsLocalRing.ResidueField (X.presheaf.stalk x)) c =
    e.hom ((X.Γevaluation x).hom (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom c))
  rw [← hf, IsScalarTower.algebraMap_apply K (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)), hx, RingHom.comp_apply]
  exact (congrArg (fun g : Γ(X, ⊤) ⟶ CommRingCat.of
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) ↦ g (algebraMap K Γ(X, ⊤) c)) hc).symm

/-- **Over a field, the rank is a sum of local lengths.** Let `f : X ⟶ Spec K` be finite.
Then the rank of `f` is the sum over the finitely many points `x` of `X` of the length
of the Artinian local ring `𝒪_{X,x}` times the residue degree `[κ(x) : K]`. -/
theorem Scheme.Hom.finrank_eq_finsum_residueDegree_mul_length {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] (s : Spec (.of K)) :
    f.finrank s = ∑ᶠ x : X,
      f.residueDegree x * (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat := by
  let : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop rfl
  have : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  have := Fintype.ofFinite (PrimeSpectrum Γ(X, ⊤))
  have hU := isAffineOpen_top X
  rw [f.finrank_eq_finrank_of_field rfl s, IsArtinianRing.finrank_eq_sum_primeSpectrum,
    ← finsum_eq_sum_of_fintype]
  -- The points of the affine scheme `X` are the primes of `Γ(X, ⊤)`.
  let e : X ≃ PrimeSpectrum Γ(X, ⊤) :=
    (Equiv.subtypeUnivEquiv (p := (· ∈ (⊤ : X.Opens))) fun _ ↦ trivial).symm.trans
      (Scheme.homeoOfIso hU.isoSpec).toEquiv
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun x ↦ ?_
  -- The local ring `𝒪_{X,x}` is the localization of `Γ(X, ⊤)` at the prime of `x`.
  let := X.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : X.Opens))
  have := hU.isLocalization_stalk ⟨x, trivial⟩
  let : Algebra K (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp (algebraMap K Γ(X, ⊤))).toAlgebra
  have : IsScalarTower K Γ(X, ⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let φ := IsLocalization.algEquiv (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, trivial⟩).asIdeal) (X.presheaf.stalk x)
  have h := TauCeti.finrank_eq_length_mul_finrank_residueField K
    (X.presheaf.stalk x) (X.presheaf.stalk x)
  have he : e x = hU.primeIdealOf ⟨x, trivial⟩ := rfl
  rw [mul_comm, he, (φ.restrictScalars K).toLinearEquiv.finrank_eq, h,
    finrank_residueField_stalk f x rfl rfl]

end AlgebraicGeometry
