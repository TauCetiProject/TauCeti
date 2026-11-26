/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.DegreewiseQuasiIso
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Tower
public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.Cohomology.SectionsHomology
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.WeakSerre
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Global sections of unbounded complexes with quasi-coherent cohomology

Let `X` be an affine scheme and `K` an unbounded complex of `𝒪_X`-modules all of whose cohomology
sheaves are quasi-coherent. This file shows that global sections of a K-injective replacement of
`K` compute the global sections of the cohomology sheaves of `K`: derived global sections
`RΓ(X, -)` commute with cohomology on such complexes
([Stacks, Section 36.3](https://stacks.math.columbia.edu/tag/06YZ)). Two consequences are
recorded, in the form used for the equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` of
[Stacks, Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0):

* `Scheme.Modules.quasiIso_map_sectionsFunctor_of_isKInjective`: if global sections already commute
  with the cohomology of `K` (for instance if the cycles and boundaries of `K` are quasi-coherent),
  then for every quasi-isomorphism `K ⟶ I` into a K-injective complex the induced map
  `Γ(X, K) ⟶ Γ(X, I)` is a quasi-isomorphism.
* `Scheme.Modules.exactAt_of_exactAt_map_sectionsFunctor`: a K-injective complex with
  quasi-coherent cohomology sheaves whose complex of global sections is exact in degree `m` is
  exact in degree `m`.

Nothing is assumed about the boundedness of `K`, and the cohomological dimension of `X` may be
infinite, so the bounded below argument does not apply directly. The proof follows the Stacks
project. The canonical truncations `τ^{≥ -n} K` are bounded below, and their injective resolutions
`Iₙ` can be chosen to form a tower of degreewise split epimorphisms
(`CochainComplex.truncGETower`); the limit `L` of this tower is K-injective. On every affine
open `U`, global sections commute with the cohomology of the bounded below complexes `Iₙ`, since
their terms and their cohomology sheaves have no higher cohomology on `U`
(`Scheme.Modules.preservesLeftHomologyOf_sectionsFunctor_sc`). As the cohomology of the `Iₙ` in a
fixed degree stabilizes, the Milnor sequence of the tower `Γ(U, Iₙ)` shows that `Γ(U, L) ⟶ Γ(U, Iₙ)`
is an isomorphism on cohomology in a fixed degree once `n` is large. Since the affine opens form a
basis of the topology, `L ⟶ Iₙ` is then an isomorphism on cohomology sheaves in that degree, so
`K ⟶ L` is a quasi-isomorphism, and `L` is a K-injective replacement of `K` whose global sections
are understood.

## References

* [Stacks: Section 36.3](https://stacks.math.columbia.edu/tag/06YZ), whose proof of
  Lemma 36.3.5 (tag 06Z0) uses derived limits of canonical truncations in the same way.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry CochainComplex HomologicalComplex

universe u

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

section Tower

/-- The hypotheses on a tower of complexes of `𝒪_X`-modules under which global sections behave well
in the limit: each complex is bounded below with injective terms and quasi-coherent cohomology
sheaves, and the transitions are degreewise split epimorphisms. -/
private structure GoodTower {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ) : Prop where
  isStrictlyGE (k : ℕ) : ∃ a : ℤ, (D.obj (op k)).IsStrictlyGE a
  injective (k : ℕ) (i : ℤ) : Injective ((D.obj (op k)).X i)
  isQuasicoherent (k : ℕ) (i : ℤ) : ((D.obj (op k)).homology i).IsQuasicoherent
  isSplitEpi (k : ℕ) (i : ℤ) : IsSplitEpi ((D.map (homOfLE (Nat.le_succ k)).op).f i)

/-- Over an affine scheme, global sections commute with the cohomology of the terms of a good
tower. -/
private lemma GoodTower.preservesLeftHomologyOf {X : Scheme.{u}} [IsAffine X]
    {D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ} (hD : GoodTower D) (k : ℕ) (j : ℤ) :
    (Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).PreservesLeftHomologyOf
      ((D.obj (op k)).sc j) := by
  obtain ⟨a, _⟩ := hD.isStrictlyGE k
  exact preservesLeftHomologyOf_sectionsFunctor_sc _ a
    (fun i p ↦ have := hD.injective k i
      Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque _ p)
    (fun i p ↦ have := hD.isQuasicoherent k i
      Scheme.Modules.subsingleton_cohomology_succ_of_isAffine _ p) j

/-- The tower of complexes of global sections of a tower of complexes of `𝒪_X`-modules. -/
private abbrev sectionsTower {X : Scheme.{u}} (D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ) :
    ComplexTower Γ(X, ⊤) (ComplexShape.up ℤ) :=
  D ⋙ (Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _

/-- The global sections of a limit of a tower of complexes are the limit complex of the tower of
global sections. -/
private lemma GoodTower.exists_iso {X : Scheme.{u}} {D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ}
    {c : Cone D} (hc : IsLimit c) :
    ∃ e : ((Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _).obj c.pt ≅
      ComplexTower.limComplex (sectionsTower D),
      ∀ n : ℕ, e.hom ≫ ComplexTower.limComplexπ _ n =
        ((Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _).map
          (c.π.app (op n)) := by
  let G := Scheme.Modules.sectionsFunctor (⊤ : X.Opens)
  have : PreservesLimitsOfSize.{0, 0} G := preservesLimitsOfSize_shrink.{0, u, 0, u} G
  let E : ComplexTower Γ(X, ⊤) (ComplexShape.up ℤ) := D ⋙ G.mapHomologicalComplex _
  exact ⟨(isLimitOfPreserves (G.mapHomologicalComplex _) hc).conePointUniqueUpToIso
    E.isLimitLimComplexCone, fun n ↦
      (isLimitOfPreserves (G.mapHomologicalComplex _) hc).conePointUniqueUpToIso_hom_comp
        E.isLimitLimComplexCone (op n)⟩

/-- The transitions of the tower of global sections of a good tower are surjective. -/
private lemma GoodTower.surjective_transition {X : Scheme.{u}}
    {D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ} (hD : GoodTower D) (i : ℤ) (k : ℕ) :
    Function.Surjective ((ComplexTower.term (sectionsTower D) i).transition k) := by
  have := hD.isSplitEpi k i
  rw [ModuleTower.transition_def]
  -- a section of the transition gives a section on global sections
  refine fun y ↦ ⟨(section_ ((D.map (homOfLE (Nat.le_succ k)).op).f i)).app ⊤ y, ?_⟩
  -- the transition of the tower of global sections is the component over `⊤` of the transition
  change ((section_ _ ≫ (D.map (homOfLE (Nat.le_succ k)).op).f i).app ⊤) y = y
  rw [IsSplitEpi.id]
  rfl

/-- The projections of a limit of a good tower are surjective on global sections. -/
private lemma GoodTower.surjective_π_app {X : Scheme.{u}} {D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ}
    (hD : GoodTower D) {c : Cone D} (hc : IsLimit c) (n : ℕ) (i : ℤ) :
    Function.Surjective (((c.π.app (op n)).f i).app ⊤) := by
  let G := Scheme.Modules.sectionsFunctor (⊤ : X.Opens)
  obtain ⟨e, he⟩ := GoodTower.exists_iso hc
  have h : (G.map ((c.π.app (op n)).f i)).hom =
      ((ComplexTower.limComplexπ _ n).f i).hom ∘ₗ (e.hom.f i).hom := by
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, he]
    rfl
  -- the component over `⊤` is the image of the morphism under the sections functor
  change Function.Surjective (G.map ((c.π.app (op n)).f i)).hom
  rw [h, LinearMap.coe_comp, ComplexTower.limComplexπ_f_hom]
  exact (ModuleTower.limπ_surjective _ (hD.surjective_transition i) n).comp
    ((ModuleCat.epi_iff_surjective (e.hom.f i)).1 inferInstance)

/-- **Global sections of the limit of a good tower.** Over an affine scheme, if from the index `N`
on the transitions of a good tower are isomorphisms on cohomology in degrees `j - 1` and `j`, then
for `n ≥ N` the projection from a limit of the tower to its `n`-th term is an isomorphism on the
degree-`j` cohomology of global sections. -/
private lemma GoodTower.quasiIsoAt_map_π {X : Scheme.{u}} [IsAffine X]
    {D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ} (hD : GoodTower D) {c : Cone D} (hc : IsLimit c)
    (j : ℤ) (N : ℕ) (h : ∀ k, N ≤ k → ∀ i, j - 1 ≤ i → i ≤ j →
      QuasiIsoAt (D.map (homOfLE (Nat.le_succ k)).op) i) {n : ℕ} (hn : N ≤ n) :
    QuasiIsoAt (((Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _).map
      (c.π.app (op n))) j := by
  let G := Scheme.Modules.sectionsFunctor (⊤ : X.Opens)
  let E : ComplexTower Γ(X, ⊤) (ComplexShape.up ℤ) := D ⋙ G.mapHomologicalComplex _
  have := hD.preservesLeftHomologyOf
  obtain ⟨e, he⟩ := GoodTower.exists_iso hc
  have hE (i : ℤ) (hi₁ : j - 1 ≤ i) (hi₂ : i ≤ j) (k : ℕ) (hk : N ≤ k) :
      QuasiIsoAt (E.map (homOfLE (Nat.le_succ k)).op) i :=
    have := h k hk i hi₁ hi₂
    HomologicalComplex.quasiIsoAt_map_of_preservesLeftHomologyOf G _ i
  have := E.quasiIsoAt_limComplexπ
    (fun i ↦ (E.term i).shift_surjective (hD.surjective_transition i))
    j N (hE j (by lia) le_rfl) (fun i hij k hk ↦ by
      obtain rfl : i = j - 1 := by simp at hij; lia
      exact hE (j - 1) le_rfl (by lia) k hk) hn
  rw [← he]
  infer_instance

/-- Restriction along an open immersion preserves good towers. -/
private lemma GoodTower.restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {D : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ} (hD : GoodTower D) :
    GoodTower (D ⋙ (Scheme.Modules.restrictFunctor f).mapHomologicalComplex _) where
  isStrictlyGE k := by
    obtain ⟨a, _⟩ := hD.isStrictlyGE k
    exact ⟨a, (isStrictlyGE_iff _ a).2 fun i hi ↦
      (Scheme.Modules.restrictFunctor f).map_isZero ((D.obj (op k)).isZero_of_isStrictlyGE a i hi)⟩
  injective k i :=
    have := hD.injective k i
    (Scheme.Modules.restrictFunctor f).injective_obj _
  isQuasicoherent k i :=
    have := hD.isQuasicoherent k i
    (Scheme.Modules.isQuasicoherent Y).prop_of_iso
      (((D.obj (op k)).sc i).mapHomologyIso (Scheme.Modules.restrictFunctor f)).symm
      (@_root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor _ _ f _ _ this)
  isSplitEpi k i :=
    have := hD.isSplitEpi k i
    inferInstanceAs (IsSplitEpi ((Scheme.Modules.restrictFunctor f).map _))

end Tower

section Truncation

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}

/-- If the cohomology sheaves of `K` are quasi-coherent, then the tower of resolutions of the
truncations of `K` is good. -/
private lemma goodTower_truncGETower (hK : ∀ i, (K.homology i).IsQuasicoherent) :
    GoodTower (truncGETower K) where
  isStrictlyGE k := ⟨-k - 1, inferInstanceAs ((towerResolution _ _ k).IsStrictlyGE (-k - 1))⟩
  injective k i := inferInstanceAs (Injective ((towerResolution _ _ k).X i))
  isQuasicoherent k i := by
    have hι := (quasiIsoAt_iff_isIso_homologyMap _ _).1 (QuasiIso.quasiIsoAt
      (f := towerResolutionι (fun n ↦ K.truncGE (-(n : ℤ)))
        (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) k) i)
    refine (Scheme.Modules.isQuasicoherent X).prop_of_iso (@asIso _ _ _ _ _ hι) ?_
    by_cases hi : -(k : ℤ) ≤ i
    · have hπ := (quasiIsoAt_iff_isIso_homologyMap _ _).1 (K.quasiIsoAt_πTruncGE _ i hi)
      exact (Scheme.Modules.isQuasicoherent X).prop_of_iso (@asIso _ _ _ _ _ hπ) (hK i)
    · have : (K.truncGE (-(k : ℤ))).ExactAt i := (K.truncGE _).exactAt_of_isGE (-(k : ℤ)) i
      exact (Scheme.Modules.isQuasicoherent X).prop_of_isZero this.isZero_homology
  isSplitEpi := K.isSplitEpi_truncGETower_map_f

end Truncation

section Limit

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
  (hK : ∀ i, (K.homology i).IsQuasicoherent)

include hK in
/-- For `n` large compared with `-j`, the projection from the limit of the tower of resolutions of
the truncations of `K` is an isomorphism on degree-`j` cohomology of global sections over an
affine scheme. -/
private lemma quasiIsoAt_map_limitπ [IsAffine X] (j : ℤ) {n : ℕ} (hn : (1 - j).toNat ≤ n) :
    QuasiIsoAt (((Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _).map
      (limit.π (truncGETower K) (op n))) j :=
  (goodTower_truncGETower hK).quasiIsoAt_map_π (limit.isLimit _) j _
    (fun k hk i hi _ ↦ K.quasiIsoAt_truncGETower_map k i (by lia)) hn

include hK in
/-- For `n` large compared with `-j`, the projection from the limit of the tower of resolutions of
the truncations of `K` to its `n`-th term is an isomorphism on degree-`j` cohomology sheaves. -/
private lemma quasiIsoAt_limitπ (j : ℤ) {n : ℕ} (hn : (2 - j).toNat ≤ n) :
    QuasiIsoAt (limit.π (truncGETower K) (op n)) j := by
  have hD := goodTower_truncGETower hK
  -- on each affine open, the restricted tower is good, and its projections are isomorphisms on the
  -- cohomology of global sections in degrees `≥ j - 1`
  let R (U : X.Opens) := (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)
  have hc (U : X.Opens) := isLimitOfPreserves (R U) (limit.isLimit (truncGETower K))
  have hq (U : X.Opens) (hU : IsAffineOpen U) (i : ℤ) (hi : j - 1 ≤ i) :
      QuasiIsoAt (((Scheme.Modules.sectionsFunctor (⊤ : U.toScheme.Opens)).mapHomologicalComplex
        _).map ((R U).map (limit.π (truncGETower K) (op n)))) i :=
    have : IsAffine U := hU
    (hD.restrict U.ι).quasiIsoAt_map_π (hc U) i (2 - j).toNat (fun k hk i' hi' _ ↦ by
      rw [Functor.comp_map]
      exact HomologicalComplex.quasiIsoAt_map_of_preservesHomology _
        (Scheme.Modules.restrictFunctor U.ι) i' (hφ := K.quasiIsoAt_truncGETower_map k i' (by lia)))
      hn
  -- the projection is an epimorphism, surjective on sections over every affine open
  have : Epi (limit.π (truncGETower K) (op n)) := HomologicalComplex.epi_of_epi_f _ fun i ↦
    Scheme.Modules.Hom.epi_of_surjective_on_affineOpens _ fun U _ ↦ by
      have := (hD.restrict U.ι).surjective_π_app (hc U) n i
      -- the sections of a restriction over `⊤` are the sections over the image of `⊤`
      change Function.Surjective (((limit.π (truncGETower K) (op n)).f i).app (U.ι ''ᵁ ⊤)) at this
      rwa [Scheme.Opens.ι_image_top] at this
  -- its kernel `F` is exact in degrees `≥ j`, because it is so on global sections over every
  -- affine open
  let S := ShortComplex.mk _ _ (kernel.condition (limit.π (truncGETower K) (op n)))
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hF (i : ℤ) (hi : j ≤ i) : S.X₁.ExactAt i := exactAt_of_forall_isAffineOpen _ i fun U hU ↦ by
    have : IsAffine U := hU
    have hSU := HomologicalComplex.shortExact_of_degreewise_shortExact
      ((S.map (R U)).map ((Scheme.Modules.sectionsFunctor ⊤).mapHomologicalComplex _)) fun i' ↦
      shortExact_map_sectionsFunctor
        (((hS.map_of_exact (R U)).map_of_exact (HomologicalComplex.eval _ _ i')))
        ((hD.restrict U.ι).surjective_π_app (hc U) n i')
    exact hSU.exactAt_X₁ i
      (@IsIso.mono_of_iso _ _ _ _ _ ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq U hU i (by lia))))
      fun i' hi' ↦ by
        obtain rfl : i' = i - 1 := by simp at hi'; lia
        exact @IsIso.epi_of_iso _ _ _ _ _
          ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq U hU (i - 1) (by lia)))
  exact hS.quasiIsoAt_g j (hF j le_rfl) fun i hi ↦ hF i (by simp at hi; lia)

end Limit

section Main

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}

variable (K) in
/-- The map from `K` to the limit of the tower of resolutions of its truncations. -/
private def toLimit : K ⟶ limit (truncGETower K) :=
  limit.lift _ K.truncGETowerCone

@[reassoc]
private lemma toLimit_π (n : ℕ) :
    toLimit K ≫ limit.π (truncGETower K) (op n) = K.truncGETowerι n :=
  limit.lift_π K.truncGETowerCone (op n)

/-- The limit of the tower of resolutions of the truncations of `K` is K-injective. -/
private instance : (limit (truncGETower K)).IsKInjective :=
  (isKInjective_of_isLimit_towerResolution _ _ (limit.isLimit _)).2

/-- If the cohomology sheaves of `K` are quasi-coherent, then the limit of the tower of resolutions
of its truncations is a K-injective replacement of `K`. -/
private lemma quasiIso_toLimit (hK : ∀ i, (K.homology i).IsQuasicoherent) :
    QuasiIso (toLimit K) := by
  rw [quasiIso_iff]
  intro j
  have := quasiIsoAt_limitπ hK j (n := max (2 - j).toNat (-j).toNat) (le_max_left _ _)
  have := K.quasiIsoAt_truncGETowerι (max (2 - j).toNat (-j).toNat) j (by lia)
  exact quasiIsoAt_of_comp_right _ (limit.π (truncGETower K) (op (max (2 - j).toNat (-j).toNat))) j
    (hφφ' := by rw [toLimit_π]; infer_instance)

/-- **Global sections of K-injective replacements.** Let `X` be an affine scheme and `K` a complex
of `𝒪_X`-modules with quasi-coherent cohomology sheaves, such that global sections commute with
the cohomology of `K` (for instance because the cycles and boundaries of `K` are quasi-coherent).
Then for every quasi-isomorphism `f : K ⟶ I` into a K-injective complex, the map
`Γ(X, K) ⟶ Γ(X, I)` is a quasi-isomorphism: global sections of `K` compute `RΓ(X, K)`. -/
theorem quasiIso_map_sectionsFunctor_of_isKInjective [IsAffine X]
    (hK : ∀ i, (K.homology i).IsQuasicoherent)
    (hG : ∀ j, (Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).PreservesLeftHomologyOf (K.sc j))
    {I : CochainComplex X.Modules ℤ} [I.IsKInjective] (f : K ⟶ I) [QuasiIso f] :
    QuasiIso (((Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _).map f) := by
  let G := Scheme.Modules.sectionsFunctor (⊤ : X.Opens)
  have := quasiIso_toLimit hK
  obtain ⟨e, ⟨h⟩⟩ := CochainComplex.IsKInjective.exists_homotopyEquiv (toLimit K) f
  -- the map induced by `K ⟶ L` on global sections is a quasi-isomorphism: compose with the
  -- projections `L ⟶ Iₙ`, which are quasi-isomorphisms on global sections in a fixed degree
  have hψ : QuasiIso ((G.mapHomologicalComplex _).map (toLimit K)) := by
    rw [quasiIso_iff]
    intro j
    let n := max (1 - j).toNat (-j).toNat
    have := hG j
    have := (goodTower_truncGETower hK).preservesLeftHomologyOf n j
    have h₁ : QuasiIsoAt ((G.mapHomologicalComplex _).map (K.truncGETowerι n)) j :=
      have := K.quasiIsoAt_truncGETowerι n j (by lia)
      HomologicalComplex.quasiIsoAt_map_of_preservesLeftHomologyOf G _ j
    have := quasiIsoAt_map_limitπ hK j (n := n) (le_max_left _ _)
    exact quasiIsoAt_of_comp_right _ ((G.mapHomologicalComplex _).map (limit.π _ (op n))) j
      (hφφ' := by rw [← Functor.map_comp, toLimit_π]; exact h₁)
  have : QuasiIso ((G.mapHomologicalComplex _).map e.hom) := (G.mapHomotopyEquiv e).quasiIso_hom
  have : QuasiIso ((G.mapHomologicalComplex _).map (toLimit K ≫ e.hom)) := by
    rw [Functor.map_comp]
    infer_instance
  -- `Γ(f)` is homotopic to `Γ(K ⟶ L) ≫ Γ(e)`, so it induces the same maps on homology
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, (G.mapHomotopy h).symm.homologyMap_eq]
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance

/-- **Exactness is detected by global sections of K-injective complexes.** Let `X` be an affine
scheme and `K` a K-injective complex of `𝒪_X`-modules with quasi-coherent cohomology sheaves. If
the complex of global sections `Γ(X, K)`, which computes `RΓ(X, K)`, is exact in degree `m`, then
so is `K`. -/
theorem exactAt_of_exactAt_map_sectionsFunctor [IsAffine X] [K.IsKInjective]
    (hK : ∀ i, (K.homology i).IsQuasicoherent) (m : ℤ)
    (h : (((Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).mapHomologicalComplex _).obj
      K).ExactAt m) :
    K.ExactAt m := by
  let G := Scheme.Modules.sectionsFunctor (⊤ : X.Opens)
  have := quasiIso_toLimit hK
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (toLimit K)).1 inferInstance
  have : QuasiIso ((G.mapHomologicalComplex _).map (toLimit K)) := by
    rw [← he]
    exact (G.mapHomotopyEquiv e).quasiIso_hom
  let n := max (1 - m).toNat (-m).toNat
  have := quasiIsoAt_map_limitπ hK m (n := n) (le_max_left _ _)
  -- the global sections of `Iₙ` are exact in degree `m`, hence so are the global sections of the
  -- cohomology sheaf `Hᵐ(Iₙ)`, which therefore vanishes
  have : QuasiIsoAt ((G.mapHomologicalComplex _).map (toLimit K) ≫
      (G.mapHomologicalComplex _).map (limit.π (truncGETower K) (op n))) m := inferInstance
  have hI : ((G.mapHomologicalComplex _).obj ((truncGETower K).obj (op n))).ExactAt m :=
    (exactAt_iff_of_quasiIsoAt (((G.mapHomologicalComplex _).map (toLimit K) ≫
      (G.mapHomologicalComplex _).map (limit.π (truncGETower K) (op n)))) m).1 h
  have := (goodTower_truncGETower hK).preservesLeftHomologyOf n m
  have := (goodTower_truncGETower hK).isQuasicoherent n m
  have : Subsingleton Γ(((truncGETower K).obj (op n)).homology m, ⊤) :=
    ModuleCat.isZero_iff_subsingleton.1
      (hI.isZero_homology.of_iso ((((truncGETower K).obj (op n)).sc m).mapHomologyIso G).symm)
  have := K.quasiIsoAt_truncGETowerι n m (by lia)
  exact (exactAt_iff_of_quasiIsoAt (K.truncGETowerι n) m).2
    ((exactAt_iff_isZero_homology _ _).2
      (_root_.AlgebraicGeometry.Scheme.Modules.isZero_of_subsingleton_sections_top _))

end Main

end TauCeti.AlgebraicGeometry.Scheme.Modules
