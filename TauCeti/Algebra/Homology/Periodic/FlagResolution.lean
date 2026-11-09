/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.Periodic.GlobalDimension
public import TauCeti.Algebra.Homology.Periodic.ProjectiveFlag
public import TauCeti.CategoryTheory.Triangulated.VerdierLocalization

/-!
# Projective flag resolutions of periodic complexes

Let `C` be an abelian category with enough projectives. If the homology objects of a periodic
complex `K` all have projective dimension `< d`, then `K` receives a quasi-isomorphism from a
complex with a projective flag (`TauCeti.PeriodicComplex.exists_hasProjectiveFlag_quasiIso`).
This is the periodic form of the free flag resolutions of Avramov, Buchweitz and Iyengar.

Consequently, under the same bound, a periodic complex is homotopically projective exactly when
it is homotopy equivalent to a complex with a projective flag
(`TauCeti.PeriodicComplex.isHomotopicallyProjective_iff_exists_hasProjectiveFlag`). If every
object of `C` has projective dimension `< d`, this is also equivalent to being homotopy
equivalent to a complex with projective terms
(`TauCeti.PeriodicComplex.isHomotopicallyProjective_iff_exists_projective`). Thus in finite
global dimension the three classes of homotopically projective complexes, complexes with a
projective flag, and complexes with projective terms agree up to homotopy equivalence. Stai calls
complexes with projective terms relatively projective; this differs from the componentwise split
notion of relative projectivity used elsewhere in this library. Without the bound, a complex
with projective terms need not be homotopically projective
(`TauCeti.not_isHomotopicallyProjective_dualNumberPeriodicComplex`).

No positivity of the period is needed; at period zero, when `ZMod 0` is integer indexing, these
are resolutions of unbounded complexes with bounded homological dimension.

## Main results

* `TauCeti.PeriodicComplex.hasProjectiveDimensionLT_homology_homotopyCofiber`: killing homology
  with a complex of projectives lowers the projective dimension of the homology by one.
* `TauCeti.PeriodicComplex.exists_hasProjectiveFlag_quasiIso`: every periodic complex whose
  homology has projective dimension `< d` receives a quasi-isomorphism from a complex with a
  projective flag.
* `TauCeti.PeriodicComplex.isHomotopicallyProjective_iff_exists_hasProjectiveFlag`: under that
  bound, homotopically projective complexes are those homotopy equivalent to complexes with a
  projective flag.
* `TauCeti.PeriodicComplex.isHomotopicallyProjective_iff_exists_projective`: in finite global
  dimension, homotopically projective complexes are those homotopy equivalent to complexes with
  projective terms.

## Implementation notes

The resolution is built by killing homology. Projective objects mapping onto the cycles of
`X` form a complex `P` with zero differential and a map `g : P ⟶ X` surjective on homology. The
homology of the cone of `g` sits in short exact sequences
`0 ⟶ Hⁱ(cone g) ⟶ Pⁱ⁺¹ ⟶ Hⁱ⁺¹(X) ⟶ 0`, so its projective dimension is one less. Resolving the
cone by induction and attaching `P` along the connecting map gives an extension, in the periodic
homotopy category, of the resolution of the cone by `P`; when the homology of `X` is projective,
`g` can be chosen to be a quasi-isomorphism. Mathlib's associativity of
`ObjectProperty.extensionProduct`, which rests on the octahedral axiom, reorders these iterated
extensions into a projective flag.

## References

* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of differential
  modules*, Inventiones Mathematicae **169** (2007), 1–35, Section 2.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3, Proposition 3.10.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}

/-- The objects of the periodic homotopy category represented by complexes with projective terms
and zero differential. -/
private def projectiveZeroDifferential :
    ObjectProperty (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  fun Y ↦ ∃ P : CochainComplex C (ZMod n), (∀ i, Projective (P.X i)) ∧ (∀ i j, P.d i j = 0) ∧
    Nonempty (Y ≅ (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj P)

/-- If `g : P ⟶ X` from a complex with projective terms and zero differential is surjective on
homology, then the homology of its cone has projective dimension one less than that of `X`:
it is the kernel of `Pⁱ⁺¹ ⟶ Hⁱ⁺¹(X)`. -/
lemma hasProjectiveDimensionLT_homology_homotopyCofiber {P X : CochainComplex C (ZMod n)}
    (g : P ⟶ X) [∀ i, Projective (P.X i)] (hP : ∀ i j, P.d i j = 0)
    (hg : ∀ i, Epi (homologyMap g i)) (k : ℕ) (i : ZMod n)
    (hX : HasProjectiveDimensionLT (X.homology (i + 1)) (k + 2)) :
    HasProjectiveDimensionLT ((homotopyCofiber g).homology i) (k + 1) := by
  let S := coneSequence g
  have hS : S.ShortExact :=
    shortExact_of_degreewise_shortExact S fun j ↦ (coneSequenceSplitting g j).shortExact
  -- The cone inclusion kills homology, since `g ≫ inr g` is null-homotopic and `g` is
  -- surjective on homology.
  have hf (j : ZMod n) : homologyMap S.f j = 0 := by
    rw [← cancel_epi (homologyMap g j), comp_zero, coneSequence_f, ← homologyMap_comp,
      (homotopyCofiber.inrCompHomotopy g fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩).homologyMap_eq,
      homologyMap_zero]
  have hses : (ShortComplex.mk _ _ (hS.comp_δ i (i + 1) rfl)).ShortExact :=
    { exact := hS.homology_exact₃ i (i + 1) rfl
      mono_f := (hS.homology_exact₂ i).mono_g (hf i)
      epi_g := (hS.homology_exact₁ i (i + 1) rfl).epi_f (hf (i + 1)) }
  -- The middle term is the homology of `P⟦1⟧`, which has zero differential.
  have : Projective (S.X₃.X i) := inferInstanceAs (Projective (P.X _))
  have hd := shiftFunctor_obj_d_eq_zero hP 1
  have : Projective (S.X₃.homology i) := S.X₃.projective_homology_of_d_eq_zero i (hd _ _) (hd _ _)
  exact hses.hasProjectiveDimensionLT_X₁ (k + 1)
    (hasProjectiveDimensionLT_of_ge _ 1 (k + 1) (by lia)) hX

variable [EnoughProjectives C]

/-- The induction killing homology: a periodic complex whose homology has projective dimension
`< k + 1` receives a map, inverted in the periodic derived category, from a `k`-fold iterated
extension of complexes with projective terms and zero differential. -/
private lemma exists_extensionProductIter_isIso_Qh_map (k : ℕ) :
    ∀ X : CochainComplex C (ZMod n), (∀ i, HasProjectiveDimensionLT (X.homology i) (k + 1)) →
      ∃ (Y : HomotopyCategory C (ComplexShape.up (ZMod n)))
        (φ : Y ⟶ (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj X),
        (projectiveZeroDifferential (C := C) (n := n)).extensionProductIter k Y ∧
          IsIso ((DerivedCategory.Qh C n).map φ) := by
  induction k with
  | zero =>
    intro X hX
    -- A section of each `X.cycles i ⟶ X.homology i` gives a quasi-isomorphism from the
    -- homology of `X`, with zero differential.
    have (i : ZMod n) : Projective (X.homology i) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr (hX i)
    let e (i : ZMod n) : X.homology i ⟶ X.cycles i := Projective.factorThru (𝟙 _) (X.homologyπ i)
    have := X.quasiIso_fromGraded e fun i ↦ by
      rw [Projective.factorThru_comp]
      infer_instance
    refine ⟨_, (HomotopyCategory.quotient C _).map (X.fromGraded e),
      ⟨graded _ fun i ↦ X.homology i, fun i ↦ inferInstanceAs (Projective (X.homology i)),
        fun _ _ ↦ rfl, ⟨Iso.refl _⟩⟩, ?_⟩
    have : IsIso ((DerivedCategory.Q C n).map (X.fromGraded e)) := inferInstance
    rwa [← DerivedCategory.quotient_comp_Qh, Functor.comp_map] at this
  | succ k ih =>
    intro X hX
    -- Cover the cycles of `X` by projectives and pass to the cone of the resulting map
    -- `g : P ⟶ X`, whose homology has smaller projective dimension.
    let g := X.fromGraded (E := fun i ↦ Projective.over (X.cycles i)) fun i ↦ Projective.π _
    have : ∀ i, Projective ((graded (ComplexShape.up (ZMod n))
        fun i ↦ Projective.over (X.cycles i)).X i) :=
      fun i ↦ inferInstanceAs (Projective (Projective.over _))
    obtain ⟨Y, ψ, hY, hψ⟩ := ih (homotopyCofiber g) fun i ↦
      hasProjectiveDimensionLT_homology_homotopyCofiber g (fun _ _ ↦ rfl)
        (fun i ↦ X.epi_homologyMap_fromGraded _ i) k i (hX (i + 1))
    -- Attach `P` to the resolution `ψ : Y ⟶ cone g` along the connecting map `cone g ⟶ P⟦1⟧`,
    -- and compare the resulting triangle with the cone triangle of `g`.
    let T := mappingConeTriangle g
    obtain ⟨W, a, b, hW⟩ := distinguished_cocone_triangle₂ (ψ ≫ T.mor₃)
    obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism₂ _ T hW
      (mappingCone_mem_distTriang g) (𝟙 _) ψ (by simp)
    refine ⟨W, c, ?_, ?_⟩
    · rw [ObjectProperty.extensionProductIter_succ]
      exact ⟨_, _, a, b, _, hW, ⟨_, ‹_›, fun _ _ ↦ rfl, ⟨Iso.refl _⟩⟩, hY⟩
    · let φ : Triangle.mk a b (ψ ≫ T.mor₃) ⟶ T := Triangle.homMk _ _ (𝟙 _) c ψ hc₁ hc₂ (by simp)
      exact isIso₂_of_isIso₁₃ ((DerivedCategory.Qh C n).mapTriangle.map φ)
        ((DerivedCategory.Qh C n).map_distinguished _ hW)
        ((DerivedCategory.Qh C n).map_distinguished _ (mappingCone_mem_distTriang g))
        (by simp only [φ, Functor.mapTriangle_map_hom₁, Triangle.homMk_hom₁]; infer_instance) hψ

omit [EnoughProjectives C] in
/-- An iterated extension of complexes with projective terms and zero differential is
represented by a complex with a projective flag. -/
private lemma exists_hasProjectiveFlag_of_extensionProductIter (m : ℕ) :
    ∀ {Y : HomotopyCategory C (ComplexShape.up (ZMod n))},
      (projectiveZeroDifferential (C := C) (n := n)).extensionProductIter m Y →
        ∃ F : CochainComplex C (ZMod n), HasProjectiveFlag F ∧
          Nonempty (Y ≅ (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj F) := by
  induction m with
  | zero =>
    rintro Y ⟨P, hP, hd, ⟨e⟩⟩
    have := hP
    exact ⟨P, .of_d_eq_zero hd, ⟨e⟩⟩
  | succ m ih =>
    intro Y hY
    rw [ObjectProperty.extensionProductIter_succ'] at hY
    obtain ⟨Y₁, Z, f, g, h, hT, h₁, P, hP, hd, ⟨eZ⟩⟩ := hY
    obtain ⟨F₁, hF₁, ⟨e₁⟩⟩ := ih h₁
    -- Rotating `Y₁ ⟶ Y ⟶ Z ⟶ Y₁⟦1⟧` backwards exhibits `Y` as the cone of a map
    -- `Z⟦-1⟧ ⟶ Y₁`, which is represented by a chain map `u : P⟦-1⟧ ⟶ F₁`.
    let T := (Triangle.mk f g h).invRotate
    let e₀ : T.obj₁ ≅ (HomotopyCategory.quotient C _).obj (P⟦(-1 : ℤ)⟧) :=
      (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso eZ ≪≫
        ((HomotopyCategory.quotient C _).commShiftIso (-1 : ℤ)).symm.app P
    obtain ⟨u, hu⟩ := (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map_surjective
      (e₀.inv ≫ T.mor₁ ≫ e₁.hom)
    have : ∀ i, Projective ((P⟦(-1 : ℤ)⟧).X i) := fun i ↦ hP _
    exact ⟨homotopyCofiber u, hF₁.homotopyCofiber u (shiftFunctor_obj_d_eq_zero hd (-1)),
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T (mappingConeTriangle u)
        (inv_rot_of_distTriang _ hT) (mappingCone_mem_distTriang u) e₀ e₁
        (by rw [mappingConeTriangle_mor₁, hu, Iso.hom_inv_id_assoc]))⟩⟩

/-- **Projective flag resolutions.** In an abelian category with enough projectives, every
periodic complex whose homology objects have projective dimension `< d` receives a
quasi-isomorphism from a complex with a projective flag. -/
theorem exists_hasProjectiveFlag_quasiIso (d : ℕ) (K : CochainComplex C (ZMod n))
    (hK : ∀ i, HasProjectiveDimensionLT (K.homology i) d) :
    ∃ (F : CochainComplex C (ZMod n)) (f : F ⟶ K), HasProjectiveFlag F ∧ QuasiIso f := by
  obtain ⟨Y, φ, hY, hφ⟩ := exists_extensionProductIter_isIso_Qh_map d K fun i ↦
    have := hK i
    hasProjectiveDimensionLT_of_ge _ d (d + 1) (by lia)
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_hasProjectiveFlag_of_extensionProductIter d hY
  obtain ⟨f, hf⟩ :=
    (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map_surjective (e.inv ≫ φ)
  refine ⟨F, f, hF, ?_⟩
  -- The cone of `f` becomes zero in the periodic derived category, so it is acyclic.
  have hT := (DerivedCategory.Qh C n).map_distinguished _ (mappingCone_mem_distTriang f)
  have : IsIso ((DerivedCategory.Qh C n).mapTriangle.obj (mappingConeTriangle f)).mor₁ := by
    dsimp
    rw [hf, Functor.map_comp]
    infer_instance
  rw [quasiIso_iff_acyclic_homotopyCofiber, ← quotient_obj_mem_subcategoryAcyclic_iff,
    ← ObjectProperty.TrWLocalization.isZero_obj_iff (subcategoryAcyclic C n)
      (DerivedCategory.Qh C n)]
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).mpr this

/-- **Homotopically projective complexes have projective flags.** In an abelian category with
enough projectives, a periodic complex whose homology objects have projective dimension `< d`
is homotopically projective if and only if it is homotopy equivalent to a complex with a
projective flag. -/
theorem isHomotopicallyProjective_iff_exists_hasProjectiveFlag (d : ℕ)
    (K : CochainComplex C (ZMod n)) (hK : ∀ i, HasProjectiveDimensionLT (K.homology i) d) :
    IsHomotopicallyProjective K ↔
      ∃ F : CochainComplex C (ZMod n), HasProjectiveFlag F ∧ Nonempty (HomotopyEquiv K F) := by
  refine ⟨fun _ ↦ ?_, fun ⟨F, hF, ⟨e⟩⟩ ↦
    e.isHomotopicallyProjective_iff.mpr hF.isHomotopicallyProjective⟩
  obtain ⟨F, f, hF, hf⟩ := exists_hasProjectiveFlag_quasiIso d K hK
  have := hF.isHomotopicallyProjective
  obtain ⟨e, -⟩ := (IsHomotopicallyProjective.quasiIso_iff f).mp hf
  exact ⟨F, hF, ⟨e.symm⟩⟩

/-- **Homotopically projective complexes in finite global dimension.** In an abelian category
with enough projectives in which every object has projective dimension `< d`, a periodic complex
is homotopically projective if and only if it is homotopy equivalent to a complex with projective
terms. -/
theorem isHomotopicallyProjective_iff_exists_projective (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) (K : CochainComplex C (ZMod n)) :
    IsHomotopicallyProjective K ↔
      ∃ F : CochainComplex C (ZMod n), (∀ i, Projective (F.X i)) ∧
        Nonempty (HomotopyEquiv K F) := by
  refine ⟨fun hK ↦ ?_, fun ⟨F, hF, ⟨e⟩⟩ ↦
    e.isHomotopicallyProjective_iff.mpr (isHomotopicallyProjective_of_projective d hd F)⟩
  obtain ⟨F, hF, he⟩ :=
    (isHomotopicallyProjective_iff_exists_hasProjectiveFlag d K fun _ ↦ hd _).mp hK
  exact ⟨F, hF.projective_X, he⟩

end TauCeti.PeriodicComplex
