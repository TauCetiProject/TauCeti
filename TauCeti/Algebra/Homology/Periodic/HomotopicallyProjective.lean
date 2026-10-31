/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Derived
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Homotopically projective periodic complexes

A cyclic cochain complex `K` is **homotopically projective** when every morphism from `K` to an
acyclic cyclic complex is null-homotopic; equivalently, its class in the periodic homotopy
category is left orthogonal to the acyclic objects. This is the periodic analogue of Mathlib's
`CochainComplex.IsKProjective`. At period zero, when `ZMod 0` is integer indexing, the two
notions have the same definition.

Homotopically projective complexes are the ones on which passage from the periodic homotopy
category to the periodic derived category loses no information: morphisms out of them into any
object are the same in both categories, so the full subcategory of homotopically projective
objects of the homotopy category embeds fully faithfully into the derived category, and a
quasi-isomorphism between homotopically projective complexes is a homotopy equivalence.

The notion must be kept apart from acyclicity, contractibility, and projectivity of the terms.
A complex is contractible exactly when it is both acyclic and homotopically projective
(`isHomotopicallyProjective_and_acyclic_iff`). Projectivity of every term does not suffice: the
differential module given by multiplication by `ε` on the dual numbers is acyclic, has a free
underlying module, and is not contractible, so it is not homotopically projective
(`TauCeti.not_isHomotopicallyProjective_dualNumberPeriodicComplex`).

## Main definitions

* `TauCeti.PeriodicComplex.IsHomotopicallyProjective`: every morphism to an acyclic periodic
  complex is null-homotopic.

## Main results

* `TauCeti.PeriodicComplex.isHomotopicallyProjective_iff_leftOrthogonal`: the definition as left
  orthogonality to the acyclic objects of the periodic homotopy category.
* `TauCeti.PeriodicComplex.isHomotopicallyProjective_and_acyclic_iff`: a periodic complex is
  contractible exactly when it is acyclic and homotopically projective.
* `TauCeti.PeriodicComplex.IsHomotopicallyProjective.Qh_map_bijective`: the periodic Verdier
  localization is bijective on morphisms out of a homotopically projective complex.
* `TauCeti.PeriodicComplex.IsHomotopicallyProjective.quasiIso_iff`: between homotopically
  projective complexes, quasi-isomorphisms are exactly the homotopy equivalences.
* `TauCeti.PeriodicComplex.isHomotopicallyProjective_of_d_eq_zero`: a complex with projective
  terms and zero differential is homotopically projective.
* `TauCeti.PeriodicComplex.IsHomotopicallyProjective.of_splitting`: homotopically projective
  complexes are closed under extensions that split in every degree.
* `TauCeti.PeriodicComplex.nonempty_homotopy_zero_of_epi`: a morphism from a complex of
  projectives to `L` is null-homotopic when `L` is covered by a contractible complex `Q` and
  every morphism from the shift of the source to the kernel of `Q ⟶ L` is null-homotopic.

The proofs follow Joël Riou's treatment of K-projective complexes in
`Mathlib.Algebra.Homology.HomotopyCategory.KProjective` and
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Mathematica **65** (1988),
  121–154.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}

/-- A cyclic cochain complex `K` is homotopically projective if every morphism from `K` to an
acyclic cyclic complex is null-homotopic. This is the periodic analogue of Mathlib's
`CochainComplex.IsKProjective`. -/
class IsHomotopicallyProjective (K : CochainComplex C (ZMod n)) : Prop where
  nonempty_homotopy_zero {L : CochainComplex C (ZMod n)} (f : K ⟶ L) :
    L.Acyclic → Nonempty (Homotopy f 0)

/-- A complex is homotopically projective exactly when its class in the periodic homotopy
category admits no nonzero morphism to an acyclic object. -/
theorem isHomotopicallyProjective_iff_leftOrthogonal (K : CochainComplex C (ZMod n)) :
    IsHomotopicallyProjective K ↔
      (subcategoryAcyclic C n).leftOrthogonal
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K) := by
  refine ⟨fun hK L f hL ↦ ?_,
    fun hK ↦ ⟨fun {L} f hL ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [quotient_obj_mem_subcategoryAcyclic_iff] at hL
    obtain ⟨h⟩ := hK.nonempty_homotopy_zero f hL
    rw [HomotopyCategory.eq_of_homotopy f 0 h, Functor.map_zero]
  · rw [← quotient_obj_mem_subcategoryAcyclic_iff] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL, Functor.map_zero]

/-- The class of a homotopically projective complex is left orthogonal to the acyclic objects. -/
theorem IsHomotopicallyProjective.leftOrthogonal (K : CochainComplex C (ZMod n))
    [IsHomotopicallyProjective K] :
    (subcategoryAcyclic C n).leftOrthogonal
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K) :=
  (isHomotopicallyProjective_iff_leftOrthogonal K).mp ‹_›

/-- Homotopically projective complexes are invariant under homotopy equivalence. -/
theorem _root_.HomotopyEquiv.isHomotopicallyProjective_iff {K L : CochainComplex C (ZMod n)}
    (e : HomotopyEquiv K L) : IsHomotopicallyProjective K ↔ IsHomotopicallyProjective L := by
  simp only [isHomotopicallyProjective_iff_leftOrthogonal]
  exact ObjectProperty.prop_iff_of_iso _ (HomotopyCategory.isoOfHomotopyEquiv e)

/-- Homotopically projective complexes are stable under the integral shifts. -/
instance (K : CochainComplex C (ZMod n)) [IsHomotopicallyProjective K] (k : ℤ) :
    IsHomotopicallyProjective (K⟦k⟧) := by
  rw [isHomotopicallyProjective_iff_leftOrthogonal]
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso k).symm.app K)
    ((subcategoryAcyclic C n).leftOrthogonal.le_shift k _
      (IsHomotopicallyProjective.leftOrthogonal K))

/-- A shift of a complex is homotopically projective exactly when the complex is. -/
theorem isHomotopicallyProjective_shift_iff (K : CochainComplex C (ZMod n)) (k : ℤ) :
    IsHomotopicallyProjective (K⟦k⟧) ↔ IsHomotopicallyProjective K :=
  ⟨fun _ ↦ (HomotopyEquiv.ofIso
      ((shiftEquiv _ k).unitIso.symm.app K)).isHomotopicallyProjective_iff.mp
      (inferInstanceAs (IsHomotopicallyProjective (K⟦k⟧⟦-k⟧))),
    fun _ ↦ inferInstance⟩

/-- A contractible complex is homotopically projective. -/
theorem isHomotopicallyProjective_of_homotopy {K : CochainComplex C (ZMod n)}
    (h : Homotopy (𝟙 K) 0) : IsHomotopicallyProjective K where
  nonempty_homotopy_zero f _ :=
    ⟨((Homotopy.ofEq (Category.id_comp f).symm).trans (h.compRight f)).trans
      (Homotopy.ofEq (Limits.zero_comp))⟩

/-- A periodic complex is contractible exactly when it is acyclic and homotopically projective. -/
theorem isHomotopicallyProjective_and_acyclic_iff (K : CochainComplex C (ZMod n)) :
    IsHomotopicallyProjective K ∧ K.Acyclic ↔ Nonempty (Homotopy (𝟙 K) 0) := by
  refine ⟨fun ⟨hK, hac⟩ ↦ hK.nonempty_homotopy_zero (𝟙 K) hac, fun ⟨h⟩ ↦
    ⟨isHomotopicallyProjective_of_homotopy h, ?_⟩⟩
  rw [← quotient_obj_mem_subcategoryAcyclic_iff]
  exact ObjectProperty.prop_of_isZero _ ((HomotopyCategory.isZero_quotient_obj_iff K).mpr ⟨h⟩)

/-- A periodic complex with projective terms and zero differential is homotopically projective. -/
theorem isHomotopicallyProjective_of_d_eq_zero {K : CochainComplex C (ZMod n)}
    [∀ i, Projective (K.X i)] (hd : ∀ i j, K.d i j = 0) : IsHomotopicallyProjective K where
  nonempty_homotopy_zero {L} f hL := by
    have hex (j i : ZMod n) (hji : j + 1 = i) : (L.sc' j i (i + 1)).Exact :=
      (L.exactAt_iff' j i (i + 1) ((ComplexShape.up (ZMod n)).prev_eq' hji)
        ((ComplexShape.up (ZMod n)).next_eq' rfl)).mp (hL i)
    have hf (i : ZMod n) : f.f i ≫ L.d i (i + 1) = 0 := by
      rw [f.comm, hd, zero_comp]
    let h : ∀ i j, (ComplexShape.up (ZMod n)).Rel j i → (K.X i ⟶ L.X j) :=
      fun i j hji ↦ (hex j i hji).liftFromProjective (f.f i) (hf i)
    refine ⟨(Homotopy.ofEq ?_).trans (Homotopy.nullHomotopy' h)⟩
    ext i
    rw [Homotopy.nullHomotopicMap'_f (k₂ := i - 1) (k₀ := i + 1) (sub_add_cancel i 1) rfl, hd,
      zero_comp, zero_add]
    exact ((hex (i - 1) i (sub_add_cancel i 1)).liftFromProjective_comp (f.f i) (hf i)).symm

/-- Homotopically projective periodic complexes are closed under extensions that split in every
degree. The splittings need not be compatible with the differentials. -/
theorem IsHomotopicallyProjective.of_splitting (S : ShortComplex (CochainComplex C (ZMod n)))
    (hS : ∀ i, Nonempty (S.map (eval C (ComplexShape.up (ZMod n)) i)).Splitting)
    [IsHomotopicallyProjective S.X₁] [IsHomotopicallyProjective S.X₃] :
    IsHomotopicallyProjective S.X₂ := by
  let := ExactStructure.homologicalComplex_split_isFrobenius (C := C)
    (c := ComplexShape.up (ZMod n)) (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    (fun i ↦ ⟨i + 1, rfl⟩) |>.stableHasShift
  let := stableToHomotopyCommShift C n
  have hT := homotopyCategory_map_stableConflationTriangle_mem_distTriang C n S
    ((ExactStructure.homologicalComplex_conflation_iff _ _ S).mpr
      fun i ↦ (ExactStructure.split_conflation _).mpr (hS i))
  rw [isHomotopicallyProjective_iff_leftOrthogonal]
  -- The degreewise split sequence gives a distinguished triangle in the homotopy category whose
  -- vertices are the classes of `S.X₁`, `S.X₂` and `S.X₃`.
  simpa using (subcategoryAcyclic C n).leftOrthogonal.ext_of_isTriangulatedClosed₂ _ hT
    (by simpa using IsHomotopicallyProjective.leftOrthogonal S.X₁)
    (by simpa using IsHomotopicallyProjective.leftOrthogonal S.X₃)

/-- A morphism `f : K ⟶ L` from a periodic complex of projectives is null-homotopic as soon as
`L` is the target of a degreewise epimorphism `π : Q ⟶ L` from a contractible complex such that
every morphism `K⟦-1⟧ ⟶ ker π` is null-homotopic. -/
lemma nonempty_homotopy_zero_of_epi {K L Q : CochainComplex C (ZMod n)}
    [∀ i, Projective (K.X i)] (π : Q ⟶ L) [∀ i, Epi (π.f i)] (hQ : Homotopy (𝟙 Q) 0)
    (hN : ∀ u : K⟦(-1 : ℤ)⟧ ⟶ kernel π, Nonempty (Homotopy u 0)) (f : K ⟶ L) :
    Nonempty (Homotopy f 0) := by
  -- Lift `f` degreewise along `π`.
  let g (i : ZMod n) : K.X i ⟶ Q.X i := Projective.factorThru (f.f i) (π.f i)
  have hg (i : ZMod n) : g i ≫ π.f i = f.f i := Projective.factorThru_comp _ _
  have hgX (a b : ZMod n) (h : a = b) :
      (K.XIsoOfEq h).hom ≫ g b = g a ≫ (Q.XIsoOfEq h).hom := by
    subst h
    simp
  -- The failure of `g` to commute with the differentials, as a chain map out of `K⟦-1⟧`.
  let u : K⟦(-1 : ℤ)⟧ ⟶ Q :=
    { f i := g (i + ((-1 : ℤ) : ZMod n)) ≫ Q.d _ i - K.d _ i ≫ g i
      comm' := by
        rintro i _ rfl
        have hd (a b : ZMod n) (h : a = b) :
            K.d (i + ((-1 : ℤ) : ZMod n)) a ≫ g a ≫ Q.d a (i + 1) =
              K.d (i + ((-1 : ℤ) : ZMod n)) b ≫ g b ≫ Q.d b (i + 1) := by
          subst h
          rfl
        simp [hd i (i + 1 + ((-1 : ℤ) : ZMod n)) (by push_cast; ring)] }
  have hu : u ≫ π = 0 := by
    ext i
    simp only [u, comp_f, Preadditive.sub_comp, Category.assoc, ← π.comm, hg,
      reassoc_of% hg, f.comm, sub_self, zero_f]
  obtain ⟨H⟩ := hN (kernel.lift π u hu)
  -- A null-homotopy of `u` whose components are killed by `π`.
  let H' : Homotopy u 0 :=
    (Homotopy.ofEq (kernel.lift_ι π u hu).symm).trans
      ((H.compRight (kernel.ι π)).trans (Homotopy.ofEq zero_comp))
  have hH' (i j : ZMod n) : H'.hom i j ≫ π.f j = 0 := by
    simp [H', ← comp_f]
  let e (i : ZMod n) : K.X i ⟶ (K⟦(-1 : ℤ)⟧).X (i + 1) :=
    (K.XIsoOfEq (by push_cast; ring)).hom
  -- On `K`, the component of `u` in degree `i + 1` is the failure of `g` to commute with `d`.
  have he (i : ZMod n) :
      e i ≫ u.f (i + 1) = g i ≫ Q.d i (i + 1) - K.d i (i + 1) ≫ g (i + 1) := by
    simp [u, e, Preadditive.comp_sub, XIsoOfEq_hom_comp_d_assoc, reassoc_of% hgX]
  -- The corrected lift of `f`, a chain map `K ⟶ Q`.
  let g' : K ⟶ Q :=
    { f i := g i - e i ≫ H'.hom (i + 1) i
      comm' := by
        rintro i _ rfl
        have H₂ : e i ≫ u.f (i + 1) = -(K.d i (i + 1) ≫ e (i + 1) ≫ H'.hom (i + 1 + 1) (i + 1)) +
            e i ≫ H'.hom (i + 1) i ≫ Q.d i (i + 1) :=
          H'.comm_periodic_shift_neg_one i
        rw [he] at H₂
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc, e]
        rw [sub_eq_sub_iff_sub_eq_sub, H₂]
        abel }
  have hg' : g' ≫ π = f := by
    ext i
    simp [g', hg, hH']
  exact ⟨(Homotopy.ofEq (by simp [hg'])).trans
    (((hQ.compLeft g').compRight π).trans (Homotopy.ofEq (by simp)))⟩

namespace IsHomotopicallyProjective

/-- Passage to the periodic derived category is bijective on morphisms out of a homotopically
projective complex. -/
theorem Qh_map_bijective (K : CochainComplex C (ZMod n))
    (L : HomotopyCategory C (ComplexShape.up (ZMod n))) [IsHomotopicallyProjective K] :
    Function.Bijective ((DerivedCategory.Qh C n).map :
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K ⟶ L) → _) :=
  (IsHomotopicallyProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

/-- A morphism between homotopically projective complexes is a quasi-isomorphism exactly when it
is a homotopy equivalence. -/
theorem quasiIso_iff {K L : CochainComplex C (ZMod n)} [IsHomotopicallyProjective K]
    [IsHomotopicallyProjective L] (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (ComplexShape.up (ZMod n)) f := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  have : IsIso ((DerivedCategory.Q C n).map f) := inferInstance
  rw [← DerivedCategory.quotient_comp_Qh, Functor.comp_map] at this
  obtain ⟨g, hg⟩ := (Qh_map_bijective L _).surjective
    (inv ((DerivedCategory.Qh C n).map
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map f)))
  refine ⟨g, (Qh_map_bijective K _).injective ?_, (Qh_map_bijective L _).injective ?_⟩
  · simp [hg]
  · simp [hg]

end IsHomotopicallyProjective

namespace DerivedCategory

variable (C n)

/-- The periodic Verdier localization is full on homotopically projective objects. -/
instance : ((subcategoryAcyclic C n).leftOrthogonal.ι ⋙ Qh C n).Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := (X.property.map_bijective_of_isTriangulated (Qh C n) Y.obj).surjective g
    exact ⟨ObjectProperty.homMk f, hf⟩

/-- The periodic Verdier localization is faithful on homotopically projective objects. -/
instance : ((subcategoryAcyclic C n).leftOrthogonal.ι ⋙ Qh C n).Faithful where
  map_injective {X Y} _ _ hfg :=
    ObjectProperty.hom_ext _
      ((X.property.map_bijective_of_isTriangulated (Qh C n) Y.obj).injective hfg)

end DerivedCategory

end TauCeti.PeriodicComplex
