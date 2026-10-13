/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Data.ZMod.Basic

/-!
# Unfolding periodic complexes

Unfolding repeats a cyclically indexed complex along the integers. In degree `i`, the
unfolded complex has the term indexed by the residue of `i`, and its differential is the
corresponding cyclic differential. Differentials between nonconsecutive integers are zero,
even if their residues are consecutive.

The unfolding functor preserves homotopies and compares ordinary homology in degree `i`
with cyclic homology in degree `i mod n`. It preserves and reflects acyclicity and
quasi-isomorphisms. This allows an exact periodic tail to be used as an ordinary complex.
The construction also works for `n = 0`, when `ZMod 0` is integer indexing; only positive
`n` describes a finite period.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Sections 3.1–3.2.

The complex constructor and short-complex homology comparisons are Mathlib's
`CochainComplex.of` and `HomologicalComplex.homologyFunctorIso'`.
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace TauCeti.PeriodicComplex

variable (C : Type u) [Category.{v} C] (n : ℕ)

section

variable [HasZeroMorphisms C]

/-- Repeat a `ZMod n`-indexed complex along the integers, retaining only consecutive
integer differentials. -/
-- Expose the object builder so the dependent component formulas have literal endpoints.
@[expose, implicit_reducible]
def unfoldFunctor : HomologicalComplex C (ComplexShape.up (ZMod n)) ⥤ CochainComplex C ℤ where
  obj K := CochainComplex.of (fun i : ℤ ↦ K.X (i : ZMod n))
    (fun i ↦ K.d (i : ZMod n) ((i + 1 : ℤ) : ZMod n))
    (fun i ↦ K.d_comp_d _ _ _)
  map f := CochainComplex.ofHom (fun i ↦ f.f (i : ZMod n)) (fun i ↦ by
    simpa only [CochainComplex.of_d] using f.comm (i : ZMod n) ((i + 1 : ℤ) : ZMod n))

/-- Unfolding reads the term at the residue of the integer degree. -/
@[simp]
theorem unfoldFunctor_obj_X (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (i : ℤ) :
    ((unfoldFunctor C n).obj K).X i = K.X (i : ZMod n) := (rfl)

/-- The consecutive differential of the unfolding is the cyclic differential. -/
@[simp]
theorem unfoldFunctor_obj_d (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (i : ℤ) :
    ((unfoldFunctor C n).obj K).d i (i + 1) =
      K.d (i : ZMod n) ((i + 1 : ℤ) : ZMod n) :=
  CochainComplex.of_d (fun i : ℤ ↦ K.X (i : ZMod n))
    (fun i ↦ K.d (i : ZMod n) ((i + 1 : ℤ) : ZMod n)) i

/-- Unfolding reads a morphism at the residue of the integer degree. -/
@[simp]
theorem unfoldFunctor_map_f {K L : HomologicalComplex C (ComplexShape.up (ZMod n))}
    (f : K ⟶ L) (i : ℤ) : ((unfoldFunctor C n).map f).f i = f.f (i : ZMod n) := (rfl)

instance : (unfoldFunctor C n).Faithful where
  map_injective {K L} f g h := by
    ext j
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective j
    exact congrArg (fun k ↦ k.f i) h

/-- The three-term complexes computing unfolded and cyclic homology agree, naturally in
chain maps. The outer terms are transported along the integer-cast identities. -/
private noncomputable def unfoldShortComplexIso (i : ℤ) :
    unfoldFunctor C n ⋙ shortComplexFunctor' C (ComplexShape.up ℤ) (i - 1) i (i + 1) ≅
      shortComplexFunctor' C (ComplexShape.up (ZMod n))
        ((i : ZMod n) - 1) (i : ZMod n) ((i : ZMod n) + 1) :=
  NatIso.ofComponents (fun K ↦ ShortComplex.isoMk
    (K.XIsoOfEq (by simp)) (Iso.refl _) (K.XIsoOfEq (by simp))
    (by
      -- Normalize the consecutive integer differential before transporting its endpoints.
      dsimp only [Functor.comp_obj, shortComplexFunctor', unfoldFunctor,
        CochainComplex.of, CochainComplex.of.d, XIsoOfEq]
      simp)
    (by
      dsimp only [Functor.comp_obj, shortComplexFunctor', unfoldFunctor,
        CochainComplex.of, CochainComplex.of.d, XIsoOfEq]
      simp)) (fun f ↦ by
        ext <;> simp [shortComplexFunctor', ShortComplex.isoMk, XIsoOfEq_hom_naturality])

/-- Compare the canonical short complexes, allowing homology to be assumed locally. -/
private noncomputable def unfoldCanonicalShortComplexIso (i : ℤ) :
    unfoldFunctor C n ⋙ shortComplexFunctor C (ComplexShape.up ℤ) i ≅
      shortComplexFunctor C (ComplexShape.up (ZMod n)) (i : ZMod n) :=
  Functor.isoWhiskerLeft _
      (natIsoSc' C (ComplexShape.up ℤ) (i - 1) i (i + 1) (by simp) (by simp)) ≪≫
    unfoldShortComplexIso C n i ≪≫
    (natIsoSc' C (ComplexShape.up (ZMod n))
      ((i : ZMod n) - 1) (i : ZMod n) ((i : ZMod n) + 1) (by simp) (by simp)).symm

/-- Homology at a cyclic degree supplies homology at each integer degree above it. -/
instance (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (i : ℤ)
    [K.HasHomology (i : ZMod n)] : ((unfoldFunctor C n).obj K).HasHomology i :=
  ShortComplex.hasHomology_of_iso ((unfoldCanonicalShortComplexIso C n i).app K).symm

/-- Ordinary homology of the unfolding is cyclic homology at the residue of the degree. -/
noncomputable def unfoldHomologyIso [CategoryWithHomology C] (i : ℤ) :
    unfoldFunctor C n ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up (ZMod n)) (i : ZMod n) :=
  Functor.isoWhiskerLeft _
      (HomologicalComplex.homologyFunctorIso' C (ComplexShape.up ℤ) (i - 1) i (i + 1)
        (by simp) (by simp)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (unfoldShortComplexIso C n i) _ ≪≫
    (HomologicalComplex.homologyFunctorIso' C (ComplexShape.up (ZMod n))
      ((i : ZMod n) - 1) (i : ZMod n) ((i : ZMod n) + 1) (by simp) (by simp)).symm

/-- Unfolding preserves and reflects exactness at the corresponding residue. -/
@[simp]
theorem unfoldFunctor_exactAt_iff (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (i : ℤ) : ((unfoldFunctor C n).obj K).ExactAt i ↔ K.ExactAt (i : ZMod n) := by
  rw [exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp),
    exactAt_iff' _ ((i : ZMod n) - 1) (i : ZMod n) ((i : ZMod n) + 1)
      (by simp) (by simp)]
  exact ShortComplex.exact_iff_of_iso ((unfoldShortComplexIso C n i).app K)

/-- The unfolding is acyclic exactly when the cyclic complex is acyclic. -/
@[simp]
theorem unfoldFunctor_acyclic_iff (K : HomologicalComplex C (ComplexShape.up (ZMod n))) :
    ((unfoldFunctor C n).obj K).Acyclic ↔ K.Acyclic := by
  simp only [acyclic_iff, unfoldFunctor_exactAt_iff]
  exact ZMod.intCast_surjective.forall.symm

/-- Unfolding preserves and reflects quasi-isomorphisms at the corresponding residue. -/
@[simp]
theorem unfoldFunctor_quasiIsoAt_iff
    {K L : HomologicalComplex C (ComplexShape.up (ZMod n))} (f : K ⟶ L) (i : ℤ)
    [K.HasHomology (i : ZMod n)] [L.HasHomology (i : ZMod n)] :
    QuasiIsoAt ((unfoldFunctor C n).map f) i ↔ QuasiIsoAt f (i : ZMod n) := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (unfoldCanonicalShortComplexIso C n i) (Arrow.mk f))

/-- A cyclic map is a quasi-isomorphism exactly when its unfolding is one. -/
@[simp]
theorem unfoldFunctor_quasiIso_iff
    {K L : HomologicalComplex C (ComplexShape.up (ZMod n))} (f : K ⟶ L)
    [∀ j, K.HasHomology j] [∀ j, L.HasHomology j] :
    QuasiIso ((unfoldFunctor C n).map f) ↔ QuasiIso f := by
  simp only [quasiIso_iff, unfoldFunctor_quasiIsoAt_iff]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective j
    exact h i
  · intro h i
    exact h (i : ZMod n)

end

section

variable [Preadditive C]

instance : (unfoldFunctor C n).Additive where

instance {R : Type*} [Semiring R] [Linear R C] :
    (unfoldFunctor C n).Linear R where

end

end TauCeti.PeriodicComplex

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] {n : ℕ}
  {K L : HomologicalComplex C (ComplexShape.up (ZMod n))} {f g : K ⟶ L}

/-- Repeat a cyclic homotopy along the integers, with zero components outside degree `-1`.
The resulting homotopy witnesses invariance of unfolding under cyclic chain homotopies. -/
noncomputable def unfoldPeriodic (h : Homotopy f g) :
    Homotopy ((TauCeti.PeriodicComplex.unfoldFunctor C n).map f)
      ((TauCeti.PeriodicComplex.unfoldFunctor C n).map g) where
  hom i j := if j + 1 = i then h.hom (i : ZMod n) (j : ZMod n) else 0
  zero i j hij := ite_eq_right hij
  comm i := by
    have hi_next : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
    have hi_prev : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
    have hn : (ComplexShape.up (ZMod n)).Rel (i : ZMod n) ((i + 1 : ℤ) : ZMod n) := by simp
    have hp : (ComplexShape.up (ZMod n)).Rel ((i - 1 : ℤ) : ZMod n) (i : ZMod n) := by simp
    have d_consecutive (j k : ℤ) (hjk : j + 1 = k) :
        ((TauCeti.PeriodicComplex.unfoldFunctor C n).obj L).d j k =
          L.d (j : ZMod n) (k : ZMod n) := by
      subst k
      exact TauCeti.PeriodicComplex.unfoldFunctor_obj_d C n L j
    have hom_next : (if i + 1 = i + 1 then
        h.hom ((i + 1 : ℤ) : ZMod n) (i : ZMod n) else 0) =
        h.hom ((i + 1 : ℤ) : ZMod n) (i : ZMod n) := ite_eq_left rfl
    have hom_prev : (if (i - 1) + 1 = i then
        h.hom (i : ZMod n) ((i - 1 : ℤ) : ZMod n) else 0) =
        h.hom (i : ZMod n) ((i - 1 : ℤ) : ZMod n) := ite_eq_left (Int.sub_add_cancel i 1)
    rw [dNext_eq _ hi_next, prevD_eq _ hi_prev, hom_next, hom_prev]
    simp only [TauCeti.PeriodicComplex.unfoldFunctor_map_f,
      TauCeti.PeriodicComplex.unfoldFunctor_obj_d,
      d_consecutive (i - 1) i (Int.sub_add_cancel i 1)]
    simpa only [dNext_eq _ hn, prevD_eq _ hp] using h.comm (i : ZMod n)

/-- The consecutive component of an unfolded homotopy is the original cyclic component. -/
@[simp]
theorem unfoldPeriodic_hom (h : Homotopy f g) (i : ℤ) :
    h.unfoldPeriodic.hom (i + 1) i = h.hom ((i + 1 : ℤ) : ZMod n) (i : ZMod n) := by
  simp [unfoldPeriodic]

end Homotopy

namespace TauCeti.PeriodicComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] (n : ℕ)

/-- Unfolding descends to the cyclic homotopy category because it preserves homotopies. -/
-- As for Mathlib's `Functor.mapHomotopyCategory`, retain literal represented endpoints.
@[expose, implicit_reducible]
noncomputable def unfoldHomotopyFunctor :
    HomotopyCategory C (ComplexShape.up (ZMod n)) ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _ (unfoldFunctor C n ⋙ HomotopyCategory.quotient C _)
    (fun _ _ _ _ ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _ h.unfoldPeriodic)

/-- The class of an unfolded object is the unfolding of its cyclic homotopy class. -/
@[simp]
theorem unfoldHomotopyFunctor_obj (K : HomologicalComplex C (ComplexShape.up (ZMod n))) :
    (unfoldHomotopyFunctor C n).obj ((HomotopyCategory.quotient C _).obj K) =
      (HomotopyCategory.quotient C _).obj ((unfoldFunctor C n).obj K) :=
  (rfl)

/-- On a represented map, homotopy-category unfolding is the class of its unfolding. -/
@[simp]
theorem unfoldHomotopyFunctor_map {K L : HomologicalComplex C (ComplexShape.up (ZMod n))}
    (f : K ⟶ L) :
    (unfoldHomotopyFunctor C n).map ((HomotopyCategory.quotient C _).map f) =
      (HomotopyCategory.quotient C _).map ((unfoldFunctor C n).map f) :=
  (rfl)

/-- Unfolding commutes with passage to homotopy classes. -/
theorem quotient_comp_unfoldHomotopyFunctor :
    HomotopyCategory.quotient C (ComplexShape.up (ZMod n)) ⋙ unfoldHomotopyFunctor C n =
      unfoldFunctor C n ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance : (unfoldHomotopyFunctor C n).Additive := by
  have : (HomotopyCategory.quotient C (ComplexShape.up (ZMod n)) ⋙
      unfoldHomotopyFunctor C n).Additive := by
    rw [quotient_comp_unfoldHomotopyFunctor]
    infer_instance
  exact (HomotopyCategory.quotient C _).additive_of_full_essSurj_comp _

instance {R : Type*} [Semiring R] [Linear R C] : (unfoldHomotopyFunctor C n).Linear R := by
  have : (HomotopyCategory.quotient C (ComplexShape.up (ZMod n)) ⋙
      unfoldHomotopyFunctor C n).Linear R := by
    rw [quotient_comp_unfoldHomotopyFunctor]
    infer_instance
  exact (HomotopyCategory.quotient C _).linear_of_full_essSurj_comp _

end TauCeti.PeriodicComplex
