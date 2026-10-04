/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Cone.Basic
public import TauCeti.Algebra.Homology.Curved.Triangulated

/-!
# Distinguished mapping-cone triangles of curved duplexes

The concrete mapping cone realizes the triangulation of the homotopy category of curved
duplexes obtained from the componentwise split Frobenius structure. For every closed even map
`f : X ⟶ Y`, the triangle `X ⟶ Y ⟶ cone(f) ⟶ X⟦1⟧` is distinguished. Conversely, every
distinguished triangle is isomorphic to such a cone triangle.

The last map is **minus** the canonical projection to the parity shift, followed by its
identification with the shift by `1`. This is the same sign as Mathlib's
`CochainComplex.mappingCone.triangle`: the cone differential has lower-left block `f`.

## Main results

* `HomotopyCategory.coneTriangle_distinguished`: concrete cone triangles are distinguished.
* `HomotopyCategory.mem_distTriang_iff_nonempty_iso_coneTriangle`: cone triangles, up to
  isomorphism, exhaust the distinguished triangles.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3.
-/

public section

namespace TauCeti.CurvedDuplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w' v u

-- Component formulas use biproducts and evaluations as intermediate endpoints. Allow their
-- reduction while matching the biproduct identities, without unfolding any morphism bodies.
attribute [local implicit_reducible] CurvedDuplex.biprod diskSum eval₀ eval₁

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w'} [Semiring R] [Linear R C] {w : R} {X Y : CurvedDuplex C w}

private noncomputable def coneSequence (f : X ⟶ Y) : ShortComplex (CurvedDuplex C w) :=
  ShortComplex.mk (biprodLift (toDiskSum X) f)
    (biprodDesc (-fromDiskSum (Y := cone f) biprod.inl biprod.inl) (coneInclusion f)) (by
      ext <;> simp [biprod.lift_desc, Preadditive.comp_add])

private theorem coneSequence_connecting (f : X ⟶ Y) :
    (coneSequence f).g ≫ (-coneProjection f) =
      biprodFst (diskSum X) Y ≫ diskSumToParityShift X := by
  ext <;> apply biprod.hom_ext' <;>
    (try apply biprod.hom_ext') <;> simp [coneSequence, Category.assoc]

variable [HasZeroObject C] in
private theorem coneSequence_conflation (f : X ⟶ Y) :
    ((ExactStructure.split C).curvedDuplex w).Conflation (coneSequence f) := by
  rw [ExactStructure.curvedDuplex_conflation_iff]
  -- Normalize the private short complex before writing its component splittings.
  dsimp only [coneSequence]
  constructor
  · refine (ExactStructure.split_conflation _).2 ⟨?_⟩
    refine
      { r := biprod.fst ≫ biprod.snd
        s := biprod.lift (biprod.fst ≫ (-biprod.inl)) biprod.snd
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · simp only [ShortComplex.map_f, eval₀_map, biprodLift_f₀, toDiskSum_f₀]
      -- The source is typed through evaluation; `erw` reduces that remaining endpoint.
      erw [biprod.lift_fst_assoc, biprod.lift_snd]
      rfl
    · apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [Category.assoc]
    · apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
        (try apply biprod.hom_ext) <;> (try apply biprod.hom_ext') <;>
        simp [Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
  · refine (ExactStructure.split_conflation _).2 ⟨?_⟩
    refine
      { r := biprod.fst ≫ biprod.fst
        s := biprod.lift (biprod.fst ≫ biprod.inr) biprod.snd
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · simp only [ShortComplex.map_f, eval₁_map, biprodLift_f₁, toDiskSum_f₁]
      -- The source is typed through evaluation; `erw` reduces that remaining endpoint.
      erw [biprod.lift_fst_assoc, biprod.lift_fst]
      rfl
    · apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [Category.assoc]
    · apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
        (try apply biprod.hom_ext) <;> (try apply biprod.hom_ext') <;>
        simp [Category.assoc, Preadditive.add_comp, Preadditive.comp_add]

namespace HomotopyCategory

/-- The mapping-cone triangle of a closed even morphism, with last map minus the projection to
the parity shift, identified with the shift by `1` in the homotopy category. -/
-- Exposed because the object formulas determine the types of its three morphisms.
@[expose, implicit_reducible]
noncomputable def coneTriangle (f : X ⟶ Y) : Triangle (HomotopyCategory C w) :=
  Triangle.mk ((nullHomotopic C w).quotientFunctor.map f)
    ((nullHomotopic C w).quotientFunctor.map (coneInclusion f))
    (-(nullHomotopic C w).quotientFunctor.map (coneProjection f) ≫
      (parityShiftCompQuotientFunctorIso C w).hom.app X)

@[simp] theorem coneTriangle_obj₁ (f : X ⟶ Y) :
    (coneTriangle f).obj₁ = (nullHomotopic C w).quotientFunctor.obj X := (rfl)

@[simp] theorem coneTriangle_obj₂ (f : X ⟶ Y) :
    (coneTriangle f).obj₂ = (nullHomotopic C w).quotientFunctor.obj Y := (rfl)

@[simp] theorem coneTriangle_obj₃ (f : X ⟶ Y) :
    (coneTriangle f).obj₃ = (nullHomotopic C w).quotientFunctor.obj (cone f) := (rfl)

@[simp] theorem coneTriangle_mor₁ (f : X ⟶ Y) :
    (coneTriangle f).mor₁ = (nullHomotopic C w).quotientFunctor.map f := (rfl)

@[simp] theorem coneTriangle_mor₂ (f : X ⟶ Y) :
    (coneTriangle f).mor₂ =
      (nullHomotopic C w).quotientFunctor.map (coneInclusion f) := (rfl)

@[simp] theorem coneTriangle_mor₃ (f : X ⟶ Y) :
    (coneTriangle f).mor₃ = -(nullHomotopic C w).quotientFunctor.map (coneProjection f) ≫
      (parityShiftCompQuotientFunctorIso C w).hom.app X := (rfl)

variable [HasZeroObject C]

private noncomputable def diskSumBiprodIso (X Y : CurvedDuplex C w) :
    (nullHomotopic C w).quotientFunctor.obj Y ≅
      (nullHomotopic C w).quotientFunctor.obj (CurvedDuplex.biprod (diskSum X) Y) := by
  -- Compare the componentwise biproduct with the categorical one used by the stable API.
  let b : BinaryBicone (diskSum X) Y :=
    { pt := CurvedDuplex.biprod (diskSum X) Y
      fst := biprodFst (diskSum X) Y
      snd := biprodSnd (diskSum X) Y
      inl := biprodInl (diskSum X) Y
      inr := biprodInr (diskSum X) Y }
  let hb : IsLimit b.toCone := BinaryFan.IsLimit.mk _ (fun f g ↦ biprodLift f g)
    (fun f g ↦ biprodLift_fst f g) (fun f g ↦ biprodLift_snd f g)
    (fun f g _ h₀ h₁ ↦ biprod_hom_ext
      (h₀.trans (biprodLift_fst f g).symm) (h₁.trans (biprodLift_snd f g).symm))
  let e := biprod.uniqueUpToIso _ _ (isBinaryBilimitOfIsLimit b hb)
  exact (eqToIso (by simp)).symm ≪≫
    (ExactStructure.curvedDuplexSplitStableToHomotopy C w).mapIso
      (((ExactStructure.split C).curvedDuplex w).projectiveStableIsoBiprod
        (ExactStructure.curvedDuplex_split_isProjective_of_mem_nullHomotopic
          (id_diskSum_mem_nullHomotopic X)) Y) ≪≫
    eqToIso (by simp) ≪≫ (nullHomotopic C w).quotientFunctor.mapIso e.symm

/-- The concrete mapping-cone triangle is distinguished for Happel's triangulation of the
homotopy category of curved duplexes. No zero-curvature hypothesis is required. -/
theorem coneTriangle_distinguished (f : X ⟶ Y) :
    coneTriangle f ∈ distTriang (HomotopyCategory C w) := by
  have ha : (coneSequence f).f ≫ biprodFst (diskSum X) Y = toDiskSum X := by
    simp [coneSequence]
  have hT := mk_distinguished_of_conflation (coneSequence_conflation f)
    (biprodFst (diskSum X) Y) (-coneProjection f) ha (coneSequence_connecting f)
  -- Unfold the private short complex so its endpoints match the concrete cone triangle.
  dsimp only [coneSequence] at hT
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (diskSumBiprodIso X Y) (Iso.refl _) ?_ ?_ ?_)
  · have h : biprodLift (toDiskSum X) f - f ≫ biprodInr (diskSum X) Y =
        toDiskSum X ≫ biprodInl (diskSum X) Y := by
      apply biprod_hom_ext <;> simp [Preadditive.sub_comp, Category.assoc]
    have heq : (nullHomotopic C w).quotientFunctor.map (biprodLift (toDiskSum X) f) =
        (nullHomotopic C w).quotientFunctor.map (f ≫ biprodInr (diskSum X) Y) := by
      rw [MorphismIdeal.quotientFunctor_map_eq_iff, h]
      simpa using (nullHomotopic C w).comp_mem_right (biprodInl (diskSum X) Y)
        ((nullHomotopic C w).comp_mem_left (toDiskSum X) (id_diskSum_mem_nullHomotopic X))
    simpa [diskSumBiprodIso, coneTriangle,
      ExactStructure.curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map,
      ← Functor.map_comp] using heq.symm
  · simp [diskSumBiprodIso, coneTriangle,
      ExactStructure.curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map,
      ← Functor.map_comp]
  · simp [coneTriangle]

/-- Distinguished triangles are precisely those isomorphic to concrete mapping-cone triangles
of closed even maps of curved duplexes. -/
theorem mem_distTriang_iff_nonempty_iso_coneTriangle (T : Triangle (HomotopyCategory C w)) :
    T ∈ distTriang (HomotopyCategory C w) ↔
      ∃ (X Y : CurvedDuplex C w) (f : X ⟶ Y), Nonempty (T ≅ coneTriangle f) := by
  refine ⟨fun hT ↦ ?_, fun ⟨X, Y, f, ⟨e⟩⟩ ↦
    isomorphic_distinguished _ (coneTriangle_distinguished f) _ e⟩
  let Q := (nullHomotopic C w).quotientFunctor
  let X := Q.objPreimage T.obj₁
  let Y := Q.objPreimage T.obj₂
  let e₁ := Q.objObjPreimageIso T.obj₁
  let e₂ := Q.objObjPreimageIso T.obj₂
  let f := Q.preimage (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  refine ⟨X, Y, f, ⟨(isoTriangleOfIso₁₂ _ _ (coneTriangle_distinguished f) hT e₁ e₂ ?_).symm⟩⟩
  -- Reduce the triangle's endpoints before using fullness of the quotient.
  dsimp only [coneTriangle, Triangle.mk_mor₁]
  simpa only [X, Y, Q] using
    (by simp [f, Category.assoc] : Q.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁)

end HomotopyCategory

end TauCeti.CurvedDuplex
