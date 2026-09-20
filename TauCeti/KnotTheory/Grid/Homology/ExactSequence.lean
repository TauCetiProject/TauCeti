/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Homology.Unblocked

/-!
# The exact sequence relating unblocked and simply blocked grid homology

Blocking the `O`-marking of a column `i` of a grid diagram sets the variable `V_i` to zero. On
chains this is the coefficientwise specialization `TauCeti.simplyBlockedSpecialization`, which is
surjective with kernel the multiples of `V_i`, and multiplication by `V_i` is injective on `GC⁻`.
So

`0 ⟶ GC⁻(G) ⟶ GC⁻(G) ⟶ GC^_i(G) ⟶ 0`,

with first map multiplication by `V_i` and second map specialization, is a short exact sequence
of complexes of `R[V₀, …, V_{n-1}]`-modules, once the specialized complex is regarded over that
ring by restricting scalars along the specialization. Mathlib's homology sequence then gives the
three-periodic long exact sequence

`⋯ ⟶ GH⁻(G) --V_i--> GH⁻(G) ⟶ G-hat_i(G) --δ--> GH⁻(G) --V_i--> ⋯`

relating unblocked grid homology to the homology of the specialized complex, which for a knot
grid is the simply blocked grid homology `TauCeti.GridDiagram.IsKnot.simplyBlockedHomology`. It
is the standard tool for transferring information between the flavours of grid homology: the
cokernel of the action of `V_i` on `GH⁻(G)` embeds in the homology of the specialized complex,
which in turn surjects onto the kernel of that action. On a knot grid the action of `V_i` on
`GH⁻(G)` is the action of `U` on the `R[U]`-module of
`TauCeti.KnotTheory.Grid.Homology.Unblocked`, by
`TauCeti.GridDiagram.IsKnot.X_smul_unblockedHomology`. The knot-facing exactness corollaries below
state the outer maps using this `U`-action.

## Main definitions

* `TauCeti.simplyBlockedSpecializationHom`: specialization as a morphism of modules over the
  unspecialized polynomial ring.
* `TauCeti.GridDiagram.simplyBlockedComplexRestrictScalars`: the specialized complex, regarded
  over the unspecialized polynomial ring.
* `TauCeti.GridDiagram.simplyBlockedSpecializationChainHom`: specialization as a chain map.
* `TauCeti.GridDiagram.simplyBlockedShortComplex`: the short complex above.
* `TauCeti.GridDiagram.simplyBlockedHomologyMap` and
  `TauCeti.GridDiagram.simplyBlockedHomologyδ`: the specialization-induced map and the connecting
  map of the long exact sequence, respectively.

## Main results

* `TauCeti.GridDiagram.simplyBlockedShortComplex_shortExact`: the sequence of complexes is short
  exact.
* `TauCeti.GridDiagram.exact_X_smul_simplyBlockedHomologyMap`,
  `TauCeti.GridDiagram.exact_simplyBlockedHomologyMap_δ` and
  `TauCeti.GridDiagram.exact_simplyBlockedHomologyδ_X_smul`: exactness of the long exact sequence
  at its three spots.
* The corresponding theorems in `TauCeti.GridDiagram.IsKnot` express the outer maps using the
  `R[U]`-action on knot-grid unblocked homology.

## References

The exact sequence relating `GH⁻` and `G-hat` is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Section 4.6.
-/

public section

namespace TauCeti

open CategoryTheory MvPolynomial

section Modules

variable {n : ℕ} (R : Type*) [CommRing R] (i : Fin n)

/-- Coefficientwise specialization at `V_i = 0`, as a morphism of modules over the unspecialized
polynomial ring: the specialized chain module carries the action of `R[V₀, …, V_{n-1}]` obtained
by restricting scalars along `TauCeti.simplyBlockedRingHom`. -/
noncomputable def simplyBlockedSpecializationHom :
    ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n) ⟶
      (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
        (ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
      (ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i)))
    { toFun := simplyBlockedSpecialization R i
      map_add' := map_add _
      map_smul' := fun p c => (simplyBlockedSpecialization R i).map_smulₛₗ p c }

/-- The module morphism acts by coefficientwise specialization.

Not `@[simp]`: the target of `simplyBlockedSpecializationHom` restricts scalars along the
abbreviation `simplyBlockedRingHom`, which `simp` unfolds while normalizing the left-hand side. -/
theorem simplyBlockedSpecializationHom_apply (c : GridChainMinus R n) :
    (simplyBlockedSpecializationHom R i).hom c = simplyBlockedSpecialization R i c := by
  unfold simplyBlockedSpecializationHom
  rfl

/-- Restriction of scalars makes a source scalar act through the specialization homomorphism. -/
theorem smul_restrictScalars_gridChainHat (p : MvPolynomial (Fin n) R)
    (y : (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
      (ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i))) :
    p • y = simplyBlockedRingHom R i p • y :=
  rfl

/-- The blocked variable annihilates the specialized chain module: it acts through the
specialization, which sends it to zero. -/
@[simp]
theorem X_smul_restrictScalars_gridChainHat_eq_zero
    (y : (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
      (ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i))) :
    (MvPolynomial.X i : MvPolynomial (Fin n) R) • y = 0 := by
  rw [smul_restrictScalars_gridChainHat, simplyBlockedRingHom_X_eq_zero, zero_smul]

/-- The blocked variable annihilates the specialization map. -/
@[simp]
theorem X_smul_simplyBlockedSpecializationHom_eq_zero :
    (MvPolynomial.X i : MvPolynomial (Fin n) R) • simplyBlockedSpecializationHom R i = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun c => by
    rw [ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [X_smul_restrictScalars_gridChainHat_eq_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply])

end Modules

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-! ### The short exact sequence of complexes -/

/-- The simply blocked complex, regarded as a complex of modules over the unspecialized
polynomial ring by restricting scalars along `TauCeti.simplyBlockedRingHom`. -/
noncomputable def simplyBlockedComplexRestrictScalars :
    HomologicalComplex (ModuleCat (MvPolynomial (Fin n) R)) (ComplexShape.refl Unit) :=
  ((ModuleCat.restrictScalars (simplyBlockedRingHom R i)).mapHomologicalComplex _).obj
    (G.simplyBlockedComplex R i)

/-- The unique object of the restricted simply blocked complex. -/
@[simp]
theorem simplyBlockedComplexRestrictScalars_X (j : Unit) :
    (G.simplyBlockedComplexRestrictScalars R i).X j =
      (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
        (ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i)) := by
  unfold simplyBlockedComplexRestrictScalars
  exact congrArg (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
    (G.simplyBlockedComplex_X R i j)

/-- The unique differential of the restricted simply blocked complex. -/
@[simp]
theorem simplyBlockedComplexRestrictScalars_d :
    (G.simplyBlockedComplexRestrictScalars R i).d () () =
      eqToHom (G.simplyBlockedComplexRestrictScalars_X R i ()) ≫
        (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).map
          (ModuleCat.ofHom (G.simplyBlockedDifferential R i)) ≫
        eqToHom (G.simplyBlockedComplexRestrictScalars_X R i ()).symm := by
  unfold simplyBlockedComplexRestrictScalars
  rw [Functor.mapHomologicalComplex_obj_d, G.simplyBlockedComplex_d R i, Functor.map_comp,
    Functor.map_comp, eqToHom_map, eqToHom_map]

omit [CharP R 2] in
/-- Specialization intertwines the unblocked and the specialized differential. -/
theorem simplyBlockedSpecializationHom_comm :
    simplyBlockedSpecializationHom R i ≫
        (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).map
          (ModuleCat.ofHom (G.simplyBlockedDifferential R i)) =
      ModuleCat.ofHom (G.unblockedDifferential R) ≫ simplyBlockedSpecializationHom R i :=
  ModuleCat.hom_ext (LinearMap.ext fun c =>
    (G.simplyBlockedSpecialization_unblockedDifferential R i c).symm)

/-- Coefficientwise specialization at `V_i = 0` as a chain map from the unblocked complex to the
restricted simply blocked complex. -/
noncomputable def simplyBlockedSpecializationChainHom :
    G.unblockedComplex R ⟶ G.simplyBlockedComplexRestrictScalars R i where
  f j := eqToHom (G.unblockedComplex_X R j) ≫ simplyBlockedSpecializationHom R i ≫
    eqToHom (G.simplyBlockedComplexRestrictScalars_X R i j).symm
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    simp only [unblockedComplex_d, simplyBlockedComplexRestrictScalars_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (simplyBlockedSpecializationHom R i),
      ← Category.assoc (ModuleCat.ofHom (G.unblockedDifferential R)),
      G.simplyBlockedSpecializationHom_comm R i]

/-- The component of the specialization chain map. -/
@[simp]
theorem simplyBlockedSpecializationChainHom_f (j : Unit) :
    (G.simplyBlockedSpecializationChainHom R i).f j =
      eqToHom (G.unblockedComplex_X R j) ≫ simplyBlockedSpecializationHom R i ≫
        eqToHom (G.simplyBlockedComplexRestrictScalars_X R i j).symm :=
  (rfl)

/-- The short complex of complexes given by multiplication by `V_i` and specialization at
`V_i = 0`. -/
noncomputable def simplyBlockedShortComplex :
    ShortComplex
      (HomologicalComplex (ModuleCat (MvPolynomial (Fin n) R)) (ComplexShape.refl Unit)) :=
  ShortComplex.mk ((MvPolynomial.X i : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R))
    (G.simplyBlockedSpecializationChainHom R i) (by
      refine HomologicalComplex.hom_ext _ _ fun j => ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
        Linear.smul_comp, Category.id_comp, simplyBlockedSpecializationChainHom_f,
        ← Linear.comp_smul, ← Linear.smul_comp, X_smul_simplyBlockedSpecializationHom_eq_zero,
        Limits.zero_comp, Limits.comp_zero, HomologicalComplex.zero_f])

/-- The left-hand complex of the specialization sequence is `GC⁻(G)`. -/
@[simp]
theorem simplyBlockedShortComplex_X₁ :
    (G.simplyBlockedShortComplex R i).X₁ = G.unblockedComplex R :=
  (rfl)

/-- The middle complex of the specialization sequence is `GC⁻(G)`. -/
@[simp]
theorem simplyBlockedShortComplex_X₂ :
    (G.simplyBlockedShortComplex R i).X₂ = G.unblockedComplex R :=
  (rfl)

/-- The right-hand complex of the specialization sequence is the restricted simply blocked
complex. -/
@[simp]
theorem simplyBlockedShortComplex_X₃ :
    (G.simplyBlockedShortComplex R i).X₃ = G.simplyBlockedComplexRestrictScalars R i :=
  (rfl)

/-- The first map of the specialization sequence is multiplication by `V_i`. -/
@[simp]
theorem simplyBlockedShortComplex_f :
    eqToHom (G.simplyBlockedShortComplex_X₁ R i).symm ≫
        (G.simplyBlockedShortComplex R i).f ≫
        eqToHom (G.simplyBlockedShortComplex_X₂ R i) =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R) := by
  unfold simplyBlockedShortComplex
  simp

/-- The second map of the specialization sequence is specialization at `V_i = 0`. -/
@[simp]
theorem simplyBlockedShortComplex_g :
    eqToHom (G.simplyBlockedShortComplex_X₂ R i).symm ≫
        (G.simplyBlockedShortComplex R i).g ≫
        eqToHom (G.simplyBlockedShortComplex_X₃ R i) =
      G.simplyBlockedSpecializationChainHom R i := by
  unfold simplyBlockedShortComplex
  simp

/-- The module-level short complex underlying the sequence of complexes. -/
private noncomputable def simplyBlockedShortComplexModule :
    ShortComplex (ModuleCat (MvPolynomial (Fin n) R)) :=
  ShortComplex.mk ((MvPolynomial.X i : MvPolynomial (Fin n) R) •
      𝟙 (ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n)))
    (simplyBlockedSpecializationHom R i) (by
      rw [Linear.smul_comp, Category.id_comp, X_smul_simplyBlockedSpecializationHom_eq_zero])

omit [CharP R 2] in
private theorem simplyBlockedShortComplexModule_shortExact :
    (simplyBlockedShortComplexModule R i).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact exact_X_smul_simplyBlockedSpecialization R i
  · exact X_smul_gridChainMinus_injective R i
  · exact simplyBlockedSpecialization_surjective R i

/-- In its only degree, the short complex of complexes is the module-level short complex. -/
private noncomputable def simplyBlockedShortComplexEvalIso (j : Unit) :
    (G.simplyBlockedShortComplex R i).map (HomologicalComplex.eval _ _ j) ≅
      simplyBlockedShortComplexModule R i :=
  ShortComplex.isoMk (eqToIso (G.unblockedComplex_X R j)) (eqToIso (G.unblockedComplex_X R j))
    (eqToIso (G.simplyBlockedComplexRestrictScalars_X R i j))
    (by simp [simplyBlockedShortComplex, simplyBlockedShortComplexModule])
    (by
      simp only [ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g,
        HomologicalComplex.eval_map, simplyBlockedShortComplex,
        simplyBlockedSpecializationChainHom_f, simplyBlockedShortComplexModule, eqToIso.hom,
        Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

/-- **The specialization sequence is short exact.** Multiplication by `V_i` is injective on
`GC⁻(G)`, specialization at `V_i = 0` is surjective, and the chains it kills are exactly the
multiples of `V_i`. -/
theorem simplyBlockedShortComplex_shortExact :
    (G.simplyBlockedShortComplex R i).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun j =>
    ShortComplex.shortExact_of_iso (G.simplyBlockedShortComplexEvalIso R i j).symm
      (simplyBlockedShortComplexModule_shortExact R i)

/-! ### The long exact sequence -/

/-- The homology of the restricted simply blocked complex is the homology of the simply blocked
complex with its scalars restricted: restriction of scalars is exact. -/
noncomputable def simplyBlockedHomologyRestrictScalarsIso :
    (G.simplyBlockedComplexRestrictScalars R i).homology () ≅
      (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
        ((G.simplyBlockedComplex R i).homology ()) :=
  ((G.simplyBlockedComplex R i).sc ()).mapHomologyIso
    (ModuleCat.restrictScalars (simplyBlockedRingHom R i))

/-- The map on homology induced by blocking the `O`-marking of column `i`, from `GH⁻(G)` to the
homology of the specialized complex. -/
noncomputable def simplyBlockedHomologyMap :
    G.unblockedHomology R ⟶ (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
      ((G.simplyBlockedComplex R i).homology ()) :=
  HomologicalComplex.homologyMap (G.simplyBlockedSpecializationChainHom R i) () ≫
    (G.simplyBlockedHomologyRestrictScalarsIso R i).hom

/-- The connecting map of the specialization sequence, from the homology of the specialized
complex back to `GH⁻(G)`. -/
noncomputable def simplyBlockedHomologyδ :
    (ModuleCat.restrictScalars (simplyBlockedRingHom R i)).obj
        ((G.simplyBlockedComplex R i).homology ()) ⟶ G.unblockedHomology R :=
  (G.simplyBlockedHomologyRestrictScalarsIso R i).inv ≫
    (G.simplyBlockedShortComplex_shortExact R i).δ () () (ComplexShape.refl_rel ())

/-- Multiplication by `V_i` on the unblocked complex induces multiplication by `V_i` on its
homology. -/
theorem homologyMap_X_smul_id :
    HomologicalComplex.homologyMap
        ((MvPolynomial.X i : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedComplex R)) () =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • 𝟙 (G.unblockedHomology R) := by
  rw [HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id]

private theorem injective_simplyBlockedHomologyRestrictScalarsIso_hom :
    Function.Injective (G.simplyBlockedHomologyRestrictScalarsIso R i).hom.hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

private theorem surjective_simplyBlockedHomologyRestrictScalarsIso_inv :
    Function.Surjective (G.simplyBlockedHomologyRestrictScalarsIso R i).inv.hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- **Exactness at the middle `GH⁻(G)`**: a class killed by blocking the `O`-marking of column
`i` is a multiple of `V_i`. -/
theorem exact_X_smul_simplyBlockedHomologyMap :
    Function.Exact
      (fun x : G.unblockedHomology R => (MvPolynomial.X i : MvPolynomial (Fin n) R) • x)
      (G.simplyBlockedHomologyMap R i).hom := by
  have h := (G.simplyBlockedShortComplex_shortExact R i).homology_exact₂ ()
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  unfold simplyBlockedShortComplex at h
  simp only [G.homologyMap_X_smul_id R i] at h
  simp only [simplyBlockedHomologyMap, ModuleCat.hom_comp]
  exact ((G.injective_simplyBlockedHomologyRestrictScalarsIso_hom R i).comp_exact_iff_exact).mpr h

/-- **Exactness at the simply blocked homology**: a class killed by the connecting map comes
from `GH⁻(G)`. -/
theorem exact_simplyBlockedHomologyMap_δ :
    Function.Exact (G.simplyBlockedHomologyMap R i).hom (G.simplyBlockedHomologyδ R i).hom := by
  have h := (G.simplyBlockedShortComplex_shortExact R i).homology_exact₃ () ()
    (ComplexShape.refl_rel ())
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  unfold simplyBlockedShortComplex at h
  simp only [simplyBlockedHomologyMap, simplyBlockedHomologyδ, ModuleCat.hom_comp]
  exact (LinearEquiv.conj_exact_iff_exact _ _
    (G.simplyBlockedHomologyRestrictScalarsIso R i).toLinearEquiv).mpr h

/-- **Exactness at the outer `GH⁻(G)`**: a class annihilated by `V_i` is in the image of the
connecting map. -/
theorem exact_simplyBlockedHomologyδ_X_smul :
    Function.Exact (G.simplyBlockedHomologyδ R i).hom
      (fun x : G.unblockedHomology R => (MvPolynomial.X i : MvPolynomial (Fin n) R) • x) := by
  have h := (G.simplyBlockedShortComplex_shortExact R i).homology_exact₁ () ()
    (ComplexShape.refl_rel ())
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  unfold simplyBlockedShortComplex at h
  simp only [G.homologyMap_X_smul_id R i] at h
  simp only [simplyBlockedHomologyδ]
  exact ((G.surjective_simplyBlockedHomologyRestrictScalarsIso_inv R i).comp_exact_iff_exact).mpr h

namespace IsKnot

variable {G R}

/-- **Exactness at the middle `GH⁻(G)` for a knot grid**: a class killed by blocking the
`O`-marking of column `i` is a multiple of `U`. -/
theorem exact_X_smul_simplyBlockedHomologyMap (hG : G.IsKnot) (i : Fin n) :
    letI := hG.unblockedHomologyModule R
    Function.Exact
      (fun x : G.unblockedHomology R => (Polynomial.X : Polynomial R) • x)
      ((G.simplyBlockedHomologyMap R i).hom :
        G.unblockedHomology R → hG.simplyBlockedHomology R i) := by
  let _ := hG.unblockedHomologyModule R
  simpa only [hG.X_smul_unblockedHomology i] using
    G.exact_X_smul_simplyBlockedHomologyMap R i

/-- **Exactness at simply blocked homology for a knot grid**: a class killed by the connecting
map comes from `GH⁻(G)`. -/
theorem exact_simplyBlockedHomologyMap_δ (hG : G.IsKnot) (i : Fin n) :
    Function.Exact
      ((G.simplyBlockedHomologyMap R i).hom :
        G.unblockedHomology R → hG.simplyBlockedHomology R i)
      ((G.simplyBlockedHomologyδ R i).hom :
        hG.simplyBlockedHomology R i → G.unblockedHomology R) :=
  G.exact_simplyBlockedHomologyMap_δ R i

/-- **Exactness at the outer `GH⁻(G)` for a knot grid**: a class annihilated by `U` is in the
image of the connecting map. -/
theorem exact_simplyBlockedHomologyδ_X_smul (hG : G.IsKnot) (i : Fin n) :
    letI := hG.unblockedHomologyModule R
    Function.Exact
      ((G.simplyBlockedHomologyδ R i).hom :
        hG.simplyBlockedHomology R i → G.unblockedHomology R)
      (fun x : G.unblockedHomology R => (Polynomial.X : Polynomial R) • x) := by
  let _ := hG.unblockedHomologyModule R
  simpa only [hG.X_smul_unblockedHomology i] using
    G.exact_simplyBlockedHomologyδ_X_smul R i

end IsKnot

end GridDiagram

end TauCeti
