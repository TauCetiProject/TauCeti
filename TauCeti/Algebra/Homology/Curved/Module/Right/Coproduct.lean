/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Coproducts of curved differential graded right modules

The external direct sum of a family of curved right modules over one curved DG algebra, with the
componentwise grading, right action and differential, is again a curved right module of the same
curvature. Its summand inclusions are closed morphisms, and it is the coproduct of the family in
the closed degree-zero category.

The quotient functor to the curved homotopy category carries this coproduct to a coproduct. A
morphism out of the direct sum in the homotopy category lifts to a closed morphism by fullness of
the quotient functor. For uniqueness, odd homotopies chosen on the summands glue, through the
direct-sum universal property, to an odd homotopy on the direct sum. Hence the curved homotopy
category has all coproducts indexed by `Type u`. These are the coproducts under which the
coacyclic objects of the second kind are closed.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.directSum`: the direct sum of a family of curved right modules.
* `TauCeti.CurvedDGRightModuleCat.closedDirectSumCofan`: the cofan of closed summand inclusions.
* `TauCeti.CurvedDGRightModuleCat.homotopyDirectSumCofan`: its image in the curved homotopy
  category.

## Main results

* `TauCeti.CurvedDGRightModuleCat.closedDirectSumCofanIsColimit`: the direct sum is a coproduct
  in the closed degree-zero category.
* `TauCeti.CurvedDGRightModuleCat.dgClosedToHomotopy_map_directSum_ext`: closed maps out of a
  direct sum are homotopic as soon as their restrictions to all summands are.
* `TauCeti.CurvedDGRightModuleCat.homotopyDirectSumCofanIsColimit`: the direct sum is a coproduct
  in the curved homotopy category.
* The `HasCoproducts` instances on the closed and homotopy categories, and the preservation of
  all coproducts indexed by `Type u` by the quotient functor.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic`: the
  direct-sum universal property follows the corresponding construction for graded modules.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uM uJ uN

section Objects

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {J : Type uJ}

/-- The direct sum of a family of curved right modules, with componentwise grading, right action
and differential. -/
@[expose, implicit_reducible]
noncomputable def directSum (M : J → CurvedDGRightModuleCat.{uR, uA, uM} h) :
    CurvedDGRightModuleCat.{uR, uA, max uJ uM} h := by
  let G := InternalGrading.directSum fun j ↦ InternalGrading.ofDecomposition (M j).grading
  letI : DirectSum.Decomposition G.piece := G.isInternal.chooseDecomposition
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece :=
    ⟨fun {_ _} _ _ ha hx ↦ by
      simp only [G, InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff,
        InternalGrading.ofDecomposition_piece] at hx ⊢
      exact fun j ↦ SetLike.GradedSMul.smul_mem ha (hx j)⟩
  refine
    { carrier := ⨁ j, M j
      grading := G.piece
      differential := DirectSum.lmap fun j ↦ (M j).differential
      isCurvedDGRightModule := ⟨?_, ?_, ?_⟩ }
  · rw [LinearMap.isHomogeneous_def]
    intro p x hx
    simp only [G, InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff,
      InternalGrading.ofDecomposition_piece, DirectSum.lmap_apply] at hx ⊢
    exact fun j ↦ (M j).isCurvedDGRightModule.isHomogeneous.map_mem (hx j)
  · intro q x hx a
    simp only [G, InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff,
      InternalGrading.ofDecomposition_piece] at hx
    ext j
    simpa only [DirectSum.add_apply, Units.smul_def, DirectSum.smul_apply,
      DirectSum.lmap_apply] using (M j).isCurvedDGRightModule.leibniz (hx j) a
  · intro x
    ext j
    simpa only [DirectSum.smul_apply, DirectSum.lmap_apply] using
      (M j).isCurvedDGRightModule.sq_eq (x j)

variable (M : J → CurvedDGRightModuleCat.{uR, uA, uM} h)

/-- The homogeneous pieces of the direct sum are those of the direct-sum grading. -/
theorem directSum_grading :
    (directSum M).grading =
      InternalGrading.directSumPiece fun j ↦ InternalGrading.ofDecomposition (M j).grading :=
  funext fun p ↦ InternalGrading.directSum_piece _ p

/-- Membership in a homogeneous piece of the direct sum is componentwise. -/
@[simp]
theorem mem_directSum_grading_iff (p : ℤ) (x : ⨁ j, M j) :
    x ∈ (directSum M).grading p ↔ ∀ j, x j ∈ (M j).grading p := by
  rw [directSum_grading]
  simpa only [InternalGrading.ofDecomposition_piece] using
    InternalGrading.mem_directSumPiece_iff
      (fun j ↦ InternalGrading.ofDecomposition (M j).grading) p x

/-- The differential of the direct sum is componentwise. -/
theorem directSum_differential :
    (directSum M).differential = DirectSum.lmap fun j ↦ (M j).differential :=
  (rfl)

/-- Each component of the direct-sum differential is the differential of that summand. The
coercion to functions is written out because the carrier of `directSum M` is not syntactically a
function type; it is the one `DirectSum.ext` produces. -/
@[simp]
theorem directSum_differential_apply (x : ⨁ j, M j) (j : J) :
    DFunLike.coe (F := Π₀ j, M j) ((directSum M).differential x) j = (M j).differential (x j) :=
  (rfl)

/-- The differential of the direct sum preserves each summand. -/
@[simp]
theorem directSum_differential_of [DecidableEq J] (j : J) (x : M j) :
    (directSum M).differential (DirectSum.of (fun j ↦ M j) j x) =
      DirectSum.of (fun j ↦ M j) j ((M j).differential x) := by
  rw [directSum_differential, ← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R,
    DirectSum.lmap_lof]

/-- Precomposing a direct-sum universal map with the differential of the direct sum gives the
universal map of the summand maps precomposed with the summand differentials. -/
theorem toModule_comp_directSum_differential [DecidableEq J] {N : Type uN} [AddCommGroup N]
    [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N] (φ : ∀ j, M j →ₗ[Aᵐᵒᵖ] N) :
    (DirectSum.toModule Aᵐᵒᵖ J N φ).restrictScalars R ∘ₗ (directSum M).differential =
      DirectSum.toModule R J N fun j ↦ (φ j).restrictScalars R ∘ₗ (M j).differential := by
  refine DirectSum.linearMap_ext R fun j ↦ LinearMap.ext fun y ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, DirectSum.toModule_lof,
    directSum_differential, DirectSum.lmap_lof]
  exact DirectSum.toModule_lof Aᵐᵒᵖ j _

end Objects

universe u

-- The closed category, the quotient and its object wrappers keep the curved-module carriers.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {J : Type u} (M : J → CurvedDGRightModuleCat.{u, u, u} h)

section Closed

/-- The direct-sum universal map of a family of maps changing degree by `q` changes degree by
`q`. -/
private theorem toModule_mem_grading [DecidableEq J] {N : CurvedDGRightModuleCat.{u, u, u} h}
    (φ : ∀ j, M j →ₗ[Aᵐᵒᵖ] N) {q : ℤ}
    (hφ : ∀ j p (x : M j), x ∈ (M j).grading p → φ j x ∈ N.grading (p + q))
    {p : ℤ} {x : ⨁ j, M j} (hx : x ∈ (directSum M).grading p) :
    DirectSum.toModule Aᵐᵒᵖ J N φ x ∈ N.grading (p + q) :=
  InternalGrading.toModule_mem_of_mem_directSumPiece
    (fun j ↦ InternalGrading.ofDecomposition (M j).grading) N.grading φ
    (fun j x hx ↦ hφ j p x (by rwa [InternalGrading.ofDecomposition_piece] at hx))
    (by rwa [directSum_grading] at hx)

/-- The inclusion of a summand into the direct sum, as a closed morphism. -/
noncomputable def closedDirectSumι (j : J) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (directSum M) := by
  classical
  exact closedHomOf (DirectSum.lof Aᵐᵒᵖ J (fun j ↦ M j) j)
    (fun p x hx ↦ by
      rw [directSum_grading]
      exact InternalGrading.lof_mem_directSumPiece
          (fun j ↦ InternalGrading.ofDecomposition (M j).grading) p j
          ⟨x, by rwa [InternalGrading.ofDecomposition_piece]⟩)
    (fun x ↦ directSum_differential_of M j x)

/-- The closed summand inclusion is the direct-sum inclusion. -/
@[simp]
theorem closedHom_closedDirectSumι [hJ : DecidableEq J] (j : J) :
    closedHom (closedDirectSumι M j) = DirectSum.lof Aᵐᵒᵖ J (fun j ↦ M j) j := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  exact closedHom_closedHomOf _ _ _

variable {M} in
/-- The closed morphism out of the direct sum restricting to a prescribed family of closed
morphisms on the summands. -/
noncomputable def closedDirectSumDesc {N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (directSum M) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N := by
  classical
  exact closedHomOf (DirectSum.toModule Aᵐᵒᵖ J N fun j ↦ closedHom (f j))
    (fun p x hx ↦ by
      simpa only [add_zero] using toModule_mem_grading M (fun j ↦ closedHom (f j)) (q := 0)
        (fun j p x hx ↦ by simpa only [add_zero] using closedHom_mem (f j) hx) hx)
    (fun x ↦ by
      let F := DirectSum.toModule Aᵐᵒᵖ J N fun j ↦ closedHom (f j)
      refine LinearMap.congr_fun (?_ : N.differential ∘ₗ F.restrictScalars R =
        F.restrictScalars R ∘ₗ (directSum M).differential) x
      rw [toModule_comp_directSum_differential]
      refine DirectSum.linearMap_ext R fun j ↦ LinearMap.ext fun y ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, DirectSum.toModule_lof]
      rw [DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of Aᵐᵒᵖ, DirectSum.toModule_lof]
      exact differential_closedHom (f j) y)

/-- The closed morphism out of the direct sum is the direct-sum universal map. -/
@[simp]
theorem closedHom_closedDirectSumDesc [hJ : DecidableEq J] {N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom (closedDirectSumDesc f) = DirectSum.toModule Aᵐᵒᵖ J N fun j ↦ closedHom (f j) := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  exact closedHom_closedHomOf _ _ _

/-- The closed morphism out of the direct sum restricts to the prescribed morphisms. -/
@[reassoc (attr := simp)]
theorem closedDirectSumι_desc {N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) (j : J) :
    closedDirectSumι M j ≫ closedDirectSumDesc f = f j := by
  classical
  apply closedHom_ext
  intro x
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_closedDirectSumι,
    closedHom_closedDirectSumDesc, DirectSum.toModule_lof]

/-- Closed morphisms out of the direct sum are determined by their restrictions to the
summands. -/
theorem closedDirectSum_hom_ext {N : CurvedDGRightModuleCat.{u, u, u} h}
    {f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (directSum M) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N}
    (hfg : ∀ j, closedDirectSumι M j ≫ f = closedDirectSumι M j ≫ g) : f = g := by
  classical
  apply closedHom_injective
  apply DirectSum.linearMap_ext
  intro j
  ext x
  simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_closedDirectSumι] using
    congrArg (fun k ↦ closedHom k x) (hfg j)

/-- The cofan of closed summand inclusions into the direct sum. -/
noncomputable abbrev closedDirectSumCofan :
    Cofan fun j ↦ ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) :=
  Cofan.mk (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (directSum M))
    (closedDirectSumι M)

/-- The direct sum is the coproduct in the closed degree-zero category. -/
noncomputable def closedDirectSumCofanIsColimit : IsColimit (closedDirectSumCofan M) :=
  Cofan.IsColimit.mk _ (fun s ↦ closedDirectSumDesc s.inj)
    (fun s j ↦ closedDirectSumι_desc M s.inj j)
    (fun s _ hm ↦ closedDirectSum_hom_ext M fun j ↦
      (hm j).trans (closedDirectSumι_desc M s.inj j).symm)

noncomputable instance
    (X : J → ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) :
    HasCoproduct X :=
  HasColimit.mk
    { cocone := closedDirectSumCofan fun j ↦ ForgetEnrichment.to _ (X j)
      isColimit := closedDirectSumCofanIsColimit _ }

instance : HasCoproducts.{u}
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  fun _ ↦ ⟨fun _ ↦ hasColimit_of_iso Discrete.natIsoFunctor⟩

end Closed

section Homotopy

/-- Two closed morphisms out of a direct sum are homotopic as soon as their restrictions to all
summands are: odd homotopies on the summands glue to an odd homotopy on the direct sum. -/
theorem dgClosedToHomotopy_map_directSum_ext {N : CurvedDGRightModuleCat.{u, u, u} h}
    {f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (directSum M) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N}
    (hfg : ∀ j, (dgClosedToHomotopy R).map (closedDirectSumι M j ≫ f) =
      (dgClosedToHomotopy R).map (closedDirectSumι M j ≫ g)) :
    (dgClosedToHomotopy R).map f = (dgClosedToHomotopy R).map g := by
  classical
  simp only [quotient_map_eq_iff_exists_homotopy, closedHom_comp, LinearMap.comp_apply,
    closedHom_closedDirectSumι] at hfg ⊢
  choose k hk using hfg
  let K := DirectSum.toModule Aᵐᵒᵖ J N fun j ↦ (k j).1
  refine ⟨⟨K, ?_⟩, fun x ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    exact toModule_mem_grading M (fun j ↦ (k j).1)
      (fun j p y hy ↦ (dgRightModuleCochains.mem_iff.mp (k j).2).map_mem hy) hx
  · refine LinearMap.congr_fun (?_ : (closedHom f).restrictScalars R -
      (closedHom g).restrictScalars R =
        (N.differential ∘ₗ K.restrictScalars R : directSum M →ₗ[R] N) +
          K.restrictScalars R ∘ₗ (directSum M).differential) x
    rw [toModule_comp_directSum_differential]
    refine DirectSum.linearMap_ext R fun j ↦ LinearMap.ext fun y ↦ ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, DirectSum.toModule_lof]
    rw [DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of Aᵐᵒᵖ, DirectSum.toModule_lof]
    exact hk j y

/-- The cofan of homotopy classes of the summand inclusions into the direct sum. -/
noncomputable abbrev homotopyDirectSumCofan : Cofan fun j ↦ DGHomotopyCategory.of R (M j) :=
  Cofan.mk (DGHomotopyCategory.of R (directSum M))
    fun j ↦ (dgClosedToHomotopy R).map (closedDirectSumι M j)

/-- The direct sum is the coproduct in the curved homotopy category. -/
noncomputable def homotopyDirectSumCofanIsColimit : IsColimit (homotopyDirectSumCofan M) :=
  Cofan.IsColimit.mk _
    (fun s ↦ (dgClosedToHomotopy R).map (closedDirectSumDesc fun j ↦
      (dgClosedToHomotopy R).preimage
        (X := ForgetEnrichment.of _ (M j))
        (Y := ForgetEnrichment.of _ (DGHomotopyCategory.underlying R s.pt)) (s.inj j)))
    (fun s j ↦ by
      simp only [cofan_mk_inj, ← Functor.map_comp, closedDirectSumι_desc,
        Functor.map_preimage])
    (fun s m hm ↦ by
      obtain ⟨m, rfl⟩ := (dgClosedToHomotopy R).map_surjective
        (X := ForgetEnrichment.of _ (directSum M))
        (Y := ForgetEnrichment.of _ (DGHomotopyCategory.underlying R s.pt)) m
      refine dgClosedToHomotopy_map_directSum_ext M fun j ↦ ?_
      rw [closedDirectSumι_desc, Functor.map_preimage, Functor.map_comp]
      exact hm j)

/-- The quotient functor to the curved homotopy category preserves the direct-sum coproducts. -/
instance : PreservesColimit
    (Discrete.functor fun j ↦ ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j))
    (dgClosedToHomotopy R) :=
  preservesColimit_of_preserves_colimit_cocone (closedDirectSumCofanIsColimit M)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (homotopyDirectSumCofanIsColimit M))

/-- The quotient functor to the curved homotopy category preserves all coproducts indexed by
`J`. -/
instance : PreservesColimitsOfShape (Discrete J)
    (dgClosedToHomotopy R (C := CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun {F} ↦ preservesColimit_of_iso_diagram (K₁ := Discrete.functor fun j ↦
    ForgetEnrichment.of _ (ForgetEnrichment.to (CochainComplex (ModuleCat R) ℤ) (F.obj ⟨j⟩)))
    _ (Discrete.natIsoFunctor (F := F)).symm⟩

noncomputable instance (X : J → DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    HasCoproduct X :=
  HasColimit.mk
    { cocone := homotopyDirectSumCofan fun j ↦ DGHomotopyCategory.underlying R (X j)
      isColimit := homotopyDirectSumCofanIsColimit _ }

instance : HasCoproducts.{u} (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  fun _ ↦ ⟨fun _ ↦ hasColimit_of_iso Discrete.natIsoFunctor⟩

end Homotopy

end TauCeti.CurvedDGRightModuleCat
