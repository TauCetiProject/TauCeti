/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Homology.Periodic.ModuleCat

/-!
# The dual of a two-periodic complex of modules

Let `C` be a two-periodic complex of modules over a commutative ring `R`, with differentials
`d₀ : C₀ → C₁` and `d₁ : C₁ → C₀`. Transposing both differentials gives a two-periodic complex
`C^*` (`HomologicalComplex.parityDual`) with `C^*ᵢ = Hom_R(Cᵢ, R)` in the same degrees, and
differentials

`d₁ᵗ : C₀^* → C₁^*`, `d₀ᵗ : C₁^* → C₀^*`.

Over `ℤ`, the dual of the complex in degree `i` would sit in degree `-i`; in `ZMod 2` every degree
is its own negative, so the dual is again a complex for the shape `ComplexShape.up (ZMod 2)`, and
its differential from degree `i` to degree `j` is the transpose of the differential of `C` from
degree `j` to degree `i`. No sign is introduced: the transposes of the two differentials compose to
zero because the differentials do.

Over a field the image of a transpose is the annihilator of the kernel, and its kernel is the
annihilator of the image. Since a subspace is determined by its annihilator, the dual is exact
in a degree exactly when `C` is (`HomologicalComplex.exactAt_parityDual_iff`), and acyclic exactly
when `C` is (`HomologicalComplex.acyclic_parityDual_iff`). No finiteness is needed.

Dualizing reverses the direction of the differentials. For Morse and Floer complexes graded
modulo two, whose differentials count trajectories between generators, the transposed differentials
count the same trajectories read in the opposite direction.

## Main declarations

* `HomologicalComplex.parityDual`: the dual of a two-periodic complex of modules.
* `HomologicalComplex.parityDualBasis`: the dual bases of the dual of a based two-periodic
  complex.
* `HomologicalComplex.exactAt_parityDual_iff`, `HomologicalComplex.acyclic_parityDual_iff`: over a
  field, the dual is exact, or acyclic, exactly when `C` is.
-/

public section

open CategoryTheory

namespace HomologicalComplex

universe u

section CommRing

variable {R : Type u} [CommRing R]
  (C : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up (ZMod 2)))

/-- The dual of a two-periodic complex of modules: the duals `Hom_R(Cᵢ, R)` in the same degrees,
with the differential from degree `i` to degree `j` the transpose of the differential of `C` from
degree `j` to degree `i`. -/
@[expose] def parityDual : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up (ZMod 2)) where
  X i := ModuleCat.of R (Module.Dual R (C.X i))
  d i j := ModuleCat.ofHom (C.d j i).hom.dualMap
  shape i j hij := by
    have hji : ¬(ComplexShape.up (ZMod 2)).Rel j i := fun hji ↦
      hij (by rw [← hji]; exact CharTwo.add_cancel_right j 1)
    ext
    simp [C.shape j i hji]
  d_comp_d' i j k _ _ := by
    ext φ x
    simp [d_comp_d_apply]

/-- The objects of the dual of a two-periodic complex are the duals of its objects. -/
theorem parityDual_X (i : ZMod 2) : C.parityDual.X i = ModuleCat.of R (Module.Dual R (C.X i)) :=
  rfl

/-- The differential of the dual from degree `i` to degree `j` is the transpose of the
differential of `C` from degree `j` to degree `i`. -/
@[simp]
theorem parityDual_d_hom (i j : ZMod 2) : (C.parityDual.d i j).hom = (C.d j i).hom.dualMap :=
  rfl

variable {C} {n : ZMod 2 → ℕ}

/-- The dual bases of the dual of a based two-periodic complex: in each degree, the dual basis of
the basis of `C`. -/
@[expose] noncomputable def parityDualBasis (c : ∀ i, Module.Basis (Fin (n i)) R (C.X i))
    (i : ZMod 2) : Module.Basis (Fin (n i)) R (C.parityDual.X i) :=
  (c i).dualBasis

/-- The vectors of the dual bases are the dual vectors of the bases of `C`. -/
@[simp]
theorem parityDualBasis_apply (c : ∀ i, Module.Basis (Fin (n i)) R (C.X i)) (i : ZMod 2)
    (l : Fin (n i)) : parityDualBasis c i l = (c i).dualBasis l :=
  rfl

end CommRing

section Field

variable {K : Type u} [Field K]
  (C : HomologicalComplex (ModuleCat.{u} K) (ComplexShape.up (ZMod 2)))

/-- Over a field, the dual of a two-periodic complex is exact in a degree exactly when the complex
is. -/
@[simp]
theorem exactAt_parityDual_iff (j : ZMod 2) : C.parityDual.ExactAt j ↔ C.ExactAt j := by
  rw [C.parityDual.exactAt_iff_range_eq_ker_zmod_two rfl, C.exactAt_iff_range_eq_ker_zmod_two rfl,
    parityDual_d_hom, parityDual_d_hom]
  -- The image and kernel of a transpose are the annihilators of the kernel and image of the
  -- differential, and annihilators determine the subspaces.
  exact (Eq.congr (LinearMap.range_dualMap_eq_dualAnnihilator_ker _)
    (LinearMap.ker_dualMap_eq_dualAnnihilator_range _)).trans
    (Subspace.dualAnnihilator_inj.trans eq_comm)

/-- Over a field, the dual of a two-periodic complex is acyclic exactly when the complex is. -/
@[simp]
theorem acyclic_parityDual_iff : C.parityDual.Acyclic ↔ C.Acyclic :=
  forall_congr' C.exactAt_parityDual_iff

end Field

end HomologicalComplex
