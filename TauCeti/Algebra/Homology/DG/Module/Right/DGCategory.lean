/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Module.Right.Composition
public import TauCeti.CategoryTheory.DG.HomComplexData
public import TauCeti.CategoryTheory.DG.HomotopyCategory

/-!
# The differential graded category of differential graded right modules

The right modules over a differential graded algebra form a differential graded category: the
Hom complex from `M` to `N` is `TauCeti.dgRightModuleHomComplex`, whose degree-`p` cochains are
the right-module maps raising internal degree by `p`, and composition of homogeneous cochains is
composition of the underlying maps.  This file installs that structure on the bundled category
`TauCeti.DGRightModuleCat` through the explicit Hom-complex data of
`TauCeti/CategoryTheory/DG/HomComplexData.lean`, and identifies the resulting differential
graded calculus with the cochain calculus already available: the differential is the graded
commutator with the module differentials, the identity is the identity cochain, and composition
in Mathlib's enriched factor order is composition of cochains twisted by the Koszul sign
`(-1) ^ (p * q)`.

The closed degree-zero morphisms of this differential graded category are exactly the morphisms
of the linear category `TauCeti.DGRightModuleCat`, compatibly with identities and composition.
Thus the ordinary category of differential graded modules is the `Z⁰` category of the
differential graded one, and its homotopy category is the `H⁰` category
`TauCeti.DGHomotopyCategory` of the differential graded one.

## Main definitions

* `TauCeti.DGRightModuleCat.homComplexData`: the Hom complexes, composition, and identities of
  differential graded right modules as explicit Hom-complex data.
* `TauCeti.DGRightModuleCat.instDGCategory`: the differential graded category of differential
  graded right modules.
* `TauCeti.DGRightModuleCat.dgHomLinearEquivCochains`: the explicit identification of homogeneous
  morphisms with right-module cochains.
* `TauCeti.DGRightModuleCat.homLinearEquivDGCycles`: morphisms of differential graded right
  modules are the closed degree-zero morphisms of the differential graded category.

## Main results

* `TauCeti.DGRightModuleCat.dgDifferential_eq`, `TauCeti.DGRightModuleCat.dgId_eq` and
  `TauCeti.DGRightModuleCat.dgComp_eq`: the differential graded calculus of the category is the
  cochain calculus, with the Koszul sign in composition.
* `TauCeti.DGRightModuleCat.homLinearEquivDGCycles_id` and
  `TauCeti.DGRightModuleCat.homLinearEquivDGCycles_comp`: the identification of morphisms with
  closed degree-zero morphisms is functorial.

## Implementation notes

The Hom complex between two modules has its terms in the universe of the modules, while the
enrichment fixes the universe of the ground ring, so the differential graded structure lives on
`DGRightModuleCat.{u, u, u} h`: ground ring, algebra, and modules share one universe.  The
composition and identity cochains of `TauCeti/Algebra/Homology/DG/Module/Right/Composition.lean`
are stated in that generality as well.

The linear equivalence `dgHomLinearEquivCochains` identifies homogeneous morphisms with
right-module cochains. Under this identification, the differential is the graded commutator,
the identity is the identity cochain, and composition carries the Koszul sign.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleCat

/-! ### The explicit Hom-complex data -/

/-- The explicit Hom-complex data of the differential graded category of right modules over `h`:
the Hom complex from `M` to `N` is `TauCeti.dgRightModuleHomComplex`, composition of homogeneous
cochains is composition of the underlying maps, in Keller's order, and the identity is the
identity cochain. -/
noncomputable def homComplexData : DGCategoryData R (DGRightModuleCat.{u, u, u} h) :=
  DGCategoryData.ofKeller
    (fun M N => dgRightModuleHomComplex M.isDGRightModule N.isDGRightModule)
    (fun {_ _ _} _ _ _ hqp => LinearMap.mk₂ R (fun g f => dgRightModuleCochains.comp g f hqp)
      (fun _ _ _ => dgRightModuleCochains.add_comp _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.smul_comp _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.comp_add _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.comp_smul _ _ _ hqp))
    (fun M => dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading))
    (fun {_ _ _ _ _ _} hqp g f => by
      subst hqp
      rw [dgRightModuleHomComplex_d_apply, dgRightModuleHomComplex_d_apply,
        dgRightModuleHomComplex_d_apply]
      exact dgRightModuleCochains.differential_comp g f)
    (fun {_ _ _ _ _ _ _ _ _ _} hrq hqp _ k g f => by
      subst hrq hqp
      exact dgRightModuleCochains.comp_assoc k g f _)
    (fun g => dgRightModuleCochains.comp_id g)
    (fun f => dgRightModuleCochains.id_comp f)

variable (M N P : DGRightModuleCat.{u, u, u} h)

/-- The Hom complex of the explicit data is the Hom complex of the two modules. -/
@[simp]
theorem homComplexData_hom :
    (homComplexData (h := h)).hom M N =
      dgRightModuleHomComplex M.isDGRightModule N.isDGRightModule :=
  (rfl)

/-! ### The differential graded category -/

/-- The differential graded category of differential graded right modules over `h`. -/
noncomputable instance instDGCategory : DGCategory R (DGRightModuleCat.{u, u, u} h) :=
  (homComplexData (h := h)).toDGCategory

/-- The Hom complex of the differential graded category of right modules is the Hom complex of
the two modules. -/
@[simp↓]
theorem dgHomComplex_eq :
    dgHomComplex R M N = dgRightModuleHomComplex M.isDGRightModule N.isDGRightModule :=
  (rfl)

/-- Homogeneous morphisms of the differential graded category, identified with right-module
cochains through the equality of their Hom complexes. -/
noncomputable def dgHomLinearEquivCochains (n : ℤ) :
    DGHom R n M N ≃ₗ[R]
      dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) n :=
  (eqToIso (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
    (dgHomComplex_eq M N))).toLinearEquiv

/-- The identification with cochains acts by transport along the equality of the degree-`n`
terms of the Hom complexes. -/
theorem dgHomLinearEquivCochains_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N n f =
      (eqToHom (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
        (dgHomComplex_eq M N))).hom f :=
  Iso.toLinearEquiv_apply _ _

/-- Transported composition in the explicit Hom-complex data is composition of cochains in
reversed order, with the Koszul sign converting Keller's factor order into Mathlib's. -/
@[simp]
theorem homComplexData_comp {p q n : ℤ} (hpq : p + q = n)
    (f : DGHom R p M N) (g : DGHom R q N P) :
    dgHomLinearEquivCochains M P n ((homComplexData (h := h)).comp p q n hpq f g) =
      (p * q).negOnePow • dgRightModuleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_comp]
  · exact congrArg (fun c : (dgRightModuleHomComplex M.isDGRightModule P.isDGRightModule).X n =>
        (p * q).negOnePow • c)
      (LinearMap.mk₂_apply R _ g f)
  all_goals assumption

/-- The transported identity of the explicit data is the identity cochain. -/
@[simp]
theorem homComplexData_id :
    dgHomLinearEquivCochains M M 0 ((homComplexData (h := h)).id M) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_id]
  · erw [eqToHom_refl]
    exact ModuleCat.id_apply _ _
  all_goals assumption

/-- The transported differential of the explicit data is the graded commutator with the module
differentials. -/
@[simp]
theorem homComplexData_d_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1)
        ((((homComplexData (h := h)).hom M N).d n (n + 1)).hom f) =
      dgRightModuleCochains.differential (hM := M.isDGRightModule) (hN := N.isDGRightModule) n
        (dgHomLinearEquivCochains M N n f) :=
  dgRightModuleHomComplex_d_apply M.isDGRightModule N.isDGRightModule n
    (dgHomLinearEquivCochains M N n f)

/-- The differential of the differential graded category of right modules is the graded
commutator with the module differentials, after transport to cochains. -/
@[simp↓]
theorem dgDifferential_eq (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1) (dgDifferential R n f) =
      dgRightModuleCochains.differential (hM := M.isDGRightModule) (hN := N.isDGRightModule) n
        (dgHomLinearEquivCochains M N n f) :=
  (congrArg (dgHomLinearEquivCochains M N (n + 1))
    (DGCategoryData.dgDifferential_toDGCategory (homComplexData (h := h)) n f)).trans
      (homComplexData_d_apply M N n f)

/-- The identity of the differential graded category of right modules transports to the identity
cochain. -/
@[simp↓]
theorem dgId_eq :
    dgHomLinearEquivCochains M M 0 (dgId R M) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading) :=
  (congrArg (dgHomLinearEquivCochains M M 0)
    (DGCategoryData.dgId_toDGCategory (homComplexData (h := h)) M)).trans (homComplexData_id M)

/-- Composition in the differential graded category of right modules is composition of cochains,
carrying the Koszul sign which converts Mathlib's enriched factor order into composition of the
underlying maps, after transport to cochains. -/
@[simp↓]
theorem dgComp_eq {p q n : ℤ} (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = n) :
    dgHomLinearEquivCochains M P n (dgComp R f g hpq) =
      (p * q).negOnePow • dgRightModuleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) :=
  (congrArg (dgHomLinearEquivCochains M P n)
    (DGCategoryData.dgComp_toDGCategory (homComplexData (h := h)) f g hpq)).trans
      (homComplexData_comp M N P hpq f g)

/-! ### Closed degree-zero morphisms -/

/-- The closed degree-zero morphisms are the preimage of the zero-cocycles of the Hom complex
under the explicit identification with cochains. -/
theorem dgCycles_eq :
    dgCycles R M N = Submodule.comap (dgHomLinearEquivCochains M N 0).toLinearMap
      (LinearMap.ker (dgRightModuleCochains.differential
        (hM := M.isDGRightModule) (hN := N.isDGRightModule) 0)) := by
  ext f
  rw [mem_dgCycles, Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap,
    ← dgDifferential_eq, LinearEquiv.map_eq_zero_iff]

/-- **Morphisms of differential graded right modules are the closed degree-zero morphisms** of the
differential graded category of right modules. -/
noncomputable def homLinearEquivDGCycles : (M ⟶ N) ≃ₗ[R] dgCycles R M N :=
  ((dgRightModuleHomLinearEquivZeroCocycles M.isDGRightModule N.isDGRightModule).trans
    ((dgHomLinearEquivCochains M N 0).ofSubmodule' (LinearMap.ker
      (dgRightModuleCochains.differential (hM := M.isDGRightModule)
        (hN := N.isDGRightModule) 0))).symm).trans
    (LinearEquiv.ofEq _ _ (dgCycles_eq M N).symm)

variable {M N P}

/-- The closed degree-zero morphism attached to a morphism of differential graded right modules
has the same underlying map. -/
@[simp]
theorem coe_homLinearEquivDGCycles_apply (f : M ⟶ N) (x : M) :
    (dgHomLinearEquivCochains M N 0 (homLinearEquivDGCycles M N f)).1 x = f x := by
  simp only [homLinearEquivDGCycles, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofSubmodule'_symm_apply, LinearEquiv.apply_symm_apply]
  exact dgRightModuleHomLinearEquivZeroCocycles_apply M.isDGRightModule N.isDGRightModule f x

/-- The morphism of differential graded right modules attached to a closed degree-zero morphism
has the same underlying map. -/
@[simp]
theorem homLinearEquivDGCycles_symm_apply (f : dgCycles R M N) (x : M) :
    (homLinearEquivDGCycles M N).symm f x =
      (dgHomLinearEquivCochains M N 0 f).1 x := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (coe_homLinearEquivDGCycles_apply ((homLinearEquivDGCycles M N).symm f) x).symm

/-- The identity morphism corresponds to the identity of the differential graded category. -/
@[simp]
theorem homLinearEquivDGCycles_id :
    (homLinearEquivDGCycles M M (𝟙 M) : DGHom R 0 M M) = dgId R M := by
  apply (dgHomLinearEquivCochains M M 0).injective
  rw [dgId_eq]
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  rw [coe_homLinearEquivDGCycles_apply, id_apply, dgRightModuleCochains.id_apply]

/-- Composition of morphisms corresponds to composition of closed degree-zero morphisms in the
differential graded category. -/
@[simp]
theorem homLinearEquivDGCycles_comp (f : M ⟶ N) (g : N ⟶ P) :
    homLinearEquivDGCycles M P (f ≫ g) =
      dgCyclesComp R M N P (homLinearEquivDGCycles M N f) (homLinearEquivDGCycles N P g) := by
  apply Subtype.ext
  apply (dgHomLinearEquivCochains M P 0).injective
  rw [coe_dgCyclesComp, dgCompZero_def, dgComp_eq, mul_zero, Int.negOnePow_zero, one_smul]
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  rw [coe_homLinearEquivDGCycles_apply, comp_apply, dgRightModuleCochains.comp_apply,
    coe_homLinearEquivDGCycles_apply, coe_homLinearEquivDGCycles_apply]

end DGRightModuleCat

end TauCeti
