/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Composition
public import TauCeti.CategoryTheory.DG.ClosedCategory
public import TauCeti.CategoryTheory.DG.HomComplexData

/-!
# The differential graded category of curved differential graded right modules

The right modules over a curved differential graded algebra `(A, d, w)` form a differential
graded category.  The Hom complex from `M` to `N` is `TauCeti.curvedDGRightModuleHomComplex`,
whose degree-`p` cochains are the right-module maps raising internal degree by `p`, with the
graded commutator `f ↦ dN ∘ f - (-1) ^ p f ∘ dM` as differential; composition of homogeneous
cochains is composition of the underlying maps.  An individual curved module has no cohomology in
general, since its differential squares to the curvature action rather than to zero, but the Hom
differential squares to zero because source and target have the *same* curvature, and the graded
Leibniz rule for composition holds verbatim.  This file installs the differential
graded structure on the bundled curved right modules `TauCeti.CurvedDGRightModuleCat` through the
explicit Hom-complex data of `TauCeti/CategoryTheory/DG/HomComplexData.lean`, and identifies its
calculus with the cochain calculus: the differential is the graded commutator with the module
differentials, the identity is the identity cochain, and composition in Mathlib's enriched factor
order is composition of cochains twisted by the Koszul sign `(-1) ^ (p * q)`.

The generic constructions on a differential graded category then supply the closed morphisms and
the homotopy category of curved modules.  The closed degree-zero morphisms `TauCeti.dgCycles`
are the right-module maps commuting with the differentials; they are the morphisms of the
**closed degree-zero category**, Mathlib's underlying category `CategoryTheory.ForgetEnrichment`
of the enrichment, and this file identifies those morphisms with the zero-cocycles of the curved
Hom complex.  The degree-zero boundaries `TauCeti.dgBoundaries` are the maps `dN ∘ k + k ∘ dM`
for an **odd homotopy** `k`, a right-module map of degree `-1`: this is the degree `-1` case of
the graded commutator, whose Koszul sign `(-1) ^ (-1) = -1` turns the subtraction into an
addition.  The **curved homotopy category** is
`TauCeti.DGHomotopyCategory R (CurvedDGRightModuleCat h)`: it has the curved modules as objects
and homotopy classes of closed degree-zero morphisms as morphisms, two closed morphisms being
identified exactly when their difference is the boundary of an odd homotopy.  No homology enters:
a curved module has no cohomology in general, and the homotopy category is the quotient by
boundaries alone.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.homComplexData`: the Hom complexes, composition, and identities
  of curved differential graded right modules as explicit Hom-complex data.
* `TauCeti.CurvedDGRightModuleCat.instDGCategory`: the differential graded category of curved
  differential graded right modules.
* `TauCeti.CurvedDGRightModuleCat.dgHomLinearEquivCochains`: the explicit identification of
  homogeneous morphisms with right-module cochains.
* `TauCeti.CurvedDGRightModuleCat.dgClosedHomEquivZeroCocycles`: morphisms of the closed
  degree-zero category of curved right modules are the zero-cocycles of the curved Hom complex.

## Main results

* `TauCeti.CurvedDGRightModuleCat.dgDifferential_eq`, `TauCeti.CurvedDGRightModuleCat.dgId_eq`
  and `TauCeti.CurvedDGRightModuleCat.dgComp_eq`: the differential graded calculus of the
  category is the cochain calculus, with the Koszul sign in composition.
* `TauCeti.CurvedDGRightModuleCat.mem_dgCycles_iff`: the closed degree-zero morphisms are the
  maps commuting with the module differentials.
* `TauCeti.CurvedDGRightModuleCat.dgClosedHomEquivZeroCocycles_id` and
  `TauCeti.CurvedDGRightModuleCat.dgClosedHomEquivZeroCocycles_comp`: the identification of
  closed morphisms with zero-cocycles is functorial.
* `TauCeti.CurvedDGRightModuleCat.mem_dgBoundaries_iff`: the degree-zero boundaries are the
  boundaries `dN ∘ k + k ∘ dM` of odd homotopies.
* `TauCeti.CurvedDGRightModuleCat.homOf_eq_iff_exists_homotopy`: two closed morphisms agree in the
  curved homotopy category exactly when they are homotopic through an odd homotopy.

## Implementation notes

This module is closely adapted, declaration by declaration, from the uncurved construction in
`TauCeti/Algebra/Homology/DG/Module/Right/DGCategory.lean`: the curved Hom complex and its
differential replace the ordinary ones, and the closed degree-zero category is Mathlib's
underlying category of the enrichment rather than an independently defined linear category.

As for `TauCeti.DGRightModuleCat`, the enrichment fixes the universe of the ground ring while the
Hom complexes live in the universe of the modules, so the differential graded structure lives on
`CurvedDGRightModuleCat.{u, u, u} h`: ground ring, algebra, and modules share one universe.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Section 3.1, for curved DG modules and their homotopy category.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  His curvature is the negative of the right-module curvature used here.
* B. Keller, *Deriving DG categories*, Sections 1 and 2, for the differential graded category of
  modules.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

namespace CurvedDGRightModuleCat

/-! ### The explicit Hom-complex data -/

/-- The explicit Hom-complex data of the differential graded category of curved right modules
over `h`: the Hom complex from `M` to `N` is `TauCeti.curvedDGRightModuleHomComplex`, composition
of homogeneous cochains is composition of the underlying maps, in Keller's order, and the
identity is the identity cochain. -/
noncomputable def homComplexData : DGCategoryData R (CurvedDGRightModuleCat.{u, u, u} h) :=
  DGCategoryData.ofKeller
    (fun M N => curvedDGRightModuleHomComplex M.isCurvedDGRightModule N.isCurvedDGRightModule)
    (fun {_ _ _} _ _ _ hqp => LinearMap.mk₂ R (fun g f => dgRightModuleCochains.comp g f hqp)
      (fun _ _ _ => dgRightModuleCochains.add_comp _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.smul_comp _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.comp_add _ _ _ hqp)
      (fun _ _ _ => dgRightModuleCochains.comp_smul _ _ _ hqp))
    (fun M => dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading))
    (fun {_ _ _ _ _ _} hqp g f => by
      subst hqp
      rw [curvedDGRightModuleHomComplex_d_apply, curvedDGRightModuleHomComplex_d_apply,
        curvedDGRightModuleHomComplex_d_apply]
      exact dgRightModuleCochains.curvedDifferential_comp g f)
    (fun {_ _ _ _ _ _ _ _ _ _} hrq hqp _ k g f => by
      subst hrq hqp
      exact dgRightModuleCochains.comp_assoc k g f _)
    (fun g => dgRightModuleCochains.comp_id g)
    (fun f => dgRightModuleCochains.id_comp f)

variable (M N P : CurvedDGRightModuleCat.{u, u, u} h)

/-- The Hom complex of the explicit data is the curved Hom complex of the two modules. -/
@[simp]
theorem homComplexData_hom :
    (homComplexData (h := h)).hom M N =
      curvedDGRightModuleHomComplex M.isCurvedDGRightModule N.isCurvedDGRightModule :=
  (rfl)

/-! ### The differential graded category -/

/-- The differential graded category of curved differential graded right modules over `h`. -/
noncomputable instance instDGCategory : DGCategory R (CurvedDGRightModuleCat.{u, u, u} h) :=
  (homComplexData (h := h)).toDGCategory

/-- The Hom complex of the differential graded category of curved right modules is the curved
Hom complex of the two modules. -/
@[simp↓]
theorem dgHomComplex_eq :
    dgHomComplex R M N =
      curvedDGRightModuleHomComplex M.isCurvedDGRightModule N.isCurvedDGRightModule :=
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
  · exact congrArg (fun c : (curvedDGRightModuleHomComplex M.isCurvedDGRightModule
        P.isCurvedDGRightModule).X n => (p * q).negOnePow • c)
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
      dgRightModuleCochains.curvedDifferential (hM := M.isCurvedDGRightModule)
        (hN := N.isCurvedDGRightModule) n (dgHomLinearEquivCochains M N n f) :=
  curvedDGRightModuleHomComplex_d_apply M.isCurvedDGRightModule N.isCurvedDGRightModule n
    (dgHomLinearEquivCochains M N n f)

/-- The differential of the differential graded category of curved right modules is the graded
commutator with the module differentials, after transport to cochains. -/
@[simp↓]
theorem dgDifferential_eq (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1) (dgDifferential R n f) =
      dgRightModuleCochains.curvedDifferential (hM := M.isCurvedDGRightModule)
        (hN := N.isCurvedDGRightModule) n (dgHomLinearEquivCochains M N n f) :=
  (congrArg (dgHomLinearEquivCochains M N (n + 1))
    (DGCategoryData.dgDifferential_toDGCategory (homComplexData (h := h)) n f)).trans
      (homComplexData_d_apply M N n f)

/-- The identity of the differential graded category of curved right modules transports to the
identity cochain. -/
@[simp↓]
theorem dgId_eq :
    dgHomLinearEquivCochains M M 0 (dgId R M) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading) :=
  (congrArg (dgHomLinearEquivCochains M M 0)
    (DGCategoryData.dgId_toDGCategory (homComplexData (h := h)) M)).trans (homComplexData_id M)

/-- Composition in the differential graded category of curved right modules is composition of
cochains, carrying the Koszul sign which converts Mathlib's enriched factor order into
composition of the underlying maps, after transport to cochains. -/
@[simp↓]
theorem dgComp_eq {p q n : ℤ} (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = n) :
    dgHomLinearEquivCochains M P n (dgComp R f g hpq) =
      (p * q).negOnePow • dgRightModuleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) :=
  (congrArg (dgHomLinearEquivCochains M P n)
    (DGCategoryData.dgComp_toDGCategory (homComplexData (h := h)) f g hpq)).trans
      (homComplexData_comp M N P hpq f g)

/-! ### The closed degree-zero category -/

/-- The closed degree-zero morphisms are the preimage of the zero-cocycles of the curved Hom
complex under the explicit identification with cochains. -/
theorem dgCycles_eq :
    dgCycles R M N = Submodule.comap (dgHomLinearEquivCochains M N 0).toLinearMap
      (LinearMap.ker (dgRightModuleCochains.curvedDifferential
        (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) 0)) := by
  ext f
  rw [mem_dgCycles, Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap,
    ← dgDifferential_eq, LinearEquiv.map_eq_zero_iff]

/-- A degree-zero morphism of the differential graded category of curved right modules is closed
exactly when its underlying map commutes with the module differentials. -/
theorem mem_dgCycles_iff (f : DGHom R 0 M N) :
    f ∈ dgCycles R M N ↔
      ∀ x : M, N.differential ((dgHomLinearEquivCochains M N 0 f).1 x) =
        (dgHomLinearEquivCochains M N 0 f).1 (M.differential x) := by
  rw [dgCycles_eq, Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap,
    dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff]

/-- **Morphisms of the closed degree-zero category of curved right modules are the zero-cocycles
of the curved Hom complex.**  The closed degree-zero category is Mathlib's underlying category
`CategoryTheory.ForgetEnrichment` of the differential graded enrichment, whose morphisms are the
closed degree-zero morphisms `TauCeti.dgCycles`. -/
noncomputable def dgClosedHomEquivZeroCocycles :
    (ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N) ≃
      LinearMap.ker (dgRightModuleCochains.curvedDifferential
        (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) 0) :=
  (dgClosedHomEquiv R _ _).trans
    ((LinearEquiv.ofEq _ _ (dgCycles_eq M N)).trans
      ((dgHomLinearEquivCochains M N 0).ofSubmodule' _)).toEquiv

variable {M N P}

/-- The zero-cocycle attached to a morphism of the closed degree-zero category has the underlying
map of its closed degree-zero component. -/
@[simp]
theorem coe_dgClosedHomEquivZeroCocycles_apply
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N) (x : M) :
    ((dgClosedHomEquivZeroCocycles M N f).1.1 : M →ₗ[Aᵐᵒᵖ] N) x =
      (dgHomLinearEquivCochains M N 0
        (dgClosedHom R (X := ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M)
          (Y := ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N) f)).1 x := by
  simp only [dgClosedHomEquivZeroCocycles, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    LinearEquiv.trans_apply, LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply,
    dgClosedHomEquiv_apply_coe]

/-- The closed degree-zero component of the morphism attached to a zero-cocycle is the
corresponding homogeneous morphism. -/
@[simp]
theorem dgClosedHom_dgClosedHomEquivZeroCocycles_symm_apply
    (f : LinearMap.ker (dgRightModuleCochains.curvedDifferential
      (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) 0)) :
    dgClosedHom R ((dgClosedHomEquivZeroCocycles M N).symm f) =
      (dgHomLinearEquivCochains M N 0).symm f := by
  apply (dgHomLinearEquivCochains M N 0).injective
  rw [LinearEquiv.apply_symm_apply]
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  rw [← coe_dgClosedHomEquivZeroCocycles_apply, Equiv.apply_symm_apply]

/-- The identity of the closed degree-zero category corresponds to the identity cochain. -/
@[simp]
theorem dgClosedHomEquivZeroCocycles_id :
    ((dgClosedHomEquivZeroCocycles M M
        (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M))).1 :
        dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := M.grading) 0) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading) := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  rw [coe_dgClosedHomEquivZeroCocycles_apply, dgClosedHom_id]
  exact congrArg
    (fun c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := M.grading) 0 =>
      (c.1 : M →ₗ[Aᵐᵒᵖ] M) x) (dgId_eq M)

/-- Composition in the closed degree-zero category corresponds to composition of cochains. -/
@[simp]
theorem dgClosedHomEquivZeroCocycles_comp
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N)
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) P) :
    ((dgClosedHomEquivZeroCocycles M P (f ≫ g)).1 :
        dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := P.grading) 0) =
      dgRightModuleCochains.comp (dgClosedHomEquivZeroCocycles N P g).1
        (dgClosedHomEquivZeroCocycles M N f).1 (zero_add 0) := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  rw [dgRightModuleCochains.comp_apply, coe_dgClosedHomEquivZeroCocycles_apply,
    coe_dgClosedHomEquivZeroCocycles_apply, coe_dgClosedHomEquivZeroCocycles_apply,
    dgClosedHom_comp, dgCompZero_def]
  exact (congrArg
    (fun c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := P.grading) 0 =>
      (c.1 : M →ₗ[Aᵐᵒᵖ] P) x)
    (dgComp_eq M N P (dgClosedHom R f) (dgClosedHom R g) (zero_add 0))).trans
    (by rw [mul_zero, Int.negOnePow_zero, one_smul, dgRightModuleCochains.comp_apply])

variable (M N)

/-! ### Odd homotopies and the curved homotopy category -/

/-- A degree-zero morphism of the differential graded category of curved right modules is a
boundary exactly when its underlying map is the boundary `dN ∘ k + k ∘ dM` of an **odd
homotopy** `k`, a right-module map lowering the internal degree by one. -/
theorem mem_dgBoundaries_iff (f : DGHom R 0 M N) :
    f ∈ dgBoundaries R M N ↔
      ∃ k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1),
        ∀ x : M, (dgHomLinearEquivCochains M N 0 f).1 x =
          N.differential (k.1 x) + k.1 (M.differential x) := by
  rw [mem_dgBoundaries]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨dgHomLinearEquivCochains M N (-1) k, fun x => ?_⟩
    have hk := congrArg (fun c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading)
      (ℳN := N.grading) (-1 + 1) => (c.1 : M →ₗ[Aᵐᵒᵖ] N) x) (dgDifferential_eq M N (-1) k)
    rw [dgRightModuleCochains.curvedDifferential_neg_one_apply] at hk
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨(dgHomLinearEquivCochains M N (-1)).symm k, ?_⟩
    apply (dgHomLinearEquivCochains M N 0).injective
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    have hd := congrArg (fun c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading)
      (ℳN := N.grading) (-1 + 1) => (c.1 : M →ₗ[Aᵐᵒᵖ] N) x)
      (dgDifferential_eq M N (-1) ((dgHomLinearEquivCochains M N (-1)).symm k))
    rw [LinearEquiv.apply_symm_apply, dgRightModuleCochains.curvedDifferential_neg_one_apply]
      at hd
    rw [hk x]
    exact hd

/-- **The curved homotopy category.** Two closed degree-zero morphisms of curved right modules
represent the same morphism of the homotopy category `TauCeti.DGHomotopyCategory` exactly when
they are homotopic: their difference is the boundary `dN ∘ k + k ∘ dM` of an odd homotopy `k`. -/
theorem homOf_eq_iff_exists_homotopy {f g : DGHom R 0 M N}
    (hf : f ∈ dgCycles R M N) (hg : g ∈ dgCycles R M N) :
    DGHomotopyCategory.homOf R f hf = DGHomotopyCategory.homOf R g hg ↔
      ∃ k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1),
        ∀ x : M, (dgHomLinearEquivCochains M N 0 f).1 x -
            (dgHomLinearEquivCochains M N 0 g).1 x =
          N.differential (k.1 x) + k.1 (M.differential x) := by
  rw [DGHomotopyCategory.homOf_eq_iff, mem_dgBoundaries_iff]
  simp only [map_sub, Submodule.coe_sub, LinearMap.sub_apply]

end CurvedDGRightModuleCat

end TauCeti
