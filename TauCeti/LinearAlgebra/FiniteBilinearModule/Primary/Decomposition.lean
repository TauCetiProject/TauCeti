/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Decomposition
public import TauCeti.GroupTheory.Torsion
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component

/-!
# Primary decomposition of finite bilinear and quadratic modules

This file upgrades the primary decomposition of the underlying finite abelian group to the
form-theoretic decompositions used for discriminant forms. For a finite bilinear module, its
primary components form an orthogonal product whose pairing is the sum of the restricted
pairings. For a finite quadratic module, the analogous quadratic map is the sum of the restricted
quadratic maps.

The canonical additive equivalence is an isometry in both settings. This follows from the
orthogonality and finite-sum identities proved in
`TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component`.

## Main results

* `TauCeti.FiniteBilinearModule.primaryDecomposition`: the canonical primary decomposition as a
  bilinear isometry.
* `TauCeti.FiniteQuadraticModule.primaryDecomposition`: the canonical primary decomposition as a
  quadratic isometry.
* `TauCeti.FiniteBilinearModule.isNondegenerate_primaryComponents` and
  `TauCeti.FiniteQuadraticModule.isNondegenerate_primaryComponents`: nondegeneracy is equivalent
  to nondegeneracy of the orthogonal product.
* `TauCeti.FiniteBilinearModule.Isometry.restrictPrimaryComponent` and
  `TauCeti.FiniteQuadraticModule.Isometry.restrictPrimaryComponent`: an isometry restricts to each
  `n`-primary component.
* `TauCeti.FiniteBilinearModule.nonempty_isometry_of_forall_primaryComponent`,
  `TauCeti.FiniteQuadraticModule.nonempty_isometry_of_forall_primaryComponent`,
  `TauCeti.FiniteBilinearModule.nonempty_isometry_iff_forall_primaryComponent`, and
  `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_forall_primaryComponent`: two modules are
  isometric if and only if their prime-primary components are isometric at every prime.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open AddCommGroup

namespace TauCeti

universe u v

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-- The orthogonal product of the prime-primary restrictions of a finite bilinear module. -/
@[expose] noncomputable def primaryComponents : FiniteBilinearModule where
  carrier := ∀ p : (Nat.card A).primeFactors,
    AddCommGroup.primaryComponent A p.val
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ ∑ p, A.pairing (x p) (y p)
          map_zero' := by simp
          map_add' := fun y z ↦ by
            simp only [Pi.add_apply, AddSubgroup.coe_add, pairing_add_right,
              Finset.sum_add_distrib] }
      map_zero' := by
        ext y
        -- Expose the pointwise formula while constructing the bundled pairing itself.
        change ∑ p, A.pairing 0 (y p) = 0
        apply Finset.sum_eq_zero
        intro p _
        exact A.pairing_zero_left (y p)
      map_add' := fun x y ↦ by
        ext z
        -- Expose the pointwise formula while constructing the bundled pairing itself.
        change ∑ p, A.pairing (x p + y p) (z p) =
          (∑ p, A.pairing (x p) (z p)) + ∑ p, A.pairing (y p) (z p)
        simp only [pairing_add_left, Finset.sum_add_distrib] }
  pairing_comm x y := by
    -- Expose the pointwise formula while proving the final structure field.
    change (∑ p, A.pairing (x p) (y p)) = ∑ p, A.pairing (y p) (x p)
    apply Finset.sum_congr rfl
    intro p _
    exact A.pairing_comm (x p) (y p)

/-- The pairing on the orthogonal product is the sum of the component pairings. -/
@[simp]
theorem primaryComponents_pairing (x y : A.primaryComponents) :
    A.primaryComponents.pairing x y = ∑ p, A.pairing (x p) (y p) := by
  rfl

/-- The canonical primary decomposition is a bilinear isometry. -/
noncomputable def primaryDecomposition : Isometry A.primaryComponents A where
  toAddEquiv := AddCommGroup.primaryDecomposition A
  map_pairing' x y := by
    -- Unfolding the carrier variables and goal together aligns the bundled carrier's synthesized
    -- additive instance with the dependent-product instance used by the group decomposition.
    unfold primaryComponents at x y ⊢
    rw [AddCommGroup.primaryDecomposition_apply, AddCommGroup.primaryDecomposition_apply]
    change A.pairing (∑ p, (x p : A)) (∑ p, (y p : A)) =
      ∑ p, A.pairing (x p) (y p)
    exact A.pairing_sum_eq_sum_pairing_of_mem_primaryComponent
      Finset.univ Subtype.val (fun p ↦ x p) (fun p ↦ y p)
      (fun p _ ↦ Nat.prime_of_mem_primeFactors p.property)
      (fun p _ q _ hpq ↦ by simpa using hpq)
      (fun p _ ↦ (x p).property) (fun p _ ↦ (y p).property)

/-- The bilinear primary-decomposition isometry maps a tuple to its component sum. -/
@[simp]
theorem primaryDecomposition_apply (x : A.primaryComponents) :
    A.primaryDecomposition x = ∑ p, (x p : A) :=
  AddCommGroup.primaryDecomposition_apply A x

/-- The orthogonal product of primary components is nondegenerate exactly when the original
finite bilinear module is nondegenerate. -/
@[simp]
theorem isNondegenerate_primaryComponents :
    A.primaryComponents.IsNondegenerate ↔ A.IsNondegenerate :=
  A.primaryDecomposition.isNondegenerate_iff

/-- Equal orders give the same index set of prime factors. -/
private def primeFactorsEquiv {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
    (hcard : Nat.card A = Nat.card B) :
    (Nat.card A).primeFactors ≃ (Nat.card B).primeFactors :=
  Equiv.subtypeEquivRight fun p ↦ by rw [hcard]

/-- Additive equivalences of the primary components of two finite abelian groups of the same order
assemble to an additive equivalence of the products of their primary components: reindex along
`primeFactorsEquiv`, then apply the given equivalence componentwise. -/
private noncomputable def primaryComponentsAddEquiv {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (hcard : Nat.card A = Nat.card B)
    (f : ∀ p : ℕ, p.Prime → primaryComponent A p ≃+ primaryComponent B p) :
    A.primaryComponents ≃+ B.primaryComponents :=
  (LinearEquiv.piCongrLeft' ℤ (fun p : (Nat.card A).primeFactors ↦ primaryComponent A p.val)
    (primeFactorsEquiv hcard)).toAddEquiv.trans
    (AddEquiv.piCongrRight fun q ↦ f q.val (Nat.prime_of_mem_primeFactors q.property))

/-- `primaryComponentsAddEquiv` applies the given equivalence to the reindexed component. This is
`LinearEquiv.piCongrLeft'_apply` followed by `AddEquiv.piCongrRight_apply`, stated for the bundled
carrier `primaryComponents` so that it rewrites in the isometry proofs below. -/
private theorem primaryComponentsAddEquiv_apply {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (hcard : Nat.card A = Nat.card B)
    (f : ∀ p : ℕ, p.Prime → primaryComponent A p ≃+ primaryComponent B p)
    (x : A.primaryComponents) (q : (Nat.card B).primeFactors) :
    primaryComponentsAddEquiv hcard f x q =
      f q.val (Nat.prime_of_mem_primeFactors q.property) (x ((primeFactorsEquiv hcard).symm q)) :=
  rfl

/-- An isometry of finite bilinear modules restricts to each `n`-primary component. -/
def Isometry.restrictPrimaryComponent {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
    (f : Isometry A B) (n : ℕ) :
    Isometry (A.restrict (primaryComponent A n)) (B.restrict (primaryComponent B n)) where
  toAddEquiv := f.toAddEquiv.primaryComponent n
  map_pairing' x y := by
    rw [restrict_pairing, restrict_pairing, AddEquiv.coe_primaryComponent_apply,
      AddEquiv.coe_primaryComponent_apply, Isometry.coe_toAddEquiv]
    exact f.map_pairing x y

/-- Restricting a bilinear isometry to `n`-primary components commutes with coercion to the
ambient module. -/
@[simp]
theorem Isometry.coe_restrictPrimaryComponent_apply {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : Isometry A B) (n : ℕ)
    (x : primaryComponent A n) : (f.restrictPrimaryComponent n x : B) = f x :=
  f.toAddEquiv.coe_primaryComponent_apply n x

/-- The additive equivalence underlying a restricted bilinear isometry is the restricted additive
equivalence. -/
@[simp]
theorem Isometry.restrictPrimaryComponent_toAddEquiv {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : Isometry A B) (n : ℕ) :
    (f.restrictPrimaryComponent n).toAddEquiv = f.toAddEquiv.primaryComponent n :=
  (rfl)

/-- Restricting the identity bilinear isometry to an `n`-primary component gives the identity
bilinear isometry. -/
@[simp]
theorem Isometry.refl_restrictPrimaryComponent (A : FiniteBilinearModule.{u}) (n : ℕ) :
    (Isometry.refl A).restrictPrimaryComponent n =
      Isometry.refl (A.restrict (primaryComponent A n)) :=
  Isometry.toAddEquiv_injective (by simp)

/-- Restricting the inverse bilinear isometry to `n`-primary components gives the inverse of the
restricted isometry. -/
@[simp]
theorem Isometry.symm_restrictPrimaryComponent {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} (f : Isometry A B) (n : ℕ) :
    f.symm.restrictPrimaryComponent n = (f.restrictPrimaryComponent n).symm :=
  Isometry.toAddEquiv_injective (by simp)

/-- Restricting a composite bilinear isometry to `n`-primary components gives the composite of the
restricted isometries. -/
@[simp]
theorem Isometry.trans_restrictPrimaryComponent {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} {C : FiniteBilinearModule}
    (f : Isometry A B) (g : Isometry B C) (n : ℕ) :
    (f.trans g).restrictPrimaryComponent n =
      (f.restrictPrimaryComponent n).trans (g.restrictPrimaryComponent n) :=
  Isometry.toAddEquiv_injective (by simp)

/-- **Primary components decide isometry.** Two finite bilinear modules are isometric as soon as,
at every prime `p`, their `p`-primary components are isometric. -/
theorem nonempty_isometry_of_forall_primaryComponent {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}}
    (h : ∀ p : ℕ, p.Prime →
      Nonempty (Isometry (A.restrict (primaryComponent A p)) (B.restrict (primaryComponent B p)))) :
    Nonempty (Isometry A B) := by
  have hcard : Nat.card A = Nat.card B :=
    AddCommGroup.natCard_eq_of_natCard_primaryComponent_eq fun p hp ↦
      Nat.card_congr (h p hp).some.toAddEquiv.toEquiv
  let f p hp := (h p hp).some
  let g := primaryComponentsAddEquiv hcard fun p hp ↦ (f p hp).toAddEquiv
  refine ⟨A.primaryDecomposition.symm.trans (Isometry.trans ⟨g, fun x y ↦ ?_⟩
    B.primaryDecomposition)⟩
  rw [primaryComponents_pairing, primaryComponents_pairing]
  exact Fintype.sum_equiv (primeFactorsEquiv hcard).symm _ _ fun q ↦ by
    rw [primaryComponentsAddEquiv_apply, primaryComponentsAddEquiv_apply]
    exact (f q.val (Nat.prime_of_mem_primeFactors q.property)).map_pairing _ _

/-- **Two finite bilinear modules are isometric if and only if their prime-primary components are
isometric at every prime.** -/
theorem nonempty_isometry_iff_forall_primaryComponent {A : FiniteBilinearModule.{u}}
    {B : FiniteBilinearModule.{v}} :
    Nonempty (Isometry A B) ↔
      ∀ p : ℕ, p.Prime →
        Nonempty (Isometry (A.restrict (primaryComponent A p))
          (B.restrict (primaryComponent B p))) :=
  ⟨fun ⟨f⟩ p _ ↦ ⟨f.restrictPrimaryComponent p⟩, nonempty_isometry_of_forall_primaryComponent⟩

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- The orthogonal product of the prime-primary restrictions of a finite quadratic module. -/
@[expose] noncomputable def primaryComponents : FiniteQuadraticModule :=
  pi fun p : (Nat.card A).primeFactors ↦ A.restrict (AddCommGroup.primaryComponent A p.val)

/-- The quadratic map on the orthogonal product is the sum of the component quadratic maps. -/
@[simp]
theorem primaryComponents_quadratic (x : A.primaryComponents) :
    A.primaryComponents.quadratic x = ∑ p, A.quadratic (x p).val :=
  (pi_quadratic _ x).trans (Finset.sum_congr rfl fun p _ ↦ A.restrict_quadratic _ (x p))

/-- `AddCommGroup.primaryDecomposition` typed with the bundled carrier `A.primaryComponents`, so
that `toIntLinearEquiv` receives matching `ℤ`-module instances and `AddEquiv.coe_toIntLinearEquiv`
rewrites cleanly. -/
private noncomputable def primaryDecompositionAddEquiv : A.primaryComponents ≃+ A :=
  AddCommGroup.primaryDecomposition A

/-- The bundled-carrier primary-decomposition additive equivalence maps a tuple to its component
sum. -/
private theorem primaryDecompositionAddEquiv_apply (x : A.primaryComponents) :
    A.primaryDecompositionAddEquiv x = ∑ p, (x p).val :=
  AddCommGroup.primaryDecomposition_apply A x

/-- The canonical primary decomposition is a quadratic isometry. -/
noncomputable def primaryDecomposition : Isometry A.primaryComponents A where
  toLinearEquiv := A.primaryDecompositionAddEquiv.toIntLinearEquiv
  map_app' x := by
    rw [primaryComponents_quadratic, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
      AddEquiv.coe_toIntLinearEquiv, primaryDecompositionAddEquiv_apply]
    exact A.quadratic_sum_of_mem_primaryComponent Finset.univ Subtype.val (fun p ↦ (x p).val)
      (fun p _ ↦ Nat.prime_of_mem_primeFactors p.property)
      (fun p _ q _ hpq ↦ by simpa using hpq)
      (fun p _ ↦ (x p).property)

/-- The quadratic primary-decomposition isometry maps a tuple to its component sum. -/
@[simp]
theorem primaryDecomposition_apply (x : A.primaryComponents) :
    A.primaryDecomposition x = ∑ p, (x p).val :=
  A.primaryDecompositionAddEquiv_apply x

/-- The orthogonal product of primary components is nondegenerate exactly when the original
finite quadratic module is nondegenerate. -/
@[simp]
theorem isNondegenerate_primaryComponents :
    A.primaryComponents.IsNondegenerate ↔ A.IsNondegenerate :=
  A.primaryDecomposition.isNondegenerate_iff

/-- An isometry of finite quadratic modules restricts to each `n`-primary component. -/
def Isometry.restrictPrimaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    Isometry (A.restrict (primaryComponent A n)) (B.restrict (primaryComponent B n)) where
  toLinearEquiv := (f.toAddEquiv.primaryComponent n).toIntLinearEquiv
  map_app' x :=
    (congrArg B.quadratic (f.toAddEquiv.coe_primaryComponent_apply n x)).trans (f.map_app x.val)

/-- Restricting a quadratic isometry to `n`-primary components commutes with coercion to the
ambient module. -/
@[simp]
theorem Isometry.coe_restrictPrimaryComponent_apply {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ)
    (x : A.restrict (primaryComponent A n)) :
    (f.restrictPrimaryComponent n x).val = f x.val :=
  f.toAddEquiv.coe_primaryComponent_apply n x

/-- The additive equivalence underlying a restricted quadratic isometry is the restricted additive
equivalence. -/
@[simp]
theorem Isometry.restrictPrimaryComponent_toAddEquiv {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    (f.restrictPrimaryComponent n).toAddEquiv = f.toAddEquiv.primaryComponent n :=
  (rfl)

/-- Restricting the identity quadratic isometry to an `n`-primary component gives the identity
quadratic isometry. -/
@[simp]
theorem Isometry.refl_restrictPrimaryComponent (A : FiniteQuadraticModule.{u}) (n : ℕ) :
    Isometry.restrictPrimaryComponent (A := A) (B := A)
      (QuadraticMap.IsometryEquiv.refl A.quadratic) n =
      QuadraticMap.IsometryEquiv.refl (A.restrict (primaryComponent A n)).quadratic := by
  have hrefl (B : FiniteQuadraticModule.{u}) (y : B) :
      (QuadraticMap.IsometryEquiv.refl B.quadratic) y = y :=
    (Isometry.toHom_apply (A := B) (B := B)
      (QuadraticMap.IsometryEquiv.refl B.quadratic) y).symm.trans
      ((DFunLike.congr_fun (Isometry.refl_toHom B) y).trans (Hom.id_apply B y))
  exact DFunLike.ext _ _ fun x ↦ Subtype.ext <|
    (Isometry.coe_restrictPrimaryComponent_apply (A := A) (B := A)
      (QuadraticMap.IsometryEquiv.refl A.quadratic) n x).trans <|
      (hrefl A x.val).trans
        (congrArg Subtype.val (hrefl (A.restrict (primaryComponent A n)) x).symm)

/-- Restricting the inverse quadratic isometry to `n`-primary components gives the inverse of the
restricted isometry. -/
@[simp]
theorem Isometry.symm_restrictPrimaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    Isometry.restrictPrimaryComponent f.symm n = (f.restrictPrimaryComponent n).symm :=
  DFunLike.ext _ _ fun y ↦ by
    apply EquivLike.injective (f.restrictPrimaryComponent n)
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply]
    exact Subtype.ext (by simp)

/-- Restricting a composite quadratic isometry to `n`-primary components gives the composite of the
restricted isometries. -/
@[simp]
theorem Isometry.trans_restrictPrimaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} {C : FiniteQuadraticModule}
    (f : Isometry A B) (g : Isometry B C) (n : ℕ) :
    Isometry.restrictPrimaryComponent (A := A) (B := C) (f.trans g) n =
      (f.restrictPrimaryComponent n).trans (g.restrictPrimaryComponent n) :=
  DFunLike.ext _ _ fun x ↦ Subtype.ext <|
    (Isometry.coe_restrictPrimaryComponent_apply (A := A) (B := C) (f.trans g) n x).trans <|
      (Isometry.trans_apply f g x.val).trans <|
        (congrArg g (Isometry.coe_restrictPrimaryComponent_apply f n x).symm).trans <|
          (Isometry.coe_restrictPrimaryComponent_apply g n
            (f.restrictPrimaryComponent n x)).symm.trans
            (congrArg Subtype.val
              (Isometry.trans_apply (f.restrictPrimaryComponent n)
                (g.restrictPrimaryComponent n) x).symm)

/-- Forgetting the quadratic structure of a restricted quadratic isometry gives the restricted
polar bilinear isometry. -/
@[simp]
theorem Isometry.restrictPrimaryComponent_toFiniteBilinearModule {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : Isometry A B) (n : ℕ) :
    (f.restrictPrimaryComponent n).toFiniteBilinearModule =
      f.toFiniteBilinearModule.restrictPrimaryComponent n := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [Isometry.toFiniteBilinearModule_toAddEquiv, Isometry.restrictPrimaryComponent_toAddEquiv,
    FiniteBilinearModule.Isometry.restrictPrimaryComponent_toAddEquiv,
    Isometry.toFiniteBilinearModule_toAddEquiv]

/-- **Primary components decide isometry.** Two finite quadratic modules are isometric as soon as,
at every prime `p`, their `p`-primary components are isometric. -/
theorem nonempty_isometry_of_forall_primaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}}
    (h : ∀ p : ℕ, p.Prime →
      Nonempty (Isometry (A.restrict (primaryComponent A p)) (B.restrict (primaryComponent B p)))) :
    Nonempty (Isometry A B) := by
  have hcard : Nat.card A = Nat.card B :=
    AddCommGroup.natCard_eq_of_natCard_primaryComponent_eq fun p hp ↦
      Nat.card_congr (h p hp).some.toLinearEquiv.toAddEquiv.toEquiv
  let f p hp := (h p hp).some
  let g := FiniteBilinearModule.primaryComponentsAddEquiv hcard fun p hp ↦
    (f p hp).toLinearEquiv.toAddEquiv
  refine ⟨A.primaryDecomposition.symm.trans
    ((⟨g.toIntLinearEquiv, fun x ↦ ?_⟩ : Isometry _ _).trans B.primaryDecomposition)⟩
  rw [primaryComponents_quadratic, primaryComponents_quadratic]
  -- The coercion of `g.toIntLinearEquiv` is `g` (`AddEquiv.coe_toIntLinearEquiv` is `rfl`).
  exact Fintype.sum_equiv (FiniteBilinearModule.primeFactorsEquiv hcard).symm _ _ fun q ↦
    (congrArg (fun y : primaryComponent B.carrier q.val ↦ B.quadratic y.val)
      (FiniteBilinearModule.primaryComponentsAddEquiv_apply hcard _ x q)).trans
      ((f q.val (Nat.prime_of_mem_primeFactors q.property)).map_app _)

/-- **Two finite quadratic modules are isometric if and only if their prime-primary components are
isometric at every prime.** -/
theorem nonempty_isometry_iff_forall_primaryComponent {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} :
    Nonempty (Isometry A B) ↔
      ∀ p : ℕ, p.Prime →
        Nonempty (Isometry (A.restrict (primaryComponent A p))
          (B.restrict (primaryComponent B p))) :=
  ⟨fun ⟨f⟩ p _ ↦ ⟨Isometry.restrictPrimaryComponent f p⟩,
    nonempty_isometry_of_forall_primaryComponent⟩

end FiniteQuadraticModule

end TauCeti
