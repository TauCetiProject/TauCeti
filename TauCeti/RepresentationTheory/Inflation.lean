/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.RepresentationTheory.Invariants

/-!
# Inflation along a surjection and invariants under its kernel

Let `π : G →* Q` be a surjective group homomorphism with kernel `U`. Restriction along `π`,
Mathlib's `Rep.resFunctor π`, is *inflation*: it views a representation of `Q` as a
representation of `G` on which `U` acts trivially. In the other direction, the `U`-invariants
`A^U` of a representation `A` of `G` carry an action of `G ⧸ U ≃* Q`.

This file shows that taking `U`-invariants is adjoint to inflation on both sides:

* inflation is always left adjoint to `U`-invariants, since a `G`-equivariant map out of an
  inflated representation lands in the `U`-invariants;
* if `U` is finite of invertible order, inflation is also right adjoint to `U`-invariants: a
  `G`-equivariant map into an inflated representation is determined by its restriction to the
  `U`-invariants, through the averaging projection `A → A^U`.

These are the inflation/invariants adjunctions underlying Harish-Chandra induction and
restriction for finite groups with a split parabolic `P = L ⋉ U`, where `π : P →* L` is the
projection onto the Levi factor.

## Main definitions

* `Rep.kerInvariants π hπ A`: the representation of `Q` on the `ker π`-invariants of `A`.
* `Rep.kerInvariantsFunctor k π hπ`: the functor `A ↦ A^{ker π}` from `Rep k G` to `Rep k Q`.
* `Rep.resKerInvariantsAdjunction k π hπ`: inflation along `π` is left adjoint to
  `Rep.kerInvariantsFunctor`.
* `Rep.kerAverage π hπ A`: the averaging projection `A → A^{ker π}`, for `ker π` finite of
  invertible order.
* `Rep.kerInvariantsResAdjunction k π hπ`: when `ker π` is finite of invertible order, inflation
  along `π` is right adjoint to `Rep.kerInvariantsFunctor`.

## References

* O. Dudas and J. Michel, *Lectures on finite reductive groups and their representations*
  (2015), §7.
-/

public section

open CategoryTheory

universe w u v v'

namespace Rep

variable {k : Type u} [CommRing k] {G : Type v} [Group G] {Q : Type v'} [Group Q]
  (π : G →* Q) (hπ : Function.Surjective π)

/-- The representation of `Q` on the `ker π`-invariants of a representation `A` of `G`, for a
surjective homomorphism `π : G →* Q`; an element `π g` acts as `g` does. -/
noncomputable abbrev kerInvariants (A : Rep.{w} k G) : Rep.{w} k Q :=
  Rep.of ((A.ρ.quotientToInvariants π.ker).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom)

/-- The element `π g` acts on `A^{ker π}` as `g` acts on `A`.

This is not a `simp` lemma: `simp` proves it by unfolding `Rep.kerInvariants`. -/
theorem coe_kerInvariants_ρ_apply (A : Rep.{w} k G) (g : G)
    (v : Representation.invariants (A.ρ.comp π.ker.subtype)) :
    ((kerInvariants π hπ A).ρ (π g) v : A) = A.ρ g v := by
  simp

variable (k) in
/-- Taking invariants under the kernel of a surjective homomorphism `π : G →* Q`, as a functor
from representations of `G` to representations of `Q`. It is Mathlib's
`Rep.quotientToInvariantsFunctor` for `ker π`, transported along `G ⧸ ker π ≃* Q`.

The body is exposed so that `(kerInvariantsFunctor k π hπ).obj A` unfolds to the submodule
`Rep.kerInvariants π hπ A` of `A`, whose elements consumers manipulate directly. -/
@[expose]
noncomputable def kerInvariantsFunctor : Rep.{w} k G ⥤ Rep.{w} k Q where
  obj A := kerInvariants π hπ A
  map f := (resFunctor (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom).map
    ((quotientToInvariantsFunctor k π.ker).map f)

@[simp]
theorem kerInvariantsFunctor_obj (A : Rep.{w} k G) :
    (kerInvariantsFunctor k π hπ).obj A = kerInvariants π hπ A :=
  (rfl)

@[simp]
theorem coe_kerInvariantsFunctor_map_hom_apply {A B : Rep.{w} k G} (f : A ⟶ B)
    (v : Representation.invariants (A.ρ.comp π.ker.subtype)) :
    Subtype.val (((kerInvariantsFunctor k π hπ).map f).hom v) = f.hom v :=
  (rfl)

/-! ### Inflation is left adjoint to kernel invariants -/

/-- A `G`-equivariant map out of the inflation of a representation `M` of `Q` lands in the
`ker π`-invariants, and conversely; this is the hom-set bijection of
`Rep.resKerInvariantsAdjunction`. -/
noncomputable def resKerInvariantsHomEquiv (M : Rep.{w} k Q) (A : Rep.{w} k G) :
    (res π M ⟶ A) ≃ₗ[k] (M ⟶ kerInvariants π hπ A) where
  toFun f := Rep.ofHom ⟨f.hom.toLinearMap.codRestrict _ fun m u => by
      simpa [π.mem_ker.1 u.2] using (hom_comm_apply f (u : G) m).symm, fun q => by
    obtain ⟨g, rfl⟩ := hπ q
    ext m
    refine Eq.trans ?_ (coe_kerInvariants_ρ_apply π hπ A g _).symm
    exact hom_comm_apply f g m⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨(Submodule.subtype _) ∘ₗ f.hom.toLinearMap, fun g => by
    ext m
    simpa using congrArg Subtype.val (hom_comm_apply f (π g) m)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_resKerInvariantsHomEquiv_apply_hom_apply {M : Rep.{w} k Q} {A : Rep.{w} k G}
    (f : res π M ⟶ A) (m : M) :
    ((resKerInvariantsHomEquiv π hπ M A f).hom m : A) = f.hom m :=
  (rfl)

@[simp]
theorem resKerInvariantsHomEquiv_symm_apply_hom_apply {M : Rep.{w} k Q} {A : Rep.{w} k G}
    (f : M ⟶ kerInvariants π hπ A) (m : M) :
    ((resKerInvariantsHomEquiv π hπ M A).symm f).hom m = f.hom m :=
  (rfl)

variable (k) in
/-- **Inflation is left adjoint to invariants.** For a surjective homomorphism `π : G →* Q`,
restriction along `π` is left adjoint to taking `ker π`-invariants. -/
noncomputable def resKerInvariantsAdjunction :
    resFunctor.{w} π ⊣ kerInvariantsFunctor k π hπ :=
  Adjunction.mkOfHomEquiv
    { homEquiv M A := (resKerInvariantsHomEquiv π hπ M A).toEquiv
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

@[simp]
theorem resKerInvariantsAdjunction_homEquiv (M : Rep.{w} k Q) (A : Rep.{w} k G) :
    (resKerInvariantsAdjunction k π hπ).homEquiv M A =
      (resKerInvariantsHomEquiv π hπ M A).toEquiv :=
  (rfl)

/-- The elementwise form of `Rep.resKerInvariantsAdjunction_homEquiv`. It is not a `simp` lemma,
since `simp` rewrites its left-hand side by that lemma. -/
theorem coe_resKerInvariantsAdjunction_homEquiv_apply_hom_apply {M : Rep.{w} k Q} {A : Rep.{w} k G}
    (f : res π M ⟶ A) (m : M) :
    Subtype.val (((resKerInvariantsAdjunction k π hπ).homEquiv M A f).hom m) = f.hom m :=
  (rfl)

/-- The unit of `Rep.resKerInvariantsAdjunction` views `m : M` as a `ker π`-invariant vector of the
inflation of `M`. It is not a `simp` lemma, since `simp` rewrites the functor objects in the type
of its left-hand side. -/
theorem coe_resKerInvariantsAdjunction_unit_app_hom_apply (M : Rep.{w} k Q) (m : M) :
    Subtype.val (((resKerInvariantsAdjunction k π hπ).unit.app M).hom m) = m :=
  (rfl)

/-- The counit of `Rep.resKerInvariantsAdjunction` is the inclusion `A^{ker π} → A`. It is not a
`simp` lemma, since `simp` rewrites the functor objects in the type of its left-hand side. -/
theorem resKerInvariantsAdjunction_counit_app_hom_apply (A : Rep.{w} k G)
    (v : Representation.invariants (A.ρ.comp π.ker.subtype)) :
    ((resKerInvariantsAdjunction k π hπ).counit.app A).hom v = (v : A) :=
  (rfl)

/-! ### Inflation is right adjoint to kernel invariants -/

section Finite

variable [Fintype π.ker] [Invertible (Fintype.card π.ker : k)]

/-- The averaging projection `A → A^{ker π}`, `a ↦ ⅟#(ker π) • ∑ u ∈ ker π, u • a`, as a morphism
of representations of `G` from `A` to the inflation of `A^{ker π}`. -/
noncomputable def kerAverage (A : Rep.{w} k G) : A ⟶ res π (kerInvariants π hπ A) :=
  Rep.ofHom ⟨(Representation.averageMap (A.ρ.comp π.ker.subtype)).codRestrict _
      (Representation.averageMap_invariant (A.ρ.comp π.ker.subtype)), fun g => by
    ext a
    refine Eq.trans ?_ (coe_kerInvariants_ρ_apply π hπ A g _).symm
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply]
    rw [Representation.averageMap_apply, Representation.averageMap_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (MulAut.conjNormal (H := π.ker) g⁻¹).toEquiv _ _ fun u => ?_
    simp [← mul_apply_eq_comp, ← map_mul, mul_assoc]⟩

@[simp]
theorem coe_kerAverage_hom_apply (A : Rep.{w} k G) (a : A) :
    ((kerAverage π hπ A).hom a : A) = Representation.averageMap (A.ρ.comp π.ker.subtype) a :=
  (rfl)

/-- The averaging projection fixes the `ker π`-invariants. -/
@[simp]
theorem kerAverage_hom_apply_coe (A : Rep.{w} k G)
    (v : Representation.invariants (A.ρ.comp π.ker.subtype)) :
    (kerAverage π hπ A).hom (v : A) = v :=
  Subtype.ext (Representation.averageMap_id _ _ v.2)

/-- A `G`-equivariant map into the inflation of a representation `M` of `Q` is determined by its
restriction to the `ker π`-invariants, through the averaging projection; this is the hom-set
bijection of `Rep.kerInvariantsResAdjunction`. -/
noncomputable def kerInvariantsResHomEquiv (A : Rep.{w} k G) (M : Rep.{w} k Q) :
    (kerInvariants π hπ A ⟶ M) ≃ₗ[k] (A ⟶ res π M) where
  toFun f := kerAverage π hπ A ≫ (resFunctor π).map f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ Submodule.subtype _, fun q => by
    obtain ⟨g, rfl⟩ := hπ q
    ext v
    simpa using hom_comm_apply f g v⟩
  left_inv f := by
    ext v
    exact congrArg f.hom (kerAverage_hom_apply_coe π hπ A v)
  right_inv f := by
    ext a
    have h (u : π.ker) : f.hom (A.ρ u a) = f.hom a := by
      simp [hom_comm_apply f (u : G) a, π.mem_ker.1 u.2]
    refine (congrArg f.hom (coe_kerAverage_hom_apply π hπ A a)).trans ?_
    rw [Representation.averageMap_apply]
    simp [h, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul]

@[simp]
theorem kerInvariantsResHomEquiv_apply {A : Rep.{w} k G} {M : Rep.{w} k Q}
    (f : kerInvariants π hπ A ⟶ M) :
    kerInvariantsResHomEquiv π hπ A M f = kerAverage π hπ A ≫ (resFunctor π).map f :=
  (rfl)

@[simp]
theorem kerInvariantsResHomEquiv_symm_apply_hom_apply {A : Rep.{w} k G} {M : Rep.{w} k Q}
    (f : A ⟶ res π M) (v : Representation.invariants (A.ρ.comp π.ker.subtype)) :
    ((kerInvariantsResHomEquiv π hπ A M).symm f).hom v = f.hom v :=
  (rfl)

variable (k) in
/-- **Inflation is right adjoint to invariants under a kernel of invertible order.** For a
surjective homomorphism `π : G →* Q` whose kernel is finite of order invertible in `k`, taking
`ker π`-invariants is left adjoint to restriction along `π`. -/
noncomputable def kerInvariantsResAdjunction :
    kerInvariantsFunctor k π hπ ⊣ resFunctor.{w} π :=
  Adjunction.mkOfHomEquiv
    { homEquiv A M := (kerInvariantsResHomEquiv π hπ A M).toEquiv
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

@[simp]
theorem kerInvariantsResAdjunction_homEquiv (A : Rep.{w} k G) (M : Rep.{w} k Q) :
    (kerInvariantsResAdjunction k π hπ).homEquiv A M =
      (kerInvariantsResHomEquiv π hπ A M).toEquiv :=
  (rfl)

/-- The elementwise form of the inverse of `Rep.kerInvariantsResAdjunction_homEquiv`. It is not a
`simp` lemma, since `simp` rewrites its left-hand side by that lemma. -/
theorem kerInvariantsResAdjunction_homEquiv_symm_apply_hom_apply {A : Rep.{w} k G}
    {M : Rep.{w} k Q} (f : A ⟶ res π M) (v : Representation.invariants (A.ρ.comp π.ker.subtype)) :
    (((kerInvariantsResAdjunction k π hπ).homEquiv A M).symm f).hom v = f.hom v :=
  (rfl)

/-- The unit of `Rep.kerInvariantsResAdjunction` is the averaging projection `Rep.kerAverage`. -/
@[simp]
theorem kerInvariantsResAdjunction_unit_app (A : Rep.{w} k G) :
    (kerInvariantsResAdjunction k π hπ).unit.app A = kerAverage π hπ A :=
  (rfl)

/-- The counit of `Rep.kerInvariantsResAdjunction` is the inclusion of the `ker π`-invariants of
an inflated representation `M`, which are all of `M`. It is not a `simp` lemma, since `simp`
rewrites the functor objects in the type of its left-hand side. -/
theorem kerInvariantsResAdjunction_counit_app_hom_apply (M : Rep.{w} k Q)
    (v : Representation.invariants ((res π M).ρ.comp π.ker.subtype)) :
    ((kerInvariantsResAdjunction k π hπ).counit.app M).hom v = (v : M) :=
  (rfl)

end Finite

end Rep
