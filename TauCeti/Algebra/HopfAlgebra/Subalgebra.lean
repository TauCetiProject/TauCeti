/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Structure
import TauCeti.RingTheory.Flat.TensorProduct

/-!
# Hopf subalgebras

A subalgebra `A` of a Hopf algebra `H` over `R` is a **Hopf subalgebra** when comultiplication
maps `A` into the image of `A ⊗[R] A` in `H ⊗[R] H` and the antipode maps `A` into itself. When
`H` and `A` are flat over `R` (for instance over a field), the map `A ⊗[R] A → H ⊗[R] H` is
injective, so the comultiplication, counit and antipode of `H` restrict to a Hopf algebra
structure on `A` for which the inclusion is a morphism of bialgebras.

For commutative `H`, the inclusion of a Hopf subalgebra `A` is the coordinate map of a
homomorphism of affine groups `Spec H → Spec A`; over a field, the Hopf subalgebras are exactly
the coordinate rings of the quotients of `Spec H` (Waterhouse, §16.3). This file packages `A` as
an object of `CommHopfAlgCat` together with the inclusion morphism, and proves the universal
property: a morphism of commutative Hopf algebras into `H` factors, necessarily uniquely, through
the inclusion exactly when its image lies in `A`.

With `open TauCeti`, state the predicate as `A.IsHopfSubalgebra`. Given a proof
`hA : A.IsHopfSubalgebra`, use `hA.toSubcoalgebra` for the underlying subcoalgebra and,
under the flatness hypotheses, `hA.hopfAlgebra` and `hA.valBialgHom` for the restricted
Hopf structure and its inclusion.

## Main declarations

* `TauCeti.Subalgebra.IsHopfSubalgebra`: a subalgebra stable under comultiplication and the
  antipode.
* `TauCeti.Subalgebra.IsHopfSubalgebra.hopfAlgebra`: the restricted Hopf algebra structure, under
  flatness.
* `TauCeti.CommHopfAlgCat.ofHopfSubalgebra`: a Hopf subalgebra as a bundled commutative Hopf
  algebra.
* `TauCeti.CommHopfAlgCat.hopfSubalgebraι`: the inclusion morphism, a bialgebra morphism which
  commutes with the antipodes and is injective, hence a monomorphism.
* `TauCeti.CommHopfAlgCat.liftHopfSubalgebra`: the factorization of a morphism with image in the
  Hopf subalgebra, with `TauCeti.CommHopfAlgCat.exists_comp_hopfSubalgebraι_iff`.

## References

* M. E. Sweedler, *Hopf Algebras* (1969), §4.1.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), §§15.1 and 16.3.
-/

public section

open scoped TensorProduct

universe u v

namespace TauCeti.Subalgebra

open _root_.Subalgebra

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- A subalgebra `A` of a Hopf algebra `H` is a **Hopf subalgebra** when comultiplication maps it
into the image of `A ⊗[R] A` and the antipode maps it into itself. -/
structure IsHopfSubalgebra (A : Subalgebra R H) : Prop where
  /-- The comultiplication of an element of `A` lies in the image of `A ⊗[R] A`. -/
  comul_mem ⦃x : H⦄ : x ∈ A →
    Coalgebra.comul (R := R) x ∈
      LinearMap.range (TensorProduct.map (toSubmodule A).subtype (toSubmodule A).subtype)
  /-- The antipode maps `A` into itself. -/
  antipode_mem ⦃x : H⦄ : x ∈ A → HopfAlgebra.antipode R x ∈ A

namespace IsHopfSubalgebra

variable {A : Subalgebra R H} (hA : IsHopfSubalgebra A)
include hA

/-- The underlying subcoalgebra of a Hopf subalgebra. -/
abbrev toSubcoalgebra : Subcoalgebra R H where
  carrier := toSubmodule A
  comul_mem' := hA.comul_mem

variable [Module.Flat R H] [Module.Flat R A]

omit [Module.Flat R H] [Module.Flat R A] in
private theorem comulAlgHom_comp_val_mem_range (x : A) :
    (Bialgebra.comulAlgHom R H).comp A.val x ∈ (Algebra.TensorProduct.map A.val A.val).range := by
  have h := hA.comul_mem x.2
  rw [toSubmodule_subtype] at h
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  have hy' : Algebra.TensorProduct.map A.val A.val y = Coalgebra.comul (R := R) (x : H) := by
    rw [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq]
    exact hy
  exact hy'

/-- The comultiplication of a Hopf subalgebra, valued in its own tensor square: the unique
preimage of the comultiplication of `H` under the injective map `A ⊗[R] A → H ⊗[R] H`. -/
noncomputable def comulAlgHom : A →ₐ[R] A ⊗[R] A :=
  (AlgEquiv.ofInjective _ (Algebra.TensorProduct.map_injective_of_flat_flat A.val A.val
    Subtype.val_injective Subtype.val_injective)).symm.toAlgHom.comp
    (((Bialgebra.comulAlgHom R H).comp A.val).codRestrict _ hA.comulAlgHom_comp_val_mem_range)

/-- The comultiplication of a Hopf subalgebra is the restriction of that of `H`. -/
@[simp]
theorem map_val_comulAlgHom (x : A) :
    Algebra.TensorProduct.map A.val A.val (hA.comulAlgHom x) = Coalgebra.comul (R := R) (x : H) :=
  (AlgEquiv.ofInjective_apply _ (Algebra.TensorProduct.map_injective_of_flat_flat A.val A.val
    Subtype.val_injective Subtype.val_injective) _).symm.trans
    (congrArg Subtype.val (AlgEquiv.apply_symm_apply _ _))

private theorem map_val_comulAlgHom' (x : A) :
    TensorProduct.map A.val.toLinearMap A.val.toLinearMap (hA.comulAlgHom x) =
      Coalgebra.comul (R := R) (x : H) := by
  have h := hA.map_val_comulAlgHom x
  rwa [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq] at h

/-- The restriction of the antipode of `H` to a Hopf subalgebra. -/
def antipode : A →ₗ[R] A :=
  (HopfAlgebra.antipode R).restrict (p := toSubmodule A) (q := toSubmodule A)
    fun _ hx ↦ hA.antipode_mem hx

omit [Module.Flat R H] [Module.Flat R A] in
/-- The restricted antipode has the same values as the ambient antipode. -/
@[simp]
theorem coe_antipode (x : A) : (antipode hA x : H) = HopfAlgebra.antipode R (x : H) :=
  LinearMap.coe_restrict_apply (p := toSubmodule A) (q := toSubmodule A)
    (fun _ hx ↦ hA.antipode_mem hx) x

private theorem mul_antipode_rTensor_comulAlgHom (x : A) :
    LinearMap.mul' R A ((antipode hA).rTensor A (hA.comulAlgHom x)) =
      algebraMap R A (Coalgebra.counit (R := R) (x : H)) := by
  have h (t : A ⊗[R] A) :
      (LinearMap.mul' R A ((antipode hA).rTensor A t) : H) =
        LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H
          (TensorProduct.map A.val.toLinearMap A.val.toLinearMap t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp [coe_antipode]
    | add s t hs ht => simp only [map_add, Subalgebra.coe_add, hs, ht]
  apply Subtype.val_injective
  simp [h, map_val_comulAlgHom']

private theorem mul_antipode_lTensor_comulAlgHom (x : A) :
    LinearMap.mul' R A ((antipode hA).lTensor A (hA.comulAlgHom x)) =
      algebraMap R A (Coalgebra.counit (R := R) (x : H)) := by
  have h (t : A ⊗[R] A) :
      (LinearMap.mul' R A ((antipode hA).lTensor A t) : H) =
        LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H
          (TensorProduct.map A.val.toLinearMap A.val.toLinearMap t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp [coe_antipode]
    | add s t hs ht => simp only [map_add, Subalgebra.coe_add, hs, ht]
  apply Subtype.val_injective
  simp [h, map_val_comulAlgHom']

private theorem toSubcoalgebra_comulLinearMap (x : A) :
    letI : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
    hA.toSubcoalgebra.comulLinearMap x = hA.comulAlgHom x := by
  have : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
  apply TensorProduct.map_injective_of_flat_flat A.val.toLinearMap A.val.toLinearMap
    Subtype.val_injective Subtype.val_injective
  exact (hA.toSubcoalgebra.map_subtype_comulLinearMap x).trans
    (hA.map_val_comulAlgHom' x).symm

private theorem coalgebra_comul_apply (x : A) :
    letI : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
    letI : Coalgebra R A := hA.toSubcoalgebra.coalgebra
    Coalgebra.comul (R := R) x = hA.comulAlgHom x := by
  have : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
  exact (hA.toSubcoalgebra.comul_apply x).trans (hA.toSubcoalgebra_comulLinearMap x)

private theorem coalgebra_counit_apply (x : A) :
    letI : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
    letI : Coalgebra R A := hA.toSubcoalgebra.coalgebra
    Coalgebra.counit (R := R) x = Coalgebra.counit (R := R) (x : H) := by
  have : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
  exact hA.toSubcoalgebra.counit_apply x

/-- The Hopf algebra structure on a flat Hopf subalgebra of a flat Hopf algebra: comultiplication,
counit and antipode are restricted from `H`. This is not an instance because it depends on the
proof `hA`. -/
-- Expose the inherited algebra structure so instance synthesis can identify its module structure
-- with the existing subalgebra module; characteristic lemmas below expose the Hopf operations.
@[expose, instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R A :=
  letI : Module.Flat R hA.toSubcoalgebra.toSubmodule := inferInstanceAs (Module.Flat R A)
  letI : Coalgebra R A := hA.toSubcoalgebra.coalgebra
  { Bialgebra.mk' R A
      (by simp [hA.coalgebra_counit_apply])
      (by intro a b; simp [hA.coalgebra_counit_apply])
      (by simpa only [hA.coalgebra_comul_apply] using
        map_one hA.comulAlgHom)
      (by intro a b; simpa only [hA.coalgebra_comul_apply] using map_mul hA.comulAlgHom a b) with
    antipode := antipode hA
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro x
      simpa only [LinearMap.comp_apply, hA.coalgebra_comul_apply, hA.coalgebra_counit_apply,
        Algebra.linearMap_apply] using hA.mul_antipode_rTensor_comulAlgHom x
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro x
      simpa only [LinearMap.comp_apply, hA.coalgebra_comul_apply, hA.coalgebra_counit_apply,
        Algebra.linearMap_apply] using hA.mul_antipode_lTensor_comulAlgHom x }

/-- The comultiplication of the restricted Hopf structure is the restricted algebra map. -/
@[simp]
theorem comul_apply (x : A) :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    Coalgebra.comul (R := R) x = hA.comulAlgHom x :=
  hA.coalgebra_comul_apply x

/-- The counit of the restricted Hopf structure is the counit of the ambient algebra. -/
@[simp]
theorem counit_apply (x : A) :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    Coalgebra.counit (R := R) x = Coalgebra.counit (R := R) (x : H) :=
  hA.coalgebra_counit_apply x

/-- The antipode of the restricted Hopf structure is the antipode of the ambient algebra. -/
@[simp]
theorem coe_antipode_apply (x : A) :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    ((HopfAlgebra.antipode R x : A) : H) = HopfAlgebra.antipode R (x : H) :=
  (rfl)

/-- The inclusion of a Hopf subalgebra, as a bialgebra homomorphism. -/
noncomputable def valBialgHom :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    A →ₐc[R] H :=
  letI : HopfAlgebra R A := hA.hopfAlgebra
  BialgHom.ofAlgHom A.val (by ext; simp [hA.counit_apply])
    (by ext; simp [hA.comul_apply])

/-- The inclusion bialgebra homomorphism is the underlying subalgebra inclusion. -/
@[simp]
theorem valBialgHom_apply (x : A) :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    hA.valBialgHom x = (x : H) :=
  (rfl)

/-- Corestrict a bialgebra homomorphism whose image lies in a Hopf subalgebra. -/
noncomputable def codRestrict {K : Type*} [Semiring K] [Bialgebra R K]
    (f : K →ₐc[R] H) (hf : ∀ x, f x ∈ A) :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    K →ₐc[R] A :=
  letI : HopfAlgebra R A := hA.hopfAlgebra
  BialgHom.ofAlgHom ((f : K →ₐ[R] H).codRestrict A hf)
    (by
      ext x
      exact (hA.counit_apply _).trans
        ((congrArg (Coalgebra.counit (R := R))
          (AlgHom.coe_codRestrict (f : K →ₐ[R] H) A hf x)).trans
          (CoalgHomClass.counit_comp_apply f x)))
    (by
      ext x
      apply Algebra.TensorProduct.map_injective_of_flat_flat A.val A.val
        Subtype.val_injective Subtype.val_injective
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, hA.comul_apply]
      refine Eq.trans ?_ (hA.map_val_comulAlgHom _).symm
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
      exact CoalgHomClass.map_comp_comul_apply f x)

/-- Corestriction preserves the values of the original bialgebra homomorphism. -/
@[simp]
theorem coe_codRestrict_apply {K : Type*} [Semiring K] [Bialgebra R K]
    (f : K →ₐc[R] H) (hf : ∀ x, f x ∈ A) (x : K) :
    letI : HopfAlgebra R A := hA.hopfAlgebra
    (hA.codRestrict f hf x : H) = f x :=
  (rfl)

end IsHopfSubalgebra

end TauCeti.Subalgebra

namespace TauCeti.CommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R} {A : Subalgebra R H}
variable [Module.Flat R H] [Module.Flat R A]

/-- A flat Hopf subalgebra of a flat commutative Hopf algebra, as a bundled commutative Hopf
algebra. -/
noncomputable abbrev ofHopfSubalgebra (hA : Subalgebra.IsHopfSubalgebra A) :
    _root_.CommHopfAlgCat.{v} R :=
  letI : HopfAlgebra R A := hA.hopfAlgebra
  _root_.CommHopfAlgCat.of R A

/-- The inclusion of a Hopf subalgebra as a morphism of commutative Hopf algebras. -/
noncomputable def hopfSubalgebraι (hA : Subalgebra.IsHopfSubalgebra A) : ofHopfSubalgebra hA ⟶ H :=
  _root_.CommHopfAlgCat.ofHom hA.valBialgHom

/-- The inclusion morphism of a Hopf subalgebra is the inclusion of the underlying subalgebra. -/
@[simp]
theorem hopfSubalgebraι_apply (hA : Subalgebra.IsHopfSubalgebra A) (x : A) :
    (hopfSubalgebraι hA).hom x = x :=
  (rfl)

/-- The inclusion morphism of a Hopf subalgebra is injective. -/
theorem hopfSubalgebraι_injective (hA : Subalgebra.IsHopfSubalgebra A) :
    Function.Injective (hopfSubalgebraι hA).hom :=
  Subtype.val_injective

instance (hA : Subalgebra.IsHopfSubalgebra A) : Mono (hopfSubalgebraι hA) :=
  ConcreteCategory.mono_of_injective _ (hopfSubalgebraι_injective hA)

/-- A morphism of commutative Hopf algebras whose image lies in a Hopf subalgebra, corestricted
to that Hopf subalgebra. -/
noncomputable def liftHopfSubalgebra (hA : Subalgebra.IsHopfSubalgebra A) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) : K ⟶ ofHopfSubalgebra hA :=
  _root_.CommHopfAlgCat.ofHom (hA.codRestrict f.hom hf)

/-- The corestricted morphism has the same values as the original one. -/
@[simp]
theorem coe_liftHopfSubalgebra_apply (hA : Subalgebra.IsHopfSubalgebra A) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) (x : K) :
    ((liftHopfSubalgebra hA f hf).hom x : H) = f.hom x :=
  (rfl)

/-- The corestriction followed by the inclusion is the original morphism. -/
@[reassoc (attr := simp)]
theorem liftHopfSubalgebra_comp_hopfSubalgebraι (hA : Subalgebra.IsHopfSubalgebra A) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) : liftHopfSubalgebra hA f hf ≫ hopfSubalgebraι hA = f := by
  ext x
  exact coe_liftHopfSubalgebra_apply hA f hf x

/-- A morphism into a Hopf subalgebra is determined by its composite with the inclusion. -/
theorem liftHopfSubalgebra_unique (hA : Subalgebra.IsHopfSubalgebra A) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) (g : K ⟶ ofHopfSubalgebra hA) (hg : g ≫ hopfSubalgebraι hA = f) :
    g = liftHopfSubalgebra hA f hf :=
  (cancel_mono (hopfSubalgebraι hA)).mp (by rw [hg, liftHopfSubalgebra_comp_hopfSubalgebraι])

/-- **Universal property of a Hopf subalgebra.** A morphism of commutative Hopf algebras into `H`
factors through the inclusion of a Hopf subalgebra `A` exactly when its image lies in `A`. -/
theorem exists_comp_hopfSubalgebraι_iff (hA : Subalgebra.IsHopfSubalgebra A) (f : K ⟶ H) :
    (∃ g : K ⟶ ofHopfSubalgebra hA, g ≫ hopfSubalgebraι hA = f) ↔ ∀ x, f.hom x ∈ A := by
  refine ⟨?_, fun hf ↦ ⟨_, liftHopfSubalgebra_comp_hopfSubalgebraι hA f hf⟩⟩
  rintro ⟨g, rfl⟩ x
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
  exact (hopfSubalgebraι_apply hA _).symm ▸ (g.hom x : A).2

end TauCeti.CommHopfAlgCat
