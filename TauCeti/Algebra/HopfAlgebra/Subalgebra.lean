/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

## Main declarations

* `Subalgebra.IsHopfSubalgebra`: a subalgebra stable under comultiplication and the antipode.
* `Subalgebra.IsHopfSubalgebra.hopfAlgebra`: the restricted Hopf algebra structure, under
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

namespace Subalgebra

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

variable {A : Subalgebra R H} [Module.Flat R H] [Module.Flat R A]

private theorem map_val_injective :
    Function.Injective (Algebra.TensorProduct.map A.val A.val) :=
  Algebra.TensorProduct.map_injective_of_flat_flat A.val A.val
    Subtype.val_injective Subtype.val_injective

private theorem map_val_map_val_injective :
    Function.Injective (TensorProduct.map A.val.toLinearMap
      (TensorProduct.map A.val.toLinearMap A.val.toLinearMap)) :=
  TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective map_val_injective

variable (hA : A.IsHopfSubalgebra)
include hA

omit [Module.Flat R H] [Module.Flat R A] in
private theorem comulAlgHom_comp_val_mem_range (x : A) :
    (Bialgebra.comulAlgHom R H).comp A.val x ∈ (Algebra.TensorProduct.map A.val A.val).range := by
  have h := hA.comul_mem x.2
  rw [toSubmodule_subtype] at h
  obtain ⟨y, hy⟩ := h
  -- `Algebra.TensorProduct.map` is defined as the linear `TensorProduct.map` of its arguments.
  exact ⟨y, hy⟩

/-- The comultiplication of a Hopf subalgebra, valued in its own tensor square: the unique
preimage of the comultiplication of `H` under the injective map `A ⊗[R] A → H ⊗[R] H`. -/
noncomputable def comulAlgHom : A →ₐ[R] A ⊗[R] A :=
  (AlgEquiv.ofInjective _ map_val_injective).symm.toAlgHom.comp
    (((Bialgebra.comulAlgHom R H).comp A.val).codRestrict _ hA.comulAlgHom_comp_val_mem_range)

/-- The comultiplication of a Hopf subalgebra is the restriction of that of `H`. -/
theorem map_val_comulAlgHom (x : A) :
    Algebra.TensorProduct.map A.val A.val (hA.comulAlgHom x) = Coalgebra.comul (R := R) (x : H) :=
  (AlgEquiv.ofInjective_apply _ map_val_injective _).symm.trans
    (congrArg Subtype.val (AlgEquiv.apply_symm_apply _ _))

private theorem map_val_comulAlgHom' (x : A) :
    TensorProduct.map A.val.toLinearMap A.val.toLinearMap (hA.comulAlgHom x) =
      Coalgebra.comul (R := R) (x : H) :=
  -- `Algebra.TensorProduct.map` is defined as the linear `TensorProduct.map` of its arguments.
  hA.map_val_comulAlgHom x

private theorem coassoc_comulAlgHom :
    TensorProduct.assoc R A A A ∘ₗ hA.comulAlgHom.toLinearMap.rTensor A ∘ₗ
        hA.comulAlgHom.toLinearMap =
      hA.comulAlgHom.toLinearMap.lTensor A ∘ₗ hA.comulAlgHom.toLinearMap := by
  let ι := A.val.toLinearMap
  have hcomul : TensorProduct.map ι ι ∘ₗ hA.comulAlgHom.toLinearMap =
      (Coalgebra.comul (R := R) (A := H)) ∘ₗ ι :=
    LinearMap.ext hA.map_val_comulAlgHom'
  have hleft (t : A ⊗[R] A) :
      TensorProduct.map ι (TensorProduct.map ι ι)
          (TensorProduct.assoc R A A A (hA.comulAlgHom.toLinearMap.rTensor A t)) =
        TensorProduct.assoc R H H H
          ((Coalgebra.comul (R := R) (A := H)).rTensor H (TensorProduct.map ι ι t)) := by
    rw [TensorProduct.map_map_assoc, LinearMap.map_rTensor, hcomul]
    simp only [LinearMap.rTensor, TensorProduct.map_map, LinearMap.id_comp]
  have hright (t : A ⊗[R] A) :
      TensorProduct.map ι (TensorProduct.map ι ι) (hA.comulAlgHom.toLinearMap.lTensor A t) =
        (Coalgebra.comul (R := R) (A := H)).lTensor H (TensorProduct.map ι ι t) := by
    rw [LinearMap.map_lTensor, hcomul]
    simp only [LinearMap.lTensor, TensorProduct.map_map, LinearMap.id_comp]
  ext x
  apply map_val_map_val_injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  rw [hleft, hright, map_val_comulAlgHom', Coalgebra.coassoc_apply]

private theorem rTensor_counit_comulAlgHom :
    (Coalgebra.counit (R := R) (A := H) ∘ₗ A.val.toLinearMap).rTensor A ∘ₗ
        hA.comulAlgHom.toLinearMap = TensorProduct.mk R R A 1 := by
  have h (t : A ⊗[R] A) :
      (TensorProduct.lid R A
          ((Coalgebra.counit (R := R) (A := H) ∘ₗ A.val.toLinearMap).rTensor A t) : H) =
        TensorProduct.lid R H ((Coalgebra.counit (R := R) (A := H)).rTensor H
          (TensorProduct.map A.val.toLinearMap A.val.toLinearMap t)) := by
    let ι := A.val.toLinearMap
    let ε := Coalgebra.counit (R := R) (A := H)
    -- `CoassocSimps.lid_comp_map` is stated for linear maps. Expose the subtype
    -- coercion as `ι` and the counit as `ε` to match its two sides.
    change ι (TensorProduct.lid R A (((ε ∘ₗ ι).rTensor A) t)) =
      TensorProduct.lid R H (ε.rTensor H (TensorProduct.map ι ι t))
    simpa only [LinearMap.rTensor, TensorProduct.map_map, LinearMap.id_comp,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using
      (LinearMap.congr_fun (CoassocSimps.lid_comp_map (ε ∘ₗ ι) ι) t).symm
  ext x
  apply (TensorProduct.lid R A).injective
  apply Subtype.val_injective
  simp [h, map_val_comulAlgHom']

private theorem lTensor_counit_comulAlgHom :
    (Coalgebra.counit (R := R) (A := H) ∘ₗ A.val.toLinearMap).lTensor A ∘ₗ
        hA.comulAlgHom.toLinearMap = (TensorProduct.mk R A R).flip 1 := by
  have h (t : A ⊗[R] A) :
      (TensorProduct.rid R A
          ((Coalgebra.counit (R := R) (A := H) ∘ₗ A.val.toLinearMap).lTensor A t) : H) =
        TensorProduct.rid R H ((Coalgebra.counit (R := R) (A := H)).lTensor H
          (TensorProduct.map A.val.toLinearMap A.val.toLinearMap t)) := by
    let ι := A.val.toLinearMap
    let ε := Coalgebra.counit (R := R) (A := H)
    -- `CoassocSimps.rid_comp_map` likewise uses linear maps; identify the subtype
    -- coercion with `ι` before applying that lemma to the right counit law.
    change ι (TensorProduct.rid R A (((ε ∘ₗ ι).lTensor A) t)) =
      TensorProduct.rid R H (ε.lTensor H (TensorProduct.map ι ι t))
    simpa only [LinearMap.lTensor, TensorProduct.map_map, LinearMap.id_comp,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using
      (LinearMap.congr_fun (CoassocSimps.rid_comp_map ι (ε ∘ₗ ι)) t).symm
  ext x
  apply (TensorProduct.rid R A).injective
  apply Subtype.val_injective
  simp [h, map_val_comulAlgHom']

/-- The restriction of the antipode of `H` to a Hopf subalgebra. -/
private def antipode : A →ₗ[R] A where
  toFun x := ⟨HopfAlgebra.antipode R (x : H), hA.antipode_mem x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

private theorem mul_antipode_rTensor_comulAlgHom (x : A) :
    LinearMap.mul' R A ((antipode hA).rTensor A (hA.comulAlgHom x)) =
      algebraMap R A (Coalgebra.counit (R := R) (x : H)) := by
  have h (t : A ⊗[R] A) :
      (LinearMap.mul' R A ((antipode hA).rTensor A t) : H) =
        LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H
          (TensorProduct.map A.val.toLinearMap A.val.toLinearMap t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp [antipode]
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
    | tmul a b => simp [antipode]
    | add s t hs ht => simp only [map_add, Subalgebra.coe_add, hs, ht]
  apply Subtype.val_injective
  simp [h, map_val_comulAlgHom']

/-- The Hopf algebra structure on a flat Hopf subalgebra of a flat Hopf algebra: comultiplication,
counit and antipode are restricted from `H`. This is not an instance because it depends on the
proof `hA`. -/
@[instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R A where
  comul := hA.comulAlgHom.toLinearMap
  counit := Coalgebra.counit (R := R) (A := H) ∘ₗ A.val.toLinearMap
  coassoc := hA.coassoc_comulAlgHom
  rTensor_counit_comp_comul := hA.rTensor_counit_comulAlgHom
  lTensor_counit_comp_comul := hA.lTensor_counit_comulAlgHom
  counit_one := by simp
  mul_compr₂_counit := by ext; simp
  comul_one := map_one hA.comulAlgHom
  mul_compr₂_comul := by ext x y; exact map_mul hA.comulAlgHom x y
  antipode := antipode hA
  mul_antipode_rTensor_comul := LinearMap.ext hA.mul_antipode_rTensor_comulAlgHom
  mul_antipode_lTensor_comul := LinearMap.ext hA.mul_antipode_lTensor_comulAlgHom

end IsHopfSubalgebra

end Subalgebra

namespace TauCeti.CommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R} {A : Subalgebra R H}
variable [Module.Flat R H] [Module.Flat R A]

/-- A flat Hopf subalgebra of a flat commutative Hopf algebra, as a bundled commutative Hopf
algebra. -/
noncomputable abbrev ofHopfSubalgebra (hA : A.IsHopfSubalgebra) : _root_.CommHopfAlgCat.{v} R :=
  letI := hA.hopfAlgebra
  _root_.CommHopfAlgCat.of R A

/-- The inclusion of a Hopf subalgebra as a morphism of commutative Hopf algebras. -/
noncomputable def hopfSubalgebraι (hA : A.IsHopfSubalgebra) : ofHopfSubalgebra hA ⟶ H :=
  letI := hA.hopfAlgebra
  -- The counit of `hA.hopfAlgebra` is by definition the counit of `H` restricted to `A`.
  _root_.CommHopfAlgCat.ofHom (BialgHom.ofAlgHom A.val (by ext; rfl)
    (AlgHom.ext hA.map_val_comulAlgHom))

/-- The inclusion morphism of a Hopf subalgebra is the inclusion of the underlying subalgebra. -/
@[simp]
theorem hopfSubalgebraι_apply (hA : A.IsHopfSubalgebra) (x : A) :
    (hopfSubalgebraι hA).hom x = x :=
  (rfl)

/-- The inclusion morphism of a Hopf subalgebra is injective. -/
theorem hopfSubalgebraι_injective (hA : A.IsHopfSubalgebra) :
    Function.Injective (hopfSubalgebraι hA).hom :=
  Subtype.val_injective

instance (hA : A.IsHopfSubalgebra) : Mono (hopfSubalgebraι hA) :=
  ConcreteCategory.mono_of_injective _ (hopfSubalgebraι_injective hA)

/-- A morphism of commutative Hopf algebras whose image lies in a Hopf subalgebra, corestricted
to that Hopf subalgebra. -/
noncomputable def liftHopfSubalgebra (hA : A.IsHopfSubalgebra) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) : K ⟶ ofHopfSubalgebra hA :=
  letI := hA.hopfAlgebra
  -- The counit of `hA.hopfAlgebra` is by definition the counit of `H` restricted to `A`.
  _root_.CommHopfAlgCat.ofHom (BialgHom.ofAlgHom ((f.hom : K →ₐ[R] H).codRestrict A hf)
    (by ext x; exact (CoalgHomClass.counit_comp_apply f.hom x :))
    (by
      ext x
      apply Subalgebra.IsHopfSubalgebra.map_val_injective
      refine Eq.trans ?_ (hA.map_val_comulAlgHom _).symm
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
      exact (CoalgHomClass.map_comp_comul_apply f.hom x :)))

/-- The corestricted morphism has the same values as the original one. -/
@[simp]
theorem coe_liftHopfSubalgebra_apply (hA : A.IsHopfSubalgebra) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) (x : K) :
    ((liftHopfSubalgebra hA f hf).hom x : H) = f.hom x :=
  (rfl)

/-- The corestriction followed by the inclusion is the original morphism. -/
@[reassoc (attr := simp)]
theorem liftHopfSubalgebra_comp_hopfSubalgebraι (hA : A.IsHopfSubalgebra) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) : liftHopfSubalgebra hA f hf ≫ hopfSubalgebraι hA = f := by
  ext x
  exact coe_liftHopfSubalgebra_apply hA f hf x

/-- A morphism into a Hopf subalgebra is determined by its composite with the inclusion. -/
theorem liftHopfSubalgebra_unique (hA : A.IsHopfSubalgebra) (f : K ⟶ H)
    (hf : ∀ x, f.hom x ∈ A) (g : K ⟶ ofHopfSubalgebra hA) (hg : g ≫ hopfSubalgebraι hA = f) :
    g = liftHopfSubalgebra hA f hf :=
  (cancel_mono (hopfSubalgebraι hA)).mp (by rw [hg, liftHopfSubalgebra_comp_hopfSubalgebraι])

/-- **Universal property of a Hopf subalgebra.** A morphism of commutative Hopf algebras into `H`
factors through the inclusion of a Hopf subalgebra `A` exactly when its image lies in `A`. -/
theorem exists_comp_hopfSubalgebraι_iff (hA : A.IsHopfSubalgebra) (f : K ⟶ H) :
    (∃ g : K ⟶ ofHopfSubalgebra hA, g ≫ hopfSubalgebraι hA = f) ↔ ∀ x, f.hom x ∈ A := by
  refine ⟨?_, fun hf ↦ ⟨_, liftHopfSubalgebra_comp_hopfSubalgebraι hA f hf⟩⟩
  rintro ⟨g, rfl⟩ x
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
  exact (hopfSubalgebraι_apply hA _).symm ▸ (g.hom x : A).2

end TauCeti.CommHopfAlgCat
