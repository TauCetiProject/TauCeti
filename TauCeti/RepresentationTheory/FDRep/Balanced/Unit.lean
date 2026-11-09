/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Balanced.Evaluation
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basis
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The balanced tensor–Hom unit

For a simple finite-dimensional representation `A`, tensoring with a multiplicity
vector identifies any right `End A`-module `M` with the intertwiners from `A` into
`M ⊗_{End A} A`. The target action is specified by its pure-tensor formula:
it acts only on `A`. This formulation applies directly to restrictions of other
representations, without transporting intertwiners along an equality of actions.
No ambient group, normal subgroup, section or semilinear action is required.

The tensor is balanced over the full endomorphism division algebra, not just the
ground field, and `M` may be infinite-dimensional. The unit is canonical; its
bijectivity proof uses a right-commutant basis. A nonzero vector of `A` detects
which coordinate endomorphisms vanish, giving finite support for each intertwiner.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
* `Module.Basis.balancedTensorProductEquiv` supplies tensor coordinates.
-/

public noncomputable section

namespace FDRep

open CategoryTheory MulOpposite TauCeti

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Monoid G] (A : FDRep k G)
  {M : Type w} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]

local notation "R" => forget₂ (FDRep k G) (Rep k G)
local notation "F" => (R) ⋙ forget₂ (Rep k G) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k G)

attribute [local instance] endModule

private local instance : IsScalarTower k (End A) V := (F).endModule_isScalarTower A

local notation "E" => BalancedTensorProduct k (End A) M V

variable (ρ : Representation k G
    (BalancedTensorProduct k (End A) M ((forget₂ (FDRep k G) (Rep k G)).obj A)))
  (hρ : ∀ (g : G) (m : M) (x : (forget₂ (FDRep k G) (Rep k G)).obj A),
    ρ g (BalancedTensorProduct.tmul k (End A) m x) =
      BalancedTensorProduct.tmul k (End A)
        (N := (forget₂ (FDRep k G) (Rep k G)).obj A) m (A.ρ g x))

omit [IsScalarTower k (End A)ᵐᵒᵖ M] in
include hρ in
private theorem balancedTensor_action (g : G) (m : M) (x : V) :
    ρ g (BalancedTensorProduct.tmul k (End A) m x) =
      BalancedTensorProduct.tmul k (End A) m ((V).ρ g x) := by
  -- Rewriting the forgotten action changes its carrier view; reflexivity bridges it.
  rw [hρ, FDRep.forget₂_ρ]
  rfl

/-- Tensoring with a multiplicity vector gives an intertwiner into any balanced
tensor representation whose action is on the representation factor alone. -/
def balancedTensorUnit : M →ₗ[k] Representation.IntertwiningMap (V).ρ ρ where
  toFun m :=
    { toLinearMap := BalancedTensorProduct.mk k (End A) m
      isIntertwining' := fun g => by
        ext x
        simpa only [LinearMap.comp_apply, BalancedTensorProduct.mk_apply] using
          (balancedTensor_action A ρ hρ g m x).symm }
  map_add' m m' := by
    ext x
    simp [BalancedTensorProduct.mk_apply]
  map_smul' r m := by
    ext x
    simp [BalancedTensorProduct.mk_apply]

omit [IsScalarTower k (End A)ᵐᵒᵖ M] in
/-- The balanced tensor–Hom unit evaluates to a pure tensor. -/
@[simp]
theorem balancedTensorUnit_apply (m : M) (x : V) :
    balancedTensorUnit A ρ hρ m x =
      BalancedTensorProduct.tmul k (End A) (N := V) m x := by
  simp [balancedTensorUnit, BalancedTensorProduct.mk_apply]

section Coordinates

variable {ι : Type*} (b : Module.Basis ι (End A)ᵐᵒᵖ M)

local notation "e" => b.balancedTensorProductEquiv (k := k) (N := V)

include hρ in
private theorem unit_coordinates_action (g : G) (z : E) :
    e (ρ g z) = Finsupp.mapRange ((V).ρ g) (map_zero _) (e z) := by
  have hg (a : End A) (x : V) : (V).ρ g (a • x) = a • (V).ρ g x := by
    simp only [(F).endModule_smul, Functor.comp_map, Rep.forget₂_moduleCat_map,
      ModuleCat.hom_ofHom]
    exact (((R).map a.asHom).hom.isIntertwining _ _ g x).symm
  have hmap : ρ g =
      BalancedTensorProduct.map LinearMap.id ((V).ρ g) (fun _ _ => rfl) hg := by
    apply BalancedTensorProduct.hom_ext
    intro m x
    simpa only [BalancedTensorProduct.map_tmul, LinearMap.id_apply] using
      balancedTensor_action A ρ hρ g m x
  rw [hmap]
  exact LinearMap.congr_fun (b.balancedTensorProductEquiv_map ((V).ρ g) hg) z

private def unitCoordinate (f : Representation.IntertwiningMap (V).ρ ρ) (i : ι) : End A :=
  End.of (forget₂HomLinearEquiv A A ((Rep.homLinearEquiv V V).symm
    { toLinearMap := (Finsupp.lapply i).comp ((e).toLinearMap.comp f.toLinearMap)
      isIntertwining' := fun g => by
        ext x
        have h := congrArg (fun z => e z i) (f.isIntertwining _ _ g x)
        simpa only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
          unit_coordinates_action A ρ hρ, Finsupp.mapRange_apply,
          Representation.IntertwiningMap.coe_toLinearMap] using h }))

private theorem unitCoordinate_apply (f : Representation.IntertwiningMap (V).ρ ρ)
    (i : ι) (x : V) :
    ((F).map (unitCoordinate A ρ hρ b f i).asHom).hom x = e (f x) i := by
  simp [unitCoordinate, Functor.comp_map, forget₂_map_forget₂HomLinearEquiv,
    Rep.homLinearEquiv]

include b in
private theorem unit_injective_of_basis :
    Function.Injective (balancedTensorUnit A ρ hρ) := by
  intro m m' h
  apply b.repr.injective
  ext i
  apply unop_injective
  apply End.ext
  apply (R).map_injective
  ext x
  have hx := congrArg (fun f : Representation.IntertwiningMap (V).ρ ρ => e (f x) i) h
  simpa only [balancedTensorUnit_apply,
    Module.Basis.balancedTensorProductEquiv_tmul_apply, (F).endModule_smul,
    Functor.comp_map, Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom] using hx

variable [Simple A]

include b in
private theorem unit_surjective_of_basis :
    Function.Surjective (balancedTensorUnit A ρ hρ) := by
  classical
  have : Nontrivial V := by
    have h := isIrreducible_of_simple A
    rw [← FDRep.forget₂_ρ] at h
    exact h.nontrivial
  intro f
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let t := (e (f x)).support
  let d := unitCoordinate A ρ hρ b f
  have hd (i : ι) (hi : i ∉ t) : d i = 0 := by
    have hz : (d i) • x = 0 := by
      rw [(F).endModule_smul, unitCoordinate_apply]
      exact Finsupp.notMem_support_iff.mp hi
    exact (smul_eq_zero.mp hz).resolve_right hx
  let m := b.repr.symm (Finsupp.ofSupportFinite (fun i => op (d i))
    (t.finite_toSet.subset fun i hi => by_contra fun h => hi (by simp [hd i h])))
  have hm (i : ι) : b.repr m i = op (d i) := by
    simp [m, Finsupp.ofSupportFinite_coe]
  refine ⟨m, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  apply (e).injective
  ext i
  simp only [Representation.IntertwiningMap.coe_toLinearMap]
  rw [balancedTensorUnit_apply,
    Module.Basis.balancedTensorProductEquiv_tmul_apply, hm, unop_op,
    (F).endModule_smul, unitCoordinate_apply]

end Coordinates

variable [Simple A]

/-- Over the full commutant of a simple representation, the tensor–Hom unit is
bijective for arbitrary right multiplicity modules. -/
theorem balancedTensorUnit_bijective :
    Function.Bijective (balancedTensorUnit A ρ hρ) :=
  ⟨unit_injective_of_basis A ρ hρ (Module.Free.chooseBasis _ _),
    unit_surjective_of_basis A ρ hρ (Module.Free.chooseBasis _ _)⟩

/-- The ground-field-linear balanced tensor–Hom unit equivalence. -/
def balancedTensorUnitEquiv : M ≃ₗ[k] Representation.IntertwiningMap (V).ρ ρ :=
  LinearEquiv.ofBijective (balancedTensorUnit A ρ hρ) (balancedTensorUnit_bijective A ρ hρ)

/-- The unit equivalence has the canonical tensoring map as its forward map. -/
@[simp]
theorem balancedTensorUnitEquiv_apply (m : M) :
    balancedTensorUnitEquiv A ρ hρ m = balancedTensorUnit A ρ hρ m := (rfl)

/-- The inverse unit recovers a multiplicity vector from its tensoring map. -/
@[simp]
theorem balancedTensorUnitEquiv_symm_balancedTensorUnit (m : M) :
    (balancedTensorUnitEquiv A ρ hρ).symm (balancedTensorUnit A ρ hρ m) = m :=
  (balancedTensorUnitEquiv A ρ hρ).symm_apply_apply m

/-- Tensoring with the recovered multiplicity vector gives the original intertwiner. -/
@[simp]
theorem balancedTensorUnit_balancedTensorUnitEquiv_symm_apply
    (f : Representation.IntertwiningMap (V).ρ ρ) :
    balancedTensorUnit A ρ hρ ((balancedTensorUnitEquiv A ρ hρ).symm f) = f :=
  (balancedTensorUnitEquiv A ρ hρ).apply_symm_apply f

end FDRep
