/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Functoriality of symmetric tensor powers, and the symmetrization back into the tensor power

This file equips Mathlib's symmetric tensor power with the linear map induced by a linear map of
the underlying modules, and the linear equivalence induced by a linear equivalence. It proves the
expected action on pure tensors, identity law, and composition law. It also records that a
symmetric power indexed by a finite type is finitely generated when its underlying module is.

It then builds the map back, `SymmetricPower.toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M`,
for a finite index type. The **symmetrization** `∑_σ σ` of the tensor power is constant on the
fibres of the quotient map `SymmetricPower.mk`, because reindexing a pure tensor only permutes the
terms of that sum, so it descends to the symmetric power; `toTensorPower` is that descent. It is
the exact counterpart of Mathlib's `exteriorPower.toTensorPower`, and it takes a pure symmetric
tensor to the sum of the pure tensors over all orderings of its factors.

Composing back the other way multiplies by the order of the permutation group: `mk ∘ toTensorPower`
is `(card ι)!`, because each of the `(card ι)!` reorderings becomes the same symmetric tensor
again. So as soon as `(card ι)!` is a unit -- for instance over a `ℚ`-algebra -- the symmetrization
is injective, and it identifies the symmetric power with the image of the symmetrization operator
inside the tensor power. That is the statement a Young symmetrizer of a one-row shape consumes.

## Main definitions

* `SymmetricPower.map` is the map induced on a symmetric tensor power.
* `SymmetricPower.congr` is the linear equivalence induced by a linear equivalence.
* `SymmetricPower.toTensorPower` is the symmetrization, from the symmetric power back into the
  tensor power.

## Main results

* `SymmetricPower.ext`: linear maps out of a symmetric power are determined by pure tensors.
* `LinearMap.apply_mem_of_forall_symmetricPower_tprod`: a linear map out of a symmetric power
  lands in a submodule once every pure tensor does.
* `SymmetricPower.toTensorPower_tprod`: the symmetrization of a pure symmetric tensor is the sum
  of the pure tensors over all orderings of its factors.
* `SymmetricPower.mk_comp_toTensorPower`: composing the symmetrization with the quotient map is
  multiplication by `(card ι)!`.
* `SymmetricPower.toTensorPower_injective`: the symmetrization is injective once `(card ι)!` is a
  unit.
* `SymmetricPower.range_toTensorPower`: its image is the image of the symmetrization operator on
  the tensor power.
* `SymmetricPower.toTensorPower_comp_map`: the symmetrization is natural in the module.

## References

The quotient construction of `SymmetricPower`, including `SymmetricPower.mk` and
`SymmetricPower.tprod`, is from Kenny Lau's
`Mathlib.LinearAlgebra.TensorPower.Symmetric`.
-/

public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {ι : Type w} {M : Type v}

namespace SymmetricPower

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- A linear map out of a symmetric power is determined by its values on pure symmetric
tensors. -/
@[ext]
theorem ext {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h :=
  LinearMap.ext_on_range (span_tprod_eq_top R ι M) hgh

/-- A linear map sends every symmetric tensor into a submodule if it does so on pure tensors. -/
theorem _root_.LinearMap.apply_mem_of_forall_symmetricPower_tprod (f : Sym[R] ι M →ₗ[R] N)
    (p : Submodule R N) (h : ∀ m : ι → M, f (⨂ₛ[R] i, m i) ∈ p) (x : Sym[R] ι M) : f x ∈ p := by
  have hle : Submodule.span R (Set.range (tprod R)) ≤ p.comap f :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun m => Submodule.mem_comap.2 (h m))
  exact hle (span_tprod_eq_top R ι M ▸ Submodule.mem_top)

private theorem map_rel (f : M →ₗ[R] N) :
    addConGen (Rel R ι M) ≤
      AddCon.ker ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom) := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      apply (AddCon.ker_rel _).2
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        PiTensorProduct.map_tprod, tprod, LinearMap.compMultilinearMap_apply,
        Function.comp_apply] using (tprod_equiv (R := R) e (f ∘ m)).symm

/-- A linear map induces a linear map on every symmetric tensor power. -/
noncomputable def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (Rel R ι M)).lift
      ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x =>
    congrArg (mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)

/-- The map on symmetric powers commutes with the quotient map from the tensor power. -/
@[simp]
theorem map_mk (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map f (mk R ι M x) = mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  AddCon.lift_mk' (map_rel f) x

/-- The map induced on symmetric powers sends a pure tensor to the tensor of the images. -/
@[simp]
theorem map_tprod (f : M →ₗ[R] N) (m : ι → M) :
    map f (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) := by
  simp only [tprod, LinearMap.compMultilinearMap_apply, map_mk,
    PiTensorProduct.map_tprod]

/-- The map induced by the identity is the identity on the symmetric power. -/
@[simp]
theorem map_id :
    map (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  ext m
  simp

/-- Symmetric powers preserve composition of linear maps. -/
@[simp]
theorem map_comp {P : Type*} [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map (ι := ι) g).comp (map (ι := ι) f) := by
  ext m
  simp

/-- A linear equivalence induces a linear equivalence on every symmetric tensor power. -/
noncomputable def congr (e : M ≃ₗ[R] N) : Sym[R] ι M ≃ₗ[R] Sym[R] ι N :=
  LinearEquiv.ofLinearMap (map e.toLinearMap) (map e.symm.toLinearMap)
    (by rw [← map_comp, e.comp_symm, map_id]) (by rw [← map_comp, e.symm_comp, map_id])

@[simp]
theorem congr_toLinearMap (e : M ≃ₗ[R] N) : (congr (ι := ι) e).toLinearMap = map e.toLinearMap :=
  (rfl)

@[simp]
theorem congr_symm (e : M ≃ₗ[R] N) : (congr (ι := ι) e).symm = congr e.symm :=
  (rfl)

/-- The equivalence induced by the identity is the identity on the symmetric power. -/
@[simp]
theorem congr_refl : congr (ι := ι) (LinearEquiv.refl R M) = LinearEquiv.refl R _ :=
  LinearEquiv.toLinearMap_injective map_id

/-- Symmetric powers preserve composition of linear equivalences. -/
@[simp]
theorem congr_trans {P : Type*} [AddCommMonoid P] [Module R P] (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    congr (ι := ι) (e.trans f) = (congr e).trans (congr f) :=
  LinearEquiv.toLinearMap_injective (map_comp e.toLinearMap f.toLinearMap)

/-- The induced equivalence sends a pure tensor to the tensor of the images. -/
@[simp]
theorem congr_tprod (e : M ≃ₗ[R] N) (m : ι → M) :
    congr e (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, e (m i) :=
  map_tprod e.toLinearMap m

/-- A symmetric power indexed by a finite type is finitely generated when the underlying module
is finitely generated. -/
noncomputable instance finite [Finite ι] [Module.Finite R M] : Module.Finite R (Sym[R] ι M) :=
  Module.Finite.of_surjective (mk R ι M) (LinearMap.range_eq_top.mp (range_mk R ι M))

/-! ### The symmetrization back into the tensor power -/

section Symmetrization

variable [Fintype ι] [DecidableEq ι]

variable (R ι M) in
/-- The symmetrization operator `∑_σ σ` on the tensor power, permuting the tensor factors. -/
private noncomputable def symmetrizer : (⨂[R] (_ : ι), M) →ₗ[R] ⨂[R] (_ : ι), M :=
  ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap

private theorem symmetrizer_tprod (m : ι → M) :
    symmetrizer R ι M (⨂ₜ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [symmetrizer, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm ι)) _ _ fun σ => ?_
  simp

private theorem symmetrizer_rel :
    addConGen (Rel R ι M) ≤ AddCon.ker (symmetrizer R ι M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, symmetrizer_tprod]
      exact Fintype.sum_bijective (e⁻¹ * ·) (Group.mulLeft_bijective _) _ _ fun σ => by simp

variable (R ι M) in
/-- **The symmetrization**, from the symmetric power back into the tensor power: the descent of
the symmetrization operator `∑_σ σ` through the quotient map `SymmetricPower.mk`.

This is the counterpart of Mathlib's `exteriorPower.toTensorPower`. -/
noncomputable def toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M where
  toFun := (addConGen (Rel R ι M)).lift (symmetrizer R ι M).toAddMonoidHom symmetrizer_rel
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (symmetrizer R ι M).map_smul r x

private theorem toTensorPower_mk' (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) = (symmetrizer R ι M).toAddMonoidHom x :=
  AddCon.lift_mk' (f := (symmetrizer R ι M).toAddMonoidHom) symmetrizer_rel x

/-- The symmetrization of the class of a tensor is the sum of its reindexings by all
permutations. -/
@[simp]
theorem toTensorPower_mk (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) =
      ∑ σ : Equiv.Perm ι, PiTensorProduct.reindex R (fun _ : ι => M) σ x := by
  simp [toTensorPower_mk', symmetrizer]

/-- The symmetrization of a pure symmetric tensor is the sum of the pure tensors over all
orderings of its factors. -/
@[simp]
theorem toTensorPower_tprod (m : ι → M) :
    toTensorPower R ι M (⨂ₛ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, toTensorPower_mk', LinearMap.toAddMonoidHom_coe,
    symmetrizer_tprod]

private theorem toTensorPower_comp_mk :
    (toTensorPower R ι M) ∘ₗ mk R ι M =
      ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap :=
  LinearMap.ext fun x => by simp

/-- The image of the symmetrization is the image of the symmetrization operator `∑_σ σ` on the
tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R ι M) =
      LinearMap.range (∑ σ : Equiv.Perm ι,
        ((PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap)) := by
  rw [← toTensorPower_comp_mk, LinearMap.range_comp, range_mk, Submodule.map_top]

/-- Symmetrizing and then projecting back to the symmetric power multiplies by `(card ι)!`: the
`(card ι)!` reorderings of a pure tensor all become the same symmetric tensor. -/
@[simp]
theorem mk_comp_toTensorPower :
    (mk R ι M) ∘ₗ (toTensorPower R ι M) =
      (Fintype.card ι).factorial • LinearMap.id (R := R) (M := Sym[R] ι M) := by
  ext m
  have h (σ : Equiv.Perm ι) : mk R ι M (⨂ₜ[R] i, m (σ i)) = ⨂ₛ[R] i, m i :=
    tprod_equiv σ m
  simp [h, Fintype.card_perm]

/-- The symmetrization is injective as soon as `(card ι)!` is a unit in the base ring, for
instance over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit ((Fintype.card ι).factorial : R)) :
    Function.Injective (toTensorPower R ι M) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the quotient map by `u⁻¹` makes it a left inverse of the symmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • mk R ι M) ?_
  rw [LinearMap.smul_comp, mk_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← hu]
  simp

/-- The symmetrization is natural in the module. -/
theorem toTensorPower_comp_map (f : M →ₗ[R] N) :
    (toTensorPower R ι N) ∘ₗ (map (ι := ι) f) =
      (PiTensorProduct.map fun _ : ι => f) ∘ₗ (toTensorPower R ι M) := by
  ext m
  simp

end Symmetrization

end SymmetricPower
