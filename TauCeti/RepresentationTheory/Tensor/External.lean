/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.Flat.Basic
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# External tensor products of representations

For a representation `ρ` of a monoid `G` on `V` and a representation `σ` of a monoid `H` on `W`,
the **external tensor product** `ρ.externalTensor σ` is the representation of the product
`G × H` on `V ⊗ W` in which `(g, h)` acts by `ρ g ⊗ σ h`, so that
`(g, h) • (v ⊗ w) = ρ g v ⊗ σ h w`. It is the internal tensor product `Representation.tprod`
of the pullbacks of `ρ` and `σ` along the two projections of `G × H`.

It is not the direct sum `Representation.prod`, nor the internal tensor product of two
representations of one group: the internal tensor product of two representations of `G` is the
restriction of their external tensor product along the diagonal `G → G × G`
(`Representation.externalTensor_comp_diag`).

This file provides the construction with its functoriality in intertwining maps and equivalences,
the comparisons of the external tensor product with the swap of the two factors, with
reassociation, with the trivial line, with duals and with binary direct sums, and two facts on
which the classification of the irreducible representations of a product of groups rests:

* the character of `ρ.externalTensor σ` at `(g, h)` is `χ_ρ(g) * χ_σ(h)`;
* over an algebraically closed field, the external tensor product of a finite-dimensional
  irreducible representation and an irreducible representation is irreducible. The proof is
  Burnside's density theorem for the first factor
  (`Representation.exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul`): a nonzero
  subrepresentation contains some `v ⊗ m` with `m ≠ 0` for every `v`, and the vectors `m` with
  this property form a nonzero subrepresentation of the irreducible second factor.

Only the first factor needs to be finite-dimensional, and neither factor needs to be a
representation of a finite group.

## Main definitions

* `Representation.externalTensor`: the external tensor product of two representations.
* `Representation.IntertwiningMap.externalTensor` and `Representation.Equiv.externalTensor`: the
  external tensor product of intertwining maps and of equivalences.
* `Representation.externalTensorComm`, `Representation.externalTensorAssoc`,
  `Representation.externalTensorRid`, `Representation.externalTensorLid`,
  `Representation.externalTensorDual`, `Representation.externalTensorProdLeft` and
  `Representation.externalTensorProdRight`: the comparison equivalences.

## Main results

* `Representation.externalTensor_apply_tmul`: `(g, h)` acts on `v ⊗ w` by `ρ g v ⊗ σ h w`.
* `Representation.externalTensor_comp_diag`: along the diagonal, the external tensor product
  restricts to the internal one.
* `Representation.char_externalTensor`: the character is `χ_ρ(g) * χ_σ(h)`.
* `Representation.isIrreducible_externalTensor`: the external tensor product of irreducible
  representations over an algebraically closed field is irreducible.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  Exercise 2.36.
* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §3.2.
-/

public section

open TensorProduct

namespace Representation

section Monoid

variable {k G H K V V' W W' U : Type*} [CommSemiring k] [Monoid G] [Monoid H] [Monoid K]
  [AddCommMonoid V] [Module k V] [AddCommMonoid V'] [Module k V']
  [AddCommMonoid W] [Module k W] [AddCommMonoid W'] [Module k W']
  [AddCommMonoid U] [Module k U]

/-- **The external tensor product** of a representation `ρ` of `G` on `V` and a representation
`σ` of `H` on `W`: the representation of `G × H` on `V ⊗ W` in which `(g, h)` acts by
`ρ g ⊗ σ h`. It is the tensor product of the pullbacks of `ρ` and `σ` along the two
projections. -/
noncomputable def externalTensor (ρ : Representation k G V) (σ : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) :=
  tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

variable (ρ : Representation k G V) (ρ' : Representation k G V') (σ : Representation k H W)
  (σ' : Representation k H W') (τ : Representation k K U)

@[simp]
theorem externalTensor_apply (p : G × H) :
    ρ.externalTensor σ p = TensorProduct.map (ρ p.1) (σ p.2) :=
  (rfl)

theorem externalTensor_apply_tmul (p : G × H) (v : V) (w : W) :
    ρ.externalTensor σ p (v ⊗ₜ w) = ρ p.1 v ⊗ₜ σ p.2 w := by
  simp

/-- **The internal tensor product is the diagonal restriction of the external one.** -/
@[simp]
theorem externalTensor_comp_diag (σ : Representation k G W) :
    (ρ.externalTensor σ).comp ((MonoidHom.id G).prod (MonoidHom.id G)) = ρ.tprod σ :=
  (rfl)

/-- The first factor `G × 1` acts on the first tensor factor only. -/
@[simp]
theorem externalTensor_comp_inl :
    (ρ.externalTensor σ).comp (MonoidHom.inl G H) = ρ.tprod (trivial k G W) := by
  ext g : 1
  exact TensorProduct.ext' fun _ _ ↦ by simp

/-- The second factor `1 × H` acts on the second tensor factor only. -/
@[simp]
theorem externalTensor_comp_inr :
    (ρ.externalTensor σ).comp (MonoidHom.inr G H) = (trivial k H V).tprod σ := by
  ext h : 1
  exact TensorProduct.ext' fun _ _ ↦ by simp

/-! ### Functoriality -/

namespace IntertwiningMap

variable {ρ ρ' σ σ'}

/-- **The external tensor product of two intertwining maps**, acting as `f ⊗ g` on the underlying
modules. -/
noncomputable def externalTensor (f : IntertwiningMap ρ ρ') (g : IntertwiningMap σ σ') :
    IntertwiningMap (ρ.externalTensor σ) (ρ'.externalTensor σ') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' p := TensorProduct.ext' fun v w ↦ by
    simp [IntertwiningMap.isIntertwining]

@[simp]
theorem externalTensor_tmul (f : IntertwiningMap ρ ρ') (g : IntertwiningMap σ σ') (v : V)
    (w : W) : f.externalTensor g (v ⊗ₜ w) = f v ⊗ₜ g w :=
  (rfl)

@[simp]
theorem externalTensor_id :
    (IntertwiningMap.id ρ).externalTensor (IntertwiningMap.id σ) =
      IntertwiningMap.id (ρ.externalTensor σ) :=
  IntertwiningMap.ext (TensorProduct.map_id)

theorem externalTensor_comp {V'' W'' : Type*} [AddCommMonoid V''] [Module k V'']
    [AddCommMonoid W''] [Module k W''] {ρ'' : Representation k G V''}
    {σ'' : Representation k H W''} (f₂ : IntertwiningMap ρ' ρ'') (f₁ : IntertwiningMap ρ ρ')
    (g₂ : IntertwiningMap σ' σ'') (g₁ : IntertwiningMap σ σ') :
    (f₂.comp f₁).externalTensor (g₂.comp g₁) =
      (f₂.externalTensor g₂).comp (f₁.externalTensor g₁) :=
  IntertwiningMap.ext (TensorProduct.map_comp _ _ _ _)

end IntertwiningMap

namespace Equiv

variable {ρ ρ' σ σ'}

/-- **The external tensor product of two equivalences of representations**, acting as
`e₁ ⊗ e₂` on the underlying modules. -/
noncomputable def externalTensor (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') :
    Equiv (ρ.externalTensor σ) (ρ'.externalTensor σ') :=
  .mk (_root_.TensorProduct.congr e₁.toLinearEquiv e₂.toLinearEquiv) fun p ↦
    TensorProduct.ext' fun v w ↦ by
      simp [IntertwiningMap.isIntertwining ρ ρ' e₁.toIntertwiningMap,
        IntertwiningMap.isIntertwining σ σ' e₂.toIntertwiningMap]

@[simp]
theorem externalTensor_tmul (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') (v : V) (w : W) :
    e₁.externalTensor e₂ (v ⊗ₜ w) = e₁ v ⊗ₜ e₂ w :=
  (rfl)

end Equiv

/-! ### Comparisons -/

/-- **Swapping the two factors.** Pulled back along the swap `H × G ≃* G × H`, the external
tensor product `ρ ⊠ σ` is `σ ⊠ ρ`, through the swap `V ⊗ W ≃ W ⊗ V` of the tensor factors. -/
noncomputable def externalTensorComm :
    Equiv ((ρ.externalTensor σ).comp (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom)
      (σ.externalTensor ρ) :=
  .mk (_root_.TensorProduct.comm k V W) fun _ ↦ TensorProduct.ext' fun _ _ ↦ by simp

@[simp]
theorem externalTensorComm_tmul (v : V) (w : W) :
    ρ.externalTensorComm σ (v ⊗ₜ w) = w ⊗ₜ v :=
  (rfl)

/-- **Reassociating.** Pulled back along `(G × H) × K ≃* G × (H × K)`, the external tensor product
`ρ ⊠ (σ ⊠ τ)` is `(ρ ⊠ σ) ⊠ τ`, through the associator of the tensor product. -/
noncomputable def externalTensorAssoc :
    Equiv ((ρ.externalTensor σ).externalTensor τ)
      ((ρ.externalTensor (σ.externalTensor τ)).comp
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom) :=
  .mk (_root_.TensorProduct.assoc k V W U) fun _ ↦
    TensorProduct.ext (TensorProduct.ext' fun _ _ ↦ LinearMap.ext fun _ ↦ by simp)

@[simp]
theorem externalTensorAssoc_tmul (v : V) (w : W) (u : U) :
    ρ.externalTensorAssoc σ τ ((v ⊗ₜ w) ⊗ₜ u) = v ⊗ₜ (w ⊗ₜ u) :=
  (rfl)

/-- **A trivial line on the right.** Tensoring with the trivial representation of `H` on the
scalars gives the pullback of `ρ` along the first projection. -/
noncomputable def externalTensorRid :
    Equiv (ρ.externalTensor (trivial k H k)) (ρ.comp (MonoidHom.fst G H)) :=
  .mk (_root_.TensorProduct.rid k V) fun _ ↦ TensorProduct.ext' fun _ _ ↦ by simp

@[simp]
theorem externalTensorRid_tmul (v : V) (c : k) :
    ρ.externalTensorRid (H := H) (v ⊗ₜ c) = c • v :=
  (rfl)

/-- **A trivial line on the left.** Tensoring the trivial representation of `G` on the scalars
with `σ` gives the pullback of `σ` along the second projection. -/
noncomputable def externalTensorLid :
    Equiv ((trivial k G k).externalTensor σ) (σ.comp (MonoidHom.snd G H)) :=
  .mk (_root_.TensorProduct.lid k W) fun _ ↦ TensorProduct.ext' fun _ _ ↦ by simp

@[simp]
theorem externalTensorLid_tmul (c : k) (w : W) :
    σ.externalTensorLid (G := G) (c ⊗ₜ w) = c • w :=
  (rfl)

/-- **Direct sums on the left.** The external tensor product distributes over a direct sum in the
first factor. -/
noncomputable def externalTensorProdLeft :
    Equiv ((ρ.prod ρ').externalTensor σ) ((ρ.externalTensor σ).prod (ρ'.externalTensor σ)) :=
  .mk (_root_.TensorProduct.prodLeft k k V V' W) fun _ ↦ TensorProduct.ext' fun x _ ↦ by
    obtain ⟨v, v'⟩ := x
    simp

@[simp]
theorem externalTensorProdLeft_tmul (x : V × V') (w : W) :
    ρ.externalTensorProdLeft ρ' σ (x ⊗ₜ w) = (x.1 ⊗ₜ w, x.2 ⊗ₜ w) :=
  (rfl)

/-- **Direct sums on the right.** The external tensor product distributes over a direct sum in
the second factor. -/
noncomputable def externalTensorProdRight :
    Equiv (ρ.externalTensor (σ.prod σ')) ((ρ.externalTensor σ).prod (ρ.externalTensor σ')) :=
  .mk (_root_.TensorProduct.prodRight k k V W W') fun _ ↦ TensorProduct.ext' fun _ y ↦ by
    obtain ⟨w, w'⟩ := y
    simp

@[simp]
theorem externalTensorProdRight_tmul (v : V) (y : W × W') :
    ρ.externalTensorProdRight σ σ' (v ⊗ₜ y) = (v ⊗ₜ y.1, v ⊗ₜ y.2) :=
  (rfl)

end Monoid

section Group

variable {k G H V W : Type*} [CommSemiring k] [Group G] [Group H]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  [Module.Finite k V] [Module.Projective k V] [Module.Finite k W] [Module.Projective k W]
  (ρ : Representation k G V) (σ : Representation k H W)

/-- **Duals.** For finite projective modules, the external tensor product of the duals is the
dual of the external tensor product, through `TensorProduct.dualDistribEquiv`, which sends
`f ⊗ g` to the linear form `v ⊗ w ↦ f v * g w`. -/
noncomputable def externalTensorDual :
    Equiv (ρ.dual.externalTensor σ.dual) (ρ.externalTensor σ).dual :=
  .mk (_root_.TensorProduct.dualDistribEquiv k V W) fun _ ↦ TensorProduct.ext' fun _ _ ↦
    TensorProduct.ext' fun _ _ ↦ by simp [Module.Dual.transpose_apply]

@[simp]
theorem externalTensorDual_tmul_apply_tmul (f : Module.Dual k V) (g : Module.Dual k W) (v : V)
    (w : W) : ρ.externalTensorDual σ (f ⊗ₜ g) (v ⊗ₜ w) = f v * g w := by
  simp [externalTensorDual, mul_comm]

end Group

section Field

variable {k G H V W : Type*} [Field k] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k H W)

/-- **The character of an external tensor product** is the product of the characters of the two
factors: `χ_{ρ ⊠ σ}(g, h) = χ_ρ(g) * χ_σ(h)`. -/
@[simp]
theorem char_externalTensor [FiniteDimensional k V] [FiniteDimensional k W] (p : G × H) :
    (ρ.externalTensor σ).character p = ρ.character p.1 * σ.character p.2 :=
  LinearMap.trace_tensorProduct' (ρ p.1) (σ p.2)

open scoped MonoidAlgebra in
/-- The action of the monoid algebra of `G` on the first tensor factor preserves every
subrepresentation of the external tensor product. -/
private theorem rTensor_asAlgebraHom_mem (N : Subrepresentation (ρ.externalTensor σ)) (r : k[G])
    {z : V ⊗[k] W} (hz : z ∈ N.toSubmodule) :
    (ρ.asAlgebraHom r).rTensor W z ∈ N.toSubmodule := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, LinearMap.rTensor_add, LinearMap.add_apply]
    exact N.toSubmodule.add_mem ha hb
  | single g c =>
    have h := N.apply_mem_toSubmodule (g, 1) hz
    rw [externalTensor_apply, map_one, Module.End.one_eq_id] at h
    rw [asAlgebraHom_single, LinearMap.rTensor_smul, LinearMap.smul_apply]
    exact N.toSubmodule.smul_mem c h

/-- **External tensor products of irreducibles are irreducible.** Over an algebraically closed
field, if `ρ` is a finite-dimensional irreducible representation of `G` and `σ` an irreducible
representation of `H`, then `ρ.externalTensor σ` is an irreducible representation of `G × H`. -/
theorem isIrreducible_externalTensor [IsAlgClosed k] [FiniteDimensional k V]
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) : (ρ.externalTensor σ).IsIrreducible := by
  have := hρ.nontrivial
  have := hσ.nontrivial
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have : Nontrivial (V ⊗[k] W) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right k V W
      (LinearMap.toSpanSingleton k V v₀) (smul_left_injective k hv₀)
  refine ⟨fun N ↦ (eq_or_ne N ⊥).imp_right fun hN ↦ ?_⟩
  obtain ⟨z, hzN, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot fun h : N.toSubmodule = ⊥ ↦
    hN (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
  -- By Burnside density on the first factor, `N` contains `v ⊗ m` for one `m ≠ 0` and every `v`.
  obtain ⟨m, hm, hr⟩ := exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul ρ hρ hz
  -- The vectors `w` with `v ⊗ w ∈ N` for every `v` form a subrepresentation of `σ`.
  let M : Subrepresentation σ :=
    { toSubmodule :=
        { carrier := {w | ∀ v : V, v ⊗ₜ[k] w ∈ N.toSubmodule}
          add_mem' := fun ha hb v ↦ by
            simpa [TensorProduct.tmul_add] using N.toSubmodule.add_mem (ha v) (hb v)
          zero_mem' := fun v ↦ by simp
          smul_mem' := fun c w hw v ↦ by
            simpa [TensorProduct.tmul_smul] using N.toSubmodule.smul_mem c (hw v) }
      apply_mem_toSubmodule := fun h w hw v ↦ by
        simpa using N.apply_mem_toSubmodule (1, h) (hw v) }
  have hmM : m ∈ M.toSubmodule := fun v ↦ by
    obtain ⟨r, hr⟩ := hr v
    exact hr ▸ rTensor_asAlgebraHom_mem ρ σ N r hzN
  have hM : M = ⊤ := (hσ.eq_bot_or_eq_top M).resolve_left fun h ↦ hm <| by
    simpa [h] using hmM
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.mpr ?_)
  rw [← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨v, w, rfl⟩
  have hw : w ∈ M.toSubmodule := by simp [hM]
  exact hw v

end Field

end Representation
