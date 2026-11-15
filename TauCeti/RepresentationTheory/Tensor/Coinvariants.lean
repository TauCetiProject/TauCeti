/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import TauCeti.RepresentationTheory.OfMulAction

/-!
# Tensor coinvariants with a retract of the regular representation

Let `τ` and `ρ` be representations of a group `G` on `k`-modules `V` and `W`. The coinvariants
`(V ⊗ W)_G` are the balanced tensor product `V ⊗_{k[G]} W`, with `V` made a right `k[G]`-module
by `v · g = τ(g⁻¹) v`: the coinvariant kernel of `τ ⊗ ρ` is spanned by the balancing relations
`τ(g⁻¹) v ⊗ w - v ⊗ ρ(g) w` (`Representation.coinvariantsKer_tprod_eq_span`).

For the regular representation Mathlib identifies `(V ⊗ k[G])_G` with `V`
(`Representation.coinvariantsTprodLeftRegularLEquiv`), sending the class of `v ⊗ x` to the action
on `v` of the antipode `S(x)` of `x`, the linear extension of `g ↦ g⁻¹`
(`Representation.ofCoinvariantsTprodLeftRegular_mk_tmul`). This file extends the identification
to a retract of the regular representation: a representation `ρ` with intertwining maps
`i : ρ → k[G]` and `p : k[G] → ρ` such that `p ∘ i = id`, that is, a direct summand of `k[G]`.
The contraction `v ⊗ w ↦ S(i w) · v` then has kernel exactly the coinvariant kernel of `τ ⊗ ρ`
(`Representation.IntertwiningMap.ker_tprodContraction`), so it identifies `V ⊗_{k[G]} W` with its
image, and that image is the image of the action of `S(e)` on `V` for the idempotent
`e = i (p 1)` of `k[G]` (`Representation.IntertwiningMap.range_tprodContraction`).

This is the module-theoretic fact `V ⊗_A Ae ≅ V e` for an idempotent `e` of an algebra `A`,
stated for group algebras in the language of representations. Over `ℂ` it identifies a balanced
tensor product of a tensor power with a Specht module with a Schur functor.

## Main definitions

* `Representation.IntertwiningMap.tprodContraction`: the contraction `V ⊗ W → V`,
  `v ⊗ w ↦ S(i w) · v`, of an intertwining map `i : ρ → k[G]`.

## Main results

* `Representation.coinvariantsKer_tprod_eq_span`: the coinvariant kernel of a tensor product
  is spanned by the balancing relations.
* `Representation.IntertwiningMap.coinvariantsKer_le_ker_tprodContraction`: the contraction
  vanishes on the coinvariant kernel.
* `Representation.IntertwiningMap.ker_tprodContraction` and
  `Representation.IntertwiningMap.range_tprodContraction`: for a retract of the regular
  representation, the kernel of the contraction is the coinvariant kernel and its image is the
  image of `S(e)`.

## References

* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapter III, for the coinvariants
  `(V ⊗ W)_G` as the tensor product over the group algebra.
-/

public section

open TensorProduct

namespace Representation

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- **The coinvariant kernel of a tensor product is spanned by the balancing relations**
`τ(g⁻¹) v ⊗ w - v ⊗ ρ(g) w`, those of the balanced tensor product `V ⊗_{k[G]} W` for the right
action `v · g = τ(g⁻¹) v`. -/
theorem coinvariantsKer_tprod_eq_span (τ : Representation k G V) (ρ : Representation k G W) :
    Coinvariants.ker (τ.tprod ρ) = Submodule.span k {x | ∃ (v : V) (w : W) (g : G),
      x = τ g⁻¹ v ⊗ₜ w - v ⊗ₜ ρ g w} := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨⟨g, x⟩, rfl⟩
    dsimp only
    induction x using TensorProduct.inductionOn with
    | tmul v w => exact Submodule.subset_span ⟨v, ρ g w, g⁻¹, by simp⟩
    | add x y hx hy =>
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  · rintro _ ⟨v, w, g, rfl⟩
    exact Coinvariants.mem_ker_of_eq g⁻¹ (v ⊗ₜ ρ g w) _ (by simp)

/-- The identification `(V ⊗ k[G])_G ≅ V` sends the class of `v ⊗ x` to the action of the
antipode of `x` on `v`. -/
@[simp]
theorem ofCoinvariantsTprodLeftRegular_mk_tmul (τ : Representation k G V) (v : V)
    (x : MonoidAlgebra k G) :
    ofCoinvariantsTprodLeftRegular τ (Coinvariants.mk _ (v ⊗ₜ x)) =
      τ.asAlgebraHom (HopfAlgebra.antipode k x) v := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [tmul_add, hx, hy]
  | single g r => simp [asAlgebraHom_single]

namespace IntertwiningMap

variable {τ : Representation k G V} {ρ : Representation k G W}

variable (i : ρ.IntertwiningMap (leftRegular k G))

/-- **The contraction of `V ⊗ W` along an intertwining map `i : W → k[G]`**: the map
`v ⊗ w ↦ S(i w) · v` to `V`, where `S` is the antipode of `k[G]`. It factors through the
coinvariants `(V ⊗ W)_G` as the map induced by `i` to `(V ⊗ k[G])_G`, followed by the
identification of the latter with `V`. -/
noncomputable def tprodContraction (τ : Representation k G V) : V ⊗[k] W →ₗ[k] V :=
  ofCoinvariantsTprodLeftRegular τ ∘ₗ
    Coinvariants.map (τ.tprod ρ) (τ.tprod (leftRegular k G)) (i.lTensor τ) ∘ₗ Coinvariants.mk _

/-- The contraction as the composite of the coinvariant projection, the map induced by `i` and
the identification `(V ⊗ k[G])_G ≅ V`. -/
theorem tprodContraction_def (τ : Representation k G V) :
    i.tprodContraction τ = ofCoinvariantsTprodLeftRegular τ ∘ₗ
      Coinvariants.map (τ.tprod ρ) (τ.tprod (leftRegular k G)) (i.lTensor τ) ∘ₗ
        Coinvariants.mk _ :=
  (rfl)

/-- The contraction vanishes on the coinvariant kernel: it factors through `(V ⊗ W)_G`. -/
theorem coinvariantsKer_le_ker_tprodContraction (τ : Representation k G V) :
    Coinvariants.ker (τ.tprod ρ) ≤ LinearMap.ker (i.tprodContraction τ) := by
  rw [tprodContraction_def, ← LinearMap.comp_assoc]
  exact (Submodule.ker_mkQ _).ge.trans (LinearMap.ker_le_ker_comp _ _)

/-- The contraction is `G`-invariant: it is unchanged by the action of `τ ⊗ ρ`. -/
theorem tprodContraction_tprod_apply (τ : Representation k G V) (g : G) (x : V ⊗[k] W) :
    i.tprodContraction τ (τ.tprod ρ g x) = i.tprodContraction τ x := by
  simp only [tprodContraction_def, LinearMap.comp_apply, Coinvariants.mk_self_apply]

/-- The contraction sends `v ⊗ w` to the action of the antipode of `i w` on `v`. -/
@[simp]
theorem tprodContraction_tmul (v : V) (w : W) :
    i.tprodContraction τ (v ⊗ₜ w) = τ.asAlgebraHom (HopfAlgebra.antipode k (i w)) v := by
  simp [tprodContraction_def, ofCoinvariantsTprodLeftRegular_mk_tmul]

variable {i} {p : (leftRegular k G).IntertwiningMap ρ}

/-- **For a retract of the regular representation, the kernel of the contraction is the
coinvariant kernel**: the contraction identifies `(V ⊗ W)_G` with its image. -/
theorem ker_tprodContraction (h : p.comp i = .id ρ) :
    LinearMap.ker (i.tprodContraction τ) = Coinvariants.ker (τ.tprod ρ) := by
  have hpi (w : W) : p (i w) = w := DFunLike.congr_fun h w
  -- the map induced by `i` on coinvariants has the map induced by `p` as a left inverse
  have key : Coinvariants.map _ _ (p.lTensor τ) ∘ₗ
      Coinvariants.map (τ.tprod ρ) (τ.tprod (leftRegular k G)) (i.lTensor τ) = LinearMap.id := by
    rw [Coinvariants.map_comp]
    ext v w
    simp [hpi]
  have hinj : Function.Injective
      (Coinvariants.map (τ.tprod ρ) (τ.tprod (leftRegular k G)) (i.lTensor τ)) :=
    Function.LeftInverse.injective fun x => congrArg (fun f => f x) key
  rw [tprodContraction_def, ← LinearMap.comp_assoc, LinearMap.ker_comp_of_ker_eq_bot]
  · exact Submodule.ker_mkQ _
  · rw [LinearMap.ker_eq_bot]
    exact (coinvariantsTprodLeftRegularLEquiv τ).injective.comp hinj

/-- **For a retract of the regular representation, the image of the contraction is the image of
the antipode of the idempotent** `e = i (p 1)` acting on `V`. -/
theorem range_tprodContraction (h : p.comp i = .id ρ) :
    LinearMap.range (i.tprodContraction τ) = LinearMap.range
      (τ.asAlgebraHom (HopfAlgebra.antipode k (i (p (MonoidAlgebra.single 1 1))))) := by
  have hpi (w : W) : p (i w) = w := DFunLike.congr_fun h w
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      refine ⟨τ.asAlgebraHom (HopfAlgebra.antipode k (i w)) v, ?_⟩
      -- `i w` is fixed by right multiplication with `e`, since `i ∘ p` is
      have hw : i w = i w * i (p (MonoidAlgebra.single 1 1)) := by
        simpa [hpi] using apply_eq_mul_apply_single_one (i.comp p) (i w)
      rw [tprodContraction_tmul, ← mul_apply_eq_comp, ← map_mul,
        ← HopfAlgebra.antipode_mul_antidistrib, ← hw]
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · rintro _ ⟨v, rfl⟩
    exact ⟨v ⊗ₜ p (MonoidAlgebra.single 1 1), by simp⟩

end IntertwiningMap

end Representation
