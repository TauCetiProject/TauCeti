/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Top exterior powers of a short exact sequence

For a short exact sequence `0 → U → V → W → 0` of finite-dimensional vector spaces, with maps
`f : U → V` and `g : V → W`, write `a = dim U` and `c = dim W`. There is a canonical isomorphism
of lines
`⋀ᵃ U ⊗ ⋀ᶜ W ≃ ⋀ᵃ⁺ᶜ V`, `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c) ↦ f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c`,
where `vⱼ` is any lift of `wⱼ` along `g`. Since `a + c = dim V`, this identifies the tensor product
of the top exterior powers of `U` and `W` with the top exterior power of `V`. The factor of the
subspace comes first.

The value does not depend on the lifts because the `a` vectors `f uᵢ` already exhaust the
`a`-dimensional subspace `range f = ker g`: changing a lift by an element of that subspace adds an
exterior product with `a + 1` factors in an `a`-dimensional space, which vanishes
(`Submodule.ιMulti_eq_of_sub_mem`). The map is constructed from a choice of linear section of
`g`, and the characterization `TauCeti.exteriorPower.shortExactEquiv_tmul_ιMulti` shows that the
choice does not matter.

This is the determinant-line identity `det V ≅ det U ⊗ det W`. It is the linear-algebra input for
comparing determinant lines along exact sequences, such as the kernel/cokernel sequence of a
stabilized Fredholm operator, and for orienting a vector space from orientations of a subspace and
of the quotient.

## Main declarations

* `TauCeti.exteriorPower.shortExactEquiv`: the isomorphism `⋀ᵃ U ⊗ ⋀ᶜ W ≃ ⋀ᵃ⁺ᶜ V`.
* `TauCeti.exteriorPower.shortExactEquiv_tmul_ιMulti`: its value on exterior products, for
  arbitrary lifts.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section

open Module TensorProduct exteriorPower

namespace TauCeti

namespace exteriorPower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {U W : Type*} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  {f : U →ₗ[K] V} {g : V →ₗ[K] W}

/-- The wedge of the image of `f` with the image of a linear map `s`, the comparison map
underlying `TauCeti.exteriorPower.shortExactEquiv` for a section `s` of `g`. -/
private noncomputable def shortExactWedge (f : U →ₗ[K] V) (s : W →ₗ[K] V) (a c : ℕ) :
    ⋀[K]^a U ⊗[K] ⋀[K]^c W →ₗ[K] ⋀[K]^(a + c) V :=
  TensorProduct.lift ((wedge K V a c).compl₁₂ (map a f) (map c s))

/-- For a section `s` of `g`, the comparison map sends `u ⊗ w` to `f u ∧ v` for every lift `v`
of `w`. -/
private theorem shortExactWedge_tmul_ιMulti [FiniteDimensional K U] (hfg : Function.Exact f g)
    {s : W →ₗ[K] V} (hs : ∀ w, g (s w) = w) {c : ℕ} (u : Fin (finrank K U) → U)
    (w : Fin c → W) (v : Fin c → V) (hv : ∀ j, g (v j) = w j) :
    shortExactWedge f s (finrank K U) c (ιMulti K _ u ⊗ₜ ιMulti K c w) =
      ιMulti K _ (Fin.append (f ∘ u) v) := by
  simp only [shortExactWedge, lift.tmul, LinearMap.compl₁₂_apply, map_apply_ιMulti,
    wedge_ιMulti]
  -- The first `dim U` factors exhaust `range f = ker g`, and the lifts agree modulo `ker g`.
  refine (LinearMap.range f).ιMulti_eq_of_sub_mem (Finset.univ.map (Fin.castAddEmb c))
    (by simpa using LinearMap.finrank_range_le f) (by simp) (by simp) fun i hi ↦ ?_
  obtain ⟨j, rfl⟩ : ∃ j, Fin.natAdd (finrank K U) j = i := by
    induction i using Fin.addCases with
    | left i => simp at hi
    | right j => exact ⟨j, rfl⟩
  exact (hfg _).1 (by simp [hv, hs])

/-- For a section `s` of `g`, the comparison map in the top degrees is bijective. -/
private theorem shortExactWedge_bijective [FiniteDimensional K U] [FiniteDimensional K W]
    (hf : Function.Injective f) (hfg : Function.Exact f g) {s : W →ₗ[K] V}
    (hs : ∀ w, g (s w) = w) :
    Function.Bijective (shortExactWedge f s (finrank K U) (finrank K W)) := by
  have hg : Function.Surjective g := fun w ↦ ⟨s w, hs w⟩
  have : FiniteDimensional K V := Module.Finite.of_exact hfg hg
  have hdim : finrank K V = finrank K U + finrank K W := by
    rw [← g.finrank_range_add_finrank_ker, LinearMap.range_eq_top.2 hg, finrank_top,
      hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf, add_comm]
  set bU := Module.finBasis K U
  set bW := Module.finBasis K W
  -- The images of `bU` followed by the lifts of `bW` are linearly independent: applying `g`
  -- kills the first block and recovers the coefficients of `bW`, and `f` is injective.
  have hli : LinearIndependent K (Fin.append (f ∘ bU) (s ∘ bW)) := by
    refine Fintype.linearIndependent_iff.2 fun t ht ↦ ?_
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Function.comp_apply] at ht
    have htW : ∀ j, t (Fin.natAdd _ j) = 0 := by
      refine Fintype.linearIndependent_iff.1 bW.linearIndependent _ ?_
      simpa [hfg.apply_apply_eq_zero, hs] using congrArg g ht
    simp only [htW, zero_smul, Finset.sum_const_zero, add_zero] at ht
    have htU : ∀ i, t (Fin.castAdd _ i) = 0 :=
      Fintype.linearIndependent_iff.1 bU.linearIndependent _ (hf (by simpa using ht))
    exact fun i ↦ Fin.addCases htU htW i
  -- Hence they form a basis of `V`, whose exterior product spans the top exterior power.
  set b : Basis (Fin (finrank K U + finrank K W)) K V :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [Fintype.card_fin, hdim])
  have hsurj : Function.Surjective (shortExactWedge f s (finrank K U) (finrank K W)) := by
    intro y
    refine ⟨b.exteriorPowerTopEquiv y • (ιMulti K _ ⇑bU ⊗ₜ ιMulti K _ ⇑bW), ?_⟩
    rw [map_smul, shortExactWedge_tmul_ιMulti hfg hs _ _ (s ∘ ⇑bW) fun j ↦ hs _]
    have hy := b.exteriorPowerTopEquiv.symm_apply_apply y
    rwa [Module.Basis.exteriorPowerTopEquiv_symm_apply,
      coe_basisOfLinearIndependentOfCardEqFinrank'] at hy
  refine OrzechProperty.bijective_of_surjective_of_finrank_le _ hsurj ?_
  simp [Module.finrank_tensorProduct, hdim]

/-- A linear section of the surjection `g`, used to build
`TauCeti.exteriorPower.shortExactEquiv`. -/
private noncomputable def sectionOfSurjective (hg : Function.Surjective g) : W →ₗ[K] V :=
  Classical.choose (g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg))

private theorem apply_sectionOfSurjective (hg : Function.Surjective g) (w : W) :
    g (sectionOfSurjective hg w) = w :=
  LinearMap.congr_fun
    (Classical.choose_spec (g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg))) w

/-- For a short exact sequence `0 → U → V → W → 0` of finite-dimensional vector spaces, the
canonical isomorphism `⋀ᵃ U ⊗ ⋀ᶜ W ≃ ⋀ᵃ⁺ᶜ V`, where `a = dim U` and `c = dim W`. It sends
`(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to `f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` for any lifts `vⱼ` of the
`wⱼ` along `g` (`TauCeti.exteriorPower.shortExactEquiv_tmul_ιMulti`). -/
noncomputable def shortExactEquiv [FiniteDimensional K U] [FiniteDimensional K W]
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    ⋀[K]^(finrank K U) U ⊗[K] ⋀[K]^(finrank K W) W ≃ₗ[K]
      ⋀[K]^(finrank K U + finrank K W) V :=
  LinearEquiv.ofBijective (shortExactWedge f (sectionOfSurjective hg) _ _)
    (shortExactWedge_bijective hf hfg (apply_sectionOfSurjective hg))

variable [FiniteDimensional K U] [FiniteDimensional K W] (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

/-- `TauCeti.exteriorPower.shortExactEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` for every choice of lifts `vⱼ` of the `wⱼ` along `g`. -/
theorem shortExactEquiv_tmul_ιMulti (u : Fin (finrank K U) → U) (w : Fin (finrank K W) → W)
    (v : Fin (finrank K W) → V) (hv : ∀ j, g (v j) = w j) :
    shortExactEquiv hf hfg hg (ιMulti K _ u ⊗ₜ ιMulti K _ w) =
      ιMulti K _ (Fin.append (f ∘ u) v) :=
  shortExactWedge_tmul_ιMulti hfg (apply_sectionOfSurjective hg) u w v hv

/-- `TauCeti.exteriorPower.shortExactEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (g v₁ ∧ ⋯ ∧ g v_c)` to
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c`. -/
@[simp]
theorem shortExactEquiv_tmul_ιMulti_comp (u : Fin (finrank K U) → U)
    (v : Fin (finrank K W) → V) :
    shortExactEquiv hf hfg hg (ιMulti K _ u ⊗ₜ ιMulti K _ (g ∘ v)) =
      ιMulti K _ (Fin.append (f ∘ u) v) :=
  shortExactEquiv_tmul_ιMulti hf hfg hg u _ v fun _ ↦ rfl

/-- The inverse of `TauCeti.exteriorPower.shortExactEquiv` splits
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` as `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (g v₁ ∧ ⋯ ∧ g v_c)`. -/
@[simp]
theorem shortExactEquiv_symm_ιMulti (u : Fin (finrank K U) → U) (v : Fin (finrank K W) → V) :
    (shortExactEquiv hf hfg hg).symm (ιMulti K _ (Fin.append (f ∘ u) v)) =
      ιMulti K _ u ⊗ₜ ιMulti K _ (g ∘ v) :=
  (LinearEquiv.symm_apply_eq _).2 (shortExactEquiv_tmul_ιMulti_comp hf hfg hg u v).symm

end exteriorPower

end TauCeti
