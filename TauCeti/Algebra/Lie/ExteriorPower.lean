/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Lie actions on exterior powers

An endomorphism of a module acts infinitesimally on an exterior power by applying the
endomorphism to one factor at a time. This construction is linear in the endomorphism and carries
commutators to commutators, hence defines a Lie algebra representation.

## Main definitions

* `exteriorPower.lieMap`: the natural Lie action of `Module.End K V` on `⋀[K]^d V`.

## Main results

* `exteriorPower.lieMap_apply_ιMulti`: the action on a decomposable wedge is the sum of the terms
  obtained by applying the endomorphism to one factor.
-/

public section

namespace exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The multilinear map `v ↦ ∑ i, ιMulti K d (update v i (f (v i)))`. -/
private noncomputable def actionMultilinear (d : ℕ) (f : Module.End K V) :
    MultilinearMap K (fun _ : Fin d => V) (⋀[K]^d V) :=
  ∑ i : Fin d, (ιMulti K d).toMultilinearMap.compLinearMap
    (Function.update (fun _ => LinearMap.id) i f)

private theorem actionMultilinear_apply (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    actionMultilinear d f v =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) := by
  simp only [actionMultilinear, sum_apply, MultilinearMap.compLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg (ιMulti K d) (funext fun j => ?_)
  rcases eq_or_ne j i with rfl | hji <;> simp [*]

private theorem actionMultilinear_map_eq_zero_of_eq (d : ℕ) (f : Module.End K V)
    (v : Fin d → V) (i j : Fin d) (hv : v i = v j) (hij : i ≠ j) :
    actionMultilinear d f v = 0 := by
  rw [actionMultilinear_apply, Fintype.sum_eq_add i j hij fun k ⟨hki, hkj⟩ =>
    (ιMulti K d).map_eq_zero_of_eq _ (i := i) (j := j) (by simp [hki.symm, hkj.symm, hv]) hij]
  -- The `j`-th term is the `i`-th term with the two factors swapped.
  have hswap : Function.update v j (f (v j)) =
      Function.update v i (f (v i)) ∘ Equiv.swap i j := by
    funext k
    simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  rw [hswap]
  exact (ιMulti K d).map_add_swap _ hij

/-- `actionMultilinear d f`, bundled as an alternating map. -/
private noncomputable def actionAlternating (d : ℕ) (f : Module.End K V) :
    V [⋀^Fin d]→ₗ[K] (⋀[K]^d V) where
  toMultilinearMap := actionMultilinear d f
  map_eq_zero_of_eq' v i j hv hij :=
    actionMultilinear_map_eq_zero_of_eq d f v i j hv hij

@[simp]
private theorem actionAlternating_apply (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    actionAlternating d f v =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) := by
  simp [actionAlternating, actionMultilinear_apply]

/-- The induced endomorphism of `⋀[K]^d V`, as a linear function of `f`. -/
private noncomputable def actionLinear (d : ℕ) :
    Module.End K V →ₗ[K] Module.End K (⋀[K]^d V) where
  toFun f := alternatingMapLinearEquiv (actionAlternating d f)
  map_add' f g := linearMap_ext <| AlternatingMap.ext fun v => by
    simp [Finset.sum_add_distrib]
  map_smul' r f := linearMap_ext <| AlternatingMap.ext fun v => by
    simp [Finset.smul_sum]

@[simp]
private theorem actionLinear_apply_ιMulti (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    actionLinear d f (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) := by
  simp [actionLinear]

/-- The term of `actionLinear d f (actionLinear d g (ιMulti K d v))` in which `g` acts on the
`i`-th factor and then `f` acts on the `j`-th factor. -/
private def actionTerm (d : ℕ) (f g : Module.End K V) (v : Fin d → V)
    (i j : Fin d) : ⋀[K]^d V :=
  ιMulti K d (Function.update (Function.update v i (g (v i))) j
    (f (Function.update v i (g (v i)) j)))

private theorem actionTerm_swap (d : ℕ) (f g : Module.End K V) (v : Fin d → V)
    {i j : Fin d} (hij : i ≠ j) :
    actionTerm d f g v i j = actionTerm d g f v j i := by
  apply congrArg (ιMulti K d)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `actionLinear d` carries commutators to commutators. -/
private theorem actionLinear_mul_sub_mul (d : ℕ) (f g : Module.End K V) :
    actionLinear d (f * g - g * f) =
      actionLinear d f * actionLinear d g - actionLinear d g * actionLinear d f := by
  have hcomp (f g : Module.End K V) (v : Fin d → V) :
      actionLinear d f (actionLinear d g (ιMulti K d v)) =
        ∑ i : Fin d, ∑ j : Fin d, actionTerm d f g v i j := by
    simp [actionTerm]
  refine linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.sub_apply, Module.End.mul_apply]
  -- Off-diagonal terms of the two composites cancel in pairs by `actionTerm_swap`, leaving the
  -- diagonal terms, where the commutator acts on a single factor.
  rw [hcomp, hcomp, actionLinear_apply_ιMulti, Finset.sum_comm (f := actionTerm d g f v),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single i fun j hj =>
    sub_eq_zero.mpr (actionTerm_swap d f g v (Ne.symm hj))]
  simp [actionTerm]

/-- The infinitesimal action of endomorphisms on an exterior power. -/
noncomputable def lieMap (d : ℕ) :
    Module.End K V →ₗ⁅K⁆ Module.End K (⋀[K]^d V) :=
  { actionLinear d with
    map_lie' := fun {f g} => by
      rw [Ring.lie_def, Ring.lie_def]
      exact actionLinear_mul_sub_mul d f g }

/-- An endomorphism acts on a decomposable wedge by acting on one factor at a time. -/
@[simp]
theorem lieMap_apply_ιMulti (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    lieMap d f (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) := by
  rw [lieMap, ← LieHom.coe_toLinearMap, actionLinear_apply_ιMulti]

end exteriorPower
