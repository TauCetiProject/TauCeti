/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Endomorphisms acting on alternating maps as derivations

An endomorphism `f` of `M` acts on alternating maps `ω : M [⋀^ι]→ₗ[R] N` by applying `f` to one
argument at a time and summing,
`f.alternatingDerivation ω v = ∑ i, ω (update v i (f (v i)))`.
This is the infinitesimal form of the action `ω ↦ ω ∘ g` of automorphisms `g` of `M`. The commutator
of two such derivations is the derivation of the commutator of the endomorphisms, taken in the
opposite order (`LinearMap.alternatingDerivation_alternatingDerivation_sub`), they commute with
linear maps of coefficients, and inserting a first argument `x` splits off the term in which `f`
hits `x` (`LinearMap.curryLeft_alternatingDerivation`).

For a Lie algebra acting on `M` and on `N`, these derivations give the action of the Lie algebra
on the arguments of alternating maps from `M` to `N`; for `M = L` this is the Lie derivative of
Chevalley–Eilenberg cochains.

## Implementation notes

The definition and the proofs of alternation and of the commutator formula follow the continuous
real version `ContinuousLinearMap.alternatingDerivation` in
`TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType`, stated here for alternating maps
over a commutative semiring without topology.
-/

public section

open Function

namespace LinearMap

variable {R M N N₂ ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂] [Fintype ι] [DecidableEq ι]

/-- The sum, over all arguments, of an alternating map with `f` applied to that argument vanishes
on tuples with two equal entries. -/
private theorem sum_map_update_eq_zero (f : M →ₗ[R] M) (ω : M [⋀^ι]→ₗ[R] N) (v : ι → M)
    {a b : ι} (hv : v a = v b) (hab : a ≠ b) : ∑ i, ω (update v i (f (v i))) = 0 := by
  rw [Fintype.sum_eq_add a b hab]
  · have hswap : update v b (f (v b)) = update v a (f (v a)) ∘ Equiv.swap a b := by
      rw [update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left, ← hv]
      congr 1
      ext j
      rcases eq_or_ne j a with rfl | hja
      · simp [hv]
      rcases eq_or_ne j b with rfl | hjb
      · simp [hv]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb]
    rw [hswap, add_comm]
    exact ω.map_swap_add (update v a (f (v a))) hab
  · rintro i ⟨hia, hib⟩
    exact ω.map_eq_zero_of_eq _ (by simp [update_of_ne hia.symm, update_of_ne hib.symm, hv]) hab

/-- The multilinear map obtained by applying `f` to the `i`-th argument. -/
private def compSlot (f : M →ₗ[R] M) (ω : M [⋀^ι]→ₗ[R] N) (i : ι) :
    MultilinearMap R (fun _ : ι ↦ M) N :=
  ω.toMultilinearMap.compLinearMap (update (fun _ ↦ .id) i f)

omit [Fintype ι] in
private theorem compSlot_apply (f : M →ₗ[R] M) (ω : M [⋀^ι]→ₗ[R] N) (i : ι) (v : ι → M) :
    compSlot f ω i v = ω (update v i (f (v i))) := by
  simp only [compSlot, MultilinearMap.compLinearMap_apply, AlternatingMap.coe_multilinearMap]
  refine congrArg ω (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [update_of_ne hj]

/-- An endomorphism `f` of `M` acts on alternating maps on `M` as a derivation: the result is the
sum, over all arguments, of the alternating map with `f` applied to that argument. -/
def alternatingDerivation (f : M →ₗ[R] M) : (M [⋀^ι]→ₗ[R] N) →ₗ[R] M [⋀^ι]→ₗ[R] N where
  toFun ω :=
    { toMultilinearMap := ∑ i, compSlot f ω i
      map_eq_zero_of_eq' := fun v a b hv hab ↦ by
        simpa [compSlot_apply] using sum_map_update_eq_zero f ω v hv hab }
  map_add' ω ω' := by
    ext v
    simp [compSlot_apply, Finset.sum_add_distrib]
  map_smul' c ω := by
    ext v
    simp [compSlot_apply, Finset.smul_sum]

/-- The value of the derivation: the sum of the values with `f` applied to one argument. -/
theorem alternatingDerivation_apply (f : M →ₗ[R] M) (ω : M [⋀^ι]→ₗ[R] N) (v : ι → M) :
    f.alternatingDerivation ω v = ∑ i, ω (update v i (f (v i))) := by
  simp [alternatingDerivation, compSlot_apply]

/-- The derivation is additive in the endomorphism. -/
@[simp]
theorem alternatingDerivation_add (f g : M →ₗ[R] M) :
    (f + g).alternatingDerivation (N := N) (ι := ι) =
      f.alternatingDerivation + g.alternatingDerivation := by
  ext ω v
  simp [alternatingDerivation_apply, AlternatingMap.map_update_add, Finset.sum_add_distrib]

/-- The derivation is compatible with subtraction of endomorphisms. -/
@[simp]
theorem alternatingDerivation_sub {M : Type*} [AddCommGroup M] [Module R M] (f g : M →ₗ[R] M) :
    (f - g).alternatingDerivation (N := N) (ι := ι) =
      f.alternatingDerivation - g.alternatingDerivation := by
  ext ω v
  simp [alternatingDerivation_apply, AlternatingMap.map_update_sub, Finset.sum_sub_distrib]

/-- The derivation commutes with linear maps of coefficients. -/
theorem alternatingDerivation_compAlternatingMap (f : M →ₗ[R] M) (g : N →ₗ[R] N₂)
    (ω : M [⋀^ι]→ₗ[R] N) :
    f.alternatingDerivation (g.compAlternatingMap ω) =
      g.compAlternatingMap (f.alternatingDerivation ω) := by
  ext v
  simp [alternatingDerivation_apply]

/-- The commutator of the derivations induced by two endomorphisms is induced by their commutator,
taken in the opposite order since the endomorphisms act on the arguments. -/
theorem alternatingDerivation_alternatingDerivation_sub (f g : M →ₗ[R] M)
    (ω : M [⋀^ι]→ₗ[R] N) :
    f.alternatingDerivation (g.alternatingDerivation ω) -
        g.alternatingDerivation (f.alternatingDerivation ω) =
      (g ∘ₗ f).alternatingDerivation ω - (f ∘ₗ g).alternatingDerivation ω := by
  ext v
  -- Split each double sum into its diagonal part, where both endomorphisms hit the same
  -- argument, and its off-diagonal part, which is symmetric in the two endomorphisms.
  have hsplit (X Y : M →ₗ[R] M) :
      ∑ i, ∑ j, ω (update (update v i (X (v i))) j (Y (update v i (X (v i)) j))) =
        ∑ i, ω (update v i (Y (X (v i)))) +
          ∑ i, ∑ j, if i = j then 0 else ω (update (update v i (X (v i))) j (Y (v j))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h (j : ι) : ω (update (update v i (X (v i))) j (Y (update v i (X (v i)) j))) =
        (if i = j then ω (update v i (Y (X (v i)))) else 0) +
          if i = j then 0 else ω (update (update v i (X (v i))) j (Y (v j))) := by
      rcases eq_or_ne i j with rfl | h
      · simp
      · simp [h, Ne.symm h]
    simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hsymm : ∑ i, ∑ j, (if i = j then 0 else
        ω (update (update v i (g (v i))) j (f (v j)))) =
      ∑ i, ∑ j, if i = j then 0 else ω (update (update v i (f (v i))) j (g (v j))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [h, Ne.symm h, update_comm h]
  simp only [sub_apply, alternatingDerivation_apply, comp_apply, hsplit, hsymm]
  abel

/-- Inserting `x` as the first argument of `f.alternatingDerivation ω` splits off the term in
which `f` is applied to `x`. -/
theorem curryLeft_alternatingDerivation {n : ℕ} (f : M →ₗ[R] M)
    (ω : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M) :
    (f.alternatingDerivation ω).curryLeft x =
      f.alternatingDerivation (ω.curryLeft x) + ω.curryLeft (f x) := by
  ext v
  simp [alternatingDerivation_apply, Fin.sum_univ_succ, Matrix.vecCons, ← Fin.cons_update,
    Fin.update_cons_zero, add_comm]

end LinearMap
