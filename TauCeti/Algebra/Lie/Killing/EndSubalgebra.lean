/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.Lie.Basic
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Algebra.Lie.TraceForm
import TauCeti.Algebra.Lie.Weights.Central

/-!
# Killing Lie subalgebras of `𝔤𝔩(V)`

Let `L ⊆ 𝔤𝔩(V)` be a Lie subalgebra with nondegenerate Killing form, acting on the
finite-dimensional vector space `V`. This file records how the `L`-submodules of `V` control
membership in `L`, following the key step of Humphreys' proof that `L` contains the Jordan–Chevalley
parts of its elements.

Every element of `L` preserves each `L`-submodule `W ⊆ V` (`LieSubalgebra.apply_mem_of_mem`), and
has trace zero on it because `L` is perfect (`LieSubalgebra.trace_restrict_eq_zero_of_mem`).
Conversely, over an algebraically closed field of characteristic zero, an
endomorphism `y` of `V` lies in `L` as soon as it normalizes `L`, preserves every `L`-submodule of
`V` and has trace zero on each of them. By Weyl's theorem `L` has an `L`-stable complement `Q` in
`𝔤𝔩(V)`; write `y = a + q` with `a ∈ L` and `q ∈ Q`. The bracket of `q` with `L` lies in
`L ∩ Q = 0`, so `q` commutes with `L`. Schur's lemma makes `q` a scalar on each irreducible
`L`-submodule, and that scalar vanishes by the trace condition. Since `V` is a sum of irreducible
submodules, again by Weyl's theorem, `q = 0`.

## Main results

* `LieSubalgebra.eq_zero_of_forall_commute`: an endomorphism commuting with `L` and having trace
  zero on every `L`-submodule vanishes.
* `LieSubalgebra.mem_of_forall_lie_mem`: an endomorphism normalizing `L`, preserving every
  `L`-submodule and having trace zero on each lies in `L`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.4.
-/

public section

open LieAlgebra LieModule Module Module.End

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (L : LieSubalgebra K (Module.End K V))

variable [FiniteDimensional K V] [CharZero K] [IsAlgClosed K] [IsKilling K L]

/-- An endomorphism `q` of `V` that commutes with a Killing Lie subalgebra `L` of `𝔤𝔩(V)`, preserves
every `L`-submodule and has trace zero on each of them vanishes: by Schur's lemma it is a scalar on
each irreducible summand of `V`, and the trace condition forces that scalar to be zero. -/
theorem eq_zero_of_forall_commute (q : Module.End K V) (hcomm : ∀ z ∈ L, Commute z q)
    (hinv : ∀ W : LieSubmodule K L V, ∀ w ∈ W, q w ∈ W)
    (htr : ∀ W : LieSubmodule K L V, LinearMap.trace K W (q.restrict (hinv W)) = 0) :
    q = 0 := by
  obtain ⟨k, N, hint, hirr⟩ := TauCeti.exists_isInternal_isIrreducible_of_isKilling K L V
  suffices h : ∀ i, (N i : Submodule K V) ≤ LinearMap.ker q by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hint.submodule_iSup_eq_top]
    exact iSup_le h
  intro i
  have := hirr i
  have := LieModule.nontrivial_of_isIrreducible K L (N i)
  -- The restriction of `q` to the irreducible summand `N i` is a morphism of `L`-modules.
  let f : N i →ₗ⁅K,L⁆ N i :=
    { q.restrict (hinv (N i)) with
      map_lie' := fun {z w} ↦ Subtype.ext <| by
        simp only [LinearMap.toFun_eq_coe, LieSubmodule.coe_bracket, LinearMap.coe_restrict_apply,
          coe_bracket_of_module, Module.End.lie_apply]
        exact congr($((hcomm z z.2).eq) (w : V)).symm }
  obtain ⟨c, hc⟩ := TauCeti.exists_forall_apply_eq_smul K L (N i) f
  have hres : q.restrict (hinv (N i)) = c • LinearMap.id := LinearMap.ext hc
  have hc0 : c = 0 := by
    have := htr (N i)
    rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_right (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  intro v hv
  simpa [LinearMap.coe_restrict_apply, hc0] using congr(($hres ⟨v, hv⟩ : V))

/-- An endomorphism of `V` that normalizes a Killing Lie subalgebra `L` of `𝔤𝔩(V)`, preserves every
`L`-submodule of `V` and has trace zero on each of them lies in `L`. Split it along an `L`-stable
complement of `L` in `𝔤𝔩(V)`: the complementary component commutes with `L`, so it vanishes by
`LieSubalgebra.eq_zero_of_forall_commute`. -/
theorem mem_of_forall_lie_mem (y : Module.End K V) (hnorm : ∀ z ∈ L, ⁅y, z⁆ ∈ L)
    (hinv : ∀ W : LieSubmodule K L V, ∀ w ∈ W, y w ∈ W)
    (htr : ∀ W : LieSubmodule K L V, LinearMap.trace K W (y.restrict (hinv W)) = 0) : y ∈ L := by
  obtain ⟨Q, hQ⟩ := TauCeti.exists_isCompl_of_isKilling L.toLieSubmodule
  obtain ⟨a, ha, q, hq, rfl⟩ :=
    (LieSubmodule.mem_sup _ _ _).1 (hQ.sup_eq_top ▸ LieSubmodule.mem_top y)
  have ha' : a ∈ L := ha
  suffices q = 0 by simpa [this] using ha'
  have hqW (W : LieSubmodule K L V) (w : V) (hw : w ∈ W) : q w ∈ W := by
    simpa using W.sub_mem (hinv W w hw) (L.apply_mem_of_mem ha' W w hw)
  refine L.eq_zero_of_forall_commute q ?_ hqW fun W ↦ ?_
  · -- The bracket of `q` with `L` lies in both `L` and `Q`, hence vanishes.
    intro z hz
    have hzQ : ⁅z, q⁆ ∈ Q := by simpa using Q.lie_mem (x := ⟨z, hz⟩) hq
    have hzL : ⁅z, q⁆ ∈ L := by
      have : ⁅z, q⁆ = -⁅a + q, z⁆ - ⁅z, a⁆ := by
        rw [add_lie, ← lie_skew z q, ← lie_skew z a]
        abel
      rw [this]
      exact L.sub_mem (L.neg_mem (hnorm z hz)) (L.lie_mem hz ha')
    have h0 : ⁅z, q⁆ ∈ L.toLieSubmodule ⊓ Q := ⟨(L.mem_toLieSubmodule _).2 hzL, hzQ⟩
    rw [hQ.inf_eq_bot, LieSubmodule.mem_bot] at h0
    rwa [LieRing.of_associative_ring_bracket, sub_eq_zero] at h0
  · have hsplit : q.restrict (hqW W) =
        (a + q).restrict (hinv W) - a.restrict (L.apply_mem_of_mem ha' W) := by
      ext w
      simp [LinearMap.coe_restrict_apply]
    rw [hsplit, map_sub, htr W,
      L.trace_restrict_eq_zero_of_mem (TauCeti.derivedSeries_one_eq_top_of_isKilling K L) ha' W,
      sub_zero]

end LieSubalgebra
