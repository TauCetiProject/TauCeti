/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Finite
public import TauCeti.GroupTheory.Coxeter.Matsumoto

/-!
# Reduced-word elements of the type-A Hecke algebra

Let `cs` be a Coxeter system of type `A_(n-1)` on a group `W`, so that its simple reflections are
indexed by the generators `T i`, `i : Fin (n - 1)`, of the Hecke algebra `TypeAHeckeAlgebra R q n`
on `n` strands. For `w : W` the element `TypeAHeckeAlgebra.Tw cs w`, usually written `T_w`, is the
product `T i₁ * ⋯ * T iₖ` along any reduced expression `w = s i₁ ⋯ s iₖ`. By Matsumoto's theorem
(`TauCeti.matsumoto`) this does not depend on the reduced expression, because the generators `T i`
satisfy the braid relations of the type-A Coxeter matrix.

The elements `T_w` multiply by the length rule: `T_v * T_w = T_(v * w)` when lengths add, and
multiplication by a generator `T i` on either side follows the length-increase/length-decrease
rule,
* `T i * T_w = T_(s i * w)` if `ℓ (s i * w) = ℓ w + 1`, and
* `T i * T_w = (q - q⁻¹) • T_w + T_(s i * w)` if `ℓ (s i * w) < ℓ w`,

with the mirror statements on the right. Consequently the elements `T_w` span the Hecke algebra as
an `R`-module. The Coxeter system is an arbitrary one of type `A_(n-1)`, so these statements apply
to the abstract Coxeter group `(CoxeterMatrix.A (n - 1)).Group` and to any concrete model of it,
such as the symmetric group on `n` letters.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.Tw`: the element `T_w` attached to `w : W`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.Tw_wordProd`: `T_w` is the product of the generators along any
  reduced expression of `w`.
* `TauCeti.TypeAHeckeAlgebra.Tw_mul_Tw`: `T_v * T_w = T_(v * w)` when `ℓ (v * w) = ℓ v + ℓ w`.
* `TauCeti.TypeAHeckeAlgebra.T_mul_Tw_of_not_isLeftDescent`,
  `TauCeti.TypeAHeckeAlgebra.T_mul_Tw_of_isLeftDescent`,
  `TauCeti.TypeAHeckeAlgebra.Tw_mul_T_of_not_isRightDescent` and
  `TauCeti.TypeAHeckeAlgebra.Tw_mul_T_of_isRightDescent`: multiplication by a generator.
* `TauCeti.TypeAHeckeAlgebra.span_range_Tw`: the elements `T_w` span the Hecke algebra.

## References

* N. Iwahori, *On the structure of a Hecke ring of a Chevalley group over a finite field*,
  J. Fac. Sci. Univ. Tokyo Sect. I 10 (1964), 215–236.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 7.1.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4.
-/

public section

namespace TauCeti

namespace TypeAHeckeAlgebra

open CoxeterSystem

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

/-- The Hecke generators satisfy every braid relation of the type-A Coxeter matrix: for all
`i` and `j`, the two alternating words in `T i` and `T j` whose length is the Coxeter-matrix
entry at `(i, j)` have the same product. -/
theorem prod_map_T_braidWord (i j : Fin (n - 1)) :
    ((braidWord (CoxeterMatrix.A (n - 1)) i j).map (T (R := R) q)).prod =
      ((braidWord (CoxeterMatrix.A (n - 1)) j i).map (T q)).prod := by
  have hgen (k : Fin (n - 1)) :
      ((Units.coeHom _).comp (braidHom R q n)) (ArtinGroup.gen (CoxeterMatrix.A (n - 1)) k) =
        T q k := by
    simp [← BraidGroup.sigma_eq_gen]
  have h := congrArg ((Units.coeHom _).comp (braidHom R q n))
    (ArtinGroup.prod_map_gen_braidWord (CoxeterMatrix.A (n - 1)) i j)
  simpa only [map_list_prod, List.map_map, Function.comp_def, hgen] using h

variable (q) in
/-- The element `T_w` of the type-A Hecke algebra attached to an element `w` of a Coxeter system
of type `A_(n-1)`: the product of the generators `T i` along a reduced expression of `w`. It is
the reduced-word lift of Matsumoto's theorem (`TauCeti.existsUnique_reducedWordLift`), so it does
not depend on the reduced expression (`TauCeti.TypeAHeckeAlgebra.Tw_wordProd`). -/
noncomputable def Tw (w : W) : TypeAHeckeAlgebra R q n :=
  (existsUnique_reducedWordLift cs (T q) prod_map_T_braidWord).exists.choose w

/-- `T_w` is the product of the generators along any reduced expression of `w`. -/
theorem Tw_wordProd {ω : List (Fin (n - 1))} (hω : cs.IsReduced ω) :
    Tw q cs (cs.wordProd ω) = (ω.map (T (R := R) q)).prod :=
  (existsUnique_reducedWordLift cs (T q) prod_map_T_braidWord).exists.choose_spec ω hω

/-- The element `T_w` attached to the identity is `1`. -/
@[simp]
theorem Tw_one : Tw q cs (1 : W) = (1 : TypeAHeckeAlgebra R q n) := by
  simpa using Tw_wordProd (R := R) (q := q) cs (ω := []) (by simp [CoxeterSystem.IsReduced])

/-- The element `T_w` attached to a simple reflection is the corresponding generator. -/
@[simp]
theorem Tw_simple (i : Fin (n - 1)) :
    Tw q cs (cs.simple i) = (T q i : TypeAHeckeAlgebra R q n) := by
  simpa using Tw_wordProd (R := R) (q := q) cs (ω := [i]) (by simp [CoxeterSystem.IsReduced])

/-- Each element `T_w` is invertible. -/
theorem isUnit_Tw (w : W) : IsUnit (Tw q cs w : TypeAHeckeAlgebra R q n) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [Tw_wordProd cs hω]
  exact List.prod_isUnit fun _ hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact isUnit_T i

/-- **Length additivity.** If `ℓ (v * w) = ℓ v + ℓ w`, then `T_v * T_w = T_(v * w)`. -/
theorem Tw_mul_Tw {v w : W} (h : cs.length (v * w) = cs.length v + cs.length w) :
    Tw q cs v * Tw q cs w = (Tw q cs (v * w) : TypeAHeckeAlgebra R q n) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced v
  obtain ⟨ω', hω', rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ ω') := by
    rw [CoxeterSystem.IsReduced, wordProd_append, h, hω.eq, hω'.eq, List.length_append]
  rw [← wordProd_append, Tw_wordProd cs hω, Tw_wordProd cs hω', Tw_wordProd cs hred,
    List.map_append, List.prod_append]

/-- **Left multiplication, length increase.** If `s i * w` is longer than `w`, then
`T i * T_w = T_(s i * w)`. -/
theorem T_mul_Tw_of_not_isLeftDescent {w : W} {i : Fin (n - 1)} (h : ¬cs.IsLeftDescent w i) :
    T q i * Tw q cs w = (Tw q cs (cs.simple i * w) : TypeAHeckeAlgebra R q n) := by
  rw [← Tw_simple cs, Tw_mul_Tw cs]
  rw [cs.not_isLeftDescent_iff.mp h, length_simple, add_comm]

/-- **Right multiplication, length increase.** If `w * s i` is longer than `w`, then
`T_w * T i = T_(w * s i)`. -/
theorem Tw_mul_T_of_not_isRightDescent {w : W} {i : Fin (n - 1)} (h : ¬cs.IsRightDescent w i) :
    Tw q cs w * T q i = (Tw q cs (w * cs.simple i) : TypeAHeckeAlgebra R q n) := by
  rw [← Tw_simple cs, Tw_mul_Tw cs]
  rw [cs.not_isRightDescent_iff.mp h, length_simple]

/-- **Left multiplication, length decrease.** If `s i * w` is shorter than `w`, then
`T i * T_w = (q - q⁻¹) • T_w + T_(s i * w)`. -/
theorem T_mul_Tw_of_isLeftDescent {w : W} {i : Fin (n - 1)} (h : cs.IsLeftDescent w i) :
    T q i * Tw q cs w =
      ((q : R) - ↑q⁻¹) • Tw q cs w + (Tw q cs (cs.simple i * w) : TypeAHeckeAlgebra R q n) := by
  have hw : Tw q cs w = (T q i * Tw q cs (cs.simple i * w) : TypeAHeckeAlgebra R q n) := by
    rw [T_mul_Tw_of_not_isLeftDescent cs, simple_mul_simple_cancel_left]
    rwa [cs.isLeftDescent_iff_not_isLeftDescent_mul] at h
  conv_lhs => rw [hw]
  rw [← mul_assoc, T_mul_self, add_mul, one_mul, smul_mul_assoc, ← hw]

/-- **Right multiplication, length decrease.** If `w * s i` is shorter than `w`, then
`T_w * T i = (q - q⁻¹) • T_w + T_(w * s i)`. -/
theorem Tw_mul_T_of_isRightDescent {w : W} {i : Fin (n - 1)} (h : cs.IsRightDescent w i) :
    Tw q cs w * T q i =
      ((q : R) - ↑q⁻¹) • Tw q cs w + (Tw q cs (w * cs.simple i) : TypeAHeckeAlgebra R q n) := by
  have hw : Tw q cs w = (Tw q cs (w * cs.simple i) * T q i : TypeAHeckeAlgebra R q n) := by
    rw [Tw_mul_T_of_not_isRightDescent cs, simple_mul_simple_cancel_right]
    rwa [cs.isRightDescent_iff_not_isRightDescent_mul] at h
  conv_lhs => rw [hw]
  rw [mul_assoc, T_mul_self, mul_add, mul_one, mul_smul_comm, ← hw]

/-- Left multiplication by a generator preserves the span of the elements `T_w`. -/
private theorem T_mul_mem_span_range_Tw (i : Fin (n - 1)) {x : TypeAHeckeAlgebra R q n}
    (hx : x ∈ Submodule.span R (Set.range (Tw q cs))) :
    T q i * x ∈ Submodule.span R (Set.range (Tw q cs)) := by
  induction hx using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨w, rfl⟩ := hy
    by_cases h : cs.IsLeftDescent w i
    · rw [T_mul_Tw_of_isLeftDescent cs h]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩))
        (Submodule.subset_span ⟨_, rfl⟩)
    · rw [T_mul_Tw_of_not_isLeftDescent cs h]
      exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add _ _ _ _ hy hz => simpa only [mul_add] using add_mem hy hz
  | smul r _ _ hy => simpa only [mul_smul_comm] using Submodule.smul_mem _ r hy

/-- The elements `T_w` span the type-A Hecke algebra as an `R`-module. -/
theorem span_range_Tw :
    Submodule.span R (Set.range (Tw q cs : W → TypeAHeckeAlgebra R q n)) = ⊤ := by
  set S := Submodule.span R (Set.range (Tw (R := R) q cs))
  -- Every element of the algebra multiplies `S` into itself, since the generators do.
  have hmul (x : TypeAHeckeAlgebra R q n) : ∀ y ∈ S, x * y ∈ S := by
    have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
      rw [adjoin_range_T]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem _ hx =>
      obtain ⟨i, rfl⟩ := hx
      exact fun y hy ↦ T_mul_mem_span_range_Tw cs i hy
    | algebraMap r => exact fun y hy ↦ by simpa [Algebra.smul_def] using S.smul_mem r hy
    | add _ _ _ _ hx hz =>
      exact fun y hy ↦ by simpa only [add_mul] using add_mem (hx y hy) (hz y hy)
    | mul _ _ _ _ hx hz => exact fun y hy ↦ by simpa only [mul_assoc] using hx _ (hz y hy)
  refine eq_top_iff.mpr fun x _ ↦ ?_
  simpa using hmul x 1 (Submodule.subset_span ⟨1, Tw_one cs⟩)

end TypeAHeckeAlgebra

end TauCeti
