/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.RootExponential
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.Lie.Weights.Rank

/-!
# Conjugacy of Cartan subalgebras

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over an algebraically
closed field `K` of characteristic zero. Any two Cartan subalgebras `H` and `H'` of `L` are
conjugate under the group `Int(L)` of inner automorphisms (`TauCeti.intLieAlgebra`): some
`g ∈ Int(L)` carries `H` onto `H'`.

The proof is Chevalley's density argument. The root-exponential parametrization
`(t, h) ↦ ∏_α exp(t_α ad e_α) h` of the conjugates `Int(L) · H` has surjective differential at
some point, so its image contains a nonempty principal open set of `L`
(`LieSubalgebra.exists_ne_zero_forall_eval_ne_zero_mem_intCartan`). The same holds for `H'`,
and the regular elements of `L` also form a nonempty principal open set. Since `L` is irreducible,
these three sets meet, in a regular element `x = g h = g' h'` with `g, g' ∈ Int(L)`, `h ∈ H` and
`h' ∈ H'`. A regular element of a Cartan subalgebra has that Cartan subalgebra as its Engel
subalgebra, so the Engel subalgebra of `x` is both `g H` and `g' H'`.

## Main results

* `LieSubalgebra.exists_ne_zero_forall_eval_ne_zero_mem_intCartan`: the conjugates
  `Int(L) · H` of a Cartan subalgebra contain every point outside the zero locus of a nonzero
  polynomial in the coordinates of a basis of `L`.
* `LieSubalgebra.exists_map_intLieAlgebraLieEquiv_eq`: **conjugacy of Cartan subalgebras**, two
  Cartan subalgebras are conjugate under `Int(L)`.

## References

* J.-P. Serre, *Complex Semisimple Lie Algebras*, Springer, 1987, Chapter III, where Cartan
  subalgebras are shown to be conjugate by this density argument.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VII, §3.
-/

public section

namespace TauCeti

open LieAlgebra MvPolynomial

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [CharZero K] [IsAlgClosed K]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

/-- **The conjugates of a Cartan subalgebra contain a nonempty principal open set.** Over an
algebraically closed field, there is a nonzero polynomial `q` in the coordinates of a basis `b`
of `L` such that every `x` with `q(x) ≠ 0` is of the form `g h` with `g ∈ Int(L)` and `h ∈ H`. -/
theorem _root_.LieSubalgebra.exists_ne_zero_forall_eval_ne_zero_mem_intCartan
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] {ι : Type*} [Finite ι]
    (b : Module.Basis ι K L) :
    ∃ q : MvPolynomial ι K, q ≠ 0 ∧ ∀ x : L, eval (b.equivFun x) q ≠ 0 →
      ∃ g ∈ intLieAlgebra K L, ∃ h ∈ H, g • h = x := by
  obtain ⟨p, ⟨v, hv⟩, hp⟩ :=
    H.exists_rootExponentialPolynomialParametrization b (Module.finBasis K H)
  obtain ⟨q, hq0, hq⟩ :=
    (algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt
      hv).exists_ne_zero_setOf_eval_ne_zero_subset_range
  refine ⟨q, hq0, fun x hx ↦ ?_⟩
  obtain ⟨t, ht⟩ := hq hx
  obtain ⟨g, hg, h, hh, hgh⟩ := hp t
  exact ⟨g, hg, h, hh, b.equivFun.injective (hgh.trans ht)⟩

/-- **Conjugacy of Cartan subalgebras.** In a finite-dimensional Lie algebra with nondegenerate
Killing form over an algebraically closed field of characteristic zero, any two Cartan
subalgebras `H` and `H'` are conjugate under the group `Int(L)` of inner automorphisms. -/
theorem _root_.LieSubalgebra.exists_map_intLieAlgebraLieEquiv_eq (H H' : LieSubalgebra K L)
    [H.IsCartanSubalgebra] [H'.IsCartanSubalgebra] :
    ∃ g : intLieAlgebra K L, H.map (intLieAlgebraLieEquiv g).toLieHom = H' := by
  classical
  let b := Module.finBasis K L
  obtain ⟨q, hq0, hq⟩ := H.exists_ne_zero_forall_eval_ne_zero_mem_intCartan b
  obtain ⟨q', hq0', hq'⟩ := H'.exists_ne_zero_forall_eval_ne_zero_mem_intCartan b
  -- the regular elements are those outside the zero locus of a nonzero polynomial `c`
  obtain ⟨c, hc0, hc⟩ : ∃ c : MvPolynomial _ K, c ≠ 0 ∧
      ∀ x : L, eval (b.equivFun x) c ≠ 0 → IsRegular K x :=
    ⟨_, polyCharpoly_coeff_rank_ne_zero K L b,
      fun x hx ↦ (isRegular_iff_coeff_polyCharpoly_rank_ne_zero K b x).mpr (by simpa using hx)⟩
  -- a point outside the zero loci of `q`, `q'` and `c`
  obtain ⟨y, hy⟩ : ∃ y, eval y (q * q' * c) ≠ 0 := by
    by_contra! hy
    exact mul_ne_zero (mul_ne_zero hq0 hq0') hc0 (MvPolynomial.funext fun y ↦ by simpa using hy y)
  obtain ⟨x, rfl⟩ := b.equivFun.surjective y
  simp only [map_mul, mul_ne_zero_iff] at hy
  obtain ⟨⟨hyq, hyq'⟩, hyc⟩ := hy
  have hx : IsRegular K x := hc x hyc
  -- `x` is `g h` and `g' h'`, so its Engel subalgebra is both `g H` and `g' H'`
  obtain ⟨g, hg, h, hh, hgh⟩ := hq x hyq
  obtain ⟨g', hg', h', hh', hgh'⟩ := hq' x hyq'
  have hH : H.map (intLieAlgebraLieEquiv ⟨g, hg⟩).toLieHom =
      H'.map (intLieAlgebraLieEquiv ⟨g', hg'⟩).toLieHom := by
    rw [← H.engel_eq_map_of_isRegular _ hh (by rwa [intLieAlgebraLieEquiv_apply, hgh]),
      ← H'.engel_eq_map_of_isRegular _ hh' (by rwa [intLieAlgebraLieEquiv_apply, hgh']),
      intLieAlgebraLieEquiv_apply, intLieAlgebraLieEquiv_apply, hgh, hgh']
  -- hence `g'⁻¹ g` carries `H` onto `H'`
  refine ⟨⟨g', hg'⟩⁻¹ * ⟨g, hg⟩, LieSubalgebra.ext _ _ fun z ↦ ?_⟩
  simpa [LieSubalgebra.mem_map, intLieAlgebraLieEquiv_mul, LieEquiv.symm_apply_eq] using
    congrArg (intLieAlgebraLieEquiv ⟨g', hg'⟩ z ∈ ·) hH

end TauCeti
