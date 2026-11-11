/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.RingTheory.Idempotents.Triangular

/-!
# The perturbation lemma for strictly triangular perturbations

A cube of chain complexes is a module `M = ⨁_ε M_ε` indexed by the vertices `ε` of a cube, the
subsets `I = Finset (Fin n)` ordered by inclusion, with a differential `dM + δ`: the internal
differentials `dM` of the vertices together with the arrows `δ` of the cube, each of which goes
from a vertex `ε` to a vertex `ε' > ε`. If every vertex is contracted onto a smaller complex,
homological perturbation transfers the arrows of the cube to the contracted vertices. This file
proves that the transfer is a finite computation along strictly increasing paths of the cube.
Nothing about cubes is used beyond the order: we work with any finite preordered set
`I`.

The summands are recorded by complete families of orthogonal idempotents `eM` of `M` and `eN` of
`N`. Let `c` be a special contraction of `(M, dM)` onto `(N, dN)` which is diagonal: its
homotopy `h` commutes with every `eM k`, and its inclusion `i` and projection `p` intertwine
`eN k` with `eM k`. Let `δ` be strictly triangular: its component `eM j * δ * eM i` vanishes
unless `i < j` (`TauCeti.IsStrictlyTriangular`). Then:

* `δ h` is strictly triangular, hence nilpotent, so `1 + δ h` is invertible
  (`TauCeti.LinearSpecialContraction.isUnit_one_add_mul_homotopy_of_isStrictlyTriangular`).
  This is the invertibility hypothesis of the basic perturbation lemma
  `TauCeti.LinearSpecialContraction.perturb`, which applies to `δ` once moreover
  `(dM + δ)² = dM²`, for instance when `dM` and `dM + δ` are both differentials;
* the perturbation operator `X = (1 + δ h)⁻¹ δ` is the finite sum
  `∑_{k < #I} (-1)ᵏ (δ h)ᵏ δ`
  (`TauCeti.LinearSpecialContraction.perturbationSeries_eq_sum_of_isStrictlyTriangular`);
* its components satisfy the recursion
  `X_{ji} = δ_{ji} - ∑_{i < k < j} δ_{jk} h X_{ki}`
  (`TauCeti.LinearSpecialContraction.mul_perturbationSeries_mul_eq_sub_sum`), where
  `X_{ji} = eM j * X * eM i`. Unrolling it writes `X_{ji}` as the sum, over the strictly
  increasing chains `i = k₀ < k₁ < ⋯ < k_m = j`, of `(-1)^(m-1) δ_{k_m k_{m-1}} h ⋯ h δ_{k₁ k₀}`;
* the transferred differential `dN + p X i` agrees with `dN` except on the strictly increasing
  components, where its component from `i` to `j` adds `p X_{ji} i`
  (`TauCeti.LinearSpecialContraction.isStrictlyTriangular_perturbedDifferential_sub` and
  `TauCeti.LinearSpecialContraction.comp_perturbedDifferential_comp`). If `dM` is diagonal then so
  is `dN` (`TauCeti.LinearContraction.comp_dN_eq_dN_comp`), so the transferred structure is
  again a cube with the vertex differentials `dN`;
* when `(dM + δ)² = dM²`, so that the perturbed contraction exists, its inclusion, projection
  and homotopy differ from those of `c` only in strictly increasing components
  (`TauCeti.LinearSpecialContraction.comp_perturb_incl_comp_of_not_lt` and its two companions), so
  the perturbed contraction is again diagonal up to strictly increasing terms.

The invertibility, the finite series, the component recursion and the components of the
transferred differential hold for every strictly triangular `δ`; only the statements about the
perturbed contraction need `(dM + δ)² = dM²`. Neither `dM` nor `dN` needs to be diagonal for
these statements, and only `eM` is required to be a complete family of orthogonal idempotents;
`eN` only enters through the intertwining hypotheses.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
* C. Manolescu and P. Ozsváth, *Heegaard Floer homology and integer surgeries on links*,
  arXiv:1011.1317 (homological perturbation of hypercubes of chain complexes).
-/

public section

open Finset

namespace TauCeti.LinearSpecialContraction

variable {R M N I : Type*} [Semiring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  (δ : Module.End R M) {eM : I → Module.End R M} {eN : I → Module.End R N}

/-! ### The perturbation operator of a strictly triangular perturbation -/

section PerturbationSeries

variable [Preorder I] [Fintype I] (he : CompleteOrthogonalIdempotents eM)
  (hh : ∀ k, Commute (eM k) c.homotopy) (hδ : IsStrictlyTriangular eM δ)
include he hh hδ

/-- **Invertibility for strictly triangular perturbations.** If the homotopy of `c` commutes with
a complete family of orthogonal idempotents indexed by a finite preordered set and `δ` is strictly
triangular, then `δ h` is nilpotent and `1 + δ h` is invertible. This is the invertibility
hypothesis of the basic perturbation lemma `LinearSpecialContraction.perturb`, which applies to `δ`
when moreover `(dM + δ)² = dM²`. -/
theorem isUnit_one_add_mul_homotopy_of_isStrictlyTriangular : IsUnit (1 + δ * c.homotopy) :=
  (hδ.mul_of_forall_commute hh).isUnit_one_add he

/-- **The perturbation operator of a strictly triangular perturbation is a finite sum.** It is the
geometric series `∑_{k < #I} (-1)ᵏ (δ h)ᵏ δ`, truncated at the cardinality of the index set. -/
theorem perturbationSeries_eq_sum_of_isStrictlyTriangular :
    c.perturbationSeries δ =
      ∑ k ∈ range (Fintype.card I), (-(δ * c.homotopy)) ^ k * δ := by
  have hu : (δ * c.homotopy) ^ Fintype.card I = 0 :=
    (hδ.mul_of_forall_commute hh).pow_card_eq_zero he
  ext z : 1
  rw [c.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero δ
      (c.isUnit_one_add_mul_homotopy_of_isStrictlyTriangular δ he hh hδ)
      (by rw [hu, LinearMap.zero_apply]), LinearMap.sum_apply]
  simp only [mul_apply_eq_comp]

/-- The perturbation operator of a strictly triangular perturbation is strictly triangular. -/
theorem isStrictlyTriangular_perturbationSeries :
    IsStrictlyTriangular eM (c.perturbationSeries δ) := by
  rw [c.perturbationSeries_eq_sum_of_isStrictlyTriangular δ he hh hδ]
  have hk (k : ℕ) : IsStrictlyTriangular eM ((-(δ * c.homotopy)) ^ k * δ) := by
    induction k with
    | zero => rwa [pow_zero, one_mul]
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      exact (hδ.mul_of_forall_commute hh).neg.mul he ih
  exact IsStrictlyTriangular.sum fun k _ ↦ hk k

/-- **The components of the perturbation operator along strictly increasing paths.** The
component `X_{ji} = eM j * X * eM i` of the perturbation operator is determined by the components
of `δ` and the components `X_{ki}` with `i < k < j`:

`X_{ji} = δ_{ji} - ∑_{i < k < j} δ_{jk} h X_{ki}`.

Unrolling this recursion, `X_{ji}` is the sum over the strictly increasing chains
`i = k₀ < k₁ < ⋯ < k_m = j` of `(-1)^(m-1) δ_{k_m k_{m-1}} h ⋯ h δ_{k₁ k₀}`. -/
theorem mul_perturbationSeries_mul_eq_sub_sum [LocallyFiniteOrder I] (i j : I) :
    eM j * c.perturbationSeries δ * eM i =
      eM j * δ * eM i -
        ∑ k ∈ Ioo i j, eM j * δ * eM k * c.homotopy * (eM k * c.perturbationSeries δ * eM i) := by
  have hU := c.isUnit_one_add_mul_homotopy_of_isStrictlyTriangular δ he hh hδ
  have hX := c.isStrictlyTriangular_perturbationSeries δ he hh hδ
  -- The fixed-point equation `X = δ - δ h X`.
  have hfix : c.perturbationSeries δ = δ - δ * (c.homotopy * c.perturbationSeries δ) := by
    have h := c.comp_homotopy_comp_perturbationSeries δ hU
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp] at h
    rw [h, sub_sub_cancel]
  conv_lhs => rw [hfix]
  rw [mul_sub, sub_mul,
    hδ.mul_mul_mul_eq_sum_Ioo he (hX.mul_of_forall_commute_left hh) i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc (eM k), (hh k).eq]
  simp only [mul_assoc]

end PerturbationSeries

/-! ### The transferred differential -/

section Retract

variable (hincl : ∀ k, c.incl ∘ₗ eN k = eM k ∘ₗ c.incl)
  (hproj : ∀ k, eN k ∘ₗ c.proj = c.proj ∘ₗ eM k)
include hincl hproj

/-- The component of the transferred differential `dN + p X i` from `i` to `j` is the component
of `dN` plus the compression of the component `X_{ji}` of the perturbation operator. -/
theorem comp_perturbedDifferential_comp (i j : I) :
    eN j ∘ₗ c.perturbedDifferential δ ∘ₗ eN i =
      eN j ∘ₗ dN ∘ₗ eN i +
        c.proj ∘ₗ (eM j * c.perturbationSeries δ * eM i) ∘ₗ c.incl := by
  rw [perturbedDifferential_def, LinearMap.add_comp, LinearMap.comp_add,
    c.comp_proj_comp_comp_incl_comp hincl hproj]

variable [Preorder I] [Fintype I] (he : CompleteOrthogonalIdempotents eM)
  (hh : ∀ k, Commute (eM k) c.homotopy) (hδ : IsStrictlyTriangular eM δ)
include he hh hδ

/-- **The transferred arrows are strictly triangular.** For a strictly triangular perturbation of
a diagonal contraction, the transferred differential `dN + p X i` differs from `dN` by a strictly
triangular endomorphism of the retract. -/
theorem isStrictlyTriangular_perturbedDifferential_sub :
    IsStrictlyTriangular eN (c.perturbedDifferential δ - dN) := by
  refine isStrictlyTriangular_iff.2 fun i j h ↦ ?_
  rw [perturbedDifferential_def, add_sub_cancel_left, Module.End.mul_eq_comp,
    Module.End.mul_eq_comp, LinearMap.comp_assoc, c.comp_proj_comp_comp_incl_comp hincl hproj,
    (c.isStrictlyTriangular_perturbationSeries δ he hh hδ).mul_mul_eq_zero h, LinearMap.zero_comp,
    LinearMap.comp_zero]

/-- Away from the strictly increasing components, and in particular on the diagonal, the
transferred differential agrees with `dN`. -/
theorem comp_perturbedDifferential_comp_of_not_lt {i j : I} (h : ¬i < j) :
    eN j ∘ₗ c.perturbedDifferential δ ∘ₗ eN i = eN j ∘ₗ dN ∘ₗ eN i := by
  rw [c.comp_perturbedDifferential_comp δ hincl hproj,
    (c.isStrictlyTriangular_perturbationSeries δ he hh hδ).mul_mul_eq_zero h, LinearMap.zero_comp,
    LinearMap.comp_zero, add_zero]

variable (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM)

omit hproj in
/-- Away from the strictly increasing components, the perturbed inclusion `i - h X i` agrees with
the inclusion of `c`. -/
theorem comp_perturb_incl_comp_of_not_lt {i j : I} (h : ¬i < j) :
    eM j ∘ₗ (c.perturb δ hsq
        (c.isUnit_one_add_mul_homotopy_of_isStrictlyTriangular δ he hh hδ)).incl ∘ₗ eN i =
      eM j ∘ₗ c.incl ∘ₗ eN i := by
  have hX := (c.isStrictlyTriangular_perturbationSeries δ he hh hδ).mul_mul_eq_zero h
  have hjh (f : N →ₗ[R] M) : eM j ∘ₗ c.homotopy ∘ₗ f = c.homotopy ∘ₗ eM j ∘ₗ f := by
    rw [← LinearMap.comp_assoc, ← Module.End.mul_eq_comp, (hh j).eq, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
  -- Push the idempotents inwards to the component `eM j * X * eM i`, which vanishes.
  have key : eM j ∘ₗ (c.homotopy ∘ₗ c.perturbationSeries δ ∘ₗ c.incl) ∘ₗ eN i =
      c.homotopy ∘ₗ (eM j * c.perturbationSeries δ * eM i) ∘ₗ c.incl := by
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc, hincl, hjh]
  rw [perturb_incl, LinearMap.sub_comp, LinearMap.comp_sub, sub_eq_self, key, hX,
    LinearMap.zero_comp, LinearMap.comp_zero]

omit hincl in
/-- Away from the strictly increasing components, the perturbed projection `p - p X h` agrees with
the projection of `c`. -/
theorem comp_perturb_proj_comp_of_not_lt {i j : I} (h : ¬i < j) :
    eN j ∘ₗ (c.perturb δ hsq
        (c.isUnit_one_add_mul_homotopy_of_isStrictlyTriangular δ he hh hδ)).proj ∘ₗ eM i =
      eN j ∘ₗ c.proj ∘ₗ eM i := by
  have hX := (c.isStrictlyTriangular_perturbationSeries δ he hh hδ).mul_mul_eq_zero h
  have hpj (f : M →ₗ[R] M) : eN j ∘ₗ c.proj ∘ₗ f = c.proj ∘ₗ eM j ∘ₗ f := by
    rw [← LinearMap.comp_assoc, hproj, LinearMap.comp_assoc]
  have hhi : c.homotopy ∘ₗ eM i = eM i ∘ₗ c.homotopy := by
    rw [← Module.End.mul_eq_comp, ← (hh i).eq, Module.End.mul_eq_comp]
  -- Push the idempotents inwards to the component `eM j * X * eM i`, which vanishes.
  have key : eN j ∘ₗ (c.proj ∘ₗ c.perturbationSeries δ ∘ₗ c.homotopy) ∘ₗ eM i =
      c.proj ∘ₗ (eM j * c.perturbationSeries δ * eM i) ∘ₗ c.homotopy := by
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc, hhi, hpj]
  rw [perturb_proj, LinearMap.sub_comp, LinearMap.comp_sub, sub_eq_self, key, hX,
    LinearMap.zero_comp, LinearMap.comp_zero]

omit hincl hproj in
/-- Away from the strictly increasing components, the perturbed homotopy `h - h X h` agrees with
the homotopy of `c`. -/
theorem comp_perturb_homotopy_comp_of_not_lt {i j : I} (h : ¬i < j) :
    eM j ∘ₗ (c.perturb δ hsq
        (c.isUnit_one_add_mul_homotopy_of_isStrictlyTriangular δ he hh hδ)).homotopy ∘ₗ eM i =
      eM j ∘ₗ c.homotopy ∘ₗ eM i := by
  have hX := (c.isStrictlyTriangular_perturbationSeries δ he hh hδ).mul_mul_eq_zero h
  rw [perturb_homotopy, LinearMap.sub_comp, LinearMap.comp_sub, sub_eq_self]
  simp only [← Module.End.mul_eq_comp]
  -- Push the idempotents inwards to the component `eM j * X * eM i`, which vanishes.
  calc eM j * (c.homotopy * (c.perturbationSeries δ * c.homotopy) * eM i)
      = c.homotopy * (eM j * c.perturbationSeries δ * eM i) * c.homotopy := by
        simp only [mul_assoc, (hh j).left_comm, ← (hh i).eq]
    _ = 0 := by rw [hX, mul_zero, zero_mul]

end Retract

end TauCeti.LinearSpecialContraction
