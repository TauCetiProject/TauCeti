/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
public import TauCeti.Algebra.Ring.Units
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# The basic perturbation lemma

Let `c` be a special contraction of `(M, dM)` onto `(N, dN)`, with inclusion `i`, projection `p`
and homotopy `h`, and let `δ` be a *perturbation* of `dM`: an endomorphism with
`(dM + δ)² = dM²`, so that `dM + δ` is again a differential whenever `dM` is.  The basic
perturbation lemma transports the contraction to the perturbed differential.  Its engine is the
operator

`X = (1 + δ h)⁻¹ δ = δ (1 + h δ)⁻¹`,

which is the geometric series `∑ₙ (-1)ⁿ (δ h)ⁿ δ` whenever that series is pointwise finite; the
lemma is stated for any `δ` making `1 + δ h` invertible, and
`Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero` supplies the pointwise-finite case.
The operator satisfies the identity

`dM X + X dM + X i p X = 0`   (`LinearSpecialContraction.perturbationSeries_maurerCartan`),

and the perturbed contraction is

`i' = i - h X i`,   `p' = p - p X h`,   `h' = h - h X h`,   `dN' = dN + p X i`.

The square of the perturbed differential of the retract is the square of the original one, so it
is a differential whenever `dN` is.

With the convention `1 - i p = dM h + h dM` fixed in `TauCeti.Contraction`, the homotopy is the
negative of the one in Crainic's account, whence the signs `1 + δ h` and `- h X i` in place of
Crainic's `1 - δ h` and `+ h X i`.

## Main definitions

* `TauCeti.LinearSpecialContraction.perturbationSeries`: the operator `X = (1 + δ h)⁻¹ δ`.
* `TauCeti.LinearSpecialContraction.perturbedDifferential`: the endomorphism `dN + p X i`.
* `TauCeti.LinearSpecialContraction.perturb`: the basic perturbation lemma, as a special
  contraction of `(M, dM + δ)` onto `(N, dN + p X i)`.

## Main results

* `TauCeti.LinearSpecialContraction.perturbationSeries_maurerCartan`: the identity
  `dM X + X dM + X i p X = 0`.
* `TauCeti.LinearSpecialContraction.perturbationSeries_mem`: the perturbation operator preserves
  every additive subgroup preserved by `δ` and `h`, wherever the geometric series is finite.
* `TauCeti.LinearSpecialContraction.perturbedDifferential_comp_perturbedDifferential`: the
  perturbed differential of the retract squares to the square of `dN`.
* `TauCeti.LinearSpecialContraction.perturb_proj_comp_one_add_mul`: the perturbed projection
  satisfies `p' (1 + δ h) = p`; with `TauCeti.LinearSpecialContraction.perturb_proj_comp_homotopy`
  and `TauCeti.LinearSpecialContraction.perturb_proj_comp_incl`, these are the identities making
  `p'` a coalgebra morphism in the tensor trick.
* `TauCeti.LinearSpecialContraction.comp_perturbationSeries_eq_comp`,
  `TauCeti.LinearSpecialContraction.comp_perturb_incl_eq_comp` and
  `TauCeti.LinearSpecialContraction.comp_perturb_proj_eq_comp`: a map intertwining `δ` and `h`
  with endomorphisms of another module intertwines the perturbation operator and the perturbed
  inclusion and projection too.  The specialisations
  `TauCeti.LinearSpecialContraction.comp_perturbationSeries_eq_rTensor_comp` and
  `TauCeti.LinearSpecialContraction.comp_perturbationSeries_eq_map_comp` (with their `incl` and
  `proj` versions) say that the perturbation data are maps of right comodules, respectively odd
  maps of left comodules, whenever `δ`, `h`, `i` and `p` are.
* `TauCeti.LinearSpecialContraction.isHomogeneous_perturbationSeries`,
  `TauCeti.LinearSpecialContraction.isHomogeneous_perturb_incl` and
  `TauCeti.LinearSpecialContraction.isHomogeneous_perturb_proj`: for `δ` of degree `q`, `h` of
  degree `-q` and `δ h` locally nilpotent, `X` has degree `q`; then `i'` and `p'` have degree
  zero when `i` and `p` do.  `TauCeti.LinearSpecialContraction.isHomogeneous_perturbedDifferential`
  gives the degree `q` of `dN + p X i` when `dN` has degree `q`.

## References

* E. H. Brown, *Twisted tensor products, I*, Annals of Mathematics 69 (1959), 223--246.
* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

universe uR uM uN uP

namespace TauCeti

namespace LinearSpecialContraction

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  (δ : Module.End R M) {P : Type uP} [AddCommMonoid P] [Module R P]

/-- The **perturbation operator** `X = (1 + δ h)⁻¹ δ` of the basic perturbation lemma.  When
`δ h` is locally nilpotent it is the pointwise finite geometric series `∑ₙ (-1)ⁿ (δ h)ⁿ δ`.  It is
defined through `Ring.inverse`, so it is meaningful for every `δ`, and satisfies its defining
equations once `1 + δ h` is a unit. -/
noncomputable def perturbationSeries : Module.End R M :=
  Ring.inverse (1 + δ * c.homotopy) * δ

/-- The perturbation operator is `Ring.inverse (1 + δ h)` composed with `δ`. -/
theorem perturbationSeries_def :
    c.perturbationSeries δ = Ring.inverse (1 + δ * c.homotopy) * δ := (rfl)

section Units

variable (hU : IsUnit (1 + δ * c.homotopy))
include hU

/-- `(1 + δ h) X = δ`. -/
theorem one_add_mul_perturbationSeries : (1 + δ * c.homotopy) * c.perturbationSeries δ = δ := by
  rw [perturbationSeries_def, ← mul_assoc, Ring.mul_inverse_cancel _ hU, one_mul]

/-- `X (1 + h δ) = δ`. -/
theorem perturbationSeries_mul_one_add : c.perturbationSeries δ * (1 + c.homotopy * δ) = δ := by
  have h : δ * (1 + c.homotopy * δ) = (1 + δ * c.homotopy) * δ := by noncomm_ring
  rw [perturbationSeries_def, mul_assoc, h, ← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]

/-- The fixed-point equation `δ h X = δ - X` of the perturbation operator. -/
theorem comp_homotopy_comp_perturbationSeries :
    δ ∘ₗ c.homotopy ∘ₗ c.perturbationSeries δ = δ - c.perturbationSeries δ := by
  have h := c.one_add_mul_perturbationSeries δ hU
  rw [add_mul, one_mul, mul_assoc] at h
  simpa only [Module.End.mul_eq_comp] using eq_sub_of_add_eq' h

/-- The fixed-point equation `X h δ = δ - X` of the perturbation operator. -/
theorem perturbationSeries_comp_homotopy_comp :
    c.perturbationSeries δ ∘ₗ c.homotopy ∘ₗ δ = δ - c.perturbationSeries δ := by
  have h := c.perturbationSeries_mul_one_add δ hU
  rw [mul_add, mul_one] at h
  simpa only [Module.End.mul_eq_comp] using eq_sub_of_add_eq' h

/-- The fixed-point equation `δ h X = δ - X`, with a further factor on the right. -/
theorem comp_homotopy_comp_perturbationSeries_assoc (f : P →ₗ[R] M) :
    δ ∘ₗ c.homotopy ∘ₗ c.perturbationSeries δ ∘ₗ f = δ ∘ₗ f - c.perturbationSeries δ ∘ₗ f := by
  rw [← LinearMap.sub_comp, ← c.comp_homotopy_comp_perturbationSeries δ hU,
    LinearMap.comp_assoc, LinearMap.comp_assoc]

/-- The fixed-point equation `X h δ = δ - X`, with a further factor on the right. -/
theorem perturbationSeries_comp_homotopy_comp_assoc (f : P →ₗ[R] M) :
    c.perturbationSeries δ ∘ₗ c.homotopy ∘ₗ δ ∘ₗ f = δ ∘ₗ f - c.perturbationSeries δ ∘ₗ f := by
  rw [← LinearMap.sub_comp, ← c.perturbationSeries_comp_homotopy_comp δ hU,
    LinearMap.comp_assoc, LinearMap.comp_assoc]

/-- On an element `z` killed by `(δ h)^k δ`, the perturbation operator is the finite geometric
series `∑_{j < k} (-1)^j (δ h)^j δ`. -/
theorem perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero {z : M} {k : ℕ}
    (hz : ((δ * c.homotopy) ^ k) (δ z) = 0) :
    c.perturbationSeries δ z = ∑ j ∈ Finset.range k, ((-(δ * c.homotopy)) ^ j) (δ z) := by
  set u := δ * c.homotopy
  have hgeom : (1 + u) * ∑ j ∈ Finset.range k, (-u) ^ j = 1 - (-u) ^ k := by
    simpa only [sub_neg_eq_add] using mul_neg_geom_sum (-u) k
  have hk : ((-u) ^ k) (δ z) = 0 := by
    rw [neg_pow, mul_apply_eq_comp, hz, map_zero]
  have h1 : (1 + u) ((∑ j ∈ Finset.range k, (-u) ^ j) (δ z)) = δ z := by
    rw [← mul_apply_eq_comp, hgeom, LinearMap.sub_apply, one_apply_eq_self, hk, sub_zero]
  calc c.perturbationSeries δ z
      = Ring.inverse (1 + u) ((1 + u) ((∑ j ∈ Finset.range k, (-u) ^ j) (δ z))) := by
        rw [h1, perturbationSeries_def, mul_apply_eq_comp]
    _ = (∑ j ∈ Finset.range k, (-u) ^ j) (δ z) := by
        rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hU, one_apply_eq_self]
    _ = ∑ j ∈ Finset.range k, ((-u) ^ j) (δ z) := LinearMap.sum_apply _ _ _

omit hU in
/-- **The perturbation operator preserves invariant subgroups.**  If `δ` and `h` preserve an
additive subgroup `S`, such as a submodule, then the perturbation operator sends every `z ∈ S` with
`(δ h)^k δ z = 0` back into `S`, being the finite geometric series `∑_{j < k} (-1)^j (δ h)^j δ`
on `z` when `1 + δ h` is a unit, and `0` otherwise. -/
theorem perturbationSeries_mem {S : AddSubgroup M} (hδ : ∀ z ∈ S, δ z ∈ S)
    (hh : ∀ z ∈ S, c.homotopy z ∈ S) {z : M} (hz : z ∈ S) {k : ℕ}
    (hk : ((δ * c.homotopy) ^ k) (δ z) = 0) : c.perturbationSeries δ z ∈ S := by
  by_cases hU : IsUnit (1 + δ * c.homotopy)
  swap
  · rw [perturbationSeries_def, Ring.inverse_non_unit _ hU, zero_mul]
    exact S.zero_mem
  rw [c.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero δ hU hk]
  have key (j : ℕ) : ((-(δ * c.homotopy)) ^ j) (δ z) ∈ S := by
    induction j with
    | zero => simpa using hδ z hz
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, LinearMap.neg_apply, mul_apply_eq_comp]
      exact S.neg_mem (hδ _ (hh _ ih))
  exact sum_mem fun j _ ↦ key j

omit hU in
/-- The perturbation operator satisfies the Maurer--Cartan-type identity
`dM X + X dM + X i p X = 0`; this single identity drives every equation of the basic
perturbation lemma. When `1 + δ h` is not a unit the operator is `0` and the identity is trivial. -/
theorem perturbationSeries_maurerCartan (hδ : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) :
    dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
      c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ = 0 := by
  by_cases hU : IsUnit (1 + δ * c.homotopy)
  on_goal 2 => simp [perturbationSeries_def, Ring.inverse_non_unit _ hU]
  set X := c.perturbationSeries δ
  have hT : dM * δ + δ * dM + δ * δ = 0 := by
    calc dM * δ + δ * dM + δ * δ = (dM + δ) * (dM + δ) - dM * dM := by noncomm_ring
      _ = 0 := by simp only [Module.End.mul_eq_comp]; rw [hδ, sub_self]
  have hip : c.incl ∘ₗ c.proj = 1 - (dM * c.homotopy + c.homotopy * dM) := by
    rw [Module.End.one_eq_id, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact c.incl_comp_proj
  have hUX := c.one_add_mul_perturbationSeries δ hU
  have hXV := c.perturbationSeries_mul_one_add δ hU
  -- Conjugating the identity by the units `1 + δ h` and `1 + h δ` turns it into `(dM + δ)² = dM²`.
  have key : (1 + δ * c.homotopy) * (dM * X + X * dM + X * (c.incl ∘ₗ c.proj) * X) *
      (1 + c.homotopy * δ) = 0 := by
    rw [hip]
    calc (1 + δ * c.homotopy) * (dM * X + X * dM +
          X * (1 - (dM * c.homotopy + c.homotopy * dM)) * X) * (1 + c.homotopy * δ)
        = (1 + δ * c.homotopy) * dM * (X * (1 + c.homotopy * δ)) +
            ((1 + δ * c.homotopy) * X) * dM * (1 + c.homotopy * δ) +
            ((1 + δ * c.homotopy) * X) * (1 - (dM * c.homotopy + c.homotopy * dM)) *
              (X * (1 + c.homotopy * δ)) := by noncomm_ring
      _ = (1 + δ * c.homotopy) * dM * δ + δ * dM * (1 + c.homotopy * δ) +
            δ * (1 - (dM * c.homotopy + c.homotopy * dM)) * δ := by rw [hUX, hXV]
      _ = dM * δ + δ * dM + δ * δ := by noncomm_ring
      _ = 0 := hT
  have key' : dM * X + X * dM + X * (c.incl ∘ₗ c.proj) * X = 0 :=
    hU.mul_right_eq_zero.1 ((isUnit_one_add_mul_comm.1 hU).mul_left_eq_zero.1 key)
  simpa only [Module.End.mul_eq_comp, LinearMap.comp_assoc] using key'

end Units

/-- The perturbed endomorphism `dN + p X i` of the retract. -/
noncomputable def perturbedDifferential : Module.End R N :=
  dN + c.proj ∘ₗ c.perturbationSeries δ ∘ₗ c.incl

/-- The perturbed differential of the retract is `dN + p X i`. -/
theorem perturbedDifferential_def :
    c.perturbedDifferential δ = dN + c.proj ∘ₗ c.perturbationSeries δ ∘ₗ c.incl := (rfl)

section Perturb

variable (hδ : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) (hU : IsUnit (1 + δ * c.homotopy))
include hδ hU

omit hU in
/-- The perturbed differential of the retract squares to the square of `dN`; in particular it is
a differential whenever `dN` is. -/
theorem perturbedDifferential_comp_perturbedDifferential :
    c.perturbedDifferential δ ∘ₗ c.perturbedDifferential δ = dN ∘ₗ dN := by
  have h1 : c.proj ∘ₗ (dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
      c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ) ∘ₗ c.incl = 0 := by
    rw [c.perturbationSeries_maurerCartan δ hδ, LinearMap.zero_comp, LinearMap.comp_zero]
  rw [perturbedDifferential_def]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_assoc, ← c.dM_comp_incl, ← c.proj_comp_dM_assoc,
    c.incl_comp_proj_assoc] at h1 ⊢
  linear_combination (norm := abel) h1

omit hU in
/-- If `dM` squares to zero, so does the perturbed differential of the retract. -/
theorem perturbedDifferential_comp_perturbedDifferential_eq_zero (h : dM ∘ₗ dM = 0) :
    c.perturbedDifferential δ ∘ₗ c.perturbedDifferential δ = 0 := by
  rw [c.perturbedDifferential_comp_perturbedDifferential δ hδ, c.dN_comp_dN_eq_zero h]

/-- **The basic perturbation lemma.**  A special contraction of `(M, dM)` onto `(N, dN)` and a
perturbation `δ` of `dM` with `1 + δ h` invertible yield a special contraction of `(M, dM + δ)`
onto `(N, dN + p X i)`, with

`i' = i - h X i`,   `p' = p - p X h`,   `h' = h - h X h`,

where `X = (1 + δ h)⁻¹ δ` is the perturbation operator. -/
noncomputable def perturb : LinearSpecialContraction (dM + δ) (c.perturbedDifferential δ) where
  incl := c.incl - c.homotopy ∘ₗ c.perturbationSeries δ ∘ₗ c.incl
  proj := c.proj - c.proj ∘ₗ c.perturbationSeries δ ∘ₗ c.homotopy
  homotopy := c.homotopy - c.homotopy ∘ₗ c.perturbationSeries δ ∘ₗ c.homotopy
  dM_comp_incl := by
    have h1 : c.homotopy ∘ₗ (dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
        c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ) ∘ₗ c.incl = 0 := by
      rw [c.perturbationSeries_maurerCartan δ hδ, LinearMap.zero_comp, LinearMap.comp_zero]
    rw [perturbedDifferential_def]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp,
      LinearMap.comp_assoc, ← c.dM_comp_incl, c.incl_comp_proj_assoc,
      c.comp_homotopy_comp_perturbationSeries_assoc δ hU] at h1 ⊢
    linear_combination (norm := abel) h1
  proj_comp_dM := by
    have h1 : c.proj ∘ₗ (dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
        c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ) ∘ₗ
          c.homotopy = 0 := by
      rw [c.perturbationSeries_maurerCartan δ hδ, LinearMap.zero_comp, LinearMap.comp_zero]
    rw [perturbedDifferential_def]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp,
      LinearMap.comp_assoc, ← c.proj_comp_dM, ← c.proj_comp_dM_assoc, c.incl_comp_proj,
      c.incl_comp_proj_assoc, c.perturbationSeries_comp_homotopy_comp δ hU,
      LinearMap.comp_id] at h1 ⊢
    linear_combination (norm := abel) h1
  proj_comp_incl := by
    simp [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    have h1 : c.homotopy ∘ₗ (dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
        c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ) ∘ₗ
          c.homotopy = 0 := by
      rw [c.perturbationSeries_maurerCartan δ hδ, LinearMap.zero_comp, LinearMap.comp_zero]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp,
      LinearMap.comp_assoc, c.incl_comp_proj, c.incl_comp_proj_assoc,
      c.comp_homotopy_comp_perturbationSeries_assoc δ hU,
      c.perturbationSeries_comp_homotopy_comp δ hU, LinearMap.comp_id] at h1 ⊢
    linear_combination (norm := abel) h1
  homotopy_comp_incl := by
    simp [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc]
  proj_comp_homotopy := by
    simp [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc]
  homotopy_comp_homotopy := by
    simp [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc]

/-- The inclusion of the perturbed contraction is `i - h X i`. -/
@[simp]
theorem perturb_incl :
    (c.perturb δ hδ hU).incl = c.incl - c.homotopy ∘ₗ c.perturbationSeries δ ∘ₗ c.incl := (rfl)

/-- The projection of the perturbed contraction is `p - p X h`. -/
@[simp]
theorem perturb_proj :
    (c.perturb δ hδ hU).proj = c.proj - c.proj ∘ₗ c.perturbationSeries δ ∘ₗ c.homotopy := (rfl)

/-- The homotopy of the perturbed contraction is `h - h X h`. -/
@[simp]
theorem perturb_homotopy :
    (c.perturb δ hδ hU).homotopy =
      c.homotopy - c.homotopy ∘ₗ c.perturbationSeries δ ∘ₗ c.homotopy := (rfl)

/-- The perturbed projection annihilates the unperturbed homotopy, `p' h = 0`. -/
theorem perturb_proj_comp_homotopy : (c.perturb δ hδ hU).proj ∘ₗ c.homotopy = 0 := by
  simp [LinearMap.sub_comp, LinearMap.comp_assoc]

/-- The perturbed projection is a left inverse of the unperturbed inclusion, `p' i = 1`. -/
theorem perturb_proj_comp_incl : (c.perturb δ hδ hU).proj ∘ₗ c.incl = LinearMap.id := by
  simp [LinearMap.sub_comp, LinearMap.comp_assoc]

/-- The perturbed projection solves the fixed-point equation `p' (1 + δ h) = p`. -/
theorem perturb_proj_comp_one_add_mul :
    (c.perturb δ hδ hU).proj ∘ₗ (1 + δ * c.homotopy) = c.proj := by
  have h := congrArg (fun f ↦ c.proj ∘ₗ f ∘ₗ c.homotopy)
    (c.perturbationSeries_comp_homotopy_comp δ hU)
  simp only [LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.sub_comp] at h
  rw [perturb_proj, Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id,
    LinearMap.comp_id]
  simp only [LinearMap.sub_comp, LinearMap.comp_assoc, h]
  abel

/-- The perturbed homotopy solves the fixed-point equation `h' (1 + δ h) = h`. -/
theorem perturb_homotopy_comp_one_add_mul :
    (c.perturb δ hδ hU).homotopy ∘ₗ (1 + δ * c.homotopy) = c.homotopy := by
  have h := congrArg (fun f ↦ c.homotopy ∘ₗ f ∘ₗ c.homotopy)
    (c.perturbationSeries_comp_homotopy_comp δ hU)
  simp only [LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.sub_comp] at h
  rw [perturb_homotopy, Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id,
    LinearMap.comp_id]
  simp only [LinearMap.sub_comp, LinearMap.comp_assoc, h]
  abel

/-- The perturbed inclusion satisfies `i' + h' δ i = i`. -/
theorem perturb_incl_add_homotopy_comp :
    (c.perturb δ hδ hU).incl +
      (c.perturb δ hδ hU).homotopy ∘ₗ δ ∘ₗ c.incl = c.incl := by
  have h := congrArg (fun f ↦ c.homotopy ∘ₗ f ∘ₗ c.incl)
    (c.perturbationSeries_comp_homotopy_comp δ hU)
  simp only [LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.sub_comp] at h
  rw [perturb_incl, perturb_homotopy]
  simp only [LinearMap.sub_comp, LinearMap.comp_assoc, h]
  abel

end Perturb

/-! ### Maps intertwining the perturbation data -/

section Intertwining

variable {Q : Type*} [AddCommMonoid Q] [Module R Q] (hU : IsUnit (1 + δ * c.homotopy))
include hU

/-- If `Δ` intertwines `δ` with `δ'` and the homotopy `h` with `h'`, then it intertwines the
perturbation operator `X` with every `X'` solving `X' (1 + h' δ') = δ'`.  Unlike
`TauCeti.LinearSpecialContraction.perturbationSeries_naturality`, the target need not carry a
contraction, nor `1 + δ' h'` be invertible. -/
theorem comp_perturbationSeries_eq_comp (Δ : M →ₗ[R] Q) {δ' h' X' : Module.End R Q}
    (hδ' : Δ ∘ₗ δ = δ' ∘ₗ Δ) (hh' : Δ ∘ₗ c.homotopy = h' ∘ₗ Δ)
    (hX' : X' * (1 + h' * δ') = δ') :
    Δ ∘ₗ c.perturbationSeries δ = X' ∘ₗ Δ := by
  -- `V = 1 + h δ` is surjective, so it suffices to compare both sides after `V`, where they both
  -- become `δ' Δ` by `X V = δ`, `Δ V = (1 + h' δ') Δ` and `X' (1 + h' δ') = δ'`.
  have hV : Function.Surjective ⇑(1 + c.homotopy * δ) :=
    ((Module.End.isUnit_iff _).1 (isUnit_one_add_mul_comm.1 hU)).2
  have hΔV : Δ ∘ₗ (1 + c.homotopy * δ) = (1 + h' * δ') ∘ₗ Δ := by
    simp only [Module.End.mul_eq_comp, LinearMap.comp_add, LinearMap.add_comp,
      Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
    rw [← LinearMap.comp_assoc, hh', LinearMap.comp_assoc, hδ', LinearMap.comp_assoc]
  refine (LinearMap.cancel_right hV).1 ?_
  rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, c.perturbationSeries_mul_one_add δ hU, hδ',
    LinearMap.comp_assoc, hΔV, ← LinearMap.comp_assoc, ← Module.End.mul_eq_comp, hX']

variable (hδ : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) {QM QN : Type*}

/-- Maps `ΔM`, `ΔN` intertwining the inclusion with `i'`, the homotopy with `h'` and the
perturbation operator with `X'` intertwine the perturbed inclusion with `i' - h' X' i'`. -/
theorem comp_perturb_incl_eq_comp [AddCommGroup QM] [Module R QM] [AddCommMonoid QN]
    [Module R QN] (ΔM : M →ₗ[R] QM) (ΔN : N →ₗ[R] QN) {h' X' : Module.End R QM}
    {i' : QN →ₗ[R] QM} (hi : ΔM ∘ₗ c.incl = i' ∘ₗ ΔN) (hh : ΔM ∘ₗ c.homotopy = h' ∘ₗ ΔM)
    (hX : ΔM ∘ₗ c.perturbationSeries δ = X' ∘ₗ ΔM) :
    ΔM ∘ₗ (c.perturb δ hδ hU).incl = (i' - h' ∘ₗ X' ∘ₗ i') ∘ₗ ΔN := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hi hh hX
  ext x
  simp [hi, hh, hX]

/-- Maps `ΔM`, `ΔN` intertwining the projection with `p'`, the homotopy with `h'` and the
perturbation operator with `X'` intertwine the perturbed projection with `p' - p' X' h'`. -/
theorem comp_perturb_proj_eq_comp [AddCommMonoid QM] [Module R QM] [AddCommGroup QN]
    [Module R QN] (ΔM : M →ₗ[R] QM) (ΔN : N →ₗ[R] QN) {h' X' : Module.End R QM}
    {p' : QM →ₗ[R] QN} (hp : ΔN ∘ₗ c.proj = p' ∘ₗ ΔM) (hh : ΔM ∘ₗ c.homotopy = h' ∘ₗ ΔM)
    (hX : ΔM ∘ₗ c.perturbationSeries δ = X' ∘ₗ ΔM) :
    ΔN ∘ₗ (c.perturb δ hδ hU).proj = (p' - p' ∘ₗ X' ∘ₗ h') ∘ₗ ΔM := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hp hh hX
  ext x
  simp [hp, hh, hX]

end Intertwining

end LinearSpecialContraction

/-! ### Degrees of the perturbation data -/

namespace LinearSpecialContraction

section Graded

variable {R : Type uR} {M : Type uM} {N : Type uN} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {δ : Module.End R M} {ι : Type*} [AddCommGroup ι] {𝒜 : ι → Submodule R M}
  {ℬ : ι → Submodule R N} {q : ι}

/-- If the perturbation `δ` has degree `q`, the homotopy has degree `-q` and `δ h` is locally
nilpotent, the perturbation operator has degree `q`. -/
theorem isHomogeneous_perturbationSeries (hδ : LinearMap.IsHomogeneous δ 𝒜 𝒜 q)
    (hh : LinearMap.IsHomogeneous c.homotopy 𝒜 𝒜 (-q))
    (hnil : ∀ z, ∃ n, ((δ * c.homotopy) ^ n) z = 0) :
    LinearMap.IsHomogeneous (c.perturbationSeries δ) 𝒜 𝒜 q := by
  have hδh : LinearMap.IsHomogeneous (δ * c.homotopy) 𝒜 𝒜 0 := by
    rw [Module.End.mul_eq_comp]
    simpa only [neg_add_cancel] using hδ.comp hh
  rw [perturbationSeries_def, Module.End.mul_eq_comp]
  simpa only [add_zero] using (hδh.ringInverse_one_add hnil).comp hδ

variable (hincl : LinearMap.IsHomogeneous c.incl ℬ 𝒜 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜 ℬ 0)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜 𝒜 (-q))
  (hX : LinearMap.IsHomogeneous (c.perturbationSeries δ) 𝒜 𝒜 q)
  (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) (hU : IsUnit (1 + δ * c.homotopy))

include hincl hh hX in
/-- If the homotopy has degree `-q` and the perturbation operator has degree `q`, the perturbed
inclusion has degree zero when the inclusion does. -/
theorem isHomogeneous_perturb_incl :
    LinearMap.IsHomogeneous (c.perturb δ hsq hU).incl ℬ 𝒜 0 := by
  have hhXi := hh.comp (hX.comp hincl)
  rw [zero_add, add_neg_cancel] at hhXi
  rw [perturb_incl]
  exact hincl.sub hhXi

include hproj hh hX in
/-- If the homotopy has degree `-q` and the perturbation operator has degree `q`, the perturbed
projection has degree zero when the projection does. -/
theorem isHomogeneous_perturb_proj :
    LinearMap.IsHomogeneous (c.perturb δ hsq hU).proj 𝒜 ℬ 0 := by
  have hpXh := hproj.comp (hX.comp hh)
  rw [add_zero, neg_add_cancel] at hpXh
  rw [perturb_proj]
  exact hproj.sub hpXh

include hincl hproj hX in
/-- If the perturbation operator has degree `q`, the perturbed differential of the retract has
degree `q` when the inclusion and projection have degree zero and `dN` has degree `q`. -/
theorem isHomogeneous_perturbedDifferential (hdN : LinearMap.IsHomogeneous dN ℬ ℬ q) :
    LinearMap.IsHomogeneous (c.perturbedDifferential δ) ℬ ℬ q := by
  have hpXi := hproj.comp (hX.comp hincl)
  rw [zero_add, add_zero] at hpXi
  rw [perturbedDifferential_def]
  exact hdN.add hpXi

end Graded

/-! ### Comodule-type maps intertwining the perturbation data -/

section TensorProduct

open scoped TensorProduct

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommSemiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {δ : Module.End R M} (hU : IsUnit (1 + δ * c.homotopy))
  (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) {C : Type*}

section RTensor

variable [AddCommMonoid C] [Module R C] {ΔM : M →ₗ[R] M ⊗[R] C}
  (hδ : ΔM ∘ₗ δ = δ.rTensor C ∘ₗ ΔM) (hh : ΔM ∘ₗ c.homotopy = c.homotopy.rTensor C ∘ₗ ΔM)
include hU hδ hh

/-- If `δ` and the homotopy commute with a map `ΔM : M → M ⊗ C`, such as a right coaction, so does
the perturbation operator. -/
theorem comp_perturbationSeries_eq_rTensor_comp :
    ΔM ∘ₗ c.perturbationSeries δ = (c.perturbationSeries δ).rTensor C ∘ₗ ΔM :=
  c.comp_perturbationSeries_eq_comp δ hU ΔM hδ hh <| by
    rw [← LinearMap.rTensor_mul, Module.End.one_eq_id, ← LinearMap.rTensor_id,
      ← LinearMap.rTensor_add, ← LinearMap.rTensor_mul, ← Module.End.one_eq_id,
      c.perturbationSeries_mul_one_add δ hU]

/-- If `δ`, the homotopy and the inclusion commute with maps `ΔM : M → M ⊗ C` and
`ΔN : N → N ⊗ C`, such as right coactions, so does the perturbed inclusion. -/
theorem comp_perturb_incl_eq_rTensor_comp {ΔN : N →ₗ[R] N ⊗[R] C}
    (hi : ΔM ∘ₗ c.incl = c.incl.rTensor C ∘ₗ ΔN) :
    ΔM ∘ₗ (c.perturb δ hsq hU).incl = (c.perturb δ hsq hU).incl.rTensor C ∘ₗ ΔN := by
  rw [c.comp_perturb_incl_eq_comp δ hU hsq ΔM ΔN hi hh
    (c.comp_perturbationSeries_eq_rTensor_comp hU hδ hh), perturb_incl, LinearMap.rTensor_sub,
    LinearMap.rTensor_comp, LinearMap.rTensor_comp]

/-- If `δ`, the homotopy and the projection commute with maps `ΔM : M → M ⊗ C` and
`ΔN : N → N ⊗ C`, such as right coactions, so does the perturbed projection. -/
theorem comp_perturb_proj_eq_rTensor_comp {ΔN : N →ₗ[R] N ⊗[R] C}
    (hp : ΔN ∘ₗ c.proj = c.proj.rTensor C ∘ₗ ΔM) :
    ΔN ∘ₗ (c.perturb δ hsq hU).proj = (c.perturb δ hsq hU).proj.rTensor C ∘ₗ ΔM := by
  rw [c.comp_perturb_proj_eq_comp δ hU hsq ΔM ΔN hp hh
    (c.comp_perturbationSeries_eq_rTensor_comp hU hδ hh), perturb_proj, LinearMap.rTensor_sub,
    LinearMap.rTensor_comp, LinearMap.rTensor_comp]

end RTensor

section Twisted

section Series

variable [AddCommMonoid C] [Module R C] {τ : C →ₗ[R] C} (hτ : τ ∘ₗ τ = LinearMap.id)
  {ΔM : M →ₗ[R] C ⊗[R] M} (hδ : ΔM ∘ₗ δ = TensorProduct.map τ δ ∘ₗ ΔM)
  (hh : ΔM ∘ₗ c.homotopy = TensorProduct.map τ c.homotopy ∘ₗ ΔM)
include hU hτ hδ hh

/-- If `δ` and the homotopy intertwine a map `ΔM : M → C ⊗ M`, such as a left coaction, up to the
same involution `τ` of `C`, so does the perturbation operator.  For `τ` a Koszul twist: if `δ` and
the homotopy are odd maps of left comodules, so is the perturbation operator. -/
theorem comp_perturbationSeries_eq_map_comp :
    ΔM ∘ₗ c.perturbationSeries δ = TensorProduct.map τ (c.perturbationSeries δ) ∘ₗ ΔM :=
  c.comp_perturbationSeries_eq_comp δ hU ΔM hδ hh <| by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← TensorProduct.map_comp, hτ,
      ← LinearMap.lTensor_def, Module.End.one_eq_id, ← LinearMap.lTensor_id,
      ← LinearMap.lTensor_add, LinearMap.map_comp_lTensor, ← Module.End.one_eq_id,
      ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, c.perturbationSeries_mul_one_add δ hU]

end Series

-- The perturbed inclusion and projection involve differences tensored with `C` on the left.
variable [AddCommGroup C] [Module R C] {τ : C →ₗ[R] C} (hτ : τ ∘ₗ τ = LinearMap.id)
  {ΔM : M →ₗ[R] C ⊗[R] M} (hδ : ΔM ∘ₗ δ = TensorProduct.map τ δ ∘ₗ ΔM)
  (hh : ΔM ∘ₗ c.homotopy = TensorProduct.map τ c.homotopy ∘ₗ ΔM)
include hU hτ hδ hh

/-- If `δ` and the homotopy intertwine maps `ΔM : M → C ⊗ M` up to the same involution `τ` of `C`
and the inclusion commutes with `ΔM` and `ΔN : N → C ⊗ N`, then the perturbed inclusion commutes
with them.  For `τ` a Koszul twist: the perturbed inclusion is a map of left comodules. -/
theorem comp_perturb_incl_eq_lTensor_comp {ΔN : N →ₗ[R] C ⊗[R] N}
    (hi : ΔM ∘ₗ c.incl = c.incl.lTensor C ∘ₗ ΔN) :
    ΔM ∘ₗ (c.perturb δ hsq hU).incl = (c.perturb δ hsq hU).incl.lTensor C ∘ₗ ΔN := by
  rw [c.comp_perturb_incl_eq_comp δ hU hsq ΔM ΔN hi hh
    (c.comp_perturbationSeries_eq_map_comp hU hτ hδ hh), perturb_incl, LinearMap.lTensor_sub,
    LinearMap.map_comp_lTensor, ← TensorProduct.map_comp, hτ, ← LinearMap.lTensor_def]

/-- If `δ` and the homotopy intertwine maps `ΔM : M → C ⊗ M` up to the same involution `τ` of `C`
and the projection commutes with `ΔM` and `ΔN : N → C ⊗ N`, then the perturbed projection commutes
with them.  For `τ` a Koszul twist: the perturbed projection is a map of left comodules. -/
theorem comp_perturb_proj_eq_lTensor_comp {ΔN : N →ₗ[R] C ⊗[R] N}
    (hp : ΔN ∘ₗ c.proj = c.proj.lTensor C ∘ₗ ΔM) :
    ΔN ∘ₗ (c.perturb δ hsq hU).proj = (c.perturb δ hsq hU).proj.lTensor C ∘ₗ ΔM := by
  rw [c.comp_perturb_proj_eq_comp δ hU hsq ΔM ΔN hp hh
    (c.comp_perturbationSeries_eq_map_comp hU hτ hδ hh), perturb_proj, LinearMap.lTensor_sub,
    ← TensorProduct.map_comp, hτ, LinearMap.lTensor_comp_map, ← LinearMap.lTensor_def]

end Twisted

end TensorProduct

end LinearSpecialContraction

end TauCeti
