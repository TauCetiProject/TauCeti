/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear
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
* `TauCeti.LinearSpecialContraction.perturbedDifferential_comp_perturbedDifferential`: the
  perturbed differential of the retract squares to the square of `dN`.
* `TauCeti.LinearSpecialContraction.perturb_proj_comp_one_add_mul`: the perturbed projection
  satisfies `p' (1 + δ h) = p`; with `TauCeti.LinearSpecialContraction.perturb_proj_comp_homotopy`
  and `TauCeti.LinearSpecialContraction.perturb_proj_comp_incl`, these are the identities making
  `p'` a coalgebra morphism in the tensor trick.

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
  set u := δ * c.homotopy with hu
  have hgeom : (1 + u) * ∑ j ∈ Finset.range k, (-u) ^ j = 1 - (-u) ^ k := by
    simpa only [sub_neg_eq_add] using mul_neg_geom_sum (-u) k
  have hk : ((-u) ^ k) (δ z) = 0 := by
    rw [neg_pow, Module.End.mul_apply, hz, map_zero]
  have h1 : (1 + u) ((∑ j ∈ Finset.range k, (-u) ^ j) (δ z)) = δ z := by
    rw [← Module.End.mul_apply, hgeom, LinearMap.sub_apply, Module.End.one_apply, hk, sub_zero]
  calc c.perturbationSeries δ z
      = Ring.inverse (1 + u) ((1 + u) ((∑ j ∈ Finset.range k, (-u) ^ j) (δ z))) := by
        rw [h1, perturbationSeries_def, Module.End.mul_apply]
    _ = (∑ j ∈ Finset.range k, (-u) ^ j) (δ z) := by
        rw [← Module.End.mul_apply, Ring.inverse_mul_cancel _ hU, Module.End.one_apply]
    _ = ∑ j ∈ Finset.range k, ((-u) ^ j) (δ z) := LinearMap.sum_apply _ _ _

/-- The perturbation operator satisfies the Maurer--Cartan-type identity
`dM X + X dM + X i p X = 0`; this single identity drives every equation of the basic
perturbation lemma. -/
theorem perturbationSeries_maurerCartan (hδ : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) :
    dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
      c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ = 0 := by
  set X := c.perturbationSeries δ with hX
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

/-- The perturbed differential of the retract squares to the square of `dN`; in particular it is
a differential whenever `dN` is. -/
theorem perturbedDifferential_comp_perturbedDifferential :
    c.perturbedDifferential δ ∘ₗ c.perturbedDifferential δ = dN ∘ₗ dN := by
  have h1 : c.proj ∘ₗ (dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
      c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ) ∘ₗ c.incl = 0 := by
    rw [c.perturbationSeries_maurerCartan δ hU hδ, LinearMap.zero_comp, LinearMap.comp_zero]
  rw [perturbedDifferential_def]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_assoc, ← c.dM_comp_incl, ← c.proj_comp_dM_assoc,
    c.incl_comp_proj_assoc] at h1 ⊢
  linear_combination (norm := abel) h1

/-- If `dM` squares to zero, so does the perturbed differential of the retract. -/
theorem perturbedDifferential_comp_perturbedDifferential_eq_zero (h : dM ∘ₗ dM = 0) :
    c.perturbedDifferential δ ∘ₗ c.perturbedDifferential δ = 0 := by
  rw [c.perturbedDifferential_comp_perturbedDifferential δ hδ hU, c.dN_comp_dN_eq_zero h]

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
      rw [c.perturbationSeries_maurerCartan δ hU hδ, LinearMap.zero_comp, LinearMap.comp_zero]
    rw [perturbedDifferential_def]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp,
      LinearMap.comp_assoc, ← c.dM_comp_incl, c.incl_comp_proj_assoc,
      c.comp_homotopy_comp_perturbationSeries_assoc δ hU] at h1 ⊢
    linear_combination (norm := abel) h1
  proj_comp_dM := by
    have h1 : c.proj ∘ₗ (dM ∘ₗ c.perturbationSeries δ + c.perturbationSeries δ ∘ₗ dM +
        c.perturbationSeries δ ∘ₗ c.incl ∘ₗ c.proj ∘ₗ c.perturbationSeries δ) ∘ₗ
          c.homotopy = 0 := by
      rw [c.perturbationSeries_maurerCartan δ hU hδ, LinearMap.zero_comp, LinearMap.comp_zero]
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
      rw [c.perturbationSeries_maurerCartan δ hU hδ, LinearMap.zero_comp, LinearMap.comp_zero]
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

end LinearSpecialContraction

end TauCeti
