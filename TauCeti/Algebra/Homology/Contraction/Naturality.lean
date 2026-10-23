/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Perturbation

/-!
# Naturality of the basic perturbation lemma

Maps between two special contractions that commute with the inclusions, projections and
homotopies continue to do so after compatible perturbations. The map on the retracts intertwines
the perturbed differentials. These identities allow homological transfer to preserve maps that
respect chosen contractions, rather than merely producing unrelated structures on the retracts.

The perturbations need only make `1 + δ h` invertible. No filtration, nilpotence or grading
hypothesis is needed for these naturality identities.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

namespace TauCeti.LinearSpecialContraction

universe uR uM uN uM' uN'

variable {R : Type uR} [Semiring R]
  {M : Type uM} {N : Type uN} {M' : Type uM'} {N' : Type uN'}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  {dM : Module.End R M} {dN : Module.End R N}
  {dM' : Module.End R M'} {dN' : Module.End R N'}
  (c : LinearSpecialContraction dM dN) (c' : LinearSpecialContraction dM' dN')
  (f : M →ₗ[R] M') (g : N →ₗ[R] N')
  {δ : Module.End R M} {δ' : Module.End R M'}

/-- A map commuting with homotopies and perturbations intertwines their perturbation operators.
Only the two invertibility hypotheses are required, not the perturbation-square equations. -/
theorem perturbationSeries_naturality
    (hh : f ∘ₗ c.homotopy = c'.homotopy ∘ₗ f)
    (hδ : f ∘ₗ δ = δ' ∘ₗ f)
    (hU : IsUnit (1 + δ * c.homotopy))
    (hU' : IsUnit (1 + δ' * c'.homotopy)) :
    f ∘ₗ c.perturbationSeries δ = c'.perturbationSeries δ' ∘ₗ f := by
  have hT : (1 + δ' * c'.homotopy) ∘ₗ f = f ∘ₗ (1 + δ * c.homotopy) := by
    simp only [Module.End.mul_eq_comp, LinearMap.add_comp, LinearMap.comp_add,
      Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
    have hh' := hh
    have hδ' := hδ
    simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hh' hδ'
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hh', hδ']
  have hinj := ((Module.End.isUnit_iff _).mp hU').1
  ext x
  apply hinj
  have hTX := congrArg (fun a ↦ a x) (c.one_add_mul_perturbationSeries δ hU)
  have hTX' := congrArg (fun a ↦ a (f x)) (c'.one_add_mul_perturbationSeries δ' hU')
  have hTf := LinearMap.congr_fun hT (c.perturbationSeries δ x)
  have hδf := LinearMap.congr_fun hδ x
  simpa only [LinearMap.comp_apply, Module.End.mul_apply] using hTf.trans
    ((congrArg f hTX).trans (hδf.trans hTX'.symm))

/-- The induced map on retracts commutes with the perturbed differentials. Compatibility with
the old retract differential is explicit; no chain-map assumption on the large complexes is
needed for this identity. -/
theorem perturbedDifferential_naturality
    (hi : f ∘ₗ c.incl = c'.incl ∘ₗ g)
    (hp : g ∘ₗ c.proj = c'.proj ∘ₗ f)
    (hh : f ∘ₗ c.homotopy = c'.homotopy ∘ₗ f)
    (hd : g ∘ₗ dN = dN' ∘ₗ g)
    (hδ : f ∘ₗ δ = δ' ∘ₗ f)
    (hU : IsUnit (1 + δ * c.homotopy))
    (hU' : IsUnit (1 + δ' * c'.homotopy)) :
    g ∘ₗ c.perturbedDifferential δ = c'.perturbedDifferential δ' ∘ₗ g := by
  have hX := c.perturbationSeries_naturality c' f hh hδ hU hU'
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hi hp hd hX
  ext x
  simp [perturbedDifferential_def, hi, hp, hd, hX]

section Perturb

variable (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM)
  (hsq' : (dM' + δ') ∘ₗ (dM' + δ') = dM' ∘ₗ dM')
  (hU : IsUnit (1 + δ * c.homotopy))
  (hU' : IsUnit (1 + δ' * c'.homotopy))

/-- Compatible maps commute with the inclusions after perturbation. -/
theorem perturb_incl_naturality
    (hi : f ∘ₗ c.incl = c'.incl ∘ₗ g)
    (hh : f ∘ₗ c.homotopy = c'.homotopy ∘ₗ f)
    (hδ : f ∘ₗ δ = δ' ∘ₗ f) :
    f ∘ₗ (c.perturb δ hsq hU).incl = (c'.perturb δ' hsq' hU').incl ∘ₗ g := by
  have hX := c.perturbationSeries_naturality c' f hh hδ hU hU'
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hi hh hX
  ext x
  simp [hi, hh, hX]

/-- Compatible maps commute with the projections after perturbation. -/
theorem perturb_proj_naturality
    (hp : g ∘ₗ c.proj = c'.proj ∘ₗ f)
    (hh : f ∘ₗ c.homotopy = c'.homotopy ∘ₗ f)
    (hδ : f ∘ₗ δ = δ' ∘ₗ f) :
    g ∘ₗ (c.perturb δ hsq hU).proj = (c'.perturb δ' hsq' hU').proj ∘ₗ f := by
  have hX := c.perturbationSeries_naturality c' f hh hδ hU hU'
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hp hh hX
  ext x
  simp [hp, hh, hX]

/-- Compatible maps commute with the homotopies after perturbation. -/
theorem perturb_homotopy_naturality
    (hh : f ∘ₗ c.homotopy = c'.homotopy ∘ₗ f)
    (hδ : f ∘ₗ δ = δ' ∘ₗ f) :
    f ∘ₗ (c.perturb δ hsq hU).homotopy =
      (c'.perturb δ' hsq' hU').homotopy ∘ₗ f := by
  have hX := c.perturbationSeries_naturality c' f hh hδ hU hU'
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hh hX
  ext x
  simp [hh, hX]

end Perturb

end TauCeti.LinearSpecialContraction
