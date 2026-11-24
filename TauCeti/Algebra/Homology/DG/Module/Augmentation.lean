/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Abel

/-!
# Comparison maps between acyclic augmented complexes

Let `M` and `N` be `R`-modules with differentials `dM` and `dN` and augmentations
`εM : M → R` and `εN : N → R`, such that `εN` vanishes on boundaries, and let `f : M → N` commute
with the differentials and the augmentations. Suppose both augmented complexes are acyclic: a
cycle of augmentation zero is a boundary. Suppose also that `M` has a cycle `s` of augmentation
`1`. Then every relative cycle `(u, w)` of `f`, with `dM u = 0` and `f u = dN w`, is a relative
boundary `(dM u', f u' + dN w')` (`TauCeti.exists_differential_eq_and_add_eq_of_augmentation`).
When `f` is a degree-zero map of differential graded modules this is the acyclicity of the mapping
cone of `f`, written on elements, so it says that `f` is a quasi-isomorphism (compare
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`): two resolutions of `R` that are
compatible over `R` are quasi-isomorphic.

The proof is a chase on elements. The cycle `u` has augmentation `εN (dN w) = 0`, so it is a
boundary `dM v`. Then `z = w - f v` is a cycle, and `z - f (εN z • s)` is a cycle of augmentation
zero, hence a boundary `dN w'`, and `u' = v + εN z • s` works.

No grading and no square-zero condition is needed, so the statement is about bare linear maps. It
is the form in which Brown's semi-free resolution of a CW complex is compared with the chains on
its based path space, both being resolutions of the ground ring over the chains on the loop space.

The same element form of quasi-isomorphisms is stable under composition
(`TauCeti.exists_differential_eq_and_comp_add_eq`): if the relative cycles of `g : K → M` and of
`f : M → N` are relative boundaries, so are those of `f ∘ g`. This is how a resolution compared
quasi-isomorphically with the chains on the based path space becomes, through the augmentation of
those chains, a resolution of the ground ring.

## Main results

* `TauCeti.exists_differential_eq_and_add_eq_of_augmentation`: a map compatible with the
  differentials and the augmentations between two acyclic augmented complexes has relative cycles
  that are relative boundaries.
* `TauCeti.exists_differential_eq_and_comp_add_eq`: if the relative cycles of two composable maps
  of complexes are relative boundaries, so are those of their composite.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A comparison of acyclic augmented complexes is a quasi-isomorphism.** Let
`f : M → N` commute with the differentials `dM` and `dN` and with the augmentations `εM` and `εN`,
where `εN` vanishes on boundaries, and let `s` be a cycle of `M` of augmentation `1`. If in both
`M` and `N` a cycle of augmentation zero is a boundary, then every relative cycle `(u, w)` of `f`,
with `dM u = 0` and `f u = dN w`, is a relative boundary `(dM u', f u' + dN w')`. -/
theorem exists_differential_eq_and_add_eq_of_augmentation {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}
    {f : M →ₗ[R] N} {εM : M →ₗ[R] R} {εN : N →ₗ[R] R} (hf : ∀ x, f (dM x) = dN (f x))
    (hεf : ∀ x, εN (f x) = εM x) (hεN : ∀ x, εN (dN x) = 0) {s : M} (hs : dM s = 0)
    (hεs : εM s = 1) (hM : ∀ {u}, dM u = 0 → εM u = 0 → ∃ v, dM v = u)
    (hN : ∀ {w}, dN w = 0 → εN w = 0 → ∃ v, dN v = w) {u : M} {w : N} (hu : dM u = 0)
    (hw : f u = dN w) : ∃ u' w', dM u' = u ∧ f u' + dN w' = w := by
  -- The cycle `u` has augmentation zero, so it is a boundary `dM v`.
  obtain ⟨v, hv⟩ := hM hu (by rw [← hεf, hw, hεN])
  -- Then `z = w - f v` is a cycle; correct its augmentation by a multiple of `s`.
  set z := w - f v with hz
  have hdz : dN (z - f (εN z • s)) = 0 := by
    simp [hz, ← hf, hv, hs, ← hw]
  have hεz : εN (z - f (εN z • s)) = 0 := by
    simp [hεf, hεs]
  obtain ⟨w', hw'⟩ := hN hdz hεz
  refine ⟨v + εN z • s, w', ?_, ?_⟩
  · simp [hv, hs]
  · rw [hw', map_add, hz]
    abel


/-- **Relative cycles compose.** Let `g : K → M` and `f : M → N` commute with the differentials.
If every relative cycle of `g` and every relative cycle of `f` is a relative boundary, then so is
every relative cycle `(u, w)` of `f ∘ g`, with `dK u = 0` and `f (g u) = dN w`: when `g` and `f`
are quasi-isomorphisms, so is their composite. -/
theorem exists_differential_eq_and_comp_add_eq {K : Type*} [AddCommGroup K] [Module R K]
    {dK : K →ₗ[R] K} {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {g : K →ₗ[R] M} {f : M →ₗ[R] N}
    (hg : ∀ x, g (dK x) = dM (g x)) (hf : ∀ x, f (dM x) = dN (f x))
    (hgrel : ∀ u w, dK u = 0 → g u = dM w → ∃ u' w', dK u' = u ∧ g u' + dM w' = w)
    (hfrel : ∀ u w, dM u = 0 → f u = dN w → ∃ u' w', dM u' = u ∧ f u' + dN w' = w)
    (u : K) (w : N) (hu : dK u = 0) (hw : f (g u) = dN w) :
    ∃ u' w', dK u' = u ∧ f (g u') + dN w' = w := by
  -- The cycle `g u` is a relative cycle of `f`: it bounds some `y` up to `f`.
  obtain ⟨y, v, hy, hv⟩ := hfrel (g u) w (by rw [← hg, hu, map_zero]) hw
  -- Then `(u, y)` is a relative cycle of `g`.
  obtain ⟨u', v', hu', hv'⟩ := hgrel u y hu hy.symm
  refine ⟨u', f v' + v, hu', ?_⟩
  rw [map_add, ← hf, ← add_assoc, ← map_add, hv', hv]

end TauCeti
