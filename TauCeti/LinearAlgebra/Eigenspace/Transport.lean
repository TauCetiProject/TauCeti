/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Transporting eigenspaces along intertwining maps

If an injective linear map `e : U →ₗ[R] W` intertwines endomorphisms `f` of `U` and `g` of `W`,
then every generalized eigenspace of `f` is the preimage under `e` of the corresponding generalized
eigenspace of `g`. Mathlib's `Module.End.map_genEigenspace_le` gives only the inclusion of the
image; this file records this preimage description, the resulting description of the image as the
generalized eigenvectors of `g` in the range of `e`, and the eigenspace form for an intertwining
linear equivalence.

Over a domain, a surjective intertwining map into a torsion-free module carries each maximal
generalized eigenspace of `f` onto the corresponding one of `g`, provided `U` is the sum of the
maximal generalized eigenspaces of `f` (for instance, when `U` is finite-dimensional over an
algebraically closed field). In particular, taking maximal generalized eigenspaces commutes with
passing to quotients.

## Main results

* `TauCeti.genEigenspace_eq_comap_of_intertwine`: each generalized eigenspace of `f` is the
  preimage under an injective intertwining map of the corresponding one of `g`.
* `TauCeti.eigenspace_eq_comap_of_intertwine`: an intertwining linear equivalence identifies the
  eigenspaces of the two endomorphisms.
* `TauCeti.map_genEigenspace_eq_of_intertwine`: an injective intertwining map carries the
  generalized eigenspaces of `f` onto the generalized eigenvectors of `g` in its range.
* `TauCeti.map_maxGenEigenspace_eq_of_intertwine`: a surjective intertwining map carries the
  maximal generalized eigenspaces of `f` onto those of `g`.
-/

public section

namespace TauCeti

variable {R U W : Type*} [CommRing R] [AddCommGroup U] [Module R U] [AddCommGroup W]
  [Module R W]

/-- If an injective linear map `e` intertwines `f` and `g`, then each generalized eigenspace of
`f` is the preimage under `e` of the generalized eigenspace of `g` for the same eigenvalue and
exponent. -/
theorem genEigenspace_eq_comap_of_intertwine {e : U →ₗ[R] W} (he : Function.Injective e)
    {f : Module.End R U} {g : Module.End R W} (h : ∀ x, e (f x) = g (e x)) (μ : R) (k : ℕ∞) :
    f.genEigenspace μ k = (g.genEigenspace μ k).comap e := by
  -- `e` intertwines each power of `f - μ` with the same power of `g - μ`.
  have hμ (l : ℕ) (x : U) : e (((f - μ • 1) ^ l) x) = ((g - μ • 1) ^ l) (e x) := by
    simpa using congr($(Module.End.commute_pow_left_of_commute
      (f := e) (g := f - μ • 1) (g₂ := g - μ • 1) (by ext; simp [h]) l) x).symm
  ext x
  simp only [Module.End.mem_genEigenspace, Submodule.mem_comap, LinearMap.mem_ker, ← hμ,
    map_eq_zero_iff e he]

/-- An intertwining linear equivalence identifies the eigenspaces of the two endomorphisms. This
is the eigenspace form of `genEigenspace_eq_comap_of_intertwine` for an equivalence. -/
theorem eigenspace_eq_comap_of_intertwine {e : U ≃ₗ[R] W} {f : Module.End R U}
    {g : Module.End R W} (h : ∀ x, e (f x) = g (e x)) (μ : R) :
    f.eigenspace μ = (g.eigenspace μ).comap e.toLinearMap :=
  -- `Module.End.eigenspace f μ` is the reducible abbreviation of `f.genEigenspace μ 1`.
  genEigenspace_eq_comap_of_intertwine e.injective h μ 1

/-- An injective linear map intertwining `f` and `g` carries each generalized eigenspace of `f`
onto the generalized eigenvectors of `g` for the same eigenvalue and exponent that lie in its
range. -/
theorem map_genEigenspace_eq_of_intertwine {e : U →ₗ[R] W} (he : Function.Injective e)
    {f : Module.End R U} {g : Module.End R W} (h : ∀ x, e (f x) = g (e x)) (μ : R) (k : ℕ∞) :
    (f.genEigenspace μ k).map e = LinearMap.range e ⊓ g.genEigenspace μ k := by
  rw [genEigenspace_eq_comap_of_intertwine he h, Submodule.map_comap_eq]

/-- A surjective linear map intertwining `f` and `g` carries each maximal generalized eigenspace
of `f` onto the maximal generalized eigenspace of `g` for the same eigenvalue, provided the
maximal generalized eigenspaces of `f` span the source. -/
theorem map_maxGenEigenspace_eq_of_intertwine [IsDomain R] [Module.IsTorsionFree R W]
    {e : U →ₗ[R] W} (he : Function.Surjective e) {f : Module.End R U} {g : Module.End R W}
    (h : ∀ x, e (f x) = g (e x)) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) (μ : R) :
    (f.maxGenEigenspace μ).map e = g.maxGenEigenspace μ := by
  have hle : (fun ν => (f.maxGenEigenspace ν).map e) ≤ g.maxGenEigenspace := fun ν =>
    Module.End.map_genEigenspace_le e (LinearMap.ext fun x => (h x).symm) ν ⊤
  have htop : ⨆ ν, (f.maxGenEigenspace ν).map e = ⊤ := by
    rw [← Submodule.map_iSup, hf, Submodule.map_top, LinearMap.range_eq_top.mpr he]
  exact congrFun (((Module.End.independent_maxGenEigenspace g).le_iff_eq_of_iSup_eq_top
    htop).mp hle) μ

end TauCeti
