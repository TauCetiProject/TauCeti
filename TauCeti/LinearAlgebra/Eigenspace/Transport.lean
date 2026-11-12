/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Transporting eigenspaces along intertwining maps

If a linear equivalence `e : U ≃ₗ[R] W` intertwines endomorphisms `f` of `U` and `g` of `W`,
then every eigenspace of `f` is the preimage under `e` of the corresponding eigenspace of `g`.
Mathlib's `Module.End.map_genEigenspace_le` gives only the inclusion of the image; this file
records the equality available for an equivalence.

Over a domain, a surjective intertwining map into a torsion-free module carries each maximal
generalized eigenspace of `f` onto the corresponding one of `g`, provided `U` is the sum of the
maximal generalized eigenspaces of `f` (for instance, when `U` is finite-dimensional over an
algebraically closed field). In particular, taking generalized eigenspaces is exact on quotients.

## Main results

* `TauCeti.eigenspace_eq_comap_of_intertwine`: an intertwining linear equivalence identifies the
  eigenspaces of the two endomorphisms.
* `TauCeti.map_maxGenEigenspace_eq_of_intertwine`: a surjective intertwining map carries the
  maximal generalized eigenspaces of `f` onto those of `g`.
-/

public section

namespace TauCeti

variable {R U W : Type*} [CommRing R] [AddCommGroup U] [Module R U] [AddCommGroup W]
  [Module R W]

/-- An intertwining linear equivalence identifies the eigenspaces of the two endomorphisms. -/
theorem eigenspace_eq_comap_of_intertwine {e : U ≃ₗ[R] W} {f : U →ₗ[R] U} {g : W →ₗ[R] W}
    (h : ∀ x, e (f x) = g (e x)) (μ : R) :
    Module.End.eigenspace f μ = (Module.End.eigenspace g μ).comap e.toLinearMap := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap]
  constructor
  · intro hx
    calc
      g (e x) = e (f x) := (h x).symm
      _ = e (μ • x) := congrArg e hx
      _ = μ • e x := map_smul e μ x
  · intro hx
    apply e.injective
    calc
      e (f x) = g (e x) := h x
      _ = μ • e x := hx
      _ = e (μ • x) := (map_smul e μ x).symm

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
