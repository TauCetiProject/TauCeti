/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Ore
public import TauCeti.RingTheory.OreLocalization.Ring

/-!
# Based charts in the skew field of fractions of a based quantum torus

Let `R` be a commutative domain and `L` a torsion-free abelian group. The based quantum torus
`TauCeti.QuantumTorus R L u Λ` is then a domain satisfying the Ore condition, so Mathlib's
`OreLocalization (QuantumTorus R L u Λ)⁰ (QuantumTorus R L u Λ)` is a division ring, its skew
field of fractions (see `TauCeti.Algebra.MonoidAlgebra.Twisted.Ore`). The numerator map is an
injective `R`-algebra map, so it is a faithful based chart `TauCeti.BasedChart.oreLocalization u Λ`
with values in a division ring.

This chart is initial among based charts in division rings: every based chart `M` in a division
`R`-algebra `D` is the transport of `TauCeti.BasedChart.oreLocalization u Λ` along a unique
`R`-algebra map `M.liftOreLocalization` from the skew field of fractions to `D`
(`TauCeti.BasedChart.map_liftOreLocalization`, `TauCeti.BasedChart.eq_liftOreLocalization`).

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §4.
-/

public section

open nonZeroDivisors OreLocalization

namespace TauCeti.BasedChart

variable {R L D : Type*} [CommRing R] [IsDomain R] [AddCommGroup L] [Module.IsTorsionFree ℤ L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L} [DivisionRing D] [Algebra R D]

variable (u Λ) in
/-- The based chart of a based quantum torus in its skew field of fractions, given by the
numerator map. -/
noncomputable def oreLocalization :
    BasedChart u Λ (OreLocalization (QuantumTorus R L u Λ)⁰ (QuantumTorus R L u Λ)) :=
  ofInjective (numeratorAlgHom R)
    (numeratorAlgHom_injective fun _ h ↦ (mem_nonZeroDivisors_iff'.1 h).left)

@[simp]
theorem val_oreLocalization_monomial (a : L) :
    ((oreLocalization u Λ).monomial a :
        OreLocalization (QuantumTorus R L u Λ)⁰ (QuantumTorus R L u Λ)) =
      numeratorHom (QuantumTorus.monomial u Λ a) := by
  simp [oreLocalization]

@[simp]
theorem eval_oreLocalization :
    (oreLocalization u Λ).eval = numeratorAlgHom R (S := (QuantumTorus R L u Λ)⁰) :=
  eval_ofInjective ..

/-- The `R`-algebra map from the skew field of fractions of the based quantum torus to a division
ring `D` extending the chart map of a based chart `M` in `D`. -/
noncomputable def liftOreLocalization (M : BasedChart u Λ D) :
    OreLocalization (QuantumTorus R L u Λ)⁰ (QuantumTorus R L u Λ) →ₐ[R] D :=
  liftAlgHom M.eval M.eval_injective

@[simp]
theorem liftOreLocalization_apply (M : BasedChart u Λ D) (x : QuantumTorus R L u Λ)
    (s : (QuantumTorus R L u Λ)⁰) : M.liftOreLocalization (x /ₒ s) = (M.eval s)⁻¹ * M.eval x :=
  liftAlgHom_apply ..

theorem liftOreLocalization_numeratorHom (M : BasedChart u Λ D) (x : QuantumTorus R L u Λ) :
    M.liftOreLocalization (numeratorHom x) = M.eval x :=
  liftAlgHom_numeratorHom ..

@[simp]
theorem liftOreLocalization_comp_numeratorAlgHom (M : BasedChart u Λ D) :
    M.liftOreLocalization.comp (numeratorAlgHom R) = M.eval :=
  liftAlgHom_comp_numeratorAlgHom ..

/-- Every based chart in a division ring is the transport of the chart in the skew field of
fractions along `TauCeti.BasedChart.liftOreLocalization`. -/
@[simp]
theorem map_liftOreLocalization (M : BasedChart u Λ D) :
    (oreLocalization u Λ).map M.liftOreLocalization (RingHom.injective _) = M := by
  simp only [oreLocalization, map_ofInjective, liftOreLocalization_comp_numeratorAlgHom,
    ofInjective_eval]

/-- An `R`-algebra map out of the skew field of fractions that matches the monomials of a based
chart `M` is `M.liftOreLocalization`. -/
theorem eq_liftOreLocalization (M : BasedChart u Λ D)
    {φ : OreLocalization (QuantumTorus R L u Λ)⁰ (QuantumTorus R L u Λ) →ₐ[R] D}
    (h : ∀ a, φ ((oreLocalization u Λ).monomial a) = M.monomial a) :
    φ = M.liftOreLocalization := by
  have key : φ.comp (numeratorAlgHom R) = M.eval :=
    QuantumTorus.algHom_ext fun a ↦ by simpa using h a
  exact liftAlgHom_unique _ _ φ fun x ↦ by simpa using AlgHom.congr_fun key x

end TauCeti.BasedChart
