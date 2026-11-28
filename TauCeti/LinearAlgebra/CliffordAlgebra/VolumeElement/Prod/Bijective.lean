/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Bijective
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Bijectivity of graded tensor products of complex Clifford modules

When `ρ₁` and `ρ₂` are spinor representations (bijective onto `End_ℂ E` and `End_ℂ F`) and `W` is
finite-dimensional, the graded tensor product representation `CliffordAlgebra.complexProdTensor` is
also bijective onto `End_ℂ (E ⊗ F)`.

## Main results

* `CliffordAlgebra.complexProdTensor_bijective`: the graded tensor product of spinor modules is a
  spinor module.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **The graded tensor product of spinor modules is a spinor module.** When `W` is
finite-dimensional and `ρ₁`, `ρ₂` are bijective onto `End_ℂ E` and `End_ℂ F`, `complexProdTensor`
is bijective onto `End_ℂ (E ⊗ F)`. -/
theorem complexProdTensor_bijective [FiniteDimensional ℝ W]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    Function.Bijective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  have : Module.Finite ℂ E := Module.Finite.of_surjective_end ρ₁ hρ₁.surjective
  have : Module.Finite ℂ F := Module.Finite.of_surjective_end ρ₂ hρ₂.surjective
  rw [complexProdTensor_eq_comp, ← equivOfIsometry_toAlgHom, AlgHom.coe_comp]
  exact (AlgHom.cliffordProdTensor_bijective ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂
    hρ₁ hρ₂).comp
    (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).bijective

end CliffordAlgebra
