/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Eigenspace

/-!
# Half-spin dimension of the orthogonal sum of two negative planes

For an oriented plane `V` (`dim_ℝ V = 2`, `Q₁ v = -‖v‖²`) and a second plane `W` (`dim_ℝ W = 2`,
`Q₂ w = -‖w‖²`) with spinor modules `E` and `F` (`dim_ℂ E = dim_ℂ F = 2`), the graded tensor
product `E ⊗ F` is a `4`-dimensional spinor module of `V ⊕ W` (`WithLp 2 (V × W)`), and for any
orientation `o` of `V ⊕ W` each `±1`-eigenspace of the product chirality `complexVolume Q o` has
complex dimension `2`.
-/

public section

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
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]

/-- **Two-plane half-spin check**: for two negative planes `V` and `W` (`n = 2`, `m = 2`) with `V`
oriented by `o₁`, spinor modules `E` and `F`, and any orientation `o` of `V ⊕ W`, each
`±1`-eigenspace of `complexVolume Q o` on `E ⊗ F` has complex dimension `2`. -/
theorem finrank_eigenspace_complexProdTensor_two_two (hn2 : n = 2) (hm2 : m = 2)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂)
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) = 2 := by
  subst hn2 hm2
  simpa using finrank_eigenspace_complexProdTensor_of_bijective hQ o₁ hQ₁ hn hQ₂ h₁ h₂
    (by decide) o hμ

end CliffordAlgebra
