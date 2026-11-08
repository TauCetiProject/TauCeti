/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Hom
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.MetricSpace.Bounded
import TauCeti.Algebra.Module.ZLattice.LiftBaseChange

/-!
# Elements of a finitely generated abelian group with bounded real pairings

Let `H` be a finitely generated abelian group and `θ i : H →+ ℝ` a family of real-valued
homomorphisms spanning the real vector space `H →+ ℝ`. Then only finitely many `A : H` have all
pairings `θ i A` in a bounded window: `{A | ∀ i, |θ i A| ≤ C i}` is finite
(`TauCeti.finite_setOf_forall_abs_apply_le`). Torsion elements are not lost: each window contains
whole cosets of the finite torsion subgroup.

The spanning hypothesis cannot be weakened to joint injectivity modulo torsion: for
`H = ℤ²` the single homomorphism `(a, b) ↦ a + b √2` vanishes only at zero, yet takes infinitely
many values in `[-1, 1]`.

The intended application is to pseudoholomorphic curves. There `H` is the integral homology
`H₂(X; ℤ)` of a closed manifold and the `θ i` are the pairings with a basis of closed two-forms,
which span `H²(X; ℝ) = Hom(H₂(X; ℤ), ℝ)` by de Rham's theorem. The classes `A` with `σ A ≤ a`
and `|θ i A| ≤ K i σ A` form a finite set
(`TauCeti.finite_setOf_apply_le_and_forall_abs_apply_le_mul`). The integral `∫_C u^* θ` over a
curve is bounded by the comass of `θ` times the symplectic area of the curve
(`TauCeti.abs_integralTopForm_mpullback_le`). Concluding that below an area cutoff only finitely
many homology classes carry pseudoholomorphic curves also requires identifying `∫_C u^* θ` with
the pairing of `[θ]` with the class of the curve. That de Rham comparison is not provided here.

## Implementation notes

Real-valued homomorphisms on `H` are the real linear functionals on `ℝ ⊗[ℤ] H`, a
finite-dimensional space, so finitely many of the `θ i` already span. Evaluation at these has
injective real extension `ℝ ⊗[ℤ] H → ℝᵇ`, and a window lies in the preimage of a bounded box, so
it is finite by `LinearMap.finite_preimage_of_injective_liftBaseChange`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §1.
-/
public section

open Set

namespace TauCeti

variable {H ι : Type*} [AddCommGroup H] [AddGroup.FG H]

/-- **Bounded real pairings cut out a finite set.** In a finitely generated abelian group `H`, if
the real-valued homomorphisms `θ i` span `H →+ ℝ`, then only finitely many elements have all
pairings `|θ i A| ≤ C i`. -/
theorem finite_setOf_forall_abs_apply_le (θ : ι → H →+ ℝ)
    (hθ : Submodule.span ℝ (range θ) = ⊤) (C : ι → ℝ) :
    {A : H | ∀ i, |θ i A| ≤ C i}.Finite := by
  classical
  -- Real-valued homomorphisms on `H` are the real linear functionals on `ℝ ⊗[ℤ] H`.
  let Ψ : (H →+ ℝ) ≃ₗ[ℝ] Module.Dual ℝ (TensorProduct ℤ ℝ H) :=
    (addMonoidHomLequivInt ℝ).trans (LinearMap.liftBaseChangeEquiv ℝ)
  have : FiniteDimensional ℝ (H →+ ℝ) := Ψ.symm.finiteDimensional
  -- A finite linearly independent subfamily `b` of the `θ i` still spans.
  obtain ⟨b, hbθ, hbspan, hb⟩ := exists_linearIndependent ℝ (range θ)
  have : Fintype b := hb.setFinite.fintype
  choose c hc using fun f : b ↦ hbθ f.2
  -- Evaluation at `b` has injective real extension, since `b` spans the dual of `ℝ ⊗[ℤ] H`.
  let l : H →ₗ[ℤ] b → ℝ := LinearMap.pi fun f ↦ (f : H →+ ℝ).toIntLinearMap
  have hl : Function.Injective (l.liftBaseChange ℝ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦
      (Module.forall_dual_apply_eq_zero_iff ℝ x).1 fun φ ↦ ?_
    have hΨ (f : b) (y : TensorProduct ℤ ℝ H) : Ψ f y = l.liftBaseChange ℝ y f := by
      induction y using TensorProduct.inductionOn <;> simp_all [Ψ, l]
    have hx' (g : H →+ ℝ) (hg : g ∈ Submodule.span ℝ b) : Ψ g x = 0 := by
      induction hg using Submodule.span_induction with
      | mem f hf => simpa [hx] using hΨ ⟨f, hf⟩ x
      | zero => simp
      | add => simp_all
      | smul => simp_all
    simpa using hx' (Ψ.symm φ) (by simp [hbspan, hθ])
  refine (l.finite_preimage_of_injective_liftBaseChange hl
    (Bornology.IsBounded.pi fun f ↦ Metric.isBounded_Icc (-C (c f)) (C (c f)))).subset
    fun A hA ↦ ?_
  simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_Icc]
  intro f
  simpa [l, hc] using abs_le.1 (hA (c f))

/-- **Finitely many classes below an area cutoff.** In a finitely generated abelian group `H`,
let the real-valued homomorphisms `θ i` span `H →+ ℝ`, and let `σ : H →+ ℝ` and `K i ≥ 0`. Then
only finitely many `A` satisfy `σ A ≤ a` and `|θ i A| ≤ K i * σ A` for all `i`. These are the
bounds expected from the area `σ A` of a pseudoholomorphic curve in the class `A` on its pairings
with closed two-forms of comass at most `K i`, once integrals over curves are identified with
pairings of homology classes. -/
theorem finite_setOf_apply_le_and_forall_abs_apply_le_mul (θ : ι → H →+ ℝ)
    (hθ : Submodule.span ℝ (range θ) = ⊤) (σ : H →+ ℝ) {K : ι → ℝ} (hK : ∀ i, 0 ≤ K i)
    (a : ℝ) : {A : H | σ A ≤ a ∧ ∀ i, |θ i A| ≤ K i * σ A}.Finite :=
  (finite_setOf_forall_abs_apply_le θ hθ fun i ↦ K i * a).subset fun _ hA i ↦
    (hA.2 i).trans (mul_le_mul_of_nonneg_left hA.1 (hK i))

end TauCeti
