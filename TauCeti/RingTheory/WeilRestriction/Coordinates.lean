/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Coefficients of the universal point of a Weil restriction

For a finite projective algebra `B` over `A`, the coefficients of the universal point, extracted
by `A`-linear functionals on `B`, generate the coordinate algebra of the Weil restriction.
The construction does not choose a basis. Its compatibility with evaluation allows the point
topology of a Weil restriction to be compared with the module topology on `B`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, §1.5.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Exercise 2.4.
-/

public noncomputable section

open TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [Algebra.FinitePresentation B C]

/-- The coefficient of the universal point at `c`, extracted by the linear functional `φ`
on the coefficient algebra `B`. -/
def universalCoefficient (φ : Module.Dual A B) (c : C) : WeilRestriction A B C :=
  LinearMap.tensorComponent φ
    (TensorProduct.comm A B (WeilRestriction A B C) (universalPoint A B C c))

/-- Evaluating a universal coefficient is the same as extracting the corresponding coefficient
of the classified point. -/
theorem map_universalCoefficient {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) (φ : Module.Dual A B) (c : C) :
    g (universalCoefficient φ c) = LinearMap.tensorComponent φ
      (TensorProduct.comm A B T (homEquiv A B C T g c)) := by
  simp only [universalCoefficient, homEquiv_apply, AlgHom.comp_apply]
  -- The algebra tensor map is `B`-linear, whereas contraction uses `A`-linear tensor maps.
  -- Pure tensors avoid identifying these differently bundled maps by definitional equality.
  induction universalPoint A B C c using TensorProduct.inductionOn with
  | tmul b w => simp
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The coefficients of the universal point generate the Weil restriction as an `A`-algebra.
All linear functionals may be used, so no basis or projective splitting is part of the statement. -/
theorem adjoin_range_universalCoefficient :
    Algebra.adjoin A (Set.range fun p : Module.Dual A B × C ↦
      universalCoefficient p.1 p.2) = ⊤ := by
  classical
  let S := Algebra.adjoin A (Set.range fun p : Module.Dual A B × C ↦
    universalCoefficient p.1 p.2)
  suffices (AlgHom.id A (WeilRestriction A B C)).range ≤ S by simpa using this
  apply (range_le_iff_range_homEquiv_le).2
  rintro _ ⟨c, rfl⟩
  obtain ⟨n, p, s, -, -, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  let b (i : Fin n) := p (Pi.single i 1)
  let φ (i : Fin n) : Module.Dual A B := LinearMap.proj i ∘ₗ s
  have hb (x : B) : ∑ i, φ i x • b i = x := by
    simpa only [φ, b, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.id_apply,
      ← map_smul, ← map_sum, ← pi_eq_sum_univ'] using LinearMap.congr_fun hs x
  have expand (z : B ⊗[A] WeilRestriction A B C) :
      ∑ i, b i ⊗ₜ[A] LinearMap.tensorComponent (φ i)
        (TensorProduct.comm A B _ z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simpa only [TensorProduct.comm_tmul, LinearMap.tensorComponent_tmul, sum_tmul,
        smul_tmul', tmul_smul] using congrArg (fun x : B ↦ x ⊗ₜ[A] y) (hb x)
    | add x y hx hy => simp [tmul_add, Finset.sum_add_distrib, hx, hy]
  have hc (i : Fin n) : universalCoefficient (φ i) c ∈ S :=
    Algebra.subset_adjoin ⟨(φ i, c), rfl⟩
  refine ⟨∑ i, b i ⊗ₜ[A] (⟨universalCoefficient (φ i) c, hc i⟩ : S), ?_⟩
  simpa [homEquiv_apply, universalCoefficient] using expand (universalPoint A B C c)

end TauCeti.Algebra.WeilRestriction
