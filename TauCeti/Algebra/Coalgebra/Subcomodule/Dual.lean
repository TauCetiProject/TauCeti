/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Dual
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Submodule
import TauCeti.LinearAlgebra.Dual.Annihilator

/-!
# Subcomodules of the dual comodule

Let `M` be a finite-dimensional right comodule over a commutative Hopf algebra `H` over a field
`k`, and let `M*` carry the dual comodule structure `TauCeti.Comodule.dual`. Annihilators
exchange the subcomodules of `M` and of `M*`: the annihilator `N^⊥ ≤ M*` of a subcomodule
`N ≤ M` is a subcomodule, and so is the common kernel `W° ≤ M` of a subcomodule `W ≤ M*`. These
constructions are mutually inverse, so they give an order-reversing bijection between the two
lattices of subcomodules (`TauCeti.Subcomodule.dualAnnihilatorOrderIso`). Thus, for example, a
simple subcomodule of `M` contained in every nonzero subcomodule corresponds to a maximal proper
subcomodule of `M*` containing every proper subcomodule.

Both directions compare matrix coefficients of `M` and `M*` through the equation
`c(ev_m, φ) = S(c(φ, m))` (`TauCeti.Comodule.matrixCoefficient_dual_eval`). For the common
kernel the antipode `S` has to be cancelled, which uses that it is an involution of the
commutative Hopf algebra `H`.

## Main declarations

* `TauCeti.Subcomodule.dualAnnihilator`: the annihilator of a subcomodule, as a subcomodule of
  the dual.
* `TauCeti.Subcomodule.dualCoannihilator`: the common kernel of a subcomodule of the dual.
* `TauCeti.Subcomodule.dualCoannihilator_dualAnnihilator` and
  `TauCeti.Subcomodule.dualAnnihilator_dualCoannihilator`: the two constructions are inverse.
* `TauCeti.Subcomodule.dualAnnihilatorOrderIso`: the order-reversing bijection between
  subcomodules of `M` and of its dual.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Subcomodule

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

attribute [local instance] Comodule.dual

section Ring

variable [Ring H] [HopfAlgebra k H] [Comodule k H M]

/-- **The annihilator of a subcomodule.** The functionals vanishing on a subcomodule `N ≤ M`
form a subcomodule `N^⊥` of the dual comodule. -/
noncomputable def dualAnnihilator (N : Subcomodule k H M) :
    Subcomodule k H (Module.Dual k M) :=
  ofSubmodule N.toSubmodule.dualAnnihilator fun φ hφ ↦ by
    refine (Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero _ φ).mpr fun Ψ ↦ ?_
    -- In finite dimension, the functionals on `M*` vanishing on `N^⊥` are evaluations at `N`.
    have hΨ := N.toSubmodule.dualAnnihilator.comp_mkQ_mem_dualAnnihilator Ψ
    rw [Subspace.dualAnnihilator_dualAnnihilator_eq, Module.mapEvalEquiv_apply] at hΨ
    obtain ⟨m, hm, hmΨ⟩ := hΨ
    rw [← hmΨ, Comodule.matrixCoefficient_dual_eval,
      N.toSubmodule.matrixCoefficient_eq_zero_of_mem_dualAnnihilator (N.coact_mem hm) hφ, map_zero]

@[simp]
theorem dualAnnihilator_toSubmodule (N : Subcomodule k H M) :
    N.dualAnnihilator.toSubmodule = N.toSubmodule.dualAnnihilator :=
  (rfl)

@[simp]
theorem mem_dualAnnihilator {N : Subcomodule k H M} {φ : Module.Dual k M} :
    φ ∈ N.dualAnnihilator ↔ ∀ m ∈ N, φ m = 0 := by
  rw [← mem_toSubmodule, dualAnnihilator_toSubmodule, Submodule.mem_dualAnnihilator]
  simp only [mem_toSubmodule]

/-- Taking annihilators reverses inclusions of subcomodules and reflects them. -/
theorem dualAnnihilator_le_dualAnnihilator_iff {N P : Subcomodule k H M} :
    N.dualAnnihilator ≤ P.dualAnnihilator ↔ P ≤ N := by
  rw [← toSubmodule_le_toSubmodule, ← toSubmodule_le_toSubmodule, dualAnnihilator_toSubmodule,
    dualAnnihilator_toSubmodule, Subspace.dualAnnihilator_le_dualAnnihilator_iff]

theorem dualAnnihilator_injective :
    Function.Injective (dualAnnihilator (k := k) (H := H) (M := M)) := fun _ _ h ↦
  le_antisymm (dualAnnihilator_le_dualAnnihilator_iff.mp h.ge)
    (dualAnnihilator_le_dualAnnihilator_iff.mp h.le)

@[simp]
theorem dualAnnihilator_bot : (⊥ : Subcomodule k H M).dualAnnihilator = ⊤ :=
  ext fun φ ↦ by simp [mem_bot]

@[simp]
theorem dualAnnihilator_top : (⊤ : Subcomodule k H M).dualAnnihilator = ⊥ :=
  ext fun φ ↦ by simp [mem_bot, mem_top, LinearMap.ext_iff]

@[simp]
theorem dualAnnihilator_eq_top_iff {N : Subcomodule k H M} : N.dualAnnihilator = ⊤ ↔ N = ⊥ := by
  rw [← dualAnnihilator_bot, dualAnnihilator_injective.eq_iff]

@[simp]
theorem dualAnnihilator_eq_bot_iff {N : Subcomodule k H M} : N.dualAnnihilator = ⊥ ↔ N = ⊤ := by
  rw [← dualAnnihilator_top, dualAnnihilator_injective.eq_iff]

end Ring

variable [CommRing H] [HopfAlgebra k H] [Comodule k H M]

/-- **The common kernel of a subcomodule of the dual.** The vectors killed by every functional
of a subcomodule `W ≤ M*` form a subcomodule `W°` of `M`. -/
noncomputable def dualCoannihilator (W : Subcomodule k H (Module.Dual k M)) :
    Subcomodule k H M :=
  ofSubmodule W.toSubmodule.dualCoannihilator fun m hm ↦ by
    refine (Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero _ m).mpr fun ψ ↦ ?_
    -- In finite dimension, the functionals vanishing on `W°` are the elements of `W`.
    have hψ := W.toSubmodule.dualCoannihilator.comp_mkQ_mem_dualAnnihilator ψ
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq, mem_toSubmodule] at hψ
    -- Evaluation at `m ∈ W°` vanishes on `W`; cancel the antipode, an involution of `H`.
    have hm' : Module.Dual.eval k M m ∈ W.toSubmodule.dualAnnihilator :=
      (Submodule.mem_dualAnnihilator _).mpr fun φ hφ ↦ by
        simpa using (Submodule.mem_dualCoannihilator m).mp hm φ hφ
    rw [← HopfAlgebra.antipode_antipode (R := k) (Comodule.matrixCoefficient (R := k) (C := H) _ m),
      ← Comodule.matrixCoefficient_dual_eval,
      W.toSubmodule.matrixCoefficient_eq_zero_of_mem_dualAnnihilator (W.coact_mem hψ) hm', map_zero]

@[simp]
theorem dualCoannihilator_toSubmodule (W : Subcomodule k H (Module.Dual k M)) :
    W.dualCoannihilator.toSubmodule = W.toSubmodule.dualCoannihilator :=
  (rfl)

@[simp]
theorem mem_dualCoannihilator {W : Subcomodule k H (Module.Dual k M)} {m : M} :
    m ∈ W.dualCoannihilator ↔ ∀ φ ∈ W, φ m = 0 := by
  rw [← mem_toSubmodule, dualCoannihilator_toSubmodule, Submodule.mem_dualCoannihilator]
  simp only [mem_toSubmodule]

/-- The common kernel of the annihilator of a subcomodule is the subcomodule itself. -/
@[simp]
theorem dualAnnihilator_dualCoannihilator (N : Subcomodule k H M) :
    N.dualAnnihilator.dualCoannihilator = N :=
  ext fun m ↦ by
    rw [← mem_toSubmodule, dualCoannihilator_toSubmodule, dualAnnihilator_toSubmodule,
      Subspace.dualAnnihilator_dualCoannihilator_eq, mem_toSubmodule]

/-- The annihilator of the common kernel of a subcomodule of the dual is that subcomodule. -/
@[simp]
theorem dualCoannihilator_dualAnnihilator (W : Subcomodule k H (Module.Dual k M)) :
    W.dualCoannihilator.dualAnnihilator = W :=
  ext fun φ ↦ by
    rw [← mem_toSubmodule, dualAnnihilator_toSubmodule, dualCoannihilator_toSubmodule,
      Subspace.dualCoannihilator_dualAnnihilator_eq, mem_toSubmodule]

theorem dualCoannihilator_le_dualCoannihilator_iff {W X : Subcomodule k H (Module.Dual k M)} :
    W.dualCoannihilator ≤ X.dualCoannihilator ↔ X ≤ W := by
  rw [← dualAnnihilator_le_dualAnnihilator_iff, dualCoannihilator_dualAnnihilator,
    dualCoannihilator_dualAnnihilator]

variable (k H M) in
/-- **Subcomodules of the dual.** Over a field, taking annihilators is an order-reversing
bijection between the subcomodules of a finite-dimensional comodule `M` over a commutative
Hopf algebra and the subcomodules of its dual `M*`, with inverse the common kernel. -/
noncomputable def dualAnnihilatorOrderIso :
    Subcomodule k H M ≃o (Subcomodule k H (Module.Dual k M))ᵒᵈ where
  toFun N := OrderDual.toDual N.dualAnnihilator
  invFun W := (OrderDual.ofDual W).dualCoannihilator
  left_inv := dualAnnihilator_dualCoannihilator
  right_inv := dualCoannihilator_dualAnnihilator
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

@[simp]
theorem dualAnnihilatorOrderIso_apply (N : Subcomodule k H M) :
    dualAnnihilatorOrderIso k H M N = OrderDual.toDual N.dualAnnihilator :=
  (rfl)

@[simp]
theorem dualAnnihilatorOrderIso_symm_apply (W : (Subcomodule k H (Module.Dual k M))ᵒᵈ) :
    (dualAnnihilatorOrderIso k H M).symm W = (OrderDual.ofDual W).dualCoannihilator :=
  (rfl)

theorem dualCoannihilator_injective :
    Function.Injective (dualCoannihilator (k := k) (H := H) (M := M)) :=
  Function.LeftInverse.injective dualCoannihilator_dualAnnihilator

@[simp]
theorem dualCoannihilator_eq_bot_iff {W : Subcomodule k H (Module.Dual k M)} :
    W.dualCoannihilator = ⊥ ↔ W = ⊤ := by
  rw [← dualAnnihilator_eq_top_iff, dualCoannihilator_dualAnnihilator]

@[simp]
theorem dualCoannihilator_eq_top_iff {W : Subcomodule k H (Module.Dual k M)} :
    W.dualCoannihilator = ⊤ ↔ W = ⊥ := by
  rw [← dualAnnihilator_eq_bot_iff, dualCoannihilator_dualAnnihilator]

end TauCeti.Subcomodule
