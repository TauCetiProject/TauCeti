/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Finiteness.Lattice
import TauCeti.Algebra.Coalgebra.Subcoalgebra

/-!
# Binary joins of subcoalgebras

This file adds the binary join operation on the lightweight `Subcoalgebra` structure. The join
of two subcoalgebras has underlying submodule `D.toSubmodule ⊔ E.toSubmodule`; the
comultiplication is stable because `Δ` is linear and each tensor square maps into the tensor
square of the larger submodule.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target on
finite-dimensional subcoalgebras: finite sums of finite subcoalgebras remain finite.

## Main declarations

* `Subcoalgebra.instSemilatticeSup`: binary joins of subcoalgebras.
* `Subcoalgebra.sup_toSubmodule`, `Subcoalgebra.mem_sup`: characteristic API for joins.
* `Subcoalgebra.sup_finite`, `Subcoalgebra.finset_sup_finite`: finite generation is
  preserved by finite joins.
-/

open scoped TensorProduct

namespace TauCeti

universe u v

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

omit [Coalgebra R C] in
private lemma tensorSquare_range_mono {P Q : Submodule R C} (hPQ : P ≤ Q) :
    LinearMap.range (TensorProduct.map P.subtype P.subtype) ≤
      LinearMap.range (TensorProduct.map Q.subtype Q.subtype) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨TensorProduct.map (Submodule.inclusion hPQ) (Submodule.inclusion hPQ) x, ?_⟩
  induction x with
  | zero => simp
  | tmul p q => rfl
  | add x y hx hy => simp [hx, hy]

private lemma comul_mem_sup (D E : Subcoalgebra R C) {c : C}
    (hc : c ∈ D.toSubmodule ⊔ E.toSubmodule) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range
        (TensorProduct.map (D.toSubmodule ⊔ E.toSubmodule).subtype
          (D.toSubmodule ⊔ E.toSubmodule).subtype) := by
  rcases Submodule.mem_sup.1 hc with ⟨d, hd, e, he, rfl⟩
  rw [LinearMap.map_add]
  exact add_mem
    (tensorSquare_range_mono (show D.toSubmodule ≤ D.toSubmodule ⊔ E.toSubmodule from
      le_sup_left) (D.comul_mem hd))
    (tensorSquare_range_mono (show E.toSubmodule ≤ D.toSubmodule ⊔ E.toSubmodule from
      le_sup_right) (E.comul_mem he))

/-- The join of two subcoalgebras has underlying submodule the join of the underlying
submodules. -/
instance instMax : Max (Subcoalgebra R C) where
  max D E :=
    { carrier := D.toSubmodule ⊔ E.toSubmodule
      comul_mem' := by
        intro c hc
        exact comul_mem_sup D E hc }

/-- The underlying submodule of the join is the join of the underlying submodules. -/
@[simp]
theorem sup_toSubmodule (D E : Subcoalgebra R C) :
    (D ⊔ E).toSubmodule = D.toSubmodule ⊔ E.toSubmodule :=
  rfl

/-- Membership in the join of two subcoalgebras. -/
theorem mem_sup {D E : Subcoalgebra R C} {c : C} :
    c ∈ D ⊔ E ↔ ∃ d ∈ D, ∃ e ∈ E, d + e = c := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]
  rfl

/-- The left subcoalgebra is contained in the join. -/
theorem le_sup_left (D E : Subcoalgebra R C) : D ≤ D ⊔ E := by
  intro c hc
  rw [← mem_toSubmodule, sup_toSubmodule]
  exact Submodule.mem_sup_left ((mem_toSubmodule).2 hc)

/-- The right subcoalgebra is contained in the join. -/
theorem le_sup_right (D E : Subcoalgebra R C) : E ≤ D ⊔ E := by
  intro c hc
  rw [← mem_toSubmodule, sup_toSubmodule]
  exact Submodule.mem_sup_right ((mem_toSubmodule).2 hc)

/-- To prove a join of subcoalgebras is contained in a third subcoalgebra, prove containment
for each summand. -/
theorem sup_le {D E F : Subcoalgebra R C} (hD : D ≤ F) (hE : E ≤ F) :
    D ⊔ E ≤ F := by
  intro c hc
  rw [mem_sup] at hc
  rcases hc with ⟨d, hd, e, he, rfl⟩
  exact add_mem (hD hd) (hE he)

instance instSemilatticeSup : SemilatticeSup (Subcoalgebra R C) :=
  SemilatticeSup.mk (fun D E => D ⊔ E) le_sup_left le_sup_right
    (fun _ _ _ => sup_le)

/-- The join of finitely generated subcoalgebras is finitely generated as an `R`-module. -/
theorem sup_finite (D E : Subcoalgebra R C)
    [Module.Finite R D.toSubmodule] [Module.Finite R E.toSubmodule] :
    Module.Finite R (D ⊔ E).toSubmodule := by
  rw [sup_toSubmodule, Module.Finite.iff_fg]
  exact (Module.Finite.iff_fg.mp inferInstance).sup (Module.Finite.iff_fg.mp inferInstance)

/-- The join of finitely generated subcoalgebras is finitely generated as an `R`-module. -/
instance instFiniteSup (D E : Subcoalgebra R C)
    [Module.Finite R D.toSubmodule] [Module.Finite R E.toSubmodule] :
    Module.Finite R (D ⊔ E).toSubmodule :=
  sup_finite D E

variable {ι : Type*}

/-- The underlying submodule of a finite join of subcoalgebras is the finite join of the
underlying submodules. -/
@[simp]
theorem finset_sup_toSubmodule (s : Finset ι) (D : ι → Subcoalgebra R C) :
    (s.sup D).toSubmodule = s.sup fun i => (D i).toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => exact bot_toSubmodule
  | insert a s _ ih =>
      rw [Finset.sup_insert, sup_toSubmodule, ih, Finset.sup_insert]

/-- A subcoalgebra in a finite family is contained in the finite join of the family. -/
theorem le_finset_sup {s : Finset ι} {D : ι → Subcoalgebra R C} {i : ι} (hi : i ∈ s) :
    D i ≤ s.sup D := by
  exact Finset.le_sup hi

/-- To prove a finite join of subcoalgebras is contained in a subcoalgebra, prove containment
for each member of the finite family. -/
theorem finset_sup_le {s : Finset ι} {D : ι → Subcoalgebra R C} {E : Subcoalgebra R C}
    (hD : ∀ i ∈ s, D i ≤ E) :
    s.sup D ≤ E := by
  exact Finset.sup_le hD

/-- A finite join of finitely generated subcoalgebras is finitely generated as an
`R`-module. -/
theorem finset_sup_finite (s : Finset ι) (D : ι → Subcoalgebra R C)
    (hD : ∀ i ∈ s, Module.Finite R (D i).toSubmodule) :
    Module.Finite R (s.sup D).toSubmodule := by
  classical
  rw [finset_sup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_finset_sup s (fun i => (D i).toSubmodule)
    fun i hi => Module.Finite.iff_fg.mp (hD i hi)

end Subcoalgebra

end TauCeti
