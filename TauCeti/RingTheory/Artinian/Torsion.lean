/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Nakayama

/-!
# Torsion of Artinian modules

Let `R` be a commutative ring and `M` an Artinian `R`-module. For any finitely generated ideal `I`
contained in the Jacobson radical of `R`, the descending chain `n ↦ I ^ n • R • x` stabilizes for
each `x ∈ M`, so Nakayama's lemma forces `I ^ n • x = 0`
(`Ideal.primaryComponent_eq_top_of_isArtinian`). Moreover, for any ideal `I` with semisimple
quotient `R ⧸ I`, the `I`-torsion submodule of an Artinian module is finitely generated over `R ⧸ I`
(`TauCeti.finite_quotient_torsionBySet`). No Noetherian or local hypothesis on `R` is needed.

## Main results

* `Ideal.primaryComponent_eq_top_of_isArtinian`: over any commutative ring, an Artinian module is
  `I`-power torsion for every finitely generated ideal `I ≤ Ring.jacobson R`.
* `TauCeti.finite_quotient_torsionBySet`: for any ideal `I` with semisimple quotient `R ⧸ I`, the
  `I`-torsion submodule of an Artinian module is finitely generated over `R ⧸ I`.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Over any commutative ring, an Artinian module is `I`-power torsion for every finitely generated
ideal `I` contained in the Jacobson radical. Neither a Noetherian nor a local hypothesis is
needed. -/
theorem primaryComponent_eq_top_of_isArtinian (I : Ideal R) [IsArtinian R M]
    (hI : I.FG) (hJ : I ≤ Ring.jacobson R) :
    I.primaryComponent M = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  -- The descending chain `I ^ n • (R • x)` stabilizes because `M` is Artinian.
  let f : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual (I ^ n • Submodule.span R {x}), fun m n hmn ↦
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  have hstab : I ^ n • Submodule.span R {x} = I • (I ^ n • Submodule.span R {x}) := by
    have h1 : I ^ n • Submodule.span R {x} = I ^ (n + 1) • Submodule.span R {x} :=
      OrderDual.toDual.injective (hn (n + 1) (Nat.le_succ n))
    rw [pow_succ', mul_smul] at h1
    exact h1
  have hfg : (I ^ n • Submodule.span R {x}).FG :=
    Submodule.FG.smul hI.pow (Submodule.fg_span_singleton x)
  have hbot : I ^ n • Submodule.span R {x} = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson I _ hfg hstab.le hJ
  refine (I.primaryComponent_mem M x).mpr ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr fun r ↦ ?_⟩
  have hmem : (r : R) • x ∈ I ^ n • Submodule.span R {x} :=
    Submodule.smul_mem_smul r.property (Submodule.mem_span_singleton_self x)
  rwa [hbot, Submodule.mem_bot] at hmem

end Ideal

namespace TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For any ideal `I` with semisimple quotient `R ⧸ I`, the `I`-torsion submodule of an Artinian
`R`-module is finitely generated over `R ⧸ I`. No Noetherian or local hypothesis is needed. -/
theorem finite_quotient_torsionBySet [IsArtinian R M] (I : Ideal R) [IsSemisimpleRing (R ⧸ I)] :
    Module.Finite (R ⧸ I) (Submodule.torsionBySet R M (I : Set R)) := by
  have : IsArtinian (R ⧸ I) (Submodule.torsionBySet R M (I : Set R)) :=
    isArtinian_of_tower R (isArtinian_submodule' _)
  exact ((IsSemisimpleModule.finite_tfae (R := R ⧸ I)
    (M := Submodule.torsionBySet R M (I : Set R))).out 3 1).mp this

end TauCeti
