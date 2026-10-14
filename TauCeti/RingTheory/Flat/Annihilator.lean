/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Annihilators under flat scalar extension

Flat extension of scalars preserves the annihilator of a finite module. The finite
generation hypothesis permits testing annihilation on a finite family, whose tensor
product commutes with its product of targets. The cyclic statement applies to the
element `1 ⊗ₜ m`, without any finiteness hypothesis on the ambient module.

The argument reuses `LinearMap.ker_baseChange_of_flat` and Mathlib's finite product
comparison `TensorProduct.piRight`.

These formulas identify the scheme theoretic support of a finite module after flat
base change. The main result is Stacks Project, Lemma 10.40.4,
[Tag 07T8](https://stacks.math.columbia.edu/tag/07T8).
-/

public section

open TensorProduct

namespace TauCeti

section Semiring

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Extension of the annihilator is contained in the annihilator after arbitrary base change. -/
theorem annihilator_map_le_baseChange :
    (Module.annihilator R M).map (algebraMap R S) ≤
      Module.annihilator S (S ⊗[R] M) := by
  refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    simp [← TensorProduct.tmul_smul,
      Module.mem_annihilator.mp hr m]
  | add x y hx hy => simp [smul_add, hx, hy]

end Semiring

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- For a finite family, flat base change preserves the annihilator of its span. -/
theorem annihilator_flat_baseChange_generators {ι : Type*} [Finite ι]
    [Module.Flat R S] (g : ι → M) :
    (Submodule.span S (Set.range fun i ↦ (1 : S) ⊗ₜ[R] g i)).annihilator =
      (Submodule.span R (Set.range g)).annihilator.map (algebraMap R S) := by
  classical
  let := Fintype.ofFinite ι
  let f : R →ₗ[R] (ι → M) := LinearMap.pi fun i ↦ LinearMap.toSpanSingleton R M (g i)
  have hker : (Submodule.span R (Set.range g)).annihilator = LinearMap.ker f := by
    ext r
    simp [Submodule.mem_annihilator_span, LinearMap.mem_ker, funext_iff,
      LinearMap.pi_apply, f]
  ext s
  rw [hker, f.mem_map_ker_iff_of_flat s, Submodule.mem_annihilator_span]
  constructor
  · intro hs
    apply (TensorProduct.piRight R S S (fun _ : ι ↦ M)).injective
    ext i
    simpa [f, TensorProduct.smul_tmul'] using
      hs ⟨(1 : S) ⊗ₜ[R] g i, ⟨i, rfl⟩⟩
  · intro hs x
    obtain ⟨i, hi⟩ := x.property
    rw [← hi]
    have hi := congrArg (fun z ↦ TensorProduct.piRight R S S (fun _ : ι ↦ M) z i) hs
    simpa [f, TensorProduct.smul_tmul'] using hi

/-- For a flat coefficient algebra, the annihilator of a finite module extends exactly.
This is Stacks Project, Lemma 10.40.4 (Tag 07T8). -/
theorem annihilator_flat_baseChange [Module.Flat R S] [Module.Finite R M] :
    Module.annihilator S (S ⊗[R] M) =
      (Module.annihilator R M).map (algebraMap R S) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hbase : Submodule.span S (Set.range fun i ↦ (1 : S) ⊗ₜ[R] g i) = ⊤ := by
    simpa [Submodule.baseChange_span, ← Set.range_comp, Function.comp_def,
      TensorProduct.mk_apply] using
      congrArg (Submodule.baseChange S) hg
  rw [← Submodule.annihilator_top, ← hbase,
    annihilator_flat_baseChange_generators, hg, Submodule.annihilator_top]

/-- Flat scalar extension preserves the annihilator of the element `1 ⊗ₜ m`.
The ambient module need not be finite. -/
theorem element_annihilator_flat_baseChange [Module.Flat R S] (m : M) :
    (Submodule.span S {(1 : S) ⊗ₜ[R] m}).annihilator =
      (Submodule.span R {m}).annihilator.map (algebraMap R S) := by
  simpa using annihilator_flat_baseChange_generators (S := S) (fun _ : Unit ↦ m)

end TauCeti
