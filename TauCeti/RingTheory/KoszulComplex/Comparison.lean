/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import TauCeti.RingTheory.KoszulComplex.Basis
import TauCeti.RingTheory.Ideal.Cotangent.LinearIndependent

/-!
# Maps out of a Koszul complex that are injective modulo an ideal

Let `M` be a free module with basis `(bᵢ)` and let `φ : M → R` be a linear functional, with
values `xᵢ = φ(bᵢ)`. This file proves the inductive step of the proof of Stacks, Lemma 10.110.3
(00OA). Suppose the `xᵢ` lie in an ideal `I` and are linearly independent in `I/I²`, and compare
the Koszul complex with a complex whose differential `d'` lands in `I` times its target, as for a
minimal free resolution over a local ring with `I` the maximal ideal. If a chain map `α` is
injective modulo `I` in degree `n`, with free target, then it is injective modulo `I` in degree
`n + 1`: if `α(z) ∈ I F'` then `α(d z) = d'(α z) ∈ I² F`, so `∑ xᵢ α(ιᵢ z) ∈ I² F`, where `ιᵢ` is
the contraction by the coordinate `bᵢ*`, whence every `α(ιᵢ z) ∈ I F`, every `ιᵢ z ∈ I ⋀ⁿ M`,
and finally `z ∈ I ⋀ⁿ⁺¹ M` by `Module.Basis.mem_smul_top_iff_forall_koszulDifferential_coord_mem`.

## Main results

* `Module.Basis.comap_smul_top_le_of_comp_koszulDifferential`: a map compatible with the Koszul
  differential and a differential landing in `I` times its target is injective modulo `I` in
  degree `n + 1` if it is so in degree `n`.

## References

* [The Stacks Project, Lemma 10.110.3](https://stacks.math.columbia.edu/tag/00OA)
-/

public section

noncomputable section

universe u v

open TauCeti

namespace Module.Basis

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {ι : Type*}


/-- **The inductive step of Stacks 00OA.** Let `φ(bᵢ) ∈ I` be linearly independent in `I/I²`,
let `d : F' → F` be a map into a free module with image in `I F`, and let `α`, `α'` be maps out of
`⋀ⁿ M` and `⋀ⁿ⁺¹ M` with `d ∘ α' = α ∘ d_φ`, where `d_φ` is the Koszul differential of `φ`. If
`α` is injective modulo `I`, i.e. `α(z) ∈ I F` forces `z ∈ I ⋀ⁿ M`, then so is `α'`. -/
theorem comap_smul_top_le_of_comp_koszulDifferential [Finite ι] (b : Module.Basis ι R M)
    (φ : Module.Dual R M) {I : Ideal R} (hφ : ∀ i, φ (b i) ∈ I)
    (hli : LinearIndependent (R ⧸ I) fun i ↦ I.toCotangent ⟨φ (b i), hφ i⟩)
    {F F' : Type*} [AddCommGroup F] [Module R F] [Module.Free R F] [AddCommGroup F']
    [Module R F'] {d : F' →ₗ[R] F} (hd : LinearMap.range d ≤ I • ⊤) {n : ℕ}
    {α : ⋀[R]^n M →ₗ[R] F} {α' : ⋀[R]^(n + 1) M →ₗ[R] F'}
    (hcomm : d ∘ₗ α' = α ∘ₗ koszulDifferential φ n)
    (hα : (I • ⊤ : Submodule R F).comap α ≤ I • ⊤) :
    (I • ⊤ : Submodule R F').comap α' ≤ I • ⊤ := by
  let := Fintype.ofFinite ι
  intro z hz
  rw [Submodule.mem_comap] at hz
  -- Since `d` lands in `I F`, the image `d (α' z) = α (d_φ z)` lies in `I² F`.
  have hd' : d (α' z) ∈ I ^ 2 • (⊤ : Submodule R F) := by
    have : d (α' z) ∈ (I • ⊤ : Submodule R F').map d := Submodule.mem_map_of_mem hz
    rw [Submodule.map_smul'', Submodule.map_top] at this
    rw [pow_two, Submodule.mul_smul]
    exact smul_mono_right I hd this
  rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, b.koszulDifferential_eq_sum,
    map_sum] at hd'
  simp only [map_smul] at hd'
  refine (b.mem_smul_top_iff_forall_koszulDifferential_coord_mem I z).mpr fun i ↦ hα ?_
  exact I.mem_smul_top_of_sum_smul_mem_sq_smul_top hli hd' i

end Module.Basis
