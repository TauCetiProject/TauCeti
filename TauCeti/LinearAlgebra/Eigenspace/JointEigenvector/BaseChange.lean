/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Artinian.Socle
public import TauCeti.RingTheory.Support.BaseChange
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.Algebra.Module.LocalizedModule.Lift
import TauCeti.RingTheory.TensorProduct.CentralBaseChange

/-!
# Joint eigenvectors of a finite algebra after scalar extension to a field

Let `A` be a commutative `O`-algebra which is finite as an `O`-module, acting on a module `L`
which is finite over `A`, and let `φ : A →ₐ[O] k` be a character with values in a field. Base
change along `O → k` makes every `a : A` act on `k ⊗[O] L`. This file shows that `φ` has a
nonzero joint eigenvector there, that is a nonzero `v` with `a • v = φ a • v` for every `a`,
exactly when `φ` vanishes on the annihilator of `L`, that is when the kernel of `φ` lies in the
support of `L`.

The typical case is a Hecke algebra `A` acting on a lattice `L` over a coefficient ring `O`, with
`k` the residue field of `O`. A residual character `φ` then occurs in the reduction `k ⊗[O] L`
exactly when it lies in the residual support of `L`, which can be tested on the reduction of `L`
modulo any ideal killed by `φ`, for instance modulo a uniformizer. In particular every residual
character of a Hecke algebra acting faithfully on `L` occurs, and a character which occurs on a
module on which an ideal `I` acts trivially kills `I`, so it factors through `A ⧸ I`. The
resulting nonzero residual eigenvector is the input of the Deligne–Serre lifting lemma.

The proof works over the Artinian ring `k ⊗[O] A`. The canonical map from `k ⊗[O] L` onto the
fibre `k ⊗[A] L` of `L` at `φ` turns the action of `b : k ⊗[O] A` into multiplication by the
extension of `φ` to `k ⊗[O] A`. The fibre is nonzero when the kernel of `φ` contains the
annihilator of `L`, by Nakayama's lemma. Hence the extended character vanishes on the annihilator
of `k ⊗[O] L`, and the socle of an Artinian module provides the eigenvector.

## Main results

* `AlgHom.annihilator_le_ker_of_baseChange_eq_smul`: a character with a nonzero joint
  eigenvector in `k ⊗[O] L` vanishes on the annihilator of `L`.
* `AlgHom.exists_ne_zero_forall_baseChange_eq_smul_of_annihilator_le`: conversely, a character
  vanishing on the annihilator of `L` has a nonzero joint eigenvector in `k ⊗[O] L`.
* `AlgHom.exists_ne_zero_forall_baseChange_eq_smul_iff_annihilator_le`: the two together.
* `AlgHom.exists_ne_zero_forall_baseChange_eq_smul_iff_mem_support_quotient`: the same condition
  in terms of the support of `L ⧸ I • L`, for an ideal `I` killed by the character.
* `AlgHom.exists_ne_zero_forall_baseChange_eq_smul`: every character has a nonzero joint
  eigenvector when `A` acts faithfully on `L`.
* `AlgHom.exists_ne_zero_forall_baseChange_lsmul_apply_eq_smul`: the same for a character
  `A → V` with values in a domain `V`, when `L` is moreover flat over `O`. The character to the
  fraction field of `V` occurs on `L` after base change, and clearing denominators along the
  localization `V ⊗[O] L → k ⊗[O] L` gives a nonzero integral eigenvector. This is the occurrence
  step of the Deligne–Serre eigenvalue lifting lemma.

## References

* K. A. Ribet and W. A. Stein, *Lectures on Serre's conjectures*, §3.6 and §3.9.
* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. ENS 7 (1974), §6.
-/

public section

open TensorProduct

variable {O A L k : Type*} [CommRing O] [CommRing A] [Algebra O A]
  [AddCommGroup L] [Module A L] [Module O L] [IsScalarTower O A L] [Field k] [Algebra O k]

namespace AlgHom

/-- A character `φ` with a nonzero joint eigenvector in `k ⊗[O] L` vanishes on the annihilator
of `L`. -/
theorem annihilator_le_ker_of_baseChange_eq_smul (φ : A →ₐ[O] k) {v : k ⊗[O] L} (hv : v ≠ 0)
    (hφ : ∀ a : A, (Algebra.lsmul O O L a).baseChange k v = φ a • v) :
    Module.annihilator A L ≤ RingHom.ker φ := by
  intro a ha
  have h0 : Algebra.lsmul O O L a = 0 := LinearMap.ext fun l ↦ Module.mem_annihilator.1 ha l
  have := hφ a
  rw [h0, LinearMap.baseChange_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
  exact this.resolve_right hv

section CentralBaseChange

open TauCeti.CentralBaseChange

attribute [local instance low] TauCeti.CentralBaseChange.module

/-- A character `φ` of a finite `O`-algebra `A` which acts on `k ⊗[O] L`, through some nonzero
`k`-linear map, by multiplication by `φ` has a nonzero joint eigenvector in `k ⊗[O] L`. -/
private theorem exists_ne_zero_forall_baseChange_eq_smul_of_linearMap [Module.Finite O A]
    (φ : A →ₐ[O] k) {W : Type*} [AddCommGroup W] [Module k W] (π : k ⊗[O] L →ₗ[k] W)
    (hπ : π ≠ 0) (hπφ : ∀ (a : A) (v : k ⊗[O] L),
      π ((Algebra.lsmul O O L a).baseChange k v) = φ a • π v) :
    ∃ v : k ⊗[O] L, v ≠ 0 ∧ ∀ a : A, (Algebra.lsmul O O L a).baseChange k v = φ a • v := by
  -- `k ⊗[O] A` acts on `k ⊗[O] L`, and `χ` is the extension of `φ` to it.
  let χ : k ⊗[O] A →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k) φ fun _ _ ↦ Commute.all _ _
  have : IsArtinianRing (k ⊗[O] A) := IsArtinianRing.of_finite k _
  -- `π` turns the action of `b` into multiplication by `χ b`.
  have hπχ (b : k ⊗[O] A) (v : k ⊗[O] L) : π (b • v) = χ b • π v := by
    induction b using TensorProduct.inductionOn with
    | tmul c a => simp [smul_def, lsmul_tmul, χ, hπφ, mul_smul]
    | add x y hx hy => simp [add_smul, hx, hy]
  -- Hence `χ` vanishes on the annihilator of `k ⊗[O] L`, and the socle provides the eigenvector.
  have hann : Module.annihilator (k ⊗[O] A) (k ⊗[O] L) ≤ RingHom.ker χ := by
    intro b hb
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hπ
    have := hπχ b v
    rw [Module.mem_annihilator.1 hb, map_zero, eq_comm, smul_eq_zero] at this
    exact this.resolve_right hv
  obtain ⟨v, hv0, hv⟩ := χ.exists_ne_zero_forall_smul_eq_smul_of_annihilator_le hann
  exact ⟨v, hv0, fun a ↦ by simpa [smul_def, lsmul_tmul, χ] using hv (1 ⊗ₜ a)⟩

end CentralBaseChange

variable [Module.Finite O A] [Module.Finite A L]

/-- **Occurrence of characters after base change.** Let `A` be a commutative `O`-algebra, finite
as an `O`-module, acting on a module `L` finite over `A`. Every character `φ : A →ₐ[O] k` to a
field which vanishes on the annihilator of `L` has a nonzero joint eigenvector `v` in
`k ⊗[O] L`: every `a : A` acts on `v` by `φ a`. -/
theorem exists_ne_zero_forall_baseChange_eq_smul_of_annihilator_le (φ : A →ₐ[O] k)
    (h : Module.annihilator A L ≤ RingHom.ker φ) :
    ∃ v : k ⊗[O] L, v ≠ 0 ∧ ∀ a : A, (Algebra.lsmul O O L a).baseChange k v = φ a • v := by
  let _ : Algebra A k := φ.toAlgebra
  have : IsScalarTower O A k := .of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  -- The fibre `k ⊗[A] L` of `L` at `φ` is nonzero.
  have : Nontrivial (k ⊗[A] L) := by
    rw [← not_subsingleton_iff_nontrivial,
      ← TauCeti.Module.annihilator_map_eq_top_iff_subsingleton_tensorProduct,
      (Ideal.map_eq_bot_iff_le_ker (algebraMap A k)).2 h]
    exact bot_ne_top
  -- The canonical map `k ⊗[O] L → k ⊗[A] L` is onto, and `a` acts on its target by `φ a`.
  let π := mapOfCompatibleSMul A O k k L
  refine exists_ne_zero_forall_baseChange_eq_smul_of_linearMap φ π ?_ fun a v ↦ ?_
  · obtain ⟨w, hw⟩ := exists_ne (0 : k ⊗[A] L)
    obtain ⟨v, rfl⟩ := mapOfCompatibleSMul_surjective A O k k L w
    exact ne_of_apply_ne (· v) hw
  · induction v using TensorProduct.inductionOn with
    | tmul c l =>
      simp [π, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        RingHom.algebraMap_toAlgebra]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- A character `φ : A →ₐ[O] k` has a nonzero joint eigenvector in `k ⊗[O] L` if and only if it
vanishes on the annihilator of `L`. -/
theorem exists_ne_zero_forall_baseChange_eq_smul_iff_annihilator_le (φ : A →ₐ[O] k) :
    (∃ v : k ⊗[O] L, v ≠ 0 ∧ ∀ a : A, (Algebra.lsmul O O L a).baseChange k v = φ a • v) ↔
      Module.annihilator A L ≤ RingHom.ker φ :=
  ⟨fun ⟨_, hv, hφ⟩ ↦ φ.annihilator_le_ker_of_baseChange_eq_smul hv hφ,
    φ.exists_ne_zero_forall_baseChange_eq_smul_of_annihilator_le⟩

/-- **Residual support.** Let `I` be an ideal of `A` killed by the character `φ : A →ₐ[O] k`. Then
`φ` has a nonzero joint eigenvector in `k ⊗[O] L` if and only if the kernel of `φ` lies in the
support of `L ⧸ I • L`. For `k` the residue field of a discrete valuation ring `O` and `I`
generated by a uniformizer, this says that `φ` occurs in the reduction of `L` exactly when the
localization of `L ⧸ π L` at the kernel of `φ` is nonzero. -/
theorem exists_ne_zero_forall_baseChange_eq_smul_iff_mem_support_quotient (φ : A →ₐ[O] k)
    {I : Ideal A} (hI : I ≤ RingHom.ker φ) :
    (∃ v : k ⊗[O] L, v ≠ 0 ∧ ∀ a : A, (Algebra.lsmul O O L a).baseChange k v = φ a • v) ↔
      (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∈
        Module.support A (L ⧸ (I • ⊤ : Submodule A L)) := by
  rw [Module.support_quotient, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
    Module.mem_support_iff_of_finite, φ.exists_ne_zero_forall_baseChange_eq_smul_iff_annihilator_le]
  exact (and_iff_left hI).symm

/-- **Occurrence of characters on a faithful module.** If `A` acts faithfully on `L`, then every
character `φ : A →ₐ[O] k` has a nonzero joint eigenvector in `k ⊗[O] L`. -/
theorem exists_ne_zero_forall_baseChange_eq_smul [FaithfulSMul A L] (φ : A →ₐ[O] k) :
    ∃ v : k ⊗[O] L, v ≠ 0 ∧ ∀ a : A, (Algebra.lsmul O O L a).baseChange k v = φ a • v :=
  φ.exists_ne_zero_forall_baseChange_eq_smul_of_annihilator_le <| by
    simp [Module.annihilator_eq_bot.2 ‹_›]

variable (k) {V : Type*} [CommRing V] [Algebra O V] [Algebra V k] [IsFractionRing V k]
  [IsScalarTower O V k] in
include k in
/-- **Occurrence of an integral character.** Let `A` be a commutative `O`-algebra, finite as an
`O`-module, acting faithfully on a module `L` finite over `A` and flat over `O`, and let `V` be a
domain over `O` with fraction field `k`. Every `O`-algebra map `ψ : A →ₐ[O] V` occurs on
`V ⊗[O] L`: some nonzero `n` satisfies `(a • ·).baseChange V n = ψ a • n` for every `a : A`. -/
theorem exists_ne_zero_forall_baseChange_lsmul_apply_eq_smul [Module.Flat O L] [FaithfulSMul A L]
    (ψ : A →ₐ[O] V) :
    ∃ n : V ⊗[O] L, n ≠ 0 ∧ ∀ a : A, (Algebra.lsmul O O L a).baseChange V n = ψ a • n := by
  -- The character `A → k` induced by `ψ` occurs on the faithful module `k ⊗[O] L`.
  obtain ⟨v, hv0, hv⟩ :=
    ((IsScalarTower.toAlgHom O V k).comp ψ).exists_ne_zero_forall_baseChange_eq_smul (L := L)
  -- Clear the denominators of `v` along the localization `V ⊗[O] L → k ⊗[O] L`.
  let g : V ⊗[O] L →ₗ[V] k ⊗[O] L := AlgebraTensorModule.rTensor O L (Algebra.linearMap V k)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap ((Algebra.linearMap V k).restrictScalars O)
      (IsFractionRing.injective V k)
  obtain ⟨n, hn0, hn, -⟩ :=
    IsLocalizedModule.exists_ne_zero_forall_apply_eq_smul_of_injective (nonZeroDivisors V) hg
      (T := fun a : A ↦ (Algebra.lsmul O O L a).baseChange V)
      (T' := fun a : A ↦ ((Algebra.lsmul O O L a).baseChange k).restrictScalars V)
      (fun a ↦ by ext; simp [g]) hv0 (b := fun a ↦ ψ a) fun a ↦ by
        simpa [algebraMap_smul] using hv a
  exact ⟨n, hn0, hn⟩

end AlgHom
