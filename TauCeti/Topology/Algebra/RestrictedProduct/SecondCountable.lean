/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Box
import Mathlib.Logic.Equiv.List

/-!
# Second countability of restricted products

A restricted product `Πʳ i, [R i, A i]` over a countable index type `ι` of second-countable spaces
`R i` is second countable whenever `A i` is open for cofinitely many `i`
(`RestrictedProduct.secondCountableTopology_of_cofinite`). When `[Fact (∀ i, IsOpen (A i))]` holds
(or when `ι` is finite, with no openness assumption on `A i`), this is registered as a typeclass
instance. Every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` and the `⊥`-filter restricted product are
second countable with no assumption on `A i` (via the topological embedding into `Π i, R i`), while
`Πʳ i, [R i, A i]_[⊤]` requires second countability only on the reference subspaces `A i` (via
`RestrictedProduct.homeoTop`).

Second countability ensures that the open-box topological basis generates the Borel σ-algebra of
`Πʳ i, [R i, A i]` and unlocks standard Borel, product-measure, restricted Haar-measure, and
quotient-measure arguments on countable restricted products such as adele and idele groups. We
establish it by covering `Πʳ i, [R i, A i]` with countably many open second-countable principal
stages obtained by deleting arbitrary finite sets alongside the finite locus where `A i` fails to
be open.

The cofinite openness hypothesis cannot be dropped, even when every factor is compact metrizable
and every reference set is a closed singleton: `TauCeti.not_firstCountableTopology_cantorSingleton`
shows by diagonalization that `Πʳ _ : ℕ, [ℕ → Bool, {fun _ ↦ false}]` is not first countable (and
hence not second countable).

## Main results

* `RestrictedProduct.secondCountableTopology_of_top`: `Πʳ i, [R i, A i]_[⊤]` is second countable
  when `ι` is countable and every subspace `A i` is second countable.
* `RestrictedProduct.secondCountableTopology_of_principal`,
  `RestrictedProduct.secondCountableTopology_of_bot`: principal and `⊥` stages of a countable
  family of second-countable spaces are second countable.
* `RestrictedProduct.secondCountableTopology_of_cofinite`: `Πʳ i, [R i, A i]` is second countable
  when `ι` is countable, every `R i` is second countable, and `∀ᶠ i in cofinite, IsOpen (A i)`.
* `RestrictedProduct.instSecondCountableTopology`: instance under `[Fact (∀ i, IsOpen (A i))]`.
* `RestrictedProduct.secondCountableTopology_of_finite`: instance over `[Finite ι]` with no
  openness hypothesis on `A i`.
* `TauCeti.not_firstCountableTopology_cantorSingleton`,
  `TauCeti.not_secondCountableTopology_cantorSingleton`: sharpness of cofinite openness of `A i`.

## References

* N. Bourbaki, *General Topology*.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Chapter 5.
* A. Weil, *Basic Number Theory*.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

/-- The `⊤`-filter restricted product `Πʳ i, [R i, A i]_[⊤]` over a countable index type with
second-countable reference subspaces `A i` is second countable. -/
instance secondCountableTopology_of_top {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
    [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (A i)] :
    SecondCountableTopology (Πʳ i, [R i, A i]_[⊤]) :=
  homeoTop.symm.isEmbedding.secondCountableTopology

section Principal

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
variable [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]

/-- Every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` over a countable index type with
second-countable factors is second countable, with no assumption on `A i` or `S`. -/
instance secondCountableTopology_of_principal {S : Set ι} :
    SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 S]) :=
  isEmbedding_coe_of_principal.secondCountableTopology

/-- The `⊥`-filter restricted product `Πʳ i, [R i, A i]_[⊥]` over a countable index type with
second-countable factors is second countable. -/
instance secondCountableTopology_of_bot :
    SecondCountableTopology (Πʳ i, [R i, A i]_[⊥]) :=
  isEmbedding_coe_of_bot.secondCountableTopology

/-- A restricted product `Πʳ i, [R i, A i]` over a countable index type with second-countable
factors is second countable whenever `A i` is open for cofinitely many `i`. -/
theorem secondCountableTopology_of_cofinite (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  let S : Finset ι → Set ι := fun F ↦ ({i | IsOpen (A i)}ᶜ ∪ ↑F)ᶜ
  have hS : ∀ F : Finset ι, cofinite ≤ 𝓟 (S F) := fun F ↦
    le_principal_iff.mpr (mem_cofinite.mpr (by
      simpa only [S, compl_compl] using (mem_cofinite.mp hA).union F.finite_toSet))
  have hA_S : ∀ (F : Finset ι) (i : ι), i ∈ S F → IsOpen (A i) := fun F i hi ↦ by
    by_contra hnot
    exact hi (Or.inl hnot)
  have hemb : ∀ F : Finset ι, IsOpenEmbedding (inclusion R A (hS F)) := fun F ↦
    isOpenEmbedding_inclusion_principal_of_forall_mem (hS F) (hA_S F)
  let U : Finset ι → Set (Πʳ i, [R i, A i]) := fun F ↦ range (inclusion R A (hS F))
  have : ∀ F : Finset ι, SecondCountableTopology (U F) := fun F ↦
    (hemb F).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := U) (fun F ↦ (hemb F).isOpen_range) (eq_univ_iff_forall.mpr fun x ↦ ?_)
  have hx : {i | x i ∉ A i}.Finite := mem_cofinite.mp x.2
  refine mem_iUnion.mpr ⟨hx.toFinset, ?_⟩
  dsimp only [U]
  rw [range_inclusion, mem_ofPred_eq, eventually_principal]
  intro i hi
  by_contra hnot
  exact hi (Or.inr (hx.mem_toFinset.mpr hnot))

/-- A restricted product `Πʳ i, [R i, A i]` over a countable index type with second-countable
factors and open reference sets (`[Fact (∀ i, IsOpen (A i))]`) is second countable. -/
instance instSecondCountableTopology [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_of_cofinite (.of_forall hA.out)

end Principal

section Finite

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
variable [Finite ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]

/-- Over a finite index type, `Πʳ i, [R i, A i]` is second countable whenever every factor `R i`
is second countable, with no openness assumption on `A i`. -/
instance secondCountableTopology_of_finite :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_of_cofinite (eventually_cofinite.mpr (Set.toFinite _))

end Finite

end RestrictedProduct

namespace TauCeti

/-- Without cofinite openness of `A i`, a countable restricted product of compact metrizable
spaces need not even be first countable: for Cantor space `ℕ → Bool` with closed singleton
reference set `{fun _ ↦ false}` at every coordinate, `Πʳ _ : ℕ, [ℕ → Bool, {fun _ ↦ false}]` is
not first countable. -/
theorem not_firstCountableTopology_cantorSingleton :
    ¬ FirstCountableTopology
      (Πʳ _ : ℕ, [ℕ → Bool, ({fun _ ↦ false} : Set (ℕ → Bool))]) := by
  intro _
  let x₀ : Πʳ _ : ℕ, [ℕ → Bool, ({fun _ ↦ false} : Set (ℕ → Bool))] :=
    RestrictedProduct.mk (fun _ _ ↦ false) (.of_forall fun _ ↦ rfl)
  obtain ⟨U, hU⟩ := (𝓝 x₀).exists_antitone_basis
  let e : ℕ → ℕ → Bool := fun m k ↦ decide (k = m)
  have he : Tendsto e atTop (𝓝 (fun _ ↦ false)) := tendsto_pi_nhds.mpr fun k ↦
    tendsto_const_nhds.congr'
      (eventually_atTop.mpr ⟨k + 1, fun m hm ↦ by simp [e, Nat.ne_of_lt hm]⟩)
  have hn : ∀ n : ℕ, (cofinite : Filter ℕ) ≤ 𝓟 {n}ᶜ := fun n ↦
    le_principal_iff.mpr (Set.finite_singleton n).compl_mem_cofinite
  let f : ∀ n : ℕ, (ℕ → Bool) →
      Πʳ _ : ℕ, [ℕ → Bool, ({fun _ ↦ false} : Set (ℕ → Bool))]_[𝓟 {n}ᶜ] := fun n y ↦
    RestrictedProduct.mk (Function.update (fun _ _ ↦ false) n y)
      (eventually_principal.mpr fun k hk ↦ Function.update_of_ne hk _ _)
  let ins : ℕ → (ℕ → Bool) →
      Πʳ _ : ℕ, [ℕ → Bool, ({fun _ ↦ false} : Set (ℕ → Bool))] := fun n y ↦
    RestrictedProduct.inclusion _ _ (hn n) (f n y)
  have hex : ∀ n : ℕ, ∃ m : ℕ, ins n (e m) ∈ U n := fun n ↦ by
    have hf : Continuous (ins n) :=
      (RestrictedProduct.continuous_inclusion (hn n)).comp
        (RestrictedProduct.continuous_rng_of_principal.mpr
          (continuous_const.update n continuous_id))
    have h0 : ins n (fun _ ↦ false) = x₀ := by
      ext k j
      simp [ins, f, x₀]
    have hmem : ins n ⁻¹' U n ∈ 𝓝 (fun _ ↦ false) :=
      hf.continuousAt (by rw [h0]; exact hU.mem n)
    exact (he.eventually hmem).exists
  choose m hm using hex
  let C : ℕ → Set (ℕ → Bool) := fun n ↦ (fun y : ℕ → Bool ↦ y (m n)) ⁻¹' {false}
  have hCopen : IsOpen (RestrictedProduct.box C :
      Set (Πʳ _ : ℕ, [ℕ → Bool, ({fun _ ↦ false} : Set (ℕ → Bool))])) :=
    RestrictedProduct.isOpen_box
      (fun n ↦ (isOpen_discrete {false}).preimage (continuous_apply (m n)))
      (.of_forall fun _ _ hy ↦ by simp [C, mem_singleton_iff.mp hy])
  obtain ⟨n, hnU⟩ := hU.mem_iff.mp (hCopen.mem_nhds (by simp [C, x₀]))
  have hfalse : ins n (e (m n)) n (m n) = false :=
    RestrictedProduct.mem_box.mp (hnU (hm n)) n
  simp [ins, f, e] at hfalse

/-- Without cofinite openness of `A i`, `Πʳ _ : ℕ, [ℕ → Bool, {fun _ ↦ false}]` is not second
countable, showing that `hA : ∀ᶠ i in cofinite, IsOpen (A i)` in
`RestrictedProduct.secondCountableTopology_of_cofinite` cannot be dropped. -/
theorem not_secondCountableTopology_cantorSingleton :
    ¬ SecondCountableTopology
      (Πʳ _ : ℕ, [ℕ → Bool, ({fun _ ↦ false} : Set (ℕ → Bool))]) := fun _ ↦
  not_firstCountableTopology_cantorSingleton inferInstance

end TauCeti
