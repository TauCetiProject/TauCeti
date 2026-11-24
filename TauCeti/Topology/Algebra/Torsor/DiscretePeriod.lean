/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Discrete and dense degree-zero periods of torsors

Let `N : H →+ ℝ` and `δ : H →+ D` be jointly injective homomorphisms, `Disjoint N.ker δ.ker`,
thought of as a period and a degree. The subgroup `N (ker δ)` of `ℝ` of *degree-zero periods*
controls how many elements of a fixed degree have period in a bounded window.

* If the degree-zero periods are discrete, only finitely many elements of `H` of a given degree
  have period in a bounded window (`TauCeti.AddTorsor.finite_setOf_eq_and_mem_Icc`). The same
  holds on a finite union `Σ k, P k` of torsors under `H` for a potential and a degree shifted by
  `N` and `δ` (`TauCeti.AddTorsor.finite_setOf_sigma_eq_and_mem_Icc`).
* If the degree-zero periods are dense, every open interval contains the periods of infinitely
  many elements of degree zero (`TauCeti.AddTorsor.infinite_setOf_eq_zero_and_mem_Ioo`).
-/

public section

namespace TauCeti

open Set

variable {H D : Type*} [AddGroup H] [AddGroup D] {N : H →+ ℝ} {δ : H →+ D}

namespace AddTorsor

/-- If `N` and `δ` are jointly injective and the degree-zero periods `N (ker δ)` are discrete,
only finitely many elements of a given degree `e` have period in a bounded window. -/
theorem finite_setOf_eq_and_mem_Icc (hNδ : Disjoint N.ker δ.ker)
    (hdisc : DiscreteTopology (δ.ker.map N)) (e : D) (a b : ℝ) :
    {h : H | δ h = e ∧ N h ∈ Icc a b}.Finite := by
  rcases eq_empty_or_nonempty {h : H | δ h = e ∧ N h ∈ Icc a b} with hs | ⟨h₀, he₀, -⟩
  · rw [hs]
    exact finite_empty
  have hinj : InjOn N {h : H | δ h = e ∧ N h ∈ Icc a b} := by
    intro h hh h' hh' hN
    have hmem : h - h' ∈ N.ker ⊓ δ.ker :=
      ⟨by simp [hN], by simp [hh.1, hh'.1]⟩
    rw [hNδ.eq_bot, AddSubgroup.mem_bot] at hmem
    exact sub_eq_zero.1 hmem
  have hK : (Icc (a - N h₀) (b - N h₀) ∩ ((δ.ker.map N : AddSubgroup ℝ) : Set ℝ)).Finite :=
    Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.2 hdisc)
      (Metric.isBounded_Icc _ _) AddSubgroup.isClosed_of_discreteTopology
  refine Finite.of_finite_image ((hK.image (· + N h₀)).subset ?_) hinj
  rintro _ ⟨h, ⟨hδ, hmem⟩, rfl⟩
  refine ⟨N h - N h₀, ⟨⟨by linarith [hmem.1], by linarith [hmem.2]⟩,
    ⟨h - h₀, by simp [AddMonoidHom.mem_ker, hδ, he₀], by simp⟩⟩, sub_add_cancel _ _⟩

/-- If the degree-zero periods `N (ker δ)` are dense in `ℝ`, every open interval contains the
periods of infinitely many elements of degree zero. -/
theorem infinite_setOf_eq_zero_and_mem_Ioo (hdense : Dense ((δ.ker.map N : AddSubgroup ℝ) : Set ℝ))
    {a b : ℝ} (hab : a < b) : {h : H | δ h = 0 ∧ N h ∈ Ioo a b}.Infinite := by
  have hK : (((δ.ker.map N : AddSubgroup ℝ) : Set ℝ) ∩ Ioo a b).Infinite := fun hfin => by
    obtain ⟨x, hx, hxK⟩ :=
      (hdense.sdiff_finite hfin).inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.2 hab)
    exact hxK.2 ⟨hxK.1, hx⟩
  refine Infinite.of_image N (hK.mono ?_)
  rintro _ ⟨⟨h, hh, rfl⟩, hmem⟩
  exact ⟨h, ⟨hh, hmem⟩, rfl⟩

variable {ι : Type*} {P : ι → Type*} [∀ k, AddTorsor H (P k)] {F : (Σ k, P k) → ℝ}
  {d : (Σ k, P k) → D}

/-- On a finite union of torsors with potential `F` and degree `d` shifted by jointly injective
homomorphisms `N` and `δ` with discrete degree-zero periods, only finitely many generators of a
given degree have potential in a bounded window. -/
theorem finite_setOf_sigma_eq_and_mem_Icc [Finite ι]
    (hF : ∀ k (h : H) (p : P k), F ⟨k, h +ᵥ p⟩ = N h + F ⟨k, p⟩)
    (hd : ∀ k (h : H) (p : P k), d ⟨k, h +ᵥ p⟩ = δ h + d ⟨k, p⟩) (hNδ : Disjoint N.ker δ.ker)
    (hdisc : DiscreteTopology (δ.ker.map N)) (e : D) (a b : ℝ) :
    {p | d p = e ∧ F p ∈ Icc a b}.Finite := by
  let r := fun k => Classical.arbitrary (P k)
  refine (finite_iUnion fun k => (finite_setOf_eq_and_mem_Icc hNδ hdisc (e - d ⟨k, r k⟩)
    (a - F ⟨k, r k⟩) (b - F ⟨k, r k⟩)).image
      fun h => (⟨k, h +ᵥ r k⟩ : Σ k, P k)).subset ?_
  rintro ⟨k, p⟩ ⟨hdp, hFp⟩
  have hdk := hd k (p -ᵥ r k) (r k)
  have hFk := hF k (p -ᵥ r k) (r k)
  rw [vsub_vadd] at hdk hFk
  refine mem_iUnion.2 ⟨k, p -ᵥ r k, ⟨?_, ?_, ?_⟩, by simp⟩
  · rw [eq_sub_iff_add_eq, ← hdk, hdp]
  · linarith [hFp.1]
  · linarith [hFp.2]

end AddTorsor

end TauCeti
