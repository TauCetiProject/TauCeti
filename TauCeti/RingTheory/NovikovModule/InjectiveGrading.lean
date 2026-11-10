/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.Algebra.Torsor.Sigma

/-!
# Completed combinations with an injective grading shift

Let the generators be a finite union `Σ i, P i` of torsors under a group `H`, graded by a degree
`d` with `d (h +ᵥ p) = δ h + d p` for a homomorphism `δ : H →+ D`. The file
`TauCeti.RingTheory.NovikovModule.Residue` treats the case `δ = 0`, where the degree is constant on
orbits. This file treats the opposite case of an *injective* `δ`. Then each orbit meets each
degree at most once (`TauCeti.AddTorsor.finite_setOf_sigma_eq`), with three consequences.

* Homogeneous completed combinations are finite combinations
  (`NovikovModule.mem_range_ofFinsupp_of_mem_gradeBy`).
* A kernel with a fixed degree shift has finitely many nonzero entries in each row
  (`NovikovModule.finite_support_kernel_of_eq_add`,
  `NovikovModule.finite_support_productKernel_of_eq_add_add`). This is the hypothesis `hmfin`
  of `TauCeti.NovikovModule.kernelMap` (and `hfin` of `TauCeti.NovikovModule.kernelProduct`),
  and by `NovikovModule.kernelMap_ofFinsupp_mem_range` and
  `NovikovModule.kernelProduct_ofFinsupp_mem_range` such a kernel preserves finite
  combinations, so its map and product are already defined before completion.
* If the potentials `F` are equivariant, `F (h +ᵥ p) = F p - N h`, then the potential change
  `F₀ p₀ - F₁ p₁` is bounded over *all* pairs of generators with a fixed degree difference
  (`NovikovModule.exists_abs_sub_le_of_eq_add`), and likewise
  `F₀ p₀ - (F₁ p₁ + F₂ p₂)` over triples with `d₀ p₀ = d₁ p₁ + d₂ p₂ + ε`
  (`NovikovModule.exists_abs_sub_add_le_of_eq_add_add`). In particular such a kernel satisfies
  the potential bound of `TauCeti.NovikovModule.kernelMap` with a constant depending only on its
  degree shift.

In capped Hamiltonian Floer theory on a spherically monotone target, recapping by a class `γ` of
the period group shifts the Conley–Zehnder grading by `2 c₁(γ)`, and `2 c₁` is injective on the
period group. The kernels of the Floer differential, continuation maps, chain homotopies and the
pair-of-pants product have fixed degree shifts given by the index of the rigid or one-parameter
moduli spaces they count. The results above then say that the support hypotheses of the kernel
constructions follow from the index alone: the action change, and hence the energy, of every
configuration counted by such a kernel is bounded independently of its class, and each row of
the kernel involves only finitely many classes. This is the finite Laurent model of the monotone
case. If instead the first Chern class vanishes on spheres while the area does not, `δ = 0` on a
nontrivial group and the index gives no such bound.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611, for the monotone case, in which the index of a Floer trajectory determines its energy.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

namespace TauCeti.NovikovModule

open Function Set

variable {R H D : Type*} [AddGroup H]

section Homogeneous

variable [Semiring R] [AddGroup D] {δ : H →+ D} {ι : Type*} [Finite ι] {P : ι → Type*}
  [∀ i, AddTorsor H (P i)] {F : (Σ i, P i) → ℝ} {d : (Σ i, P i) → D}

/-- If the degree shift `δ` of a finite union of torsors is injective, every homogeneous
completed combination is a finite combination: it has at most one nonzero coefficient in each
orbit. -/
theorem mem_range_ofFinsupp_of_mem_gradeBy
    (hd : ∀ i (h : H) (p : P i), d ⟨i, h +ᵥ p⟩ = δ h + d ⟨i, p⟩) (hδ : Injective δ) {k : D}
    {a : NovikovModule R F} (ha : a ∈ gradeBy R F d k) :
    a ∈ LinearMap.range (ofFinsupp F) :=
  mem_range_ofFinsupp_iff.2 ((AddTorsor.finite_setOf_sigma_eq hd hδ k).subset
    fun s hs => mem_gradeBy_iff.1 ha s hs)

end Homogeneous

section Kernel

variable [Zero R] [AddGroup D] {δ : H →+ D} {ι₀ : Type*} [Finite ι₀] {P₀ : ι₀ → Type*}
  [∀ k, AddTorsor H (P₀ k)] {d₀ : (Σ k, P₀ k) → D}
  (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩) (hδ : Injective δ)
include hd₀ hδ

/-- If the degree shift of the output generators is injective, a kernel with a fixed degree
shift `ε` has only finitely many nonzero entries in each row. -/
theorem finite_support_kernel_of_eq_add {S₁ : Type*} {d₁ : S₁ → D} {ε : D}
    {m : S₁ → (Σ k, P₀ k) → R} (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + ε) (p₁ : S₁) :
    (support (m p₁)).Finite :=
  (AddTorsor.finite_setOf_sigma_eq hd₀ hδ (d₁ p₁ + ε)).subset fun p₀ hp₀ => hm p₁ p₀ hp₀

/-- If the degree shift of the output generators is injective, a product kernel with a fixed
degree shift `ε` has only finitely many nonzero outputs at each pair of inputs. -/
theorem finite_support_productKernel_of_eq_add_add {S₁ S₂ : Type*} {d₁ : S₁ → D}
    {d₂ : S₂ → D} {ε : D} {n : S₁ → S₂ → (Σ k, P₀ k) → R}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂ + ε) (p₁ : S₁) (p₂ : S₂) :
    (support (n p₁ p₂)).Finite :=
  (AddTorsor.finite_setOf_sigma_eq hd₀ hδ (d₁ p₁ + d₂ p₂ + ε)).subset
    fun p₀ hp₀ => hn p₁ p₂ p₀ hp₀

end Kernel

section Potential

variable {N : H →+ ℝ}

/-- A potential `F (h +ᵥ p) = F p - N h` shifts under translation by the homomorphism `-N`. -/
private theorem neg_apply_add_of_sub {ι : Type*} {P : ι → Type*} [∀ i, AddTorsor H (P i)]
    {F : (Σ i, P i) → ℝ} (hF : ∀ i (h : H) (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
    (i : ι) (h : H) (p : P i) : F ⟨i, h +ᵥ p⟩ = (-N) h + F ⟨i, p⟩ := by
  rw [hF, AddMonoidHom.neg_apply, sub_eq_neg_add]

variable {ι₁ ι₀ : Type*} [Finite ι₁] [Finite ι₀] {P₁ : ι₁ → Type*}
  {P₀ : ι₀ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i (h : H) (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₀ : ∀ k (h : H) (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
include hF₁ hF₀

/-- If the degree shift `δ` is injective, the potential change `F₀ p₀ - F₁ p₁` is bounded over all
pairs of generators of two finite unions of torsors with a fixed degree difference
`d₀ p₀ = d₁ p₁ + ε`. In particular a kernel with degree shift `ε` obeys a potential bound
`F₀ p₀ ≤ F₁ p₁ + C`, as required by `TauCeti.NovikovModule.kernelMap`. -/
theorem exists_abs_sub_le_of_eq_add [AddGroup D] {δ : H →+ D} {d₁ : (Σ i, P₁ i) → D}
    {d₀ : (Σ k, P₀ k) → D}
    (hd₁ : ∀ i (h : H) (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
    (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)
    (hδ : Injective δ) (ε : D) :
    ∃ C, ∀ p₁ p₀, d₀ p₀ = d₁ p₁ + ε → |F₀ p₀ - F₁ p₁| ≤ C := by
  obtain ⟨C, hC⟩ := ((AddTorsor.finite_image_sub_setOf_eq_add (neg_apply_add_of_sub hF₁)
    (neg_apply_add_of_sub hF₀) hd₁ hd₀ hδ ε).image abs).bddAbove
  exact ⟨C, fun p₁ p₀ h => hC ⟨_, ⟨(p₁, p₀), h, rfl⟩, rfl⟩⟩

/-- If the degree shift `δ` is injective, the potential change `F₀ p₀ - (F₁ p₁ + F₂ p₂)` is
bounded over all triples of generators of three finite unions of torsors with
`d₀ p₀ = d₁ p₁ + d₂ p₂ + ε`. In particular a product kernel with degree shift `ε` obeys a
potential bound `F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C`, as required by
`TauCeti.NovikovModule.kernelProduct`. -/
theorem exists_abs_sub_add_le_of_eq_add_add [AddCommGroup D] {δ : H →+ D} {ι₂ : Type*} [Finite ι₂]
    {P₂ : ι₂ → Type*} [∀ j, AddTorsor H (P₂ j)] {F₂ : (Σ j, P₂ j) → ℝ}
    (hF₂ : ∀ j (h : H) (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
    {d₁ : (Σ i, P₁ i) → D} {d₂ : (Σ j, P₂ j) → D} {d₀ : (Σ k, P₀ k) → D}
    (hd₁ : ∀ i (h : H) (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
    (hd₂ : ∀ j (h : H) (p : P₂ j), d₂ ⟨j, h +ᵥ p⟩ = δ h + d₂ ⟨j, p⟩)
    (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)
    (hδ : Injective δ) (ε : D) :
    ∃ C, ∀ p₁ p₂ p₀, d₀ p₀ = d₁ p₁ + d₂ p₂ + ε → |F₀ p₀ - (F₁ p₁ + F₂ p₂)| ≤ C := by
  obtain ⟨C, hC⟩ := ((AddTorsor.finite_image_sub_add_setOf_eq_add_add
    (neg_apply_add_of_sub hF₁) (neg_apply_add_of_sub hF₂) (neg_apply_add_of_sub hF₀)
    hd₁ hd₂ hd₀ hδ ε).image abs).bddAbove
  exact ⟨C, fun p₁ p₂ p₀ h => hC ⟨_, ⟨((p₁, p₂), p₀), h, rfl⟩, rfl⟩⟩

end Potential

end TauCeti.NovikovModule
