/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Fintype.Lattice
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic

/-!
# The length filtration of the strands algebra

The *length* of a strand diagram (`TauCeti.StrandDiagram.length`) is the number of points of `α`
passed by its strands, counted with multiplicity. It adds under concatenation and vanishes exactly
on the identity diagrams `I(S)`. The elements of the strands algebra supported on the diagrams of
length at least `k` form a filtration (`TauCeti.StrandsAlgebra.lengthFiltration`) with
`F_a F_b ⊆ F_{a+b}`. Since lengths are bounded, every element of `F_1`, which consists of the
elements with no identity diagram in their support, is nilpotent.

## Main definitions

* `TauCeti.StrandsAlgebra.lengthFiltration R k`: the elements supported on the diagrams of length
  at least `k`.

## Main results

* `TauCeti.StrandsAlgebra.mul_mem_lengthFiltration`: `F_a F_b ⊆ F_{a+b}`.
* `TauCeti.StrandsAlgebra.mem_lengthFiltration_one_iff`: `F_1` consists of the elements whose
  coefficients at the identity diagrams vanish.
* `TauCeti.StrandsAlgebra.isNilpotent_of_mem_lengthFiltration_one`: the elements of `F_1` are
  nilpotent.
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable (R : Type*) {α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- The part `F_k` of the length filtration of the strands algebra: the elements supported on the
strand diagrams of length at least `k`, that is, the image of `Finsupp.supported` under the basis
of strand diagrams. -/
def lengthFiltration (k : ℕ) : Submodule R (StrandsAlgebra R α) :=
  (Finsupp.supported R R {φ : StrandDiagram α | k ≤ φ.length}).map
    ((basis R α).repr.symm : (StrandDiagram α →₀ R) →ₗ[R] StrandsAlgebra R α)

variable {R}

/-- An element lies in `F_k` exactly when every strand diagram in its support has length at least
`k`. -/
theorem mem_lengthFiltration {k : ℕ} {x : StrandsAlgebra R α} :
    x ∈ lengthFiltration R k ↔ ∀ φ ∈ ((basis R α).repr x).support, k ≤ φ.length := by
  rw [lengthFiltration, Submodule.mem_map_equiv, LinearEquiv.symm_symm, Finsupp.mem_supported]
  rfl

/-- `F_k` is the span of the strand diagrams of length at least `k`. -/
theorem lengthFiltration_eq_span (k : ℕ) :
    lengthFiltration R k = Submodule.span R (of '' {φ : StrandDiagram α | k ≤ φ.length}) := by
  rw [lengthFiltration, Finsupp.supported_eq_span_single, Submodule.map_span, ← Set.image_comp]
  congr 2
  ext φ
  simp [← basis_apply]

/-- A strand diagram of length at least `k` lies in `F_k`. -/
theorem of_mem_lengthFiltration {k : ℕ} {φ : StrandDiagram α} (h : k ≤ φ.length) :
    (of φ : StrandsAlgebra R α) ∈ lengthFiltration R k := by
  rw [lengthFiltration_eq_span]
  exact Submodule.subset_span ⟨φ, h, rfl⟩

/-- Over a nontrivial ring, a strand diagram lies in `F_k` exactly when its length is at least
`k`. -/
@[simp]
theorem of_mem_lengthFiltration_iff [Nontrivial R] {k : ℕ} {φ : StrandDiagram α} :
    (of φ : StrandsAlgebra R α) ∈ lengthFiltration R k ↔ k ≤ φ.length := by
  refine ⟨fun h ↦ ?_, of_mem_lengthFiltration⟩
  rw [mem_lengthFiltration, ← basis_apply, Module.Basis.repr_self,
    Finsupp.support_single _ one_ne_zero] at h
  simpa using h

/-- The filtration starts with the whole strands algebra. -/
@[simp]
theorem lengthFiltration_zero : lengthFiltration R 0 = (⊤ : Submodule R (StrandsAlgebra R α)) :=
  eq_top_iff.2 fun _ _ ↦ mem_lengthFiltration.2 fun _ _ ↦ Nat.zero_le _

/-- The length filtration is decreasing. -/
theorem lengthFiltration_antitone :
    Antitone (lengthFiltration R : ℕ → Submodule R (StrandsAlgebra R α)) :=
  fun _ _ hkl _ hx ↦ mem_lengthFiltration.2 fun φ hφ ↦ hkl.trans (mem_lengthFiltration.1 hx φ hφ)

/-- An element lies in `F_1` exactly when its coefficients at the identity diagrams vanish. -/
theorem mem_lengthFiltration_one_iff {x : StrandsAlgebra R α} :
    x ∈ lengthFiltration R 1 ↔ ∀ s : Finset α, (basis R α).repr x (idOn s) = 0 := by
  rw [mem_lengthFiltration]
  refine ⟨fun h s ↦ ?_, fun h φ hφ ↦ one_le_length_iff.2 fun hφ' ↦ ?_⟩
  · by_contra hs
    simpa using h _ (Finsupp.mem_support_iff.2 hs)
  · exact Finsupp.mem_support_iff.1 hφ (hφ' ▸ h φ.source)

/-- **The strands algebra is filtered by length**: `F_a F_b ⊆ F_{a+b}`. -/
theorem mul_mem_lengthFiltration {a b : ℕ} {x y : StrandsAlgebra R α}
    (hx : x ∈ lengthFiltration R a) (hy : y ∈ lengthFiltration R b) :
    x * y ∈ lengthFiltration R (a + b) := by
  have hxy := Submodule.mul_mem_mul hx hy
  rw [lengthFiltration_eq_span, lengthFiltration_eq_span, Submodule.span_mul_span] at hxy
  refine Submodule.span_le.2 ?_ hxy
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, _, ⟨ψ, hψ, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe, of_mul_of]
  split_ifs with hφψ
  · refine of_mem_lengthFiltration ?_
    rw [length_trans hφψ.target_eq]
    exact Nat.add_le_add hφ hψ
  · exact zero_mem _

/-- The `n`-th power of an element of `F_1` lies in `F_n`. -/
theorem pow_mem_lengthFiltration {x : StrandsAlgebra R α} (hx : x ∈ lengthFiltration R 1)
    (n : ℕ) : x ^ n ∈ lengthFiltration R n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact mul_mem_lengthFiltration ih hx

/-- **The elements of `F_1` are nilpotent**: lengths of strand diagrams are bounded. -/
theorem isNilpotent_of_mem_lengthFiltration_one {x : StrandsAlgebra R α}
    (hx : x ∈ lengthFiltration R 1) : IsNilpotent x := by
  have : Nonempty (StrandDiagram α) := ⟨idOn ∅⟩
  obtain ⟨φ₀, hφ₀⟩ := Finite.exists_max (length : StrandDiagram α → ℕ)
  refine ⟨φ₀.length + 1, (basis R α).repr.injective (Finsupp.ext fun φ ↦ ?_)⟩
  by_contra hφ
  have := mem_lengthFiltration.1 (pow_mem_lengthFiltration hx (φ₀.length + 1)) φ
    (Finsupp.mem_support_iff.2 (by simpa using hφ))
  exact absurd (hφ₀ φ) (by omega)

end StrandsAlgebra

end TauCeti
