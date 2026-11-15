/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Lattice
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic

/-!
# Weight and coweight lattices of a rational realization

Let `R` be a rational realization of an integral matrix `A`, with simple coroots `hᵢ ∈ H` and
simple roots `αᵢ ∈ H*`. A coweight lattice of `R` is a full `ℤ`-lattice `Y ⊆ H` containing every
`hᵢ` on which every `αᵢ` takes integral values. Its weight lattice `P ⊆ H*` is the integral dual
of `Y`, so it contains every `αᵢ`. The evaluation pairing `P × Y → ℤ` is perfect, and on the
simple roots and coroots it recovers the matrix: `⟨αⱼ, hᵢ⟩ = aᵢⱼ`. The roots and coroots stay
linearly independent over `ℤ` in `P` and `Y`. These lattices are the integral input of the
Kac–Moody algebra's weight theory and of the quantized enveloping algebra of the full lattice
pair, where `Y` carries the toral generators.

A coweight lattice is extra data, not determined by the realization: in type `A₁` with
`H = ℚ h`, both `ℤ h` and `ℤ (h / 2)` are coweight lattices. The fundamental weights, functionals
`ωᵢ` with `ωᵢ(hⱼ) = δᵢⱼ`, always exist in `H*` because the coroots are independent, but they lie
in `P` only for some choices of `Y`: for `ℤ h` they do, while for `ℤ (h / 2)` the weight lattice
is `ℤ α` and every weight takes an even value on `h`. Lattices with fundamental weights are those
for which the coroot coordinates `P → ℤ^I`, `λ ↦ (λ(hᵢ))ᵢ`, are surjective. Every rational
realization on a finite-dimensional space admits such a coweight lattice.

## Main definitions

* `TauCeti.CartanRealization.CoweightLattice`: a coweight lattice of a rational realization.
* `TauCeti.CartanRealization.CoweightLattice.weightLattice`: its weight lattice, the integral
  dual.
* `TauCeti.CartanRealization.CoweightLattice.pairing`: the integral pairing `P × Y → ℤ`.
* `TauCeti.CartanRealization.CoweightLattice.root`,
  `TauCeti.CartanRealization.CoweightLattice.coroot`: the simple roots and coroots as elements
  of the two lattices.
* `TauCeti.CartanRealization.CoweightLattice.corootCoordinates`: the map `λ ↦ (λ(hᵢ))ᵢ`.
* `TauCeti.CartanRealization.CoweightLattice.HasFundamentalWeights`: the weight lattice
  contains fundamental weights.
* `TauCeti.CartanRealization.CoweightLattice.ofBasis`: the coweight lattice spanned by a basis.

## Main results

* `TauCeti.CartanRealization.CoweightLattice.isPerfPair_pairing`: the pairing is perfect.
* `TauCeti.CartanRealization.CoweightLattice.pairing_root_coroot`: `⟨αⱼ, hᵢ⟩ = aᵢⱼ` in `ℤ`.
* `TauCeti.CartanRealization.CoweightLattice.linearIndependent_root`,
  `TauCeti.CartanRealization.CoweightLattice.linearIndependent_coroot`: integral independence.
* `TauCeti.CartanRealization.CoweightLattice.hasFundamentalWeights_iff_surjective`: fundamental
  weights exist exactly when the coroot coordinates are surjective.
* `TauCeti.CartanRealization.exists_hasFundamentalWeights`: every rational realization on a
  finite-dimensional space has a coweight lattice with fundamental weights.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1 (realizations) and §6.1
  (the lattice `P` of integral weights).
* G. Lusztig, *Introduction to Quantum Groups*, §2.2 (root data and their lattices).
-/

public section

open Module

namespace TauCeti

namespace CartanRealization

variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {A : Matrix I I ℤ}

/-- A **coweight lattice** of a rational realization of an integral matrix: a full `ℤ`-lattice of
the ambient space containing every simple coroot, on which every simple root takes integral
values. Its integral dual is the weight lattice
`TauCeti.CartanRealization.CoweightLattice.weightLattice`. -/
structure CoweightLattice (R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H) where
  /-- The coweight lattice, as a `ℤ`-submodule of the ambient space. -/
  lattice : Submodule ℤ H
  [isLattice : lattice.IsLattice ℚ]
  /-- Every simple coroot is a coweight. -/
  coroot_mem (i : I) : R.coroot i ∈ lattice
  /-- Every simple root is integral on the coweight lattice. -/
  root_mem_dualLattice (i : I) : R.root i ∈ lattice.dualLattice ℚ

namespace CoweightLattice

attribute [instance] isLattice

variable {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H} (L : R.CoweightLattice)

/-- A coweight lattice is determined by its underlying submodule. -/
@[ext]
theorem ext {L' : R.CoweightLattice} (h : L.lattice = L'.lattice) : L = L' := by
  cases L
  cases L'
  congr

/-! ### The weight lattice and the pairing -/

/-- The **weight lattice** `P`: the functionals taking integral values on the coweight lattice. -/
def weightLattice : Submodule ℤ (Dual ℚ H) :=
  L.lattice.dualLattice ℚ

theorem weightLattice_def : L.weightLattice = L.lattice.dualLattice ℚ := (rfl)

/-- A weight is a functional taking integral values on every coweight. -/
theorem mem_weightLattice_iff (φ : Dual ℚ H) :
    φ ∈ L.weightLattice ↔ ∀ y ∈ L.lattice, ∃ n : ℤ, (n : ℚ) = φ y := by
  simp [weightLattice, Submodule.mem_one]

/-- The weight lattice is a full lattice in the dual space. -/
instance isLattice_weightLattice : L.weightLattice.IsLattice ℚ :=
  Submodule.isLattice_dualLattice L.lattice

/-- The integral pairing `⟨λ, y⟩` between weights and coweights. -/
noncomputable def pairing : L.weightLattice →ₗ[ℤ] L.lattice →ₗ[ℤ] ℤ :=
  L.lattice.dualLatticePairing ℚ

/-- The integral pairing is evaluation. -/
@[simp, norm_cast]
theorem cast_pairing (φ : L.weightLattice) (y : L.lattice) :
    (L.pairing φ y : ℚ) = (φ : Dual ℚ H) y :=
  L.lattice.algebraMap_dualLatticePairing φ y

/-- **The weight and coweight lattices are in perfect duality.** -/
instance isPerfPair_pairing : L.pairing.IsPerfPair :=
  Submodule.isPerfPair_dualLatticePairing L.lattice

/-! ### Simple roots and coroots -/

/-- The simple root `αᵢ` as a weight. -/
def root (i : I) : L.weightLattice :=
  ⟨R.root i, L.root_mem_dualLattice i⟩

/-- The simple coroot `hᵢ` as a coweight. -/
def coroot (i : I) : L.lattice :=
  ⟨R.coroot i, L.coroot_mem i⟩

@[simp]
theorem coe_root (i : I) : (L.root i : Dual ℚ H) = R.root i := (rfl)

@[simp]
theorem coe_coroot (i : I) : (L.coroot i : H) = R.coroot i := (rfl)

/-- The integral pairing of the simple roots and coroots is the matrix: `⟨αⱼ, hᵢ⟩ = aᵢⱼ`. -/
@[simp]
theorem pairing_root_coroot (i j : I) : L.pairing (L.root j) (L.coroot i) = A i j := by
  have h := L.cast_pairing (L.root j) (L.coroot i)
  rw [coe_root, coe_coroot, R.root_coroot, Matrix.map_apply] at h
  exact_mod_cast h

/-- The simple roots remain linearly independent over `ℤ` in the weight lattice. -/
theorem linearIndependent_root : LinearIndependent ℤ L.root :=
  LinearIndependent.of_comp L.weightLattice.subtype
    (R.root_linearIndependent.restrict_scalars' ℤ)

/-- The simple coroots remain linearly independent over `ℤ` in the coweight lattice. -/
theorem linearIndependent_coroot : LinearIndependent ℤ L.coroot :=
  LinearIndependent.of_comp L.lattice.subtype (R.coroot_linearIndependent.restrict_scalars' ℤ)

/-! ### Fundamental weights -/

/-- The coroot coordinates `λ ↦ (⟨λ, hᵢ⟩)ᵢ` of a weight. -/
noncomputable def corootCoordinates : L.weightLattice →ₗ[ℤ] (I → ℤ) :=
  LinearMap.pi fun i ↦ L.pairing.flip (L.coroot i)

@[simp]
theorem corootCoordinates_apply (φ : L.weightLattice) (i : I) :
    L.corootCoordinates φ i = L.pairing φ (L.coroot i) := (rfl)

/-- The weight lattice **has fundamental weights** if it contains weights `ωᵢ` with
`⟨ωᵢ, hⱼ⟩ = δᵢⱼ`. -/
def HasFundamentalWeights [DecidableEq I] : Prop :=
  ∃ ω : I → L.weightLattice, ∀ i, L.corootCoordinates (ω i) = Pi.single i 1

/-- Fundamental weights exist exactly when every integer vector is the coroot coordinate vector
of a weight. -/
theorem hasFundamentalWeights_iff_surjective [Finite I] [DecidableEq I] :
    L.HasFundamentalWeights ↔ Function.Surjective L.corootCoordinates := by
  have := Fintype.ofFinite I
  refine ⟨fun ⟨ω, hω⟩ c ↦ ⟨∑ i, c i • ω i, ?_⟩, fun h ↦ ?_⟩
  · simp only [map_sum, map_zsmul, hω]
    ext j
    simp [Pi.single_apply]
  · choose ω hω using fun i : I ↦ h (Pi.single i 1)
    exact ⟨ω, hω⟩

/-! ### Lattices spanned by bases -/

section OfBasis

variable {κ : Type*} [Finite κ] (b : Basis κ ℚ H)
  (hcoroot : ∀ i, R.coroot i ∈ Submodule.span ℤ (Set.range b))
  (hroot : ∀ i k, ∃ m : ℤ, (m : ℚ) = R.root i (b k))

/-- The coweight lattice spanned by a basis of the ambient space, when the span contains every
simple coroot and every simple root is integral on the basis. -/
noncomputable def ofBasis : R.CoweightLattice where
  lattice := Submodule.span ℤ (Set.range b)
  isLattice := Submodule.isLattice_span (Set.finite_range b) b.span_eq
  coroot_mem := hcoroot
  root_mem_dualLattice i := (Submodule.mem_dualLattice_span_iff _ _).mpr <| by
    rintro _ ⟨k, rfl⟩
    exact Submodule.mem_one.mpr (hroot i k)

/-- The lattice of `ofBasis` is the span of the basis. -/
@[simp]
theorem lattice_ofBasis : (ofBasis b hcoroot hroot).lattice = Submodule.span ℤ (Set.range b) :=
  (rfl)

/-- The dual basis spans the weight lattice of a lattice spanned by a basis. -/
theorem weightLattice_ofBasis [DecidableEq κ] :
    (ofBasis b hcoroot hroot).weightLattice = Submodule.span ℤ (Set.range b.dualBasis) :=
  b.dualLattice_span

/-- If the simple coroots are basis vectors, then the dual basis vectors at them are fundamental
weights. -/
theorem hasFundamentalWeights_ofBasis [DecidableEq I] (f : I → κ)
    (hf : ∀ i, b (f i) = R.coroot i) : (ofBasis b hcoroot hroot).HasFundamentalWeights := by
  classical
  have hω (i : I) : b.dualBasis (f i) ∈ (ofBasis b hcoroot hroot).weightLattice := by
    rw [weightLattice_ofBasis]
    exact Submodule.subset_span ⟨f i, rfl⟩
  have hfinj : Function.Injective f := fun i j h ↦
    R.coroot_linearIndependent.injective (by rw [← hf, ← hf, h])
  refine ⟨fun i ↦ ⟨_, hω i⟩, fun i ↦ funext fun j ↦ Int.cast_injective (α := ℚ) ?_⟩
  simp [← hf, Pi.single_apply, Finsupp.single_apply, hfinj.eq_iff, eq_comm]

end OfBasis

end CoweightLattice

/-! ### Existence -/

/-- **Every rational realization on a finite-dimensional space has a coweight lattice with
fundamental weights.** -/
theorem exists_hasFundamentalWeights [Finite I] [DecidableEq I] [FiniteDimensional ℚ H]
    (R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H) :
    ∃ L : R.CoweightLattice, L.HasFundamentalWeights := by
  -- Extend the simple coroots by a basis of a complement of their span, scaled to make every
  -- simple root integral on it, and take the lattice spanned by the resulting basis.
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Submodule.span ℚ (Set.range R.coroot))
  let c₀ := Module.finBasis ℚ W
  -- A common denominator `n` for the values of the simple roots on `c₀`.
  obtain ⟨⟨n, hn⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) fun p : I × Fin (finrank ℚ W) ↦ R.root p.1 (c₀ p.2)
  have hn₀ : (n : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hn
  let c := c₀.unitsSMul fun _ ↦ Units.mk0 _ hn₀
  let v : I ⊕ Fin (finrank ℚ W) → H := Sum.elim R.coroot (W.subtype ∘ c)
  have hspan : Submodule.span ℚ (Set.range (W.subtype ∘ c)) = W := by
    rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli : LinearIndependent ℚ v := by
    refine R.coroot_linearIndependent.sum_type (c.linearIndependent.map' W.subtype W.ker_subtype)
      ?_
    rw [hspan]
    exact hW.disjoint
  let b : Basis (I ⊕ Fin (finrank ℚ W)) ℚ H := Basis.mk hli <| by
    rw [Set.Sum.elim_range, Submodule.span_union, hspan]
    exact hW.sup_eq_top.ge
  have hb (p) : b p = v p := Basis.mk_apply hli _ p
  have hroot (j : I) : ∀ p, ∃ m : ℤ, (m : ℚ) = R.root j (b p)
    | .inl i => ⟨A i j, by simp [hb, v]⟩
    | .inr k => by
      obtain ⟨m, hm⟩ := hint (j, k)
      exact ⟨m, by simpa [hb, v, c, Basis.unitsSMul_apply] using hm⟩
  exact ⟨_, CoweightLattice.hasFundamentalWeights_ofBasis b
    (fun i ↦ Submodule.subset_span ⟨.inl i, hb _⟩) hroot Sum.inl fun i ↦ hb (.inl i)⟩

/-- Every rational realization on a finite-dimensional space admits a coweight lattice. -/
instance [Finite I] [FiniteDimensional ℚ H] (R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H) :
    Nonempty R.CoweightLattice := by
  classical
  exact (exists_hasFundamentalWeights R).nonempty

end CartanRealization

end TauCeti
