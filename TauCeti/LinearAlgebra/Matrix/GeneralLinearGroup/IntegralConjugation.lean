/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Conjugations preserving the integral matrices over a valuation ring

Let `O` be a valuation ring with fraction field `K`, and let `a ∈ GL_n(K)`. If conjugation by `a`
carries every member of a family `T` spanning `M_n(O)` into `M_n(O)`, then `a` is a scalar
multiple of an element of `GL_n(O)`: `a = α • b` with `α ∈ Kˣ` and `b ∈ GL_n(O)`. In terms of
lattices: the lattice `a Oⁿ` is a homothetic copy `α Oⁿ` of the standard lattice. So a lattice
in `Kⁿ` stable under a family that spans `M_n(O)` on the standard lattice is unique up to
homothety.

The proof: conjugation by `a` then preserves all of `M_n(O)`, so every product
`(a⁻¹)_{p,i} a_{j,q}` lies in `O` (it is an entry of `a⁻¹ E_{ij} a`). Pick an entry `α` of `a` of
largest valuation. Then `α⁻¹ a` has integral entries because `α` dominates every entry of `a`,
and `α a⁻¹` has integral entries by the products above. These two integral matrices are mutually
inverse.

## Main results

* `Matrix.GeneralLinearGroup.exists_eq_smul_map_of_span_eq_top`: a conjugation preserving the
  integrality of a spanning family of `M_n(O)` is a scalar times an element of `GL_n(O)`.

## Provenance

Adapted from `New.Selmer.exists_eq_smul_of_conj_eq` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), stated there
for rings of integers of finite extensions of `ℚ_ℓ` in an algebraic closure, using norms;
here for an arbitrary valuation ring and its valuation.
-/

public section

open Function Submodule

namespace Matrix.GeneralLinearGroup

variable {O K ι n : Type*} [CommRing O] [Field K] [Algebra O K] [Fintype n] [DecidableEq n]

/-- If conjugation by `a` maps every `T i` into `M_n(O)` and the `T i` span `M_n(O)`, then it maps
all of `M_n(O)` into `M_n(O)`. -/
private theorem conj_mem_range_of_span_eq_top {T : ι → Matrix n n O}
    (hT : span O (Set.range T) = ⊤) (a : GL n K)
    (h : ∀ i, (a⁻¹ : GL n K) * (T i).map (algebraMap O K) * a ∈
      Set.range (Matrix.map · (algebraMap O K)))
    (x : Matrix n n O) :
    (a⁻¹ : GL n K) * x.map (algebraMap O K) * a ∈ Set.range (Matrix.map · (algebraMap O K)) := by
  let φ := (Algebra.ofId O K).mapMatrix (m := n)
  let L : Matrix n n O →ₗ[O] Matrix n n K :=
    LinearMap.mulLeft O (a⁻¹ : GL n K).val ∘ₗ LinearMap.mulRight O a.val ∘ₗ φ.toLinearMap
  have hφ (y : Matrix n n O) : φ y = y.map (algebraMap O K) := rfl
  have hL (y : Matrix n n O) : L y = (a⁻¹ : GL n K) * y.map (algebraMap O K) * a := by
    simp [L, hφ, mul_assoc]
  have hle : span O (Set.range T) ≤ (Subalgebra.toSubmodule φ.range).comap L := by
    refine span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hy⟩ := h i
    exact ⟨y, by simpa [hφ, hL] using hy⟩
  obtain ⟨y, hy⟩ := (hT ▸ hle) (mem_top (x := x))
  exact ⟨y, by simpa [hφ, hL] using hy⟩

/-- **A conjugation preserving the integrality of a spanning family is integral up to a scalar.**
Let `O` be a valuation ring with fraction field `K`, let the matrices `T i` span `M_n(O)`, and let
`a ∈ GL_n(K)` conjugate every `T i` into `M_n(O)`. Then `a = α • b` for a unit `α` of `K` and some
`b ∈ GL_n(O)`; equivalently, the lattice `a Oⁿ` is the homothetic copy `α Oⁿ` of `Oⁿ`. -/
theorem exists_eq_smul_map_of_span_eq_top [IsDomain O] [ValuationRing O] [IsFractionRing O K]
    {T : ι → Matrix n n O} (hT : span O (Set.range T) = ⊤) (a : GL n K)
    (h : ∀ i, (a⁻¹ : GL n K) * (T i).map (algebraMap O K) * a ∈
      Set.range (Matrix.map · (algebraMap O K))) :
    ∃ (α : Kˣ) (b : GL n O),
      (a : Matrix n n K) = (α : K) • (b : Matrix n n O).map (algebraMap O K) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  have hinj : Injective (algebraMap O K) := IsFractionRing.injective O K
  let v := ValuationRing.valuation O K
  have hint (x : K) (hx : v x ≤ 1) : ∃ b : O, algebraMap O K b = x :=
    (ValuationRing.mem_integer_iff O K x).mp hx
  -- Every product `(a⁻¹)_{p,i} a_{j,q}` is integral: it is an entry of `a⁻¹ E_{ij} a`.
  have hprod (p i j q : n) : ∃ b : O, algebraMap O K b = (a⁻¹ : GL n K) p i * a j q := by
    obtain ⟨y, hy⟩ := conj_mem_range_of_span_eq_top hT a h (single i j 1)
    refine ⟨y p q, ?_⟩
    simpa [Matrix.mul_apply, single_apply, ite_and] using congrFun₂ hy p q
  -- An entry `α` of `a` of largest valuation dominates all the entries of `a`.
  obtain ⟨⟨j, q⟩, hmax⟩ := Finite.exists_max fun x : n × n ↦ v (a x.1 x.2)
  have hα : (a : Matrix n n K) j q ≠ 0 := fun h0 ↦
    a.ne_zero (Matrix.ext fun u w ↦ by simpa [h0] using hmax (u, w))
  set α := (a : Matrix n n K) j q
  -- The entries of `α⁻¹ a` and of `α a⁻¹` are integral.
  have hk (u w : n) : ∃ b : O, algebraMap O K b = α⁻¹ * a u w := by
    refine hint _ ?_
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (v.pos_iff.mpr hα), mul_one]
    exact hmax (u, w)
  have hk' (u w : n) : ∃ b : O, algebraMap O K b = α * (a⁻¹ : GL n K) u w := by
    obtain ⟨b, hb⟩ := hprod u w j q
    exact ⟨b, by rw [hb, mul_comm]⟩
  choose k hk using hk
  choose k' hk' using hk'
  have hmapk : (Matrix.of k).map (algebraMap O K) = α⁻¹ • (a : Matrix n n K) := by
    ext u w; simp [hk]
  have hmapk' : (Matrix.of k').map (algebraMap O K) = α • ((a⁻¹ : GL n K) : Matrix n n K) := by
    ext u w; simp [hk']
  have hkk : Matrix.of k * Matrix.of k' = 1 := by
    refine Matrix.map_injective hinj ?_
    dsimp only
    rw [Matrix.map_mul, hmapk, hmapk', smul_mul_smul_comm, inv_mul_cancel₀ hα, one_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨Units.mk0 α hα, ⟨_, _, hkk, mul_eq_one_comm.mp hkk⟩, ?_⟩
  simp only [Units.val_mk0, hmapk, smul_inv_smul₀ hα]

end Matrix.GeneralLinearGroup
