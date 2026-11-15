/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Basis
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Wall

/-!
# `Ω` acts simply transitively on the special nodes

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P` over a
linearly ordered field, with fundamental alcove `A` in the coweight space `N`, affine simple roots
`aₖ` (`a₀ = 1 - θ` and `aᵢ = αᵢ`) and marks `mₖ`. The stabilizer `Ω` of `A` in the extended
affine Weyl group `W_ext = P∨ ⋊ W` acts on the nodes of the affine Dynkin diagram through its
action on the walls of `A` (`RootPairing.fundamentalAlcoveStabilizerToPerm`, written `ω ↦ σ_ω`),
by symmetries of the affine Cartan matrix. This file proves that the map `ω ↦ σ_ω(0)` is a
bijection from `Ω` onto the **special nodes**, the nodes of mark `1`
(`RootPairing.fundamentalAlcoveStabilizerEquivSpecialNodes`), and deduces that every symmetry of
the affine Cartan matrix is, in exactly one way, the action of an element of `Ω` composed with the
extension of a symmetry of the finite Cartan matrix fixing the affine node.

## The argument

Since `ω` permutes the walls, it preserves the closed fundamental alcove `Ā`, the set where every
`aₖ` is nonnegative. The origin is the vertex of `Ā` at which `a₀ = 1` and every other `aₖ`
vanishes, so `ω 0` is the vertex at which `a_{σ_ω 0} = 1` and every other `aₖ` vanishes. The
null-root relation `∑ₖ mₖ aₖ = 1` at this point shows that `σ_ω(0)` is special. Its translation
part `ω 0` is a coweight in `Ā`, and conversely:

* **Uniqueness.** Two elements of `Ω` with the same translation part are equal, because
  `Ω → P∨ / Q∨` is injective. For a root system `ω 0` is determined by the values of the simple
  roots, hence by `σ_ω(0)`, so `ω ↦ σ_ω(0)` is injective.
* **Existence.** Over an archimedean field, let `p` be a coweight in `Ā`. The affine Weyl group
  carries the alcove `A - p` back to `A`, by some `g`, and then `ω = g ∘ t_{-p}` lies in `Ω`. The
  point `ω p = g 0` lies in `Ā` and in the coroot lattice `Q∨`; every root takes a value in
  `[-1, 1]` on `Ā`, and the only such element of `Q∨` is `0`. So `ω⁻¹ 0 = p`. For a special node
  `j`, the fundamental coweight `ϖⱼ` is the vertex of `Ā` opposite the wall `aⱼ = 0`, since
  `θ(ϖⱼ) = mⱼ = 1`, so it is `ω 0` for some `ω` with `σ_ω(0) = j`.

Finally, a symmetry `σ` of the affine Cartan matrix carries the affine node to a special node
(`RootPairing.Base.apply_mem_specialNodes_iff`), which is `σ_ω(0)` for a unique `ω ∈ Ω`; then
`σ_ω⁻¹ σ` fixes the affine node, so it is the extension of a symmetry of the finite Cartan matrix
(`RootPairing.Base.range_affineExtension`).

## Main definitions

* `RootPairing.fundamentalAlcoveStabilizerEquivSpecialNodes`: the bijection `ω ↦ σ_ω(0)` from `Ω`
  onto the special nodes.

## Main results

* `RootPairing.apply_mem_closedFundamentalAlcove_iff`: `Ω` preserves the closed fundamental
  alcove.
* `RootPairing.exists_mem_fundamentalAlcoveStabilizer_apply_zero_eq`: every coweight in the
  closed fundamental alcove is the translation part of an element of `Ω`.
* `RootPairing.fundamentalAlcoveStabilizerToPerm_apply_none_mem_specialNodes`: `σ_ω(0)` is a
  special node.
* `RootPairing.fundamentalAlcoveStabilizerToPerm_apply_none_injective` and
  `RootPairing.exists_fundamentalAlcoveStabilizerToPerm_apply_none_eq`: **`Ω` acts simply
  transitively on the special nodes.**
* `RootPairing.existsUnique_fundamentalAlcoveStabilizerToMatrixSymmetryGroup_mul_affineExtension`:
  **every symmetry of the affine Cartan matrix is uniquely `σ_ω ∘ τ̂`**, for `ω ∈ Ω` and `τ̂` the
  extension of a symmetry `τ` of the finite Cartan matrix.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2.3 (the group `Ω` and the
  special vertices of the alcove) and §4.3 (the automorphism group of the extended Dynkin
  diagram).
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §1.
-/

public section

open Set

namespace RootPairing

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} (b : P.Base) [Finite ι]
  [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-! ### `Ω` preserves the closed fundamental alcove -/

/-- **The stabilizer of the fundamental alcove preserves the closed fundamental alcove.** -/
theorem apply_mem_closedFundamentalAlcove_iff (ω : P.fundamentalAlcoveStabilizer b) {x : N} :
    ω.1 x ∈ closedFundamentalAlcove P b ↔ x ∈ closedFundamentalAlcove P b := by
  -- `ω` permutes the affine simple roots, whose nonnegativity cuts out the closed alcove.
  simp only [mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg]
  refine (Equiv.forall_congr_right (q := fun k ↦ 0 ≤ b.affineSimpleRoot k (ω.1 x))
    (fundamentalAlcoveStabilizerToPerm b ω)).symm.trans ?_
  simp

/-! ### The translation part of an element of `Ω` -/

/-- The translation part `ω 0` of an element of `Ω` lies in the closed fundamental alcove. -/
theorem apply_zero_mem_closedFundamentalAlcove (ω : P.fundamentalAlcoveStabilizer b) :
    ω.1 0 ∈ closedFundamentalAlcove P b :=
  (apply_mem_closedFundamentalAlcove_iff b ω).2 zero_mem_closedFundamentalAlcove

/-- **Every coweight in the closed fundamental alcove is the translation part of an element of
`Ω`.** -/
theorem exists_mem_fundamentalAlcoveStabilizer_apply_zero_eq [Archimedean R] {p : N}
    (hp : p ∈ P.coweightLattice) (hp' : p ∈ closedFundamentalAlcove P b) :
    ∃ ω ∈ P.fundamentalAlcoveStabilizer b, ω 0 = p := by
  -- The affine Weyl group carries the alcove `A - p` back to `A`, by some `g`, so `g ∘ t_{-p}`
  -- lies in `Ω`; it carries `p` to `g 0`, a point of the closed alcove in the coroot lattice.
  obtain ⟨g, hg, hgp⟩ := exists_mem_affineWeylGroup_mul_mem_fundamentalAlcoveStabilizer b
    ((P.constVAdd_mem_extendedAffineWeylGroup_iff (v := -p)).2 (neg_mem hp))
  set ω : P.fundamentalAlcoveStabilizer b := ⟨_, hgp⟩
  have hωp : ω.1 p = 0 := by
    refine eq_zero_of_mem_corootSpan_of_mem_closedFundamentalAlcove b ?_
      ((apply_mem_closedFundamentalAlcove_iff b ω).2 hp')
    have : ω.1 p = g 0 := by simp [ω]
    exact this ▸ (P.mem_affineWeylGroup_iff.1 hg).2
  refine ⟨ω.1⁻¹, inv_mem ω.2, ?_⟩
  rw [← hωp, AffineEquiv.inv_def, AffineEquiv.symm_apply_apply]

/-! ### The action of `Ω` on the special nodes -/

/-- At the translation part `ω 0` of `ω ∈ Ω`, every affine simple root other than `a_{σ_ω 0}`
vanishes: `ω 0` is the vertex of the closed alcove opposite the wall `a_{σ_ω 0} = 0`. -/
private lemma affineSimpleRoot_apply_zero_eq_zero (ω : P.fundamentalAlcoveStabilizer b)
    {l : Option b.support} (hl : l ≠ fundamentalAlcoveStabilizerToPerm b ω none) :
    b.affineSimpleRoot l (ω.1 0) = 0 := by
  obtain ⟨k, rfl⟩ := (fundamentalAlcoveStabilizerToPerm b ω).surjective l
  rw [affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply]
  rcases k with _ | i
  · exact absurd rfl hl
  · simp

/-- **`Ω` carries the affine node to a special node**: `σ_ω(0)` has mark `1`. -/
theorem fundamentalAlcoveStabilizerToPerm_apply_none_mem_specialNodes
    (ω : P.fundamentalAlcoveStabilizer b) :
    fundamentalAlcoveStabilizerToPerm b ω none ∈ b.specialNodes := by
  -- In the null-root relation `∑ₖ mₖ aₖ = 1` at `ω 0`, only `a_{σ_ω 0} = 1` is nonzero.
  set k := fundamentalAlcoveStabilizerToPerm b ω none
  have h := b.sum_affineMarks_mul_affineSimpleRoot (ω.1 0)
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k) fun l _ hl ↦ by
    rw [affineSimpleRoot_apply_zero_eq_zero b ω hl, mul_zero]] at h
  have hk : b.affineSimpleRoot k (ω.1 0) = 1 := by
    simp [k, affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply]
  rw [hk, mul_one] at h
  exact b.mem_specialNodes.mpr (by exact_mod_cast h)

/-- **`Ω` acts freely on the special nodes**: for a root system, an element `ω` of `Ω` is
determined by the node `σ_ω(0)`. -/
theorem fundamentalAlcoveStabilizerToPerm_apply_none_injective [P.IsRootSystem] :
    Function.Injective fun ω : P.fundamentalAlcoveStabilizer b ↦
      fundamentalAlcoveStabilizerToPerm b ω none := by
  intro ω₁ ω₂ h
  beta_reduce at h
  refine fundamentalAlcoveStabilizer_apply_zero_injective b ?_
  -- Every affine simple root takes the same value at `ω₁ 0` and at `ω₂ 0`.
  have heq (l : Option b.support) :
      b.affineSimpleRoot l (ω₁.1 0) = b.affineSimpleRoot l (ω₂.1 0) := by
    by_cases hl : l = fundamentalAlcoveStabilizerToPerm b ω₁ none
    · rw [hl, affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply, h,
        affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply]
    · rw [affineSimpleRoot_apply_zero_eq_zero b ω₁ hl,
        affineSimpleRoot_apply_zero_eq_zero b ω₂ (h ▸ hl)]
  -- The simple roots are the coordinates in the fundamental coweights.
  exact b.fundamentalCoweightBasis.ext_elem fun i ↦ by simpa using heq (some i)

/-- **`Ω` acts transitively on the special nodes**: for a root system over an archimedean field,
every special node is `σ_ω(0)` for some `ω ∈ Ω`. -/
theorem exists_fundamentalAlcoveStabilizerToPerm_apply_none_eq [P.IsRootSystem] [Archimedean R]
    {k : Option b.support} (hk : k ∈ b.specialNodes) :
    ∃ ω : P.fundamentalAlcoveStabilizer b, fundamentalAlcoveStabilizerToPerm b ω none = k := by
  -- Take `ω` carrying the origin to the vertex `x` of the closed alcove at the node `k`.
  obtain ⟨x, hx, hxk, hx0⟩ := b.exists_mem_coweightLattice_affineSimpleRoot_eq hk
  have hx' : x ∈ closedFundamentalAlcove P b :=
    (mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg b).mpr fun l ↦ by
      by_cases hl : l = k
      · simp [hl, hxk]
      · simp [hx0 l hl]
  obtain ⟨ω, hω, rfl⟩ := exists_mem_fundamentalAlcoveStabilizer_apply_zero_eq b hx hx'
  refine ⟨⟨ω, hω⟩, by_contra fun hne ↦ ?_⟩
  -- Otherwise `a_{σ_ω 0}` would vanish at `ω 0`, where it takes the value `a₀(0) = 1`.
  have h := affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply b ⟨ω, hω⟩ none 0
  rw [hx0 _ hne] at h
  simp at h

/-- **`Ω` acts simply transitively on the special nodes**: for a root system over an archimedean
linearly ordered field, `ω ↦ σ_ω(0)` is a bijection from the stabilizer of the fundamental alcove
onto the special nodes of the affine Dynkin diagram, the nodes of mark `1`. -/
noncomputable def fundamentalAlcoveStabilizerEquivSpecialNodes [P.IsRootSystem] [Archimedean R] :
    P.fundamentalAlcoveStabilizer b ≃ b.specialNodes :=
  Equiv.ofBijective
    (fun ω ↦ ⟨fundamentalAlcoveStabilizerToPerm b ω none,
      fundamentalAlcoveStabilizerToPerm_apply_none_mem_specialNodes b ω⟩)
    ⟨fun _ _ h ↦ fundamentalAlcoveStabilizerToPerm_apply_none_injective b (congrArg Subtype.val h),
      fun k ↦ (exists_fundamentalAlcoveStabilizerToPerm_apply_none_eq b k.2).imp
        fun _ h ↦ Subtype.ext h⟩

@[simp]
lemma coe_fundamentalAlcoveStabilizerEquivSpecialNodes_apply [P.IsRootSystem] [Archimedean R]
    (ω : P.fundamentalAlcoveStabilizer b) :
    (fundamentalAlcoveStabilizerEquivSpecialNodes b ω : Option b.support) =
      fundamentalAlcoveStabilizerToPerm b ω none :=
  (rfl)

/-- The inverse of `RootPairing.fundamentalAlcoveStabilizerEquivSpecialNodes` carries a special
node `k` to the element `ω` of `Ω` with `σ_ω(0) = k`. -/
@[simp]
lemma fundamentalAlcoveStabilizerToPerm_fundamentalAlcoveStabilizerEquivSpecialNodes_symm_apply
    [P.IsRootSystem] [Archimedean R] (k : b.specialNodes) :
    fundamentalAlcoveStabilizerToPerm b ((fundamentalAlcoveStabilizerEquivSpecialNodes b).symm k)
      none = k :=
  congrArg Subtype.val ((fundamentalAlcoveStabilizerEquivSpecialNodes b).apply_symm_apply k)

/-! ### The symmetries of the affine Cartan matrix -/

/-- **Every symmetry of the affine Cartan matrix is uniquely the action of an element of `Ω`
composed with the extension of a symmetry of the finite Cartan matrix**: for a root system over an
archimedean linearly ordered field, each automorphism `σ` of the affine Dynkin diagram is
`σ_ω ∘ τ̂` for exactly one pair of `ω ∈ Ω` and a symmetry `τ` of the finite Cartan matrix, with
`τ̂ = RootPairing.Base.affineExtension τ` fixing the affine node. The element `ω` is the one with
`σ_ω(0) = σ(0)`. -/
theorem existsUnique_fundamentalAlcoveStabilizerToMatrixSymmetryGroup_mul_affineExtension
    [P.IsRootSystem] [Archimedean R] (σ : TauCeti.matrixSymmetryGroup b.affineCartanMatrix) :
    ∃! p : P.fundamentalAlcoveStabilizer b × TauCeti.matrixSymmetryGroup b.cartanMatrix,
      fundamentalAlcoveStabilizerToMatrixSymmetryGroup b p.1 * b.affineExtension p.2 = σ := by
  set φ := fundamentalAlcoveStabilizerToMatrixSymmetryGroup b
  -- A factorization `σ = σ_ω ∘ τ̂` has `σ_ω(0) = σ(0)`, since `τ̂` fixes the affine node.
  have happly {ω τ} (h : φ ω * b.affineExtension τ = σ) :
      fundamentalAlcoveStabilizerToPerm b ω none = (σ : Equiv.Perm (Option b.support)) none := by
    simp [← h, φ, Equiv.Perm.mul_apply]
  obtain ⟨ω, hω⟩ := exists_fundamentalAlcoveStabilizerToPerm_apply_none_eq b
    ((b.apply_mem_specialNodes_iff σ.2).mpr b.none_mem_specialNodes)
  -- `σ_ω⁻¹ σ` fixes the affine node, so it is the extension of a finite symmetry.
  obtain ⟨τ, hτ⟩ : (φ ω)⁻¹ * σ ∈ b.affineExtension.range := by
    rw [Base.range_affineExtension, MulAction.mem_stabilizer_iff]
    simp [Subgroup.smul_def, φ, ← hω]
  refine ⟨(ω, τ), by simp [hτ], fun ⟨ω', τ'⟩ h ↦ ?_⟩
  have hω' : ω' = ω :=
    fundamentalAlcoveStabilizerToPerm_apply_none_injective b ((happly h).trans hω.symm)
  subst hω'
  refine Prod.ext rfl (b.affineExtension_injective ?_)
  rw [hτ, eq_inv_mul_iff_mul_eq]
  exact h

end RootPairing
