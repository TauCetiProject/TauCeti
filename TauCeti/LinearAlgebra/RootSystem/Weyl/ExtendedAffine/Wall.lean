/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Alcove

/-!
# The action of `Ω` on the walls of the fundamental alcove

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P`, with simple
roots `αᵢ`, highest root `θ` and fundamental alcove `A` in the coweight space `N`. The walls of `A`
are the zero sets of the **affine simple roots** (`RootPairing.Base.affineSimpleRoot`, defined
with the fundamental alcove), indexed by the nodes of the affine Dynkin diagram, `Option b.support`:

`a₀ = 1 - θ` at the affine node `0`, and `aᵢ = αᵢ` at a node `i`,

so that `A = {x | aₖ(x) > 0 for every node k}`. Their linear parts are the affine simple roots
`α₀ = -θ` and `αᵢ` of the affine Cartan matrix `RootPairing.Base.affineCartanMatrix`, and writing
`θ = ∑ mᵢ αᵢ` and `m₀ = 1` they satisfy the null-root relation `∑ₖ mₖ aₖ = 1`.

This file proves that the stabilizer `Ω` of `A` in the extended affine Weyl group
(`RootPairing.fundamentalAlcoveStabilizer`) permutes the walls of `A`: for every `ω ∈ Ω` there is
a permutation `σ` of the nodes with `a_{σ k} ∘ ω = aₖ`, so that `ω` carries the wall `aₖ = 0` onto
the wall `a_{σ k} = 0`. This defines a homomorphism `Ω → Perm (Option b.support)`
(`RootPairing.fundamentalAlcoveStabilizerToPerm`), and its image consists of symmetries of the
affine Cartan matrix: `σ` preserves every Cartan integer `⟨αₖ, αₗ^∨⟩`
(`RootPairing.fundamentalAlcoveStabilizerToPerm_mem_matrixSymmetryGroup`). For a root system the
action is faithful (`RootPairing.fundamentalAlcoveStabilizerToPerm_injective`): an element of `Ω`
fixing every wall fixes the values of the simple roots, which determine a point of `N`.

## The argument

An element `ω ∈ Ω` permutes the affine roots `α + n`, so each `aₖ ∘ ω⁻¹` is an affine root, and it
is positive on `A` because `ω⁻¹(A) = A`. Measure an affine root `α + n` by its height
`ht(α) + n h`, where `h = ht(θ) + 1`; this is `h` times its value at the point `x₀ ∈ A` at which
every simple root takes the value `1 / h`, so a positive affine root has height at least `1`, and
the affine simple roots have height exactly `1`. The null-root relation, evaluated at `ω⁻¹ x₀`,
gives `∑ₖ mₖ ht(aₖ ∘ ω⁻¹) = ∑ₖ mₖ`. Since every mark `mₖ` is positive, every `aₖ ∘ ω⁻¹` has height
`1`. An affine root of height `1` is an affine simple root: either `n = 0` and `α` is a root of
height `1`, hence simple (`RootPairing.Base.height_eq_one_iff`), or `n = 1` and `α` has height
`-ht(θ)`, hence is `-θ`. The Cartan integers are preserved because the linear part of `ω` lies in
the Weyl group, which preserves the pairing of roots and coroots
(`RootPairing.pairing_eq_of_root'_apply_eq`).

## Main definitions

* `RootPairing.fundamentalAlcoveStabilizerToPerm`: the action of `Ω` on the nodes of the affine
  Dynkin diagram, through its action on the walls of the fundamental alcove.
* `RootPairing.fundamentalAlcoveStabilizerToMatrixSymmetryGroup`: the same action, as a
  homomorphism to the symmetry group of the affine Cartan matrix.

## Main results

* `RootPairing.affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply`: `a_{σ k}(ω x) = aₖ(x)`.
* `RootPairing.fundamentalAlcoveStabilizerToPerm_mem_matrixSymmetryGroup`: **the action of `Ω` on
  the walls preserves the affine Cartan matrix.**
* `RootPairing.fundamentalAlcoveStabilizerToPerm_injective`: for a root system the action is
  faithful.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2.3 (the group `Ω` and its
  action on the extended Dynkin diagram).
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §1.
-/

public section

open Set

namespace RootPairing

variable {ι R M N : Type*}

/-! ### `Ω` permutes the affine simple roots -/

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} (b : P.Base) [Finite ι] [Nonempty ι]
  [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

omit [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] in
/-- An element of the extended affine Weyl group carries each affine simple root to an affine root
`α + n`. -/
private lemma exists_affineSimpleRoot_apply_eq_root'_add {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.extendedAffineWeylGroup) (k : Option b.support) :
    ∃ (j : ι) (n : ℤ), ∀ x, b.affineSimpleRoot k (f x) = P.root' j x + n := by
  obtain ⟨j, m, hm⟩ := P.exists_root'_apply_eq_add_intCast_of_mem_extendedAffineWeylGroup hf
    (b.affineSimpleRootIndex k)
  obtain ⟨c, hc⟩ : ∃ c : ℤ, b.affineSimpleRoot k 0 = c := by
    rcases k with _ | i
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  exact ⟨j, m + c, fun x ↦ by rw [b.affineSimpleRoot_eq_root'_add, hm, hc]; push_cast; ring⟩

/-- **An element of `Ω` carries each affine simple root to an affine simple root**: for `f` in the
stabilizer of the fundamental alcove, `aₖ ∘ f` is again an affine simple root. -/
private lemma exists_affineSimpleRoot_comp_eq {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.fundamentalAlcoveStabilizer b) (k : Option b.support) :
    ∃ l, ∀ x, b.affineSimpleRoot k (f x) = b.affineSimpleRoot l x := by
  -- Each `aₖ ∘ f` is an affine root `α_{jₖ} + nₖ`.
  choose j n hjn using exists_affineSimpleRoot_apply_eq_root'_add b
    (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b hf)
  -- Its height `H k = ht(α_{jₖ}) + nₖ h`, with `h = ht(θ) + 1`, is `h` times its value at `x₀`.
  have hD : (0 : R) < b.height b.highestRoot + 1 := by
    have : (0 : R) < b.height b.highestRoot := by exact_mod_cast b.isPos_highestRoot
    linarith
  obtain ⟨x₀, hx₀A, hx₀⟩ := exists_mem_fundamentalAlcove_root'_eq_height_div b
  set H : Option b.support → ℤ := fun k ↦ b.height (j k) + n k * (b.height b.highestRoot + 1)
  have hval (k : Option b.support) :
      b.affineSimpleRoot k (f x₀) = H k / ((b.height b.highestRoot : R) + 1) := by
    rw [hjn, hx₀]
    push_cast [H]
    field_simp
  -- `x₀` lies in `A`, hence so does `f x₀`, and every `aₖ ∘ f` has height at least `1`.
  have hfx₀ : f x₀ ∈ fundamentalAlcove P b :=
    ((P.mem_fundamentalAlcoveStabilizer b).mp hf).2 ▸ mem_image_of_mem f hx₀A
  have hH (k : Option b.support) : 1 ≤ H k := by
    have := (mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos b).mp hfx₀ k
    rw [hval, div_pos_iff_of_pos_right hD] at this
    exact_mod_cast this
  -- The null-root relation at `f x₀` gives `∑ₖ mₖ H k = h = ∑ₖ mₖ`, so every `H k` is `1`.
  have hsum : ∑ k, b.affineMarks k * (H k - 1) = 0 := by
    have hR : ∑ k, (b.affineMarks k : R) * H k = (b.height b.highestRoot : R) + 1 := by
      calc ∑ k, (b.affineMarks k : R) * H k
          = ∑ k, (b.affineMarks k : R) * b.affineSimpleRoot k (f x₀) *
              ((b.height b.highestRoot : R) + 1) :=
            Finset.sum_congr rfl fun k _ ↦ by rw [hval]; field_simp
        _ = (b.height b.highestRoot : R) + 1 := by
            rw [← Finset.sum_mul, b.sum_affineMarks_mul_affineSimpleRoot, one_mul]
    have hZ : ∑ k, b.affineMarks k * H k = b.height b.highestRoot + 1 := by exact_mod_cast hR
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hZ, b.sum_affineMarks, sub_self]
  have hH1 : H k = 1 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ ↦
      mul_nonneg (b.affineMarks_pos l).le (sub_nonneg.mpr (hH l))).mp hsum k (Finset.mem_univ k)
    have := (mul_eq_zero.mp this).resolve_left (b.affineMarks_pos k).ne'
    omega
  obtain ⟨l, hl⟩ := b.exists_affineSimpleRoot_eq_of_height_eq_one hH1
  exact ⟨l, fun x ↦ (hjn k x).trans (hl x).symm⟩

/-- For `f` in `Ω`, the node `l` with `a_l ∘ f = aₖ`. -/
private noncomputable def wallIndex {f : N ≃ᵃ[R] N} (hf : f ∈ P.fundamentalAlcoveStabilizer b)
    (k : Option b.support) : Option b.support :=
  (exists_affineSimpleRoot_comp_eq b (inv_mem hf) k).choose

private lemma affineSimpleRoot_wallIndex_apply {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.fundamentalAlcoveStabilizer b) (k : Option b.support) (x : N) :
    b.affineSimpleRoot (wallIndex b hf k) (f x) = b.affineSimpleRoot k x := by
  have := (exists_affineSimpleRoot_comp_eq b (inv_mem hf) k).choose_spec (f x)
  simp only [AffineEquiv.inv_def, AffineEquiv.symm_apply_apply] at this
  exact this.symm

private lemma wallIndex_eq_iff {f : N ≃ᵃ[R] N} (hf : f ∈ P.fundamentalAlcoveStabilizer b)
    {k l : Option b.support} :
    wallIndex b hf k = l ↔ ∀ x, b.affineSimpleRoot l (f x) = b.affineSimpleRoot k x := by
  refine ⟨fun h ↦ h ▸ affineSimpleRoot_wallIndex_apply b hf k, fun h ↦ ?_⟩
  refine b.affineSimpleRoot_injective (funext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := f.surjective y
  rw [affineSimpleRoot_wallIndex_apply, h]

/-- **The action of `Ω` on the walls of the fundamental alcove.** An element `ω` of the stabilizer
`Ω` of the fundamental alcove in the extended affine Weyl group carries the wall `aₖ = 0` of the
alcove onto the wall `a_{σ k} = 0`, where `σ` is the permutation of the nodes of the affine
Dynkin diagram with `a_{σ k} ∘ ω = aₖ`
(`RootPairing.affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply`). -/
noncomputable def fundamentalAlcoveStabilizerToPerm :
    P.fundamentalAlcoveStabilizer b →* Equiv.Perm (Option b.support) where
  toFun ω :=
    { toFun := wallIndex b ω.2
      invFun := wallIndex b (inv_mem ω.2)
      left_inv k := (wallIndex_eq_iff b _).mpr fun x ↦ by
        rw [← affineSimpleRoot_wallIndex_apply b ω.2 k (ω.1⁻¹ x)]
        simp only [AffineEquiv.inv_def, AffineEquiv.apply_symm_apply]
      right_inv k := (wallIndex_eq_iff b _).mpr fun x ↦ by
        rw [← affineSimpleRoot_wallIndex_apply b (inv_mem ω.2) k (ω.1 x)]
        simp only [AffineEquiv.inv_def, AffineEquiv.symm_apply_apply] }
  map_one' := Equiv.Perm.ext fun k ↦
    (wallIndex_eq_iff (l := k) b (1 : P.fundamentalAlcoveStabilizer b).2).mpr fun x ↦ by simp
  map_mul' ω₁ ω₂ := Equiv.Perm.ext fun k ↦
    (wallIndex_eq_iff (l := wallIndex b ω₁.2 (wallIndex b ω₂.2 k)) b (ω₁ * ω₂).2).mpr
      fun x ↦ by simp [affineSimpleRoot_wallIndex_apply]

/-- **`ω` carries the wall `aₖ = 0` onto the wall `a_{σ k} = 0`**: `a_{σ k}(ω x) = aₖ(x)`, where
`σ = fundamentalAlcoveStabilizerToPerm b ω`. -/
@[simp]
theorem affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply
    (ω : P.fundamentalAlcoveStabilizer b) (k : Option b.support) (x : N) :
    b.affineSimpleRoot (fundamentalAlcoveStabilizerToPerm b ω k) (ω.1 x) =
      b.affineSimpleRoot k x :=
  affineSimpleRoot_wallIndex_apply b ω.2 k x

/-- The permutation of the nodes induced by `ω ∈ Ω` is characterized by `a_{σ k} ∘ ω = aₖ`. -/
theorem fundamentalAlcoveStabilizerToPerm_apply_eq_iff (ω : P.fundamentalAlcoveStabilizer b)
    {k l : Option b.support} :
    fundamentalAlcoveStabilizerToPerm b ω k = l ↔
      ∀ x, b.affineSimpleRoot l (ω.1 x) = b.affineSimpleRoot k x :=
  wallIndex_eq_iff b ω.2

/-- **The action of `Ω` on the walls of the fundamental alcove preserves the affine Cartan
matrix**: the permutation `σ` of the nodes induced by `ω ∈ Ω` satisfies
`⟨α_{σ k}, α_{σ l}^∨⟩ = ⟨αₖ, αₗ^∨⟩`, so it is an automorphism of the affine Dynkin diagram. -/
theorem fundamentalAlcoveStabilizerToPerm_mem_matrixSymmetryGroup
    (ω : P.fundamentalAlcoveStabilizer b) :
    fundamentalAlcoveStabilizerToPerm b ω ∈ TauCeti.matrixSymmetryGroup b.affineCartanMatrix := by
  set σ := fundamentalAlcoveStabilizerToPerm b ω
  have hw := (P.mem_extendedAffineWeylGroup_iff.mp
    (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b ω.2)).1
  -- The linear part of `ω` carries the root functional of `α_{σ k}` to that of `αₖ`.
  have hlin (k : Option b.support) (x : N) :
      P.root' (b.affineSimpleRootIndex (σ k)) (ω.1.linear x) =
        P.root' (b.affineSimpleRootIndex k) x := by
    have h₁ := affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply b ω k x
    have h₀ := affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply b ω k 0
    rw [b.affineSimpleRoot_eq_root'_add (σ k), AffineEquiv.apply_eq_linear_add ω.1 x, map_add] at h₁
    rw [b.affineSimpleRoot_eq_root'_add (σ k)] at h₀
    rw [b.affineSimpleRoot_eq_root'_add k] at h₁
    linear_combination h₁ - h₀
  rw [TauCeti.mem_matrixSymmetryGroup_iff]
  ext k l
  simp only [Matrix.submatrix_apply, Base.affineCartanMatrix_apply]
  refine FaithfulSMul.algebraMap_injective ℤ R ?_
  simp only [algebraMap_pairingIn]
  exact (P.pairing_eq_of_root'_apply_eq hw (hlin k) (hlin l)).symm

/-- The action of the stabilizer of the fundamental alcove on the nodes of the affine Dynkin
diagram, as a homomorphism to the symmetry group of the affine Cartan matrix. -/
noncomputable def fundamentalAlcoveStabilizerToMatrixSymmetryGroup :
    P.fundamentalAlcoveStabilizer b →* TauCeti.matrixSymmetryGroup b.affineCartanMatrix :=
  (fundamentalAlcoveStabilizerToPerm b).codRestrict _
    (fundamentalAlcoveStabilizerToPerm_mem_matrixSymmetryGroup b)

@[simp]
lemma coe_fundamentalAlcoveStabilizerToMatrixSymmetryGroup_apply
    (ω : P.fundamentalAlcoveStabilizer b) :
    (fundamentalAlcoveStabilizerToMatrixSymmetryGroup b ω : Equiv.Perm (Option b.support)) =
      fundamentalAlcoveStabilizerToPerm b ω :=
  (rfl)

/-- **For a root system, `Ω` acts faithfully on the affine Dynkin diagram**: an element fixing
every wall of the fundamental alcove is the identity, since the simple roots then take the same
values at `x` and at `ω x`, and they determine a point of the coweight space. -/
theorem fundamentalAlcoveStabilizerToPerm_injective [P.IsRootSystem] :
    Function.Injective (fundamentalAlcoveStabilizerToPerm b) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro ω hω
  rw [MonoidHom.mem_ker] at hω
  rw [Subgroup.mem_bot]
  refine Subtype.ext (AffineEquiv.ext fun x ↦ ?_)
  -- Every simple root takes the same value at `ω x` and at `x`.
  have hsimple (i : ι) (hi : i ∈ b.support) : P.root' i (ω.1 x - x) = 0 := by
    have := affineSimpleRoot_fundamentalAlcoveStabilizerToPerm_apply b ω (some ⟨i, hi⟩) x
    rw [hω, Equiv.Perm.coe_one, id, Base.affineSimpleRoot_some,
      Base.affineSimpleRoot_some] at this
    rw [map_sub, this, sub_self]
  -- Hence so does every root, and the roots span the weight space.
  simpa [sub_eq_zero] using (P.flip.eq_zero_iff_forall_coroot'_eq_zero.mpr
    (P.flip.coroot'_eq_zero_of_forall_mem_support b.flip hsimple))

/-- For a root system, the homomorphism from the fundamental alcove stabilizer to the symmetry
group of the affine Cartan matrix is injective. -/
theorem fundamentalAlcoveStabilizerToMatrixSymmetryGroup_injective [P.IsRootSystem] :
    Function.Injective (fundamentalAlcoveStabilizerToMatrixSymmetryGroup b) := by
  intro ω₁ ω₂ h
  apply fundamentalAlcoveStabilizerToPerm_injective b
  simpa only [coe_fundamentalAlcoveStabilizerToMatrixSymmetryGroup_apply] using
    congrArg Subtype.val h

end Field

end RootPairing
