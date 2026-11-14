/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.ApproximateDiagonal
public import TauCeti.Analysis.Normed.Algebra.Arens.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Bimodule
public import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
import TauCeti.Analysis.Normed.Module.Dual.Goldstine

/-!
# Virtual diagonals of Banach algebras

Let `A` be a possibly nonunital Banach algebra over `𝕜`. The completed projective tensor product
`A ⊗̂π A` carries the outer bimodule actions `mulLeft 𝕜 A` and `mulRight 𝕜 A`, so its bidual
`(A ⊗̂π A)**` carries the iterated dual actions `dualAction (dualAction (mulLeft 𝕜 A))` on the left
and `dualAction (dualAction (mulRight 𝕜 A))` on the right. Likewise, the bidual `A**` carries the
iterated dual actions of left and right multiplication on `A`, which agree on the canonical image of
`A` with both Arens products `TauCeti.arensMul` and `TauCeti.arensMulRev`.

A *virtual diagonal* of `A`, introduced by B. E. Johnson, is an element `M ∈ (A ⊗̂π A)**` such that
`a · M = M · a` and `a · Δ** M = J_A a` for every `a : A`, where `Δ = mul' 𝕜 A : A ⊗̂π A →L[𝕜] A`
is the multiplication map and `J_A = NormedSpace.inclusionInDoubleDual 𝕜 A`. Intertwining of `Δ**`
immediately gives the symmetric right-multiplication identity `Δ** M · a = J_A a`, so `Δ** M` acts
as a two-sided identity on `J_A(A)` for both Arens products.

Over a proper nontrivially normed field, Banach–Alaoglu turns any approximate diagonal bounded by
`C` into a virtual diagonal of norm at most `C` via a weak-star cluster point. Conversely, over `ℝ`
or `ℂ`, Goldstine's theorem and the coincidence of weak and norm closures on convex sets convert
any virtual diagonal `M` into an approximate diagonal bounded by `‖M‖`. Hence a real or complex
Banach algebra has a virtual diagonal (of norm at most `C`) if and only if it has an approximate
diagonal (eventually bounded by `C`).

## Main definitions

* `TauCeti.IsVirtualDiagonal`: virtual diagonals in `(A ⊗̂π A)**`.

## Main results

* `TauCeti.IsVirtualDiagonal.dualAction_mul_flip_precomp_mul'`: a virtual diagonal also satisfies
  `Δ** M · a = J_A a`, so `Δ** M` acts as a two-sided identity on `J_A(A)` for both Arens products.
* `TauCeti.IsApproximateDiagonal.isVirtualDiagonal_of_mapClusterPt` and
  `TauCeti.IsApproximateDiagonal.exists_isVirtualDiagonal`: passage from a bounded approximate
  diagonal to a virtual diagonal with the same norm bound.
* `TauCeti.IsVirtualDiagonal.exists_isApproximateDiagonal`: passage from a virtual diagonal `M` to
  an approximate diagonal eventually bounded by `‖M‖`.
* `TauCeti.exists_norm_le_and_isVirtualDiagonal_iff` and
  `TauCeti.exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal`: equivalence of virtual
  diagonals and bounded approximate diagonals over `ℝ` or `ℂ`.

## References

* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, Definition 2.2.2 and Theorem 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter NormedSpace Topology ContinuousLinearMap

open scoped TensorProduct

namespace TauCeti

-- Shorten instance synthesis for iterated duals of `A` and `A ⊗̂π A`.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

open CompletedProjectiveTensor

section VirtualDiagonal

variable (𝕜 : Type*) {A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- An element `M` of the bidual `(A ⊗̂π A)**` is a *virtual diagonal* of the Banach algebra `A` if
`a · M = M · a` for the bidual outer actions of `A` on `(A ⊗̂π A)**` and `a · Δ** M = J_A a` for
every `a : A`, where `Δ = mul' 𝕜 A : A ⊗̂π A →L[𝕜] A` is the multiplication map. -/
structure IsVirtualDiagonal
    (M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) : Prop where
  /-- The bidual outer left and right actions of every `a : A` agree on `M`. -/
  dualAction_mulLeft_eq (a : A) :
    dualAction (dualAction (mulLeft 𝕜 A)) a M = dualAction (dualAction (mulRight 𝕜 A)) a M
  /-- Left-multiplying `Δ** M` by `a` gives the canonical bidual image of `a`. -/
  dualAction_mul_precomp_mul' (a : A) :
    dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
      (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = inclusionInDoubleDual 𝕜 A a

variable {𝕜}
variable {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}

/-- The defining conditions of a virtual diagonal. -/
theorem isVirtualDiagonal_def :
    IsVirtualDiagonal 𝕜 M ↔
      (∀ a : A,
        dualAction (dualAction (mulLeft 𝕜 A)) a M = dualAction (dualAction (mulRight 𝕜 A)) a M) ∧
        ∀ a : A, dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
          (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = inclusionInDoubleDual 𝕜 A a :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsVirtualDiagonal

/-- Right-multiplying `Δ** M` by `a` also gives the canonical bidual image of `a`, because `Δ**`
intertwines the bidual outer actions with the bidual multiplication actions. -/
theorem dualAction_mul_flip_precomp_mul' (h : IsVirtualDiagonal 𝕜 M) (a : A) :
    dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) a
        (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) =
      inclusionInDoubleDual 𝕜 A a := by
  have hR := precomp_precomp_dualAction_dualAction_apply
    (M := mulRight 𝕜 A) (N := (ContinuousLinearMap.mul 𝕜 A).flip) (T := mul' 𝕜 A)
    (fun c m ↦ mul'_mulRight_apply c m) a M
  have hL := precomp_precomp_dualAction_dualAction_apply
    (M := mulLeft 𝕜 A) (N := ContinuousLinearMap.mul 𝕜 A) (T := mul' 𝕜 A)
    (fun c m ↦ mul'_mulLeft_apply c m) a M
  rw [← hR, ← h.dualAction_mulLeft_eq a, hL, h.dualAction_mul_precomp_mul' a]

/-- Under the first Arens product, `Δ** M` acts as a right identity on the canonical image of
`A`. -/
theorem arensMul_inclusionInDoubleDual_precomp_mul' (h : IsVirtualDiagonal 𝕜 M) (a : A) :
    arensMul 𝕜 A (inclusionInDoubleDual 𝕜 A a) (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) =
      inclusionInDoubleDual 𝕜 A a := by
  rw [arensMul_inclusionInDoubleDual_left, h.dualAction_mul_precomp_mul' a]

/-- Under the second Arens product, `Δ** M` acts as a right identity on the canonical image of
`A`. -/
theorem arensMulRev_inclusionInDoubleDual_precomp_mul' (h : IsVirtualDiagonal 𝕜 M) (a : A) :
    arensMulRev 𝕜 A (inclusionInDoubleDual 𝕜 A a) (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) =
      inclusionInDoubleDual 𝕜 A a := by
  rw [arensMulRev_inclusionInDoubleDual_left, h.dualAction_mul_precomp_mul' a]

/-- Under the first Arens product, `Δ** M` acts as a left identity on the canonical image of
`A`. -/
theorem arensMul_precomp_mul'_inclusionInDoubleDual (h : IsVirtualDiagonal 𝕜 M) (a : A) :
    arensMul 𝕜 A (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) (inclusionInDoubleDual 𝕜 A a) =
      inclusionInDoubleDual 𝕜 A a := by
  rw [arensMul_inclusionInDoubleDual_right, h.dualAction_mul_flip_precomp_mul' a]

/-- Under the second Arens product, `Δ** M` acts as a left identity on the canonical image of
`A`. -/
theorem arensMulRev_precomp_mul'_inclusionInDoubleDual (h : IsVirtualDiagonal 𝕜 M) (a : A) :
    arensMulRev 𝕜 A (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) (inclusionInDoubleDual 𝕜 A a) =
      inclusionInDoubleDual 𝕜 A a := by
  rw [arensMulRev_inclusionInDoubleDual_right, h.dualAction_mul_flip_precomp_mul' a]

end IsVirtualDiagonal

/-- Any weak-star cluster point in `(A ⊗̂π A)**` of an approximate diagonal is a virtual diagonal.
The approximate diagonal need not be bounded once the cluster point is given. -/
theorem IsApproximateDiagonal.isVirtualDiagonal_of_mapClusterPt
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (hl : IsApproximateDiagonal 𝕜 l)
    (hM : MapClusterPt (StrongDual.toWeakDual M) l
      (fun m ↦ StrongDual.toWeakDual
        (inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 A A) m))) :
    IsVirtualDiagonal 𝕜 M where
  dualAction_mulLeft_eq a := by
    ext f
    rw [dualAction_apply_apply, dualAction_apply_apply, ← sub_eq_zero, ← map_sub]
    refine hM.apply_eq_of_tendsto_inclusionInDoubleDual _ ?_
    simpa only [Function.comp_def, sub_apply, dualAction_apply_apply, ← map_sub] using
      (f.continuous.tendsto' 0 0 (map_zero f)).comp (hl.tendsto_mulLeft_sub_mulRight a)
  dualAction_mul_precomp_mul' a := by
    ext f
    rw [dualAction_apply_apply, precomp_apply, comp_apply, precomp_apply, dual_def]
    refine hM.apply_eq_of_tendsto_inclusionInDoubleDual _ ?_
    simpa only [Function.comp_def, comp_apply, dualAction_apply_apply, mul_apply'] using
      (f.continuous.tendsto a).comp (hl.tendsto_mul_mul' a)

/-- Over a proper nontrivially normed field, an approximate diagonal eventually bounded by `C`
supplies a virtual diagonal of norm at most `C`. -/
theorem IsApproximateDiagonal.exists_isVirtualDiagonal [ProperSpace 𝕜]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (hl : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      ‖M‖ ≤ C ∧ IsVirtualDiagonal 𝕜 M := by
  have := hl.neBot
  obtain ⟨M, hMC, hM⟩ := hC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜)
  exact ⟨M, hMC, hl.isVirtualDiagonal_of_mapClusterPt hM⟩

/-- In a subsingleton Banach algebra, `0` is a virtual diagonal. -/
theorem isVirtualDiagonal_zero [Subsingleton A] :
    IsVirtualDiagonal 𝕜
      (0 : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) where
  dualAction_mulLeft_eq _ := by simp
  dualAction_mul_precomp_mul' a := by simp [Subsingleton.elim a 0]

end VirtualDiagonal

section Goldstine

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- **Virtual diagonal to bounded approximate diagonal.** Over `ℝ` or `ℂ`, a virtual diagonal `M`
of `A` yields an approximate diagonal eventually bounded in norm by `‖M‖`, by Goldstine's theorem
and the coincidence of weak and norm closures on convex sets. -/
theorem IsVirtualDiagonal.exists_isApproximateDiagonal
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) :
    ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
      IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ ‖M‖ := by
  -- Bundle `(a · m - m · a, a * Δ m)` into a single operator `A ⊗̂π A →L[𝕜] (A ⊗̂π A) × A` for each
  -- `a : A` so that Goldstine–Mazur applies uniformly across all `a : A`.
  let T : A → CompletedProjectiveTensor 𝕜 A A →L[𝕜] CompletedProjectiveTensor 𝕜 A A × A :=
    fun a ↦ (mulLeft 𝕜 A a - mulRight 𝕜 A a).prod ((ContinuousLinearMap.mul 𝕜 A a).comp (mul' 𝕜 A))
  let y : A → CompletedProjectiveTensor 𝕜 A A × A := fun a ↦ (0, a)
  have hT (a : A) :
      precomp 𝕜 (precomp 𝕜 (T a) :
          StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A × A) →L[𝕜]
            StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)) M =
        inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 A A × A) (y a) := by
    ext g
    let g₁ := g.comp (.inl 𝕜 (CompletedProjectiveTensor 𝕜 A A) A)
    let g₂ := g.comp (.inr 𝕜 (CompletedProjectiveTensor 𝕜 A A) A)
    have hg : precomp 𝕜 (T a) g =
        (dualAction (mulLeft 𝕜 A) a g₁ - dualAction (mulRight 𝕜 A) a g₁) +
          precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A) a g₂) := by
      refine DFunLike.ext _ _ fun m ↦ ?_
      simp only [T, g₁, g₂, precomp_apply, comp_apply, ContinuousLinearMap.prod_apply, sub_apply,
        add_apply, dualAction_apply_apply, mul_apply', inl_apply, inr_apply, ← map_sub, ← map_add,
        Prod.mk_sub_mk, sub_zero, Prod.mk_add_mk, add_zero, zero_add]
    rw [precomp_apply, comp_apply, hg, map_add, map_sub]
    have h₁ := congr($(hM.dualAction_mulLeft_eq a) g₁)
    have h₂ := congr($(hM.dualAction_mul_precomp_mul' a) g₂)
    simp only [dualAction_apply_apply, precomp_apply, comp_apply] at h₁ h₂
    rw [h₁, sub_self, zero_add]
    simpa [g₂, y] using h₂
  obtain ⟨l, hl_ne, hbound, htend⟩ :=
    M.exists_neBot_tendsto_of_forall_precomp_precomp_eq le_rfl T y hT
  exact ⟨l,
    { tendsto_mulLeft_sub_mulRight := fun a ↦ (continuous_fst.tendsto (0, a)).comp (htend a)
      tendsto_mul_mul' := fun a ↦ (continuous_snd.tendsto (0, a)).comp (htend a)
      neBot := hl_ne },
    hbound⟩

/-- Over `ℝ` or `ℂ`, a Banach algebra has a virtual diagonal of norm at most `C` if and only if it
has an approximate diagonal eventually bounded by `C`. -/
theorem exists_norm_le_and_isVirtualDiagonal_iff {C : ℝ} :
    (∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        ‖M‖ ≤ C ∧ IsVirtualDiagonal 𝕜 M) ↔
      ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  ⟨fun ⟨_, hMC, hM⟩ ↦
    let ⟨l, hl, hbound⟩ := hM.exists_isApproximateDiagonal
    ⟨l, hl, hbound.mono fun _ hm ↦ hm.trans hMC⟩,
    fun ⟨_, hl, hC⟩ ↦ hl.exists_isVirtualDiagonal hC⟩

/-- Over `ℝ` or `ℂ`, a Banach algebra has a virtual diagonal if and only if it has a bounded
approximate diagonal. -/
theorem exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal :
    (∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M) ↔
      ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
        IsApproximateDiagonal 𝕜 l ∧ ∃ C, ∀ᶠ m in l, ‖m‖ ≤ C :=
  ⟨fun ⟨M, hM⟩ ↦
    let ⟨l, hl, hbound⟩ := hM.exists_isApproximateDiagonal
    ⟨l, hl, ‖M‖, hbound⟩,
    fun ⟨_, hl, _, hC⟩ ↦
      let ⟨M, _, hM⟩ := hl.exists_isVirtualDiagonal hC
      ⟨M, hM⟩⟩

end Goldstine

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- In a unital Banach algebra, the canonical bidual image of an exact diagonal `m ∈ A ⊗̂π A`
(satisfying `a · m = m · a` and `Δ m = 1`) is a virtual diagonal. -/
theorem isVirtualDiagonal_inclusionInDoubleDual {m : CompletedProjectiveTensor 𝕜 A A}
    (hm : ∀ a, mulLeft 𝕜 A a m = mulRight 𝕜 A a m) (h1 : mul' 𝕜 A m = 1) :
    IsVirtualDiagonal 𝕜 (inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 A A) m) where
  dualAction_mulLeft_eq a := by
    rw [dualAction_dualAction_inclusionInDoubleDual, dualAction_dualAction_inclusionInDoubleDual,
      hm a]
  dualAction_mul_precomp_mul' a := by
    have hΔ : precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A))
        (inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 A A) m) =
        inclusionInDoubleDual 𝕜 A 1 := by
      rw [← h1]
      exact (mul' 𝕜 A).precomp_precomp_inclusionInDoubleDual m
    rw [hΔ, dualAction_dualAction_inclusionInDoubleDual, mul_apply', mul_one]

variable (𝕜) in
/-- The canonical bidual image of `1 ⊗ 1` is a virtual diagonal of the base field `𝕜`. -/
theorem isVirtualDiagonal_inclusionInDoubleDual_one_tmul_one [CompleteSpace 𝕜] :
    IsVirtualDiagonal 𝕜 (inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 𝕜 𝕜)
      ((⟨1 ⊗ₜ 1⟩ : ProjectiveTensor 𝕜 𝕜 𝕜) : CompletedProjectiveTensor 𝕜 𝕜 𝕜)) :=
  isVirtualDiagonal_inclusionInDoubleDual (fun a ↦ by
    rw [mulLeft_apply_coe_tmul, mulRight_apply_coe_tmul, ← smul_eq_mul a 1,
      TensorProduct.smul_tmul, smul_eq_mul, mul_one, one_mul]) (by simp)

end Unital

end TauCeti
