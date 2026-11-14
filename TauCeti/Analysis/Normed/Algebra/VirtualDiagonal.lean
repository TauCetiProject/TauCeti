/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.ApproximateDiagonal
public import TauCeti.Analysis.Normed.Algebra.Arens.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Bimodule
import TauCeti.Analysis.Normed.Module.Dual.Bidual
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
import TauCeti.Topology.MetricSpace.SimultaneousApproximation

/-!
# Virtual diagonals of Banach algebras

Let `A` be a possibly nonunital Banach algebra over `𝕜`. Its completed projective tensor square
`A ⊗̂π A` carries the outer bimodule actions `mulLeft 𝕜 A` and `mulRight 𝕜 A`, and multiplication
induces the bounded bimodule contraction `Δ = CompletedProjectiveTensor.mul' 𝕜 A : A ⊗̂π A →L[𝕜] A`.
Giving each bidual the iterated dual actions `dualAction (dualAction ·)`, an element
`M ∈ (A ⊗̂π A)**` is a *virtual diagonal* of `A` (`TauCeti.IsVirtualDiagonal`) if

`a · M = M · a` and `a · Δ** M = J_A a`

for every `a : A`, where `J_A = NormedSpace.inclusionInDoubleDual 𝕜 A`. Because `Δ` intertwines
the outer actions with left and right multiplication on `A`, the commutation law `a · M = M · a`
automatically gives the symmetric identity `Δ** M · a = J_A a`, and `Δ** M` is a mixed identity of
`A**` for the two Arens products (`arensMul 𝕜 A F (Δ** M) = F` and
`arensMulRev 𝕜 A (Δ** M) F = F`).

Any weak-star cluster point in `(A ⊗̂π A)**` of an approximate diagonal is a virtual diagonal, so
over a proper scalar field an approximate diagonal bounded by `C` yields a virtual diagonal of norm
at most `C` by Banach–Alaoglu. Conversely, over `ℝ` or `ℂ`, Goldstine's theorem and convex
weak-norm closure (`StrongDual.exists_norm_le_and_forall_norm_sub_lt`) approximate a virtual
diagonal `M` on every finite subset of `A` by tensors of norm at most `‖M‖`, producing an
approximate diagonal bounded by `‖M‖`. Thus a Banach algebra over `ℝ` or `ℂ` has a virtual diagonal
of norm at most `C` if and only if it has an approximate diagonal bounded by `C`.

## Main definitions

* `TauCeti.IsVirtualDiagonal`: virtual diagonals in `(A ⊗̂π A)**`.

## Main results

* `TauCeti.exists_isApproximateDiagonal_iff_forall_finset`: finite-set criterion for an approximate
  diagonal bounded by `C`.
* `TauCeti.IsVirtualDiagonal.dualAction_mul_flip_precomp_mul'`,
  `TauCeti.IsVirtualDiagonal.arensMul_precomp_mul'`,
  `TauCeti.IsVirtualDiagonal.arensMulRev_precomp_mul'`: right-action symmetry and mixed-identity
  laws for `Δ** M`.
* `TauCeti.IsApproximateDiagonal.isVirtualDiagonal_of_mapClusterPt` and
  `TauCeti.IsApproximateDiagonal.exists_isVirtualDiagonal`: passage from a bounded approximate
  diagonal to a virtual diagonal.
* `TauCeti.IsVirtualDiagonal.exists_isApproximateDiagonal`: Goldstine passage from a virtual
  diagonal `M` to an approximate diagonal bounded by `‖M‖`.
* `TauCeti.exists_isVirtualDiagonal_norm_le_iff_exists_isApproximateDiagonal` and
  `TauCeti.exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal`: equivalence of virtual
  diagonals and bounded approximate diagonals.

## References

* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.2, Theorem 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

noncomputable section

open Filter NormedSpace Topology ContinuousLinearMap
open scoped TensorProduct

namespace TauCeti

open CompletedProjectiveTensor

-- Shorten instance search for iterated duals of `A` and `A ⊗̂π A`.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

section ApproximateDiagonal

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- Filter-product characterization of `TauCeti.IsApproximateDiagonal`, bundling the two
convergence conditions into `A ⊗̂π A × A`. -/
theorem isApproximateDiagonal_iff_neBot_and_tendsto_prod
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} :
    IsApproximateDiagonal 𝕜 l ↔ l.NeBot ∧ ∀ a : A,
      Tendsto (fun m ↦ (mulLeft 𝕜 A a m - mulRight 𝕜 A a m, a * mul' 𝕜 A m)) l (𝓝 (0, a)) := by
  simp only [tendsto_prod_iff', nhds_prod_eq]
  refine ⟨fun h ↦ ⟨h.neBot, fun a ↦ ⟨h.tendsto_mulLeft_sub_mulRight a, h.tendsto_mul_mul' a⟩⟩,
    fun ⟨hne, h⟩ ↦ ?_⟩
  exact { tendsto_mulLeft_sub_mulRight := fun a ↦ (h a).1
          tendsto_mul_mul' := fun a ↦ (h a).2
          neBot := hne }

/-- A Banach algebra has an approximate diagonal bounded by `C` if and only if every finite subset
of `A` satisfies both approximate-diagonal conditions to any accuracy at a single element of
`A ⊗̂π A` of norm at most `C`. -/
theorem exists_isApproximateDiagonal_iff_forall_finset {C : ℝ} :
    (∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
      IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C) ↔
      ∀ s : Finset A, ∀ ε > 0, ∃ m : CompletedProjectiveTensor 𝕜 A A, ‖m‖ ≤ C ∧
        ∀ a ∈ s, ‖mulLeft 𝕜 A a m - mulRight 𝕜 A a m‖ < ε ∧ ‖a * mul' 𝕜 A m - a‖ < ε := by
  simp only [isApproximateDiagonal_iff_neBot_and_tendsto_prod, and_assoc]
  refine (exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm).trans ?_
  simpa [Prod.dist_eq, dist_eq_norm] using
    exists_neBot_tendsto_iff_forall_finset_dist_lt
      (p := fun m : CompletedProjectiveTensor 𝕜 A A ↦ ‖m‖ ≤ C)
      (F := fun (a : A) m ↦ (mulLeft 𝕜 A a m - mulRight 𝕜 A a m, a * mul' 𝕜 A m))
      (x := fun a : A ↦ ((0 : CompletedProjectiveTensor 𝕜 A A), a))

end ApproximateDiagonal

section VirtualDiagonal

variable (𝕜 : Type*) {A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- An element `M` of `(A ⊗̂π A)**` is a *virtual diagonal* of the Banach algebra `A` if
`a · M = M · a` and `a · Δ** M = J_A a` for every `a : A`, where `A ⊗̂π A` has the outer actions
`mulLeft 𝕜 A` and `mulRight 𝕜 A`, `A` has left multiplication `ContinuousLinearMap.mul 𝕜 A`, each
bidual carries the iterated dual actions `dualAction (dualAction ·)`, `Δ = mul' 𝕜 A` is the
multiplication map, and `J_A = inclusionInDoubleDual 𝕜 A` is the canonical map into `A**`. -/
structure IsVirtualDiagonal
    (M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) : Prop where
  /-- The biduals of the outer left and right actions of `A` agree on `M`: `a · M = M · a`. -/
  dualAction_mulLeft_eq_mulRight (a : A) :
    dualAction (dualAction (mulLeft 𝕜 A)) a M = dualAction (dualAction (mulRight 𝕜 A)) a M
  /-- Left action of `a` on `Δ** M` recovers the canonical image `J_A a`. -/
  dualAction_mul_precomp_mul' (a : A) :
    dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
      (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = inclusionInDoubleDual 𝕜 A a

variable {𝕜}

namespace IsVirtualDiagonal

section Algebraic

variable {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}

/-- Pointwise form of `a · M = M · a`: `M (φ ∘ mulLeft a) = M (φ ∘ mulRight a)` for every
`φ ∈ (A ⊗̂π A)*`. -/
theorem apply_comp_mulLeft_eq_mulRight (hM : IsVirtualDiagonal 𝕜 M) (a : A)
    (φ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)) :
    M (φ.comp (mulLeft 𝕜 A a)) = M (φ.comp (mulRight 𝕜 A a)) := by
  have h := congr($(hM.dualAction_mulLeft_eq_mulRight a) φ)
  simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply] using h

/-- Pointwise form of `a · Δ** M = J_A a`: `M (f ∘ mul a ∘ Δ) = f a` for every `f ∈ A*`. -/
theorem apply_comp_mul_comp_mul' (hM : IsVirtualDiagonal 𝕜 M) (a : A) (f : StrongDual 𝕜 A) :
    M ((f.comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A)) = f a := by
  have h := congr($(hM.dualAction_mul_precomp_mul' a) f)
  simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply, dual_def]
    using h

/-- Construct a virtual diagonal from its pointwise functional equations on `(A ⊗̂π A)*` and
`A*`. -/
theorem of_forall_apply
    (hcomm : ∀ (a : A) (φ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      M (φ.comp (mulLeft 𝕜 A a)) = M (φ.comp (mulRight 𝕜 A a)))
    (hmul : ∀ (a : A) (f : StrongDual 𝕜 A),
      M ((f.comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A)) = f a) :
    IsVirtualDiagonal 𝕜 M where
  dualAction_mulLeft_eq_mulRight a := ext fun φ ↦ by
    simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply] using hcomm a φ
  dualAction_mul_precomp_mul' a := ext fun f ↦ by
    simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply, dual_def] using
      hmul a f

/-- Pointwise right-multiplication identity for a virtual diagonal:
`M (f ∘ (· * a) ∘ Δ) = f a` for every `f ∈ A*`. -/
theorem apply_comp_mul_flip_comp_mul' (hM : IsVirtualDiagonal 𝕜 M) (a : A) (f : StrongDual 𝕜 A) :
    M ((f.comp ((ContinuousLinearMap.mul 𝕜 A).flip a)).comp (mul' 𝕜 A)) = f a := by
  have hR : (f.comp ((ContinuousLinearMap.mul 𝕜 A).flip a)).comp (mul' 𝕜 A) =
      (f.comp (mul' 𝕜 A)).comp (mulRight 𝕜 A a) := by
    ext m
    simp [mul_assoc]
  have hL : (f.comp (mul' 𝕜 A)).comp (mulLeft 𝕜 A a) =
      (f.comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A) := by
    ext m
    simp [mul_assoc]
  rw [hR, ← hM.apply_comp_mulLeft_eq_mulRight a, hL, hM.apply_comp_mul_comp_mul']

/-- Right action of `a` on `Δ** M` also recovers `J_A a`: `Δ** M · a = J_A a`. -/
theorem dualAction_mul_flip_precomp_mul' (hM : IsVirtualDiagonal 𝕜 M) (a : A) :
    dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) a
      (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = inclusionInDoubleDual 𝕜 A a :=
  ext fun f ↦ by
    simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply, dual_def] using
      hM.apply_comp_mul_flip_comp_mul' a f

/-- The image `Δ** M` of a virtual diagonal in `A**` is a right identity for the first Arens
product. -/
theorem arensMul_precomp_mul' (hM : IsVirtualDiagonal 𝕜 M) (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMul 𝕜 A F (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = F := by
  ext f
  rw [arensMul_apply]
  congr 1
  ext a
  rw [bilinearTranspose_apply, precomp_apply, comp_apply, ← hM.apply_comp_mul_comp_mul' a f]
  congr 1
  ext m
  simp

/-- The image `Δ** M` of a virtual diagonal in `A**` is a left identity for the second Arens
product. -/
theorem arensMulRev_precomp_mul' (hM : IsVirtualDiagonal 𝕜 M)
    (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMulRev 𝕜 A (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) F = F := by
  ext f
  rw [arensMulRev_apply]
  congr 1
  ext a
  rw [bilinearTranspose_apply, precomp_apply, comp_apply, ← hM.apply_comp_mul_flip_comp_mul' a f]
  congr 1
  ext m
  simp

end Algebraic

end IsVirtualDiagonal

/-- Any weak-star cluster point in `(A ⊗̂π A)**` of an approximate diagonal is a virtual diagonal.
The approximate diagonal need not be norm bounded once the cluster point is given. -/
theorem IsApproximateDiagonal.isVirtualDiagonal_of_mapClusterPt
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (hl : IsApproximateDiagonal 𝕜 l)
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : MapClusterPt (StrongDual.toWeakDual M) l
      (fun m ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 _ m))) :
    IsVirtualDiagonal 𝕜 M := by
  refine .of_forall_apply (fun a φ ↦ ?_) (fun a f ↦ ?_)
  · have h0 : M (φ.comp (mulLeft 𝕜 A a - mulRight 𝕜 A a)) = 0 := by
      refine hM.apply_eq_of_tendsto_inclusionInDoubleDual _ ?_
      simpa only [Function.comp_def, comp_apply, sub_apply, map_zero] using
        (φ.continuous.tendsto 0).comp (hl.tendsto_mulLeft_sub_mulRight a)
    have hsub : φ.comp (mulLeft 𝕜 A a - mulRight 𝕜 A a) =
        φ.comp (mulLeft 𝕜 A a) - φ.comp (mulRight 𝕜 A a) := by
      ext m
      simp
    rw [hsub, map_sub, sub_eq_zero] at h0
    exact h0
  · refine hM.apply_eq_of_tendsto_inclusionInDoubleDual _ ?_
    simpa only [Function.comp_def, comp_apply, mul_apply'] using
      (f.continuous.tendsto a).comp (hl.tendsto_mul_mul' a)

/-- Over a proper scalar field, an approximate diagonal bounded by `C` has a weak-star cluster
point in `(A ⊗̂π A)**`, which is a virtual diagonal of norm at most `C`. -/
theorem IsApproximateDiagonal.exists_isVirtualDiagonal [ProperSpace 𝕜]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (hl : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M ∧ ‖M‖ ≤ C := by
  have := hl.neBot
  obtain ⟨M, hMC, hM⟩ := hC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜)
  exact ⟨M, hl.isVirtualDiagonal_of_mapClusterPt hM, hMC⟩

end VirtualDiagonal

section Goldstine

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- **Goldstine passage from a virtual diagonal to a bounded approximate diagonal.** Over `ℝ` or
`ℂ`, every virtual diagonal `M` of a Banach algebra `A` gives rise to an approximate diagonal
bounded by `‖M‖`. -/
theorem IsVirtualDiagonal.exists_isApproximateDiagonal
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) :
    ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
      IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ ‖M‖ := by
  rw [exists_isApproximateDiagonal_iff_forall_finset]
  intro s ε hε
  let Z : s ⊕ s → Type _
    | .inl _ => CompletedProjectiveTensor 𝕜 A A
    | .inr _ => A
  let : ∀ i, SeminormedAddCommGroup (Z i)
    | .inl _ => inferInstance
    | .inr _ => inferInstance
  let : ∀ i, NormedSpace 𝕜 (Z i)
    | .inl _ => inferInstance
    | .inr _ => inferInstance
  let S : ∀ i, CompletedProjectiveTensor 𝕜 A A →L[𝕜] Z i
    | .inl a => mulLeft 𝕜 A a.1 - mulRight 𝕜 A a.1
    | .inr a => ContinuousLinearMap.mul 𝕜 A a.1 ∘L mul' 𝕜 A
  let z : ∀ i, Z i
    | .inl _ => 0
    | .inr a => a.1
  have hz : ∀ i (f : StrongDual 𝕜 (Z i)), M (f.comp (S i)) = f (z i) := by
    rintro (a | a) f
    · dsimp only [Z, S, z] at f ⊢
      have hsub : f.comp (mulLeft 𝕜 A a.1 - mulRight 𝕜 A a.1) =
          f.comp (mulLeft 𝕜 A a.1) - f.comp (mulRight 𝕜 A a.1) := by
        ext x
        simp
      rw [hsub, map_sub, hM.apply_comp_mulLeft_eq_mulRight, sub_self, map_zero]
    · exact hM.apply_comp_mul_comp_mul' a.1 f
  obtain ⟨m, hm, happrox⟩ := M.exists_norm_le_and_forall_norm_sub_lt S z hz le_rfl hε
  refine ⟨m, hm, fun a ha ↦ ?_⟩
  have h₁ := happrox (.inl ⟨a, ha⟩)
  have h₂ := happrox (.inr ⟨a, ha⟩)
  simpa only [S, z, sub_zero, sub_apply, comp_apply, mul_apply'] using And.intro h₁ h₂

/-- Over `ℝ` or `ℂ`, a Banach algebra has a virtual diagonal of norm at most `C` if and only if it
has an approximate diagonal bounded by `C`. -/
theorem exists_isVirtualDiagonal_norm_le_iff_exists_isApproximateDiagonal {C : ℝ} :
    (∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M ∧ ‖M‖ ≤ C) ↔
      ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C := by
  refine ⟨fun ⟨M, hM, hMC⟩ ↦ ?_, fun ⟨l, hl, hC⟩ ↦ hl.exists_isVirtualDiagonal hC⟩
  obtain ⟨l, hl, hm⟩ := hM.exists_isApproximateDiagonal
  exact ⟨l, hl, hm.mono fun _ h ↦ h.trans hMC⟩

/-- Over `ℝ` or `ℂ`, a Banach algebra has a virtual diagonal if and only if it has a bounded
approximate diagonal. -/
theorem exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal :
    (∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M) ↔
      ∃ (C : ℝ) (l : Filter (CompletedProjectiveTensor 𝕜 A A)),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  ⟨fun ⟨M, hM⟩ ↦ ⟨‖M‖, hM.exists_isApproximateDiagonal⟩,
    fun ⟨_, _, hl, hC⟩ ↦ let ⟨M, hM, _⟩ := hl.exists_isVirtualDiagonal hC; ⟨M, hM⟩⟩

end Goldstine

section Examples

section Subsingleton

variable (𝕜 : Type*) {A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A] [Subsingleton A]

/-- In a zero Banach algebra, `0` is a constant approximate diagonal. -/
theorem isApproximateDiagonal_pure_zero :
    IsApproximateDiagonal 𝕜 (pure (0 : CompletedProjectiveTensor 𝕜 A A)) where
  tendsto_mulLeft_sub_mulRight a := by
    simpa using tendsto_pure_nhds (fun m ↦ mulLeft 𝕜 A a m - mulRight 𝕜 A a m) 0
  tendsto_mul_mul' a := by
    convert tendsto_pure_nhds (fun m : CompletedProjectiveTensor 𝕜 A A ↦ a * mul' 𝕜 A m) 0

/-- In a zero Banach algebra, `0` is a virtual diagonal. -/
theorem isVirtualDiagonal_zero :
    IsVirtualDiagonal 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) :=
  .of_forall_apply (fun _ _ ↦ by simp) fun a f ↦ by simp [Subsingleton.elim a 0]

end Subsingleton

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- In a unital Banach algebra, the canonical bidual image of a diagonal `m ∈ A ⊗̂π A` is a virtual
diagonal. -/
theorem isVirtualDiagonal_inclusionInDoubleDual {m : CompletedProjectiveTensor 𝕜 A A}
    (hm : ∀ a, mulLeft 𝕜 A a m = mulRight 𝕜 A a m) (h1 : mul' 𝕜 A m = 1) :
    IsVirtualDiagonal 𝕜 (inclusionInDoubleDual 𝕜 _ m) :=
  .of_forall_apply (fun a φ ↦ by simp [hm a]) fun a f ↦ by simp [h1]

variable (𝕜) in
/-- For the base field over itself, the canonical bidual image of `1 ⊗ 1` is a virtual diagonal. -/
theorem isVirtualDiagonal_inclusionInDoubleDual_one_tmul_one [CompleteSpace 𝕜] :
    IsVirtualDiagonal 𝕜
      (inclusionInDoubleDual 𝕜 _
        ((⟨1 ⊗ₜ 1⟩ : ProjectiveTensor 𝕜 𝕜 𝕜) : CompletedProjectiveTensor 𝕜 𝕜 𝕜)) :=
  isVirtualDiagonal_inclusionInDoubleDual (fun a ↦ by
    rw [mulLeft_apply_coe_tmul, mulRight_apply_coe_tmul, ← smul_eq_mul a 1,
      TensorProduct.smul_tmul, smul_eq_mul, mul_one, one_mul]) (by simp)

end Unital

end Examples

end TauCeti
