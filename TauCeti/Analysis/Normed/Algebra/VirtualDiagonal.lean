/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.ApproximateDiagonal
public import TauCeti.Analysis.Normed.Algebra.Arens.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Bimodule
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
import TauCeti.Analysis.Normed.Module.Dual.Goldstine

/-!
# Virtual diagonals of Banach algebras

Let `A` be a possibly nonunital Banach algebra over `𝕜`. Its completed projective tensor square
`A ⊗̂π A` carries the outer bimodule actions `mulLeft 𝕜 A` and `mulRight 𝕜 A`, and multiplication
induces the bounded bimodule contraction `Δ = CompletedProjectiveTensor.mul' 𝕜 A : A ⊗̂π A →L[𝕜] A`.
Giving each bidual the iterated dual actions `dualAction (dualAction ·)`, an element
`M ∈ (A ⊗̂π A)**` is a *virtual diagonal* of `A` (`TauCeti.IsVirtualDiagonal`) if

`a · M = M · a` and `a · Δ** M = J_A a`

for every `a : A`, where `J_A = NormedSpace.inclusionInDoubleDual 𝕜 A`. Virtual diagonals linearize
approximate diagonals into a single element of `(A ⊗̂π A)**`: they give B. E. Johnson's bidual
characterization of amenable Banach algebras and allow derivation innerness and kernel corrections
to be carried out algebraically without repeated weak-star limits.

Because `Δ` intertwines the outer actions with left and right multiplication on `A`, the
commutation law `a · M = M · a` automatically gives the symmetric identity `Δ** M · a = J_A a`,
and `Δ** M` is a mixed identity of `A**` for the two Arens products (`arensMul 𝕜 A F (Δ** M) = F`
and `arensMulRev 𝕜 A (Δ** M) F = F`).

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

* `TauCeti.isVirtualDiagonal_iff`: pointwise characterization of `IsVirtualDiagonal` on
  `(A ⊗̂π A)*` and `A*`.
* `TauCeti.IsVirtualDiagonal.dualAction_mul_flip_precomp_mul'`,
  `TauCeti.IsVirtualDiagonal.arensMul_precomp_mul'`,
  `TauCeti.IsVirtualDiagonal.arensMulRev_precomp_mul'`: right-action symmetry and mixed-identity
  laws for `Δ** M`.
* `TauCeti.IsApproximateDiagonal.isVirtualDiagonal_of_mapClusterPt`,
  `TauCeti.IsApproximateDiagonal.isVirtualDiagonal_inclusionInDoubleDual`, and
  `TauCeti.IsApproximateDiagonal.exists_isVirtualDiagonal`: passage from approximate diagonals to
  virtual diagonals.
* `TauCeti.IsVirtualDiagonal.exists_isApproximateDiagonal`: passage from a virtual diagonal `M` to
  an approximate diagonal bounded by `‖M‖`.
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

end IsVirtualDiagonal

/-- Pointwise characterization of a virtual diagonal by its functional equations on `(A ⊗̂π A)*` and
`A*`. -/
theorem isVirtualDiagonal_iff
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))} :
    IsVirtualDiagonal 𝕜 M ↔
      (∀ (a : A) (φ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        M (φ.comp (mulLeft 𝕜 A a)) = M (φ.comp (mulRight 𝕜 A a))) ∧
      ∀ (a : A) (f : StrongDual 𝕜 A),
        M ((f.comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A)) = f a :=
  ⟨fun hM ↦ ⟨hM.apply_comp_mulLeft_eq_mulRight, hM.apply_comp_mul_comp_mul'⟩,
    fun ⟨hcomm, hmul⟩ ↦
      { dualAction_mulLeft_eq_mulRight a := ext fun φ ↦ by
          simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply] using
            hcomm a φ
        dualAction_mul_precomp_mul' a := ext fun f ↦ by
          simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply,
            dual_def] using hmul a f }⟩

namespace IsVirtualDiagonal

section Algebraic

variable {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}

/-- Construct a virtual diagonal from its pointwise functional equations on `(A ⊗̂π A)*` and
`A*`. -/
theorem of_forall_apply
    (hcomm : ∀ (a : A) (φ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      M (φ.comp (mulLeft 𝕜 A a)) = M (φ.comp (mulRight 𝕜 A a)))
    (hmul : ∀ (a : A) (f : StrongDual 𝕜 A),
      M ((f.comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A)) = f a) :
    IsVirtualDiagonal 𝕜 M :=
  isVirtualDiagonal_iff.2 ⟨hcomm, hmul⟩

/-- Pointwise right-multiplication identity for a virtual diagonal:
`M (f ∘ (· * a) ∘ Δ) = f a` for every `f ∈ A*`. -/
theorem apply_comp_mul_flip_comp_mul' (hM : IsVirtualDiagonal 𝕜 M) (a : A) (f : StrongDual 𝕜 A) :
    M ((f.comp ((ContinuousLinearMap.mul 𝕜 A).flip a)).comp (mul' 𝕜 A)) = f a := by
  rw [comp_assoc, ← mul'_comp_mulRight, ← comp_assoc, ← hM.apply_comp_mulLeft_eq_mulRight a,
    comp_assoc, mul'_comp_mulLeft, ← comp_assoc, hM.apply_comp_mul_comp_mul']

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
    rwa [comp_sub, map_sub, sub_eq_zero] at h0
  · refine hM.apply_eq_of_tendsto_inclusionInDoubleDual _ ?_
    simpa only [Function.comp_def, comp_apply, mul_apply'] using
      (f.continuous.tendsto a).comp (hl.tendsto_mul_mul' a)

/-- If the constant filter `pure m` on `A ⊗̂π A` is an approximate diagonal, then the canonical
bidual image of `m` is a virtual diagonal. -/
theorem IsApproximateDiagonal.isVirtualDiagonal_inclusionInDoubleDual
    {m : CompletedProjectiveTensor 𝕜 A A} (hm : IsApproximateDiagonal 𝕜 (pure m)) :
    IsVirtualDiagonal 𝕜 (inclusionInDoubleDual 𝕜 _ m) :=
  hm.isVirtualDiagonal_of_mapClusterPt
    (tendsto_pure_nhds (fun x ↦ StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 _ x)) m).mapClusterPt

/-- Over a proper scalar field, a Banach algebra with an approximate diagonal bounded by `C` has a
virtual diagonal of norm at most `C`. -/
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

/-- Over `ℝ` or `ℂ`, every virtual diagonal `M` of a Banach algebra `A` yields an approximate
diagonal bounded by `‖M‖`. -/
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
  have hS_inl (a : s) : S (.inl a) = mulLeft 𝕜 A a.1 - mulRight 𝕜 A a.1 := rfl
  have hS_inr (a : s) : S (.inr a) = ContinuousLinearMap.mul 𝕜 A a.1 ∘L mul' 𝕜 A := rfl
  have hz_inl (a : s) : z (.inl a) = 0 := rfl
  have hz_inr (a : s) : z (.inr a) = a.1 := rfl
  have hz : ∀ i (f : StrongDual 𝕜 (Z i)), M (f.comp (S i)) = f (z i) := by
    rintro (a | a) f
    · rw [hS_inl a, hz_inl a, comp_sub, map_sub, hM.apply_comp_mulLeft_eq_mulRight, sub_self,
        map_zero]
    · rw [hS_inr a, hz_inr a]
      exact hM.apply_comp_mul_comp_mul' a.1 f
  obtain ⟨m, hm, happrox⟩ := M.exists_norm_le_and_forall_norm_sub_lt S z hz le_rfl hε
  refine ⟨m, hm, fun a ha ↦ ?_⟩
  have h₁ := happrox (.inl ⟨a, ha⟩)
  have h₂ := happrox (.inr ⟨a, ha⟩)
  rw [hS_inl ⟨a, ha⟩, hz_inl ⟨a, ha⟩, sub_zero, sub_apply] at h₁
  rw [hS_inr ⟨a, ha⟩, hz_inr ⟨a, ha⟩, comp_apply, mul_apply'] at h₂
  exact ⟨h₁, h₂⟩

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

/-- In a zero Banach algebra, `0` is a virtual diagonal. -/
theorem isVirtualDiagonal_zero :
    IsVirtualDiagonal 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) := by
  simpa using (isApproximateDiagonal_pure_zero 𝕜 (A := A)).isVirtualDiagonal_inclusionInDoubleDual

end Subsingleton

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- In a unital Banach algebra, the canonical bidual image of a diagonal `m ∈ A ⊗̂π A` is a virtual
diagonal. -/
theorem isVirtualDiagonal_inclusionInDoubleDual {m : CompletedProjectiveTensor 𝕜 A A}
    (hm : ∀ a, mulLeft 𝕜 A a m = mulRight 𝕜 A a m) (h1 : mul' 𝕜 A m = 1) :
    IsVirtualDiagonal 𝕜 (inclusionInDoubleDual 𝕜 _ m) :=
  (isApproximateDiagonal_pure hm h1).isVirtualDiagonal_inclusionInDoubleDual

variable (𝕜) in
/-- For a complete base field over itself, the canonical bidual image of `1 ⊗ 1` is a virtual
diagonal. -/
theorem isVirtualDiagonal_inclusionInDoubleDual_one_tmul_one [CompleteSpace 𝕜] :
    IsVirtualDiagonal 𝕜
      (inclusionInDoubleDual 𝕜 _
        ((⟨1 ⊗ₜ 1⟩ : ProjectiveTensor 𝕜 𝕜 𝕜) : CompletedProjectiveTensor 𝕜 𝕜 𝕜)) :=
  (isApproximateDiagonal_pure_one_tmul_one 𝕜).isVirtualDiagonal_inclusionInDoubleDual

end Unital

end Examples

end TauCeti
