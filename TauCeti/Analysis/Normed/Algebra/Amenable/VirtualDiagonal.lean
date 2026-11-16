/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Bilinear
import Mathlib.Analysis.Normed.Module.TransferInstance
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
import TauCeti.Analysis.Normed.Ring.ApproximateUnit

/-!
# Virtual diagonals and Johnson's characterization of amenability

A *virtual diagonal* of a Banach algebra `A` over `𝕜` is an element `M` of the bidual
`(A ⊗̂π A)**` satisfying `a · M = M · a` and `a · Δ**(M) = J_A(a)` for every `a ∈ A`, where
`Δ : A ⊗̂π A →L[𝕜] A` is the multiplication map `CompletedProjectiveTensor.mul' 𝕜 A`,
`J_A : A →L[𝕜] A**` is the canonical bidual embedding `NormedSpace.inclusionInDoubleDual 𝕜 A`, and
the bidual actions are the double dual actions of `mulLeft`, `mulRight`, and multiplication on `A`.

This file proves B. E. Johnson's characterizations of amenability for Banach algebras over `ℝ` or
`ℂ`:

1. **Virtual diagonals and bounded approximate diagonals.** Over any proper nontrivially normed
   field, every approximate diagonal bounded by `C` has a weak-star cluster point in `(A ⊗̂π A)**`
   which is a virtual diagonal of norm at most `C`. Conversely, over `ℝ` or `ℂ`, Hahn–Banach
   separation on finite products turns a virtual diagonal `M` into an approximate diagonal bounded
   by `‖M‖`. In particular, a Banach algebra has a virtual diagonal of norm at most `C` if and only
   if it has an approximate diagonal bounded by `C`.
2. **Bounded approximate identities.** Every amenable normed algebra over `ℝ` or `ℂ` has a bounded
   two-sided approximate identity: applying amenability to `A*` with one zero action supplies
   one-sided approximate identities, which Dixon's combination unites into a two-sided one.
3. **Amenability implies a virtual diagonal.** Given a bounded two-sided approximate identity
   `(eᵢ)` bounded by `C`, a weak-star cluster point `E₀ ∈ (A ⊗̂π A)**` of `eᵢ ⊗ eᵢ` satisfies
   `a · Δ**(E₀) = J_A(a) = Δ**(E₀) · a`, so `a ↦ a · E₀ - E₀ · a` is a bounded derivation into
   `ker Δ**`. By Cohen's factorization theorem `Δ` is surjective, so the dual exact sequence
   identifies `ker Δ**` isometrically with `(ker Δ)**`. Applying amenability to `(ker Δ)*` yields
   `N ∈ ker Δ**` implementing this derivation, and `M = E₀ - N` is a virtual diagonal.
4. **Universe independence.** Passing through bounded approximate diagonals shows that in an
   amenable Banach algebra over `ℝ` or `ℂ`, every bounded derivation into the dual of a bounded
   bimodule in any universe is inner, and `H¹(A, E*)` vanishes in every universe.

## Main definitions

* `TauCeti.IsVirtualDiagonal`: virtual diagonals of a Banach algebra.

## Main results

* `TauCeti.exists_isApproximateDiagonal_iff_forall_finset` and
  `TauCeti.exists_isApproximateDiagonal_iff_exists_net`: finite-set and net criteria for bounded
  approximate diagonals.
* `TauCeti.IsApproximateDiagonal.exists_isVirtualDiagonal` and
  `TauCeti.IsVirtualDiagonal.exists_isApproximateDiagonal`: passage between bounded approximate
  diagonals and virtual diagonals preserving the norm bound.
* `TauCeti.exists_isVirtualDiagonal_norm_le_iff_exists_isApproximateDiagonal` and
  `TauCeti.exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal`: equivalence of virtual and
  bounded approximate diagonals.
* `TauCeti.IsAmenable.exists_isApproximateUnit`: every amenable normed algebra over `ℝ` or `ℂ` has
  a bounded two-sided approximate identity.
* `TauCeti.IsAmenable.exists_isVirtualDiagonal`: every amenable Banach algebra over `ℝ` or `ℂ` has
  a virtual diagonal.
* `TauCeti.isAmenable_iff_exists_isVirtualDiagonal` and
  `TauCeti.isAmenable_iff_exists_isApproximateDiagonal`: Johnson's characterization of amenability.
* `TauCeti.IsAmenable.exists_eq_dualAction_sub_dualAction_univ` and
  `TauCeti.IsAmenable.subsingleton_hochschildBimoduleCohomology_one`: universe-polymorphic
  vanishing of `H¹(A, E*)` for amenable Banach algebras.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, Proposition 2.2.1 and Theorem 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

noncomputable section

universe u v w

open Filter Topology Metric ContinuousLinearMap NormedSpace
open scoped TensorProduct

namespace TauCeti

open CompletedProjectiveTensor

-- Shorten instance search for iterated strong duals in public signatures and proofs.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup ContinuousLinearMap.strongBidualNormedSpace

/-! ### Virtual diagonals -/

section VirtualDiagonal

variable (𝕜 : Type*) {A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- A *virtual diagonal* of a Banach algebra `A` is an element `M` of the bidual `(A ⊗̂π A)**`
commuting with every `a ∈ A` under the bidual outer actions (`a · M = M · a`) and satisfying
`a · Δ**(M) = J_A(a)` for every `a ∈ A`, where `Δ = CompletedProjectiveTensor.mul' 𝕜 A`. -/
structure IsVirtualDiagonal
    (M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) : Prop where
  /-- `M` commutes with every element of `A` under the bidual outer actions. -/
  dualAction_mulLeft_eq_mulRight (a : A) :
    dualAction (dualAction (mulLeft 𝕜 A)) a M =
      dualAction (dualAction (mulRight 𝕜 A)) a M
  /-- Left multiplication by `a` sends `Δ**(M)` to the canonical bidual image of `a`. -/
  dualAction_mul_precomp_precomp_mul' (a : A) :
    dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
      (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = inclusionInDoubleDual 𝕜 A a

variable {𝕜}

/-- `Δ**` intertwines the bidual outer left action on `(A ⊗̂π A)**` with the bidual left
multiplication action on `A**`. -/
private theorem precomp_precomp_mul'_dualAction_mulLeft (a : A)
    (M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) :
    precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) (dualAction (dualAction (mulLeft 𝕜 A)) a M) =
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
        (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) :=
  precomp_dualAction_apply
    (fun b f ↦ precomp_dualAction_apply (fun c m ↦ mul'_mulLeft_apply c m) b f) a M

/-- `Δ**` intertwines the bidual outer right action on `(A ⊗̂π A)**` with the bidual right
multiplication action on `A**`. -/
private theorem precomp_precomp_mul'_dualAction_mulRight (a : A)
    (M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) :
    precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) (dualAction (dualAction (mulRight 𝕜 A)) a M) =
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) a
        (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) :=
  precomp_dualAction_apply
    (fun b f ↦ precomp_dualAction_apply (fun c m ↦ mul'_mulRight_apply c m) b f) a M

namespace IsVirtualDiagonal

/-- Right multiplication by `a` also sends `Δ**(M)` to the canonical bidual image of `a`. -/
theorem dualAction_mul_flip_precomp_precomp_mul'
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) (a : A) :
    dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) a
      (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) M) = inclusionInDoubleDual 𝕜 A a := by
  rw [← precomp_precomp_mul'_dualAction_mulRight, ← hM.dualAction_mulLeft_eq_mulRight a,
    precomp_precomp_mul'_dualAction_mulLeft, hM.dualAction_mul_precomp_precomp_mul']

/-- On a trivial Banach algebra, every element of the bidual (in particular `0`) is a virtual
diagonal. -/
theorem of_subsingleton [Subsingleton A]
    (M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) :
    IsVirtualDiagonal 𝕜 M where
  dualAction_mulLeft_eq_mulRight a := by
    ext φ
    rw [Subsingleton.elim a 0]
    simp
  dualAction_mul_precomp_precomp_mul' a := by
    ext f
    rw [Subsingleton.elim a 0]
    simp

end IsVirtualDiagonal

/-- When continuous functionals separate points of `A ⊗̂π A` and `A` (in particular over `ℝ` or
`ℂ`), the canonical bidual image of `m : A ⊗̂π A` is a virtual diagonal if and only if
`a · m = m · a` and `a * Δ m = a` for all `a`. -/
theorem isVirtualDiagonal_inclusionInDoubleDual_iff
    [SeparatingDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)] [SeparatingDual 𝕜 A]
    {m : CompletedProjectiveTensor 𝕜 A A} :
    IsVirtualDiagonal 𝕜 (inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 A A) m) ↔
      (∀ a : A, mulLeft 𝕜 A a m = mulRight 𝕜 A a m) ∧ ∀ a : A, a * mul' 𝕜 A m = a := by
  constructor
  · intro h
    refine ⟨fun a ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ ?_,
      fun a ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun f ↦ ?_⟩
    · simpa [dual_def] using congr($(h.dualAction_mulLeft_eq_mulRight a) φ)
    · simpa [dual_def] using congr($(h.dualAction_mul_precomp_precomp_mul' a) f)
  · rintro ⟨hcomm, hmul⟩
    refine ⟨fun a ↦ ?_, fun a ↦ ?_⟩
    · ext φ
      simp [dual_def, hcomm a]
    · ext f
      simp [dual_def, hmul a]

variable (𝕜) in
/-- On the base field `𝕜` over itself, the canonical bidual image of `1 ⊗ 1` is a virtual
diagonal. -/
theorem isVirtualDiagonal_inclusionInDoubleDual_one_tmul_one [CompleteSpace 𝕜] :
    IsVirtualDiagonal 𝕜
      (inclusionInDoubleDual 𝕜 (CompletedProjectiveTensor 𝕜 𝕜 𝕜)
        ((⟨1 ⊗ₜ 1⟩ : ProjectiveTensor 𝕜 𝕜 𝕜) : CompletedProjectiveTensor 𝕜 𝕜 𝕜)) where
  dualAction_mulLeft_eq_mulRight a := by
    ext φ
    simp only [dualAction_apply_apply, dual_def, mulLeft_apply_coe_tmul, mulRight_apply_coe_tmul]
    rw [← smul_eq_mul a 1, TensorProduct.smul_tmul, smul_eq_mul, mul_one, one_mul]
  dualAction_mul_precomp_precomp_mul' a := by
    ext f
    simp [dual_def]

end VirtualDiagonal

/-! ### Finite-set and net criteria for bounded approximate diagonals -/

section Criteria

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- On a trivial Banach algebra, `pure 0` is an approximate diagonal. -/
theorem isApproximateDiagonal_pure_zero [Subsingleton A] :
    IsApproximateDiagonal 𝕜 (pure (0 : CompletedProjectiveTensor 𝕜 A A)) where
  tendsto_mulLeft_sub_mulRight a := by
    simpa [Subsingleton.elim a 0] using
      tendsto_pure_nhds (fun m ↦ mulLeft 𝕜 A a m - mulRight 𝕜 A a m) 0
  tendsto_mul_mul' a := by
    simp [Subsingleton.elim a 0]

/-- An approximate diagonal is a proper filter along which `(a · m - m · a, a * Δ m) → (0, a)`
for every `a`. -/
private theorem isApproximateDiagonal_iff_neBot_and_tendsto_prod
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} :
    IsApproximateDiagonal 𝕜 l ↔
      l.NeBot ∧ ∀ a : A,
        Tendsto (fun m ↦ (mulLeft 𝕜 A a m - mulRight 𝕜 A a m, a * mul' 𝕜 A m)) l (𝓝 (0, a)) := by
  constructor
  · intro h
    exact ⟨h.neBot, fun a ↦
      (h.tendsto_mulLeft_sub_mulRight a).prodMk_nhds (h.tendsto_mul_mul' a)⟩
  · rintro ⟨hl, h⟩
    exact
      { tendsto_mulLeft_sub_mulRight := fun a ↦ by
          simpa [Function.comp_def] using (continuous_fst.tendsto (0, a)).comp (h a)
        tendsto_mul_mul' := fun a ↦ by
          simpa [Function.comp_def] using (continuous_snd.tendsto (0, a)).comp (h a)
        neBot := hl }

/-- A Banach algebra has an approximate diagonal bounded by `C` iff every finite subset is
simultaneously almost commuted with and almost right-fixed by a single tensor of norm at most
`C`. -/
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
      (F := fun a m ↦ (mulLeft 𝕜 A a m - mulRight 𝕜 A a m, a * mul' 𝕜 A m))
      (x := fun a ↦ (0, a))

/-- A Banach algebra has an approximate diagonal bounded by `C` iff it has one in the form of a
net indexed by `Finset A × ℕ`, all of whose terms have norm at most `C`. -/
theorem exists_isApproximateDiagonal_iff_exists_net {C : ℝ} :
    (∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C) ↔
      ∃ m : Finset A × ℕ → CompletedProjectiveTensor 𝕜 A A, (∀ i, ‖m i‖ ≤ C) ∧
        IsApproximateDiagonal 𝕜 (map m atTop) := by
  classical
  simp only [isApproximateDiagonal_iff_neBot_and_tendsto_prod, and_assoc]
  refine (exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm).trans ?_
  simpa [tendsto_map'_iff, Function.comp_def, atTop_neBot.map] using
    exists_neBot_tendsto_iff_exists_net
      (p := fun m : CompletedProjectiveTensor 𝕜 A A ↦ ‖m‖ ≤ C)
      (F := fun a m ↦ (mulLeft 𝕜 A a m - mulRight 𝕜 A a m, a * mul' 𝕜 A m))
      (x := fun a ↦ (0, a))

end Criteria

/-! ### Equivalence of virtual diagonals and bounded approximate diagonals -/

section VirtualApproxEquiv

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- Every approximate diagonal bounded by `C` has a weak-star cluster point in `(A ⊗̂π A)**` which
is a virtual diagonal of norm at most `C`. -/
theorem IsApproximateDiagonal.exists_isVirtualDiagonal [ProperSpace 𝕜]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M ∧ ‖M‖ ≤ C := by
  have := h.neBot
  obtain ⟨M, hMC, hM⟩ := hC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜)
  refine ⟨M, ⟨fun a ↦ ?_, fun a ↦ ?_⟩, hMC⟩
  · ext φ
    -- `M` vanishes on `a · φ - φ · a`, since `(a · φ - φ · a) m = φ (a · m - m · a) → 0`.
    have h0 : M (dualAction (mulLeft 𝕜 A) a φ - dualAction (mulRight 𝕜 A) a φ) = 0 := by
      refine hM.apply_eq_of_tendsto_inclusionInDoubleDual _ ?_
      have hφ := (φ.continuous.tendsto 0).comp (h.tendsto_mulLeft_sub_mulRight a)
      simpa [Function.comp_def] using hφ
    rw [map_sub, sub_eq_zero] at h0
    simpa only [dualAction_apply_apply] using h0
  · ext f
    simp only [dualAction_apply_apply, precomp_apply, comp_apply, dual_def]
    refine hM.apply_eq_of_tendsto_inclusionInDoubleDual
      (precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A) a f)) ?_
    simpa [Function.comp_def] using (f.continuous.tendsto a).comp (h.tendsto_mul_mul' a)

/-- **Virtual diagonal implies bounded approximate diagonal.** Over `ℝ` or `ℂ`, a virtual diagonal
`M` gives an approximate diagonal bounded by `‖M‖`, via Hahn–Banach separation on finite
products. -/
theorem IsVirtualDiagonal.exists_isApproximateDiagonal {𝕜 A : Type*} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) :
    ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
      IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ ‖M‖ := by
  classical
  rw [exists_isApproximateDiagonal_iff_forall_finset]
  intro s ε hε
  set X := CompletedProjectiveTensor 𝕜 A A
  let T : X →L[𝕜] (s → X) × (s → A) :=
    (ContinuousLinearMap.pi fun a : s ↦ mulLeft 𝕜 A a.1 - mulRight 𝕜 A a.1).prod
      (ContinuousLinearMap.pi fun a : s ↦ ContinuousLinearMap.mul 𝕜 A a.1 ∘L mul' 𝕜 A)
  let y : (s → X) × (s → A) := (0, fun a : s ↦ a.1)
  -- `T** M = J y`: decompose any functional `ψ` on `(s → X) × (s → A)` into coordinate functionals.
  have hTM : precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 ((s → X) × (s → A)) →L[𝕜] StrongDual 𝕜 X) M =
      inclusionInDoubleDual 𝕜 ((s → X) × (s → A)) y := by
    ext ψ
    let ψ₁ : StrongDual 𝕜 (s → X) := ψ.comp (.inl 𝕜 (s → X) (s → A))
    let ψ₂ : StrongDual 𝕜 (s → A) := ψ.comp (.inr 𝕜 (s → X) (s → A))
    let φ₁ : s → StrongDual 𝕜 X := fun a ↦ ψ₁.comp (.single 𝕜 (fun _ : s ↦ X) a)
    let f₂ : s → StrongDual 𝕜 A := fun a ↦ ψ₂.comp (.single 𝕜 (fun _ : s ↦ A) a)
    have hcomp : ψ.comp T =
        ∑ a : s, (dualAction (mulLeft 𝕜 A) a.1 (φ₁ a) - dualAction (mulRight 𝕜 A) a.1 (φ₁ a)) +
        ∑ a : s, precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A) a.1 (f₂ a)) := by
      refine ContinuousLinearMap.ext fun m ↦ ?_
      have hsplit : ψ (T m) = ψ₁ (T m).1 + ψ₂ (T m).2 := by
        simp [ψ₁, ψ₂, ← map_add]
      rw [comp_apply, hsplit, ← ψ₁.sum_comp_single, ← ψ₂.sum_comp_single]
      simp [T, φ₁, f₂, sum_apply, map_sub, Finset.sum_sub_distrib]
    have hcomm (a : s) :
        M (dualAction (mulLeft 𝕜 A) a.1 (φ₁ a) - dualAction (mulRight 𝕜 A) a.1 (φ₁ a)) = 0 := by
      rw [map_sub, sub_eq_zero]
      simpa only [dualAction_apply_apply] using
        congr($(hM.dualAction_mulLeft_eq_mulRight a.1) (φ₁ a))
    have hmul (a : s) :
        M (precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A) a.1 (f₂ a))) =
          f₂ a a.1 := by
      simpa [dual_def] using congr($(hM.dualAction_mul_precomp_precomp_mul' a.1) (f₂ a))
    have hψy : ψ y = ∑ a : s, f₂ a a.1 := by
      have hy : ψ y = ψ₂ (fun a : s ↦ a.1) := rfl
      rw [hy, ← ψ₂.sum_comp_single]
    rw [precomp_apply, comp_apply, precomp_apply, dual_def, hcomp, map_add, map_sum, map_sum]
    simp only [hcomm, Finset.sum_const_zero, zero_add, hmul, hψy]
  -- Hahn–Banach separation places `y` in the norm closure of `T '' closedBall 0 ‖M‖`.
  have hy_mem := T.mem_closure_image_closedBall_of_precomp_precomp_eq le_rfl hTM
  obtain ⟨_, ⟨m, hm, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hy_mem ε hε
  refine ⟨m, mem_closedBall_zero_iff.1 hm, fun a ha ↦ ?_⟩
  rw [dist_comm, Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε, dist_pi_lt_iff hε] at hdist
  exact ⟨by simpa [T, y, dist_eq_norm] using hdist.1 ⟨a, ha⟩,
    by simpa [T, y, dist_eq_norm] using hdist.2 ⟨a, ha⟩⟩

/-- A Banach algebra over `ℝ` or `ℂ` has a virtual diagonal of norm at most `C` if and only if
it has an approximate diagonal bounded by `C`. -/
theorem exists_isVirtualDiagonal_norm_le_iff_exists_isApproximateDiagonal {𝕜 A : Type*} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] {C : ℝ} :
    (∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M ∧ ‖M‖ ≤ C) ↔
      ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C := by
  constructor
  · rintro ⟨M, hM, hMC⟩
    obtain ⟨l, hl, hMl⟩ := hM.exists_isApproximateDiagonal
    exact ⟨l, hl, hMl.mono fun m hm ↦ hm.trans hMC⟩
  · rintro ⟨l, hl, hC⟩
    exact hl.exists_isVirtualDiagonal hC

/-- A Banach algebra over `ℝ` or `ℂ` has a virtual diagonal if and only if it has a bounded
approximate diagonal. -/
theorem exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal {𝕜 A : Type*} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] :
    (∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M) ↔
      ∃ (l : Filter (CompletedProjectiveTensor 𝕜 A A)) (C : ℝ),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨l, hl, hMl⟩ := hM.exists_isApproximateDiagonal
    exact ⟨l, ‖M‖, hl, hMl⟩
  · rintro ⟨l, C, hl, hC⟩
    obtain ⟨M, hM, -⟩ := hl.exists_isVirtualDiagonal hC
    exact ⟨M, hM⟩

/-- Every bounded derivation from a Banach algebra with a virtual diagonal into the dual of a
bounded bimodule (in any universe) is inner. -/
theorem IsVirtualDiagonal.exists_eq_dualAction_sub_dualAction {𝕜 A E : Type*} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  obtain ⟨l, hl, hC⟩ := hM.exists_isApproximateDiagonal
  exact hl.exists_eq_dualAction_sub_dualAction hC hL hR hLR D hD

/-- A Banach algebra over `ℝ` or `ℂ` with a virtual diagonal is amenable. -/
theorem IsVirtualDiagonal.isAmenable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) : IsAmenable 𝕜 A :=
  let ⟨_, hl, hC⟩ := hM.exists_isApproximateDiagonal
  hl.isAmenable hC

end VirtualApproxEquiv

/-! ### Universe transfer and bounded approximate identities for amenable algebras -/

section AmenableBAI

variable {𝕜 : Type v} {A : Type u} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A]

/-- A trivial normed algebra is amenable. -/
theorem IsAmenable.of_subsingleton [Subsingleton A] : IsAmenable 𝕜 A :=
  isAmenable_def.2 fun _ _ _ _ _ _ _ _ _ D _ ↦ ⟨0, fun a ↦ by rw [Subsingleton.elim a 0]; simp⟩

/-- Pulling back a bounded bilinear action along a linear isometry equivalence `φ : E' ≃ₗᵢ[𝕜] E`. -/
private def conjAction {E E' : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] (φ : E' ≃ₗᵢ[𝕜] E)
    (M : A →L[𝕜] E →L[𝕜] E) : A →L[𝕜] E' →L[𝕜] E' :=
  LinearMap.mkContinuous
    { toFun a :=
        φ.symm.toLinearIsometry.toContinuousLinearMap ∘L M a ∘L
          φ.toLinearIsometry.toContinuousLinearMap
      map_add' a b := by ext x; simp
      map_smul' c a := by ext x; simp }
    ‖M‖ fun a ↦ opNorm_le_bound _ (mul_nonneg (norm_nonneg M) (norm_nonneg a)) fun x ↦ by
      simpa using M.le_opNorm₂ a (φ x)

/-- Transport innerness of derivations along a linear isometry equivalence of bimodules. -/
private theorem exists_eq_dualAction_sub_dualAction_of_linearIsometryEquiv
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (φ : E' ≃ₗᵢ[𝕜] E)
    (hE' : ∀ (L' R' : A →L[𝕜] E' →L[𝕜] E'),
      (∀ a b x, L' (a * b) x = L' a (L' b x)) →
      (∀ a b x, R' (a * b) x = R' b (R' a x)) →
      (∀ a b x, L' a (R' b x) = R' b (L' a x)) →
      ∀ D' : A →L[𝕜] StrongDual 𝕜 E',
        (∀ a b, D' (a * b) = dualAction R' a (D' b) + dualAction L' b (D' a)) →
        ∃ ψ : StrongDual 𝕜 E', ∀ a, D' a = dualAction R' a ψ - dualAction L' a ψ)
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ ψ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a ψ - dualAction L a ψ := by
  let L' := conjAction φ L
  let R' := conjAction φ R
  have hφL (a : A) (x : E') : φ (L' a x) = L a (φ x) := by simp [L', conjAction]
  have hφR (a : A) (x : E') : φ (R' a x) = R a (φ x) := by simp [R', conjAction]
  let D' : A →L[𝕜] StrongDual 𝕜 E' :=
    (precomp 𝕜 φ.toLinearIsometry.toContinuousLinearMap :
      StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E') ∘L D
  have hD' (a b : A) : D' (a * b) = dualAction R' a (D' b) + dualAction L' b (D' a) := by
    ext x
    have := congr($(hD a b) (φ x))
    simpa [D', hφL, hφR] using this
  obtain ⟨ψ', hψ'⟩ := hE' L' R'
    (fun a b x ↦ by apply φ.injective; simp [hφL, hL])
    (fun a b x ↦ by apply φ.injective; simp [hφR, hR])
    (fun a b x ↦ by apply φ.injective; simp [hφL, hφR, hLR])
    D' hD'
  refine ⟨ψ'.comp φ.symm.toLinearIsometry.toContinuousLinearMap, fun a ↦ ?_⟩
  ext x
  have := congr($(hψ' a) (φ.symm x))
  simpa [D', L', R', conjAction] using this

/-- In an amenable normed algebra `A : Type u`, every bounded derivation into the dual of a Banach
bimodule `E : Type w` that is `Small.{u}` is inner. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction_of_small (h : IsAmenable 𝕜 A)
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Small.{u} E]
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ ψ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a ψ - dualAction L a ψ := by
  let e : Shrink.{u} E ≃ E := (equivShrink E).symm
  let : NormedAddCommGroup (Shrink.{u} E) := e.normedAddCommGroup
  let ea : Shrink.{u} E ≃+ E :=
    { toEquiv := e
      map_add' _ _ := e.apply_symm_apply _ }
  let : Module 𝕜 (Shrink.{u} E) := ea.module 𝕜
  let : NormedSpace 𝕜 (Shrink.{u} E) :=
    { norm_smul_le c x := by
        change ‖e (c • x)‖ ≤ ‖c‖ * ‖e x‖
        rw [show e (c • x) = c • e x from (ea.linearEquiv 𝕜).map_smul c x]
        exact norm_smul_le c (e x) }
  let φ : Shrink.{u} E ≃ₗᵢ[𝕜] E :=
    { toLinearEquiv := ea.linearEquiv 𝕜
      norm_map' _ := rfl }
  have : CompleteSpace (Shrink.{u} E) := ⟨fun {f} hf ↦ by
    obtain ⟨y, hy⟩ := CompleteSpace.complete (hf.map φ.isometry.uniformContinuous)
    refine ⟨φ.symm y, ?_⟩
    have h1 : Tendsto (φ.symm ∘ φ) f (𝓝 (φ.symm y)) :=
      (φ.symm.continuous.tendsto y).comp hy
    rwa [Tendsto, show φ.symm ∘ φ = id from funext φ.symm_apply_apply, Filter.map_id] at h1⟩
  exact exists_eq_dualAction_sub_dualAction_of_linearIsometryEquiv φ
    (fun L' R' hL' hR' hLR' D' hD' ↦
      h.exists_eq_dualAction_sub_dualAction hL' hR' hLR' D' hD')
    hL hR hLR D hD

/-- Over a nontrivial normed algebra `A : Type u`, the scalar field `𝕜` is `Small.{u}`. -/
private theorem small_field_of_nontrivial [Nontrivial A] : Small.{u} 𝕜 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  exact small_of_injective (smul_left_injective 𝕜 ha)

/-- If `X : Type u` and `A : Type u` is nontrivial, then `StrongDual 𝕜 X` is `Small.{u}`. -/
private theorem small_strongDual_of_nontrivial [Nontrivial A] (X : Type u)
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] : Small.{u} (StrongDual 𝕜 X) := by
  have : Small.{u} 𝕜 := small_field_of_nontrivial (A := A)
  exact small_of_injective DFunLike.coe_injective

/-- Hahn–Banach separation on a finite product: if `Φ ∈ A**` satisfies `Φ (dualAction B a f) = f a`
for a bounded bilinear operator `B : A →L[𝕜] A →L[𝕜] A`, then for every finite set `s` and `ε > 0`
there is `e ∈ A` with `‖e‖ ≤ ‖Φ‖` and `‖B a e - a‖ < ε` for all `a ∈ s`. -/
private theorem exists_norm_le_and_forall_sub_lt_of_bidual {𝕜 A : Type*} [RCLike 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] {B : A →L[𝕜] A →L[𝕜] A}
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 A)} (hΦ : ∀ a f, Φ (dualAction B a f) = f a)
    (s : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : A, ‖e‖ ≤ ‖Φ‖ ∧ ∀ a ∈ s, ‖B a e - a‖ < ε := by
  classical
  let T : A →L[𝕜] (s → A) := ContinuousLinearMap.pi fun a : s ↦ B a.1
  let y : s → A := fun a : s ↦ a.1
  have hTΦ : precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 (s → A) →L[𝕜] StrongDual 𝕜 A) Φ =
      inclusionInDoubleDual 𝕜 (s → A) y := by
    ext ψ
    have hcomp : ψ.comp T = ∑ a : s, dualAction B a.1 (ψ.comp (.single 𝕜 (fun _ : s ↦ A) a)) := by
      ext e
      rw [comp_apply, ← ψ.sum_comp_single]
      simp [T, sum_apply]
    have hψy : ψ y = ∑ a : s, (ψ.comp (.single 𝕜 (fun _ : s ↦ A) a)) a.1 := by
      rw [← ψ.sum_comp_single]
    simp only [precomp_apply, comp_apply, dual_def, hcomp, map_sum, hΦ, hψy]
  obtain ⟨_, ⟨e, he, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1
    (T.mem_closure_image_closedBall_of_precomp_precomp_eq le_rfl hTΦ) ε hε
  refine ⟨e, mem_closedBall_zero_iff.1 he, fun a ha ↦ ?_⟩
  rw [dist_comm, dist_pi_lt_iff hε] at hdist
  simpa [T, y, dist_eq_norm] using hdist ⟨a, ha⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded right approximate identity. -/
theorem IsAmenable.exists_tendsto_mul_left {𝕜 : Type v} {A : Type u} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    (h : IsAmenable 𝕜 A) :
    ∃ (l : Filter A) (C : ℝ), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧
      ∀ a, Tendsto (a * ·) l (𝓝 a) := by
  by_cases hA : Subsingleton A
  · refine ⟨pure 0, 0, inferInstance, eventually_pure.2 (by simp), fun a ↦ ?_⟩
    simp [Subsingleton.elim a 0]
  have : Nontrivial A := not_subsingleton_iff_nontrivial.1 hA
  have : Small.{u} (StrongDual 𝕜 A) := small_strongDual_of_nontrivial (A := A) A
  -- Apply amenability to `E = A*` with left action `0` and right action `dualAction (mul 𝕜 A)`.
  let R : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A :=
    dualAction (ContinuousLinearMap.mul 𝕜 A)
  have hR : ∀ a b φ, R (a * b) φ = R b (R a φ) :=
    dualAction_mul_apply_of_left fun a b c ↦ mul_assoc a b c
  have hD : ∀ a b : A, inclusionInDoubleDual 𝕜 A (a * b) =
      dualAction R a (inclusionInDoubleDual 𝕜 A b) +
        dualAction (0 : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A) b
          (inclusionInDoubleDual 𝕜 A a) := fun a b ↦ by
    ext f
    simp [R, dual_def]
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_dualAction_sub_dualAction_of_small
    (L := 0) (R := R) (fun _ _ _ ↦ by simp) hR (fun _ _ _ ↦ by simp)
    (inclusionInDoubleDual 𝕜 A) hD
  have hΦ' (a : A) (f : StrongDual 𝕜 A) :
      Φ (dualAction (ContinuousLinearMap.mul 𝕜 A) a f) = f a := by
    have := congr($(hΦ a) f)
    simpa [R, dual_def] using this.symm
  obtain ⟨l, hl⟩ := exists_tendsto_mul_left_iff_forall_finset.2 fun s ε hε ↦
    exists_norm_le_and_forall_sub_lt_of_bidual hΦ' s hε
  exact ⟨l, ‖Φ‖, hl⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded left approximate identity. -/
theorem IsAmenable.exists_tendsto_mul_right {𝕜 : Type v} {A : Type u} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    (h : IsAmenable 𝕜 A) :
    ∃ (l : Filter A) (C : ℝ), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧
      ∀ a, Tendsto (· * a) l (𝓝 a) := by
  by_cases hA : Subsingleton A
  · refine ⟨pure 0, 0, inferInstance, eventually_pure.2 (by simp), fun a ↦ ?_⟩
    simp [Subsingleton.elim a 0]
  have : Nontrivial A := not_subsingleton_iff_nontrivial.1 hA
  have : Small.{u} (StrongDual 𝕜 A) := small_strongDual_of_nontrivial (A := A) A
  -- Apply amenability to `E = A*` with left action `(mul 𝕜 A).flip*` and right action `0`.
  let L : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A :=
    dualAction (ContinuousLinearMap.mul 𝕜 A).flip
  have hL : ∀ a b φ, L (a * b) φ = L a (L b φ) :=
    dualAction_mul_apply_of_right fun a b c ↦ (mul_assoc c a b).symm
  have hD : ∀ a b : A, inclusionInDoubleDual 𝕜 A (a * b) =
      dualAction (0 : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A) a
          (inclusionInDoubleDual 𝕜 A b) +
        dualAction L b (inclusionInDoubleDual 𝕜 A a) := fun a b ↦ by
    ext f
    simp [L, dual_def]
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_dualAction_sub_dualAction_of_small
    (L := L) (R := 0) hL (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (inclusionInDoubleDual 𝕜 A) hD
  let Ψ := -Φ
  have hΨ (a : A) (f : StrongDual 𝕜 A) :
      Ψ (dualAction (ContinuousLinearMap.mul 𝕜 A).flip a f) = f a := by
    have := congr($(hΦ a) f)
    simpa [Ψ, L, dual_def] using this.symm
  obtain ⟨l, hl⟩ := exists_tendsto_mul_right_iff_forall_finset.2 fun s ε hε ↦
    exists_norm_le_and_forall_sub_lt_of_bidual hΨ s hε
  exact ⟨l, ‖Ψ‖, hl⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded two-sided approximate identity. -/
theorem IsAmenable.exists_isApproximateUnit {𝕜 : Type v} {A : Type u} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    (h : IsAmenable 𝕜 A) :
    ∃ (l : Filter A) (C : ℝ), l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C := by
  obtain ⟨l₁, C₁, h₁, hC₁, hl₁⟩ := h.exists_tendsto_mul_right
  obtain ⟨l₂, C₂, h₂, hC₂, hl₂⟩ := h.exists_tendsto_mul_left
  obtain ⟨l, hl, hC⟩ :=
    exists_isApproximateUnit_of_left_of_right ⟨l₁, h₁, hC₁, hl₁⟩ ⟨l₂, h₂, hC₂, hl₂⟩
  exact ⟨l, C₁ + C₂ + C₁ * C₂, hl, hC⟩

end AmenableBAI

/-! ### Johnson's characterization of amenability -/

section Johnson

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Along an eventually bounded right approximate identity, `a * (e * e) → a`. -/
private theorem tendsto_mul_mul_self_of_tendsto_mul_left {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) {a : A} (ha : Tendsto (a * ·) l (𝓝 a)) :
    Tendsto (fun e ↦ a * (e * e)) l (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at ha ⊢
  have hdom : Tendsto (fun e ↦ (|C| + 1) * ‖a * e - a‖) l (𝓝 0) := by
    simpa using ha.const_mul (|C| + 1)
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hdom
  filter_upwards [hC] with e he
  have hid : a * (e * e) - a = (a * e - a) * e + (a * e - a) := by
    simp only [sub_mul, mul_assoc]
    abel
  calc ‖a * (e * e) - a‖
      = ‖(a * e - a) * e + (a * e - a)‖ := by rw [hid]
    _ ≤ ‖(a * e - a) * e‖ + ‖a * e - a‖ := norm_add_le _ _
    _ ≤ ‖a * e - a‖ * ‖e‖ + ‖a * e - a‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖a * e - a‖ * |C| + ‖a * e - a‖ := by gcongr; exact he.trans (le_abs_self C)
    _ = (|C| + 1) * ‖a * e - a‖ := by ring

omit [CompleteSpace A] in
/-- Along an eventually bounded left approximate identity, `(e * e) * a → a`. -/
private theorem tendsto_mul_self_mul_of_tendsto_mul_right {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) {a : A} (ha : Tendsto (· * a) l (𝓝 a)) :
    Tendsto (fun e ↦ (e * e) * a) l (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at ha ⊢
  have hdom : Tendsto (fun e ↦ (|C| + 1) * ‖e * a - a‖) l (𝓝 0) := by
    simpa using ha.const_mul (|C| + 1)
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hdom
  filter_upwards [hC] with e he
  have hid : (e * e) * a - a = e * (e * a - a) + (e * a - a) := by
    simp only [mul_sub, mul_assoc]
    abel
  calc ‖(e * e) * a - a‖
      = ‖e * (e * a - a) + (e * a - a)‖ := by rw [hid]
    _ ≤ ‖e * (e * a - a)‖ + ‖e * a - a‖ := norm_add_le _ _
    _ ≤ ‖e‖ * ‖e * a - a‖ + ‖e * a - a‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ |C| * ‖e * a - a‖ + ‖e * a - a‖ := by gcongr; exact he.trans (le_abs_self C)
    _ = (|C| + 1) * ‖e * a - a‖ := by ring

/-- A weak-star cluster point `E₀ ∈ (A ⊗̂π A)**` of `e ⊗ e` along a bounded two-sided approximate
identity satisfies `a · Δ**(E₀) = J_A(a) = Δ**(E₀) · a`. -/
private theorem exists_bidual_mul'_eq_inclusionInDoubleDual {l : Filter A}
    (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    ∃ E₀ : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      (∀ a, dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
        (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) E₀) = inclusionInDoubleDual 𝕜 A a) ∧
      (∀ a, dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) a
        (precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) E₀) = inclusionInDoubleDual 𝕜 A a) := by
  have := hl.neBot
  let p : A → CompletedProjectiveTensor 𝕜 A A := fun e ↦ (⟨e ⊗ₜ e⟩ : ProjectiveTensor 𝕜 A A)
  have hpC : ∀ᶠ m in l.map p, ‖m‖ ≤ C * C := by
    rw [eventually_map]
    filter_upwards [hC] with e he
    exact (norm_coe_tmul_le e e).trans <|
      mul_le_mul he he (norm_nonneg e) ((norm_nonneg e).trans he)
  obtain ⟨E₀, -, hE₀⟩ := hpC.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜)
  refine ⟨E₀, fun a ↦ ?_, fun a ↦ ?_⟩
  · ext f
    simp only [dualAction_apply_apply, precomp_apply, comp_apply, dual_def]
    refine hE₀.apply_eq_of_tendsto_inclusionInDoubleDual
      (precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A) a f)) ?_
    rw [tendsto_map'_iff]
    simpa [Function.comp_def, p] using (f.continuous.tendsto a).comp
      (tendsto_mul_mul_self_of_tendsto_mul_left hC (hl.tendsto_mul_left a))
  · ext f
    simp only [dualAction_apply_apply, precomp_apply, comp_apply, dual_def]
    refine hE₀.apply_eq_of_tendsto_inclusionInDoubleDual
      (precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A).flip a f)) ?_
    rw [tendsto_map'_iff]
    simpa [Function.comp_def, p] using (f.continuous.tendsto a).comp
      (tendsto_mul_self_mul_of_tendsto_mul_right hC (hl.tendsto_mul_right a))

/-- Pulling the commutator `a ↦ a · E₀ - E₀ · a` back along `(ker T)** ≃ₗᵢ[𝕜] ker T**` yields a
bounded derivation `D : A →L[𝕜] (ker T)**`. -/
private theorem exists_ker_precomp_precomp_derivation
    {𝕜 : Type v} {A X Y : Type u} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (T : X →L[𝕜] Y) (hT : IsClosed (T.range : Set Y))
    {L R : A →L[𝕜] X →L[𝕜] X}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (hTL : ∀ a, ∀ x ∈ T.ker, L a x ∈ T.ker) (hTR : ∀ a, ∀ x ∈ T.ker, R a x ∈ T.ker)
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 X))
    (hE₀ : ∀ a : A,
      precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X)
        (dualAction (dualAction L) a E₀ - dualAction (dualAction R) a E₀) = 0) :
    ∃ D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker),
      (∀ (a : A) (f : StrongDual 𝕜 X),
        D a (f.comp T.ker.subtypeL) =
          (dualAction (dualAction L) a E₀ - dualAction (dualAction R) a E₀) f) ∧
      ∀ a b : A,
        D (a * b) =
          dualAction (dualAction (L.restrictSubmodule T.ker hTL)) a (D b) +
            dualAction (dualAction (R.restrictSubmodule T.ker hTR)) b (D a) := by
  let e := T.kerDoubleDualEquivKerPrecompPrecomp hT
  let D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X) :=
    (dualAction (dualAction L)).flip E₀ - (dualAction (dualAction R)).flip E₀
  have hD₀_der (a b : A) (φ : StrongDual 𝕜 X) :
      D₀ (a * b) φ = D₀ b (dualAction L a φ) + D₀ a (dualAction R b φ) := by
    have hLφ : dualAction L (a * b) φ = dualAction L b (dualAction L a φ) :=
      dualAction_mul_apply_of_left hL a b φ
    have hRφ : dualAction R (a * b) φ = dualAction R a (dualAction R b φ) :=
      dualAction_mul_apply_of_right hR a b φ
    have hcomm : dualAction L a (dualAction R b φ) = dualAction R b (dualAction L a φ) :=
      (dualAction_apply_dualAction_apply_comm hLR b a φ).symm
    simp only [D₀, sub_apply, flip_apply, dualAction_apply_apply, hLφ, hRφ, hcomm]
    ring
  have hD₀_ker (a : A) :
      D₀ a ∈ (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) :
        StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y)).ker :=
    hE₀ a
  let D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker) :=
    e.symm.toLinearIsometry.toContinuousLinearMap ∘L D₀.codRestrict _ hD₀_ker
  have hD_eval (a : A) (f : StrongDual 𝕜 X) : D a (f.comp T.ker.subtypeL) = D₀ a f := by
    have hDa : D a = e.symm ⟨D₀ a, hD₀_ker a⟩ := by
      simp only [D, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry]
      rfl
    rw [hDa, kerDoubleDualEquivKerPrecompPrecomp_symm_apply_comp_subtypeL]
  refine ⟨D, hD_eval, fun a b ↦ ?_⟩
  ext g
  obtain ⟨f, rfl⟩ := T.ker.surjective_precomp_subtypeL g
  have hL' :
      dualAction (L.restrictSubmodule T.ker hTL) a (f.comp T.ker.subtypeL) =
        (dualAction L a f).comp T.ker.subtypeL := by
    ext x; simp
  have hR' :
      dualAction (R.restrictSubmodule T.ker hTR) b (f.comp T.ker.subtypeL) =
        (dualAction R b f).comp T.ker.subtypeL := by
    ext x; simp
  simp only [precomp_apply, add_apply, dualAction_apply_apply, hL', hR', hD_eval]
  exact hD₀_der a b f

/-- Core cohomological lifting step of Johnson's theorem: if `A` is a nontrivial amenable normed
algebra, `T : X →L[𝕜] Y` is a closed-range operator between Banach spaces, `L` and `R` are
commuting bounded `A`-actions on `X` leaving `T.ker` invariant, and `E₀ ∈ X**` has commutator
`a · E₀ - E₀ · a ∈ ker T**` for all `a`, then there exists `N ∈ ker T**` such that `E₀ - N`
commutes with every `a ∈ A`. -/
private theorem IsAmenable.exists_ker_precomp_precomp_comm
    {𝕜 : Type v} {A X Y : Type u} [RCLike 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [Nontrivial A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (h : IsAmenable 𝕜 A) (T : X →L[𝕜] Y) (hT : IsClosed (T.range : Set Y))
    {L R : A →L[𝕜] X →L[𝕜] X}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (hTL : ∀ a, ∀ x ∈ T.ker, L a x ∈ T.ker) (hTR : ∀ a, ∀ x ∈ T.ker, R a x ∈ T.ker)
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 X))
    (hE₀ : ∀ a : A,
      precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X)
        (dualAction (dualAction L) a E₀ - dualAction (dualAction R) a E₀) = 0) :
    ∃ N : StrongDual 𝕜 (StrongDual 𝕜 X),
      precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) N = 0 ∧
      ∀ a : A, dualAction (dualAction L) a (E₀ - N) = dualAction (dualAction R) a (E₀ - N) := by
  let e := T.kerDoubleDualEquivKerPrecompPrecomp hT
  let LK : A →L[𝕜] T.ker →L[𝕜] T.ker := L.restrictSubmodule T.ker hTL
  let RK : A →L[𝕜] T.ker →L[𝕜] T.ker := R.restrictSubmodule T.ker hTR
  obtain ⟨D, hD_eval, hD⟩ := exists_ker_precomp_precomp_derivation T hT hL hR hLR hTL hTR E₀ hE₀
  have : Small.{u} (StrongDual 𝕜 T.ker) := small_strongDual_of_nontrivial (A := A) T.ker
  obtain ⟨N₀, hN₀⟩ := h.exists_eq_dualAction_sub_dualAction_of_small
    (E := StrongDual 𝕜 T.ker) (L := dualAction RK) (R := dualAction LK)
    (dualAction_mul_apply_of_right (restrictSubmodule_mul_apply_of_right hR T.ker hTR))
    (dualAction_mul_apply_of_left (restrictSubmodule_mul_apply_of_left hL T.ker hTL))
    (dualAction_apply_dualAction_apply_comm
      (restrictSubmodule_apply_comm hLR T.ker hTL hTR))
    D hD
  have hN₀_eval (a : A) (g : StrongDual 𝕜 T.ker) :
      D a g = N₀ (dualAction LK a g) - N₀ (dualAction RK a g) := by
    simpa only [sub_apply, dualAction_apply_apply] using congr($(hN₀ a) g)
  refine ⟨(e N₀ : StrongDual 𝕜 (StrongDual 𝕜 X)), (e N₀).property, fun a ↦ ?_⟩
  ext f
  have hL' :
      dualAction LK a (f.comp T.ker.subtypeL) = (dualAction L a f).comp T.ker.subtypeL := by
    ext x; simp [LK]
  have hR' :
      dualAction RK a (f.comp T.ker.subtypeL) = (dualAction R a f).comp T.ker.subtypeL := by
    ext x; simp [RK]
  have hcomm :
      (dualAction (dualAction L) a E₀ - dualAction (dualAction R) a E₀) f =
        N₀ ((dualAction L a f).comp T.ker.subtypeL) -
          N₀ ((dualAction R a f).comp T.ker.subtypeL) := by
    rw [← hD_eval a f, hN₀_eval a (f.comp T.ker.subtypeL), hL', hR']
  simp only [dualAction_apply_apply, sub_apply, kerDoubleDualEquivKerPrecompPrecomp_apply, e]
    at hcomm ⊢
  exact sub_eq_sub_iff_sub_eq_sub.1 hcomm

/-- **Johnson's theorem (existence of a virtual diagonal).** Every amenable Banach algebra over `ℝ`
or `ℂ` admits a virtual diagonal. -/
theorem IsAmenable.exists_isVirtualDiagonal (h : IsAmenable 𝕜 A) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M := by
  by_cases hA : Subsingleton A
  · exact ⟨0, IsVirtualDiagonal.of_subsingleton 0⟩
  have : Nontrivial A := not_subsingleton_iff_nontrivial.1 hA
  -- Step 1: pick a bounded two-sided BAI and a weak-star cluster point `E₀` of `e ⊗ e`.
  obtain ⟨l, C, hl, hC⟩ := h.exists_isApproximateUnit
  have := hl.neBot
  obtain ⟨E₀, hE₀L, hE₀R⟩ := exists_bidual_mul'_eq_inclusionInDoubleDual (𝕜 := 𝕜) hl hC
  -- Step 2: Cohen–Hewitt makes `Δ = mul' 𝕜 A` surjective, hence of closed range.
  have hclosed : IsClosed ((mul' 𝕜 A).range : Set A) := by
    rw [LinearMap.range_eq_top.2 (mul'_surjective hC hl.tendsto_mul_right)]
    exact isClosed_univ
  -- Step 3: apply the cohomological lifting lemma to `Δ = mul' 𝕜 A` and `E₀`.
  obtain ⟨N, hN_ker, hN_comm⟩ := h.exists_ker_precomp_precomp_comm (mul' 𝕜 A) hclosed
    mulLeft_mul_apply mulRight_mul_apply mulLeft_mulRight_apply_comm
    (fun a x hx ↦ by rw [LinearMap.mem_ker, coe_coe] at hx ⊢; simp [hx])
    (fun a x hx ↦ by rw [LinearMap.mem_ker, coe_coe] at hx ⊢; simp [hx])
    E₀ fun a ↦ by
      rw [map_sub, precomp_precomp_mul'_dualAction_mulLeft,
        precomp_precomp_mul'_dualAction_mulRight, hE₀L a, hE₀R a, sub_self]
  exact ⟨E₀ - N, ⟨hN_comm, fun a ↦ by rw [map_sub, hN_ker, sub_zero, hE₀L a]⟩⟩

/-- **Johnson's characterization of amenability (virtual diagonals).** A Banach algebra over `ℝ` or
`ℂ` is amenable if and only if it has a virtual diagonal. -/
theorem isAmenable_iff_exists_isVirtualDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M :=
  ⟨IsAmenable.exists_isVirtualDiagonal, fun ⟨_, hM⟩ ↦ hM.isAmenable⟩

/-- **Johnson's characterization of amenability (bounded approximate diagonals).** A Banach algebra
over `ℝ` or `ℂ` is amenable if and only if it has a bounded approximate diagonal. -/
theorem isAmenable_iff_exists_isApproximateDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ (l : Filter (CompletedProjectiveTensor 𝕜 A A)) (C : ℝ),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  isAmenable_iff_exists_isVirtualDiagonal.trans
    exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal

/-- **Universe independence of amenability.** In an amenable Banach algebra over `ℝ` or `ℂ`, every
bounded derivation into the dual of a bounded bimodule in any universe is inner. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction_univ (h : IsAmenable 𝕜 A)
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  let ⟨_, hM⟩ := h.exists_isVirtualDiagonal
  hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

/-- In an amenable Banach algebra over `ℝ` or `ℂ`, the first bounded Hochschild cohomology
`H¹(A, E*)` vanishes for every bounded `A`-bimodule `E` in any universe. -/
theorem IsAmenable.subsingleton_hochschildBimoduleCohomology_one (h : IsAmenable 𝕜 A)
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    Subsingleton (hochschildBimoduleCohomology (dualAction R) (dualAction L)
      (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
      (dualAction_apply_dualAction_apply_comm hLR) 1) :=
  (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).2 fun D hD ↦
    h.exists_eq_dualAction_sub_dualAction_univ hL hR hLR D hD

end Johnson

end TauCeti
