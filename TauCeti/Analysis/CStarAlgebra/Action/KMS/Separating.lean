/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.Adjoin
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing
import TauCeti.Analysis.CStarAlgebra.GNS
import TauCeti.Analysis.VonNeumannAlgebra.Density

/-!
# The GNS vector of a KMS state is separating

Let `α` be a point-norm continuous real action on a unital C⋆-algebra `A`, and let `ω` be a
β-KMS state of `α` for some real `β`. Write `π_ω` for the GNS representation of `ω` on the
Hilbert space `H_ω`, `[a]` for the class of `a ∈ A` in `H_ω`, and `Ω = [1]` for the cyclic
vector. The vector `Ω` is *separating* for the von Neumann algebra `M = π_ω(A)''`: an operator
`x ∈ M` with `x Ω = 0` is zero,
`TauCeti.CStarAction.IsKMSState.eq_zero_of_apply_toPreGNS_one_eq_zero`. Since `Ω` is also cyclic
for `M`, the pair `(M, Ω)` is the input of Tomita–Takesaki modular theory.

The first step extends the analytic KMS identity `ω (a⋆ c α_{iβ}(b)) = ω (b a⋆ c)` from
`π_ω(c)` to every `x ∈ M`: `⟪[a], x [α_{iβ}(b)]⟫ = ⟪[a b⋆], x Ω⟫` for `a ∈ A` and entire
analytic `b`, `TauCeti.CStarAction.IsKMSState.inner_apply_toPreGNS_entireExtension_mul_I`. Both
sides are vector functionals of `x` and agree on `π_ω(A)`, and by the von Neumann density
theorem, `StarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`, every
`x ∈ M` is approximated by some `π_ω(c)` simultaneously on `Ω` and on `[α_{iβ}(b)]`.

If `x Ω = 0`, the identity makes `x [α_{iβ}(b)]` orthogonal to every class `[a]`. The classes are
dense in `H_ω`, so `x [α_{iβ}(b)] = 0`. Every entire analytic element has the form `α_{iβ}(b)`,
namely for `b = α_{-iβ}(c)`, and the entire analytic elements are dense in `A`, so `x` vanishes on
the dense subspace of classes and `x = 0`.

The argument uses neither invariance of `ω` nor the condition `β ≠ 0`. At `β = 0` the KMS states
are the tracial states, so the GNS vector of a tracial state is separating as well.

## References

Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Corollary 5.3.9, for the separating property of the GNS vector of a KMS state.
-/

public section

open Complex PositiveLinearMap UniformSpace
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.CStarAction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-- **The KMS condition on the GNS von Neumann algebra.** Let `ω` be a β-KMS state on a unital
C⋆-algebra, with GNS representation `π_ω`, classes `[a]` and GNS vector `Ω = [1]`. For every
operator `x` in the von Neumann algebra `π_ω(A)''`, every `a` and every entire analytic `b`,
`⟪[a], x [α_{iβ}(b)]⟫ = ⟪[a b⋆], x Ω⟫`. For `x = π_ω(c)` this is the analytic KMS identity
`ω (a⋆ c α_{iβ}(b)) = ω (b a⋆ c)`. -/
theorem IsKMSState.inner_apply_toPreGNS_entireExtension_mul_I (hω : α.IsKMSState β ω)
    {x : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hx : x ∈ VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom))
    (a : A) {b : A} (hb : α.IsEntireAnalytic b) :
    ⟪(ω.toPositiveLinearMap.toPreGNS a : ω.toPositiveLinearMap.GNS),
        x (ω.toPositiveLinearMap.toPreGNS (α.entireExtension b (β * I)))⟫_ℂ =
      ⟪(ω.toPositiveLinearMap.toPreGNS (a * star b) : ω.toPositiveLinearMap.GNS),
        x (ω.toPositiveLinearMap.toPreGNS 1)⟫_ℂ := by
  let f := ω.toPositiveLinearMap
  let π := f.gnsStarAlgHom
  -- the class of `a` in the GNS space, so that `π c (cls a) = cls (c * a)`
  let cls : A → f.GNS := fun a => (f.toPreGNS a : f.GNS)
  have hπ (c a : A) : π c (cls a) = cls (c * a) := by
    simp [π, cls, f.gnsNonUnitalStarAlgHom_apply_coe]
  have hinner (a b : A) : ⟪cls a, cls b⟫_ℂ = ω (star a * b) := by
    simp [cls, f, Completion.inner_coe, preGNS_inner_def]
  -- `x` lies in the double commutant of the star subalgebra `π(A)`
  have hx' : x ∈ ((π.range : StarSubalgebra ℂ _) : Set _).centralizer.centralizer := by
    -- the carrier of `π.range` is the range of the underlying algebra homomorphism
    have hrange : ((π.range : StarSubalgebra ℂ _) : Set _) = Set.range π := rfl
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_adjoin, ← hrange,
      StarMemClass.star_coe_eq, Set.union_self] at hx
    exact hx
  set v := cls (α.entireExtension b (β * I))
  set C := ‖cls a‖ + ‖cls (a * star b)‖
  -- the difference of the two sides is smaller than every `ε > 0`
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨s, ⟨c, hcs⟩, hc⟩ :=
    StarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer π.range hx'
      ![cls 1, v] (div_pos hε (by positivity : (0 : ℝ) < C + 1))
  obtain rfl : s = π c := hcs.symm
  have h₀ : ‖π c (cls 1) - x (cls 1)‖ < ε / (C + 1) := by
    simpa [norm_sub_rev] using hc 0
  have h₁ : ‖x v - π c v‖ < ε / (C + 1) := by simpa using hc 1
  -- the analytic KMS identity for the pair `a⋆ c, b`
  have hkms : ⟪cls a, π c v⟫_ℂ = ⟪cls (a * star b), π c (cls 1)⟫_ℂ := by
    rw [hπ, hπ, hinner, hinner, mul_one, ← mul_assoc,
      hω.apply_mul_entireExtension_mul_I _ hb, star_mul, star_star, mul_assoc]
  have hsplit : ⟪cls a, x v⟫_ℂ - ⟪cls (a * star b), x (cls 1)⟫_ℂ =
      ⟪cls a, x v - π c v⟫_ℂ + ⟪cls (a * star b), π c (cls 1) - x (cls 1)⟫_ℂ := by
    rw [inner_sub_right, inner_sub_right, hkms]
    ring
  rw [zero_add, hsplit]
  calc ‖⟪cls a, x v - π c v⟫_ℂ + ⟪cls (a * star b), π c (cls 1) - x (cls 1)⟫_ℂ‖
      ≤ ‖cls a‖ * ‖x v - π c v‖ + ‖cls (a * star b)‖ * ‖π c (cls 1) - x (cls 1)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖cls a‖ * (ε / (C + 1)) + ‖cls (a * star b)‖ * (ε / (C + 1)) := by gcongr
    _ = C * (ε / (C + 1)) := by ring
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **The GNS vector of a KMS state is separating.** Let `ω` be a β-KMS state on a unital
C⋆-algebra, with GNS representation `π_ω` and GNS vector `Ω = [1]`. An operator `x` in the von
Neumann algebra `π_ω(A)''` with `x Ω = 0` is zero. -/
theorem IsKMSState.eq_zero_of_apply_toPreGNS_one_eq_zero (hω : α.IsKMSState β ω)
    {x : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hx : x ∈ VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom))
    (hx₀ : x (ω.toPositiveLinearMap.toPreGNS 1) = 0) : x = 0 := by
  let f := ω.toPositiveLinearMap
  let cls : A → f.GNS := fun a => (f.toPreGNS a : f.GNS)
  -- `x` kills `[α_{iβ}(b)]` for entire analytic `b`, as this vector is orthogonal to every class
  have hkill (b : A) (hb : α.IsEntireAnalytic b) : x (cls (α.entireExtension b (β * I))) = 0 := by
    have horth (u : f.GNS) : ⟪u, x (cls (α.entireExtension b (β * I)))⟫_ℂ = 0 := by
      induction u using Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) continuous_const
      | ih u =>
        have h := hω.inner_apply_toPreGNS_entireExtension_mul_I hx (f.ofPreGNS u) hb
        rwa [hx₀, inner_zero_right] at h
    exact inner_self_eq_zero.mp (horth _)
  -- every entire analytic `c` is `α_{iβ}(α_{-iβ}(c))`, and these are dense in `A`
  have hentire (c : A) (hc : α.IsEntireAnalytic c) : x (cls c) = 0 := by
    have h := hkill _ (hc.isEntireAnalytic_entireExtension (-(β * I)))
    rwa [hc.entireExtension_entireExtension, neg_add_cancel, hc.entireExtension_apply_zero] at h
  have hclosed : IsClosed {c : A | x (cls c) = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcls (c : A) : x (cls c) = 0 :=
    hclosed.closure_subset_iff.mpr (fun c hc => hentire c (mem_entireAnalytic.mp hc))
      (α.dense_entireAnalytic c)
  -- so `x` vanishes on the dense subspace of classes
  ext u
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_const
  | ih u => exact hcls (f.ofPreGNS u)

end TauCeti.CStarAction
