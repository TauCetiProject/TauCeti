/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.Conformal.Montel.Basic
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.Complex.Wirtinger.Weyl

/-!
# Compactness for the weak Cauchy–Riemann equation with the standard structure

This file proves the planar compactness theorem for the weak equation
`TauCeti.IsWeakCauchyRiemannOn` (McDuff–Salamon, Theorem 4.1.1, in its planar form with fixed
data) for the standard structure `J = i` and `η = 0`, with values in a finite-dimensional complex
space `F`. If the images of compact subsets of `Ω` stay in fixed compact sets, a subsequence and
a weak solution `v` exist with `D^k u_{φ(m)} → D^k v` locally uniformly on `Ω` for every `k`,
where `D^k` is the real iterated Fréchet derivative `iteratedFDeriv ℝ k`.

For `J = i` the weak solutions are the holomorphic maps: a weak solution has vanishing weak
conjugate Wirtinger derivative, so it is holomorphic by Weyl's lemma, and a holomorphic map is a
weak solution with every exponent. The images bound is local boundedness, so Montel's theorem
selects a locally uniformly convergent subsequence with a holomorphic limit, and Weierstrass's
theorem gives the convergence of every iterated derivative. The gradient bound of the general
theorem is not needed for `J = i`: Cauchy's estimates derive it from the image bound.

## Main results

* `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_I_smul_id`: the
  planar compactness theorem for `J = i` and `η = 0`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 4.1.1 and Theorem B.4.2.
-/

public section

open Complex Filter Set TopologicalSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {p : ENNReal} {Ω : Opens ℂ}

/-- **Planar compactness for the standard structure.** Let `u m` be weak solutions on an open set
`Ω` of the homogeneous equation for `J = i`, with values in a finite-dimensional complex space,
such that the images of each compact `K ⊆ Ω` lie in a fixed compact set. Then a subsequence
`u (φ m)` and a weak solution `v` of the same equation exist such that every real iterated
derivative of `u (φ m)` converges to that of `v` locally uniformly on `Ω`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_I_smul_id
    {u : ℕ → ℂ → F}
    (hu : ∀ m, IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F)
      (fun _ _ => 0) (u m))
    (hK : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ K' : Set F, IsCompact K' ∧ ∀ m, MapsTo (u m) K K') :
    ∃ (φ : ℕ → ℕ) (v : ℂ → F), StrictMono φ ∧
      IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F) (fun _ _ => 0) v ∧
      ∀ k, TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ k (u (φ m)))
        (iteratedFDeriv ℝ k v) atTop Ω := by
  have := FiniteDimensional.proper ℂ F
  have hd (m : ℕ) : DifferentiableOn ℂ (u m) Ω :=
    (hu m).hasWeakConjWirtingerDerivOn_zero.differentiableOn (hu m).continuousOn
  have hb : IsLocallyBoundedOn u Ω := isLocallyBoundedOn_def.2 fun K hKΩ hKc => by
    obtain ⟨K', hK', huK⟩ := hK K hKΩ hKc
    obtain ⟨C, hC⟩ := hK'.isBounded.exists_norm_le
    exact ⟨C, fun m z hz => hC _ (huK m hz)⟩
  obtain ⟨φ, v, hφ, hv, hconv⟩ := montel Ω.isOpen hd hb
  exact ⟨φ, v, hφ, hv.isWeakCauchyRiemannOn,
    hconv.iteratedFDeriv ℝ (.of_forall fun m => hd (φ m)) Ω.isOpen⟩

end TauCeti
