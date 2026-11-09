/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import TauCeti.Analysis.Normed.Algebra.GelfandRadius
public import TauCeti.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Analysis.Normed.Operator.SeparatingSpace

/-!
# Idempotents in the separating space of a homomorphism

Let `θ : A → B` be a homomorphism of complex Banach algebras, not assumed continuous. An algebra
homomorphism can only shrink quasispectra, so the spectral radius of `θ x` is at most `‖x‖`.
This rules out nonzero idempotents of `B` that lie both in the range of `θ` and in its
separating space: if `θ (a n) → p = θ u` with `a n → 0`, then the elements `θ (u * a n * u)` lie
in the corner `p B p`, tend to `p`, and have spectral radii tending to zero, which is impossible
near a nonzero idempotent. In particular, the separating space of a surjective homomorphism
contains no nonzero idempotent.

The structure theory of separating ideals produces a nonzero idempotent in every nonzero
finite-dimensional separating ideal of a semisimple algebra; this obstruction is what excludes
it for surjective homomorphisms.

## Main results

* `NonUnitalAlgHom.eq_zero_of_isIdempotentElem_of_mem_separatingSpace`: an idempotent in the
  range and in the separating space of `θ` is zero.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2, in particular the treatment of
  the separating spaces of epimorphisms leading to Johnson's uniqueness-of-norm theorem.
* B. E. Johnson, *The uniqueness of the (complete) norm topology*, Bull. Amer. Math. Soc. 73
  (1967), 537–539.
-/

public section

open Filter Topology

namespace NonUnitalAlgHom

variable {A B : Type*}
  [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [CompleteSpace A]
  [NonUnitalNormedRing B] [NormedSpace ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
  [CompleteSpace B]

/-- **Separating spaces of homomorphisms contain no idempotents from the range.** Let
`θ : A → B` be a homomorphism of complex Banach algebras, not assumed continuous. An idempotent
`p` of `B` lying both in the range of `θ` and in the separating space of `θ` is zero. For
surjective `θ`, the separating space contains no nonzero idempotent. -/
theorem eq_zero_of_isIdempotentElem_of_mem_separatingSpace (θ : A →ₙₐ[ℂ] B) {p : B}
    (hp : IsIdempotentElem p) (hpθ : p ∈ Set.range θ)
    (hpS : p ∈ (θ : A →ₗ[ℂ] B).separatingSpace) : p = 0 := by
  by_contra h0
  obtain ⟨u, rfl⟩ := hpθ
  obtain ⟨a, ha, hθa⟩ := (θ : A →ₗ[ℂ] B).mem_separatingSpace_iff_exists_seq.1 hpS
  -- The isometric embedding of `B` into its ℓ¹ unitization.
  let e : Unitization ℂ B →ₐ[ℂ] WithLp 1 (Unitization ℂ B) :=
    (WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := B) ℂ).symm
  let ι : B →ₙₐ[ℂ] WithLp 1 (Unitization ℂ B) :=
    e.toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom ℂ B)
  have hι (b : B) : ι b = WithLp.toLp 1 (b : Unitization ℂ B) := rfl
  have hιc : Continuous ι := by
    simpa only [← hι] using (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := B)).continuous
  -- The compressions `x n = u * a n * u` tend to zero, and `y n = ι (θ (x n))` lies in the corner
  -- of the nonzero idempotent `P = ι (θ u)` and tends to `P`.
  set P := ι (θ u)
  let x : ℕ → A := fun n ↦ u * a n * u
  let y : ℕ → WithLp 1 (Unitization ℂ B) := fun n ↦ ι (θ (x n))
  have hP : IsIdempotentElem P := hp.map ι
  have hP0 : P ≠ 0 := (map_ne_zero_iff ι fun b c h ↦
    WithLp.unitization_isometry_inr.injective (by simpa only [hι] using h)).2 h0
  have hx : Tendsto x atTop (𝓝 0) := by simpa using (ha.const_mul u).mul_const u
  have hy : Tendsto y atTop (𝓝 P) := by
    have h := (hθa.const_mul (θ u)).mul_const (θ u)
    rw [hp.eq, hp.eq] at h
    simpa [y, x, Function.comp_def] using (hιc.tendsto (θ u)).comp h
  have hPy (n : ℕ) : P * y n = y n := by
    simp only [y, x, P, map_mul, ← mul_assoc, hP.eq]
  have hyP (n : ℕ) : y n * P = y n := by
    simp only [y, x, P, map_mul, mul_assoc, hP.eq]
  -- `θ` does not increase spectral radii, so by Gelfand's formula in the unitization the Gelfand
  -- radius of `y n` is at most `‖x n‖`.
  have hyx (n : ℕ) : gelfandRadius (y n) ≤ ‖x n‖ := by
    have h := (spectralRadius_apply_le θ (x n)).trans (spectralRadius_le_nnnorm (x n))
    rw [TauCeti.spectralRadius_eq_gelfandRadius_toLp_inr] at h
    simpa only [y, hι, toReal_coe_nnnorm] using
      (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 h
  -- `1 - P + y n → 1`, so it is eventually a unit.
  have hW : Tendsto (fun n ↦ 1 - P + y n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := 1 - P)).add hy
  have hlim : Tendsto (fun n ↦ ‖x n‖ * ‖Ring.inverse (1 - P + y n)‖) atTop (𝓝 0) := by
    have hinv := (NormedRing.inverse_continuousAt (1 : (WithLp 1 (Unitization ℂ B))ˣ)).tendsto
    simpa using hx.norm.mul (hinv.comp (by simpa using hW)).norm
  refine zero_lt_one.not_ge (ge_of_tendsto hlim ?_)
  filter_upwards [hW.eventually (Units.isOpen.mem_nhds isUnit_one)] with n hn
  calc 1 ≤ gelfandRadius (y n) * ‖Ring.inverse (1 - P + y n)‖ :=
        hP.one_le_gelfandRadius_mul_norm_inverse hP0 (hPy n) (hyP n) hn
    _ ≤ ‖x n‖ * ‖Ring.inverse (1 - P + y n)‖ := by grw [hyx n]

end NonUnitalAlgHom
