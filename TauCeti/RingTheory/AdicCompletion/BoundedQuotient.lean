/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Finite

/-!
# Adic completeness with a bounded-torsion quotient

Let `P` be a submodule of `M` such that `I ^ k • M ⊆ P`. If `P` is `I`-adically complete,
then so is `M`. Neither finite generation nor Noetherianity is needed: the filtrations on `P`
induced by `I ^ n • M` and by `I ^ n • P` are cofinal, with a uniform shift of `k`.
Separatedness and precompleteness also pass separately from `P` to `M`.

In particular, over an `I`-adically complete Noetherian ring, a module receiving a map from a
finite module with cokernel annihilated by a power of `I` is `I`-adically complete. The target
module need not be finite.
This is the completeness step in the comparison of sections on a punctured spectrum with
formal sections: the image of the original finite module is finite, and its cokernel is the
first local cohomology module.

## References

* [The Stacks Project, Lemma 10.96.4](https://stacks.math.columbia.edu/tag/0BNG),
  the cofinal-filtration argument for a quotient annihilated by an ideal power.
* [The Stacks Project, Lemma 52.12.7](https://stacks.math.columbia.edu/tag/0EII),
  the formal-section comparison using this completeness consequence.
-/

public section

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

namespace Submodule

/-- If `I ^ k • M ⊆ P`, shifting by `k` compares the ambient `I`-adic filtration with that
of `P`. -/
theorem pow_add_smul_top_le_pow_smul (P : Submodule R M) {I : Ideal R} {k : ℕ}
    (hk : I ^ k • (⊤ : Submodule R M) ≤ P) (n : ℕ) :
    I ^ (n + k) • (⊤ : Submodule R M) ≤ I ^ n • P := by
  rw [pow_add, mul_smul]
  exact smul_mono_right _ hk

/-- If a submodule is `I`-adically separated and its quotient is annihilated by a power of `I`,
then the ambient module is `I`-adically separated. -/
theorem isHausdorff_of_pow_smul_top_le (P : Submodule R M) {I : Ideal R}
    [IsHausdorff I P] {k : ℕ}
    (hk : I ^ k • (⊤ : Submodule R M) ≤ P) : IsHausdorff I M := by
  refine ⟨fun x hx ↦ ?_⟩
  let y : P := ⟨x, hk (SModEq.zero.mp (hx k))⟩
  have hy : y = 0 := IsHausdorff.haus' (I := I) y fun n ↦
    SModEq.zero.mpr ((mem_smul_top_iff _ _ _).mpr
      (P.pow_add_smul_top_le_pow_smul hk n (SModEq.zero.mp (hx (n + k)))))
  exact congrArg P.subtype hy

/-- If a submodule is `I`-adically precomplete and its quotient is annihilated by a power of `I`,
then the ambient module is `I`-adically precomplete. -/
theorem isPrecomplete_of_pow_smul_top_le (P : Submodule R M) {I : Ideal R}
    [IsPrecomplete I P] {k : ℕ}
    (hk : I ^ k • (⊤ : Submodule R M) ≤ P) : IsPrecomplete I M := by
  refine ⟨fun x hx ↦ ?_⟩
  -- Translate a tail of the Cauchy sequence into `P`, where it has a limit.
  let y (n : ℕ) : P := ⟨x (n + k) - x k,
    hk (SModEq.sub_mem.mp (hx (Nat.le_add_left k n)).symm)⟩
  have hy {m n : ℕ} (hmn : m ≤ n) :
      y m ≡ y n [SMOD (I ^ m • ⊤ : Submodule R P)] := by
    rw [SModEq.sub_mem, mem_smul_top_iff]
    exact P.pow_add_smul_top_le_pow_smul hk m (by
      simpa only [Submodule.coe_sub, y, sub_sub_sub_cancel_right] using
        SModEq.sub_mem.mp (hx (Nat.add_le_add_right hmn k)))
  obtain ⟨z, hz⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I P) @hy
  refine ⟨x k + z, fun n ↦ (hx (Nat.le_add_right n k)).trans ?_⟩
  have h := (hz n).map P.subtype
  simp only [map_smul'', map_top, range_subtype] at h
  have h' := h.mono (smul_mono_right (I ^ n) le_top)
  simpa only [subtype_apply, y, add_sub_cancel] using (SModEq.refl (x k)).add h'

/-- An `I`-adically complete submodule with quotient annihilated by a power of `I` makes the
ambient module `I`-adically complete as well. -/
theorem isAdicComplete_of_pow_smul_top_le (P : Submodule R M) {I : Ideal R}
    [IsAdicComplete I P] {k : ℕ}
    (hk : I ^ k • (⊤ : Submodule R M) ≤ P) : IsAdicComplete I M where
  toIsHausdorff := Submodule.isHausdorff_of_pow_smul_top_le P hk
  toIsPrecomplete := Submodule.isPrecomplete_of_pow_smul_top_le P hk

end Submodule

/-- Over an `I`-adically complete Noetherian ring, a module receiving a map from a finite module
with cokernel annihilated by a power of `I` is `I`-adically complete. No finiteness of the target
is required. -/
theorem LinearMap.isAdicComplete_of_finite_of_pow_smul_top_le_range
    [IsNoetherianRing R] [IsAdicComplete I R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] (f : N →ₗ[R] M) {k : ℕ}
    (hk : I ^ k • (⊤ : Submodule R M) ≤ LinearMap.range f) : IsAdicComplete I M := by
  have : IsAdicComplete I (LinearMap.range f) := IsAdicComplete.of_finite I _
  exact Submodule.isAdicComplete_of_pow_smul_top_le (LinearMap.range f) hk
