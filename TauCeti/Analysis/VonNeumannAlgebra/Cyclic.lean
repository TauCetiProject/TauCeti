/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# Cyclic and separating vectors for von Neumann algebras

Let `M` be a concrete von Neumann algebra acting on a complex Hilbert space `H`.

* `ξ : H` is **cyclic** for `M` (`VonNeumannAlgebra.IsCyclic`) when the orbit `M ξ` is dense in `H`.
* `ξ : H` is **separating** for `M` (`VonNeumannAlgebra.IsSeparating`) when `x ξ = 0` forces `x = 0`
  for `x ∈ M`.
* Using the orthogonal projection onto the closed orbit `closure (M ξ)`, which belongs to the
  commutant `M'`, `ξ` is cyclic for `M` if and only if it is separating for `M'`
  (`VonNeumannAlgebra.isCyclic_iff_isSeparating_commutant`,
  `VonNeumannAlgebra.isSeparating_iff_isCyclic_commutant`).

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), §2.1.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §2.1.
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector `ξ : H` is **cyclic** for `M` when the orbit `M ξ` is dense in `H`. -/
def IsCyclic (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  Dense (Set.range fun x : M => (x : H →L[ℂ] H) ξ)

theorem isCyclic_def (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsCyclic ξ ↔ Dense (Set.range fun x : M => (x : H →L[ℂ] H) ξ) :=
  Iff.rfl

/-- For a cyclic vector `ξ`, the bundled orbit `Set.range (fun x : M => x ξ)` is dense in `H`. -/
theorem IsCyclic.dense {M : VonNeumannAlgebra H} {ξ : H} (hξ : M.IsCyclic ξ) :
    Dense (Set.range fun x : M => (x : H →L[ℂ] H) ξ) :=
  hξ

/-- Set-image form of `VonNeumannAlgebra.IsCyclic`. -/
theorem isCyclic_iff (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsCyclic ξ ↔ Dense ((· ξ) '' (M : Set (H →L[ℂ] H))) := by
  rw [isCyclic_def]
  congr! 1
  ext v
  exact ⟨fun ⟨⟨x, hx⟩, hxv⟩ => ⟨x, hx, hxv⟩, fun ⟨x, hx, hxv⟩ => ⟨⟨x, hx⟩, hxv⟩⟩

/-- For a cyclic vector `ξ`, the orbit `(· ξ) '' (M : Set (H →L[ℂ] H))` is dense in `H`. -/
theorem IsCyclic.dense_image {M : VonNeumannAlgebra H} {ξ : H} (hξ : M.IsCyclic ξ) :
    Dense ((· ξ) '' (M : Set (H →L[ℂ] H))) :=
  (M.isCyclic_iff ξ).1 hξ

/-- A vector `ξ : H` is **separating** for `M` when `x ξ = 0` forces `x = 0` for `x ∈ M`. -/
def IsSeparating (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  ∀ x : M, (x : H →L[ℂ] H) ξ = 0 → x = 0

theorem isSeparating_def (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsSeparating ξ ↔ ∀ x : M, (x : H →L[ℂ] H) ξ = 0 → x = 0 :=
  Iff.rfl

/-- Membership-predicate form of `VonNeumannAlgebra.IsSeparating`. -/
theorem isSeparating_iff (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsSeparating ξ ↔ ∀ x ∈ M, x ξ = 0 → x = 0 :=
  ⟨fun h x hx hx0 => congr_arg Subtype.val (h ⟨x, hx⟩ hx0),
    fun h ⟨x, hx⟩ hx0 => Subtype.ext (h x hx hx0)⟩

/-- An operator in `M` that annihilates a separating vector is `0`. -/
theorem IsSeparating.eq_zero {M : VonNeumannAlgebra H} {ξ : H} (hξ : M.IsSeparating ξ)
    {x : H →L[ℂ] H} (hx : x ∈ M) (hx0 : x ξ = 0) : x = 0 :=
  (M.isSeparating_iff ξ).1 hξ x hx hx0

/-- Two operators in `M` agreeing on a separating vector are equal. -/
theorem IsSeparating.eq_of_apply_eq {M : VonNeumannAlgebra H} {ξ : H} (hξ : M.IsSeparating ξ)
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hy : y ∈ M) (hxy : x ξ = y ξ) : x = y :=
  sub_eq_zero.1 <| hξ.eq_zero (sub_mem hx hy) (by simp [hxy])

/-- **Cyclic versus separating.** A vector is cyclic for `M` if and only if it is separating for
the commutant `M'`. -/
theorem isCyclic_iff_isSeparating_commutant (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsCyclic ξ ↔ M.commutant.IsSeparating ξ := by
  refine ⟨fun hcyc => (M.commutant.isSeparating_iff ξ).2 fun y hy hy0 => ?_, fun hsep => ?_⟩
  · have hzero : Set.EqOn y (0 : H →L[ℂ] H) (Set.range fun x : M => (x : H →L[ℂ] H) ξ) := by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      have hcomm : x * y = y * x := mem_commutant_iff.1 hy x hx
      calc y (x ξ) = (y * x) ξ := rfl
        _ = (x * y) ξ := by rw [hcomm]
        _ = x (y ξ) := rfl
        _ = 0 := by rw [hy0, map_zero]
    have hall : closure (Set.range fun x : M => (x : H →L[ℂ] H) ξ) ⊆ {v : H | y v = 0} :=
      closure_minimal hzero (isClosed_eq y.continuous continuous_zero)
    exact ContinuousLinearMap.ext fun v => hall (hcyc v)
  · set K : Submodule ℂ H :=
      (M.toStarSubalgebra.toSubalgebra.toSubmodule.map
        (ContinuousLinearMap.apply ℂ H ξ).toLinearMap).topologicalClosure with hK
    have hKcoe : (K : Set H) = closure ((· ξ) '' (M : Set (H →L[ℂ] H))) := by
      rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
      -- The carrier of `M.toStarSubalgebra.toSubalgebra.toSubmodule` equals `(M : Set _)`.
      rfl
    have hp : K.starProjection ∈ M.commutant := by
      rw [VonNeumannAlgebra.IsStarProjection.mem_iff (isStarProjection_starProjection (U := K))
        M.commutant, M.commutant_commutant, K.range_starProjection]
      intro t ht
      rw [Module.End.mem_invtSubmodule]
      refine Submodule.topologicalClosure_minimal _ ?_
        ((Submodule.isClosed_topologicalClosure _).preimage t.continuous)
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨t * s, M.mul_mem ht hs, rfl⟩
    have hξK : ξ ∈ K := Submodule.le_topologicalClosure _ ⟨1, M.one_mem, rfl⟩
    have h1p : (1 - K.starProjection) ξ = 0 := by
      rw [sub_apply, one_apply_eq_self, K.starProjection_eq_self_iff.2 hξK, sub_self]
    have hp1 : K.starProjection = 1 :=
      (sub_eq_zero.1 (hsep.eq_zero (sub_mem M.commutant.one_mem hp) h1p)).symm
    rw [M.isCyclic_iff ξ, dense_iff_closure_eq, ← hKcoe]
    refine Set.eq_univ_of_forall fun v => ?_
    rw [SetLike.mem_coe, ← K.starProjection_eq_self_iff, hp1, one_apply_eq_self]

/-- A vector is separating for `M` if and only if it is cyclic for `M'`. -/
theorem isSeparating_iff_isCyclic_commutant (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsSeparating ξ ↔ M.commutant.IsCyclic ξ := by
  rw [isCyclic_iff_isSeparating_commutant, commutant_commutant]

end VonNeumannAlgebra
