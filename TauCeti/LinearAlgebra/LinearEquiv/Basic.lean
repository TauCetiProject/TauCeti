/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Ideal.Maps
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining semilinear equivalence.
Symmetry of a linear automorphism agrees with inversion in its group structure.
Through a linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, vᵢ)` for a spanning
family `v` of `M₂` span the kernel of `u ↦ (L u).1`.
A ring isomorphism over a common target carries the kernel of one map to the kernel of the other.
-/

public section

namespace LinearEquiv

/-- Symmetry of a linear automorphism is its group inverse. -/
theorem symm_eq_inv {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (e : V ≃ₗ[R] V) : e.symm = e⁻¹ := rfl

/-- Transport stability of a mapped submodule through an intertwining semilinear
equivalence. -/
theorem mem_of_preserves_map
    {R S V W : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module S W]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : V ≃ₛₗ[σ] W) (p : Submodule R V) (q : Submodule S W)
    (hmap : p.map (e : V →ₛₗ[σ] W) = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  subst hmap
  simpa [← hcomm] using hstable (Submodule.mem_map_of_mem hx)

/-- Through a linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, vᵢ)` for a spanning
family `v` of `M₂` span the kernel of the first component `u ↦ (L u).1`. -/
theorem span_range_symm_inr_eq_ker {R M M₁ M₂ ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] (L : M ≃ₗ[R] M₁ × M₂) {v : ι → M₂}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range fun i ↦ L.symm (0, v i)) =
      LinearMap.ker (LinearMap.fst R M₁ M₂ ∘ₗ L.toLinearMap) := by
  -- The vectors are the values of `L.symm ∘ inr` on `v`, so they span its range.
  have hspan : Submodule.span R (Set.range fun i ↦ L.symm (0, v i)) =
      LinearMap.range (L.symm.toLinearMap ∘ₗ LinearMap.inr R M₁ M₂) := by
    rw [← Submodule.span_eq (LinearMap.range _), LinearMap.coe_range,
      Submodule.span_range_eq_span_range_comp_of_span_eq_top hv]
    rfl
  -- The range of `L.symm ∘ inr` is the image under `L.symm` of `{0} × M₂ = ker (fst)`.
  rw [hspan, LinearMap.range_comp, LinearMap.range_inr, LinearMap.ker_comp,
    Submodule.map_equiv_eq_comap_symm, L.symm_symm]

end LinearEquiv

namespace RingEquiv

/-- A ring isomorphism over a common target carries the kernel of one map to the kernel of the
other, as a semilinear image. -/
theorem map_ker_toSemilinearEquiv {A B S : Type*} [Semiring A] [Semiring B] [Semiring S]
    (Φ : A ≃+* B) (g : A →+* S) (h : B →+* S)
    (hΦ : ∀ x, h (Φ x) = g x) :
    Submodule.map (Φ.toSemilinearEquiv : A →ₛₗ[(Φ : A →+* B)] B) (RingHom.ker g) =
      RingHom.ker h := by
  have : RingHomInvPair (Φ : A →+* B) (Φ.symm : B →+* A) := .of_ringEquiv Φ
  have : RingHomInvPair (Φ.symm : B →+* A) (Φ : A →+* B) := .of_ringEquiv_symm Φ
  ext y
  rw [Submodule.mem_map_equiv, RingHom.mem_ker, RingHom.mem_ker, ← hΦ]
  exact Iff.of_eq (congrArg (· = 0) (congrArg _ (Φ.apply_symm_apply y)))

end RingEquiv
