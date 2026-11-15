/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.Curved.Algebra.ConnectionChange.Basic

/-!
# Strict curved morphisms under simultaneous connection changes

If `f : (A, dA, wA) → (B, dB, wB)` is strict and `a ∈ A¹`, the same algebra map is strict
after changing the source connection by `a` and the target connection by `f a`.
It intertwines `dA + [a, -]` and `dB + [f a, -]`, and carries
`wA - dA a - a²` to `wB - dB (f a) - (f a)²`.

Thus simultaneous connection change respects identities and composition of strict morphisms.
This does not turn a connection change into a strict map from an algebra to its twist:
both endpoints of the given strict map are changed.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  We store the negative of his curvature, so the curvature change has two minus signs.
-/

public section

namespace TauCeti.CurvedDGAlgHom

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {wA : A} {wB : B} {wC : C}
  {hA : IsCurvedDGAlgebra 𝒜 dA wA} {hB : IsCurvedDGAlgebra ℬ dB wB}
  {hC : IsCurvedDGAlgebra 𝒞 dC wC}

/-- A strict curved morphism remains strict when both connections are changed by corresponding
degree-one elements. The underlying graded algebra homomorphism is unchanged. -/
noncomputable def connectionChange (f : CurvedDGAlgHom hA hB) {a : A} (ha : a ∈ 𝒜 1) :
    CurvedDGAlgHom (hA.connectionChange ha)
      (hB.connectionChange (GradedFunLike.map_mem f ha)) where
  toGradedAlgHom := f.toGradedAlgHom
  map_d' x := by
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q x =>
      obtain ⟨x, hx⟩ := x
      simp only [coe_toGradedAlgHom]
      rw [TauCeti.connectionChange_apply_of_mem ℬ (GradedFunLike.map_mem f hx),
        TauCeti.connectionChange_apply_of_mem 𝒜 hx]
      simpa only [map_sub, map_add, map_mul, Units.smul_def, map_zsmul] using
        congrArg (fun y ↦ y + f a * f x - q.negOnePow • (f x * f a)) (f.map_d x)
    | add x y hx hy => simp only [map_add, hx, hy]
  map_curvature' := by simp only [map_sub, map_mul, coe_toGradedAlgHom, map_curvature, map_d]

@[simp]
theorem connectionChange_toGradedAlgHom (f : CurvedDGAlgHom hA hB) {a : A} (ha : a ∈ 𝒜 1) :
    (f.connectionChange ha).toGradedAlgHom = f.toGradedAlgHom := (rfl)

@[simp]
theorem connectionChange_apply (f : CurvedDGAlgHom hA hB) {a : A} (ha : a ∈ 𝒜 1) (x : A) :
    f.connectionChange ha x = f x := (rfl)

/-- Simultaneous connection change preserves the identity strict morphism. -/
@[simp]
theorem connectionChange_id {a : A} (ha : a ∈ 𝒜 1) :
    (CurvedDGAlgHom.id hA).connectionChange ha = CurvedDGAlgHom.id (hA.connectionChange ha) := by
  apply toGradedAlgHom_injective
  simp

/-- Simultaneous connection change preserves composition of strict morphisms. -/
@[simp]
theorem connectionChange_comp (g : CurvedDGAlgHom hB hC) (f : CurvedDGAlgHom hA hB)
    {a : A} (ha : a ∈ 𝒜 1) :
    (g.comp f).connectionChange ha =
      (g.connectionChange (GradedFunLike.map_mem f ha)).comp (f.connectionChange ha) := by
  apply toGradedAlgHom_injective
  simp

end TauCeti.CurvedDGAlgHom
