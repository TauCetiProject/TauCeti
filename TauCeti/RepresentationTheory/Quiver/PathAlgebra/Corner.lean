/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# Corners of path-algebra images

Under a surjective algebra homomorphism, a submodule containing the images of every path
from `a` to `b` contains the corner cut out by the images of their vertex idempotents.
This turns reductions of individual paths into spanning statements for corners of relation
quotients. No finiteness assumption on the quiver or its paths is needed.

The argument is extracted from the type-`A` corner construction in
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm`.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver

universe u v w z

variable {k : Type u} [CommSemiring k] {Q : Type v} [Quiver.{w} Q]
  {A : Type z} [Semiring A] [Algebra k A]

/-- A submodule containing all path images from `a` to `b` contains the corresponding corner
of any surjective image of the path algebra. -/
theorem cornerSubmodule_le_of_ofPath_mem (φ : pathAlgebra k Q →ₙₐ[k] A)
    (hφ : Function.Surjective φ) (a b : Q) (M : Submodule k A)
    (hp : ∀ p : Path a b, φ (ofPath ⟨a, b, p⟩) ∈ M) :
    cornerSubmodule k (φ (vertexIdempotent k b)) (φ (vertexIdempotent k a)) ≤ M := by
  have hcut (x : TauCeti.Quiver.TotalPath Q) :
      φ (vertexIdempotent k b) * φ (ofPath x) * φ (vertexIdempotent k a) ∈ M := by
    obtain ⟨c, d, p⟩ := x
    by_cases hc : a = c
    swap
    · rw [mul_assoc, ← map_mul, ofPath_mul_vertexIdempotent_of_ne _ hc,
        map_zero, mul_zero]
      exact M.zero_mem
    subst c
    by_cases hd : b = d
    swap
    · rw [← map_mul, vertexIdempotent_mul_ofPath_of_ne _ hd, map_zero, zero_mul]
      exact M.zero_mem
    subst d
    rw [← map_mul, vertexIdempotent_mul_ofPath, ← map_mul, ofPath_mul_vertexIdempotent]
    exact hp p
  intro z hz
  have hid (i : Q) : IsIdempotentElem (φ (vertexIdempotent k i)) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) i) φ
  rw [mem_cornerSubmodule_iff k (hid b) (hid a)] at hz
  rw [← hz]
  obtain ⟨f, rfl⟩ := hφ z
  clear hz
  induction f using induction_linear with
  | zero =>
    simp only [map_zero, mul_zero, zero_mul]
    exact M.zero_mem
  | add f g hf hg =>
    simpa only [map_add, mul_add, add_mul] using M.add_mem hf hg
  | single x r =>
    simpa only [single_eq_smul_ofPath, map_smul, mul_smul_comm, smul_mul_assoc] using
      M.smul_mem r (hcut x)

end TauCeti.PathAlgebra
