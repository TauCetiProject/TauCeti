/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Vector fields preserving a distribution

A vector field `X` on a manifold **preserves** a distribution `D`
(`TauCeti.PreservesDistribution I D X`) when its Lie bracket with every smooth vector field tangent
to `D` on an open set `U` is again tangent to `D` on `U`:

`V x ∈ D x` for all `x ∈ U` implies `[X, V] x ∈ D x` for all `x ∈ U`.

This is the infinitesimal form of invariance of `D` under the local flow of `X`, `L_X Γ(D) ⊆ Γ(D)`.
For a hyperplane field it is defined without any defining one-form or coorientation, so it applies
to contact structures that are not the kernel of a global one-form: the vector fields preserving a
contact structure are its *contact vector fields*.

The vector fields preserving `D` form a Lie algebra:

* they form a vector space, at least among differentiable fields
  (`TauCeti.PreservesDistribution.add`, `TauCeti.PreservesDistribution.const_smul`,
  `TauCeti.PreservesDistribution.neg`, `TauCeti.PreservesDistribution.sub`);
* the Lie bracket of two smooth fields preserving `D` preserves `D`
  (`TauCeti.PreservesDistribution.mlieBracket`). This follows from the Leibniz identity
  `[[X, Y], V] = [X, [Y, V]] - [Y, [X, V]]`, since `[Y, V]` and `[X, V]` are again smooth fields
  tangent to `D` on `U`.

If `D` is involutive, every differentiable vector field tangent to `D` preserves `D`
(`TauCeti.IsInvolutiveDistribution.preservesDistribution`).

## Main definitions

* `TauCeti.PreservesDistribution I D X`: the vector field `X` preserves the distribution `D`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.3 (contact vector fields).
* P. Libermann, C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, D. Reidel, 1987,
  Chapter V, Section 13 (infinitesimal automorphisms of a contact structure).
-/

public section

open Set VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {X Y : Π x : M, TangentSpace I x}

variable (I) in
/-- A vector field `X` **preserves** the distribution `D` when, for every open set `U` and every
vector field `V` that is smooth and tangent to `D` on `U`, the Lie bracket `[X, V]` is tangent to
`D` on `U`. This is the infinitesimal invariance of `D` under the local flow of `X`; no defining
one-form or coorientation of `D` enters. -/
def PreservesDistribution (D : Π x : M, Submodule 𝕜 (TangentSpace I x))
    (X : Π x : M, TangentSpace I x) : Prop :=
  ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃V : Π x : M, TangentSpace I x⦄,
    CMDiff[U] ∞ (T% V) → (∀ x ∈ U, V x ∈ D x) → ∀ x ∈ U, mlieBracket I X V x ∈ D x

/-- The defining property of a vector field preserving a distribution. -/
theorem preservesDistribution_iff : PreservesDistribution I D X ↔
    ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃V : Π x : M, TangentSpace I x⦄,
      CMDiff[U] ∞ (T% V) → (∀ x ∈ U, V x ∈ D x) → ∀ x ∈ U, mlieBracket I X V x ∈ D x :=
  Iff.rfl

/-- The zero vector field preserves every distribution. -/
@[simp]
theorem preservesDistribution_zero : PreservesDistribution I D 0 := fun _ _ _ _ _ x _ ↦ by
  rw [mlieBracket_zero_left]
  exact zero_mem _

namespace PreservesDistribution

/-- A constant multiple of a vector field preserving `D` preserves `D`. -/
theorem const_smul (hX : PreservesDistribution I D X) (c : 𝕜) :
    PreservesDistribution I D (c • X) := fun _ hU _ hV hVD x hx ↦ by
  rw [mlieBracket_const_smul_left_field]
  exact Submodule.smul_mem _ c (hX hU hV hVD x hx)

/-- The negative of a vector field preserving `D` preserves `D`. -/
theorem neg (hX : PreservesDistribution I D X) : PreservesDistribution I D (-X) :=
  fun _ hU _ hV hVD x hx ↦ by
  rw [mlieBracket_neg_left]
  exact neg_mem (hX hU hV hVD x hx)

section Linear

variable [IsManifold I 2 M] [CompleteSpace E]

/-- The sum of two differentiable vector fields preserving `D` preserves `D`. -/
theorem add (hX : PreservesDistribution I D X) (hY : PreservesDistribution I D Y)
    (hXd : MDiff (T% X)) (hYd : MDiff (T% Y)) : PreservesDistribution I D (X + Y) :=
  fun _ hU _ hV hVD x hx ↦ by
  rw [mlieBracket_add_left (hXd x) (hYd x)]
  exact add_mem (hX hU hV hVD x hx) (hY hU hV hVD x hx)

/-- The difference of two differentiable vector fields preserving `D` preserves `D`. -/
theorem sub (hX : PreservesDistribution I D X) (hY : PreservesDistribution I D Y)
    (hXd : MDiff (T% X)) (hYd : MDiff (T% Y)) : PreservesDistribution I D (X - Y) := by
  rw [sub_eq_add_neg]
  exact hX.add hY.neg hXd fun x ↦ mdifferentiableAt_neg_section (hYd x)

end Linear

section Bracket

variable [IsRCLikeNormedField 𝕜] [CompleteSpace E] [IsManifold I ∞ M]

/-- **The vector fields preserving a distribution are closed under the Lie bracket.** If two smooth
vector fields preserve `D`, so does their Lie bracket. No regularity of `D` is needed. -/
theorem mlieBracket (hX : PreservesDistribution I D X) (hY : PreservesDistribution I D Y)
    (hXd : CMDiff ∞ (T% X)) (hYd : CMDiff ∞ (T% Y)) :
    PreservesDistribution I D (VectorField.mlieBracket I X Y) := by
  let _ : IsManifold I (minSmoothness 𝕜 3) M :=
    IsManifold.of_le (m := minSmoothness 𝕜 3) (n := ∞) (by simp)
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
    IsManifold.of_le (m := (∞ : ℕ∞ω) + 1) (n := ∞) (by simp)
  intro U hU V hV hVD x hx
  have hVat (y : M) (hy : y ∈ U) : CMDiffAt ∞ (T% V) y := hV.contMDiffAt (hU.mem_nhds hy)
  -- The brackets `[X, V]` and `[Y, V]` are again smooth on `U` and tangent to `D` there.
  have hbr {Z : Π x : M, TangentSpace I x} (hZd : CMDiff ∞ (T% Z)) :
      CMDiff[U] ∞ (T% (VectorField.mlieBracket I Z V)) := fun y hy ↦
    (ContMDiffAt.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (hZd y) (hVat y hy)
      (by simp)).contMDiffWithinAt
  have h2 {Z : Π x : M, TangentSpace I x} (hZd : CMDiff ∞ (T% Z)) (y : M) :
      CMDiffAt (minSmoothness 𝕜 2) (T% Z) y := (hZd y).of_le (by simp)
  -- The Leibniz identity `[X, [Y, V]] = [[X, Y], V] + [Y, [X, V]]` at `x`.
  have hL := leibniz_identity_mlieBracket_apply (h2 hXd x) (h2 hYd x)
    ((hVat x hx).of_le (by simp))
  rw [← sub_eq_of_eq_add hL]
  exact sub_mem (hX hU (hbr hYd) (hY hU hV hVD) x hx) (hY hU (hbr hXd) (hX hU hV hVD) x hx)

end Bracket

end PreservesDistribution

/-- **An involutive distribution is preserved by its tangent vector fields.** Every differentiable
vector field tangent to an involutive distribution `D` preserves `D`. -/
theorem IsInvolutiveDistribution.preservesDistribution (hD : IsInvolutiveDistribution I D)
    (hXd : MDiff (T% X)) (hXD : ∀ x, X x ∈ D x) : PreservesDistribution I D X :=
  fun _ hU _ hV hVD ↦ isInvolutiveDistribution_iff.1 hD hU hXd.mdifferentiableOn
    (hV.mdifferentiableOn (by simp)) (fun x _ ↦ hXD x) hVD

end TauCeti
