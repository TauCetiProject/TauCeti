/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact

/-!
# Unitary invariance of the boundary map of the Hopf fibration

A unitary matrix `A ∈ U(n + 1)` acts on the unit sphere `S²ⁿ⁺¹ ⊂ ℂⁿ⁺¹` and on `CPⁿ`
(`TauCeti.ComplexProjectiveSpace.smul_mk`), and the Hopf projection `mk : S²ⁿ⁺¹ → CPⁿ` intertwines
the two actions. So `A` is a map of the Hopf fibration to itself. On the fibres it is complex
linear: it carries `u • v` to `u • A v` for a unit scalar `u`. In the circle coordinates
`u ↦ u • v` and `u ↦ u • A v` of the fibres over `[v]` and `[A v]`
(`TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`) it is therefore the identity of the circle.

By the naturality of the boundary map of a Serre fibration
(`TauCeti.TopCat.fibrationBoundary_map_of_eq`), the boundary map
`π_{k+1}(CPⁿ, [v]) → π_k(S¹, 1)` of the Hopf fibration is invariant under `A`
(`TauCeti.ComplexProjectiveSpace.hopfBoundary_map_smul`). In particular, for `n ≥ 1` the
isomorphism `π₂(CPⁿ, [v]) ≃* ℤ` of the Hopf fibration does not change when a class is moved by a
unitary matrix (`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_map_smul`). As `U(n + 1)` acts
transitively on the unit sphere, this compares the isomorphisms `π₂(CPⁿ) ≃* ℤ` at any two base
points.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Example 4.45.
-/

public section

noncomputable section

open CategoryTheory Matrix Metric
open scoped Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (A : unitaryGroup (Fin (n + 1)) ℂ)
  (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- **The boundary map of the Hopf fibration is invariant under unitary matrices.** For a unitary
`A`, the boundary map `π_{k+1}(CPⁿ, [A v]) → π_k(S¹, 1)` applied to the image under `A` of a class
of `π_{k+1}(CPⁿ, [v])` agrees with the boundary map at `[v]` applied to the class itself. -/
@[simp]
theorem hopfBoundary_map_smul (N : Type*) [Finite N]
    (a : HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v)) :
    hopfBoundary (UnitaryGroup.toLinearIsometryEquiv A • v) N
        (HomotopyGroup.map ⟨(A • ·), continuous_const_smul A⟩ (smul_mk A v) a) =
      hopfBoundary v N a := by
  set g := UnitaryGroup.toLinearIsometryEquiv A
  -- `A` acting on the sphere and on `CPⁿ` is a map of the Hopf fibration to itself.
  have sq : CommSq (TopCat.ofHom ⟨(g • ·), continuous_const_smul g⟩) (hopfHom n) (hopfHom n)
      (TopCat.ofHom ⟨(A • ·), continuous_const_smul A⟩) :=
    ⟨by ext x; exact (smul_mk A x).symm⟩
  -- On the fibres it is `u • v ↦ u • g v`.
  let φ : C((hopfHom n).fiber (mk n v), (hopfHom n).fiber (mk n (g • v))) :=
    ⟨fun x ↦ ⟨g • x.val, by
      simpa [g, ← smul_mk] using congrArg (A • ·) (Set.mem_singleton_iff.1 x.property)⟩,
      by fun_prop⟩
  -- `TopCat.ofHom f` has underlying map `f` by definition, so `key` is the naturality of the
  -- boundary map for this square, read without `TopCat.ofHom`.
  have key : TopCat.fibrationBoundary (mk_mem_serreFibrations n)
      (⟨g • v, rfl⟩ : (hopfHom n).fiber (mk n (g • v)))
      (HomotopyGroup.map ⟨(A • ·), continuous_const_smul A⟩ (smul_mk A v) a) =
        HomotopyGroup.map φ rfl (TopCat.fibrationBoundary (mk_mem_serreFibrations n)
          (⟨v, rfl⟩ : (hopfHom n).fiber (mk n v)) a) :=
    TopCat.fibrationBoundary_map_of_eq (N := N) sq (mk_mem_serreFibrations n)
      (mk_mem_serreFibrations n) (smul_mk A v) (e := ⟨v, rfl⟩) φ (fun _ ↦ rfl) rfl a
  rw [hopfBoundary_apply, hopfBoundary_apply, key, HomotopyGroup.homeomorphEquivOfEq_apply,
    HomotopyGroup.homeomorphEquivOfEq_apply, HomotopyGroup.map_comp_apply]
  refine HomotopyGroup.map_congr (ContinuousMap.ext fun x ↦ ?_) _ _ _
  -- In the circle coordinates of the two fibres, `φ` is the identity of the circle.
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Homeomorph.symm_apply_eq]
  obtain ⟨u, rfl⟩ := (hopfFiberHomeomorph v).surjective x
  refine Subtype.ext (Subtype.ext ?_)
  simp [φ, g, coe_hopfFiberHomeomorph_apply, Sphere.coe_sphere_smul]

/-- **The isomorphism `π₂(CPⁿ) ≃* ℤ` of the Hopf fibration is invariant under unitary matrices.**
For `n ≥ 1` and a unitary `A`, the image under `A` of a class of `π₂(CPⁿ, [v])` has, at the base
point `[A v]`, the same image in `ℤ` as the class itself at `[v]`. -/
@[simp]
theorem pi2MulEquivInt_map_smul (hn : n ≠ 0)
    (a : HomotopyGroup (Fin 2) (ComplexProjectiveSpace n) (mk n v)) :
    pi2MulEquivInt (UnitaryGroup.toLinearIsometryEquiv A • v) hn
        (HomotopyGroup.map ⟨(A • ·), continuous_const_smul A⟩ (smul_mk A v) a) =
      pi2MulEquivInt v hn a := by
  rw [pi2MulEquivInt_apply, pi2MulEquivInt_apply, ← HomotopyGroup.map_congrEquiv,
    hopfBoundary_map_smul]

end TauCeti.ComplexProjectiveSpace
