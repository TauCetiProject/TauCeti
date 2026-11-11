/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Prism

/-!
# Module-linear inverse homotopies for path chains

Prepending the reversal of a Moore path from `a` to `b`, followed by the path itself,
induces the identity on `C_*(P_{a→c} B; R)` up to a homotopy **linear over `C_*(Ω_c B; R)`**.
The homotopy is the cubical prism of the growing retracing prefix. Every time slice commutes
with the right action. In cohomological grading it has degree minus one.

Applying `pathChainPrependHomotopy_spec` also to the reversed path gives both inverse
homotopies for `pathChainPrepend R γ c`. Thus the path-chain maps are homotopy equivalences
of right DG modules, strengthening their underlying quasi-isomorphism statement. These
module-linear homotopies, unlike coefficient-linear inverse homotopies alone, can be used
in tensor products over the loop-chain algebra.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public noncomputable section

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] (R : Type*) [CommRing R] {a b : B}

/-- The module-linear prism growing the retracing prefix `γ ⋆ γ⁻¹`. Its boundary is
prepending `γ` after `γ⁻¹`, minus the identity. -/
def pathChainPrependHomotopy (γ : MoorePathBetween B a b) (c : B) :
    pathChainLocalSystem R a c →ₗ[(loopChainAlgebra B c R)ᵐᵒᵖ]
      pathChainLocalSystem R a c :=
  cubicalChainModulePrismLinearMap (γ.prependSymmHomotopy c)
    (fun t ω δ ↦ γ.prependSymmHomotopy_op_smul t δ ω)

variable {R}

/-- On a homogeneous chain the inverse homotopy is the normalized prism of the retracing
prefix homotopy. -/
@[simp]
theorem pathChainPrependHomotopy_lof (γ : MoorePathBetween B a b) (c : B) {n : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a c) R n) :
    pathChainPrependHomotopy R γ c
        (cubicalChainModuleLof (MoorePathBetween B a c) (MooreLoopSpace B c) R n x) =
      cubicalChainModuleLof (MoorePathBetween B a c) (MooreLoopSpace B c) R (n + 1)
        (NormalizedCubicalChain.prism R (γ.prependSymmHomotopy c) n x) := by
  simp [pathChainPrependHomotopy]

/-- The module-linear inverse homotopy lowers cohomological degree by one. -/
theorem pathChainPrependHomotopy_mem (γ : MoorePathBetween B a b) (c : B) {i : ℤ}
    {x : pathChainLocalSystem R a c}
    (hx : x ∈ cubicalChainModuleGrading (MoorePathBetween B a c) (MooreLoopSpace B c) R i) :
    pathChainPrependHomotopy R γ c x ∈
      cubicalChainModuleGrading (MoorePathBetween B a c) (MooreLoopSpace B c) R (i - 1) := by
  simpa only [pathChainPrependHomotopy, cubicalChainModulePrismLinearMap_apply] using
    cubicalChainModulePrism_mem (γ.prependSymmHomotopy c) hx

/-- **Prepending a path and its reversal is module-linearly homotopic to the identity.**
The homotopy for the other composite is this same statement applied to `γ.symm`.
No contractibility or separation assumption on the space is required. -/
theorem pathChainPrependHomotopy_spec (γ : MoorePathBetween B a b) (c : B)
    (x : pathChainLocalSystem R a c) :
    cubicalChainModuleDifferential (MoorePathBetween B a c) (MooreLoopSpace B c) R
          (pathChainPrependHomotopy R γ c x) +
        pathChainPrependHomotopy R γ c
          (cubicalChainModuleDifferential (MoorePathBetween B a c) (MooreLoopSpace B c) R x) =
      pathChainPrepend R γ c (pathChainPrepend R γ.symm c x) - x := by
  have h := cubicalChainModuleDifferential_prism_add_prism_differential
    (G := MooreLoopSpace B c) (R := R) (γ.prependSymmHomotopy c) x
  rw [cubicalChainModuleLinearMap_comp, cubicalChainModuleLinearMap_id,
    LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [pathChainPrepend_apply, pathChainPrepend_apply]
  simpa only [pathChainPrependHomotopy, cubicalChainModulePrismLinearMap_apply] using h

end TauCeti
