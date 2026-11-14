/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Prism
public import TauCeti.Topology.PathSpace.Moore.Between.Append

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

Symmetrically, appending the reversal of a Moore path `δ` from `a` to `b`, followed by `δ`
itself, is homotopic to the identity on `C_*(P_{a→b} B; R)` through the prism with time last of
the growing retracing suffix (`pathChainAppendHomotopy`). It is graded linear for the loops at
`a` acting in front, with the Koszul sign of an odd operator
(`pathChainAppendHomotopy_smul`), which is the form a homotopy of left modules takes in a
tensor product over `C_*(Ω_a B; R)`.

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

section Append

variable (R) in
/-- The homotopy on `C_*(P_{a→b} B; R)` growing the retracing suffix `δ⁻¹ ⋆ δ`: the prism with
time last of `TauCeti.MoorePathBetween.appendSymmHomotopy`. Its boundary is appending `δ⁻¹`
and then `δ`, minus the identity. -/
def pathChainAppendHomotopy (δ : MoorePathBetween B a b) :
    pathChainLocalSystem R a b →ₗ[R] pathChainLocalSystem R a b :=
  cubicalChainModulePrismLast R (MoorePathBetween.appendSymmHomotopy δ a)

/-- **Appending a path and its reversal is homotopic to the identity**, through the prism with
time last of the growing retracing suffix. -/
theorem pathChainAppendHomotopy_spec (δ : MoorePathBetween B a b) (x : pathChainLocalSystem R a b) :
    cubicalChainModuleDifferential (MoorePathBetween B a b) (MooreLoopSpace B b) R
          (pathChainAppendHomotopy R δ x) +
        pathChainAppendHomotopy R δ
          (cubicalChainModuleDifferential (MoorePathBetween B a b) (MooreLoopSpace B b) R x) =
      cubicalChainModuleLinearMap R
        ((MoorePathBetween.append δ a).comp (MoorePathBetween.append δ.symm a)) x - x := by
  rw [pathChainAppendHomotopy,
    cubicalChainModuleDifferential_prismLast_add_prismLast_differential,
    cubicalChainModuleLinearMap_id, LinearMap.id_apply]

/-- The append homotopy is graded linear for the loops at the starting point acting in front: a
chain of loops of cohomological degree `i` passes it with the sign `(-1) ^ i`. -/
theorem pathChainAppendHomotopy_smul (δ : MoorePathBetween B a b) {i : ℤ}
    {α : loopChainAlgebra B a R} (hα : α ∈ cubicalChainGrading (MooreLoopSpace B a) R i)
    (x : pathChainLocalSystem R a b) :
    pathChainAppendHomotopy R δ (α • x) = i.negOnePow • (α • pathChainAppendHomotopy R δ x) :=
  cubicalChainModulePrismLast_smul _
    (fun t ω γ ↦ MoorePathBetween.appendSymmHomotopy_smul δ t γ ω) hα x

end Append

end TauCeti
