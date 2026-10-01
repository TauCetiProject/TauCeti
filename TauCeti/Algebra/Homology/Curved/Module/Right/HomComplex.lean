/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Defs
public import TauCeti.Algebra.Homology.DG.Module.Right.HomComplex

/-!
# The Hom complex of curved differential graded right modules

Let `M` and `N` be curved differential graded right modules over the same curved differential
graded algebra `(A, d, w)`.  As for ordinary DG modules, the degree-`p` cochains are the
right-module maps raising internal degree by `p`, and the differential is the graded commutator

`δ(f) = d_N ∘ f - (-1)^p f ∘ d_M`.

Individual curved modules have no cohomology, since `d_M² x = x * w` need not vanish.  The Hom
differential nevertheless squares to zero: the mixed terms cancel by the sign rule, leaving

`δ²(f)(x) = d_N² (f x) - f (d_M² x) = f x * w - f (x * w) = 0`,

because both modules square to right multiplication by the *same* curvature and `f` is a
right-module map.  Hence the cochains form an honest cochain complex of modules over the ground
ring, which is the input for the DG category of curved modules and its homotopy category.  At
curvature zero it is the Hom complex of the underlying ordinary DG right modules.

## Main definitions

* `TauCeti.dgRightModuleCochains.curvedDifferential`: the graded-commutator differential on
  cochains between two curved differential graded right modules.
* `TauCeti.curvedDGRightModuleHomComplex`: the Hom complex of two curved differential graded
  right modules.

## Main results

* `TauCeti.dgRightModuleCochains.curvedDifferential_comp_self`: the Hom differential squares to
  zero.
* `TauCeti.dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff`: the closed degree-zero
  cochains are the maps commuting with the module differentials.
* `TauCeti.curvedDGRightModuleHomComplex_zero`: at curvature zero the curved Hom complex is the
  ordinary DG Hom complex.

## Implementation notes

As for `TauCeti.dgRightModuleHomComplex`, the complex is exposed so that the component types in
its public differential application lemma reduce to the homogeneous-cochain modules.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
* B. Keller, *Deriving DG categories*, Section 2, for the uncurved Hom complex.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}
  {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {ℳN : ℤ → Submodule R N}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] {dN : N →ₗ[R] N}

namespace dgRightModuleCochains

variable {hM : IsCurvedDGRightModule h ℳ dM} {hN : IsCurvedDGRightModule h ℳN dN}

/-- The differential on homogeneous right-module cochains between two curved differential graded
right modules over the same curved algebra: the graded commutator with the two module
differentials. -/
def curvedDifferential (p : ℤ) :
    dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p →ₗ[R]
      dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) (p + 1) :=
  gradedCommutator hM.isHomogeneous hM.leibniz hN.isHomogeneous hN.leibniz p

/-- Evaluating the curved Hom differential gives the graded commutator with the module
differentials. -/
@[simp]
theorem curvedDifferential_apply (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) (x : M) :
    ((curvedDifferential (hM := hM) (hN := hN) p f).1 : M →ₗ[Aᵐᵒᵖ] N) x =
      dN (f.1 x) - p.negOnePow • f.1 (dM x) :=
  gradedCommutator_apply _ _ _ _ p f x

/-- **The curved Hom differential squares to zero.** Both modules square to right
multiplication by the same curvature `w`, and a cochain is a right-module map, so
`f x * w - f (x * w)` vanishes. -/
theorem curvedDifferential_comp_self (p : ℤ) :
    (curvedDifferential (hM := hM) (hN := hN) (p + 1)).comp
      (curvedDifferential (hM := hM) (hN := hN) p) = 0 := by
  ext f x
  simp only [LinearMap.comp_apply, curvedDifferential, gradedCommutator_gradedCommutator_apply,
    hN.sq_eq, hM.sq_eq, map_smul, sub_self, Submodule.coe_zero, LinearMap.zero_apply]

/-- The curved Hom differential applied twice vanishes. -/
@[simp]
theorem curvedDifferential_curvedDifferential (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :
    curvedDifferential (hM := hM) (hN := hN) (p + 1)
      (curvedDifferential (hM := hM) (hN := hN) p f) = 0 :=
  LinearMap.congr_fun (curvedDifferential_comp_self p) f

/-- A degree-zero cochain is closed exactly when it commutes with the module differentials. -/
theorem curvedDifferential_zero_eq_zero_iff
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) 0) :
    curvedDifferential (hM := hM) (hN := hN) 0 f = 0 ↔ ∀ x, dN (f.1 x) = f.1 (dM x) := by
  simp only [Subtype.ext_iff, LinearMap.ext_iff, curvedDifferential_apply, Int.negOnePow_zero,
    one_smul, Submodule.coe_zero, LinearMap.zero_apply, sub_eq_zero]

/-- **Zero curvature.** For ordinary differential graded right modules, regarded as curved
modules of curvature zero, the curved Hom differential is the ordinary DG Hom differential. -/
theorem curvedDifferential_isCurvedDGRightModule_zero {hDG : IsDGAlgebra 𝒜 d}
    {hM : IsDGRightModule hDG ℳ dM} {hN : IsDGRightModule hDG ℳN dN} (p : ℤ) :
    curvedDifferential (hM := hM.isCurvedDGRightModule_zero)
      (hN := hN.isCurvedDGRightModule_zero) p = differential (hM := hM) (hN := hN) p := by
  ext f x
  simp

end dgRightModuleCochains

/-- The Hom complex between two curved differential graded right modules over the same curved
algebra.  Its degree-`p` term consists of the right-module linear maps raising internal degree by
`p`, and its differential is the graded commutator with the two module differentials. -/
@[expose]
def curvedDGRightModuleHomComplex (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGRightModule h ℳN dN) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of
    (fun p ↦ ModuleCat.of R
      (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p))
    (fun p ↦ ModuleCat.ofHom (dgRightModuleCochains.curvedDifferential (hM := hM) (hN := hN) p))
    (fun p ↦ ModuleCat.hom_ext <| dgRightModuleCochains.curvedDifferential_comp_self p)

/-- The degree-`p` term of the curved Hom complex is the module of degree-`p` homogeneous
cochains. -/
@[simp]
theorem curvedDGRightModuleHomComplex_X (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGRightModule h ℳN dN) (p : ℤ) :
    (curvedDGRightModuleHomComplex hM hN).X p = ModuleCat.of R
      (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :=
  rfl

/-- The differential morphism of the curved Hom complex is induced by the graded commutator. -/
@[simp]
theorem curvedDGRightModuleHomComplex_d (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGRightModule h ℳN dN) (p : ℤ) :
    (curvedDGRightModuleHomComplex hM hN).d p (p + 1) =
      ModuleCat.ofHom (dgRightModuleCochains.curvedDifferential (hM := hM) (hN := hN) p) := by
  apply CochainComplex.of_d

/-- The differential of the curved Hom complex, evaluated on a homogeneous cochain, is the graded
commutator with the module differentials. -/
@[simp↓]
theorem curvedDGRightModuleHomComplex_d_apply (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGRightModule h ℳN dN) (p : ℤ)
    (f : (curvedDGRightModuleHomComplex hM hN).X p) :
    ((curvedDGRightModuleHomComplex hM hN).d p (p + 1)).hom f =
      dgRightModuleCochains.curvedDifferential (hM := hM) (hN := hN) p f := by
  rw [curvedDGRightModuleHomComplex_d]
  exact LinearMap.congr_fun
    (ModuleCat.hom_ofHom (dgRightModuleCochains.curvedDifferential (hM := hM) (hN := hN) p)) f

/-- **Zero curvature.** For ordinary differential graded right modules, regarded as curved
modules of curvature zero, the curved Hom complex is the ordinary DG Hom complex. -/
theorem curvedDGRightModuleHomComplex_zero {hDG : IsDGAlgebra 𝒜 d}
    (hM : IsDGRightModule hDG ℳ dM) (hN : IsDGRightModule hDG ℳN dN) :
    curvedDGRightModuleHomComplex hM.isCurvedDGRightModule_zero hN.isCurvedDGRightModule_zero =
      dgRightModuleHomComplex hM hN := by
  unfold curvedDGRightModuleHomComplex dgRightModuleHomComplex
  congr 1
  funext p
  rw [dgRightModuleCochains.curvedDifferential_isCurvedDGRightModule_zero]

end TauCeti
