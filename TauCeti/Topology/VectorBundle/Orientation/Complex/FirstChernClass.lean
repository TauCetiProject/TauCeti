/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The first Chern class of a complex line bundle

Let `L → B` be a complex line bundle over a topological space `B`, with model fibre `F` of complex
dimension one. Its underlying real bundle `L_ℝ` is an oriented real plane bundle, each fibre being
oriented by `(v, i v)` for any nonzero `v` (`TauCeti.VectorBundleOrientation.complex`). The
**first Chern class** `c₁(L) ∈ H²(B; ℤ)` (`TauCeti.lineFirstChernClass`) is the Euler class of this
oriented plane bundle, which is `TauCeti.complexEulerClass` in complex rank one.

The first laws are inherited from those of the Euler class:

* naturality under continuous pullback (`TauCeti.lineFirstChernClass_pullback`), and more generally
  under a fibrewise complex-linear isomorphism over a continuous map of bases
  (`TauCeti.lineFirstChernClass_eq_singularCohomologyMap_of_fiberwise`);
* invariance under complex-linear isomorphism of line bundles over the same base, possibly with
  different model fibres (`TauCeti.lineFirstChernClass_eq_of_fiberwise`);
* vanishing for a line bundle with a nowhere-zero continuous section
  (`TauCeti.lineFirstChernClass_eq_zero_of_forall_ne_zero`), in particular for the trivial line
  bundle `B × F` (`TauCeti.lineFirstChernClass_trivial`);
* the sign rule for the conjugate line: a fibrewise conjugate-linear isomorphism `L' ≅ L` gives
  `c₁(L') = -c₁(L)` (`TauCeti.lineFirstChernClass_eq_neg_of_conjugateFiberwise`), since it carries
  the complex orientation `(v, i v)` of `L'` to the opposite orientation `(φ v, -i φ v)` of `L`.

The conjugate statement is phrased for an abstract fibrewise conjugate-linear isomorphism, so it
applies to every model of the conjugate line `conj L`, and, through the conjugate-linear Riesz
isomorphism of a Hermitian metric, to the dual line `L*`.

## Implementation notes

The class is named `lineFirstChernClass` because it is the first Chern class of a line bundle,
defined directly as an Euler class. The first Chern class of a complex vector bundle `E` of higher
constant rank is to be the class of its determinant line, `c₁(E) = c₁(det E)`, and on a line the
two agree through `det L ≃ L`. The rank hypothesis is `finrank ℂ F = 1`, and the class lives in
degree `2`, definitionally the degree `2 * 0 + 2` of `complexEulerClass` in rank `0 + 1`.
Integral coefficients are `ULift ℤ`, as for the Euler class.

## Main definitions

* `TauCeti.lineFirstChernClass`: the first Chern class `c₁(L) ∈ H²(B; ℤ)` of a complex line bundle,
  the Euler class of its underlying real plane bundle with the complex orientation.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the top Chern class as the Euler class of the underlying real bundle, and
  Lemma 14.9 on the conjugate bundle).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §20 (the first Chern class of a complex line bundle as its Euler class).
-/

public section

noncomputable section

open Bundle Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B]

section Definition

variable (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  (hF : finrank ℂ F = 1)

/-- **The first Chern class of a complex line bundle** `L → B`: the class `c₁(L) ∈ H²(B; ℤ)`, the
Euler class of the underlying oriented real plane bundle `L_ℝ` with its complex orientation
`(v, i v)`, that is `complexEulerClass` in complex rank one. -/
def lineFirstChernClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) 2 :=
  complexEulerClass F E (r := 0) hF

/-- The first Chern class of a complex line bundle is the Euler class of its underlying real plane
bundle with the complex orientation. -/
theorem lineFirstChernClass_def :
    lineFirstChernClass F E hF = complexEulerClass F E (r := 0) hF :=
  (rfl)

/-- **Naturality of the first Chern class.** The first Chern class of the pullback `f*L` along a
continuous map `f : B' → B` is the pull-back along `f` of the first Chern class of `L`. -/
theorem lineFirstChernClass_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) :
    lineFirstChernClass F ((⇑f) *ᵖ E) hF =
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2 (lineFirstChernClass F E hF) :=
  complexEulerClass_pullback F E (r := 0) hF f

/-- **A nowhere-vanishing section kills the first Chern class.** If the complex line bundle `L` has
a continuous section `s` with `s b ≠ 0` for every `b`, then `c₁(L) = 0`. -/
theorem lineFirstChernClass_eq_zero_of_forall_ne_zero {s : ∀ b, E b}
    (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) (hs₀ : ∀ b, s b ≠ 0) :
    lineFirstChernClass F E hF = 0 :=
  complexEulerClass_eq_zero_of_forall_ne_zero F E (r := 0) hF hs hs₀

variable (B) in
/-- **The first Chern class of the trivial line bundle vanishes**: `c₁(B × F) = 0` for a model
fibre `F` of complex dimension one. -/
@[simp]
theorem lineFirstChernClass_trivial : lineFirstChernClass F (Bundle.Trivial B F) hF = 0 :=
  complexEulerClass_trivial B F (r := 0) hF

end Definition

/-! ### Fibrewise complex- and conjugate-linear isomorphisms -/

section Fiberwise

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  (hF : finrank ℂ F = 1)

section BaseMap

variable {B' : Type w} [TopologicalSpace B']
  {F' : Type w} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℂ F']
  [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℂ F']
  {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommGroup (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, IsScalarTower ℝ ℂ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℂ F' E']
  (hF' : finrank ℂ F' = 1)

/-- **Naturality of the first Chern class under complex-linear bundle maps.** For a fibrewise
complex-linear isomorphism `φ b' : L'_{b'} ≃ L_{g b'}` of complex line bundles over a continuous
map `g : B' → B`, continuous on total spaces, `c₁(L')` is the pull-back along `g` of `c₁(L)`. -/
theorem lineFirstChernClass_eq_singularCohomologyMap_of_fiberwise {g : C(B', B)}
    {φ : ∀ b', E' b' ≃L[ℂ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    lineFirstChernClass F' E' hF' =
      TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (lineFirstChernClass F E hF) :=
  complexEulerClass_eq_singularCohomologyMap_of_fiberwise (r := 0) hF hF' hφ

/-- **Conjugate-linear bundle maps negate the first Chern class.** For a fibrewise conjugate-linear
isomorphism `φ b' : L'_{b'} ≃ L_{g b'}` of complex line bundles over a continuous map `g : B' → B`,
continuous on total spaces, `c₁(L')` is minus the pull-back along `g` of `c₁(L)`. -/
theorem lineFirstChernClass_eq_neg_singularCohomologyMap_of_conjugateFiberwise {g : C(B', B)}
    {φ : ∀ b', E' b' ≃L⋆[ℂ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    lineFirstChernClass F' E' hF' =
      -TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (lineFirstChernClass F E hF) := by
  rw [lineFirstChernClass_def,
    complexEulerClass_eq_neg_one_pow_smul_singularCohomologyMap_of_conjugateFiberwise (r := 0) hF
      hF' hφ, pow_one, neg_one_zsmul]
  rfl

end BaseMap

variable {F' : Type w} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℂ F']
  [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℂ F']
  {E' : B → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommGroup (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, IsScalarTower ℝ ℂ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℂ F' E']
  (hF' : finrank ℂ F' = 1)

/-- **Isomorphic complex line bundles have the same first Chern class.** For a fibrewise
complex-linear isomorphism `φ b : L'_b ≃ L_b` over the same base, continuous on total spaces,
`c₁(L') = c₁(L)`. The model fibres of `L'` and `L` may differ. -/
theorem lineFirstChernClass_eq_of_fiberwise {φ : ∀ b, E' b ≃L[ℂ] E b}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2)) :
    lineFirstChernClass F' E' hF' = lineFirstChernClass F E hF :=
  complexEulerClass_eq_of_fiberwise (r := 0) hF hF' hφ

/-- **The first Chern class of the conjugate line is the negative**: for a fibrewise
conjugate-linear isomorphism `φ b : L'_b ≃ L_b` over the same base, continuous on total spaces,
`c₁(L') = -c₁(L)`. This is `c₁(conj L) = -c₁(L)` for any model of the conjugate line `conj L`. -/
theorem lineFirstChernClass_eq_neg_of_conjugateFiberwise {φ : ∀ b, E' b ≃L⋆[ℂ] E b}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2)) :
    lineFirstChernClass F' E' hF' = -lineFirstChernClass F E hF :=
  complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise hF hF' hφ

end Fiberwise

end TauCeti
